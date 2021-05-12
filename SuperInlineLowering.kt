/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.backend.common.lower.inline

import org.jetbrains.kotlin.backend.common.*
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.UNDEFINED_OFFSET
import org.jetbrains.kotlin.ir.builders.irReturn
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.*
import org.jetbrains.kotlin.ir.symbols.IrValueSymbol
import org.jetbrains.kotlin.ir.symbols.impl.IrReturnableBlockSymbolImpl
import org.jetbrains.kotlin.ir.types.IrSimpleType
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.typeOrNull
import org.jetbrains.kotlin.ir.util.*
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.IrElementVisitor
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.util.OperatorNameConventions
import java.util.Collections.addAll


//todo test without lambda param - should work
class SuperInlineLowering(val context: CommonBackendContext) : BodyLoweringPass, IrElementTransformerVoidWithContext() {
    val superInlineAnnotationFqName: FqName = FqName("Script.SuperInline")

    private val IrFunction.needsInlining get() = this.isInline && !this.isExternal

    private var containerScope: ScopeWithIr? = null

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        containerScope = createScope(container as IrSymbolOwner)
        irBody.accept(this, null)

        irBody.transform(object : IrElementTransformerVoidWithContext() {
            var isTopLevelStatement: Boolean = false
            val newStatements = mutableListOf<IrStatement>()

            override fun visitDeclaration(declaration: IrDeclarationBase): IrStatement {
                isTopLevelStatement = false
                return super.visitDeclaration(declaration)
            }

            override fun visitExpression(expression: IrExpression): IrExpression {
                isTopLevelStatement = false
                expression.transformChildrenVoid()

                return expression
            }

            override fun visitComposite(expression: IrComposite): IrExpression {
                when(val origin = expression.origin) {
                    is SuperInlinedFunctionBodyOrigin -> {
                        if (!isTopLevelStatement) {
                            val scopeWithIr = currentScope ?: containerScope
                            val tmpVar = scopeWithIr!!.scope.createTemporaryVariableDeclaration(expression.type, origin.calleeName)
                            expression.transformChildren(object : IrElementTransformerVoid() {
                                override fun visitReturn(expression: IrReturn): IrExpression {
                                    return if(expression.returnTargetSymbol == scopeWithIr.scope.scopeOwnerSymbol)
                                        IrSetValueImpl( //todo FIX! Only returns from this
                                            expression.startOffset,
                                            expression.endOffset,
                                            expression.type,
                                            tmpVar.symbol,
                                            expression.value,
                                            null
                                        ) else
                                            expression
                                }
                            }, null)
                            newStatements.apply {
                                add(tmpVar)
                                addAll(expression.statements)
                            }
                            return IrGetValueImpl(expression.startOffset, expression.endOffset, tmpVar.symbol, null)
                        } else
                            return IrCompositeImpl(
                                expression.startOffset,
                                expression.endOffset,
                                expression.type,
                                null,
                                expression.statements
                            )
                    }
                    else -> {
                        isTopLevelStatement = false
                        return super.visitComposite(expression)
                    }
                }
            }

            //TODO add support later
            /*override fun visitExpressionBody(body: IrExpressionBody): IrBody {
                body.transformChildrenVoid()
                return super.visitExpressionBody(body)
            }*/

            override fun visitBlockBody(body: IrBlockBody): IrBody {
                val indicesToNewStatements = mutableMapOf<Int,List<IrStatement>>()
                body.statements.forEachIndexed { i, statement ->
                    isTopLevelStatement = true
                    body.statements[i] = statement.transform(this, null) as IrStatement
                    if (newStatements.isNotEmpty()) {
                        indicesToNewStatements.computeIfAbsent(i) { mutableListOf<IrStatement>().apply { addAll(newStatements) }}
                        newStatements.clear()
                    }
                }
                if (indicesToNewStatements.isNotEmpty()) {
                    val extendedBodyStatements = mutableListOf<IrStatement>()
                    for (i in body.statements.indices) {
                        indicesToNewStatements[i]?.let { extendedBodyStatements.addAll(it) }
                        extendedBodyStatements.add(body.statements[i])
                    }
                    return body.apply {
                        statements.clear()
                        statements.addAll(extendedBodyStatements)
                    }
                }

                return body
            }
        }, null)

        containerScope = null

        irBody.patchDeclarationParents(container as? IrDeclarationParent ?: container.parent)
    }

    /*override fun lower(irFile: IrFile) {
        irFile.accept(this, null)
        irFile.patchDeclarationParents(irFile)
    }*/

    override fun visitFunctionAccess(expression: IrFunctionAccessExpression): IrExpression {
        if (expression.symbol.owner.hasAnnotation(superInlineAnnotationFqName)) {
            when(expression) {
                /*is IrConstructorCall -> {
                    expression.getArgumentsWithIr()
                        .filter { it.second.type.isFunction() }
                        .map { it.second.transform(object: IrElementTransformerVoid() {
                            override fun visitFunctionExpression(expression: IrFunctionExpression): IrExpression {
                                return expression.apply { this.function.transformChildren(this@SuperInlineLowering, null) }
                            }
                        }, null) }

                    return expression
                }*/

                is IrCall -> return Inliner(expression, expression.symbol.owner, currentScope ?: containerScope!!, allScopes.map { it.irElement }.filterIsInstance<IrDeclarationParent>().lastOrNull()
                    ?: allScopes.map { it.irElement }.filterIsInstance<IrDeclaration>().lastOrNull()?.parent ?: containerScope?.irElement as? IrDeclarationParent
                    ?: (containerScope?.irElement as? IrDeclaration)?.parent, context).inline()//SuperInliningInliner(expression, expression.symbol.owner, currentScope, expression.symbol.owner.parent).inline()
            }
        }

        return super.visitFunctionAccess(expression)
    }

    private inner class Inliner(
        val callSite: IrFunctionAccessExpression,
        val callee: IrFunction,
        val currentScope: ScopeWithIr,
        val parent: IrDeclarationParent?,
        val context: CommonBackendContext
    ) {

        val copyIrElement = run {
            val typeParameters =
                if (callee is IrConstructor)
                    callee.parentAsClass.typeParameters
                else callee.typeParameters
            val typeArguments =
                (0 until callSite.typeArgumentsCount).associate {
                    typeParameters[it].symbol to callSite.getTypeArgument(it)
                }
            DeepCopyIrTreeWithSymbolsForInliner(typeArguments, parent)
        }

        val substituteMap = mutableMapOf<IrValueParameter, IrExpression>()

        fun inline() = inlineFunction(callSite, callee, false)

        /**
         * TODO: JVM inliner crashed on attempt inline this function from transform.kt with:
         *  j.l.IllegalStateException: Couldn't obtain compiled function body for
         *  public inline fun <reified T : org.jetbrains.kotlin.ir.IrElement> kotlin.collections.MutableList<T>.transform...
         */
        private inline fun <reified T : IrElement> MutableList<T>.transform(transformation: (T) -> IrElement) {
            forEachIndexed { i, item ->
                set(i, transformation(item) as T)
            }
        }

        private fun inlineFunction(
            callSite: IrFunctionAccessExpression,
            callee: IrFunction,
            performRecursiveInline: Boolean
        ): IrComposite {
            val copiedCallee = (copyIrElement.copy(callee) as IrFunction).apply {
                parent = callee.parent
                if (performRecursiveInline) {
                    body?.transformChildrenVoid()
                    valueParameters.forEachIndexed { index, param ->
                        if (callSite.getValueArgument(index) == null) {
                            // Default values can recursively reference [callee] - transform only needed.
                            param.defaultValue = param.defaultValue?.transform(this@SuperInlineLowering, null)
                        }
                    }
                }
            }

            val evaluationStatements = evaluateArguments(callSite, copiedCallee)
            val statements = (copiedCallee.body as IrBlockBody).statements

            val scopeSymbol = currentScope.scope.scopeOwnerSymbol
            val irBuilder = context.createIrBuilder(scopeSymbol)

            /*val irReturnableBlockSymbol = IrReturnableBlockSymbolImpl()
            val endOffset = callee.endOffset
            *//* creates irBuilder appending to the end of the given returnable block: thus why we initialize
             * irBuilder with (..., endOffset, endOffset).
             *//*
            val irBuilder = context.createIrBuilder(irReturnableBlockSymbol, endOffset, endOffset)*/

            val transformer = ParameterSubstitutor()
            statements.transform { it.transform(transformer, data = null) }
            statements.addAll(0, evaluationStatements)

            return IrCompositeImpl( //TODO finish
                callSite.startOffset,
                callSite.endOffset,
                callSite.type,
                SuperInlinedFunctionBodyOrigin(callee.symbol.owner.name.toString()),
                statements
            ).apply {
                transformChildrenVoid(object : IrElementTransformerVoid() {
                    override fun visitReturn(expression: IrReturn): IrExpression {
                        expression.transformChildrenVoid(this)

                        if (expression.returnTargetSymbol == copiedCallee.symbol) // return target is lifted to scopeOwner because the function is inlined
                            return irBuilder.irReturn(expression.value)
                        return expression
                    }
                })
                patchDeclarationParents(parent) // TODO: Why it is not enough to just run SetDeclarationsParentVisitor?
            }

            /*return IrReturnableBlockImpl(
                startOffset = callSite.startOffset,
                endOffset = callSite.endOffset,
                type = callSite.type,
                symbol = irReturnableBlockSymbol,
                origin = null,
                statements = statements,
                inlineFunctionSymbol = callee.symbol
            ).apply {
                transformChildrenVoid(object : IrElementTransformerVoid() {
                    override fun visitReturn(expression: IrReturn): IrExpression {
                        expression.transformChildrenVoid(this)

                        if (expression.returnTargetSymbol == copiedCallee.symbol) // return target is lifted to scopeOwner because the function is inlined
                            return irBuilder.irReturn(expression.value)
                        return expression
                    }
                })
                patchDeclarationParents(parent) // TODO: Why it is not enough to just run SetDeclarationsParentVisitor?
            }*/
        }

        //---------------------------------------------------------------------//

        private inner class ParameterSubstitutor : IrElementTransformerVoid() {

            override fun visitGetValue(expression: IrGetValue): IrExpression {
                val newExpression = super.visitGetValue(expression) as IrGetValue
                val argument = substituteMap[newExpression.symbol.owner] ?: return newExpression

                argument.transformChildrenVoid(this) // Default argument can contain subjects for substitution.

                return if (argument is IrGetValueWithoutLocation)
                    argument.withLocation(newExpression.startOffset, newExpression.endOffset)
                else (copyIrElement.copy(argument) as IrExpression)
            }

            //-----------------------------------------------------------------//

            override fun visitCall(expression: IrCall): IrExpression {
                if (!isLambdaCall(expression))
                    return super.visitCall(expression)

                val dispatchReceiver = expression.dispatchReceiver as IrGetValue
                val functionArgument = substituteMap[dispatchReceiver.symbol.owner] ?: return super.visitCall(expression)
                if ((dispatchReceiver.symbol.owner as? IrValueParameter)?.isNoinline == true)
                    return super.visitCall(expression)

                if (functionArgument is IrFunctionReference) {
                    functionArgument.transformChildrenVoid(this)

                    val function = functionArgument.symbol.owner
                    val functionParameters = function.explicitParameters
                    val boundFunctionParameters = functionArgument.getArgumentsWithIr()
                    val unboundFunctionParameters = functionParameters - boundFunctionParameters.map { it.first }
                    val boundFunctionParametersMap = boundFunctionParameters.associate { it.first to it.second }

                    var unboundIndex = 0
                    val unboundArgsSet = unboundFunctionParameters.toSet()
                    val valueParameters = expression.getArgumentsWithIr().drop(1) // Skip dispatch receiver.

                    val superType = functionArgument.type as IrSimpleType
                    val superTypeArgumentsMap = expression.symbol.owner.parentAsClass.typeParameters.associate { typeParam ->
                        typeParam.symbol to superType.arguments[typeParam.index].typeOrNull!!
                    }

                    val immediateCall = with(expression) {
                        when (function) {
                            is IrConstructor -> {
                                val classTypeParametersCount = function.parentAsClass.typeParameters.size
                                IrConstructorCallImpl.fromSymbolOwner(
                                    startOffset,
                                    endOffset,
                                    function.returnType,
                                    function.symbol,
                                    classTypeParametersCount
                                )
                            }
                            is IrSimpleFunction ->
                                IrCallImpl(
                                    startOffset,
                                    endOffset,
                                    function.returnType,
                                    function.symbol,
                                    function.typeParameters.size,
                                    function.valueParameters.size
                                )
                            else ->
                                error("Unknown function kind : ${function.render()}")
                        }
                    }.apply {
                        for (parameter in functionParameters) {
                            val argument =
                                if (parameter !in unboundArgsSet) {
                                    val arg = boundFunctionParametersMap[parameter]!!
                                    if (arg is IrGetValueWithoutLocation)
                                        arg.withLocation(expression.startOffset, expression.endOffset)
                                    else arg
                                } else {
                                    if (unboundIndex == valueParameters.size && parameter.defaultValue != null)
                                        copyIrElement.copy(parameter.defaultValue!!.expression) as IrExpression
                                    else if (!parameter.isVararg) {
                                        assert(unboundIndex < valueParameters.size) {
                                            "Attempt to use unbound parameter outside of the callee's value parameters"
                                        }
                                        valueParameters[unboundIndex++].second
                                    } else {
                                        val elements = mutableListOf<IrVarargElement>()
                                        while (unboundIndex < valueParameters.size) {
                                            val (param, value) = valueParameters[unboundIndex++]
                                            val substitutedParamType = param.type.substitute(superTypeArgumentsMap)
                                            if (substitutedParamType == parameter.varargElementType!!)
                                                elements += value
                                            else
                                                elements += IrSpreadElementImpl(expression.startOffset, expression.endOffset, value)
                                        }
                                        IrVarargImpl(
                                            expression.startOffset, expression.endOffset,
                                            parameter.type,
                                            parameter.varargElementType!!,
                                            elements
                                        )
                                    }
                                }
                            when (parameter) {
                                function.dispatchReceiverParameter ->
                                    this.dispatchReceiver = argument.implicitCastIfNeededTo(function.dispatchReceiverParameter!!.type)

                                function.extensionReceiverParameter ->
                                    this.extensionReceiver = argument.implicitCastIfNeededTo(function.extensionReceiverParameter!!.type)

                                else ->
                                    putValueArgument(
                                        parameter.index,
                                        argument.implicitCastIfNeededTo(function.valueParameters[parameter.index].type)
                                    )
                            }
                        }
                        assert(unboundIndex == valueParameters.size) { "Not all arguments of the callee are used" }
                        for (index in 0 until functionArgument.typeArgumentsCount)
                            putTypeArgument(index, functionArgument.getTypeArgument(index))
                    }.implicitCastIfNeededTo(expression.type)
                    return this@SuperInlineLowering.visitExpression(super.visitExpression(immediateCall))
                }
                if (functionArgument !is IrFunctionExpression)
                    return super.visitCall(expression)

                // Inline the lambda. Lambda parameters will be substituted with lambda arguments.
                val newExpression = inlineFunction(
                    expression,
                    functionArgument.function,
                    false
                )
                // Substitute lambda arguments with target function arguments.
                return newExpression.transform(
                    this,
                    null
                )
            }

            //-----------------------------------------------------------------//

            override fun visitElement(element: IrElement) = element.accept(this, null)
        }

        private fun IrExpression.implicitCastIfNeededTo(type: IrType) =
            if (type == this.type)
                this
            else
                IrTypeOperatorCallImpl(startOffset, endOffset, type, IrTypeOperator.IMPLICIT_CAST, type, this)

        private fun isLambdaCall(irCall: IrCall): Boolean {
            val callee = irCall.symbol.owner
            val dispatchReceiver = callee.dispatchReceiverParameter ?: return false
            assert(!dispatchReceiver.type.isKFunction())

            return (dispatchReceiver.type.isFunction() || dispatchReceiver.type.isSuspendFunction())
                    && callee.name == OperatorNameConventions.INVOKE
                    && irCall.dispatchReceiver is IrGetValue
        }

        //-------------------------------------------------------------------------//

        private inner class ParameterToArgument(
            val parameter: IrValueParameter,
            val argumentExpression: IrExpression
        ) {

            val isInlinableLambdaArgument: Boolean
                get() = parameter.isInlineParameter() &&
                        (argumentExpression is IrFunctionReference
                                || argumentExpression is IrFunctionExpression)

            val isImmutableVariableLoad: Boolean
                get() = argumentExpression.let { argument ->
                    argument is IrGetValue && !argument.symbol.owner.let { it is IrVariable && it.isVar }
                }
        }

        // callee might be a copied version of callsite.symbol.owner
        private fun buildParameterToArgument(callSite: IrFunctionAccessExpression, callee: IrFunction): List<ParameterToArgument> {

            val parameterToArgument = mutableListOf<ParameterToArgument>()

            if (callSite.dispatchReceiver != null && callee.dispatchReceiverParameter != null)
                parameterToArgument += ParameterToArgument(
                    parameter = callee.dispatchReceiverParameter!!,
                    argumentExpression = callSite.dispatchReceiver!!
                )

            val valueArguments =
                callSite.symbol.owner.valueParameters.map { callSite.getValueArgument(it.index) }.toMutableList()

            if (callee.extensionReceiverParameter != null) {
                parameterToArgument += ParameterToArgument(
                    parameter = callee.extensionReceiverParameter!!,
                    argumentExpression = if (callSite.extensionReceiver != null) {
                        callSite.extensionReceiver!!
                    } else {
                        // Special case: lambda with receiver is called as usual lambda:
                        valueArguments.removeAt(0)!!
                    }
                )
            } else if (callSite.extensionReceiver != null) {
                // Special case: usual lambda is called as lambda with receiver:
                valueArguments.add(0, callSite.extensionReceiver!!)
            }

            val parametersWithDefaultToArgument = mutableListOf<ParameterToArgument>()
            for (parameter in callee.valueParameters) {
                val argument = valueArguments[parameter.index]
                when {
                    argument != null -> {
                        parameterToArgument += ParameterToArgument(
                            parameter = parameter,
                            argumentExpression = argument
                        )
                    }

                    // After ExpectDeclarationsRemoving pass default values from expect declarations
                    // are represented correctly in IR.
                    parameter.defaultValue != null -> {  // There is no argument - try default value.
                        parametersWithDefaultToArgument += ParameterToArgument(
                            parameter = parameter,
                            argumentExpression = parameter.defaultValue!!.expression
                        )
                    }

                    parameter.varargElementType != null -> {
                        val emptyArray = IrVarargImpl(
                            startOffset = callSite.startOffset,
                            endOffset = callSite.endOffset,
                            type = parameter.type,
                            varargElementType = parameter.varargElementType!!
                        )
                        parameterToArgument += ParameterToArgument(
                            parameter = parameter,
                            argumentExpression = emptyArray
                        )
                    }

                    else -> {
                        val message = "Incomplete expression: call to ${callee.render()} " +
                                "has no argument at index ${parameter.index}"
                        throw Error(message)
                    }
                }
            }
            // All arguments except default are evaluated at callsite,
            // but default arguments are evaluated inside callee.
            return parameterToArgument + parametersWithDefaultToArgument
        }

        //-------------------------------------------------------------------------//

        private fun evaluateArguments(functionReference: IrFunctionReference): List<IrStatement> {
            val arguments = functionReference.getArgumentsWithIr().map { ParameterToArgument(it.first, it.second) }
            val evaluationStatements = mutableListOf<IrStatement>()
            val substitutor = ParameterSubstitutor()
            val referenced = functionReference.symbol.owner
            arguments.forEach {
                val newArgument = if (it.isImmutableVariableLoad) {
                    it.argumentExpression.transform( // Arguments may reference the previous ones - substitute them.
                        substitutor,
                        data = null
                    )
                } else {
                    val newVariable =
                        currentScope.scope.createTemporaryVariable(
                            irExpression = it.argumentExpression.transform( // Arguments may reference the previous ones - substitute them.
                                substitutor,
                                data = null
                            ),
                            nameHint = callee.symbol.owner.name.toString(),
                            isMutable = false
                        )

                    evaluationStatements.add(newVariable)

                    IrGetValueWithoutLocation(newVariable.symbol)
                }
                when (it.parameter) {
                    referenced.dispatchReceiverParameter -> functionReference.dispatchReceiver = newArgument
                    referenced.extensionReceiverParameter -> functionReference.extensionReceiver = newArgument
                    else -> functionReference.putValueArgument(it.parameter.index, newArgument)
                }
            }
            return evaluationStatements
        }

        private fun evaluateArguments(callSite: IrFunctionAccessExpression, callee: IrFunction): List<IrStatement> {
            val arguments = buildParameterToArgument(callSite, callee)
            val evaluationStatements = mutableListOf<IrStatement>()
            val substitutor = ParameterSubstitutor()
            arguments.forEach { argument ->
                /*
                 * We need to create temporary variable for each argument except inlinable lambda arguments.
                 * For simplicity and to produce simpler IR we don't create temporaries for every immutable variable,
                 * not only for those referring to inlinable lambdas.
                 */
                if (argument.isInlinableLambdaArgument) {
                    substituteMap[argument.parameter] = argument.argumentExpression
                    (argument.argumentExpression as? IrFunctionReference)?.let { evaluationStatements += evaluateArguments(it) }
                    return@forEach
                }

                if (argument.isImmutableVariableLoad) {
                    substituteMap[argument.parameter] =
                        argument.argumentExpression.transform( // Arguments may reference the previous ones - substitute them.
                            substitutor,
                            data = null
                        )
                    return@forEach
                }

                // Arguments may reference the previous ones - substitute them.
                val variableInitializer = argument.argumentExpression.transform(substitutor, data = null)

                val newVariable =
                    currentScope.scope.createTemporaryVariable(
                        irExpression = IrBlockImpl(
                            variableInitializer.startOffset,
                            variableInitializer.endOffset,
                            variableInitializer.type,
                            InlinerExpressionLocationHint((currentScope.irElement as IrSymbolOwner).symbol)
                        ).apply {
                            statements.add(variableInitializer)
                        },
                        nameHint = callee.symbol.owner.name.toString(),
                        isMutable = false
                    )

                evaluationStatements.add(newVariable)
                substituteMap[argument.parameter] = IrGetValueWithoutLocation(newVariable.symbol)
            }
            return evaluationStatements
        }
    }

    private inner class SuperInliningInliner(
        val callSite: IrFunctionAccessExpression,
        val callee: IrFunction,
        val currentScope: ScopeWithIr?,
        val parent: IrDeclarationParent
    ) : IrElementTransformerVoid() {
        val copyIrElement = run {
            val typeParameters =
                if (callee is IrConstructor)
                    callee.parentAsClass.typeParameters
                else callee.typeParameters
            val typeArguments =
                (0 until callSite.typeArgumentsCount).associate {
                    typeParameters[it].symbol to callSite.getTypeArgument(it)
                }
            DeepCopyIrTreeWithSymbolsForInliner(typeArguments, parent)
        }

        val evaluationStatements = mutableListOf<IrStatement>()
        lateinit var copiedCalleeValueParamsToOldCalleeValueParams: Map<IrValueParameter,IrValueParameter>

        fun inline(): IrExpression {
            //callee.transformChildrenVoid() //TODO revert cause we CAN'T change initial function(callee) declaration
            val copiedCallee = (copyIrElement.copy(callee) as IrFunction).apply {
                parent = callee.parent
            }
            copiedCalleeValueParamsToOldCalleeValueParams = copiedCallee.valueParameters.zip(callee.valueParameters).toMap()
            if (callee.dispatchReceiverParameter != null && copiedCallee.dispatchReceiverParameter != null) {
                copiedCalleeValueParamsToOldCalleeValueParams = copiedCalleeValueParamsToOldCalleeValueParams + (copiedCallee.dispatchReceiverParameter!! to callee.dispatchReceiverParameter!!)
            }
            if (callee.extensionReceiverParameter != null && copiedCallee.extensionReceiverParameter != null) {
                copiedCalleeValueParamsToOldCalleeValueParams = copiedCalleeValueParamsToOldCalleeValueParams + (copiedCallee.extensionReceiverParameter!! to callee.extensionReceiverParameter!!)
            }
            copiedCallee.transformChildrenVoid()
            val irReturnableBlockSymbol = IrReturnableBlockSymbolImpl()
            val endOffset = copiedCallee.endOffset
            val irBuilder = context.createIrBuilder(irReturnableBlockSymbol, endOffset, endOffset)

            return IrReturnableBlockImpl(
                startOffset = callSite.startOffset,
                endOffset = callSite.endOffset,
                type = callSite.type,
                symbol = irReturnableBlockSymbol,
                origin = null,
                statements = (copiedCallee.body!! as IrBlockBody).statements.apply { addAll(0, evaluationStatements) },
                inlineFunctionSymbol = callee.symbol
            ).apply {
                transformChildrenVoid(object : IrElementTransformerVoid() {
                    override fun visitReturn(expression: IrReturn): IrExpression {
                        expression.transformChildrenVoid(this)

                        if (expression.returnTargetSymbol == copiedCallee.symbol)
                            return irBuilder.irReturn(expression.value)
                        return expression
                    }
                })
                patchDeclarationParents(parent)
            }
        }

        override fun visitGetValue(expression: IrGetValue): IrExpression {
            return when(val arg = callSite.getArgumentsWithIr().find { it.first == copiedCalleeValueParamsToOldCalleeValueParams[expression.symbol.owner] }?.second) { //TODO with copied callee!
                is IrConstructorCall -> arg
                is Any -> {
                    val newVariable =
                        currentScope!!.scope.createTemporaryVariable(
                            irExpression = IrBlockImpl(
                                arg.startOffset,
                                arg.endOffset,
                                arg.type,
                                InlinerExpressionLocationHint((currentScope.irElement as IrSymbolOwner).symbol)
                            ).apply {
                                statements.add(arg)
                            },
                            nameHint = callee.symbol.owner.name.toString(),
                            isMutable = false
                        )
                    evaluationStatements.add(newVariable)

                    return IrGetValueImpl(expression.startOffset, expression.endOffset, newVariable.symbol)
                }
                else -> expression
            }
            /*return entrypointCall.getArgumentsWithIr()
                .find { it.first == expression.symbol.owner }?.second
                ?: super.visitGetValue(expression)*/
        }

        /*override fun visitTypeParameter(declaration: IrTypeParameter): IrStatement {
            TODO()
        }*/

        /*override fun visitFunctionAccess(expression: IrFunctionAccessExpression): IrExpression {
            expression
            return super.visitFunctionAccess(expression)
        }*/
    }

    private class IrGetValueWithoutLocation(
        override val symbol: IrValueSymbol,
        override val origin: IrStatementOrigin? = null
    ) : IrGetValue() {
        override val startOffset: Int get() = UNDEFINED_OFFSET
        override val endOffset: Int get() = UNDEFINED_OFFSET

        override var type: IrType
            get() = symbol.owner.type
            set(value) {
                symbol.owner.type = value
            }

        override fun <R, D> accept(visitor: IrElementVisitor<R, D>, data: D) =
            visitor.visitGetValue(this, data)

        override fun copy(): IrGetValue {
            TODO("not implemented")
        }

        fun withLocation(startOffset: Int, endOffset: Int) =
            IrGetValueImpl(startOffset, endOffset, type, symbol, origin)
    }

    class SuperInlinedFunctionBodyOrigin(val calleeName: String) : IrStatementOriginImpl("")
}