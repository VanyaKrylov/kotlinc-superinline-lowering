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
import org.jetbrains.kotlin.ir.declarations.lazy.IrLazyFunction
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.*
import org.jetbrains.kotlin.ir.symbols.IrReturnTargetSymbol
import org.jetbrains.kotlin.ir.symbols.IrValueSymbol
import org.jetbrains.kotlin.ir.symbols.impl.IrReturnableBlockSymbolImpl
import org.jetbrains.kotlin.ir.types.IrType
import org.jetbrains.kotlin.ir.types.isNullable
import org.jetbrains.kotlin.ir.types.isUnit
import org.jetbrains.kotlin.ir.util.*
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.IrElementVisitor
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.util.OperatorNameConventions
import org.jetbrains.kotlin.utils.addToStdlib.safeAs
import kotlin.math.exp

fun IrReturn.withReturnTargetSymbol(returnTargetSymbol: IrReturnTargetSymbol) =
    IrReturnImpl(startOffset, endOffset, type, returnTargetSymbol, value)

fun IrValueParameter.isSuperInlineParameter(type: IrType = this.type) =
    !isNoinline && !type.isNullable() && (type.isFunction() || type.isSuspendFunction())

fun IrFunctionAccessExpression.isInlinableLambdaInvokeCall(): Boolean {
    val callee = this.symbol.owner
    val dispatchReceiverParameter = callee.dispatchReceiverParameter ?: return false
    val dispatchReceiverOrigin = this.dispatchReceiver.safeAs<IrReturnableBlock>()?.origin ?: return false

    return this is IrCall
            && callee.name == OperatorNameConventions.INVOKE
            && dispatchReceiverParameter.type.isFunction()
            && dispatchReceiverOrigin is SuperInlineLowering.SuperInlinedFunctionBodyOrigin
}

fun IrFunctionAccessExpression.isInlinableExtensionLambdaCall(): Boolean {
    val callee = this.symbol.owner
    val extensionReceiverParameter = callee.extensionReceiverParameter ?: return false
    val extensionReceiverOrigin = this.extensionReceiver.safeAs<IrReturnableBlock>()?.origin ?: return false

    return this is IrCall
            && callee.isInline
            && extensionReceiverParameter.type.isFunction()
            && extensionReceiverOrigin is SuperInlineLowering.SuperInlinedFunctionBodyOrigin
}

// TODO:
// 1) Change from IrComposite to IrReturnableBlock and add returnSymbol checks
// 2) Flatten IrComposite (or whatever Inliner returns)
// 3) Add captured variables suppost in Inliner via isTopLevelCallSite checks
class SuperInlineLowering(val context: CommonBackendContext) : BodyLoweringPass, IrElementTransformerVoidWithContext() {
    val superInlineAnnotationFqName: FqName = FqName("Script.SuperInline") //TODO change
    val superInlineAnnotationFqNameForCommandLine: FqName = FqName("SuperInline") //TODO change
    private val IrFunction.needsInlining get() = this.isInline && !this.isExternal
    private var containerScope: ScopeWithIr? = null
    private var isEnabled: Boolean = false
    private var inliningTriggered: Boolean = false

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        containerScope = createScope(container as IrSymbolOwner)
        irBody.accept(this, null)

        if (inliningTriggered) {
            irBody.transform(IrCompositeFlatteningTransformer(), null)
            irBody.transform(InlinedIrCompositePostProcessingTransformer(containerScope!!), null)
        }

        containerScope = null
        inliningTriggered = false

        irBody.patchDeclarationParents(container as? IrDeclarationParent ?: container.parent)
    }

    //todo use visitCall() instead?
    override fun visitFunctionAccess(expression: IrFunctionAccessExpression): IrExpression {
        val callee = expression.symbol.owner

        if (!callee.hasAnnotation(superInlineAnnotationFqName) &&
            !callee.hasAnnotation(superInlineAnnotationFqNameForCommandLine) &&
            !isEnabled ||
            expression !is IrCall ||
            callee is IrLazyFunction
        ) {
            return super.visitFunctionAccess(expression)
        }

        isEnabled = true //TODO change to true
        inliningTriggered = true
        expression.transformChildrenVoid() //TODO uncomment

        val parent = allScopes.map { it.irElement }.filterIsInstance<IrDeclarationParent>().lastOrNull()
            ?: allScopes.map { it.irElement }.filterIsInstance<IrDeclaration>().lastOrNull()?.parent
            ?: containerScope?.irElement as? IrDeclarationParent
            ?: (containerScope?.irElement as? IrDeclaration)?.parent
        val scope = currentScope ?: containerScope!!
        val inliner = Inliner(expression, callee, scope, parent, context)

        if (callee.hasAnnotation(superInlineAnnotationFqName) ||
            callee.hasAnnotation(superInlineAnnotationFqNameForCommandLine)
        ) {
            val inlined = inliner.inline()
            isEnabled = false

            return inlined
        }

        when (val dispatchReceiver = expression.dispatchReceiver) {
            is IrReturnableBlock -> if (expression.isInlinableLambdaInvokeCall() && isEnabled) {
                val callSite = expression

                return dispatchReceiver.apply {
                    transformChildren(object : IrElementTransformerVoid() {
                        override fun visitReturn(expression: IrReturn): IrExpression {
                            if (expression.returnTargetSymbol != dispatchReceiver.symbol)
                                return super.visitReturn(expression)

                            val function = expression.value.safeAs<IrFunctionExpression>()?.function ?: return super.visitReturn(expression)

                            return Inliner(callSite, function, scope, parent, context, true).inline()
                        }
                    }, null)
                    flattenAndPatchReturnTargetSymbol()
                }
            }
        }

        when (val extensionReceiver = expression.extensionReceiver) {
            is IrReturnableBlock -> if (expression.isInlinableExtensionLambdaCall() && isEnabled) {
                val callSite = expression

                return extensionReceiver.apply {
                    transformChildren(object : IrElementTransformerVoid() {
                        override fun visitReturn(expression: IrReturn): IrExpression {
                            if (expression.returnTargetSymbol != extensionReceiver.symbol)
                                return super.visitReturn(expression)

                            val extensionReceiverArgument =
                                expression.value.safeAs<IrFunctionExpression>()
                                    ?: return super.visitReturn(expression) //todo remove cast to IrFunctionExpression? because ideally we want to process any argument regardless the type

                            return Inliner(
                                callSite.apply { this.extensionReceiver = extensionReceiverArgument },
                                callee,
                                scope,
                                parent,
                                context
                            ).inline()
                        }
                    }, null)
                    flattenAndPatchReturnTargetSymbol()
                }
            }
        }

        //todo IrReturnableBlock can be not only an extension receiver but a value parameter as well

        return if (callee.isInline && !callee.isExternal && isEnabled)
            inliner.inline()
        else
            expression
    }

    private inner class Inliner(
        val callSite: IrFunctionAccessExpression,
        val callee: IrFunction,
        val currentScope: ScopeWithIr,
        val parent: IrDeclarationParent?,
        val context: CommonBackendContext,
        val ignoreDispatchReceiver: Boolean = false,
        val isTopLevelCallSite: Boolean = false
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

        private fun inlineFunction(
            callSite: IrFunctionAccessExpression,
            callee: IrFunction,
            performRecursiveInline: Boolean
        ): IrReturnableBlock {
            val copiedCallee = (copyIrElement.copy(callee) as IrFunction).apply {
                parent = callee.parent
            }

            val evaluationStatements = evaluateArguments(callSite, copiedCallee)
            val statements = (copiedCallee.body as IrBlockBody).statements
            val irReturnableBlockSymbol = IrReturnableBlockSymbolImpl()
            val endOffset = callee.endOffset
            val irBuilder = context.createIrBuilder(irReturnableBlockSymbol, endOffset, endOffset)
            val transformer = ParameterSubstitutor()

            statements.transform { it.transform(transformer, data = null) }

            // Process chained invoke calls. It's needed to be done after the ParameterSubstitutor, because we need to have
            // all the lambdas passed as parameter to be already inlined
            // Example:
            // lambdaParam.invoke().invoke() ==> (after ParameterSubstitutor) IrReturnableBlock( ... IrReturn(IrFuncExpr) ... ).invoke() ==> IrReturnableBlock( ... IrReturn ... )
            statements.transform { it.transform(this@SuperInlineLowering, null) } //TODO uncomment

            statements.addAll(0, evaluationStatements)

            return IrReturnableBlockImpl(
                startOffset = callSite.startOffset,
                endOffset = callSite.endOffset,
                type = callSite.type,
                symbol = irReturnableBlockSymbol,
                origin = SuperInlinedFunctionBodyOrigin(callee.symbol.owner.name.toString()),
                statements = statements,
                inlineFunctionSymbol = callee.symbol
            ).apply {
                flattenAndPatchReturnTargetSymbol()
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
                get() = parameter.isSuperInlineParameter() &&
                        argumentExpression is IrFunctionExpression //todo add support for FunctionReferences

            val isImmutableVariableLoad: Boolean
                get() = argumentExpression.let { argument ->
                    argument is IrGetValue && !argument.symbol.owner.let { it is IrVariable && it.isVar }
                }
        }

        // callee might be a copied version of callsite.symbol.owner
        private fun buildParameterToArgument(callSite: IrFunctionAccessExpression, callee: IrFunction): List<ParameterToArgument> {
            val parameterToArgument = mutableListOf<ParameterToArgument>()

            if (callSite.dispatchReceiver != null && callee.dispatchReceiverParameter != null && !ignoreDispatchReceiver)
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
                //argument.argumentExpression.transform(this@SuperInlineLowering, null)

                /*
                 * We need to create temporary variable for each argument except inlinable lambda arguments.
                 * For simplicity and to produce simpler IR we don't create temporaries for every immutable variable,
                 * not only for those referring to inlinable lambdas.
                 */
                /*if (argument.isInlinableLambdaArgument) {
                    substituteMap[argument.parameter] = argument.argumentExpression
                    (argument.argumentExpression as? IrFunctionReference)?.let { evaluationStatements += evaluateArguments(it) }
                    return@forEach
                }*/

                if (argument.isInlinableLambdaArgument) {
                    substituteMap[argument.parameter] = argument.argumentExpression
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

    class SuperInliner : IrElementTransformerVoidWithContext() {
        override fun visitCall(expression: IrCall): IrExpression {
            return super.visitCall(expression)
        }
    }

    private class InlinedIrCompositePostProcessingTransformer(val containerScope: ScopeWithIr) : IrElementTransformerVoidWithContext() {
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

        override fun visitComposite(expression: IrComposite): IrExpression { //todo rewrite for IrReturnableBlock
            when (val origin = expression.origin) {
                is SuperInlinedFunctionBodyOrigin -> {

                    if (!isTopLevelStatement) {
                        val scopeWithIr = currentScope ?: containerScope

                        if (expression.type.isUnit()) {
                            expression.transformChildren(object : IrElementTransformerVoid() {
                                override fun visitReturn(expression: IrReturn): IrExpression {
                                    return if (expression.returnTargetSymbol == scopeWithIr.scope.scopeOwnerSymbol) //initializers for variables inside composite have the same returnTargetSymbol... :/
                                        expression.value
                                    else
                                        expression
                                }

                                override fun visitComposite(expression: IrComposite): IrExpression {
                                    return this@InlinedIrCompositePostProcessingTransformer.visitComposite(expression)
                                }
                            }, null)

                            /*newStatements.apply {
                                addAll(1, expression.statements)
                            }*/

                            return expression
                        }

                        val tmpVar = scopeWithIr.scope.createTemporaryVariableDeclaration(expression.type, origin.calleeName)

                        expression.transformChildren(object : IrElementTransformerVoid() {
                            override fun visitReturn(expression: IrReturn): IrExpression {
                                return if (expression.returnTargetSymbol == scopeWithIr.scope.scopeOwnerSymbol) //initializers for variables inside composite have the same returnTargetSymbol... :/
                                    IrSetValueImpl(
                                        expression.startOffset,
                                        expression.endOffset,
                                        expression.value.type,
                                        tmpVar.symbol,
                                        expression.value,
                                        null
                                    ) else
                                    expression
                            }
/*
                            override fun visitComposite(expression: IrComposite): IrExpression {
                                return this@InlinedIrCompositePostProcessingTransformer.visitComposite(expression)
                            }*/
                        }, null)

                        newStatements.apply {
                            add(0, tmpVar)
                            addAll(1, expression.statements)
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
            val indicesToNewStatements = mutableMapOf<Int, List<IrStatement>>()

            body.statements.forEachIndexed { i, statement ->
                isTopLevelStatement = true
                body.statements[i] = statement.transform(this, null) as IrStatement
                if (newStatements.isNotEmpty()) {
                    indicesToNewStatements.computeIfAbsent(i) { mutableListOf<IrStatement>().apply { addAll(newStatements) } }
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
    }

    private inner class IrCompositeFlatteningTransformer : IrElementTransformerVoid() {
        /*override fun visitComposite(expression: IrComposite): IrExpression {
            expression.transformChildrenVoid()

            expression.statements.transformFlat {
                when (it) {
                    is IrComposite -> it.statements
                    is IrReturn ->
                        when (it.value.safeAs<IrComposite>()?.origin) {
                            is SuperInlinedFunctionBodyOrigin -> it.value.safeAs<IrComposite>()!!.statements
                            else -> null
                        }

                    else -> null
                }
            }

            return expression
        }*/

        override fun visitBlock(expression: IrBlock): IrExpression {
            return when (expression) {
                is IrReturnableBlock -> {
                    expression.transformChildrenVoid()

                    val parentBlock = expression
                    expression.statements.transformFlat {
                        when (val parentStatement = it) {
                            is IrReturnableBlock -> parentStatement.statements.apply {
                                transformInPlace {
                                    it.transform(object : IrElementTransformerVoid() {
                                        override fun visitReturn(expression: IrReturn): IrExpression {
                                            return if (expression.returnTargetSymbol == parentStatement.symbol)
                                                IrReturnImpl(
                                                    expression.startOffset,
                                                    expression.endOffset,
                                                    expression.type,
                                                    parentBlock.symbol,
                                                    expression.value
                                                )
                                            else
                                                expression
                                        }
                                    }, null)
                                }
                            }

                            is IrReturn -> when (parentStatement.value.safeAs<IrReturnableBlock>()?.origin) {
                                is SuperInlinedFunctionBodyOrigin -> parentStatement.value.safeAs<IrReturnableBlock>()!!.statements
                                else -> null
                            }

                            else -> null
                        }
                    }

                    return expression
                }
                else -> super.visitBlock(expression)
            }
        }

        override fun visitTypeOperator(expression: IrTypeOperatorCall): IrExpression {
            when (val arg = expression.argument) {
                is IrComposite -> {
                    if (arg.origin is SuperInlinedFunctionBodyOrigin) {
                        arg.type = expression.typeOperand
                    }
                }
            }

            return super.visitTypeOperator(expression)
        }
    }

    private fun IrReturnableBlock.flattenAndPatchReturnTargetSymbol() = apply {
        fun IrStatement.patchReturnTargetSymbols(
            innerReturnableBlockSymbol: IrReturnTargetSymbol,
            irReturnableBlockSymbol: IrReturnTargetSymbol
        ) = transform(object : IrElementTransformerVoid() {

            override fun visitReturn(expression: IrReturn): IrExpression {
                return if (expression.returnTargetSymbol == innerReturnableBlockSymbol)
                    expression.withReturnTargetSymbol(irReturnableBlockSymbol)
                else
                    super.visitReturn(expression)
            }

        }, null)

        fun IrReturnableBlock.flattenAndPatchWithReturnTargetSymbol() =
            if (origin is SuperInlinedFunctionBodyOrigin) {
                val innerReturnableBlockSymbol = symbol

                statements.apply {
                    transform {
                        it.patchReturnTargetSymbols(innerReturnableBlockSymbol, this@flattenAndPatchReturnTargetSymbol.symbol)
                    }
                }
            } else {
                null
            }

        statements.transformFlat {
            when (it) {
                is IrReturnableBlock -> it.flattenAndPatchWithReturnTargetSymbol()
                is IrReturn -> when (val v = it.value) {
                    is IrReturnableBlock -> return@transformFlat v.flattenAndPatchWithReturnTargetSymbol()
                    else -> return@transformFlat null
                }

                else -> null
            }
        }
    }

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