/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

@file:Suppress("DuplicatedCode")

package org.jetbrains.kotlin.backend.common.lower.inline

import org.jetbrains.kotlin.backend.common.BodyLoweringPass
import org.jetbrains.kotlin.backend.common.CommonBackendContext
import org.jetbrains.kotlin.backend.common.IrElementTransformerVoidWithContext
import org.jetbrains.kotlin.backend.common.ScopeWithIr
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.UNDEFINED_OFFSET
import org.jetbrains.kotlin.ir.builders.irComposite
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
import org.jetbrains.kotlin.ir.util.*
import org.jetbrains.kotlin.ir.visitors.IrElementTransformer
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.IrElementVisitor
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.util.OperatorNameConventions
import org.jetbrains.kotlin.utils.addToStdlib.safeAs

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
// 1) Add captured variables support in Inliner via isTopLevelCallSite checks
class SuperInlineLowering(val context: CommonBackendContext) : BodyLoweringPass, IrElementTransformerVoidWithContext() {
    private val superInlineAnnotationFqName: FqName = FqName("Script.SuperInline")
    private val superInlineAnnotationFqNameForCommandLine: FqName = FqName("ik.SuperInline")
    private val IrFunction.needsInlining get() = this.isInline && !this.isExternal && this !is IrLazyFunction
    private var containerScope: ScopeWithIr? = null
    private var isInliningEnabled: Boolean = false
    private var inliningTriggered: Boolean = false

    private val postProcessingEvaluationStatements = mutableListOf<IrStatement>()

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        containerScope = createScope(container as IrSymbolOwner)
        irBody.accept(this, null)

        if (inliningTriggered) {
            irBody.transform(InliningPostProcessingTransformer(containerScope!!), null)

            when (irBody) {
                is IrBlockBody -> irBody.statements.addAll(0, postProcessingEvaluationStatements)
                else -> TODO("Not supported yet")
            }
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
            !isInliningEnabled ||
            expression !is IrCall ||
            callee is IrLazyFunction
        ) {
            return super.visitFunctionAccess(expression)
        }

        isInliningEnabled = true
        inliningTriggered = true

        expression.transformChildrenVoid()

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
            isInliningEnabled = false

            return inlined
        }

        when (val dispatchReceiver = expression.dispatchReceiver) {
            is IrReturnableBlock -> if (expression.isInlinableLambdaInvokeCall() && isInliningEnabled) {
                val dispatchTransformer = inliner.dispatchReceiverInliningTransformer

                return dispatchReceiver.apply {
                    transformChildren(dispatchTransformer, dispatchReceiver to expression)
                    flattenAndPatchReturnTargetSymbol()
                }
            }
        }

        when (val callSiteExtensionReceiver = expression.extensionReceiver) {
            is IrReturnableBlock -> if (expression.isInlinableExtensionLambdaCall() && isInliningEnabled) {
                val extensionTransformer = inliner.extensionReceiverInliningTransformer

                return callSiteExtensionReceiver.apply {
                    transformChildren(extensionTransformer, callSiteExtensionReceiver to expression)
                    flattenAndPatchReturnTargetSymbol()
                }
            }
        }

        return if (callee.needsInlining && isInliningEnabled)
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

        val extensionReceiverInliningTransformer = ReceiverInliningTransformer(isExtension = true)
        val dispatchReceiverInliningTransformer = ReceiverInliningTransformer(isExtension = false)

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

        fun inline() = inlineFunction(callSite, callee)

        private fun inlineFunction(
            callSite: IrFunctionAccessExpression,
            callee: IrFunction
        ): IrExpression {
            val copiedCallee = (copyIrElement.copy(callee) as IrFunction).apply { parent = callee.parent }
            val evaluationStatements = evaluateArguments(callSite, copiedCallee)
            val statements = (copiedCallee.body as IrBlockBody).statements

            val irReturnableBlockSymbol = IrReturnableBlockSymbolImpl()
            val endOffset = callee.endOffset
            val irBuilder = context.createIrBuilder(irReturnableBlockSymbol, endOffset, endOffset)
            val transformer = ParameterSubstitutor()

            statements.transform { it.transform(transformer, data = null) }

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

                        if (expression.returnTargetSymbol == copiedCallee.symbol) // return target is set to IrReturnableBlockSymbol
                            return irBuilder.irReturn(expression.value)

                        return expression
                    }
                })

                patchDeclarationParents(parent)

                destructureReturnableBlockIfSingleReturnStatement()
            }
        }

        //---------------------------------------------------------------------//

        private inner class ParameterSubstitutor : IrElementTransformerVoidWithContext() { //todo changed to ..withContext

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
                expression.transformChildrenVoid() //same as in SuperInlineLowering (transformer) - we are walking the IR tree depth-first

                when (val dispatchReceiver = expression.dispatchReceiver) {
                    is IrReturnableBlock ->
                        if (expression.isInlinableLambdaInvokeCall()) {

                            return dispatchReceiver.apply {
                                transformChildren(dispatchReceiverInliningTransformer, this to expression)
                                flattenAndPatchReturnTargetSymbol()
                            }
                        }
                }

                when (val callSiteExtensionReceiver = expression.extensionReceiver) {
                    is IrReturnableBlock ->
                        if (expression.isInlinableExtensionLambdaCall()) {
                            val transformer = Inliner(
                                expression,
                                expression.symbol.owner,
                                this@ParameterSubstitutor.currentScope ?: this@Inliner.currentScope,
                                parent,
                                context
                            ).extensionReceiverInliningTransformer

                            return callSiteExtensionReceiver.apply {
                                transformChildren(transformer, this to expression)
                                flattenAndPatchReturnTargetSymbol()
                            }
                        }
                }

                if (isLambdaCall(expression)) {
                    val functionArgument = when (val value = expression.dispatchReceiver) {
                        is IrGetValue ->
                            if ((value.symbol.owner as? IrValueParameter)?.isNoinline == true)
                                return expression
                            else
                                substituteMap[value.symbol.owner] ?: return expression
                        is IrFunctionExpression -> value
                        else -> TODO("Should be either IrGetValue or IrFunctionExpression")
                    }

                    if (functionArgument !is IrFunctionExpression)
                        return expression

                    // Inline the lambda. Lambda parameters will be substituted with lambda arguments.
                    val newExpression = inlineFunction(
                        expression.apply { transformValueArguments { it.destructureReturnableBlockIfSingleReturnStatement() } },
                        functionArgument.function
                    )

                    // Substitute lambda arguments with target function arguments.
                    return newExpression.transform(
                        this,
                        null
                    )
                }

                val callee = expression.symbol.owner

                return if (callee.needsInlining) {
                    Inliner(
                        expression,
                        callee,
                        this@ParameterSubstitutor.currentScope ?: this@Inliner.currentScope,
                        parent,
                        context
                    ).inline()
                } else
                    expression
            }

            //-----------------------------------------------------------------//

            override fun visitElement(element: IrElement) = element.accept(this, null)
        }

        private fun isLambdaCall(irCall: IrCall): Boolean {
            val callee = irCall.symbol.owner
            val dispatchReceiver = callee.dispatchReceiverParameter ?: return false
            assert(!dispatchReceiver.type.isKFunction())

            return (dispatchReceiver.type.isFunction() || dispatchReceiver.type.isSuspendFunction())
                    && callee.name == OperatorNameConventions.INVOKE
                    && (irCall.dispatchReceiver is IrGetValue
                    || irCall.dispatchReceiver is IrFunctionExpression) //case when the lambda argument was already substituted
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

        private fun evaluateArguments(callSite: IrFunctionAccessExpression, callee: IrFunction): List<IrStatement> {
            val arguments = buildParameterToArgument(callSite, callee)
            val evaluationStatements = mutableListOf<IrStatement>()
            val substitutor = ParameterSubstitutor()
            arguments.forEach { argument ->
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

        private inner class ReceiverInliningTransformer(val isExtension: Boolean) : IrElementTransformer<Pair<IrReturnableBlock, IrCall>> {

            override fun visitReturn(expression: IrReturn, data: Pair<IrReturnableBlock, IrCall>): IrExpression {
                val callSiteExtensionReceiver = data.first
                if (expression.returnTargetSymbol != callSiteExtensionReceiver.symbol)
                    return super.visitReturn(expression, data)

                val receiverArgument = expression.value.safeAs<IrFunctionExpression>()
                    ?: return super.visitReturn(
                        expression,
                        data
                    ) //todo remove cast to IrFunctionExpression? because ideally we want to process any argument regardless the type

                val callSite = data.second.apply { transformValueArguments { it.destructureReturnableBlockIfSingleReturnStatement() } }

                return if (isExtension)
                    inlineFunction(
                        callSite.apply { extensionReceiver = receiverArgument },
                        callSite.symbol.owner
                    )
                else
                    inlineFunction(callSite, receiverArgument.function)
            }
        }
    }

    private inner class InliningPostProcessingTransformer(val containerScope: ScopeWithIr) : IrElementTransformerVoid() {

        override fun visitVariable(declaration: IrVariable): IrStatement {
            declaration.transformChildrenVoid()

            if (declaration.initializer.isInlinedBlock()) {
                val tmpVar = containerScope.scope.createTemporaryVariableDeclaration(declaration.type, declaration.name.toString())
                val initializer = declaration.initializer as IrReturnableBlock

                initializer.transformChildren(object : IrElementTransformerVoid() {
                    override fun visitReturn(expression: IrReturn): IrExpression {
//                        expression.transformChildrenVoid() //theoretically we shouldn't face situations with nested returns with same returnSymbol
                        return if (expression.returnTargetSymbol == initializer.symbol)
                            IrSetValueImpl(
                                expression.startOffset,
                                expression.endOffset,
                                expression.value.type,
                                tmpVar.symbol,
                                expression.value,
                                null
                            )
                        else
                            expression
                    }
                }, null)

                postProcessingEvaluationStatements.add(0, tmpVar)

                val irBuilder = context.createIrBuilder(declaration.symbol, declaration.startOffset, declaration.endOffset)

                return irBuilder.irComposite(origin = SuperInlinedFunctionBodyOrigin("")) {
                    initializer.statements.forEach { +it }
                    +declaration.apply {
                        this.initializer = IrGetValueImpl(initializer.startOffset, initializer.endOffset, tmpVar.symbol, null)
                    }
                }
            }

            return declaration
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

    private fun IrReturnableBlock.isSingleReturnStatement() =
        statements.size == 1 && statements.last() is IrReturn

    private fun IrExpression.destructureReturnableBlockIfSingleReturnStatement() =
        when (this) {
            is IrReturnableBlock ->
                if (isSingleReturnStatement())
                    statements.last().safeAs<IrReturn>()?.value ?: this
                else
                    this
            else -> this
        }

    private fun IrFunctionAccessExpression.transformValueArguments(transformation: (IrExpression) -> IrExpression) {
        for (i in 0 until valueArgumentsCount) {
            val arg = getValueArgument(i) ?: continue
            putValueArgument(i, transformation(arg))
        }
    }

    private fun IrExpression?.isInlinedBlock() = this?.safeAs<IrReturnableBlock>()?.origin is SuperInlinedFunctionBodyOrigin

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