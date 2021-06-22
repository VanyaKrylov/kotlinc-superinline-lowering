/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

@file:Suppress("DuplicatedCode")

package org.jetbrains.kotlin.backend.common.lower.inline

import org.jetbrains.kotlin.backend.common.*
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.UNDEFINED_OFFSET
import org.jetbrains.kotlin.ir.builders.*
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
import org.jetbrains.kotlin.ir.visitors.*
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.util.OperatorNameConventions
import org.jetbrains.kotlin.utils.addToStdlib.safeAs
import kotlin.math.exp


// TODO:
// 1) Add captured variables support in Inliner via isTopLevelCallSite checks
class SuperInlineLowering(val context: CommonBackendContext) : BodyLoweringPass, IrElementTransformerVoidWithContext() {
    private val superInlineAnnotationFqName: FqName = FqName("Script.SuperInline")
    private val superInlineAnnotationFqNameForCommandLine: FqName = FqName("ik.SuperInline") //todo add/remove ik.
    private val IrFunction.needsInlining get() = this.isInline && !this.isExternal && this !is IrLazyFunction
    private var containerScope: ScopeWithIr? = null
    private var inliningTriggered: Boolean = false

    private val postProcessingEvaluationStatements = mutableListOf<IrStatement>()
    private var capturedVariables = mutableListOf<IrVariable>()

    override fun lower(irBody: IrBody, container: IrDeclaration) {
        containerScope = createScope(container as IrSymbolOwner)
        irBody.accept(this, null)

        if (inliningTriggered) {
            irBody.safeAs<IrBlockBody>()?.statements?.addAll(0, capturedVariables) //todo cover cases with other IrBody subtypes
            irBody.transform(InliningPostProcessingTransformer(containerScope!!), null)

            when (irBody) {
                is IrBlockBody -> irBody.statements.addAll(capturedVariables.size, postProcessingEvaluationStatements)
                else -> TODO("Not supported yet")
            }
        }

        containerScope = null
        inliningTriggered = false
        postProcessingEvaluationStatements.clear()
        capturedVariables.clear()

        irBody.patchDeclarationParents(container as? IrDeclarationParent ?: container.parent)
    }

    //todo use visitCall() instead?
    override fun visitFunctionAccess(expression: IrFunctionAccessExpression): IrExpression {
        val callee = expression.symbol.owner

        if (!callee.hasAnnotation(superInlineAnnotationFqName) &&
            !callee.hasAnnotation(superInlineAnnotationFqNameForCommandLine) ||
            expression !is IrCall ||
            callee is IrLazyFunction
        ) {
            return super.visitFunctionAccess(expression)
        }

        inliningTriggered = true

        if (callee.hasAnnotation(superInlineAnnotationFqName) ||
            callee.hasAnnotation(superInlineAnnotationFqNameForCommandLine)
        ) {
            val parent = allScopes.map { it.irElement }.filterIsInstance<IrDeclarationParent>().lastOrNull()
                ?: allScopes.map { it.irElement }.filterIsInstance<IrDeclaration>().lastOrNull()?.parent
                ?: containerScope?.irElement as? IrDeclarationParent
                ?: (containerScope?.irElement as? IrDeclaration)?.parent

            val scope = currentScope ?: containerScope!!
            val inliner = Inliner(expression, callee, scope, parent, context, needsCapturing = false)
            val inlined = inliner.inline()

            return inlined
        }

        return expression
    }

    private inner class Inliner(
        val callSite: IrFunctionAccessExpression,
        val callee: IrFunction,
        val currentScope: ScopeWithIr,
        val parent: IrDeclarationParent?,
        val context: CommonBackendContext,
        val ignoreDispatchReceiver: Boolean = false,
        val needsCapturing: Boolean = true
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
            DeepCopyIrTreeWithSymbolsForInliner(typeArguments, parent, isJvmTarget = true)
        }

        val substituteMap = mutableMapOf<IrValueParameter, IrExpression>()

        fun inline() = inlineFunction(callSite, callee)

        fun inlineFunction(
            callSite: IrFunctionAccessExpression,
            callee: IrFunction
        ): IrExpression {
            val copiedCallee = (copyIrElement.copy(callee) as IrFunction).apply { parent = callee.parent }
            val movedFromArgumentsStatements = mutableListOf<IrStatement>()
            val evaluationStatements = evaluateArguments(callSite.prepareValueArguments(movedFromArgumentsStatements), copiedCallee)
            val statements = (copiedCallee.body as IrBlockBody).statements

            val transformer = BodyInliningTransformer()
            statements.transform { runInliningTransformerWithResetFlags(transformer, it) }
            statements.addAll(0, movedFromArgumentsStatements + evaluationStatements)

            val irReturnableBlockSymbol = IrReturnableBlockSymbolImpl()
            val endOffset = callee.endOffset
            val irBuilder = context.createIrBuilder(irReturnableBlockSymbol, endOffset, endOffset)

            return IrReturnableBlockImpl(
                startOffset = callSite.startOffset,
                endOffset = callSite.endOffset,
                type = callSite.type,
                symbol = irReturnableBlockSymbol,
                origin = SuperInlinedFunctionBodyOrigin(callee.symbol.owner.name.toString()),
                statements = statements,
                inlineFunctionSymbol = copiedCallee.symbol
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
                destructureIfIsOnlyReturnStatement()
            }
        }

        private inner class BodyInliningTransformer : InliningTransformer(this)

        private inner class ParameterToArgument(
            val parameter: IrValueParameter,
            val argumentExpression: IrExpression
        ) {
            val isInlinableLambdaArgument: Boolean
                get() = parameter.isSuperInlineParameter() &&
                        argumentExpression is IrFunctionExpression //todo add support for FunctionReferences

            val isImmutableVariableLoad: Boolean
                get() = argumentExpression.let { argument ->
                    argument is IrGetValue && !argument.symbol.owner.let { it is IrVariable && it.isVar } || argument is IrConst<*>
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
            val substitutor = BodyInliningTransformer()
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
                val callReceiverBlock = data.first
                if (expression.returnTargetSymbol != callReceiverBlock.symbol)
                    return super.visitReturn(expression, data)

                val receiverArgument = expression.value
                val callSite = data.second

                return if (isExtension)
                    inlineFunction(
                        callSite.apply { extensionReceiver = receiverArgument },
                        callSite.symbol.owner
                    )
                else
                    inlineFunction(
                        callSite,
                        receiverArgument.safeAs<IrFunctionExpression>()?.function
                            ?: return super.visitReturn(expression, data)
                    )
            }
        }

        private fun runInliningTransformerWithResetFlags(transformer: InliningTransformer, statement: IrStatement) =
            statement.transform(transformer.apply {
                this.isFirstInvocation = true
                this.isInliningAllowed = true
            }, null)
    }

    //parentInliner !=null for body inlining and ==null for arguments inlining (when IrCall is passed as an argument)
    private open inner class InliningTransformer(var parentInliner: Inliner? = null) : IrElementTransformerVoidWithContext() {
        var isFirstInvocation: Boolean = true
        var isInliningAllowed: Boolean = true

        override fun visitGetValue(expression: IrGetValue): IrExpression {
            if (parentInliner == null) {
                return super.visitGetValue(expression)
            } else {
                with(parentInliner!!) {
                    val newExpression = super.visitGetValue(expression) as IrGetValue
                    val argument = substituteMap[newExpression.symbol.owner] ?: return newExpression

                    argument.transformChildrenVoid(this@InliningTransformer) // Default argument can contain subjects for substitution.

                    return if (argument is IrGetValueWithoutLocation)
                        argument.withLocation(newExpression.startOffset, newExpression.endOffset)
                    else (copyIrElement.copy(argument) as IrExpression)
                }
            }
        }

        override fun visitCall(expression: IrCall): IrExpression {
            val needsCapturing = !isFirstInvocation || parentInliner?.needsCapturing ?: true
            isFirstInvocation = false

            expression.transformChildrenVoid() //we are walking the IR tree depth-first

            val callee = expression.symbol.owner
            val parent = allScopes.map { it.irElement }.filterIsInstance<IrDeclarationParent>().lastOrNull()
                ?: allScopes.map { it.irElement }.filterIsInstance<IrDeclaration>().lastOrNull()?.parent
                ?: containerScope?.irElement as? IrDeclarationParent
                ?: (containerScope?.irElement as? IrDeclaration)?.parent

            val inliner = Inliner(
                expression,
                callee,
                currentScope ?: containerScope!!,
                parent,
                context,
                needsCapturing = needsCapturing
            )

            if (expression.isInlinableLambdaInvokeCall()) {

                val functionArgument = when (val dispatchReceiver = expression.dispatchReceiver) {

                    is IrReturnableBlock -> {
                        if (!isInliningAllowed)
                            return expression
                        val transformer = (parentInliner ?: inliner).dispatchReceiverInliningTransformer

                        return dispatchReceiver.postProcessReceiverInliningResult(transformer, dispatchReceiver to expression)
                    }

                    is IrGetValue ->
                        if ((dispatchReceiver.symbol.owner as? IrValueParameter)?.isNoinline == true)
                            return expression
                        else
                            inliner.substituteMap[dispatchReceiver.symbol.owner] ?: return expression

                    is IrFunctionExpression -> dispatchReceiver

                    else -> TODO("Should be either IrGetValue or IrFunctionExpression")
                }

                if (functionArgument !is IrFunctionExpression)
                    return expression

                val newExpression = inliner.inlineFunction(expression, functionArgument.function)

                return if (parentInliner == null)
                    newExpression
                else
                    newExpression.transform(this, null)
            }

            when (val callSiteExtensionReceiver = expression.extensionReceiver) {
                is IrReturnableBlock ->
                    if (expression.isInlinableExtensionLambdaCall() && isInliningAllowed) {
                        val transformer = inliner.extensionReceiverInliningTransformer

                        return callSiteExtensionReceiver.postProcessReceiverInliningResult(
                            transformer,
                            callSiteExtensionReceiver to expression
                        )
                    }
            }

            return if (callee.needsInlining && isInliningAllowed)
                inliner.inline()
            else
                expression
        }

        //calls inside lambdas should only be processed when the lambda is invoked
        override fun visitFunctionExpression(expression: IrFunctionExpression): IrExpression {
            val tmp = isInliningAllowed
            isInliningAllowed = false
            val res = super.visitFunctionExpression(expression)
            isInliningAllowed = tmp

            return res
        }

        override fun visitElement(element: IrElement) = element.accept(this, null)

        private fun IrReturnableBlock.postProcessReceiverInliningResult(
            transformer: IrElementTransformer<Pair<IrReturnableBlock, IrCall>>,
            data: Pair<IrReturnableBlock, IrCall>
        ) = this.apply {
            val movedStatements = mutableListOf<IrStatement>()
            transformChildren(transformer, data.apply { this.second.destructureSingleReturnBlockArguments(movedStatements) })
            statements.addAll(0, movedStatements)
            flattenAndPatchReturnTargetSymbol()
        }
    }

    //-----------------------------------------------------------------//

    private inner class InliningPostProcessingTransformer(val containerScope: ScopeWithIr) : IrElementTransformerVoid() {

        override fun visitVariable(declaration: IrVariable): IrStatement {
            declaration.transformChildrenVoid()

            if (isInlinedInitializer(declaration.initializer)) {
                val tmpVar = containerScope.scope.createTemporaryVariableDeclaration(declaration.type, declaration.name.toString())
                val initializer = declaration.initializer.safeAs()
                    ?: (declaration.initializer as IrBlock).statements.last() as IrReturnableBlock

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

            val initializer = declaration.initializer.safeAs<IrCall>() ?: return declaration
            val dispatchReceiver = initializer.dispatchReceiver.safeAs<IrReturnableBlock>() ?: return declaration

            if (!dispatchReceiver.isInlinedBlock())
                return declaration

            val tmpVar = containerScope.scope.createTemporaryVariableDeclaration(dispatchReceiver.type, declaration.name.toString())

            dispatchReceiver.transformChildren(object : IrElementTransformerVoid() {
                override fun visitReturn(expression: IrReturn): IrExpression {
//                        expression.transformChildrenVoid() //theoretically we shouldn't face situations with nested returns with same returnSymbol
                    return if (expression.returnTargetSymbol == dispatchReceiver.symbol)
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
            initializer.dispatchReceiver = IrGetValueImpl(dispatchReceiver.startOffset, dispatchReceiver.endOffset, tmpVar.symbol, null)

            val irBuilder = context.createIrBuilder(declaration.symbol, declaration.startOffset, declaration.endOffset)

            return irBuilder.irComposite(origin = SuperInlinedFunctionBodyOrigin("")) {
                dispatchReceiver.statements.forEach { +it }
                +declaration
            }
        }

        override fun visitBlock(expression: IrBlock): IrExpression {
            expression.transformChildrenVoid()

            val firstStatement = expression.statements[0].safeAs<IrCompositeImpl>() ?: expression
            if (firstStatement.origin !is SuperInlinedFunctionBodyOrigin)
                return expression

            val variableDeclaration = firstStatement.statements.last().safeAs<IrVariable>() ?: return expression
            expression.statements.apply {
                removeAt(0)
                add(0, variableDeclaration)
            }

            return IrCompositeImpl(
                expression.startOffset,
                expression.endOffset,
                expression.type,
                expression.origin,
                firstStatement.statements.apply {
                    removeLast()
                    add(expression)
                }
            )
        }

        override fun visitSetValue(expression: IrSetValue): IrExpression {
            expression.transformChildrenVoid()

            if (!expression.value.isInlinedBlock())
                return expression

            val irReturnableBlock = expression.value.safeAs<IrReturnableBlock>() ?: return expression

            val tmpVar = containerScope.scope.createTemporaryVariableDeclaration(
                expression.value.type,
                irReturnableBlock.origin?.safeAs<SuperInlinedFunctionBodyOrigin>()?.calleeName
            )

            postProcessingEvaluationStatements.add(0, tmpVar)

            irReturnableBlock.transformChildren(object : IrElementTransformerVoid() {
                override fun visitReturn(expression: IrReturn): IrExpression {
                    return if (expression.returnTargetSymbol == irReturnableBlock.symbol)
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
            expression.value = IrGetValueImpl(irReturnableBlock.startOffset, irReturnableBlock.endOffset, tmpVar.symbol, null)

            return IrCompositeImpl(
                expression.startOffset,
                expression.endOffset,
                expression.type,
                expression.origin,
                irReturnableBlock.statements.apply { add(expression) }
            )
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
                        .also { this@flattenAndPatchReturnTargetSymbol.type = expression.value.type }
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

    private fun MutableList<IrStatement>.filterUnitStubs() =
        this.filterNot { it.safeAs<IrGetObjectValue>()?.type?.isUnit() ?: false }

    private fun IrExpression.destructureIfIsOnlyReturnStatement() =
        when (this) {
            //unit stubs come from captured variables
            is IrReturnableBlock -> statements.filterUnitStubs().singleOrNull()?.safeAs<IrReturn>()?.value ?: this
            else -> this
        }

    private fun IrReturnableBlock.isSingleReturnBlock(): Boolean {
        var count = 0

        this.acceptChildrenVoid(object : IrElementVisitorVoid {
            override fun visitElement(element: IrElement) {
                if (count < 1)
                    element.acceptChildren(this, null)
            }

            override fun visitReturn(expression: IrReturn) {
                if (expression.returnTargetSymbol == this@isSingleReturnBlock.symbol)
                    count++
                super.visitReturn(expression)
            }
        })

        return count == 1
    }

    private fun IrCall.destructureSingleReturnBlockArguments(movedStatements: MutableList<IrStatement>) = this.apply {
        transformValueArguments {
            it.transformSingleReturnBlock(movedStatements)
        }
    }

    private fun IrExpression.transformSingleReturnBlock(movedStatements: MutableList<IrStatement>) =
        this.safeAs<IrReturnableBlock>()?.apply {
            val returnStatement = statements.last().safeAs<IrReturn>()
            if (isSingleReturnBlock() && returnStatement?.returnTargetSymbol == this.symbol) {
                movedStatements.addAll(statements.filterUnitStubs().dropLast(1))
                statements.apply {
                    clear()
                    add(returnStatement)
                }
            }
        } ?: this

    private fun IrFunctionAccessExpression.prepareValueArguments(movedStatements: MutableList<IrStatement>) = this.apply {
        transformValueArguments {
            it.transformSingleReturnBlock(movedStatements)
            it.destructureIfIsOnlyReturnStatement()
        }
    }

    private fun IrFunctionAccessExpression.transformValueArguments(transformation: (IrExpression) -> IrExpression) {
        for (i in 0 until valueArgumentsCount) {
            val arg = getValueArgument(i) ?: continue
            putValueArgument(i, transformation(arg))
        }
    }

    private fun IrStatement?.isInlinedBlock() = this?.safeAs<IrReturnableBlock>()?.origin is SuperInlinedFunctionBodyOrigin

    private fun isInlinedInitializer(irStatement: IrStatement?) =
        irStatement?.isInlinedBlock() == true || irStatement?.safeAs<IrBlock>()?.statements?.singleOrNull()?.isInlinedBlock() ?: false

    private fun IrValueParameter.isSuperInlineParameter(type: IrType = this.type) =
        !isNoinline && !type.isNullable() && (type.isFunction() || type.isSuspendFunction())

    private fun IrFunctionAccessExpression.isInlinableLambdaInvokeCall(): Boolean {
        val callee = this.symbol.owner
        val dispatchReceiverParameter = callee.dispatchReceiverParameter ?: return false
        assert(!dispatchReceiverParameter.type.isKFunction())

        return this is IrCall
                && callee.name == OperatorNameConventions.INVOKE
                && dispatchReceiverParameter.type.isFunction()
                && (this.dispatchReceiver is IrGetValue
                || this.dispatchReceiver is IrFunctionExpression
                || this.dispatchReceiver.safeAs<IrReturnableBlock>()?.origin is SuperInlinedFunctionBodyOrigin)
    }

    private fun IrFunctionAccessExpression.isInlinableExtensionLambdaCall(): Boolean {
        val callee = this.symbol.owner
        val extensionReceiverParameter = callee.extensionReceiverParameter ?: return false
        val extensionReceiverOrigin = this.extensionReceiver.safeAs<IrReturnableBlock>()?.origin ?: return false

        return this is IrCall
                && callee.isInline
                && extensionReceiverParameter.type.isFunction()
                && extensionReceiverOrigin is SuperInlinedFunctionBodyOrigin
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

fun IrReturn.withReturnTargetSymbol(returnTargetSymbol: IrReturnTargetSymbol) =
    IrReturnImpl(startOffset, endOffset, type, returnTargetSymbol, value)
