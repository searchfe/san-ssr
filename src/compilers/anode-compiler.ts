/**
 * 把 ANode 编译成 SSR 代码块
 *
 * 每个组件的 template 对应于一个根 ANode。从它出发递归地编译整个 template。
 * 这里要做的就是区分 ANode 类型，做不同的编译。
 */
import assert from 'assert'
import { camelCase } from 'lodash'
import { ANode, AIfNode, AForNode, ASlotNode, ATemplateNode, AFragmentNode, ATextNode } from 'san'
import { ComponentInfo } from '../models/component-info'
import { ElementCompiler } from './element-compiler'
import { getANodePropByName } from '../ast/san-ast-util'
import * as TypeGuards from '../ast/san-ast-type-guards'
import { IDGenerator } from '../utils/id-generator'
import { JSONStringify, RegexpReplace, Statement, SlotRendererDefinition, ElseIf, Else, MapAssign, Foreach, If, MapLiteral, ComponentRendererReference, FunctionCall, SlotRenderCall, Expression, GetRootCtxCall, ComponentReferenceLiteral } from '../ast/renderer-ast-dfn'
import { CTX_DATA, createHTMLExpressionAppend, createHTMLLiteralAppend, L, I, ASSIGN, STATEMENT, UNARY, DEF, BINARY, RETURN } from '../ast/renderer-ast-util'
import { sanExpr, OutputType } from '../compilers/san-expr-compiler'

/**
 * ANode 编译
 *
 * 负责单个 ComponentClass 的编译，每个 ANodeCompiler 对应于一个 ComponentInfo。
 */
export class ANodeCompiler<T extends 'none' | 'typed'> {
    private elementCompiler: ElementCompiler
    private inScript = false

    /**
     * @param componentInfo 要被编译的节点所在组件的信息
     * @param ssrOnly san-ssr 当做模板引擎来使用（产出 HTML 更简单，但无法反解）
     * @param id 抗冲突变量名产生器
     */
    constructor (
        private componentInfo: ComponentInfo,
        private ssrOnly: boolean,
        private id: IDGenerator
    ) {
        this.elementCompiler = new ElementCompiler(this, this.id)
    }

    compile (aNode: ANode, isRootElement: boolean): Generator<Statement> {
        if (TypeGuards.isATextNode(aNode)) return this.compileText(aNode)
        if (TypeGuards.isAIfNode(aNode)) return this.compileIf(aNode)
        if (TypeGuards.isAForNode(aNode)) return this.compileFor(aNode)
        if (TypeGuards.isASlotNode(aNode)) return this.compileSlot(aNode)
        if (TypeGuards.isATemplateNode(aNode)) return this.compileTemplate(aNode)
        if (TypeGuards.isAFragmentNode(aNode)) {
            if (isRootElement) {
                console.warn('根元素为 <fragment> 不支持反解')
            }
            return this.compileFragment(aNode)
        }

        const childComponentReference = this.generateRef(aNode)
        if (childComponentReference) {
            return this.compileComponent(aNode, childComponentReference, isRootElement)
        }
        return this.compileElement(aNode, isRootElement)
    }

    private generateRef (aNode: ANode) {
        if (aNode.directives.is) {
            const refs = BINARY(I('ctx'), '.', I('refs'))
            return BINARY(refs, '[]', sanExpr(aNode.directives.is.value))
        }
        if (this.componentInfo.childComponents.has(aNode.tagName)) {
            return new ComponentReferenceLiteral(this.componentInfo.childComponents.get(aNode.tagName)!)
        }
    }

    private * compileText (aNode: ATextNode): Generator<Statement> {
        const shouldEmitComment = TypeGuards.isExprTextNode(aNode.textExpr) && aNode.textExpr.original && !this.ssrOnly && !this.inScript
        const outputType = this.inScript ? OutputType.HTML : OutputType.ESCAPE_HTML
        if (shouldEmitComment) yield createHTMLLiteralAppend('<!--s-text-->')
        yield createHTMLExpressionAppend(sanExpr(aNode.textExpr, outputType))
        if (shouldEmitComment) yield createHTMLLiteralAppend('<!--/s-text-->')
    }

    private * compileTemplate (aNode: ATemplateNode) {
        // if、for 等区块 wrap，只渲染内容。
        // 注意：<template> 为组件根节点时，tagName=null, isATemplateNode=false
        yield * this.elementCompiler.inner(aNode)
    }

    private * compileFragment (aNode: AFragmentNode) {
        if (TypeGuards.isATextNode(aNode.children[0]) && !this.ssrOnly && !this.inScript) {
            yield createHTMLLiteralAppend('<!--s-frag-->')
        }
        yield * this.elementCompiler.inner(aNode)
        if (TypeGuards.isATextNode(aNode.children[aNode.children.length - 1]) && !this.ssrOnly && !this.inScript) {
            yield createHTMLLiteralAppend('<!--/s-frag-->')
        }
    }

    private * compileIf (aNode: AIfNode): Generator<Statement> {
        const ifDirective = aNode.directives.if
        const aNodeWithoutIf = Object.assign({}, aNode)

        // 防止重新进入 compileIf：删掉 if 指令，再递归进入当前 aNode
        delete aNodeWithoutIf.directives.if

        yield new If(sanExpr(ifDirective.value), this.compile(aNodeWithoutIf, false))

        for (const elseANode of aNode.elses || []) {
            const elifDirective = elseANode.directives.elif
            const body = this.compile(elseANode, false)
            yield elifDirective ? new ElseIf(sanExpr(elifDirective.value), body) : new Else(body)
        }
    }

    private * compileFor (aNode: AForNode): Generator<Statement> {
        const { id } = this
        const forElementANode = {
            children: aNode.children,
            props: aNode.props,
            events: aNode.events,
            tagName: aNode.tagName,
            directives: { ...aNode.directives }
        }
        // 防止重新进入 compileFor
        delete forElementANode.directives.for

        const { item, index, value } = aNode.directives.for
        const key = I(id.next('key'))
        const val = I(id.next('val'))
        const list = id.next('list')

        yield DEF(list, sanExpr(value))
        yield new Foreach(key, val, I(list), [
            ...index ? [ASSIGN(BINARY(CTX_DATA, '[]', L(index)), key)] : [],
            ASSIGN(BINARY(CTX_DATA, '[]', L(item!)), val),
            ...this.compile(forElementANode, false)
        ])
    }

    private * compileSlot (aNode: ASlotNode): Generator<Statement> {
        const { id } = this
        assert(!this.inScript, '<slot> is not allowed inside <script>')

        const defaultRender = I(id.next('defaultRender'))
        yield DEF(defaultRender.name, this.compileSlotRenderer(aNode.children))

        const slotData = I(id.next('slotData'))
        yield DEF(slotData.name, new MapLiteral([]))
        if (aNode.directives.bind) {
            yield STATEMENT(new MapAssign(slotData, [sanExpr(aNode.directives.bind.value)]))
        }

        const props = aNode.vars || []
        if (props.length) {
            yield STATEMENT(new MapAssign(
                slotData,
                [new MapLiteral(props.map(prop => [L(prop.name), sanExpr(prop.expr)]))]
            ))
        }

        const slotName = I(id.next('slotName'))
        const render = I(id.next('render'))

        const nameProp = getANodePropByName(aNode, 'name')
        yield DEF(slotName.name, nameProp ? sanExpr(nameProp.expr) : L(''))
        yield (DEF(render.name, BINARY(
            BINARY(BINARY(I('ctx'), '.', I('slots')), '[]', slotName),
            '||',
            defaultRender
        )))
        yield createHTMLExpressionAppend(new SlotRenderCall(render, [I('parentCtx'), slotData]))
    }

    private * compileElement (aNode: ANode, isRootElement: boolean): Generator<Statement> {
        yield * this.elementCompiler.tagStart(aNode)
        if (aNode.tagName === 'script') this.inScript = true
        if (isRootElement && !this.ssrOnly && !this.inScript) {
            yield new If(UNARY('!', I('noDataOutput')), this.createDataComment())
        }

        yield * this.elementCompiler.inner(aNode)
        this.inScript = false
        yield * this.elementCompiler.tagEnd(aNode)
    }

    private createDataComment () {
        const dataExpr = BINARY(new GetRootCtxCall([I('ctx')]), '.', I('data'))
        return [
            createHTMLLiteralAppend('<!--s-data:'),
            createHTMLExpressionAppend(new RegexpReplace(new JSONStringify(dataExpr), '(?<=-)-', L('\\-'))),
            createHTMLLiteralAppend('-->')
        ]
    }

    private * compileComponent (aNode: ANode, ref: Expression, isRootElement: boolean) {
        const defaultSlotContents: ANode[] = []
        const namedSlotContents = new Map()

        assert(!this.inScript, 'component reference is not allowed inside <script>')

        for (const child of aNode.children!) { // nodes without children (like pATextNode) has been taken over by other methods
            const slotBind = !child.textExpr && getANodePropByName(child, 'slot')
            if (slotBind) {
                const slotName = slotBind.expr.value
                if (!namedSlotContents.has(slotName)) {
                    namedSlotContents.set(slotName, { children: [], prop: slotBind })
                }
                namedSlotContents.get(slotName).children.push(child)
            } else {
                defaultSlotContents.push(child)
            }
        }

        const childSlots = I(this.id.next('childSlots'))
        yield DEF(childSlots.name, new MapLiteral([]))
        if (defaultSlotContents.length) {
            yield ASSIGN(
                BINARY(childSlots, '[]', L('')),
                this.compileSlotRenderer(defaultSlotContents)
            )
        }

        for (const sourceSlotCode of namedSlotContents.values()) {
            yield ASSIGN(
                BINARY(childSlots, '[]', sanExpr(sourceSlotCode.prop.expr)),
                this.compileSlotRenderer(sourceSlotCode.children)
            )
        }

        const ndo = isRootElement ? I('noDataOutput') : L(true)

        const childRenderCall = new FunctionCall(
            new ComponentRendererReference(ref),
            [this.childRenderData(aNode), ndo, I('parentCtx'), L(aNode.tagName), childSlots]
        )
        yield createHTMLExpressionAppend(childRenderCall)
    }

    private compileSlotRenderer (content: ANode[]) {
        const args = [DEF('parentCtx'), DEF('data')]
        const body: Statement[] = []
        if (content.length) {
            body.push(DEF('html', L('')))

            const compData = this.id.next('compData')
            body.push(DEF(compData, CTX_DATA))
            body.push(STATEMENT(new MapAssign(CTX_DATA, [I('data')])))

            for (const child of content) body.push(...this.compile(child, false))

            body.push(ASSIGN(CTX_DATA, I(compData)))
            body.push(RETURN(I('html')))
        } else {
            body.push(RETURN(L('')))
        }
        return new SlotRendererDefinition('', args, body)
    }

    private childRenderData (aNode: ANode) {
        const propData = new MapLiteral(
            aNode.props.map(prop => [L(camelCase(prop.name)), sanExpr(prop.expr)])
        )
        const bindDirective = aNode.directives.bind
        return bindDirective ? new MapAssign(sanExpr(bindDirective.value), [propData]) : propData
    }
}
