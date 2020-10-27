import debugFactory from 'debug'
import { ancestor } from 'acorn-walk'
import { Node as AcornNode, parse } from 'acorn'
import { CallExpression, Program, Node, Class } from 'estree'
import { JSComponentInfo } from '../models/component-info'
import { location, isMemberExpression, isObjectExpression, isCallExpression, isIdentifier, getMemberAssignmentsTo, getPropertyFromObject, getPropertiesFromObject, getMembersFromClassDeclaration, isClass, getClassName, getStringValue, isExportsMemberExpression, isRequireSpecifier, findExportNames, isModuleExports, findESMImports, findScriptRequires } from '../utils/js-ast-util'
import { JSSanSourceFile } from '../models/san-source-file'
import { componentID, ComponentReference } from '../models/component-reference'
import { readFileSync } from 'fs'

const debug = debugFactory('ts-component-parser')
const DEFAULT_LOADER_CMP = 'SanSSRDefaultLoaderComponent'

type LocalName = string
type ImportName = string
type ExportName = string
type ImportSpecifier = string

/**
 * 把包含 San 组件定义的 JavaScript 源码，通过静态分析（AST），得到组件信息。
 */
export class JavaScriptSanParser {
    root: Program
    componentInfos: JSComponentInfo[] = []
    entryComponentInfo?: JSComponentInfo
    readonly fileContent: string

    private sanComponentIdentifier?: string
    private defineComponentIdentifier?: string
    private defaultExport?: string
    private imports: Map<LocalName, [ImportSpecifier, ImportName]> = new Map()
    private exports: Map<LocalName, ExportName> = new Map()
    private componentIDs: Map<Node | undefined, string> = new Map()
    private defaultPlaceholderComponent?: JSComponentInfo
    private id = 0

    constructor (
        private readonly filePath: string,
        fileContent?: string,
        sourceType: 'module' | 'script' = 'script'
    ) {
        this.fileContent = fileContent === undefined ? readFileSync(filePath, 'utf8') : fileContent
        this.root = parse(this.fileContent, { ecmaVersion: 2020, sourceType }) as any as Program
    }

    parse () {
        this.parseNames()
        this.parseComponents()
        this.wireChildComponents()
        return new JSSanSourceFile(this.filePath, this.fileContent, this.componentInfos, this.entryComponentInfo)
    }

    parseComponents (): [JSComponentInfo[], JSComponentInfo | undefined] {
        const parseComponentFromNode = (node: AcornNode, ancestors: AcornNode[]) => {
            const parent = ancestors[ancestors.length - 2] as Node
            if (!this.isComponent(node as Node)) return
            const component = this.parseComponentFromNode(node as Node, parent)
            if (component.className === this.defaultExport) {
                this.entryComponentInfo = component
            }
        }
        ancestor(this.root as any as AcornNode, {
            CallExpression: parseComponentFromNode,
            ClassExpression: parseComponentFromNode,
            ClassDeclaration: parseComponentFromNode
        })
        return [this.componentInfos, this.entryComponentInfo]
    }

    wireChildComponents () {
        for (const info of this.componentInfos) {
            for (const [key, value] of info.getComponentsDelcarations()) {
                info.childComponents.set(key, this.createChildComponentReference(value))
            }
        }
    }

    private createChildComponentReference (child: Node): ComponentReference {
        if (this.componentIDs.has(child)) {
            return { specifier: '.', id: this.componentIDs.get(child)! }
        }
        if (isIdentifier(child)) {
            if (this.imports.has(child.name)) {
                const [specifier, id] = this.imports.get(child.name)!
                return { specifier, id }
            }
            return { specifier: '.', id: child.name }
        }
        if (this.isCreateComponentLoaderCall(child)) {
            const options = child.arguments[0]
            const placeholder = isObjectExpression(options) && getPropertyFromObject(options, 'placeholder')

            // placeholder 是一个组件声明或组件的引用
            if (placeholder) return this.createChildComponentReference(placeholder)

            // placeholder 未定义，生成一个默认的组件
            const cmpt = this.getOrCreateDefaultLoaderComponent()
            return { specifier: '.', id: cmpt.id }
        }
        throw new Error(`${location(child)} cannot parse components`)
    }

    private parseComponentFromNode (node: Node, parent: Node) {
        // export default Component
        if (parent.type === 'ExportDefaultDeclaration') {
            return (this.entryComponentInfo = this.createComponent(node, undefined, true))
        }
        // module.exports = Component
        if (parent.type === 'AssignmentExpression' && isModuleExports(parent.left)) {
            return (this.entryComponentInfo = this.createComponent(node, undefined, true))
        }
        // exports.Foo = Component
        if (parent.type === 'AssignmentExpression' && isExportsMemberExpression(parent.left)) {
            return this.createComponent(node, getStringValue(parent.left['property']))
        }
        // const Foo = Component
        if (parent.type === 'VariableDeclarator') {
            return this.createComponent(node, parent.id['name'])
        }
        // Foo = Component
        if (parent.type === 'AssignmentExpression' && isIdentifier(parent.left)) {
            return this.createComponent(node, parent.left.name)
        }
        // { 'x-list': san.defineComponent() }
        if (parent.type === 'Property' && this.isComponent(parent.value)) {
            return this.createComponent(node)
        }
        return this.createComponent(node)
    }

    /**
     * 解析文件中出现的名字：找到重要的类名、方法名以及它们的来源
     */
    parseNames () {
        for (const [local, specifier, imported] of this.parseImportedNames()) {
            this.imports.set(local, [specifier, imported])
            if (imported === 'Component' && specifier === 'san') {
                this.sanComponentIdentifier = local
            }
            if (imported === 'defineComponent' && specifier === 'san') {
                this.defineComponentIdentifier = local
            }
        }
        for (const [local, exported] of findExportNames(this.root)) {
            if (exported === 'default') this.defaultExport = local
            this.exports.set(local, exported)
        }
    }

    * parseImportedNames (): Generator<[string, string, string]> {
        for (const entry of findESMImports(this.root)) yield entry
        for (const entry of findScriptRequires(this.root)) yield entry
    }

    createComponent (node: Node, name: string = getClassName(node), isDefault = false) {
        const properties = new Map(this.getPropertiesFromComponentDeclaration(node, name))
        const id = componentID(isDefault, (name
            ? (this.exports.get(name) || name)
            : ('SanSSRAnonymousComponent' + this.id++)
        ))
        this.componentIDs.set(node, id)
        const comp = new JSComponentInfo(id, name, properties, this.stringify(node))
        this.componentInfos.push(comp)
        return comp
    }

    private getOrCreateDefaultLoaderComponent (): JSComponentInfo {
        if (!this.defaultPlaceholderComponent) {
            this.defaultPlaceholderComponent = new JSComponentInfo(DEFAULT_LOADER_CMP, '', new Map(), 'function(){}')
            this.componentInfos.push(this.defaultPlaceholderComponent)
        }
        return this.defaultPlaceholderComponent
    }

    private * getPropertiesFromComponentDeclaration (node: Node, name: string) {
        if (this.isComponentClass(node)) yield * getMembersFromClassDeclaration(node as Class)
        else yield * getPropertiesFromObject(node['arguments'][0])
        yield * getMemberAssignmentsTo(this.root, name)
    }

    private isComponent (node: Node) {
        return this.isDefineComponentCall(node) || this.isComponentClass(node)
    }

    private isDefineComponentCall (node: Node): node is CallExpression {
        return isCallExpression(node) && this.isImportedFromSan(node.callee, 'defineComponent')
    }

    private isCreateComponentLoaderCall (node: Node): node is CallExpression {
        return isCallExpression(node) && this.isImportedFromSan(node.callee, 'createComponentLoader')
    }

    private isComponentClass (node: Node): node is Class {
        return isClass(node) && !!node.superClass && this.isImportedFromSan(node.superClass, 'Component')
    }

    private isImportedFromSan (expr: Node, sanExport: string): boolean {
        if (isIdentifier(expr)) return this.isImportedFrom(expr.name, 'san', sanExport)
        if (isMemberExpression(expr)) return this.isImportedFromSan(expr.object, 'default') && getStringValue(expr.property) === sanExport
        if (isCallExpression(expr)) return isRequireSpecifier(expr, 'san') && sanExport === 'default'
        return false
    }

    private isImportedFrom (localName: string, packageSpec: string, importedName: string) {
        if (!this.imports.has(localName)) return false

        const [spec, name] = this.imports.get(localName)!
        return spec === packageSpec && name === importedName
    }

    private stringify (node: Node) {
        return this.fileContent.slice(node['start'], node['end'])
    }
}
