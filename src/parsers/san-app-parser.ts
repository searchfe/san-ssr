import { getComponentClassIdentifier, isChildClassOf } from '../utils/ast-util'
import { ComponentClassFinder } from './component-class-finder'
import { CommonJS } from '../loaders/common-js'
import { ts2js } from '../target-js/compilers/ts2js'
import { normalizeComponentClass } from './normalize-component'
import { SanSourceFile } from '../models/san-sourcefile'
import { Project, SourceFile, ClassDeclaration } from 'ts-morph'
import { getDefaultConfigPath } from './tsconfig'
import { getDependenciesRecursively } from './dependency-resolver'
import { SanApp } from '../models/san-app'
import { SourceFileType, getSourceFileTypeOrThrow } from '../models/source-file-type'
import debugFactory from 'debug'

const debug = debugFactory('component-parser')

export class SanAppParser {
    private root: string
    private id: number = 0
    public project: Project

    constructor (project: Project) {
        this.project = project
    }

    static createUsingTsconfig (tsConfigFilePath: string) {
        return new SanAppParser(new Project({ tsConfigFilePath }))
    }

    static createUsingDefaultTypeScriptConfig () {
        return SanAppParser.createUsingTsconfig(getDefaultConfigPath())
    }

    public parseSanApp (entryFilePath: string): SanApp {
        debug('parsComponent', entryFilePath)
        const entrySourceFile = getSourceFileTypeOrThrow(entryFilePath) === SourceFileType.js
            ? SanSourceFile.createFromJSFilePath(entryFilePath)
            : this.parseSanSourceFile(this.project.getSourceFileOrThrow(entryFilePath))

        const projectFiles: Map<string, SanSourceFile> = new Map([[entryFilePath, entrySourceFile]])
        if (entrySourceFile.fileType === SourceFileType.ts) {
            const sourceFiles = getDependenciesRecursively(entrySourceFile.tsSourceFile)

            for (const [path, file] of sourceFiles) {
                projectFiles.set(path, this.parseSanSourceFile(file))
            }
        }

        const entryClass = this.evaluateFile(entrySourceFile, projectFiles)
        const componentClasses = new ComponentClassFinder(entryClass).find()

        if (entrySourceFile.fileType === SourceFileType.js) {
            for (let i = 0; i < componentClasses.length; i++) {
                const componentClass = componentClasses[i]
                componentClass.sanssrCid = i
            }
        }
        return new SanApp(entrySourceFile, projectFiles, componentClasses)
    }

    private evaluateFile (sourceFile: SanSourceFile, projectFiles: Map<string, SanSourceFile>) {
        if (sourceFile.fileType === SourceFileType.js) {
            return new CommonJS().require(sourceFile.getFilePath())
        }
        const commonJS = new CommonJS(filepath => {
            if (!projectFiles.has(filepath)) return null
            const sourceFile = projectFiles.get(filepath)
            return ts2js(sourceFile.tsSourceFile)
        })
        return commonJS.require(sourceFile.getFilePath()).default
    }

    private parseSanSourceFile (sourceFile: SourceFile) {
        debug('parseSanSourceFile', sourceFile.getFilePath())
        const componentClassIdentifier = getComponentClassIdentifier(sourceFile)
        const sanSourceFile = SanSourceFile.createFromTSSourceFile(sourceFile, componentClassIdentifier)

        if (!componentClassIdentifier) return sanSourceFile
        debug('san identifier', componentClassIdentifier)

        for (const clazz of sourceFile.getClasses()) {
            if (!isChildClassOf(clazz, componentClassIdentifier)) continue
            normalizeComponentClass(clazz)
            this.setComponentID(sanSourceFile, clazz)
        }
        return sanSourceFile
    }

    public setComponentID (sourceFile: SanSourceFile, clazz: ClassDeclaration) {
        const decl = clazz.addProperty({
            isStatic: true,
            name: 'sanssrCid',
            type: 'number',
            initializer: String(this.id)
        })
        sourceFile.fakeProperties.push(decl)
        sourceFile.componentClassDeclarations.set(this.id++, clazz)
    }
}