import { AbbreviationProvider } from "@leanprover/unicode-input";
import {
  Disposable,
  TextEditor,
  commands,
  languages,
  window,
  workspace,
} from "vscode";
import { AbbreviationHoverProvider } from "./AbbreviationHoverProvider";
import { QdtAbbreviationConfig } from "./AbbreviationConfig";
import { QdtAbbreviationRewriter } from "./AbbreviationRewriter";

export class AbbreviationFeature implements Disposable {
  private readonly disposables = new Array<Disposable>();
  private activeRewriter: QdtAbbreviationRewriter | undefined;

  private readonly config: QdtAbbreviationConfig;
  private readonly abbreviations: AbbreviationProvider;

  constructor() {
    this.config = new QdtAbbreviationConfig();
    this.abbreviations = new AbbreviationProvider(this.config);

    this.disposables.push(
      this.config,
      languages.registerHoverProvider(
        { language: "qdt" },
        new AbbreviationHoverProvider(this.config, this.abbreviations),
      ),
      commands.registerTextEditorCommand("qdt.input.convert", async () => {
        await this.activeRewriter?.replaceAllTrackedAbbreviations();
      }),
      window.onDidChangeActiveTextEditor((editor) =>
        this.changedActiveTextEditor(editor),
      ),
      workspace.onDidOpenTextDocument(async (doc) => {
        const activeEditor = window.activeTextEditor;
        if (activeEditor === undefined) return;
        if (activeEditor.document.uri.toString() !== doc.uri.toString()) return;
        if (
          this.activeRewriter === undefined &&
          this.isQdtEditor(activeEditor)
        ) {
          this.activeRewriter = new QdtAbbreviationRewriter(
            this.config,
            this.abbreviations,
            activeEditor,
          );
        } else if (
          this.activeRewriter !== undefined &&
          !this.isQdtEditor(activeEditor)
        ) {
          await this.disposeActiveRewriter();
        }
      }),
    );

    this.changedActiveTextEditor(window.activeTextEditor);
  }

  private isQdtEditor(editor: TextEditor): boolean {
    return languages.match({ language: "qdt" }, editor.document) > 0;
  }

  private async disposeActiveRewriter() {
    const rewriter = this.activeRewriter;
    this.activeRewriter = undefined;
    if (rewriter === undefined) return;
    await rewriter.replaceAllTrackedAbbreviations();
    rewriter.dispose();
  }

  private changedActiveTextEditor(editor: TextEditor | undefined) {
    void this.disposeActiveRewriter().then(() => {
      if (editor === undefined || !this.isQdtEditor(editor)) return;
      this.activeRewriter = new QdtAbbreviationRewriter(
        this.config,
        this.abbreviations,
        editor,
      );
    });
  }

  dispose(): void {
    for (const d of this.disposables) {
      d.dispose();
    }
    this.activeRewriter?.dispose();
  }
}
