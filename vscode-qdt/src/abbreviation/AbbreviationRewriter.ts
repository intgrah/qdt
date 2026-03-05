import {
  AbbreviationConfig,
  AbbreviationProvider,
  AbbreviationRewriter,
  AbbreviationTextSource,
  Change,
  Range,
  SelectionMoveMode,
} from "@leanprover/unicode-input";
import {
  Disposable,
  Range as LineColRange,
  Selection,
  TextDocument,
  TextEditor,
  commands,
  window,
  workspace,
} from "vscode";

export class QdtAbbreviationRewriter implements AbbreviationTextSource {
  private readonly disposables = new Array<Disposable>();
  private readonly rewriter: AbbreviationRewriter;

  private readonly decorationType = window.createTextEditorDecorationType({
    textDecoration: "underline",
  });

  constructor(
    readonly config: AbbreviationConfig,
    readonly abbreviationProvider: AbbreviationProvider,
    private readonly textEditor: TextEditor,
  ) {
    this.rewriter = new AbbreviationRewriter(
      config,
      abbreviationProvider,
      this,
    );

    this.disposables.push(this.decorationType);

    this.disposables.push(
      workspace.onDidChangeTextDocument(async (e) => {
        if (e.document !== this.textEditor.document) {
          return;
        }

        const changes: Change[] = e.contentChanges.map((changeEvent) => ({
          range: new Range(changeEvent.rangeOffset, changeEvent.rangeLength),
          newText: changeEvent.text,
        }));
        this.rewriter.changeInput(changes);
        await this.rewriter.triggerAbbreviationReplacement();

        this.updateState();
      }),
    );
    this.disposables.push(
      window.onDidChangeTextEditorSelection(async (e) => {
        if (e.textEditor.document !== this.textEditor.document) {
          return;
        }

        const selections = e.selections.map((s) =>
          fromVsCodeRange(s, e.textEditor.document),
        );
        await this.rewriter.changeSelections(selections);
        this.updateState();
      }),
    );
  }

  selectionMoveMode(): SelectionMoveMode {
    return {
      kind: "OnlyMoveCursorSelections",
      updateUnchangedSelections: false,
    };
  }

  collectSelections(): Range[] {
    return this.textEditor.selections.map((s) =>
      fromVsCodeRange(s, this.textEditor.document),
    );
  }

  setSelections(selections: Range[]): void {
    this.textEditor.selections = selections.map((s) => {
      const vr = toVsCodeRange(s, this.textEditor.document);
      return new Selection(vr.start, vr.end);
    });
  }

  async replaceAbbreviations(changes: Change[]): Promise<boolean> {
    let ok = false;
    let retries = 0;
    try {
      while (!ok && retries < 10) {
        ok = await this.textEditor.edit((builder) => {
          for (const c of changes) {
            builder.replace(
              toVsCodeRange(c.range, this.textEditor.document),
              c.newText,
            );
          }
        });
        retries++;
      }
    } catch (e) {
      if (
        !(e instanceof Error) ||
        e.message !== "TextEditor#edit not possible on closed editors"
      ) {
        console.error("QDT: Error while replacing abbreviation: " + e);
      }
    }
    return ok;
  }

  async replaceAllTrackedAbbreviations() {
    await this.rewriter.replaceAllTrackedAbbreviations();
    this.updateState();
  }

  private updateState() {
    const trackedAbbreviations = this.rewriter.getTrackedAbbreviations();

    this.textEditor.setDecorations(
      this.decorationType,
      [...trackedAbbreviations].map((a) =>
        toVsCodeRange(a.range, this.textEditor.document),
      ),
    );

    void commands.executeCommand(
      "setContext",
      "qdt.input.isActive",
      trackedAbbreviations.size > 0,
    );
  }

  dispose(): void {
    for (const d of this.disposables) {
      d.dispose();
    }
  }
}

function fromVsCodeRange(range: LineColRange, doc: TextDocument): Range {
  const start = doc.offsetAt(range.start);
  const end = doc.offsetAt(range.end);
  return new Range(start, end - start);
}

function toVsCodeRange(range: Range, doc: TextDocument): LineColRange {
  const start = doc.positionAt(range.offset);
  const end = doc.positionAt(range.offsetEnd + 1);
  return new LineColRange(start, end);
}
