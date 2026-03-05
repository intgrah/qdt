import {
  AbbreviationConfig,
  SymbolsByAbbreviation,
} from "@leanprover/unicode-input";
import { Disposable, workspace } from "vscode";

export class QdtAbbreviationConfig implements AbbreviationConfig, Disposable {
  abbreviationCharacter: string = "\\";
  customTranslations: SymbolsByAbbreviation = {};
  eagerReplacementEnabled: boolean = true;

  private subscriptions: Disposable[] = [];

  constructor() {
    this.reloadConfig();
    this.subscriptions.push(
      workspace.onDidChangeConfiguration((e) => {
        if (e.affectsConfiguration("qdt.input")) {
          this.reloadConfig();
        }
      }),
    );
  }

  private reloadConfig() {
    this.abbreviationCharacter = workspace
      .getConfiguration("qdt.input")
      .get("leader", "\\");
    this.customTranslations = workspace
      .getConfiguration("qdt.input")
      .get("customTranslations", {});
    this.eagerReplacementEnabled = workspace
      .getConfiguration("qdt.input")
      .get("eagerReplacementEnabled", true);
  }

  dispose() {
    for (const s of this.subscriptions) {
      s.dispose();
    }
  }
}
