import * as VSCode from "vscode";
import {
  LanguageClient,
  RevealOutputChannelOn,
  type LanguageClientOptions,
  type ServerOptions,
} from "vscode-languageclient/node";
import { AbbreviationFeature } from "./abbreviation/AbbreviationFeature";

interface LspRange {
  start: { line: number; character: number };
  end: { line: number; character: number };
}

interface FileProgressProcessingInfo {
  range: LspRange;
  kind?: number;
}

interface FileProgressParams {
  textDocument: { uri: string; version?: number };
  processing: FileProgressProcessingInfo[];
}

let client: LanguageClient | undefined;

export async function activate(
  context: VSCode.ExtensionContext,
): Promise<void> {
  const output = VSCode.window.createOutputChannel("QDT");
  context.subscriptions.push(output);

  context.subscriptions.push(new AbbreviationFeature());

  const processingDecoration = VSCode.window.createTextEditorDecorationType({
    overviewRulerLane: VSCode.OverviewRulerLane.Left,
    overviewRulerColor: "rgba(255, 165, 0, 0.5)",
    dark: {
      gutterIconPath: context.asAbsolutePath("media/progress-dark.svg"),
      gutterIconSize: "contain",
    },
    light: {
      gutterIconPath: context.asAbsolutePath("media/progress-light.svg"),
      gutterIconSize: "contain",
    },
  });
  context.subscriptions.push(processingDecoration);

  const serverOptions: ServerOptions = {
    command: "qdt-lsp",
    args: [],
    options: { cwd: VSCode.workspace.workspaceFolders?.[0]?.uri.fsPath },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { scheme: "file", language: "qdt" },
      { scheme: "untitled", language: "qdt" },
    ],
    outputChannel: output,
    revealOutputChannelOn: RevealOutputChannelOn.Error,
  };

  client = new LanguageClient("qdt", "QDT", serverOptions, clientOptions);
  context.subscriptions.push({ dispose: () => client?.stop() });

  context.subscriptions.push(
    VSCode.commands.registerCommand("qdt.restartServer", async () => {
      await client?.restart();
    }),
    VSCode.commands.registerCommand("qdt.stopServer", async () => {
      await client?.stop();
    }),
  );

  try {
    await client.start();
    client.onNotification("$/lean/fileProgress", (params: FileProgressParams) => {
      const uri = VSCode.Uri.parse(params.textDocument.uri);
      const decos: VSCode.DecorationOptions[] = params.processing
        .filter((i) => i.kind === undefined || i.kind === 1)
        .map((i) => ({
          range: new VSCode.Range(i.range.start.line, 0, i.range.end.line, 0),
          hoverMessage: "Processing...",
        }));
      for (const editor of VSCode.window.visibleTextEditors) {
        if (editor.document.uri.toString() === uri.toString()) {
          editor.setDecorations(processingDecoration, decos);
        }
      }
    });
  } catch (err: unknown) {
    output.appendLine(`[qdt] Failed to start: ${String(err)}`);
    output.show(true);
    VSCode.window.showErrorMessage("qdt-lsp not on PATH");
  }
}

export async function deactivate(): Promise<void> {
  await client?.stop();
  client = undefined;
}
