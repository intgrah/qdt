import * as VSCode from "vscode";
import {
  LanguageClient,
  RevealOutputChannelOn,
  type LanguageClientOptions,
  type ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export async function activate(
  context: VSCode.ExtensionContext
): Promise<void> {
  const output = VSCode.window.createOutputChannel("QDT");
  context.subscriptions.push(output);

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

  try {
    await client.start();
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
