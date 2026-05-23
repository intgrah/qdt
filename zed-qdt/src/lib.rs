use zed_extension_api::{self as zed, settings::LspSettings};

struct QdtExtension;

impl zed::Extension for QdtExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        language_server_id: &zed::LanguageServerId,
        worktree: &zed::Worktree,
    ) -> zed::Result<zed::Command> {
        let binary = LspSettings::for_worktree(language_server_id.as_ref(), worktree)?
            .binary
            .ok_or_else(|| "qdt: set lsp.qdt.binary.path in Zed settings".to_string())?;
        let command = binary
            .path
            .ok_or_else(|| "qdt: lsp.qdt.binary.path is required".to_string())?;
        Ok(zed::Command {
            command,
            args: binary.arguments.unwrap_or_default(),
            env: binary.env.map(|m| m.into_iter().collect()).unwrap_or_default(),
        })
    }
}

zed::register_extension!(QdtExtension);
