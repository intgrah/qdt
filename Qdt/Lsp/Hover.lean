module

public import Qdt.Error

@[expose] public section

namespace Qdt.Lsp

def formatHover (hover : HoverContent) : String :=
  hover.format

end Qdt.Lsp
