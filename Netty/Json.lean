import Lean
import Netty.Doc

/-!
# Saving and loading a proof

"Using a menu item, a proof in a proof pane can be saved as a file … and the
proof pane can be loaded from a proof file, and the context and suggestions
will be recalculated." A `Doc` is ordinary first-order data, so saving it is
`Lean.Json` and nothing else; the context and the suggestions are not stored,
because they are functions of the document and are recomputed on load.

The file carries a format version so that a later change to the document model
can be recognised rather than misread.
-/

namespace Netty

deriving instance Lean.ToJson, Lean.FromJson for BinOp
deriving instance Lean.ToJson, Lean.FromJson for Ty
deriving instance Lean.ToJson, Lean.FromJson for Pos
deriving instance Lean.ToJson, Lean.FromJson for Dir
deriving instance Lean.ToJson, Lean.FromJson for Expr
deriving instance Lean.ToJson, Lean.FromJson for Law
deriving instance Lean.ToJson, Lean.FromJson for Line
deriving instance Lean.ToJson, Lean.FromJson for Frame
deriving instance Lean.ToJson, Lean.FromJson for Doc

/-- The version of the save format written by this kernel. -/
def saveFormatVersion : Nat := 1

/-- A proof file: the format version and the document. -/
def toSaveJson (d : Doc) : Lean.Json :=
  Lean.Json.mkObj [("netty", Lean.toJson saveFormatVersion), ("doc", Lean.toJson d)]

/-- Read a proof file. -/
def ofSaveJson (j : Lean.Json) : Except String Doc := do
  let v : Nat ← (j.getObjVal? "netty").bind Lean.fromJson?
  if v != saveFormatVersion then
    throw s!"this is a Netty proof file of format {v}; this kernel writes and \
      reads format {saveFormatVersion}"
  (j.getObjVal? "doc").bind Lean.fromJson?

/-- The text of a proof file. -/
def saveText (d : Doc) : String := (toSaveJson d).pretty ++ "\n"

/-- Read the text of a proof file. -/
def loadText (s : String) : Except String Doc := do
  ofSaveJson (← Lean.Json.parse s)

end Netty
