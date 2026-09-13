import VersoManual
import VersoBlueprint.PreviewManifest
import LaPToP.Blueprint

open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LaPToP.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
