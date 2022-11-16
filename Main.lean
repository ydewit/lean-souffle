import Lean
import Lean.Compiler.LCNF
import Init.Data.Format
import Init.Data.List
import Lean.Compiler.LCNF.Probing

import Souffle

open Lean Meta Compiler LCNF

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


-- #eval Probe.runOnModule `LeanLcnf (phase := .mono)
--   <| emitRelations
--   >=> Probe.declNames

#eval Probe.runGlobally (phase := .mono)
  <| Souffle.emitRelations
  >=> Probe.count
