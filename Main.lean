import Lean
import Lean.Compiler.LCNF
import Init.Data.Format
import Init.Data.List
import Lean.Compiler.LCNF.Probing

import Souffle

open Lean Meta Compiler LCNF

def main : IO Unit :=
  IO.println s!"Hello!"

-- #eval Probe.runOnModule `LeanLcnf (phase := .mono)
--   <| Souffle.emitRelations
--   >=> Probe.declNames

-- set_option trace.Compiler.init true in
-- #eval Lean.Compiler.compile #[``Lean.Compiler.LCNF.Probe.filterByFun]

#eval Souffle.emitRelations

-- #eval Probe.runGlobally (phase := .mono)
--   <| Souffle.emitRelations
--   >=> Probe.count

set_option pp.funBinderTypes true in
set_option pp.letVarTypes true in
set_option pp.showLetValues true in
set_option trace.Compiler.result true in
def b (p: Nat × Nat) : Nat × (String × Nat) :=
  { p with fst := p.fst + 1, snd := (toString p.snd, p.snd + 2) }

set_option pp.funBinderTypes true in
set_option pp.letVarTypes true in
set_option pp.showLetValues true in
set_option trace.Compiler.result true in
def a (x: Nat): Nat :=
  let b := b (x, 2)
  b.snd.snd

set_option pp.funBinderTypes true in
set_option pp.letVarTypes true in
set_option pp.showLetValues true in
set_option trace.Compiler.result true in
def a1 (x: Nat): Nat :=
  let b := (1, x)
  b.snd

-- set_option pp.funBinderTypes true in
-- set_option pp.letVarTypes true in
-- set_option pp.showLetValues true in
-- set_option trace.Compiler.result true in
-- def blah : BaseIO String := pure "blah"

set_option trace.Compiler.result true in
def blah1 (str: String) : BaseIO String := pure (str ++ "blah")

#reduce BaseIO String
#reduce EStateM.Result Empty PUnit String

set_option pp.funBinderTypes true in
set_option pp.letVarTypes true in
set_option pp.showLetValues true in
set_option trace.Compiler.result true in
def a : IO String := pure "aa"
