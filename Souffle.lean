import Lean
import Souffle.Basic
import Souffle.CommonPhase
import Souffle.LcnfPhase
import Souffle.ElabPhase

namespace Souffle

open Lean Meta

def emitRelations : CoreM Unit :=
  go |>.run' {}
where
  go : RelationsM Unit := do
    -- emit .types & .decls
    Souffle.emitCommonTypes
    Souffle.emitElabTypes
    Souffle.emitLcnfTypes
    -- emit facts
    Souffle.emitCommonFacts
    Souffle.emitElabFacts
    Souffle.emitLcnfFacts