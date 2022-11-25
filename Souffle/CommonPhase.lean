import Lean
import Souffle.Basic

open Lean Meta

namespace Souffle

inductive CommonRel
| Namespace
| Module
| ModuleImport

def CommonRel.toString : CommonRel -> String
| .Namespace => "Namespace"
| .Module => "Module"
| .ModuleImport => "ModuleImport"

instance : ToString CommonRel := ⟨ CommonRel.toString ⟩

open Souffle

protected def emitCommonTypes: RelationsM Unit := do
  let h ← declsHandle
  h.putStrLn ".type Bool <: symbol"
  h.putStrLn ".type Name <: symbol"
  h.putStrLn ".type FVarId <: symbol"
  h.putStrLn ".type MVarId <: symbol"
  h.putStrLn ".type Hash <: unsigned"
  h.putStrLn ".type Nat <: unsigned // max 2^32"
  h.putStrLn ".type String <: symbol"
  h.putStrLn ""
  h.flush

protected def runNamespacesGlobally (action: Name → RelationsM Unit) : RelationsM Unit := do
  (← getEnv).getNamespaceSet.forM action

protected def runModulesGlobally (action: Name → Nat → ModuleData → RelationsM Unit) : RelationsM Unit := do
  let env ← getEnv
  for modName in env.allImportedModuleNames do
    let .some modIdx := env.getModuleIdx? modName | panic! "Unknown module name!"
    let .some modData := env.header.moduleData.get? modIdx | panic! "Unknown module index!"
    action modName modIdx modData

protected def emitCommonFacts: RelationsM Unit := do
  Souffle.runNamespacesGlobally emitNamespace
  Souffle.runModulesGlobally emitModule
where
  emitModule (modName: Name) (modIdx: Nat) (modData: ModuleData) : RelationsM Unit := do
    Souffle.writeFact CommonRel.Module #[modName.toString, toString modIdx]
    for imp in modData.imports do
      Souffle.writeFact CommonRel.ModuleImport #[modName.toString, imp.module.toString]

  emitNamespace (ns: Name) : RelationsM Unit :=
    Souffle.writeFact CommonRel.Namespace #[ns]
