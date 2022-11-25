import Lean
import Lean.Compiler.LCNF.Probing

import Souffle.Util

open Lean Meta Compiler LCNF

namespace Souffle

/-
Track relation handles since Souffle expects one .facts file
per relation
-/
structure RelationState where
  /- One .facts handle per relation -/
  factsHandle : HashMap String (Option IO.FS.Handle) := {}
  /- One .dl handle per set of relations (e.g. Expr or LCNF, ) -/
  declsHandle : Option IO.FS.Handle := .none
  lcnfPhase : Phase := .base

abbrev RelationsM (α : Type) := StateT RelationState CoreM α

def getLcnfPhase : RelationsM Phase := do
  pure (← get).lcnfPhase

/-
Retrieve the decls file handle (.dl) for a given RelationGroup
-/
def declsHandle: RelationsM IO.FS.Handle := do
  let s ← get
  if let .some h := s.declsHandle then
    pure h
  else
    -- TODO Parameterize me
    let h ← IO.FS.Handle.mk s!"./facts.dl" IO.FS.Mode.write
    modifyGet (fun s => (h, { s with declsHandle := .some h }))

/-
Retrieve the facts file handle (.facts) for a given Relation
-/
def factsHandle [ToString α] (rel: α) : RelationsM IO.FS.Handle := do
  let s ← get
  if let .some (.some h) := s.factsHandle.find? (toString rel) then
    pure h
  else
    -- TODO Parameterize me
    IO.FS.createDirAll s!"./facts/"
    let h ← IO.FS.Handle.mk s!"./facts/{rel}.facts" IO.FS.Mode.write
    modifyGet (fun s => (h, { s with factsHandle := s.factsHandle.insert (toString rel) (.some h) }))

open Souffle

def writeDecl [ToString α] [ToString β] [ToString r] (rel: r) (keys: Array (α × β)) (fields: Array (α × β) := {}) (printSize: Bool := false) : RelationsM Unit := do
  let h ← declsHandle
  h.putStr s!".decl {rel}"
  let keysStr := keys.map fun key => (s!"{key.fst}:{key.snd}")
  let fieldsStr := fields.map fun field => (s!"{field.fst}:{field.snd}")
  h.putStr s!"({Souffle.joinSep keysStr}{Souffle.joinSep (pre := ", ") fieldsStr})"
  if keys.size < fields.size then
    h.putStr s!" choice-domain ({Souffle.joinSep (keys.map (·.fst))})"
  h.putStrLn ""
  h.putStrLn s!".input {rel}"
  unless printSize == false do h.putStrLn s!".printsize {rel}"

protected def writeFact [ToString α] [ToString β] (rel: α) (fields: Array β) : RelationsM Unit := do
  let line := fields.foldl (init := "")
    (fun line field => line ++ (if line.length == 0 then s!"{field}" else s!"\t{field}"))
  (← factsHandle rel).putStrLn line
