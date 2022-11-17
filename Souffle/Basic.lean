import Lean
import Lean.Compiler.LCNF.Probing

open Lean Meta Compiler LCNF

namespace Souffle

-- TODO: LCNF missing Hashable on AltCore
deriving instance Hashable for AltCore

/-
All the LCNF relations including module import relations
-/
inductive Relation
| Param
| ArgErased
| ArgFVar
| ArgType
| Decl
| DeclParam
-- | Code
| Let
| LetValueNat
| LetValueStr
| LetValueErased
| LetValueProj
| LetValueConst
| LetValueConstArg
| LetValueFVar
| LetValueFVarArg
| Fun
| FunParam
| Jp
| JpParam
| Jmp
| JmpArg
| Cases
| Alt
| AltParam
| AltDefault
| Return
| Unreach
| Module
| ModuleImport
deriving Hashable, BEq

instance : ToString Relation where
  toString
  | .Param => "Param"
  | .ArgErased => "ArgErased"
  | .ArgFVar => "ArgFVar"
  | .ArgType => "ArgType"
  | .Decl => "Decl"
  | .DeclParam => "DeclParam"
  | .Let => "Let"
  | .LetValueNat => "LetValueNat"
  | .LetValueStr => "LetValueStr"
  | .LetValueErased => "LetValueErased"
  | .LetValueProj => "LetValueProj"
  | .LetValueConst => "LetValueConst"
  | .LetValueConstArg => "LetValueConstArg"
  | .LetValueFVar => "LetValueFVar"
  | .LetValueFVarArg => "LetValueFVarArg"
  | .Fun => "Fun"
  | .FunParam => "FunParam"
  | .Jp => "Jp"
  | .JpParam => "JpParam"
  | .Jmp => "Jmp"
  | .JmpArg => "JmpArg"
  | .Cases => "Cases"
  | .Alt => "Alt"
  | .AltParam => "AltParam"
  | .AltDefault => "AltDefault"
  | .Return => "Return"
  | .Unreach => "Unreach"
  | .Module => "Module"
  | .ModuleImport => "ModuleImport"

/-
Track relation handles since Souffle expects one .facts file
per relation
-/
structure RelationState where
  handles : HashMap Relation (Option IO.FS.Handle) := {}


abbrev RelationsM (α : Type) := StateT RelationState CoreM α

/-
Helper to retrieve the corresponding IO Handle for each relation
-/
def handle (rel : Relation) : RelationsM IO.FS.Handle := do
  let s ← get
  if let .some (.some h) := s.handles.find? rel then
    pure h
  else
    -- TODO Parameterize me
    let h ← IO.FS.Handle.mk s!"./gen/facts/{rel}.facts" IO.FS.Mode.write
    modifyGet (fun s => (h, { s with handles := s.handles.insert rel (.some h) }))

/-
If you declare the .input for a relation, Souffle expects the .facts file to
exist. So we force the creation of all .facts files.

TODO: avoid hardcoding duplicating all cases
-/
def init : RelationsM Unit := do
  let _ ← handle .Unreach
  let _ ← handle .Unreach
  let _ ← handle .Param
  let _ ← handle .ArgErased
  let _ ← handle .ArgFVar
  let _ ← handle .ArgType
  let _ ← handle .Decl
  let _ ← handle .DeclParam
  let _ ← handle .Let
  let _ ← handle .LetValueNat
  let _ ← handle .LetValueStr
  let _ ← handle .LetValueErased
  let _ ← handle .LetValueProj
  let _ ← handle .LetValueConst
  let _ ← handle .LetValueConstArg
  let _ ← handle .LetValueFVar
  let _ ← handle .LetValueFVarArg
  let _ ← handle .Fun
  let _ ← handle .FunParam
  let _ ← handle .Jp
  let _ ← handle .JpParam
  let _ ← handle .Jmp
  let _ ← handle .JmpArg
  let _ ← handle .Cases
  let _ ← handle .Alt
  let _ ← handle .AltParam
  let _ ← handle .AltDefault
  let _ ← handle .Return
  let _ ← handle .Unreach

open Souffle

/-
Base helper to emit relations
-/
protected def emit [ToString α] (h : IO.FS.Handle) (fields: Array α) : RelationsM Unit :=
  let line := fields.foldl (init := "")
    (fun line field => line ++ (if line.length == 0 then (toString field) else "\t" ++ (toString field)))
  h.putStrLn line

protected def emitArg (arg: Arg) : RelationsM String := do
  let argId := toString <| hash arg
  match arg with
  | .erased =>
    Souffle.emit (← handle .ArgErased) #[argId]
  | .fvar fvarId =>
    Souffle.emit (← handle .ArgFVar) #[argId, toString fvarId.name]
  | .type type =>
    let typeId := toString <| hash type
    Souffle.emit (← handle .ArgType) #[argId, typeId]
  pure argId

protected def emitParam (param: Param) : RelationsM String := do
  let paramId := toString <| hash param
  let typeId := toString <| hash param.type
  Souffle.emit (← handle .Param) #[paramId, toString param.fvarId.name, toString param.binderName, typeId]
  pure paramId

protected def emitLetValue (decl: Decl) (letCode: Code) (letVal: LetValue) : RelationsM Unit := do
  let declId := toString decl.name
  let letCodeId := toString <| hash letCode
  match letVal with
  | .value (.strVal litVal) =>
    Souffle.emit (← handle .LetValueStr) #[declId, letCodeId, litVal.replace "\n" "\\n"]
  | .value (.natVal natVal) =>
    Souffle.emit (← handle .LetValueNat) #[declId, letCodeId, toString natVal]
  | .erased =>
    Souffle.emit (← handle .LetValueErased) #[declId, letCodeId]
  | .proj typeName idx struct =>
    Souffle.emit (← handle .LetValueProj) #[declId, letCodeId, toString typeName, toString idx, toString struct.name]
  | .const declName us args =>
    Souffle.emit (← handle .LetValueConst) #[declId, letCodeId, toString declName]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.emit (← handle .LetValueConstArg) #[declId, letCodeId, toString i, argId]
  | .fvar fvarId args =>
    Souffle.emit (← handle .LetValueFVar) #[declId, letCodeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.emit (← handle .LetValueFVarArg) #[declId, letCodeId, toString i, argId]

protected partial def emitCode (decl: Decl) (code : Code) : RelationsM Unit := do
  let declId := decl.name.toString
  let codeId := toString <| hash code
  match code with

  | .let ⟨fvarId, binderName, type, value⟩ next =>
    let nextId := toString <| hash next
    let typeId := toString <| hash type
    Souffle.emit (← handle .Let) #[declId, codeId, toString fvarId.name, toString binderName, typeId, nextId]
    Souffle.emitLetValue decl code value
    Souffle.emitCode decl next

  | .fun ⟨fvarId, binderName, params, type, value⟩ next =>
    emitFunOrJp declId codeId fvarId binderName params type value next .Fun .FunParam

  | .jp ⟨fvarId, binderName, params, type, value⟩ next =>
    emitFunOrJp declId codeId fvarId binderName params type value next .Jp .JpParam

  | .jmp fvarId args =>
    Souffle.emit (← handle .Jmp) #[declId, codeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.emit (← handle .JmpArg) #[declId, codeId, toString i, argId]

  | .cases ⟨typeName, resultType, disc, alts⟩ => do
    let resultTypeId := toString <| hash resultType
    Souffle.emit (← handle .Cases) #[declId, codeId, toString typeName, resultTypeId, toString disc.name]
    for alt in alts do
      emitAlt declId codeId alt
  | .return fvarId =>
    Souffle.emit (← handle .Return) #[declId, codeId, fvarId.name.toString]
  | .unreach type =>
    let typeId := toString <| hash type
    Souffle.emit (← handle .Unreach) #[declId, codeId, typeId]
where
  emitAlt (declId: String) (codeId : String) (alt: AltCore Code) : RelationsM Unit := do
    let altId := toString <| hash alt
    match alt with
    | .alt ctorName params code =>
      Souffle.emit (← handle .Alt) #[declId, codeId, altId, toString ctorName]
      for i in [:params.size] do
        let paramId ← Souffle.emitParam params[i]!
        Souffle.emit (← handle .AltParam) #[declId, codeId, altId, toString i, paramId]
      Souffle.emitCode decl code
    | .default next =>
      let nextId := toString <| hash code
      Souffle.emit (← handle .AltDefault) #[declId, codeId, altId, nextId]
      Souffle.emitCode decl next

  emitFunOrJp (declId: String) (codeId: String) (fvarId: FVarId) (binderName: Name) (params: Array Param) (type: Expr) (value: Code) (next: Code) (rel: Relation) (paramRel: Relation): RelationsM Unit := do
    let typeId := toString <| hash type
    let valueId := toString <| hash value
    let nextId := toString <| hash next
    Souffle.emit (← handle rel) #[declId, codeId, toString fvarId.name, toString binderName, typeId, valueId, nextId]
    for i in [:params.size] do
      let paramId ← Souffle.emitParam params[i]!
      Souffle.emit (← handle paramRel) #[declId, codeId, toString i, paramId]
    Souffle.emitCode decl value
    Souffle.emitCode decl next

protected def emitDecl (modName: Name) (decl : Decl) : RelationsM Decl := do
  let declId := decl.name.toString
  let typeId := toString <| hash decl.type
  Souffle.emit (← handle .Decl) #[declId, typeId, modName.toString]
  for i in [:decl.params.size] do
    let paramId ← Souffle.emitParam decl.params[i]!
    Souffle.emit (← handle .DeclParam) #[declId, toString i, paramId]
  Souffle.emitCode decl decl.value
  pure decl

protected def emitModules : RelationsM Unit := do
  let env ← getEnv
  for modName in env.allImportedModuleNames do
    let .some idx0 := env.getModuleIdx? modName | panic! "Unknown module name!"
    Souffle.emit (← handle .Module) #[toString idx0, modName.toString]
    let .some imports := env.header.moduleData.get? idx0 |>.map (·.imports) | panic! "Unknown module index!"
    for imp in imports do
      Souffle.emit (← handle .ModuleImport) #[modName.toString, imp.module.toString]

/-
Main entrypoint to emit relations for a Decl.
-/
def emitRelations : Probe Decl Decl :=
  fun decls => go decls |>.run' {}
where
  getModName (decl: Decl) : RelationsM Name := do
    let env ← getEnv
    if let .some modIdx := env.getModuleIdxFor? decl.name then
      if let .some modName := env.allImportedModuleNames.get? modIdx.toNat then
        pure modName
      else
        pure Name.anonymous
    else
      pure Name.anonymous
    pure Name.anonymous

  go (decls : Array Decl) : RelationsM (Array Decl) := do
    init
    Souffle.emitModules
    for decl in decls do
      let modName ← getModName decl
      let _ ← Souffle.emitDecl modName decl
    pure decls
