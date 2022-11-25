import Lean

import Souffle.Basic
import Souffle.CommonPhase
import Souffle.ElabPhase

open Lean Meta Compiler LCNF

namespace Souffle

-- TODO: LCNF missing Hashable on AltCore
deriving instance Hashable for AltCore

/-
All the LCNF relations including module import relations
-/
inductive LcnfRel
| ArgErased
| ArgFVar
| ArgType
| Decl
| DeclParam
| DeclModule
-- | Code
| Let
| LetValueLit
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

deriving Hashable, BEq

def LcnfRel.toString : LcnfRel → String
| .ArgErased => "ArgErased"
| .ArgFVar => "ArgFVar"
| .ArgType => "ArgType"
| .Decl => "Decl"
| .DeclParam => "DeclParam"
| .DeclModule => "DeclModule"
| .Let => "Let"
| .LetValueLit => "LetValueLit"
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

instance : ToString LcnfRel := ⟨ LcnfRel.toString ⟩

open Souffle

protected def emitArg (arg: Arg) : RelationsM String := do
  let argId := toString <| hash arg
  match arg with
  | .erased =>
    Souffle.writeFact LcnfRel.ArgErased
      #[argId]
  | .fvar fvarId =>
    Souffle.writeFact LcnfRel.ArgFVar
      #[argId, toString fvarId.name]
  | .type type =>
    let typeId := toString <| hash type
    Souffle.emitExpr type
    Souffle.writeFact LcnfRel.ArgType
      #[argId, typeId]
  pure argId

protected def emitLetValue (decl: Decl) (letCode: Code) (letVal: LetValue) : RelationsM Unit := do
  let declId := toString decl.name
  let letCodeId := toString <| hash letCode
  match letVal with
  | .value (.strVal litVal) =>
    Souffle.writeFact LcnfRel.LetValueLit
      #[declId, letCodeId, "StrVal", Souffle.escape litVal]
  | .value (.natVal natVal) =>
    Souffle.writeFact LcnfRel.LetValueLit
      #[declId, letCodeId, "NatVal", toString natVal]
  | .erased =>
    Souffle.writeFact LcnfRel.LetValueErased
      #[declId, letCodeId]
  | .proj typeName idx struct =>
    Souffle.writeFact LcnfRel.LetValueProj
      #[declId, letCodeId, toString typeName, toString idx, toString struct.name]
  | .const declName us args =>
    Souffle.writeFact LcnfRel.LetValueConst
      #[declId, letCodeId, toString declName]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact LcnfRel.LetValueConstArg
        #[declId, letCodeId, toString i, argId]
  | .fvar fvarId args =>
    Souffle.writeFact LcnfRel.LetValueFVar
      #[declId, letCodeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact LcnfRel.LetValueFVarArg
        #[declId, letCodeId, toString i, argId]

protected partial def emitCode (decl: Decl) (code : Code) : RelationsM Unit := do
  let declId := decl.name.toString
  let codeId := toString <| hash code
  match code with

  | .let ⟨fvarId, binderName, type, value⟩ next =>
    let nextId := toString <| hash next
    let typeId := toString <| hash type
    Souffle.emitExpr type
    Souffle.writeFact LcnfRel.Let
      #[declId, codeId, toString fvarId.name, toString binderName, typeId, nextId]
    Souffle.emitLetValue decl code value
    Souffle.emitCode decl next

  | .fun ⟨fvarId, binderName, params, type, value⟩ next =>
    Souffle.emitExpr type
    emitFunOrJp declId codeId fvarId binderName params type value next .Fun .FunParam

  | .jp ⟨fvarId, binderName, params, type, value⟩ next =>
    Souffle.emitExpr type
    emitFunOrJp declId codeId fvarId binderName params type value next .Jp .JpParam

  | .jmp fvarId args =>
    Souffle.writeFact LcnfRel.Jmp
      #[declId, codeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact LcnfRel.JmpArg
        #[declId, codeId, toString i, argId]

  | .cases ⟨typeName, resultType, disc, alts⟩ => do
    Souffle.emitExpr resultType
    let resultTypeId := toString <| hash resultType
    Souffle.writeFact LcnfRel.Cases
      #[declId, codeId, toString typeName, resultTypeId, toString disc.name]
    for altIdx in [:alts.size] do
      let alt := alts[altIdx]!
      emitAlt declId codeId altIdx alt
  | .return fvarId =>
    Souffle.writeFact LcnfRel.Return
      #[declId, codeId, fvarId.name.toString]
  | .unreach type =>
    let typeId := toString <| hash type
    Souffle.writeFact LcnfRel.Unreach
      #[declId, codeId, typeId]
where
  emitAlt (declId: String) (casesCodeId : String) (altIdx: Nat) (alt: AltCore Code) : RelationsM Unit := do
    match alt with
    | .alt ctorName params code =>
      let nextId := toString <| hash code
      Souffle.writeFact LcnfRel.Alt
        #[declId, casesCodeId, toString altIdx, toString ctorName, nextId]
      for paramIdx in [:params.size] do
        let param := params[paramIdx]!
        let typeId := toString <| hash param.type
        Souffle.emitExpr param.type
        Souffle.writeFact LcnfRel.AltParam
          #[declId, casesCodeId, toString altIdx, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
      Souffle.emitCode decl code
    | .default next =>
      let nextId := toString <| hash code
      Souffle.writeFact LcnfRel.AltDefault
        #[declId, casesCodeId, toString altIdx, nextId]
      Souffle.emitCode decl next

  emitFunOrJp (declId: String) (codeId: String) (fvarId: FVarId) (binderName: Name) (params: Array Param) (type: Expr) (value: Code) (next: Code) (rel: LcnfRel) (paramRel: LcnfRel): RelationsM Unit := do
    let typeId := toString <| hash type
    let valueId := toString <| hash value
    let nextId := toString <| hash next
    Souffle.writeFact rel #[declId, codeId, toString fvarId.name, toString binderName, typeId, valueId, nextId]
    for paramIdx in [:params.size] do
      let param := params[paramIdx]!
      let typeId := toString <| hash param.type
      Souffle.emitExpr param.type
      Souffle.writeFact paramRel #[declId, codeId, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
    Souffle.emitCode decl value
    Souffle.emitCode decl next

protected def emitDecl (decl : Decl) : RelationsM Unit := do
  let declId := decl.name.toString
  let typeId := toString <| hash decl.type
  -- Write Decl
  Souffle.writeFact LcnfRel.Decl #[declId, typeId]
  -- write a DeclModule fact only if there is a module for the given Decl
  if let .some modIdx := (← getEnv).getModuleIdxFor? decl.name then
    Souffle.writeFact LcnfRel.DeclModule #[declId, toString modIdx]
  -- Write DeclParam's
  for paramIdx in [:decl.params.size] do
    let param := decl.params[paramIdx]!
    Souffle.writeFact LcnfRel.DeclParam #[declId, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
  Souffle.emitCode decl decl.value

/-
-/
protected def emitLcnfTypes : RelationsM Unit := do
  let h ← declsHandle
  h.putStrLn ".type LitType <: symbol // = NatVal | StrVal"
  h.putStrLn ""

  -- Arg
  Souffle.writeDecl LcnfRel.ArgErased #[("argId","Hash")] #[]
  Souffle.writeDecl LcnfRel.ArgFVar   #[("argId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl LcnfRel.ArgType   #[("argId","Hash")] #[("typeId","Hash")]
  h.putStrLn ""

  -- Decl
  Souffle.writeDecl LcnfRel.Decl #[("declName","Name")] #[("typeId","Name")]
  Souffle.writeDecl LcnfRel.DeclParam #[("declName","Name"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  Souffle.writeDecl LcnfRel.DeclModule #[("declName","Name"),("moduleIdx","Nat")] #[]
  h.putStrLn ""

  -- Code
  Souffle.writeDecl LcnfRel.Let #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl LcnfRel.LetValueLit #[("declName","Name"),("codeId","Hash")] #[("litType","LitType"),("value","String")]
  Souffle.writeDecl LcnfRel.LetValueErased #[("declName","Name"),("codeId","Hash")]
  Souffle.writeDecl LcnfRel.LetValueProj #[("declName","Name"),("codeId","Hash")] #[("typeName","Name"),("idx","Nat"),("struct","FVarId")]
  Souffle.writeDecl LcnfRel.LetValueConst #[("declName","Name"),("codeId","Hash")] #[("constName","Name")]
  Souffle.writeDecl LcnfRel.LetValueConstArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("argId","Hash")]
  Souffle.writeDecl LcnfRel.LetValueFVar #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl LcnfRel.LetValueFVarArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")]  #[("argId","Hash")]
  h.putStrLn ""

  -- Fun
  Souffle.writeDecl LcnfRel.Fun #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("valueId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl LcnfRel.FunParam #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  h.putStrLn ""

  -- Jp
  Souffle.writeDecl LcnfRel.Jp #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("valueId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl LcnfRel.JpParam #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  h.putStrLn ""

  -- Jmp
  Souffle.writeDecl LcnfRel.Jmp #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl LcnfRel.JmpArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("argId","Hash")]
  h.putStrLn ""

  -- Cases
  Souffle.writeDecl LcnfRel.Cases #[("declName","Name"),("codeId","Hash")] #[("typeName","Name"),("resultTypeId","Hash"),("disc","FVarId")]
  Souffle.writeDecl LcnfRel.Alt #[("declName","Name"),("codeId","Hash"),("altIdx","Nat")] #[("ctorName","Name"),("nextCodeId","Hash")]
  Souffle.writeDecl LcnfRel.AltParam #[("declName","Name"),("codeId","Hash"),("altIdx","Nat"),("paramIdx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  Souffle.writeDecl LcnfRel.AltDefault #[("declName","Name"),("codeId","Hash"),("altIdx","Nat")] #[("nextCodeId","Hash")]
  h.putStrLn ""

  -- Return
  Souffle.writeDecl LcnfRel.Return #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  h.putStrLn ""

  -- Unreach
  Souffle.writeDecl LcnfRel.Unreach #[("declName","Name"),("codeId","Hash")] #[("typeId","Hash")]
  h.putStrLn ""
  h.flush
/-
Main entrypoint to emit relations for a Decl.
-/
-- def emitCoreDecls : CoreM Unit := do
--   initCoreDecls |>.run' {}

-- def emitCoreFacts : CoreM Unit := do
--   emitFacts |>.run' {}

-- def emitLcnfDecls : CoreM Unit := do
--   go |>.run' {}
-- where
--   go : RelationsM Unit := do
--     Souffle.emitCoreDecls
--     initTypes

-- def emitLcnfFacts : CoreM Unit := do
--   emitFacts |>.run' {}


protected def runDeclsGlobally (action: Decl → RelationsM Unit) (phase: Phase := .base) : RelationsM Unit := do
  let ext := getExt phase
  let env ← getEnv
  for modIdx in [:env.allImportedModuleNames.size] do
    let decls := ext.getModuleEntries env modIdx
    for decl in decls do
      action decl

protected def emitLcnfFacts : RelationsM Unit := do
  -- initFacts
  Souffle.runDeclsGlobally Souffle.emitDecl

  -- initFacts : RelationsM Unit := do
  --   let _ ← factsHandle LcnfRel.Unreach
  --   let _ ← factsHandle LcnfRel.ArgErased
  --   let _ ← factsHandle LcnfRel.ArgFVar
  --   let _ ← factsHandle LcnfRel.ArgType
  --   let _ ← factsHandle LcnfRel.Decl
  --   let _ ← factsHandle LcnfRel.DeclParam
  --   let _ ← factsHandle LcnfRel.DeclModule
  --   let _ ← factsHandle LcnfRel.Let
  --   let _ ← factsHandle LcnfRel.LetValueLit
  --   let _ ← factsHandle LcnfRel.LetValueErased
  --   let _ ← factsHandle LcnfRel.LetValueProj
  --   let _ ← factsHandle LcnfRel.LetValueConst
  --   let _ ← factsHandle LcnfRel.LetValueConstArg
  --   let _ ← factsHandle LcnfRel.LetValueFVar
  --   let _ ← factsHandle LcnfRel.LetValueFVarArg
  --   let _ ← factsHandle LcnfRel.Fun
  --   let _ ← factsHandle LcnfRel.FunParam
  --   let _ ← factsHandle LcnfRel.Jp
  --   let _ ← factsHandle LcnfRel.JpParam
  --   let _ ← factsHandle LcnfRel.Jmp
  --   let _ ← factsHandle LcnfRel.JmpArg
  --   let _ ← factsHandle LcnfRel.Cases
  --   let _ ← factsHandle LcnfRel.Alt
  --   let _ ← factsHandle LcnfRel.AltParam
  --   let _ ← factsHandle LcnfRel.AltDefault
  --   let _ ← factsHandle LcnfRel.Return
  --   let _ ← factsHandle LcnfRel.Unreach
