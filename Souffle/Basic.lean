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
-- NS
| Namespace
-- MODULE
| Module
| ModuleImport
-- CONSTANT INFO
-- | ConstantInfo
| InductiveVal
| ConstructorVal
| DefinitionVal
| OpaqueVal
| AxiomVal
| TheoremVal
| QuotVal
| RecVal
| RecValRule
-- Expr
| ExprBVar
| ExprFVar
| ExprMVar
| ExprSort
| ExprConst
| ExprApp
| ExprLam
| ExprForall
| ExprLet
| ExprLit
| ExprMData
| ExprMDataKVEntry
| ExprProj


deriving Hashable, BEq

instance : ToString Relation where
  toString
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
  | .Namespace => "Namespace"
  | .Module => "Module"
  | .ModuleImport => "ModuleImport"
  -- | .ConstantInfo => "ConstantInfo"
  | .InductiveVal => "InductiveVal"
  | .ConstructorVal => "ConstructorVal"
  | .DefinitionVal => "DefinitionVal"
  | .OpaqueVal => "OpaqueVal"
  | .AxiomVal => "AxiomVal"
  | .TheoremVal => "TheoremVal"
  | .QuotVal => "QuotVal"
  | .RecVal => "RecVal"
  | .RecValRule => "RecValRule"
  | .ExprBVar => "ExprBVar"
  | .ExprFVar => "ExprFVar"
  | .ExprMVar => "ExprMVar"
  | .ExprSort => "ExprSort"
  | .ExprConst => "ExprConst"
  | .ExprApp => "ExprApp"
  | .ExprLam => "ExprLam"
  | .ExprForall => "ExprForall"
  | .ExprLet => "ExprLet"
  | .ExprLit => "ExprLit"
  | .ExprMData => "ExprMData"
  | .ExprMDataKVEntry => "ExprMDataKVEntry"
  | .ExprProj => "ExprProj"



/-
Track relation handles since Souffle expects one .facts file
per relation
-/
structure RelationState where
  factsHandle : HashMap String (Option IO.FS.Handle) := {}
  declsHandle : Option IO.FS.Handle := .none

abbrev RelationsM (α : Type) := StateT RelationState CoreM α

/-
Helper to retrieve the corresponding IO Handle for each relation
-/
def declsHandle : RelationsM IO.FS.Handle := do
  let s ← get
  if let .some h := s.declsHandle then
    pure h
  else
    -- TODO Parameterize me
    let h ← IO.FS.Handle.mk s!"./dl/Lean.dl" IO.FS.Mode.write
    modifyGet (fun s => (h, { s with declsHandle := h }))

def factHandle (rel : Relation) : RelationsM IO.FS.Handle := do
  let s ← get
  if let .some (.some h) := s.factsHandle.find? (toString rel) then
    pure h
  else
    -- TODO Parameterize me
    let h ← IO.FS.Handle.mk s!"./facts/{rel}.facts" IO.FS.Mode.write
    modifyGet (fun s => (h, { s with factsHandle := s.factsHandle.insert (toString rel) (.some h) }))

open Souffle

protected def joinSep {α : Type u} [ToString α] (items: Array α)  (pre: String := "") (sep: String := ", ") (post: String := ""): String :=
  (if items.size > 0 then pre else "")
    ++ items.foldl (init := "") (fun acc item => acc ++ if acc.length == 0 then (toString item) else sep ++ (toString item))
    ++ post

protected def writeDecl [ToString α] [ToString β] (rel : Relation) (keys: Array (α × β)) (fields: Array (α × β) := {}) (printSize: Bool := true) : RelationsM Unit := do
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

-- TODO: for now, hardcoding
def initDecls : RelationsM Unit := do
  let h ← declsHandle
  h.putStrLn ".type Bool <: symbol"
  h.putStrLn ".type Name <: symbol"
  h.putStrLn ".type FVarId <: symbol"
  h.putStrLn ".type MVarId <: symbol"
  h.putStrLn ".type Hash <: unsigned"
  h.putStrLn ".type Nat <: unsigned // max 2^32"
  h.putStrLn ".type String <: symbol"
  h.putStrLn ".type LitType <: symbol // = NatVal | StrVal"
  h.putStrLn ".type DefinitionSafety <: symbol // = unsafe | safe | partial"
  h.putStrLn ".type QuotKind <: symbol // = type | ctor | lift | ind"
  h.putStrLn ".type BinderInfo <: symbol // = default | implicit | strictImplicit | instImplicit"
  h.putStrLn ""

  -- Arg
  Souffle.writeDecl .ArgErased #[("argId","Hash")] #[]
  Souffle.writeDecl .ArgFVar   #[("argId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl .ArgType   #[("argId","Hash")] #[("typeId","Hash")]
  h.putStrLn ""

  -- Decl
  Souffle.writeDecl .Decl #[("declName","Name")] #[("typeId","Name")]
  Souffle.writeDecl .DeclParam #[("declName","Name"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  Souffle.writeDecl .DeclModule #[("declName","Name"),("moduleIdx","Nat")] #[]
  h.putStrLn ""

  -- Code
  Souffle.writeDecl .Let #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl .LetValueLit #[("declName","Name"),("codeId","Hash")] #[("litType","LitType"),("value","String")]
  Souffle.writeDecl .LetValueErased #[("declName","Name"),("codeId","Hash")]
  Souffle.writeDecl .LetValueProj #[("declName","Name"),("codeId","Hash")] #[("typeName","Name"),("idx","Nat"),("struct","FVarId")]
  Souffle.writeDecl .LetValueConst #[("declName","Name"),("codeId","Hash")] #[("constName","Name")]
  Souffle.writeDecl .LetValueConstArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("argId","Hash")]
  Souffle.writeDecl .LetValueFVar #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl .LetValueFVarArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")]  #[("argId","Hash")]
  h.putStrLn ""

  -- Fun
  Souffle.writeDecl .Fun #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("valueId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl .FunParam #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  h.putStrLn ""

  -- Jp
  Souffle.writeDecl .Jp #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId"),("binderName","Name"),("typeId","Hash"),("valueId","Hash"),("nextCodeId","Hash")]
  Souffle.writeDecl .JpParam #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  h.putStrLn ""

  -- Jmp
  Souffle.writeDecl .Jmp #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  Souffle.writeDecl .JmpArg #[("declName","Name"),("codeId","Hash"),("idx","Nat")] #[("argId","Hash")]
  h.putStrLn ""

  -- Cases
  Souffle.writeDecl .Cases #[("declName","Name"),("codeId","Hash")] #[("typeName","Name"),("resultTypeId","Hash"),("disc","FVarId")]
  Souffle.writeDecl .Alt #[("declName","Name"),("codeId","Hash"),("altIdx","Nat")] #[("ctorName","Name"),("nextCodeId","Hash")]
  Souffle.writeDecl .AltParam #[("declName","Name"),("codeId","Hash"),("altIdx","Nat"),("paramIdx","Nat")] #[("fvarId", "FVarId"),("binderName", "Name"),("typeId","Hash")]
  Souffle.writeDecl .AltDefault #[("declName","Name"),("codeId","Hash"),("altIdx","Nat")] #[("nextCodeId","Hash")]
  h.putStrLn ""

  -- Return
  Souffle.writeDecl .Return #[("declName","Name"),("codeId","Hash")] #[("fvarId","FVarId")]
  h.putStrLn ""

  -- Unreach
  Souffle.writeDecl .Unreach #[("declName","Name"),("codeId","Hash")] #[("typeId","Hash")]
  h.putStrLn ""

  -- NS
  Souffle.writeDecl .Namespace #[("namespace", "Name")] #[]
  h.putStrLn ""

  -- Module
  Souffle.writeDecl .Module #[("modName", "Name"), ("modIdx", "Nat")] #[]
  Souffle.writeDecl .ModuleImport #[("modName", "Name")] #[("importName", "Name")]
  h.putStrLn ""

  -- ConstantInfo
  Souffle.writeDecl .InductiveVal #[("declName", "Name")] #[("type", "Hash"), ( "numParams", "Nat"), ("numIndices", "Nat"), ("rec", "Bool"),("unsafe","Bool"),("reflexive","Bool"),("nested","Bool")]
  Souffle.writeDecl .ConstructorVal #[("declName", "Name")] #[("type", "Hash"), ( "inductName", "Name"), ("cidx", "Nat"), ("numParams", "Nat"), ("numFields", "Nat"), ("unsafe", "Bool")]
  Souffle.writeDecl .DefinitionVal #[("declName", "Name")] #[("type", "Hash"), ( "value", "Hash"), ("hints", "String"), ("safety", "DefinitionSafety")]
  Souffle.writeDecl .OpaqueVal #[("declName", "Name")] #[("type", "Hash"), ( "value", "Hash"), ("unsafe","Bool")]
  Souffle.writeDecl .AxiomVal #[("declName", "Name")] #[("type", "Hash"), ("unsafe","Bool")]
  Souffle.writeDecl .TheoremVal #[("declName", "Name")] #[("type", "Hash"), ("value","Hash")]
  Souffle.writeDecl .QuotVal #[("declName", "Name")] #[("type", "Hash"), ("kind","QuotKind")]
  Souffle.writeDecl .RecVal #[("declName", "Name")] #[("type", "Hash"), ("numParams","Nat"),("numIndices","Nat"),("numMotives","Nat"),("numMinors","Nat"),("k","Bool"),("unsafe","Bool")]
  Souffle.writeDecl .RecValRule #[("declName", "Name"),("ctorName","Name")] #[("numFields", "Nat"), ("rhs","Hash")]
  h.putStrLn ""

  -- Expr
  Souffle.writeDecl .ExprBVar   #[("exprId", "Hash")] #[("bvar", "Nat")]
  Souffle.writeDecl .ExprFVar   #[("exprId", "Hash")] #[("fvar", "FVarId")]
  Souffle.writeDecl .ExprMVar   #[("exprId", "Hash")] #[("mvar", "MVarId")]
  Souffle.writeDecl .ExprSort   #[("exprId", "Hash")] #[("u", "String")]
  Souffle.writeDecl .ExprConst  #[("exprId", "Hash")] #[("declName","Name")]
  Souffle.writeDecl .ExprApp    #[("exprId", "Hash")] #[("fnExprId","Hash"),("argExprId","Hash")]
  Souffle.writeDecl .ExprLam    #[("exprId", "Hash")] #[("binderName", "Name"),("binderType","Hash"),("bodyExprId","Hash")]
  Souffle.writeDecl .ExprForall #[("exprId", "Hash")] #[("binderName","Name"),("bodyExprId","Hash"),("binderInfo","BinderInfo")]
  Souffle.writeDecl .ExprLet    #[("exprId", "Hash")] #[("declName","Name"),("typeExprId","Hash"),("valueExprId","Hash"),("bodyExprId","Hash"),("nonDep","Bool")]
  Souffle.writeDecl .ExprLit    #[("exprId", "Hash")] #[("literal","LitType")]
  Souffle.writeDecl .ExprProj   #[("exprId", "Hash")] #[("typeName","Name"),("idx","Nat"),("structExprId","Hash")]
  Souffle.writeDecl .ExprMData  #[("exprId", "Hash")] #[("expr","Hash")]
  Souffle.writeDecl .ExprMDataKVEntry #[("exprId", "Hash"),("key","String")] #[("value","String")]


/-
If you declare the .input for a relation, Souffle expects the .facts file to
exist. So we force the creation of all .facts files.

TODO: avoid hardcoding duplicating all cases
-/
def initFacts : RelationsM Unit := do
  let _ ← factHandle .Unreach
  let _ ← factHandle .ArgErased
  let _ ← factHandle .ArgFVar
  let _ ← factHandle .ArgType
  let _ ← factHandle .Decl
  let _ ← factHandle .DeclParam
  let _ ← factHandle .DeclModule
  let _ ← factHandle .Let
  let _ ← factHandle .LetValueLit
  let _ ← factHandle .LetValueErased
  let _ ← factHandle .LetValueProj
  let _ ← factHandle .LetValueConst
  let _ ← factHandle .LetValueConstArg
  let _ ← factHandle .LetValueFVar
  let _ ← factHandle .LetValueFVarArg
  let _ ← factHandle .Fun
  let _ ← factHandle .FunParam
  let _ ← factHandle .Jp
  let _ ← factHandle .JpParam
  let _ ← factHandle .Jmp
  let _ ← factHandle .JmpArg
  let _ ← factHandle .Cases
  let _ ← factHandle .Alt
  let _ ← factHandle .AltParam
  let _ ← factHandle .AltDefault
  let _ ← factHandle .Return
  let _ ← factHandle .Unreach
  let _ ← factHandle .Module
  let _ ← factHandle .ModuleImport

  let _ ← factHandle .InductiveVal
  let _ ← factHandle .ConstructorVal
  let _ ← factHandle .DefinitionVal
  let _ ← factHandle .OpaqueVal
  let _ ← factHandle .AxiomVal
  let _ ← factHandle .TheoremVal
  let _ ← factHandle .QuotVal
  let _ ← factHandle .RecVal
  let _ ← factHandle .RecValRule
  let _ ← factHandle .ExprBVar
  let _ ← factHandle .ExprFVar
  let _ ← factHandle .ExprMVar
  let _ ← factHandle .ExprSort
  let _ ← factHandle .ExprConst
  let _ ← factHandle .ExprApp
  let _ ← factHandle .ExprLam
  let _ ← factHandle .ExprForall
  let _ ← factHandle .ExprLet
  let _ ← factHandle .ExprLit
  let _ ← factHandle .ExprProj
  let _ ← factHandle .ExprMData
  let _ ← factHandle .ExprMDataKVEntry

protected def escape (str: String) : String := str.replace "\n" "\\n"

/-
Base helper to emit relations
-/
protected def writeFact [ToString α] (rel: Relation) (fields: Array α) : RelationsM Unit := do
  let line := fields.foldl (init := "")
    (fun line field => line ++ (if line.length == 0 then s!"{field}" else s!"\t{field}"))
  (← factHandle rel).putStrLn line

-- def toStr [ToString α] (a : Array α) : String := toString a

-- #check toStr #[hash "a", Name.anonymous, 1]
-- #check toStr #[Name.anonymous, 1, hash "a"]
-- #check toStr #[1, hash "a", Name.anonymous]

instance : ToString BinderInfo where
  toString
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

protected def emitExpr (expr: Expr) : RelationsM Unit := do
  let exprId := toString <| hash expr
  match expr with
  | .bvar bvar => Souffle.writeFact .ExprBVar #[exprId, toString bvar]
  | .fvar fvar => Souffle.writeFact .ExprFVar #[exprId, toString fvar.name]
  | .mvar mvar => Souffle.writeFact .ExprMVar #[exprId, toString mvar.name]
  | .sort u =>    Souffle.writeFact .ExprSort #[exprId, toString u.toNat] -- TODO HERE
  | .const declName us => Souffle.writeFact .ExprConst #[exprId, toString declName] -- TODO HERE
  | .app fs arg =>
    Souffle.writeFact .ExprApp #[exprId, toString <| hash fs, toString <| hash arg]
    Souffle.emitExpr fs
    Souffle.emitExpr arg
  | .lam     bn bt body bi =>
    Souffle.writeFact .ExprLam #[exprId, toString bn, toString <| hash bt, toString <| hash body, toString bi]
    Souffle.emitExpr bt
    Souffle.emitExpr body
  | .forallE bn bt body bi =>
    Souffle.writeFact .ExprForall #[exprId, toString bn, toString <| hash bt, toString <| hash body, toString bi]
    Souffle.emitExpr bt
    Souffle.emitExpr body
  | .letE dn t v body nonDep =>
    Souffle.writeFact .ExprLet #[exprId, toString dn, toString <| hash t, toString <| hash v, toString <| hash body,toString nonDep]
    Souffle.emitExpr t
    Souffle.emitExpr v
    Souffle.emitExpr body
  | .lit (.natVal val) => Souffle.writeFact .ExprLit #[exprId, Souffle.escape <| toString val]
  | .lit (.strVal val) => Souffle.writeFact .ExprLit #[exprId, Souffle.escape <| toString val]
  | .proj typeName idx struct =>
    Souffle.writeFact .ExprProj #[toString <| hash expr, toString typeName, toString idx, toString <| hash struct]
    Souffle.emitExpr struct
  | .mdata data dataExpr =>
    Souffle.writeFact .ExprMData #[exprId, toString <| hash dataExpr]
    for (name, value) in data do
      Souffle.writeFact .ExprMDataKVEntry #[exprId, toString name, Souffle.escape <| toString value]
    Souffle.emitExpr dataExpr

protected def emitArg (arg: Arg) : RelationsM String := do
  let argId := toString <| hash arg
  match arg with
  | .erased =>
    Souffle.writeFact .ArgErased #[argId]
  | .fvar fvarId =>
    Souffle.writeFact .ArgFVar #[argId, toString fvarId.name]
  | .type type =>
    let typeId := toString <| hash type
    Souffle.writeFact .ArgType #[argId, typeId]
  pure argId

-- protected def emitParams (param: Param) : RelationsM String := do
--   let paramId := toString <| hash param
--   let typeId := toString <| hash param.type
--   Souffle.writeFact .Param #[paramId, toString param.fvarId.name, toString param.binderName, typeId]
--   pure paramId

protected def emitLetValue (decl: Decl) (letCode: Code) (letVal: LetValue) : RelationsM Unit := do
  let declId := toString decl.name
  let letCodeId := toString <| hash letCode
  match letVal with
  | .value (.strVal litVal) =>
    Souffle.writeFact .LetValueLit #[declId, letCodeId, "StrVal", Souffle.escape litVal]
  | .value (.natVal natVal) =>
    Souffle.writeFact .LetValueLit #[declId, letCodeId, "NatVal", toString natVal]
  | .erased =>
    Souffle.writeFact .LetValueErased #[declId, letCodeId]
  | .proj typeName idx struct =>
    Souffle.writeFact .LetValueProj #[declId, letCodeId, toString typeName, toString idx, toString struct.name]
  | .const declName us args =>
    Souffle.writeFact .LetValueConst #[declId, letCodeId, toString declName]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact .LetValueConstArg #[declId, letCodeId, toString i, argId]
  | .fvar fvarId args =>
    Souffle.writeFact .LetValueFVar #[declId, letCodeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact .LetValueFVarArg #[declId, letCodeId, toString i, argId]

protected partial def emitCode (decl: Decl) (code : Code) : RelationsM Unit := do
  let declId := decl.name.toString
  let codeId := toString <| hash code
  match code with

  | .let ⟨fvarId, binderName, type, value⟩ next =>
    let nextId := toString <| hash next
    let typeId := toString <| hash type
    Souffle.writeFact .Let #[declId, codeId, toString fvarId.name, toString binderName, typeId, nextId]
    Souffle.emitLetValue decl code value
    Souffle.emitCode decl next

  | .fun ⟨fvarId, binderName, params, type, value⟩ next =>
    emitFunOrJp declId codeId fvarId binderName params type value next .Fun .FunParam

  | .jp ⟨fvarId, binderName, params, type, value⟩ next =>
    emitFunOrJp declId codeId fvarId binderName params type value next .Jp .JpParam

  | .jmp fvarId args =>
    Souffle.writeFact .Jmp #[declId, codeId, toString fvarId.name]
    for i in [:args.size] do
      let argId ← Souffle.emitArg args[i]!
      Souffle.writeFact .JmpArg #[declId, codeId, toString i, argId]

  | .cases ⟨typeName, resultType, disc, alts⟩ => do
    let resultTypeId := toString <| hash resultType
    Souffle.writeFact .Cases #[declId, codeId, toString typeName, resultTypeId, toString disc.name]
    for altIdx in [:alts.size] do
      let alt := alts[altIdx]!
      emitAlt declId codeId altIdx alt
  | .return fvarId =>
    Souffle.writeFact .Return #[declId, codeId, fvarId.name.toString]
  | .unreach type =>
    let typeId := toString <| hash type
    Souffle.writeFact .Unreach #[declId, codeId, typeId]
where
  emitAlt (declId: String) (casesCodeId : String) (altIdx: Nat) (alt: AltCore Code) : RelationsM Unit := do
    match alt with
    | .alt ctorName params code =>
      let nextId := toString <| hash code
      Souffle.writeFact .Alt #[declId, casesCodeId, toString altIdx, toString ctorName, nextId]
      for paramIdx in [:params.size] do
        let param := params[paramIdx]!
        let paramId := toString <| hash param
        let typeId := toString <| hash param.type
        Souffle.writeFact .AltParam #[declId, casesCodeId, toString altIdx, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
      Souffle.emitCode decl code
    | .default next =>
      let nextId := toString <| hash code
      Souffle.writeFact .AltDefault #[declId, casesCodeId, toString altIdx, nextId]
      Souffle.emitCode decl next

  emitFunOrJp (declId: String) (codeId: String) (fvarId: FVarId) (binderName: Name) (params: Array Param) (type: Expr) (value: Code) (next: Code) (rel: Relation) (paramRel: Relation): RelationsM Unit := do
    let typeId := toString <| hash type
    let valueId := toString <| hash value
    let nextId := toString <| hash next
    Souffle.writeFact rel #[declId, codeId, toString fvarId.name, toString binderName, typeId, valueId, nextId]
    for paramIdx in [:params.size] do
      let param := params[paramIdx]!
      let typeId := toString <| hash param.type
      Souffle.writeFact paramRel #[declId, codeId, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
    Souffle.emitCode decl value
    Souffle.emitCode decl next

protected def emitDecl (decl : Decl) : RelationsM Unit := do
  let declId := decl.name.toString
  let typeId := toString <| hash decl.type
  -- Write Decl
  Souffle.writeFact .Decl #[declId, typeId]
  -- write a DeclModule fact only if there is a module for the given Decl
  if let .some modIdx := (← getEnv).getModuleIdxFor? decl.name then
    Souffle.writeFact .DeclModule #[declId, toString modIdx]
  -- Write DeclParam's
  for paramIdx in [:decl.params.size] do
    let param := decl.params[paramIdx]!
    Souffle.writeFact .DeclParam #[declId, toString paramIdx, toString param.fvarId.name, toString param.binderName, typeId]
  Souffle.emitCode decl decl.value

protected def emitModule (modName: Name) (modIdx: Nat) (modData: ModuleData) : RelationsM Unit := do
  Souffle.writeFact .Module #[modName.toString, toString modIdx]
  for imp in modData.imports do
    Souffle.writeFact .ModuleImport #[modName.toString, imp.module.toString]

instance : ToString DefinitionSafety where
  toString
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

instance : ToString QuotKind where
  toString
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

protected def emitConstantInfo (ci: ConstantInfo) : RelationsM Unit := do
  match ci with
  | .inductInfo val =>
    Souffle.writeFact .InductiveVal
      #[toString val.name, toString <| hash val.type, toString val.numParams, toString val.numIndices, toString val.isRec, toString val.isUnsafe, toString val.isReflexive, toString val.isNested]
    Souffle.emitExpr val.type
  | .ctorInfo val =>
    Souffle.writeFact .ConstructorVal
      #[toString val.name, toString <| hash val.type, toString val.induct, toString val.cidx, toString val.numParams, toString val.numFields, toString val.isUnsafe]
    Souffle.emitExpr val.type
  | .axiomInfo val =>
    Souffle.writeFact .AxiomVal
      #[toString val.name, toString <| hash val.type, toString val.isUnsafe]
    Souffle.emitExpr val.type
  | .defnInfo val =>
    Souffle.writeFact .DefinitionVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, "", toString val.safety]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .thmInfo val =>
    Souffle.writeFact .TheoremVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, ""]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .opaqueInfo val =>
    Souffle.writeFact .OpaqueVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, toString val.isUnsafe]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .quotInfo val =>
    Souffle.writeFact .QuotVal
      #[toString val.name, toString <| hash val.type, toString val.kind]
    Souffle.emitExpr val.type
  | .recInfo val => do
    Souffle.writeFact .RecVal
      #[toString val.name, toString <| hash val.type, toString val.numParams, toString val.numIndices, toString val.numMotives, toString val.numMinors, toString val.k, toString val.isUnsafe]
    for rule in val.rules do
      Souffle.writeFact .RecValRule
        #[toString val.name, toString rule.ctor, toString rule.nfields, toString <| hash rule.rhs]
    Souffle.emitExpr val.type

def runConstantsGlobally (action: Name → ConstantInfo → RelationsM Unit) : RelationsM Unit := do
  let env ← getEnv
  env.constants.forM action

def emitNamespace (ns: Name) : RelationsM Unit :=
  Souffle.writeFact .Namespace #[toString ns]

def runNamespacesGlobally (action: Name → RelationsM Unit) : RelationsM Unit := do
  (← getEnv).getNamespaceSet.forM action

def runModulesGlobally (action: Name → Nat → ModuleData → RelationsM Unit) : RelationsM Unit := do
  let env ← getEnv
  for modName in env.allImportedModuleNames do
    let .some modIdx := env.getModuleIdx? modName | panic! "Unknown module name!"
    let .some modData := env.header.moduleData.get? modIdx | panic! "Unknown module index!"
    action modName modIdx modData

def runDeclsGlobally (action: Decl → RelationsM Unit) : RelationsM Unit := do
  let ext := getExt Phase.base
  let env ← getEnv
  for modIdx in [:env.allImportedModuleNames.size] do
    let decls := ext.getModuleEntries env modIdx
    for decl in decls do
      action decl

/-
Main entrypoint to emit relations for a Decl.
-/
def emitRelations : CoreM Unit := do
  go |>.run' {}
where
  go : RelationsM Unit := do
    initDecls -- init ./dl/LCNF.dl
    initFacts -- init ./facts/*.facts
    runNamespacesGlobally emitNamespace
    runConstantsGlobally fun _ ci => Souffle.emitConstantInfo ci
    runModulesGlobally Souffle.emitModule
    runDeclsGlobally Souffle.emitDecl
