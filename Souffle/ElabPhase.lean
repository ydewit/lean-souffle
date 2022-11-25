import Lean

import Souffle.Basic
import Souffle.CommonPhase

open Lean Meta Compiler LCNF

namespace Souffle

inductive ConstantRel
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

def ConstantRel.toString : ConstantRel -> String
-- | group => "ConstantInfo"
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

instance : ToString ConstantRel := ⟨ ConstantRel.toString ⟩

instance : ToString BinderInfo where
  toString
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

protected def emitExpr (expr: Expr) : RelationsM Unit := do
  let exprId := toString <| hash expr
  match expr with
  | .bvar bvar =>
    Souffle.writeFact ConstantRel.ExprBVar
      #[exprId, toString bvar]
  | .fvar fvar =>
    Souffle.writeFact ConstantRel.ExprFVar
      #[exprId, toString fvar.name]
  | .mvar mvar =>
    Souffle.writeFact ConstantRel.ExprMVar
      #[exprId, toString mvar.name]
  | .sort u =>
    Souffle.writeFact ConstantRel.ExprSort
      #[exprId, toString u.toNat] -- TODO HERE
  | .const declName us =>
    Souffle.writeFact ConstantRel.ExprConst
      #[exprId, toString declName] -- TODO HERE
  | .app fs arg =>
    Souffle.writeFact ConstantRel.ExprApp
      #[exprId, toString <| hash fs, toString <| hash arg]
    Souffle.emitExpr fs
    Souffle.emitExpr arg
  | .lam     bn bt body bi =>
    Souffle.writeFact ConstantRel.ExprLam
      #[exprId, toString bn, toString <| hash bt, toString <| hash body, toString bi]
    Souffle.emitExpr bt
    Souffle.emitExpr body
  | .forallE bn bt body bi =>
    Souffle.writeFact ConstantRel.ExprForall
      #[exprId, toString bn, toString <| hash bt, toString <| hash body, toString bi]
    Souffle.emitExpr bt
    Souffle.emitExpr body
  | .letE dn t v body nonDep =>
    Souffle.writeFact ConstantRel.ExprLet
      #[exprId, toString dn, toString <| hash t, toString <| hash v, toString <| hash body,toString nonDep]
    Souffle.emitExpr t
    Souffle.emitExpr v
    Souffle.emitExpr body
  | .lit (.natVal val) =>
    Souffle.writeFact ConstantRel.ExprLit
      #[exprId, Souffle.escape <| toString val]
  | .lit (.strVal val) =>
    Souffle.writeFact ConstantRel.ExprLit
      #[exprId, Souffle.escape <| toString val]
  | .proj typeName idx struct =>
    Souffle.writeFact ConstantRel.ExprProj
      #[toString <| hash expr, toString typeName, toString idx, toString <| hash struct]
    Souffle.emitExpr struct
  | .mdata data dataExpr =>
    Souffle.writeFact ConstantRel.ExprMData
      #[exprId, toString <| hash dataExpr]
    for (name, value) in data do
      Souffle.writeFact ConstantRel.ExprMDataKVEntry
        #[exprId, toString name, Souffle.escape <| toString value]
    Souffle.emitExpr dataExpr

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

protected def runConstantsGlobally (action: Name → ConstantInfo → RelationsM Unit) : RelationsM Unit := do
  let env ← getEnv
  env.constants.forM action

protected def emitConstantInfo (_: Name) (ci: ConstantInfo): RelationsM Unit := do
  match ci with
  | .inductInfo val =>
    Souffle.writeFact ConstantRel.InductiveVal
      #[toString val.name, toString <| hash val.type, toString val.numParams, toString val.numIndices, toString val.isRec, toString val.isUnsafe, toString val.isReflexive, toString val.isNested]
    Souffle.emitExpr val.type
  | .ctorInfo val =>
    Souffle.writeFact ConstantRel.ConstructorVal
      #[toString val.name, toString <| hash val.type, toString val.induct, toString val.cidx, toString val.numParams, toString val.numFields, toString val.isUnsafe]
    Souffle.emitExpr val.type
  | .axiomInfo val =>
    Souffle.writeFact ConstantRel.AxiomVal
      #[toString val.name, toString <| hash val.type, toString val.isUnsafe]
    Souffle.emitExpr val.type
  | .defnInfo val =>
    Souffle.writeFact ConstantRel.DefinitionVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, "", toString val.safety]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .thmInfo val =>
    Souffle.writeFact ConstantRel.TheoremVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, ""]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .opaqueInfo val =>
    Souffle.writeFact ConstantRel.OpaqueVal
      #[toString val.name, toString <| hash val.type, toString <| hash val.value, toString val.isUnsafe]
    Souffle.emitExpr val.type
    Souffle.emitExpr val.value
  | .quotInfo val =>
    Souffle.writeFact ConstantRel.QuotVal
      #[toString val.name, toString <| hash val.type, toString val.kind]
    Souffle.emitExpr val.type
  | .recInfo val => do
    Souffle.writeFact ConstantRel.RecVal
      #[toString val.name, toString <| hash val.type, toString val.numParams, toString val.numIndices, toString val.numMotives, toString val.numMinors, toString val.k, toString val.isUnsafe]
    for rule in val.rules do
      Souffle.writeFact ConstantRel.RecValRule
        #[toString val.name, toString rule.ctor, toString rule.nfields, toString <| hash rule.rhs]
    Souffle.emitExpr val.type

/-
Main entrypoint to emit relations for a ConstantInfo
-/
protected def emitElabTypes: RelationsM Unit := do
  let h ← declsHandle
  h.putStrLn ".type DefinitionSafety <: symbol // = unsafe | safe | partial"
  h.putStrLn ".type QuotKind <: symbol // = type | ctor | lift | ind"
  h.putStrLn ".type BinderInfo <: symbol // = default | implicit | strictImplicit | instImplicit"
  h.putStrLn ""

  -- ConstantInfo
  Souffle.writeDecl ConstantRel.InductiveVal #[("declName", "Name")] #[("type", "Hash"), ( "numParams", "Nat"), ("numIndices", "Nat"), ("rec", "Bool"),("unsafe","Bool"),("reflexive","Bool"),("nested","Bool")]
  Souffle.writeDecl ConstantRel.ConstructorVal #[("declName", "Name")] #[("type", "Hash"), ( "inductName", "Name"), ("cidx", "Nat"), ("numParams", "Nat"), ("numFields", "Nat"), ("unsafe", "Bool")]
  Souffle.writeDecl ConstantRel.DefinitionVal #[("declName", "Name")] #[("type", "Hash"), ( "value", "Hash"), ("hints", "String"), ("safety", "DefinitionSafety")]
  Souffle.writeDecl ConstantRel.OpaqueVal #[("declName", "Name")] #[("type", "Hash"), ( "value", "Hash"), ("unsafe","Bool")]
  Souffle.writeDecl ConstantRel.AxiomVal #[("declName", "Name")] #[("type", "Hash"), ("unsafe","Bool")]
  Souffle.writeDecl ConstantRel.TheoremVal #[("declName", "Name")] #[("type", "Hash"), ("value","Hash")]
  Souffle.writeDecl ConstantRel.QuotVal #[("declName", "Name")] #[("type", "Hash"), ("kind","QuotKind")]
  Souffle.writeDecl ConstantRel.RecVal #[("declName", "Name")] #[("type", "Hash"), ("numParams","Nat"),("numIndices","Nat"),("numMotives","Nat"),("numMinors","Nat"),("k","Bool"),("unsafe","Bool")]
  Souffle.writeDecl ConstantRel.RecValRule #[("declName", "Name"),("ctorName","Name")] #[("numFields", "Nat"), ("rhs","Hash")]
  h.putStrLn ""

  -- Expr
  Souffle.writeDecl ConstantRel.ExprBVar   #[("exprId", "Hash")] #[("bvar", "Nat")]
  Souffle.writeDecl ConstantRel.ExprFVar   #[("exprId", "Hash")] #[("fvar", "FVarId")]
  Souffle.writeDecl ConstantRel.ExprMVar   #[("exprId", "Hash")] #[("mvar", "MVarId")]
  Souffle.writeDecl ConstantRel.ExprSort   #[("exprId", "Hash")] #[("u", "String")]
  Souffle.writeDecl ConstantRel.ExprConst  #[("exprId", "Hash")] #[("declName","Name")]
  Souffle.writeDecl ConstantRel.ExprApp    #[("exprId", "Hash")] #[("fnExprId","Hash"),("argExprId","Hash")]
  Souffle.writeDecl ConstantRel.ExprLam    #[("exprId", "Hash")] #[("binderName", "Name"),("binderType","Hash"),("bodyExprId","Hash")]
  Souffle.writeDecl ConstantRel.ExprForall #[("exprId", "Hash")] #[("binderName","Name"),("bodyExprId","Hash"),("binderInfo","BinderInfo")]
  Souffle.writeDecl ConstantRel.ExprLet    #[("exprId", "Hash")] #[("declName","Name"),("typeExprId","Hash"),("valueExprId","Hash"),("bodyExprId","Hash"),("nonDep","Bool")]
  Souffle.writeDecl ConstantRel.ExprLit    #[("exprId", "Hash")] #[("literal","LitType")]
  Souffle.writeDecl ConstantRel.ExprProj   #[("exprId", "Hash")] #[("typeName","Name"),("idx","Nat"),("structExprId","Hash")]
  Souffle.writeDecl ConstantRel.ExprMData  #[("exprId", "Hash")] #[("expr","Hash")]
  Souffle.writeDecl ConstantRel.ExprMDataKVEntry #[("exprId", "Hash"),("key","String")] #[("value","String")]
  h.putStrLn ""
  h.flush

protected def emitElabFacts : RelationsM Unit := do
  Souffle.runConstantsGlobally Souffle.emitConstantInfo

  -- initFacts : RelationsM Unit := do
  --   let _ ← factsHandle ConstantRel.InductiveVal
  --   let _ ← factsHandle ConstantRel.ConstructorVal
  --   let _ ← factsHandle ConstantRel.DefinitionVal
  --   let _ ← factsHandle ConstantRel.OpaqueVal
  --   let _ ← factsHandle ConstantRel.AxiomVal
  --   let _ ← factsHandle ConstantRel.TheoremVal
  --   let _ ← factsHandle ConstantRel.QuotVal
  --   let _ ← factsHandle ConstantRel.RecVal
  --   let _ ← factsHandle ConstantRel.RecValRule
  --   let _ ← factsHandle ConstantRel.ExprBVar
  --   let _ ← factsHandle ConstantRel.ExprFVar
  --   let _ ← factsHandle ConstantRel.ExprMVar
  --   let _ ← factsHandle ConstantRel.ExprSort
  --   let _ ← factsHandle ConstantRel.ExprConst
  --   let _ ← factsHandle ConstantRel.ExprApp
  --   let _ ← factsHandle ConstantRel.ExprLam
  --   let _ ← factsHandle ConstantRel.ExprForall
  --   let _ ← factsHandle ConstantRel.ExprLet
  --   let _ ← factsHandle ConstantRel.ExprLit
  --   let _ ← factsHandle ConstantRel.ExprProj
  --   let _ ← factsHandle ConstantRel.ExprMData
  --   let _ ← factsHandle ConstantRel.ExprMDataKVEntry
