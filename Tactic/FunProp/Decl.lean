/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Init

/-!
## `funProp` environment extension that stores all registered function properties
-/

public meta section


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/--
Definition of `FunPropDecl` / `FunPropDecl` 的定义

English:
structure FunPropDecl
  parameters: where
  axioms and operations (3):
    - funPropName : Name
    - path : Array DiscrTree.Key
    - funArgId : Nat

中文:
结构 FunPropDecl
  参数: where
  公理与运算 (3 个):
    - funPropName : Name
    - path : 数组 DiscrTree.Key
    - funArgId : 自然数
-/
structure FunPropDecl where
  /-- function transformation name -/
  funPropName : Name
  /-- path for discrimination tree -/
  path : Array DiscrTree.Key
  /-- argument index of a function this function property talks about.
  For example, this would be 4 for `@Continuous α β _ _ f` -/
  funArgId : Nat
  deriving Inhabited, BEq

/--
Definition of `FunPropDecls` / `FunPropDecls` 的定义

English:
structure FunPropDecls
  parameters: where
  axioms and operations (1):
    - decls : DiscrTree FunPropDecl  [default: {}]

中文:
结构 FunPropDecls
  参数: where
  公理与运算 (1 个):
    - decls : DiscrTree FunPropDecl  [默认: {}]
-/
structure FunPropDecls where
  /-- Discrimination tree for function properties. -/
  decls : DiscrTree FunPropDecl := {}
  deriving Inhabited

set_option linter.style.docString.empty false in
/--
Definition of `FunPropDeclsExt` / `FunPropDeclsExt` 的定义

English:
abbreviation FunPropDeclsExt
  body: SimpleScopedEnvExtension FunPropDecl FunPropDecls

中文:
缩写 FunPropDeclsExt
  定义体: SimpleScopedEnvExtension FunPropDecl FunPropDecls

Depends on / 依赖: FunPropDecl, FunPropDecls, SimpleScopedEnvExtension
-/
abbrev FunPropDeclsExt := SimpleScopedEnvExtension FunPropDecl FunPropDecls

/-- Extension storing function properties tracked and used by the `fun_prop` attribute and tactic,
including, for example, `Continuous`, `Measurable`, `Differentiable`, etc. -/
initialize funPropDeclsExt : FunPropDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e =>
      {d with decls := d.decls.insertKeyValue e.path e}
  }

/--
Definition of `addFunPropDecl` / `addFunPropDecl` 的定义

English:
definition addFunPropDecl
  signature: (declName : Name)
  body: do

  let info ← getConstInfo declName

  let (xs, bi, b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fun_prop declaration, has to be `Prop`-valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  le

中文:
定义 addFunPropDecl
  签名: (declName : Name)
  定义体: do

  let info ← getConstInfo declName

  let (xs, bi, b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fun_prop declaration, has to be `Prop`-valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  le
-/
def addFunPropDecl (declName : Name) : MetaM Unit := do

  let info ← getConstInfo declName

  let (xs, bi, b) ← forallMetaTelescope info.type

  if ¬b.isProp then
    throwError "invalid fun_prop declaration, has to be `Prop`-valued function"

  let lvls := info.levelParams.map (fun l => Level.param l)
  let e := mkAppN (.const declName lvls) xs
  let path ← DiscrTree.mkPath e

  -- find the argument position of the function `f` in `P f`
  let mut some funArgId ← (xs.zip bi).findIdxM? fun (x,bi) => do
    if (← inferType x).isForall && bi.isExplicit then
      return true
    else
      return false
    | throwError "invalid fun_prop declaration, can't find argument of type `α -> β`"

  let decl : FunPropDecl := {
    funPropName := declName
    path := path
    funArgId := funArgId
  }

  modifyEnv fun env => funPropDeclsExt.addEntry env decl

  trace[Meta.Tactic.fun_prop.attr]
    "added new function property `{declName}`\nlook up pattern is `{path}`"


/--
Definition of `getFunProp?` / `getFunProp?` 的定义

English:
definition getFunProp?
  signature: (e : Expr)
  body: do
  let ext := funPropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e (← read)

  if h : decls.size = 0 then
    return none
  else
    if decls.size > 1 then
      throwError "fun_prop bug: expression {← ppExpr e} matches multiple function properties\n\
        {decls.map (fun d =

中文:
定义 getFunProp?
  签名: (e : Expr)
  定义体: do
  let ext := funPropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e (← read)

  if h : decls.size = 0 then
    return none
  else
    if decls.size > 1 then
      throwError "fun_prop bug: expression {← ppExpr e} matches multiple function properties\n\
        {decls.map (fun d =
-/
def getFunProp? (e : Expr) : MetaM (Option (FunPropDecl × Expr)) := do
  let ext := funPropDeclsExt.getState (← getEnv)

  let decls ← ext.decls.getMatch e (← read)

  if h : decls.size = 0 then
    return none
  else
    if decls.size > 1 then
      throwError "fun_prop bug: expression {← ppExpr e} matches multiple function properties\n\
        {decls.map (fun d => d.funPropName)}"

    let decl := decls[0]
    unless decl.funArgId < e.getAppNumArgs do return none
    let f := e.getArg! decl.funArgId

    return (decl,f)

/--
Definition of `isFunProp` / `isFunProp` 的定义

English:
definition isFunProp
  signature: (e : Expr)
  body: do return (← getFunProp? e).isSome

中文:
定义 isFunProp
  签名: (e : Expr)
  定义体: do return (← getFunProp? e).isSome

Depends on / 依赖: getFunProp, isSome, return
-/
def isFunProp (e : Expr) : MetaM Bool := do return (← getFunProp? e).isSome

/--
Definition of `isFunPropGoal` / `isFunPropGoal` 的定义

English:
definition isFunPropGoal
  signature: (e : Expr)
  body: do
  forallTelescope e fun _ b =>
  return (← getFunProp? b).isSome

中文:
定义 isFunPropGoal
  签名: (e : Expr)
  定义体: do
  forallTelescope e fun _ b =>
  return (← getFunProp? b).isSome
-/
def isFunPropGoal (e : Expr) : MetaM Bool := do
  forallTelescope e fun _ b =>
  return (← getFunProp? b).isSome

/--
Definition of `getFunPropDecl?` / `getFunPropDecl?` 的定义

English:
definition getFunPropDecl?
  signature: (e : Expr)
  body: do
  match ← getFunProp? e with
  | some (decl, _) => return decl
  | none => return none

中文:
定义 getFunPropDecl?
  签名: (e : Expr)
  定义体: do
  match ← getFunProp? e with
  | some (decl, _) => return decl
  | none => return none
-/
def getFunPropDecl? (e : Expr) : MetaM (Option FunPropDecl) := do
  match ← getFunProp? e with
  | some (decl, _) => return decl
  | none => return none


/--
Definition of `getFunPropFun?` / `getFunPropFun?` 的定义

English:
definition getFunPropFun?
  signature: (e : Expr)
  body: do
  match ← getFunProp? e with
  | some (_, f) => return f
  | none => return none

中文:
定义 getFunPropFun?
  签名: (e : Expr)
  定义体: do
  match ← getFunProp? e with
  | some (_, f) => return f
  | none => return none
-/
def getFunPropFun? (e : Expr) : MetaM (Option Expr) := do
  match ← getFunProp? e with
  | some (_, f) => return f
  | none => return none


open Elab Term in
/--
Definition of `tacticToDischarge` / `tacticToDischarge` 的定义

English:
definition tacticToDischarge
  signature: (tacticCode : TSyntax `tactic)
  body: fun e =>
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => do pure s!"discharging: {← ppExpr e}") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `funProp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        instantiateMVarDeclMVars mvar.mvarId!

        let _ ←
          w

中文:
定义 tacticToDischarge
  签名: (tacticCode : TSyntax `tactic)
  定义体: fun e =>
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => do pure s!"discharging: {← ppExpr e}") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `funProp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        instantiateMVarDeclMVars mvar.mvarId!

        let _ ←
          w
-/
def tacticToDischarge (tacticCode : TSyntax `tactic) : Expr -> MetaM (Option Expr) := fun e =>
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => do pure s!"discharging: {← ppExpr e}") do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `funProp.discharger
    let runTac? : TermElabM (Option Expr) :=
      try
        instantiateMVarDeclMVars mvar.mvarId!

        let _ ←
          withSynthesize (postpone := .no) do
            Tactic.run mvar.mvarId! (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)

        let result ← instantiateMVars mvar
        if result.hasExprMVar then
          return none
        else
          return some result
      catch _ =>
        return none
    let (result?, _) ← runTac?.run {} {}

    return result?

end Meta.FunProp

end Mathlib
