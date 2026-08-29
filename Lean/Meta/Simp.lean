/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Gabriel Ebner, Floris van Doorn
-/
module

public import Mathlib.Init
public import Lean.Elab.Tactic.Simp
public import Lean.Meta.DiscrTree

/-!
# Helper functions for using the simplifier.

[TODO] Needs documentation, cleanup, and possibly reunification of `mkSimpContext'` with core.
-/

@[expose] public section

open Lean Elab.Tactic

/--
Definition of `Lean.PHashSet.toList.` / `Lean.PHashSet.toList.` 的定义

English:
definition Lean.PHashSet.toList.{u}
  signature: {α : Type u} [BEq α] [Hashable α] (s : Lean.PHashSet α)
  body: s.1.toList.map (·.1)

中文:
定义 Lean.PHashSet.toList.{u}
  签名: {α : 类型u} [BEq α] [Hashable α] (s : Lean.PHashSet α)
  定义体: s.1.toList.map (·.1)

Depends on / 依赖: toList, toList.map
-/
def Lean.PHashSet.toList.{u} {α : Type u} [BEq α] [Hashable α] (s : Lean.PHashSet α) : List α :=
  s.1.toList.map (·.1)

namespace Lean

namespace Meta.Simp
open Elab.Tactic

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat SimpTheorems
  body: f!"pre:
{s.pre.values.toList}
post:
{s.post.values.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"

中文:
实例 :
  签名: ToFormat SimpTheorems
  定义体: f!"pre:
{s.pre.values.toList}
post:
{s.post.values.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"

Depends on / 依赖: erased, lemmaNames, s.erased.toList.map, s.lemmaNames.toList.map, s.post.values.toList, s.pre.values.toList, s.toUnfold.toList, s.toUnfoldThms.toList, toList, toUnfold, toUnfoldThms, values
-/
instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.values.toList}
post:
{s.post.values.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"

/--
Definition of `Result.ofTrue` / `Result.ofTrue` 的定义

English:
definition Result.ofTrue
  signature: (r : Simp.Result)
  body: if r.expr.isConstOf ``True then
some < > match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

中文:
定义 Result.ofTrue
  签名: (r : Simp.Result)
  定义体: if r.expr.isConstOf ``True then
some < > match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

Depends on / 依赖: True.intro, isConstOf, mkConst, mkOfEqTrue, r.expr.isConstOf, r.proof
-/
def Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
some < > match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

/--
Definition of `getPropHyps` / `getPropHyps` 的定义

English:
definition getPropHyps
  signature: : MetaM (Array FVarId)
  body: do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

中文:
定义 getPropHyps
  签名: : MetaM (Array FVarId)
  定义体: do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result
-/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

end Simp

/--
Definition of `simpTheoremsOfNames` / `simpTheoremsOfNames` 的定义

English:
definition simpTheoremsOfNames
  signature: (lemmas : List Name := []) (simpOnly : Bool := false)
  body: do
  lemmas.foldlM (·.addConst ·)
    (← if simpOnly then
      simpOnlyBuiltins.foldlM (·.addConst ·) {}
    else
      getSimpTheorems)

中文:
定义 simpTheoremsOfNames
  签名: (lemmas : List Name := []) (simpOnly : 布尔 := false)
  定义体: do
  lemmas.foldlM (·.addConst ·)
    (← if simpOnly then
      simpOnlyBuiltins.foldlM (·.addConst ·) {}
    else
      getSimpTheorems)

Depends on / 依赖: simpOnly
-/
def simpTheoremsOfNames (lemmas : List Name := []) (simpOnly : Bool := false) :
    MetaM SimpTheorems := do
  lemmas.foldlM (·.addConst ·)
    (← if simpOnly then
      simpOnlyBuiltins.foldlM (·.addConst ·) {}
    else
      getSimpTheorems)

-- TODO We need to write a `mkSimpContext` in `MetaM`
-- that supports all the bells and whistles in `simp`.
-- It should generalize this, and another partial implementation in `Tactic.Simps.Basic`.

/--
Definition of `Simp.Context.ofNames` / `Simp.Context.ofNames` 的定义

English:
definition Simp.Context.ofNames
  signature: (lemmas : List Name := []) (simpOnly : Bool := false)
  body: do
  Simp.mkContext config
    (simpTheorems := #[← simpTheoremsOfNames lemmas simpOnly])
    (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)

中文:
定义 Simp.Context.ofNames
  签名: (lemmas : List Name := []) (simpOnly : 布尔 := false)
  定义体: do
  Simp.mkContext config
    (simpTheorems := #[← simpTheoremsOfNames lemmas simpOnly])
    (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)

Depends on / 依赖: simpOnly
-/
def Simp.Context.ofNames (lemmas : List Name := []) (simpOnly : Bool := false)
    (config : Simp.Config := {}) : MetaM Simp.Context := do
  Simp.mkContext config
    (simpTheorems := #[← simpTheoremsOfNames lemmas simpOnly])
    (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)

-- adapted from `Lean.Elab.Tactic.mkSimpContext`
/--
Definition of `Simp.Context.ofArgs` / `Simp.Context.ofArgs` 的定义

English:
definition Simp.Context.ofArgs
  signature: (args : TSyntax ``Parser.Tactic.simpArgs) (config : Simp.Config := {})
  body: do
  let simpTheorems ← Meta.getSimpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Simp.mkContext config
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs args (eraseLocal := false) (kind := SimpKind.simp) (simprocs := {}) ctx
  return r.ctx

中文:
定义 Simp.Context.ofArgs
  签名: (args : TSyntax ``Parser.Tactic.simpArgs) (config : Simp.Config := {})
  定义体: do
  let simpTheorems ← Meta.getSimpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Simp.mkContext config
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs args (eraseLocal := false) (kind := SimpKind.simp) (simprocs := {}) ctx
  return r.ctx
-/
def Simp.Context.ofArgs (args : TSyntax ``Parser.Tactic.simpArgs) (config : Simp.Config := {}) :
    TacticM Simp.Context := do
  let simpTheorems ← Meta.getSimpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Simp.mkContext config
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs args (eraseLocal := false) (kind := SimpKind.simp) (simprocs := {}) ctx
  return r.ctx

/--
Definition of `simpOnlyNames` / `simpOnlyNames` 的定义

English:
definition simpOnlyNames
  signature: (lemmas : List Name) (e : Expr) (config : Simp.Config := {})
  body: do
(·.1) < > simp e (← Simp.Context.ofNames lemmas true config)

中文:
定义 simpOnlyNames
  签名: (lemmas : List Name) (e : Expr) (config : Simp.Config := {})
  定义体: do
(·.1) < > simp e (← Simp.Context.ofNames lemmas true config)
-/
def simpOnlyNames (lemmas : List Name) (e : Expr) (config : Simp.Config := {}) :
    MetaM Simp.Result := do
(·.1) < > simp e (← Simp.Context.ofNames lemmas true config)

/--
Definition of `simpType` / `simpType` 的定义

English:
definition simpType
  signature: (S : Expr -> MetaM Simp.Result) (e : Expr) (type? : Option Expr := none)
  body: do
  let type ← type?.getDM (inferType e)
  match ← S type with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'

中文:
定义 simpType
  签名: (S : Expr -> MetaM Simp.Result) (e : Expr) (type? : Option Expr := none)
  定义体: do
  let type ← type?.getDM (inferType e)
  match ← S type with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'
-/
def simpType (S : Expr -> MetaM Simp.Result) (e : Expr) (type? : Option Expr := none) :
    MetaM Expr := do
  let type ← type?.getDM (inferType e)
  match ← S type with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'

/--
Definition of `simpEq` / `simpEq` 的定义

English:
definition simpEq
  signature: (S : Expr -> MetaM Simp.Result) (type pf : Expr)
  body: do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEq

中文:
定义 simpEq
  签名: (S : Expr -> MetaM Simp.Result) (type pf : Expr)
  定义体: do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEq
-/
def simpEq (S : Expr -> MetaM Simp.Result) (type pf : Expr) : MetaM (Expr × Expr) := do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEqTrans (← mkEqSymm lhspf) pf'
    if let some rhspf := rhspf? then
      pf' ← mkEqTrans pf' rhspf
    let type' := mkApp3 (mkConst ``Eq [u]) α lhs' rhs'
    return (← mkForallFVars fvars type', ← mkLambdaFVars fvars pf')

/--
Definition of `SimpTheorems.contains` / `SimpTheorems.contains` 的定义

English:
definition SimpTheorems.contains
  signature: (d : SimpTheorems) (declName : Name)
  body: d.isLemma (.decl declName) || d.isDeclToUnfold declName

中文:
定义 SimpTheorems.contains
  签名: (d : SimpTheorems) (declName : Name)
  定义体: d.isLemma (.decl declName) || d.isDeclToUnfold declName

Depends on / 依赖: d.isDeclToUnfold, d.isLemma, declName, isDeclToUnfold, isLemma
-/
def SimpTheorems.contains (d : SimpTheorems) (declName : Name) :=
  d.isLemma (.decl declName) || d.isDeclToUnfold declName

/--
Definition of `isInSimpSet` / `isInSimpSet` 的定义

English:
definition isInSimpSet
  signature: (simpAttr decl : Name)
  body: do
  let some simpDecl ← getSimpExtension? simpAttr | return false
  return (← simpDecl.getTheorems).contains decl

中文:
定义 isInSimpSet
  签名: (simpAttr decl : Name)
  定义体: do
  let some simpDecl ← getSimpExtension? simpAttr | return false
  return (← simpDecl.getTheorems).contains decl
-/
def isInSimpSet (simpAttr decl : Name) : CoreM Bool := do
  let some simpDecl ← getSimpExtension? simpAttr | return false
  return (← simpDecl.getTheorems).contains decl

/--
Definition of `getAllSimpDecls` / `getAllSimpDecls` 的定义

English:
definition getAllSimpDecls
  signature: (simpAttr : Name)
  body: do
  let some simpDecl ← getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl => some decl
    | _ => none

中文:
定义 getAllSimpDecls
  签名: (simpAttr : Name)
  定义体: do
  let some simpDecl ← getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl => some decl
    | _ => none
-/
def getAllSimpDecls (simpAttr : Name) : CoreM (List Name) := do
  let some simpDecl ← getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl => some decl
    | _ => none

/--
Definition of `getAllSimpAttrs` / `getAllSimpAttrs` 的定义

English:
definition getAllSimpAttrs
  signature: (decl : Name)
  body: do
  let mut simpAttrs := #[]
  for (simpAttr, simpDecl) in ← simpExtensionMapRef.get do
    if (← simpDecl.getTheorems).contains decl then
      simpAttrs := simpAttrs.push simpAttr
  return simpAttrs

中文:
定义 getAllSimpAttrs
  签名: (decl : Name)
  定义体: do
  let mut simpAttrs := #[]
  for (simpAttr, simpDecl) in ← simpExtensionMapRef.get do
    if (← simpDecl.getTheorems).contains decl then
      simpAttrs := simpAttrs.push simpAttr
  return simpAttrs
-/
def getAllSimpAttrs (decl : Name) : CoreM (Array Name) := do
  let mut simpAttrs := #[]
  for (simpAttr, simpDecl) in ← simpExtensionMapRef.get do
    if (← simpDecl.getTheorems).contains decl then
      simpAttrs := simpAttrs.push simpAttr
  return simpAttrs

/-- Run `e` while the entries in `declNames` are erased from the `simp` set, while preserving the
rest of the `simp` configuration.

Performance note: the code in `e` will be run with a new cache (which is discarded at the end of the
function). The original cache is restored when this function returns.
-/
meta def Simp.withoutTheorems {α} (declNames : Array Name) (e : SimpM α) : SimpM α := do
  let mut theorems ← getSimpTheorems
  let mut procs ← getSimprocs
  for name in declNames do
    -- Erase all variants of the theorem, not just the forward post-proc.
    theorems := theorems
.eraseTheorem (.decl name)
.eraseTheorem (.decl name (inv := true))
.eraseTheorem (.decl name (post := false))
.eraseTheorem (.decl name (inv := true) (post := false))
    procs := procs.erase name
  let oldMethods ← getMethods
  let methods := mkMethods #[procs] oldMethods.discharge? oldMethods.wellBehavedDischarge
  -- Preserve the cache, otherwise a deleted theorem might continue firing,
  -- or conversely a failure inside `e` could be propagated outside.
withPreservedCache withSimpTheorems theorems do
    let (x, s) ← e.run (← getContext) (← get) methods
    set s
    return x

end Lean.Meta
