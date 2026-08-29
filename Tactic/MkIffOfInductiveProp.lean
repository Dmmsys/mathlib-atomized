/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, David Renshaw
-/
module

public meta import Lean.Elab.DeclarationRange
public meta import Lean.Meta.Tactic.Cases
public meta import Mathlib.Lean.Meta
public meta import Mathlib.Lean.Name

/-!
# mk_iff_of_inductive_prop

This file defines a command `mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `List.Chain`, it creates a declaration with
the following type:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃ (b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/

public meta section

namespace Mathlib.Tactic.MkIff

open Lean Meta Elab

/--
Definition of `select` / `select` 的定义

English:
definition select
  signature: (m n : Nat) (goal : MVarId)
  body: match m,n with
  | 0, 0 => pure goal
  | 0, (_ + 1) => do
    let [new_goal] ← goal.nthConstructor `left 0 (some 2)
      | throwError "expected only one new goal"
    pure new_goal
  | (m + 1), (n + 1) => do
    let [new_goal] ← goal.nthConstructor `right 1 (some 2)
      | throwError "expected onl

中文:
定义 select
  签名: (m n : 自然数) (goal : MVarId)
  定义体: match m,n with
  | 0, 0 => pure goal
  | 0, (_ + 1) => do
    let [new_goal] ← goal.nthConstructor `left 0 (some 2)
      | throwError "expected only one new goal"
    pure new_goal
  | (m + 1), (n + 1) => do
    let [new_goal] ← goal.nthConstructor `right 1 (some 2)
      | throwError "expected onl
-/
private def select (m n : Nat) (goal : MVarId) : MetaM MVarId :=
  match m,n with
  | 0, 0 => pure goal
  | 0, (_ + 1) => do
    let [new_goal] ← goal.nthConstructor `left 0 (some 2)
      | throwError "expected only one new goal"
    pure new_goal
  | (m + 1), (n + 1) => do
    let [new_goal] ← goal.nthConstructor `right 1 (some 2)
      | throwError "expected only one new goal"
    select m n new_goal
  | _, _ => failure

/--
Definition of `compactRelation` / `compactRelation` 的定义

English:
definition compactRelation
  signature: :
  body: compactRelation bs as_ps
      (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e => e.replaceFVar b a
      let (bs, as_ps', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ => (a, i p)))
      (none :: bs, as_

中文:
定义 compactRelation
  签名: :
  定义体: compactRelation bs as_ps
      (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e => e.replaceFVar b a
      let (bs, as_ps', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ => (a, i p)))
      (none :: bs, as_
-/
partial def compactRelation :
    List Expr -> List (Expr × Expr) -> List (Option Expr) × List (Expr × Expr) × (Expr -> Expr)
| [], as_ps => ([], as_ps, id)
| b::bs, as_ps =>
  match as_ps.span (fun ⟨_, p⟩ => p != b) with
    | (_, []) => -- found nothing in ps equal to b
      let (bs, as_ps', subst) := compactRelation bs as_ps
      (b::bs, as_ps', subst)
    | (ps₁, (a, _) :: ps₂) => -- found one that matches b. Remove it.
      let i := fun e => e.replaceFVar b a
      let (bs, as_ps', subst) :=
        compactRelation (bs.map i) ((ps₁ ++ ps₂).map (fun ⟨a, p⟩ => (a, i p)))
      (none :: bs, as_ps', i ∘ subst)

/--
Definition of `updateLambdaBinderInfoD!` / `updateLambdaBinderInfoD!` 的定义

English:
definition updateLambdaBinderInfoD!
  signature: (e : Expr)
  body: match e with
  | .lam n domain body _ => .lam n domain body .default
  | _ => panic! "lambda expected"

中文:
定义 updateLambdaBinderInfoD!
  签名: (e : Expr)
  定义体: match e with
  | .lam n domain body _ => .lam n domain body .default
  | _ => panic! "lambda expected"
-/
private def updateLambdaBinderInfoD! (e : Expr) : Expr :=
  match e with
  | .lam n domain body _ => .lam n domain body .default
  | _ => panic! "lambda expected"

/--
Definition of `mkExistsList` / `mkExistsList` 的定义

English:
definition mkExistsList
  signature: (args : List Expr) (inner : Expr)
  body: args.foldrM
    (fun arg i:Expr => do
      let t ← inferType arg
      let l := (← inferType t).sortLevel!
      if arg.occurs i || l != Level.zero
        then pure (mkApp2 (.const `Exists [l]) t
          (updateLambdaBinderInfoD! <| ← mkLambdaFVars #[arg] i))
else pure mkApp2 (mkConst `And) t i)

中文:
定义 mkExistsList
  签名: (args : 列表 Expr) (inner : Expr)
  定义体: args.foldrM
    (fun arg i:Expr => do
      let t ← inferType arg
      let l := (← inferType t).sortLevel!
      if arg.occurs i || l != Level.zero
        then pure (mkApp2 (.const `Exists [l]) t
          (updateLambdaBinderInfoD! <| ← mkLambdaFVars #[arg] i))
else pure mkApp2 (mkConst `And) t i)

Depends on / 依赖: Exists, Level.zero, arg.occurs, args.foldrM, foldrM, inferType, mkApp2, mkConst, mkLambdaFVars, occurs, sortLevel, updateLambdaBinderInfoD
-/
def mkExistsList (args : List Expr) (inner : Expr) : MetaM Expr :=
  args.foldrM
    (fun arg i:Expr => do
      let t ← inferType arg
      let l := (← inferType t).sortLevel!
      if arg.occurs i || l != Level.zero
        then pure (mkApp2 (.const `Exists [l]) t
          (updateLambdaBinderInfoD! <| ← mkLambdaFVars #[arg] i))
else pure mkApp2 (mkConst `And) t i)
    inner

/--
Definition of `mkOpList` / `mkOpList` 的定义

English:
definition mkOpList
  signature: (op : Expr) (empty : Expr)

中文:
定义 mkOpList
  签名: (op : Expr) (empty : Expr)
-/
def mkOpList (op : Expr) (empty : Expr) : List Expr -> Expr
  | [] => empty
  | [e] => e
| (e :: es) => mkApp2 op e mkOpList op empty es

/--
Definition of `mkAndList` / `mkAndList` 的定义

English:
definition mkAndList
  signature: : List Expr -> Expr
  body: mkOpList (mkConst `And) (mkConst `True)

中文:
定义 mkAndList
  签名: : 列表 Expr -> Expr
  定义体: mkOpList (mkConst `And) (mkConst `True)

Depends on / 依赖: mkConst, mkOpList
-/
def mkAndList : List Expr -> Expr := mkOpList (mkConst `And) (mkConst `True)

/--
Definition of `mkOrList` / `mkOrList` 的定义

English:
definition mkOrList
  signature: : List Expr -> Expr
  body: mkOpList (mkConst `Or) (mkConst `False)

中文:
定义 mkOrList
  签名: : 列表 Expr -> Expr
  定义体: mkOpList (mkConst `Or) (mkConst `False)

Depends on / 依赖: mkConst, mkOpList
-/
def mkOrList : List Expr -> Expr := mkOpList (mkConst `Or) (mkConst `False)

/--
Definition of `List.init` / `List.init` 的定义

English:
definition List.init
  signature: {α : Type*}

中文:
定义 列表.init
  签名: {α : 类型}
-/
def List.init {α : Type*} : List α -> List α
  | [] => []
  | [_] => []
  | a::l => a::init l

/--
Definition of `Shape` / `Shape` 的定义

English:
structure Shape
  parameters: : Type where
  axioms and operations (2):
    - variablesKept : List Bool
    - neqs : Option Nat

中文:
结构 形状
  参数: : 类型 where
  公理与运算 (2 个):
    - variablesKept : 列表 布尔值
    - neqs : 选项类型 自然数
-/
structure Shape : Type where
  /-- For each forall-bound variable in the type of the constructor, minus
  the "params" that apply to the entire inductive type, this list contains `true`
  if that variable has been kept after `compactRelation`.

  For example, `List.Chain.nil` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a : α}, List.Chain R a []`
  ```
  and the first two variables `α` and `R` are "params", while the `a : α` gets
  eliminated in a `compactRelation`, so `variablesKept = [false]`.

  `List.Chain.cons` has type
  ```lean
    ∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l : List α},
       R a b → List.Chain R b l → List.Chain R a (b :: l)
  ```
  and the `a : α` gets eliminated, so `variablesKept = [false,true,true,true,true]`.
  -/
  variablesKept : List Bool

  /-- The number of equalities, or `none` in the case when we've reduced something
  of the form `p ∧ True` to just `p`.
  -/
  neqs : Option Nat

/--
Definition of `constrToProp` / `constrToProp` 的定义

English:
definition constrToProp
  signature: (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name)
  body: do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
pure ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty => do
    let idxs_inst := ty.getAppArgs.toList.drop params.lengt

中文:
定义 constrToProp
  签名: (univs : 列表 Level) (params : 列表 Expr) (idxs : 列表 Expr) (c : Name)
  定义体: do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
pure ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty => do
    let idxs_inst := ty.getAppArgs.toList.drop params.lengt
-/
def constrToProp (univs : List Level) (params : List Expr) (idxs : List Expr) (c : Name) :
    MetaM (Shape × Expr) := do
  let type := (← getConstInfo c).instantiateTypeLevelParams univs
  let type' ← Meta.forallBoundedTelescope type (params.length) fun fvars ty => do
pure ty.replaceFVars fvars params.toArray
  Meta.forallTelescope type' fun fvars ty => do
    let idxs_inst := ty.getAppArgs.toList.drop params.length
    let (bs, eqs, subst) := compactRelation fvars.toList (idxs.zip idxs_inst)
    let eqs ← eqs.mapM (fun ⟨idx, inst⟩ => do
      let ty ← idx.fvarId!.getType
      let instTy ← inferType inst
      let u := (← inferType ty).sortLevel!
      if ← isDefEq ty instTy
      then pure (mkApp3 (.const `Eq [u]) ty idx inst)
      else pure (mkApp4 (.const `HEq [u]) ty idx instTy inst))
    let (n, r) ← match bs.filterMap id, eqs with
    | [], [] => do
      pure (some 0, (mkConst `True))
    | bs', [] => do
      let t : Expr ← bs'.getLast!.fvarId!.getType
      let l := (← inferType t).sortLevel!
      if l == Level.zero then do
        let r ← mkExistsList (List.init bs') t
        pure (none, subst r)
      else do
        let r ← mkExistsList bs' (mkConst `True)
        pure (some 0, subst r)
    | bs', _ => do
      let r ← mkExistsList bs' (mkAndList eqs)
      pure (some eqs.length, subst r)
    pure (⟨bs.map Option.isSome, n⟩, r)

/--
Definition of `splitThenConstructor` / `splitThenConstructor` 的定义

English:
definition splitThenConstructor
  signature: (mvar : MVarId) (n : Nat)
  body: match n with
| 0 => do
let (subgoals',_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n + 1 => do
let (subgoals,_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tact

中文:
定义 splitThenConstructor
  签名: (mvar : MVarId) (n : 自然数)
  定义体: match n with
| 0 => do
let (subgoals',_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n + 1 => do
let (subgoals,_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tact

Depends on / 依赖: Tactic, Tactic.evalTactic, Tactic.run, Term.TermElabM.run, TermElabM, evalTactic, expected, subgoals, tactic, throwError
-/
def splitThenConstructor (mvar : MVarId) (n : Nat) : MetaM Unit :=
match n with
| 0 => do
let (subgoals',_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  pure ()
| n + 1 => do
let (subgoals,_) ← Term.TermElabM.run Tactic.run mvar do
    Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
  let [sg1, sg2] := subgoals | throwError "expected two subgoals"
let (subgoals',_) ← Term.TermElabM.run Tactic.run sg1 do
    Tactic.evalTactic (← `(tactic| constructor))
  let [] := subgoals' | throwError "expected no subgoals"
  splitThenConstructor sg2 n

/--
Definition of `toCases` / `toCases` 的定义

English:
definition toCases
  signature: (mvar : MVarId) (shape : List Shape)
  body: do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ => do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ => if c then some v else none)
    let mvar'' ← select p (

中文:
定义 toCases
  签名: (mvar : MVarId) (shape : 列表 形状)
  定义体: do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ => do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ => if c then some v else none)
    let mvar'' ← select p (

Depends on / 依赖: List.init, assign, existsi, fields, filterMap, intro1, length, mv.assign, mvar.intro1, mvarId, select, shape.length, shape.zip, splitThenConstructor, subgoal, subgoal.fields, subgoal.mvarId, subgoals, subgoals.size, subgoals.toList
-/
def toCases (mvar : MVarId) (shape : List Shape) : MetaM Unit :=
do
  let ⟨h, mvar'⟩ ← mvar.intro1
  let subgoals ← mvar'.cases h
  let _ ← (shape.zip subgoals.toList).zipIdx.mapM fun ⟨⟨⟨shape, t⟩, subgoal⟩, p⟩ => do
    let vars := subgoal.fields
    let si := (shape.zip vars.toList).filterMap (fun ⟨c,v⟩ => if c then some v else none)
    let mvar'' ← select p (subgoals.size - 1) subgoal.mvarId
    match t with
    | none => do
      let v := vars[shape.length - 1]!
      let mv ← mvar''.existsi (List.init si)
      mv.assign v
    | some n => do
      let mv ← mvar''.existsi si
      splitThenConstructor mv (n - 1)
  pure ()

/--
Definition of `nCasesSum` / `nCasesSum` 的定义

English:
definition nCasesSum
  signature: (n : Nat) (mvar : MVarId) (h : FVarId)
  body: match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2

中文:
定义 nCasesSum
  签名: (n : 自然数) (mvar : MVarId) (h : FVarId)
  定义体: match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2

Depends on / 依赖: Expr.fvar, expected, fields, mvar.cases, mvarId, nCasesSum, sg1.fields, sg1.mvarId, sg2.fields, sg2.mvarId, subgoals, throwError
-/
def nCasesSum (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (List (FVarId × MVarId)) :=
match n with
| 0 => pure [(h, mvar)]
| n' + 1 => do
  let #[sg1, sg2] ← mvar.cases h | throwError "expected two case subgoals"
  let #[Expr.fvar fvar1] ← pure sg1.fields | throwError "expected fvar"
  let #[Expr.fvar fvar2] ← pure sg2.fields | throwError "expected fvar"
  let rest ← nCasesSum n' sg2.mvarId fvar2
  pure ((fvar1, sg1.mvarId)::rest)

/--
Definition of `nCasesProd` / `nCasesProd` 的定义

English:
definition nCasesProd
  signature: (n : Nat) (mvar : MVarId) (h : FVarId)
  body: match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

中文:
定义 nCasesProd
  签名: (n : 自然数) (mvar : MVarId) (h : FVarId)
  定义体: match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

Depends on / 依赖: Expr.fvar, expected, fields, mvar.cases, mvarId, nCasesProd, sg.fields, sg.mvarId, subgoals, throwError
-/
def nCasesProd (n : Nat) (mvar : MVarId) (h : FVarId) : MetaM (MVarId × List FVarId) :=
match n with
| 0 => pure (mvar, [h])
| n' + 1 => do
  let #[sg] ← mvar.cases h | throwError "expected one case subgoals"
  let #[Expr.fvar fvar1, Expr.fvar fvar2] ← pure sg.fields | throwError "expected fvar"
  let (mvar', rest) ← nCasesProd n' sg.mvarId fvar2
  pure (mvar', fvar1::rest)

/--
Definition of `listBoolMerge` / `listBoolMerge` 的定义

English:
definition listBoolMerge
  signature: {α : Type*}

中文:
定义 list布尔Merge
  签名: {α : 类型}
-/
def listBoolMerge {α : Type*} : List Bool -> List α -> List (Option α)
  | [], _ => []
  | false :: xs, ys => none :: listBoolMerge xs ys
  | true :: xs, y :: ys => some y :: listBoolMerge xs ys
  | true :: _, [] => []

/--
Definition of `toInductive` / `toInductive` 的定义

English:
definition toInductive
  signature: (mvar : MVarId) (cs : List Name)
  body: do
  match s.length with
  | 0 => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constr_name, ⟨h, mv⟩, bs, e⟩ => do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← matc

中文:
定义 toInductive
  签名: (mvar : MVarId) (cs : 列表 Name)
  定义体: do
  match s.length with
  | 0 => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constr_name, ⟨h, mv⟩, bs, e⟩ => do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← matc
-/
def toInductive (mvar : MVarId) (cs : List Name)
    (gs : List Expr) (s : List Shape) (h : FVarId) :
    MetaM Unit := do
  match s.length with
  | 0 => do let _ ← mvar.cases h
                  pure ()
  | (n + 1) => do
      let subgoals ← nCasesSum n mvar h
      let _ ← (cs.zip (subgoals.zip s)).mapM fun ⟨constr_name, ⟨h, mv⟩, bs, e⟩ => do
        let n := (bs.filter id).length
        let (mvar', _fvars) ← match e with
        | none => nCasesProd (n-1) mv h
        | some 0 => do let ⟨mvar', fvars⟩ ← nCasesProd n mv h
                          let mvar'' ← mvar'.tryClear fvars.getLast!
                          pure ⟨mvar'', fvars⟩
        | some (e + 1) => do
           let (mv', fvars) ← nCasesProd n mv h
           let lastfv := fvars.getLast!
           let (mv2, fvars') ← nCasesProd e mv' lastfv

           /- `fvars'.foldlM subst mv2` fails when we have dependent equalities (`HEq`).
           `subst` will change the dependent hypotheses, so that the `uniq` local names
           are wrong afterwards. Instead we revert them and pull them out one-by-one. -/
           let (_, mv3) ← mv2.revert fvars'.toArray
           let mv4 ← fvars'.foldlM (fun mv _ => do let ⟨fv, mv'⟩ ← mv.intro1; subst mv' fv) mv3
           pure (mv4, fvars)
        mvar'.withContext do
          let fvarIds := (← getLCtx).getFVarIds.toList
          let gs := fvarIds.take gs.length
          let hs := (fvarIds.reverse.take n).reverse
          let m := gs.map some ++ listBoolMerge bs hs
          let args ← m.mapM fun a =>
            match a with
            | some v => pure (mkFVar v)
            | none => mkFreshExprMVar none
          let c ← mkConstWithFreshMVarLevels constr_name
          let e := mkAppN c args.toArray
          let t ← inferType e
          let mt ← mvar'.getType
          let _ ← isDefEq t mt -- infer values for those mvars we just made
          mvar'.assign e

/--
Definition of `mkIffOfInductivePropImpl` / `mkIffOfInductivePropImpl` 的定义

English:
definition mkIffOfInductivePropImpl
  signature: (ind : Name) (rel : Name) (relStx : Syntax)
  body: do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /

中文:
定义 mkIffOfInductivePropImpl
  签名: (ind : Name) (rel : Name) (relStx : Syntax)
  定义体: do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /
-/
def mkIffOfInductivePropImpl (ind : Name) (rel : Name) (relStx : Syntax) : MetaM Unit := do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam
  /- we use these names for our universe parameters, maybe we should construct a copy of them
  using `uniq_name` -/

  let (thmTy, shape) ← Meta.forallTelescope type fun fvars ty => do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst ind univs) fvars
    let fvars' := fvars.toList
    let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shape_rhss.unzip
    pure (← mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrList rhss)), shape)

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

addDecl .thmDecl {
    name := rel
    levelParams := univNames
    type := thmTy
    value := ← instantiateMVars mvar
  }
  addDeclarationRangesFromSyntax rel (← getRef) relStx
.run' Term.addTermInfo' relStx (← mkConstWithLevelParams rel) (isBinder := true)

/--
Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for each constructor for each of
  the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : Nat), Foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar]
structure Foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), Foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ ps is, i as ↔ ⋁_j, ∃ cs, is = cs`, where
* `ps` are the type parameters,
* `is` are the indices,
* `j` ranges over all possible constructors,
* the `cs` are the parameters for each of the constructors, and
* the equalities `is = cs` are the instantiations for
  each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `List.Chain` produces:

```lean
∀ { α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃ (b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.
-/
syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop " ident ppSpace ident : command

elab_rules : command
| `(command| mk_iff_of_inductive_prop $i:ident $r:ident) =>
Command.liftCoreM MetaM.run' do
      mkIffOfInductivePropImpl i.getId r.getId r

initialize Lean.registerBuiltinAttribute {
  name := `mkIff
  descr := "Generate an `iff` lemma for an inductive `Prop`."
  add := fun decl stx _ => Lean.Meta.MetaM.run' do
    let (tgt, idStx) ← match stx with
      | `(attr| mk_iff $tgt:ident) =>
        pure ((← mkDeclName (← getCurrNamespace) {} tgt.getId).1, tgt.raw)
      | `(attr| mk_iff) => pure (decl.decapitalize.appendAfter "_iff", stx)
      | _ => throwError "unrecognized syntax"
    mkIffOfInductivePropImpl decl tgt idStx
}

end Mathlib.Tactic.MkIff
