/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Coherence.Normalize
public import Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence
public meta import Mathlib.Tactic.ToDual

/-!
# The Core function for `monoidal` and `bicategory` tactics

This file provides the function `BicategoryLike.main` for proving equalities in monoidal categories
and bicategories. Using `main`, we will define the following tactics:
- `monoidal` at `Mathlib/Tactic/CategoryTheory/Monoidal/Basic.lean`
- `bicategory` at `Mathlib/Tactic/CategoryTheory/Bicategory/Basic.lean`

The `main` first normalizes the both sides using `eval`, then compares the corresponding components.
It closes the goal at non-structural parts with `rfl` and the goal at structural parts by
`pureCoherence`.

-/

public meta section

open Lean Meta Elab
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Mathlib.Tactic.BicategoryLike

/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b')
  statement: a = b
  proof: by
  simp [h, ha, hb]

中文:
定理 mk_eq
  条件: {α : 类型 _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b')
  结论: a = b
  证明: by
  simp [h, ha, hb]
-/
theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

/--
Definition of `normalForm` / `normalForm` 的定义

English:
definition normalForm
  signature: (ρ : Type) [Context ρ]
  body: do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    withTraceNode nm (fun _ => return m!"normalize: {e}") do
      let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| e).eq?
        | throwError "{nm}_nf requires an equality goal"
      let ctx : ρ ← mkContext e₁
      Coh

中文:
定义 normalForm
  签名: (ρ : 类型) [余ntext ρ]
  定义体: do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    withTraceNode nm (fun _ => return m!"normalize: {e}") do
      let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| e).eq?
        | throwError "{nm}_nf requires an equality goal"
      let ctx : ρ ← mkContext e₁
      Coh
-/
def normalForm (ρ : Type) [Context ρ]
    [MonadMor₁ (CoherenceM ρ)]
    [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)]
    [MkMor₂ (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    withTraceNode nm (fun _ => return m!"normalize: {e}") do
      let some (_, e₁, e₂) := (← whnfR <| ← instantiateMVars <| e).eq?
        | throwError "{nm}_nf requires an equality goal"
      let ctx : ρ ← mkContext e₁
      CoherenceM.run (ctx := ctx) do
        let e₁' ← MkMor₂.ofExpr e₁
        let e₂' ← MkMor₂.ofExpr e₂
        let e₁'' ← eval nm e₁'
        let e₂'' ← eval nm e₂'
        let H ← mkAppM ``mk_eq #[e₁, e₂, e₁''.expr.e.e, e₂''.expr.e.e, e₁''.proof, e₂''.proof]
        mvarId.apply H

universe v u

/--
theorem `mk_eq_of_cons` / 定理 `mk_eq_of_cons`

English:
theorem mk_eq_of_cons
  statement: {C : Type u} [CategoryStruct.{v} C]
  proof: by
  simp [e_α, e_η, e_ηs]

中文:
定理 mk_eq_of_cons
  结论: {C : 类型u} [CategoryStruct.{v} C]
  证明: by
  simp [e_α, e_η, e_ηs]
-/
theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (e_α : α = α') (e_η : η = η') (e_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [e_α, e_η, e_ηs]

/--
Definition of `ofNormalizedEq` / `ofNormalizedEq` 的定义

English:
definition ofNormalizedEq
  signature: (mvarId : MVarId)
  body: do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]),
      (``CategoryStruct

中文:
定义 ofNormalizedEq
  签名: (mvarId : MVarId)
  定义体: do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]),
      (``CategoryStruct
-/
def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
let e ← instantiateMVars ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]),
      (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
      match (← whnfR η).getAppFnArgs, (← whnfR η').getAppFnArgs with
      | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]),
        (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
        let e_α ← mkFreshExprMVar (← Meta.mkEq α α')
        let e_η ← mkFreshExprMVar (← Meta.mkEq η η')
        let e_ηs ← mkFreshExprMVar (← Meta.mkEq ηs ηs')
        let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', e_α, e_η, e_ηs])
        return x
      | _, _ => throwError "failed to make a normalized equality for {e}"
    | _, _ => throwError "failed to make a normalized equality for {e}"

/--
Definition of `List.splitEvenOdd` / `List.splitEvenOdd` 的定义

English:
definition List.splitEvenOdd
  signature: {α : Type u}
  body: List.splitEvenOdd xs
    (a::as, b::bs)

中文:
定义 列表.splitEvenOdd
  签名: {α : 类型u}
  定义体: List.splitEvenOdd xs
    (a::as, b::bs)

Depends on / 依赖: List.splitEvenOdd, splitEvenOdd
-/
def List.splitEvenOdd {α : Type u} : List α -> List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a::b::xs =>
    let (as, bs) := List.splitEvenOdd xs
    (a::as, b::bs)

/--
Definition of `main` / `main` 的定义

English:
definition main
  signature: (ρ : Type) [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]
  body: mvarId.withContext do
    let mvarIds ← normalForm ρ nm mvarId
    let (mvarIdsCoherence, mvarIdsRefl) := List.splitEvenOdd (← repeat' ofNormalizedEq mvarIds)
    for mvarId in mvarIdsRefl do mvarId.refl
    let mvarIds'' ← mvarIdsCoherence.mapM fun mvarId => do
      withTraceNode nm (fun _ => do r

中文:
定义 main
  签名: (ρ : 类型) [余ntext ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]
  定义体: mvarId.withContext do
    let mvarIds ← normalForm ρ nm mvarId
    let (mvarIdsCoherence, mvarIdsRefl) := List.splitEvenOdd (← repeat' ofNormalizedEq mvarIds)
    for mvarId in mvarIdsRefl do mvarId.refl
    let mvarIds'' ← mvarIdsCoherence.mapM fun mvarId => do
      withTraceNode nm (fun _ => do r

Depends on / 依赖: List.splitEvenOdd, flatten, getType, mvarId, mvarId.getType, mvarId.refl, mvarId.withContext, mvarIds, mvarIdsCoherence, mvarIdsCoherence.mapM, mvarIdsRefl, normalForm, ofNormalizedEq, pureCoherence, repeat, return, splitEvenOdd, withContext, withTraceNode
-/
def main (ρ : Type) [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)] [MkMor₂ (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)] [MonadCoherehnceHom (CoherenceM ρ)]
    [MonadNormalizeNaturality (CoherenceM ρ)] [MkEqOfNaturality (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    let mvarIds ← normalForm ρ nm mvarId
    let (mvarIdsCoherence, mvarIdsRefl) := List.splitEvenOdd (← repeat' ofNormalizedEq mvarIds)
    for mvarId in mvarIdsRefl do mvarId.refl
    let mvarIds'' ← mvarIdsCoherence.mapM fun mvarId => do
      withTraceNode nm (fun _ => do return m!"goal: {← mvarId.getType}") do
        try
          pureCoherence ρ nm mvarId
        catch _ => return [mvarId]
    return mvarIds''.flatten

end Mathlib.Tactic.BicategoryLike
