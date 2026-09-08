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

/-
**Mathlib.Tactic.BicategoryLike.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
BicategoryLike`。
形式化陈述：mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b
') : a = b
参数：a b a' b' : α；ha : a = a'；hb : b = b'；h : a' = b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
/-
**Mathlib.Tactic.BicategoryLike.normalForm** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.BicategoryLike`。
形式化陈述：normalForm (ρ : Type) [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso
 (CoherenceM ρ)] [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)] [MkMor
₂ (CoherenceM ρ)] [MonadMor₂ (CoherenceM ρ)] (nm : Name) (mvarId : MVarId) : Met
aM (List MVarId)
参数：ρ : Type；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；Coh
erenceM ρ；nm : Name；mvarId : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transform an equality between 2-morphisms into the equality between their normal
izations.
-/
def normalForm (ρ : Type) [Context ρ]
    [MonadMor₁ (CoherenceM ρ)]
    [MonadMor₂Iso (CoherenceM ρ)]
    [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)]
    [MkMor₂ (CoherenceM ρ)]
    [MonadMor₂ (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
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
/-
**Mathlib.Tactic.BicategoryLike.mk_eq_of_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.BicategoryLike`。
形式化陈述：mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' 
: f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄) (e_α : α = α') (e_η : η = η') (e_
ηs : ηs = ηs') : α ≫ η ≫ ηs = α' ≫ η' ≫ ηs'
参数：α α' : f₁ ⟶ f₂；η η' : f₂ ⟶ f₃；ηs ηs' : f₃ ⟶ f₄；e_α : α = α'；e_η : η = η'；e_ηs
 : ηs = ηs'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_of_cons {C : Type u} [CategoryStruct.{v} C]
    {f₁ f₂ f₃ f₄ : C}
    (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs ηs' : f₃ ⟶ f₄)
    (e_α : α = α') (e_η : η = η') (e_ηs : ηs = ηs') :
    α ≫ η ≫ ηs = α' ≫ η' ≫ ηs' := by
  simp [e_α, e_η, e_ηs]

/-- Split the goal `α ≫ η ≫ ηs = α' ≫ η' ≫ ηs'` into `α = α'`, `η = η'`, and `ηs = ηs'`. -/
/-
**Mathlib.Tactic.BicategoryLike.ofNormalizedEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.BicategoryLike`。
形式化陈述：ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId)
参数：mvarId : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split the goal `α ≫ η ≫ ηs = α' ≫ η' ≫ ηs'` into `α = α'`, `η = η'`, and `ηs = η
s'`.
-/
def ofNormalizedEq (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let e ← instantiateMVars <| ← mvarId.getType
    let some (_, e₁, e₂) := (← whnfR e).eq? | throwError "requires an equality goal"
    match (← whnfR e₁).getAppFnArgs, (← whnfR e₂).getAppFnArgs with
    | (``CategoryStruct.comp, #[_, _, _, _, _, α, η]),
      (``CategoryStruct.comp, #[_, _, _, _, _, α', η']) =>
      match (← whnfR η).getAppFnArgs, (← whnfR η').getAppFnArgs with
      | (``CategoryStruct.comp, #[_, _, _, _, _, η, ηs]),
        (``CategoryStruct.comp, #[_, _, _, _, _, η', ηs']) =>
        let e_α ← mkFreshExprMVar (← Meta.mkEq α α')
        let e_η  ← mkFreshExprMVar (← Meta.mkEq η η')
        let e_ηs ← mkFreshExprMVar (← Meta.mkEq ηs ηs')
        let x ← mvarId.apply (← mkAppM ``mk_eq_of_cons #[α, α', η, η', ηs, ηs', e_α, e_η, e_ηs])
        return x
      | _, _ => throwError "failed to make a normalized equality for {e}"
    | _, _ => throwError "failed to make a normalized equality for {e}"

/-- List.splitEvenOdd [0, 1, 2, 3, 4] = ([0, 2, 4], [1, 3]) -/
/-
**Mathlib.Tactic.BicategoryLike.List.splitEvenOdd** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Tactic.BicategoryLike.List`。
形式化陈述：{α : Type u} → List α → List α × List α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List.splitEvenOdd [0, 1, 2, 3, 4] = ([0, 2, 4], [1, 3])
-/
def List.splitEvenOdd {α : Type u} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a::b::xs =>
    let (as, bs) := List.splitEvenOdd xs
    (a::as, b::bs)

/-- The core function for `monoidal` and `bicategory` tactics. -/
/-
**Mathlib.Tactic.BicategoryLike.main** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.B
icategoryLike`。
形式化陈述：main (ρ : Type) [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (Cohe
renceM ρ)] [MonadNormalExpr (CoherenceM ρ)] [MkEval (CoherenceM ρ)] [MkMor₂ (Coh
erenceM ρ)] [MonadMor₂ (CoherenceM ρ)] [MonadCoherehnceHom (CoherenceM ρ)] [Mona
dNormalizeNaturality (CoherenceM ρ)] [MkEqOfNaturality (CoherenceM ρ)] (nm : Nam
e) (mvarId : MVarId) : MetaM (List MVarId)
参数：ρ : Type；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；Coh
erenceM ρ；CoherenceM ρ；CoherenceM ρ；CoherenceM ρ；nm : Name；mvarId : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The core function for `monoidal` and `bicategory` tactics.
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

