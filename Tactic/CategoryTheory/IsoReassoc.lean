/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Extension of `reassoc` to isomorphisms.

We extend `reassoc` and `reassoc_of%` for equality of isomorphisms.
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ≅ Y` in some category will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`
but with the conclusions simplified using basic proportions in isomorphisms in a category
(`Iso.trans_refl`, `Iso.refl_trans`, `Iso.trans_assoc`, `Iso.trans_symm`,
`Iso.symm_self_id` and `Iso.self_symm_id`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.Reassoc

/-
**Mathlib.Tactic.Reassoc.Iso.eq_whisker** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Reassoc.Iso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} {
f g : X ≅ Y},   f = g → ∀ {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h
参数：h : Y ≅ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Iso.eq_whisker {C : Type*} [Category* C]
    {X Y : C} {f g : X ≅ Y} (w : f = g) {Z : C} (h : Y ≅ Z) :
    f ≪≫ h = g ≪≫ h := by rw [w]

/-- Simplify an expression using only the axioms of a groupoid. -/
/-
**Mathlib.Tactic.Reassoc.categoryIsoSimp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Reassoc`。
形式化陈述：categoryIsoSimp (e : Expr) : MetaM Simp.Result
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simplify an expression using only the axioms of a groupoid.
-/
def categoryIsoSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decide := false })

/--
Given an equation `f = g` between isomorphisms `X ≅ Y` in a category,
produce the equation `∀ {Z} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`,
but with compositions fully right associated, identities removed, and functors applied.
-/
/-
**Mathlib.Tactic.Reassoc.reassocExprIso** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Reassoc`。
形式化陈述：reassocExprIso (e : Expr) : MetaM (Expr × Array MVarId)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equation `f = g` between isomorphisms `X ≅ Y` in a category,
produce the equation `∀ {Z} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`,
but with compositions fully right associated, identities removed, and functors a
pplied.
-/
def reassocExprIso (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``Iso.eq_whisker
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType categoryIsoSimp (mkAppN lem₀ args), #[inst.mvarId!])

initialize registerReassocExpr reassocExprIso

end Mathlib.Tactic.Reassoc

