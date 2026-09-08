/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Order.Hom.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Constructing nonarchimedean (ultrametric) normed groups from nonarchimedean normed homs

This file defines constructions that upgrade `Add(Comm)Group` to `(Semi)NormedAdd(Comm)Group`
using an `AddGroup(Semi)normClass` when the codomain is the reals and the hom is nonarchimedean.

## Implementation details

The lemmas need to assume `[Dist α]` to be able to be stated, so they take an extra argument
that shows that this distance instance is propositionally equal to the one that comes from the
hom-based `AddGroupSeminormClass.toSeminormedAddGroup f` construction. To help at use site,
the argument is an autoparam that resolves by definitional equality when using these constructions.
-/

public section

variable {F α : Type*} [FunLike F α ℝ]

/-- Proves that when a `SeminormedAddGroup` structure is constructed from an
`AddGroupSeminormClass` that satisfies `IsNonarchimedean`, the group has an `IsUltrametricDist`. -/
/-
**AddGroupSeminormClass.isUltrametricDist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddGroupSeminormClass.isUltrametricDist [AddGroup α] [AddGroupSeminormClas
s F α Real] [inst : Dist α] {f : F} (hna : IsNonarchimedean f) (hd : inst = (Add
GroupSeminormClass.toSeminormedAddGroup f).toDist
参数：hna : IsNonarchimedean f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_neg_add`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a 
b : E), dist a b = ‖-a + b‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
Proves that when a `SeminormedAddGroup` structure is constructed from an
`AddGroupSeminormClass` that satisfies `IsNonarchimedean`, the group has an `IsU
ltrametricDist`.
-/
lemma AddGroupSeminormClass.isUltrametricDist [AddGroup α] [AddGroupSeminormClass F α ℝ]
    [inst : Dist α] {f : F} (hna : IsNonarchimedean f)
    (hd : inst = (AddGroupSeminormClass.toSeminormedAddGroup f).toDist := by rfl) :
    IsUltrametricDist α :=
  ⟨fun x y z ↦ by
    simp +instances only [hd, dist_eq_norm_neg_add,
      AddGroupSeminormClass.toSeminormedAddGroup_norm_eq]
    convert! hna (-x + y) (-y + z) using 2
    rw [add_assoc, ← add_assoc y, add_neg_cancel, zero_add]⟩
