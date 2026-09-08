/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Final functors between intervals

-/

public section

universe u

/-
**Set.Ici.subtype_functor_final** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.Ici.subtype_functor_final {J : Type u} [LinearOrder J] (j : J) : (Subt
ype.mono_coe (· in Set.Ici j)).functor.Final
参数：j : J。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Monotone.final_functor_iff`：Monotone.final_functor_iff {J₁ J₂ : Type*} [
Preorder J₁] [Preorder J₂] [IsDirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f)
 : hf.functor.Fi…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
instance Set.Ici.subtype_functor_final {J : Type u} [LinearOrder J] (j : J) :
    (Subtype.mono_coe (· ∈ Set.Ici j)).functor.Final := by
  rw [Monotone.final_functor_iff]
  intro k
  exact ⟨⟨max j k, le_max_left _ _⟩, le_max_right _ _⟩
