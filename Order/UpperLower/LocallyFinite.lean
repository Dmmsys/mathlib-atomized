/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.UpperLower.Closure

/-!
# Upper and lower sets in a locally finite order

In this file we characterise the interaction of `UpperSet`/`LowerSet` and `LocallyFiniteOrder`.
-/

public section


namespace Set

variable {α : Type*} [Preorder α] {s : Set α}

/-
**Set.Finite.upperClosure** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} [LocallyFiniteOrderTop α]
, s.Finite → (↑(upperClosure s)).Finite
参数：↑(upperClosure s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_upperClosure`：coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a
 in s, Ici a
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.finite_Ici`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Top α] (a : α), (Set.Ici a).Finite
-/
protected theorem Finite.upperClosure [LocallyFiniteOrderTop α] (hs : s.Finite) :
    (upperClosure s : Set α).Finite := by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _
/-
**Set.Finite.lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} [LocallyFiniteOrderBot α]
, s.Finite → (↑(lowerClosure s)).Finite
参数：↑(lowerClosure s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] (s : Set α), ↑(lo
werClosure s) = ⋃ a ∈ s, Set.Iic a
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
-/
protected theorem Finite.lowerClosure [LocallyFiniteOrderBot α] (hs : s.Finite) :
    (lowerClosure s : Set α).Finite := by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _

end Set

