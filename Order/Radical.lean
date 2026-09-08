/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison
-/
module

public import Mathlib.Order.Atoms

/-!
# The radical of a lattice

This file contains results on the order radical of a lattice: the infimum of the coatoms.
-/

@[expose] public section

/--
The infimum of all coatoms.

This notion specializes, e.g. in the subgroup lattice of a group to the Frattini subgroup,
or in the lattices of ideals in a ring `R` to the Jacobson ideal.
-/
/-
**Order.radical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Order.radical (α : Type*) [Preorder α] [OrderTop α] [InfSet α] : α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of all coatoms.

This notion specializes, e.g. in the subgroup lattice of a group to the Frattini
 subgroup,
or in the lattices of ideals in a ring `R` to the Jacobson ideal.
-/
def Order.radical (α : Type*) [Preorder α] [OrderTop α] [InfSet α] : α :=
  ⨅ a ∈ {H | IsCoatom H}, a

variable {α : Type*} [CompleteLattice α]
/-
**Order.radical_le_coatom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Order.radical_le_coatom {a : α} (h : IsCoatom a) : radical α <= a
参数：h : IsCoatom a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
-/
lemma Order.radical_le_coatom {a : α} (h : IsCoatom a) : radical α ≤ a := biInf_le _ h

variable {β : Type*} [CompleteLattice β]
/-
**OrderIso.map_radical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_radical (f : α ≃o β) : f (Order.radical α) = Order.radical β
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: InfSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨅ x,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem OrderIso.map_radical (f : α ≃o β) : f (Order.radical α) = Order.radical β := by
  unfold Order.radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · simp
/-
**Order.radical_nongenerating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.radical_nongenerating [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤)
 : a = ⊤
参数：h : a ⊔ radical α = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `Order.radical_le_coatom`：Order.radical_le_coatom {a : α} (h : IsCoatom a
) : radical α <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem Order.radical_nongenerating [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤) : a = ⊤ := by
  -- Since the lattice is coatomic, either `a` is already the top element,
  -- or there is a coatom above it.
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · -- In the first case, we're done, this was already the goal.
    rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α ≤ m := sup_le le (radical_le_coatom c)
    -- Now note that `a ⊔ radical α ≤ m` since both `a ≤ m` and `radical α ≤ m`.
    rw [h, top_le_iff] at q
    simpa using c.1 q
