/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Properties of `Equiv.Perm` on `Finite` types

Let `α` be a `Finite` type.

* `Nat.card_perm`: cardinality of `Equiv.Perm α`.

* `Equiv.Perm.isCyclic_of_card_le_two`: if `Nat.card α ≤ 2`,
  then `Equiv.Perm α` is cyclic.

* `Equiv.Perm.isCyclic_iff_card_le_two`: `Equiv.Perm α` is cyclic iff `Nat.card α ≤ 2`.

* `Equiv.Perm.isMulCommutative_iff_card_le_two`: `Equiv.Perm α` is commutative iff `Nat.card α ≤ 2`.

-/

public section

assert_not_exists Field

open Equiv Nat

variable {α : Type*} [Finite α]

namespace Nat

/-
**Nat.card_perm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_perm : Nat.card (Perm α) = (Nat.card α)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!
-/
theorem card_perm : Nat.card (Perm α) = (Nat.card α)! := by
  classical
  have := Fintype.ofFinite α
  rw [card_eq_fintype_card, card_eq_fintype_card, Fintype.card_perm]

end Nat

namespace Equiv.Perm

/-
**Equiv.Perm.isCyclic_of_card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCyclic_of_card_le_two (hα : Nat.card α <= 2) : IsCyclic (Perm α)
参数：hα : Nat.card α <= 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_card_dvd_prime`：isCyclic_of_card_dvd_prime {p : Nat} [hp : F
act p.Prime] (h : Nat.card α ∣ p) : IsCyclic α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用定理 `Nat.factorial_dvd_factorial`：factorial_dvd_factorial {m n} (h : m <= n) 
: m ! ∣ n !
-/
theorem isCyclic_of_card_le_two (hα : Nat.card α ≤ 2) :
    IsCyclic (Perm α) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  simpa [card_perm] using factorial_dvd_factorial hα
/-
**Equiv.Perm.isMulCommutative_iff_card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：isMulCommutative_iff_card_le_two : IsMulCommutative (Perm α) ↔ Nat.card α 
<= 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Set.two_lt_ncard_iff`：two_lt_ncard_iff (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.Perm.isCyclic_of_card_le_two`：isCyclic_of_card_le_two (hα : Nat.ca
rd α <= 2) : IsCyclic (Perm α)
-/
theorem isMulCommutative_iff_card_le_two :
    IsMulCommutative (Perm α) ↔ Nat.card α ≤ 2 := by
  refine ⟨?_, fun h ↦ (isCyclic_of_card_le_two h).isMulCommutative⟩
  classical
  rintro ⟨⟨h⟩⟩
  rw [← not_lt, ← Set.ncard_univ, Set.two_lt_ncard_iff]
  rintro ⟨a, b, c, _, _, _, hab, hac, hbc⟩
  apply hbc
  simp_rw [Perm.ext_iff] at h
  simpa [swap_apply_of_ne_of_ne hab hac] using h (swap a b) (swap b c) a
/-
**Equiv.Perm.isCyclic_iff_card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCyclic_iff_card_le_two : IsCyclic (Perm α) ↔ Nat.card α <= 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.isMulCommutative_iff_card_le_two`：isMulCommutative_iff_card_l
e_two : IsMulCommutative (Perm α) ↔ Nat.card α <= 2
· 使用定理 `Equiv.Perm.isCyclic_of_card_le_two`：isCyclic_of_card_le_two (hα : Nat.ca
rd α <= 2) : IsCyclic (Perm α)
-/
theorem isCyclic_iff_card_le_two :
    IsCyclic (Perm α) ↔ Nat.card α ≤ 2 :=
  ⟨fun h ↦ isMulCommutative_iff_card_le_two.mp h.isMulCommutative, isCyclic_of_card_le_two⟩

end Equiv.Perm

