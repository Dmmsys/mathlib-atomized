/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Fintype instances relating to units
-/

public section

assert_not_exists Field

variable {α : Type*}

/-
**UnitsInt.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：UnitsInt.fintype : Fintype Intˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x ↦ by cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]
/-
**UnitsInt.univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UnitsInt.univ : (Finset.univ : Finset Intˣ) = {1, -1}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} := rfl

@[simp]
/-
**Fintype.card_units_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_units_int : Fintype.card Intˣ = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [Finite α] : Finite αˣ := .of_injective _ Units.val_injective

variable (α)
/-
**Nat.card_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.card α - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Nat.card_sum`：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Na
t.card α + Nat.card β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
-/
theorem Nat.card_units [GroupWithZero α] :
    Nat.card αˣ = Nat.card α - 1 := by
  classical
  rw [Nat.card_congr unitsEquivNeZero, eq_comm, ← Nat.card_congr (Equiv.sumCompl (· = (0 : α)))]
  rcases finite_or_infinite {a : α // a ≠ 0}
  · rw [Nat.card_sum, Nat.card_unique, add_tsub_cancel_left]
  · rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_tsub]
/-
**Nat.card_eq_card_units_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.card_eq_card_units_add_one [GroupWithZero α] [Finite α] : Nat.card α =
 Nat.card αˣ + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem Nat.card_eq_card_units_add_one [GroupWithZero α] [Finite α] :
    Nat.card α = Nat.card αˣ + 1 := by
  rw [Nat.card_units, tsub_add_cancel_of_le Nat.card_pos]
/-
**Fintype.card_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_units [GroupWithZero α] [Fintype α] [DecidableEq α] : Fintype
.card αˣ = Fintype.card α - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1
-/
theorem Fintype.card_units [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card]
/-
**Fintype.card_eq_card_units_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_eq_card_units_add_one [GroupWithZero α] [Fintype α] [Decidabl
eEq α] : Fintype.card α = Fintype.card αˣ + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem Fintype.card_eq_card_units_add_one [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card α = Fintype.card αˣ + 1 := by
  rw [Fintype.card_units, tsub_add_cancel_of_le Fintype.card_pos]
