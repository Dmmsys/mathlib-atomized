/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Finset.Density

/-!
# Doubling and difference constants

This file defines the doubling and difference constants of two finsets in a group.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace Finset
section Group
variable {G G' : Type*} [Group G] [AddGroup G'] [DecidableEq G] [DecidableEq G'] {A B : Finset G}

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`.

The notation `σₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`.

The notation `σ[A, B]` is available in scope `Combinatorics.Additive`. -/]
/-
**Finset.mulConst** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulConst (A B : Finset G) : Rat>=0
参数：A B : Finset G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulConst (A B : Finset G) : ℚ≥0 := #(A * B) / #A

/-- The difference constant `δₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`.

The notation `δₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`.

The notation `δ[A, B]` is available in scope `Combinatorics.Additive`. -/]
/-
**Finset.divConst** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：divConst (A B : Finset G) : Rat>=0
参数：A B : Finset G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def divConst (A B : Finset G) : ℚ≥0 := #(A / B) / #A

/-- The doubling constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A * B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A ", " B "]" => Finset.mulConst A B

/-- The doubling constant `σₘ[A]` of a finset `A` in a group is `|A * A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σₘ[" A "]" => Finset.mulConst A A

/-- The doubling constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A + B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A ", " B "]" => Finset.addConst A B

/-- The doubling constant `σ[A]` of a finset `A` in a group is `|A + A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "σ[" A "]" => Finset.addConst A A

/-- The difference constant `σₘ[A, B]` of two finsets `A` and `B` in a group is `|A / B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A ", " B "]" => Finset.divConst A B

/-- The difference constant `σₘ[A]` of a finset `A` in a group is `|A / A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δₘ[" A "]" => Finset.divConst A A

/-- The difference constant `σ[A, B]` of two finsets `A` and `B` in a group is `|A - B| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A ", " B "]" => Finset.subConst A B

/-- The difference constant `σ[A]` of a finset `A` in a group is `|A - A| / |A|`. -/
scoped[Combinatorics.Additive] notation3:max "δ[" A "]" => Finset.subConst A A

open scoped Combinatorics.Additive

@[to_additive (attr := simp) addConst_mul_card]
/-
**Finset.mulConst_mul_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_mul_card (A B : Finset G) : σₘ[A, B] * #A = #(A * B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.empty_mul`：empty_mul (s : Finset α) : ∅ * s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
-/
lemma mulConst_mul_card (A B : Finset G) : σₘ[A, B] * #A = #(A * B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) subConst_mul_card]
/-
**Finset.divConst_mul_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_mul_card (A B : Finset G) : δₘ[A, B] * #A = #(A / B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.empty_div`：empty_div (s : Finset α) : ∅ / s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
-/
lemma divConst_mul_card (A B : Finset G) : δₘ[A, B] * #A = #(A / B) := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · exact div_mul_cancel₀ _ (by positivity)

@[to_additive (attr := simp) card_mul_addConst]
/-
**Finset.card_mul_mulConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_mulConst (A B : Finset G) : #A * σₘ[A, B] = #(A * B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mulConst_mul_card`：mulConst_mul_card (A B : Finset G) : σₘ[A, B] 
* #A = #(A * B)
-/
lemma card_mul_mulConst (A B : Finset G) : #A * σₘ[A, B] = #(A * B) := by
  rw [mul_comm, mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]
/-
**Finset.card_mul_divConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_divConst (A B : Finset G) : #A * δₘ[A, B] = #(A / B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.divConst_mul_card`：divConst_mul_card (A B : Finset G) : δₘ[A, B] 
* #A = #(A / B)
-/
lemma card_mul_divConst (A B : Finset G) : #A * δₘ[A, B] = #(A / B) := by
  rw [mul_comm, divConst_mul_card]

@[to_additive (attr := simp)]
/-
**Finset.mulConst_empty_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_empty_left (B : Finset G) : σₘ[∅, B] = 0
参数：B : Finset G。
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
· 使用定理 `Finset.empty_mul`：empty_mul (s : Finset α) : ∅ * s = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulConst_empty_left (B : Finset G) : σₘ[∅, B] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
/-
**Finset.divConst_empty_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_empty_left (B : Finset G) : δₘ[∅, B] = 0
参数：B : Finset G。
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
· 使用定理 `Finset.empty_div`：empty_div (s : Finset α) : ∅ / s = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divConst_empty_left (B : Finset G) : δₘ[∅, B] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
/-
**Finset.mulConst_empty_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_empty_right (A : Finset G) : σₘ[A, ∅] = 0
参数：A : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mul_empty`：mul_empty (s : Finset α) : s * ∅ = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulConst_empty_right (A : Finset G) : σₘ[A, ∅] = 0 := by simp [mulConst]

@[to_additive (attr := simp)]
/-
**Finset.divConst_empty_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_empty_right (A : Finset G) : δₘ[A, ∅] = 0
参数：A : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.div_empty`：div_empty (s : Finset α) : s / ∅ = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divConst_empty_right (A : Finset G) : δₘ[A, ∅] = 0 := by simp [divConst]

@[to_additive (attr := simp)]
/-
**Finset.mulConst_inv_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_inv_right (A B : Finset G) : σₘ[A, B⁻¹] = δₘ[A, B]
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
lemma mulConst_inv_right (A B : Finset G) : σₘ[A, B⁻¹] = δₘ[A, B] := by
  rw [mulConst, divConst, ← div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**Finset.divConst_inv_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_inv_right (A B : Finset G) : δₘ[A, B⁻¹] = σₘ[A, B]
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
-/
lemma divConst_inv_right (A B : Finset G) : δₘ[A, B⁻¹] = σₘ[A, B] := by
  rw [mulConst, divConst, div_inv_eq_mul]

@[to_additive]
/-
**Finset.one_le_mulConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_le_mulConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 <= σₘ[A, B]
参数：hA : A.Nonempty；hB : B.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用引理 `one_le_div₀`：one_le_div₀ (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_le_card_mul_right`：card_le_card_mul_right (ht : t.Nonempty) 
: #s <= #(s * t)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
lemma one_le_mulConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 ≤ σₘ[A, B] := by
  rw [mulConst, one_le_div₀]
  · exact mod_cast card_le_card_mul_right hB
  · simpa

@[to_additive]
/-
**Finset.one_le_mulConst_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_le_mulConst_self (hA : A.Nonempty) : 1 <= σₘ[A]
参数：hA : A.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.one_le_mulConst`：one_le_mulConst (hA : A.Nonempty) (hB : B.Nonemp
ty) : 1 <= σₘ[A, B]
-/
lemma one_le_mulConst_self (hA : A.Nonempty) : 1 ≤ σₘ[A] := one_le_mulConst hA hA

@[to_additive]
/-
**Finset.one_le_divConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_le_divConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 <= δₘ[A, B]
参数：hA : A.Nonempty；hB : B.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mulConst_inv_right`：mulConst_inv_right (A B : Finset G) : σₘ[A, B
⁻¹] = δₘ[A, B]
· 使用引理 `Finset.one_le_mulConst`：one_le_mulConst (hA : A.Nonempty) (hB : B.Nonemp
ty) : 1 <= σₘ[A, B]
-/
lemma one_le_divConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 ≤ δₘ[A, B] := by
  rw [← mulConst_inv_right]
  apply one_le_mulConst hA (by simpa)

@[to_additive]
/-
**Finset.one_le_divConst_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_le_divConst_self (hA : A.Nonempty) : 1 <= δₘ[A]
参数：hA : A.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.one_le_divConst`：one_le_divConst (hA : A.Nonempty) (hB : B.Nonemp
ty) : 1 <= δₘ[A, B]
-/
lemma one_le_divConst_self (hA : A.Nonempty) : 1 ≤ δₘ[A] := one_le_divConst hA hA

@[to_additive]
/-
**Finset.mulConst_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_le_card : σₘ[A, B] <= #B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mulConst_empty_left`：mulConst_empty_left (B : Finset G) : σₘ[∅, B
] = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.card_mul_le`：card_mul_le : #(s * t) <= #s * #t
-/
lemma mulConst_le_card : σₘ[A, B] ≤ #B := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [mulConst, div_le_iff₀' (by positivity)]
  exact mod_cast card_mul_le

@[to_additive]
/-
**Finset.divConst_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_le_card : δₘ[A, B] <= #B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.divConst_empty_left`：divConst_empty_left (B : Finset G) : δₘ[∅, B
] = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.card_div_le`：card_div_le : #(s / t) <= #s * #t
-/
lemma divConst_le_card : δₘ[A, B] ≤ #B := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  rw [divConst, div_le_iff₀' (by positivity)]
  exact mod_cast card_div_le

section Fintype
variable [Fintype G]

/-- Dense sets have small doubling. -/
@[to_additive addConst_le_inv_dens /-- Dense sets have small doubling. -/]
/-
**Finset.mulConst_le_inv_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_le_inv_dens : σₘ[A, B] <= A.dens⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.dens.eq_1`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α), s.
dens = ↑s.card / ↑(Fintype.card α)
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
Dense sets have small doubling.
-/
lemma mulConst_le_inv_dens : σₘ[A, B] ≤ A.dens⁻¹ := by
  rw [dens, inv_div, mulConst]; gcongr; exact card_le_univ _

/-- Dense sets have small difference constant. -/
@[to_additive subConst_le_inv_dens /-- Dense sets have small difference constant. -/]
/-
**Finset.divConst_le_inv_dens** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_le_inv_dens : δₘ[A, B] <= A.dens⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.dens.eq_1`：∀ {α : Type u_2} [inst : Fintype α] (s : Finset α), s.
dens = ↑s.card / ↑(Fintype.card α)
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
Dense sets have small difference constant.
-/
lemma divConst_le_inv_dens : δₘ[A, B] ≤ A.dens⁻¹ := by
  rw [dens, inv_div, divConst]; gcongr; exact card_le_univ _

end Fintype

variable {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]

@[to_additive (dont_translate := 𝕜)]
/-
**Finset.cast_mulConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：cast_mulConst (A B : Finset G) : (σₘ[A, B] : 𝕜) = #(A * B) / #A
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_div`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cast_mulConst (A B : Finset G) : (σₘ[A, B] : 𝕜) = #(A * B) / #A := by simp [mulConst]

@[to_additive (dont_translate := 𝕜)]
/-
**Finset.cast_divConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：cast_divConst (A B : Finset G) : (δₘ[A, B] : 𝕜) = #(A / B) / #A
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.cast_div`：∀ {α : Type u_3} [inst : DivisionSemiring α] [CharZero α
] (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cast_divConst (A B : Finset G) : (δₘ[A, B] : 𝕜) = #(A / B) / #A := by simp [divConst]

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_addConst_mul_card]
/-
**Finset.cast_mulConst_mul_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：cast_mulConst_mul_card (A B : Finset G) : (σₘ[A, B] * #A : 𝕜) = #(A * B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用引理 `Finset.mulConst_mul_card`：mulConst_mul_card (A B : Finset G) : σₘ[A, B] 
* #A = #(A * B)
-/
lemma cast_mulConst_mul_card (A B : Finset G) : (σₘ[A, B] * #A : 𝕜) = #(A * B) := by
  norm_cast; exact mulConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_subConst_mul_card]
/-
**Finset.cast_divConst_mul_card** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：cast_divConst_mul_card (A B : Finset G) : (δₘ[A, B] * #A : 𝕜) = #(A / B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用引理 `Finset.divConst_mul_card`：divConst_mul_card (A B : Finset G) : δₘ[A, B] 
* #A = #(A / B)
-/
lemma cast_divConst_mul_card (A B : Finset G) : (δₘ[A, B] * #A : 𝕜) = #(A / B) := by
  norm_cast; exact divConst_mul_card _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_addConst]
/-
**Finset.card_mul_cast_mulConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_cast_mulConst (A B : Finset G) : (#A * σₘ[A, B] : 𝕜) = #(A * B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用引理 `Finset.card_mul_mulConst`：card_mul_mulConst (A B : Finset G) : #A * σₘ[A
, B] = #(A * B)
-/
lemma card_mul_cast_mulConst (A B : Finset G) : (#A * σₘ[A, B] : 𝕜) = #(A * B) := by
  norm_cast; exact card_mul_mulConst _ _

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_subConst]
/-
**Finset.card_mul_cast_divConst** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_cast_divConst (A B : Finset G) : (#A * δₘ[A, B] : 𝕜) = #(A / B)
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用引理 `Finset.card_mul_divConst`：card_mul_divConst (A B : Finset G) : #A * δₘ[A
, B] = #(A / B)
-/
lemma card_mul_cast_divConst (A B : Finset G) : (#A * δₘ[A, B] : 𝕜) = #(A / B) := by
  norm_cast; exact card_mul_divConst _ _

/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
/-
**Finset.divConst_le_mulConst_sq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_le_mulConst_sq : δₘ[A] <= σₘ[A] ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.divConst_empty_right`：divConst_empty_right (A : Finset G) : δₘ[A,
 ∅] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mulConst_empty_right`：mulConst_empty_right (A : Finset G) : σₘ[A,
 ∅] = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.divConst_mul_card`：divConst_mul_card (A B : Finset G) : δₘ[A, B] 
* #A = #(A / B)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.ruzsa_triangle_inequality_div_mul_mul`：ruzsa_triangle_inequality_
div_mul_mul (A B C : Finset G) : #(A / C) * #B <= #(A * B) * #(C * B)
· 使用引理 `Finset.mulConst_mul_card`：mulConst_mul_card (A B : Finset G) : σₘ[A, B] 
* #A = #(A * B)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 54 条，此处仅展示前 30 条）
-/
lemma divConst_le_mulConst_sq : δₘ[A] ≤ σₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A / A) * (#A : ℚ≥0) := by rw [← mul_assoc, divConst_mul_card]
    _ ≤ #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul_mul ..
    _ = _ := by rw [← mulConst_mul_card]; ring

end Group

open scoped Combinatorics.Additive

section CommGroup
variable {G : Type*} [CommGroup G] [DecidableEq G] {A B : Finset G}

@[to_additive (attr := simp)]
/-
**Finset.mulConst_inv_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_inv_left (A B : Finset G) : σₘ[A⁻¹, B] = δₘ[A, B]
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
-/
lemma mulConst_inv_left (A B : Finset G) : σₘ[A⁻¹, B] = δₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, mul_inv_rev, inv_inv, inv_mul_eq_div]

@[to_additive (attr := simp)]
/-
**Finset.divConst_inv_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：divConst_inv_left (A B : Finset G) : δₘ[A⁻¹, B] = σₘ[A, B]
参数：A B : Finset G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mulConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.mulConst B = ↑(A * B).card / ↑A.card
· 使用定理 `Finset.divConst.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decida
bleEq G] (A B : Finset G), A.divConst B = ↑(A / B).card / ↑A.card
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma divConst_inv_left (A B : Finset G) : δₘ[A⁻¹, B] = σₘ[A, B] := by
  rw [mulConst, divConst, card_inv, ← card_inv, inv_div, div_inv_eq_mul, mul_comm]

/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
/-
**Finset.mulConst_le_divConst_sq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mulConst_le_divConst_sq : σₘ[A] <= δₘ[A] ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mulConst_empty_right`：mulConst_empty_right (A : Finset G) : σₘ[A,
 ∅] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.divConst_empty_right`：divConst_empty_right (A : Finset G) : δₘ[A,
 ∅] = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.mulConst_mul_card`：mulConst_mul_card (A B : Finset G) : σₘ[A, B] 
* #A = #(A * B)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.ruzsa_triangle_inequality_mul_div_div`：ruzsa_triangle_inequality_
mul_div_div (A B C : Finset G) : #(A * C) * #B <= #(A / B) * #(B / C)
· 使用引理 `Finset.divConst_mul_card`：divConst_mul_card (A B : Finset G) : δₘ[A, B] 
* #A = #(A / B)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 54 条，此处仅展示前 30 条）
-/
lemma mulConst_le_divConst_sq : σₘ[A] ≤ δₘ[A] ^ 2 := by
  obtain rfl | hA' := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A * A) * (#A : ℚ≥0) := by rw [← mul_assoc, mulConst_mul_card]
    _ ≤ #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div_div ..
    _ = _ := by rw [← divConst_mul_card]; ring

end CommGroup
end Finset

