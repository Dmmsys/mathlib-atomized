/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a linearly ordered field. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` satisfies `IsStrictOrderedRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided in `Mathlib/Analysis/RCLike/Basic.lean` as

* `RCLike.toStrictOrderedCommRing`
* `RCLike.toStarOrderedRing`
* `RCLike.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

@[expose] public section

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
@[instance_reducible]
/-
**Complex.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：PartialOrder ℂ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonne
gative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partialOrder : PartialOrder ℂ where
  le z w := z.re ≤ w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_ge z w := by
    rw [lt_iff_le_not_ge]
    tauto
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2

namespace _root_.ComplexOrder

scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

/-
**Complex.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = w.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl
/-
**Complex.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lt_def {z w : Complex} : z < w ↔ z.re < w.re ∧ z.im = w.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl
/-
**Complex.nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nonneg_iff {z : Complex} : 0 <= z ↔ 0 <= z.re ∧ 0 = z.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.le_def`：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = 
w.im
-/
theorem nonneg_iff {z : ℂ} : 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im :=
  le_def
/-
**Complex.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：pos_iff {z : Complex} : 0 < z ↔ 0 < z.re ∧ 0 = z.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.lt_def`：lt_def {z w : Complex} : z < w ↔ z.re < w.re ∧ z.im = w.
im
-/
theorem pos_iff {z : ℂ} : 0 < z ↔ 0 < z.re ∧ 0 = z.im :=
  lt_def
/-
**Complex.nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nonpos_iff {z : Complex} : z <= 0 ↔ z.re <= 0 ∧ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.le_def`：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = 
w.im
-/
theorem nonpos_iff {z : ℂ} : z ≤ 0 ↔ z.re ≤ 0 ∧ z.im = 0 :=
  le_def
/-
**Complex.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_iff {z : Complex} : z < 0 ↔ z.re < 0 ∧ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.lt_def`：lt_def {z w : Complex} : z < w ↔ z.re < w.re ∧ z.im = w.
im
-/
theorem neg_iff {z : ℂ} : z < 0 ↔ z.re < 0 ∧ z.im = 0 :=
  lt_def
/-
**Complex.sq_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sq_nonneg_iff {z : Complex} : 0 <= z ^ 2 ↔ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.nonneg_iff`：nonneg_iff {z : Complex} : 0 <= z ↔ 0 <= z.re ∧ 0 = 
z.im
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_zero_iff_right`：mul_eq_zero_iff_right (hb : b != 0) : a * b = 0 ↔
 a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
（共 31 条，此处仅展示前 30 条）
-/
theorem sq_nonneg_iff {z : ℂ} : 0 ≤ z ^ 2 ↔ z.im = 0 := by
  rw [nonneg_iff, pow_two, mul_re, mul_im, mul_comm z.im z.re, ← mul_two, eq_comm,
    mul_eq_zero_iff_right two_ne_zero, ← pow_two, ← pow_two, mul_eq_zero]
  exact ⟨by aesop, fun h ↦ by simpa [h] using sq_nonneg z.re⟩
/-
**Complex.sq_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sq_nonpos_iff {z : Complex} : z ^ 2 <= 0 ↔ z.re = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.nonpos_iff`：nonpos_iff {z : Complex} : z <= 0 ↔ z.re <= 0 ∧ z.im
 = 0
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `mul_eq_zero_iff_right`：mul_eq_zero_iff_right (hb : b != 0) : a * b = 0 ↔
 a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
（共 32 条，此处仅展示前 30 条）
-/
theorem sq_nonpos_iff {z : ℂ} : z ^ 2 ≤ 0 ↔ z.re = 0 := by
  rw [nonpos_iff, pow_two, mul_re, mul_im, mul_comm z.im z.re, ← mul_two, mul_eq_zero_iff_right
    two_ne_zero, ← pow_two, ← pow_two, mul_eq_zero]
  exact ⟨by aesop, fun h ↦ by simpa [h] using sq_nonneg z.im⟩

@[simp, norm_cast]
/-
**Complex.real_le_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：real_le_real {x y : Real} : (x : Complex) <= (y : Complex) ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def, ofReal]

@[simp, norm_cast]
/-
**Complex.real_lt_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：real_lt_real {x y : Real} : (x : Complex) < (y : Complex) ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def, ofReal]

@[simp, norm_cast]
/-
**Complex.zero_le_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_le_real {x : Real} : (0 : Complex) <= (x : Complex) ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.real_le_real`：real_le_real {x y : Real} : (x : Complex) <= (y : 
Complex) ↔ x <= y
-/
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real

@[simp, norm_cast]
/-
**Complex.zero_lt_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_lt_real {x : Real} : (0 : Complex) < (x : Complex) ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.real_lt_real`：real_lt_real {x y : Real} : (x : Complex) < (y : C
omplex) ↔ x < y
-/
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real
/-
**Complex.not_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：not_le_iff {z w : Complex} : ¬z <= w ↔ w.re < z.re ∨ z.im != w.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.le_def`：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = 
w.im
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_or, not_le]
/-
**Complex.not_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：not_lt_iff {z w : Complex} : ¬z < w ↔ w.re <= z.re ∨ z.im != w.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.lt_def`：lt_def {z w : Complex} : z < w ↔ z.re < w.re ∧ z.im = w.
im
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_or, not_lt]
/-
**Complex.not_le_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：not_le_zero_iff {z : Complex} : ¬z <= 0 ↔ 0 < z.re ∨ z.im != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.not_le_iff`：not_le_iff {z w : Complex} : ¬z <= w ↔ w.re < z.re ∨
 z.im != w.im
-/
theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff
/-
**Complex.not_lt_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：not_lt_zero_iff {z : Complex} : ¬z < 0 ↔ 0 <= z.re ∨ z.im != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.not_lt_iff`：not_lt_iff {z w : Complex} : ¬z < w ↔ w.re <= z.re ∨
 z.im != w.im
-/
theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff
/-
**Complex.eq_re_of_ofReal_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eq_re_of_ofReal_le {r : Real} {z : Complex} (hz : (r : Complex) <= z) : z 
= z.re
参数：hz : (r : Complex) <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_eq_iff_re`：conj_eq_iff_re {z : Complex} : conj z = z ↔ (z.r
e : Complex) = z
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.le_def`：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = 
w.im
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
-/
theorem eq_re_of_ofReal_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re := by
  rw [eq_comm, ← conj_eq_iff_re, conj_eq_iff_im, ← (Complex.le_def.1 hz).2, Complex.ofReal_im]

@[simp]
/-
**Complex.re_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_eq_norm {z : Complex} : z.re = ‖z‖ ↔ 0 <= z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Complex.abs_re_eq_norm`：abs_re_eq_norm {z : Complex} : |z.re| = ‖z‖ ↔ z.
im = 0
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma re_eq_norm {z : ℂ} : z.re = ‖z‖ ↔ 0 ≤ z :=
  have : 0 ≤ ‖z‖ := norm_nonneg z
  ⟨fun h ↦ ⟨h.symm ▸ this, (abs_re_eq_norm.1 <| h.symm ▸ abs_of_nonneg this).symm⟩,
    fun ⟨h₁, h₂⟩ ↦ by rw [← abs_re_eq_norm.2 h₂.symm, abs_of_nonneg h₁]⟩

@[simp]
/-
**Complex.neg_re_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：neg_re_eq_norm {z : Complex} : -z.re = ‖z‖ ↔ z <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `Complex.re_eq_norm`：re_eq_norm {z : Complex} : z.re = ‖z‖ ↔ 0 <= z
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
-/
lemma neg_re_eq_norm {z : ℂ} : -z.re = ‖z‖ ↔ z ≤ 0 := by
  rw [← neg_re, ← norm_neg z, re_eq_norm]
  exact neg_nonneg.and <| eq_comm.trans neg_eq_zero

@[simp]
/-
**Complex.re_eq_neg_norm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_eq_neg_norm {z : Complex} : z.re = -‖z‖ ↔ z <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `Complex.neg_re_eq_norm`：neg_re_eq_norm {z : Complex} : -z.re = ‖z‖ ↔ z <
= 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma re_eq_neg_norm {z : ℂ} : z.re = -‖z‖ ↔ z ≤ 0 := by rw [← neg_eq_iff_eq_neg, neg_re_eq_norm]
/-
**Complex.monotone_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：monotone_ofReal : Monotone ofReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma monotone_ofReal : Monotone ofReal := by
  intro x y hxy
  simp only [real_le_real, hxy]

end Complex

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

alias ⟨_, ofReal_pos⟩ := zero_lt_real
alias ⟨_, ofReal_nonneg⟩ := zero_le_real
alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal _, Complex.ofReal _]
meta def evalComplexOfReal : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.ofReal $a) =>
    assumeInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa => return .positive q(ofReal_pos $pa)
    | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
    | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _ => throwError "not Complex.ofReal"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : 0 < x) : 0 < (x : ℂ) := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x : ℂ) := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : x ≠ 0) : (x : ℂ) ≠ 0 := by positivity

end Mathlib.Meta.Positivity

