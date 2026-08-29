/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Partial sums of geometric series in a field

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^iy^{n - 1 - i}=\frac{x^n-y^{n-m}x^m}{x-y}$
  in a field.

Several variants are recorded, generalising in particular to the case of a division ring in
which `x` and `y` commute.
-/

public section

assert_not_exists IsOrderedRing

variable {R K : Type*}

open Finset MulOpposite

section DivisionRing
variable [DivisionRing K] {x y : K}

/--
theorem `Commute.geom_sum₂` / 定理 `Commute.geom_sum₂`

English:
theorem Commute.geom_sum₂
  statement: (h' : Commute x y) (h : x != y)
  proof: by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul]; rw [mul_div_cancel_right₀ _ this]

中文:
定理 Commute.geom_sum₂
  结论: (h' : Commute x y) (h : x != y)
  证明: by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul]; rw [mul_div_cancel_right₀ _ this]
-/
protected theorem Commute.geom_sum₂ (h' : Commute x y) (h : x != y)
    (n : Nat) : ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul]; rw [mul_div_cancel_right₀ _ this]

/--
theorem `geom_sum_eq` / 定理 `geom_sum_eq`

English:
theorem geom_sum_eq
  given: (h : x != 1) (n : Nat)
  statement: ∑ i in range n, x ^ i = (x ^ n - 1) / (x - 1)
  proof: by
  have : x - 1 != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul]; rw [mul_div_cancel_right₀ _ this]

中文:
定理 geom_sum_eq
  条件: (h : x != 1) (n : 自然数)
  结论: ∑ i in range n, x ^ i = (x ^ n - 1) / (x - 1)
  证明: by
  have : x - 1 != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul]; rw [mul_div_cancel_right₀ _ this]

Depends on / 依赖: geom_sum_mul, sub_eq_iff_eq_add
-/
theorem geom_sum_eq (h : x != 1) (n : Nat) : ∑ i in range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul]; rw [mul_div_cancel_right₀ _ this]

/--
theorem `Commute.geom_sum₂_Ico` / 定理 `Commute.geom_sum₂_Ico`

English:
theorem Commute.geom_sum₂_Ico
  given: (h : Commute x y) (hxy : x != y) {m n : Nat} (hmn : m <= n)
  proof: by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn]; rw [mul_div_cancel_right₀ _ this]

中文:
定理 Commute.geom_sum₂_Ico
  条件: (h : Commute x y) (hxy : x != y) {m n : 自然数} (hmn : m <= n)
  证明: by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn]; rw [mul_div_cancel_right₀ _ this]
-/
protected theorem Commute.geom_sum₂_Ico (h : Commute x y) (hxy : x != y) {m n : Nat} (hmn : m <= n) :
    ∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y != 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn]; rw [mul_div_cancel_right₀ _ this]

/--
lemma `geom_sum_Ico` / 引理 `geom_sum_Ico`

English:
lemma geom_sum_Ico
  given: (hx : x != 1) {m n : Nat} (hmn : m <= n)
  proof: by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

中文:
引理 geom_sum_Ico
  条件: (hx : x != 1) {m n : 自然数} (hmn : m <= n)
  证明: by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

Depends on / 依赖: div_sub_div_same, geom_sum_eq, sub_sub_sub_cancel_right, sum_Ico_eq_sub
-/
lemma geom_sum_Ico (hx : x != 1) {m n : Nat} (hmn : m <= n) :
    ∑ i in Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

/--
lemma `geom_sum_Ico'` / 引理 `geom_sum_Ico'`

English:
lemma geom_sum_Ico'
  given: (hx : x != 1) {m n : Nat} (hmn : m <= n)
  proof: by
  simpa [geom_sum_Ico hx hmn] using neg_div_neg_eq (x ^ m - x ^ n) (1 - x)

中文:
引理 geom_sum_Ico'
  条件: (hx : x != 1) {m n : 自然数} (hmn : m <= n)
  证明: by
  simpa [geom_sum_Ico hx hmn] using neg_div_neg_eq (x ^ m - x ^ n) (1 - x)

Depends on / 依赖: geom_sum_Ico, neg_div_neg_eq
-/
lemma geom_sum_Ico' (hx : x != 1) {m n : Nat} (hmn : m <= n) :
    ∑ i in Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simpa [geom_sum_Ico hx hmn] using neg_div_neg_eq (x ^ m - x ^ n) (1 - x)

/--
lemma `geom_sum_inv` / 引理 `geom_sum_inv`

English:
lemma geom_sum_inv
  given: (hx1 : x != 1) (hx0 : x != 0) (n : Nat)
  proof: by
  have h₁ : x⁻¹ != 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 != 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 != 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ']; rw [mul_inv_rev]; rw [← mul_assoc]; rw [h]; rw [mul_assoc]; rw [mul_inv_cancel₀ hx0]; rw [mul_assoc]; rw [inv_mul_cancel₀ hx0]
  rw [geom_sum_eq h₁]; rw [div_eq_iff_mul_eq h₂]; rw [← mul_right_inj' h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_cancel₀ h₃]
  simp only [inv_pow, sub_eq_add_neg, mul_add, one_mul, mul_neg, add_mul, mul_inv_cancel₀ hx0,
    neg_mul, mul_assoc, mul_one, add_comm, neg_add_rev, neg_neg, h₄, add_left_comm]
  rw [add_comm _ (-x)]; rw [add_assoc]; rw [add_assoc _ _ 1]

中文:
引理 geom_sum_inv
  条件: (hx1 : x != 1) (hx0 : x != 0) (n : 自然数)
  证明: by
  have h₁ : x⁻¹ != 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 != 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 != 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ']; rw [mul_inv_rev]; rw [← mul_assoc]; rw [h]; rw [mul_assoc]; rw [mul_inv_cancel₀ hx0]; rw [mul_assoc]; rw [inv_mul_cancel₀ hx0]
  rw [geom_sum_eq h₁]; rw [div_eq_iff_mul_eq h₂]; rw [← mul_right_inj' h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_cancel₀ h₃]
  simp only [inv_pow, sub_eq_add_neg, mul_add, one_mul, mul_neg, add_mul, mul_inv_cancel₀ hx0,
    neg_mul, mul_assoc, mul_one, add_comm, neg_add_rev, neg_neg, h₄, add_left_comm]
  rw [add_comm _ (-x)]; rw [add_assoc]; rw [add_assoc _ _ 1]

Depends on / 依赖: Nat.recOn, div_eq_iff_mul_eq, geom_sum_eq, inv_eq_one_div, mul_, mul_assoc, mul_inv_rev, mul_right_inj, one_mul, pow_succ, sub_eq_zero
-/
lemma geom_sum_inv (hx1 : x != 1) (hx0 : x != 0) (n : Nat) :
    ∑ i in range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ != 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 != 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 != 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ']; rw [mul_inv_rev]; rw [← mul_assoc]; rw [h]; rw [mul_assoc]; rw [mul_inv_cancel₀ hx0]; rw [mul_assoc]; rw [inv_mul_cancel₀ hx0]
  rw [geom_sum_eq h₁]; rw [div_eq_iff_mul_eq h₂]; rw [← mul_right_inj' h₃]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_cancel₀ h₃]
  simp only [inv_pow, sub_eq_add_neg, mul_add, one_mul, mul_neg, add_mul, mul_inv_cancel₀ hx0,
    neg_mul, mul_assoc, mul_one, add_comm, neg_add_rev, neg_neg, h₄, add_left_comm]
  rw [add_comm _ (-x)]; rw [add_assoc]; rw [add_assoc _ _ 1]

end DivisionRing

section Field
variable [Field K] {x y : K}

/--
lemma `geom₂_sum` / 引理 `geom₂_sum`

English:
lemma geom₂_sum
  given: (h : x != y) (n : Nat)
  proof: (Commute.all x y).geom_sum₂ h n

中文:
引理 geom₂_sum
  条件: (h : x != y) (n : 自然数)
  证明: (Commute.all x y).geom_sum₂ h n

Depends on / 依赖: Commute, Commute.all
-/
lemma geom₂_sum (h : x != y) (n : Nat) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

/--
lemma `geom_sum₂_Ico` / 引理 `geom_sum₂_Ico`

English:
lemma geom_sum₂_Ico
  given: (hxy : x != y) {m n : Nat} (hmn : m <= n)
  proof: (Commute.all x y).geom_sum₂_Ico hxy hmn

中文:
引理 geom_sum₂_Ico
  条件: (hxy : x != y) {m n : 自然数} (hmn : m <= n)
  证明: (Commute.all x y).geom_sum₂_Ico hxy hmn

Depends on / 依赖: Commute, Commute.all
-/
lemma geom_sum₂_Ico (hxy : x != y) {m n : Nat} (hmn : m <= n) :
    (∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

end Field
