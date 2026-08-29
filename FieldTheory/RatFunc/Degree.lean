/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The degree of rational functions

## Main definitions
We define the degree of a rational function, with values in `ℤ`:
- `intDegree` is the degree of a rational function, defined as the difference between the
  `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
  `intDegree 0 = 0`.
-/

@[expose] public section


noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section IntDegree

open Polynomial

variable [Field K]

/--
Definition of `intDegree` / `intDegree` 的定义

English:
definition intDegree
  signature: (x : K⟮X⟯)
  body: natDegree x.num - natDegree x.denom

@[simp]

中文:
定义 intDegree
  签名: (x : K⟮X⟯)
  定义体: natDegree x.num - natDegree x.denom

@[simp]

Depends on / 依赖: natDegree, x.denom, x.num
-/
def intDegree (x : K⟮X⟯) : Int :=
  natDegree x.num - natDegree x.denom

@[simp]
/--
theorem `intDegree_zero` / 定理 `intDegree_zero`

English:
theorem intDegree_zero
  statement: intDegree (0 : K⟮X⟯) = 0
  proof: by
  rw [intDegree]; rw [num_zero]; rw [natDegree_zero]; rw [denom_zero]; rw [natDegree_one]; rw [sub_self]

@[simp]

中文:
定理 intDegree_zero
  结论: intDegree (0 : K⟮X⟯) = 0
  证明: by
  rw [intDegree]; rw [num_zero]; rw [natDegree_zero]; rw [denom_zero]; rw [natDegree_one]; rw [sub_self]

@[simp]

Depends on / 依赖: denom_zero, intDegree, natDegree_one, natDegree_zero, num_zero, sub_self
-/
theorem intDegree_zero : intDegree (0 : K⟮X⟯) = 0 := by
  rw [intDegree]; rw [num_zero]; rw [natDegree_zero]; rw [denom_zero]; rw [natDegree_one]; rw [sub_self]

@[simp]
/--
theorem `intDegree_one` / 定理 `intDegree_one`

English:
theorem intDegree_one
  statement: intDegree (1 : K⟮X⟯) = 0
  proof: by
  rw [intDegree]; rw [num_one]; rw [denom_one]; rw [sub_self]

@[simp]

中文:
定理 intDegree_one
  结论: intDegree (1 : K⟮X⟯) = 0
  证明: by
  rw [intDegree]; rw [num_one]; rw [denom_one]; rw [sub_self]

@[simp]

Depends on / 依赖: denom_one, intDegree, num_one, sub_self
-/
theorem intDegree_one : intDegree (1 : K⟮X⟯) = 0 := by
  rw [intDegree]; rw [num_one]; rw [denom_one]; rw [sub_self]

@[simp]
/--
theorem `intDegree_C` / 定理 `intDegree_C`

English:
theorem intDegree_C
  given: (k : K)
  statement: intDegree (C k) = 0
  proof: by
  rw [intDegree]; rw [num_C]; rw [natDegree_C]; rw [denom_C]; rw [natDegree_one]; rw [sub_self]

@[simp]

中文:
定理 intDegree_C
  条件: (k : K)
  结论: intDegree (C k) = 0
  证明: by
  rw [intDegree]; rw [num_C]; rw [natDegree_C]; rw [denom_C]; rw [natDegree_one]; rw [sub_self]

@[simp]

Depends on / 依赖: denom_C, intDegree, natDegree_C, natDegree_one, num_C, sub_self
-/
theorem intDegree_C (k : K) : intDegree (C k) = 0 := by
  rw [intDegree]; rw [num_C]; rw [natDegree_C]; rw [denom_C]; rw [natDegree_one]; rw [sub_self]

@[simp]
/--
theorem `intDegree_X` / 定理 `intDegree_X`

English:
theorem intDegree_X
  statement: intDegree (X : K⟮X⟯) = 1
  proof: by
  rw [intDegree]; rw [num_X]; rw [Polynomial.natDegree_X]; rw [denom_X]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_one]; rw [Int.ofNat_zero]; rw [sub_zero]

@[simp]

中文:
定理 intDegree_X
  结论: intDegree (X : K⟮X⟯) = 1
  证明: by
  rw [intDegree]; rw [num_X]; rw [Polynomial.natDegree_X]; rw [denom_X]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_one]; rw [Int.ofNat_zero]; rw [sub_zero]

@[simp]

Depends on / 依赖: Int.ofNat_one, Int.ofNat_zero, Polynomial, Polynomial.natDegree_X, Polynomial.natDegree_one, denom_X, intDegree, natDegree_X, natDegree_one, num_X, ofNat_one, ofNat_zero, sub_zero
-/
theorem intDegree_X : intDegree (X : K⟮X⟯) = 1 := by
  rw [intDegree]; rw [num_X]; rw [Polynomial.natDegree_X]; rw [denom_X]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_one]; rw [Int.ofNat_zero]; rw [sub_zero]

@[simp]
/--
theorem `intDegree_polynomial` / 定理 `intDegree_polynomial`

English:
theorem intDegree_polynomial
  given: {p : K[X]}
  proof: by
  rw [intDegree]; rw [RatFunc.num_algebraMap]; rw [RatFunc.denom_algebraMap]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_zero]; rw [sub_zero]

中文:
定理 intDegree_polynomial
  条件: {p : K[X]}
  证明: by
  rw [intDegree]; rw [RatFunc.num_algebraMap]; rw [RatFunc.denom_algebraMap]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_zero]; rw [sub_zero]

Depends on / 依赖: Int.ofNat_zero, Polynomial, Polynomial.natDegree_one, RatFunc, RatFunc.denom_algebraMap, RatFunc.num_algebraMap, denom_algebraMap, intDegree, natDegree_one, num_algebraMap, ofNat_zero, sub_zero
-/
theorem intDegree_polynomial {p : K[X]} :
    intDegree (algebraMap K[X] K⟮X⟯ p) = natDegree p := by
  rw [intDegree]; rw [RatFunc.num_algebraMap]; rw [RatFunc.denom_algebraMap]; rw [Polynomial.natDegree_one]; rw [Int.ofNat_zero]; rw [sub_zero]

/--
theorem `intDegree_mul` / 定理 `intDegree_mul`

English:
theorem intDegree_mul
  given: {x y : K⟮X⟯} (hx : x != 0) (hy : y != 0)
  proof: by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero]; rw [←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_

中文:
定理 intDegree_mul
  条件: {x y : K⟮X⟯} (hx : x != 0) (hy : y != 0)
  证明: by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero]; rw [←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_

Depends on / 依赖: Polynomial, Polynomial.natDegree_mul, RatFunc, RatFunc.num_ne_zero, add_sub, denom_ne_zero, intDegree, mul_ne_zero, natDegree_mul, num_ne_zero, sub_add, sub_eq_sub_iff_add_eq_add, sub_sub, sub_sub_eq_add_sub, x.denom_ne_zero, y.denom_ne_zero
-/
theorem intDegree_mul {x y : K⟮X⟯} (hx : x != 0) (hy : y != 0) :
    intDegree (x * y) = intDegree x + intDegree y := by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero]; rw [←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)]; rw [← Polynomial.natDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy)]; rw [←
    Polynomial.natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (x * y).denom_ne_zero]; rw [RatFunc.num_denom_mul]

@[simp]
/--
theorem `intDegree_inv` / 定理 `intDegree_inv`

English:
theorem intDegree_inv
  given: (x : K⟮X⟯)
  statement: intDegree (x⁻¹) = - intDegree x
  proof: by
  by_cases hx : x = 0 <;> simp [hx, eq_neg_iff_add_eq_zero, ← intDegree_mul (inv_ne_zero hx) hx]

中文:
定理 intDegree_inv
  条件: (x : K⟮X⟯)
  结论: intDegree (x⁻¹) = - intDegree x
  证明: by
  by_cases hx : x = 0 <;> simp [hx, eq_neg_iff_add_eq_zero, ← intDegree_mul (inv_ne_zero hx) hx]

Depends on / 依赖: eq_neg_iff_add_eq_zero, intDegree_mul, inv_ne_zero
-/
theorem intDegree_inv (x : K⟮X⟯) : intDegree (x⁻¹) = - intDegree x := by
  by_cases hx : x = 0 <;> simp [hx, eq_neg_iff_add_eq_zero, ← intDegree_mul (inv_ne_zero hx) hx]

/--
lemma `intDegree_div` / 引理 `intDegree_div`

English:
lemma intDegree_div
  given: {x y : RatFunc K} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [div_eq_mul_inv]; rw [intDegree_mul]; rw [intDegree_inv]; rw [← sub_eq_add_neg] <;> grind

@[simp]

中文:
引理 intDegree_div
  条件: {x y : 有理函数 K} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [div_eq_mul_inv]; rw [intDegree_mul]; rw [intDegree_inv]; rw [← sub_eq_add_neg] <;> grind

@[simp]

Depends on / 依赖: div_eq_mul_inv, intDegree_inv, intDegree_mul, sub_eq_add_neg
-/
lemma intDegree_div {x y : RatFunc K} (hx : x != 0) (hy : y != 0) :
    (x / y).intDegree = x.intDegree - y.intDegree := by
  rw [div_eq_mul_inv]; rw [intDegree_mul]; rw [intDegree_inv]; rw [← sub_eq_add_neg] <;> grind

@[simp]
/--
theorem `intDegree_neg` / 定理 `intDegree_neg`

English:
theorem intDegree_neg
  given: (x : K⟮X⟯)
  statement: intDegree (-x) = intDegree x
  proof: by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)

中文:
定理 intDegree_neg
  条件: (x : K⟮X⟯)
  结论: intDegree (-x) = intDegree x
  证明: by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)

Depends on / 依赖: denom_ne_zero, intDegree, natDegree_neg, natDegree_sub_eq_of_prod_eq, neg_ne_zero, neg_ne_zero.mpr, neg_zero, num_denom_neg, num_ne_zero, x.num
-/
theorem intDegree_neg (x : K⟮X⟯) : intDegree (-x) = intDegree x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)

/--
theorem `intDegree_add` / 定理 `intDegree_add`

English:
theorem intDegree_add
  given: {x y : K⟮X⟯} (hxy : x + y != 0)
  proof: natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)

中文:
定理 intDegree_add
  条件: {x y : K⟮X⟯} (hxy : x + y != 0)
  证明: natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)

Depends on / 依赖: denom_ne_zero, mul_ne_zero, natDegree_sub_eq_of_prod_eq, num_denom_add, num_mul_denom_add_denom_mul_num_ne_zero, num_ne_zero, x.denom_ne_zero, y.denom_ne_zero
-/
theorem intDegree_add {x y : K⟮X⟯} (hxy : x + y != 0) :
    (x + y).intDegree =
      (x.num * y.denom + x.denom * y.num).natDegree - (x.denom * y.denom).natDegree :=
  natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)

/--
theorem `natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree` / 定理 `natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree`

English:
theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree
  statement: {x : K⟮X⟯}
  proof: by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]

中文:
定理 natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree
  结论: {x : K⟮X⟯}
  证明: by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]

Depends on / 依赖: denom_ne_zero, mul_assoc, mul_ne_zero, natDegree_sub_eq_of_prod_eq, num_ne_zero, x.denom_ne_zero
-/
theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : K⟮X⟯}
    (hx : x != 0) {s : K[X]} (hs : s != 0) :
    ((x.num * s).natDegree : Int) - (s * x.denom).natDegree = x.intDegree := by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]

/--
theorem `intDegree_add_le` / 定理 `intDegree_add_le`

English:
theorem intDegree_add_le
  given: {x y : K⟮X⟯} (hy : y != 0) (hxy : x + y != 0)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  rw [intDegree_add hxy]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero]; rw [mul_comm y.denom]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero]; rw [le_max_iff]; r

中文:
定理 intDegree_add_le
  条件: {x y : K⟮X⟯} (hy : y != 0) (hxy : x + y != 0)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  rw [intDegree_add hxy]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero]; rw [mul_comm y.denom]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero]; rw [le_max_iff]; r

Depends on / 依赖: Int.ofNat_le, denom_ne_zero, intDegree_add, le_max_iff, mul_comm, natDegree_add_le, natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree, ofNat_le, sub_le_sub_iff_right, x.denom_ne_zero, y.denom, y.denom_ne_zero, y.num
-/
theorem intDegree_add_le {x y : K⟮X⟯} (hy : y != 0) (hxy : x + y != 0) :
    intDegree (x + y) <= max (intDegree x) (intDegree y) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intDegree_add hxy]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero]; rw [mul_comm y.denom]; rw [←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero]; rw [le_max_iff]; rw [sub_le_sub_iff_right]; rw [Int.ofNat_le]; rw [sub_le_sub_iff_right]; rw [Int.ofNat_le]; rw [←
    le_max_iff]; rw [mul_comm y.num]
  exact natDegree_add_le _ _

end IntDegree

end RatFunc
