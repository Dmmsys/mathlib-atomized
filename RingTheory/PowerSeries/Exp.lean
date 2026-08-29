/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Ralf Stephan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Exponential Power Series

This file defines the exponential power series `exp A = ∑ Xⁿ/n!` over ℚ-algebras and develops
its key properties, including the fundamental differential equation `(exp A)' = exp A`,
a uniqueness characterization, and the functional equation for multiplication.

## Main definitions

* `PowerSeries.exp`: The exponential power series `exp A = ∑ Xⁿ/n!` over a ℚ-algebra `A`.

## Main results

* `PowerSeries.coeff_exp`: The coefficient of `exp A` at `n` is `1/n!`.
* `PowerSeries.constantCoeff_exp`: The constant term of `exp A` is `1`.
* `PowerSeries.map_exp`: `exp` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.derivative_exp`: The derivative of exp equals exp: `d⁄dX A (exp A) = exp A`.
* `PowerSeries.exp_unique_of_derivative_eq_self`: A power series with derivative equal to itself
  and constant term `1` must be `exp`.
* `PowerSeries.isUnit_exp`: `exp A` is a unit (invertible).
* `PowerSeries.order_exp`: The order of `exp A` is `0`.
* `PowerSeries.exp_mul_exp_eq_exp_add`: The functional equation `e^{aX} * e^{bX} = e^{(a+b)X}`.
* `PowerSeries.exp_mul_exp_neg_eq_one`: The identity `e^X * e^{-X} = 1`.
* `PowerSeries.exp_pow_eq_rescale_exp`: Powers of exp satisfy `(e^X)^k = e^{kX}`.
* `PowerSeries.exp_pow_sum`: Formula for the sum of powers of `exp`.
-/

@[expose] public section

namespace PowerSeries

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra Rat A] [Algebra Rat A']

open Nat

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: : PowerSeries A
  body: mk fun n => algebraMap Rat A (1 / n !)

中文:
定义 exp
  签名: : 幂级数 A
  定义体: mk fun n => algebraMap Rat A (1 / n !)

Depends on / 依赖: algebraMap
-/
def exp : PowerSeries A :=
  mk fun n => algebraMap Rat A (1 / n !)

variable {A A'} (n : Nat) (f : A ->+* A')

@[simp]
/--
theorem `coeff_exp` / 定理 `coeff_exp`

English:
theorem coeff_exp
  statement: coeff n (exp A) = algebraMap Rat A (1 / n !)
  proof: coeff_mk _ _

@[simp]

中文:
定理 coeff_exp
  结论: coeff n (exp A) = algebraMap 有理数 A (1 / n !)
  证明: coeff_mk _ _

@[simp]

Depends on / 依赖: TopologicalSpace, coeff_mk
-/
theorem coeff_exp : coeff n (exp A) = algebraMap Rat A (1 / n !) :=
  coeff_mk _ _

@[simp]
/--
theorem `constantCoeff_exp` / 定理 `constantCoeff_exp`

English:
theorem constantCoeff_exp
  statement: constantCoeff (exp A) = 1
  proof: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_exp]
  simp

@[simp]

中文:
定理 constantCoeff_exp
  结论: constantCoeff (exp A) = 1
  证明: by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_exp]
  simp

@[simp]

Depends on / 依赖: coeff_exp, coeff_zero_eq_constantCoeff_apply
-/
theorem constantCoeff_exp : constantCoeff (exp A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [coeff_exp]
  simp

@[simp]
/--
theorem `map_exp` / 定理 `map_exp`

English:
theorem map_exp
  statement: map (f : A ->+* A') (exp A) = exp A'
  proof: by
  ext
  simp

中文:
定理 map_exp
  结论: map (f : A ->+* A') (exp A) = exp A'
  证明: by
  ext
  simp

Depends on / 依赖: X.fintype, fintype
-/
theorem map_exp : map (f : A ->+* A') (exp A) = exp A' := by
  ext
  simp


/--
theorem `derivative_exp` / 定理 `derivative_exp`

English:
theorem derivative_exp
  given: (A : Type*) [CommRing A] [Algebra Rat A]
  proof: by
  ext n
  rw [coeff_derivative]; rw [coeff_exp]; rw [coeff_exp]
  have key : (n + 1 : A) = algebraMap Rat A (n + 1) := by
    rw [map_add]; rw [map_natCast]; rw [map_one]
  rw [key]; rw [← map_mul]; rw [factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_add_one]
  congr 1
  field_simp

中文:
定理 derivative_exp
  条件: (A : 类型) [交换环 A] [代数 有理数 A]
  证明: by
  ext n
  rw [coeff_derivative]; rw [coeff_exp]; rw [coeff_exp]
  have key : (n + 1 : A) = algebraMap Rat A (n + 1) := by
    rw [map_add]; rw [map_natCast]; rw [map_one]
  rw [key]; rw [← map_mul]; rw [factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_add_one]
  congr 1
  field_simp

Depends on / 依赖: Nat.cast_add_one, Nat.cast_mul, algebraMap, cast_add_one, cast_mul, coeff_derivative, coeff_exp, factorial_succ, map_add, map_mul, map_natCast, map_one
-/
theorem derivative_exp (A : Type*) [CommRing A] [Algebra Rat A] :
    d⁄dX A (exp A) = exp A := by
  ext n
  rw [coeff_derivative]; rw [coeff_exp]; rw [coeff_exp]
  have key : (n + 1 : A) = algebraMap Rat A (n + 1) := by
    rw [map_add]; rw [map_natCast]; rw [map_one]
  rw [key]; rw [← map_mul]; rw [factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_add_one]
  congr 1
  field_simp

/-! ### Uniqueness characterization -/

variable {A : Type*}

/--
theorem `exp_unique_of_derivative_eq_self` / 定理 `exp_unique_of_derivative_eq_self`

English:
theorem exp_unique_of_derivative_eq_self
  statement: [CommRing A] [Algebra Rat A] [IsAddTorsionFree A]
  proof: by
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff]; rw [hc]; rw [constantCoeff_exp]
  | succ n ih =>
    have eq1 : coeff n (d⁄dX A f) = coeff n f := congrArg (coeff n) hd
    rw [coeff_derivative] at eq1
    have eq2 : coeff n (d⁄dX A (exp A)) = coeff n (exp A) := congrArg (coeff n) (derivative_exp A)
    rw [coeff_derivative] at eq2
    rw [ih] at eq1
    have h : coeff (n + 1) f * (n + 1) = coeff (n + 1) (exp A) * (n + 1) := by
      rw [eq1]; rw [eq2]
    rw [← Nat.cast_succ]; rw [mul_comm]; rw [← nsmul_eq_mul]; rw [mul_comm]; rw [← nsmul_eq_mul] at h
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp h

中文:
定理 exp_unique_of_derivative_eq_self
  结论: [交换环 A] [代数 有理数 A] [是加法无挠 A]
  证明: by
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff]; rw [hc]; rw [constantCoeff_exp]
  | succ n ih =>
    have eq1 : coeff n (d⁄dX A f) = coeff n f := congrArg (coeff n) hd
    rw [coeff_derivative] at eq1
    have eq2 : coeff n (d⁄dX A (exp A)) = coeff n (exp A) := congrArg (coeff n) (derivative_exp A)
    rw [coeff_derivative] at eq2
    rw [ih] at eq1
    have h : coeff (n + 1) f * (n + 1) = coeff (n + 1) (exp A) * (n + 1) := by
      rw [eq1]; rw [eq2]
    rw [← Nat.cast_succ]; rw [mul_comm]; rw [← nsmul_eq_mul]; rw [mul_comm]; rw [← nsmul_eq_mul] at h
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp h

Depends on / 依赖: Nat.cast_succ, cast_succ, coeff_derivative, coeff_zero_eq_constantCoeff, constantCoeff_exp, derivative_exp, mul_comm, nsmul_eq_mu
-/
theorem exp_unique_of_derivative_eq_self [CommRing A] [Algebra Rat A] [IsAddTorsionFree A]
    {f : PowerSeries A} (hd : d⁄dX A f = f) (hc : constantCoeff f = 1) :
    f = exp A := by
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff]; rw [hc]; rw [constantCoeff_exp]
  | succ n ih =>
    have eq1 : coeff n (d⁄dX A f) = coeff n f := congrArg (coeff n) hd
    rw [coeff_derivative] at eq1
    have eq2 : coeff n (d⁄dX A (exp A)) = coeff n (exp A) := congrArg (coeff n) (derivative_exp A)
    rw [coeff_derivative] at eq2
    rw [ih] at eq1
    have h : coeff (n + 1) f * (n + 1) = coeff (n + 1) (exp A) * (n + 1) := by
      rw [eq1]; rw [eq2]
    rw [← Nat.cast_succ]; rw [mul_comm]; rw [← nsmul_eq_mul]; rw [mul_comm]; rw [← nsmul_eq_mul] at h
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp h


/--
theorem `isUnit_exp` / 定理 `isUnit_exp`

English:
theorem isUnit_exp
  given: (A : Type*) [Ring A] [Algebra Rat A]
  statement: IsUnit (exp A)
  proof: isUnit_iff_constantCoeff.mpr (by simp)

@[simp]

中文:
定理 isUnit_exp
  条件: (A : 类型) [环 A] [代数 有理数 A]
  结论: 是单位 (exp A)
  证明: isUnit_iff_constantCoeff.mpr (by simp)

@[simp]

Depends on / 依赖: X.unop.str, isUnit_iff_constantCoeff, isUnit_iff_constantCoeff.mpr
-/
theorem isUnit_exp (A : Type*) [Ring A] [Algebra Rat A] : IsUnit (exp A) :=
  isUnit_iff_constantCoeff.mpr (by simp)

@[simp]
/--
theorem `order_exp` / 定理 `order_exp`

English:
theorem order_exp
  given: (A : Type*) [Ring A] [Algebra Rat A] [Nontrivial A]
  statement: (exp A).order = 0
  proof: order_zero_of_unit (isUnit_exp A)

中文:
定理 order_exp
  条件: (A : 类型) [环 A] [代数 有理数 A] [非平凡 A]
  结论: (exp A).order = 0
  证明: order_zero_of_unit (isUnit_exp A)

Depends on / 依赖: isUnit_exp, order_zero_of_unit
-/
theorem order_exp (A : Type*) [Ring A] [Algebra Rat A] [Nontrivial A] : (exp A).order = 0 :=
  order_zero_of_unit (isUnit_exp A)


open RingHom

open Finset Nat

variable {A : Type*} [CommRing A]

/--
theorem `exp_mul_exp_eq_exp_add` / 定理 `exp_mul_exp_eq_exp_add`

English:
theorem exp_mul_exp_eq_exp_add
  given: [Algebra Rat A] (a b : A)
  proof: by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap Rat A (1 / ↑x.factorial) * algebraMap Rat A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap Rat A) (1 / ↑n.factorial))
    by convert! this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap Rat A) (n.choose x)]; rw [← map_mul]; rw [← map_mul]
  refine RingHom.congr_arg _ ?_
  rw [mul_one_div (↑(n.choose x) : Rat)]; rw [one_div_mul_one_div]
  symm
  rw [div_eq_iff]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [choose_eq_factorial_div_factorial]
  · norm_cast
    rw [cast_div_charZero]
    apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]

中文:
定理 exp_mul_exp_eq_exp_add
  条件: [代数 有理数 A] (a b : A)
  证明: by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap Rat A (1 / ↑x.factorial) * algebraMap Rat A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap Rat A) (1 / ↑n.factorial))
    by convert! this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap Rat A) (n.choose x)]; rw [← map_mul]; rw [← map_mul]
  refine RingHom.congr_arg _ ?_
  rw [mul_one_div (↑(n.choose x) : Rat)]; rw [one_div_mul_one_div]
  symm
  rw [div_eq_iff]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [choose_eq_factorial_div_factorial]
  · norm_cast
    rw [cast_div_charZero]
    apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk, OneHom, OneHom.coe_mk, add_pow, algebraMap, coe_mk, coeff_mk, coeff_mul, convert, factorial, map_mul, map_natCast, n.choose, n.factorial, rescale, sum_antidiagonal_eq_sum_range_succ_mk, sum_congr, sum_mul
-/
theorem exp_mul_exp_eq_exp_add [Algebra Rat A] (a b : A) :
    rescale a (exp A) * rescale b (exp A) = rescale (a + b) (exp A) := by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap Rat A (1 / ↑x.factorial) * algebraMap Rat A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap Rat A) (1 / ↑n.factorial))
    by convert! this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap Rat A) (n.choose x)]; rw [← map_mul]; rw [← map_mul]
  refine RingHom.congr_arg _ ?_
  rw [mul_one_div (↑(n.choose x) : Rat)]; rw [one_div_mul_one_div]
  symm
  rw [div_eq_iff]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [choose_eq_factorial_div_factorial]
  · norm_cast
    rw [cast_div_charZero]
    apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]

/--
theorem `exp_mul_exp_neg_eq_one` / 定理 `exp_mul_exp_neg_eq_one`

English:
theorem exp_mul_exp_neg_eq_one
  given: [Algebra Rat A]
  statement: exp A * evalNegHom (exp A) = 1
  proof: by
  convert! exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp

中文:
定理 exp_mul_exp_neg_eq_one
  条件: [代数 有理数 A]
  结论: exp A * evalNegHom (exp A) = 1
  证明: by
  convert! exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp

Depends on / 依赖: convert, exp_mul_exp_eq_exp_add
-/
theorem exp_mul_exp_neg_eq_one [Algebra Rat A] : exp A * evalNegHom (exp A) = 1 := by
  convert! exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp

/--
theorem `exp_pow_eq_rescale_exp` / 定理 `exp_pow_eq_rescale_exp`

English:
theorem exp_pow_eq_rescale_exp
  given: [Algebra Rat A] (k : Nat)
  statement: exp A ^ k = rescale (k : A) (exp A)
  proof: by
  induction k with
  | zero =>
    simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero,
      pow_zero (exp A), coe_comp]
  | succ k h =>
    simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
      id_apply, rescale_one] using pow_succ (exp A) k

中文:
定理 exp_pow_eq_rescale_exp
  条件: [代数 有理数 A] (k : 自然数)
  结论: exp A ^ k = rescale (k : A) (exp A)
  证明: by
  induction k with
  | zero =>
    simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero,
      pow_zero (exp A), coe_comp]
  | succ k h =>
    simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
      id_apply, rescale_one] using pow_succ (exp A) k

Depends on / 依赖: Function, Function.comp_apply, cast_add, cast_one, cast_zero, coe_comp, comp_apply, constantCoeff_exp, exp_mul_exp_eq_exp_add, id_apply, map_one, pow_succ, pow_zero, rescale_one, rescale_zero, succ_eq_add_one
-/
theorem exp_pow_eq_rescale_exp [Algebra Rat A] (k : Nat) : exp A ^ k = rescale (k : A) (exp A) := by
  induction k with
  | zero =>
    simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero,
      pow_zero (exp A), coe_comp]
  | succ k h =>
    simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
      id_apply, rescale_one] using pow_succ (exp A) k

/--
theorem `exp_pow_sum` / 定理 `exp_pow_sum`

English:
theorem exp_pow_sum
  given: [Algebra Rat A] (n : Nat)
  proof: by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, map_sum]

中文:
定理 exp_pow_sum
  条件: [代数 有理数 A] (n : 自然数)
  证明: by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, map_sum]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, coe_mk, coeff_exp, coeff_mk, exp_pow_eq_rescale_exp, map_sum, one_div, rescale
-/
theorem exp_pow_sum [Algebra Rat A] (n : Nat) :
    ((Finset.range n).sum fun k => exp A ^ k) =
      PowerSeries.mk fun p => (Finset.range n).sum
        fun k => (k ^ p : A) * algebraMap Rat A p.factorial⁻¹ := by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, map_sum]

end PowerSeries

end
