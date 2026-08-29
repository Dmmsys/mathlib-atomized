/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `hasSum_zeta_nat`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `hasSum_zeta_two` and `hasSum_zeta_four`: special cases given explicitly.
* `hasSum_one_div_nat_pow_mul_cos`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `hasSum_one_div_nat_pow_mul_sin`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/

@[expose] public section

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/


/--
Definition of `bernoulliFun` / `bernoulliFun` 的定义

English:
definition bernoulliFun
  signature: (k : Nat) (x : Real)
  body: (Polynomial.map (algebraMap Rat Real) (Polynomial.bernoulli k)).eval x

中文:
定义 bernoulliFun
  签名: (k : 自然数) (x : 实数)
  定义体: (Polynomial.map (algebraMap Rat Real) (Polynomial.bernoulli k)).eval x

Depends on / 依赖: Polynomial, Polynomial.bernoulli, Polynomial.map, algebraMap, bernoulli
-/
def bernoulliFun (k : Nat) (x : Real) : Real :=
  (Polynomial.map (algebraMap Rat Real) (Polynomial.bernoulli k)).eval x

section Evaluation

@[simp]
/--
theorem `bernoulliFun_zero` / 定理 `bernoulliFun_zero`

English:
theorem bernoulliFun_zero
  given: (x : Real)
  statement: bernoulliFun 0 x = 1
  proof: by
  simp only [bernoulliFun, Polynomial.bernoulli_zero, Polynomial.map_one, Polynomial.eval_one]

@[simp]

中文:
定理 bernoulliFun_zero
  条件: (x : 实数)
  结论: bernoulliFun 0 x = 1
  证明: by
  simp only [bernoulliFun, Polynomial.bernoulli_zero, Polynomial.map_one, Polynomial.eval_one]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.bernoulli_zero, Polynomial.eval_one, Polynomial.map_one, bernoulliFun, bernoulli_zero, eval_one, map_one
-/
theorem bernoulliFun_zero (x : Real) : bernoulliFun 0 x = 1 := by
  simp only [bernoulliFun, Polynomial.bernoulli_zero, Polynomial.map_one, Polynomial.eval_one]

@[simp]
/--
theorem `bernoulliFun_one` / 定理 `bernoulliFun_one`

English:
theorem bernoulliFun_one
  given: (x : Real)
  statement: bernoulliFun 1 x = x - 1 / 2
  proof: by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

@[simp]

中文:
定理 bernoulliFun_one
  条件: (x : 实数)
  结论: bernoulliFun 1 x = x - 1 / 2
  证明: by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

@[simp]

Depends on / 依赖: Finset, Finset.sum_range_succ, Polynomial, Polynomial.bernoulli_def, bernoulliFun, bernoulli_def, sum_range_succ
-/
theorem bernoulliFun_one (x : Real) : bernoulliFun 1 x = x - 1 / 2 := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

@[simp]
/--
theorem `bernoulliFun_two` / 定理 `bernoulliFun_two`

English:
theorem bernoulliFun_two
  given: (x : Real)
  statement: bernoulliFun 2 x = x ^ 2 - x + 6⁻¹
  proof: by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

中文:
定理 bernoulliFun_two
  条件: (x : 实数)
  结论: bernoulliFun 2 x = x ^ 2 - x + 6⁻¹
  证明: by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

Depends on / 依赖: Finset, Finset.sum_range_succ, Polynomial, Polynomial.bernoulli_def, bernoulliFun, bernoulli_def, sum_range_succ
-/
theorem bernoulliFun_two (x : Real) : bernoulliFun 2 x = x ^ 2 - x + 6⁻¹ := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

/--
theorem `bernoulliFun_eval_zero` / 定理 `bernoulliFun_eval_zero`

English:
theorem bernoulliFun_eval_zero
  given: (k : Nat)
  statement: bernoulliFun k 0 = bernoulli k
  proof: by
  rw [bernoulliFun]; rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]

中文:
定理 bernoulliFun_eval_zero
  条件: (k : 自然数)
  结论: bernoulliFun k 0 = bernoulli k
  证明: by
  rw [bernoulliFun]; rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]

Depends on / 依赖: Polynomial, Polynomial.bernoulli_eval_zero, Polynomial.eval_zero_map, bernoulliFun, bernoulli_eval_zero, eq_ratCast, eval_zero_map
-/
theorem bernoulliFun_eval_zero (k : Nat) : bernoulliFun k 0 = bernoulli k := by
  rw [bernoulliFun]; rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]

/--
theorem `bernoulliFun_endpoints_eq_of_ne_one` / 定理 `bernoulliFun_endpoints_eq_of_ne_one`

English:
theorem bernoulliFun_endpoints_eq_of_ne_one
  given: {k : Nat} (hk : k != 1)
  proof: by
  rw [bernoulliFun_eval_zero]; rw [bernoulliFun]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]; rw [bernoulli_eq_bernoulli'_of_ne_one hk]; rw [eq_ratCast]

中文:
定理 bernoulliFun_endpoints_eq_of_ne_one
  条件: {k : 自然数} (hk : k != 1)
  证明: by
  rw [bernoulliFun_eval_zero]; rw [bernoulliFun]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]; rw [bernoulli_eq_bernoulli'_of_ne_one hk]; rw [eq_ratCast]

Depends on / 依赖: Polynomial, Polynomial.bernoulli_eval_one, Polynomial.eval_one_map, _of_ne_one, bernoulliFun, bernoulliFun_eval_zero, bernoulli_eq_bernoulli, bernoulli_eval_one, eq_ratCast, eval_one_map
-/
theorem bernoulliFun_endpoints_eq_of_ne_one {k : Nat} (hk : k != 1) :
    bernoulliFun k 1 = bernoulliFun k 0 := by
  rw [bernoulliFun_eval_zero]; rw [bernoulliFun]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]; rw [bernoulli_eq_bernoulli'_of_ne_one hk]; rw [eq_ratCast]

/--
theorem `bernoulliFun_eval_one` / 定理 `bernoulliFun_eval_one`

English:
theorem bernoulliFun_eval_one
  given: (k : Nat)
  statement: bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0
  proof: by
  rw [bernoulliFun]; rw [bernoulliFun_eval_zero]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]
  split_ifs with h
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast; ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_ratCast]

中文:
定理 bernoulliFun_eval_one
  条件: (k : 自然数)
  结论: bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0
  证明: by
  rw [bernoulliFun]; rw [bernoulliFun_eval_zero]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]
  split_ifs with h
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast; ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_ratCast]

Depends on / 依赖: Polynomial, Polynomial.bernoulli_eval_one, Polynomial.eval_one_map, _of_ne_one, _one, add_zero, bernoulli, bernoulliFun, bernoulliFun_eval_zero, bernoulli_eq_bernoulli, bernoulli_eval_one, bernoulli_one, eq_ratCast, eval_one_map, split_ifs
-/
theorem bernoulliFun_eval_one (k : Nat) : bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0 := by
  rw [bernoulliFun]; rw [bernoulliFun_eval_zero]; rw [Polynomial.eval_one_map]; rw [Polynomial.bernoulli_eval_one]
  split_ifs with h
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast; ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_ratCast]

end Evaluation

section Calculus

/--
theorem `hasDerivAt_bernoulliFun` / 定理 `hasDerivAt_bernoulliFun`

English:
theorem hasDerivAt_bernoulliFun
  given: (k : Nat) (x : Real)
  proof: by
  convert! ((Polynomial.bernoulli k).map <| algebraMap Rat Real).hasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_natCast]

中文:
定理 hasDerivAt_bernoulliFun
  条件: (k : 自然数) (x : 实数)
  证明: by
  convert! ((Polynomial.bernoulli k).map <| algebraMap Rat Real).hasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_natCast]

Depends on / 依赖: Polynomial, Polynomial.bernoulli, Polynomial.derivative_bernoulli, Polynomial.derivative_map, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.map_mul, Polynomial.map_natCast, algebraMap, bernoulli, bernoulliFun, convert, derivative_bernoulli, derivative_map, eval_mul, eval_natCast, hasDerivAt, map_mul, map_natCast
-/
theorem hasDerivAt_bernoulliFun (k : Nat) (x : Real) :
    HasDerivAt (bernoulliFun k) (k * bernoulliFun (k - 1) x) x := by
  convert! ((Polynomial.bernoulli k).map <| algebraMap Rat Real).hasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_natCast]

variable (k : Nat)

/--
theorem `contDiff_bernoulliFun` / 定理 `contDiff_bernoulliFun`

English:
theorem contDiff_bernoulliFun
  statement: ContDiff Real ⊤ (bernoulliFun k)
  proof: by
  simp +unfoldPartialApp [bernoulliFun, Polynomial.eval_map_algebraMap, Polynomial.contDiff_aeval]

@[continuity, fun_prop]

中文:
定理 contDiff_bernoulliFun
  结论: ContDiff 实数 ⊤ (bernoulliFun k)
  证明: by
  simp +unfoldPartialApp [bernoulliFun, Polynomial.eval_map_algebraMap, Polynomial.contDiff_aeval]

@[continuity, fun_prop]

Depends on / 依赖: Polynomial, Polynomial.contDiff_aeval, Polynomial.eval_map_algebraMap, bernoulliFun, contDiff_aeval, eval_map_algebraMap, unfoldPartialApp
-/
theorem contDiff_bernoulliFun : ContDiff Real ⊤ (bernoulliFun k) := by
  simp +unfoldPartialApp [bernoulliFun, Polynomial.eval_map_algebraMap, Polynomial.contDiff_aeval]

@[continuity, fun_prop]
/--
theorem `continuous_bernoulliFun` / 定理 `continuous_bernoulliFun`

English:
theorem continuous_bernoulliFun
  statement: Continuous (bernoulliFun k)
  proof: Polynomial.continuous_aeval _

中文:
定理 continuous_bernoulliFun
  结论: Continuous (bernoulliFun k)
  证明: Polynomial.continuous_aeval _

Depends on / 依赖: Polynomial, Polynomial.continuous_aeval, continuous_aeval
-/
theorem continuous_bernoulliFun : Continuous (bernoulliFun k) := Polynomial.continuous_aeval _

/--
theorem `intervalIntegrable_bernoulliFun` / 定理 `intervalIntegrable_bernoulliFun`

English:
theorem intervalIntegrable_bernoulliFun
  given: (a b : Real)
  proof: (continuous_bernoulliFun k).intervalIntegrable a b

@[simp]

中文:
定理 intervalIntegrable_bernoulliFun
  条件: (a b : 实数)
  证明: (continuous_bernoulliFun k).intervalIntegrable a b

@[simp]

Depends on / 依赖: continuous_bernoulliFun, intervalIntegrable
-/
theorem intervalIntegrable_bernoulliFun (a b : Real) :
    IntervalIntegrable (bernoulliFun k) volume a b :=
  (continuous_bernoulliFun k).intervalIntegrable a b

@[simp]
/--
theorem `deriv_bernoulliFun` / 定理 `deriv_bernoulliFun`

English:
theorem deriv_bernoulliFun
  proof: by
  ext x
  exact (hasDerivAt_bernoulliFun _ _).deriv

中文:
定理 deriv_bernoulliFun
  证明: by
  ext x
  exact (hasDerivAt_bernoulliFun _ _).deriv

Depends on / 依赖: hasDerivAt_bernoulliFun
-/
theorem deriv_bernoulliFun :
    deriv (bernoulliFun k) = fun x => k * bernoulliFun (k - 1) x := by
  ext x
  exact (hasDerivAt_bernoulliFun _ _).deriv

/--
theorem `antideriv_bernoulliFun` / 定理 `antideriv_bernoulliFun`

English:
theorem antideriv_bernoulliFun
  given: (k : Nat) (x : Real)
  proof: by
  convert! (hasDerivAt_bernoulliFun (k + 1) x).div_const _ using 1
  simp [Nat.cast_add_one_ne_zero k]

中文:
定理 antideriv_bernoulliFun
  条件: (k : 自然数) (x : 实数)
  证明: by
  convert! (hasDerivAt_bernoulliFun (k + 1) x).div_const _ using 1
  simp [Nat.cast_add_one_ne_zero k]

Depends on / 依赖: Nat.cast_add_one_ne_zero, cast_add_one_ne_zero, convert, div_const, hasDerivAt_bernoulliFun
-/
theorem antideriv_bernoulliFun (k : Nat) (x : Real) :
    HasDerivAt (fun x => bernoulliFun (k + 1) x / (k + 1)) (bernoulliFun k x) x := by
  convert! (hasDerivAt_bernoulliFun (k + 1) x).div_const _ using 1
  simp [Nat.cast_add_one_ne_zero k]

/--
theorem `integral_bernoulliFun` / 定理 `integral_bernoulliFun`

English:
theorem integral_bernoulliFun
  statement: ∫ x : Real in 0..1, bernoulliFun k x = if k = 0 then 1 else 0
  proof: by
  simp +contextual [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun k x)
      (intervalIntegrable_bernoulliFun k _ _), bernoulliFun_eval_one, ← sub_div, ite_div]

中文:
定理 integral_bernoulliFun
  结论: ∫ x : 实数 in 0..1, bernoulliFun k x = if k = 0 then 1 else 0
  证明: by
  simp +contextual [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun k x)
      (intervalIntegrable_bernoulliFun k _ _), bernoulliFun_eval_one, ← sub_div, ite_div]

Depends on / 依赖: antideriv_bernoulliFun, bernoulliFun_eval_one, contextual, integral_eq_sub_of_hasDerivAt, intervalIntegrable_bernoulliFun, ite_div, sub_div
-/
theorem integral_bernoulliFun : ∫ x : Real in 0..1, bernoulliFun k x = if k = 0 then 1 else 0 := by
  simp +contextual [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun k x)
      (intervalIntegrable_bernoulliFun k _ _), bernoulliFun_eval_one, ← sub_div, ite_div]

variable {k} in
/--
theorem `integral_bernoulliFun_eq_zero` / 定理 `integral_bernoulliFun_eq_zero`

English:
theorem integral_bernoulliFun_eq_zero
  given: (hk : k != 0)
  proof: by
  rw [integral_bernoulliFun]; rw [if_neg hk]

中文:
定理 integral_bernoulliFun_eq_zero
  条件: (hk : k != 0)
  证明: by
  rw [integral_bernoulliFun]; rw [if_neg hk]

Depends on / 依赖: if_neg, integral_bernoulliFun
-/
theorem integral_bernoulliFun_eq_zero (hk : k != 0) :
    ∫ x : Real in 0..1, bernoulliFun k x = 0 := by
  rw [integral_bernoulliFun]; rw [if_neg hk]

/--
theorem `bernoulliFun_eq_integral` / 定理 `bernoulliFun_eq_integral`

English:
theorem bernoulliFun_eq_integral
  given: (k : Nat) (x y : Real)
  proof: by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]; rw [add_sub_cancel]
  · exact fun y _ => hasDerivAt_bernoulliFun _ y
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

中文:
定理 bernoulliFun_eq_integral
  条件: (k : 自然数) (x y : 实数)
  证明: by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]; rw [add_sub_cancel]
  · exact fun y _ => hasDerivAt_bernoulliFun _ y
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

Depends on / 依赖: Continuous, Continuous.intervalIntegrable, add_sub_cancel, fun_prop, hasDerivAt_bernoulliFun, integral_eq_sub_of_hasDerivAt, intervalIntegrable, intervalIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt
-/
theorem bernoulliFun_eq_integral (k : Nat) (x y : Real) :
    bernoulliFun (k + 1) y =
      bernoulliFun (k + 1) x + ∫ t in x..y, (k + 1 : Nat) * bernoulliFun k t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]; rw [add_sub_cancel]
  · exact fun y _ => hasDerivAt_bernoulliFun _ y
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

end Calculus

/--
theorem `bernoulliFun_eval_one_sub` / 定理 `bernoulliFun_eval_one_sub`

English:
theorem bernoulliFun_eval_one_sub
  given: {k : Nat} {x : Real}
  proof: by
  simpa [bernoulliFun, Polynomial.aeval_comp]
    using congr_arg (·.aeval x) (Polynomial.bernoulli_comp_one_sub_X k)

中文:
定理 bernoulliFun_eval_one_sub
  条件: {k : 自然数} {x : 实数}
  证明: by
  simpa [bernoulliFun, Polynomial.aeval_comp]
    using congr_arg (·.aeval x) (Polynomial.bernoulli_comp_one_sub_X k)

Depends on / 依赖: Polynomial, Polynomial.aeval_comp, Polynomial.bernoulli_comp_one_sub_X, aeval_comp, bernoulliFun, bernoulli_comp_one_sub_X, congr_arg
-/
theorem bernoulliFun_eval_one_sub {k : Nat} {x : Real} :
    bernoulliFun k (1 - x) = (-1) ^ k * bernoulliFun k x := by
  simpa [bernoulliFun, Polynomial.aeval_comp]
    using congr_arg (·.aeval x) (Polynomial.bernoulli_comp_one_sub_X k)

/--
theorem `bernoulliFun_mul` / 定理 `bernoulliFun_mul`

English:
theorem bernoulliFun_mul
  given: (k : Nat) {m : Nat} (m0 : m != 0) (x : Real)
  proof: by
  have m0' : (m : Real) != 0 := Nat.cast_ne_zero.mpr m0
  let f (k x) := bernoulliFun k (m * x) -
    m ^ k / m * ∑ i in Finset.range m, bernoulliFun k (x + i / ↑m)
  suffices h : forall x, f k x = 0 by
    rw [← sub_eq_zero]
    exact h x
  induction k with
  | zero =>
    intro x
    simp only 

中文:
定理 bernoulliFun_mul
  条件: (k : 自然数) {m : 自然数} (m0 : m != 0) (x : 实数)
  证明: by
  have m0' : (m : Real) != 0 := Nat.cast_ne_zero.mpr m0
  let f (k x) := bernoulliFun k (m * x) -
    m ^ k / m * ∑ i in Finset.range m, bernoulliFun k (x + i / ↑m)
  suffices h : forall x, f k x = 0 by
    rw [← sub_eq_zero]
    exact h x
  induction k with
  | zero =>
    intro x
    simp only 

Depends on / 依赖: Finset, Finset.card_range, Finset.range, Finset.sum_const, HasDerivAt, Nat.cast_ne_zero.mpr, bernoulliFun, bernoulliFun_zero, card_range, cast_ne_zero, mul_one, nsmul_eq_mul, one_div, pow_zero, sub_eq_zero, sum_const
-/
theorem bernoulliFun_mul (k : Nat) {m : Nat} (m0 : m != 0) (x : Real) :
    bernoulliFun k (m * x) =
      m ^ k / m * ∑ i in Finset.range m, bernoulliFun k (x + i / m) := by
  have m0' : (m : Real) != 0 := Nat.cast_ne_zero.mpr m0
  let f (k x) := bernoulliFun k (m * x) -
    m ^ k / m * ∑ i in Finset.range m, bernoulliFun k (x + i / ↑m)
  suffices h : forall x, f k x = 0 by
    rw [← sub_eq_zero]
    exact h x
  induction k with
  | zero =>
    intro x
    simp only [f, bernoulliFun_zero, pow_zero, one_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, sub_eq_zero]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr m0)]
  | succ k h =>
    have d (x) : HasDerivAt (f (k + 1)) (m * (k + 1) * f k x) x := by
      simp only [f, mul_sub, Finset.mul_sum, pow_succ, mul_div_cancel_right₀ _ m0',
        ← mul_assoc, mul_comm _ (_ / _), div_mul_cancel₀ _ m0']
      apply HasDerivAt.sub
      · rw [mul_assoc, mul_comm (m : Real) _, ← Nat.cast_add_one]
        exact (hasDerivAt_bernoulliFun _ _).comp _ (hasDerivAt_const_mul ..)
      · refine HasDerivAt.fun_sum fun i _ => ?_
        simp only [mul_assoc, ← Nat.cast_add_one]
        apply HasDerivAt.const_mul
        rw [← mul_one (_ * _)]
        exact (hasDerivAt_bernoulliFun _ _).comp _ ((hasDerivAt_id' _).add_const _)
    simp only [h, mul_zero] at d
    have fc (x) : f (k + 1) x = f (k + 1) 0 :=
      is_const_of_deriv_eq_zero (fun _ => (d _).differentiableAt) (fun _ => (d _).deriv) x 0
    generalize f (k + 1) 0 = c at fc
    have i : ∫ x in (0 : Real)..m⁻¹, f (k + 1) x = 0 := by
      simp only [f]
      rw [intervalIntegral.integral_sub]; rw [intervalIntegral.integral_comp_mul_left _ m0']; rw [mul_zero]; rw [mul_inv_cancel₀ m0']; rw [integral_bernoulliFun_eq_zero (by lia)]; rw [smul_zero]; rw [sub_eq_zero]; rw [intervalIntegral.integral_const_mul]; rw [eq_comm (a := 0)]; rw [mul_eq_zero]
      · right
        rw [intervalIntegral.integral_finsetSum]
        · simp only [intervalIntegral.integral_comp_add_right, zero_add, ← one_div, ← add_div,
            add_comm (1 : Real), ← Nat.cast_add_one]
          rw [intervalIntegral.sum_integral_adjacent_intervals]
          · simp [div_self m0', integral_bernoulliFun_eq_zero]
          · intros; exact Continuous.intervalIntegrable (by fun_prop) _ _
        · intros; exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
    simp only [fc, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_eq_zero, inv_eq_zero,
      Nat.cast_eq_zero, m0, false_or] at i
    simpa only [i] using fc


/--
theorem `bernoulliFun_eval_half_eq_zero` / 定理 `bernoulliFun_eval_half_eq_zero`

English:
theorem bernoulliFun_eval_half_eq_zero
  given: (k : Nat)
  statement: bernoulliFun (2 * k + 1) 2⁻¹ = 0
  proof: by
  have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := 2⁻¹)
  simp only [pow_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_neg, mul_one, neg_mul,
    one_mul, ← one_div, (sub_eq_of_eq_add (add_halves (1 : Real)).symm)] at h
  linarith

中文:
定理 bernoulliFun_eval_half_eq_zero
  条件: (k : 自然数)
  结论: bernoulliFun (2 * k + 1) 2⁻¹ = 0
  证明: by
  have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := 2⁻¹)
  simp only [pow_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_neg, mul_one, neg_mul,
    one_mul, ← one_div, (sub_eq_of_eq_add (add_halves (1 : Real)).symm)] at h
  linarith

Depends on / 依赖: Even.mul_right, Even.neg_pow, add_halves, bernoulliFun_eval_one_sub, even_two, mul_neg, mul_one, mul_right, neg_mul, neg_pow, one_div, one_mul, one_pow, pow_succ, sub_eq_of_eq_add
-/
theorem bernoulliFun_eval_half_eq_zero (k : Nat) : bernoulliFun (2 * k + 1) 2⁻¹ = 0 := by
  have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := 2⁻¹)
  simp only [pow_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_neg, mul_one, neg_mul,
    one_mul, ← one_div, (sub_eq_of_eq_add (add_halves (1 : Real)).symm)] at h
  linarith

/--
theorem `bernoulliFun_eval_half` / 定理 `bernoulliFun_eval_half`

English:
theorem bernoulliFun_eval_half
  given: (k : Nat)
  statement: bernoulliFun k 2⁻¹ = (2 / 2 ^ k - 1) * bernoulli k
  proof: by
  by_cases k1 : k = 1
  · simp [k1]
  · have m := bernoulliFun_mul k two_ne_zero 2⁻¹
    simp_rw [Nat.cast_ofNat, mul_inv_cancel₀ (two_ne_zero' Real), Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, ← one_div, add_halves,
      bernoulliFun_eval_one, if_neg k1, be

中文:
定理 bernoulliFun_eval_half
  条件: (k : 自然数)
  结论: bernoulliFun k 2⁻¹ = (2 / 2 ^ k - 1) * bernoulli k
  证明: by
  by_cases k1 : k = 1
  · simp [k1]
  · have m := bernoulliFun_mul k two_ne_zero 2⁻¹
    simp_rw [Nat.cast_ofNat, mul_inv_cancel₀ (two_ne_zero' Real), Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, ← one_div, add_halves,
      bernoulliFun_eval_one, if_neg k1, be

Depends on / 依赖: Finset, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, add_halves, add_zero, bernoulliFun_eval_one, bernoulliFun_eval_zero, bernoulliFun_mul, cast_ofNat, cast_one, cast_zero, if_neg, inv_div, one_div, simp_rw, sub_eq_iff_eq_add, sub_one_mul
-/
theorem bernoulliFun_eval_half (k : Nat) : bernoulliFun k 2⁻¹ = (2 / 2 ^ k - 1) * bernoulli k := by
  by_cases k1 : k = 1
  · simp [k1]
  · have m := bernoulliFun_mul k two_ne_zero 2⁻¹
    simp_rw [Nat.cast_ofNat, mul_inv_cancel₀ (two_ne_zero' Real), Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, ← one_div, add_halves,
      bernoulliFun_eval_one, if_neg k1, bernoulliFun_eval_zero, zero_div, add_zero, zero_add] at m
    rw [← inv_mul_eq_iff_eq_mul₀ (by positivity)]; rw [← sub_eq_iff_eq_add]; rw [← sub_one_mul]; rw [inv_div] at m
    rw [m]; rw [one_div]

end BernoulliFunProps

section BernoulliFourierCoeffs

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/


/--
Definition of `bernoulliFourierCoeff` / `bernoulliFourierCoeff` 的定义

English:
definition bernoulliFourierCoeff
  signature: (k : Nat) (n : Int)
  body: fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n

中文:
定义 bernoulliFourierCoeff
  签名: (k : 自然数) (n : 整数)
  定义体: fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n

Depends on / 依赖: bernoulliFun, fourierCoeffOn, zero_lt_one
-/
def bernoulliFourierCoeff (k : Nat) (n : Int) : Complex :=
  fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n

/--
theorem `bernoulliFourierCoeff_recurrence` / 定理 `bernoulliFourierCoeff_recurrence`

English:
theorem bernoulliFourierCoeff_recurrence
  given: (k : Nat) {n : Int} (hn : n != 0)
  proof: by
  unfold bernoulliFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ => (hasDerivAt_bernoulliFun k x).ofReal_comp)
      ((continuous_ofReal.comp <|
continuous_const.mul Polynomial.continuous _).intervalIntegrable
        _ _)]
  simp_rw [ofReal_one, ofReal_zero, sub_ze

中文:
定理 bernoulliFourierCoeff_recurrence
  条件: (k : 自然数) {n : 整数} (hn : n != 0)
  证明: by
  unfold bernoulliFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ => (hasDerivAt_bernoulliFun k x).ofReal_comp)
      ((continuous_ofReal.comp <|
continuous_const.mul Polynomial.continuous _).intervalIntegrable
        _ _)]
  simp_rw [ofReal_one, ofReal_zero, sub_ze

Depends on / 依赖: Polynomial, Polynomial.continuous, QuotientAddGroup, QuotientAddGroup.mk_zero, add_sub_cancel_left, bernoulliFourierCoeff, bernoulliFun_eval_one, continuous, continuous_const, continuous_const.mul, continuous_ofReal, continuous_ofReal.comp, fourierCoeffOn_of_hasDerivAt, fourier_eval_zero, hasDerivAt_bernoulliFun, intervalIntegrable, mk_zero, ofReal_comp, ofReal_one, ofReal_sub
-/
theorem bernoulliFourierCoeff_recurrence (k : Nat) {n : Int} (hn : n != 0) :
    bernoulliFourierCoeff k n =
      1 / (-2 * π * I * n) * (ite (k = 1) 1 0 - k * bernoulliFourierCoeff (k - 1) n) := by
  unfold bernoulliFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ => (hasDerivAt_bernoulliFun k x).ofReal_comp)
      ((continuous_ofReal.comp <|
continuous_const.mul Polynomial.continuous _).intervalIntegrable
        _ _)]
  simp_rw [ofReal_one, ofReal_zero, sub_zero, one_mul]
  rw [QuotientAddGroup.mk_zero]; rw [fourier_eval_zero]; rw [one_mul]; rw [← ofReal_sub]; rw [bernoulliFun_eval_one]; rw [add_sub_cancel_left]
  congr 2
  · split_ifs <;> simp only [ofReal_one, ofReal_zero]
  · simp_rw [ofReal_mul, ofReal_natCast, fourierCoeffOn.const_mul]

/--
theorem `bernoulli_zero_fourier_coeff` / 定理 `bernoulli_zero_fourier_coeff`

English:
theorem bernoulli_zero_fourier_coeff
  given: {n : Int} (hn : n != 0)
  statement: bernoulliFourierCoeff 0 n = 0
  proof: by
  simpa using bernoulliFourierCoeff_recurrence 0 hn

中文:
定理 bernoulli_zero_fourier_coeff
  条件: {n : 整数} (hn : n != 0)
  结论: bernoulliFourierCoeff 0 n = 0
  证明: by
  simpa using bernoulliFourierCoeff_recurrence 0 hn

Depends on / 依赖: bernoulliFourierCoeff_recurrence
-/
theorem bernoulli_zero_fourier_coeff {n : Int} (hn : n != 0) : bernoulliFourierCoeff 0 n = 0 := by
  simpa using bernoulliFourierCoeff_recurrence 0 hn

/--
theorem `bernoulliFourierCoeff_zero` / 定理 `bernoulliFourierCoeff_zero`

English:
theorem bernoulliFourierCoeff_zero
  given: {k : Nat} (hk : k != 0)
  statement: bernoulliFourierCoeff k 0 = 0
  proof: by
  simp_rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one, one_smul, intervalIntegral.integral_ofReal, integral_bernoulliFun_eq_zero hk,
    ofReal_zero]

中文:
定理 bernoulliFourierCoeff_zero
  条件: {k : 自然数} (hk : k != 0)
  结论: bernoulliFourierCoeff k 0 = 0
  证明: by
  simp_rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one, one_smul, intervalIntegral.integral_ofReal, integral_bernoulliFun_eq_zero hk,
    ofReal_zero]

Depends on / 依赖: bernoulliFourierCoeff, div_one, fourierCoeffOn_eq_integral, fourier_zero, integral_bernoulliFun_eq_zero, integral_ofReal, intervalIntegral, intervalIntegral.integral_ofReal, neg_zero, ofReal_zero, one_smul, simp_rw, sub_zero
-/
theorem bernoulliFourierCoeff_zero {k : Nat} (hk : k != 0) : bernoulliFourierCoeff k 0 = 0 := by
  simp_rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one, one_smul, intervalIntegral.integral_ofReal, integral_bernoulliFun_eq_zero hk,
    ofReal_zero]

/--
theorem `bernoulliFourierCoeff_eq` / 定理 `bernoulliFourierCoeff_eq`

English:
theorem bernoulliFourierCoeff_eq
  given: {k : Nat} (hk : k != 0) (n : Int)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · rw [bernoulliFourierCoeff_zero hk, Int.cast_zero, mul_zero, zero_pow hk,
      div_zero]
  refine Nat.le_induction ?_ (fun k hk h'k => ?_) k (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulliFourierCoeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_s

中文:
定理 bernoulliFourierCoeff_eq
  条件: {k : 自然数} (hk : k != 0) (n : 整数)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · rw [bernoulliFourierCoeff_zero hk, Int.cast_zero, mul_zero, zero_pow hk,
      div_zero]
  refine Nat.le_induction ?_ (fun k hk h'k => ?_) k (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulliFourierCoeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_s

Depends on / 依赖: Int.cast_zero, Nat.cast_one, Nat.factorial_one, Nat.le_induction, Nat.one_le_iff_ne_zero.mpr, bernoulliFourierCoeff_recurrence, bernoulliFourierCoeff_zero, bernoulli_zero_fourier_coeff, cast_one, cast_zero, div_neg, div_zero, eq_or_ne, factorial_one, if_neg, if_true, le_induction, mul_one, mul_zero, neg_div
-/
theorem bernoulliFourierCoeff_eq {k : Nat} (hk : k != 0) (n : Int) :
    bernoulliFourierCoeff k n = -k ! / (2 * π * I * n) ^ k := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · rw [bernoulliFourierCoeff_zero hk, Int.cast_zero, mul_zero, zero_pow hk,
      div_zero]
  refine Nat.le_induction ?_ (fun k hk h'k => ?_) k (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulliFourierCoeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_self, neg_mul, one_mul, if_true,
      Nat.factorial_one, pow_one]
    rw [bernoulli_zero_fourier_coeff hn]; rw [sub_zero]; rw [mul_one]; rw [div_neg]; rw [neg_div]
  · rw [bernoulliFourierCoeff_recurrence (k + 1) hn, if_neg (by grind), Nat.add_sub_cancel k 1, h'k,
      Nat.factorial_succ, zero_sub, Nat.cast_mul, pow_add]
    ring

end BernoulliFourierCoeffs

section BernoulliPeriodized

/-! In this section we use the above evaluations of the Fourier coefficients of Bernoulli
polynomials, together with the theorem `has_pointwise_sum_fourier_series_of_summable` from Fourier
theory, to obtain an explicit formula for `∑ (n:ℤ), 1 / n ^ k * fourier n x`. -/


/--
Definition of `periodizedBernoulli` / `periodizedBernoulli` 的定义

English:
definition periodizedBernoulli
  signature: (k : Nat)
  body: AddCircle.liftIco 1 0 (bernoulliFun k)

中文:
定义 periodizedBernoulli
  签名: (k : 自然数)
  定义体: AddCircle.liftIco 1 0 (bernoulliFun k)

Depends on / 依赖: AddCircle, AddCircle.liftIco, bernoulliFun, liftIco
-/
def periodizedBernoulli (k : Nat) : 𝕌 -> Real :=
  AddCircle.liftIco 1 0 (bernoulliFun k)

/--
theorem `periodizedBernoulli.continuous` / 定理 `periodizedBernoulli.continuous`

English:
theorem periodizedBernoulli.continuous
  given: {k : Nat} (hk : k != 1)
  statement: Continuous (periodizedBernoulli k)
  proof: AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn

中文:
定理 periodizedBernoulli.continuous
  条件: {k : 自然数} (hk : k != 1)
  结论: Continuous (periodizedBernoulli k)
  证明: AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn

Depends on / 依赖: AddCircle, AddCircle.liftIco_zero_continuous, Polynomial, Polynomial.continuous, bernoulliFun_endpoints_eq_of_ne_one, continuous, continuousOn, liftIco_zero_continuous, mod_cast
-/
theorem periodizedBernoulli.continuous {k : Nat} (hk : k != 1) : Continuous (periodizedBernoulli k) :=
  AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn

/--
theorem `fourierCoeff_bernoulli_eq` / 定理 `fourierCoeff_bernoulli_eq`

English:
theorem fourierCoeff_bernoulli_eq
  given: {k : Nat} (hk : k != 0) (n : Int)
  proof: by
  have : ((↑) ∘ periodizedBernoulli k : 𝕌 -> Complex) = AddCircle.liftIco 1 0 ((↑) ∘ bernoulliFun k) := by
    ext1 x; rfl
  rw [this]; rw [fourierCoeff_liftIco_eq]
  simpa only [zero_add] using! bernoulliFourierCoeff_eq hk n

中文:
定理 fourierCoeff_bernoulli_eq
  条件: {k : 自然数} (hk : k != 0) (n : 整数)
  证明: by
  have : ((↑) ∘ periodizedBernoulli k : 𝕌 -> Complex) = AddCircle.liftIco 1 0 ((↑) ∘ bernoulliFun k) := by
    ext1 x; rfl
  rw [this]; rw [fourierCoeff_liftIco_eq]
  simpa only [zero_add] using! bernoulliFourierCoeff_eq hk n

Depends on / 依赖: AddCircle, AddCircle.liftIco, bernoulliFourierCoeff_eq, bernoulliFun, fourierCoeff_liftIco_eq, liftIco, periodizedBernoulli, zero_add
-/
theorem fourierCoeff_bernoulli_eq {k : Nat} (hk : k != 0) (n : Int) :
    fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 -> Complex) n = -k ! / (2 * π * I * n) ^ k := by
  have : ((↑) ∘ periodizedBernoulli k : 𝕌 -> Complex) = AddCircle.liftIco 1 0 ((↑) ∘ bernoulliFun k) := by
    ext1 x; rfl
  rw [this]; rw [fourierCoeff_liftIco_eq]
  simpa only [zero_add] using! bernoulliFourierCoeff_eq hk n

/--
theorem `summable_bernoulli_fourier` / 定理 `summable_bernoulli_fourier`

English:
theorem summable_bernoulli_fourier
  given: {k : Nat} (hk : 2 <= k)
  proof: by
  have :
      forall n : Int, -(k ! : Complex) / (2 * π * I * n) ^ k = -k ! / (2 * π * I) ^ k * (1 / (n : Complex) ^ k) := by
    intro n; rw [mul_one_div, div_div, ← mul_pow]
  simp_rw [this]
refine Summable.mul_left _ .of_norm ?_
  have : (fun x : Int => ‖1 / (x : Complex) ^ k‖) = fun x : Int 

中文:
定理 summable_bernoulli_fourier
  条件: {k : 自然数} (hk : 2 <= k)
  证明: by
  have :
      forall n : Int, -(k ! : Complex) / (2 * π * I * n) ^ k = -k ! / (2 * π * I) ^ k * (1 / (n : Complex) ^ k) := by
    intro n; rw [mul_one_div, div_div, ← mul_pow]
  simp_rw [this]
refine Summable.mul_left _ .of_norm ?_
  have : (fun x : Int => ‖1 / (x : Complex) ^ k‖) = fun x : Int 

Depends on / 依赖: Real.summable_one_div_int_pow, Summable, Summable.mul_left, abs_inv, div_div, mul_left, mul_one_div, mul_pow, norm_intCast, norm_inv, norm_pow, of_norm, one_div, pow_abs, simp_rw, summable_abs_iff, summable_one_div_int_pow
-/
theorem summable_bernoulli_fourier {k : Nat} (hk : 2 <= k) :
    Summable (fun n => -k ! / (2 * π * I * n) ^ k : Int -> Complex) := by
  have :
      forall n : Int, -(k ! : Complex) / (2 * π * I * n) ^ k = -k ! / (2 * π * I) ^ k * (1 / (n : Complex) ^ k) := by
    intro n; rw [mul_one_div, div_div, ← mul_pow]
  simp_rw [this]
refine Summable.mul_left _ .of_norm ?_
  have : (fun x : Int => ‖1 / (x : Complex) ^ k‖) = fun x : Int => |1 / (x : Real) ^ k| := by
    ext1 x
    simp only [one_div, norm_inv, norm_pow, norm_intCast, pow_abs, abs_inv]
  simp_rw [this]
  rwa [summable_abs_iff, Real.summable_one_div_int_pow]

/--
theorem `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` / 定理 `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun`

English:
theorem hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
  statement: {k : Nat} (hk : 2 <= k) {x : Real}
  proof: by
  -- first show it suffices to prove result for `Ico 0 1`
  suffices forall {y : Real}, y in Ico (0 : Real) 1 ->
      HasSum (fun (n : Int) => 1 / (n : Complex) ^ k * fourier n y)
        (-(2 * (π : Complex) * I) ^ k / k ! * bernoulliFun k y) by
    rw [← Ico_insert_right (zero_le_one' Real)]; 

中文:
定理 hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
  结论: {k : 自然数} (hk : 2 <= k) {x : 实数}
  证明: by
  -- first show it suffices to prove result for `Ico 0 1`
  suffices forall {y : Real}, y in Ico (0 : Real) 1 ->
      HasSum (fun (n : Int) => 1 / (n : Complex) ^ k * fourier n y)
        (-(2 * (π : Complex) * I) ^ k / k ! * bernoulliFun k y) by
    rw [← Ico_insert_right (zero_le_one' Real)]; 
-/
theorem hasSum_one_div_pow_mul_fourier_mul_bernoulliFun {k : Nat} (hk : 2 <= k) {x : Real}
    (hx : x in Icc (0 : Real) 1) :
    HasSum (fun n : Int => 1 / (n : Complex) ^ k * fourier n (x : 𝕌))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by
  -- first show it suffices to prove result for `Ico 0 1`
  suffices forall {y : Real}, y in Ico (0 : Real) 1 ->
      HasSum (fun (n : Int) => 1 / (n : Complex) ^ k * fourier n y)
        (-(2 * (π : Complex) * I) ^ k / k ! * bernoulliFun k y) by
    rw [← Ico_insert_right (zero_le_one' Real)]; rw [mem_insert_iff]; rw [or_comm] at hx
    rcases hx with (hx | rfl)
    · exact this hx
    · convert! this (left_mem_Ico.mpr zero_lt_one) using 1
      · rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
      · rw [bernoulliFun_endpoints_eq_of_ne_one (by lia : k != 1)]
  intro y hy
  let B : C(𝕌, Complex) :=
    ContinuousMap.mk ((↑) ∘ periodizedBernoulli k)
      (continuous_ofReal.comp (periodizedBernoulli.continuous (by lia)))
  have step1 : forall n : Int, fourierCoeff B n = -k ! / (2 * π * I * n) ^ k := by
    rw [ContinuousMap.coe_mk]; exact fourierCoeff_bernoulli_eq (by lia : k != 0)
  have step2 :=
    has_pointwise_sum_fourier_series_of_summable
      ((summable_bernoulli_fourier hk).congr fun n => (step1 n).symm) y
  simp_rw [step1] at step2
  convert! step2.mul_left (-(2 * ↑π * I) ^ k / (k ! : Complex)) using 2 with n
  · rw [smul_eq_mul, ← mul_assoc, mul_div, mul_neg, div_mul_cancel₀, neg_neg, mul_pow _ (n : Complex),
      ← div_div, div_self]
    · rw [Ne, pow_eq_zero_iff', not_and_or]
      exact Or.inl two_pi_I_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [ContinuousMap.coe_mk, Function.comp_apply, ofReal_inj, periodizedBernoulli,
      AddCircle.liftIco_coe_apply (show y in Ico 0 (0 + 1) by rwa [zero_add])]

end BernoulliPeriodized

section Cleanup

-- This section is just reformulating the results in a nicer form.
/--
theorem `hasSum_one_div_nat_pow_mul_fourier` / 定理 `hasSum_one_div_nat_pow_mul_fourier`

English:
theorem hasSum_one_div_nat_pow_mul_fourier
  given: {k : Nat} (hk : 2 <= k) {x : Real} (hx : x in Icc (0 : Real) 1)
  proof: by
  convert! (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).nat_add_neg using 1
  · ext1 n
    rw [Int.cast_neg]; rw [mul_add]; rw [← mul_assoc]
    conv_rhs => rw [neg_eq_neg_one_mul, mul_pow, ← div_div]
    congr 2
    rw [div_mul_eq_mul_div₀]; rw [one_mul]
    congr 1
    rw [eq_div_iff

中文:
定理 hasSum_one_div_nat_pow_mul_fourier
  条件: {k : 自然数} (hk : 2 <= k) {x : 实数} (hx : x in Icc (0 : 实数) 1)
  证明: by
  convert! (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).nat_add_neg using 1
  · ext1 n
    rw [Int.cast_neg]; rw [mul_add]; rw [← mul_assoc]
    conv_rhs => rw [neg_eq_neg_one_mul, mul_pow, ← div_div]
    congr 2
    rw [div_mul_eq_mul_div₀]; rw [one_mul]
    congr 1
    rw [eq_div_iff

Depends on / 依赖: Int.cast_neg, Int.cast_zero, add_zero, cast_neg, cast_zero, conv_rhs, convert, div_div, div_zero, eq_div_iff, hasSum_one_div_pow_mul_fourier_mul_bernoulliFun, mul_add, mul_assoc, mul_pow, nat_add_neg, neg_eq_neg_one_mul, neg_ne_zero, neg_neg, one_mul, one_ne_zero
-/
theorem hasSum_one_div_nat_pow_mul_fourier {k : Nat} (hk : 2 <= k) {x : Real} (hx : x in Icc (0 : Real) 1) :
    HasSum
      (fun n : Nat =>
        (1 : Complex) / (n : Complex) ^ k * (fourier n (x : 𝕌) + (-1 : Complex) ^ k * fourier (-n) (x : 𝕌)))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by
  convert! (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).nat_add_neg using 1
  · ext1 n
    rw [Int.cast_neg]; rw [mul_add]; rw [← mul_assoc]
    conv_rhs => rw [neg_eq_neg_one_mul, mul_pow, ← div_div]
    congr 2
    rw [div_mul_eq_mul_div₀]; rw [one_mul]
    congr 1
    rw [eq_div_iff]; rw [← mul_pow]; rw [← neg_eq_neg_one_mul]; rw [neg_neg]; rw [one_pow]
    apply pow_ne_zero; rw [neg_ne_zero]; exact one_ne_zero
  · rw [Int.cast_zero, zero_pow (by positivity : k != 0), div_zero, zero_mul, add_zero]

/--
theorem `hasSum_one_div_nat_pow_mul_cos` / 定理 `hasSum_one_div_nat_pow_mul_cos`

English:
theorem hasSum_one_div_nat_pow_mul_cos
  given: {k : Nat} (hk : k != 0) {x : Real} (hx : x in Icc (0 : Real) 1)
  proof: by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * (2 * (π : Complex)) ^ (2 * k) / (2 * k)! * bernoulliFun (2 * k) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 <= 2 * k) hx using 3

中文:
定理 hasSum_one_div_nat_pow_mul_cos
  条件: {k : 自然数} (hk : k != 0) {x : 实数} (hx : x in Icc (0 : 实数) 1)
  证明: by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * (2 * (π : Complex)) ^ (2 * k) / (2 * k)! * bernoulliFun (2 * k) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 <= 2 * k) hx using 3

Depends on / 依赖: HasSum, I_sq, bernoulliFun, conv_rhs, convert, fourier, hasSum_one_div_nat_pow_mul_fourier, mul_pow, neg_one_sq, ofReal_two, one_mul, one_pow, pow_add, pow_mul, pow_one
-/
theorem hasSum_one_div_nat_pow_mul_cos {k : Nat} (hk : k != 0) {x : Real} (hx : x in Icc (0 : Real) 1) :
    HasSum (fun n : Nat => 1 / (n : Real) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : Real) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        (Polynomial.map (algebraMap Rat Real) (Polynomial.bernoulli (2 * k))).eval x) := by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * (2 * (π : Complex)) ^ (2 * k) / (2 * k)! * bernoulliFun (2 * k) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 <= 2 * k) hx using 3
    · rw [pow_mul (-1 : Complex), neg_one_sq, one_pow, one_mul]
    · rw [pow_add, pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : Real) : Complex) = 2 := by norm_cast
  convert! ((hasSum_iff _ _).mp (this.div_const 2)).1 with n
  · convert! (ofReal_re _).symm
    rw [ofReal_mul]; rw [← mul_div]; congr
    · rw [ofReal_div, ofReal_one, ofReal_pow]; rfl
    · rw [ofReal_cos, ofReal_mul, fourier_coe_apply, fourier_coe_apply, cos, ofReal_one, div_one,
        div_one, ofReal_mul, ofReal_mul, ofReal_two, Int.cast_neg, Int.cast_natCast,
        ofReal_natCast]
      congr 3
      · ring
      · ring
  · convert! (ofReal_re _).symm
    rw [ofReal_mul]; rw [ofReal_div]; rw [ofReal_div]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_natCast]; rw [ofReal_mul]; rw [ofReal_two]; rw [ofReal_one]
    rw [bernoulliFun]
    ring

/--
theorem `hasSum_one_div_nat_pow_mul_sin` / 定理 `hasSum_one_div_nat_pow_mul_sin`

English:
theorem hasSum_one_div_nat_pow_mul_sin
  given: {k : Nat} (hk : k != 0) {x : Real} (hx : x in Icc (0 : Real) 1)
  proof: by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * I * (2 * π : Complex) ^ (2 * k + 1) / (2 * k + 1)! *
        bernoulliFun (2 * k + 1) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by li

中文:
定理 hasSum_one_div_nat_pow_mul_sin
  条件: {k : 自然数} (hk : k != 0) {x : 实数} (hx : x in Icc (0 : 实数) 1)
  证明: by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * I * (2 * π : Complex) ^ (2 * k + 1) / (2 * k + 1)! *
        bernoulliFun (2 * k + 1) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by li

Depends on / 依赖: HasSum, bernoulliFun, convert, fourier, hasSum_one_div_nat_pow_mul_fourier, neg_eq_neg_one_mul, neg_one_sq, one_mul, one_pow, pow_ad, pow_add, pow_mul, pow_one, sub_eq_add_neg
-/
theorem hasSum_one_div_nat_pow_mul_sin {k : Nat} (hk : k != 0) {x : Real} (hx : x in Icc (0 : Real) 1) :
    HasSum (fun n : Nat => 1 / (n : Real) ^ (2 * k + 1) * Real.sin (2 * π * n * x))
      ((-1 : Real) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
        (Polynomial.map (algebraMap Rat Real) (Polynomial.bernoulli (2 * k + 1))).eval x) := by
  have :
    HasSum (fun n : Nat => 1 / (n : Complex) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
      ((-1 : Complex) ^ (k + 1) * I * (2 * π : Complex) ^ (2 * k + 1) / (2 * k + 1)! *
        bernoulliFun (2 * k + 1) x) := by
    convert! hasSum_one_div_nat_pow_mul_fourier (by lia : 2 <= 2 * k + 1) hx using 1
    · ext1 n
      rw [pow_add (-1 : Complex)]; rw [pow_mul (-1 : Complex)]; rw [neg_one_sq]; rw [one_pow]; rw [one_mul]; rw [pow_one]; rw [←
        neg_eq_neg_one_mul]; rw [← sub_eq_add_neg]
    · congr
      rw [pow_add]; rw [pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_add, pow_one, pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : Real) : Complex) = 2 := by norm_cast
  convert! ((hasSum_iff _ _).mp (this.div_const (2 * I))).1
  · convert! (ofReal_re _).symm
    rw [ofReal_mul]; rw [← mul_div]; congr
    · rw [ofReal_div, ofReal_one, ofReal_pow]; rfl
    · rw [ofReal_sin, ofReal_mul, fourier_coe_apply, fourier_coe_apply, sin, ofReal_one, div_one,
        div_one, ofReal_mul, ofReal_mul, ofReal_two, Int.cast_neg, Int.cast_natCast,
        ofReal_natCast, ← div_div, div_I, div_mul_eq_mul_div₀, ← neg_div, ← neg_mul, neg_sub]
      congr 4
      · ring
      · ring
  · convert! (ofReal_re _).symm
    rw [ofReal_mul]; rw [ofReal_div]; rw [ofReal_div]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_natCast]; rw [ofReal_mul]; rw [ofReal_two]; rw [ofReal_one]; rw [← div_div]; rw [div_I]; rw [div_mul_eq_mul_div₀]
    have : forall α β γ δ : Complex, α * I * β / γ * δ * I = I ^ 2 * α * β / γ * δ := by intros; ring
    rw [this]; rw [I_sq]
    rw [bernoulliFun]
    ring

/--
theorem `hasSum_zeta_nat` / 定理 `hasSum_zeta_nat`

English:
theorem hasSum_zeta_nat
  given: {k : Nat} (hk : k != 0)
  proof: by
  convert! hasSum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one) using 1
  · ext1 n; rw [mul_zero, Real.cos_zero, mul_one]
  rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]
  have : (2 : Real) ^ (2 * k - 1) = (2 : Real) ^ (2 * k) / 2 := by
    rw [eq

中文:
定理 hasSum_zeta_nat
  条件: {k : 自然数} (hk : k != 0)
  证明: by
  convert! hasSum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one) using 1
  · ext1 n; rw [mul_zero, Real.cos_zero, mul_one]
  rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]
  have : (2 : Real) ^ (2 * k - 1) = (2 : Real) ^ (2 * k) / 2 := by
    rw [eq

Depends on / 依赖: Nat.sub_add_cancel, Polynomial, Polynomial.bernoulli_eval_zero, Polynomial.eval_zero_map, Real.cos_zero, bernoulli_eval_zero, conv_lhs, convert, cos_zero, eq_div_iff, eq_ratCast, eval_zero_map, hasSum_one_div_nat_pow_mul_cos, left_mem_Icc, left_mem_Icc.mpr, mul_one, mul_pow, mul_zero, pow_add, pow_one
-/
theorem hasSum_zeta_nat {k : Nat} (hk : k != 0) :
    HasSum (fun n : Nat => 1 / (n : Real) ^ (2 * k))
      ((-1 : Real) ^ (k + 1) * (2 : Real) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (2 * k)!) := by
  convert! hasSum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one) using 1
  · ext1 n; rw [mul_zero, Real.cos_zero, mul_one]
  rw [Polynomial.eval_zero_map]; rw [Polynomial.bernoulli_eval_zero]; rw [eq_ratCast]
  have : (2 : Real) ^ (2 * k - 1) = (2 : Real) ^ (2 * k) / 2 := by
    rw [eq_div_iff (two_ne_zero' Real)]
    conv_lhs =>
      congr
      · skip
      · rw [← pow_one (2 : Real)]
    rw [← pow_add]; rw [Nat.sub_add_cancel]
    lia
  rw [this]; rw [mul_pow]
  ring

end Cleanup

section Examples

/--
theorem `hasSum_zeta_two` / 定理 `hasSum_zeta_two`

English:
theorem hasSum_zeta_two
  statement: HasSum (fun n : Nat => (1 : Real) / (n : Real) ^ 2) (π ^ 2 / 6)
  proof: by
  convert! hasSum_zeta_nat one_ne_zero using 1; rw [mul_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 != 1)]; rw [bernoulli'_two]
  simp [Nat.factorial]; ring

中文:
定理 hasSum_zeta_two
  结论: HasSum (fun n : 自然数 => (1 : 实数) / (n : 实数) ^ 2) (π ^ 2 / 6)
  证明: by
  convert! hasSum_zeta_nat one_ne_zero using 1; rw [mul_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 != 1)]; rw [bernoulli'_two]
  simp [Nat.factorial]; ring

Depends on / 依赖: Nat.factorial, _of_ne_one, _two, bernoulli, bernoulli_eq_bernoulli, convert, factorial, hasSum_zeta_nat, mul_one, one_ne_zero
-/
theorem hasSum_zeta_two : HasSum (fun n : Nat => (1 : Real) / (n : Real) ^ 2) (π ^ 2 / 6) := by
  convert! hasSum_zeta_nat one_ne_zero using 1; rw [mul_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 != 1)]; rw [bernoulli'_two]
  simp [Nat.factorial]; ring

/--
theorem `hasSum_zeta_four` / 定理 `hasSum_zeta_four`

English:
theorem hasSum_zeta_four
  statement: HasSum (fun n : Nat => (1 : Real) / (n : Real) ^ 4) (π ^ 4 / 90)
  proof: by
  convert! hasSum_zeta_nat two_ne_zero using 1
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one]; rw [bernoulli'_four]
  · simp [Nat.factorial]; ring
  · decide

中文:
定理 hasSum_zeta_four
  结论: HasSum (fun n : 自然数 => (1 : 实数) / (n : 实数) ^ 4) (π ^ 4 / 90)
  证明: by
  convert! hasSum_zeta_nat two_ne_zero using 1
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one]; rw [bernoulli'_four]
  · simp [Nat.factorial]; ring
  · decide

Depends on / 依赖: Nat.add_one_sub_one, Nat.factorial, Nat.reduceAdd, Nat.reduceMul, _four, _of_ne_one, add_one_sub_one, bernoulli, bernoulli_eq_bernoulli, convert, factorial, hasSum_zeta_nat, reduceAdd, reduceMul, two_ne_zero
-/
theorem hasSum_zeta_four : HasSum (fun n : Nat => (1 : Real) / (n : Real) ^ 4) (π ^ 4 / 90) := by
  convert! hasSum_zeta_nat two_ne_zero using 1
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.add_one_sub_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one]; rw [bernoulli'_four]
  · simp [Nat.factorial]; ring
  · decide

/--
theorem `hasSum_L_function_mod_four_eval_three` / 定理 `hasSum_L_function_mod_four_eval_three`

English:
theorem hasSum_L_function_mod_four_eval_three
  proof: by
apply (congr_arg₂ HasSum ?_ ?_).to_iff.mp
    hasSum_one_div_nat_pow_mul_sin one_ne_zero (?_ : 1 / 4 in Icc (0 : Real) 1)
  · ext1 n
    ring_nf
  · have : (1 / 4 : Real) = (algebraMap Rat Real) (1 / 4 : Rat) := by simp
    rw [this]; rw [mul_pow]; rw [Polynomial.eval_map]; rw [Polynomial.eval₂_a

中文:
定理 hasSum_L_function_mod_four_eval_three
  证明: by
apply (congr_arg₂ HasSum ?_ ?_).to_iff.mp
    hasSum_one_div_nat_pow_mul_sin one_ne_zero (?_ : 1 / 4 in Icc (0 : Real) 1)
  · ext1 n
    ring_nf
  · have : (1 / 4 : Real) = (algebraMap Rat Real) (1 / 4 : Rat) := by simp
    rw [this]; rw [mul_pow]; rw [Polynomial.eval_map]; rw [Polynomial.eval₂_a

Depends on / 依赖: HasSum, Nat.factorial, Polynomial, Polynomial.bernoulli_three_eval_one_quarter, Polynomial.eval, Polynomial.eval_map, algebraMap, bernoulli_three_eval_one_quarter, eval_map, factorial, hasSum_one_div_nat_pow_mul_sin, mem_Icc, mul_pow, one_ne_zero, ring_nf, to_iff, to_iff.mp
-/
theorem hasSum_L_function_mod_four_eval_three :
    HasSum (fun n : Nat => (1 : Real) / (n : Real) ^ 3 * Real.sin (π * n / 2)) (π ^ 3 / 32) := by
apply (congr_arg₂ HasSum ?_ ?_).to_iff.mp
    hasSum_one_div_nat_pow_mul_sin one_ne_zero (?_ : 1 / 4 in Icc (0 : Real) 1)
  · ext1 n
    ring_nf
  · have : (1 / 4 : Real) = (algebraMap Rat Real) (1 / 4 : Rat) := by simp
    rw [this]; rw [mul_pow]; rw [Polynomial.eval_map]; rw [Polynomial.eval₂_at_apply]; rw [(by decide : 2 * 1 + 1 = 3)]; rw [Polynomial.bernoulli_three_eval_one_quarter]
    simp [Nat.factorial]; ring
  · rw [mem_Icc]; constructor
    · linarith
    · linarith

end Examples
