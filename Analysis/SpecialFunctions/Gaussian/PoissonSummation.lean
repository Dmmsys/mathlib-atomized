/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Poisson summation applied to the Gaussian

In `Real.tsum_exp_neg_mul_int_sq` and `Complex.tsum_exp_neg_mul_int_sq`, we use Poisson summation
to prove the identity

`∑' (n : ℤ), exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`

for positive real `a`, or complex `a` with positive real part. (See also
`NumberTheory.ModularForms.JacobiTheta`.)
-/

public section

open Real Set MeasureTheory Filter Asymptotics intervalIntegral

open scoped Real Topology FourierTransform RealInnerProductSpace

open Complex hiding exp continuous_exp

noncomputable section

section GaussianPoisson


/--
lemma `rexp_neg_quadratic_isLittleO_rpow_atTop` / 引理 `rexp_neg_quadratic_isLittleO_rpow_atTop`

English:
lemma rexp_neg_quadratic_isLittleO_rpow_atTop
  given: {a : Real} (ha : a < 0) (b s : Real)
  proof: by
  suffices (fun x => rexp (a * x ^ 2 + b * x)) =o[atTop] (fun x => rexp (-x)) by
    refine this.trans ?_
    simpa only [neg_one_mul] using isLittleO_exp_neg_mul_rpow_atTop zero_lt_one s
  rw [isLittleO_exp_comp_exp_comp]
  have : (fun x => -x - (a * x ^ 2 + b * x)) = fun x => x * (-a * x - (b +

中文:
引理 rexp_neg_quadratic_isLittleO_rpow_atTop
  条件: {a : 实数} (ha : a < 0) (b s : 实数)
  证明: by
  suffices (fun x => rexp (a * x ^ 2 + b * x)) =o[atTop] (fun x => rexp (-x)) by
    refine this.trans ?_
    simpa only [neg_one_mul] using isLittleO_exp_neg_mul_rpow_atTop zero_lt_one s
  rw [isLittleO_exp_comp_exp_comp]
  have : (fun x => -x - (a * x ^ 2 + b * x)) = fun x => x * (-a * x - (b +

Depends on / 依赖: const_mul_atTop, isLittleO_exp_comp_exp_comp, isLittleO_exp_neg_mul_rpow_atTop, neg_one_mul, neg_pos, neg_pos.mpr, ring_nf, tendsto_atTop_add_const_right, tendsto_id, tendsto_id.atTop_mul_atTop, tendsto_id.const_mul_atTop, this.trans, zero_lt_one
-/
lemma rexp_neg_quadratic_isLittleO_rpow_atTop {a : Real} (ha : a < 0) (b s : Real) :
    (fun x => rexp (a * x ^ 2 + b * x)) =o[atTop] (· ^ s) := by
  suffices (fun x => rexp (a * x ^ 2 + b * x)) =o[atTop] (fun x => rexp (-x)) by
    refine this.trans ?_
    simpa only [neg_one_mul] using isLittleO_exp_neg_mul_rpow_atTop zero_lt_one s
  rw [isLittleO_exp_comp_exp_comp]
  have : (fun x => -x - (a * x ^ 2 + b * x)) = fun x => x * (-a * x - (b + 1)) := by
    ext1 x; ring_nf
  rw [this]
exact tendsto_id.atTop_mul_atTop₀ tendsto_atTop_add_const_right _ _
    tendsto_id.const_mul_atTop (neg_pos.mpr ha)

/--
lemma `cexp_neg_quadratic_isLittleO_rpow_atTop` / 引理 `cexp_neg_quadratic_isLittleO_rpow_atTop`

English:
lemma cexp_neg_quadratic_isLittleO_rpow_atTop
  given: {a : Complex} (ha : a.re < 0) (b : Complex) (s : Real)
  proof: by
  apply Asymptotics.IsLittleO.of_norm_left
  convert! rexp_neg_quadratic_isLittleO_rpow_atTop ha b.re s with x
  simp_rw [Complex.norm_exp, add_re, ← ofReal_pow, mul_comm (_ : Complex) ↑(_ : Real),
      re_ofReal_mul, mul_comm _ (re _)]

中文:
引理 cexp_neg_quadratic_isLittleO_rpow_atTop
  条件: {a : Complex} (ha : a.re < 0) (b : Complex) (s : 实数)
  证明: by
  apply Asymptotics.IsLittleO.of_norm_left
  convert! rexp_neg_quadratic_isLittleO_rpow_atTop ha b.re s with x
  simp_rw [Complex.norm_exp, add_re, ← ofReal_pow, mul_comm (_ : Complex) ↑(_ : Real),
      re_ofReal_mul, mul_comm _ (re _)]

Depends on / 依赖: Asymptotics, Asymptotics.IsLittleO.of_norm_left, Complex.norm_exp, IsLittleO, add_re, b.re, convert, mul_comm, norm_exp, ofReal_pow, of_norm_left, re_ofReal_mul, rexp_neg_quadratic_isLittleO_rpow_atTop, simp_rw
-/
lemma cexp_neg_quadratic_isLittleO_rpow_atTop {a : Complex} (ha : a.re < 0) (b : Complex) (s : Real) :
    (fun x : Real => cexp (a * x ^ 2 + b * x)) =o[atTop] (· ^ s) := by
  apply Asymptotics.IsLittleO.of_norm_left
  convert! rexp_neg_quadratic_isLittleO_rpow_atTop ha b.re s with x
  simp_rw [Complex.norm_exp, add_re, ← ofReal_pow, mul_comm (_ : Complex) ↑(_ : Real),
      re_ofReal_mul, mul_comm _ (re _)]

/--
lemma `cexp_neg_quadratic_isLittleO_abs_rpow_cocompact` / 引理 `cexp_neg_quadratic_isLittleO_abs_rpow_cocompact`

English:
lemma cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
  given: {a : Complex} (ha : a.re < 0) (b : Complex) (s : Real)
  proof: by
  rw [cocompact_eq_atBot_atTop]; rw [isLittleO_sup]
  constructor
  · refine ((cexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun x => by simp) ?_
    · refine (eventually_lt_atBot 0).mp (Eventually.of_forall fun 

中文:
引理 cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
  条件: {a : Complex} (ha : a.re < 0) (b : Complex) (s : 实数)
  证明: by
  rw [cocompact_eq_atBot_atTop]; rw [isLittleO_sup]
  constructor
  · refine ((cexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun x => by simp) ?_
    · refine (eventually_lt_atBot 0).mp (Eventually.of_forall fun 

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyEq, EventuallyEq.rfl, Filter, Filter.tendsto_neg_atBot_atTop, Function, Function.comp_apply, abs_of_neg, cexp_neg_quadratic_isLittleO_rpow_atTop, cocompact_eq_atBot_atTop, comp_apply, comp_tendsto, eventually_gt_atTop, eventually_lt_atBot, isLittleO_sup, of_forall, tendsto_neg_atBot_atTop
-/
lemma cexp_neg_quadratic_isLittleO_abs_rpow_cocompact {a : Complex} (ha : a.re < 0) (b : Complex) (s : Real) :
    (fun x : Real => cexp (a * x ^ 2 + b * x)) =o[cocompact Real] (|·| ^ s) := by
  rw [cocompact_eq_atBot_atTop]; rw [isLittleO_sup]
  constructor
  · refine ((cexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun x => by simp) ?_
    · refine (eventually_lt_atBot 0).mp (Eventually.of_forall fun x hx => ?_)
      simp only [Function.comp_apply, abs_of_neg hx]
  · refine (cexp_neg_quadratic_isLittleO_rpow_atTop ha b s).congr' EventuallyEq.rfl ?_
    refine (eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_)
    simp_rw [abs_of_pos hx]

/--
theorem `tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact` / 定理 `tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact`

English:
theorem tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
  given: {a : Real} (ha : 0 < a) (s : Real)
  proof: by
  conv in rexp _ => rw [← sq_abs]
  rw [cocompact_eq_atBot_atTop]; rw [← comap_abs_atTop]
  erw [tendsto_comap'_iff (m := fun y => y ^ s * rexp (-a * y ^ 2))
      (mem_atTop_sets.mpr ⟨0, fun b hb => ⟨b, abs_of_nonneg hb⟩⟩)]
  exact
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha s).tendsto_zer

中文:
定理 tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
  条件: {a : 实数} (ha : 0 < a) (s : 实数)
  证明: by
  conv in rexp _ => rw [← sq_abs]
  rw [cocompact_eq_atBot_atTop]; rw [← comap_abs_atTop]
  erw [tendsto_comap'_iff (m := fun y => y ^ s * rexp (-a * y ^ 2))
      (mem_atTop_sets.mpr ⟨0, fun b hb => ⟨b, abs_of_nonneg hb⟩⟩)]
  exact
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha s).tendsto_zer

Depends on / 依赖: _iff, abs_of_nonneg, cocompact_eq_atBot_atTop, comap_abs_atTop, const_mul_atTop_of_neg, mem_atTop_sets, mem_atTop_sets.mpr, neg_lt_zero, neg_lt_zero.mpr, one_half_pos, rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg, sq_abs, tendsto_comap, tendsto_exp_atBot, tendsto_exp_atBot.comp, tendsto_id, tendsto_id.const_mul_atTop_of_neg, tendsto_zero_of_tendsto
-/
theorem tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact {a : Real} (ha : 0 < a) (s : Real) :
    Tendsto (fun x : Real => |x| ^ s * rexp (-a * x ^ 2)) (cocompact Real) (𝓝 0) := by
  conv in rexp _ => rw [← sq_abs]
  rw [cocompact_eq_atBot_atTop]; rw [← comap_abs_atTop]
  erw [tendsto_comap'_iff (m := fun y => y ^ s * rexp (-a * y ^ 2))
      (mem_atTop_sets.mpr ⟨0, fun b hb => ⟨b, abs_of_nonneg hb⟩⟩)]
  exact
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha s).tendsto_zero_of_tendsto
      (tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr one_half_pos))

/--
theorem `isLittleO_exp_neg_mul_sq_cocompact` / 定理 `isLittleO_exp_neg_mul_sq_cocompact`

English:
theorem isLittleO_exp_neg_mul_sq_cocompact
  given: {a : Complex} (ha : 0 < a.re) (s : Real)
  proof: by
  convert! cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (?_ : (-a).re < 0) 0 s using 1
  · simp_rw [zero_mul, add_zero]
  · rwa [neg_re, neg_lt_zero]

中文:
定理 isLittleO_exp_neg_mul_sq_cocompact
  条件: {a : Complex} (ha : 0 < a.re) (s : 实数)
  证明: by
  convert! cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (?_ : (-a).re < 0) 0 s using 1
  · simp_rw [zero_mul, add_zero]
  · rwa [neg_re, neg_lt_zero]

Depends on / 依赖: add_zero, cexp_neg_quadratic_isLittleO_abs_rpow_cocompact, convert, neg_lt_zero, neg_re, simp_rw, zero_mul
-/
theorem isLittleO_exp_neg_mul_sq_cocompact {a : Complex} (ha : 0 < a.re) (s : Real) :
    (fun x : Real => Complex.exp (-a * x ^ 2)) =o[cocompact Real] fun x : Real => |x| ^ s := by
  convert! cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (?_ : (-a).re < 0) 0 s using 1
  · simp_rw [zero_mul, add_zero]
  · rwa [neg_re, neg_lt_zero]

/--
theorem `Complex.tsum_exp_neg_quadratic` / 定理 `Complex.tsum_exp_neg_quadratic`

English:
theorem Complex.tsum_exp_neg_quadratic
  given: {a : Complex} (ha : 0 < a.re) (b : Complex)
  proof: by
  let f : Real -> Complex := fun x => cexp (-π * a * x ^ 2 + 2 * π * b * x)
  have hFf : 𝓕 f = fun x : Real => 1 / a ^ (1 / 2 : Complex) * cexp (-π / a * (x + I * b) ^ 2) :=
    fourier_gaussian_pi' ha b
  have h1 : 0 < (π * a).re := by
    rw [re_ofReal_mul]
    exact mul_pos pi_pos ha
  have h2

中文:
定理 Complex.tsum_exp_neg_quadratic
  条件: {a : Complex} (ha : 0 < a.re) (b : Complex)
  证明: by
  let f : Real -> Complex := fun x => cexp (-π * a * x ^ 2 + 2 * π * b * x)
  have hFf : 𝓕 f = fun x : Real => 1 / a ^ (1 / 2 : Complex) * cexp (-π / a * (x + I * b) ^ 2) :=
    fourier_gaussian_pi' ha b
  have h1 : 0 < (π * a).re := by
    rw [re_ofReal_mul]
    exact mul_pos pi_pos ha
  have h2

Depends on / 依赖: cocompact, contrapose, div_eq_mul_inv, div_pos, f_bd, fourier_gaussian_pi, inv_re, mul_pos, normSq_pos, normSq_pos.mpr, pi_pos, re_ofReal_mul, zero_re
-/
theorem Complex.tsum_exp_neg_quadratic {a : Complex} (ha : 0 < a.re) (b : Complex) :
    (∑' n : Int, cexp (-π * a * n ^ 2 + 2 * π * b * n)) =
      1 / a ^ (1 / 2 : Complex) * ∑' n : Int, cexp (-π / a * (n + I * b) ^ 2) := by
  let f : Real -> Complex := fun x => cexp (-π * a * x ^ 2 + 2 * π * b * x)
  have hFf : 𝓕 f = fun x : Real => 1 / a ^ (1 / 2 : Complex) * cexp (-π / a * (x + I * b) ^ 2) :=
    fourier_gaussian_pi' ha b
  have h1 : 0 < (π * a).re := by
    rw [re_ofReal_mul]
    exact mul_pos pi_pos ha
  have h2 : 0 < (π / a).re := by
    rw [div_eq_mul_inv]; rw [re_ofReal_mul]; rw [inv_re]
    refine mul_pos pi_pos (div_pos ha <| normSq_pos.mpr ?_)
    contrapose! ha
    rw [ha]; rw [zero_re]
  have f_bd : f =O[cocompact Real] (fun x => |x| ^ (-2 : Real)) := by
    convert! (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ?_ _ (-2)).isBigO
    rwa [neg_mul, neg_re, neg_lt_zero]
  have Ff_bd : (𝓕 f) =O[cocompact Real] (fun x => |x| ^ (-2 : Real)) := by
    rw [hFf]
    have : forall (x : Real), -π / a * (x + I * b) ^ 2 =
        -π / a * x ^ 2 + (-2 * π * I * b) / a * x + π * b ^ 2 / a := by
      intro x; ring_nf; rw [I_sq]; ring
    simp_rw [this]
    conv => enter [2, x]; rw [Complex.exp_add, ← mul_assoc _ _ (Complex.exp _), mul_comm]
    refine ((cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
      ?_ (-2 * π * I * b / a) (-2)).isBigO.const_mul_left _).const_mul_left _
    rwa [neg_div, neg_re, neg_lt_zero]
  convert! Real.tsum_eq_tsum_fourier_of_rpow_decay (by fun_prop) one_lt_two f_bd Ff_bd 0 using 1
  · simp only [f, zero_add, ofReal_intCast]
  · simp [← tsum_mul_left, hFf]

/--
theorem `Complex.tsum_exp_neg_mul_int_sq` / 定理 `Complex.tsum_exp_neg_mul_int_sq`

English:
theorem Complex.tsum_exp_neg_mul_int_sq
  given: {a : Complex} (ha : 0 < a.re)
  proof: by
  simpa only [mul_zero, zero_mul, add_zero] using Complex.tsum_exp_neg_quadratic ha 0

中文:
定理 Complex.tsum_exp_neg_mul_int_sq
  条件: {a : Complex} (ha : 0 < a.re)
  证明: by
  simpa only [mul_zero, zero_mul, add_zero] using Complex.tsum_exp_neg_quadratic ha 0

Depends on / 依赖: Complex.tsum_exp_neg_quadratic, add_zero, mul_zero, tsum_exp_neg_quadratic, zero_mul
-/
theorem Complex.tsum_exp_neg_mul_int_sq {a : Complex} (ha : 0 < a.re) :
    (∑' n : Int, cexp (-π * a * (n : Complex) ^ 2)) =
      1 / a ^ (1 / 2 : Complex) * ∑' n : Int, cexp (-π / a * (n : Complex) ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using Complex.tsum_exp_neg_quadratic ha 0

/--
theorem `Real.tsum_exp_neg_mul_int_sq` / 定理 `Real.tsum_exp_neg_mul_int_sq`

English:
theorem Real.tsum_exp_neg_mul_int_sq
  given: {a : Real} (ha : 0 < a)
  proof: by
  simpa only [← ofReal_inj, ofReal_tsum, ofReal_exp, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_intCast, ofReal_div, ofReal_one, ofReal_cpow ha.le, ofReal_ofNat, mul_zero, zero_mul,
    add_zero] using Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re] : 0 < (a : Complex).re) 0

中文:
定理 Real.tsum_exp_neg_mul_int_sq
  条件: {a : 实数} (ha : 0 < a)
  证明: by
  simpa only [← ofReal_inj, ofReal_tsum, ofReal_exp, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_intCast, ofReal_div, ofReal_one, ofReal_cpow ha.le, ofReal_ofNat, mul_zero, zero_mul,
    add_zero] using Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re] : 0 < (a : Complex).re) 0

Depends on / 依赖: Complex.tsum_exp_neg_quadratic, add_zero, ha.le, mul_zero, ofReal_cpow, ofReal_div, ofReal_exp, ofReal_inj, ofReal_intCast, ofReal_mul, ofReal_neg, ofReal_ofNat, ofReal_one, ofReal_pow, ofReal_re, ofReal_tsum, tsum_exp_neg_quadratic, zero_mul
-/
theorem Real.tsum_exp_neg_mul_int_sq {a : Real} (ha : 0 < a) :
    (∑' n : Int, exp (-π * a * (n : Real) ^ 2)) =
      (1 : Real) / a ^ (1 / 2 : Real) * (∑' n : Int, exp (-π / a * (n : Real) ^ 2)) := by
  simpa only [← ofReal_inj, ofReal_tsum, ofReal_exp, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_intCast, ofReal_div, ofReal_one, ofReal_cpow ha.le, ofReal_ofNat, mul_zero, zero_mul,
    add_zero] using Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re] : 0 < (a : Complex).re) 0

end GaussianPoisson
