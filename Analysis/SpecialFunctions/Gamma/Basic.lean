/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `Complex.Gamma`: the `Γ` function (of a complex variable).
* `Complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `Complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `Complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.

## Gamma function: main statements (real case)

* `Real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`.

## Tags

Gamma
-/

public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open scoped Nat Topology ComplexConjugate

namespace Real

/--
theorem `Gamma_integrand_isLittleO` / 定理 `Gamma_integrand_isLittleO`

English:
theorem Gamma_integrand_isLittleO
  given: (s : Real)
  proof: by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : Real => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : Real => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

中文:
定理 Gamma_integrand_isLittleO
  条件: (s : 实数)
  证明: by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : Real => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : Real => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

Depends on / 依赖: exp_neg, exp_nsmul, exp_pos, inv_tendsto_atTop, isLittleO_of_tendsto, one_half_pos, tendsto_exp_mul_div_rpow_atTop
-/
theorem Gamma_integrand_isLittleO (s : Real) :
    (fun x : Real => exp (-x) * x ^ s) =o[atTop] fun x : Real => exp (-(1 / 2) * x) := by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : Real => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : Real => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

/--
theorem `GammaIntegral_convergent` / 定理 `GammaIntegral_convergent`

English:
theorem GammaIntegral_convergent
  given: {s : Real} (h : 0 < s)
  proof: by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one Real _ _ _ _)]; rw [integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith)).continuousOn_mul continuousOn_id.neg.rexp)
  · exact integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Gamma_integrand_isLittleO _).isBigO

中文:
定理 Gamma整数egral_convergent
  条件: {s : 实数} (h : 0 < s)
  证明: by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one Real _ _ _ _)]; rw [integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith)).continuousOn_mul continuousOn_id.neg.rexp)
  · exact integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Gamma_integrand_isLittleO _).isBigO

Depends on / 依赖: Gamma_integrand_isLittleO, Ioc_union_Ioi_eq_Ioi, continuousOn_id, continuousOn_id.neg.rexp, continuousOn_id.neg.rexp.mul, continuousOn_id.rpow_const, continuousOn_mul, integrableOn_Icc_iff_integrableOn_Ioc, integrableOn_union, integrable_of_isBigO_exp_neg, intervalIntegrable_iff_integrableOn_Icc_of_le, intervalIntegrable_rpow, isBigO, one_half_pos, rpow_const, zero_le_one
-/
theorem GammaIntegral_convergent {s : Real} (h : 0 < s) :
    IntegrableOn (fun x : Real => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one Real _ _ _ _)]; rw [integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith)).continuousOn_mul continuousOn_id.neg.rexp)
  · exact integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Gamma_integrand_isLittleO _).isBigO

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(Real.exp (-x)), Complex.exp (↑(-x)), and Complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/--
theorem `GammaIntegral_convergent` / 定理 `GammaIntegral_convergent`

English:
theorem GammaIntegral_convergent
  given: {s : Complex} (hs : 0 < s.re)
  proof: by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : Complex => x ^ (s - 1)) ↑x :=
continuousAt_cpow_const ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul]; rw [Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x]; rw [norm_cpow_eq_rpow_re_of_pos hx _]
    simp

中文:
定理 Gamma整数egral_convergent
  条件: {s : 复形} (hs : 0 < s.re)
  证明: by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : Complex => x ^ (s - 1)) ↑x :=
continuousAt_cpow_const ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul]; rw [Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x]; rw [norm_cpow_eq_rpow_re_of_pos hx _]
    simp

Depends on / 依赖: ContinuousAt, ContinuousAt.comp, ContinuousOn, ContinuousOn.aestronglyMeasurable, GammaIntegral_convergent, HasFiniteIntegral, HasFiniteIntegral.congr, Real.GammaIntegral_convergent, ae_restrict_iff, aestronglyMeasurable, continuousAt, continuousAt_cpow_const, continuousOn, continuousOn.mul, continuousOn_of_forall_continuousAt, continuous_neg, continuous_neg.rexp, continuous_ofReal, continuous_ofReal.comp, continuous_ofReal.continuousAt
-/
theorem GammaIntegral_convergent {s : Complex} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : Real -> Complex) (Ioi 0) := by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : Complex => x ^ (s - 1)) ↑x :=
continuousAt_cpow_const ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul]; rw [Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x]; rw [norm_cpow_eq_rpow_re_of_pos hx _]
    simp

/--
Definition of `GammaIntegral` / `GammaIntegral` 的定义

English:
definition GammaIntegral
  signature: (s : Complex)
  body: ∫ x in Ioi (0 : Real), ↑(-x).exp * ↑x ^ (s - 1)

中文:
定义 Gamma整数egral
  签名: (s : 复形)
  定义体: ∫ x in Ioi (0 : Real), ↑(-x).exp * ↑x ^ (s - 1)
-/
@[expose] def GammaIntegral (s : Complex) : Complex :=
  ∫ x in Ioi (0 : Real), ↑(-x).exp * ↑x ^ (s - 1)

/--
theorem `GammaIntegral_conj` / 定理 `GammaIntegral_conj`

English:
theorem GammaIntegral_conj
  given: (s : Complex)
  statement: GammaIntegral (conj s) = conj (GammaIntegral s)
  proof: by
  rw [GammaIntegral]; rw [GammaIntegral]; rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [map_mul]; rw [conj_ofReal]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [← exp_conj]; rw [map_mul]; rw [← ofReal_log (le_of_lt hx)]; rw [conj_ofReal]; rw [map_sub]; rw [map_one]

中文:
定理 Gamma整数egral_conj
  条件: (s : 复形)
  结论: Gamma整数egral (conj s) = conj (Gamma整数egral s)
  证明: by
  rw [GammaIntegral]; rw [GammaIntegral]; rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [map_mul]; rw [conj_ofReal]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [← exp_conj]; rw [map_mul]; rw [← ofReal_log (le_of_lt hx)]; rw [conj_ofReal]; rw [map_sub]; rw [map_one]

Depends on / 依赖: GammaIntegral, conj_ofReal, cpow_def_of_ne_zero, exp_conj, integral_conj, le_of_lt, map_mul, map_one, map_sub, measurableSet_Ioi, ne_of_gt, ofReal_log, ofReal_ne_zero, ofReal_ne_zero.mpr, setIntegral_congr_fun
-/
theorem GammaIntegral_conj (s : Complex) : GammaIntegral (conj s) = conj (GammaIntegral s) := by
  rw [GammaIntegral]; rw [GammaIntegral]; rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [map_mul]; rw [conj_ofReal]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx))]; rw [← exp_conj]; rw [map_mul]; rw [← ofReal_log (le_of_lt hx)]; rw [conj_ofReal]; rw [map_sub]; rw [map_one]

/--
theorem `GammaIntegral_ofReal` / 定理 `GammaIntegral_ofReal`

English:
theorem GammaIntegral_ofReal
  given: (s : Real)
  proof: by
  have : forall r : Real, Complex.ofReal r = @RCLike.ofReal Complex _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul]; rw [ofReal_cpow (mem_Ioi.mp hx).le]
  simp

@[simp]

中文:
定理 Gamma整数egral_of实数
  条件: (s : 实数)
  证明: by
  have : forall r : Real, Complex.ofReal r = @RCLike.ofReal Complex _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul]; rw [ofReal_cpow (mem_Ioi.mp hx).le]
  simp

@[simp]

Depends on / 依赖: Complex.ofReal, GammaIntegral, RCLike, RCLike.ofReal, _root_, _root_.integral_ofReal, conv_rhs, integral_ofReal, measurableSet_Ioi, mem_Ioi, mem_Ioi.mp, ofReal, ofReal_cpow, ofReal_mul, setIntegral_congr_fun
-/
theorem GammaIntegral_ofReal (s : Real) :
    GammaIntegral ↑s = ↑(∫ x : Real in Ioi 0, Real.exp (-x) * x ^ (s - 1)) := by
  have : forall r : Real, Complex.ofReal r = @RCLike.ofReal Complex _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul]; rw [ofReal_cpow (mem_Ioi.mp hx).le]
  simp

@[simp]
/--
theorem `GammaIntegral_one` / 定理 `GammaIntegral_one`

English:
theorem GammaIntegral_one
  statement: GammaIntegral 1 = 1
  proof: by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero

中文:
定理 Gamma整数egral_one
  结论: Gamma整数egral 1 = 1
  证明: by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero

Depends on / 依赖: GammaIntegral_ofReal, integral_exp_neg_Ioi_zero, mul_one, ofReal_inj, ofReal_one, rpow_zero, sub_self
-/
theorem GammaIntegral_one : GammaIntegral 1 = 1 := by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/--
Definition of `partialGamma` / `partialGamma` 的定义

English:
definition partialGamma
  signature: (s : Complex) (X : Real)
  body: ∫ x in 0..X, (-x).exp * x ^ (s - 1)

中文:
定义 partialGamma
  签名: (s : 复形) (X : 实数)
  定义体: ∫ x in 0..X, (-x).exp * x ^ (s - 1)
-/
@[expose] def partialGamma (s : Complex) (X : Real) : Complex :=
  ∫ x in 0..X, (-x).exp * x ^ (s - 1)

/--
theorem `tendsto_partialGamma` / 定理 `tendsto_partialGamma`

English:
theorem tendsto_partialGamma
  given: {s : Complex} (hs : 0 < s.re)
  proof: intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id

中文:
定理 tendsto_partialGamma
  条件: {s : 复形} (hs : 0 < s.re)
  证明: intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id

Depends on / 依赖: GammaIntegral_convergent, intervalIntegral_tendsto_integral_Ioi, tendsto_id
-/
theorem tendsto_partialGamma {s : Complex} (hs : 0 < s.re) :
    Tendsto (fun X : Real => partialGamma s X) atTop (𝓝 <| GammaIntegral s) :=
  intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id

/--
theorem `Gamma_integrand_intervalIntegrable` / 定理 `Gamma_integrand_intervalIntegrable`

English:
theorem Gamma_integrand_intervalIntegrable
  given: (s : Complex) {X : Real} (hs : 0 < s.re) (hX : 0 <= X)
  proof: by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self

中文:
定理 Gamma_integrand_interval整数egrable
  条件: (s : 复形) {X : 实数} (hs : 0 < s.re) (hX : 0 <= X)
  证明: by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self
-/
private theorem Gamma_integrand_intervalIntegrable (s : Complex) {X : Real} (hs : 0 < s.re) (hX : 0 <= X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : Real -> Complex) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self

/--
theorem `Gamma_integrand_deriv_integrable_A` / 定理 `Gamma_integrand_deriv_integrable_A`

English:
theorem Gamma_integrand_deriv_integrable_A
  given: {s : Complex} (hs : 0 < s.re) {X : Real} (hX : 0 <= X)
  proof: by
  convert! (Gamma_integrand_intervalIntegrable (s + 1) _ hX).neg
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel_right]; rfl
  · simp only [add_re, one_re]; linarith

中文:
定理 Gamma_integrand_deriv_integrable_A
  条件: {s : 复形} (hs : 0 < s.re) {X : 实数} (hX : 0 <= X)
  证明: by
  convert! (Gamma_integrand_intervalIntegrable (s + 1) _ hX).neg
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel_right]; rfl
  · simp only [add_re, one_re]; linarith
-/
private theorem Gamma_integrand_deriv_integrable_A {s : Complex} (hs : 0 < s.re) {X : Real} (hX : 0 <= X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : Real -> Complex) volume 0 X := by
  convert! (Gamma_integrand_intervalIntegrable (s + 1) _ hX).neg
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel_right]; rfl
  · simp only [add_re, one_re]; linarith

/--
theorem `Gamma_integrand_deriv_integrable_B` / 定理 `Gamma_integrand_deriv_integrable_B`

English:
theorem Gamma_integrand_deriv_integrable_B
  given: {s : Complex} (hs : 0 < s.re) {Y : Real} (hY : 0 <= Y)
  proof: by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : Real -> Complex) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : Real -> Complex) := by ext1; ring
  rw [this]; rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine (continuousOn_const.mul ?_).aestronglyMeasurable measurableSet_Ioc
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    refine (?_ : ContinuousAt (fun x : Complex => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
exact continuousAt_cpow_const ofReal_mem_slitPlane.2 hx.1
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_mul]
  refine (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr ?_).const_mul _
  rw [EventuallyEq]; rw [ae_restrict_iff']
  · filter_upwards with x hx
    rw [Complex.norm_of_nonneg (exp_pos _).le]; rw [norm_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc

中文:
定理 Gamma_integrand_deriv_integrable_B
  条件: {s : 复形} (hs : 0 < s.re) {Y : 实数} (hY : 0 <= Y)
  证明: by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : Real -> Complex) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : Real -> Complex) := by ext1; ring
  rw [this]; rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine (continuousOn_const.mul ?_).aestronglyMeasurable measurableSet_Ioc
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    refine (?_ : ContinuousAt (fun x : Complex => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
exact continuousAt_cpow_const ofReal_mem_slitPlane.2 hx.1
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_mul]
  refine (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr ?_).const_mul _
  rw [EventuallyEq]; rw [ae_restrict_iff']
  · filter_upwards with x hx
    rw [Complex.norm_of_nonneg (exp_pos _).le]; rw [norm_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc
-/
private theorem Gamma_integrand_deriv_integrable_B {s : Complex} (hs : 0 < s.re) {Y : Real} (hY : 0 <= Y) :
    IntervalIntegrable (fun x : Real => (-x).exp * (s * x ^ (s - 1)) : Real -> Complex) volume 0 Y := by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : Real -> Complex) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : Real -> Complex) := by ext1; ring
  rw [this]; rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  constructor
  · refine (continuousOn_const.mul ?_).aestronglyMeasurable measurableSet_Ioc
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    refine (?_ : ContinuousAt (fun x : Complex => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
exact continuousAt_cpow_const ofReal_mem_slitPlane.2 hx.1
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_mul]
  refine (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr ?_).const_mul _
  rw [EventuallyEq]; rw [ae_restrict_iff']
  · filter_upwards with x hx
    rw [Complex.norm_of_nonneg (exp_pos _).le]; rw [norm_cpow_eq_rpow_re_of_pos hx.1]
    simp
  · exact measurableSet_Ioc

/--
theorem `partialGamma_add_one` / 定理 `partialGamma_add_one`

English:
theorem partialGamma_add_one
  given: {s : Complex} (hs : 0 < s.re) {X : Real} (hX : 0 <= X)
  proof: by
  rw [partialGamma]; rw [partialGamma]; rw [add_sub_cancel_right]
  have F_der_I : forall x : Real, x in Ioo 0 X -> HasDerivAt (fun x => (-x).exp * x ^ s : Real -> Complex)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : Real => (-y).exp) (-(-x).exp) x := by
      simpa using! (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : Real => (y : Complex) ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      · simpa only [mul_one] using! t.comp_ofReal
      · exact ofReal_mem_slitPlane.2 hx.1
    simpa only [ofReal_neg, neg_mul] using! d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.rexp).mul (continuous_ofReal_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : Complex => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX)]; rw [intervalIntegral.integral_neg]; rw [neg_add]; rw [neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval]; rw [sub_neg_eq_add]; rw [neg_sub]; rw [add_comm]; rw [add_sub]
  have hn : s != 0 := by contrapose! hs; rw [hs, zero_re]
  simp only [Pi.mul_apply, Function.comp_apply, ofReal_zero, zero_cpow hn, mul_zero, add_zero,
    ← intervalIntegral.integral_const_mul]
  congr with x
  ring

中文:
定理 partialGamma_add_one
  条件: {s : 复形} (hs : 0 < s.re) {X : 实数} (hX : 0 <= X)
  证明: by
  rw [partialGamma]; rw [partialGamma]; rw [add_sub_cancel_right]
  have F_der_I : forall x : Real, x in Ioo 0 X -> HasDerivAt (fun x => (-x).exp * x ^ s : Real -> Complex)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : Real => (-y).exp) (-(-x).exp) x := by
      simpa using! (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : Real => (y : Complex) ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      · simpa only [mul_one] using! t.comp_ofReal
      · exact ofReal_mem_slitPlane.2 hx.1
    simpa only [ofReal_neg, neg_mul] using! d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.rexp).mul (continuous_ofReal_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : Complex => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX)]; rw [intervalIntegral.integral_neg]; rw [neg_add]; rw [neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval]; rw [sub_neg_eq_add]; rw [neg_sub]; rw [add_comm]; rw [add_sub]
  have hn : s != 0 := by contrapose! hs; rw [hs, zero_re]
  simp only [Pi.mul_apply, Function.comp_apply, ofReal_zero, zero_cpow hn, mul_zero, add_zero,
    ← intervalIntegral.integral_const_mul]
  congr with x
  ring

Depends on / 依赖: F_der_I, HasDerivAt, HasDerivAt.cpow_const, add_sub_cancel_right, cpow_const, hasDerivAt_id, hasDerivAt_neg, partialGamma
-/
theorem partialGamma_add_one {s : Complex} (hs : 0 < s.re) {X : Real} (hX : 0 <= X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s := by
  rw [partialGamma]; rw [partialGamma]; rw [add_sub_cancel_right]
  have F_der_I : forall x : Real, x in Ioo 0 X -> HasDerivAt (fun x => (-x).exp * x ^ s : Real -> Complex)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : Real => (-y).exp) (-(-x).exp) x := by
      simpa using! (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : Real => (y : Complex) ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      · simpa only [mul_one] using! t.comp_ofReal
      · exact ofReal_mem_slitPlane.2 hx.1
    simpa only [ofReal_neg, neg_mul] using! d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.rexp).mul (continuous_ofReal_cpow_const hs)
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : Complex => -x at int_eval
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX)]; rw [intervalIntegral.integral_neg]; rw [neg_add]; rw [neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval]; rw [sub_neg_eq_add]; rw [neg_sub]; rw [add_comm]; rw [add_sub]
  have hn : s != 0 := by contrapose! hs; rw [hs, zero_re]
  simp only [Pi.mul_apply, Function.comp_apply, ofReal_zero, zero_cpow hn, mul_zero, add_zero,
    ← intervalIntegral.integral_const_mul]
  congr with x
  ring

/--
theorem `GammaIntegral_add_one` / 定理 `GammaIntegral_add_one`

English:
theorem GammaIntegral_add_one
  given: {s : Complex} (hs : 0 < s.re)
  proof: by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine tendsto_nhds_unique ?_ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : Real => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : Real))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine Tendsto.congr' this ?_
  suffices Tendsto (fun X => -X ^ s * (-X).exp : Real -> Complex) atTop (𝓝 0) by
    simpa using! Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have :
      (fun e : Real => ‖-(e : Complex) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : Real => e ^ s.re * (-1 * e).exp := by
    refine eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_
    intro x hx; dsimp only
    rw [norm_mul]; rw [norm_neg]; rw [norm_cpow_eq_rpow_re_of_pos hx]; rw [Complex.norm_of_nonneg (exp_pos (-x)).le]; rw [neg_mul]; rw [one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)

中文:
定理 Gamma整数egral_add_one
  条件: {s : 复形} (hs : 0 < s.re)
  证明: by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine tendsto_nhds_unique ?_ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : Real => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : Real))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine Tendsto.congr' this ?_
  suffices Tendsto (fun X => -X ^ s * (-X).exp : Real -> Complex) atTop (𝓝 0) by
    simpa using! Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have :
      (fun e : Real => ‖-(e : Complex) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : Real => e ^ s.re * (-1 * e).exp := by
    refine eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_
    intro x hx; dsimp only
    rw [norm_mul]; rw [norm_neg]; rw [norm_cpow_eq_rpow_re_of_pos hx]; rw [Complex.norm_of_nonneg (exp_pos (-x)).le]; rw [neg_mul]; rw [one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)

Depends on / 依赖: GammaIntegral, Ici_mem_atTop, Tendsto, Tendsto.congr, add_re, eventuallyEq_of_mem, mem_Ici, mem_Ici.mp, one_re, partialGamma, partialGamma_add_one, ring_nf, tendsto_nhds_unique, tendsto_partialGamma
-/
theorem GammaIntegral_add_one {s : Complex} (hs : 0 < s.re) :
    GammaIntegral (s + 1) = s * GammaIntegral s := by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine tendsto_nhds_unique ?_ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : Real => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : Real))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine Tendsto.congr' this ?_
  suffices Tendsto (fun X => -X ^ s * (-X).exp : Real -> Complex) atTop (𝓝 0) by
    simpa using! Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have :
      (fun e : Real => ‖-(e : Complex) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : Real => e ^ s.re * (-1 * e).exp := by
    refine eventuallyEq_of_mem (Ioi_mem_atTop 0) ?_
    intro x hx; dsimp only
    rw [norm_mul]; rw [norm_neg]; rw [norm_cpow_eq_rpow_re_of_pos hx]; rw [Complex.norm_of_nonneg (exp_pos (-x)).le]; rw [neg_mul]; rw [one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ zero_lt_one)

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def GammaAux

中文:
定义 noncomputable
  签名: def GammaAux
-/
private noncomputable def GammaAux : Nat -> Complex -> Complex
  | 0 => GammaIntegral
  | n + 1 => fun s : Complex => GammaAux n (s + 1) / s

/--
theorem `GammaAux_recurrence1` / 定理 `GammaAux_recurrence1`

English:
theorem GammaAux_recurrence1
  given: (s : Complex) (n : Nat) (h1 : -s.re < ↑n)
  proof: by
  induction n generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    rw [mul_comm]; rw [mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  | succ n hn =>
    dsimp only [GammaAux]
    have hh1 : -(s + 1).re < n := by
      rw [Nat.cast_add]; rw [Nat.cast_one] at h1
      rw [add_re]; rw [one_re]; linarith
    rw [← hn (s + 1) hh1]

中文:
定理 GammaAux_recurrence1
  条件: (s : 复形) (n : 自然数) (h1 : -s.re < ↑n)
  证明: by
  induction n generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    rw [mul_comm]; rw [mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  | succ n hn =>
    dsimp only [GammaAux]
    have hh1 : -(s + 1).re < n := by
      rw [Nat.cast_add]; rw [Nat.cast_one] at h1
      rw [add_re]; rw [one_re]; linarith
    rw [← hn (s + 1) hh1]

Depends on / 依赖: isLeftAdjoint, ofIsRightAdjoint
-/
private theorem GammaAux_recurrence1 (s : Complex) (n : Nat) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux n (s + 1) / s := by
  induction n generalizing s with
  | zero =>
    simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    rw [mul_comm]; rw [mul_div_cancel_right₀]; contrapose! h1; rw [h1]
    simp
  | succ n hn =>
    dsimp only [GammaAux]
    have hh1 : -(s + 1).re < n := by
      rw [Nat.cast_add]; rw [Nat.cast_one] at h1
      rw [add_re]; rw [one_re]; linarith
    rw [← hn (s + 1) hh1]

/--
theorem `GammaAux_recurrence2` / 定理 `GammaAux_recurrence2`

English:
theorem GammaAux_recurrence2
  given: (s : Complex) (n : Nat) (h1 : -s.re < ↑n)
  proof: by
  rcases n with - | n
  · simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]
    rw [GammaIntegral_add_one h1]; rw [mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [GammaAux]
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.cast_add]; rw [Nat.cast_one] at h1
        rw [add_re]; rw [one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]

中文:
定理 GammaAux_recurrence2
  条件: (s : 复形) (n : 自然数) (h1 : -s.re < ↑n)
  证明: by
  rcases n with - | n
  · simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]
    rw [GammaIntegral_add_one h1]; rw [mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [GammaAux]
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.cast_add]; rw [Nat.cast_one] at h1
        rw [add_re]; rw [one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]
-/
private theorem GammaAux_recurrence2 (s : Complex) (n : Nat) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux (n + 1) s := by
  rcases n with - | n
  · simp only [CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    dsimp only [GammaAux]
    rw [GammaIntegral_add_one h1]; rw [mul_div_cancel_left₀]
    rintro rfl
    rw [zero_re] at h1
    exact h1.false
  · dsimp only [GammaAux]
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.cast_add]; rw [Nat.cast_one] at h1
        rw [add_re]; rw [one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]

/- This definition is deliberately not @[expose]'d, since `GammaAux` is not mathematically
interesting. -/
/--
Definition of `Gamma` / `Gamma` 的定义

English:
definition Gamma
  signature: (s : Complex)
  body: GammaAux ⌊1 - s.re⌋₊ s

中文:
定义 Gamma
  签名: (s : 复形)
  定义体: GammaAux ⌊1 - s.re⌋₊ s
-/
@[irreducible, pp_nodot] def Gamma (s : Complex) : Complex :=
  GammaAux ⌊1 - s.re⌋₊ s

/--
theorem `Gamma_eq_GammaAux` / 定理 `Gamma_eq_GammaAux`

English:
theorem Gamma_eq_GammaAux
  given: (s : Complex) (n : Nat) (h1 : -s.re < ↑n)
  statement: Gamma s = GammaAux n s
  proof: by
  have u : forall k : Nat, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := fun k => by
    induction k with
    | zero => simp [Gamma]
    | succ k hk =>
      rw [← hk]; rw [← add_assoc]
      refine (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) ?_).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine lt_add_of_lt_of_nonneg i0 ?_
      rw [← Nat.cast_zero]; rw [Nat.cast_le]; exact Nat.zero_le k
  convert! (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases h : 0 <= 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    · lia
    · linarith

中文:
定理 Gamma_eq_GammaAux
  条件: (s : 复形) (n : 自然数) (h1 : -s.re < ↑n)
  结论: Gamma s = GammaAux n s
  证明: by
  have u : forall k : Nat, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := fun k => by
    induction k with
    | zero => simp [Gamma]
    | succ k hk =>
      rw [← hk]; rw [← add_assoc]
      refine (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) ?_).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine lt_add_of_lt_of_nonneg i0 ?_
      rw [← Nat.cast_zero]; rw [Nat.cast_le]; exact Nat.zero_le k
  convert! (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases h : 0 <= 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    · lia
    · linarith
-/
private theorem Gamma_eq_GammaAux (s : Complex) (n : Nat) (h1 : -s.re < ↑n) : Gamma s = GammaAux n s := by
  have u : forall k : Nat, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := fun k => by
    induction k with
    | zero => simp [Gamma]
    | succ k hk =>
      rw [← hk]; rw [← add_assoc]
      refine (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) ?_).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine lt_add_of_lt_of_nonneg i0 ?_
      rw [← Nat.cast_zero]; rw [Nat.cast_le]; exact Nat.zero_le k
  convert! (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  by_cases h : 0 <= 1 - s.re
  · apply Nat.le_of_lt_succ
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
  · rw [Nat.floor_of_nonpos]
    · lia
    · linarith

/-- The recurrence relation for the `Γ` function. -/
@[grind =]
/--
theorem `Gamma_add_one` / 定理 `Gamma_add_one`

English:
theorem Gamma_add_one
  given: (s : Complex) (h2 : s != 0)
  statement: Gamma (s + 1) = s * Gamma s
  proof: by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_GammaAux s n t1]; rw [Gamma_eq_GammaAux (s + 1) n t2]; rw [GammaAux_recurrence1 s n t1]
  field

中文:
定理 Gamma_add_one
  条件: (s : 复形) (h2 : s != 0)
  结论: Gamma (s + 1) = s * Gamma s
  证明: by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_GammaAux s n t1]; rw [Gamma_eq_GammaAux (s + 1) n t2]; rw [GammaAux_recurrence1 s n t1]
  field

Depends on / 依赖: GammaAux_recurrence1, Gamma_eq_GammaAux, Nat.sub_one_lt_floor, add_re, one_re, s.re, sub_one_lt_floor, sub_sub_cancel_left
-/
theorem Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma (s + 1) = s * Gamma s := by
  let n := ⌊1 - s.re⌋₊
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  rw [Gamma_eq_GammaAux s n t1]; rw [Gamma_eq_GammaAux (s + 1) n t2]; rw [GammaAux_recurrence1 s n t1]
  field

/--
theorem `Gamma_eq_integral` / 定理 `Gamma_eq_integral`

English:
theorem Gamma_eq_integral
  given: {s : Complex} (hs : 0 < s.re)
  statement: Gamma s = GammaIntegral s
  proof: Gamma_eq_GammaAux s 0 (by norm_cast; linarith)

@[simp]

中文:
定理 Gamma_eq_integral
  条件: {s : 复形} (hs : 0 < s.re)
  结论: Gamma s = Gamma整数egral s
  证明: Gamma_eq_GammaAux s 0 (by norm_cast; linarith)

@[simp]

Depends on / 依赖: Gamma_eq_GammaAux
-/
theorem Gamma_eq_integral {s : Complex} (hs : 0 < s.re) : Gamma s = GammaIntegral s :=
  Gamma_eq_GammaAux s 0 (by norm_cast; linarith)

@[simp]
/--
theorem `Gamma_one` / 定理 `Gamma_one`

English:
theorem Gamma_one
  statement: Gamma 1 = 1
  proof: by rw [Gamma_eq_integral] <;> simp

中文:
定理 Gamma_one
  结论: Gamma 1 = 1
  证明: by rw [Gamma_eq_integral] <;> simp

Depends on / 依赖: Gamma_eq_integral
-/
theorem Gamma_one : Gamma 1 = 1 := by rw [Gamma_eq_integral] <;> simp

/--
theorem `Gamma_nat_eq_factorial` / 定理 `Gamma_nat_eq_factorial`

English:
theorem Gamma_nat_eq_factorial
  given: (n : Nat)
  statement: Gamma (n + 1) = n !
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr

@[simp]

中文:
定理 Gamma_nat_eq_factorial
  条件: (n : 自然数)
  结论: Gamma (n + 1) = n !
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr

@[simp]

Depends on / 依赖: Gamma_add_one, Nat.cast_mul, Nat.cast_ne_zero.mpr, Nat.cast_succ, Nat.factorial_succ, Nat.succ_ne_zero, cast_mul, cast_ne_zero, cast_succ, factorial_succ, n.succ, succ_ne_zero
-/
theorem Gamma_nat_eq_factorial (n : Nat) : Gamma (n + 1) = n ! := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]
    congr

@[simp]
/--
theorem `Gamma_ofNat_eq_factorial` / 定理 `Gamma_ofNat_eq_factorial`

English:
theorem Gamma_ofNat_eq_factorial
  given: (n : Nat) [(n + 1).AtLeastTwo]
  proof: mod_cast Gamma_nat_eq_factorial (n : Nat)

中文:
定理 Gamma_of自然数_eq_factorial
  条件: (n : 自然数) [(n + 1).AtLeastTwo]
  证明: mod_cast Gamma_nat_eq_factorial (n : Nat)

Depends on / 依赖: Gamma_nat_eq_factorial, mod_cast
-/
theorem Gamma_ofNat_eq_factorial (n : Nat) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : Complex) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : Nat)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
/--
theorem `Gamma_zero` / 定理 `Gamma_zero`

English:
theorem Gamma_zero
  statement: Gamma 0 = 0
  proof: by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]

中文:
定理 Gamma_zero
  结论: Gamma 0 = 0
  证明: by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]

Depends on / 依赖: GammaAux, Nat.floor_one, div_zero, floor_one, simp_rw, sub_zero, zero_re
-/
theorem Gamma_zero : Gamma 0 = 0 := by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]

/--
theorem `Gamma_neg_nat_eq_zero` / 定理 `Gamma_neg_nat_eq_zero`

English:
theorem Gamma_neg_nat_eq_zero
  given: (n : Nat)
  statement: Gamma (-n) = 0
  proof: by
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, Gamma_zero]
  | succ n IH =>
    have A : -(n.succ : Complex) != 0 := by
      rw [neg_ne_zero]; rw [Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : Complex) = -↑n.succ + 1 := by simp
    rw [this]; rw [Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH

中文:
定理 Gamma_neg_nat_eq_zero
  条件: (n : 自然数)
  结论: Gamma (-n) = 0
  证明: by
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, Gamma_zero]
  | succ n IH =>
    have A : -(n.succ : Complex) != 0 := by
      rw [neg_ne_zero]; rw [Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : Complex) = -↑n.succ + 1 := by simp
    rw [this]; rw [Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH

Depends on / 依赖: Gamma_add_one, Gamma_zero, Nat.cast_ne_zero, Nat.cast_zero, Nat.succ_ne_zero, cast_ne_zero, cast_zero, contrapose, mul_ne_zero, n.succ, neg_ne_zero, neg_zero, succ_ne_zero
-/
theorem Gamma_neg_nat_eq_zero (n : Nat) : Gamma (-n) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, Gamma_zero]
  | succ n IH =>
    have A : -(n.succ : Complex) != 0 := by
      rw [neg_ne_zero]; rw [Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : Complex) = -↑n.succ + 1 := by simp
    rw [this]; rw [Gamma_add_one _ A] at IH
    contrapose! IH
    exact mul_ne_zero A IH

/--
theorem `Gamma_conj` / 定理 `Gamma_conj`

English:
theorem Gamma_conj
  given: (s : Complex)
  statement: Gamma (conj s) = conj (Gamma s)
  proof: by
  suffices forall (n : Nat) (s : Complex), GammaAux n (conj s) = conj (GammaAux n s) by
    simp [Gamma, this]
  intro n
  induction n with
  | zero => rw [GammaAux]; exact GammaIntegral_conj
  | succ n IH =>
    intro s
    rw [GammaAux]
    dsimp only
    rw [div_eq_mul_inv _ s]; rw [map_mul]; rw [conj_inv]; rw [← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [map_add]; rw [map_one]

中文:
定理 Gamma_conj
  条件: (s : 复形)
  结论: Gamma (conj s) = conj (Gamma s)
  证明: by
  suffices forall (n : Nat) (s : Complex), GammaAux n (conj s) = conj (GammaAux n s) by
    simp [Gamma, this]
  intro n
  induction n with
  | zero => rw [GammaAux]; exact GammaIntegral_conj
  | succ n IH =>
    intro s
    rw [GammaAux]
    dsimp only
    rw [div_eq_mul_inv _ s]; rw [map_mul]; rw [conj_inv]; rw [← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [map_add]; rw [map_one]

Depends on / 依赖: GammaAux, GammaIntegral_conj, conj_inv, div_eq_mul_inv, map_add, map_mul, map_one
-/
theorem Gamma_conj (s : Complex) : Gamma (conj s) = conj (Gamma s) := by
  suffices forall (n : Nat) (s : Complex), GammaAux n (conj s) = conj (GammaAux n s) by
    simp [Gamma, this]
  intro n
  induction n with
  | zero => rw [GammaAux]; exact GammaIntegral_conj
  | succ n IH =>
    intro s
    rw [GammaAux]
    dsimp only
    rw [div_eq_mul_inv _ s]; rw [map_mul]; rw [conj_inv]; rw [← div_eq_mul_inv]
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    rw [map_add]; rw [map_one]

/--
lemma `integral_cpow_mul_exp_neg_mul_Ioi` / 引理 `integral_cpow_mul_exp_neg_mul_Ioi`

English:
lemma integral_cpow_mul_exp_neg_mul_Ioi
  given: {a : Complex} {r : Real} (ha : 0 < a.re) (hr : 0 < r)
  proof: by
  have aux : (1 / r : Complex) ^ a = 1 / r * (1 / r) ^ (a - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : Complex)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne')]; rw [add_sub_cancel]
  calc
    _ = ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * (r * t) ^ (a - 1) * exp (-(r * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le]; rw [← mul_assoc]; rw [one_div]; rw [← ofReal_inv]; rw [← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le]; rw [← ofReal_mul r⁻¹]; rw [inv_mul_cancel₀ hr.ne']; rw [ofReal_one]; rw [one_cpow]; rw [one_mul]
    _ = 1 / r * ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * t ^ (a - 1) * exp (-t) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x => _ * x ^ (a - 1) * exp (-x)) _ hr]; rw [mul_zero]; rw [real_smul]; rw [← one_div]; rw [ofReal_div]; rw [ofReal_one]
    _ = 1 / r * (1 / r : Complex) ^ (a - 1) * (∫ (t : Real) in Ioi 0, t ^ (a - 1) * exp (-t)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ a * Gamma a := by
      rw [aux]; rw [Gamma_eq_integral ha]
      congr 2 with x
      rw [ofReal_exp]; rw [ofReal_neg]; rw [mul_comm]

中文:
引理 integral_cpow_mul_exp_neg_mul_Ioi
  条件: {a : 复形} {r : 实数} (ha : 0 < a.re) (hr : 0 < r)
  证明: by
  have aux : (1 / r : Complex) ^ a = 1 / r * (1 / r) ^ (a - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : Complex)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne')]; rw [add_sub_cancel]
  calc
    _ = ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * (r * t) ^ (a - 1) * exp (-(r * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le]; rw [← mul_assoc]; rw [one_div]; rw [← ofReal_inv]; rw [← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le]; rw [← ofReal_mul r⁻¹]; rw [inv_mul_cancel₀ hr.ne']; rw [ofReal_one]; rw [one_cpow]; rw [one_mul]
    _ = 1 / r * ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * t ^ (a - 1) * exp (-t) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x => _ * x ^ (a - 1) * exp (-x)) _ hr]; rw [mul_zero]; rw [real_smul]; rw [← one_div]; rw [ofReal_div]; rw [ofReal_one]
    _ = 1 / r * (1 / r : Complex) ^ (a - 1) * (∫ (t : Real) in Ioi 0, t ^ (a - 1) * exp (-t)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ a * Gamma a := by
      rw [aux]; rw [Gamma_eq_integral ha]
      congr 2 with x
      rw [ofReal_exp]; rw [ofReal_neg]; rw [mul_comm]

Depends on / 依赖: MeasureTheory, MeasureTheory.setIntegral_congr_fun, add_sub_cancel, cpow_add, cpow_one, hr.le, hr.ne, hx.le, measurableSet_Ioi, mem_Ioi, mul_assoc, mul_cpow_, mul_cpow_ofReal_nonneg, nth_rewrite, ofReal_inv, ofReal_ne_zero, ofReal_ne_zero.mpr, one_div, one_div_ne_zero, setIntegral_congr_fun
-/
lemma integral_cpow_mul_exp_neg_mul_Ioi {a : Complex} {r : Real} (ha : 0 < a.re) (hr : 0 < r) :
    ∫ (t : Real) in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  have aux : (1 / r : Complex) ^ a = 1 / r * (1 / r) ^ (a - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : Complex)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne')]; rw [add_sub_cancel]
  calc
    _ = ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * (r * t) ^ (a - 1) * exp (-(r * t)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le]; rw [← mul_assoc]; rw [one_div]; rw [← ofReal_inv]; rw [← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le]; rw [← ofReal_mul r⁻¹]; rw [inv_mul_cancel₀ hr.ne']; rw [ofReal_one]; rw [one_cpow]; rw [one_mul]
    _ = 1 / r * ∫ (t : Real) in Ioi 0, (1 / r) ^ (a - 1) * t ^ (a - 1) * exp (-t) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x => _ * x ^ (a - 1) * exp (-x)) _ hr]; rw [mul_zero]; rw [real_smul]; rw [← one_div]; rw [ofReal_div]; rw [ofReal_one]
    _ = 1 / r * (1 / r : Complex) ^ (a - 1) * (∫ (t : Real) in Ioi 0, t ^ (a - 1) * exp (-t)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ a * Gamma a := by
      rw [aux]; rw [Gamma_eq_integral ha]
      congr 2 with x
      rw [ofReal_exp]; rw [ofReal_neg]; rw [mul_comm]

end GammaDef

end Complex

namespace Real

/--
Definition of `Gamma` / `Gamma` 的定义

English:
definition Gamma
  signature: (s : Real)
  body: (Complex.Gamma s).re

中文:
定义 Gamma
  签名: (s : 实数)
  定义体: (Complex.Gamma s).re
-/
@[pp_nodot, expose] def Gamma (s : Real) : Real :=
  (Complex.Gamma s).re

/--
theorem `Gamma_eq_integral` / 定理 `Gamma_eq_integral`

English:
theorem Gamma_eq_integral
  given: {s : Real} (hs : 0 < s)
  proof: by
  rw [Gamma]; rw [Complex.Gamma_eq_integral (RCLike.ofReal_pos.mp hs)]; rw [Complex.GammaIntegral_ofReal]; rw [Complex.ofReal_re]

中文:
定理 Gamma_eq_integral
  条件: {s : 实数} (hs : 0 < s)
  证明: by
  rw [Gamma]; rw [Complex.Gamma_eq_integral (RCLike.ofReal_pos.mp hs)]; rw [Complex.GammaIntegral_ofReal]; rw [Complex.ofReal_re]

Depends on / 依赖: Complex.GammaIntegral_ofReal, Complex.Gamma_eq_integral, Complex.ofReal_re, GammaIntegral_ofReal, Gamma_eq_integral, RCLike, RCLike.ofReal_pos.mp, ofReal_pos, ofReal_re
-/
theorem Gamma_eq_integral {s : Real} (hs : 0 < s) :
    Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) := by
  rw [Gamma]; rw [Complex.Gamma_eq_integral (RCLike.ofReal_pos.mp hs)]; rw [Complex.GammaIntegral_ofReal]; rw [Complex.ofReal_re]

/--
theorem `Gamma_add_one` / 定理 `Gamma_add_one`

English:
theorem Gamma_add_one
  given: {s : Real} (hs : s != 0)
  statement: Gamma (s + 1) = s * Gamma s
  proof: by
  simp_rw [Gamma]
  rw [Complex.ofReal_add]; rw [Complex.ofReal_one]; rw [Complex.Gamma_add_one]; rw [Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]

@[simp]

中文:
定理 Gamma_add_one
  条件: {s : 实数} (hs : s != 0)
  结论: Gamma (s + 1) = s * Gamma s
  证明: by
  simp_rw [Gamma]
  rw [Complex.ofReal_add]; rw [Complex.ofReal_one]; rw [Complex.Gamma_add_one]; rw [Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]

@[simp]

Depends on / 依赖: Complex.Gamma_add_one, Complex.ofReal_add, Complex.ofReal_ne_zero, Complex.ofReal_one, Complex.re_ofReal_mul, Gamma_add_one, ofReal_add, ofReal_ne_zero, ofReal_one, re_ofReal_mul, simp_rw
-/
theorem Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 1) = s * Gamma s := by
  simp_rw [Gamma]
  rw [Complex.ofReal_add]; rw [Complex.ofReal_one]; rw [Complex.Gamma_add_one]; rw [Complex.re_ofReal_mul]
  rwa [Complex.ofReal_ne_zero]

@[simp]
/--
theorem `Gamma_one` / 定理 `Gamma_one`

English:
theorem Gamma_one
  statement: Gamma 1 = 1
  proof: by
  rw [Gamma]; rw [Complex.ofReal_one]; rw [Complex.Gamma_one]; rw [Complex.one_re]

中文:
定理 Gamma_one
  结论: Gamma 1 = 1
  证明: by
  rw [Gamma]; rw [Complex.ofReal_one]; rw [Complex.Gamma_one]; rw [Complex.one_re]

Depends on / 依赖: Complex.Gamma_one, Complex.ofReal_one, Complex.one_re, Gamma_one, ofReal_one, one_re
-/
theorem Gamma_one : Gamma 1 = 1 := by
  rw [Gamma]; rw [Complex.ofReal_one]; rw [Complex.Gamma_one]; rw [Complex.one_re]

/--
theorem `_root_.Complex.Gamma_ofReal` / 定理 `_root_.Complex.Gamma_ofReal`

English:
theorem _root_.Complex.Gamma_ofReal
  given: (s : Real)
  statement: Complex.Gamma (s : Complex) = Gamma s
  proof: by
  rw [Gamma]; rw [eq_comm]; rw [← Complex.conj_eq_iff_re]; rw [← Complex.Gamma_conj]; rw [Complex.conj_ofReal]

中文:
定理 _root_.复形.Gamma_of实数
  条件: (s : 实数)
  结论: 复形.Gamma (s : 复形) = Gamma s
  证明: by
  rw [Gamma]; rw [eq_comm]; rw [← Complex.conj_eq_iff_re]; rw [← Complex.Gamma_conj]; rw [Complex.conj_ofReal]

Depends on / 依赖: Complex.Gamma_conj, Complex.conj_eq_iff_re, Complex.conj_ofReal, Gamma_conj, conj_eq_iff_re, conj_ofReal, eq_comm
-/
theorem _root_.Complex.Gamma_ofReal (s : Real) : Complex.Gamma (s : Complex) = Gamma s := by
  rw [Gamma]; rw [eq_comm]; rw [← Complex.conj_eq_iff_re]; rw [← Complex.Gamma_conj]; rw [Complex.conj_ofReal]

/--
theorem `Gamma_nat_eq_factorial` / 定理 `Gamma_nat_eq_factorial`

English:
theorem Gamma_nat_eq_factorial
  given: (n : Nat)
  statement: Gamma (n + 1) = n !
  proof: by
  rw [Gamma]; rw [Complex.ofReal_add]; rw [Complex.ofReal_natCast]; rw [Complex.ofReal_one]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Complex.ofReal_natCast]; rw [Complex.ofReal_re]

@[simp]

中文:
定理 Gamma_nat_eq_factorial
  条件: (n : 自然数)
  结论: Gamma (n + 1) = n !
  证明: by
  rw [Gamma]; rw [Complex.ofReal_add]; rw [Complex.ofReal_natCast]; rw [Complex.ofReal_one]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Complex.ofReal_natCast]; rw [Complex.ofReal_re]

@[simp]

Depends on / 依赖: Complex.Gamma_nat_eq_factorial, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_re, Gamma_nat_eq_factorial, ofReal_add, ofReal_natCast, ofReal_one, ofReal_re
-/
theorem Gamma_nat_eq_factorial (n : Nat) : Gamma (n + 1) = n ! := by
  rw [Gamma]; rw [Complex.ofReal_add]; rw [Complex.ofReal_natCast]; rw [Complex.ofReal_one]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Complex.ofReal_natCast]; rw [Complex.ofReal_re]

@[simp]
/--
theorem `Gamma_ofNat_eq_factorial` / 定理 `Gamma_ofNat_eq_factorial`

English:
theorem Gamma_ofNat_eq_factorial
  given: (n : Nat) [(n + 1).AtLeastTwo]
  proof: mod_cast Gamma_nat_eq_factorial (n : Nat)

中文:
定理 Gamma_of自然数_eq_factorial
  条件: (n : 自然数) [(n + 1).AtLeastTwo]
  证明: mod_cast Gamma_nat_eq_factorial (n : Nat)

Depends on / 依赖: Gamma_nat_eq_factorial, mod_cast
-/
theorem Gamma_ofNat_eq_factorial (n : Nat) [(n + 1).AtLeastTwo] :
    Gamma (ofNat(n + 1) : Real) = n ! :=
  mod_cast Gamma_nat_eq_factorial (n : Nat)

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
@[simp]
/--
theorem `Gamma_zero` / 定理 `Gamma_zero`

English:
theorem Gamma_zero
  statement: Gamma 0 = 0
  proof: by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero

中文:
定理 Gamma_zero
  结论: Gamma 0 = 0
  证明: by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero

Depends on / 依赖: Complex.Gamma_ofReal, Complex.Gamma_zero, Complex.ofReal_inj, Complex.ofReal_zero, Gamma_ofReal, Gamma_zero, ofReal_inj, ofReal_zero
-/
theorem Gamma_zero : Gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero

/--
theorem `Gamma_neg_nat_eq_zero` / 定理 `Gamma_neg_nat_eq_zero`

English:
theorem Gamma_neg_nat_eq_zero
  given: (n : Nat)
  statement: Gamma (-n) = 0
  proof: by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n

中文:
定理 Gamma_neg_nat_eq_zero
  条件: (n : 自然数)
  结论: Gamma (-n) = 0
  证明: by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n

Depends on / 依赖: Complex.Gamma_neg_nat_eq_zero, Complex.Gamma_ofReal, Complex.ofReal_eq_zero, Complex.ofReal_natCast, Complex.ofReal_neg, Gamma_neg_nat_eq_zero, Gamma_ofReal, ofReal_eq_zero, ofReal_natCast, ofReal_neg
-/
theorem Gamma_neg_nat_eq_zero (n : Nat) : Gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n

/--
theorem `Gamma_pos_of_pos` / 定理 `Gamma_pos_of_pos`

English:
theorem Gamma_pos_of_pos
  given: {s : Real} (hs : 0 < s)
  statement: 0 < Gamma s
  proof: by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : Real => exp (-x) * x ^ (s - 1)) inter Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact GammaIntegral_convergent hs

中文:
定理 Gamma_pos_of_pos
  条件: {s : 实数} (hs : 0 < s)
  结论: 0 < Gamma s
  证明: by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : Real => exp (-x) * x ^ (s - 1)) inter Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact GammaIntegral_convergent hs

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, ENNReal.ofReal_zero, Function, Function.mem_support, Function.support, Gamma_eq_integral, eventually_of_mem, exp_pos, inter_eq_right, measurableSet_Ioi, mem_support, mul_ne_zero, mul_pos, ofReal_lt_top, ofReal_zero, rpow_pos_of_pos, self_mem_ae_restrict, setIntegral_pos_iff_support_of_nonneg_ae, support
-/
theorem Gamma_pos_of_pos {s : Real} (hs : 0 < s) : 0 < Gamma s := by
  rw [Gamma_eq_integral hs]
  have : (Function.support fun x : Real => exp (-x) * x ^ (s - 1)) inter Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
  · exact GammaIntegral_convergent hs

/--
theorem `Gamma_nonneg_of_nonneg` / 定理 `Gamma_nonneg_of_nonneg`

English:
theorem Gamma_nonneg_of_nonneg
  given: {s : Real} (hs : 0 <= s)
  statement: 0 <= Gamma s
  proof: by
  obtain rfl | h := eq_or_lt_of_le hs
  · rw [Gamma_zero]
  · exact (Gamma_pos_of_pos h).le

中文:
定理 Gamma_nonneg_of_nonneg
  条件: {s : 实数} (hs : 0 <= s)
  结论: 0 <= Gamma s
  证明: by
  obtain rfl | h := eq_or_lt_of_le hs
  · rw [Gamma_zero]
  · exact (Gamma_pos_of_pos h).le

Depends on / 依赖: Gamma_pos_of_pos, Gamma_zero, eq_or_lt_of_le
-/
theorem Gamma_nonneg_of_nonneg {s : Real} (hs : 0 <= s) : 0 <= Gamma s := by
  obtain rfl | h := eq_or_lt_of_le hs
  · rw [Gamma_zero]
  · exact (Gamma_pos_of_pos h).le

open Complex in
/--
lemma `integral_rpow_mul_exp_neg_mul_Ioi` / 引理 `integral_rpow_mul_exp_neg_mul_Ioi`

English:
lemma integral_rpow_mul_exp_neg_mul_Ioi
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r)
  proof: by
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [← Gamma_ofReal]; rw [ofReal_cpow (by positivity)]; rw [ofReal_div]
  convert! integral_cpow_mul_exp_neg_mul_Ioi (by rwa [ofReal_re] : 0 < (a : Complex).re) hr
refine integral_ofReal.symm.trans setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  norm_cast
  simp_rw [← ofReal_cpow ht.le, RCLike.ofReal_mul, coe_algebraMap]

中文:
引理 integral_rpow_mul_exp_neg_mul_Ioi
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r)
  证明: by
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [← Gamma_ofReal]; rw [ofReal_cpow (by positivity)]; rw [ofReal_div]
  convert! integral_cpow_mul_exp_neg_mul_Ioi (by rwa [ofReal_re] : 0 < (a : Complex).re) hr
refine integral_ofReal.symm.trans setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  norm_cast
  simp_rw [← ofReal_cpow ht.le, RCLike.ofReal_mul, coe_algebraMap]

Depends on / 依赖: Gamma_ofReal, RCLike, RCLike.ofReal_mul, coe_algebraMap, convert, ht.le, integral_cpow_mul_exp_neg_mul_Ioi, integral_ofReal, integral_ofReal.symm.trans, measurableSet_Ioi, ofReal_cpow, ofReal_div, ofReal_inj, ofReal_mul, ofReal_re, setIntegral_congr_fun, simp_rw
-/
lemma integral_rpow_mul_exp_neg_mul_Ioi {a r : Real} (ha : 0 < a) (hr : 0 < r) :
    ∫ t : Real in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a := by
  rw [← ofReal_inj]; rw [ofReal_mul]; rw [← Gamma_ofReal]; rw [ofReal_cpow (by positivity)]; rw [ofReal_div]
  convert! integral_cpow_mul_exp_neg_mul_Ioi (by rwa [ofReal_re] : 0 < (a : Complex).re) hr
refine integral_ofReal.symm.trans setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  norm_cast
  simp_rw [← ofReal_cpow ht.le, RCLike.ofReal_mul, coe_algebraMap]

open Lean.Meta Qq Mathlib.Meta.Positivity in
/-- The `positivity` extension which identifies expressions of the form `Gamma a`. -/
@[positivity Gamma (_ : Real)]
meta def _root_.Mathlib.Meta.Positivity.evalGamma : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Gamma $a) =>
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(Gamma_pos_of_pos $pa))
    | .nonnegative pa =>
      assertInstancesCommute
      pure (.nonnegative q(Gamma_nonneg_of_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Gamma application"

/--
theorem `Gamma_ne_zero` / 定理 `Gamma_ne_zero`

English:
theorem Gamma_ne_zero
  given: {s : Real} (hs : forall m : Nat, s != -m)
  statement: Gamma s != 0
  proof: by
  suffices forall {n : Nat}, -(n : Real) < s -> Gamma s != 0 by
    apply this
    swap
    · exact ⌊-s⌋₊ + 1
    rw [neg_lt]; rw [Nat.cast_add]; rw [Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s with
  | zero =>
    intro hs
    refine (Gamma_pos_of_pos ?_).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  | succ _ n_ih =>
    intro hs'
    have : Gamma (s + 1) != 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one]; rw [mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0

中文:
定理 Gamma_ne_zero
  条件: {s : 实数} (hs : 对任意 m : 自然数, s != -m)
  结论: Gamma s != 0
  证明: by
  suffices forall {n : Nat}, -(n : Real) < s -> Gamma s != 0 by
    apply this
    swap
    · exact ⌊-s⌋₊ + 1
    rw [neg_lt]; rw [Nat.cast_add]; rw [Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s with
  | zero =>
    intro hs
    refine (Gamma_pos_of_pos ?_).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  | succ _ n_ih =>
    intro hs'
    have : Gamma (s + 1) != 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one]; rw [mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0

Depends on / 依赖: Gamma_pos_of_pos, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.lt_floor_add_one, cast_add, cast_one, cast_zero, contrapose, eq_sub_iff_add_eq, generalizing, lt_floor_add_one, n_ih, neg_lt, neg_zero, specialize
-/
theorem Gamma_ne_zero {s : Real} (hs : forall m : Nat, s != -m) : Gamma s != 0 := by
  suffices forall {n : Nat}, -(n : Real) < s -> Gamma s != 0 by
    apply this
    swap
    · exact ⌊-s⌋₊ + 1
    rw [neg_lt]; rw [Nat.cast_add]; rw [Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  induction n generalizing s with
  | zero =>
    intro hs
    refine (Gamma_pos_of_pos ?_).ne'
    rwa [Nat.cast_zero, neg_zero] at hs
  | succ _ n_ih =>
    intro hs'
    have : Gamma (s + 1) != 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one]; rw [mul_ne_zero_iff] at this
    · exact this.2
    · simpa using hs 0

/--
theorem `Gamma_eq_zero_iff` / 定理 `Gamma_eq_zero_iff`

English:
theorem Gamma_eq_zero_iff
  given: (s : Real)
  statement: Gamma s = 0 ↔ exists m : Nat, s = -m
  proof: ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩

中文:
定理 Gamma_eq_zero_iff
  条件: (s : 实数)
  结论: Gamma s = 0 ↔ 存在 m : 自然数, s = -m
  证明: ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩

Depends on / 依赖: Gamma_ne_zero, Gamma_neg_nat_eq_zero, contrapose
-/
theorem Gamma_eq_zero_iff (s : Real) : Gamma s = 0 ↔ exists m : Nat, s = -m :=
  ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩

end Real
