/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = √(π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `Complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

open Complex hiding exp

/--
theorem `exp_neg_mul_rpow_isLittleO_exp_neg` / 定理 `exp_neg_mul_rpow_isLittleO_exp_neg`

English:
theorem exp_neg_mul_rpow_isLittleO_exp_neg
  given: {p b : Real} (hb : 0 < b) (hp : 1 < p)
  proof: by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : Real)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field
  apply tendsto_id.atTop_mul_atTop₀
  refine tendsto_atTop_add_const_right atTop (-1 : Real) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))

中文:
定理 exp_neg_mul_rpow_isLittleO_exp_neg
  条件: {p b : 实数} (hb : 0 < b) (hp : 1 < p)
  证明: by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : Real)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field
  apply tendsto_id.atTop_mul_atTop₀
  refine tendsto_atTop_add_const_right atTop (-1 : Real) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))

Depends on / 依赖: Ioi_mem_atTop, Tendsto, Tendsto.congr, Tendsto.const_mul_atTop, const_mul_atTop, eventuallyEq_of_mem, hx.ne, isLittleO_exp_comp_exp_comp, mem_Ioi, rpow_sub_one, tendsto_atTop_add_const_right, tendsto_id, tendsto_id.atTop_mul_atTop, tendsto_rpow_atTop
-/
theorem exp_neg_mul_rpow_isLittleO_exp_neg {p b : Real} (hb : 0 < b) (hp : 1 < p) :
    (fun x : Real => exp (- b * x ^ p)) =o[atTop] fun x : Real => exp (-x) := by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : Real)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field
  apply tendsto_id.atTop_mul_atTop₀
  refine tendsto_atTop_add_const_right atTop (-1 : Real) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))

/--
theorem `exp_neg_mul_sq_isLittleO_exp_neg` / 定理 `exp_neg_mul_sq_isLittleO_exp_neg`

English:
theorem exp_neg_mul_sq_isLittleO_exp_neg
  given: {b : Real} (hb : 0 < b)
  proof: by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two

中文:
定理 exp_neg_mul_sq_isLittleO_exp_neg
  条件: {b : 实数} (hb : 0 < b)
  证明: by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two

Depends on / 依赖: exp_neg_mul_rpow_isLittleO_exp_neg, one_lt_two, rpow_two, simp_rw
-/
theorem exp_neg_mul_sq_isLittleO_exp_neg {b : Real} (hb : 0 < b) :
    (fun x : Real => exp (-b * x ^ 2)) =o[atTop] fun x : Real => exp (-x) := by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two

/--
theorem `rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg` / 定理 `rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg`

English:
theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg
  given: (s : Real) {b p : Real} (hp : 1 < p) (hb : 0 < b)
  proof: by
  apply ((isBigO_refl (fun x : Real => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

中文:
定理 rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg
  条件: (s : 实数) {b p : 实数} (hp : 1 < p) (hb : 0 < b)
  证明: by
  apply ((isBigO_refl (fun x : Real => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

Depends on / 依赖: Gamma_integrand_isLittleO, Real.Gamma_integrand_isLittleO, exp_neg_mul_rpow_isLittleO_exp_neg, isBigO_refl, isEquivalence_preservesColimits, mul_comm, mul_isLittleO
-/
theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : Real) {b p : Real} (hp : 1 < p) (hb : 0 < b) :
    (fun x : Real => x ^ s * exp (- b * x ^ p)) =o[atTop] fun x : Real => exp (-(1 / 2) * x) := by
  apply ((isBigO_refl (fun x : Real => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

/--
theorem `rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg` / 定理 `rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg`

English:
theorem rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
  given: {b : Real} (hb : 0 < b) (s : Real)
  proof: by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb

中文:
定理 rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
  条件: {b : 实数} (hb : 0 < b) (s : 实数)
  证明: by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb

Depends on / 依赖: one_lt_two, rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg, rpow_two, simp_rw
-/
theorem rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg {b : Real} (hb : 0 < b) (s : Real) :
    (fun x : Real => x ^ s * exp (-b * x ^ 2)) =o[atTop] fun x : Real => exp (-(1 / 2) * x) := by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb

/--
theorem `integrableOn_rpow_mul_exp_neg_rpow` / 定理 `integrableOn_rpow_mul_exp_neg_rpow`

English:
theorem integrableOn_rpow_mul_exp_neg_rpow
  given: {p s : Real} (hs : -1 < s) (hp : 0 < p)
  proof: by
  -- Substitute `u = x ^ p`, reducing to convergence of the `Γ`-integral at `(s + 1) / p`.
  have ht : (0 : Real) < (s + 1) / p := div_pos (by linarith) hp
  refine ((integrableOn_Ioi_comp_rpow_iff' _ hp.ne').mpr
    (GammaIntegral_convergent ht)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [mul_comm (exp (-x ^ p))]; rw [← mul_assoc]; rw [← rpow_mul hx.le]; rw [← rpow_add hx]
  field_simp
  ring_nf

中文:
定理 integrableOn_rpow_mul_exp_neg_rpow
  条件: {p s : 实数} (hs : -1 < s) (hp : 0 < p)
  证明: by
  -- Substitute `u = x ^ p`, reducing to convergence of the `Γ`-integral at `(s + 1) / p`.
  have ht : (0 : Real) < (s + 1) / p := div_pos (by linarith) hp
  refine ((integrableOn_Ioi_comp_rpow_iff' _ hp.ne').mpr
    (GammaIntegral_convergent ht)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [mul_comm (exp (-x ^ p))]; rw [← mul_assoc]; rw [← rpow_mul hx.le]; rw [← rpow_add hx]
  field_simp
  ring_nf
-/
theorem integrableOn_rpow_mul_exp_neg_rpow {p s : Real} (hs : -1 < s) (hp : 0 < p) :
    IntegrableOn (fun x : Real => x ^ s * exp (- x ^ p)) (Ioi 0) := by
  -- Substitute `u = x ^ p`, reducing to convergence of the `Γ`-integral at `(s + 1) / p`.
  have ht : (0 : Real) < (s + 1) / p := div_pos (by linarith) hp
  refine ((integrableOn_Ioi_comp_rpow_iff' _ hp.ne').mpr
    (GammaIntegral_convergent ht)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [mul_comm (exp (-x ^ p))]; rw [← mul_assoc]; rw [← rpow_mul hx.le]; rw [← rpow_add hx]
  field_simp
  ring_nf

/--
theorem `integrableOn_rpow_mul_exp_neg_mul_rpow` / 定理 `integrableOn_rpow_mul_exp_neg_mul_rpow`

English:
theorem integrableOn_rpow_mul_exp_neg_mul_rpow
  given: {p s b : Real} (hs : -1 < s) (hp : 0 < p) (hb : 0 < b)
  proof: by
  have hib : 0 < b ^ (-p⁻¹) := rpow_pos_of_pos hb _
  suffices IntegrableOn (fun x => (b ^ (-p⁻¹)) ^ s * (x ^ s * exp (-x ^ p))) (Ioi 0) by
    rw [show 0 = b ^ (-p⁻¹) * 0 by rw [mul_zero], ← integrableOn_Ioi_comp_mul_left_iff _ _ hib]
    refine this.congr_fun (fun _ hx => ?_) measurableSet_Ioi
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    rw [← mul_assoc]; rw [mul_rpow]; rw [mul_rpow]; rw [← rpow_mul (z := p)]; rw [neg_mul]; rw [neg_mul]; rw [inv_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp

中文:
定理 integrableOn_rpow_mul_exp_neg_mul_rpow
  条件: {p s b : 实数} (hs : -1 < s) (hp : 0 < p) (hb : 0 < b)
  证明: by
  have hib : 0 < b ^ (-p⁻¹) := rpow_pos_of_pos hb _
  suffices IntegrableOn (fun x => (b ^ (-p⁻¹)) ^ s * (x ^ s * exp (-x ^ p))) (Ioi 0) by
    rw [show 0 = b ^ (-p⁻¹) * 0 by rw [mul_zero], ← integrableOn_Ioi_comp_mul_left_iff _ _ hib]
    refine this.congr_fun (fun _ hx => ?_) measurableSet_Ioi
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    rw [← mul_assoc]; rw [mul_rpow]; rw [mul_rpow]; rw [← rpow_mul (z := p)]; rw [neg_mul]; rw [neg_mul]; rw [inv_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp

Depends on / 依赖: IntegrableOn, adaptation_note, because, congr_fun, different, github, github.com, instantiation, integrableOn_Ioi_comp_mul_left_iff, leanprover, measurableSet_Ioi, mul_zero, removed, rpow_pos_of_pos, slightly, this.congr_fun
-/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow {p s b : Real} (hs : -1 < s) (hp : 0 < p) (hb : 0 < b) :
    IntegrableOn (fun x : Real => x ^ s * exp (- b * x ^ p)) (Ioi 0) := by
  have hib : 0 < b ^ (-p⁻¹) := rpow_pos_of_pos hb _
  suffices IntegrableOn (fun x => (b ^ (-p⁻¹)) ^ s * (x ^ s * exp (-x ^ p))) (Ioi 0) by
    rw [show 0 = b ^ (-p⁻¹) * 0 by rw [mul_zero], ← integrableOn_Ioi_comp_mul_left_iff _ _ hib]
    refine this.congr_fun (fun _ hx => ?_) measurableSet_Ioi
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    rw [← mul_assoc]; rw [mul_rpow]; rw [mul_rpow]; rw [← rpow_mul (z := p)]; rw [neg_mul]; rw [neg_mul]; rw [inv_mul_cancel₀]; rw [rpow_neg_one]; rw [mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp

/--
theorem `integrableOn_rpow_mul_exp_neg_mul_sq` / 定理 `integrableOn_rpow_mul_exp_neg_mul_sq`

English:
theorem integrableOn_rpow_mul_exp_neg_mul_sq
  given: {b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s)
  proof: by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs two_pos hb

中文:
定理 integrableOn_rpow_mul_exp_neg_mul_sq
  条件: {b : 实数} (hb : 0 < b) {s : 实数} (hs : -1 < s)
  证明: by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs two_pos hb

Depends on / 依赖: integrableOn_rpow_mul_exp_neg_mul_rpow, rpow_two, simp_rw, two_pos
-/
theorem integrableOn_rpow_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s) :
    IntegrableOn (fun x : Real => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs two_pos hb

/--
theorem `integrable_rpow_mul_exp_neg_mul_sq` / 定理 `integrable_rpow_mul_exp_neg_mul_sq`

English:
theorem integrable_rpow_mul_exp_neg_mul_sq
  given: {b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s)
  proof: by
  rw [← integrableOn_univ]; rw [← @Iio_union_Ici _ _ (0 : Real)]; rw [integrableOn_union]; rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure Real)).integrableOn_comp_preimage
      (Homeomorph.neg Real).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
  apply Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.aestronglyMeasurable
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : Real)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 <= x := le_of_lt hx
    rw [Real.norm_eq_abs]; rw [abs_mul]; rw [abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s

中文:
定理 integrable_rpow_mul_exp_neg_mul_sq
  条件: {b : 实数} (hb : 0 < b) {s : 实数} (hs : -1 < s)
  证明: by
  rw [← integrableOn_univ]; rw [← @Iio_union_Ici _ _ (0 : Real)]; rw [integrableOn_union]; rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure Real)).integrableOn_comp_preimage
      (Homeomorph.neg Real).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
  apply Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.aestronglyMeasurable
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : Real)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 <= x := le_of_lt hx
    rw [Real.norm_eq_abs]; rw [abs_mul]; rw [abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s

Depends on / 依赖: Function, Function.comp_def, Homeomorph, Homeomorph.neg, Iio_union_Ici, Integrable, Integrable.mono, Measurable, Measurable.aestronglyMeasurabl, Measure, Measure.measurePreserving_neg, aestronglyMeasurabl, comp_def, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_comp_preimage, integrableOn_rpow_mul_exp_neg_mul_sq, integrableOn_union, integrableOn_univ, measurableEmbedding, measurePreserving_neg
-/
theorem integrable_rpow_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s) :
    Integrable fun x : Real => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrableOn_univ]; rw [← @Iio_union_Ici _ _ (0 : Real)]; rw [integrableOn_union]; rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure Real)).integrableOn_comp_preimage
      (Homeomorph.neg Real).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
  apply Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.aestronglyMeasurable
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : Real)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 <= x := le_of_lt hx
    rw [Real.norm_eq_abs]; rw [abs_mul]; rw [abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s

/--
theorem `integrable_exp_neg_mul_sq` / 定理 `integrable_exp_neg_mul_sq`

English:
theorem integrable_exp_neg_mul_sq
  given: {b : Real} (hb : 0 < b)
  proof: by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 0)

中文:
定理 integrable_exp_neg_mul_sq
  条件: {b : 实数} (hb : 0 < b)
  证明: by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 0)

Depends on / 依赖: integrable_rpow_mul_exp_neg_mul_sq
-/
theorem integrable_exp_neg_mul_sq {b : Real} (hb : 0 < b) :
    Integrable fun x : Real => exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 0)

/--
theorem `integrableOn_Ioi_exp_neg_mul_sq_iff` / 定理 `integrableOn_Ioi_exp_neg_mul_sq_iff`

English:
theorem integrableOn_Ioi_exp_neg_mul_sq_iff
  given: {b : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : Real in Ioi 0, 1 <= ∫⁻ x : Real in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x => _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x => mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2

中文:
定理 integrableOn_Ioi_exp_neg_mul_sq_iff
  条件: {b : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : Real in Ioi 0, 1 <= ∫⁻ x : Real in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x => _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x => mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2

Depends on / 依赖: ENNReal, ENNReal.one_le_coe_iff, Real.norm_of_nonneg, Right.nonneg_neg_iff, coe_nnnorm, exp_pos, integrableOn, integrable_exp_neg_mul_sq, lintegral_mono, mul_nonpos_of_nonpos_of_nonneg, neg_mul, nonneg_neg_iff, norm_of_nonneg, one_le_coe_iff, one_le_exp_iff, sq_nonneg, this.trans_lt, toNNReal_le_iff_le_coe, toNNReal_one, trans_lt
-/
theorem integrableOn_Ioi_exp_neg_mul_sq_iff {b : Real} :
    IntegrableOn (fun x : Real => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine ⟨fun h => ?_, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : Real in Ioi 0, 1 <= ∫⁻ x : Real in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x => _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x => mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2

/--
theorem `integrable_exp_neg_mul_sq_iff` / 定理 `integrable_exp_neg_mul_sq_iff`

English:
theorem integrable_exp_neg_mul_sq_iff
  given: {b : Real}
  proof: ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩

中文:
定理 integrable_exp_neg_mul_sq_iff
  条件: {b : 实数}
  证明: ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩

Depends on / 依赖: h.integrableOn, integrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, integrableOn_Ioi_exp_neg_mul_sq_iff.mp, integrable_exp_neg_mul_sq
-/
theorem integrable_exp_neg_mul_sq_iff {b : Real} :
    (Integrable fun x : Real => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩

/--
theorem `integrable_mul_exp_neg_mul_sq` / 定理 `integrable_mul_exp_neg_mul_sq`

English:
theorem integrable_mul_exp_neg_mul_sq
  given: {b : Real} (hb : 0 < b)
  proof: by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 1)

中文:
定理 integrable_mul_exp_neg_mul_sq
  条件: {b : 实数} (hb : 0 < b)
  证明: by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 1)

Depends on / 依赖: integrable_rpow_mul_exp_neg_mul_sq
-/
theorem integrable_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) :
    Integrable fun x : Real => x * exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : Real) < 1)

/--
theorem `norm_cexp_neg_mul_sq` / 定理 `norm_cexp_neg_mul_sq`

English:
theorem norm_cexp_neg_mul_sq
  given: (b : Complex) (x : Real)
  proof: by
  rw [norm_exp]; rw [← ofReal_pow]; rw [mul_comm (-b) _]; rw [re_ofReal_mul]; rw [neg_re]; rw [mul_comm]

中文:
定理 norm_cexp_neg_mul_sq
  条件: (b : 复形) (x : 实数)
  证明: by
  rw [norm_exp]; rw [← ofReal_pow]; rw [mul_comm (-b) _]; rw [re_ofReal_mul]; rw [neg_re]; rw [mul_comm]

Depends on / 依赖: mul_comm, neg_re, norm_exp, ofReal_pow, re_ofReal_mul
-/
theorem norm_cexp_neg_mul_sq (b : Complex) (x : Real) :
    ‖Complex.exp (-b * (x : Complex) ^ 2)‖ = exp (-b.re * x ^ 2) := by
  rw [norm_exp]; rw [← ofReal_pow]; rw [mul_comm (-b) _]; rw [re_ofReal_mul]; rw [neg_re]; rw [mul_comm]

/--
theorem `integrable_cexp_neg_mul_sq` / 定理 `integrable_cexp_neg_mul_sq`

English:
theorem integrable_cexp_neg_mul_sq
  given: {b : Complex} (hb : 0 < b.re)
  proof: by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2

中文:
定理 integrable_cexp_neg_mul_sq
  条件: {b : 复形} (hb : 0 < b.re)
  证明: by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2

Depends on / 依赖: fun_prop, hasFiniteIntegral_norm_iff, integrable_exp_neg_mul_sq, norm_cexp_neg_mul_sq, simp_rw
-/
theorem integrable_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) :
    Integrable fun x : Real => cexp (-b * (x : Complex) ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2

/--
theorem `integrable_mul_cexp_neg_mul_sq` / 定理 `integrable_mul_cexp_neg_mul_sq`

English:
theorem integrable_mul_cexp_neg_mul_sq
  given: {b : Complex} (hb : 0 < b.re)
  proof: by
  refine ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp ?_)).aestronglyMeasurable, ?_⟩
  · fun_prop
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert! this
  rw [norm_mul]; rw [norm_mul]; rw [norm_cexp_neg_mul_sq b]; rw [norm_real]; rw [norm_of_nonneg (exp_pos _).le]

中文:
定理 integrable_mul_cexp_neg_mul_sq
  条件: {b : 复形} (hb : 0 < b.re)
  证明: by
  refine ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp ?_)).aestronglyMeasurable, ?_⟩
  · fun_prop
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert! this
  rw [norm_mul]; rw [norm_mul]; rw [norm_cexp_neg_mul_sq b]; rw [norm_real]; rw [norm_of_nonneg (exp_pos _).le]

Depends on / 依赖: Complex.continuous_exp.comp, aestronglyMeasurable, continuous_exp, continuous_ofReal, continuous_ofReal.mul, convert, exp_pos, fun_prop, hasFiniteIntegral, hasFiniteIntegral_norm_iff, integrable_mul_exp_neg_mul_sq, norm_cexp_neg_mul_sq, norm_mul, norm_of_nonneg, norm_real
-/
theorem integrable_mul_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) :
    Integrable fun x : Real => ↑x * cexp (-b * (x : Complex) ^ 2) := by
  refine ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp ?_)).aestronglyMeasurable, ?_⟩
  · fun_prop
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert! this
  rw [norm_mul]; rw [norm_mul]; rw [norm_cexp_neg_mul_sq b]; rw [norm_real]; rw [norm_of_nonneg (exp_pos _).le]

/--
theorem `integral_mul_cexp_neg_mul_sq` / 定理 `integral_mul_cexp_neg_mul_sq`

English:
theorem integral_mul_cexp_neg_mul_sq
  given: {b : Complex} (hb : 0 < b.re)
  proof: by
  have hb' : b != 0 := by contrapose! hb; rw [hb, zero_re]
  have A : forall x : Complex, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert! ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field
  have B : Tendsto (fun y : Real => -(2 * b)⁻¹ * cexp (-b * (y : Complex) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert!
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
      (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add, reduceCtorEq]

中文:
定理 integral_mul_cexp_neg_mul_sq
  条件: {b : 复形} (hb : 0 < b.re)
  证明: by
  have hb' : b != 0 := by contrapose! hb; rw [hb, zero_re]
  have A : forall x : Complex, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert! ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field
  have B : Tendsto (fun y : Real => -(2 * b)⁻¹ * cexp (-b * (y : Complex) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert!
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
      (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add, reduceCtorEq]

Depends on / 依赖: HasDerivAt, Tendsto, Tendsto.const_mul, cexp.const_mul, const_mul, contrapose, convert, hasDerivAt_pow, isEquivalencePreservesLimits, norm_cexp_neg_mul_sq, simp_rw, tendsto_, tendsto_zero_iff_norm_tendsto_zero, tendsto_zero_iff_norm_tendsto_zero.mpr, zero_re
-/
theorem integral_mul_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) :
    ∫ r : Real in Ioi 0, (r : Complex) * cexp (-b * (r : Complex) ^ 2) = (2 * b)⁻¹ := by
  have hb' : b != 0 := by contrapose! hb; rw [hb, zero_re]
  have A : forall x : Complex, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert! ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field
  have B : Tendsto (fun y : Real => -(2 * b)⁻¹ * cexp (-b * (y : Complex) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert!
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
      (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add, reduceCtorEq]

/--
theorem `integral_gaussian_sq_complex` / 定理 `integral_gaussian_sq_complex`

English:
theorem integral_gaussian_sq_complex
  given: {b : Complex} (hb : 0 < b.re)
  proof: by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : Real, cexp (-b * (x : Complex) ^ 2)) ^ 2 =
        ∫ p : Real × Real, cexp (-b * (p.1 : Complex) ^ 2) * cexp (-b * (p.2 : Complex) ^ 2) := by
      rw [pow_two]; rw [← integral_prod_mul]; rfl
    _ = ∫ p : Real × Real, cexp (-b * ((p.1 : Complex) ^ 2 + (p.2 : Complex) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add]; rw [mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : Real), r * cexp (-b * (r : Complex) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : Complex) ^ 2), ← sin_sq_add_cos_sq (p.2 : Complex)]
      ring
    _ = ↑π / b := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, real_smul, mul_one, integral_mul_cexp_neg_mul_sq hb]
      rw [volume_real_Ioo_of_le (by linarith [pi_nonneg])]
      simp
      ring

中文:
定理 integral_gaussian_sq_complex
  条件: {b : 复形} (hb : 0 < b.re)
  证明: by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : Real, cexp (-b * (x : Complex) ^ 2)) ^ 2 =
        ∫ p : Real × Real, cexp (-b * (p.1 : Complex) ^ 2) * cexp (-b * (p.2 : Complex) ^ 2) := by
      rw [pow_two]; rw [← integral_prod_mul]; rfl
    _ = ∫ p : Real × Real, cexp (-b * ((p.1 : Complex) ^ 2 + (p.2 : Complex) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add]; rw [mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : Real), r * cexp (-b * (r : Complex) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : Complex) ^ 2), ← sin_sq_add_cos_sq (p.2 : Complex)]
      ring
    _ = ↑π / b := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, real_smul, mul_one, integral_mul_cexp_neg_mul_sq hb]
      rw [volume_real_Ioo_of_le (by linarith [pi_nonneg])]
      simp
      ring
-/
theorem integral_gaussian_sq_complex {b : Complex} (hb : 0 < b.re) :
    (∫ x : Real, cexp (-b * (x : Complex) ^ 2)) ^ 2 = π / b := by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : Real, cexp (-b * (x : Complex) ^ 2)) ^ 2 =
        ∫ p : Real × Real, cexp (-b * (p.1 : Complex) ^ 2) * cexp (-b * (p.2 : Complex) ^ 2) := by
      rw [pow_two]; rw [← integral_prod_mul]; rfl
    _ = ∫ p : Real × Real, cexp (-b * ((p.1 : Complex) ^ 2 + (p.2 : Complex) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add]; rw [mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : Real), r * cexp (-b * (r : Complex) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : Complex) ^ 2), ← sin_sq_add_cos_sq (p.2 : Complex)]
      ring
    _ = ↑π / b := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, real_smul, mul_one, integral_mul_cexp_neg_mul_sq hb]
      rw [volume_real_Ioo_of_le (by linarith [pi_nonneg])]
      simp
      ring

/--
theorem `integral_gaussian` / 定理 `integral_gaussian`

English:
theorem integral_gaussian
  given: (b : Real)
  statement: ∫ x : Real, exp (-b * x ^ 2) = √(π / b)
  proof: by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [← ofReal_inj]; rw [ofReal_pow]; rw [← coe_algebraMap]; rw [RCLike.algebraMap_eq_ofReal]; rw [← integral_ofReal]; rw [sq_sqrt (div_pos pi_pos hb).le]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]; rw [ofReal_div]
  convert! integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : Complex).re) with _ x
  rw [ofReal_exp]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_neg]

中文:
定理 integral_gaussian
  条件: (b : 实数)
  结论: ∫ x : 实数, exp (-b * x ^ 2) = √(π / b)
  证明: by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [← ofReal_inj]; rw [ofReal_pow]; rw [← coe_algebraMap]; rw [RCLike.algebraMap_eq_ofReal]; rw [← integral_ofReal]; rw [sq_sqrt (div_pos pi_pos hb).le]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]; rw [ofReal_div]
  convert! integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : Complex).re) with _ x
  rw [ofReal_exp]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_neg]
-/
theorem integral_gaussian (b : Real) : ∫ x : Real, exp (-b * x ^ 2) = √(π / b) := by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [← ofReal_inj]; rw [ofReal_pow]; rw [← coe_algebraMap]; rw [RCLike.algebraMap_eq_ofReal]; rw [← integral_ofReal]; rw [sq_sqrt (div_pos pi_pos hb).le]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]; rw [ofReal_div]
  convert! integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : Complex).re) with _ x
  rw [ofReal_exp]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_neg]

/--
theorem `continuousAt_gaussian_integral` / 定理 `continuousAt_gaussian_integral`

English:
theorem continuousAt_gaussian_integral
  given: (b : Complex) (hb : 0 < re b)
  proof: by
  let f : Complex -> Real -> Complex := fun (c : Complex) (x : Real) => cexp (-c * (x : Complex) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_le_bd : forallᶠ c : Complex in 𝓝 b, forallᵐ x : Real, ‖f c x‖ <= exp (-d * x ^ 2) := by
    refine eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') ?_
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact continuousAt_of_dominated (Eventually.of_forall (by fun_prop)) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ (by fun_prop))

中文:
定理 continuousAt_gaussian_integral
  条件: (b : 复形) (hb : 0 < re b)
  证明: by
  let f : Complex -> Real -> Complex := fun (c : Complex) (x : Real) => cexp (-c * (x : Complex) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_le_bd : forallᶠ c : Complex in 𝓝 b, forallᵐ x : Real, ‖f c x‖ <= exp (-d * x ^ 2) := by
    refine eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') ?_
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact continuousAt_of_dominated (Eventually.of_forall (by fun_prop)) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ (by fun_prop))

Depends on / 依赖: Eventually, Eventually.of_forall, continuousAt_of_dominated, continuous_re, continuous_re.isOpen_preimage, eventually_of_mem, exists_between, f_le_bd, filter_upwards, fun_prop, integrable, isOpen_Ioi, isOpen_preimage, le_of_lt, mem_nhds, norm_cexp_neg_mul_sq, of_forall
-/
theorem continuousAt_gaussian_integral (b : Complex) (hb : 0 < re b) :
    ContinuousAt (fun c : Complex => ∫ x : Real, cexp (-c * (x : Complex) ^ 2)) b := by
  let f : Complex -> Real -> Complex := fun (c : Complex) (x : Real) => cexp (-c * (x : Complex) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_le_bd : forallᶠ c : Complex in 𝓝 b, forallᵐ x : Real, ‖f c x‖ <= exp (-d * x ^ 2) := by
    refine eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') ?_
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact continuousAt_of_dominated (Eventually.of_forall (by fun_prop)) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ (by fun_prop))

/--
theorem `integral_gaussian_complex` / 定理 `integral_gaussian_complex`

English:
theorem integral_gaussian_complex
  given: {b : Complex} (hb : 0 < re b)
  proof: by
  have nv : forall {b : Complex}, 0 < re b -> b != 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfSpace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : Complex)) ?_ hb
  · -- integral is continuous
    exact continuousOn_of_forall_continuousAt continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine
      continuousOn_of_forall_continuousAt fun b hb =>
        (continuousAt_cpow_const (Or.inl ?_)).comp (continuousAt_const.div continuousAt_id (nv hb))
    rw [div_re]; rw [ofReal_im]; rw [ofReal_re]; rw [zero_mul]; rw [zero_div]; rw [add_zero]
    exact div_pos (mul_pos pi_pos hb) (normSq_pos.mpr (nv hb))
  · -- equality at 1
    have : forall x : Real, cexp (-(1 : Complex) * (x : Complex) ^ 2) = exp (-(1 : Real) * x ^ 2) := by
      intro x
      simp only [ofReal_exp, neg_mul, one_mul, ofReal_neg, ofReal_pow]
    simp_rw [this, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, coe_algebraMap]
    conv_rhs =>
      congr
      · rw [← ofReal_one, ← ofReal_div]
      · rw [← ofReal_one, ← ofReal_ofNat, ← ofReal_div]
    rw [← ofReal_cpow]; rw [ofReal_inj]
    · convert! integral_gaussian (1 : Real) using 1
      rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc]; rw [sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))

中文:
定理 integral_gaussian_complex
  条件: {b : 复形} (hb : 0 < re b)
  证明: by
  have nv : forall {b : Complex}, 0 < re b -> b != 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfSpace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : Complex)) ?_ hb
  · -- integral is continuous
    exact continuousOn_of_forall_continuousAt continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine
      continuousOn_of_forall_continuousAt fun b hb =>
        (continuousAt_cpow_const (Or.inl ?_)).comp (continuousAt_const.div continuousAt_id (nv hb))
    rw [div_re]; rw [ofReal_im]; rw [ofReal_re]; rw [zero_mul]; rw [zero_div]; rw [add_zero]
    exact div_pos (mul_pos pi_pos hb) (normSq_pos.mpr (nv hb))
  · -- equality at 1
    have : forall x : Real, cexp (-(1 : Complex) * (x : Complex) ^ 2) = exp (-(1 : Real) * x ^ 2) := by
      intro x
      simp only [ofReal_exp, neg_mul, one_mul, ofReal_neg, ofReal_pow]
    simp_rw [this, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, coe_algebraMap]
    conv_rhs =>
      congr
      · rw [← ofReal_one, ← ofReal_div]
      · rw [← ofReal_one, ← ofReal_ofNat, ← ofReal_div]
    rw [← ofReal_cpow]; rw [ofReal_inj]
    · convert! integral_gaussian (1 : Real) using 1
      rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc]; rw [sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))

Depends on / 依赖: Or.inl, continuous, continuousAt_c, continuousAt_cpow_const, continuousAt_gaussian_integral, continuousOn_of_forall_continuousAt, contrapose, convex_halfSpace_re_gt, eq_of_sq_eq, integral, isPreconnected, isPreconnected.eq_of_sq_eq
-/
theorem integral_gaussian_complex {b : Complex} (hb : 0 < re b) :
    ∫ x : Real, cexp (-b * (x : Complex) ^ 2) = (π / b) ^ (1 / 2 : Complex) := by
  have nv : forall {b : Complex}, 0 < re b -> b != 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfSpace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : Complex)) ?_ hb
  · -- integral is continuous
    exact continuousOn_of_forall_continuousAt continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine
      continuousOn_of_forall_continuousAt fun b hb =>
        (continuousAt_cpow_const (Or.inl ?_)).comp (continuousAt_const.div continuousAt_id (nv hb))
    rw [div_re]; rw [ofReal_im]; rw [ofReal_re]; rw [zero_mul]; rw [zero_div]; rw [add_zero]
    exact div_pos (mul_pos pi_pos hb) (normSq_pos.mpr (nv hb))
  · -- equality at 1
    have : forall x : Real, cexp (-(1 : Complex) * (x : Complex) ^ 2) = exp (-(1 : Real) * x ^ 2) := by
      intro x
      simp only [ofReal_exp, neg_mul, one_mul, ofReal_neg, ofReal_pow]
    simp_rw [this, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, coe_algebraMap]
    conv_rhs =>
      congr
      · rw [← ofReal_one, ← ofReal_div]
      · rw [← ofReal_one, ← ofReal_ofNat, ← ofReal_div]
    rw [← ofReal_cpow]; rw [ofReal_inj]
    · convert! integral_gaussian (1 : Real) using 1
      rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc]; rw [sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne]; rw [cpow_eq_zero_iff]; rw [not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`.
/--
theorem `integral_gaussian_complex_Ioi` / 定理 `integral_gaussian_complex_Ioi`

English:
theorem integral_gaussian_complex_Ioi
  given: {b : Complex} (hb : 0 < re b)
  proof: by
  let f : Real -> Complex := fun x => cexp (-b * (x : Complex) ^ 2)
  have full_integral := integral_gaussian_complex hb
  have h_eq := calc
    ∫ x : Real in Iic 0, f x = ∫ x : Real in Ioi 0, f (-x) := by
      simpa [f] using (integral_comp_neg_Ioi 0 f).symm
    _ = ∫ x : Real in Ioi 0, f x :=
      setIntegral_congr_fun measurableSet_Ioi fun _ _ => (by simp [f])
  rw [← integral_add_compl (s := Ioi 0) (by simp) (integrable_cexp_neg_mul_sq hb)]; rw [compl_Ioi]; rw [h_eq]; rw [← mul_two] at full_integral
  exact (eq_div_iff two_ne_zero).2 (by simpa using full_integral)

中文:
定理 integral_gaussian_complex_Ioi
  条件: {b : 复形} (hb : 0 < re b)
  证明: by
  let f : Real -> Complex := fun x => cexp (-b * (x : Complex) ^ 2)
  have full_integral := integral_gaussian_complex hb
  have h_eq := calc
    ∫ x : Real in Iic 0, f x = ∫ x : Real in Ioi 0, f (-x) := by
      simpa [f] using (integral_comp_neg_Ioi 0 f).symm
    _ = ∫ x : Real in Ioi 0, f x :=
      setIntegral_congr_fun measurableSet_Ioi fun _ _ => (by simp [f])
  rw [← integral_add_compl (s := Ioi 0) (by simp) (integrable_cexp_neg_mul_sq hb)]; rw [compl_Ioi]; rw [h_eq]; rw [← mul_two] at full_integral
  exact (eq_div_iff two_ne_zero).2 (by simpa using full_integral)

Depends on / 依赖: compl_Ioi, eq_div_, full_integral, h_eq, integrable_cexp_neg_mul_sq, integral_add_compl, integral_comp_neg_Ioi, integral_gaussian_complex, measurableSet_Ioi, mul_two, setIntegral_congr_fun
-/
theorem integral_gaussian_complex_Ioi {b : Complex} (hb : 0 < re b) :
    ∫ x : Real in Ioi 0, cexp (-b * (x : Complex) ^ 2) = (π / b) ^ (1 / 2 : Complex) / 2 := by
  let f : Real -> Complex := fun x => cexp (-b * (x : Complex) ^ 2)
  have full_integral := integral_gaussian_complex hb
  have h_eq := calc
    ∫ x : Real in Iic 0, f x = ∫ x : Real in Ioi 0, f (-x) := by
      simpa [f] using (integral_comp_neg_Ioi 0 f).symm
    _ = ∫ x : Real in Ioi 0, f x :=
      setIntegral_congr_fun measurableSet_Ioi fun _ _ => (by simp [f])
  rw [← integral_add_compl (s := Ioi 0) (by simp) (integrable_cexp_neg_mul_sq hb)]; rw [compl_Ioi]; rw [h_eq]; rw [← mul_two] at full_integral
  exact (eq_div_iff two_ne_zero).2 (by simpa using full_integral)

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`.
/--
theorem `integral_gaussian_Ioi` / 定理 `integral_gaussian_Ioi`

English:
theorem integral_gaussian_Ioi
  given: (b : Real)
  proof: by
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := Complex)]; rw [← integral_ofReal]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]
  convert! integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : Complex).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    · simp
    · exact (div_pos pi_pos hb).le

中文:
定理 integral_gaussian_Ioi
  条件: (b : 实数)
  证明: by
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := Complex)]; rw [← integral_ofReal]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]
  convert! integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : Complex).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    · simp
    · exact (div_pos pi_pos hb).le

Depends on / 依赖: IntegrableOn, RCLike, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_inj, algebraMap_eq_ofReal, coe_algebraMap, convert, div_nonpos_of_nonneg_of_nonpos, integrableOn_Ioi_exp_neg_mul_sq_iff, integral_gaussian_complex_Ioi, integral_ofReal, integral_undef, le_or_gt, not_lt, ofReal_cpow, ofReal_div, ofReal_inj, ofReal_re, pi_pos, pi_pos.le
-/
theorem integral_gaussian_Ioi (b : Real) :
    ∫ x in Ioi (0 : Real), exp (-b * x ^ 2) = √(π / b) / 2 := by
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := Complex)]; rw [← integral_ofReal]; rw [← RCLike.algebraMap_eq_ofReal]; rw [coe_algebraMap]
  convert! integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : Complex).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    · simp
    · exact (div_pos pi_pos hb).le

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `Real.Gamma_one_half_eq` / 定理 `Real.Gamma_one_half_eq`

English:
theorem Real.Gamma_one_half_eq
  statement: Real.Gamma (1 / 2) = √π
  proof: by
  rw [Gamma_eq_integral one_half_pos]; rw [← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert! congr_arg (fun x : Real => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have : (x ^ (2 : Real)) ^ (1 / (2 : Real) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx)]; rw [rpow_one]
    rw [smul_eq_mul]; rw [this]
    simp [field, (ne_of_lt (show 0 < x from hx)).symm]
    norm_num
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' Real)]

中文:
定理 实数.Gamma_one_half_eq
  结论: 实数.Gamma (1 / 2) = √π
  证明: by
  rw [Gamma_eq_integral one_half_pos]; rw [← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert! congr_arg (fun x : Real => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have : (x ^ (2 : Real)) ^ (1 / (2 : Real) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx)]; rw [rpow_one]
    rw [smul_eq_mul]; rw [this]
    simp [field, (ne_of_lt (show 0 < x from hx)).symm]
    norm_num
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' Real)]

Depends on / 依赖: Gamma_eq_integral, congr_arg, convert, div_one, integral_comp_rpow_Ioi_of_pos, integral_const_mul, integral_gaussian_Ioi, le_of_lt, measurableSet_Ioi, ne_of_lt, one_half_pos, rpow_mul, rpow_neg, rpow_one, setIntegral_congr_fun, smul_eq_mul, zero_lt_two
-/
theorem Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π := by
  rw [Gamma_eq_integral one_half_pos]; rw [← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert! congr_arg (fun x : Real => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have : (x ^ (2 : Real)) ^ (1 / (2 : Real) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx)]; rw [rpow_one]
    rw [smul_eq_mul]; rw [this]
    simp [field, (ne_of_lt (show 0 < x from hx)).symm]
    norm_num
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' Real)]

/--
theorem `Complex.Gamma_one_half_eq` / 定理 `Complex.Gamma_one_half_eq`

English:
theorem Complex.Gamma_one_half_eq
  statement: Complex.Gamma (1 / 2) = (π : Complex) ^ (1 / 2 : Complex)
  proof: by
  convert! congr_arg ((↑) : Real -> Complex) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]

中文:
定理 复形.Gamma_one_half_eq
  结论: 复形.Gamma (1 / 2) = (π : 复形) ^ (1 / 2 : 复形)
  证明: by
  convert! congr_arg ((↑) : Real -> Complex) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]

Depends on / 依赖: Gamma_ofReal, Gamma_one_half_eq, Real.Gamma_one_half_eq, congr_arg, convert, ofReal_cpow, ofReal_div, ofReal_inv, ofReal_ofNat, ofReal_one, one_div, pi_pos, pi_pos.le, sqrt_eq_rpow
-/
theorem Complex.Gamma_one_half_eq : Complex.Gamma (1 / 2) = (π : Complex) ^ (1 / 2 : Complex) := by
  convert! congr_arg ((↑) : Real -> Complex) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]

open scoped Nat in
/--
lemma `Real.Gamma_nat_add_one_add_half` / 引理 `Real.Gamma_nat_add_one_add_half`

English:
lemma Real.Gamma_nat_add_one_add_half
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simp [-one_div, add_comm (1 : Real), Gamma_add_one, Gamma_one_half_eq]; ring
  | succ k ih =>
    rw [add_right_comm]; rw [Gamma_add_one (by positivity)]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [ih]; rw [Nat.mul_add]
    simp
    ring

中文:
引理 实数.Gamma_nat_add_one_add_half
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simp [-one_div, add_comm (1 : Real), Gamma_add_one, Gamma_one_half_eq]; ring
  | succ k ih =>
    rw [add_right_comm]; rw [Gamma_add_one (by positivity)]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [ih]; rw [Nat.mul_add]
    simp
    ring

Depends on / 依赖: Gamma_add_one, Gamma_one_half_eq, Nat.cast_add, Nat.cast_one, Nat.mul_add, add_comm, add_right_comm, cast_add, cast_one, mul_add, one_div
-/
lemma Real.Gamma_nat_add_one_add_half (k : Nat) :
    Gamma (k + 1 + 1 / 2) = (2 * k + 1 : Nat)‼ * √π / (2 ^ (k + 1)) := by
  induction k with
  | zero => simp [-one_div, add_comm (1 : Real), Gamma_add_one, Gamma_one_half_eq]; ring
  | succ k ih =>
    rw [add_right_comm]; rw [Gamma_add_one (by positivity)]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [ih]; rw [Nat.mul_add]
    simp
    ring

open scoped Nat in
/--
lemma `Real.Gamma_nat_add_half` / 引理 `Real.Gamma_nat_add_half`

English:
lemma Real.Gamma_nat_add_half
  given: (k : Nat)
  proof: by
  cases k with
  | zero => simp [-one_div, Gamma_one_half_eq]
  | succ k => simpa [-one_div, mul_add] using Gamma_nat_add_one_add_half k

中文:
引理 实数.Gamma_nat_add_half
  条件: (k : 自然数)
  证明: by
  cases k with
  | zero => simp [-one_div, Gamma_one_half_eq]
  | succ k => simpa [-one_div, mul_add] using Gamma_nat_add_one_add_half k

Depends on / 依赖: Gamma_nat_add_one_add_half, Gamma_one_half_eq, mul_add, one_div
-/
lemma Real.Gamma_nat_add_half (k : Nat) :
    Gamma (k + 1 / 2) = (2 * k - 1 : Nat)‼ * √π / (2 ^ k) := by
  cases k with
  | zero => simp [-one_div, Gamma_one_half_eq]
  | succ k => simpa [-one_div, mul_add] using Gamma_nat_add_one_add_half k
