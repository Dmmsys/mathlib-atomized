/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier inversion formula

In a finite-dimensional real inner product space, we show the Fourier inversion formula, i.e.,
`𝓕⁻ (𝓕 f) v = f v` if `f` and `𝓕 f` are integrable, and `f` is continuous at `v`. This is proved
in `MeasureTheory.Integrable.fourier_inversion`. See also `Continuous.fourier_inversion`
giving `𝓕⁻ (𝓕 f) = f` under an additional continuity assumption for `f`.

We use the following proof. A naïve computation gives
`𝓕⁻ (𝓕 f) v
= ∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw
= ∫_w exp (2 I π ⟪w, v⟫) ∫_x, exp (-2 I π ⟪w, x⟫) f x dx) dw
= ∫_x (∫_ w, exp (2 I π ⟪w, v - x⟫ dw) f x dx `

However, the Fubini step does not make sense for lack of integrability, and the middle integral
`∫_ w, exp (2 I π ⟪w, v - x⟫ dw` (which one would like to be a Dirac at `v - x`) is not defined.
To gain integrability, one multiplies with a Gaussian function `exp (-c⁻¹ ‖w‖^2)`, with a large
(but finite) `c`. As this function converges pointwise to `1` when `c → ∞`, we get
`∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw = lim_c ∫_w exp (-c⁻¹ ‖w‖^2 + 2 I π ⟪w, v⟫) 𝓕 f (w) dw`.
One can perform Fubini on the right-hand side for fixed `c`, writing the integral as
`∫_x (∫_w exp (-c⁻¹‖w‖^2 + 2 I π ⟪w, v - x⟫ dw)) f x dx`.
The middle factor is the Fourier transform of a more and more flat function
(converging to the constant `1`), hence it becomes more and more concentrated, around the
point `v`. (Morally, it converges to the Dirac at `v`). Moreover, it has integral one.
Therefore, multiplying by `f` and integrating, one gets a term converging to `f v` as `c → ∞`.
Since it also converges to `𝓕⁻ (𝓕 f) v`, this proves the result.

To check the concentration property of the middle factor and the fact that it has integral one, we
rely on the explicit computation of the Fourier transform of Gaussians.
-/

public section

open Filter MeasureTheory Complex Module Metric Real Bornology

open scoped Topology FourierTransform RealInnerProductSpace Complex

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
  [NormedAddCommGroup E] [NormedSpace Complex E] {f : V -> E}

namespace Real

/--
lemma `tendsto_integral_cexp_sq_smul` / 引理 `tendsto_integral_cexp_sq_smul`

English:
lemma tendsto_integral_cexp_sq_smul
  given: (hf : Integrable f)
  proof: by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    nth_rewrite 2 [show f v = cexp (- (0 : Real) * ‖v‖ ^ 2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
  · filter_upwards with c using

中文:
引理 tendsto_integral_cexp_sq_smul
  条件: (hf : 可积 f)
  证明: by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    nth_rewrite 2 [show f v = cexp (- (0 : Real) * ‖v‖ ^ 2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
  · filter_upwards with c using

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.smul, Continuous, Continuous.aestronglyMeasurable, Ici_mem_atTop, Tendsto, Tendsto.cexp, aestronglyMeasurable, filter_upwards, fun_prop, hf.norm, mul_const, neg_mul, norm_cas, norm_smul, nth_rewrite, ofReal, ofReal_inv, smul_const, tendsto_integral_filter_of_dominated_convergence
-/
lemma tendsto_integral_cexp_sq_smul (hf : Integrable f) :
    Tendsto (fun (c : Real) => (∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) • f v))
      atTop (𝓝 (∫ v : V, f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    nth_rewrite 2 [show f v = cexp (- (0 : Real) * ‖v‖ ^ 2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
  · filter_upwards with c using
      AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop)) hf.1
  · filter_upwards [Ici_mem_atTop (0 : Real)] with c (hc : 0 <= c)
    filter_upwards with v
    simp only [ofReal_inv, neg_mul, norm_smul]
    norm_cast
    conv_rhs => rw [← one_mul (‖f v‖)]
    gcongr
    simp only [norm_eq_abs, abs_exp, exp_le_one_iff, Left.neg_nonpos_iff]
    positivity

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tendsto_integral_gaussian_smul` / 引理 `tendsto_integral_gaussian_smul`

English:
lemma tendsto_integral_gaussian_smul
  given: (hf : Integrable f) (h'f : Integrable (𝓕 f)) (v : V)
  proof: by
  have A : Tendsto (fun (c : Real) => (∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)
       • (𝓕 f) w)) atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w => 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa

中文:
引理 tendsto_integral_gaussian_smul
  条件: (hf : 可积 f) (h'f : 可积 (𝓕 f)) (v : V)
  证明: by
  have A : Tendsto (fun (c : Real) => (∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)
       • (𝓕 f) w)) atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w => 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa

Depends on / 依赖: Continuous, Integrable, Real.continuous_fourierChar, Real.fourierChar_apply, Submonoid, Submonoid.smul_def, Tendsto, VectorFourier, VectorFourier.fourierIntegral_convergent_iff, continuous_fourierChar, continuous_inner, continuous_inner.neg, convert, fourierChar_apply, fourierIntegral_convergent_iff, smul_def, smul_smul, tendsto_integral_cexp_sq_smul
-/
lemma tendsto_integral_gaussian_smul (hf : Integrable f) (h'f : Integrable (𝓕 f)) (v : V) :
    Tendsto (fun (c : Real) =>
      ∫ w : V, ((π * c) ^ (finrank Real V / 2 : Complex) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
  have A : Tendsto (fun (c : Real) => (∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)
       • (𝓕 f) w)) atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w => 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa using!
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar B v).2 h'f
    convert! tendsto_integral_cexp_sq_smul this using 4 with c w
    · rw [Submonoid.smul_def, Real.fourierChar_apply, smul_smul, ← Complex.exp_add, real_inner_comm]
      congr 3
      simp only [ofReal_mul, ofReal_ofNat]
      ring
    · simp [fourierInv_eq]
  have B : Tendsto (fun (c : Real) => (∫ w : V,
        𝓕 (fun w => cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) w • f w)) atTop
      (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    apply A.congr'
    filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    have J : Integrable (fun w => cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [fourier_gaussian_innerProductSpace' (by simpa)]
  congr
  · simp
  · simp; ring

/--
lemma `tendsto_integral_gaussian_smul'` / 引理 `tendsto_integral_gaussian_smul'`

English:
lemma tendsto_integral_gaussian_smul'
  given: (hf : Integrable f) {v : V} (h'f : ContinuousAt f v)
  proof: by
  let φ : V -> Real := fun w => π ^ (finrank Real V / 2 : Real) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : Real) => ∫ w : V, (c ^ finrank Real V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x => by p

中文:
引理 tendsto_integral_gaussian_smul'
  条件: (hf : 可积 f) {v : V} (h'f : ContinuousAt f v)
  证明: by
  let φ : V -> Real := fun w => π ^ (finrank Real V / 2 : Real) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : Real) => ∫ w : V, (c ^ finrank Real V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x => by p

Depends on / 依赖: GaussianFourier, GaussianFourier.integral_rexp_neg_mul_sq_norm, Real.exp, Tendsto, finrank, integral_const_mul, integral_rexp_neg_mul_sq_norm, nth_rewrite, pi_nonneg, pi_pos, pow_one, rpow_mul, rpow_natCast, rpow_sub, tendsto_integral_comp_smul_smul_of_integrable
-/
lemma tendsto_integral_gaussian_smul' (hf : Integrable f) {v : V} (h'f : ContinuousAt f v) :
    Tendsto (fun (c : Real) =>
      ∫ w : V, ((π * c : Complex) ^ (finrank Real V / 2 : Complex) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (f v)) := by
  let φ : V -> Real := fun w => π ^ (finrank Real V / 2 : Real) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : Real) => ∫ w : V, (c ^ finrank Real V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x => by positivity
    · rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
      nth_rewrite 2 [← pow_one π]
      rw [← rpow_natCast]; rw [← rpow_natCast]; rw [← rpow_sub pi_pos]; rw [← rpow_mul pi_nonneg]; rw [← rpow_add pi_pos]
      ring_nf
      exact rpow_zero _
    · have A : Tendsto (fun (w : V) => π ^ 2 * ‖w‖ ^ 2) (cobounded V) atTop := by
        rw [tendsto_const_mul_atTop_of_pos (by positivity)]
        apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
      have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank Real V / 2) 1
.const_mul (π ^ (-finrank Real V / 2 : Real)) .comp A zero_lt_one
      rw [mul_zero] at B
      convert! B using 2 with x
      simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← rpow_natCast, φ]
      congr 1
      rw [mul_rpow (by positivity) (by positivity)]; rw [← rpow_mul pi_nonneg]; rw [← rpow_mul (norm_nonneg _)]; rw [← mul_assoc]; rw [← rpow_add pi_pos]; rw [mul_comm]
      congr <;> ring
    · exact hf
    · exact h'f
  have B : Tendsto
      (fun (c : Real) =>
        ∫ w : V, ((c ^ (1 / 2 : Real)) ^ finrank Real V * φ ((c ^ (1 / 2 : Real)) • (v - w))) • f w)
      atTop (𝓝 (f v)) :=
    A.comp (tendsto_rpow_atTop (by simp))
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [← coe_smul]
  congr
  rw [ofReal_mul]; rw [ofReal_mul]; rw [ofReal_exp]; rw [← mul_assoc]
  congr
  · rw [mul_cpow_ofReal_nonneg pi_nonneg hc.le, ← rpow_natCast, ← rpow_mul hc.le, mul_comm,
      ofReal_cpow pi_nonneg, ofReal_cpow hc.le]
    simp [div_eq_inv_mul]
  · norm_cast
    simp only [one_div, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, neg_inj,
      ← rpow_natCast, ← rpow_mul hc.le, mul_assoc]
    simp

end Real

variable [CompleteSpace E]

/--
theorem `MeasureTheory.Integrable.fourierInv_fourier_eq` / 定理 `MeasureTheory.Integrable.fourierInv_fourier_eq`

English:
theorem MeasureTheory.Integrable.fourierInv_fourier_eq
  proof: tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

中文:
定理 测度论.可积.fourierInv_fourier_eq
  证明: tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

Depends on / 依赖: Real.tendsto_integral_gaussian_smul, tendsto_integral_gaussian_smul, tendsto_nhds_unique
-/
theorem MeasureTheory.Integrable.fourierInv_fourier_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v :=
  tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

/--
theorem `Continuous.fourierInv_fourier_eq` / 定理 `Continuous.fourierInv_fourier_eq`

English:
theorem Continuous.fourierInv_fourier_eq
  statement: (h : Continuous f)
  proof: by
  ext v
  exact hf.fourierInv_fourier_eq h'f h.continuousAt

中文:
定理 连续.fourierInv_fourier_eq
  结论: (h : 连续 f)
  证明: by
  ext v
  exact hf.fourierInv_fourier_eq h'f h.continuousAt

Depends on / 依赖: continuousAt, fourierInv_fourier_eq, h.continuousAt, hf.fourierInv_fourier_eq
-/
theorem Continuous.fourierInv_fourier_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := by
  ext v
  exact hf.fourierInv_fourier_eq h'f h.continuousAt

/--
theorem `MeasureTheory.Integrable.fourier_fourierInv_eq` / 定理 `MeasureTheory.Integrable.fourier_fourierInv_eq`

English:
theorem MeasureTheory.Integrable.fourier_fourierInv_eq
  proof: by
  rw [fourierInv_comm]
  exact hf.fourierInv_fourier_eq h'f hv

中文:
定理 测度论.可积.fourier_fourierInv_eq
  证明: by
  rw [fourierInv_comm]
  exact hf.fourierInv_fourier_eq h'f hv

Depends on / 依赖: fourierInv_comm, fourierInv_fourier_eq, hf.fourierInv_fourier_eq
-/
theorem MeasureTheory.Integrable.fourier_fourierInv_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v := by
  rw [fourierInv_comm]
  exact hf.fourierInv_fourier_eq h'f hv

/--
theorem `Continuous.fourier_fourierInv_eq` / 定理 `Continuous.fourier_fourierInv_eq`

English:
theorem Continuous.fourier_fourierInv_eq
  statement: (h : Continuous f)
  proof: by
  ext v
  exact hf.fourier_fourierInv_eq h'f h.continuousAt

中文:
定理 连续.fourier_fourierInv_eq
  结论: (h : 连续 f)
  证明: by
  ext v
  exact hf.fourier_fourierInv_eq h'f h.continuousAt

Depends on / 依赖: continuousAt, fourier_fourierInv_eq, h.continuousAt, hf.fourier_fourierInv_eq
-/
theorem Continuous.fourier_fourierInv_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕 (𝓕⁻ f) = f := by
  ext v
  exact hf.fourier_fourierInv_eq h'f h.continuousAt
