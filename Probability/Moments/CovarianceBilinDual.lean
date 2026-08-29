/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a Banach space `E`,
as a continuous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` (for `RCLike 𝕜`)
  into the space `Lp 𝕜 p μ` for `p ≥ 1`. This needs a hypothesis `MemLp id p μ` (we set it to the
  junk value 0 if that's not the case).
* `covarianceBilinDual` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a Banach space,
  as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
  If the second moment of `μ` is not finite, we set `covarianceBilinDual μ = 0`.

## Main statements

* `covarianceBilinDual_apply` : the covariance of `μ` on `L₁, L₂ : Dual ℝ E` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.
* `covarianceBilinDual_same_eq_variance`: `covarianceBilinDual μ L L = Var[L; μ]`.

## Implementation notes

The hypothesis that `μ` has a second moment is written as `MemLp id 2 μ` in the code.

-/

@[expose] public section


open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : Real>=0∞}

namespace StrongDual

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

open scoped Classical in
/-- Linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ` and to 0 otherwise. -/
noncomputable
/--
Definition of `toLpₗ` / `toLpₗ` 的定义

English:
definition toLpₗ
  signature: (μ : Measure E) (p : Real>=0∞)
  body: if h_Lp : MemLp id p μ then
  { toFun := fun L => MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]

中文:
定义 toLpₗ
  签名: (μ : Measure E) (p : 实数>=0∞)
  定义体: if h_Lp : MemLp id p μ then
  { toFun := fun L => MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]

Depends on / 依赖: MemLp.toLp, MemLp.toLp_add, MemLp.toLp_const_smul, continuousLinearMap_comp, h_Lp, h_Lp.continuousLinearMap_comp, map_add, map_smul, toLp_add, toLp_const_smul
-/
def toLpₗ (μ : Measure E) (p : Real>=0∞) :
    StrongDual 𝕜 E ->ₗ[𝕜] Lp 𝕜 p μ :=
  if h_Lp : MemLp id p μ then
  { toFun := fun L => MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]
/--
lemma `toLpₗ_apply` / 引理 `toLpₗ_apply`

English:
lemma toLpₗ_apply
  given: (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E)
  proof: by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]

中文:
引理 toLpₗ_apply
  条件: (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E)
  证明: by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]

Depends on / 依赖: dif_pos, h_Lp
-/
lemma toLpₗ_apply (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]
/--
lemma `toLpₗ_of_not_memLp` / 引理 `toLpₗ_of_not_memLp`

English:
lemma toLpₗ_of_not_memLp
  given: (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E)
  proof: by
  simp [toLpₗ, dif_neg h_Lp]

中文:
引理 toLpₗ_of_not_memLp
  条件: (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E)
  证明: by
  simp [toLpₗ, dif_neg h_Lp]

Depends on / 依赖: dif_neg, h_Lp
-/
lemma toLpₗ_of_not_memLp (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = 0 := by
  simp [toLpₗ, dif_neg h_Lp]

/--
lemma `norm_toLpₗ_le` / 引理 `norm_toLpₗ_le`

English:
lemma norm_toLpₗ_le
  given: [OpensMeasurableSpace E] (L : StrongDual 𝕜 E)
  proof: by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, StrongDual.toLpₗ_apply h_Lp, Lp.norm_

中文:
引理 norm_toLpₗ_le
  条件: [OpensMeasurableSpace E] (L : StrongDual 𝕜 E)
  证明: by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, StrongDual.toLpₗ_apply h_Lp, Lp.norm_

Depends on / 依赖: ENNReal, ENNReal.essSup_const_mul, ENNReal.toReal_mul, Lp.norm_toLp, Lp.norm_zero, StrongDual, StrongDual.toLp, eLpNormEssSup, eLpNorm_exponent_top, essSup, essSup_const_mul, h_Lp, hp_top, id_eq, norm_toLp, norm_zero, not_false_eq_true, toReal, toReal_e, toReal_mul
-/
lemma norm_toLpₗ_le [OpensMeasurableSpace E] (L : StrongDual 𝕜 E) :
    ‖L.toLpₗ μ p‖ <= ‖L‖ * (eLpNorm id p μ).toReal := by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, StrongDual.toLpₗ_apply h_Lp, Lp.norm_toLp, eLpNorm_exponent_top] at h_Lp ⊢
    simp only [eLpNormEssSup, id_eq]
    suffices (essSup (fun x => ‖L x‖ₑ) μ).toReal <= (essSup (fun x => ‖L‖ₑ * ‖x‖ₑ) μ).toReal by
      rwa [ENNReal.essSup_const_mul, ENNReal.toReal_mul, toReal_enorm] at this
    gcongr
    · rw [ENNReal.essSup_const_mul]
      exact ENNReal.mul_ne_top (by simp) h_Lp.eLpNorm_ne_top
· exact essSup_mono_ae ae_of_all _ L.le_opENorm
  have h0 : 0 < p.toReal := by simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, hp, Ne.lt_top hp_top]
  suffices ‖L.toLpₗ μ p‖
      <= (‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ).toReal ^ p.toReal⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow]; rw [Real.mul_rpow (by positivity) (by positivity)]; rw [← Real.rpow_mul (by positivity)]; rw [mul_inv_cancel₀ h0.ne']; rw [Real.rpow_one]; rw [toReal_enorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [StrongDual.toLpₗ_apply h_Lp]; rw [Lp.norm_toLp]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top]
  simp only [one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ <= ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := h_Lp.eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top] at h
    simpa [h0] using h
  calc ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ
  _ <= ∫⁻ x, ‖L‖ₑ ^ p.toReal * ‖x‖ₑ ^ p.toReal ∂μ := by
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.mul_rpow_of_nonneg]
    swap; · positivity
    gcongr
    exact L.le_opENorm x
  _ = ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_const_mul]; fun_prop

end LinearMap

section ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [OpensMeasurableSpace E]

/-- Continuous linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ`
and to 0 otherwise. -/
noncomputable
/--
Definition of `toLp` / `toLp` 的定义

English:
definition toLp
  signature: (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)]
  body: StrongDual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs => ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs => ?_⟩
    specialize hxr L hLs
    refine (Stron

中文:
定义 toLp
  签名: (μ : Measure E) (p : 实数>=0∞) [Fact (1 <= p)]
  定义体: StrongDual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs => ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs => ?_⟩
    specialize hxr L hLs
    refine (Stron

Depends on / 依赖: StrongDual, StrongDual.toLp
-/
def toLp (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)] :
    StrongDual 𝕜 E ->L[𝕜] Lp 𝕜 p μ where
  toLinearMap := StrongDual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs => ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs => ?_⟩
    specialize hxr L hLs
    refine (StrongDual.norm_toLpₗ_le L).trans ?_
    gcongr

@[simp]
/--
lemma `toLp_apply` / 引理 `toLp_apply`

English:
lemma toLp_apply
  given: [Fact (1 <= p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E)
  proof: by
  simp [toLp, h_Lp]

@[simp]

中文:
引理 toLp_apply
  条件: [Fact (1 <= p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E)
  证明: by
  simp [toLp, h_Lp]

@[simp]

Depends on / 依赖: h_Lp
-/
lemma toLp_apply [Fact (1 <= p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLp, h_Lp]

@[simp]
/--
lemma `toLp_of_not_memLp` / 引理 `toLp_of_not_memLp`

English:
lemma toLp_of_not_memLp
  given: [Fact (1 <= p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E)
  proof: by
  simp [toLp, h_Lp]

中文:
引理 toLp_of_not_memLp
  条件: [Fact (1 <= p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E)
  证明: by
  simp [toLp, h_Lp]

Depends on / 依赖: h_Lp
-/
lemma toLp_of_not_memLp [Fact (1 <= p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = 0 := by
  simp [toLp, h_Lp]

end ContinuousLinearMap

end StrongDual

namespace ProbabilityTheory

section Centered

variable [NormedSpace Real E] [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is equal to the covariance only if `μ` is centered. -/
noncomputable
/--
Definition of `uncenteredCovarianceBilinDual` / `uncenteredCovarianceBilinDual` 的定义

English:
definition uncenteredCovarianceBilinDual
  signature: (μ : Measure E)
  body: ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := Real)).toContinuousLinearMap
    (StrongDual.toLp μ 2) (StrongDual.toLp μ 2)

中文:
定义 uncenteredCovarianceBilinDual
  签名: (μ : Measure E)
  定义体: ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := Real)).toContinuousLinearMap
    (StrongDual.toLp μ 2) (StrongDual.toLp μ 2)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bilinearComp, StrongDual, StrongDual.toLp, bilinearComp, isBoundedBilinearMap_inner, toContinuousLinearMap
-/
def uncenteredCovarianceBilinDual (μ : Measure E) : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := Real)).toContinuousLinearMap
    (StrongDual.toLp μ 2) (StrongDual.toLp μ 2)

/--
lemma `uncenteredCovarianceBilinDual_apply` / 引理 `uncenteredCovarianceBilinDual_apply`

English:
lemma uncenteredCovarianceBilinDual_apply
  given: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  simp only [uncenteredCovarianceBilinDual, ContinuousLinearMap.bilinearComp_apply,
    StrongDual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLine

中文:
引理 uncenteredCovarianceBilinDual_apply
  条件: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  simp only [uncenteredCovarianceBilinDual, ContinuousLinearMap.bilinearComp_apply,
    StrongDual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLine

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bilinearComp_apply, L2.inner_def, MemLp.coeFn_toLp, RCLike, RCLike.inner_apply, StrongDual, StrongDual.toLp_apply, bilinearComp_apply, coeFn_toLp, conj_trivial, continuousLinearMap_comp, filter_upwards, h.continuousLinearMap_comp, id_eq, inner_apply, inner_def, integral_congr_ae, mul_comm, toLp_apply
-/
lemma uncenteredCovarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [uncenteredCovarianceBilinDual, ContinuousLinearMap.bilinearComp_apply,
    StrongDual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap_comp L₂)] with x hxL₁ hxL₂
  simp only [id_eq] at hxL₁ hxL₂
  rw [hxL₁]; rw [hxL₂]; rw [mul_comm]

/--
lemma `uncenteredCovarianceBilinDual_of_not_memLp` / 引理 `uncenteredCovarianceBilinDual_of_not_memLp`

English:
lemma uncenteredCovarianceBilinDual_of_not_memLp
  given: (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  simp [uncenteredCovarianceBilinDual, StrongDual.toLp_of_not_memLp h]

@[simp]

中文:
引理 uncenteredCovarianceBilinDual_of_not_memLp
  条件: (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  simp [uncenteredCovarianceBilinDual, StrongDual.toLp_of_not_memLp h]

@[simp]

Depends on / 依赖: StrongDual, StrongDual.toLp_of_not_memLp, toLp_of_not_memLp, uncenteredCovarianceBilinDual
-/
lemma uncenteredCovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = 0 := by
  simp [uncenteredCovarianceBilinDual, StrongDual.toLp_of_not_memLp h]

@[simp]
/--
lemma `uncenteredCovarianceBilinDual_zero` / 引理 `uncenteredCovarianceBilinDual_zero`

English:
lemma uncenteredCovarianceBilinDual_zero
  statement: uncenteredCovarianceBilinDual (0 : Measure E) = 0
  proof: by
  ext
  have : Subsingleton (Lp Real 2 (0 : Measure E)) := ⟨fun x y => Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilinDual, Subsingleton.eq_zero (StrongDual.toLp 0 2)]

中文:
引理 uncenteredCovarianceBilinDual_zero
  结论: uncenteredCovarianceBilinDual (0 : Measure E) = 0
  证明: by
  ext
  have : Subsingleton (Lp Real 2 (0 : Measure E)) := ⟨fun x y => Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilinDual, Subsingleton.eq_zero (StrongDual.toLp 0 2)]

Depends on / 依赖: Lp.ext_iff, Measure, StrongDual, StrongDual.toLp, Subsingleton, Subsingleton.eq_zero, eq_zero, ext_iff, uncenteredCovarianceBilinDual
-/
lemma uncenteredCovarianceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Measure E) = 0 := by
  ext
  have : Subsingleton (Lp Real 2 (0 : Measure E)) := ⟨fun x y => Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilinDual, Subsingleton.eq_zero (StrongDual.toLp 0 2)]

/--
lemma `norm_uncenteredCovarianceBilinDual_le` / 引理 `norm_uncenteredCovarianceBilinDual_le`

English:
lemma norm_uncenteredCovarianceBilinDual_le
  given: (L₁ L₂ : StrongDual Real E)
  proof: by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilinDual_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilinDual μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilinDual_apply h]
  _ <= ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_int

中文:
引理 norm_uncenteredCovarianceBilinDual_le
  条件: (L₁ L₂ : StrongDual 实数 E)
  证明: by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilinDual_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilinDual μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilinDual_apply h]
  _ <= ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_int

Depends on / 依赖: MemLp.integrable_mul, ae_of_all, continuousLinearMap_comp, h.continuousLinearMap_comp, integrable_mul, integral_mono_ae, norm_integral_le_integral_norm, norm_mul, norm_zero, simp_rw, uncenteredCovarianceBilinDual, uncenteredCovarianceBilinDual_apply, uncenteredCovarianceBilinDual_of_not_memLp
-/
lemma norm_uncenteredCovarianceBilinDual_le (L₁ L₂ : StrongDual Real E) :
    ‖uncenteredCovarianceBilinDual μ L₁ L₂‖ <= ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilinDual_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilinDual μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilinDual_apply h]
  _ <= ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_integral_norm _).trans (by simp)
  _ <= ∫ x, ‖L₁‖ * ‖x‖ * ‖L₂‖ * ‖x‖ ∂μ := by
    refine integral_mono_ae ?_ ?_ (ae_of_all _ fun x => ?_)
    · simp_rw [← norm_mul]
      exact (MemLp.integrable_mul (h.continuousLinearMap_comp L₁)
        (h.continuousLinearMap_comp L₂)).norm
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc, mul_comm _ (‖L₂‖), mul_assoc, ← pow_two]
      refine Integrable.const_mul ?_ _
      exact h.integrable_norm_pow (by simp)
    · simp only
      rw [mul_assoc]
      gcongr
      · exact ContinuousLinearMap.le_opNorm L₁ x
      · exact ContinuousLinearMap.le_opNorm L₂ x
  _ = ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    congr with x
    ring

end Centered

section Covariance

variable [NormedSpace Real E] [BorelSpace E]

/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`
if `MemLp id 2 μ`. If not, we set it to zero. -/
noncomputable
/--
Definition of `covarianceBilinDual` / `covarianceBilinDual` 的定义

English:
definition covarianceBilinDual
  signature: (μ : Measure E)
  body: uncenteredCovarianceBilinDual (μ.map (fun x => x - ∫ x, x ∂μ))

omit [BorelSpace E] in

中文:
定义 covarianceBilinDual
  签名: (μ : Measure E)
  定义体: uncenteredCovarianceBilinDual (μ.map (fun x => x - ∫ x, x ∂μ))

omit [BorelSpace E] in

Depends on / 依赖: uncenteredCovarianceBilinDual
-/
def covarianceBilinDual (μ : Measure E) : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real :=
  uncenteredCovarianceBilinDual (μ.map (fun x => x - ∫ x, x ∂μ))

omit [BorelSpace E] in
/--
lemma `_root_.MeasureTheory.memLp_id_of_self_sub_integral` / 引理 `_root_.MeasureTheory.memLp_id_of_self_sub_integral`

English:
lemma _root_.MeasureTheory.memLp_id_of_self_sub_integral
  statement: {p : Real>=0∞}
  proof: by
  have : (id : E -> E) = fun x => x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  apply h_Lp.add
  set c := ∫ x, x ∂μ
  /- We need to check that the constant `c = ∫ x, x ∂μ` is in `L^p`. Note that we don't assume
  that `μ` is finite, so this requires an argument. If the constant is zero,

中文:
引理 _root_.MeasureTheory.memLp_id_of_self_sub_integral
  结论: {p : 实数>=0∞}
  证明: by
  have : (id : E -> E) = fun x => x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  apply h_Lp.add
  set c := ∫ x, x ∂μ
  /- We need to check that the constant `c = ∫ x, x ∂μ` is in `L^p`. Note that we don't assume
  that `μ` is finite, so this requires an argument. If the constant is zero,

Depends on / 依赖: h_Lp, h_Lp.add
-/
lemma _root_.MeasureTheory.memLp_id_of_self_sub_integral {p : Real>=0∞}
    (h_Lp : MemLp (fun x => x - ∫ y, y ∂μ) p μ) : MemLp id p μ := by
  have : (id : E -> E) = fun x => x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  apply h_Lp.add
  set c := ∫ x, x ∂μ
  /- We need to check that the constant `c = ∫ x, x ∂μ` is in `L^p`. Note that we don't assume
  that `μ` is finite, so this requires an argument. If the constant is zero, it's obvious.
  If it's nonzero, this means that `x` is integrable for `μ` (as otherwise the integral would be
  `0` by our choice of junk value), so `‖x‖ ^ (1/p)` is in `L^p`.
  The constant `c` is controlled by `2 ‖x - c‖` close to `0` (say when `‖x‖ ≤ ‖c‖ / 2`)
  and by a multiple of `‖x‖ ^ (1/p)` away from `0`. Those two functions
  are in `L^p` by assumptions, so the constant `c` also is. -/
  by_cases hx : c = 0
  · simp [hx]
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [aestronglyMeasurable_const]
  rcases eq_or_ne p ∞ with rfl | hptop
  · exact memLp_top_const c
  apply (integrable_norm_rpow_iff (by fun_prop) hp0 hptop).1
  have I : Integrable (fun (x : E) => ‖x‖) μ := by
    apply Integrable.norm
    contrapose hx
    exact integral_undef hx
  have := (h_Lp.integrable_norm_rpow hp0 hptop).const_mul (2 ^ p.toReal)
  apply (((I.const_mul (2 * ‖c‖ ^ (p.toReal - 1))).add this)).mono' (by fun_prop)
  filter_upwards [] with y
  lift p to Real>=0 using hptop
  simp only [ENNReal.coe_toReal, Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by positivity)]
  rcases le_total ‖y‖ (‖c‖ / 2)
  · have : ‖c‖ <= ‖y‖ + ‖y - c‖ := Eq.trans_le (by abel_nf) (norm_sub_le y (y - c))
    calc ‖c‖ ^ (p : Real)
    _ <= (2 * ‖y - c‖) ^ (p : Real) := by
      gcongr
      linarith
    _ = 0 + 2 ^ (p : Real) * ‖y - c‖ ^ (p : Real) := by
      rw [Real.mul_rpow (by simp) (by positivity)]
      ring
    _ <= 2 * ‖c‖ ^ (p - 1 : Real) * ‖y‖ + 2 ^ (p : Real) * ‖y - c‖ ^ (p : Real) := by
      gcongr
      positivity
  · calc ‖c‖ ^ (p : Real)
    _ = ‖c‖ ^ ((p - 1) + 1 : Real) := by abel_nf
    _ = ‖c‖ ^ (p - 1 : Real) * ‖c‖ := by rw [Real.rpow_add (by positivity), Real.rpow_one]
    _ <= ‖c‖ ^ (p - 1 : Real) * (2 * ‖y‖) := by gcongr; linarith
    _ = 2 * ‖c‖ ^ (p - 1 : Real) * ‖y‖ + 0 := by ring
    _ <= 2 * ‖c‖ ^ (p - 1 : Real) * ‖y‖ + 2 ^ (p : Real) * ‖y - c‖ ^ (p : Real) := by gcongr; positivity

/--
lemma `covarianceBilinDual_of_not_memLp'` / 引理 `covarianceBilinDual_of_not_memLp'`

English:
lemma covarianceBilinDual_of_not_memLp'
  statement: (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ)
  proof: by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  exact h

@[simp]

中文:
引理 covarianceBilinDual_of_not_memLp'
  结论: (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ)
  证明: by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  exact h

@[simp]

Depends on / 依赖: covarianceBilinDual, measurableEmbedding_subRight, memLp_map_measure_iff, uncenteredCovarianceBilinDual_of_not_memLp
-/
lemma covarianceBilinDual_of_not_memLp' (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ)
    (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  exact h

@[simp]
/--
lemma `covarianceBilinDual_of_not_memLp` / 引理 `covarianceBilinDual_of_not_memLp`

English:
lemma covarianceBilinDual_of_not_memLp
  given: (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  apply covarianceBilinDual_of_not_memLp'
  contrapose h
  exact memLp_id_of_self_sub_integral h

@[simp]

中文:
引理 covarianceBilinDual_of_not_memLp
  条件: (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  apply covarianceBilinDual_of_not_memLp'
  contrapose h
  exact memLp_id_of_self_sub_integral h

@[simp]

Depends on / 依赖: contrapose, covarianceBilinDual_of_not_memLp, memLp_id_of_self_sub_integral
-/
lemma covarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  apply covarianceBilinDual_of_not_memLp'
  contrapose h
  exact memLp_id_of_self_sub_integral h

@[simp]
/--
lemma `covarianceBilinDual_zero` / 引理 `covarianceBilinDual_zero`

English:
lemma covarianceBilinDual_zero
  statement: covarianceBilinDual (0 : Measure E) = 0
  proof: by
  rw [covarianceBilinDual]; rw [Measure.map_zero]; rw [uncenteredCovarianceBilinDual_zero]

中文:
引理 covarianceBilinDual_zero
  结论: covarianceBilinDual (0 : Measure E) = 0
  证明: by
  rw [covarianceBilinDual]; rw [Measure.map_zero]; rw [uncenteredCovarianceBilinDual_zero]

Depends on / 依赖: Measure, Measure.map_zero, covarianceBilinDual, map_zero, uncenteredCovarianceBilinDual_zero
-/
lemma covarianceBilinDual_zero : covarianceBilinDual (0 : Measure E) = 0 := by
  rw [covarianceBilinDual]; rw [Measure.map_zero]; rw [uncenteredCovarianceBilinDual_zero]

/--
lemma `covarianceBilinDual_comm` / 引理 `covarianceBilinDual_comm`

English:
lemma covarianceBilinDual_comm
  given: (L₁ L₂ : StrongDual Real E)
  proof: by
  by_cases h : MemLp (fun x => x - ∫ y, y ∂μ) 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x => x - ∫ (x : E), x ∂μ) μ) :=
(measurableEmbedding_subRight _).memLp_map_measure_iff.mpr h
    simp_rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply h', mul_comm (L₁ _)]
  · simp [h, covaria

中文:
引理 covarianceBilinDual_comm
  条件: (L₁ L₂ : StrongDual 实数 E)
  证明: by
  by_cases h : MemLp (fun x => x - ∫ y, y ∂μ) 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x => x - ∫ (x : E), x ∂μ) μ) :=
(measurableEmbedding_subRight _).memLp_map_measure_iff.mpr h
    simp_rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply h', mul_comm (L₁ _)]
  · simp [h, covaria

Depends on / 依赖: Measure, Measure.map, covarianceBilinDual, covarianceBilinDual_of_not_memLp, measurableEmbedding_subRight, memLp_map_measure_iff, memLp_map_measure_iff.mpr, mul_comm, simp_rw, uncenteredCovarianceBilinDual_apply
-/
lemma covarianceBilinDual_comm (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = covarianceBilinDual μ L₂ L₁ := by
  by_cases h : MemLp (fun x => x - ∫ y, y ∂μ) 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x => x - ∫ (x : E), x ∂μ) μ) :=
(measurableEmbedding_subRight _).memLp_map_measure_iff.mpr h
    simp_rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply h', mul_comm (L₁ _)]
  · simp [h, covarianceBilinDual_of_not_memLp']

@[simp]
/--
lemma `covarianceBilinDual_self_nonneg` / 引理 `covarianceBilinDual_self_nonneg`

English:
lemma covarianceBilinDual_self_nonneg
  given: (L : StrongDual Real E)
  statement: 0 <= covarianceBilinDual μ L L
  proof: by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilinDual, uncenteredCovarianceBilinDual,
      ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap.toContinuousLinearMap_apply]
    exact real_inner_self_nonneg
  · simp [h]

中文:
引理 covarianceBilinDual_self_nonneg
  条件: (L : StrongDual 实数 E)
  结论: 0 <= covarianceBilinDual μ L L
  证明: by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilinDual, uncenteredCovarianceBilinDual,
      ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap.toContinuousLinearMap_apply]
    exact real_inner_self_nonneg
  · simp [h]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap, IsBoundedBilinearMap.toContinuousLinearMap_apply, bilinearComp_apply, covarianceBilinDual, real_inner_self_nonneg, toContinuousLinearMap_apply, uncenteredCovarianceBilinDual
-/
lemma covarianceBilinDual_self_nonneg (L : StrongDual Real E) : 0 <= covarianceBilinDual μ L L := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilinDual, uncenteredCovarianceBilinDual,
      ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap.toContinuousLinearMap_apply]
    exact real_inner_self_nonneg
  · simp [h]

/--
lemma `isPosSemidef_covarianceBilinDual` / 引理 `isPosSemidef_covarianceBilinDual`

English:
lemma isPosSemidef_covarianceBilinDual
  statement: (covarianceBilinDual μ).toBilinForm.IsPosSemidef where
  proof: covarianceBilinDual_comm
  nonneg := covarianceBilinDual_self_nonneg

中文:
引理 isPosSemidef_covarianceBilinDual
  结论: (covarianceBilinDual μ).toBilinForm.IsPosSemidef where
  证明: covarianceBilinDual_comm
  nonneg := covarianceBilinDual_self_nonneg

Depends on / 依赖: covarianceBilinDual_comm
-/
lemma isPosSemidef_covarianceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilinDual_comm
  nonneg := covarianceBilinDual_self_nonneg

variable [CompleteSpace E] [IsFiniteMeasure μ]

/--
lemma `covarianceBilinDual_apply` / 引理 `covarianceBilinDual_apply`

English:
lemma covarianceBilinDual_apply
  given: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
      L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
· exact (measurableEmbedding_subRight _).memLp_map_

中文:
引理 covarianceBilinDual_apply
  条件: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
      L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
· exact (measurableEmbedding_subRight _).memLp_map_

Depends on / 依赖: H.out.choose_spec.choose_spec.choose_spec.choose, H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty, L.integral_comp_comm, StrongDual, choose_spec, covarianceBilinDual, fun_prop, h.integrable, h.sub, integrable, integral_comp_comm, integral_map, measurableEmbedding_subRight, memLp_const, memLp_map_measure_iff, memLp_map_measure_iff.mpr, nonempty, uncenteredCovarianceBilinDual_apply
-/
lemma covarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ := by
  rw [covarianceBilinDual]; rw [uncenteredCovarianceBilinDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
      L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
· exact (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr h.sub (memLp_const _)

/--
lemma `covarianceBilinDual_apply'` / 引理 `covarianceBilinDual_apply'`

English:
lemma covarianceBilinDual_apply'
  given: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  rw [covarianceBilinDual_apply h]
  have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

中文:
引理 covarianceBilinDual_apply'
  条件: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  rw [covarianceBilinDual_apply h]
  have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

Depends on / 依赖: L.integral_comp_comm, StrongDual, covarianceBilinDual_apply, h.integrable, integrable, integral_comp_comm
-/
lemma covarianceBilinDual_apply' (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilinDual_apply h]
  have hL (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

/--
lemma `covarianceBilinDual_eq_covariance` / 引理 `covarianceBilinDual_eq_covariance`

English:
lemma covarianceBilinDual_eq_covariance
  given: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E)
  proof: by
  rw [covarianceBilinDual_apply h]; rw [covariance]

中文:
引理 covarianceBilinDual_eq_covariance
  条件: (h : MemLp id 2 μ) (L₁ L₂ : StrongDual 实数 E)
  证明: by
  rw [covarianceBilinDual_apply h]; rw [covariance]

Depends on / 依赖: Function, Function.bijective_id, IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective, bijective_id, covariance, covarianceBilinDual_apply, of_algebraMap_bijective
-/
lemma covarianceBilinDual_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
    covarianceBilinDual μ L₁ L₂ = cov[L₁, L₂; μ] := by
  rw [covarianceBilinDual_apply h]; rw [covariance]

/--
lemma `covarianceBilinDual_self_eq_variance` / 引理 `covarianceBilinDual_self_eq_variance`

English:
lemma covarianceBilinDual_self_eq_variance
  given: (h : MemLp id 2 μ) (L : StrongDual Real E)
  proof: by
  rw [covarianceBilinDual_eq_covariance h]; rw [covariance_self (by fun_prop)]

中文:
引理 covarianceBilinDual_self_eq_variance
  条件: (h : MemLp id 2 μ) (L : StrongDual 实数 E)
  证明: by
  rw [covarianceBilinDual_eq_covariance h]; rw [covariance_self (by fun_prop)]

Depends on / 依赖: IsStandardSmooth, IsStandardSmooth.finitePresentation, covarianceBilinDual_eq_covariance, covariance_self, finitePresentation, fun_prop
-/
lemma covarianceBilinDual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual Real E) :
    covarianceBilinDual μ L L = Var[L; μ] := by
  rw [covarianceBilinDual_eq_covariance h]; rw [covariance_self (by fun_prop)]

end Covariance

end ProbabilityTheory
