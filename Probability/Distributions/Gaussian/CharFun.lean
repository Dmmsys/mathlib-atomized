/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Facts about Gaussian characteristic function

In this file we prove that Gaussian measures over a Banach space `E` are exactly those measures
`μ` such that there exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
positive semidefinite (satisfying `f.toBilinForm.IsPosSemidef`) such that
`charFunDual μ L = exp (L m * I - f L L / 2)`.
We also prove that such `m` and `f` are unique and equal to `∫ x, x ∂μ` and `covarianceBilinDual μ`.

We also specialize these statements in the case of Hilbert spaces, with
`f : E →L[ℝ] E →L[ℝ] ℝ`, `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)` and
`f = covarianceBilin μ`.

## Main statements

* `isGaussian_iff_gaussian_charFunDual μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f L L / 2)`.
* `isGaussian_iff_gaussian_charFun μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : E →L[ℝ] E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)`.

## Tags

Gaussian measure, characteristic function
-/

public section


open Complex MeasureTheory WithLp ContinuousLinearMap

open scoped Matrix NNReal Real RealInnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}

section NormedSpace

variable [NormedSpace Real E]

/--
lemma `IsGaussian.charFunDual_eq'` / 引理 `IsGaussian.charFunDual_eq'`

English:
lemma IsGaussian.charFunDual_eq'
  given: [IsGaussian μ] (L : StrongDual Real E)
  proof: by
  rw [IsGaussian.charFunDual_eq]; rw [covarianceBilinDual_self_eq_variance]; rw [integral_complex_ofReal]; rw [L.integral_comp_id_comm']
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

中文:
引理 是Gaussian.charFunDual_eq'
  条件: [是Gaussian μ] (L : StrongDual 实数 E)
  证明: by
  rw [IsGaussian.charFunDual_eq]; rw [covarianceBilinDual_self_eq_variance]; rw [integral_complex_ofReal]; rw [L.integral_comp_id_comm']
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

Depends on / 依赖: IsGaussian, IsGaussian.charFunDual_eq, IsGaussian.integrable_id, IsGaussian.memLp_two_id, L.integral_comp_id_comm, charFunDual_eq, covarianceBilinDual_self_eq_variance, integrable_id, integral_comp_id_comm, integral_complex_ofReal, memLp_two_id
-/
lemma IsGaussian.charFunDual_eq' [IsGaussian μ] (L : StrongDual Real E) :
    charFunDual μ L = exp ((L μ[id]) * I - covarianceBilinDual μ L L / 2) := by
  rw [IsGaussian.charFunDual_eq]; rw [covarianceBilinDual_self_eq_variance]; rw [integral_complex_ofReal]; rw [L.integral_comp_id_comm']
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

/--
lemma `isGaussian_iff_gaussian_charFunDual` / 引理 `isGaussian_iff_gaussian_charFunDual`

English:
lemma isGaussian_iff_gaussian_charFunDual
  given: [IsFiniteMeasure μ]
  proof: by
  refine ⟨fun h => ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
    h.charFunDual_eq'⟩,
    fun ⟨m, f, hf, h⟩ => isGaussian_of_map_eq_gaussianReal fun L => ⟨L m, (f L L).toNNReal, ?_⟩⟩
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_map_eq_charFunDual_smul, h, charFu

中文:
引理 isGaussian_iff_gaussian_charFunDual
  条件: [是有限测度 μ]
  证明: by
  refine ⟨fun h => ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
    h.charFunDual_eq'⟩,
    fun ⟨m, f, hf, h⟩ => isGaussian_of_map_eq_gaussianReal fun L => ⟨L m, (f L L).toNNReal, ?_⟩⟩
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_map_eq_charFunDual_smul, h, charFu

Depends on / 依赖: Measure, Measure.ext_of_charFun, Real.coe_toNNReal, charFunDual_eq, charFun_gaussianReal, charFun_map_eq_charFunDual_smul, coe_toNNReal, congrm, covarianceBilinDual, ext_of_charFun, h.charFunDual_eq, hf.nonneg, isGaussian_of_map_eq_gaussianReal, isPosSemidef_covarianceBilinDual, map_smul, nonneg, ofReal, simp_rw, smul_apply, smul_eq_mul
-/
lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    exists (m : E) (f : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real),
      f.toBilinForm.IsPosSemidef ∧ forall L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h => ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
    h.charFunDual_eq'⟩,
    fun ⟨m, f, hf, h⟩ => isGaussian_of_map_eq_gaussianReal fun L => ⟨L m, (f L L).toNNReal, ?_⟩⟩
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
    smul_apply, map_smul, smul_apply, smul_eq_mul]
  norm_cast
  congrm exp (_ - ofReal ?_)
  rw [Real.coe_toNNReal]
  · ring
  exact hf.nonneg L

/--
lemma `gaussian_charFunDual_congr` / 引理 `gaussian_charFunDual_congr`

English:
lemma gaussian_charFunDual_congr
  statement: [IsFiniteMeasure μ] {m : E}
  proof: by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq', Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h L : (n L : Complex) = (L (∫ x, id x ∂μ) * I - covarianceBilinDual μ L L / 2 -
      L m * I + f L L / 2) / (2 * π * I) := by
    r

中文:
引理 gaussian_charFunDual_congr
  结论: [是有限测度 μ] {m : E}
  证明: by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq', Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h L : (n L : Complex) = (L (∫ x, id x ∂μ) * I - covarianceBilinDual μ L L / 2 -
      L m * I + f L L / 2) / (2 * π * I) := by
    r

Depends on / 依赖: Complex.exp_eq_exp_iff_exists_int, Complex.isometry_intCast.comp_continuous_iff, Continuous, IsLocallyConstant, IsLocallyConstant.iff_continuo, charFunDual_eq, comp_continuous_iff, covarianceBilinDual, eq_const, exp_eq_exp_iff_exists_int, fun_prop, iff_continuo, isGaussian_iff_gaussian_charFunDual, isometry_intCast, simp_rw
-/
lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real}
    (hf : f.toBilinForm.IsPosSemidef) (h : forall L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq', Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h L : (n L : Complex) = (L (∫ x, id x ∂μ) * I - covarianceBilinDual μ L L / 2 -
      L m * I + f L L / 2) / (2 * π * I) := by
    rw [hn L]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L => (n L : Complex))
    simp_rw [h]
    fun_prop
.eq_const have := (IsLocallyConstant.iff_continuous n).2 this
  have this L : n L = 0 := by
    rw [this 0]; rw [← Int.cast_inj (α := Complex)]
    simp [h]
  simp only [id_eq, this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re,
    ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im,
    zero_div, sub_zero] at hn
  constructor
  · rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
    simp [hn]
  · rw [← toBilinForm_inj]
    apply LinearMap.BilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    simp [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, (hn x).1.symm]

/--
lemma `IsGaussian.ext_covarianceBilinDual` / 引理 `IsGaussian.ext_covarianceBilinDual`

English:
lemma IsGaussian.ext_covarianceBilinDual
  statement: {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
  proof: by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq', hm, hv]

中文:
引理 是Gaussian.ext_covarianceBilinDual
  结论: {ν : 测度 E} [是Gaussian μ] [是Gaussian ν]
  证明: by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq', hm, hv]
-/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq', hm, hv]

/--
lemma `IsGaussian.ext_iff_covarianceBilinDual` / 引理 `IsGaussian.ext_iff_covarianceBilinDual`

English:
lemma IsGaussian.ext_iff_covarianceBilinDual
  statement: {ν : Measure E} [IsGaussian μ]
  proof: by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

中文:
引理 是Gaussian.ext_iff_covarianceBilinDual
  结论: {ν : 测度 E} [是Gaussian μ]
  证明: by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2
-/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace Real E]

/--
lemma `IsGaussian.charFun_eq'` / 引理 `IsGaussian.charFun_eq'`

English:
lemma IsGaussian.charFun_eq'
  given: [IsGaussian μ] (t : E)
  proof: by
  rw [IsGaussian.charFun_eq]; rw [covarianceBilin_self]; rw [integral_complex_ofReal]; rw [integral_inner]
  · rfl
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

中文:
引理 是Gaussian.charFun_eq'
  条件: [是Gaussian μ] (t : E)
  证明: by
  rw [IsGaussian.charFun_eq]; rw [covarianceBilin_self]; rw [integral_complex_ofReal]; rw [integral_inner]
  · rfl
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

Depends on / 依赖: IsGaussian, IsGaussian.charFun_eq, IsGaussian.integrable_id, IsGaussian.memLp_two_id, charFun_eq, covarianceBilin_self, integrable_id, integral_complex_ofReal, integral_inner, memLp_two_id
-/
lemma IsGaussian.charFun_eq' [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫ * I - covarianceBilin μ t t / 2) := by
  rw [IsGaussian.charFun_eq]; rw [covarianceBilin_self]; rw [integral_complex_ofReal]; rw [integral_inner]
  · rfl
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isGaussian_iff_gaussian_charFun` / 引理 `isGaussian_iff_gaussian_charFun`

English:
lemma isGaussian_iff_gaussian_charFun
  given: [IsFiniteMeasure μ]
  proof: by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ => ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap Real E).toContinuousLinearMap
      (InnerProductSpace.toDualMap Real E).toContinuousLinearMap,
    ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ => ⟨m,
   

中文:
引理 isGaussian_iff_gaussian_charFun
  条件: [是有限测度 μ]
  证明: by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ => ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap Real E).toContinuousLinearMap
      (InnerProductSpace.toDualMap Real E).toContinuousLinearMap,
    ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ => ⟨m,
   

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toDual, InnerProductSpace.toDualMap, any_goals, bilinearComp, f.bilinearComp, isGaussian_iff_gaussian_charFunDual, symm.toLinearIsometry.toContinuousLinearMap, toContinuousLinearMap, toDual, toDualMap, toLinearIsometry
-/
lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    exists (m : E) (f : E ->L[Real] E ->L[Real] Real),
      f.toBilinForm.IsPosSemidef ∧ forall t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ => ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap Real E).toContinuousLinearMap
      (InnerProductSpace.toDualMap Real E).toContinuousLinearMap,
    ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ => ⟨m,
      f.bilinearComp (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩⟩
  any_goals simpa using hf.eq ..
  any_goals simpa using hf.nonneg _
  · simp [charFun_eq_charFunDual_toDualMap, h, -InnerProductSpace.toContinuousLinearMap_toDualMap]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `gaussian_charFun_congr` / 引理 `gaussian_charFun_congr`

English:
lemma gaussian_charFun_congr
  statement: [IsFiniteMeasure μ] (m : E) (f : E ->L[Real] E ->L[Real] Real)
  proof: by
  let g : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real :=
    f.bilinearComp (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
  have : forall L : StrongDual Real E, cha

中文:
引理 gaussian_charFun_congr
  结论: [是有限测度 μ] (m : E) (f : E ->L[实数] E ->L[实数] 实数)
  证明: by
  let g : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real :=
    f.bilinearComp (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
  have : forall L : StrongDual Real E, cha

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toDual, IsPosSemidef, StrongDual, bilinearComp, charFunDual, charFun_toDual_symm_eq_charFunDual, f.bilinearComp, g.toBilinForm.IsPosSemidef, hf.eq, hf.no, symm.toLinearIsometry.toContinuousLinearMap, toBilinForm, toContinuousLinearMap, toDual, toLinearIsometry
-/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : E ->L[Real] E ->L[Real] Real)
    (hf : f.toBilinForm.IsPosSemidef) (h : forall t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilin μ := by
  let g : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real :=
    f.bilinearComp (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual Real E).symm.toLinearIsometry.toContinuousLinearMap
  have : forall L : StrongDual Real E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.toBilinForm.IsPosSemidef :=
    ⟨⟨fun x y => by simpa [g] using hf.eq ..⟩, ⟨fun x => by simpa [g] using hf.nonneg _⟩⟩
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covarianceBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    -InnerProductSpace.toContinuousLinearMap_toDualMap]

/--
lemma `IsGaussian.ext` / 引理 `IsGaussian.ext`

English:
lemma IsGaussian.ext
  statement: {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
  proof: by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq', hm, hv]

中文:
引理 是Gaussian.ext
  结论: {ν : 测度 E} [是Gaussian μ] [是Gaussian ν]
  证明: by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq', hm, hv]
-/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq', hm, hv]

/--
lemma `IsGaussian.ext_iff` / 引理 `IsGaussian.ext_iff`

English:
lemma IsGaussian.ext_iff
  given: {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
  proof: by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

中文:
引理 是Gaussian.ext_iff
  条件: {ν : 测度 E} [是Gaussian μ] [是Gaussian ν]
  证明: by simp [h]
  mpr h := IsGaussian.ext h.1 h.2
-/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilin μ = covarianceBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

end ProbabilityTheory
