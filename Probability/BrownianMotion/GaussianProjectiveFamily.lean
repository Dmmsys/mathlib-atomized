/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Finite dimensional distributions of Brownian motion

In this file we define `projectiveFamily : (I : Finset ℝ≥0) → Measure (I → ℝ)`. Each
`projectiveFamily I` is the centered Gaussian measure over `I → ℝ`
with covariance matrix given by `covMatrix I s t := min s t`.
Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov's extension
theorem, which is phrased in this language.

We prove that these measures satisfy `IsProjectiveMeasureFamily`, which means that they can be
extended into a measure over `ℝ≥0 → ℝ` thanks to the Kolmogorov's extension theorem
(not in Mathlib yet). The obtained measure is a measure over the set of real processes indexed
by `ℝ≥0` and is the law of the Brownian motion.

## Main definition

* `BrownianReal.projectiveFamily I`: The centered Gaussian measure over `I → ℝ`
  with covariance matrix given by `covMatrix I s t := min s t`.

## Main statement

* `BrownianReal.isProjectiveMeasureFamily_projectiveFamily`:
  `BrownianReal.projectiveFamily` satisfies `IsProjectiveMeasureFamily`,
  which means it can be extended into a measure over `ℝ≥0 → ℝ`.

## Tags

Brownian motion, covariance matrix, projective family
-/

@[expose] public section


open MeasureTheory NormedSpace Set WithLp
open scoped ENNReal NNReal

namespace ProbabilityTheory.BrownianReal

variable {I J : Finset Real>=0}

/--
Definition of `covMatrix` / `covMatrix` 的定义

English:
definition covMatrix
  signature: (I : Finset Real>=0)
  body: .of fun s t => min s t

@[simp]

中文:
定义 covMatrix
  签名: (I : Finset 实数>=0)
  定义体: .of fun s t => min s t

@[simp]
-/
def covMatrix (I : Finset Real>=0) : Matrix I I Real := .of fun s t => min s t

@[simp]
/--
lemma `covMatrix_apply` / 引理 `covMatrix_apply`

English:
lemma covMatrix_apply
  given: (s t : I)
  proof: rfl

中文:
引理 covMatrix_apply
  条件: (s t : I)
  证明: rfl
-/
lemma covMatrix_apply (s t : I) :
    covMatrix I s t = min s.1 t.1 := rfl

/--
lemma `covMatrix_submatrix` / 引理 `covMatrix_submatrix`

English:
lemma covMatrix_submatrix
  given: (hJI : J subseteq I)
  proof: rfl

中文:
引理 covMatrix_submatrix
  条件: (hJI : J subseteq I)
  证明: rfl
-/
lemma covMatrix_submatrix (hJI : J subseteq I) :
    (covMatrix I).submatrix (fun i : J => ⟨i.1, hJI i.2⟩) (fun i : J => ⟨i.1, hJI i.2⟩) =
    covMatrix J := rfl

/--
lemma `posSemidef_covMatrix` / 引理 `posSemidef_covMatrix`

English:
lemma posSemidef_covMatrix
  given: (I : Finset Real>=0)
  proof: by
  have : covMatrix I = .of fun s t => volume.real ((Icc 0 s.1.1) inter (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ => measurableSet_Icc)
    (fun _ => isCompact_Icc.measure_ne_top)

中文:
引理 posSemidef_covMatrix
  条件: (I : Finset 实数>=0)
  证明: by
  have : covMatrix I = .of fun s t => volume.real ((Icc 0 s.1.1) inter (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ => measurableSet_Icc)
    (fun _ => isCompact_Icc.measure_ne_top)

Depends on / 依赖: Icc_inter_Icc, covMatrix, isCompact_Icc, isCompact_Icc.measure_ne_top, measurableSet_Icc, measure_ne_top, posSemidef_matrix_measure_inter, volume, volume.real
-/
lemma posSemidef_covMatrix (I : Finset Real>=0) :
    (covMatrix I).PosSemidef := by
  have : covMatrix I = .of fun s t => volume.real ((Icc 0 s.1.1) inter (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ => measurableSet_Icc)
    (fun _ => isCompact_Icc.measure_ne_top)

/--
Definition of `projectiveFamily` / `projectiveFamily` 的定义

English:
definition projectiveFamily
  signature: (I : Finset Real>=0)
  body: .map (MeasurableEquiv.toLp 2 (I -> Real)).symm multivariateGaussian 0 (covMatrix I)

中文:
定义 projectiveFamily
  签名: (I : Finset 实数>=0)
  定义体: .map (MeasurableEquiv.toLp 2 (I -> Real)).symm multivariateGaussian 0 (covMatrix I)

Depends on / 依赖: CanLift, MeasurableEquiv, MeasurableEquiv.toLp, NonUnitalSubring, covMatrix, multivariateGaussian
-/
noncomputable def projectiveFamily (I : Finset Real>=0) : Measure (I -> Real) :=
.map (MeasurableEquiv.toLp 2 (I -> Real)).symm multivariateGaussian 0 (covMatrix I)

/--
lemma `measurePreserving_ofLp_multivariateGaussian` / 引理 `measurePreserving_ofLp_multivariateGaussian`

English:
lemma measurePreserving_ofLp_multivariateGaussian
  given: (I : Finset Real>=0)
  proof: by fun_prop
  map_eq := rfl

中文:
引理 measurePreserving_ofLp_multivariateGaussian
  条件: (I : Finset 实数>=0)
  证明: by fun_prop
  map_eq := rfl

Depends on / 依赖: fun_prop, map_eq
-/
lemma measurePreserving_ofLp_multivariateGaussian (I : Finset Real>=0) :
    MeasurePreserving ofLp
      (multivariateGaussian 0 (covMatrix I)) (projectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

/--
lemma `measurePreserving_toLp_projectiveFamily` / 引理 `measurePreserving_toLp_projectiveFamily`

English:
lemma measurePreserving_toLp_projectiveFamily
  given: (I : Finset Real>=0)
  proof: by fun_prop
  map_eq := by
    rw [projectiveFamily]; rw [Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

中文:
引理 measurePreserving_toLp_projectiveFamily
  条件: (I : Finset 实数>=0)
  证明: by fun_prop
  map_eq := by
    rw [projectiveFamily]; rw [Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.coe_toLp, Measure, Measure.map_map, all_goals, coe_toLp, fun_prop, map_eq, map_map, projectiveFamily
-/
lemma measurePreserving_toLp_projectiveFamily (I : Finset Real>=0) :
    MeasurePreserving (toLp 2) (projectiveFamily I)
      (multivariateGaussian 0 (covMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [projectiveFamily]; rw [Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

/--
lemma `integral_projectiveFamily` / 引理 `integral_projectiveFamily`

English:
lemma integral_projectiveFamily
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  simp [projectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_projectiveFamily]

中文:
引理 integral_projectiveFamily
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  simp [projectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_projectiveFamily]

Depends on / 依赖: integral_map_equiv, projectiveFamily
-/
lemma integral_projectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (I : Finset Real>=0) (f : (I -> Real) -> E) :
    ∫ x, f x ∂projectiveFamily I =
      ∫ x, f (ofLp x) ∂multivariateGaussian 0 (covMatrix I) := by
  simp [projectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_projectiveFamily]
/--
lemma `covariance_projectiveFamily` / 引理 `covariance_projectiveFamily`

English:
lemma covariance_projectiveFamily
  given: (I : Finset Real>=0) (f g : (I -> Real) -> Real)
  proof: by
  rw [projectiveFamily]; rw [covariance_map_equiv]
  rfl

@[to_fun variance_fun_projectiveFamily]

中文:
引理 covariance_projectiveFamily
  条件: (I : Finset 实数>=0) (f g : (I -> 实数) -> 实数)
  证明: by
  rw [projectiveFamily]; rw [covariance_map_equiv]
  rfl

@[to_fun variance_fun_projectiveFamily]

Depends on / 依赖: covariance_map_equiv, projectiveFamily
-/
lemma covariance_projectiveFamily (I : Finset Real>=0) (f g : (I -> Real) -> Real) :
    cov[f, g; projectiveFamily I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily]; rw [covariance_map_equiv]
  rfl

@[to_fun variance_fun_projectiveFamily]
/--
lemma `variance_projectiveFamily` / 引理 `variance_projectiveFamily`

English:
lemma variance_projectiveFamily
  given: (I : Finset Real>=0) (f : (I -> Real) -> Real)
  proof: by
  rw [projectiveFamily]; rw [variance_map_equiv]
  rfl

中文:
引理 variance_projectiveFamily
  条件: (I : Finset 实数>=0) (f : (I -> 实数) -> 实数)
  证明: by
  rw [projectiveFamily]; rw [variance_map_equiv]
  rfl

Depends on / 依赖: projectiveFamily, variance_map_equiv
-/
lemma variance_projectiveFamily (I : Finset Real>=0) (f : (I -> Real) -> Real) :
    Var[f; projectiveFamily I] =
      Var[f ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily]; rw [variance_map_equiv]
  rfl

/--
Instance `isGaussian_projectiveFamily` / 实例 `isGaussian_projectiveFamily`

English:
instance isGaussian_projectiveFamily
  signature: (I : Finset Real>=0)
  body: by
  rw [projectiveFamily]; rw [show ⇑(MeasurableEquiv.toLp 2 (I -> Real)).symm = ⇑(EuclideanSpace.equiv I Real) from rfl]
  infer_instance

@[simp]

中文:
实例 isGaussian_projectiveFamily
  签名: (I : Finset 实数>=0)
  定义体: by
  rw [projectiveFamily]; rw [show ⇑(MeasurableEquiv.toLp 2 (I -> Real)).symm = ⇑(EuclideanSpace.equiv I Real) from rfl]
  infer_instance

@[simp]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.equiv, MeasurableEquiv, MeasurableEquiv.toLp, infer_instance, projectiveFamily
-/
instance isGaussian_projectiveFamily (I : Finset Real>=0) :
    IsGaussian (projectiveFamily I) := by
  rw [projectiveFamily]; rw [show ⇑(MeasurableEquiv.toLp 2 (I -> Real)).symm = ⇑(EuclideanSpace.equiv I Real) from rfl]
  infer_instance

@[simp]
/--
lemma `integral_id_projectiveFamily` / 引理 `integral_id_projectiveFamily`

English:
lemma integral_id_projectiveFamily
  given: (I : Finset Real>=0)
  proof: by
  rw [integral_projectiveFamily]; rw [← PiLp.coe_continuousLinearEquiv 2 Real]; rw [ContinuousLinearEquiv.integral_comp_id_comm]; rw [integral_id_multivariateGaussian]; rw [map_zero]

中文:
引理 integral_id_projectiveFamily
  条件: (I : Finset 实数>=0)
  证明: by
  rw [integral_projectiveFamily]; rw [← PiLp.coe_continuousLinearEquiv 2 Real]; rw [ContinuousLinearEquiv.integral_comp_id_comm]; rw [integral_id_multivariateGaussian]; rw [map_zero]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.integral_comp_id_comm, PiLp.coe_continuousLinearEquiv, coe_continuousLinearEquiv, integral_comp_id_comm, integral_id_multivariateGaussian, integral_projectiveFamily, map_zero
-/
lemma integral_id_projectiveFamily (I : Finset Real>=0) :
    ∫ x, x ∂(projectiveFamily I) = 0 := by
  rw [integral_projectiveFamily]; rw [← PiLp.coe_continuousLinearEquiv 2 Real]; rw [ContinuousLinearEquiv.integral_comp_id_comm]; rw [integral_id_multivariateGaussian]; rw [map_zero]

/--
lemma `integral_id_projectiveFamily'` / 引理 `integral_id_projectiveFamily'`

English:
lemma integral_id_projectiveFamily'
  given: (I : Finset Real>=0)
  proof: integral_id_projectiveFamily I

@[simp]

中文:
引理 integral_id_projectiveFamily'
  条件: (I : Finset 实数>=0)
  证明: integral_id_projectiveFamily I

@[simp]

Depends on / 依赖: integral_id_projectiveFamily
-/
lemma integral_id_projectiveFamily' (I : Finset Real>=0) :
    (projectiveFamily I)[id] = 0 := integral_id_projectiveFamily I

@[simp]
/--
lemma `integral_eval_projectiveFamily` / 引理 `integral_eval_projectiveFamily`

English:
lemma integral_eval_projectiveFamily
  given: (I : Finset Real>=0) (s : I)
  proof: by
  conv => enter [1, 2]; change fun x => ContinuousLinearMap.proj (R := Real) s x
  rw [ContinuousLinearMap.integral_comp_id_comm]; rw [integral_id_projectiveFamily]; rw [map_zero]
  exact IsGaussian.integrable_id

中文:
引理 integral_eval_projectiveFamily
  条件: (I : Finset 实数>=0) (s : I)
  证明: by
  conv => enter [1, 2]; change fun x => ContinuousLinearMap.proj (R := Real) s x
  rw [ContinuousLinearMap.integral_comp_id_comm]; rw [integral_id_projectiveFamily]; rw [map_zero]
  exact IsGaussian.integrable_id

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_id_comm, ContinuousLinearMap.proj, IsGaussian, IsGaussian.integrable_id, integrable_id, integral_comp_id_comm, integral_id_projectiveFamily, map_zero
-/
lemma integral_eval_projectiveFamily (I : Finset Real>=0) (s : I) :
    ∫ x, x s ∂(projectiveFamily I) = 0 := by
  conv => enter [1, 2]; change fun x => ContinuousLinearMap.proj (R := Real) s x
  rw [ContinuousLinearMap.integral_comp_id_comm]; rw [integral_id_projectiveFamily]; rw [map_zero]
  exact IsGaussian.integrable_id

/--
lemma `covariance_eval_projectiveFamily` / 引理 `covariance_eval_projectiveFamily`

English:
lemma covariance_eval_projectiveFamily
  given: (I : Finset Real>=0) (s t : I)
  proof: by
  rw [covariance_fun_projectiveFamily]; rw [covariance_eval_multivariateGaussian (posSemidef_covMatrix I)]; rw [covMatrix_apply]

中文:
引理 covariance_eval_projectiveFamily
  条件: (I : Finset 实数>=0) (s t : I)
  证明: by
  rw [covariance_fun_projectiveFamily]; rw [covariance_eval_multivariateGaussian (posSemidef_covMatrix I)]; rw [covMatrix_apply]

Depends on / 依赖: covMatrix_apply, covariance_eval_multivariateGaussian, covariance_fun_projectiveFamily, posSemidef_covMatrix
-/
lemma covariance_eval_projectiveFamily (I : Finset Real>=0) (s t : I) :
    cov[fun x => x s, fun x => x t; projectiveFamily I] = min s.1 t.1 := by
  rw [covariance_fun_projectiveFamily]; rw [covariance_eval_multivariateGaussian (posSemidef_covMatrix I)]; rw [covMatrix_apply]

/--
lemma `variance_eval_projectiveFamily` / 引理 `variance_eval_projectiveFamily`

English:
lemma variance_eval_projectiveFamily
  given: (s : I)
  proof: by
  rw [← covariance_self]; rw [covariance_eval_projectiveFamily]; rw [min_self]
  exact aemeasurable_id.eval s

中文:
引理 variance_eval_projectiveFamily
  条件: (s : I)
  证明: by
  rw [← covariance_self]; rw [covariance_eval_projectiveFamily]; rw [min_self]
  exact aemeasurable_id.eval s

Depends on / 依赖: aemeasurable_id, aemeasurable_id.eval, covariance_eval_projectiveFamily, covariance_self, min_self
-/
lemma variance_eval_projectiveFamily (s : I) :
    Var[fun x => x s; projectiveFamily I] = s := by
  rw [← covariance_self]; rw [covariance_eval_projectiveFamily]; rw [min_self]
  exact aemeasurable_id.eval s

/--
lemma `measurePreserving_eval_projectiveFamily` / 引理 `measurePreserving_eval_projectiveFamily`

English:
lemma measurePreserving_eval_projectiveFamily
  given: (s : I)
  proof: by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal]; rw [integral_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [Real.toNNReal_coe]

中文:
引理 measurePreserving_eval_projectiveFamily
  条件: (s : I)
  证明: by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal]; rw [integral_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [Real.toNNReal_coe]

Depends on / 依赖: IsGaussian, IsGaussian.hasGaussianLaw_id.eval, Real.toNNReal_coe, fun_prop, hasGaussianLaw_id, integral_eval_projectiveFamily, map_eq, map_eq_gaussianReal, toNNReal_coe, variance_eval_projectiveFamily
-/
lemma measurePreserving_eval_projectiveFamily (s : I) :
    MeasurePreserving (fun x => x s) (projectiveFamily I) (gaussianReal 0 s) where
  measurable := by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal]; rw [integral_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [Real.toNNReal_coe]

/--
lemma `measurePreserving_eval_sub_eval_projectiveFamily` / 引理 `measurePreserving_eval_sub_eval_projectiveFamily`

English:
lemma measurePreserving_eval_sub_eval_projectiveFamily
  given: (I : Finset Real>=0) (s t : I)
  proof: by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal]; rw [variance_fun_sub]; rw [variance_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [covariance_eval_projectiveFamily]; rw [integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub]; rw

中文:
引理 measurePreserving_eval_sub_eval_projectiveFamily
  条件: (I : Finset 实数>=0) (s t : I)
  证明: by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal]; rw [variance_fun_sub]; rw [variance_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [covariance_eval_projectiveFamily]; rw [integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub]; rw

Depends on / 依赖: HasGaussianLaw, HasGaussianLaw.map_eq_gaussianReal, NNReal, NNReal.coe_add, NNReal.coe_sub, Real.toNNReal_coe, add_comm, coe_add, coe_sub, convert, covariance_eval_projectiveFamily, fun_prop, generalizing, integral_sub, le_of_not_ge, map_eq, map_eq_gaussianReal, min_comm, min_eq_left, nndist_comm
-/
lemma measurePreserving_eval_sub_eval_projectiveFamily (I : Finset Real>=0) (s t : I) :
    MeasurePreserving (fun x => x s - x t) (projectiveFamily I)
      (gaussianReal 0 (nndist s.1 t.1)) where
  measurable := by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal]; rw [variance_fun_sub]; rw [variance_eval_projectiveFamily]; rw [variance_eval_projectiveFamily]; rw [covariance_eval_projectiveFamily]; rw [integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub]; rw [← NNReal.coe_add]; rw [← NNReal.coe_sub]; rw [Real.toNNReal_coe]
      · wlog hst : (s : Real>=0) <= t generalizing s t
        · convert this t s (le_of_not_ge hst) using 1
          · rw [add_comm, min_comm]
          · rw [nndist_comm]
        grw [min_eq_left hst, NNReal.nndist_eq, max_eq_right (by grw [hst]), two_mul,
          add_tsub_add_eq_tsub_left]
      nth_grw 1 [two_mul, min_le_left, min_le_right]
    · exact (IsGaussian.hasGaussianLaw_id.eval s).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval t).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub

/--
lemma `isProjectiveMeasureFamily_projectiveFamily` / 引理 `isProjectiveMeasureFamily_projectiveFamily`

English:
lemma isProjectiveMeasureFamily_projectiveFamily
  proof: by
  intro I J hJI
  nth_rw 2 [projectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ => Real) hJI ∘ (MeasurableEquiv.toLp 2 (I -> Real)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this]; rw [((measurePreserving_ofLp_multivariateGaussian 

中文:
引理 isProjectiveMeasureFamily_projectiveFamily
  证明: by
  intro I J hJI
  nth_rw 2 [projectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ => Real) hJI ∘ (MeasurableEquiv.toLp 2 (I -> Real)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this]; rw [((measurePreserving_ofLp_multivariateGaussian 

Depends on / 依赖: EuclideanSpace, EuclideanSpace.restrict, Finset, Finset.measurable_restrict, Finset.restrict, MeasurableEquiv, MeasurableEquiv.toLp, Measure, Measure.map_map, fun_prop, map_eq, map_map, measurePreserving_ofLp_multivariateGaussian, nth_rw, posSemidef_covMatrix, projectiveFamily
-/
lemma isProjectiveMeasureFamily_projectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ => Real) projectiveFamily := by
  intro I J hJI
  nth_rw 2 [projectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ => Real) hJI ∘ (MeasurableEquiv.toLp 2 (I -> Real)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this]; rw [((measurePreserving_ofLp_multivariateGaussian J).comp
        (measurePreserving_restrict₂_multivariateGaussian (posSemidef_covMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

/--
lemma `measurePreserving_restrict_projectiveFamily` / 引理 `measurePreserving_restrict_projectiveFamily`

English:
lemma measurePreserving_restrict_projectiveFamily
  given: (hIJ : I subseteq J)
  proof: Finset.measurable_restrict₂ _
.symm map_eq := isProjectiveMeasureFamily_projectiveFamily J I hIJ

中文:
引理 measurePreserving_restrict_projectiveFamily
  条件: (hIJ : I subseteq J)
  证明: Finset.measurable_restrict₂ _
.symm map_eq := isProjectiveMeasureFamily_projectiveFamily J I hIJ

Depends on / 依赖: projectiveFamily
-/
lemma measurePreserving_restrict_projectiveFamily (hIJ : I subseteq J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ => Real) hIJ) (projectiveFamily J)
      (projectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
.symm map_eq := isProjectiveMeasureFamily_projectiveFamily J I hIJ

end ProbabilityTheory.BrownianReal
