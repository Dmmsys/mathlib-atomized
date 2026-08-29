/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Multivariate Gaussian distributions

In this file we define the standard Gaussian distribution over a Euclidean space and multivariate
Gaussian distributions over `EuclideanSpace ℝ ι`.

## Main definitions

* `stdGaussian E`: Standard Gaussian distribution on a finite-dimensional real inner product space
  `E`. This is the random vector whose coordinates in an orthonormal basis are independent standard
  Gaussian.
* `multivariateGaussian μ S`: The multivariate Gaussian distribution on `EuclideanSpace ℝ ι`
  with mean `μ` and covariance matrix `S`, when `S` is a positive semidefinite matrix.

## TODO

- Generalize `multivariateGaussian μ S` when `S` is a symmetric trace class operator over a
  Hilbert space.

## Tags

multivariate Gaussian distribution

-/

@[expose] public section


open MeasureTheory Matrix WithLp Module Complex
open scoped RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

section stdGaussian

/-! ### Standard Gaussian measure over a Euclidean space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E]

variable (E) in
/-- Standard Gaussian distribution on a finite-dimensional real inner product space `E`.
This is the random vector whose coordinates in an orthonormal basis are independent standard
Gaussian.

The definition uses `stdOrthonormalBasis ℝ E` but does not actually depend on the
basis, see `stdGaussian_eq_map_pi_orthonormalBasis`. -/
noncomputable
/--
Definition of `stdGaussian` / `stdGaussian` 的定义

English:
definition stdGaussian
  signature: : Measure E
  body: (Measure.pi (fun _ : Fin (Module.finrank Real E) => gaussianReal 0 1)).map
    (fun x => ∑ i, x i • stdOrthonormalBasis Real E i)

中文:
定义 stdGaussian
  签名: : Measure E
  定义体: (Measure.pi (fun _ : Fin (Module.finrank Real E) => gaussianReal 0 1)).map
    (fun x => ∑ i, x i • stdOrthonormalBasis Real E i)

Depends on / 依赖: Measure, Measure.pi, Module, Module.finrank, finrank, gaussianReal, stdOrthonormalBasis
-/
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank Real E) => gaussianReal 0 1)).map
    (fun x => ∑ i, x i • stdOrthonormalBasis Real E i)

variable [BorelSpace E]

/--
Instance `isProbabilityMeasure_stdGaussian` / 实例 `isProbabilityMeasure_stdGaussian`

English:
instance isProbabilityMeasure_stdGaussian
  signature: : IsProbabilityMeasure (stdGaussian E)
  body: Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]

中文:
实例 isProbabilityMeasure_stdGaussian
  签名: : IsProbabilityMeasure (stdGaussian E)
  定义体: Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]

Depends on / 依赖: Measurable, Measurable.aemeasurable, Measure, Measure.isProbabilityMeasure_map, aemeasurable, fun_prop, isProbabilityMeasure_map
-/
instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
  Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]
/--
lemma `integral_id_stdGaussian` / 引理 `integral_id_stdGaussian`

English:
lemma integral_id_stdGaussian
  statement: ∫ x, x ∂(stdGaussian E) = 0
  proof: by
  rw [stdGaussian]; rw [integral_map _ (by fun_prop)]; rw [integral_finsetSum]
  · simp [integral_smul_const, integral_eval]
  · exact fun i _ => Integrable.smul_const (integrable_eval IsGaussian.integrable_id) _
  · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable

中文:
引理 integral_id_stdGaussian
  结论: ∫ x, x ∂(stdGaussian E) = 0
  证明: by
  rw [stdGaussian]; rw [integral_map _ (by fun_prop)]; rw [integral_finsetSum]
  · simp [integral_smul_const, integral_eval]
  · exact fun i _ => Integrable.smul_const (integrable_eval IsGaussian.integrable_id) _
  · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable

Depends on / 依赖: Finset, Finset.measurable_sum, Integrable, Integrable.smul_const, IsGaussian, IsGaussian.integrable_id, aemeasurable, fun_prop, integrable_eval, integrable_id, integral_eval, integral_finsetSum, integral_map, integral_smul_const, measurable_sum, smul_const, stdGaussian
-/
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian]; rw [integral_map _ (by fun_prop)]; rw [integral_finsetSum]
  · simp [integral_smul_const, integral_eval]
  · exact fun i _ => Integrable.smul_const (integrable_eval IsGaussian.integrable_id) _
  · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable

/--
lemma `variance_dual_stdGaussian` / 引理 `variance_dual_stdGaussian`

English:
lemma variance_dual_stdGaussian
  given: (L : StrongDual Real E)
  proof: by
  rw [stdGaussian]; rw [variance_map L.continuous.aemeasurable (Measurable.aemeasurable (by fun_prop))]
  have : L ∘ (fun x : Fin (Module.finrank Real E) -> Real => ∑ i, x i • stdOrthonormalBasis Real E i) =
      ∑ i, (fun x : Fin (Module.finrank Real E) -> Real => L (stdOrthonormalBasis Real E 

中文:
引理 variance_dual_stdGaussian
  条件: (L : StrongDual 实数 E)
  证明: by
  rw [stdGaussian]; rw [variance_map L.continuous.aemeasurable (Measurable.aemeasurable (by fun_prop))]
  have : L ∘ (fun x : Fin (Module.finrank Real E) -> Real => ∑ i, x i • stdOrthonormalBasis Real E i) =
      ∑ i, (fun x : Fin (Module.finrank Real E) -> Real => L (stdOrthonormalBasis Real E 

Depends on / 依赖: L.continuous.aemeasurable, Measurable, Measurable.aemeasurable, Module, Module.finrank, aemeasurable, continuous, finrank, fun_prop, gaussianReal, mul_comm, simp_rw, stdGaussian, stdOrthonormalBasis, variance_const_mul, variance_id_gaussianReal, variance_map, variance_sum_pi
-/
lemma variance_dual_stdGaussian (L : StrongDual Real E) :
    Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian]; rw [variance_map L.continuous.aemeasurable (Measurable.aemeasurable (by fun_prop))]
  have : L ∘ (fun x : Fin (Module.finrank Real E) -> Real => ∑ i, x i • stdOrthonormalBasis Real E i) =
      ∑ i, (fun x : Fin (Module.finrank Real E) -> Real => L (stdOrthonormalBasis Real E i) * x i) := by
    ext x; simp [mul_comm]
  rw [this]; rw [variance_sum_pi]
  · change ∑ i, Var[fun x => _ * (id x); gaussianReal 0 1] = _
    simp_rw [variance_const_mul, variance_id_gaussianReal, (stdOrthonormalBasis Real E).norm_dual]
    simp
  · exact fun i => IsGaussian.memLp_two_id.const_mul _

/--
lemma `charFun_stdGaussian` / 引理 `charFun_stdGaussian`

English:
lemma charFun_stdGaussian
  given: (t : E)
  proof: by
  rw [charFun_apply]; rw [stdGaussian]; rw [integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [sum_inner, ofReal_sum, Finset.sum_mul, exp_sum,
    integral_fintype_prod_eq_prod (f := fun i x => exp (⟪x • stdOrthonormalBasis Real E 

中文:
引理 charFun_stdGaussian
  条件: (t : E)
  证明: by
  rw [charFun_apply]; rw [stdGaussian]; rw [integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [sum_inner, ofReal_sum, Finset.sum_mul, exp_sum,
    integral_fintype_prod_eq_prod (f := fun i x => exp (⟪x • stdOrthonormalBasis Real E 

Depends on / 依赖: Finset, Finset.sum_mul, Measurable, Measurable.aemeasurable, Measurable.aestronglyMeasurable, NNReal, NNReal.coe_one, aemeasurable, aestronglyMeasurable, charFun_apply, charFun_apply_real, charFun_gaussianReal, coe_one, exp_sum, fun_prop, integral_fintype_prod_eq_prod, integral_map, mul_comm, mul_zero, ofReal_mul
-/
lemma charFun_stdGaussian (t : E) :
    charFun (stdGaussian E) t = exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply]; rw [stdGaussian]; rw [integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [sum_inner, ofReal_sum, Finset.sum_mul, exp_sum,
    integral_fintype_prod_eq_prod (f := fun i x => exp (⟪x • stdOrthonormalBasis Real E i, t⟫ * I)),
    real_inner_smul_left, mul_comm _ (⟪_, _⟫), ofReal_mul, ← charFun_apply_real,
    charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, ofReal_one, one_mul,
    zero_sub]
  simp_rw [← exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← ofReal_pow,
    ← ofReal_sum, (stdOrthonormalBasis Real E).sum_sq_inner_right, neg_div]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isGaussian_stdGaussian` / 实例 `isGaussian_stdGaussian`

English:
instance isGaussian_stdGaussian
  signature: : IsGaussian (stdGaussian E)
  body: by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL Real,
    LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner, ?_⟩
  simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

@[simp]

中文:
实例 isGaussian_stdGaussian
  签名: : IsGaussian (stdGaussian E)
  定义体: by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL Real,
    LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner, ?_⟩
  simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

@[simp]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.isPosSemidef_iff, charFun_stdGaussian, innerSL, innerSL_apply_apply, isGaussian_iff_gaussian_charFun, isPosSemidef_iff, isPosSemidef_inner, neg_div
-/
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL Real,
    LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner, ?_⟩
  simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

@[simp]
/--
lemma `integral_strongDual_stdGaussian` / 引理 `integral_strongDual_stdGaussian`

English:
lemma integral_strongDual_stdGaussian
  given: (L : StrongDual Real E)
  statement: (stdGaussian E)[L] = 0
  proof: by
  rw [L.integral_comp_id_comm IsGaussian.integrable_id]; rw [integral_id_stdGaussian]; rw [map_zero]

中文:
引理 integral_strongDual_stdGaussian
  条件: (L : StrongDual 实数 E)
  结论: (stdGaussian E)[L] = 0
  证明: by
  rw [L.integral_comp_id_comm IsGaussian.integrable_id]; rw [integral_id_stdGaussian]; rw [map_zero]

Depends on / 依赖: IsGaussian, IsGaussian.integrable_id, L.integral_comp_id_comm, integrable_id, integral_comp_id_comm, integral_id_stdGaussian, map_zero
-/
lemma integral_strongDual_stdGaussian (L : StrongDual Real E) : (stdGaussian E)[L] = 0 := by
  rw [L.integral_comp_id_comm IsGaussian.integrable_id]; rw [integral_id_stdGaussian]; rw [map_zero]

/--
lemma `charFunDual_stdGaussian` / 引理 `charFunDual_stdGaussian`

English:
lemma charFunDual_stdGaussian
  given: (L : StrongDual Real E)
  proof: by
  simp [IsGaussian.charFunDual_eq, integral_complex_ofReal, variance_dual_stdGaussian, neg_div]

中文:
引理 charFunDual_stdGaussian
  条件: (L : StrongDual 实数 E)
  证明: by
  simp [IsGaussian.charFunDual_eq, integral_complex_ofReal, variance_dual_stdGaussian, neg_div]

Depends on / 依赖: IsGaussian, IsGaussian.charFunDual_eq, charFunDual_eq, integral_complex_ofReal, neg_div, variance_dual_stdGaussian
-/
lemma charFunDual_stdGaussian (L : StrongDual Real E) :
    charFunDual (stdGaussian E) L = exp (- ‖L‖ ^ 2 / 2) := by
  simp [IsGaussian.charFunDual_eq, integral_complex_ofReal, variance_dual_stdGaussian, neg_div]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `covarianceBilin_stdGaussian` / 引理 `covarianceBilin_stdGaussian`

English:
lemma covarianceBilin_stdGaussian
  proof: by
.2.symm refine gaussian_charFun_congr 0 _ ?_ ?_
  · exact LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

中文:
引理 covarianceBilin_stdGaussian
  证明: by
.2.symm refine gaussian_charFun_congr 0 _ ?_ ?_
  · exact LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.isPosSemidef_iff, charFun_stdGaussian, gaussian_charFun_congr, innerSL_apply_apply, isPosSemidef_iff, isPosSemidef_inner, neg_div
-/
lemma covarianceBilin_stdGaussian :
    covarianceBilin (stdGaussian E) = innerSL Real := by
.2.symm refine gaussian_charFun_congr 0 _ ?_ ?_
  · exact LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div, innerSL_apply_apply Real]

/--
lemma `stdGaussian_map` / 引理 `stdGaussian_map`

English:
lemma stdGaussian_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F] [MeasurableSpace F]
  proof: f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [show ⇑f = f.toContinuousLinearEquiv.toContinuousLinearMap from rfl, charFunDual_map,
    charFunDual_stdGaussian, L.opNorm_comp_linearIsometryEquiv]

中文:
引理 stdGaussian_map
  结论: {F : 类型} [NormedAddCommGroup F] [InnerProductSpace 实数 F] [MeasurableSpace F]
  证明: f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [show ⇑f = f.toContinuousLinearEquiv.toContinuousLinearMap from rfl, charFunDual_map,
    charFunDual_stdGaussian, L.opNorm_comp_linearIsometryEquiv]

Depends on / 依赖: L.opNorm_comp_linearIsometryEquiv, Measure, Measure.ext_of_charFunDual, charFunDual_map, charFunDual_stdGaussian, ext_of_charFunDual, f.finiteDimensional, f.toContinuousLinearEquiv.toContinuousLinearMap, finiteDimensional, opNorm_comp_linearIsometryEquiv, simp_rw, stdGaussian, toContinuousLinearEquiv, toContinuousLinearMap
-/
lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[Real] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [show ⇑f = f.toContinuousLinearEquiv.toContinuousLinearMap from rfl, charFunDual_map,
    charFunDual_stdGaussian, L.opNorm_comp_linearIsometryEquiv]

/--
lemma `map_pi_eq_stdGaussian` / 引理 `map_pi_eq_stdGaussian`

English:
lemma map_pi_eq_stdGaussian
  proof: by
  apply Measure.ext_of_charFun (E := EuclideanSpace Real ι)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← exp_sum, ← ofReal_pow,
    EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

中文:
引理 map_pi_eq_stdGaussian
  证明: by
  apply Measure.ext_of_charFun (E := EuclideanSpace Real ι)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← exp_sum, ← ofReal_pow,
    EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.real_norm_sq_eq, Finset, Finset.sum_div, Measure, Measure.ext_of_charFun, charFun_gaussianReal, charFun_pi, charFun_stdGaussian, exp_sum, ext_of_charFun, neg_div, ofReal_pow, real_norm_sq_eq, simp_rw, sum_div
-/
lemma map_pi_eq_stdGaussian :
    (Measure.pi (fun _ => gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace Real ι) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace Real ι)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← exp_sum, ← ofReal_pow,
    EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

/--
lemma `stdGaussian_eq_map_pi_orthonormalBasis` / 引理 `stdGaussian_eq_map_pi_orthonormalBasis`

English:
lemma stdGaussian_eq_map_pi_orthonormalBasis
  given: (b : OrthonormalBasis ι Real E)
  proof: by
  have : (fun (x : ι -> Real) => ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι Real).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this]; rw [← Measure.map_map]; rw [map_pi_eq_stdGaussian]; rw [stdGaussian_map]
  all_goals fun_prop

中文:
引理 stdGaussian_eq_map_pi_orthonormalBasis
  条件: (b : OrthonormalBasis ι 实数 E)
  证明: by
  have : (fun (x : ι -> Real) => ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι Real).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this]; rw [← Measure.map_map]; rw [map_pi_eq_stdGaussian]; rw [stdGaussian_map]
  all_goals fun_prop

Depends on / 依赖: Equiv.refl, EuclideanSpace, EuclideanSpace.basisFun, Measure, Measure.map_map, all_goals, b.equiv_apply_euclideanSpace, basisFun, equiv_apply_euclideanSpace, fun_prop, map_map, map_pi_eq_stdGaussian, simp_rw, stdGaussian_map
-/
lemma stdGaussian_eq_map_pi_orthonormalBasis (b : OrthonormalBasis ι Real E) :
    stdGaussian E = (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i, x i • b i) := by
  have : (fun (x : ι -> Real) => ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι Real).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this]; rw [← Measure.map_map]; rw [map_pi_eq_stdGaussian]; rw [stdGaussian_map]
  all_goals fun_prop

end stdGaussian

section multivariateGaussian

/-! ### Multivariate Gaussian measures over `ℝⁿ` -/

variable [DecidableEq ι]

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. This only makes sense when `S` is positive semidefinite,
as then `CFC.sqrt S * CFC.sqrt S = S`. Otherwise `CFC.sqrt S = 0`, and
`multivariateGaussian μ S = Measure.dirac μ` (see `multivariateGaussian_of_not_posSemidef`). -/
noncomputable
/--
Definition of `multivariateGaussian` / `multivariateGaussian` 的定义

English:
definition multivariateGaussian
  signature: (μ : EuclideanSpace Real ι) (S : Matrix ι ι Real)
  body: (stdGaussian (EuclideanSpace Real ι)).map (fun x => μ + toEuclideanCLM (𝕜 := Real) (CFC.sqrt S) x)

中文:
定义 multivariateGaussian
  签名: (μ : EuclideanSpace 实数 ι) (S : Matrix ι ι 实数)
  定义体: (stdGaussian (EuclideanSpace Real ι)).map (fun x => μ + toEuclideanCLM (𝕜 := Real) (CFC.sqrt S) x)

Depends on / 依赖: CFC.sqrt, EuclideanSpace, stdGaussian, toEuclideanCLM
-/
def multivariateGaussian (μ : EuclideanSpace Real ι) (S : Matrix ι ι Real) :
    Measure (EuclideanSpace Real ι) :=
  (stdGaussian (EuclideanSpace Real ι)).map (fun x => μ + toEuclideanCLM (𝕜 := Real) (CFC.sqrt S) x)

/--
lemma `multivariateGaussian_of_not_posSemidef` / 引理 `multivariateGaussian_of_not_posSemidef`

English:
lemma multivariateGaussian_of_not_posSemidef
  statement: (μ : EuclideanSpace Real ι) {S : Matrix ι ι Real}
  proof: by
  rw [multivariateGaussian]; rw [CFC.sqrt]; rw [cfcₙ_apply_of_not_predicate]
  · simp
  change ¬ (S - 0).PosSemidef
  simpa

@[simp]

中文:
引理 multivariateGaussian_of_not_posSemidef
  结论: (μ : EuclideanSpace 实数 ι) {S : Matrix ι ι 实数}
  证明: by
  rw [multivariateGaussian]; rw [CFC.sqrt]; rw [cfcₙ_apply_of_not_predicate]
  · simp
  change ¬ (S - 0).PosSemidef
  simpa

@[simp]

Depends on / 依赖: CFC.sqrt, PosSemidef, multivariateGaussian
-/
lemma multivariateGaussian_of_not_posSemidef (μ : EuclideanSpace Real ι) {S : Matrix ι ι Real}
    (hS : ¬ S.PosSemidef) : multivariateGaussian μ S = .dirac μ := by
  rw [multivariateGaussian]; rw [CFC.sqrt]; rw [cfcₙ_apply_of_not_predicate]
  · simp
  change ¬ (S - 0).PosSemidef
  simpa

@[simp]
/--
lemma `multivariateGaussian_zero_one` / 引理 `multivariateGaussian_zero_one`

English:
lemma multivariateGaussian_zero_one
  proof: by
  simp [multivariateGaussian]

中文:
引理 multivariateGaussian_zero_one
  证明: by
  simp [multivariateGaussian]

Depends on / 依赖: multivariateGaussian
-/
lemma multivariateGaussian_zero_one :
    multivariateGaussian 0 (1 : Matrix ι ι Real) = stdGaussian (EuclideanSpace Real ι) := by
  simp [multivariateGaussian]

variable {μ : EuclideanSpace Real ι} {S : Matrix ι ι Real}

/--
Instance `isGaussian_multivariateGaussian` / 实例 `isGaussian_multivariateGaussian`

English:
instance isGaussian_multivariateGaussian
  signature: : IsGaussian (multivariateGaussian μ S)
  body: by
  have h : (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) =
    (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) := rfl
  simp only [multivariateGaussian]
  rw [h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  infer_instance

@[simp]

中文:
实例 isGaussian_multivariateGaussian
  签名: : IsGaussian (multivariateGaussian μ S)
  定义体: by
  have h : (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) =
    (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) := rfl
  simp only [multivariateGaussian]
  rw [h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  infer_instance

@[simp]

Depends on / 依赖: CFC.sqrt, Measure, Measure.map_map, fun_prop, infer_instance, map_map, measurable_const_add, multivariateGaussian, toEuclideanCLM
-/
instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) =
    (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) := rfl
  simp only [multivariateGaussian]
  rw [h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  infer_instance

@[simp]
/--
lemma `integral_id_multivariateGaussian` / 引理 `integral_id_multivariateGaussian`

English:
lemma integral_id_multivariateGaussian
  statement: ∫ x, x ∂(multivariateGaussian μ S) = μ
  proof: by
  rw [multivariateGaussian]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_add (integrable_const _)]; rw [integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

中文:
引理 integral_id_multivariateGaussian
  结论: ∫ x, x ∂(multivariateGaussian μ S) = μ
  证明: by
  rw [multivariateGaussian]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_add (integrable_const _)]; rw [integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, IsGaussian, IsGaussian.integrable_fun_id, IsGaussian.integrable_id.comp_measurable, comp_measurable, fun_prop, integrable_const, integrable_fun_id, integrable_id, integral_add, integral_comp_comm, integral_const, integral_map, multivariateGaussian
-/
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [integral_add (integrable_const _)]; rw [integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

/--
lemma `integral_id_multivariateGaussian'` / 引理 `integral_id_multivariateGaussian'`

English:
lemma integral_id_multivariateGaussian'
  statement: (multivariateGaussian μ S)[id] = μ
  proof: by simp

中文:
引理 integral_id_multivariateGaussian'
  结论: (multivariateGaussian μ S)[id] = μ
  证明: by simp
-/
lemma integral_id_multivariateGaussian' : (multivariateGaussian μ S)[id] = μ := by simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `covarianceBilin_multivariateGaussian` / 引理 `covarianceBilin_multivariateGaussian`

English:
lemma covarianceBilin_multivariateGaussian
  given: (hS : S.PosSemidef) (x y : EuclideanSpace Real ι)
  proof: by
  have h : (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) =
    (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]; rw [covarianceBilin_map_const_add]; rw [c

中文:
引理 covarianceBilin_multivariateGaussian
  条件: (hS : S.PosSemidef) (x y : EuclideanSpace 实数 ι)
  证明: by
  have h : (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) =
    (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]; rw [covarianceBilin_map_const_add]; rw [c

Depends on / 依赖: CFC.sqrt, Continuo, ContinuousLinearMap, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, IsSelfAdjoint, IsSelfAdjoint.adjoint_eq, Measure, Measure.map_map, adjoint_eq, adjoint_inner_left, comp_apply, covarianceBilin_map, covarianceBilin_map_const_add, covarianceBilin_stdGaussian, fun_prop, innerSL_apply_apply, map_map, measurable_const_add, multivariateGaussian
-/
lemma covarianceBilin_multivariateGaussian (hS : S.PosSemidef) (x y : EuclideanSpace Real ι) :
    covarianceBilin (multivariateGaussian μ S) x y = x ⬝ᵥ S *ᵥ y := by
  have h : (fun x => μ + x) ∘ ((toEuclideanCLM (𝕜 := Real) (CFC.sqrt S))) =
    (fun x => μ + (toEuclideanCLM (𝕜 := Real) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h]; rw [← Measure.map_map (measurable_const_add μ) (by fun_prop)]; rw [covarianceBilin_map_const_add]; rw [covarianceBilin_map]; rw [covarianceBilin_stdGaussian]; rw [innerSL_apply_apply]; rw [ContinuousLinearMap.adjoint_inner_left]; rw [IsSelfAdjoint.adjoint_eq]; rw [← ContinuousLinearMap.comp_apply]; rw [← ContinuousLinearMap.mul_def]; rw [← map_mul]; rw [CFC.sqrt_mul_sqrt_self _ hS.nonneg]; rw [inner_toEuclideanCLM]
  · exact (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  · exact IsGaussian.memLp_two_id

/--
lemma `covariance_eval_multivariateGaussian` / 引理 `covariance_eval_multivariateGaussian`

English:
lemma covariance_eval_multivariateGaussian
  given: (hS : S.PosSemidef) (i j : ι)
  proof: by
  have (i : ι) : (fun x : EuclideanSpace Real ι => x i) =
      fun x => ⟪EuclideanSpace.basisFun ι Real i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this]; rw [this]; rw [← covarianceBilin_apply_eq_cov]; rw [covarianceBilin_multivariateGaussian hS]
  · simp
  · exact IsGaussian.memLp_two_id

中文:
引理 covariance_eval_multivariateGaussian
  条件: (hS : S.PosSemidef) (i j : ι)
  证明: by
  have (i : ι) : (fun x : EuclideanSpace Real ι => x i) =
      fun x => ⟪EuclideanSpace.basisFun ι Real i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this]; rw [this]; rw [← covarianceBilin_apply_eq_cov]; rw [covarianceBilin_multivariateGaussian hS]
  · simp
  · exact IsGaussian.memLp_two_id

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, IsGaussian, IsGaussian.memLp_two_id, PiLp.inner_apply, basisFun, covarianceBilin_apply_eq_cov, covarianceBilin_multivariateGaussian, inner_apply, memLp_two_id
-/
lemma covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) :
    cov[fun x => x i, fun x => x j; multivariateGaussian μ S] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace Real ι => x i) =
      fun x => ⟪EuclideanSpace.basisFun ι Real i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this]; rw [this]; rw [← covarianceBilin_apply_eq_cov]; rw [covarianceBilin_multivariateGaussian hS]
  · simp
  · exact IsGaussian.memLp_two_id

/--
lemma `variance_eval_multivariateGaussian` / 引理 `variance_eval_multivariateGaussian`

English:
lemma variance_eval_multivariateGaussian
  given: (hS : S.PosSemidef) (i : ι)
  proof: by
  rw [← covariance_self]; rw [covariance_eval_multivariateGaussian hS]
exact Measurable.aemeasurable by fun_prop

中文:
引理 variance_eval_multivariateGaussian
  条件: (hS : S.PosSemidef) (i : ι)
  证明: by
  rw [← covariance_self]; rw [covariance_eval_multivariateGaussian hS]
exact Measurable.aemeasurable by fun_prop

Depends on / 依赖: Measurable, Measurable.aemeasurable, aemeasurable, covariance_eval_multivariateGaussian, covariance_self, fun_prop
-/
lemma variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    Var[fun x => x i; multivariateGaussian μ S] = S i i := by
  rw [← covariance_self]; rw [covariance_eval_multivariateGaussian hS]
exact Measurable.aemeasurable by fun_prop

/--
lemma `measurePreserving_eval_multivariateGaussian` / 引理 `measurePreserving_eval_multivariateGaussian`

English:
lemma measurePreserving_eval_multivariateGaussian
  given: (hS : S.PosSemidef) {i : ι}
  proof: by fun_prop
  map_eq := by
    rw [← EuclideanSpace.coe_proj]; rw [IsGaussian.map_eq_gaussianReal]; rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

中文:
引理 measurePreserving_eval_multivariateGaussian
  条件: (hS : S.PosSemidef) {i : ι}
  证明: by fun_prop
  map_eq := by
    rw [← EuclideanSpace.coe_proj]; rw [IsGaussian.map_eq_gaussianReal]; rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_id_comm, EuclideanSpace, EuclideanSpace.coe_proj, IsGaussian, IsGaussian.integrable_id, IsGaussian.map_eq_gaussianReal, coe_proj, fun_prop, integrable_id, integral_comp_id_comm, map_eq, map_eq_gaussianReal, variance_eval_multivariateGaussian
-/
lemma measurePreserving_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    MeasurePreserving (fun x => x i) (multivariateGaussian μ S)
      (gaussianReal (μ i) (S i i).toNNReal) where
  measurable := by fun_prop
  map_eq := by
    rw [← EuclideanSpace.coe_proj]; rw [IsGaussian.map_eq_gaussianReal]; rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

/--
lemma `charFun_multivariateGaussian` / 引理 `charFun_multivariateGaussian`

English:
lemma charFun_multivariateGaussian
  given: (hS : S.PosSemidef) (x : EuclideanSpace Real ι)
  proof: by
  simp [IsGaussian.charFun_eq', covarianceBilin_multivariateGaussian hS]

中文:
引理 charFun_multivariateGaussian
  条件: (hS : S.PosSemidef) (x : EuclideanSpace 实数 ι)
  证明: by
  simp [IsGaussian.charFun_eq', covarianceBilin_multivariateGaussian hS]

Depends on / 依赖: IsGaussian, IsGaussian.charFun_eq, charFun_eq, covarianceBilin_multivariateGaussian
-/
lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace Real ι) :
    charFun (multivariateGaussian μ S) x =
      exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2) := by
  simp [IsGaussian.charFun_eq', covarianceBilin_multivariateGaussian hS]

/--
lemma `measurePreserving_restrict₂_multivariateGaussian` / 引理 `measurePreserving_restrict₂_multivariateGaussian`

English:
lemma measurePreserving_restrict₂_multivariateGaussian
  statement: {ι : Type*} [DecidableEq ι] {I J : Finset ι}
  proof: by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map]; rw [integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap

中文:
引理 measurePreserving_restrict₂_multivariateGaussian
  结论: {ι : 类型} [DecidableEq ι] {I J : Finset ι}
  证明: by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map]; rw [integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap

Depends on / 依赖: BilinForm, ContinuousLinearMap, ContinuousLinearMap.integral_id_map, ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_inj, EuclideanSpace, EuclideanSpace.basisFun, IsGaussian, IsGaussian.ext, IsGaussian.integrable_id, LinearMap, LinearMap.BilinForm.ext_basis, basisFun, covarianceBilin_apply_eq_cov, covariance_map, ext_basis, fun_prop, id_eq, integrable_id, integral_id_map
-/
lemma measurePreserving_restrict₂_multivariateGaussian {ι : Type*} [DecidableEq ι] {I J : Finset ι}
    {μ : EuclideanSpace Real I} {S : Matrix I I Real} (hS : S.PosSemidef) (hJI : J subseteq I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI) (multivariateGaussian μ S)
      (multivariateGaussian (μ.restrict₂ hJI)
        (S.submatrix (fun i : J => ⟨i.1, hJI i.2⟩) (fun i : J => ⟨i.1, hJI i.2⟩))) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map]; rw [integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J Real).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply]; rw [ContinuousLinearMap.toBilinForm_apply]; rw [covarianceBilin_apply_eq_cov]; rw [covariance_map]
    · have (i : J) : (fun u => ⟪(EuclideanSpace.basisFun J Real).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u => u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

end multivariateGaussian

end ProbabilityTheory
