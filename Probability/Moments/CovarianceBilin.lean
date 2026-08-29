/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# Covariance in Hilbert spaces

Given a measure `μ` defined over a Banach space `E`, one can consider the associated covariance
bilinear form which maps `L₁ L₂ : StrongDual ℝ E` to `cov[L₁, L₂; μ]`. This is called
`covarianceBilinDual μ` and is defined in the `CovarianceBilinDual` file.

In the special case where `E` is a Hilbert space, each `L : StrongDual ℝ E` can be represented
as the scalar product against some element of `E`. This motivates the definition of
`covarianceBilin`, which is a continuous bilinear form mapping `x y : E` to
`cov[⟪x, ·⟫, ⟪y, ·⟫; μ]`.

## Main definitions

* `covarianceBilin μ`: the continuous bilinear form over `E` representing the covariance of a
  measure over `E`.
* `covarianceOperator μ`: the bounded operator over `E` such that
  `⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ`.

## Tags

covariance, Hilbert space, bilinear form
-/

@[expose] public section

open MeasureTheory InnerProductSpace NormedSpace WithLp EuclideanSpace
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
/--
Definition of `covarianceBilin` / `covarianceBilin` 的定义

English:
definition covarianceBilin
  signature: (μ : Measure E)
  body: ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

中文:
定义 covarianceBilin
  签名: (μ : 测度 E)
  定义体: ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bilinearComp, bilinearComp, covarianceBilinDual, toContinuousLinearMap, toDualMap
-/
def covarianceBilin (μ : Measure E) : E ->L[Real] E ->L[Real] Real :=
  ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `covarianceBilin_zero` / 引理 `covarianceBilin_zero`

English:
lemma covarianceBilin_zero
  statement: covarianceBilin (0 : Measure E) = 0
  proof: by
  rw [covarianceBilin]
  simp

中文:
引理 covarianceBilin_zero
  结论: covarianceBilin (0 : 测度 E) = 0
  证明: by
  rw [covarianceBilin]
  simp

Depends on / 依赖: covarianceBilin
-/
lemma covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0 := by
  rw [covarianceBilin]
  simp

/--
lemma `covarianceBilin_eq_covarianceBilinDual` / 引理 `covarianceBilin_eq_covarianceBilinDual`

English:
lemma covarianceBilin_eq_covarianceBilinDual
  given: (x y : E)
  proof: rfl

@[simp]

中文:
引理 covarianceBilin_eq_covarianceBilinDual
  条件: (x y : E)
  证明: rfl

@[simp]
-/
lemma covarianceBilin_eq_covarianceBilinDual (x y : E) :
    covarianceBilin μ x y = covarianceBilinDual μ (toDualMap Real E x) (toDualMap Real E y) := rfl

@[simp]
/--
lemma `covarianceBilin_of_not_memLp` / 引理 `covarianceBilin_of_not_memLp`

English:
lemma covarianceBilin_of_not_memLp
  given: (h : ¬MemLp id 2 μ)
  proof: by
  ext
  simp [covarianceBilin_eq_covarianceBilinDual, h]

中文:
引理 covarianceBilin_of_not_memLp
  条件: (h : ¬MemLp id 2 μ)
  证明: by
  ext
  simp [covarianceBilin_eq_covarianceBilinDual, h]

Depends on / 依赖: covarianceBilin_eq_covarianceBilinDual
-/
lemma covarianceBilin_of_not_memLp (h : ¬MemLp id 2 μ) :
    covarianceBilin μ = 0 := by
  ext
  simp [covarianceBilin_eq_covarianceBilinDual, h]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `covarianceBilin_apply` / 引理 `covarianceBilin_apply`

English:
lemma covarianceBilin_apply
  given: [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E)
  proof: by
  simp [covarianceBilin, covarianceBilinDual_apply' h]

中文:
引理 covarianceBilin_apply
  条件: [完备空间 E] [是有限测度 μ] (h : MemLp id 2 μ) (x y : E)
  证明: by
  simp [covarianceBilin, covarianceBilinDual_apply' h]

Depends on / 依赖: covarianceBilin, covarianceBilinDual_apply
-/
lemma covarianceBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y, z - μ[id]⟫ ∂μ := by
  simp [covarianceBilin, covarianceBilinDual_apply' h]

/--
lemma `covarianceBilin_comm` / 引理 `covarianceBilin_comm`

English:
lemma covarianceBilin_comm
  given: (x y : E)
  proof: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_comm]; rw [covarianceBilin_eq_covarianceBilinDual]

中文:
引理 covarianceBilin_comm
  条件: (x y : E)
  证明: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_comm]; rw [covarianceBilin_eq_covarianceBilinDual]

Depends on / 依赖: covarianceBilinDual_comm, covarianceBilin_eq_covarianceBilinDual
-/
lemma covarianceBilin_comm (x y : E) :
    covarianceBilin μ x y = covarianceBilin μ y x := by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_comm]; rw [covarianceBilin_eq_covarianceBilinDual]

/--
lemma `covarianceBilin_self` / 引理 `covarianceBilin_self`

English:
lemma covarianceBilin_self
  given: [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E)
  proof: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_self_eq_variance h]
  rfl

中文:
引理 covarianceBilin_self
  条件: [完备空间 E] [是有限测度 μ] (h : MemLp id 2 μ) (x : E)
  证明: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_self_eq_variance h]
  rfl

Depends on / 依赖: covarianceBilinDual_self_eq_variance, covarianceBilin_eq_covarianceBilinDual
-/
lemma covarianceBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    covarianceBilin μ x x = Var[fun u => ⟪x, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_self_eq_variance h]
  rfl

/--
lemma `covarianceBilin_apply_eq_cov` / 引理 `covarianceBilin_apply_eq_cov`

English:
lemma covarianceBilin_apply_eq_cov
  statement: [CompleteSpace E] [IsFiniteMeasure μ]
  proof: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_eq_covariance h]
  rfl

中文:
引理 covarianceBilin_apply_eq_cov
  结论: [完备空间 E] [是有限测度 μ]
  证明: by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_eq_covariance h]
  rfl

Depends on / 依赖: covarianceBilinDual_eq_covariance, covarianceBilin_eq_covarianceBilinDual
-/
lemma covarianceBilin_apply_eq_cov [CompleteSpace E] [IsFiniteMeasure μ]
    (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = cov[fun u => ⟪x, u⟫, fun u => ⟪y, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual]; rw [covarianceBilinDual_eq_covariance h]
  rfl

/--
lemma `covarianceBilin_real` / 引理 `covarianceBilin_real`

English:
lemma covarianceBilin_real
  given: {μ : Measure Real} [IsFiniteMeasure μ] (x y : Real)
  proof: by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilin_apply_eq_cov h, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [← mul_assoc]; rw [covariance_self aemeasurable_id']; rw [Function.id_def]
  · simp [h, variance_of_not_me

中文:
引理 covarianceBilin_real
  条件: {μ : 测度 实数} [是有限测度 μ] (x y : 实数)
  证明: by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilin_apply_eq_cov h, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [← mul_assoc]; rw [covariance_self aemeasurable_id']; rw [Function.id_def]
  · simp [h, variance_of_not_me

Depends on / 依赖: Function, Function.id_def, RCLike, RCLike.inner_apply, aemeasurable_id, aestronglyMeasurable_id, conj_trivial, covarianceBilin_apply_eq_cov, covariance_const_mul_left, covariance_const_mul_right, covariance_self, id_def, inner_apply, mul_assoc, mul_comm, variance_of_not_memLp
-/
lemma covarianceBilin_real {μ : Measure Real} [IsFiniteMeasure μ] (x y : Real) :
    covarianceBilin μ x y = x * y * Var[id; μ] := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilin_apply_eq_cov h, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [← mul_assoc]; rw [covariance_self aemeasurable_id']; rw [Function.id_def]
  · simp [h, variance_of_not_memLp, aestronglyMeasurable_id]

/--
lemma `covarianceBilin_real_self` / 引理 `covarianceBilin_real_self`

English:
lemma covarianceBilin_real_self
  given: {μ : Measure Real} [IsFiniteMeasure μ] (x : Real)
  proof: by
  rw [covarianceBilin_real]; rw [pow_two]

中文:
引理 covarianceBilin_real_self
  条件: {μ : 测度 实数} [是有限测度 μ] (x : 实数)
  证明: by
  rw [covarianceBilin_real]; rw [pow_two]

Depends on / 依赖: covarianceBilin_real, pow_two
-/
lemma covarianceBilin_real_self {μ : Measure Real} [IsFiniteMeasure μ] (x : Real) :
    covarianceBilin μ x x = x ^ 2 * Var[id; μ] := by
  rw [covarianceBilin_real]; rw [pow_two]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `covarianceBilin_self_nonneg` / 引理 `covarianceBilin_self_nonneg`

English:
lemma covarianceBilin_self_nonneg
  given: (x : E)
  proof: by
  simp [covarianceBilin]

中文:
引理 covarianceBilin_self_nonneg
  条件: (x : E)
  证明: by
  simp [covarianceBilin]

Depends on / 依赖: covarianceBilin
-/
lemma covarianceBilin_self_nonneg (x : E) :
    0 <= covarianceBilin μ x x := by
  simp [covarianceBilin]

/--
lemma `isPosSemidef_covarianceBilin` / 引理 `isPosSemidef_covarianceBilin`

English:
lemma isPosSemidef_covarianceBilin
  proof: covarianceBilin_comm
  nonneg := covarianceBilin_self_nonneg

中文:
引理 isPosSemidef_covarianceBilin
  证明: covarianceBilin_comm
  nonneg := covarianceBilin_self_nonneg

Depends on / 依赖: covarianceBilin_comm
-/
lemma isPosSemidef_covarianceBilin :
    (covarianceBilin μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilin_comm
  nonneg := covarianceBilin_self_nonneg

/--
lemma `covarianceBilin_map` / 引理 `covarianceBilin_map`

English:
lemma covarianceBilin_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: by
  rw [covarianceBilin_apply]; rw [covarianceBilin_apply h]
  · simp_rw [id, L.integral_id_map (h.integrable (by simp))]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
.2 (L.comp_memLp' h) · exact memLp_map_measure_iff (by fun_prop) (by fun_prop)

中文:
引理 covarianceBilin_map
  结论: {F : 类型} [赋范交换加群 F] [内积空间 实数 F]
  证明: by
  rw [covarianceBilin_apply]; rw [covarianceBilin_apply h]
  · simp_rw [id, L.integral_id_map (h.integrable (by simp))]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
.2 (L.comp_memLp' h) · exact memLp_map_measure_iff (by fun_prop) (by fun_prop)

Depends on / 依赖: L.adjoint_inner_left, L.comp_memLp, L.integral_id_map, adjoint_inner_left, all_goals, comp_memLp, covarianceBilin_apply, fun_prop, h.integrable, integrable, integral_id_map, integral_map, map_sub, memLp_map_measure_iff, simp_rw
-/
lemma covarianceBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]
    [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E ->L[Real] F) (u v : F) :
    covarianceBilin (μ.map L) u v = covarianceBilin μ (L.adjoint u) (L.adjoint v) := by
  rw [covarianceBilin_apply]; rw [covarianceBilin_apply h]
  · simp_rw [id, L.integral_id_map (h.integrable (by simp))]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
.2 (L.comp_memLp' h) · exact memLp_map_measure_iff (by fun_prop) (by fun_prop)

/--
lemma `covarianceBilin_map_const_add` / 引理 `covarianceBilin_map_const_add`

English:
lemma covarianceBilin_map_const_add
  given: [CompleteSpace E] [IsProbabilityMeasure μ] (c : E)
  proof: by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x => c + x)) :=
(measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr (memLp_const c).add h
    rw [covarianceBilin_apply h_Lp]; rw [covarianceBilin_apply h]; rw [integral_map (by fun_prop) (by fun_prop)]
    congr

中文:
引理 covarianceBilin_map_const_add
  条件: [完备空间 E] [是概率测度 μ] (c : E)
  证明: by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x => c + x)) :=
(measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr (memLp_const c).add h
    rw [covarianceBilin_apply h_Lp]; rw [covarianceBilin_apply h]; rw [integral_map (by fun_prop) (by fun_prop)]
    congr

Depends on / 依赖: covarianceBilin_apply, covarianceBilin_of_not_memLp, fun_prop, h.integrable, h_Lp, id_eq, integrable, integrable_const, integral_add, integral_map, measurableEmbedding_addLeft, memLp_const, memLp_map_measure_iff, memLp_map_measure_iff.mpr
-/
lemma covarianceBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    covarianceBilin (μ.map (fun x => c + x)) = covarianceBilin μ := by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x => c + x)) :=
(measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr (memLp_const c).add h
    rw [covarianceBilin_apply h_Lp]; rw [covarianceBilin_apply h]; rw [integral_map (by fun_prop) (by fun_prop)]
    congr with z
    rw [integral_map (by fun_prop) h_Lp.1]
    simp only [id_eq]
    rw [integral_add (integrable_const _)]
    · simp
    · exact h.integrable (by simp)
  · ext
    rw [covarianceBilin_of_not_memLp]; rw [covarianceBilin_of_not_memLp h]
    rw [(measurableEmbedding_addLeft _).memLp_map_measure_iff.not]
    contrapose h
    convert! (memLp_const (-c)).add h
    ext; simp

/--
lemma `covarianceBilin_apply_basisFun` / 引理 `covarianceBilin_apply_basisFun`

English:
lemma covarianceBilin_apply_basisFun
  statement: {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  proof: by
  have (i : ι) := (hX i).aemeasurable
  rw [covarianceBilin_apply_eq_cov]; rw [covariance_map]
  · simp [basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMea

中文:
引理 covarianceBilin_apply_basisFun
  结论: {ι Ω : 类型} [有限类型 ι] {mΩ : 可测空间 Ω}
  证明: by
  have (i : ι) := (hX i).aemeasurable
  rw [covarianceBilin_apply_eq_cov]; rw [covariance_map]
  · simp [basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMea

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, MemLp.of_eval_piLp, aemeasurable, aestronglyMeasurable, aestronglyMeasurable_id, basisFun_inner, covarianceBilin_apply_eq_cov, covariance_map, fun_prop, memLp_map_measure_iff, of_eval_piLp
-/
lemma covarianceBilin_apply_basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real} (hX : forall i, MemLp (X i) 2 μ) (i j : ι) :
    covarianceBilin (μ.map (fun ω => toLp 2 (X · ω)))
      (basisFun ι Real i) (basisFun ι Real j) = cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  rw [covarianceBilin_apply_eq_cov]; rw [covariance_map]
  · simp [basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

/--
lemma `covarianceBilin_apply_basisFun_self` / 引理 `covarianceBilin_apply_basisFun_self`

English:
lemma covarianceBilin_apply_basisFun_self
  statement: {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  proof: by
  rw [covarianceBilin_apply_basisFun hX]; rw [covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop

中文:
引理 covarianceBilin_apply_basisFun_self
  结论: {ι Ω : 类型} [有限类型 ι] {mΩ : 可测空间 Ω}
  证明: by
  rw [covarianceBilin_apply_basisFun hX]; rw [covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop

Depends on / 依赖: aemeasurable, covarianceBilin_apply_basisFun, covariance_self, fun_prop
-/
lemma covarianceBilin_apply_basisFun_self {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real} (hX : forall i, MemLp (X i) 2 μ) (i : ι) :
    covarianceBilin (μ.map (fun ω => toLp 2 (X · ω)))
      (basisFun ι Real i) (basisFun ι Real i) = Var[X i; μ] := by
  rw [covarianceBilin_apply_basisFun hX]; rw [covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop

/--
lemma `covarianceBilin_apply_pi` / 引理 `covarianceBilin_apply_pi`

English:
lemma covarianceBilin_apply_pi
  statement: {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  proof: by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun, ← (basisFun ι Real).sum_repr' x,
    ← (basisFun ι Real).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, basisFun_inner]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr

中文:
引理 covarianceBilin_apply_pi
  结论: {ι Ω : 类型} [有限类型 ι] {mΩ : 可测空间 Ω}
  证明: by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun, ← (basisFun ι Real).sum_repr' x,
    ← (basisFun ι Real).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, basisFun_inner]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr

Depends on / 依赖: Finset, Finset.sum_congr, Measurable, Measurable.aestronglyMeasurable, aemeasurable, aestronglyMeasurable, all_goals, any_goals, basisFun, basisFun_inner, const_mul, covarianceBilin_apply_eq_cov, covariance_const_mul_left, covariance_const_mul_right, covariance_fun_sum_fun_sum, covariance_map_fun, nth_rw, real_inner_smul_left, simp_rw, sum_congr
-/
lemma covarianceBilin_apply_pi {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real}
    (hX : forall i, MemLp (X i) 2 μ) (x y : EuclideanSpace Real ι) :
    covarianceBilin (μ.map (fun ω => toLp 2 (X · ω))) x y =
      ∑ i, ∑ j, x i * y j * cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun, ← (basisFun ι Real).sum_repr' x,
    ← (basisFun ι Real).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, basisFun_inner]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [covariance_const_mul_left]; rw [covariance_const_mul_right]
      ring
    all_goals exact fun i => (hX i).const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

section covarianceOperator

variable [CompleteSpace E]

/--
Definition of `covarianceOperator` / `covarianceOperator` 的定义

English:
definition covarianceOperator
  signature: (μ : Measure E)
  body: continuousLinearMapOfBilin ContinuousLinearMap.bilinearComp (uncenteredCovarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

中文:
定义 covarianceOperator
  签名: (μ : 测度 E)
  定义体: continuousLinearMapOfBilin ContinuousLinearMap.bilinearComp (uncenteredCovarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bilinearComp, bilinearComp, continuousLinearMapOfBilin, toContinuousLinearMap, toDualMap, uncenteredCovarianceBilinDual
-/
noncomputable def covarianceOperator (μ : Measure E) : E ->L[Real] E :=
continuousLinearMapOfBilin ContinuousLinearMap.bilinearComp (uncenteredCovarianceBilinDual μ)
    (toDualMap Real E).toContinuousLinearMap (toDualMap Real E).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `covarianceOperator_zero` / 引理 `covarianceOperator_zero`

English:
lemma covarianceOperator_zero
  statement: covarianceOperator (0 : Measure E) = 0
  proof: by
  simp [covarianceOperator]

中文:
引理 covarianceOperator_zero
  结论: covarianceOperator (0 : 测度 E) = 0
  证明: by
  simp [covarianceOperator]

Depends on / 依赖: covarianceOperator
-/
lemma covarianceOperator_zero : covarianceOperator (0 : Measure E) = 0 := by
  simp [covarianceOperator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `covarianceOperator_of_not_memLp` / 引理 `covarianceOperator_of_not_memLp`

English:
lemma covarianceOperator_of_not_memLp
  given: (hμ : ¬MemLp id 2 μ)
  proof: by
  ext x
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  simp [hμ, uncenteredCovarianceBilinDual_of_not_memLp]

中文:
引理 covarianceOperator_of_not_memLp
  条件: (hμ : ¬MemLp id 2 μ)
  证明: by
  ext x
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  simp [hμ, uncenteredCovarianceBilinDual_of_not_memLp]

Depends on / 依赖: uncenteredCovarianceBilinDual_of_not_memLp, unique_continuousLinearMapOfBilin
-/
lemma covarianceOperator_of_not_memLp (hμ : ¬MemLp id 2 μ) :
    covarianceOperator μ = 0 := by
  ext x
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  simp [hμ, uncenteredCovarianceBilinDual_of_not_memLp]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `covarianceOperator_inner` / 引理 `covarianceOperator_inner`

English:
lemma covarianceOperator_inner
  given: (hμ : MemLp id 2 μ) (x y : E)
  proof: by
  simp [covarianceOperator, uncenteredCovarianceBilinDual_apply hμ]

中文:
引理 covarianceOperator_inner
  条件: (hμ : MemLp id 2 μ) (x y : E)
  证明: by
  simp [covarianceOperator, uncenteredCovarianceBilinDual_apply hμ]

Depends on / 依赖: covarianceOperator, uncenteredCovarianceBilinDual_apply
-/
lemma covarianceOperator_inner (hμ : MemLp id 2 μ) (x y : E) :
    ⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ := by
  simp [covarianceOperator, uncenteredCovarianceBilinDual_apply hμ]

/--
lemma `covarianceOperator_apply` / 引理 `covarianceOperator_apply`

English:
lemma covarianceOperator_apply
  given: (hμ : MemLp id 2 μ) (x : E)
  proof: by
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  rw [real_inner_comm]; rw [← integral_inner]
  · simp_rw [inner_smul_right, ← continuousLinearMapOfBilin_apply, ← covarianceOperator_inner hμ]
    rfl
exact memLp_one_iff_integrable.1 hμ.smul (hμ.const_inner x)

中文:
引理 covarianceOperator_apply
  条件: (hμ : MemLp id 2 μ) (x : E)
  证明: by
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  rw [real_inner_comm]; rw [← integral_inner]
  · simp_rw [inner_smul_right, ← continuousLinearMapOfBilin_apply, ← covarianceOperator_inner hμ]
    rfl
exact memLp_one_iff_integrable.1 hμ.smul (hμ.const_inner x)

Depends on / 依赖: const_inner, continuousLinearMapOfBilin_apply, covarianceOperator_inner, inner_smul_right, integral_inner, memLp_one_iff_integrable, real_inner_comm, simp_rw, unique_continuousLinearMapOfBilin
-/
lemma covarianceOperator_apply (hμ : MemLp id 2 μ) (x : E) :
    covarianceOperator μ x = ∫ y, ⟪x, y⟫ • y ∂μ := by
  refine (unique_continuousLinearMapOfBilin _ fun y => ?_).symm
  rw [real_inner_comm]; rw [← integral_inner]
  · simp_rw [inner_smul_right, ← continuousLinearMapOfBilin_apply, ← covarianceOperator_inner hμ]
    rfl
exact memLp_one_iff_integrable.1 hμ.smul (hμ.const_inner x)

/--
lemma `isPositive_covarianceOperator` / 引理 `isPositive_covarianceOperator`

English:
lemma isPositive_covarianceOperator
  statement: (covarianceOperator μ).toLinearMap.IsPositive
  proof: by
  by_cases hμ : MemLp id 2 μ
  swap; · simp [hμ]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp_rw [ContinuousLinearMap.coe_coe, real_inner_comm _ x, covarianceOperator_inner hμ,
      mul_comm]
  · simp only [ContinuousLinearMap.coe_coe, covarianceOperator_inner hμ, ← pow_two,
      RCLike.re_to

中文:
引理 isPositive_covarianceOperator
  结论: (covarianceOperator μ).toLinearMap.IsPositive
  证明: by
  by_cases hμ : MemLp id 2 μ
  swap; · simp [hμ]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp_rw [ContinuousLinearMap.coe_coe, real_inner_comm _ x, covarianceOperator_inner hμ,
      mul_comm]
  · simp only [ContinuousLinearMap.coe_coe, covarianceOperator_inner hμ, ← pow_two,
      RCLike.re_to

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, RCLike, RCLike.re_to_real, coe_coe, covarianceOperator_inner, mul_comm, pow_two, re_to_real, real_inner_comm, simp_rw
-/
lemma isPositive_covarianceOperator : (covarianceOperator μ).toLinearMap.IsPositive := by
  by_cases hμ : MemLp id 2 μ
  swap; · simp [hμ]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp_rw [ContinuousLinearMap.coe_coe, real_inner_comm _ x, covarianceOperator_inner hμ,
      mul_comm]
  · simp only [ContinuousLinearMap.coe_coe, covarianceOperator_inner hμ, ← pow_two,
      RCLike.re_to_real]
    positivity

end covarianceOperator

end ProbabilityTheory
