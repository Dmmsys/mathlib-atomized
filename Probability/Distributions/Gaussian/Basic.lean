/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file
`Mathlib/Probability/Distributions/Gaussian/Real.lean`.

## Main definitions

* `IsGaussian`: a measure `μ` is Gaussian if its map by every continuous linear form
  `L : Dual ℝ E` is a real Gaussian measure.
  That is, `μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal`.

## Main statements

* `isGaussian_iff_charFunDual_eq`: a finite measure `μ` is Gaussian if and only if
  its characteristic function has value `exp (μ[L] * I - Var[L; μ] / 2)` for every
  continuous linear form `L : Dual ℝ E`.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

public section

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

/--
Definition of `IsGaussian` / `IsGaussian` 的定义

English:
class IsGaussian
  parameters: {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E]
  axioms and operations (1):
    - map_eq_gaussianReal((L : StrongDual Real E)) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

中文:
类 是Gaussian
  参数: {E : 类型} [拓扑空间 E] [加法交换幺半群 E] [模 实数 E]
  公理与运算 (1 个):
    - map_eq_gaussianReal((L : StrongDual 实数 E)) : μ.map L = gaussian实数 (μ[L]) (Var[L; μ]).toNN实数

Depends on / 依赖: add_oreDiv, add_smul, smul_one_oreDiv_one_smul, zero_oreDiv, zero_smul
-/
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E]
    {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : StrongDual Real E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

/--
Instance `IsGaussian.toIsProbabilityMeasure` / 实例 `IsGaussian.toIsProbabilityMeasure`

English:
instance IsGaussian.toIsProbabilityMeasure
  signature: {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
  body: by
    have : μ.map (0 : StrongDual Real E) Set.univ = 1 := by
      simp [-FunLike.coe_zero, IsGaussian.map_eq_gaussianReal]
    simpa [-FunLike.coe_zero,
      Measure.map_apply (by fun_prop : Measurable (0 : StrongDual Real E)) .univ] using this

中文:
实例 是Gaussian.toIsProbabilityMeasure
  签名: {E : 类型} [拓扑空间 E] [加法交换幺半群 E]
  定义体: by
    have : μ.map (0 : StrongDual Real E) Set.univ = 1 := by
      simp [-FunLike.coe_zero, IsGaussian.map_eq_gaussianReal]
    simpa [-FunLike.coe_zero,
      Measure.map_apply (by fun_prop : Measurable (0 : StrongDual Real E)) .univ] using this

Depends on / 依赖: FunLike, FunLike.coe_zero, IsGaussian, IsGaussian.map_eq_gaussianReal, Measurable, Measure, Measure.map_apply, Set.univ, StrongDual, coe_zero, fun_prop, map_apply, map_eq_gaussianReal
-/
instance IsGaussian.toIsProbabilityMeasure {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module Real E] {mE : MeasurableSpace E} (μ : Measure E) [IsGaussian μ] :
    IsProbabilityMeasure μ where
  measure_univ := by
    have : μ.map (0 : StrongDual Real E) Set.univ = 1 := by
      simp [-FunLike.coe_zero, IsGaussian.map_eq_gaussianReal]
    simpa [-FunLike.coe_zero,
      Measure.map_apply (by fun_prop : Measurable (0 : StrongDual Real E)) .univ] using this

/--
Instance `isGaussian_gaussianReal` / 实例 `isGaussian_gaussianReal`

English:
instance isGaussian_gaussianReal
  signature: (m : Real) (v : Real>=0)
  body: by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity)]; rw [Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    posit

中文:
实例 isGaussian_gaussian实数
  签名: (m : 实数) (v : 实数>=0)
  定义体: by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity)]; rw [Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    posit

Depends on / 依赖: Real.coe_toNNReal, Real.toNNReal_coe, Real.toNNReal_mul, coe_toNNReal, gaussianReal_map_continuousLinearMap, integral_continuousLinearMap_gaussianReal, left_eq_sup, toNNReal_coe, toNNReal_mul, variance_continuousLinearMap_gaussianReal
-/
instance isGaussian_gaussianReal (m : Real) (v : Real>=0) : IsGaussian (gaussianReal m v) where
  map_eq_gaussianReal L := by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity)]; rw [Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    positivity

/--
lemma `IsGaussian.eq_gaussianReal` / 引理 `IsGaussian.eq_gaussianReal`

English:
lemma IsGaussian.eq_gaussianReal
  given: (μ : Measure Real) (h : IsGaussian μ)
  proof: calc
  μ = μ.map (ContinuousLinearMap.id Real Real) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp

中文:
引理 是Gaussian.eq_gaussian实数
  条件: (μ : 测度 实数) (h : 是Gaussian μ)
  证明: calc
  μ = μ.map (ContinuousLinearMap.id Real Real) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp

Depends on / 依赖: Module
-/
lemma IsGaussian.eq_gaussianReal (μ : Measure Real) (h : IsGaussian μ) :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := calc
  μ = μ.map (ContinuousLinearMap.id Real Real) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp

/--
lemma `isGaussian_of_isGaussian_map` / 引理 `isGaussian_of_isGaussian_map`

English:
lemma isGaussian_of_isGaussian_map
  statement: {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
  proof: by
  refine ⟨fun L => ?_⟩
  rw [(h L).eq_gaussianReal]; rw [integral_map]; rw [variance_map]
  · simp
  all_goals fun_prop

中文:
引理 isGaussian_of_isGaussian_map
  结论: {E : 类型} [拓扑空间 E] [加法交换幺半群 E]
  证明: by
  refine ⟨fun L => ?_⟩
  rw [(h L).eq_gaussianReal]; rw [integral_map]; rw [variance_map]
  · simp
  all_goals fun_prop

Depends on / 依赖: all_goals, eq_gaussianReal, fun_prop, integral_map, variance_map
-/
lemma isGaussian_of_isGaussian_map {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : forall L : E ->L[Real] Real, IsGaussian (μ.map L)) : IsGaussian μ := by
  refine ⟨fun L => ?_⟩
  rw [(h L).eq_gaussianReal]; rw [integral_map]; rw [variance_map]
  · simp
  all_goals fun_prop

/--
lemma `isGaussian_of_map_eq_gaussianReal` / 引理 `isGaussian_of_map_eq_gaussianReal`

English:
lemma isGaussian_of_map_eq_gaussianReal
  statement: {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
  proof: by
  refine isGaussian_of_isGaussian_map fun L => ?_
  obtain ⟨m, v, h⟩ := h L
  rw [h]
  infer_instance

中文:
引理 isGaussian_of_map_eq_gaussian实数
  结论: {E : 类型} [拓扑空间 E] [加法交换幺半群 E]
  证明: by
  refine isGaussian_of_isGaussian_map fun L => ?_
  obtain ⟨m, v, h⟩ := h L
  rw [h]
  infer_instance

Depends on / 依赖: infer_instance, isGaussian_of_isGaussian_map
-/
lemma isGaussian_of_map_eq_gaussianReal {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : forall L : E ->L[Real] Real, exists (m : Real) (v : Real>=0), μ.map L = gaussianReal m v) :
    IsGaussian μ := by
  refine isGaussian_of_isGaussian_map fun L => ?_
  obtain ⟨m, v, h⟩ := h L
  rw [h]
  infer_instance

/--
lemma `isGaussian_map_of_measurable` / 引理 `isGaussian_map_of_measurable`

English:
lemma isGaussian_map_of_measurable
  statement: {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
  proof: by
  refine isGaussian_of_map_eq_gaussianReal fun L' => ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL]; rw [← ContinuousLinearMap.coe_comp]; rw [IsGaussian.map_eq_gaussianReal]

中文:
引理 isGaussian_map_of_measurable
  结论: {E F : 类型} [拓扑空间 E] [加法交换幺半群 E]
  证明: by
  refine isGaussian_of_map_eq_gaussianReal fun L' => ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL]; rw [← ContinuousLinearMap.coe_comp]; rw [IsGaussian.map_eq_gaussianReal]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_comp, IsGaussian, IsGaussian.map_eq_gaussianReal, Measure, Measure.map_map, coe_comp, fun_prop, isGaussian_of_map_eq_gaussianReal, map_eq_gaussianReal, map_map, toNNReal
-/
lemma isGaussian_map_of_measurable {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module Real E] {mE : MeasurableSpace E} [TopologicalSpace F] [AddCommMonoid F]
    [Module Real F] {mF : MeasurableSpace F} [OpensMeasurableSpace F] {μ : Measure E}
    {L : E ->L[Real] F} [IsGaussian μ] (hL : Measurable L) : IsGaussian (μ.map L) := by
  refine isGaussian_of_map_eq_gaussianReal fun L' => ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL]; rw [← ContinuousLinearMap.coe_comp]; rw [IsGaussian.map_eq_gaussianReal]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace Real F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsGaussian μ]

/-- Dirac measures are Gaussian. -/
instance {x : E} : IsGaussian (Measure.dirac x) where
  map_eq_gaussianReal L := by simp

omit [IsGaussian μ] in
/--
lemma `IsGaussian.of_subsingleton` / 引理 `IsGaussian.of_subsingleton`

English:
lemma IsGaussian.of_subsingleton
  given: [Subsingleton E] [IsProbabilityMeasure μ]
  proof: by
  convert! instIsGaussianDirac (x := (0 : E))
  ext s -
  apply Subsingleton.set_cases (p := fun s => μ s = _)
  all_goals simp

中文:
引理 是Gaussian.of_subsingleton
  条件: [子单例 E] [是概率测度 μ]
  证明: by
  convert! instIsGaussianDirac (x := (0 : E))
  ext s -
  apply Subsingleton.set_cases (p := fun s => μ s = _)
  all_goals simp

Depends on / 依赖: Subsingleton, Subsingleton.set_cases, all_goals, convert, instIsGaussianDirac, set_cases
-/
lemma IsGaussian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure μ] :
    IsGaussian μ := by
  convert! instIsGaussianDirac (x := (0 : E))
  ext s -
  apply Subsingleton.set_cases (p := fun s => μ s = _)
  all_goals simp

/--
lemma `IsGaussian.memLp_dual` / 引理 `IsGaussian.memLp_dual`

English:
lemma IsGaussian.memLp_dual
  statement: (μ : Measure E) [IsGaussian μ] (L : StrongDual Real E)
  proof: by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop)]; rw [IsGaussian.map_eq_gaussianReal L]
  convert! memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]

中文:
引理 是Gaussian.memLp_dual
  结论: (μ : 测度 E) [是Gaussian μ] (L : StrongDual 实数 E)
  证明: by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop)]; rw [IsGaussian.map_eq_gaussianReal L]
  convert! memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]

Depends on / 依赖: IsGaussian, IsGaussian.map_eq_gaussianReal, convert, fun_prop, map_eq_gaussianReal, memLp_id_gaussianReal, memLp_map_measure_iff, p.toNNReal, toNNReal
-/
lemma IsGaussian.memLp_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual Real E)
    (p : Real>=0∞) (hp : p != ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop)]; rw [IsGaussian.map_eq_gaussianReal L]
  convert! memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]
/--
lemma `IsGaussian.integrable_dual` / 引理 `IsGaussian.integrable_dual`

English:
lemma IsGaussian.integrable_dual
  given: (μ : Measure E) [IsGaussian μ] (L : StrongDual Real E)
  proof: by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

中文:
引理 是Gaussian.integrable_dual
  条件: (μ : 测度 E) [是Gaussian μ] (L : StrongDual 实数 E)
  证明: by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

Depends on / 依赖: IsGaussian, IsGaussian.memLp_dual, memLp_dual, memLp_one_iff_integrable
-/
lemma IsGaussian.integrable_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual Real E) :
    Integrable L μ := by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

/--
Instance `isGaussian_map` / 实例 `isGaussian_map`

English:
instance isGaussian_map
  signature: (L : E ->L[Real] F)
  body: isGaussian_map_of_measurable (by fun_prop)

中文:
实例 isGaussian_map
  签名: (L : E ->L[实数] F)
  定义体: isGaussian_map_of_measurable (by fun_prop)

Depends on / 依赖: fun_prop, isGaussian_map_of_measurable
-/
instance isGaussian_map (L : E ->L[Real] F) : IsGaussian (μ.map L) :=
  isGaussian_map_of_measurable (by fun_prop)

/--
Instance `isGaussian_map_equiv` / 实例 `isGaussian_map_equiv`

English:
instance isGaussian_map_equiv
  signature: (L : E ≃L[Real] F)
  body: isGaussian_map (L : E ->L[Real] F)

中文:
实例 isGaussian_map_equiv
  签名: (L : E ≃L[实数] F)
  定义体: isGaussian_map (L : E ->L[Real] F)

Depends on / 依赖: isGaussian_map
-/
instance isGaussian_map_equiv (L : E ≃L[Real] F) : IsGaussian (μ.map L) :=
  isGaussian_map (L : E ->L[Real] F)

/--
lemma `isGaussian_map_equiv_iff` / 引理 `isGaussian_map_equiv_iff`

English:
lemma isGaussian_map_equiv_iff
  given: {μ : Measure E} (L : E ≃L[Real] F)
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  suffices μ = (μ.map L).map L.symm by rw [this]; infer_instance
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp

中文:
引理 isGaussian_map_equiv_iff
  条件: {μ : 测度 E} (L : E ≃L[实数] F)
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  suffices μ = (μ.map L).map L.symm by rw [this]; infer_instance
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp

Depends on / 依赖: L.symm, Measure, Measure.map_map, fun_prop, infer_instance, map_map
-/
lemma isGaussian_map_equiv_iff {μ : Measure E} (L : E ≃L[Real] F) :
    IsGaussian (μ.map L) ↔ IsGaussian μ := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  suffices μ = (μ.map L).map L.symm by rw [this]; infer_instance
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp

section charFunDual

/--
lemma `IsGaussian.charFunDual_eq` / 引理 `IsGaussian.charFunDual_eq`

English:
lemma IsGaussian.charFunDual_eq
  given: (L : StrongDual Real E)
  proof: by
  calc charFunDual μ L
  _ = charFun (μ.map L) 1 := by rw [charFunDual_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = exp (μ[L] * I - Var[L; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one,

中文:
引理 是Gaussian.charFunDual_eq
  条件: (L : StrongDual 实数 E)
  证明: by
  calc charFunDual μ L
  _ = charFun (μ.map L) 1 := by rw [charFunDual_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = exp (μ[L] * I - Var[L; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one,

Depends on / 依赖: IsGaussian, IsGaussian.map_eq_gaussianReal, Real.coe_toNNReal, charFun, charFunDual, charFunDual_eq_charFun_map_one, charFun_gaussianReal, coe_toNNReal, gaussianReal, integral_complex_ofReal, map_eq_gaussianReal, mul_one, ofReal_one, one_mul, one_pow, sup_eq_left, toNNReal, variance_nonneg
-/
lemma IsGaussian.charFunDual_eq (L : StrongDual Real E) :
    charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  calc charFunDual μ L
  _ = charFun (μ.map L) 1 := by rw [charFunDual_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = exp (μ[L] * I - Var[L; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one, one_mul, Real.coe_toNNReal', one_pow, mul_one]
    congr
    · rw [integral_complex_ofReal]
    · simp only [sup_eq_left]
      exact variance_nonneg _ _

/--
theorem `isGaussian_iff_charFunDual_eq` / 定理 `isGaussian_iff_charFunDual_eq`

English:
theorem isGaussian_iff_charFunDual_eq
  given: {μ : Measure E} [IsFiniteMeasure μ]
  proof: by
  refine ⟨fun h => h.charFunDual_eq, fun h => ⟨fun L => Measure.ext_of_charFun ?_⟩⟩
  ext u
  rw [charFun_map_eq_charFunDual_smul L u]; rw [h (u • L)]; rw [charFun_gaussianReal]
  simp only [smul_apply, smul_eq_mul, ofReal_mul, Real.coe_toNNReal']
  congr
  · rw [integral_const_mul, integral_comp

中文:
定理 isGaussian_iff_charFunDual_eq
  条件: {μ : 测度 E} [是有限测度 μ]
  证明: by
  refine ⟨fun h => h.charFunDual_eq, fun h => ⟨fun L => Measure.ext_of_charFun ?_⟩⟩
  ext u
  rw [charFun_map_eq_charFunDual_smul L u]; rw [h (u • L)]; rw [charFun_gaussianReal]
  simp only [smul_apply, smul_eq_mul, ofReal_mul, Real.coe_toNNReal']
  congr
  · rw [integral_const_mul, integral_comp

Depends on / 依赖: Measure, Measure.ext_of_charFun, Real.coe_toNNReal, charFunDual_eq, charFun_gaussianReal, charFun_map_eq_charFunDual_smul, coe_toNNReal, ext_of_charFun, h.charFunDual_eq, integral_complex_ofReal, integral_const_mul, max_eq_left, mul_comm, ofReal_mul, ofReal_pow, smul_apply, smul_eq_mul, variance_const_mul, variance_nonneg
-/
theorem isGaussian_iff_charFunDual_eq {μ : Measure E} [IsFiniteMeasure μ] :
    IsGaussian μ ↔ forall L : StrongDual Real E, charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  refine ⟨fun h => h.charFunDual_eq, fun h => ⟨fun L => Measure.ext_of_charFun ?_⟩⟩
  ext u
  rw [charFun_map_eq_charFunDual_smul L u]; rw [h (u • L)]; rw [charFun_gaussianReal]
  simp only [smul_apply, smul_eq_mul, ofReal_mul, Real.coe_toNNReal']
  congr
  · rw [integral_const_mul, integral_complex_ofReal]
  · rw [max_eq_left (variance_nonneg _ _), mul_comm, ← ofReal_pow, ← ofReal_mul,
      ← variance_const_mul]
    congr

alias ⟨_, isGaussian_of_charFunDual_eq⟩ := isGaussian_iff_charFunDual_eq

end charFunDual

section charFun

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E}

/--
lemma `IsGaussian.charFun_eq` / 引理 `IsGaussian.charFun_eq`

English:
lemma IsGaussian.charFun_eq
  given: [IsGaussian μ] (t : E)
  proof: by
  rw [charFun_eq_charFunDual_toDualMap]; rw [IsGaussian.charFunDual_eq]
  simp [toDualMap]

中文:
引理 是Gaussian.charFun_eq
  条件: [是Gaussian μ] (t : E)
  证明: by
  rw [charFun_eq_charFunDual_toDualMap]; rw [IsGaussian.charFunDual_eq]
  simp [toDualMap]

Depends on / 依赖: IsGaussian, IsGaussian.charFunDual_eq, charFunDual_eq, charFun_eq_charFunDual_toDualMap, toDualMap
-/
lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (μ[fun x => ⟪t, x⟫] * I - Var[fun x => ⟪t, x⟫; μ] / 2) := by
  rw [charFun_eq_charFunDual_toDualMap]; rw [IsGaussian.charFunDual_eq]
  simp [toDualMap]

-- TODO: This should not require completeness as `toDualMap` has dense range, but this is not
-- in mathlib.
/--
lemma `isGaussian_iff_charFun_eq` / 引理 `isGaussian_iff_charFun_eq`

English:
lemma isGaussian_iff_charFun_eq
  given: [CompleteSpace E] [IsFiniteMeasure μ]
  proof: by
  simp_rw [isGaussian_iff_charFunDual_eq, (toDual Real E).surjective.forall,
    charFun_eq_charFunDual_toDualMap]
  simp [toDualMap, toDual]

中文:
引理 isGaussian_iff_charFun_eq
  条件: [完备空间 E] [是有限测度 μ]
  证明: by
  simp_rw [isGaussian_iff_charFunDual_eq, (toDual Real E).surjective.forall,
    charFun_eq_charFunDual_toDualMap]
  simp [toDualMap, toDual]

Depends on / 依赖: charFun_eq_charFunDual_toDualMap, isGaussian_iff_charFunDual_eq, simp_rw, surjective, surjective.forall, toDual, toDualMap
-/
lemma isGaussian_iff_charFun_eq [CompleteSpace E] [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    forall t, charFun μ t = exp (μ[fun x => ⟪t, x⟫] * I - Var[fun x => ⟪t, x⟫; μ] / 2) := by
  simp_rw [isGaussian_iff_charFunDual_eq, (toDual Real E).surjective.forall,
    charFun_eq_charFunDual_toDualMap]
  simp [toDualMap, toDual]

end charFun

/--
Instance `isGaussian_conv` / 实例 `isGaussian_conv`

English:
instance isGaussian_conv
  signature: [SecondCountableTopology E]
  body: by
    have : (μ ∗ ν)[L] = ∫ x, x ∂((μ.map L).conv (ν.map L)) := by
      rw [← Measure.map_conv_continuousLinearMap L]; rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [Measure.map_conv_continuousLinearMap L]; rw [this]; rw [← variance_id_map (by fun_prop)]; rw [Measure.map_conv_conti

中文:
实例 isGaussian_conv
  签名: [第二可数拓扑 E]
  定义体: by
    have : (μ ∗ ν)[L] = ∫ x, x ∂((μ.map L).conv (ν.map L)) := by
      rw [← Measure.map_conv_continuousLinearMap L]; rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [Measure.map_conv_continuousLinearMap L]; rw [this]; rw [← variance_id_map (by fun_prop)]; rw [Measure.map_conv_conti

Depends on / 依赖: IsGaussian, IsGaussian.map_eq_gaussianReal, Measure, Measure.map_conv_continuousLinearMap, fun_prop, gaussianReal_conv_gaussianReal, integral_map, map_conv_continuousLinearMap, map_eq_gaussianReal, variance_id_map, variance_nonneg
-/
instance isGaussian_conv [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) where
  map_eq_gaussianReal L := by
    have : (μ ∗ ν)[L] = ∫ x, x ∂((μ.map L).conv (ν.map L)) := by
      rw [← Measure.map_conv_continuousLinearMap L]; rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [Measure.map_conv_continuousLinearMap L]; rw [this]; rw [← variance_id_map (by fun_prop)]; rw [Measure.map_conv_continuousLinearMap L]; rw [IsGaussian.map_eq_gaussianReal L]; rw [IsGaussian.map_eq_gaussianReal L]; rw [gaussianReal_conv_gaussianReal]
    congr <;> simp [variance_nonneg]

instance (c : E) : IsGaussian (μ.map (fun x => x + c)) := by
  refine isGaussian_of_charFunDual_eq fun L => ?_
  rw [charFunDual_map_add_const]; rw [IsGaussian.charFunDual_eq]; rw [← exp_add]
  have hL_comp : L ∘ (fun x => x + c) = fun x => L x + L c := by ext; simp
  rw [variance_map (by fun_prop) (by fun_prop)]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [hL_comp]; rw [variance_add_const (by fun_prop)]; rw [integral_complex_ofReal]; rw [integral_complex_ofReal]
  simp only [map_add]
  rw [integral_add (by fun_prop) (by fun_prop)]
  congr
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ofReal_add]
  ring

instance (c : E) : IsGaussian (μ.map (fun x => c + x)) := by simp_rw [add_comm c]; infer_instance

instance (c : E) : IsGaussian (μ.map (fun x => x - c)) := by simp_rw [sub_eq_add_neg]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGaussian (μ.map (fun x => -x))
  body: by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg Real))
  infer_instance

中文:
实例 :
  签名: 是Gaussian (μ.map (fun x => -x))
  定义体: by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg Real))
  infer_instance

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.neg, IsGaussian, infer_instance
-/
instance : IsGaussian (μ.map (fun x => -x)) := by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg Real))
  infer_instance

instance (c : E) : IsGaussian (μ.map (fun x => c - x)) := by
  simp_rw [sub_eq_add_neg]
  suffices IsGaussian ((μ.map (fun x => -x)).map (fun x => c + x)) by
    rwa [Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def] at this
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SecondCountableTopologyEither
  signature: E F] {ν
  body: by
  refine isGaussian_of_charFunDual_eq fun L => ?_
  rw [charFunDual_prod]; rw [IsGaussian.charFunDual_eq]; rw [IsGaussian.charFunDual_eq]; rw [← Complex.exp_add]
  congr
  let (eq := hL₁) L₁ := L.comp (.inl Real E F)
  let (eq := hL₂) L₂ := L.comp (.inr Real E F)
  rw [← hL₁]; rw [← hL₂]; rw [sub

中文:
实例 [SecondCountableTopologyEither
  签名: E F] {ν
  定义体: by
  refine isGaussian_of_charFunDual_eq fun L => ?_
  rw [charFunDual_prod]; rw [IsGaussian.charFunDual_eq]; rw [IsGaussian.charFunDual_eq]; rw [← Complex.exp_add]
  congr
  let (eq := hL₁) L₁ := L.comp (.inl Real E F)
  let (eq := hL₂) L₂ := L.comp (.inr Real E F)
  rw [← hL₁]; rw [← hL₂]; rw [sub

Depends on / 依赖: Complex.exp_add, IsGaussian, IsGaussian.charFunDual_eq, IsGaussian.integrable_dual, L.comp, add_mul, charFunDual_eq, charFunDual_prod, exp_add, integrable_dual, integral_complex_ofReal, integral_continuousLinearMap_prod, isGaussian_of_charFunDual_eq, simp_rw, sub_add_sub_comm
-/
instance [SecondCountableTopologyEither E F] {ν : Measure F} [IsGaussian ν] :
    IsGaussian (μ.prod ν) := by
  refine isGaussian_of_charFunDual_eq fun L => ?_
  rw [charFunDual_prod]; rw [IsGaussian.charFunDual_eq]; rw [IsGaussian.charFunDual_eq]; rw [← Complex.exp_add]
  congr
  let (eq := hL₁) L₁ := L.comp (.inl Real E F)
  let (eq := hL₂) L₂ := L.comp (.inr Real E F)
  rw [← hL₁]; rw [← hL₂]; rw [sub_add_sub_comm]; rw [← add_mul]
  congr
  · simp_rw [integral_complex_ofReal]
    rw [integral_continuousLinearMap_prod' (IsGaussian.integrable_dual μ (L.comp (.inl Real E F)))
      (IsGaussian.integrable_dual ν (L.comp (.inr Real E F)))]
    norm_cast
  · field_simp
    rw [variance_dual_prod' (IsGaussian.memLp_dual μ (L.comp (.inl Real E F)) 2 (by simp))
      (IsGaussian.memLp_dual ν (L.comp (.inr Real E F)) 2 (by simp))]
    norm_cast

end ProbabilityTheory
