/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `MeasureTheory.Measure.HaveLebesgueDecomposition` : A pair of measures `μ` and `ν` is said
  to `HaveLebesgueDecomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f`
* `MeasureTheory.Measure.singularPart` : If a pair of measures `HaveLebesgueDecomposition`,
  then `singularPart` chooses the measure from `HaveLebesgueDecomposition`, otherwise it
  returns the zero measure.
* `MeasureTheory.Measure.rnDeriv`: If a pair of measures
  `HaveLebesgueDecomposition`, then `rnDeriv` chooses the measurable function from
  `HaveLebesgueDecomposition`, otherwise it returns the zero function.

## Main results

* `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite` :
  the Lebesgue decomposition theorem.
* `MeasureTheory.Measure.eq_singularPart` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singularPart ν`.
* `MeasureTheory.Measure.eq_rnDeriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rnDeriv ν`.

## Tags

Lebesgue decomposition theorem
-/

@[expose] public section

assert_not_exists MeasureTheory.VectorMeasure

open scoped MeasureTheory NNReal ENNReal
open Set

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/--
Definition of `HaveLebesgueDecomposition` / `HaveLebesgueDecomposition` 的定义

English:
class HaveLebesgueDecomposition
  parameters: (μ ν : Measure α)
  axioms and operations (1):
    - lebesgue_decomposition : exists p : Measure α × (α -> Real>=0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2

中文:
类 HaveLebesgueDecomposition
  参数: (μ ν : Measure α)
  公理与运算 (1 个):
    - lebesgue_decomposition : 存在 p : Measure α × (α -> 实数>=0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2

Depends on / 依赖: Classical, Classical.choose, HaveLebesgueDecomposition, h.lebesgue_decomposition, lebesgue_decomposition
-/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    exists p : Measure α × (α -> Real>=0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2

open scoped Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `singularPart` chooses the
measure from `HaveLebesgueDecomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0

open scoped Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def rnDeriv (μ ν : Measure α) : α -> Real>=0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0

section ByDefinition

/--
theorem `haveLebesgueDecomposition_spec` / 定理 `haveLebesgueDecomposition_spec`

English:
theorem haveLebesgueDecomposition_spec
  given: (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν]
  proof: by
  rw [singularPart]; rw [rnDeriv]; rw [dif_pos h]; rw [dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition

中文:
定理 haveLebesgueDecomposition_spec
  条件: (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν]
  证明: by
  rw [singularPart]; rw [rnDeriv]; rw [dif_pos h]; rw [dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, h.lebesgue_decomposition, lebesgue_decomposition, rnDeriv, singularPart
-/
theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDeriv ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
  rw [singularPart]; rw [rnDeriv]; rw [dif_pos h]; rw [dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition

/--
lemma `rnDeriv_of_not_haveLebesgueDecomposition` / 引理 `rnDeriv_of_not_haveLebesgueDecomposition`

English:
lemma rnDeriv_of_not_haveLebesgueDecomposition
  given: (h : ¬ HaveLebesgueDecomposition μ ν)
  proof: by
  rw [rnDeriv]; rw [dif_neg h]

中文:
引理 rnDeriv_of_not_haveLebesgueDecomposition
  条件: (h : ¬ HaveLebesgueDecomposition μ ν)
  证明: by
  rw [rnDeriv]; rw [dif_neg h]

Depends on / 依赖: dif_neg, rnDeriv
-/
lemma rnDeriv_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.rnDeriv ν = 0 := by
  rw [rnDeriv]; rw [dif_neg h]

/--
lemma `singularPart_of_not_haveLebesgueDecomposition` / 引理 `singularPart_of_not_haveLebesgueDecomposition`

English:
lemma singularPart_of_not_haveLebesgueDecomposition
  given: (h : ¬ HaveLebesgueDecomposition μ ν)
  proof: by
  rw [singularPart]; rw [dif_neg h]

@[fun_prop]

中文:
引理 singularPart_of_not_haveLebesgueDecomposition
  条件: (h : ¬ HaveLebesgueDecomposition μ ν)
  证明: by
  rw [singularPart]; rw [dif_neg h]

@[fun_prop]

Depends on / 依赖: dif_neg, singularPart
-/
lemma singularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.singularPart ν = 0 := by
  rw [singularPart]; rw [dif_neg h]

@[fun_prop]
/--
theorem `measurable_rnDeriv` / 定理 `measurable_rnDeriv`

English:
theorem measurable_rnDeriv
  given: (μ ν : Measure α)
  statement: Measurable μ.rnDeriv ν
  proof: by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]
    exact measurable_zero

中文:
定理 measurable_rnDeriv
  条件: (μ ν : Measure α)
  结论: Measurable μ.rnDeriv ν
  证明: by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]
    exact measurable_zero

Depends on / 依赖: HaveLebesgueDecomposition, haveLebesgueDecomposition_spec, measurable_zero, rnDeriv_of_not_haveLebesgueDecomposition
-/
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable μ.rnDeriv ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]
    exact measurable_zero

/--
theorem `mutuallySingular_singularPart` / 定理 `mutuallySingular_singularPart`

English:
theorem mutuallySingular_singularPart
  given: (μ ν : Measure α)
  statement: μ.singularPart ν ⟂ₘ ν
  proof: by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left

中文:
定理 mutuallySingular_singularPart
  条件: (μ ν : Measure α)
  结论: μ.singularPart ν ⟂ₘ ν
  证明: by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left

Depends on / 依赖: HaveLebesgueDecomposition, MutuallySingular, MutuallySingular.zero_left, haveLebesgueDecomposition_spec, singularPart_of_not_haveLebesgueDecomposition, zero_left
-/
theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left

/--
theorem `MutuallySingular.haveLebesgueDecomposition` / 定理 `MutuallySingular.haveLebesgueDecomposition`

English:
theorem MutuallySingular.haveLebesgueDecomposition
  given: (h : μ ⟂ₘ ν)
  statement: HaveLebesgueDecomposition μ ν
  proof: ⟨⟨(μ, 0), measurable_zero, h, by simp⟩⟩

中文:
定理 MutuallySingular.haveLebesgueDecomposition
  条件: (h : μ ⟂ₘ ν)
  结论: HaveLebesgueDecomposition μ ν
  证明: ⟨⟨(μ, 0), measurable_zero, h, by simp⟩⟩

Depends on / 依赖: measurable_zero
-/
theorem MutuallySingular.haveLebesgueDecomposition (h : μ ⟂ₘ ν) : HaveLebesgueDecomposition μ ν :=
  ⟨⟨(μ, 0), measurable_zero, h, by simp⟩⟩

/--
theorem `haveLebesgueDecomposition_add` / 定理 `haveLebesgueDecomposition_add`

English:
theorem haveLebesgueDecomposition_add
  given: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  proof: (haveLebesgueDecomposition_spec μ ν).2.2

中文:
定理 haveLebesgueDecomposition_add
  条件: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  证明: (haveLebesgueDecomposition_spec μ ν).2.2

Depends on / 依赖: haveLebesgueDecomposition_spec
-/
theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2

/--
lemma `singularPart_add_rnDeriv` / 引理 `singularPart_add_rnDeriv`

English:
lemma singularPart_add_rnDeriv
  given: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  proof: (haveLebesgueDecomposition_add μ ν).symm

中文:
引理 singularPart_add_rnDeriv
  条件: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  证明: (haveLebesgueDecomposition_add μ ν).symm

Depends on / 依赖: haveLebesgueDecomposition_add
-/
lemma singularPart_add_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) = μ := (haveLebesgueDecomposition_add μ ν).symm

/--
lemma `rnDeriv_add_singularPart` / 引理 `rnDeriv_add_singularPart`

English:
lemma rnDeriv_add_singularPart
  given: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  proof: by rw [add_comm, singularPart_add_rnDeriv]

中文:
引理 rnDeriv_add_singularPart
  条件: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  证明: by rw [add_comm, singularPart_add_rnDeriv]

Depends on / 依赖: add_comm, singularPart_add_rnDeriv
-/
lemma rnDeriv_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν = μ := by rw [add_comm, singularPart_add_rnDeriv]

end ByDefinition

section HaveLebesgueDecomposition

/--
Instance `instHaveLebesgueDecompositionZeroLeft` / 实例 `instHaveLebesgueDecompositionZeroLeft`

English:
instance instHaveLebesgueDecompositionZeroLeft
  signature: : HaveLebesgueDecomposition 0 ν
  body: MutuallySingular.zero_left.haveLebesgueDecomposition

中文:
实例 instHaveLebesgueDecompositionZeroLeft
  签名: : HaveLebesgueDecomposition 0 ν
  定义体: MutuallySingular.zero_left.haveLebesgueDecomposition

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_left.haveLebesgueDecomposition, haveLebesgueDecomposition, zero_left
-/
instance instHaveLebesgueDecompositionZeroLeft : HaveLebesgueDecomposition 0 ν :=
  MutuallySingular.zero_left.haveLebesgueDecomposition

/--
Instance `instHaveLebesgueDecompositionZeroRight` / 实例 `instHaveLebesgueDecompositionZeroRight`

English:
instance instHaveLebesgueDecompositionZeroRight
  signature: : HaveLebesgueDecomposition μ 0
  body: MutuallySingular.zero_right.haveLebesgueDecomposition

中文:
实例 instHaveLebesgueDecompositionZeroRight
  签名: : HaveLebesgueDecomposition μ 0
  定义体: MutuallySingular.zero_right.haveLebesgueDecomposition

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_right.haveLebesgueDecomposition, haveLebesgueDecomposition, zero_right
-/
instance instHaveLebesgueDecompositionZeroRight : HaveLebesgueDecomposition μ 0 :=
  MutuallySingular.zero_right.haveLebesgueDecomposition

/--
Instance `instHaveLebesgueDecompositionSelf` / 实例 `instHaveLebesgueDecompositionSelf`

English:
instance instHaveLebesgueDecompositionSelf
  signature: : HaveLebesgueDecomposition μ μ where
  body: ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩

中文:
实例 instHaveLebesgueDecompositionSelf
  签名: : HaveLebesgueDecomposition μ μ where
  定义体: ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_left, measurable_const, zero_left
-/
instance instHaveLebesgueDecompositionSelf : HaveLebesgueDecomposition μ μ where
  lebesgue_decomposition := ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩

/--
Instance `HaveLebesgueDecomposition.sum_left` / 实例 `HaveLebesgueDecomposition.sum_left`

English:
instance HaveLebesgueDecomposition.sum_left
  signature: {ι : Type*} [Countable ι] (μ : ι -> Measure α)
  body: ⟨(.sum fun i => (μ i).singularPart ν, ∑' i, rnDeriv (μ i) ν),
    by dsimp only; fun_prop, by simp [mutuallySingular_singularPart], by
      simp [withDensity_tsum, measurable_rnDeriv, Measure.sum_add_sum, singularPart_add_rnDeriv]⟩

中文:
实例 HaveLebesgueDecomposition.sum_left
  签名: {ι : 类型} [Countable ι] (μ : ι -> Measure α)
  定义体: ⟨(.sum fun i => (μ i).singularPart ν, ∑' i, rnDeriv (μ i) ν),
    by dsimp only; fun_prop, by simp [mutuallySingular_singularPart], by
      simp [withDensity_tsum, measurable_rnDeriv, Measure.sum_add_sum, singularPart_add_rnDeriv]⟩

Depends on / 依赖: Measure, Measure.sum_add_sum, fun_prop, measurable_rnDeriv, mutuallySingular_singularPart, rnDeriv, singularPart, singularPart_add_rnDeriv, sum_add_sum, withDensity_tsum
-/
instance HaveLebesgueDecomposition.sum_left {ι : Type*} [Countable ι] (μ : ι -> Measure α)
    [forall i, HaveLebesgueDecomposition (μ i) ν] : HaveLebesgueDecomposition (.sum μ) ν :=
  ⟨(.sum fun i => (μ i).singularPart ν, ∑' i, rnDeriv (μ i) ν),
    by dsimp only; fun_prop, by simp [mutuallySingular_singularPart], by
      simp [withDensity_tsum, measurable_rnDeriv, Measure.sum_add_sum, singularPart_add_rnDeriv]⟩

/--
Instance `HaveLebesgueDecomposition.add_left` / 实例 `HaveLebesgueDecomposition.add_left`

English:
instance HaveLebesgueDecomposition.add_left
  signature: {μ' : Measure α} [HaveLebesgueDecomposition μ ν]
  body: by
  have : forall b, HaveLebesgueDecomposition (cond b μ μ') ν := by simp [*]
  simpa using sum_left (cond · μ μ')

中文:
实例 HaveLebesgueDecomposition.add_left
  签名: {μ' : Measure α} [HaveLebesgueDecomposition μ ν]
  定义体: by
  have : forall b, HaveLebesgueDecomposition (cond b μ μ') ν := by simp [*]
  simpa using sum_left (cond · μ μ')

Depends on / 依赖: HaveLebesgueDecomposition, sum_left
-/
instance HaveLebesgueDecomposition.add_left {μ' : Measure α} [HaveLebesgueDecomposition μ ν]
    [HaveLebesgueDecomposition μ' ν] : HaveLebesgueDecomposition (μ + μ') ν := by
  have : forall b, HaveLebesgueDecomposition (cond b μ μ') ν := by simp [*]
  simpa using sum_left (cond · μ μ')

/--
Instance `haveLebesgueDecompositionSMul'` / 实例 `haveLebesgueDecompositionSMul'`

English:
instance haveLebesgueDecompositionSMul'
  signature: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  body: by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only
    rw [withDensity_smul _ hmeas]; rw [← smul_add]; rw [← hadd]

中文:
实例 haveLebesgueDecompositionSMul'
  签名: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  定义体: by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only
    rw [withDensity_smul _ hmeas]; rw [← smul_add]; rw [← hadd]

Depends on / 依赖: const_smul, haveLebesgueDecomposition_spec, hmeas.const_smul, hsing.smul, rnDeriv, singularPart, smul_add, withDensity_smul
-/
instance haveLebesgueDecompositionSMul' (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : Real>=0∞) : (r • μ).HaveLebesgueDecomposition ν where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only
    rw [withDensity_smul _ hmeas]; rw [← smul_add]; rw [← hadd]

/--
Instance `haveLebesgueDecompositionSMul` / 实例 `haveLebesgueDecompositionSMul`

English:
instance haveLebesgueDecompositionSMul
  signature: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  body: by
  rw [ENNReal.smul_def]; infer_instance

中文:
实例 haveLebesgueDecompositionSMul
  签名: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  定义体: by
  rw [ENNReal.smul_def]; infer_instance

Depends on / 依赖: ENNReal, ENNReal.smul_def, infer_instance, smul_def
-/
instance haveLebesgueDecompositionSMul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : Real>=0) : (r • μ).HaveLebesgueDecomposition ν := by
  rw [ENNReal.smul_def]; infer_instance

/--
Instance `haveLebesgueDecompositionSMulRight` / 实例 `haveLebesgueDecompositionSMulRight`

English:
instance haveLebesgueDecompositionSMulRight
  signature: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  body: by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous

中文:
实例 haveLebesgueDecompositionSMulRight
  签名: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  定义体: by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, ENNReal, ENNReal.smul_def, const_smul, haveLebesgueDecomposition_spec, hmeas.const_smul, hsing.mono_ac, measurable_const, mono_ac, rnDeriv, singularPart, smul_absolutelyContinuous, smul_assoc, smul_def, withDensity_smul, withDensity_smul_measure
-/
instance haveLebesgueDecompositionSMulRight (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : Real>=0) :
    μ.HaveLebesgueDecomposition (r • ν) where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous, ?_⟩
    have : r⁻¹ • rnDeriv μ ν = ((r⁻¹ : Real>=0) : Real>=0∞) • rnDeriv μ ν := by simp [ENNReal.smul_def]
    rw [this]; rw [withDensity_smul _ hmeas]; rw [ENNReal.smul_def r]; rw [withDensity_smul_measure]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [ENNReal.coe_inv hr]; rw [ENNReal.inv_mul_cancel]; rw [one_smul]
    · exact hadd
    · simp [hr]
    · exact ENNReal.coe_ne_top

/--
theorem `haveLebesgueDecomposition_withDensity` / 定理 `haveLebesgueDecomposition_withDensity`

English:
theorem haveLebesgueDecomposition_withDensity
  given: (μ : Measure α) {f : α -> Real>=0∞} (hf : Measurable f)
  proof: ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩

中文:
定理 haveLebesgueDecomposition_withDensity
  条件: (μ : Measure α) {f : α -> 实数>=0∞} (hf : Measurable f)
  证明: ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩

Depends on / 依赖: zero_add, zero_left
-/
theorem haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α -> Real>=0∞} (hf : Measurable f) :
    (μ.withDensity f).HaveLebesgueDecomposition μ := ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩

/--
Instance `haveLebesgueDecompositionRnDeriv` / 实例 `haveLebesgueDecompositionRnDeriv`

English:
instance haveLebesgueDecompositionRnDeriv
  signature: (μ ν : Measure α)
  body: haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)

中文:
实例 haveLebesgueDecompositionRnDeriv
  签名: (μ ν : Measure α)
  定义体: haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)

Depends on / 依赖: haveLebesgueDecomposition_withDensity, measurable_rnDeriv
-/
instance haveLebesgueDecompositionRnDeriv (μ ν : Measure α) :
    HaveLebesgueDecomposition (ν.withDensity (μ.rnDeriv ν)) ν :=
  haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)

/--
Instance `instHaveLebesgueDecompositionSingularPart` / 实例 `instHaveLebesgueDecompositionSingularPart`

English:
instance instHaveLebesgueDecompositionSingularPart
  signature: :
  body: ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

中文:
实例 instHaveLebesgueDecompositionSingularPart
  签名: :
  定义体: ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

Depends on / 依赖: measurable_zero, mutuallySingular_singularPart, singularPart
-/
instance instHaveLebesgueDecompositionSingularPart :
    HaveLebesgueDecomposition (μ.singularPart ν) ν :=
  ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

end HaveLebesgueDecomposition

/--
theorem `singularPart_le` / 定理 `singularPart_le`

English:
theorem singularPart_le
  given: (μ ν : Measure α)
  statement: μ.singularPart ν <= μ
  proof: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ

中文:
定理 singularPart_le
  条件: (μ ν : Measure α)
  结论: μ.singularPart ν <= μ
  证明: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ

Depends on / 依赖: HaveLebesgueDecomposition, Measure, Measure.le_add_right, Measure.zero_le, conv_rhs, dif_neg, haveLebesgueDecomposition_add, le_add_right, le_rfl, singularPart, zero_le
-/
theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν <= μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ

/--
theorem `withDensity_rnDeriv_le` / 定理 `withDensity_rnDeriv_le`

English:
theorem withDensity_rnDeriv_le
  given: (μ ν : Measure α)
  statement: ν.withDensity (μ.rnDeriv ν) <= μ
  proof: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ

中文:
定理 withDensity_rnDeriv_le
  条件: (μ ν : Measure α)
  结论: ν.withDensity (μ.rnDeriv ν) <= μ
  证明: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ

Depends on / 依赖: HaveLebesgueDecomposition, Measure, Measure.le_add_left, Measure.zero_le, conv_rhs, dif_neg, haveLebesgueDecomposition_add, le_add_left, le_rfl, rnDeriv, withDensity_zero, zero_le
-/
theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ

/--
lemma `_root_.AEMeasurable.singularPart` / 引理 `_root_.AEMeasurable.singularPart`

English:
lemma _root_.AEMeasurable.singularPart
  statement: {β : Type*} {_ : MeasurableSpace β} {f : α -> β}
  proof: AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

中文:
引理 _root_.AEMeasurable.singularPart
  结论: {β : 类型} {_ : MeasurableSpace β} {f : α -> β}
  证明: AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

Depends on / 依赖: AEMeasurable, AEMeasurable.mono_measure, Measure, Measure.singularPart_le, mono_measure, singularPart_le
-/
lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α -> β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

/--
lemma `_root_.AEMeasurable.withDensity_rnDeriv` / 引理 `_root_.AEMeasurable.withDensity_rnDeriv`

English:
lemma _root_.AEMeasurable.withDensity_rnDeriv
  statement: {β : Type*} {_ : MeasurableSpace β} {f : α -> β}
  proof: AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

中文:
引理 _root_.AEMeasurable.withDensity_rnDeriv
  结论: {β : 类型} {_ : MeasurableSpace β} {f : α -> β}
  证明: AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

Depends on / 依赖: AEMeasurable, AEMeasurable.mono_measure, Measure, Measure.withDensity_rnDeriv_le, mono_measure, withDensity_rnDeriv_le
-/
lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α -> β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

/--
lemma `MutuallySingular.singularPart` / 引理 `MutuallySingular.singularPart`

English:
lemma MutuallySingular.singularPart
  given: (h : μ ⟂ₘ ν) (ν' : Measure α)
  proof: h.mono (singularPart_le μ ν') le_rfl

中文:
引理 MutuallySingular.singularPart
  条件: (h : μ ⟂ₘ ν) (ν' : Measure α)
  证明: h.mono (singularPart_le μ ν') le_rfl
-/
protected lemma MutuallySingular.singularPart (h : μ ⟂ₘ ν) (ν' : Measure α) :
    μ.singularPart ν' ⟂ₘ ν :=
  h.mono (singularPart_le μ ν') le_rfl

/--
lemma `absolutelyContinuous_withDensity_rnDeriv` / 引理 `absolutelyContinuous_withDensity_rnDeriv`

English:
lemma absolutelyContinuous_withDensity_rnDeriv
  given: [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν)
  proof: by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs => ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s]; rw [← nonpos_iff_eq_zero]
  refine (measure_union_le (s inter t) (s inter tᶜ)).trans ?_
  simp only [no

中文:
引理 absolutelyContinuous_withDensity_rnDeriv
  条件: [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν)
  证明: by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs => ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s]; rw [← nonpos_iff_eq_zero]
  refine (measure_union_le (s inter t) (s inter tᶜ)).trans ?_
  simp only [no

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, Pi.add_apply, Set.inter_subse, Set.inter_subset_right, add_apply, add_eq_zero, coe_add, haveLebesgueDecomposition_add, inter_subse, inter_subset_right, inter_union_compl, measure_mono_null, measure_union_le, mutuallySingular_singularPart, nonpos_iff_eq_zero
-/
lemma absolutelyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
    μ ≪ μ.withDensity (ν.rnDeriv μ) := by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs => ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s]; rw [← nonpos_iff_eq_zero]
  refine (measure_union_le (s inter t) (s inter tᶜ)).trans ?_
  simp only [nonpos_iff_eq_zero, add_eq_zero]
  constructor
  · refine hμν ?_
    simp only [coe_add, Pi.add_apply, add_eq_zero]
    constructor
    · exact measure_mono_null Set.inter_subset_right ht1
    · exact measure_mono_null Set.inter_subset_left hνs
  · exact measure_mono_null Set.inter_subset_right ht2

/--
lemma `AbsolutelyContinuous.withDensity_rnDeriv` / 引理 `AbsolutelyContinuous.withDensity_rnDeriv`

English:
lemma AbsolutelyContinuous.withDensity_rnDeriv
  statement: {ξ : Measure α} [μ.HaveLebesgueDecomposition ν]
  proof: by
  conv_rhs at hξμ => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  refine absolutelyContinuous_of_add_of_mutuallySingular hξμ ?_
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart μ ν).symm hξν .rfl

中文:
引理 AbsolutelyContinuous.withDensity_rnDeriv
  结论: {ξ : Measure α} [μ.HaveLebesgueDecomposition ν]
  证明: by
  conv_rhs at hξμ => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  refine absolutelyContinuous_of_add_of_mutuallySingular hξμ ?_
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart μ ν).symm hξν .rfl

Depends on / 依赖: MutuallySingular, MutuallySingular.mono_ac, absolutelyContinuous_of_add_of_mutuallySingular, add_comm, conv_rhs, haveLebesgueDecomposition_add, mono_ac, mutuallySingular_singularPart
-/
lemma AbsolutelyContinuous.withDensity_rnDeriv {ξ : Measure α} [μ.HaveLebesgueDecomposition ν]
    (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν) :
    ξ ≪ ν.withDensity (μ.rnDeriv ν) := by
  conv_rhs at hξμ => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  refine absolutelyContinuous_of_add_of_mutuallySingular hξμ ?_
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart μ ν).symm hξν .rfl

/--
lemma `absolutelyContinuous_withDensity_rnDeriv_swap` / 引理 `absolutelyContinuous_withDensity_rnDeriv_swap`

English:
lemma absolutelyContinuous_withDensity_rnDeriv_swap
  given: [ν.HaveLebesgueDecomposition μ]
  proof: (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).withDensity_rnDeriv
    (absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _))

中文:
引理 absolutelyContinuous_withDensity_rnDeriv_swap
  条件: [ν.HaveLebesgueDecomposition μ]
  证明: (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).withDensity_rnDeriv
    (absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _))

Depends on / 依赖: absolutelyContinuous_of_le, rnDeriv, withDensity_absolutelyContinuous, withDensity_rnDeriv, withDensity_rnDeriv_le
-/
lemma absolutelyContinuous_withDensity_rnDeriv_swap [ν.HaveLebesgueDecomposition μ] :
    ν.withDensity (μ.rnDeriv ν) ≪ μ.withDensity (ν.rnDeriv μ) :=
  (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).withDensity_rnDeriv
    (absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _))

/--
lemma `singularPart_eq_zero_of_ac` / 引理 `singularPart_eq_zero_of_ac`

English:
lemma singularPart_eq_zero_of_ac
  given: (h : μ ≪ ν)
  statement: μ.singularPart ν = 0
  proof: by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]

中文:
引理 singularPart_eq_zero_of_ac
  条件: (h : μ ≪ ν)
  结论: μ.singularPart ν = 0
  证明: by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, MutuallySingular, MutuallySingular.mono_ac, MutuallySingular.self_iff, absolutelyContinuous_of_le, mono_ac, mutuallySingular_singularPart, self_iff, singularPart_le
-/
lemma singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0 := by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]
/--
theorem `singularPart_zero` / 定理 `singularPart_zero`

English:
theorem singularPart_zero
  given: (ν : Measure α)
  statement: (0 : Measure α).singularPart ν = 0
  proof: singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)

@[simp]

中文:
定理 singularPart_zero
  条件: (ν : Measure α)
  结论: (0 : Measure α).singularPart ν = 0
  证明: singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)

@[simp]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.zero, singularPart_eq_zero_of_ac
-/
theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)

@[simp]
/--
lemma `singularPart_zero_right` / 引理 `singularPart_zero_right`

English:
lemma singularPart_zero_right
  given: (μ : Measure α)
  statement: μ.singularPart 0 = μ
  proof: by
  conv_rhs => rw [haveLebesgueDecomposition_add μ 0]
  simp

中文:
引理 singularPart_zero_right
  条件: (μ : Measure α)
  结论: μ.singularPart 0 = μ
  证明: by
  conv_rhs => rw [haveLebesgueDecomposition_add μ 0]
  simp

Depends on / 依赖: conv_rhs, haveLebesgueDecomposition_add
-/
lemma singularPart_zero_right (μ : Measure α) : μ.singularPart 0 = μ := by
  conv_rhs => rw [haveLebesgueDecomposition_add μ 0]
  simp

/--
lemma `singularPart_eq_zero` / 引理 `singularPart_eq_zero`

English:
lemma singularPart_eq_zero
  given: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  proof: by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, singularPart_eq_zero_of_ac⟩
  rw [h]; rw [zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

@[simp]

中文:
引理 singularPart_eq_zero
  条件: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  证明: by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, singularPart_eq_zero_of_ac⟩
  rw [h]; rw [zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

@[simp]

Depends on / 依赖: h_dec, haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac, withDensity_absolutelyContinuous, zero_add
-/
lemma singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν = 0 ↔ μ ≪ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, singularPart_eq_zero_of_ac⟩
  rw [h]; rw [zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

@[simp]
/--
lemma `withDensity_rnDeriv_eq_zero` / 引理 `withDensity_rnDeriv_eq_zero`

English:
lemma withDensity_rnDeriv_eq_zero
  given: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  proof: by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec]; rw [MutuallySingular.add_left_iff] at h
    refine MutuallySingular.m

中文:
引理 withDensity_rnDeriv_eq_zero
  条件: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  证明: by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec]; rw [MutuallySingular.add_left_iff] at h
    refine MutuallySingular.m

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, MutuallySingular, MutuallySingular.add_left_iff, MutuallySingular.mono_ac, MutuallySingular.self_iff, add_left_iff, add_zero, h_dec, haveLebesgueDecomposition_add, mono_ac, mutuallySingular_singularPart, self_iff, withDensity_absolutelyContinuous
-/
lemma withDensity_rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    ν.withDensity (μ.rnDeriv ν) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec]; rw [MutuallySingular.add_left_iff] at h
    refine MutuallySingular.mono_ac h.2 AbsolutelyContinuous.rfl ?_
    exact withDensity_absolutelyContinuous _ _

@[simp]
/--
lemma `rnDeriv_eq_zero` / 引理 `rnDeriv_eq_zero`

English:
lemma rnDeriv_eq_zero
  given: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  proof: by
  rw [← withDensity_rnDeriv_eq_zero]; rw [withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

中文:
引理 rnDeriv_eq_zero
  条件: (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν]
  证明: by
  rw [← withDensity_rnDeriv_eq_zero]; rw [withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

Depends on / 依赖: aemeasurable, measurable_rnDeriv, withDensity_eq_zero_iff, withDensity_rnDeriv_eq_zero
-/
lemma rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν := by
  rw [← withDensity_rnDeriv_eq_zero]; rw [withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

/--
lemma `rnDeriv_zero` / 引理 `rnDeriv_zero`

English:
lemma rnDeriv_zero
  given: (ν : Measure α)
  statement: (0 : Measure α).rnDeriv ν =ᵐ[ν] 0
  proof: by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left

中文:
引理 rnDeriv_zero
  条件: (ν : Measure α)
  结论: (0 : Measure α).rnDeriv ν =ᵐ[ν] 0
  证明: by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_left, rnDeriv_eq_zero, zero_left
-/
lemma rnDeriv_zero (ν : Measure α) : (0 : Measure α).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left

/--
lemma `MutuallySingular.rnDeriv_ae_eq_zero` / 引理 `MutuallySingular.rnDeriv_ae_eq_zero`

English:
lemma MutuallySingular.rnDeriv_ae_eq_zero
  given: (hμν : μ ⟂ₘ ν)
  proof: by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]

中文:
引理 MutuallySingular.rnDeriv_ae_eq_zero
  条件: (hμν : μ ⟂ₘ ν)
  证明: by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]

Depends on / 依赖: HaveLebesgueDecomposition, rnDeriv_eq_zero, rnDeriv_of_not_haveLebesgueDecomposition
-/
lemma MutuallySingular.rnDeriv_ae_eq_zero (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]
/--
theorem `singularPart_withDensity` / 定理 `singularPart_withDensity`

English:
theorem singularPart_withDensity
  given: (ν : Measure α) (f : α -> Real>=0∞)
  proof: singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)

中文:
定理 singularPart_withDensity
  条件: (ν : Measure α) (f : α -> 实数>=0∞)
  证明: singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)

Depends on / 依赖: singularPart_eq_zero_of_ac, withDensity_absolutelyContinuous
-/
theorem singularPart_withDensity (ν : Measure α) (f : α -> Real>=0∞) :
    (ν.withDensity f).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)

/--
lemma `rnDeriv_singularPart` / 引理 `rnDeriv_singularPart`

English:
lemma rnDeriv_singularPart
  given: (μ ν : Measure α)
  proof: by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]

中文:
引理 rnDeriv_singularPart
  条件: (μ ν : Measure α)
  证明: by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]

Depends on / 依赖: mutuallySingular_singularPart, rnDeriv_eq_zero
-/
lemma rnDeriv_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]
/--
lemma `singularPart_self` / 引理 `singularPart_self`

English:
lemma singularPart_self
  given: (μ : Measure α)
  statement: μ.singularPart μ = 0
  proof: singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl

中文:
引理 singularPart_self
  条件: (μ : Measure α)
  结论: μ.singularPart μ = 0
  证明: singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, singularPart_eq_zero_of_ac
-/
lemma singularPart_self (μ : Measure α) : μ.singularPart μ = 0 :=
  singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl

/--
lemma `rnDeriv_self` / 引理 `rnDeriv_self`

English:
lemma rnDeriv_self
  given: (μ : Measure α) [SigmaFinite μ]
  statement: μ.rnDeriv μ =ᵐ[μ] fun _ => 1
  proof: by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self]; rw [add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const

中文:
引理 rnDeriv_self
  条件: (μ : Measure α) [SigmaFinite μ]
  结论: μ.rnDeriv μ =ᵐ[μ] fun _ => 1
  证明: by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self]; rw [add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const

Depends on / 依赖: add_zero, aemeasurable, aemeasurable_const, conv_rhs, h_one, measurable_rnDeriv, rnDeriv_add_singularPart, singularPart_self, withDensity, withDensity_eq_iff_of_sigmaFinite
-/
lemma rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1 := by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self]; rw [add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const

/--
lemma `singularPart_eq_self` / 引理 `singularPart_eq_self`

English:
lemma singularPart_eq_self
  statement: μ.singularPart ν = μ ↔ μ ⟂ₘ ν
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · have := h.haveLebesgueDecomposition
    conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h]; rw [add_zero]

@[simp]

中文:
引理 singularPart_eq_self
  结论: μ.singularPart ν = μ ↔ μ ⟂ₘ ν
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · have := h.haveLebesgueDecomposition
    conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, conv_rhs, h.haveLebesgueDecomposition, haveLebesgueDecomposition, mutuallySingular_singularPart, singularPart_add_rnDeriv, withDensity_rnDeriv_eq_zero
-/
lemma singularPart_eq_self : μ.singularPart ν = μ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · have := h.haveLebesgueDecomposition
    conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h]; rw [add_zero]

@[simp]
/--
lemma `singularPart_singularPart` / 引理 `singularPart_singularPart`

English:
lemma singularPart_singularPart
  given: (μ ν : Measure α)
  proof: by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _

中文:
引理 singularPart_singularPart
  条件: (μ ν : Measure α)
  证明: by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _

Depends on / 依赖: Measure, Measure.mutuallySingular_singularPart, Measure.singularPart_eq_self, mutuallySingular_singularPart, singularPart_eq_self
-/
lemma singularPart_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).singularPart ν = μ.singularPart ν := by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _

/--
Instance `singularPart.instIsFiniteMeasure` / 实例 `singularPart.instIsFiniteMeasure`

English:
instance singularPart.instIsFiniteMeasure
  signature: [IsFiniteMeasure μ]
  body: isFiniteMeasure_of_le μ singularPart_le μ ν

中文:
实例 singularPart.instIsFiniteMeasure
  签名: [IsFiniteMeasure μ]
  定义体: isFiniteMeasure_of_le μ singularPart_le μ ν

Depends on / 依赖: isFiniteMeasure_of_le, singularPart_le
-/
instance singularPart.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.singularPart ν) :=
isFiniteMeasure_of_le μ singularPart_le μ ν

/--
Instance `singularPart.instSigmaFinite` / 实例 `singularPart.instSigmaFinite`

English:
instance singularPart.instSigmaFinite
  signature: [SigmaFinite μ]
  body: sigmaFinite_of_le μ singularPart_le μ ν

中文:
实例 singularPart.instSigmaFinite
  签名: [SigmaFinite μ]
  定义体: sigmaFinite_of_le μ singularPart_le μ ν

Depends on / 依赖: sigmaFinite_of_le, singularPart_le
-/
instance singularPart.instSigmaFinite [SigmaFinite μ] : SigmaFinite (μ.singularPart ν) :=
sigmaFinite_of_le μ singularPart_le μ ν

/--
Instance `singularPart.instIsLocallyFiniteMeasure` / 实例 `singularPart.instIsLocallyFiniteMeasure`

English:
instance singularPart.instIsLocallyFiniteMeasure
  signature: [TopologicalSpace α] [IsLocallyFiniteMeasure μ]
  body: isLocallyFiniteMeasure_of_le singularPart_le μ ν

中文:
实例 singularPart.instIsLocallyFiniteMeasure
  签名: [TopologicalSpace α] [IsLocallyFiniteMeasure μ]
  定义体: isLocallyFiniteMeasure_of_le singularPart_le μ ν

Depends on / 依赖: isLocallyFiniteMeasure_of_le, singularPart_le
-/
instance singularPart.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.singularPart ν) :=
isLocallyFiniteMeasure_of_le singularPart_le μ ν

/--
Instance `withDensity.instIsFiniteMeasure` / 实例 `withDensity.instIsFiniteMeasure`

English:
instance withDensity.instIsFiniteMeasure
  signature: [IsFiniteMeasure μ]
  body: isFiniteMeasure_of_le μ withDensity_rnDeriv_le μ ν

中文:
实例 withDensity.instIsFiniteMeasure
  签名: [IsFiniteMeasure μ]
  定义体: isFiniteMeasure_of_le μ withDensity_rnDeriv_le μ ν

Depends on / 依赖: isFiniteMeasure_of_le, withDensity_rnDeriv_le
-/
instance withDensity.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
isFiniteMeasure_of_le μ withDensity_rnDeriv_le μ ν

/--
Instance `withDensity.instSigmaFinite` / 实例 `withDensity.instSigmaFinite`

English:
instance withDensity.instSigmaFinite
  signature: [SigmaFinite μ]
  body: sigmaFinite_of_le μ withDensity_rnDeriv_le μ ν

中文:
实例 withDensity.instSigmaFinite
  签名: [SigmaFinite μ]
  定义体: sigmaFinite_of_le μ withDensity_rnDeriv_le μ ν

Depends on / 依赖: sigmaFinite_of_le, withDensity_rnDeriv_le
-/
instance withDensity.instSigmaFinite [SigmaFinite μ] :
    SigmaFinite (ν.withDensity <| μ.rnDeriv ν) :=
sigmaFinite_of_le μ withDensity_rnDeriv_le μ ν

/--
Instance `withDensity.instIsLocallyFiniteMeasure` / 实例 `withDensity.instIsLocallyFiniteMeasure`

English:
instance withDensity.instIsLocallyFiniteMeasure
  signature: [TopologicalSpace α] [IsLocallyFiniteMeasure μ]
  body: isLocallyFiniteMeasure_of_le withDensity_rnDeriv_le μ ν

中文:
实例 withDensity.instIsLocallyFiniteMeasure
  签名: [TopologicalSpace α] [IsLocallyFiniteMeasure μ]
  定义体: isLocallyFiniteMeasure_of_le withDensity_rnDeriv_le μ ν

Depends on / 依赖: isLocallyFiniteMeasure_of_le, withDensity_rnDeriv_le
-/
instance withDensity.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
isLocallyFiniteMeasure_of_le withDensity_rnDeriv_le μ ν

section RNDerivFinite

/--
theorem `lintegral_rnDeriv_lt_top_of_measure_ne_top` / 定理 `lintegral_rnDeriv_lt_top_of_measure_ne_top`

English:
theorem lintegral_rnDeriv_lt_top_of_measure_ne_top
  given: (ν : Measure α) {s : Set α} (hs : μ s != ∞)
  proof: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ <= (singularPart μ ν) (toMeasu

中文:
定理 lintegral_rnDeriv_lt_top_of_measure_ne_top
  条件: (ν : Measure α) {s : Set α} (hs : μ s != ∞)
  证明: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ <= (singularPart μ ν) (toMeasu

Depends on / 依赖: ENNReal, HaveLebesgueDecomposition, Measure, Measure.add_apply, Measure.rnDeriv, Pi.zero_apply, add_apply, dif_neg, haveLebesgueDecomposition_add, hs.lt_top, le_add_self, lintegral_mono_set, lintegral_zero, lt_of_le_of_lt, lt_top, measurableSet_toMeasurable, measure_toMeasurable, rnDeriv, singularPart, subset_toMeasurable
-/
theorem lintegral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s != ∞) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ <= (singularPart μ ν) (toMeasurable μ s) + _ := le_add_self
      _ = μ s := by rw [← Measure.add_apply, ← haveLebesgueDecomposition_add, measure_toMeasurable]
      _ < ⊤ := hs.lt_top
  · simp only [Measure.rnDeriv, dif_neg hl, Pi.zero_apply, lintegral_zero, ENNReal.zero_lt_top]

/--
theorem `lintegral_rnDeriv_lt_top` / 定理 `lintegral_rnDeriv_lt_top`

English:
theorem lintegral_rnDeriv_lt_top
  given: (μ ν : Measure α) [IsFiniteMeasure μ]
  proof: by
  rw [← setLIntegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne

中文:
定理 lintegral_rnDeriv_lt_top
  条件: (μ ν : Measure α) [IsFiniteMeasure μ]
  证明: by
  rw [← setLIntegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne

Depends on / 依赖: lintegral_rnDeriv_lt_top_of_measure_ne_top, measure_lt_top, setLIntegral_univ
-/
theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞ := by
  rw [← setLIntegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne

/--
theorem `rnDeriv_lt_top` / 定理 `rnDeriv_lt_top`

English:
theorem rnDeriv_lt_top
  given: (μ ν : Measure α) [SigmaFinite μ]
  statement: forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
  proof: by
  suffices forall n, forallᵐ x ∂ν, x in spanningSets μ n -> μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurableSet_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (linteg

中文:
定理 rnDeriv_lt_top
  条件: (μ ν : Measure α) [SigmaFinite μ]
  结论: 对任意ᵐ x ∂ν, μ.rnDeriv ν x < ∞
  证明: by
  suffices forall n, forallᵐ x ∂ν, x in spanningSets μ n -> μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurableSet_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (linteg

Depends on / 依赖: ae_all_iff, ae_lt_top, ae_restrict_iff, filter_upwards, lintegral_rnDeriv_lt_top_of_measure_ne_top, measurableSet_spanningSets, measurable_rnDeriv, measure_spanningSets_lt_top, mem_spanningSetsIndex, rnDeriv, spanningSets
-/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
  suffices forall n, forallᵐ x ∂ν, x in spanningSets μ n -> μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurableSet_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (lintegral_rnDeriv_lt_top_of_measure_ne_top _ ?_).ne
  exact (measure_spanningSets_lt_top _ _).ne

/--
lemma `rnDeriv_ne_top` / 引理 `rnDeriv_ne_top`

English:
lemma rnDeriv_ne_top
  given: (μ ν : Measure α) [SigmaFinite μ]
  statement: forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
  proof: by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

中文:
引理 rnDeriv_ne_top
  条件: (μ ν : Measure α) [SigmaFinite μ]
  结论: 对任意ᵐ x ∂ν, μ.rnDeriv ν x != ∞
  证明: by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

Depends on / 依赖: Measure, Measure.rnDeriv_lt_top, filter_upwards, hx.ne, rnDeriv_lt_top
-/
lemma rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

end RNDerivFinite

/--
theorem `eq_singularPart` / 定理 `eq_singularPart`

English:
theorem eq_singularPart
  statement: {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  proof: by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine non

中文:
定理 eq_singularPart
  结论: {s : Measure α} {f : α -> 实数>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  证明: by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine non

Depends on / 依赖: HaveLebesgueDecomposition, add_zero, compl_inter, haveLebesgueDecomposition_spec, le_trans, measure_union_le, nonpos_iff_eq_zero, restrict, s.restrict, singularPart, withDensity
-/
theorem eq_singularPart {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃]; rw [hS₃]; rw [add_zero]
  have heq : s.restrict (S inter T)ᶜ = (μ.singularPart ν).restrict (S inter T)ᶜ := by
    ext1 A hA
    have hf : ν.withDensity f (A inter (S inter T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    have hrn : ν.withDensity (μ.rnDeriv ν) (A inter (S inter T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA]; rw [restrict_apply hA]; rw [← add_zero (s (A inter (S inter T)ᶜ))]; rw [← hf]; rw [← add_apply]; rw [←
      hadd]; rw [add_apply]; rw [hrn]; rw [add_zero]
  have heq' : forall A : Set α, MeasurableSet A -> s A = s.restrict (S inter T)ᶜ A := by
    intro A hA
    have hsinter : s (A inter (S inter T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    rw [restrict_apply hA]; rw [← sdiff_eq]; rw [AEDisjoint.measure_sdiff_left hsinter]
  ext1 A hA
  have hμinter : μ.singularPart ν (A inter (S inter T)) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
  rw [heq' A hA]; rw [heq]; rw [restrict_apply hA]; rw [← sdiff_eq]; rw [AEDisjoint.measure_sdiff_left hμinter]

/--
theorem `singularPart_smul` / 定理 `singularPart_smul`

English:
theorem singularPart_smul
  given: (μ ν : Measure α) (r : Real>=0)
  proof: by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : Real>=0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDe

中文:
定理 singularPart_smul
  条件: (μ ν : Measure α) (r : 实数>=0)
  证明: by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : Real>=0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDe

Depends on / 依赖: ENNReal, ENNReal.smul_def, HaveLebesgueDecomposition, MutuallySingular, MutuallySingular.smul, const_smul, dif_neg, eq_singularPart, haveLebesgueDecomposition_add, inv_s, measurable_rnDeriv, mutuallySingular_singularPart, singularPart, singularPart_zero, smul_add, smul_def, smul_zero, withDensity_smul, zero_smul
-/
theorem singularPart_smul (μ ν : Measure α) (r : Real>=0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : Real>=0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]; rw [← smul_add]; rw [← haveLebesgueDecomposition_add μ ν]; rw [ENNReal.smul_def]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg, smul_zero]
    refine fun hl' => hl ?_
    rw [← inv_smul_smul₀ hr μ]
    infer_instance

/--
theorem `singularPart_smul_right` / 定理 `singularPart_smul_right`

English:
theorem singularPart_smul_right
  given: (μ ν : Measure α) (r : Real>=0) (hr : r != 0)
  proof: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure

中文:
定理 singularPart_smul_right
  条件: (μ ν : Measure α) (r : 实数>=0) (hr : r != 0)
  证明: by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, ENNReal, ENNReal.smul_def, HaveLebesgueDecomposition, Pi.smul_apply, const_smul, convert, eq_singularPart, haveLebesgueDecomposition_add, measurable_rnDeriv, mono_ac, mutuallySingular_singularPart, singularPart, smul_absolutelyContinuous, smul_apply, smul_def, withDensity_smul, withDensity_smul_measure
-/
theorem singularPart_smul_right (μ ν : Measure α) (r : Real>=0) (hr : r != 0) :
    μ.singularPart (r • ν) = μ.singularPart ν := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure, ← withDensity_smul]
      swap; · exact (measurable_rnDeriv _ _).const_smul _
      convert! haveLebesgueDecomposition_add μ ν
      ext x
      simp only [Pi.smul_apply]
      rw [← ENNReal.smul_def]; rw [smul_inv_smul₀ hr]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg]
    refine fun hl' => hl ?_
    rw [← inv_smul_smul₀ hr ν]
    infer_instance

/--
theorem `singularPart_add` / 定理 `singularPart_add`

English:
theorem singularPart_add
  statement: (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
  proof: by
  refine (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  rw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← ad

中文:
定理 singularPart_add
  结论: (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
  证明: by
  refine (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  rw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← ad

Depends on / 依赖: add_assoc, add_comm, add_left, conv_rhs, eq_singularPart, haveLebesgueDecomposition_add, measurable_rnDeriv, mutuallySingular_singularPart, rnDeriv, singularPart, withDensity, withDensity_add_left
-/
theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  rw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← add_assoc, ← add_assoc]
  rw [← haveLebesgueDecomposition_add μ₁ ν]; rw [add_assoc]; rw [add_comm (ν.withDensity (μ₂.rnDeriv ν))]; rw [← haveLebesgueDecomposition_add μ₂ ν]

/--
lemma `singularPart_restrict` / 引理 `singularPart_restrict`

English:
lemma singularPart_restrict
  statement: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  proof: by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_ad

中文:
引理 singularPart_restrict
  结论: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  证明: by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_ad

Depends on / 依赖: Measure, Measure.eq_singularPart, Measure.mutuallySingular_singularPart, Measure.restrict_add, eq_singularPart, haveLebesgueDecomposition_add, indicator, measurable_rnDeriv, mutuallySingular_singularPart, restrict, restrict_add, restrict_withDensity, rnDeriv, s.indicator, withDensity_indicator
-/
lemma singularPart_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart ν = (μ.singularPart ν).restrict s := by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_add]; rw [← μ.haveLebesgueDecomposition_add ν]

/--
theorem `singularPart_eq_restrict'` / 定理 `singularPart_eq_restrict'`

English:
theorem singularPart_eq_restrict'
  statement: {s : Set α} [μ.HaveLebesgueDecomposition ν]
  proof: by
  conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
  rwa [restrict_add, restrict_eq_self_of_ae_mem, restrict_eq_zero.2 hνs, add_zero]

中文:
定理 singularPart_eq_restrict'
  结论: {s : Set α} [μ.HaveLebesgueDecomposition ν]
  证明: by
  conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
  rwa [restrict_add, restrict_eq_self_of_ae_mem, restrict_eq_zero.2 hνs, add_zero]

Depends on / 依赖: add_zero, conv_rhs, restrict_add, restrict_eq_self_of_ae_mem, restrict_eq_zero, singularPart_add_rnDeriv
-/
theorem singularPart_eq_restrict' {s : Set α} [μ.HaveLebesgueDecomposition ν]
    (hμs : μ.singularPart ν sᶜ = 0) (hνs : ν.withDensity (μ.rnDeriv ν) s = 0) :
    μ.singularPart ν = μ.restrict s := by
  conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
  rwa [restrict_add, restrict_eq_self_of_ae_mem, restrict_eq_zero.2 hνs, add_zero]

/--
theorem `singularPart_eq_restrict` / 定理 `singularPart_eq_restrict`

English:
theorem singularPart_eq_restrict
  statement: {s : Set α} [μ.HaveLebesgueDecomposition ν]
  proof: singularPart_eq_restrict' hμs withDensity_absolutelyContinuous _ _ hνs

中文:
定理 singularPart_eq_restrict
  结论: {s : Set α} [μ.HaveLebesgueDecomposition ν]
  证明: singularPart_eq_restrict' hμs withDensity_absolutelyContinuous _ _ hνs

Depends on / 依赖: singularPart_eq_restrict, withDensity_absolutelyContinuous
-/
theorem singularPart_eq_restrict {s : Set α} [μ.HaveLebesgueDecomposition ν]
    (hμs : μ.singularPart ν sᶜ = 0) (hνs : ν s = 0) :
    μ.singularPart ν = μ.restrict s :=
singularPart_eq_restrict' hμs withDensity_absolutelyContinuous _ _ hνs

/--
lemma `measure_sub_singularPart` / 引理 `measure_sub_singularPart`

English:
lemma measure_sub_singularPart
  statement: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  proof: by
  nth_rw 1 [← rnDeriv_add_singularPart μ ν]
  exact Measure.add_sub_cancel

中文:
引理 measure_sub_singularPart
  结论: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
  证明: by
  nth_rw 1 [← rnDeriv_add_singularPart μ ν]
  exact Measure.add_sub_cancel

Depends on / 依赖: Measure, Measure.add_sub_cancel, add_sub_cancel, nth_rw, rnDeriv_add_singularPart
-/
lemma measure_sub_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    [IsFiniteMeasure μ] :
    μ - μ.singularPart ν = ν.withDensity (μ.rnDeriv ν) := by
  nth_rw 1 [← rnDeriv_add_singularPart μ ν]
  exact Measure.add_sub_cancel

/--
lemma `measure_sub_rnDeriv` / 引理 `measure_sub_rnDeriv`

English:
lemma measure_sub_rnDeriv
  given: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsFiniteMeasure μ]
  proof: by
  nth_rw 1 [← singularPart_add_rnDeriv μ ν]
  exact Measure.add_sub_cancel

中文:
引理 measure_sub_rnDeriv
  条件: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsFiniteMeasure μ]
  证明: by
  nth_rw 1 [← singularPart_add_rnDeriv μ ν]
  exact Measure.add_sub_cancel

Depends on / 依赖: Measure, Measure.add_sub_cancel, add_sub_cancel, nth_rw, singularPart_add_rnDeriv
-/
lemma measure_sub_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsFiniteMeasure μ] :
    μ - ν.withDensity (μ.rnDeriv ν) = μ.singularPart ν := by
  nth_rw 1 [← singularPart_add_rnDeriv μ ν]
  exact Measure.add_sub_cancel

/--
theorem `eq_withDensity_rnDeriv` / 定理 `eq_withDensity_rnDeriv`

English:
theorem eq_withDensity_rnDeriv
  statement: {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  proof: by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine non

中文:
定理 eq_withDensity_rnDeriv
  结论: {s : Measure α} {f : α -> 实数>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  证明: by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine non

Depends on / 依赖: HaveLebesgueDecomposition, add_zero, compl_inter, haveLebesgueDecomposition_spec, le_trans, measure_union_le, nonpos_iff_eq_zero, restrict, rnDeriv, withDensity
-/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S inter T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃]; rw [hS₃]; rw [add_zero]
  have heq :
    (ν.withDensity f).restrict (S inter T) = (ν.withDensity (μ.rnDeriv ν)).restrict (S inter T) := by
    ext1 A hA
    have hs : s (A inter (S inter T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    have hsing : μ.singularPart ν (A inter (S inter T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
    rw [restrict_apply hA]; rw [restrict_apply hA]; rw [← add_zero (ν.withDensity f (A inter (S inter T)))]; rw [← hs]; rw [←
      add_apply]; rw [add_comm]; rw [← hadd]; rw [add_apply]; rw [hsing]; rw [zero_add]
  have heq' :
    forall A : Set α, MeasurableSet A -> ν.withDensity f A = (ν.withDensity f).restrict (S inter T) A := by
    intro A hA
    have hνfinter : ν.withDensity f (A inter (S inter T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact withDensity_absolutelyContinuous ν f hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA]; rw [← add_zero (ν.withDensity f (A inter (S inter T)))]; rw [← hνfinter]; rw [← sdiff_eq]; rw [measure_inter_add_sdiff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.withDensity (μ.rnDeriv ν) (A inter (S inter T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      withDensity_absolutelyContinuous ν (μ.rnDeriv ν) hνinter ▸
        measure_mono inter_subset_right
  rw [heq' A hA]; rw [heq]; rw [← add_zero ((ν.withDensity (μ.rnDeriv ν)).restrict (S inter T) A)]; rw [← hνrn]; rw [restrict_apply hA]; rw [← sdiff_eq]; rw [measure_inter_add_sdiff _ (hS₁.inter hT₁)]

/--
theorem `eq_withDensity_rnDeriv₀` / 定理 `eq_withDensity_rnDeriv₀`

English:
theorem eq_withDensity_rnDeriv₀
  statement: {s : Measure α} {f : α -> Real>=0∞}
  proof: by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

中文:
定理 eq_withDensity_rnDeriv₀
  结论: {s : Measure α} {f : α -> 实数>=0∞}
  证明: by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

Depends on / 依赖: ae_eq_mk, eq_withDensity_rnDeriv, hf.ae_eq_mk, hf.measurable_mk, measurable_mk, withDensity_congr_ae
-/
theorem eq_withDensity_rnDeriv₀ {s : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

/--
theorem `eq_rnDeriv₀` / 定理 `eq_rnDeriv₀`

English:
theorem eq_rnDeriv₀
  statement: [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞}
  proof: (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

中文:
定理 eq_rnDeriv₀
  结论: [SigmaFinite ν] {s : Measure α} {f : α -> 实数>=0∞}
  证明: (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

Depends on / 依赖: aemeasurable, measurable_rnDeriv, withDensity_eq_iff_of_sigmaFinite
-/
theorem eq_rnDeriv₀ [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν :=
  (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

/--
theorem `eq_rnDeriv` / 定理 `eq_rnDeriv`

English:
theorem eq_rnDeriv
  statement: [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  proof: eq_rnDeriv₀ hf.aemeasurable hs hadd

中文:
定理 eq_rnDeriv
  结论: [SigmaFinite ν] {s : Measure α} {f : α -> 实数>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
  证明: eq_rnDeriv₀ hf.aemeasurable hs hadd

Depends on / 依赖: aemeasurable, hf.aemeasurable
-/
theorem eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν :=
  eq_rnDeriv₀ hf.aemeasurable hs hadd

/--
theorem `rnDeriv_withDensity₀` / 定理 `rnDeriv_withDensity₀`

English:
theorem rnDeriv_withDensity₀
  statement: (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞}
  proof: have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

中文:
定理 rnDeriv_withDensity₀
  结论: (ν : Measure α) [SigmaFinite ν] {f : α -> 实数>=0∞}
  证明: have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

Depends on / 依赖: MutuallySingular, MutuallySingular.zero_left, withDensity, zero_add, zero_left
-/
theorem rnDeriv_withDensity₀ (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞}
    (hf : AEMeasurable f ν) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

/--
theorem `rnDeriv_withDensity` / 定理 `rnDeriv_withDensity`

English:
theorem rnDeriv_withDensity
  given: (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f)
  proof: rnDeriv_withDensity₀ ν hf.aemeasurable

中文:
定理 rnDeriv_withDensity
  条件: (ν : Measure α) [SigmaFinite ν] {f : α -> 实数>=0∞} (hf : Measurable f)
  证明: rnDeriv_withDensity₀ ν hf.aemeasurable

Depends on / 依赖: aemeasurable, hf.aemeasurable
-/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  rnDeriv_withDensity₀ ν hf.aemeasurable

/--
lemma `rnDeriv_restrict` / 引理 `rnDeriv_restrict`

English:
lemma rnDeriv_restrict
  statement: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
  proof: by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs]; rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_add]; rw [← μ.haveLebesgueD

中文:
引理 rnDeriv_restrict
  结论: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
  证明: by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs]; rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_add]; rw [← μ.haveLebesgueD

Depends on / 依赖: Measure, Measure.restrict_add, eq_rnDeriv, haveLebesgueDecomposition_add, indicator, measurable_rnDeriv, mutuallySingular_singularPart, restrict, restrict_add, restrict_withDensity, singularPart, singularPart_restrict, withDensity_indicator
-/
lemma rnDeriv_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv ν =ᵐ[ν] s.indicator (μ.rnDeriv ν) := by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs]; rw [withDensity_indicator hs]; rw [← restrict_withDensity hs]; rw [← Measure.restrict_add]; rw [← μ.haveLebesgueDecomposition_add ν]

/--
theorem `rnDeriv_restrict_self` / 定理 `rnDeriv_restrict_self`

English:
theorem rnDeriv_restrict_self
  given: (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)

中文:
定理 rnDeriv_restrict_self
  条件: (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s)
  证明: by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)

Depends on / 依赖: indicator, measurable_one, measurable_one.indicator, rnDeriv_withDensity, withDensity_indicator_one
-/
theorem rnDeriv_restrict_self (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)

/--
theorem `rnDeriv_smul_left` / 定理 `rnDeriv_smul_left`

English:
theorem rnDeriv_smul_left
  statement: (ν μ : Measure α) [IsFiniteMeasure ν]
  proof: by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
 

中文:
定理 rnDeriv_smul_left
  结论: (ν μ : Measure α) [IsFiniteMeasure ν]
  证明: by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
 

Depends on / 依赖: ENNReal, ENNReal.smul_def, Measure, Measure.add_right_inj, add_right_inj, aemeasurable, aemeasurable.const, haveLebesgueDecomposition_add, measurable_rnDeriv, rnDeriv, simp_rw, singularPart, singularPart_smul, smul_add, smul_def, withDensity, withDensity_eq_iff, withDensity_smul
-/
theorem rnDeriv_smul_left (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] (r : Real>=0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ]; rw [singularPart_smul]; rw [← smul_add]; rw [← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top (r • ν) μ).ne

/--
theorem `rnDeriv_smul_left_of_ne_top` / 定理 `rnDeriv_smul_left_of_ne_top`

English:
theorem rnDeriv_smul_left_of_ne_top
  statement: (ν μ : Measure α) [IsFiniteMeasure ν]
  proof: by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

中文:
定理 rnDeriv_smul_left_of_ne_top
  结论: (ν μ : Measure α) [IsFiniteMeasure ν]
  证明: by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, ENNReal.smul_def, coe_toNNReal, r.toNNReal, rnDeriv, rnDeriv_smul_left, smul_def, toNNReal
-/
theorem rnDeriv_smul_left_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : Real>=0∞} (hr : r != ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/--
theorem `rnDeriv_smul_right` / 定理 `rnDeriv_smul_right`

English:
theorem rnDeriv_smul_right
  statement: (ν μ : Measure α) [IsFiniteMeasure ν]
  proof: by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegr

中文:
定理 rnDeriv_smul_right
  结论: (ν μ : Measure α) [IsFiniteMeasure ν]
  证明: by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegr

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero, ENNReal.smul_def, absolutelyContinuous_smul, ae_le, aemeasurable, aemeasurable.const_smul, coe_ne_zero, const_smul, lintegral_rnDeriv_lt_top, measurable_rnDeriv, rnDeriv, rotate_left, simp_rw, singularPart, smul_def, withDensity, withDensity_eq_iff, withDensity_smul
-/
theorem rnDeriv_smul_right (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : Real>=0} (hr : r != 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top ν _).ne
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ)]; rw [singularPart_smul_right _ _ _ hr]; rw [ENNReal.smul_def r]; rw [withDensity_smul_measure]; rw [← ENNReal.smul_def]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [inv_mul_cancel₀ hr]; rw [one_smul]
    exact ν.haveLebesgueDecomposition_add μ

/--
theorem `rnDeriv_smul_right_of_ne_top` / 定理 `rnDeriv_smul_right_of_ne_top`

English:
theorem rnDeriv_smul_right_of_ne_top
  statement: (ν μ : Measure α) [IsFiniteMeasure ν]
  proof: by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNR

中文:
定理 rnDeriv_smul_right_of_ne_top
  结论: (ν μ : Measure α) [IsFiniteMeasure ν]
  证明: by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNR

Depends on / 依赖: ENNReal, ENNReal.coe_inv, ENNReal.coe_toNNReal, ENNReal.smul_def, ENNReal.toNNReal_eq_zero_iff, Pi.smul_apply, coe_inv, coe_toNNReal, hr_ne_top, ne_eq, r.toNNReal, rnDeriv, rnDeriv_smul_right, simp_rw, smul_apply, smul_def, smul_eq_mul, toNNReal, toNNReal_eq_zero_iff
-/
theorem rnDeriv_smul_right_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : Real>=0∞} (hr : r != 0) (hr_ne_top : r != ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.coe_inv]; rw [ENNReal.coe_toNNReal hr_ne_top]
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  simp_rw [this, ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top] at h
  exact h

/--
theorem `rnDeriv_smul_same` / 定理 `rnDeriv_smul_same`

English:
theorem rnDeriv_smul_same
  statement: (ν μ : Measure α) [IsFiniteMeasure ν]
  proof: by
  filter_upwards [rnDeriv_smul_left ν μ r, rnDeriv_smul_right (r • ν) μ hr] with x hx1 hx2
  simp [hx1, hx2, hr]

中文:
定理 rnDeriv_smul_same
  结论: (ν μ : Measure α) [IsFiniteMeasure ν]
  证明: by
  filter_upwards [rnDeriv_smul_left ν μ r, rnDeriv_smul_right (r • ν) μ hr] with x hx1 hx2
  simp [hx1, hx2, hr]

Depends on / 依赖: filter_upwards, rnDeriv_smul_left, rnDeriv_smul_right
-/
theorem rnDeriv_smul_same (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : Real>=0} (hr : r != 0) :
    (r • ν).rnDeriv (r • μ) =ᵐ[μ] ν.rnDeriv μ := by
  filter_upwards [rnDeriv_smul_left ν μ r, rnDeriv_smul_right (r • ν) μ hr] with x hx1 hx2
  simp [hx1, hx2, hr]

/--
lemma `rnDeriv_add` / 引理 `rnDeriv_add`

English:
lemma rnDeriv_add
  statement: (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
  proof: by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [singularPart_add]

中文:
引理 rnDeriv_add
  结论: (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
  证明: by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [singularPart_add]

Depends on / 依赖: add_assoc, add_comm, add_right_inj, haveLebesgueDecomposition_add, measurable_rnDeriv, rnDeriv, singularPart, singularPart_add, withDensity, withDensity_add_left, withDensity_eq_iff
-/
lemma rnDeriv_add (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    [(ν₁ + ν₂).HaveLebesgueDecomposition μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [singularPart_add]; rw [withDensity_add_left (measurable_rnDeriv _ _)]; rw [add_assoc]; rw [add_comm (ν₂.singularPart μ)]; rw [add_assoc]; rw [add_comm _ (ν₂.singularPart μ)]; rw [← ν₂.haveLebesgueDecomposition_add μ]; rw [← add_assoc]; rw [← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable
  · exact (lintegral_rnDeriv_lt_top (ν₁ + ν₂) μ).ne

/--
theorem `exists_positive_of_not_mutuallySingular` / 定理 `exists_positive_of_not_mutuallySingular`

English:
theorem exists_positive_of_not_mutuallySingular
  statement: (μ ν : Measure α) [IsFiniteMeasure μ]
  proof: by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have h_decomp (n : Nat) : exists s : Set α, MeasurableSet s
        ∧ (forall t, MeasurableSet t -> ((1 / (n + 1) : Real>=0) • ν) (t inter s) <= μ (t inter s))
        ∧ (forall t, MeasurableSet t -> μ (t inter sᶜ) <= ((1 /

中文:
定理 exists_positive_of_not_mutuallySingular
  结论: (μ ν : Measure α) [IsFiniteMeasure μ]
  证明: by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have h_decomp (n : Nat) : exists s : Set α, MeasurableSet s
        ∧ (forall t, MeasurableSet t -> ((1 / (n + 1) : Real>=0) • ν) (t inter s) <= μ (t inter s))
        ∧ (forall t, MeasurableSet t -> μ (t inter sᶜ) <= ((1 /
-/
theorem exists_positive_of_not_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ¬ μ ⟂ₘ ν) :
    exists ε : Real>=0, 0 < ε ∧
      exists E : Set α, MeasurableSet E ∧ 0 < ν E
        ∧ forall A, MeasurableSet A -> ε * ν (A inter E) <= μ (A inter E) := by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have h_decomp (n : Nat) : exists s : Set α, MeasurableSet s
        ∧ (forall t, MeasurableSet t -> ((1 / (n + 1) : Real>=0) • ν) (t inter s) <= μ (t inter s))
        ∧ (forall t, MeasurableSet t -> μ (t inter sᶜ) <= ((1 / (n + 1) : Real>=0) • ν) (t inter sᶜ)) := by
    obtain ⟨s, hs, hs_le, hs_ge⟩ := hahn_decomposition μ ((1 / (n + 1) : Real>=0) • ν)
    refine ⟨s, hs, fun t ht => ?_, fun t ht => ?_⟩
    · exact hs_le (t inter s) (ht.inter hs) inter_subset_right
    · exact hs_ge (t inter sᶜ) (ht.inter hs.compl) inter_subset_right
  choose f hf₁ hf₂ hf₃ using h_decomp
  -- set `A` to be the intersection of all the negative parts of obtained Hahn decompositions
  -- and we show that `μ A = 0`
  let A := ⋂ n, (f n)ᶜ
  have hAmeas : MeasurableSet A := MeasurableSet.iInter fun n => (hf₁ n).compl
  have hA₂ (n : Nat) (t : Set α) (ht : MeasurableSet t) :
      μ (t inter A) <= ((1 / (n + 1) : Real>=0) • ν) (t inter A) := by
    specialize hf₃ n (t inter A) (ht.inter hAmeas)
    have : A inter (f n)ᶜ = A := inter_eq_left.mpr (iInter_subset _ n)
    rwa [inter_assoc, this] at hf₃
  have hA₃ (n : Nat) : μ A <= (1 / (n + 1) : Real>=0) * ν A := by simpa using hA₂ n univ .univ
  have hμ : μ A = 0 := by
    lift μ A to Real>=0 using measure_ne_top _ _ with μA
    lift ν A to Real>=0 using measure_ne_top _ _ with νA
    rw [ENNReal.coe_eq_zero]
    by_cases! hb : 0 < νA
    · suffices forall b, 0 < b -> μA <= b by
        by_contra h
        have h' := this (μA / 2) (half_pos (zero_lt_iff.2 h))
        rw [← @Classical.not_not (μA <= μA / 2)] at h'
        exact h' (not_le.2 (NNReal.half_lt_self h))
      intro c hc
      have : exists n : Nat, 1 / (n + 1 : Real) < c * (νA : Real)⁻¹ := by
        refine exists_nat_one_div_lt ?_
        positivity
      rcases this with ⟨n, hn⟩
      have hb₁ : (0 : Real) < (νA : Real)⁻¹ := by rw [_root_.inv_pos]; exact hb
      have h' : 1 / (↑n + 1) * νA < c := by
        rw [← NNReal.coe_lt_coe]; rw [← mul_lt_mul_iff_left₀ hb₁]; rw [NNReal.coe_mul]; rw [mul_assoc]; rw [←
          NNReal.coe_inv]; rw [← NNReal.coe_mul]; rw [mul_inv_cancel₀]; rw [← NNReal.coe_mul]; rw [mul_one]; rw [NNReal.coe_inv]
        · exact hn
        · exact hb.ne'
      refine le_trans ?_ h'.le
      rw [← ENNReal.coe_le_coe]; rw [ENNReal.coe_mul]
      exact hA₃ n
    · rw [le_zero_iff] at hb
      simpa [hb] using hA₃ 0
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw [MutuallySingular] at h; push Not at h
  have := h _ hAmeas hμ
  simp_rw [A, compl_iInter, compl_compl] at this
  -- as `Aᶜ = ⋃ n, f n`, `ν Aᶜ > 0` implies there exists some `n` such that `ν (f n) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null this
  -- thus, choosing `f n` as the set `E` suffices
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩

namespace LebesgueDecomposition

/--
Definition of `measurableLE` / `measurableLE` 的定义

English:
definition measurableLE
  signature: (μ ν : Measure α)
  body: {f | Measurable f ∧ forall (A : Set α), MeasurableSet A -> (∫⁻ x in A, f x ∂μ) <= ν A}

中文:
定义 measurableLE
  签名: (μ ν : Measure α)
  定义体: {f | Measurable f ∧ forall (A : Set α), MeasurableSet A -> (∫⁻ x in A, f x ∂μ) <= ν A}

Depends on / 依赖: Measurable, MeasurableSet
-/
def measurableLE (μ ν : Measure α) : Set (α -> Real>=0∞) :=
  {f | Measurable f ∧ forall (A : Set α), MeasurableSet A -> (∫⁻ x in A, f x ∂μ) <= ν A}

/--
theorem `zero_mem_measurableLE` / 定理 `zero_mem_measurableLE`

English:
theorem zero_mem_measurableLE
  statement: (0 : α -> Real>=0∞) in measurableLE μ ν
  proof: ⟨measurable_zero, fun A _ => by simp⟩

中文:
定理 zero_mem_measurableLE
  结论: (0 : α -> 实数>=0∞) in measurableLE μ ν
  证明: ⟨measurable_zero, fun A _ => by simp⟩

Depends on / 依赖: measurable_zero
-/
theorem zero_mem_measurableLE : (0 : α -> Real>=0∞) in measurableLE μ ν :=
  ⟨measurable_zero, fun A _ => by simp⟩

/--
theorem `sup_mem_measurableLE` / 定理 `sup_mem_measurableLE`

English:
theorem sup_mem_measurableLE
  statement: {f g : α -> Real>=0∞} (hf : f in measurableLE μ ν)
  proof: by
  refine ⟨Measurable.max hf.1 hg.1, fun A hA => ?_⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [setLIntegral_max hf.1 hg.1]
  refine (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq ?_
  simp only [← not_le, ← compl_ofPred, ← sdiff_eq]


中文:
定理 sup_mem_measurableLE
  结论: {f g : α -> 实数>=0∞} (hf : f in measurableLE μ ν)
  证明: by
  refine ⟨Measurable.max hf.1 hg.1, fun A hA => ?_⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [setLIntegral_max hf.1 hg.1]
  refine (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq ?_
  simp only [← not_le, ← compl_ofPred, ← sdiff_eq]


Depends on / 依赖: Measurable, Measurable.max, add_le_add, compl_ofPred, hA.inter, measurableSet_le, measurableSet_lt, measure_inter_add_sdiff, not_le, sdiff_eq, setLIntegral_max, trans_eq
-/
theorem sup_mem_measurableLE {f g : α -> Real>=0∞} (hf : f in measurableLE μ ν)
    (hg : g in measurableLE μ ν) : (fun a => f a ⊔ g a) in measurableLE μ ν := by
  refine ⟨Measurable.max hf.1 hg.1, fun A hA => ?_⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [setLIntegral_max hf.1 hg.1]
  refine (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq ?_
  simp only [← not_le, ← compl_ofPred, ← sdiff_eq]
  exact measure_inter_add_sdiff _ (measurableSet_le hf.1 hg.1)

/--
theorem `iSup_succ_eq_sup` / 定理 `iSup_succ_eq_sup`

English:
theorem iSup_succ_eq_sup
  given: {α} (f : Nat -> α -> Real>=0∞) (m : Nat) (a : α)
  proof: by
  set c := ⨆ (k : Nat) (_ : k <= m + 1), f k a with hc
  set d := f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a with hd
  rw [le_antisymm_iff]; rw [hc]; rw [hd]
  constructor
  · refine iSup₂_le fun n hn => ?_
    rcases Nat.of_le_succ hn with (h | h)
    · exact le_sup_of_le_right (le_iSup₂ (f :=

中文:
定理 iSup_succ_eq_sup
  条件: {α} (f : 自然数 -> α -> 实数>=0∞) (m : 自然数) (a : α)
  证明: by
  set c := ⨆ (k : Nat) (_ : k <= m + 1), f k a with hc
  set d := f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a with hd
  rw [le_antisymm_iff]; rw [hc]; rw [hd]
  constructor
  · refine iSup₂_le fun n hn => ?_
    rcases Nat.of_le_succ hn with (h | h)
    · exact le_sup_of_le_right (le_iSup₂ (f :=

Depends on / 依赖: Nat.of_le_succ, biSup_mono, hn.trans, le_antisymm_iff, le_rfl, le_succ, le_sup_left, le_sup_of_le_right, m.le_succ, m.succ, of_le_succ, sup_le
-/
theorem iSup_succ_eq_sup {α} (f : Nat -> α -> Real>=0∞) (m : Nat) (a : α) :
    ⨆ (k : Nat) (_ : k <= m + 1), f k a = f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a := by
  set c := ⨆ (k : Nat) (_ : k <= m + 1), f k a with hc
  set d := f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a with hd
  rw [le_antisymm_iff]; rw [hc]; rw [hd]
  constructor
  · refine iSup₂_le fun n hn => ?_
    rcases Nat.of_le_succ hn with (h | h)
    · exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k <= m) => f k a) n h)
    · exact h ▸ le_sup_left
  · refine sup_le ?_ (biSup_mono fun n hn => hn.trans m.le_succ)
    exact @le_iSup₂ Real>=0∞ Nat (fun i => i <= m + 1) _ _ (m + 1) le_rfl

/--
theorem `iSup_mem_measurableLE` / 定理 `iSup_mem_measurableLE`

English:
theorem iSup_mem_measurableLE
  given: (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE μ ν) (n : Nat)
  proof: by
  induction n with
  | zero =>
    constructor
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  | succ m hm =>
    have :
      (fun a : α => ⨆ (k : Nat) (_ : k <= m + 1), f k a) = fun a =>
        f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a :=
      funext fun _ => iSup_succ_eq_su

中文:
定理 iSup_mem_measurableLE
  条件: (f : 自然数 -> α -> 实数>=0∞) (hf : 对任意 n, f n in measurableLE μ ν) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    constructor
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  | succ m hm =>
    have :
      (fun a : α => ⨆ (k : Nat) (_ : k <= m + 1), f k a) = fun a =>
        f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a :=
      funext fun _ => iSup_succ_eq_su

Depends on / 依赖: Measurable, Measurable.iSup_Prop, iSup_Prop, iSup_succ_eq_sup, m.succ, sup_mem_measurableLE
-/
theorem iSup_mem_measurableLE (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE μ ν) (n : Nat) :
    (fun x => ⨆ (k) (_ : k <= n), f k x) in measurableLE μ ν := by
  induction n with
  | zero =>
    constructor
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  | succ m hm =>
    have :
      (fun a : α => ⨆ (k : Nat) (_ : k <= m + 1), f k a) = fun a =>
        f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a :=
      funext fun _ => iSup_succ_eq_sup _ _ _
    refine ⟨.iSup fun n => Measurable.iSup_Prop _ (hf n).1, fun A hA => ?_⟩
    rw [this]; exact (sup_mem_measurableLE (hf m.succ) hm).2 A hA

/--
theorem `iSup_mem_measurableLE'` / 定理 `iSup_mem_measurableLE'`

English:
theorem iSup_mem_measurableLE'
  given: (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE μ ν) (n : Nat)
  proof: by
  convert! iSup_mem_measurableLE f hf n
  simp

中文:
定理 iSup_mem_measurableLE'
  条件: (f : 自然数 -> α -> 实数>=0∞) (hf : 对任意 n, f n in measurableLE μ ν) (n : 自然数)
  证明: by
  convert! iSup_mem_measurableLE f hf n
  simp

Depends on / 依赖: convert, iSup_mem_measurableLE
-/
theorem iSup_mem_measurableLE' (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE μ ν) (n : Nat) :
    (⨆ (k) (_ : k <= n), f k) in measurableLE μ ν := by
  convert! iSup_mem_measurableLE f hf n
  simp

section SuprLemmas

--TODO: these statements should be moved elsewhere

/--
theorem `iSup_monotone` / 定理 `iSup_monotone`

English:
theorem iSup_monotone
  given: {α : Type*} (f : Nat -> α -> Real>=0∞)
  proof: fun _ _ hnm _ => biSup_mono fun _ => ge_trans hnm

中文:
定理 iSup_monotone
  条件: {α : 类型} (f : 自然数 -> α -> 实数>=0∞)
  证明: fun _ _ hnm _ => biSup_mono fun _ => ge_trans hnm

Depends on / 依赖: biSup_mono, ge_trans
-/
theorem iSup_monotone {α : Type*} (f : Nat -> α -> Real>=0∞) :
    Monotone fun n x => ⨆ (k) (_ : k <= n), f k x :=
  fun _ _ hnm _ => biSup_mono fun _ => ge_trans hnm

/--
theorem `iSup_monotone'` / 定理 `iSup_monotone'`

English:
theorem iSup_monotone'
  given: {α : Type*} (f : Nat -> α -> Real>=0∞) (x : α)
  proof: fun _ _ hnm => iSup_monotone f hnm x

中文:
定理 iSup_monotone'
  条件: {α : 类型} (f : 自然数 -> α -> 实数>=0∞) (x : α)
  证明: fun _ _ hnm => iSup_monotone f hnm x

Depends on / 依赖: iSup_monotone
-/
theorem iSup_monotone' {α : Type*} (f : Nat -> α -> Real>=0∞) (x : α) :
    Monotone fun n => ⨆ (k) (_ : k <= n), f k x := fun _ _ hnm => iSup_monotone f hnm x

/--
theorem `iSup_le_le` / 定理 `iSup_le_le`

English:
theorem iSup_le_le
  given: {α : Type*} (f : Nat -> α -> Real>=0∞) (n k : Nat) (hk : k <= n)
  proof: fun x => le_iSup₂ (f := fun k (_ : k <= n) => f k x) k hk

中文:
定理 iSup_le_le
  条件: {α : 类型} (f : 自然数 -> α -> 实数>=0∞) (n k : 自然数) (hk : k <= n)
  证明: fun x => le_iSup₂ (f := fun k (_ : k <= n) => f k x) k hk
-/
theorem iSup_le_le {α : Type*} (f : Nat -> α -> Real>=0∞) (n k : Nat) (hk : k <= n) :
    f k <= fun x => ⨆ (k) (_ : k <= n), f k x :=
  fun x => le_iSup₂ (f := fun k (_ : k <= n) => f k x) k hk

end SuprLemmas

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `measurableLEEval` / `measurableLEEval` 的定义

English:
definition measurableLEEval
  signature: (μ ν : Measure α)
  body: (fun f : α -> Real>=0∞ => ∫⁻ x, f x ∂μ) '' measurableLE μ ν

中文:
定义 measurableLEEval
  签名: (μ ν : Measure α)
  定义体: (fun f : α -> Real>=0∞ => ∫⁻ x, f x ∂μ) '' measurableLE μ ν

Depends on / 依赖: measurableLE
-/
noncomputable def measurableLEEval (μ ν : Measure α) : Set Real>=0∞ :=
  (fun f : α -> Real>=0∞ => ∫⁻ x, f x ∂μ) '' measurableLE μ ν

end LebesgueDecomposition

open LebesgueDecomposition

/--
theorem `haveLebesgueDecomposition_of_finiteMeasure` / 定理 `haveLebesgueDecomposition_of_finiteMeasure`

English:
theorem haveLebesgueDecomposition_of_finiteMeasure
  given: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
    have h := @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
      ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_

中文:
定理 haveLebesgueDecomposition_of_finiteMeasure
  条件: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  证明: by
    have h := @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
      ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, exists_seq_tendsto_sSup, measurableLEEval, zero_mem_measurableLE
-/
theorem haveLebesgueDecomposition_of_finiteMeasure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HaveLebesgueDecomposition μ ν where
  lebesgue_decomposition := by
    have h := @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
      ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_ : k <= n), f k with hξ
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξ₁ : sSup (measurableLEEval ν μ) = ∫⁻ a, ξ a ∂ν := by
      have := @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (fun n => ⨆ (k) (_ : k <= n), f k)
          (⨆ (n) (k) (_ : k <= n), f k) ?_ ?_ ?_
      · refine tendsto_nhds_unique ?_ this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds (fun n => ?_)
          fun n => ?_
        · rw [← hf₂ n]
          apply lintegral_mono
          convert! iSup_le_le f n n le_rfl
          simp only [iSup_apply]
        · exact le_sSup ⟨⨆ (k : Nat) (_ : k <= n), f k, iSup_mem_measurableLE' _ hf₁ _, rfl⟩
      · intro n
        refine Measurable.aemeasurable ?_
        convert! (iSup_mem_measurableLE _ hf₁ n).1
        simp
      · refine Filter.Eventually.of_forall fun a => ?_
        simp [iSup_monotone' f _]
      · refine Filter.Eventually.of_forall fun a => ?_
        simp [tendsto_atTop_iSup (iSup_monotone' f a)]
    have hξm : Measurable ξ := by
      convert! Measurable.iSup fun n => (iSup_mem_measurableLE _ hf₁ n).1
      simp [hξ]
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξle A (hA : MeasurableSet A) : ∫⁻ a in A, ξ a ∂ν <= μ A := by
        rw [hξ]
        simp_rw [iSup_apply]
        rw [lintegral_iSup (fun n => (iSup_mem_measurableLE _ hf₁ n).1) (iSup_monotone _)]
        exact iSup_le fun n => (iSup_mem_measurableLE _ hf₁ n).2 A hA
    have hle : ν.withDensity ξ <= μ := by
      refine le_intro fun B hB _ => ?_
      rw [withDensity_apply _ hB]
      exact hξle B hB
    have : IsFiniteMeasure (ν.withDensity ξ) := isFiniteMeasure_of_le _ hle
    -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.withDensity ξ`
    -- since we need `μ₁ + ν.withDensity ξ = μ`
    set μ₁ := μ - ν.withDensity ξ with hμ₁
    refine ⟨⟨μ₁, ξ⟩, hξm, ?_, ?_⟩
    · by_contra h
      -- if they are not mutually singular, then from `exists_positive_of_not_mutuallySingular`,
      -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
      -- positive with respect to `ν - εμ`
      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutuallySingular μ₁ ν h
      simp_rw [hμ₁] at hE₃
      -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
      have hε₂ (A : Set α) (hA : MeasurableSet A) : ∫⁻ a in A inter E, ε + ξ a ∂ν <= μ (A inter E) := by
        specialize hE₃ A hA
        rw [lintegral_add_left measurable_const]; rw [lintegral_const]; rw [restrict_apply_univ]
        rw [Measure.sub_apply (hA.inter hE₁) hle]; rw [withDensity_apply _ (hA.inter hE₁)] at hE₃
        refine add_le_of_le_tsub_right_of_le (hξle _ (hA.inter hE₁)) hE₃
      -- from this, we can show `ξ + ε * E.indicator` is a function in `measurableLE` with
      -- integral greater than `ξ`
      have hξε : (ξ + E.indicator fun _ => (ε : Real>=0∞)) in measurableLE ν μ := by
        refine ⟨hξm.add (measurable_const.indicator hE₁), fun A hA => ?_⟩
        have : ∫⁻ a in A, (ξ + E.indicator fun _ => (ε : Real>=0∞)) a ∂ν =
            ∫⁻ a in A inter E, ε + ξ a ∂ν + ∫⁻ a in A \ E, ξ a ∂ν := by
          simp only [lintegral_add_left measurable_const, lintegral_add_left hξm,
            setLIntegral_const, add_assoc, lintegral_inter_add_sdiff _ _ hE₁, Pi.add_apply,
            lintegral_indicator hE₁, restrict_apply hE₁]
          rw [inter_comm]; rw [add_comm]
        rw [this]; rw [← measure_inter_add_sdiff A hE₁]
        exact add_le_add (hε₂ A hA) (hξle (A \ E) (hA.diff hE₁))
      have : (∫⁻ a, ξ a + E.indicator (fun _ => (ε : Real>=0∞)) a ∂ν) <= sSup (measurableLEEval ν μ) :=
        le_sSup ⟨ξ + E.indicator fun _ => (ε : Real>=0∞), hξε, rfl⟩
      -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine not_lt.2 this ?_
      rw [hξ₁]; rw [lintegral_add_left hξm]; rw [lintegral_indicator hE₁]; rw [setLIntegral_const]
      refine ENNReal.lt_add_right ?_ (ENNReal.mul_pos_iff.2 ⟨ENNReal.coe_pos.2 hε₁, hE₂⟩).ne'
      have := measure_ne_top (ν.withDensity ξ) univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    -- since `ν.withDensity ξ ≤ μ`, it is clear that `μ = μ₁ + ν.withDensity ξ`
    · rw [hμ₁]
      ext1 A hA
      rw [Measure.coe_add]; rw [Pi.add_apply]; rw [Measure.sub_apply hA hle]; rw [add_comm]; rw [add_tsub_cancel_of_le (hle A)]

/--
theorem `HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure` / 定理 `HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure`

English:
theorem HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure
  statement: [SFinite μ]
  proof: sum_sfiniteSeq μ ▸ sum_left _

中文:
定理 HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure
  结论: [SFinite μ]
  证明: sum_sfiniteSeq μ ▸ sum_left _

Depends on / 依赖: sum_left, sum_sfiniteSeq
-/
theorem HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure [SFinite μ]
    (_h : forall (μ : Measure α) [IsFiniteMeasure μ], HaveLebesgueDecomposition μ ν) :
    HaveLebesgueDecomposition μ ν :=
  sum_sfiniteSeq μ ▸ sum_left _

attribute [local instance] haveLebesgueDecomposition_of_finiteMeasure

-- see Note [lower instance priority]
variable (μ ν) in
/-- **The Lebesgue decomposition theorem**:
Any s-finite measure `μ` has Lebesgue decomposition with respect to any σ-finite measure `ν`.
That is to say, there exist a measure `ξ` and a measurable function `f`,
such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f` -/
nonrec instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite
    [SFinite μ] [SigmaFinite ν] : HaveLebesgueDecomposition μ ν := by
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · exact .sfinite_of_isFiniteMeasure fun μ _ => this μ ‹_›
  -- Take a disjoint cover that consists of sets of finite measure `ν`.
  set s : Nat -> Set α := disjointed (spanningSets ν)
have hsm : forall n, MeasurableSet (s n) := .disjointed measurableSet_spanningSets _
  have hs : forall n, Fact (ν (s n) < ⊤) := fun n =>
    ⟨lt_of_le_of_lt (measure_mono <| disjointed_le ..) (measure_spanningSets_lt_top ν n)⟩
  -- Note that the restrictions of `μ` and `ν` to `s n` are finite measures.
  -- Therefore, as we proved above, these restrictions have a Lebesgue decomposition.
  -- Let `ξ n` and `f n` be the singular part and the Radon-Nikodym derivative
  -- of these restrictions.
  set ξ : Nat -> Measure α := fun n : Nat => singularPart (.restrict μ (s n)) (.restrict ν (s n))
  set f : Nat -> α -> Real>=0∞ := fun n => (s n).indicator (rnDeriv (.restrict μ (s n)) (.restrict ν (s n)))
  have hfm (n : Nat) : Measurable (f n) := by measurability
  -- Each `ξ n` is supported on `s n` and is mutually singular with the restriction of `ν` to `s n`.
  -- Therefore, `ξ n` is mutually singular with `ν`, hence their sum is mutually singular with `ν`.
  have hξ : .sum ξ ⟂ₘ ν := by
    refine MutuallySingular.sum_left.2 fun n => ?_
    rw [← ν.restrict_add_restrict_compl (hsm n)]
    refine (mutuallySingular_singularPart ..).add_right (.singularPart ?_ _)
    refine ⟨(s n)ᶜ, (hsm n).compl, ?_⟩
    simp [hsm]
  -- Finally, the sum of all `ξ n` and measure `ν` with the density `∑' n, f n`
  -- is equal to `μ`, thus `(Measure.sum ξ, ∑' n, f n)` is a Lebesgue decomposition for `μ` and `ν`.
  have hadd : .sum ξ + ν.withDensity (∑' n, f n) = μ := calc
    .sum ξ + ν.withDensity (∑' n, f n) = .sum fun n => ξ n + ν.withDensity (f n) := by
      rw [withDensity_tsum hfm]; rw [Measure.sum_add_sum]
    _ = .sum fun n => .restrict μ (s n) := by
      simp_rw [ξ, f, withDensity_indicator (hsm _), singularPart_add_rnDeriv]
    _ = μ := sum_restrict_disjointed_spanningSets ..
  exact ⟨⟨(.sum ξ, ∑' n, f n), by fun_prop, hξ, hadd.symm⟩⟩

section rnDeriv

/--
theorem `rnDeriv_smul_left'` / 定理 `rnDeriv_smul_left'`

English:
theorem rnDeriv_smul_left'
  given: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : Real>=0)
  proof: by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right

中文:
定理 rnDeriv_smul_left'
  条件: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : 实数>=0)
  证明: by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right

Depends on / 依赖: ENNReal, ENNReal.smul_def, Measure, Measure.add_right_inj, add_right_inj, aemeasurable, haveLebesgueDecomposition_add, measurable_rnDeriv, rnDeriv, simp_rw, singularPart, singularPart_smul, smul_add, smul_def, withDensity, withDensity_eq_iff_of_sigmaFinite, withDensity_smul
-/
theorem rnDeriv_smul_left' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : Real>=0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ]; rw [singularPart_smul]; rw [← smul_add]; rw [← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/--
theorem `rnDeriv_smul_left_of_ne_top'` / 定理 `rnDeriv_smul_left_of_ne_top'`

English:
theorem rnDeriv_smul_left_of_ne_top'
  statement: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  proof: by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left' ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

中文:
定理 rnDeriv_smul_left_of_ne_top'
  结论: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  证明: by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left' ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, ENNReal.smul_def, coe_toNNReal, r.toNNReal, rnDeriv, rnDeriv_smul_left, smul_def, toNNReal
-/
theorem rnDeriv_smul_left_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : Real>=0∞} (hr : r != ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left' ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/--
theorem `rnDeriv_smul_right'` / 定理 `rnDeriv_smul_right'`

English:
theorem rnDeriv_smul_right'
  statement: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  proof: by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + with

中文:
定理 rnDeriv_smul_right'
  结论: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  证明: by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + with

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero, ENNReal.smul_def, absolutelyContinuous_smul, add_right_inj, ae_le, coe_ne_zero, haveLebesgueDecomposition_add, measurable_rnDeriv, rnDeriv, simp_rw, singularPart, singularPart_smul_right, smul_def, withDensity, withDensity_eq_iff_of_sigmaFinite, withDensity_smul
-/
theorem rnDeriv_smul_right' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : Real>=0} (hr : r != 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ)]; rw [singularPart_smul_right _ _ _ hr]; rw [ENNReal.smul_def r]; rw [withDensity_smul_measure]; rw [← ENNReal.smul_def]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [inv_mul_cancel₀ hr]; rw [one_smul]
    exact ν.haveLebesgueDecomposition_add μ
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/--
theorem `rnDeriv_smul_right_of_ne_top'` / 定理 `rnDeriv_smul_right_of_ne_top'`

English:
theorem rnDeriv_smul_right_of_ne_top'
  statement: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  proof: by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right' ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  rwa [ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top,
    ← ENNReal.toNNReal_inv, ENNReal.smul_def, ENNR

中文:
定理 rnDeriv_smul_right_of_ne_top'
  结论: (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
  证明: by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right' ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  rwa [ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top,
    ← ENNReal.toNNReal_inv, ENNReal.smul_def, ENNR

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, ENNReal.inv_ne_top.mpr, ENNReal.smul_def, ENNReal.toNNReal_eq_zero_iff, ENNReal.toNNReal_inv, coe_toNNReal, hr_ne_top, inv_ne_top, ne_eq, r.toNNReal, rnDeriv, rnDeriv_smul_right, smul_def, toNNReal, toNNReal_eq_zero_iff, toNNReal_inv
-/
theorem rnDeriv_smul_right_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : Real>=0∞} (hr : r != 0) (hr_ne_top : r != ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right' ν μ ?_
    rw [ne_eq]; rw [ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  rwa [ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top,
    ← ENNReal.toNNReal_inv, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hr)] at h

/--
lemma `rnDeriv_add'` / 引理 `rnDeriv_add'`

English:
lemma rnDeriv_add'
  given: (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ]
  proof: by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [si

中文:
引理 rnDeriv_add'
  条件: (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ]
  证明: by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [si

Depends on / 依赖: add_assoc, add_comm, add_right_inj, haveLebesgueDecomposition_add, measurable_rnDeriv, rnDeriv, singularPart, singularPart_add, withDensity, withDensity_add_left, withDensity_eq_iff_of_sigmaFinite
-/
lemma rnDeriv_add' (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ]; rw [singularPart_add]; rw [withDensity_add_left (measurable_rnDeriv _ _)]; rw [add_assoc]; rw [add_comm (ν₂.singularPart μ)]; rw [add_assoc]; rw [add_comm _ (ν₂.singularPart μ)]; rw [← ν₂.haveLebesgueDecomposition_add μ]; rw [← add_assoc]; rw [← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable

/--
lemma `rnDeriv_add_of_mutuallySingular` / 引理 `rnDeriv_add_of_mutuallySingular`

English:
lemma rnDeriv_add_of_mutuallySingular
  statement: (ν₁ ν₂ μ : Measure α)
  proof: by
  filter_upwards [rnDeriv_add' ν₁ ν₂ μ, (rnDeriv_eq_zero ν₂ μ).mpr h] with x hx_add hx_zero
  simp [hx_add, hx_zero]

中文:
引理 rnDeriv_add_of_mutuallySingular
  结论: (ν₁ ν₂ μ : Measure α)
  证明: by
  filter_upwards [rnDeriv_add' ν₁ ν₂ μ, (rnDeriv_eq_zero ν₂ μ).mpr h] with x hx_add hx_zero
  simp [hx_add, hx_zero]

Depends on / 依赖: filter_upwards, hx_add, hx_zero, rnDeriv_add, rnDeriv_eq_zero
-/
lemma rnDeriv_add_of_mutuallySingular (ν₁ ν₂ μ : Measure α)
    [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] (h : ν₂ ⟂ₘ μ) :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ := by
  filter_upwards [rnDeriv_add' ν₁ ν₂ μ, (rnDeriv_eq_zero ν₂ μ).mpr h] with x hx_add hx_zero
  simp [hx_add, hx_zero]

end rnDeriv

/--
lemma `add_sub_of_mutuallySingular` / 引理 `add_sub_of_mutuallySingular`

English:
lemma add_sub_of_mutuallySingular
  given: {ξ : Measure α} (h : μ ⟂ₘ ξ)
  statement: μ + (ν - ξ) = μ + ν - ξ
  proof: by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  have h_le_s : μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s := by
    rw [h.restrict_nullSet]; rw [restrict_sub_eq_restrict_sub_restrict hs]
    simp
  have h_le_s_compl : μ.restrict sᶜ 

中文:
引理 add_sub_of_mutuallySingular
  条件: {ξ : Measure α} (h : μ ⟂ₘ ξ)
  结论: μ + (ν - ξ) = μ + ν - ξ
  证明: by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  have h_le_s : μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s := by
    rw [h.restrict_nullSet]; rw [restrict_sub_eq_restrict_sub_restrict hs]
    simp
  have h_le_s_compl : μ.restrict sᶜ 

Depends on / 依赖: MeasurableSet, h.measurableSet_nullSet, h.nullSet, h.restrict_compl_nullSet, h.restrict_nullSet, h_le_s, h_le_s_compl, hs.compl, measurableSet_nullSet, nullSet, restrict, restrict_compl_nullSet, restrict_nullSet, restrict_sub_eq_restrict_sub_restrict
-/
lemma add_sub_of_mutuallySingular {ξ : Measure α} (h : μ ⟂ₘ ξ) : μ + (ν - ξ) = μ + ν - ξ := by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  have h_le_s : μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s := by
    rw [h.restrict_nullSet]; rw [restrict_sub_eq_restrict_sub_restrict hs]
    simp
  have h_le_s_compl : μ.restrict sᶜ + (ν - ξ).restrict sᶜ =
      μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ := by
    rw [restrict_sub_eq_restrict_sub_restrict hs.compl]; rw [h.restrict_compl_nullSet]
    simp
  calc μ + (ν - ξ)
  _ = μ.restrict s + μ.restrict sᶜ + (ν - ξ).restrict s + (ν - ξ).restrict sᶜ := by
    rw [restrict_add_restrict_compl hs]; rw [add_assoc]; rw [restrict_add_restrict_compl hs]
  _ = μ.restrict s + (ν - ξ).restrict s + (μ.restrict sᶜ + (ν - ξ).restrict sᶜ) := by abel
  _ = (μ.restrict s + ν.restrict s - ξ.restrict s) +
      (μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ) := by rw [h_le_s, h_le_s_compl]
  _ = (μ + ν - ξ).restrict s + (μ + ν - ξ).restrict sᶜ := by
      simp [restrict_sub_eq_restrict_sub_restrict hs,
        restrict_sub_eq_restrict_sub_restrict hs.compl]
  _ = μ + ν - ξ := by rw [restrict_add_restrict_compl hs]

end Measure

end MeasureTheory
