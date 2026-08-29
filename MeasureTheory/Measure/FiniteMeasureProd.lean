/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Products of finite measures and probability measures

This file introduces binary products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.prod`: The product of two finite measures.
* `MeasureTheory.ProbabilityMeasure.prod`: The product of two probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_prod`: the product probability measure depends
continuously on the factors.

-/

@[expose] public section

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section FiniteMeasure_product

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (μ : FiniteMeasure α) (ν : FiniteMeasure β)
  body: ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

中文:
定义 乘积
  签名: (μ : 有限测度 α) (ν : 有限测度 β)
  定义体: ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

Depends on / 依赖: toMeasure, toMeasure.prod
-/
noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)

/--
lemma `toMeasure_prod` / 引理 `toMeasure_prod`

English:
lemma toMeasure_prod
  statement: (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure
  proof: rfl

中文:
引理 toMeasure_prod
  结论: (μ.乘积 ν).toMeasure = μ.toMeasure.乘积 ν.toMeasure
  证明: rfl
-/
@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: (s : Set (α × β)) (s_mble : MeasurableSet s)
  proof: by
  simp [coeFn_def, Measure.prod_apply s_mble]

中文:
引理 prod_apply
  条件: (s : 集合 (α × β)) (s_mble : 可测集 s)
  证明: by
  simp [coeFn_def, Measure.prod_apply s_mble]

Depends on / 依赖: Measure, Measure.prod_apply, coeFn_def, prod_apply, s_mble
-/
lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]

/--
lemma `prod_apply_symm` / 引理 `prod_apply_symm`

English:
lemma prod_apply_symm
  given: (s : Set (α × β)) (s_mble : MeasurableSet s)
  proof: by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

中文:
引理 prod_apply_symm
  条件: (s : 集合 (α × β)) (s_mble : 可测集 s)
  证明: by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

Depends on / 依赖: Measure, Measure.prod_apply_symm, coeFn_def, prod_apply_symm, s_mble
-/
lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x => ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

/--
lemma `prod_prod` / 引理 `prod_prod`

English:
lemma prod_prod
  given: (s : Set α) (t : Set β)
  statement: μ.prod ν (s ×ˢ t) = μ s * ν t
  proof: by
  simp [coeFn_def]

中文:
引理 prod_prod
  条件: (s : 集合 α) (t : 集合 β)
  结论: μ.乘积 ν (s ×ˢ t) = μ s * ν t
  证明: by
  simp [coeFn_def]
-/
@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]

/--
lemma `mass_prod` / 引理 `mass_prod`

English:
lemma mass_prod
  statement: (μ.prod ν).mass = μ.mass * ν.mass
  proof: by
  simp only [coeFn_def, mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)

中文:
引理 mass_prod
  结论: (μ.乘积 ν).mass = μ.mass * ν.mass
  证明: by
  simp only [coeFn_def, mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)

Depends on / 依赖: IsWellFounded, Std.Asymm
-/
@[simp] lemma mass_prod : (μ.prod ν).mass = μ.mass * ν.mass := by
  simp only [coeFn_def, mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)

/--
lemma `zero_prod` / 引理 `zero_prod`

English:
lemma zero_prod
  statement: (0 : FiniteMeasure α).prod ν = 0
  proof: by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [zero_mul]

中文:
引理 zero_prod
  结论: (0 : 有限测度 α).乘积 ν = 0
  证明: by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [zero_mul]

Depends on / 依赖: i.wf.transGen, transGen
-/
@[simp] lemma zero_prod : (0 : FiniteMeasure α).prod ν = 0 := by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [zero_mul]

/--
lemma `prod_zero` / 引理 `prod_zero`

English:
lemma prod_zero
  statement: μ.prod (0 : FiniteMeasure β) = 0
  proof: by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [mul_zero]

中文:
引理 prod_zero
  结论: μ.乘积 (0 : 有限测度 β) = 0
  证明: by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [mul_zero]
-/
@[simp] lemma prod_zero : μ.prod (0 : FiniteMeasure β) = 0 := by
  rw [← mass_zero_iff]; rw [mass_prod]; rw [zero_mass]; rw [mul_zero]

/--
lemma `map_fst_prod` / 引理 `map_fst_prod`

English:
lemma map_fst_prod
  statement: (μ.prod ν).map Prod.fst = ν univ • μ
  proof: by ext; simp

中文:
引理 map_fst_prod
  结论: (μ.乘积 ν).map 积类型.fst = ν univ • μ
  证明: by ext; simp
-/
@[simp] lemma map_fst_prod : (μ.prod ν).map Prod.fst = ν univ • μ := by ext; simp
/--
lemma `map_snd_prod` / 引理 `map_snd_prod`

English:
lemma map_snd_prod
  statement: (μ.prod ν).map Prod.snd = μ univ • ν
  proof: by ext; simp

中文:
引理 map_snd_prod
  结论: (μ.乘积 ν).map 积类型.snd = μ univ • ν
  证明: by ext; simp

Depends on / 依赖: WellFoundedGT, WellFoundedLT
-/
@[simp] lemma map_snd_prod : (μ.prod ν).map Prod.snd = μ univ • ν := by ext; simp

/--
lemma `map_prod_map` / 引理 `map_prod_map`

English:
lemma map_prod_map
  statement: {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
  proof: by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

中文:
引理 map_prod_map
  结论: {α' : 类型} [可测空间 α'] {β' : 类型} [可测空间 β']
  证明: by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

Depends on / 依赖: Measure, Measure.map_prod_map, Subtype, Subtype.ext, f_mble, g_mble, map_prod_map, toMeasure_map, toMeasure_prod, val_eq_toMeasure
-/
lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α -> α'} {g : β -> β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

/--
lemma `prod_swap` / 引理 `prod_swap`

English:
lemma prod_swap
  statement: (μ.prod ν).map Prod.swap = ν.prod μ
  proof: by
  apply Subtype.ext
  simp [Measure.prod_swap]

中文:
引理 prod_swap
  结论: (μ.乘积 ν).map 积类型.swap = ν.乘积 μ
  证明: by
  apply Subtype.ext
  simp [Measure.prod_swap]

Depends on / 依赖: IsWellFounded, IsWellFounded.wf.asymmetric, Measure, Measure.prod_swap, Subtype, Subtype.ext, asymm_of, prod_swap, trichotomous_of
-/
lemma prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

end FiniteMeasure -- namespace

end FiniteMeasure_product -- section

section ProbabilityMeasure_product

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)
  body: ⟨μ.toMeasure.prod ν.toMeasure, by infer_instance⟩

中文:
定义 乘积
  签名: (μ : 概率测度 α) (ν : 概率测度 β)
  定义体: ⟨μ.toMeasure.prod ν.toMeasure, by infer_instance⟩

Depends on / 依赖: IsWellOrder, infer_instance, toMeasure, toMeasure.prod
-/
noncomputable def prod (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbabilityMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, by infer_instance⟩

variable (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)

/--
lemma `toMeasure_prod` / 引理 `toMeasure_prod`

English:
lemma toMeasure_prod
  statement: (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure
  proof: rfl

中文:
引理 toMeasure_prod
  结论: (μ.乘积 ν).toMeasure = μ.toMeasure.乘积 ν.toMeasure
  证明: rfl
-/
@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: (s : Set (α × β)) (s_mble : MeasurableSet s)
  proof: by
  simp [coeFn_def, Measure.prod_apply s_mble]

中文:
引理 prod_apply
  条件: (s : 集合 (α × β)) (s_mble : 可测集 s)
  证明: by
  simp [coeFn_def, Measure.prod_apply s_mble]

Depends on / 依赖: Measure, Measure.prod_apply, coeFn_def, prod_apply, s_mble
-/
lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]

/--
lemma `prod_apply_symm` / 引理 `prod_apply_symm`

English:
lemma prod_apply_symm
  given: (s : Set (α × β)) (s_mble : MeasurableSet s)
  proof: by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

中文:
引理 prod_apply_symm
  条件: (s : 集合 (α × β)) (s_mble : 可测集 s)
  证明: by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

Depends on / 依赖: Measure, Measure.prod_apply_symm, coeFn_def, prod_apply_symm, s_mble
-/
lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x => ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

/--
lemma `prod_prod` / 引理 `prod_prod`

English:
lemma prod_prod
  given: (s : Set α) (t : Set β)
  statement: μ.prod ν (s ×ˢ t) = μ s * ν t
  proof: by
  simp [coeFn_def]

中文:
引理 prod_prod
  条件: (s : 集合 α) (t : 集合 β)
  结论: μ.乘积 ν (s ×ˢ t) = μ s * ν t
  证明: by
  simp [coeFn_def]
-/
@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]

/--
lemma `map_fst_prod` / 引理 `map_fst_prod`

English:
lemma map_fst_prod
  statement: (μ.prod ν).map measurable_fst.aemeasurable = μ
  proof: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]

中文:
引理 map_fst_prod
  结论: (μ.乘积 ν).map measurable_fst.aemeasurable = μ
  证明: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]
-/
@[simp] lemma map_fst_prod : (μ.prod ν).map measurable_fst.aemeasurable = μ := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]

/--
lemma `map_snd_prod` / 引理 `map_snd_prod`

English:
lemma map_snd_prod
  statement: (μ.prod ν).map measurable_snd.aemeasurable = ν
  proof: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]

中文:
引理 map_snd_prod
  结论: (μ.乘积 ν).map measurable_snd.aemeasurable = ν
  证明: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]
-/
@[simp] lemma map_snd_prod : (μ.prod ν).map measurable_snd.aemeasurable = ν := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]

/--
lemma `map_prod_map` / 引理 `map_prod_map`

English:
lemma map_prod_map
  statement: {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
  proof: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

中文:
引理 map_prod_map
  结论: {α' : 类型} [可测空间 α'] {β' : 类型} [可测空间 β']
  证明: by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

Depends on / 依赖: Measure, Measure.map_prod_map, Subtype, Subtype.ext, f_mble, g_mble, map_prod_map, toMeasure_map, toMeasure_prod, val_eq_to_measure
-/
lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α -> α'} {g : β -> β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f_mble.aemeasurable).prod (ν.map g_mble.aemeasurable)
      = (μ.prod ν).map (f_mble.prodMap g_mble).aemeasurable := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

/--
lemma `prod_swap` / 引理 `prod_swap`

English:
lemma prod_swap
  statement: (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ
  proof: by
  apply Subtype.ext
  simp [Measure.prod_swap]

中文:
引理 prod_swap
  结论: (μ.乘积 ν).map measurable_swap.aemeasurable = ν.乘积 μ
  证明: by
  apply Subtype.ext
  simp [Measure.prod_swap]

Depends on / 依赖: Measure, Measure.prod_swap, Subtype, Subtype.ext, prod_swap
-/
lemma prod_swap : (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

open TopologicalSpace

/-- The map associating to two probability measures their product is a continuous map. -/
@[fun_prop]
/--
theorem `continuous_prod` / 定理 `continuous_prod`

English:
theorem continuous_prod
  statement: [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology α]
  proof: by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `a ×ˢ b` where `a`

中文:
定理 continuous_prod
  结论: [拓扑空间 α] [拓扑空间 β] [第二可数拓扑 α]
  证明: by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `a ×ˢ b` where `a`

Depends on / 依赖: continuous_iff_continuousAt
-/
theorem continuous_prod [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology α]
    [SecondCountableTopology β] [PseudoMetrizableSpace α] [PseudoMetrizableSpace β]
    [OpensMeasurableSpace α] [OpensMeasurableSpace β] :
    Continuous (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β) => μ.1.prod μ.2) := by
  refine continuous_iff_continuousAt.2 (fun μ => ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `a ×ˢ b` where `a` and `b` have null frontier. -/
  let S : Set (Set (α × β)) := {t | exists (a : Set α) (b : Set β),
    MeasurableSet a ∧ μ.1 (frontier a) = 0 ∧ MeasurableSet b ∧ μ.2 (frontier b) = 0
    ∧ t = a ×ˢ b}
  have : IsPiSystem S := by
    rintro - ⟨a, b, ameas, ha, bmeas, hb, rfl⟩ - ⟨a', b', a'meas, ha', b'meas, hb', rfl⟩ -
    refine ⟨a inter a', b inter b', ameas.inter a'meas, ?_, bmeas.inter b'meas, ?_, prod_inter_prod⟩
    · rw [null_iff_toMeasure_null] at ha ha' ⊢
      exact null_frontier_inter ha ha'
    · rw [null_iff_toMeasure_null] at hb hb' ⊢
      exact null_frontier_inter hb hb'
  apply this.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, ameas, -, bmeas, -, rfl⟩
    exact ameas.prod bmeas
  · let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
    let : PseudoMetricSpace β := TopologicalSpace.pseudoMetrizableSpacePseudoMetric β
    intro u u_open x xu
    obtain ⟨ε, εpos, hε⟩ : exists ε > 0, ball x ε subseteq u := Metric.isOpen_iff.1 u_open x xu
    rcases exists_null_frontier_thickening (μ.1 : Measure α) {x.1} εpos with ⟨r, hr, μr⟩
    rcases exists_null_frontier_thickening (μ.2 : Measure β) {x.2} εpos with ⟨r', hr', μr'⟩
    simp only [thickening_singleton] at μr μr'
    refine ⟨ball x.1 r ×ˢ ball x.2 r', ⟨ball x.1 r, ball x.2 r', measurableSet_ball,
      by simp [coeFn_def, μr], measurableSet_ball, by simp [coeFn_def, μr'], rfl⟩, ?_, ?_⟩
    · exact (isOpen_ball.prod isOpen_ball).mem_nhds (by simp [hr.1, hr'.1])
    · calc ball x.1 r ×ˢ ball x.2 r'
      _ subseteq ball x.1 ε ×ˢ ball x.2 ε := by gcongr; exacts [hr.2.le, hr'.2.le]
      _ subseteq _ := by rwa [ball_prod_same]
  · rintro s ⟨a, b, ameas, ha, bmeas, hb, rfl⟩
    simp only [prod_prod]
    apply Filter.Tendsto.mul
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.fst_nhds ha
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.snd_nhds hb

end ProbabilityMeasure -- namespace

end ProbabilityMeasure_product -- section

end MeasureTheory -- namespace
