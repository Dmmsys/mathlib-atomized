/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Josha Dekker, Arav Bhattacharyya
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular

import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Tight sets of measures

A set of measures is tight if for all `0 < ε`, there exists a compact set `K` such that for all
measures in the set, the complement of `K` has measure at most `ε`.

## Main definitions

* `MeasureTheory.IsTightMeasureSet`: A set of measures `S` is tight if for all `0 < ε`, there exists
  a compact set `K` such that for all `μ ∈ S`, `μ Kᶜ ≤ ε`.
  The definition uses an equivalent formulation with filters: `⨆ μ ∈ S, μ` tends to `0` along the
  filter of cocompact sets.
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` establishes equivalence between
  the two definitions.

## Main statements

* `isTightMeasureSet_singleton_of_innerRegularWRT`: every finite, inner-regular measure is tight.
* `isTightMeasureSet_of_isCompact_closure`: every relatively compact set of measures is tight.


-/

@[expose] public section

open Filter Set TopologicalSpace

open scoped Topology

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} {S T : Set (Measure 𝓧)}

section Basic

variable [TopologicalSpace 𝓧]

/--
Definition of `IsTightMeasureSet` / `IsTightMeasureSet` 的定义

English:
definition IsTightMeasureSet
  signature: (S : Set (Measure 𝓧))
  body: Tendsto (⨆ μ in S, μ) (cocompact 𝓧).smallSets (𝓝 0)

中文:
定义 IsTightMeasureSet
  签名: (S : 集合 (测度 𝓧))
  定义体: Tendsto (⨆ μ in S, μ) (cocompact 𝓧).smallSets (𝓝 0)

Depends on / 依赖: Tendsto, cocompact, smallSets
-/
def IsTightMeasureSet (S : Set (Measure 𝓧)) : Prop :=
  Tendsto (⨆ μ in S, μ) (cocompact 𝓧).smallSets (𝓝 0)

/--
lemma `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` / 引理 `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`

English:
lemma isTightMeasureSet_iff_exists_isCompact_measure_compl_le
  proof: by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε 

中文:
引理 isTightMeasureSet_iff_存在_isCompact_measure_compl_le
  证明: by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε 

Depends on / 依赖: ENNReal, ENNReal.tendsto_nhds, ENNReal.zero_ne_top, IsTightMeasureSet, eventually_smallSets, gt_iff_lt, iSup_apply, iSup_le_iff, mem_Icc, mem_cocompact, subset_rfl, tendsto_nhds, true_and, tsub_le_iff_right, zero_add, zero_le, zero_ne_top
-/
lemma isTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔ forall ε, 0 < ε -> exists K : Set 𝓧, IsCompact K ∧ forall μ in S, μ (Kᶜ) <= ε := by
  simp only [IsTightMeasureSet, ENNReal.tendsto_nhds ENNReal.zero_ne_top, gt_iff_lt, zero_add,
    iSup_apply, mem_Icc, tsub_le_iff_right, zero_le, iSup_le_iff, true_and, eventually_smallSets,
    mem_cocompact]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · obtain ⟨A, ⟨K, h1, h2⟩, hA⟩ := h ε hε
    exact ⟨K, h1, hA Kᶜ h2⟩
  · obtain ⟨K, h1, h2⟩ := h ε hε
    exact ⟨Kᶜ, ⟨K, h1, subset_rfl⟩, fun A hA μ hμS => (μ.mono hA).trans (h2 μ hμS)⟩

/--
theorem `isTightMeasureSet_singleton_of_innerRegularWRT` / 定理 `isTightMeasureSet_singleton_of_innerRegularWRT`

English:
theorem isTightMeasureSet_singleton_of_innerRegularWRT
  statement: [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ]
  proof: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hεr.ne_bot hε.ne'
    obtain ⟨K, _, ⟨hK_compact, hK_closed⟩, hKμ⟩ := h .univ (r - ε) hεr

中文:
定理 isTightMeasureSet_singleton_of_innerRegularWRT
  结论: [OpensMeasurable空间 𝓧] [是有限测度 μ]
  证明: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hεr.ne_bot hε.ne'
    obtain ⟨K, _, ⟨hK_compact, hK_closed⟩, hKμ⟩ := h .univ (r - ε) hεr

Depends on / 依赖: ENNReal, ENNReal.sub_lt_iff_lt_right, ENNReal.sub_lt_self, Set.univ, forall_eq, hK_closed, hK_closed.measurableSet, hK_compact, isTightMeasureSet_iff_exists_isCompact_measure_compl_le, lt_or_ge, measurableSet, measure_compl, measure_ne_top, mem_singleton_iff, ne_bot, ne_top_of_lt, r.le, r.ne_bot, sub_lt_iff_lt_right, sub_lt_self
-/
theorem isTightMeasureSet_singleton_of_innerRegularWRT [OpensMeasurableSpace 𝓧] [IsFiniteMeasure μ]
    (h : μ.InnerRegularWRT (fun s => IsCompact s ∧ IsClosed s) MeasurableSet) :
    IsTightMeasureSet {μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let r := μ Set.univ
  cases lt_or_ge ε r with
  | inl hεr =>
    have hεr' : r - ε < r := ENNReal.sub_lt_self (measure_ne_top μ _) hεr.ne_bot hε.ne'
    obtain ⟨K, _, ⟨hK_compact, hK_closed⟩, hKμ⟩ := h .univ (r - ε) hεr'
    refine ⟨K, hK_compact, ?_⟩
    simp only [mem_singleton_iff, forall_eq]
    rw [measure_compl hK_closed.measurableSet (measure_ne_top μ _)]; rw [tsub_le_iff_right]
    rw [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hεr) hεr.le]; rw [add_comm] at hKμ
    exact hKμ.le
  | inr hεr => exact ⟨∅, isCompact_empty, by simpa⟩

/--
lemma `isTightMeasureSet_singleton_of_innerRegular` / 引理 `isTightMeasureSet_singleton_of_innerRegular`

English:
lemma isTightMeasureSet_singleton_of_innerRegular
  statement: [T2Space 𝓧] [OpensMeasurableSpace 𝓧]
  proof: by
  refine isTightMeasureSet_singleton_of_innerRegularWRT ?_
  intro s hs r hr
  obtain ⟨K, hKs, hK_compact, hμK⟩ := h.innerRegular hs r hr
  exact ⟨K, hKs, ⟨hK_compact, hK_compact.isClosed⟩, hμK⟩

中文:
引理 isTightMeasureSet_singleton_of_innerRegular
  结论: [T2空间 𝓧] [OpensMeasurable空间 𝓧]
  证明: by
  refine isTightMeasureSet_singleton_of_innerRegularWRT ?_
  intro s hs r hr
  obtain ⟨K, hKs, hK_compact, hμK⟩ := h.innerRegular hs r hr
  exact ⟨K, hKs, ⟨hK_compact, hK_compact.isClosed⟩, hμK⟩

Depends on / 依赖: h.innerRegular, hK_compact, hK_compact.isClosed, innerRegular, isClosed, isTightMeasureSet_singleton_of_innerRegularWRT
-/
lemma isTightMeasureSet_singleton_of_innerRegular [T2Space 𝓧] [OpensMeasurableSpace 𝓧]
    [IsFiniteMeasure μ] [h : μ.InnerRegular] :
    IsTightMeasureSet {μ} := by
  refine isTightMeasureSet_singleton_of_innerRegularWRT ?_
  intro s hs r hr
  obtain ⟨K, hKs, hK_compact, hμK⟩ := h.innerRegular hs r hr
  exact ⟨K, hKs, ⟨hK_compact, hK_compact.isClosed⟩, hμK⟩

/--
theorem `isTightMeasureSet_singleton` / 定理 `isTightMeasureSet_singleton`

English:
theorem isTightMeasureSet_singleton
  statement: {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  proof: isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

中文:
定理 isTightMeasureSet_singleton
  结论: {α : 类型} [可测空间 α] [拓扑空间 α]
  证明: isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

Depends on / 依赖: innerRegular_isCompact_isClosed_measurableSet_of_finite, isTightMeasureSet_singleton_of_innerRegularWRT
-/
theorem isTightMeasureSet_singleton {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

namespace IsTightMeasureSet

/--
lemma `of_compactSpace` / 引理 `of_compactSpace`

English:
lemma of_compactSpace
  given: [CompactSpace 𝓧]
  statement: IsTightMeasureSet S
  proof: by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ => mem_of_mem_nhds

中文:
引理 of_compactSpace
  条件: [紧空间 𝓧]
  结论: IsTightMeasureSet S
  证明: by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ => mem_of_mem_nhds

Depends on / 依赖: ENNReal, ENNReal.iSup_zero, IsTightMeasureSet, ciSup_const, cocompact_eq_bot, iSup_apply, iSup_zero, measure_empty, mem_of_mem_nhds, smallSets_bot, tendsto_pure_left
-/
lemma of_compactSpace [CompactSpace 𝓧] : IsTightMeasureSet S := by
  simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot, tendsto_pure_left, iSup_apply,
    measure_empty, ENNReal.iSup_zero, ciSup_const]
  exact fun _ => mem_of_mem_nhds

/--
lemma `subset` / 引理 `subset`

English:
lemma subset
  given: (hT : IsTightMeasureSet T) (hST : S subseteq T)
  proof: tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => by simp)
    (iSup_le_iSup_of_subset hST)

中文:
引理 subset
  条件: (hT : IsTightMeasureSet T) (hST : S subseteq T)
  证明: tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => by simp)
    (iSup_le_iSup_of_subset hST)
-/
protected lemma subset (hT : IsTightMeasureSet T) (hST : S subseteq T) :
    IsTightMeasureSet S :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => by simp)
    (iSup_le_iSup_of_subset hST)

/--
lemma `union` / 引理 `union`

English:
lemma union
  given: (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T)
  proof: by
  rw [IsTightMeasureSet]; rw [iSup_union]
  convert! Tendsto.sup_nhds hS hT
  simp

中文:
引理 union
  条件: (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T)
  证明: by
  rw [IsTightMeasureSet]; rw [iSup_union]
  convert! Tendsto.sup_nhds hS hT
  simp
-/
protected lemma union (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet (S union T) := by
  rw [IsTightMeasureSet]; rw [iSup_union]
  convert! Tendsto.sup_nhds hS hT
  simp

/--
lemma `inter` / 引理 `inter`

English:
lemma inter
  given: (hS : IsTightMeasureSet S) (T : Set (Measure 𝓧))
  proof: hS.subset inter_subset_left

中文:
引理 inter
  条件: (hS : IsTightMeasureSet S) (T : 集合 (测度 𝓧))
  证明: hS.subset inter_subset_left

Depends on / 依赖: HasLimit, HasLimit.mk, isProduct
-/
protected lemma inter (hS : IsTightMeasureSet S) (T : Set (Measure 𝓧)) :
    IsTightMeasureSet (S inter T) :=
  hS.subset inter_subset_left

/--
lemma `map` / 引理 `map`

English:
lemma map
  statement: [TopologicalSpace 𝓨] [MeasurableSpace 𝓨] [OpensMeasurableSpace 𝓨] [T2Space 𝓨]
  proof: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro ε hε
  obtain ⟨K, hK_compact, hKS⟩ := hS ε hε
  refine ⟨f '' K, hK_compact.image hf, fun μ hμS => ?_⟩
  by_cases hf_meas : AEMeasurable f 

中文:
引理 map
  结论: [拓扑空间 𝓨] [可测空间 𝓨] [OpensMeasurable空间 𝓨] [T2空间 𝓨]
  证明: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro ε hε
  obtain ⟨K, hK_compact, hKS⟩ := hS ε hε
  refine ⟨f '' K, hK_compact.image hf, fun μ hμS => ?_⟩
  by_cases hf_meas : AEMeasurable f 

Depends on / 依赖: AEMeasurable, Measure, Measure.map_apply_of_aemeasurable, Measure.map_of_not_aemeasurable, and_imp, forall_exists_index, hK_compact, hK_compact.image, hf_meas, isTightMeasureSet_iff_exists_isCompact_measure_compl_le, map_apply_of_aemeasurable, map_of_not_aemeasurable, measurableSet, measurableSet.compl, measure_mono, mem_image, preimage_com
-/
lemma map [TopologicalSpace 𝓨] [MeasurableSpace 𝓨] [OpensMeasurableSpace 𝓨] [T2Space 𝓨]
    (hS : IsTightMeasureSet S) {f : 𝓧 -> 𝓨} (hf : Continuous f) :
    IsTightMeasureSet (Measure.map f '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro ε hε
  obtain ⟨K, hK_compact, hKS⟩ := hS ε hε
  refine ⟨f '' K, hK_compact.image hf, fun μ hμS => ?_⟩
  by_cases hf_meas : AEMeasurable f μ
  swap; · simp [Measure.map_of_not_aemeasurable hf_meas]
  rw [Measure.map_apply_of_aemeasurable hf_meas (hK_compact.image hf).measurableSet.compl]
  refine (measure_mono ?_).trans (hKS μ hμS)
  simp only [preimage_compl, compl_subset_compl]
  exact subset_preimage_image f K

/--
lemma `prodMk` / 引理 `prodMk`

English:
lemma prodMk
  statement: {m𝓨 : MeasurableSpace 𝓨} [TopologicalSpace 𝓨] {μ : Set (Measure (𝓧 × 𝓨))}
  proof: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ₁ hμ₂ ⊢
  intro ε hε
  obtain ⟨K₁, hK₁_compact, hK₁_le⟩ := hμ₁ (ε / 2) (by aesop)
  obtain ⟨K₂, hK₂_compact, hK₂_le⟩ := hμ₂ (ε / 2) (by aesop)
  refine ⟨K₁ ×ˢ K₂, hK₁_compact.prod hK₂_compact, fun κ hκ_mem => ?_⟩
  grw [compl_pro

中文:
引理 prodMk
  结论: {m𝓨 : 可测空间 𝓨} [拓扑空间 𝓨] {μ : 集合 (测度 (𝓧 × 𝓨))}
  证明: by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ₁ hμ₂ ⊢
  intro ε hε
  obtain ⟨K₁, hK₁_compact, hK₁_le⟩ := hμ₁ (ε / 2) (by aesop)
  obtain ⟨K₂, hK₂_compact, hK₂_le⟩ := hμ₂ (ε / 2) (by aesop)
  refine ⟨K₁ ×ˢ K₂, hK₁_compact.prod hK₂_compact, fun κ hκ_mem => ?_⟩
  grw [compl_pro

Depends on / 依赖: ENNReal, ENNReal.add_halves, Measure, Measure.fst, Measure.le_map_apply, _compact.prod, add_halves, add_le_add, compl_prod_eq_union, fun_prop, isTightMeasureSet_iff_exists_isCompact_measure_compl_le, le_map_apply, measure_union_le, mem_image_of_mem, prod_univ, specialize
-/
lemma prodMk {m𝓨 : MeasurableSpace 𝓨} [TopologicalSpace 𝓨] {μ : Set (Measure (𝓧 × 𝓨))}
    (hμ₁ : IsTightMeasureSet (Measure.fst '' μ)) (hμ₂ : IsTightMeasureSet (Measure.snd '' μ)) :
    IsTightMeasureSet μ := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hμ₁ hμ₂ ⊢
  intro ε hε
  obtain ⟨K₁, hK₁_compact, hK₁_le⟩ := hμ₁ (ε / 2) (by aesop)
  obtain ⟨K₂, hK₂_compact, hK₂_le⟩ := hμ₂ (ε / 2) (by aesop)
  refine ⟨K₁ ×ˢ K₂, hK₁_compact.prod hK₂_compact, fun κ hκ_mem => ?_⟩
  grw [compl_prod_eq_union, measure_union_le, ← ENNReal.add_halves (a := ε)]
  apply add_le_add
· specialize hK₁_le _ mem_image_of_mem _ hκ_mem
    grw [Measure.fst, ← Measure.le_map_apply (by fun_prop)] at hK₁_le
    simpa [prod_univ] using hK₁_le
· specialize hK₂_le _ Set.mem_image_of_mem _ hκ_mem
    grw [Measure.snd, ← Measure.le_map_apply (by fun_prop)] at hK₂_le
    simpa [univ_prod] using hK₂_le

end IsTightMeasureSet
end Basic

end MeasureTheory
