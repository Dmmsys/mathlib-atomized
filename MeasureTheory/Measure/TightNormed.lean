/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Order.Filter.ENNReal

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a proper normed group, a set of measures `S`
  is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.
* `isTightMeasureSet_iff_inner_tendsto`: in a finite-dimensional inner product space,
  a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < |⟪y, x⟫|}`
  tends to `0` at infinity for all `y`.
* `isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt`: in a proper normed group,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to `0` at infinity.
* `isTightMeasureSet_range_iff_tendsto_limsup_inner`: in a finite-dimensional inner product space,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infinity for all `y`.

-/

public section

open Filter

open scoped Topology ENNReal NNReal InnerProductSpace

namespace MeasureTheory

variable {E : Type*} {mE : MeasurableSpace E} {S : Set (Measure E)}

section PseudoMetricSpace

variable [PseudoMetricSpace E]

/--
lemma `tendsto_measure_compl_closedBall_of_isTightMeasureSet` / 引理 `tendsto_measure_compl_closedBall_of_isTightMeasureSet`

English:
lemma tendsto_measure_compl_closedBall_of_isTightMeasureSet
  given: (hS : IsTightMeasureSet S) (x : E)
  proof: by
  suffices Tendsto ((⨆ μ in S, μ) ∘ (fun r => (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert! this with r
    simp
refine hS.comp .mono_right ?_ monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets

中文:
引理 tendsto_measure_compl_closedBall_of_isTightMeasureSet
  条件: (hS : IsTightMeasureSet S) (x : E)
  证明: by
  suffices Tendsto ((⨆ μ in S, μ) ∘ (fun r => (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert! this with r
    simp
refine hS.comp .mono_right ?_ monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets

Depends on / 依赖: Metric, Metric.closedBall, Metric.cobounded_le_cocompact, Metric.hasAntitoneBasis_cobounded_compl_closedBall, Tendsto, closedBall, cobounded_le_cocompact, convert, hS.comp, hasAntitoneBasis_cobounded_compl_closedBall, mono_right, monotone_smallSets, tendsto_smallSets
-/
lemma tendsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x : E) :
    Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ in S, μ) ∘ (fun r => (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert! this with r
    simp
refine hS.comp .mono_right ?_ monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets

/--
lemma `isTightMeasureSet_of_tendsto_measure_compl_closedBall` / 引理 `isTightMeasureSet_of_tendsto_measure_compl_closedBall`

English:
lemma isTightMeasureSet_of_tendsto_measure_compl_closedBall
  statement: [ProperSpace E] {x : E}
  proof: by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε => ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

中文:
引理 isTightMeasureSet_of_tendsto_measure_compl_closedBall
  结论: [命题erSpace E] {x : E}
  证明: by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε => ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

Depends on / 依赖: ENNReal, ENNReal.tendsto_atTop_zero, Metric, Metric.closedBall, closedBall, isCompact_closedBall, isTightMeasureSet_iff_exists_isCompact_measure_compl_le, isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr, le_rfl, tendsto_atTop_zero
-/
lemma isTightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E}
    (h : Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε => ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

/--
lemma `isTightMeasureSet_iff_tendsto_measure_compl_closedBall` / 引理 `isTightMeasureSet_iff_tendsto_measure_compl_closedBall`

English:
lemma isTightMeasureSet_iff_tendsto_measure_compl_closedBall
  given: [ProperSpace E] (x : E)
  proof: ⟨fun hS => tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

中文:
引理 isTightMeasureSet_iff_tendsto_measure_compl_closedBall
  条件: [命题erSpace E] (x : E)
  证明: ⟨fun hS => tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

Depends on / 依赖: isTightMeasureSet_of_tendsto_measure_compl_closedBall, tendsto_measure_compl_closedBall_of_isTightMeasureSet
-/
lemma isTightMeasureSet_iff_tendsto_measure_compl_closedBall [ProperSpace E] (x : E) :
    IsTightMeasureSet S ↔ Tendsto (fun r : Real => ⨆ μ in S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) :=
  ⟨fun hS => tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

end PseudoMetricSpace

section NormedAddCommGroup

variable [NormedAddCommGroup E]

/--
lemma `tendsto_measure_norm_gt_of_isTightMeasureSet` / 引理 `tendsto_measure_norm_gt_of_isTightMeasureSet`

English:
lemma tendsto_measure_norm_gt_of_isTightMeasureSet
  given: (hS : IsTightMeasureSet S)
  proof: by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert! h using 6 with r
  ext
  simp

中文:
引理 tendsto_measure_norm_gt_of_isTightMeasureSet
  条件: (hS : IsTightMeasureSet S)
  证明: by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert! h using 6 with r
  ext
  simp

Depends on / 依赖: HasEqualizers, HasEqualizers.isEqualizer, HasLimit, HasLimit.mk, convert, isEqualizer, tendsto_measure_compl_closedBall_of_isTightMeasureSet
-/
lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert! h using 6 with r
  ext
  simp

/--
lemma `isTightMeasureSet_of_tendsto_measure_norm_gt` / 引理 `isTightMeasureSet_of_tendsto_measure_norm_gt`

English:
lemma isTightMeasureSet_of_tendsto_measure_norm_gt
  statement: [ProperSpace E]
  proof: by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert! h using 6 with r
  ext
  simp

中文:
引理 isTightMeasureSet_of_tendsto_measure_norm_gt
  结论: [命题erSpace E]
  证明: by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert! h using 6 with r
  ext
  simp

Depends on / 依赖: convert, isTightMeasureSet_of_tendsto_measure_compl_closedBall
-/
lemma isTightMeasureSet_of_tendsto_measure_norm_gt [ProperSpace E]
    (h : Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert! h using 6 with r
  ext
  simp

/--
lemma `isTightMeasureSet_iff_tendsto_measure_norm_gt` / 引理 `isTightMeasureSet_iff_tendsto_measure_norm_gt`

English:
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt
  given: [ProperSpace E]
  proof: ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

中文:
引理 isTightMeasureSet_iff_tendsto_measure_norm_gt
  条件: [命题erSpace E]
  证明: ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

Depends on / 依赖: isTightMeasureSet_of_tendsto_measure_norm_gt, tendsto_measure_norm_gt_of_isTightMeasureSet
-/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt [ProperSpace E] :
    IsTightMeasureSet S ↔ Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

section Sequence

variable [BorelSpace E] [ProperSpace E] {μ : Nat -> Measure E} [forall i, IsFiniteMeasure (μ i)]

/--
lemma `isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt` / 引理 `isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt`

English:
lemma isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
  proof: by
  simp_rw [isTightMeasureSet_iff_tendsto_measure_norm_gt, iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) h (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {μ n} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  

中文:
引理 isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
  证明: by
  simp_rw [isTightMeasureSet_iff_tendsto_measure_norm_gt, iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) h (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {μ n} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  

Depends on / 依赖: IsTightMeasureSet, Nat.tendsto_iSup_of_tendsto_limsup, h_tight, iSup_range, isTightMeasureSet_iff_tendsto_measure_norm_gt, isTightMeasureSet_singleton, simp_rw, tendsto_iSup_of_tendsto_limsup
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
    (h : Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  simp_rw [isTightMeasureSet_iff_tendsto_measure_norm_gt, iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) h (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {μ n} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  simpa using h_tight

/--
lemma `isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt` / 引理 `isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt`

English:
lemma isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt
  proof: by
  refine ⟨fun h => ?_, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ => zero_le) ?_
  intro r
  simp_rw [iSup_range]
  exact limsup_le_iSu

中文:
引理 isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt
  证明: by
  refine ⟨fun h => ?_, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ => zero_le) ?_
  intro r
  simp_rw [iSup_range]
  exact limsup_le_iSu

Depends on / 依赖: h_sup, iSup_range, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt, limsup_le_iSup, simp_rw, tendsto_const_nhds, tendsto_measure_norm_gt_of_isTightMeasureSet, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
lemma isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt :
    IsTightMeasureSet (Set.range μ)
      ↔ Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h => ?_, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ => zero_le) ?_
  intro r
  simp_rw [iSup_range]
  exact limsup_le_iSup

end Sequence

section InnerProductSpace

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/--
lemma `isTightMeasureSet_of_forall_basis_tendsto` / 引理 `isTightMeasureSet_of_forall_basis_tendsto`

English:
lemma isTightMeasureSet_of_forall_basis_tendsto
  statement: (b : OrthonormalBasis ι 𝕜 E)
  proof: by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert! tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : Real) < Fintype.card ι := by
    simpa [← Module.finrank_eq_card_basis b.toBasis, Module.finrank_pos_iff]
 

中文:
引理 isTightMeasureSet_of_forall_basis_tendsto
  结论: (b : OrthonormalBasis ι 𝕜 E)
  证明: by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert! tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : Real) < Fintype.card ι := by
    simpa [← Module.finrank_eq_card_basis b.toBasis, Module.finrank_pos_iff]
 

Depends on / 依赖: FiniteDimensional, FiniteDimensional.proper, Fintype, Fintype.card, Fintype.card_pos_iff, IsTightMeasureSet, Module, Module.finrank_eq_card_basis, Module.finrank_pos_iff, Nonempty, ProperSpace, b.toBasis, card_pos_iff, cocompact_eq_bot, convert, finrank_eq_card_basis, finrank_pos_iff, h_le, h_rank, isTightMeasureSet_of_tendsto_measure_norm_gt
-/
lemma isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι 𝕜 E)
    (h : forall i, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪b i, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert! tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : Real) < Fintype.card ι := by
    simpa [← Module.finrank_eq_card_basis b.toBasis, Module.finrank_pos_iff]
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r => ⨆ μ in S, μ {x | r < ‖x‖})
      <= fun r => ∑ i, ⨆ μ in S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
    intro r
    calc ⨆ μ in S, μ {x | r < ‖x‖}
    _ <= ⨆ μ in S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫_𝕜‖ :=
        hx.trans_le (b.norm_le_card_mul_iSup_norm_inner x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ <= ⨆ μ in S, ∑ i, μ {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ <= ∑ i, ⨆ μ in S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      refine iSup_le fun μ => (iSup_le fun hμS => ?_)
      gcongr with i
      exact le_biSup (fun μ => μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) h_le
  rw [← Finset.sum_const_zero]
  refine tendsto_finsetSum Finset.univ fun i _ => (h i).comp ?_
  exact tendsto_id.atTop_div_const (by positivity)

variable (𝕜)

/--
lemma `isTightMeasureSet_of_inner_tendsto` / 引理 `isTightMeasureSet_of_inner_tendsto`

English:
lemma isTightMeasureSet_of_inner_tendsto
  proof: isTightMeasureSet_of_forall_basis_tendsto (stdOrthonormalBasis 𝕜 E)
    fun i => h (stdOrthonormalBasis 𝕜 E i)

中文:
引理 isTightMeasureSet_of_inner_tendsto
  证明: isTightMeasureSet_of_forall_basis_tendsto (stdOrthonormalBasis 𝕜 E)
    fun i => h (stdOrthonormalBasis 𝕜 E i)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, PartOrd, isTightMeasureSet_of_forall_basis_tendsto, stdOrthonormalBasis
-/
lemma isTightMeasureSet_of_inner_tendsto
    (h : forall y, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_forall_basis_tendsto (stdOrthonormalBasis 𝕜 E)
    fun i => h (stdOrthonormalBasis 𝕜 E i)

/--
lemma `isTightMeasureSet_iff_inner_tendsto` / 引理 `isTightMeasureSet_iff_inner_tendsto`

English:
lemma isTightMeasureSet_iff_inner_tendsto
  proof: by
  refine ⟨fun h y => ?_, isTightMeasureSet_of_inner_tendsto 𝕜⟩
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filte

中文:
引理 isTightMeasureSet_iff_inner_tendsto
  证明: by
  refine ⟨fun h y => ?_, isTightMeasureSet_of_inner_tendsto 𝕜⟩
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filte

Depends on / 依赖: FiniteDimensional, FiniteDimensional.proper, ProperSpace, Tendsto, eventually_ge_atTop, filter_upwards, h.comp, inner_zero_left, isTightMeasureSet_iff_tendsto_measure_norm_gt, isTightMeasureSet_of_inner_tendsto, not_lt, not_lt.mpr, proper, tendsto_congr, tendsto_const_nhds, tendsto_id, tendsto_mul_const_atTop_of_pos
-/
lemma isTightMeasureSet_iff_inner_tendsto :
    IsTightMeasureSet S
      ↔ forall y, Tendsto (fun r : Real => ⨆ μ in S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0) := by
  refine ⟨fun h y => ?_, isTightMeasureSet_of_inner_tendsto 𝕜⟩
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r => ⨆ μ in S, μ {x | r * ‖y‖⁻¹ < ‖x‖}) atTop (𝓝 0) :=
h.comp (tendsto_mul_const_atTop_of_pos (by positivity)).mpr tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ => zero_le) ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < ‖⟪y, x⟫_𝕜‖} <= μ {x | r * ‖y‖⁻¹ < ‖x‖} := by
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [mul_inv_lt_iff₀]
    · rw [mul_comm]
      exact hx.trans_le (norm_inner_le_norm y x)
    · positivity
  refine iSup₂_le_iff.mpr fun μ hμS => ?_
exact le_iSup_of_le (i := μ) by simp [hμS, h_le]

variable [BorelSpace E] {μ : Nat -> Measure E} [forall i, IsFiniteMeasure (μ i)]

/--
lemma `isTightMeasureSet_range_of_tendsto_limsup_inner` / 引理 `isTightMeasureSet_range_of_tendsto_limsup_inner`

English:
lemma isTightMeasureSet_range_of_tendsto_limsup_inner
  proof: by
  refine isTightMeasureSet_of_inner_tendsto 𝕜 fun z => ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) (h z) (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {(μ n).map (fun x => ⟪z, x⟫_𝕜)} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_i

中文:
引理 isTightMeasureSet_range_of_tendsto_limsup_inner
  证明: by
  refine isTightMeasureSet_of_inner_tendsto 𝕜 fun z => ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) (h z) (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {(μ n).map (fun x => ⟪z, x⟫_𝕜)} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_i

Depends on / 依赖: IsTightMeasureSet, MeasurableSet, MeasurableSet.preimage, Measure, Measure.map_apply, Nat.tendsto_iSup_of_tendsto_limsup, f.hom, fun_prop, h_map, h_tight, iSup_range, isTightMeasureSet_iff_tendsto_measure_norm_gt, isTightMeasureSet_of_inner_tendsto, isTightMeasureSet_singleton, map_apply, preimage, simp_rw, tendsto_iSup_of_tendsto_limsup
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_inner
    (h : forall y, Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_inner_tendsto 𝕜 fun z => ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n => ?_) (h z) (fun n u v huv => by gcongr)
  have h_tight : IsTightMeasureSet {(μ n).map (fun x => ⟪z, x⟫_𝕜)} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  have h_map r : (μ n).map (fun x => ⟪z, x⟫_𝕜) {x | r < ‖x‖} = μ n {x | r < ‖⟪z, x⟫_𝕜‖} := by
    rw [Measure.map_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  simpa [h_map] using h_tight

/--
lemma `isTightMeasureSet_range_iff_tendsto_limsup_inner` / 引理 `isTightMeasureSet_range_iff_tendsto_limsup_inner`

English:
lemma isTightMeasureSet_range_iff_tendsto_limsup_inner
  proof: by
  refine ⟨fun h z => ?_, isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜⟩
  rw [isTightMeasureSet_iff_inner_tendsto 𝕜] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h z)
    (fun _ => zero_le) fun r => ?_
  simp_rw [iSup_range]
  exact limsup_le_iSup

中文:
引理 isTightMeasureSet_range_iff_tendsto_limsup_inner
  证明: by
  refine ⟨fun h z => ?_, isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜⟩
  rw [isTightMeasureSet_iff_inner_tendsto 𝕜] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h z)
    (fun _ => zero_le) fun r => ?_
  simp_rw [iSup_range]
  exact limsup_le_iSup

Depends on / 依赖: iSup_range, isTightMeasureSet_iff_inner_tendsto, isTightMeasureSet_range_of_tendsto_limsup_inner, limsup_le_iSup, simp_rw, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
lemma isTightMeasureSet_range_iff_tendsto_limsup_inner :
    IsTightMeasureSet (Set.range μ)
      ↔ forall y, Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h z => ?_, isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜⟩
  rw [isTightMeasureSet_iff_inner_tendsto 𝕜] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h z)
    (fun _ => zero_le) fun r => ?_
  simp_rw [iSup_range]
  exact limsup_le_iSup

/--
lemma `isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one` / 引理 `isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one`

English:
lemma isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one
  proof: by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜 fun y => ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r : Real =>

中文:
引理 isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one
  证明: by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜 fun y => ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r : Real =>

Depends on / 依赖: Real.norm_eq_abs, Tendsto, abs_norm, eventually_ge_atTop, filter_upwards, inner_zero_left, inv_mul_can, isTightMeasureSet_range_of_tendsto_limsup_inner, limsup, norm_algebraMap, norm_eq_abs, norm_inv, norm_smul, not_lt, not_lt.mpr, specialize, tendsto_congr, tendsto_const_nhds
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one
    (h : forall y, ‖y‖ = 1
      -> Tendsto (fun r : Real => limsup (fun n => μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜 fun y => ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r : Real => limsup (fun n => μ n {x | ‖y‖⁻¹ * r < ‖⟪(‖y‖⁻¹ : 𝕜) • y, x⟫_𝕜‖})
      atTop) atTop (𝓝 0) := by
    specialize h ((‖y‖⁻¹ : 𝕜) • y) ?_
    · simp only [norm_smul, norm_inv, norm_algebraMap', Real.norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀ (by positivity)]
exact h.comp (tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id
  convert! h' using 7 with r n x
  rw [inner_smul_left]
  simp only [map_inv₀, RCLike.conj_ofReal, norm_mul, norm_inv, norm_algebraMap', norm_norm]
  rw [mul_lt_mul_iff_right₀]
  positivity

/--
lemma `isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one` / 引理 `isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one`

English:
lemma isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
  proof: by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one 𝕜 fun z hz => ?_
  have h_ofReal (r : Real) : limsup (fun n => μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop
      = ENNReal.ofReal (limsup (fun n => (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ENNRe

中文:
引理 isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
  证明: by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one 𝕜 fun z hz => ?_
  have h_ofReal (r : Real) : limsup (fun n => μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop
      = ENNReal.ofReal (limsup (fun n => (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ENNRe

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_limsup_toReal, ENNReal.ofReal_zero, ENNReal.tendsto_ofReal, Set.subset_univ, filter_upwards, h_ofReal, isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one, limsup, measureReal_def, measure_mono, ofReal, ofReal_limsup_toReal, ofReal_zero, simp_rw, subset_univ, tendsto_ofReal
-/
lemma isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
    (h : forall y, ‖y‖ = 1 ->
      Tendsto (fun r : Real => limsup (fun n => (μ n).real {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0))
    (C : Real>=0) (hμ : forallᶠ n in atTop, μ n .univ <= C) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one 𝕜 fun z hz => ?_
  have h_ofReal (r : Real) : limsup (fun n => μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop
      = ENNReal.ofReal (limsup (fun n => (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ENNReal.ofReal_limsup_toReal (C := C)]
    filter_upwards [hμ] with n hμn using (measure_mono (Set.subset_univ _)).trans hμn
  simpa only [h_ofReal, ← ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (h z hz)

end InnerProductSpace

end NormedAddCommGroup

end MeasureTheory
