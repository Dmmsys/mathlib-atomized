/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Martingale.BorelCantelli
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic

/-!

# The second Borel-Cantelli lemma

This file contains the *second Borel-Cantelli lemma* which states that, given a sequence of
independent sets `(sₙ)` in a probability space, if `∑ n, μ sₙ = ∞`, then the limsup of `sₙ` has
measure 1. We employ a proof using Lévy's generalized Borel-Cantelli by choosing an appropriate
filtration.

## Main result

- `ProbabilityTheory.measure_limsup_eq_one`: the second Borel-Cantelli lemma.

**Note**: for the *first Borel-Cantelli lemma*, which holds in general measure spaces (not only
in probability spaces), see `MeasureTheory.measure_limsup_atTop_eq_zero`.
-/

public section

open scoped ENNReal Topology
open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section BorelCantelli

variable {ι β : Type*} [LinearOrder ι] [mβ : MeasurableSpace β] [NormedAddCommGroup β]
  [BorelSpace β] {f : ι -> Ω -> β} {i j : ι} {s : ι -> Set Ω}

/--
theorem `iIndepFun.indep_comap_natural_of_lt` / 定理 `iIndepFun.indep_comap_natural_of_lt`

English:
theorem iIndepFun.indep_comap_natural_of_lt
  statement: (hf : forall i, StronglyMeasurable (f i))
  proof: by
  suffices Indep (⨆ k in ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k in {k | k <= i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)

中文:
定理 iIndepFun.indep_comap_natural_of_lt
  结论: (hf : 对任意 i, StronglyMeasurable (f i))
  证明: by
  suffices Indep (⨆ k in ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k in {k | k <= i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap, comap_le, iSup_singleton, indep_iSup_of_disjoint, measurable, measurable.comap_le
-/
theorem iIndepFun.indep_comap_natural_of_lt (hf : forall i, StronglyMeasurable (f i))
    (hfi : iIndepFun f μ) (hij : i < j) :
    Indep (MeasurableSpace.comap (f j) mβ) (Filtration.natural f hf i) μ := by
  suffices Indep (⨆ k in ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k in {k | k <= i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)

/--
theorem `iIndepFun.condExp_natural_ae_eq_of_lt` / 定理 `iIndepFun.condExp_natural_ae_eq_of_lt`

English:
theorem iIndepFun.condExp_natural_ae_eq_of_lt
  statement: [SecondCountableTopology β] [CompleteSpace β]
  proof: by
  have : IsProbabilityMeasure μ := hfi.isProbabilityMeasure
  exact condExp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)

中文:
定理 iIndepFun.condExp_natural_ae_eq_of_lt
  结论: [第二可数拓扑 β] [完备空间 β]
  证明: by
  have : IsProbabilityMeasure μ := hfi.isProbabilityMeasure
  exact condExp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)

Depends on / 依赖: Filtration, Filtration.le, IsProbabilityMeasure, comap_le, comap_measurable, condExp_indep_eq, hfi.indep_comap_natural_of_lt, hfi.isProbabilityMeasure, indep_comap_natural_of_lt, isProbabilityMeasure, measurable, measurable.comap_le, stronglyMeasurable
-/
theorem iIndepFun.condExp_natural_ae_eq_of_lt [SecondCountableTopology β] [CompleteSpace β]
    [NormedSpace Real β] (hf : forall i, StronglyMeasurable (f i)) (hfi : iIndepFun f μ)
    (hij : i < j) : μ[f j | Filtration.natural f hf i] =ᵐ[μ] fun _ => μ[f j] := by
  have : IsProbabilityMeasure μ := hfi.isProbabilityMeasure
  exact condExp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)

/--
theorem `iIndepSet.condExp_indicator_filtrationOfSet_ae_eq` / 定理 `iIndepSet.condExp_indicator_filtrationOfSet_ae_eq`

English:
theorem iIndepSet.condExp_indicator_filtrationOfSet_ae_eq
  statement: (hsm : forall n, MeasurableSet (s n))
  proof: by
  rw [Filtration.filtrationOfSet_eq_natural (β := fun _ => Real) hsm]
  refine (iIndepFun.condExp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans ?_
  simp only [integral_indicator_const _ (hsm _), smul_eq_mul, mul_one]; rfl

中文:
定理 iIndepSet.condExp_indicator_filtrationOfSet_ae_eq
  结论: (hsm : 对任意 n, 可测集 (s n))
  证明: by
  rw [Filtration.filtrationOfSet_eq_natural (β := fun _ => Real) hsm]
  refine (iIndepFun.condExp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans ?_
  simp only [integral_indicator_const _ (hsm _), smul_eq_mul, mul_one]; rfl

Depends on / 依赖: Filtration, Filtration.filtrationOfSet_eq_natural, condExp_natural_ae_eq_of_lt, filtrationOfSet_eq_natural, hs.iIndepFun_indicator, iIndepFun, iIndepFun.condExp_natural_ae_eq_of_lt, iIndepFun_indicator, integral_indicator_const, mul_one, smul_eq_mul
-/
theorem iIndepSet.condExp_indicator_filtrationOfSet_ae_eq (hsm : forall n, MeasurableSet (s n))
    (hs : iIndepSet s μ) (hij : i < j) :
    μ[(s j).indicator (fun _ => 1 : Ω -> Real) | filtrationOfSet hsm i] =ᵐ[μ]
    fun _ => μ.real (s j) := by
  rw [Filtration.filtrationOfSet_eq_natural (β := fun _ => Real) hsm]
  refine (iIndepFun.condExp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans ?_
  simp only [integral_indicator_const _ (hsm _), smul_eq_mul, mul_one]; rfl

open Filter

/--
theorem `measure_limsup_eq_one` / 定理 `measure_limsup_eq_one`

English:
theorem measure_limsup_eq_one
  statement: {s : Nat -> Set Ω} (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ)
  proof: by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k in Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this]; rw [measure_univ]
  have : forallᵐ ω ∂μ, forall n, (μ[(s (n + 1)).indicator (1 : Ω -> Real) | filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condExp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  refine eq_true (?_ : Tendsto _ _ _)
  simp_rw [hω]
  have htends : Tendsto (fun n => ∑ k in Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  refine tendsto_atTop_atTop_of_monotone' ?_ ?_
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [← sub_nonneg]; rw [Finset.sum_range_succ_sub_sum]
    exact ENNReal.toReal_nonneg
  · rintro ⟨B, hB⟩
    refine not_eventually.2 (Frequently.of_forall fun n => ?_) (htends B.toNNReal)
    rw [mem_upperBounds] at hB
    specialize hB (∑ k in Finset.range n, μ (s (k + 1))).toReal _
    · refine ⟨n, ?_⟩
      rw [ENNReal.toReal_sum (by finiteness)]
      rfl
    · rwa [not_lt, ENNReal.ofNNReal_toNNReal, ENNReal.le_ofReal_iff_toReal_le]
      · simp
      · exact le_trans (by positivity) hB

中文:
定理 measure_limsup_eq_one
  结论: {s : 自然数 -> 集合 Ω} (hsm : 对任意 n, 可测集 (s n)) (hs : iIndepSet s μ)
  证明: by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k in Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this]; rw [measure_univ]
  have : forallᵐ ω ∂μ, forall n, (μ[(s (n + 1)).indicator (1 : Ω -> Real) | filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condExp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  refine eq_true (?_ : Tendsto _ _ _)
  simp_rw [hω]
  have htends : Tendsto (fun n => ∑ k in Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  refine tendsto_atTop_atTop_of_monotone' ?_ ?_
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [← sub_nonneg]; rw [Finset.sum_range_succ_sub_sum]
    exact ENNReal.toReal_nonneg
  · rintro ⟨B, hB⟩
    refine not_eventually.2 (Frequently.of_forall fun n => ?_) (htends B.toNNReal)
    rw [mem_upperBounds] at hB
    specialize hB (∑ k in Finset.range n, μ (s (k + 1))).toReal _
    · refine ⟨n, ?_⟩
      rw [ENNReal.toReal_sum (by finiteness)]
      rfl
    · rwa [not_lt, ENNReal.ofNNReal_toNNReal, ENNReal.le_ofReal_iff_toReal_le]
      · simp
      · exact le_trans (by positivity) hB

Depends on / 依赖: Finset, Finset.range, IsProbabilityMeasure, Set.univ, Tendsto, ae_mem_limsup_atTop_iff, eventuallyEq_set, filtrationOfSet, hs.isProbabilityMeasure, indicator, isProbabilityMeasure, limsup, measurableSet_filtrationOfSet, measure_congr
-/
theorem measure_limsup_eq_one {s : Nat -> Set Ω} (hsm : forall n, MeasurableSet (s n)) (hs : iIndepSet s μ)
    (hs' : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1 := by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k in Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k in Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω -> Real)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this]; rw [measure_univ]
  have : forallᵐ ω ∂μ, forall n, (μ[(s (n + 1)).indicator (1 : Ω -> Real) | filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condExp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  refine eq_true (?_ : Tendsto _ _ _)
  simp_rw [hω]
  have htends : Tendsto (fun n => ∑ k in Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  refine tendsto_atTop_atTop_of_monotone' ?_ ?_
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [← sub_nonneg]; rw [Finset.sum_range_succ_sub_sum]
    exact ENNReal.toReal_nonneg
  · rintro ⟨B, hB⟩
    refine not_eventually.2 (Frequently.of_forall fun n => ?_) (htends B.toNNReal)
    rw [mem_upperBounds] at hB
    specialize hB (∑ k in Finset.range n, μ (s (k + 1))).toReal _
    · refine ⟨n, ?_⟩
      rw [ENNReal.toReal_sum (by finiteness)]
      rfl
    · rwa [not_lt, ENNReal.ofNNReal_toNNReal, ENNReal.le_ofReal_iff_toReal_le]
      · simp
      · exact le_trans (by positivity) hB

end BorelCantelli

end ProbabilityTheory
