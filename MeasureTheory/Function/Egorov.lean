/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`: Egorov's theorem which shows that a sequence of
  almost everywhere convergent functions converges uniformly except on an arbitrarily small set.

-/

@[expose] public section


noncomputable section

open MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [PseudoEMetricSpace β] {μ : Measure α}

namespace Egorov

/--
Definition of `notConvergentSeq` / `notConvergentSeq` 的定义

English:
definition notConvergentSeq
  signature: [Preorder ι] (f : ι -> α -> β) (g : α -> β) (n : Nat) (j : ι)
  body: ⋃ (k) (_ : j <= k), { x | (n : Real>=0∞)⁻¹ < edist (f k x) (g x) }

中文:
定义 notConvergentSeq
  签名: [预序 ι] (f : ι -> α -> β) (g : α -> β) (n : 自然数) (j : ι)
  定义体: ⋃ (k) (_ : j <= k), { x | (n : Real>=0∞)⁻¹ < edist (f k x) (g x) }
-/
def notConvergentSeq [Preorder ι] (f : ι -> α -> β) (g : α -> β) (n : Nat) (j : ι) : Set α :=
  ⋃ (k) (_ : j <= k), { x | (n : Real>=0∞)⁻¹ < edist (f k x) (g x) }

variable {n : Nat} {j : ι} {s : Set α} {ε : Real} {f : ι -> α -> β} {g : α -> β}

/--
theorem `mem_notConvergentSeq_iff` / 定理 `mem_notConvergentSeq_iff`

English:
theorem mem_notConvergentSeq_iff
  given: [Preorder ι] {x : α}
  proof: by
  simp_rw [notConvergentSeq, Set.mem_iUnion, exists_prop, mem_ofPred]

中文:
定理 mem_notConvergentSeq_iff
  条件: [预序 ι] {x : α}
  证明: by
  simp_rw [notConvergentSeq, Set.mem_iUnion, exists_prop, mem_ofPred]

Depends on / 依赖: Set.mem_iUnion, exists_prop, mem_iUnion, mem_ofPred, notConvergentSeq, simp_rw
-/
theorem mem_notConvergentSeq_iff [Preorder ι] {x : α} :
    x in notConvergentSeq f g n j ↔ exists k >= j, (n : Real>=0∞)⁻¹ < edist (f k x) (g x) := by
  simp_rw [notConvergentSeq, Set.mem_iUnion, exists_prop, mem_ofPred]

/--
theorem `notConvergentSeq_antitone` / 定理 `notConvergentSeq_antitone`

English:
theorem notConvergentSeq_antitone
  given: [Preorder ι]
  statement: Antitone (notConvergentSeq f g n)
  proof: fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩

中文:
定理 notConvergentSeq_antitone
  条件: [预序 ι]
  结论: 递减 (notConvergentSeq f g n)
  证明: fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩

Depends on / 依赖: Set.Subset.rfl, Set.iUnion, Subset, le_trans
-/
theorem notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) :=
  fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩

/--
theorem `measure_inter_notConvergentSeq_eq_zero` / 定理 `measure_inter_notConvergentSeq_eq_zero`

English:
theorem measure_inter_notConvergentSeq_eq_zero
  statement: [SemilatticeSup ι] [Nonempty ι]
  proof: by
  simp_rw [EMetric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero]; rw [← hfg]
  refine measure_mono fun x => ?_
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_notConvergentSeq_iff]
  push Not
  rintro ⟨hmem, hx⟩
  refine ⟨hmem, (n : Real>=0∞)⁻¹, by simp, fun N => ?_⟩
  obtain ⟨n, 

中文:
定理 measure_inter_notConvergentSeq_eq_zero
  结论: [SemilatticeSup ι] [非空 ι]
  证明: by
  simp_rw [EMetric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero]; rw [← hfg]
  refine measure_mono fun x => ?_
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_notConvergentSeq_iff]
  push Not
  rintro ⟨hmem, hx⟩
  refine ⟨hmem, (n : Real>=0∞)⁻¹, by simp, fun N => ?_⟩
  obtain ⟨n, 

Depends on / 依赖: EMetric, EMetric.tendsto_atTop, Set.mem_iInter, Set.mem_inter_iff, ae_iff, measure_mono, mem_iInter, mem_inter_iff, mem_notConvergentSeq_iff, nonpos_iff_eq_zero, simp_rw, tendsto_atTop
-/
theorem measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) :
    μ (s inter ⋂ j, notConvergentSeq f g n j) = 0 := by
  simp_rw [EMetric.tendsto_atTop, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero]; rw [← hfg]
  refine measure_mono fun x => ?_
  simp only [Set.mem_inter_iff, Set.mem_iInter, mem_notConvergentSeq_iff]
  push Not
  rintro ⟨hmem, hx⟩
  refine ⟨hmem, (n : Real>=0∞)⁻¹, by simp, fun N => ?_⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩

/--
theorem `notConvergentSeq_measurableSet` / 定理 `notConvergentSeq_measurableSet`

English:
theorem notConvergentSeq_measurableSet
  statement: [Preorder ι] [Countable ι]
  proof: MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
measurableSet_lt measurable_const hf k

中文:
定理 notConvergentSeq_measurableSet
  结论: [预序 ι] [可数 ι]
  证明: MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
measurableSet_lt measurable_const hf k

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, measurableSet_lt, measurable_const
-/
theorem notConvergentSeq_measurableSet [Preorder ι] [Countable ι]
    (hf : forall n, Measurable (fun a => edist (f n a) (g a))) :
    MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
measurableSet_lt measurable_const hf k

/--
theorem `measure_notConvergentSeq_tendsto_zero` / 定理 `measure_notConvergentSeq_tendsto_zero`

English:
theorem measure_notConvergentSeq_tendsto_zero
  statement: [SemilatticeSup ι] [Countable ι]
  proof: by
  rcases isEmpty_or_nonempty ι with h | h
  · have : (fun j => μ (s inter notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n]; rw [Set.inter_iInter]
  refine te

中文:
定理 measure_notConvergentSeq_tendsto_zero
  结论: [SemilatticeSup ι] [可数 ι]
  证明: by
  rcases isEmpty_or_nonempty ι with h | h
  · have : (fun j => μ (s inter notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n]; rw [Set.inter_iInter]
  refine te

Depends on / 依赖: Set.inter_iInter, Set.inter_subset_inter_right, eq_iff_true_of_subsingleton, h.some, hsm.inter, inter_iInter, inter_subset_inter_right, isEmpty_or_nonempty, measure_inter_notConvergentSeq_eq_zero, ne_top_of_le_ne_top, notConvergentSeq, notConvergentSeq_antitone, notConvergentSeq_measurableSet, nullMeasurableSet, tendsto_const_nhds, tendsto_measure_iInter_atTop
-/
theorem measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι]
    (hf : forall n, Measurable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s != ∞) (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) :
    Tendsto (fun j => μ (s inter notConvergentSeq f g n j)) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty ι with h | h
  · have : (fun j => μ (s inter notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n]; rw [Set.inter_iInter]
  refine tendsto_measure_iInter_atTop
    (fun n => (hsm.inter <| notConvergentSeq_measurableSet hf).nullMeasurableSet)
    (fun k l hkl => Set.inter_subset_inter_right _ <| notConvergentSeq_antitone hkl)
    ⟨h.some, ne_top_of_le_ne_top hs (measure_mono Set.inter_subset_left)⟩

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]

/--
theorem `exists_notConvergentSeq_lt` / 定理 `exists_notConvergentSeq_lt`

English:
theorem exists_notConvergentSeq_lt
  statement: (hε : 0 < ε)
  proof: by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hsm hs hfg n) (.ofReal (ε * 2⁻¹ ^ n))
      (by positivity)
  rw [zero_add] at hN
  exact ⟨N, (hN N le_rfl).2⟩

中文:
定理 存在_notConvergentSeq_lt
  结论: (hε : 0 < ε)
  证明: by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hsm hs hfg n) (.ofReal (ε * 2⁻¹ ^ n))
      (by positivity)
  rw [zero_add] at hN
  exact ⟨N, (hN N le_rfl).2⟩

Depends on / 依赖: ENNReal, ENNReal.tendsto_atTop, ENNReal.zero_ne_top, le_rfl, measure_notConvergentSeq_tendsto_zero, ofReal, tendsto_atTop, zero_add, zero_ne_top
-/
theorem exists_notConvergentSeq_lt (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) :
    exists j : ι, μ (s inter notConvergentSeq f g n j) <= ENNReal.ofReal (ε * 2⁻¹ ^ n) := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hsm hs hfg n) (.ofReal (ε * 2⁻¹ ^ n))
      (by positivity)
  rw [zero_add] at hN
  exact ⟨N, (hN N le_rfl).2⟩

/--
Definition of `notConvergentSeqLTIndex` / `notConvergentSeqLTIndex` 的定义

English:
definition notConvergentSeqLTIndex
  signature: (hε : 0 < ε)
  body: Classical.choose exists_notConvergentSeq_lt hε hf hsm hs hfg n

中文:
定义 notConvergentSeqLTIndex
  签名: (hε : 0 < ε)
  定义体: Classical.choose exists_notConvergentSeq_lt hε hf hsm hs hfg n

Depends on / 依赖: Classical, Classical.choose, exists_notConvergentSeq_lt
-/
def notConvergentSeqLTIndex (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) : ι :=
Classical.choose exists_notConvergentSeq_lt hε hf hsm hs hfg n

/--
theorem `notConvergentSeqLTIndex_spec` / 定理 `notConvergentSeqLTIndex_spec`

English:
theorem notConvergentSeqLTIndex_spec
  statement: (hε : 0 < ε)
  proof: Classical.choose_spec exists_notConvergentSeq_lt hε hf hsm hs hfg n

中文:
定理 notConvergentSeqLTIndex_spec
  结论: (hε : 0 < ε)
  证明: Classical.choose_spec exists_notConvergentSeq_lt hε hf hsm hs hfg n

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_notConvergentSeq_lt
-/
theorem notConvergentSeqLTIndex_spec (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : Nat) :
    μ (s inter notConvergentSeq f g n (notConvergentSeqLTIndex hε hf hsm hs hfg n)) <=
      ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
Classical.choose_spec exists_notConvergentSeq_lt hε hf hsm hs hfg n

/--
Definition of `iUnionNotConvergentSeq` / `iUnionNotConvergentSeq` 的定义

English:
definition iUnionNotConvergentSeq
  signature: (hε : 0 < ε)
  body: ⋃ n, s inter notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg n)

中文:
定义 iUnionNotConvergentSeq
  签名: (hε : 0 < ε)
  定义体: ⋃ n, s inter notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg n)

Depends on / 依赖: half_pos, notConvergentSeq, notConvergentSeqLTIndex
-/
def iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s inter notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg n)

/--
theorem `iUnionNotConvergentSeq_measurableSet` / 定理 `iUnionNotConvergentSeq_measurableSet`

English:
theorem iUnionNotConvergentSeq_measurableSet
  statement: (hε : 0 < ε)
  proof: MeasurableSet.iUnion fun _ => hsm.inter notConvergentSeq_measurableSet hf

中文:
定理 iUnionNotConvergentSeq_measurableSet
  结论: (hε : 0 < ε)
  证明: MeasurableSet.iUnion fun _ => hsm.inter notConvergentSeq_measurableSet hf

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, hsm.inter, iUnion, notConvergentSeq_measurableSet
-/
theorem iUnionNotConvergentSeq_measurableSet (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
MeasurableSet iUnionNotConvergentSeq hε hf hsm hs hfg :=
MeasurableSet.iUnion fun _ => hsm.inter notConvergentSeq_measurableSet hf

/--
theorem `measure_iUnionNotConvergentSeq` / 定理 `measure_iUnionNotConvergentSeq`

English:
theorem measure_iUnionNotConvergentSeq
  statement: (hε : 0 < ε)
  proof: by
  refine le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hsm hs hfg) ?_)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left]; rw [← ENNReal.ofReal_tsum_of_nonneg]; rw [inv_eq_one_div]; rw [tsum_geometric_

中文:
定理 measure_iUnionNotConvergentSeq
  结论: (hε : 0 < ε)
  证明: by
  refine le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hsm hs hfg) ?_)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left]; rw [← ENNReal.ofReal_tsum_of_nonneg]; rw [inv_eq_one_div]; rw [tsum_geometric_

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, ENNReal.ofReal_tsum_of_nonneg, ENNReal.tsum_le_tsum, ENNReal.tsum_mul_left, half_pos, inv_eq_one_div, le_trans, measure_iUnion_le, notConvergentSeqLTIndex_spec, ofReal_mul, ofReal_tsum_of_nonneg, simp_rw, summable_geometric_two, tsum_geometric_two, tsum_le_tsum, tsum_mul_left, two_ne_zero
-/
theorem measure_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (iUnionNotConvergentSeq hε hf hsm hs hfg) <= ENNReal.ofReal ε := by
  refine le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hsm hs hfg) ?_)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  rw [ENNReal.tsum_mul_left]; rw [← ENNReal.ofReal_tsum_of_nonneg]; rw [inv_eq_one_div]; rw [tsum_geometric_two]; rw [← ENNReal.ofReal_mul (half_pos hε).le]; rw [div_mul_cancel₀ ε two_ne_zero]
  · intro n; positivity
  · rw [inv_eq_one_div]
    exact summable_geometric_two

/--
theorem `iUnionNotConvergentSeq_subset` / 定理 `iUnionNotConvergentSeq_subset`

English:
theorem iUnionNotConvergentSeq_subset
  statement: (hε : 0 < ε)
  proof: by
  rw [iUnionNotConvergentSeq]; rw [← Set.inter_iUnion]
  exact Set.inter_subset_left

中文:
定理 iUnionNotConvergentSeq_subset
  结论: (hε : 0 < ε)
  证明: by
  rw [iUnionNotConvergentSeq]; rw [← Set.inter_iUnion]
  exact Set.inter_subset_left

Depends on / 依赖: Set.inter_iUnion, Set.inter_subset_left, iUnionNotConvergentSeq, inter_iUnion, inter_subset_left
-/
theorem iUnionNotConvergentSeq_subset (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    iUnionNotConvergentSeq hε hf hsm hs hfg subseteq s := by
  rw [iUnionNotConvergentSeq]; rw [← Set.inter_iUnion]
  exact Set.inter_subset_left

/--
theorem `tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq` / 定理 `tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq`

English:
theorem tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq
  statement: (hε : 0 < ε)
  proof: by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  rw [eventually_atTop]
  refine ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg N, fun n hn x hx => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  have : edist (f n x) (g x) <= (N : Real>=0∞)

中文:
定理 tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq
  结论: (hε : 0 < ε)
  证明: by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  rw [eventually_atTop]
  refine ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg N, fun n hn x hx => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  have : edist (f n x) (g x) <= (N : Real>=0∞)

Depends on / 依赖: EMetric, EMetric.tendstoUniformlyOn_iff, ENNReal, ENNReal.exists_inv_nat_lt, Egorov, Egorov.notConvergentSeqLTIndex, Set.mem_iUnion, edist_comm, eventually_atTop, exists_inv_nat_lt, half_pos, lt_of_le_of_lt, mem_iUnion, mem_notConvergentSeq_iff, notConvergentSeqLTIndex, not_lt, not_lt.mp, tendstoUniformlyOn_iff
-/
theorem tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : forall n, Measurable (fun a => edist (f n a) (g a))) (hsm : MeasurableSet s)
    (hs : μ s != ∞) (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg) := by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  rw [eventually_atTop]
  refine ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hsm hs hfg N, fun n hn x hx => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  have : edist (f n x) (g x) <= (N : Real>=0∞)⁻¹ :=
not_lt.mp fun h => hx.2 Set.mem_iUnion.2 ⟨N, hx.1, mem_notConvergentSeq_iff.2 ⟨n, hn, h⟩⟩
  simpa [edist_comm]

@[deprecated (since := "2026-06-03")]
alias tendstoUniformlyOn_diff_iUnionNotConvergentSeq :=
  tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]
  {f : ι -> α -> β} {g : α -> β} {s : Set α}

/--
theorem `tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist` / 定理 `tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist`

English:
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
  proof: ⟨Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq hε hf h

中文:
定理 tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
  证明: ⟨Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq hε hf h

Depends on / 依赖: Egorov, Egorov.iUnionNotConvergentSeq, Egorov.iUnionNotConvergentSeq_measurableSet, Egorov.iUnionNotConvergentSeq_subset, Egorov.measure_iUnionNotConvergentSeq, Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq, iUnionNotConvergentSeq, iUnionNotConvergentSeq_measurableSet, iUnionNotConvergentSeq_subset, measure_iUnionNotConvergentSeq, tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq
-/
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0 < ε) :
    exists t subseteq s, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hsm hs hfg,
    Egorov.tendstoUniformlyOn_sdiff_iUnionNotConvergentSeq hε hf hsm hs hfg⟩

/--
theorem `tendstoUniformlyOn_of_ae_tendsto` / 定理 `tendstoUniformlyOn_of_ae_tendsto`

English:
theorem tendstoUniformlyOn_of_ae_tendsto
  statement: (hf : forall n, StronglyMeasurable (f n))
  proof: tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (fun n => ((hf n).edist hg).measurable) hsm hs hfg hε

中文:
定理 tendstoUniformlyOn_of_ae_tendsto
  结论: (hf : 对任意 n, StronglyMeasurable (f n))
  证明: tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (fun n => ((hf n).edist hg).measurable) hsm hs hfg hε

Depends on / 依赖: measurable, tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
-/
theorem tendstoUniformlyOn_of_ae_tendsto (hf : forall n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s != ∞)
    (hfg : forallᵐ x ∂μ, x in s -> Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0 < ε) :
    exists t subseteq s, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
    (fun n => ((hf n).edist hg).measurable) hsm hs hfg hε

/--
theorem `tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'` / 定理 `tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'`

English:
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'
  statement: [IsFiniteMeasure μ]
  proof: by
  have ⟨t, _, ht, htendsto⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist hf MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine ⟨_, ht, ?_⟩
  rwa [Set.compl_eq_univ_sdiff]

中文:
定理 tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'
  结论: [是有限测度 μ]
  证明: by
  have ⟨t, _, ht, htendsto⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist hf MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine ⟨_, ht, ?_⟩
  rwa [Set.compl_eq_univ_sdiff]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.compl_eq_univ_sdiff, Set.univ, compl_eq_univ_sdiff, filter_upwards, htendsto, measure_ne_top, tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
-/
theorem tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' [IsFiniteMeasure μ]
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real} (hε : 0 < ε) :
    exists t, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ := by
  have ⟨t, _, ht, htendsto⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist hf MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine ⟨_, ht, ?_⟩
  rwa [Set.compl_eq_univ_sdiff]

/--
theorem `tendstoUniformlyOn_of_ae_tendsto'` / 定理 `tendstoUniformlyOn_of_ae_tendsto'`

English:
theorem tendstoUniformlyOn_of_ae_tendsto'
  statement: [IsFiniteMeasure μ] (hf : forall n, StronglyMeasurable (f n))
  proof: tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' (fun n => ((hf n).edist hg).measurable)
    hfg hε

中文:
定理 tendstoUniformlyOn_of_ae_tendsto'
  结论: [是有限测度 μ] (hf : 对任意 n, StronglyMeasurable (f n))
  证明: tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' (fun n => ((hf n).edist hg).measurable)
    hfg hε

Depends on / 依赖: measurable, tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
-/
theorem tendstoUniformlyOn_of_ae_tendsto' [IsFiniteMeasure μ] (hf : forall n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : Real}
    (hε : 0 < ε) :
    exists t, MeasurableSet t ∧ μ t <= ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ :=
  tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' (fun n => ((hf n).edist hg).measurable)
    hfg hε

end MeasureTheory
