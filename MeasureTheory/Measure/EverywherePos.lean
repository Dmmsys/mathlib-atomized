/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic.Group
public import Mathlib.Topology.UrysohnsLemma

/-!
# Everywhere positive sets in measure spaces

A set `s` in a topological space with a measure `μ` is *everywhere positive* (also called
*self-supporting*) if any neighborhood `n` of any point of `s` satisfies `μ (s ∩ n) > 0`.

## Main definitions and results

* `μ.IsEverywherePos s` registers that, for any point in `s`, all its neighborhoods have positive
  measure inside `s`.
* `μ.everywherePosSubset s` is the subset of `s` made of those points all of whose neighborhoods
  have positive measure inside `s`.
* `everywherePosSubset_ae_eq` shows that `s` and `μ.everywherePosSubset s` coincide almost
  everywhere if `μ` is inner regular and `s` is measurable.
* `isEverywherePos_everywherePosSubset` shows that `μ.everywherePosSubset s` satisfies the property
  `μ.IsEverywherePos` if `μ` is inner regular and `s` is measurable.

The latter two statements have also versions when `μ` is inner regular for finite measure sets,
assuming additionally that `s` has finite measure.

* `IsEverywherePos.IsGδ` proves that an everywhere positive compact closed set is a Gδ set,
  in a topological group with a left-invariant measure. This is a nontrivial statement, used
  crucially in the study of the uniqueness of Haar measures.
* `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top`: for a Haar measure, any
  finite measure set can be approximated from inside by level sets of continuous
  compactly supported functions. This property is also known as completion-regularity of Haar
  measures.
-/

@[expose] public section

open scoped Topology ENNReal NNReal
open Set Filter

namespace MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/--
Definition of `IsEverywherePos` / `IsEverywherePos` 的定义

English:
definition IsEverywherePos
  signature: (μ : Measure α) (s : Set α)
  body: forall x in s, forall n in 𝓝[s] x, 0 < μ n

中文:
定义 IsEverywherePos
  签名: (μ : 测度 α) (s : 集合 α)
  定义体: forall x in s, forall n in 𝓝[s] x, 0 < μ n
-/
def IsEverywherePos (μ : Measure α) (s : Set α) : Prop :=
  forall x in s, forall n in 𝓝[s] x, 0 < μ n

/--
Definition of `everywherePosSubset` / `everywherePosSubset` 的定义

English:
definition everywherePosSubset
  signature: (μ : Measure α) (s : Set α)
  body: {x | x in s ∧ forall n in 𝓝[s] x, 0 < μ n}

中文:
定义 everywherePosSubset
  签名: (μ : 测度 α) (s : 集合 α)
  定义体: {x | x in s ∧ forall n in 𝓝[s] x, 0 < μ n}
-/
def everywherePosSubset (μ : Measure α) (s : Set α) : Set α :=
  {x | x in s ∧ forall n in 𝓝[s] x, 0 < μ n}

/--
lemma `everywherePosSubset_subset` / 引理 `everywherePosSubset_subset`

English:
lemma everywherePosSubset_subset
  given: (μ : Measure α) (s : Set α)
  statement: μ.everywherePosSubset s subseteq s
  proof: fun _x hx => hx.1

中文:
引理 everywherePosSubset_subset
  条件: (μ : 测度 α) (s : 集合 α)
  结论: μ.everywherePosSubset s subseteq s
  证明: fun _x hx => hx.1
-/
lemma everywherePosSubset_subset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s subseteq s :=
  fun _x hx => hx.1

/--
lemma `exists_isOpen_everywherePosSubset_eq_sdiff` / 引理 `exists_isOpen_everywherePosSubset_eq_sdiff`

English:
lemma exists_isOpen_everywherePosSubset_eq_sdiff
  given: (μ : Measure α) (s : Set α)
  proof: by
  refine ⟨{x | exists n in 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w subsete

中文:
引理 存在_isOpen_everywherePosSubset_eq_sdiff
  条件: (μ : 测度 α) (s : 集合 α)
  证明: by
  refine ⟨{x | exists n in 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w subsete

Depends on / 依赖: everywherePosSubset, inter_comm, inter_mem_nhdsWithin, inter_subset_inter_left, isOpen_iff_mem_nhds, measure_mono_null, mem_nhds, mem_nhdsWithin_iff_exists_mem_nhds_inter, mem_nhds_iff, pos_iff_ne_zero, subseteq, w_open, w_open.mem_nhds
-/
lemma exists_isOpen_everywherePosSubset_eq_sdiff (μ : Measure α) (s : Set α) :
    exists u, IsOpen u ∧ μ.everywherePosSubset s = s \ u := by
  refine ⟨{x | exists n in 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w subseteq {x | exists n in 𝓝[s] x, μ n = 0} := by
    intro y yw
    refine ⟨s inter w, inter_mem_nhdsWithin _ (w_open.mem_nhds yw), measure_mono_null ?_ hx⟩
    rw [inter_comm]
    exact (inter_subset_inter_left _ wv).trans hv
  have B : w in 𝓝 x := w_open.mem_nhds xw
  exact mem_of_superset B A

@[deprecated (since := "2026-06-03")]
alias exists_isOpen_everywherePosSubset_eq_diff := exists_isOpen_everywherePosSubset_eq_sdiff

variable {μ ν : Measure α} {s k : Set α}

/--
lemma `_root_.MeasurableSet.everywherePosSubset` / 引理 `_root_.MeasurableSet.everywherePosSubset`

English:
lemma _root_.MeasurableSet.everywherePosSubset
  statement: [OpensMeasurableSpace α]
  proof: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet

中文:
引理 _root_.可测集.everywherePosSubset
  结论: [OpensMeasurable空间 α]
  证明: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet
-/
protected lemma _root_.MeasurableSet.everywherePosSubset [OpensMeasurableSpace α]
    (hs : MeasurableSet s) :
    MeasurableSet (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet

/--
lemma `_root_.IsClosed.everywherePosSubset` / 引理 `_root_.IsClosed.everywherePosSubset`

English:
lemma _root_.IsClosed.everywherePosSubset
  given: (hs : IsClosed s)
  proof: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open

中文:
引理 _root_.是闭集.everywherePosSubset
  条件: (hs : 是闭集 s)
  证明: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open
-/
protected lemma _root_.IsClosed.everywherePosSubset (hs : IsClosed s) :
    IsClosed (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open

/--
lemma `_root_.IsCompact.everywherePosSubset` / 引理 `_root_.IsCompact.everywherePosSubset`

English:
lemma _root_.IsCompact.everywherePosSubset
  given: (hs : IsCompact s)
  proof: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open

中文:
引理 _root_.是紧集.everywherePosSubset
  条件: (hs : 是紧集 s)
  证明: by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open
-/
protected lemma _root_.IsCompact.everywherePosSubset (hs : IsCompact s) :
    IsCompact (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_sdiff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open

/--
lemma `measure_eq_zero_of_subset_sdiff_everywherePosSubset` / 引理 `measure_eq_zero_of_subset_sdiff_everywherePosSubset`

English:
lemma measure_eq_zero_of_subset_sdiff_everywherePosSubset
  proof: by
  apply hk.induction_on (p := fun t => μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht => measure_mono_null hst ht
  · exact fun s t hs ht => measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : exists u in 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] 

中文:
引理 measure_eq_zero_of_subset_sdiff_everywherePosSubset
  证明: by
  apply hk.induction_on (p := fun t => μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht => measure_mono_null hst ht
  · exact fun s t hs ht => measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : exists u in 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] 

Depends on / 依赖: everywherePosSubset, hk.induction_on, induction_on, k.trans, measure_empty, measure_mono_null, measure_union_null, nhdsWithin_mono, sdiff_subset
-/
lemma measure_eq_zero_of_subset_sdiff_everywherePosSubset
    (hk : IsCompact k) (h'k : k subseteq s \ μ.everywherePosSubset s) : μ k = 0 := by
  apply hk.induction_on (p := fun t => μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht => measure_mono_null hst ht
  · exact fun s t hs ht => measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : exists u in 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] using (h'k hx).2
    exact ⟨u, nhdsWithin_mono x (h'k.trans sdiff_subset) ux, hu⟩

/--
lemma `everywherePosSubset_ae_eq` / 引理 `everywherePosSubset_ae_eq`

English:
lemma everywherePosSubset_ae_eq
  given: [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s)
  proof: by
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

中文:
引理 everywherePosSubset_ae_eq
  条件: [OpensMeasurable空间 α] [内正则 μ] (hs : 可测集 s)
  证明: by
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, ae_eq_set, everywherePosSubset, everywherePosSubset_subset, hs.diff, hs.everywherePosSubset, iSup_eq_zero, measure_empty, measure_eq_iSup_isCompact, measure_eq_zero_of_subset_sdiff_everywherePosSubset, sdiff_eq_empty, sdiff_eq_empty.mpr, true_and
-/
lemma everywherePosSubset_ae_eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

/--
lemma `everywherePosSubset_ae_eq_of_measure_ne_top` / 引理 `everywherePosSubset_ae_eq_of_measure_ne_top`

English:
lemma everywherePosSubset_ae_eq_of_measure_ne_top
  proof: by
  have A : μ (s \ μ.everywherePosSubset s) != ∞ :=
    ((measure_mono sdiff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal

中文:
引理 everywherePosSubset_ae_eq_of_measure_ne_top
  证明: by
  have A : μ (s \ μ.everywherePosSubset s) != ∞ :=
    ((measure_mono sdiff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, ae_eq_set, everywherePosSubset, everywherePosSubset_subset, hs.diff, hs.everywherePosSubset, iSup_eq_zero, lt_top, measure_empty, measure_eq_iSup_isCompact_of_ne_top, measure_eq_zero_of_subset_sdiff_everywherePosSubset, measure_mono, s.lt_top, sdiff_eq_empty, sdiff_eq_empty.mpr, sdiff_subset, trans_lt, true_and
-/
lemma everywherePosSubset_ae_eq_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  have A : μ (s \ μ.everywherePosSubset s) != ∞ :=
    ((measure_mono sdiff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, sdiff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_sdiff_everywherePosSubset h'k hk

/--
lemma `isEverywherePos_everywherePosSubset` / 引理 `isEverywherePos_everywherePosSubset`

English:
lemma isEverywherePos_everywherePosSubset
  proof: by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ]

中文:
引理 isEverywherePos_everywherePosSubset
  证明: by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ]

Depends on / 依赖: A.trans_le, B.measure_eq, ae_eq_refl, ae_eq_set_inter, everywherePosSubset, everywherePosSubset_ae_eq, inter_comm, inter_mem_nhdsWithin, measure_eq, measure_mono, mem_nhdsWithin_iff_exists_mem_nhds_inter, trans_le, u_mem
-/
lemma isEverywherePos_everywherePosSubset
    [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ] (u inter s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq hs)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

/--
lemma `isEverywherePos_everywherePosSubset_of_measure_ne_top` / 引理 `isEverywherePos_everywherePosSubset_of_measure_ne_top`

English:
lemma isEverywherePos_everywherePosSubset_of_measure_ne_top
  proof: by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ]

中文:
引理 isEverywherePos_everywherePosSubset_of_measure_ne_top
  证明: by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ]

Depends on / 依赖: A.trans_le, B.measure_eq, ae_eq_refl, ae_eq_set_inter, everywherePosSubset, everywherePosSubset_ae_eq_of_measure_ne_top, inter_comm, inter_mem_nhdsWithin, measure_eq, measure_mono, mem_nhdsWithin_iff_exists_mem_nhds_inter, trans_le, u_mem
-/
lemma isEverywherePos_everywherePosSubset_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s != ∞) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u inter s) := by
    have : u inter s in 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u inter μ.everywherePosSubset s : Set α) =ᵐ[μ] (u inter s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq_of_measure_ne_top hs h's)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

/--
lemma `IsEverywherePos.smul_measure` / 引理 `IsEverywherePos.smul_measure`

English:
lemma IsEverywherePos.smul_measure
  given: (hs : IsEverywherePos μ s) {c : Real>=0∞} (hc : c != 0)
  proof: fun x hx n hn => by simpa [hc.bot_lt, hs x hx n hn] using hc.bot_lt

中文:
引理 IsEverywherePos.smul_measure
  条件: (hs : IsEverywherePos μ s) {c : 实数>=0∞} (hc : c != 0)
  证明: fun x hx n hn => by simpa [hc.bot_lt, hs x hx n hn] using hc.bot_lt

Depends on / 依赖: bot_lt, hc.bot_lt
-/
lemma IsEverywherePos.smul_measure (hs : IsEverywherePos μ s) {c : Real>=0∞} (hc : c != 0) :
    IsEverywherePos (c • μ) s :=
  fun x hx n hn => by simpa [hc.bot_lt, hs x hx n hn] using hc.bot_lt

/--
lemma `IsEverywherePos.smul_measure_nnreal` / 引理 `IsEverywherePos.smul_measure_nnreal`

English:
lemma IsEverywherePos.smul_measure_nnreal
  given: (hs : IsEverywherePos μ s) {c : Real>=0} (hc : c != 0)
  proof: hs.smul_measure (by simpa using hc)

中文:
引理 IsEverywherePos.smul_measure_nnreal
  条件: (hs : IsEverywherePos μ s) {c : 实数>=0} (hc : c != 0)
  证明: hs.smul_measure (by simpa using hc)

Depends on / 依赖: hs.smul_measure, smul_measure
-/
lemma IsEverywherePos.smul_measure_nnreal (hs : IsEverywherePos μ s) {c : Real>=0} (hc : c != 0) :
    IsEverywherePos (c • μ) s :=
  hs.smul_measure (by simpa using hc)

/--
lemma `IsEverywherePos.of_forall_exists_nhds_eq` / 引理 `IsEverywherePos.of_forall_exists_nhds_eq`

English:
lemma IsEverywherePos.of_forall_exists_nhds_eq
  statement: (hs : IsEverywherePos μ s)
  proof: by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n inter t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

中文:
引理 IsEverywherePos.of_对任意_存在_nhds_eq
  结论: (hs : IsEverywherePos μ s)
  证明: by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n inter t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

Depends on / 依赖: inter_mem, inter_subset_left, inter_subset_right, mem_nhdsWithin_of_mem_nhds, t_mem
-/
lemma IsEverywherePos.of_forall_exists_nhds_eq (hs : IsEverywherePos μ s)
    (h : forall x in s, exists t in 𝓝 x, forall u subseteq t, ν u = μ u) : IsEverywherePos ν s := by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n inter t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

/--
lemma `isEverywherePos_iff_of_forall_exists_nhds_eq` / 引理 `isEverywherePos_iff_of_forall_exists_nhds_eq`

English:
lemma isEverywherePos_iff_of_forall_exists_nhds_eq
  given: (h : forall x in s, exists t in 𝓝 x, forall u subseteq t, ν u = μ u)
  proof: by
  refine ⟨fun H => H.of_forall_exists_nhds_eq ?_, fun H => H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu => (h't u hu).symm⟩

中文:
引理 isEverywherePos_iff_of_对任意_存在_nhds_eq
  条件: (h : 对任意 x in s, 存在 t in 𝓝 x, 对任意 u subseteq t, ν u = μ u)
  证明: by
  refine ⟨fun H => H.of_forall_exists_nhds_eq ?_, fun H => H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu => (h't u hu).symm⟩

Depends on / 依赖: H.of_forall_exists_nhds_eq, of_forall_exists_nhds_eq
-/
lemma isEverywherePos_iff_of_forall_exists_nhds_eq (h : forall x in s, exists t in 𝓝 x, forall u subseteq t, ν u = μ u) :
    IsEverywherePos ν s ↔ IsEverywherePos μ s := by
  refine ⟨fun H => H.of_forall_exists_nhds_eq ?_, fun H => H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu => (h't u hu).symm⟩

/--
lemma `_root_.IsOpen.isEverywherePos` / 引理 `_root_.IsOpen.isEverywherePos`

English:
lemma _root_.IsOpen.isEverywherePos
  given: [IsOpenPosMeasure μ] (hs : IsOpen s)
  statement: IsEverywherePos μ s
  proof: by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

中文:
引理 _root_.是开集.isEverywherePos
  条件: [是OpenPosMeasure μ] (hs : 是开集 s)
  结论: IsEverywherePos μ s
  证明: by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

Depends on / 依赖: lt_of_lt_of_le, measure_mono, measure_pos, mem_nhdsWithin, u_open, u_open.inter
-/
lemma _root_.IsOpen.isEverywherePos [IsOpenPosMeasure μ] (hs : IsOpen s) : IsEverywherePos μ s := by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]

open scoped Pointwise

/-- If a compact closed set is everywhere positive with respect to a left-invariant measure on a
topological group, then it is a Gδ set. This is nontrivial, as there is no second-countability or
metrizability assumption in the statement, so a general compact closed set has no reason to be
a countable intersection of open sets. -/
@[to_additive
/-- If a compact closed set is everywhere positive with respect to a left-invariant measure on a
topological additive group, then it is a Gδ set. This is nontrivial, as there is no
second-countability or metrizability assumption in the statement, so a general compact closed set
has no reason to be a countable intersection of open sets. -/]
/--
lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant` / 引理 `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`

English:
lemma IsEverywherePos.IsGdelta_of_isMulLeftInvariant
  proof: by
  /- Consider a decreasing sequence of open neighborhoods `Vₙ` of the identity, such that `g k \ k`
  has small measure for all `g ∈ Vₙ`. We claim that `k = ⋂ Vₙ k`, which proves
  the lemma as the sets on the right are open. The inclusion `⊆` is trivial.
  Let us show the converse. Take `x` in t

中文:
引理 IsEverywherePos.IsGdelta_of_isMulLeftInvariant
  证明: by
  /- Consider a decreasing sequence of open neighborhoods `Vₙ` of the identity, such that `g k \ k`
  has small measure for all `g ∈ Vₙ`. We claim that `k = ⋂ Vₙ k`, which proves
  the lemma as the sets on the right are open. The inclusion `⊆` is trivial.
  Let us show the converse. Take `x` in t
-/
lemma IsEverywherePos.IsGdelta_of_isMulLeftInvariant
    {k : Set G} (h : μ.IsEverywherePos k) (hk : IsCompact k) (h'k : IsClosed k) :
    IsGδ k := by
  /- Consider a decreasing sequence of open neighborhoods `Vₙ` of the identity, such that `g k \ k`
  has small measure for all `g ∈ Vₙ`. We claim that `k = ⋂ Vₙ k`, which proves
  the lemma as the sets on the right are open. The inclusion `⊆` is trivial.
  Let us show the converse. Take `x` in the intersection. For each `n`, write `x = vₙ yₙ` with
  `vₙ ∈ Vₙ` and `yₙ ∈ k`. Let `z ∈ k` be a cluster value of `yₙ`, by compactness. As multiplication
  by `vₙ = x yₙ⁻¹ ∈ Vₙ` changes the measure of `k` by very little, passing to the limit we get
  `μ (x z⁻¹ k \ k) = 0`. By invariance of the measure under `z x ⁻¹`, we get `μ (k \ z x⁻¹ k) = 0`.
  Assume `x ∉ k`. Then `z ∈ k \ z x⁻¹ k`. Even more, this set is a neighborhood of `z` within `k`
  (as `z x⁻¹ k` is closed), and it has zero measure. This contradicts the fact that `k` has
  positive measure around the point `z`. -/
  obtain ⟨u, -, u_mem, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), u n in Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : Real>=0∞) < 1)
  have : forall n, exists (W : Set G), IsOpen W ∧ 1 in W ∧ forall g in W * W, μ ((g • k) \ k) < u n :=
    fun n => exists_open_nhds_one_mul_subset
      (eventually_nhds_one_measure_smul_sdiff_lt hk h'k (u_mem n).1.ne')
  choose W W_open mem_W hW using this
  let V n := ⋂ i in Finset.range n, W i
  suffices ⋂ n, V n * k subseteq k by
    replace : k = ⋂ n, V n * k := by
      apply Subset.antisymm (subset_iInter_iff.2 (fun n => ?_)) this
      exact subset_mul_right k (by simp [V, mem_W])
    rw [this]
    refine .iInter_of_isOpen fun n => ?_
    exact .mul_right (isOpen_biInter_finset (fun i _hi => W_open i))
  intro x hx
  choose v hv y hy hvy using mem_iInter.1 hx
  obtain ⟨z, zk, hz⟩ : exists z in k, MapClusterPt z atTop y := hk.exists_mapClusterPt (by simp [hy])
  have A n : μ (((x * z⁻¹) • k) \ k) <= u n := by
    apply le_of_lt (hW _ _ ?_)
    have : W n * {z} in 𝓝 z := (IsOpen.mul_right (W_open n)).mem_nhds (by simp [mem_W])
    obtain ⟨i, hi, ni⟩ : exists i, y i in W n * {z} ∧ n < i :=
      ((hz.frequently this).and_eventually (eventually_gt_atTop n)).exists
    refine ⟨x * (y i) ⁻¹, ?_, y i * z⁻¹, by simpa using hi, by group⟩
    have I : V i subseteq W n := iInter₂_subset n (by simp [ni])
    have J : x * (y i)⁻¹ in V i := by simpa [← hvy i] using hv i
    exact I J
  have B : μ (((x * z⁻¹) • k) \ k) = 0 :=
    le_antisymm (ge_of_tendsto u_lim (Eventually.of_forall A)) bot_le
  have C : μ (k \ (z * x⁻¹) • k) = 0 := by
    have : μ ((z * x⁻¹) • (((x * z⁻¹) • k) \ k)) = 0 := by rwa [measure_smul]
    rw [← this]; rw [smul_set_sdiff]; rw [smul_smul]
    group
    simp
  by_contra H
  have : k inter ((z * x⁻¹) • k)ᶜ in 𝓝[k] z := by
    apply inter_mem_nhdsWithin k
    apply IsOpen.mem_nhds (by simpa using h'k.smul _)
    push _ in _
    contrapose H
    simpa [mem_smul_set_iff_inv_smul_mem] using H
  have : 0 < μ (k \ ((z * x⁻¹) • k)) := h z zk _ this
  exact lt_irrefl _ (C.le.trans_lt this)

/-- **Halmos' theorem: Haar measure is completion regular.** More precisely, any finite measure
set can be approximated from inside by a level set of a continuous function with compact support. -/
@[to_additive innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_addGroup
/-- **Halmos' theorem: Haar measure is completion regular.** More precisely, any finite measure
set can be approximated from inside by a level set of a continuous function with compact
support. -/]
/--
theorem `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group` / 定理 `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group`

English:
theorem innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group
  proof: by
  /- First, approximate a measurable set from inside by a compact closed set `K`. Then notice that
  the everywhere positive subset of `K` is a Gδ,
  by Lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`, and therefore the level set of a
  continuous compactly supported function. Moreover, it

中文:
定理 innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group
  证明: by
  /- First, approximate a measurable set from inside by a compact closed set `K`. Then notice that
  the everywhere positive subset of `K` is a Gδ,
  by Lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`, and therefore the level set of a
  continuous compactly supported function. Moreover, it
-/
theorem innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group :
    InnerRegularWRT μ (fun s => exists (f : G -> Real), Continuous f ∧ HasCompactSupport f ∧ s = f ⁻¹' {1})
    (fun s => MeasurableSet s ∧ μ s != ∞) := by
  /- First, approximate a measurable set from inside by a compact closed set `K`. Then notice that
  the everywhere positive subset of `K` is a Gδ,
  by Lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`, and therefore the level set of a
  continuous compactly supported function. Moreover, it has the same measure as `K`. -/
  apply InnerRegularWRT.trans _ innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
  intro K ⟨K_comp, K_closed⟩ r hr
  let L := μ.everywherePosSubset K
  have L_comp : IsCompact L := K_comp.everywherePosSubset
  have L_closed : IsClosed L := K_closed.everywherePosSubset
  refine ⟨L, everywherePosSubset_subset μ K, ?_, ?_⟩
  · have : μ.IsEverywherePos L :=
      isEverywherePos_everywherePosSubset_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne
    have L_Gδ : IsGδ L := this.IsGdelta_of_isMulLeftInvariant L_comp L_closed
    obtain ⟨⟨f, f_cont⟩, Lf, -, f_comp, -⟩ : exists f : C(G, Real), L = f ⁻¹' {1} ∧ EqOn f 0 ∅
        ∧ HasCompactSupport f ∧ forall x, f x in Icc (0 : Real) 1 :=
      exists_continuous_one_zero_of_isCompact_of_isGδ L_comp L_Gδ isClosed_empty
        (disjoint_empty L)
    exact ⟨f, f_cont, f_comp, Lf⟩
  · convert! hr using 1
    apply measure_congr
    exact everywherePosSubset_ae_eq_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne

end IsTopologicalGroup

end Measure

end MeasureTheory
