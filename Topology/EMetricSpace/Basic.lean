/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

Further results about extended metric spaces.
-/

public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

/--
theorem `edist_le_Ico_sum_edist` / 定理 `edist_le_Ico_sum_edist`

English:
theorem edist_le_Ico_sum_edist
  given: (f : Nat -> α) {m n} (h : m <= n)
  proof: by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) <= edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add i

中文:
定理 edist_le_Ico_sum_edist
  条件: (f : 自然数 -> α) {m n} (h : m <= n)
  证明: by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) <= edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add i

Depends on / 依赖: Finset, Finset.Ico, Finset.Ico_self, Finset.insert_Ico_right_eq_Ico_add_one, Finset.sum_empty, Finset.sum_insert, Ico_self, Nat.le_induction, add_comm, add_le_add, edist_self, edist_triangle, insert_Ico_right_eq_Ico_add_one, le_induction, le_rfl, sum_empty, sum_insert
-/
theorem edist_le_Ico_sum_edist (f : Nat -> α) {m n} (h : m <= n) :
    edist (f m) (f n) <= ∑ i in Finset.Ico m n, edist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) <= edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle]; rw [Finset.sum_insert]; rw [add_comm]; simp

/--
theorem `edist_le_range_sum_edist` / 定理 `edist_le_range_sum_edist`

English:
theorem edist_le_range_sum_edist
  given: (f : Nat -> α) (n : Nat)
  proof: Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

中文:
定理 edist_le_range_sum_edist
  条件: (f : 自然数 -> α) (n : 自然数)
  证明: Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, Nat.zero_le, edist_le_Ico_sum_edist, zero_le
-/
theorem edist_le_range_sum_edist (f : Nat -> α) (n : Nat) :
    edist (f 0) (f n) <= ∑ i in Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

/--
theorem `edist_le_Ico_sum_of_edist_le` / 定理 `edist_le_Ico_sum_of_edist_le`

English:
theorem edist_le_Ico_sum_of_edist_le
  statement: {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞}
  proof: le_trans (edist_le_Ico_sum_edist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

中文:
定理 edist_le_Ico_sum_of_edist_le
  结论: {f : 自然数 -> α} {m n} (hmn : m <= n) {d : 自然数 -> 实数>=0∞}
  证明: le_trans (edist_le_Ico_sum_edist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.sum_le_sum, edist_le_Ico_sum_edist, le_trans, mem_Ico, sum_le_sum
-/
theorem edist_le_Ico_sum_of_edist_le {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞}
    (hd : forall {k}, m <= k -> k < n -> edist (f k) (f (k + 1)) <= d k) :
    edist (f m) (f n) <= ∑ i in Finset.Ico m n, d i :=
le_trans (edist_le_Ico_sum_edist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/--
theorem `edist_le_range_sum_of_edist_le` / 定理 `edist_le_range_sum_of_edist_le`

English:
theorem edist_le_range_sum_of_edist_le
  statement: {f : Nat -> α} (n : Nat) {d : Nat -> Real>=0∞}
  proof: Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le zero_le fun _ => hd

中文:
定理 edist_le_range_sum_of_edist_le
  结论: {f : 自然数 -> α} (n : 自然数) {d : 自然数 -> 实数>=0∞}
  证明: Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le zero_le fun _ => hd

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, edist_le_Ico_sum_of_edist_le, zero_le
-/
theorem edist_le_range_sum_of_edist_le {f : Nat -> α} (n : Nat) {d : Nat -> Real>=0∞}
    (hd : forall {k}, k < n -> edist (f k) (f (k + 1)) <= d k) :
    edist (f 0) (f n) <= ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le zero_le fun _ => hd

namespace EMetric

/--
theorem `isUniformInducing_iff` / 定理 `isUniformInducing_iff`

English:
theorem isUniformInducing_iff
  given: [PseudoEMetricSpace β] {f : α -> β}
  proof: isUniformInducing_iff'.trans Iff.rfl.and
((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans by
      simp only [subset_def, Prod.forall]; rfl

中文:
定理 isUniformInducing_iff
  条件: [PseudoEMetric空间 β] {f : α -> β}
  证明: isUniformInducing_iff'.trans Iff.rfl.and
((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans by
      simp only [subset_def, Prod.forall]; rfl

Depends on / 依赖: Iff.rfl.and, Prod.forall, isUniformInducing_iff, le_basis_iff, subset_def, uniformity_basis_edist, uniformity_basis_edist.comap
-/
theorem isUniformInducing_iff [PseudoEMetricSpace β] {f : α -> β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, edist (f a) (f b) < ε -> edist a b < δ :=
isUniformInducing_iff'.trans Iff.rfl.and
((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans by
      simp only [subset_def, Prod.forall]; rfl

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
nonrec theorem isUniformEmbedding_iff [PseudoEMetricSpace β] {f : α -> β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, edist (f a) (f b) < ε -> edist a b < δ :=
(isUniformEmbedding_iff _).trans and_comm.trans Iff.rfl.and isUniformInducing_iff

/--
theorem `controlled_of_isUniformInducing` / 定理 `controlled_of_isUniformInducing`

English:
theorem controlled_of_isUniformInducing
  statement: [PseudoEMetricSpace β] {f : α -> β}
  proof: ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]

中文:
定理 controlled_of_isUniformInducing
  结论: [PseudoEMetric空间 β] {f : α -> β}
  证明: ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]

Depends on / 依赖: h.uniformContinuous, isUniformInducing_iff, uniformContinuous, uniformContinuous_iff
-/
theorem controlled_of_isUniformInducing [PseudoEMetricSpace β] {f : α -> β}
    (h : IsUniformInducing f) :
    (forall ε > 0, exists δ > 0, forall {a b : α}, edist a b < δ -> edist (f a) (f b) < ε) ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, edist (f a) (f b) < ε -> edist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]
/--
theorem `controlled_of_isUniformEmbedding` / 定理 `controlled_of_isUniformEmbedding`

English:
theorem controlled_of_isUniformEmbedding
  statement: [PseudoEMetricSpace β] {f : α -> β}
  proof: controlled_of_isUniformInducing h.toIsUniformInducing

中文:
定理 controlled_of_isUniformEmbedding
  结论: [PseudoEMetric空间 β] {f : α -> β}
  证明: controlled_of_isUniformInducing h.toIsUniformInducing

Depends on / 依赖: controlled_of_isUniformInducing, h.toIsUniformInducing, toIsUniformInducing
-/
theorem controlled_of_isUniformEmbedding [PseudoEMetricSpace β] {f : α -> β}
    (h : IsUniformEmbedding f) :
    (forall ε > 0, exists δ > 0, forall {a b : α}, edist a b < δ -> edist (f a) (f b) < ε) ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, edist (f a) (f b) < ε -> edist a b < δ :=
  controlled_of_isUniformInducing h.toIsUniformInducing

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {f : Filter α}
  proof: by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff

中文:
定理 cauchy_iff
  条件: {f : 滤子 α}
  证明: by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff
-/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f != ⊥ ∧ forall ε > 0, exists t in f, forall x, x in t -> forall y, y in t -> edist x y < ε := by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff

/--
theorem `complete_of_convergent_controlled_sequences` / 定理 `complete_of_convergent_controlled_sequences`

English:
theorem complete_of_convergent_controlled_sequences
  statement: (B : Nat -> Real>=0∞) (hB : forall n, 0 < B n)
  proof: UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

中文:
定理 complete_of_convergent_controlled_sequences
  结论: (B : 自然数 -> 实数>=0∞) (hB : 对任意 n, 0 < B n)
  证明: UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

Depends on / 依赖: UniformSpace, UniformSpace.complete_of_convergent_controlled_sequences, complete_of_convergent_controlled_sequences, edist_mem_uniformity
-/
theorem complete_of_convergent_controlled_sequences (B : Nat -> Real>=0∞) (hB : forall n, 0 < B n)
    (H : forall u : Nat -> α, (forall N n m : Nat, N <= n -> N <= m -> edist (u n) (u m) < B N) ->
      exists x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

/--
theorem `complete_of_cauchySeq_tendsto` / 定理 `complete_of_cauchySeq_tendsto`

English:
theorem complete_of_cauchySeq_tendsto
  proof: UniformSpace.complete_of_cauchySeq_tendsto

中文:
定理 complete_of_cauchySeq_tendsto
  证明: UniformSpace.complete_of_cauchySeq_tendsto

Depends on / 依赖: UniformSpace, UniformSpace.complete_of_cauchySeq_tendsto, complete_of_cauchySeq_tendsto
-/
theorem complete_of_cauchySeq_tendsto :
    (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto

/--
theorem `tendstoLocallyUniformlyOn_iff` / 定理 `tendstoLocallyUniformlyOn_iff`

English:
theorem tendstoLocallyUniformlyOn_iff
  statement: {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
  proof: by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

中文:
定理 tendstoLocallyUniformlyOn_iff
  结论: {ι : 类型} [拓扑空间 β] {F : ι -> β -> α} {f : β -> α}
  证明: by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

Depends on / 依赖: Ht.mono, edist_mem_uniformity, mem_uniformity_edist
-/
theorem tendstoLocallyUniformlyOn_iff {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      forall ε > 0, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, edist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/--
theorem `tendstoUniformlyOn_iff` / 定理 `tendstoUniformlyOn_iff`

English:
theorem tendstoUniformlyOn_iff
  given: {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β}
  proof: by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

中文:
定理 tendstoUniformlyOn_iff
  条件: {ι : 类型} {F : ι -> β -> α} {f : β -> α} {p : 滤子 ι} {s : 集合 β}
  证明: by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

Depends on / 依赖: edist_mem_uniformity, mem_uniformity_edist
-/
theorem tendstoUniformlyOn_iff {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ forall ε > 0, forallᶠ n in p, forall x in s, edist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/--
theorem `tendstoLocallyUniformly_iff` / 定理 `tendstoLocallyUniformly_iff`

English:
theorem tendstoLocallyUniformly_iff
  statement: {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
  proof: by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, nhdsWithin_univ]

中文:
定理 tendstoLocallyUniformly_iff
  结论: {ι : 类型} [拓扑空间 β] {F : ι -> β -> α} {f : β -> α}
  证明: by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, nhdsWithin_univ]

Depends on / 依赖: forall_const, mem_univ, nhdsWithin_univ, tendstoLocallyUniformlyOn_iff, tendstoLocallyUniformlyOn_univ
-/
theorem tendstoLocallyUniformly_iff {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      forall ε > 0, forall x : β, exists t in 𝓝 x, forallᶠ n in p, forall y in t, edist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, nhdsWithin_univ]

/--
theorem `tendstoUniformly_iff` / 定理 `tendstoUniformly_iff`

English:
theorem tendstoUniformly_iff
  given: {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Filter ι}
  proof: by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

中文:
定理 tendstoUniformly_iff
  条件: {ι : 类型} {F : ι -> β -> α} {f : β -> α} {p : 滤子 ι}
  证明: by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

Depends on / 依赖: forall_const, mem_univ, tendstoUniformlyOn_iff, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_iff {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Filter ι} :
    TendstoUniformly F f p ↔ forall ε > 0, forallᶠ n in p, forall x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

end EMetric

open Metric

namespace EMetric

variable {x y z : α} {ε ε₁ ε₂ : Real>=0∞} {s t : Set α}

/--
theorem `inseparable_iff` / 定理 `inseparable_iff`

English:
theorem inseparable_iff
  statement: Inseparable x y ↔ edist x y = 0
  proof: by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_gt_iff_le]

alias ⟨_root_.Inseparable.edist_eq_zero, _⟩ := EMetric.inseparable_iff

中文:
定理 inseparable_iff
  结论: 不可分 x y ↔ edist x y = 0
  证明: by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_gt_iff_le]

alias ⟨_root_.Inseparable.edist_eq_zero, _⟩ := EMetric.inseparable_iff

Depends on / 依赖: edist_comm, forall_gt_iff_le, inseparable_iff_mem_closure, mem_closure_iff
-/
theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_gt_iff_le]

alias ⟨_root_.Inseparable.edist_eq_zero, _⟩ := EMetric.inseparable_iff

/--
theorem `nontrivial_iff_nontrivialTopology` / 定理 `nontrivial_iff_nontrivialTopology`

English:
theorem nontrivial_iff_nontrivialTopology
  given: {α} [EMetricSpace α]
  proof: by
  simp_rw [nontrivial_iff, TopologicalSpace.nontrivial_iff_exists_not_inseparable,
    EMetric.inseparable_iff, edist_eq_zero]

中文:
定理 nontrivial_iff_nontrivialTopology
  条件: {α} [广义度量空间 α]
  证明: by
  simp_rw [nontrivial_iff, TopologicalSpace.nontrivial_iff_exists_not_inseparable,
    EMetric.inseparable_iff, edist_eq_zero]

Depends on / 依赖: EMetric, EMetric.inseparable_iff, TopologicalSpace, TopologicalSpace.nontrivial_iff_exists_not_inseparable, edist_eq_zero, inseparable_iff, nontrivial_iff, nontrivial_iff_exists_not_inseparable, simp_rw
-/
theorem nontrivial_iff_nontrivialTopology {α} [EMetricSpace α] :
    Nontrivial α ↔ NontrivialTopology α := by
  simp_rw [nontrivial_iff, TopologicalSpace.nontrivial_iff_exists_not_inseparable,
    EMetric.inseparable_iff, edist_eq_zero]

/--
theorem `subsingleton_iff_indiscreteTopology` / 定理 `subsingleton_iff_indiscreteTopology`

English:
theorem subsingleton_iff_indiscreteTopology
  given: {α} [EMetricSpace α]
  proof: by
  simpa [not_nontrivial_iff_subsingleton] using nontrivial_iff_nontrivialTopology (α := α).not

中文:
定理 subsingleton_iff_indiscreteTopology
  条件: {α} [广义度量空间 α]
  证明: by
  simpa [not_nontrivial_iff_subsingleton] using nontrivial_iff_nontrivialTopology (α := α).not

Depends on / 依赖: nontrivial_iff_nontrivialTopology, not_nontrivial_iff_subsingleton
-/
theorem subsingleton_iff_indiscreteTopology {α} [EMetricSpace α] :
    Subsingleton α ↔ IndiscreteTopology α := by
  simpa [not_nontrivial_iff_subsingleton] using nontrivial_iff_nontrivialTopology (α := α).not

/-- In an (e)metric space, every nontrivial type has a nontrivial topology. -/
instance (priority := 100) {α} [EMetricSpace α] [Nontrivial α] : NontrivialTopology α :=
  nontrivial_iff_nontrivialTopology.1 ‹_›

/--
theorem `cauchySeq_iff` / 定理 `cauchySeq_iff`

English:
theorem cauchySeq_iff
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: uniformity_basis_edist.cauchySeq_iff

中文:
定理 cauchySeq_iff
  条件: [非空 β] [SemilatticeSup β] {u : β -> α}
  证明: uniformity_basis_edist.cauchySeq_iff

Depends on / 依赖: cauchySeq_iff, uniformity_basis_edist, uniformity_basis_edist.cauchySeq_iff
-/
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β -> α} :
    CauchySeq u ↔ forall ε > 0, exists N, forall m, N <= m -> forall n, N <= n -> edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff

/--
theorem `cauchySeq_iff'` / 定理 `cauchySeq_iff'`

English:
theorem cauchySeq_iff'
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: uniformity_basis_edist.cauchySeq_iff'

中文:
定理 cauchySeq_iff'
  条件: [非空 β] [SemilatticeSup β] {u : β -> α}
  证明: uniformity_basis_edist.cauchySeq_iff'

Depends on / 依赖: cauchySeq_iff, uniformity_basis_edist, uniformity_basis_edist.cauchySeq_iff
-/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β -> α} :
    CauchySeq u ↔ forall ε > (0 : Real>=0∞), exists N, forall n >= N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'

/--
theorem `cauchySeq_iff_NNReal` / 定理 `cauchySeq_iff_NNReal`

English:
theorem cauchySeq_iff_NNReal
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: uniformity_basis_edist_nnreal.cauchySeq_iff'

中文:
定理 cauchySeq_iff_NN实数
  条件: [非空 β] [SemilatticeSup β] {u : β -> α}
  证明: uniformity_basis_edist_nnreal.cauchySeq_iff'

Depends on / 依赖: cauchySeq_iff, uniformity_basis_edist_nnreal, uniformity_basis_edist_nnreal.cauchySeq_iff
-/
theorem cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β -> α} :
    CauchySeq u ↔ forall ε : Real>=0, 0 < ε -> exists N, forall n, N <= n -> edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchySeq_iff'

/--
theorem `totallyBounded_iff` / 定理 `totallyBounded_iff`

English:
theorem totallyBounded_iff
  given: {s : Set α}
  proof: ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

中文:
定理 totallyBounded_iff
  条件: {s : 集合 α}
  证明: ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

Depends on / 依赖: edist_mem_uniformity, h.trans, mem_uniformity_edist
-/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ forall ε > 0, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, eball y ε :=
  ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

/--
theorem `totallyBounded_iff'` / 定理 `totallyBounded_iff'`

English:
theorem totallyBounded_iff'
  given: {s : Set α}
  proof: ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

中文:
定理 totallyBounded_iff'
  条件: {s : 集合 α}
  证明: ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

Depends on / 依赖: edist_mem_uniformity, h.trans, mem_uniformity_edist, totallyBounded_iff_subset
-/
theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ forall ε > 0, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, eball y ε :=
  ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
⟨t, ft, h.trans iUnion₂_mono fun _ _ _ => hε⟩⟩

section Compact

/--
theorem `subset_countable_closure_of_almost_dense_set` / 定理 `subset_countable_closure_of_almost_dense_set`

English:
theorem subset_countable_closure_of_almost_dense_set
  statement: (s : Set α)
  proof: by
  apply UniformSpace.subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := uniformity_basis_edist_le.mem_iff.1 hU
  obtain ⟨t, tC, ht⟩ := hs ε hε
  refine ⟨t, tC, ht.trans (iUnion₂_mono fun x hx y hy => UniformSpace.ball_mono hεU x ?_)⟩
  rwa [mem_closedEBall, edist_c

中文:
定理 subset_countable_closure_of_almost_dense_set
  结论: (s : 集合 α)
  证明: by
  apply UniformSpace.subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := uniformity_basis_edist_le.mem_iff.1 hU
  obtain ⟨t, tC, ht⟩ := hs ε hε
  refine ⟨t, tC, ht.trans (iUnion₂_mono fun x hx y hy => UniformSpace.ball_mono hεU x ?_)⟩
  rwa [mem_closedEBall, edist_c

Depends on / 依赖: UniformSpace, UniformSpace.ball_mono, UniformSpace.subset_countable_closure_of_almost_dense_set, ball_mono, edist_comm, ht.trans, mem_closedEBall, mem_iff, subset_countable_closure_of_almost_dense_set, uniformity_basis_edist_le, uniformity_basis_edist_le.mem_iff
-/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : forall ε > 0, exists t : Set α, t.Countable ∧ s subseteq ⋃ x in t, Metric.closedEBall x ε) :
    exists t, t subseteq s ∧ t.Countable ∧ s subseteq closure t := by
  apply UniformSpace.subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := uniformity_basis_edist_le.mem_iff.1 hU
  obtain ⟨t, tC, ht⟩ := hs ε hε
  refine ⟨t, tC, ht.trans (iUnion₂_mono fun x hx y hy => UniformSpace.ball_mono hεU x ?_)⟩
  rwa [mem_closedEBall, edist_comm] at hy

-- TODO: generalize to metrizable spaces
/--
theorem `subset_countable_closure_of_compact` / 定理 `subset_countable_closure_of_compact`

English:
theorem subset_countable_closure_of_compact
  given: {s : Set α} (hs : IsCompact s)
  proof: by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
exact ⟨t, htf.countable, hst.trans iUnion₂_mono fun _ _ => eball_subset_closedEBall⟩

中文:
定理 subset_countable_closure_of_compact
  条件: {s : 集合 α} (hs : 是紧集 s)
  证明: by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
exact ⟨t, htf.countable, hst.trans iUnion₂_mono fun _ _ => eball_subset_closedEBall⟩

Depends on / 依赖: countable, eball_subset_closedEBall, hs.totallyBounded, hst.trans, htf.countable, subset_countable_closure_of_almost_dense_set, totallyBounded, totallyBounded_iff
-/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    exists t, t subseteq s ∧ t.Countable ∧ s subseteq closure t := by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
exact ⟨t, htf.countable, hst.trans iUnion₂_mono fun _ _ => eball_subset_closedEBall⟩

end Compact

section SecondCountable

open TopologicalSpace

variable (α) in
/-- A sigma compact pseudo emetric space has second countable topology. -/
instance (priority := 90) secondCountable_of_sigmaCompact [SigmaCompactSpace α] :
    SecondCountableTopology α := by
  suffices SeparableSpace α by exact UniformSpace.secondCountable_of_separable α
  choose T _ hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine ⟨⟨⋃ n, T n, countable_iUnion hTc, fun x => ?_⟩⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_iUnion _ n) (hsubT _ hn)

/--
theorem `secondCountable_of_almost_dense_set` / 定理 `secondCountable_of_almost_dense_set`

English:
theorem secondCountable_of_almost_dense_set
  proof: by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall ε > 0, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, closedEBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this

中文:
定理 secondCountable_of_almost_dense_set
  证明: by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall ε > 0, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, closedEBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this

Depends on / 依赖: Countable, SeparableSpace, Set.Countable, UniformSpace, UniformSpace.secondCountable_of_separable, closedEBall, mem_univ, secondCountable_of_separable, subset_countable_closure_of_almost_dense_set, subseteq, univ_subset_iff
-/
theorem secondCountable_of_almost_dense_set
    (hs : forall ε > 0, exists t : Set α, t.Countable ∧ ⋃ x in t, closedEBall x ε = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : forall ε > 0, exists t : Set α, Set.Countable t ∧ univ subseteq ⋃ x in t, closedEBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

end SecondCountable

end EMetric

variable {γ : Type w} [EMetricSpace γ]

-- see Note [lower instance priority]
/-- An emetric space is separated -/
instance (priority := 100) EMetricSpace.instT0Space : T0Space γ where
t0 _ _ h := eq_of_edist_eq_zero EMetric.inseparable_iff.1 h

/--
theorem `EMetric.isUniformEmbedding_iff'` / 定理 `EMetric.isUniformEmbedding_iff'`

English:
theorem EMetric.isUniformEmbedding_iff'
  given: [PseudoEMetricSpace β] {f : γ -> β}
  proof: by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

中文:
定理 EMetric.isUniformEmbedding_iff'
  条件: [PseudoEMetric空间 β] {f : γ -> β}
  证明: by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

Depends on / 依赖: isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff
-/
theorem EMetric.isUniformEmbedding_iff' [PseudoEMetricSpace β] {f : γ -> β} :
    IsUniformEmbedding f ↔
      (forall ε > 0, exists δ > 0, forall {a b : γ}, edist a b < δ -> edist (f a) (f b) < ε) ∧
        forall δ > 0, exists ε > 0, forall {a b : γ}, edist (f a) (f b) < ε -> edist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

-- TODO: make it an instance?
/--
Definition of `EMetricSpace.ofT0PseudoEMetricSpace` / `EMetricSpace.ofT0PseudoEMetricSpace` 的定义

English:
abbreviation EMetricSpace.ofT0PseudoEMetricSpace
  signature: (α : Type*) [PseudoEMetricSpace α] [T0Space α]
  body: { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

中文:
缩写 广义度量空间.ofT0PseudoEMetricSpace
  签名: (α : 类型) [PseudoEMetric空间 α] [T0空间 α]
  定义体: { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

Depends on / 依赖: EMetric, EMetric.inseparable_iff, PseudoEMetricSpace, eq_of_edist_eq_zero, inseparable_iff
-/
abbrev EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

/--
Instance `Prod.emetricSpaceMax` / 实例 `Prod.emetricSpaceMax`

English:
instance Prod.emetricSpaceMax
  signature: [EMetricSpace β]
  body: .ofT0PseudoEMetricSpace _

中文:
实例 积类型.emetricSpaceMax
  签名: [广义度量空间 β]
  定义体: .ofT0PseudoEMetricSpace _

Depends on / 依赖: ofT0PseudoEMetricSpace
-/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  .ofT0PseudoEMetricSpace _

namespace EMetric

/--
theorem `countable_closure_of_compact` / 定理 `countable_closure_of_compact`

English:
theorem countable_closure_of_compact
  given: {s : Set γ} (hs : IsCompact s)
  proof: by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

中文:
定理 countable_closure_of_compact
  条件: {s : 集合 γ} (hs : 是紧集 s)
  证明: by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

Depends on / 依赖: antisymm, closure_minimal, hs.isClosed, hsub.antisymm, isClosed, subset_countable_closure_of_compact
-/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    exists t, t subseteq s ∧ t.Countable ∧ s = closure t := by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

end EMetric


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : EDist (SeparationQuotient X) where
  body: SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)

中文:
实例 [PseudoEMetric空间
  签名: X] : EDist (SeparationQuotient X) where
  定义体: SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)
-/
instance [PseudoEMetricSpace X] : EDist (SeparationQuotient X) where
  edist := SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)

/--
theorem `SeparationQuotient.edist_mk` / 定理 `SeparationQuotient.edist_mk`

English:
theorem SeparationQuotient.edist_mk
  given: [PseudoEMetricSpace X] (x y : X)
  proof: rfl

中文:
定理 SeparationQuotient.edist_mk
  条件: [PseudoEMetric空间 X] (x y : X)
  证明: rfl
-/
@[simp] theorem SeparationQuotient.edist_mk [PseudoEMetricSpace X] (x y : X) :
    edist (mk x) (mk y) = edist x y :=
  rfl

open SeparationQuotient in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoEMetricSpace
  signature: X] : EMetricSpace (SeparationQuotient X)
  body: @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
uniformity_edist := comap_

中文:
实例 [PseudoEMetric空间
  签名: X] : 广义度量空间 (SeparationQuotient X)
  定义体: @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
uniformity_edist := comap_

Depends on / 依赖: EMetricSpace, EMetricSpace.ofT0PseudoEMetricSpace, PseudoEMetricSpace, PseudoEMetricSpace.uniformity_edist, SeparationQuotient, comap_injective, comap_mk_uniformity, edist_comm, edist_self, edist_triangle, ofT0PseudoEMetricSpace, prodMap, surjective_mk, surjective_mk.forall, surjective_mk.prodMap, toUniformSpace, uniformity_edist
-/
instance [PseudoEMetricSpace X] : EMetricSpace (SeparationQuotient X) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
uniformity_edist := comap_injective (surjective_mk.prodMap surjective_mk) by
        simp [comap_mk_uniformity, PseudoEMetricSpace.uniformity_edist] } _

section LebesgueNumberLemma

variable {s : Set α}

/--
theorem `lebesgue_number_lemma_of_emetric` / 定理 `lebesgue_number_lemma_of_emetric`

English:
theorem lebesgue_number_lemma_of_emetric
  statement: {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s)
  proof: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma hs hc₁ hc₂

中文:
定理 lebesgue_number_lemma_of_emetric
  结论: {ι : 类型层*} {c : ι -> 集合 α} (hs : 是紧集 s)
  证明: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma hs hc₁ hc₂

Depends on / 依赖: UniformSpace, UniformSpace.ball, edist_comm, lebesgue_number_lemma, preimage_ofPred_eq, uniformity_basis_edist, uniformity_basis_edist.lebesgue_number_lemma
-/
theorem lebesgue_number_lemma_of_emetric {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s)
    (hc₁ : forall i, IsOpen (c i)) (hc₂ : s subseteq ⋃ i, c i) : exists δ > 0, forall x in s, exists i, eball x δ subseteq c i := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma hs hc₁ hc₂

/--
theorem `lebesgue_number_lemma_of_emetric_nhds'` / 定理 `lebesgue_number_lemma_of_emetric_nhds'`

English:
theorem lebesgue_number_lemma_of_emetric_nhds'
  statement: {c : (x : α) -> x in s -> Set α} (hs : IsCompact s)
  proof: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds' hs hc

中文:
定理 lebesgue_number_lemma_of_emetric_nhds'
  结论: {c : (x : α) -> x in s -> 集合 α} (hs : 是紧集 s)
  证明: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds' hs hc

Depends on / 依赖: UniformSpace, UniformSpace.ball, edist_comm, lebesgue_number_lemma_nhds, preimage_ofPred_eq, uniformity_basis_edist, uniformity_basis_edist.lebesgue_number_lemma_nhds
-/
theorem lebesgue_number_lemma_of_emetric_nhds' {c : (x : α) -> x in s -> Set α} (hs : IsCompact s)
    (hc : forall x hx, c x hx in 𝓝 x) : exists δ > 0, forall x in s, exists y : s, eball x δ subseteq c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds' hs hc

/--
theorem `lebesgue_number_lemma_of_emetric_nhds` / 定理 `lebesgue_number_lemma_of_emetric_nhds`

English:
theorem lebesgue_number_lemma_of_emetric_nhds
  statement: {c : α -> Set α} (hs : IsCompact s)
  proof: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds hs hc

中文:
定理 lebesgue_number_lemma_of_emetric_nhds
  结论: {c : α -> 集合 α} (hs : 是紧集 s)
  证明: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds hs hc

Depends on / 依赖: UniformSpace, UniformSpace.ball, edist_comm, lebesgue_number_lemma_nhds, preimage_ofPred_eq, uniformity_basis_edist, uniformity_basis_edist.lebesgue_number_lemma_nhds
-/
theorem lebesgue_number_lemma_of_emetric_nhds {c : α -> Set α} (hs : IsCompact s)
    (hc : forall x in s, c x in 𝓝 x) : exists δ > 0, forall x in s, exists y, eball x δ subseteq c y := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds hs hc

/--
theorem `lebesgue_number_lemma_of_emetric_nhdsWithin'` / 定理 `lebesgue_number_lemma_of_emetric_nhdsWithin'`

English:
theorem lebesgue_number_lemma_of_emetric_nhdsWithin'
  statement: {c : (x : α) -> x in s -> Set α}
  proof: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin' hs hc

中文:
定理 lebesgue_number_lemma_of_emetric_nhdsWithin'
  结论: {c : (x : α) -> x in s -> 集合 α}
  证明: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin' hs hc

Depends on / 依赖: UniformSpace, UniformSpace.ball, edist_comm, lebesgue_number_lemma_nhdsWithin, preimage_ofPred_eq, uniformity_basis_edist, uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin
-/
theorem lebesgue_number_lemma_of_emetric_nhdsWithin' {c : (x : α) -> x in s -> Set α}
    (hs : IsCompact s) (hc : forall x hx, c x hx in 𝓝[s] x) :
    exists δ > 0, forall x in s, exists y : s, eball x δ inter s subseteq c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin' hs hc

/--
theorem `lebesgue_number_lemma_of_emetric_nhdsWithin` / 定理 `lebesgue_number_lemma_of_emetric_nhdsWithin`

English:
theorem lebesgue_number_lemma_of_emetric_nhdsWithin
  statement: {c : α -> Set α} (hs : IsCompact s)
  proof: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin hs hc

中文:
定理 lebesgue_number_lemma_of_emetric_nhdsWithin
  结论: {c : α -> 集合 α} (hs : 是紧集 s)
  证明: by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin hs hc

Depends on / 依赖: UniformSpace, UniformSpace.ball, edist_comm, lebesgue_number_lemma_nhdsWithin, preimage_ofPred_eq, uniformity_basis_edist, uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin
-/
theorem lebesgue_number_lemma_of_emetric_nhdsWithin {c : α -> Set α} (hs : IsCompact s)
    (hc : forall x in s, c x in 𝓝[s] x) : exists δ > 0, forall x in s, exists y, eball x δ inter s subseteq c y := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin hs hc

/--
theorem `lebesgue_number_lemma_of_emetric_sUnion` / 定理 `lebesgue_number_lemma_of_emetric_sUnion`

English:
theorem lebesgue_number_lemma_of_emetric_sUnion
  statement: {c : Set (Set α)} (hs : IsCompact s)
  proof: by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_emetric hs (by simpa) hc₂

中文:
定理 lebesgue_number_lemma_of_emetric_sUnion
  结论: {c : 集合 (集合 α)} (hs : 是紧集 s)
  证明: by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_emetric hs (by simpa) hc₂

Depends on / 依赖: lebesgue_number_lemma_of_emetric, sUnion_eq_iUnion
-/
theorem lebesgue_number_lemma_of_emetric_sUnion {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : forall t in c, IsOpen t) (hc₂ : s subseteq ⋃₀ c) : exists δ > 0, forall x in s, exists t in c, eball x δ subseteq t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_emetric hs (by simpa) hc₂

end LebesgueNumberLemma
