/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
## Pseudo-metric spaces

Further results about pseudo-metric spaces.

-/

public section

open Set Filter TopologicalSpace Bornology
open scoped ENNReal NNReal Uniformity Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

variable [PseudoMetricSpace α]

/--
theorem `dist_le_Ico_sum_dist` / 定理 `dist_le_Ico_sum_dist`

English:
theorem dist_le_Ico_sum_dist
  given: (f : Nat -> α) {m n} (h : m <= n)
  proof: by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) <= dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle]; rw [Finset.sum_insert]; rw [add_comm]; simp

中文:
定理 dist_le_Ico_sum_dist
  条件: (f : 自然数 -> α) {m n} (h : m <= n)
  证明: by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) <= dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle]; rw [Finset.sum_insert]; rw [add_comm]; simp

Depends on / 依赖: Finset, Finset.Ico, Finset.Ico_self, Finset.insert_Ico_right_eq_Ico_add_one, Finset.sum_empty, Finset.sum_insert, Ico_self, Nat.le_induction, add_comm, add_le_add, dist_self, dist_triangle, insert_Ico_right_eq_Ico_add_one, le_induction, le_rfl, sum_empty, sum_insert
-/
theorem dist_le_Ico_sum_dist (f : Nat -> α) {m n} (h : m <= n) :
    dist (f m) (f n) <= ∑ i in Finset.Ico m n, dist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) <= dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ <= (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle]; rw [Finset.sum_insert]; rw [add_comm]; simp

/--
theorem `dist_le_range_sum_dist` / 定理 `dist_le_range_sum_dist`

English:
theorem dist_le_range_sum_dist
  given: (f : Nat -> α) (n : Nat)
  proof: Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

中文:
定理 dist_le_range_sum_dist
  条件: (f : 自然数 -> α) (n : 自然数)
  证明: Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, Nat.zero_le, dist_le_Ico_sum_dist, zero_le
-/
theorem dist_le_range_sum_dist (f : Nat -> α) (n : Nat) :
    dist (f 0) (f n) <= ∑ i in Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

/--
theorem `dist_le_Ico_sum_of_dist_le` / 定理 `dist_le_Ico_sum_of_dist_le`

English:
theorem dist_le_Ico_sum_of_dist_le
  statement: {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat -> Real}
  proof: le_trans (dist_le_Ico_sum_dist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

中文:
定理 dist_le_Ico_sum_of_dist_le
  结论: {f : 自然数 -> α} {m n} (hmn : m <= n) {d : 自然数 -> 实数}
  证明: le_trans (dist_le_Ico_sum_dist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.sum_le_sum, dist_le_Ico_sum_dist, le_trans, mem_Ico, sum_le_sum
-/
theorem dist_le_Ico_sum_of_dist_le {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat -> Real}
    (hd : forall {k}, m <= k -> k < n -> dist (f k) (f (k + 1)) <= d k) :
    dist (f m) (f n) <= ∑ i in Finset.Ico m n, d i :=
le_trans (dist_le_Ico_sum_dist f hmn)
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/--
theorem `dist_le_range_sum_of_dist_le` / 定理 `dist_le_range_sum_of_dist_le`

English:
theorem dist_le_range_sum_of_dist_le
  statement: {f : Nat -> α} (n : Nat) {d : Nat -> Real}
  proof: Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_of_dist_le zero_le fun _ => hd

中文:
定理 dist_le_range_sum_of_dist_le
  结论: {f : 自然数 -> α} (n : 自然数) {d : 自然数 -> 实数}
  证明: Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_of_dist_le zero_le fun _ => hd

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, dist_le_Ico_sum_of_dist_le, zero_le
-/
theorem dist_le_range_sum_of_dist_le {f : Nat -> α} (n : Nat) {d : Nat -> Real}
    (hd : forall {k}, k < n -> dist (f k) (f (k + 1)) <= d k) :
    dist (f 0) (f n) <= ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_of_dist_le zero_le fun _ => hd

namespace Metric

-- instantiate pseudometric space as a topology

nonrec theorem isUniformInducing_iff [PseudoMetricSpace β] {f : α -> β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, dist (f a) (f b) < ε -> dist a b < δ :=
isUniformInducing_iff'.trans Iff.rfl.and
((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_ofPred_eq, Prod.map_apply, mem_ofPred]

nonrec theorem isUniformEmbedding_iff [PseudoMetricSpace β] {f : α -> β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, dist (f a) (f b) < ε -> dist a b < δ := by
  rw [isUniformEmbedding_iff]; rw [and_comm]; rw [isUniformInducing_iff]

/--
theorem `controlled_of_isUniformInducing` / 定理 `controlled_of_isUniformInducing`

English:
theorem controlled_of_isUniformInducing
  statement: [PseudoMetricSpace β] {f : α -> β}
  proof: ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]

中文:
定理 controlled_of_isUniformInducing
  结论: [伪度量空间 β] {f : α -> β}
  证明: ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]

Depends on / 依赖: h.uniformContinuous, isUniformInducing_iff, uniformContinuous, uniformContinuous_iff
-/
theorem controlled_of_isUniformInducing [PseudoMetricSpace β] {f : α -> β}
    (h : IsUniformInducing f) :
    (forall ε > 0, exists δ > 0, forall {a b : α}, dist a b < δ -> dist (f a) (f b) < ε) ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, dist (f a) (f b) < ε -> dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]
/--
theorem `controlled_of_isUniformEmbedding` / 定理 `controlled_of_isUniformEmbedding`

English:
theorem controlled_of_isUniformEmbedding
  statement: [PseudoMetricSpace β] {f : α -> β}
  proof: controlled_of_isUniformInducing h.toIsUniformInducing

中文:
定理 controlled_of_isUniformEmbedding
  结论: [伪度量空间 β] {f : α -> β}
  证明: controlled_of_isUniformInducing h.toIsUniformInducing

Depends on / 依赖: controlled_of_isUniformInducing, h.toIsUniformInducing, toIsUniformInducing
-/
theorem controlled_of_isUniformEmbedding [PseudoMetricSpace β] {f : α -> β}
    (h : IsUniformEmbedding f) :
    (forall ε > 0, exists δ > 0, forall {a b : α}, dist a b < δ -> dist (f a) (f b) < ε) ∧
      forall δ > 0, exists ε > 0, forall {a b : α}, dist (f a) (f b) < ε -> dist a b < δ :=
  controlled_of_isUniformInducing h.toIsUniformInducing

/--
theorem `totallyBounded_iff` / 定理 `totallyBounded_iff`

English:
theorem totallyBounded_iff
  given: {s : Set α}
  proof: uniformity_basis_dist.totallyBounded_iff

中文:
定理 totallyBounded_iff
  条件: {s : 集合 α}
  证明: uniformity_basis_dist.totallyBounded_iff

Depends on / 依赖: totallyBounded_iff, uniformity_basis_dist, uniformity_basis_dist.totallyBounded_iff
-/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ forall ε > 0, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, ball y ε :=
  uniformity_basis_dist.totallyBounded_iff

/--
theorem `totallyBounded_of_finite_discretization` / 定理 `totallyBounded_of_finite_discretization`

English:
theorem totallyBounded_of_finite_discretization
  statement: {s : Set α}
  proof: by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  have : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine totallyBounded_iff.2 fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => ?_⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩

中文:
定理 totallyBounded_of_finite_discretization
  结论: {s : 集合 α}
  证明: by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  have : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine totallyBounded_iff.2 fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => ?_⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩

Depends on / 依赖: Function, Function.invFun, Function.invFun_eq, Inhabited, Set.mem_iUnion, Set.mem_range, Subtype, Subtype.val, eq_empty_or_nonempty, finite_range, invFun, invFun_eq, mem_iUnion, mem_range, s.eq_empty_or_nonempty, this.symm, totallyBounded_empty, totallyBounded_iff
-/
theorem totallyBounded_of_finite_discretization {s : Set α}
    (H : forall ε > (0 : Real),
        exists (β : Type u) (_ : Fintype β) (F : s -> β), forall x y, F x = F y -> dist (x : α) y < ε) :
    TotallyBounded s := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  have : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine totallyBounded_iff.2 fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => ?_⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩

/--
theorem `finite_approx_of_totallyBounded` / 定理 `finite_approx_of_totallyBounded`

English:
theorem finite_approx_of_totallyBounded
  given: {s : Set α} (hs : TotallyBounded s)
  proof: by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)

中文:
定理 finite_approx_of_totallyBounded
  条件: {s : 集合 α} (hs : 全有界 s)
  证明: by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)

Depends on / 依赖: dist_mem_uniformity, totallyBounded_iff_subset
-/
theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    forall ε > 0, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, ball y ε := by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)

/--
theorem `tendstoUniformlyOnFilter_iff` / 定理 `tendstoUniformlyOnFilter_iff`

English:
theorem tendstoUniformlyOnFilter_iff
  given: {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {p' : Filter β}
  proof: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

中文:
定理 tendstoUniformlyOnFilter_iff
  条件: {F : ι -> β -> α} {f : β -> α} {p : 滤子 ι} {p' : 滤子 β}
  证明: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

Depends on / 依赖: dist_mem_uniformity, mem_uniformity_dist
-/
theorem tendstoUniformlyOnFilter_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      forall ε > 0, forallᶠ n : ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

/--
theorem `tendstoLocallyUniformlyOn_iff` / 定理 `tendstoLocallyUniformlyOn_iff`

English:
theorem tendstoLocallyUniformlyOn_iff
  statement: [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
  proof: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

中文:
定理 tendstoLocallyUniformlyOn_iff
  结论: [拓扑空间 β] {F : ι -> β -> α} {f : β -> α}
  证明: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

Depends on / 依赖: Ht.mono, dist_mem_uniformity, mem_uniformity_dist
-/
theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      forall ε > 0, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, dist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/--
theorem `tendstoUniformlyOn_iff` / 定理 `tendstoUniformlyOn_iff`

English:
theorem tendstoUniformlyOn_iff
  given: {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β}
  proof: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

中文:
定理 tendstoUniformlyOn_iff
  条件: {F : ι -> β -> α} {f : β -> α} {p : 滤子 ι} {s : 集合 β}
  证明: by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

Depends on / 依赖: dist_mem_uniformity, mem_uniformity_dist
-/
theorem tendstoUniformlyOn_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ forall ε > 0, forallᶠ n in p, forall x in s, dist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/--
theorem `tendstoLocallyUniformly_iff` / 定理 `tendstoLocallyUniformly_iff`

English:
theorem tendstoLocallyUniformly_iff
  statement: [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
  proof: by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const]

中文:
定理 tendstoLocallyUniformly_iff
  结论: [拓扑空间 β] {F : ι -> β -> α} {f : β -> α}
  证明: by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const]

Depends on / 依赖: forall_const, mem_univ, nhdsWithin_univ, tendstoLocallyUniformlyOn_iff, tendstoLocallyUniformlyOn_univ
-/
theorem tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι -> β -> α} {f : β -> α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      forall ε > 0, forall x : β, exists t in 𝓝 x, forallᶠ n in p, forall y in t, dist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const]

/--
theorem `tendstoUniformly_iff` / 定理 `tendstoUniformly_iff`

English:
theorem tendstoUniformly_iff
  given: {F : ι -> β -> α} {f : β -> α} {p : Filter ι}
  proof: by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff]
  simp

中文:
定理 tendstoUniformly_iff
  条件: {F : ι -> β -> α} {f : β -> α} {p : 滤子 ι}
  证明: by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff]
  simp

Depends on / 依赖: tendstoUniformlyOn_iff, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_iff {F : ι -> β -> α} {f : β -> α} {p : Filter ι} :
    TendstoUniformly F f p ↔ forall ε > 0, forallᶠ n in p, forall x, dist (f x) (F n x) < ε := by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff]
  simp

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {f : Filter α}
  proof: uniformity_basis_dist.cauchy_iff

中文:
定理 cauchy_iff
  条件: {f : 滤子 α}
  证明: uniformity_basis_dist.cauchy_iff
-/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ forall ε > 0, exists t in f, forall x in t, forall y in t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

variable {s : Set α}

/--
theorem `exists_ball_inter_eq_singleton_of_mem_discrete` / 定理 `exists_ball_inter_eq_singleton_of_mem_discrete`

English:
theorem exists_ball_inter_eq_singleton_of_mem_discrete
  given: (hs : IsDiscrete s) {x : α} (hx : x in s)
  proof: nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hs hx

中文:
定理 存在_ball_inter_eq_singleton_of_mem_discrete
  条件: (hs : 是离散 s) {x : α} (hx : x in s)
  证明: nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hs hx

Depends on / 依赖: exists_inter_eq_singleton_of_mem_discrete, nhds_basis_ball, nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete
-/
theorem exists_ball_inter_eq_singleton_of_mem_discrete (hs : IsDiscrete s) {x : α} (hx : x in s) :
    exists ε > 0, Metric.ball x ε inter s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hs hx

/--
theorem `exists_closedBall_inter_eq_singleton_of_discrete` / 定理 `exists_closedBall_inter_eq_singleton_of_discrete`

English:
theorem exists_closedBall_inter_eq_singleton_of_discrete
  given: (hs : IsDiscrete s) {x : α} (hx : x in s)
  proof: nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hs hx

中文:
定理 存在_closedBall_inter_eq_singleton_of_discrete
  条件: (hs : 是离散 s) {x : α} (hx : x in s)
  证明: nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hs hx

Depends on / 依赖: exists_inter_eq_singleton_of_mem_discrete, nhds_basis_closedBall, nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete
-/
theorem exists_closedBall_inter_eq_singleton_of_discrete (hs : IsDiscrete s) {x : α} (hx : x in s) :
    exists ε > 0, Metric.closedBall x ε inter s = {x} :=
  nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hs hx

end Metric

open Metric

/--
theorem `Metric.inseparable_iff_nndist` / 定理 `Metric.inseparable_iff_nndist`

English:
theorem Metric.inseparable_iff_nndist
  given: {x y : α}
  statement: Inseparable x y ↔ nndist x y = 0
  proof: by
  rw [EMetric.inseparable_iff]; rw [edist_nndist]; rw [ENNReal.coe_eq_zero]

alias ⟨Inseparable.nndist_eq_zero, _⟩ := Metric.inseparable_iff_nndist

中文:
定理 Metric.inseparable_iff_nndist
  条件: {x y : α}
  结论: 不可分 x y ↔ nndist x y = 0
  证明: by
  rw [EMetric.inseparable_iff]; rw [edist_nndist]; rw [ENNReal.coe_eq_zero]

alias ⟨Inseparable.nndist_eq_zero, _⟩ := Metric.inseparable_iff_nndist

Depends on / 依赖: EMetric, EMetric.inseparable_iff, ENNReal, ENNReal.coe_eq_zero, coe_eq_zero, edist_nndist, inseparable_iff
-/
theorem Metric.inseparable_iff_nndist {x y : α} : Inseparable x y ↔ nndist x y = 0 := by
  rw [EMetric.inseparable_iff]; rw [edist_nndist]; rw [ENNReal.coe_eq_zero]

alias ⟨Inseparable.nndist_eq_zero, _⟩ := Metric.inseparable_iff_nndist

/--
theorem `Metric.inseparable_iff` / 定理 `Metric.inseparable_iff`

English:
theorem Metric.inseparable_iff
  given: {x y : α}
  statement: Inseparable x y ↔ dist x y = 0
  proof: by
  rw [Metric.inseparable_iff_nndist]; rw [dist_nndist]; rw [NNReal.coe_eq_zero]

alias ⟨Inseparable.dist_eq_zero, _⟩ := Metric.inseparable_iff

中文:
定理 Metric.inseparable_iff
  条件: {x y : α}
  结论: 不可分 x y ↔ dist x y = 0
  证明: by
  rw [Metric.inseparable_iff_nndist]; rw [dist_nndist]; rw [NNReal.coe_eq_zero]

alias ⟨Inseparable.dist_eq_zero, _⟩ := Metric.inseparable_iff

Depends on / 依赖: Metric, Metric.inseparable_iff_nndist, NNReal, NNReal.coe_eq_zero, coe_eq_zero, dist_nndist, inseparable_iff_nndist
-/
theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by
  rw [Metric.inseparable_iff_nndist]; rw [dist_nndist]; rw [NNReal.coe_eq_zero]

alias ⟨Inseparable.dist_eq_zero, _⟩ := Metric.inseparable_iff

/--
theorem `tendsto_nhds_unique_dist` / 定理 `tendsto_nhds_unique_dist`

English:
theorem tendsto_nhds_unique_dist
  statement: {f : β -> α} {l : Filter β} {x y : α} [NeBot l]
  proof: (tendsto_nhds_unique_inseparable ha hb).dist_eq_zero

中文:
定理 tendsto_nhds_unique_dist
  结论: {f : β -> α} {l : 滤子 β} {x y : α} [NeBot l]
  证明: (tendsto_nhds_unique_inseparable ha hb).dist_eq_zero

Depends on / 依赖: dist_eq_zero, tendsto_nhds_unique_inseparable
-/
theorem tendsto_nhds_unique_dist {f : β -> α} {l : Filter β} {x y : α} [NeBot l]
    (ha : Tendsto f l (𝓝 x)) (hb : Tendsto f l (𝓝 y)) : dist x y = 0 :=
  (tendsto_nhds_unique_inseparable ha hb).dist_eq_zero

section Real

/--
theorem `cauchySeq_iff_tendsto_dist_atTop_0` / 定理 `cauchySeq_iff_tendsto_dist_atTop_0`

English:
theorem cauchySeq_iff_tendsto_dist_atTop_0
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α}
  proof: by
  rw [cauchySeq_iff_tendsto]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]
  simp_rw [Prod.map_fst, Prod.map_snd]

中文:
定理 cauchySeq_iff_tendsto_dist_atTop_0
  条件: [非空 β] [SemilatticeSup β] {u : β -> α}
  证明: by
  rw [cauchySeq_iff_tendsto]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]
  simp_rw [Prod.map_fst, Prod.map_snd]

Depends on / 依赖: Function, Function.comp_def, Metric, Metric.uniformity_eq_comap_nhds_zero, Prod.map_fst, Prod.map_snd, cauchySeq_iff_tendsto, comp_def, map_fst, map_snd, simp_rw, tendsto_comap_iff, uniformity_eq_comap_nhds_zero
-/
theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β -> α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]
  simp_rw [Prod.map_fst, Prod.map_snd]

end Real

namespace Topology

/--
lemma `IsInducing.isSeparable_preimage` / 引理 `IsInducing.isSeparable_preimage`

English:
lemma IsInducing.isSeparable_preimage
  statement: {α : Type*} [TopologicalSpace α]
  proof: by
  let : UniformSpace α := TopologicalSpace.pseudoMetrizableSpaceUniformity α
  have := pseudoMetrizableSpaceUniformity_countably_generated
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _

中文:
引理 是Inducing.isSeparable_preimage
  结论: {α : 类型} [拓扑空间 α]
  证明: by
  let : UniformSpace α := TopologicalSpace.pseudoMetrizableSpaceUniformity α
  have := pseudoMetrizableSpaceUniformity_countably_generated
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _
-/
protected lemma IsInducing.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β -> α} [TopologicalSpace β]
    (hf : IsInducing f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) := by
  let : UniformSpace α := TopologicalSpace.pseudoMetrizableSpaceUniformity α
  have := pseudoMetrizableSpaceUniformity_countably_generated
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _

/--
theorem `IsEmbedding.isSeparable_preimage` / 定理 `IsEmbedding.isSeparable_preimage`

English:
theorem IsEmbedding.isSeparable_preimage
  statement: {α : Type*} [TopologicalSpace α]
  proof: hf.isInducing.isSeparable_preimage hs

中文:
定理 是嵌入.isSeparable_preimage
  结论: {α : 类型} [拓扑空间 α]
  证明: hf.isInducing.isSeparable_preimage hs
-/
protected theorem IsEmbedding.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β -> α} [TopologicalSpace β]
    (hf : IsEmbedding f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.isInducing.isSeparable_preimage hs

end Topology

/--
theorem `IsCompact.isSeparable` / 定理 `IsCompact.isSeparable`

English:
theorem IsCompact.isSeparable
  statement: {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
  proof: haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

中文:
定理 是紧集.isSeparable
  结论: {α : 类型} [拓扑空间 α] [PseudoMetrizable空间 α]
  证明: haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

Depends on / 依赖: CompactSpace, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, of_subtype
-/
theorem IsCompact.isSeparable {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

namespace Metric

section SecondCountable

open TopologicalSpace

/--
theorem `secondCountable_of_almost_dense_set` / 定理 `secondCountable_of_almost_dense_set`

English:
theorem secondCountable_of_almost_dense_set
  proof: by
  refine EMetric.secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans ?_ ε'ε.le⟩⟩
  exact mod_cast hyx x

中文:
定理 secondCountable_of_almost_dense_set
  证明: by
  refine EMetric.secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans ?_ ε'ε.le⟩⟩
  exact mod_cast hyx x

Depends on / 依赖: EMetric, EMetric.secondCountable_of_almost_dense_set, ENNReal, ENNReal.lt_iff_exists_nnreal_btwn, le_trans, lt_iff_exists_nnreal_btwn, mod_cast, secondCountable_of_almost_dense_set
-/
theorem secondCountable_of_almost_dense_set
    (H : forall ε > (0 : Real), exists s : Set α, s.Countable ∧ forall x, exists y in s, dist x y <= ε) :
    SecondCountableTopology α := by
  refine EMetric.secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans ?_ ε'ε.le⟩⟩
  exact mod_cast hyx x

end SecondCountable

end Metric

section Compact
variable {X : Type*} [PseudoMetricSpace X] {s : Set X} {ε : Real}

/--
theorem `finite_cover_balls_of_compact` / 定理 `finite_cover_balls_of_compact`

English:
theorem finite_cover_balls_of_compact
  given: (hs : IsCompact s) {e : Real} (he : 0 < e)
  proof: let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact

中文:
定理 finite_cover_balls_of_compact
  条件: (hs : 是紧集 s) {e : 实数} (he : 0 < e)
  证明: let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact

Depends on / 依赖: ball_mem_nhds, elim_nhds_subcover, finite_toSet, hs.elim_nhds_subcover, t.finite_toSet
-/
theorem finite_cover_balls_of_compact (hs : IsCompact s) {e : Real} (he : 0 < e) :
    exists t subseteq s, t.Finite ∧ s subseteq ⋃ x in t, ball x e :=
  let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact

/--
lemma `exists_finite_cover_balls_of_isCompact_closure` / 引理 `exists_finite_cover_balls_of_isCompact_closure`

English:
lemma exists_finite_cover_balls_of_isCompact_closure
  given: (hs : IsCompact (closure s)) (hε : 0 < ε)
  proof: by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s => ball x ε) (fun _ => isOpen_ball) fun x hx =>
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst

中文:
引理 存在_finite_cover_balls_of_isCompact_closure
  条件: (hs : 是紧集 (closure s)) (hε : 0 < ε)
  证明: by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s => ball x ε) (fun _ => isOpen_ball) fun x hx =>
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst

Depends on / 依赖: Finset, Finset.finite_toSet, Metric, Metric.mem_closure_iff, Subtype, Subtype.val, Subtype.val_injective, elim_finite_subcover, finite_toSet, hs.elim_finite_subcover, isOpen_ball, mem_closure_iff, mem_iUnion, subset_closure, subset_closure.trans, t.map, val_injective
-/
lemma exists_finite_cover_balls_of_isCompact_closure (hs : IsCompact (closure s)) (hε : 0 < ε) :
    exists t subseteq s, t.Finite ∧ s subseteq ⋃ x in t, ball x ε := by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s => ball x ε) (fun _ => isOpen_ball) fun x hx =>
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst

end Compact

/--
theorem `ContinuousOn.isSeparable_image` / 定理 `ContinuousOn.isSeparable_image`

English:
theorem ContinuousOn.isSeparable_image
  statement: {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
  proof: by
  rw [image_eq_range]; rw [← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.domRestrict

中文:
定理 ContinuousOn.isSeparable_image
  结论: {α : 类型} [拓扑空间 α] [PseudoMetrizable空间 α]
  证明: by
  rw [image_eq_range]; rw [← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.domRestrict

Depends on / 依赖: domRestrict, hf.domRestrict, hs.separableSpace, image_eq_range, image_univ, isSeparable_univ_iff, separableSpace
-/
theorem ContinuousOn.isSeparable_image {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    [TopologicalSpace β] {f : α -> β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) := by
  rw [image_eq_range]; rw [← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.domRestrict
