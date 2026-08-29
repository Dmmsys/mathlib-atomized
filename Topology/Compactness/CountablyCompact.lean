/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek, Yongxi Lin
-/
module

public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Sequences

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Perfect

/-!
# Countably compact sets

A set `A` in a topological space is **countably compact** if every countably generated proper
filter contained in `A` has a cluster point in `A`. Equivalently, every sequence in `A` has a
cluster point in `A`, and every countable open cover of `A` admits a finite subcover.

## Main definitions

* `IsCountablyCompact A`: `A` is countably compact (every countably generated proper filter
  contained in `A` has a cluster point in `A`).
* `CountablyCompactSpace E`: the whole space `E` is countably compact.

## Main results

* `IsCountablyCompact.elim_directed_cover`: for every countable open directed cover of a
  countably compact set, some single element of the cover contains the set.
* `IsCountablyCompact.elim_finite_subcover`: a countably compact set has a finite subcover for
  any countable open cover.
* `isCountablyCompact_iff_countable_open_cover`: countable compactness is equivalent to the
  finite subcover property for countable covers.
* `IsCompact.isCountablyCompact`: compact sets are countably compact.
* `IsSeqCompact.isCountablyCompact`: sequentially compact sets are countably compact.
* `IsCountablyCompact.isSeqCompact`: in a first-countable space, countable compactness implies
  sequential compactness.
* `IsCountablyCompact.exists_accPt_of_infinite`: every infinite subset of a countably compact
  set has an accumulation point in the set.
* `isCountablyCompact_iff_infinite_subset_has_accPt`: in a T₁ space, countable compactness is
  equivalent to the Bolzano–Weierstrass property (every infinite subset has an accumulation point).
* `IsLindelof.isCompact`: a countably compact Lindelöf set is compact.
* `IsCountablyCompact.image`: the continuous image of a countably compact set is countably compact.

## References

* [Engelking, *General Topology*][engelking1989]
-/

@[expose] public section

noncomputable section

open Set Filter Topology

variable {ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {A B : Set E}

/--
Definition of `IsCountablyCompact` / `IsCountablyCompact` 的定义

English:
definition IsCountablyCompact
  signature: (A : Set E)
  body: forall ⦃f⦄ [NeBot f] [f.IsCountablyGenerated], f <= 𝓟 A -> exists a in A, ClusterPt a f

中文:
定义 IsCountablyCompact
  签名: (A : Set E)
  定义体: forall ⦃f⦄ [NeBot f] [f.IsCountablyGenerated], f <= 𝓟 A -> exists a in A, ClusterPt a f

Depends on / 依赖: ClusterPt, IsCountablyGenerated, f.IsCountablyGenerated
-/
def IsCountablyCompact (A : Set E) : Prop :=
  forall ⦃f⦄ [NeBot f] [f.IsCountablyGenerated], f <= 𝓟 A -> exists a in A, ClusterPt a f

/--
Definition of `CountablyCompactSpace` / `CountablyCompactSpace` 的定义

English:
class CountablyCompactSpace
  parameters: (E : Type*) [TopologicalSpace E]
  axioms and operations (1):
    - isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)

中文:
类 CountablyCompactSpace
  参数: (E : 类型) [TopologicalSpace E]
  公理与运算 (1 个):
    - isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)
-/
class CountablyCompactSpace (E : Type*) [TopologicalSpace E] : Prop where
  isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)

/--
theorem `isCountablyCompact_empty` / 定理 `isCountablyCompact_empty`

English:
theorem isCountablyCompact_empty
  statement: IsCountablyCompact (∅ : Set E)
  proof: fun _f _ _ hle => absurd (empty_mem_iff_bot.mp (le_principal_iff.mp hle)) NeBot.ne'

中文:
定理 isCountablyCompact_empty
  结论: IsCountablyCompact (∅ : Set E)
  证明: fun _f _ _ hle => absurd (empty_mem_iff_bot.mp (le_principal_iff.mp hle)) NeBot.ne'

Depends on / 依赖: NeBot.ne, absurd, empty_mem_iff_bot, empty_mem_iff_bot.mp, le_principal_iff, le_principal_iff.mp
-/
theorem isCountablyCompact_empty : IsCountablyCompact (∅ : Set E) :=
  fun _f _ _ hle => absurd (empty_mem_iff_bot.mp (le_principal_iff.mp hle)) NeBot.ne'

/--
theorem `isCountablyCompact_singleton` / 定理 `isCountablyCompact_singleton`

English:
theorem isCountablyCompact_singleton
  given: {x : E}
  statement: IsCountablyCompact ({x} : Set E)
  proof: fun _ _ _ hle =>
⟨x, rfl, ClusterPt.of_le_nhds hle.trans (principal_singleton x ▸ pure_le_nhds x)⟩

中文:
定理 isCountablyCompact_singleton
  条件: {x : E}
  结论: IsCountablyCompact ({x} : Set E)
  证明: fun _ _ _ hle =>
⟨x, rfl, ClusterPt.of_le_nhds hle.trans (principal_singleton x ▸ pure_le_nhds x)⟩
-/
theorem isCountablyCompact_singleton {x : E} : IsCountablyCompact ({x} : Set E) := fun _ _ _ hle =>
⟨x, rfl, ClusterPt.of_le_nhds hle.trans (principal_singleton x ▸ pure_le_nhds x)⟩

/--
theorem `IsCountablyCompact.of_isClosed_subset` / 定理 `IsCountablyCompact.of_isClosed_subset`

English:
theorem IsCountablyCompact.of_isClosed_subset
  statement: (hA : IsCountablyCompact A) (hB : IsClosed B)
  proof: fun _f _ _ hle =>
  let ⟨a, _, hac⟩ := hA (hle.trans (principal_mono.mpr hBA))
  ⟨a, isClosed_iff_clusterPt.mp hB a (hac.mono hle), hac⟩

中文:
定理 IsCountablyCompact.of_isClosed_subset
  结论: (hA : IsCountablyCompact A) (hB : IsClosed B)
  证明: fun _f _ _ hle =>
  let ⟨a, _, hac⟩ := hA (hle.trans (principal_mono.mpr hBA))
  ⟨a, isClosed_iff_clusterPt.mp hB a (hac.mono hle), hac⟩
-/
theorem IsCountablyCompact.of_isClosed_subset (hA : IsCountablyCompact A) (hB : IsClosed B)
    (hBA : B subseteq A) : IsCountablyCompact B := fun _f _ _ hle =>
  let ⟨a, _, hac⟩ := hA (hle.trans (principal_mono.mpr hBA))
  ⟨a, isClosed_iff_clusterPt.mp hB a (hac.mono hle), hac⟩

/--
theorem `IsClosed.isCountablyCompact` / 定理 `IsClosed.isCountablyCompact`

English:
theorem IsClosed.isCountablyCompact
  given: [CountablyCompactSpace E] (hA : IsClosed A)
  proof: CountablyCompactSpace.isCountablyCompact_univ.of_isClosed_subset hA (subset_univ _)

中文:
定理 IsClosed.isCountablyCompact
  条件: [CountablyCompactSpace E] (hA : IsClosed A)
  证明: CountablyCompactSpace.isCountablyCompact_univ.of_isClosed_subset hA (subset_univ _)

Depends on / 依赖: CountablyCompactSpace, CountablyCompactSpace.isCountablyCompact_univ.of_isClosed_subset, isCountablyCompact_univ, of_isClosed_subset, subset_univ
-/
theorem IsClosed.isCountablyCompact [CountablyCompactSpace E] (hA : IsClosed A) :
    IsCountablyCompact A :=
  CountablyCompactSpace.isCountablyCompact_univ.of_isClosed_subset hA (subset_univ _)

/--
theorem `isCountablyCompact_iff_seq_clusterPt` / 定理 `isCountablyCompact_iff_seq_clusterPt`

English:
theorem isCountablyCompact_iff_seq_clusterPt
  proof: h (tendsto_principal.mpr hx)
  mpr hA f _ _ hle := by
    obtain ⟨x, hx⟩ := f.exists_seq_tendsto
    obtain ⟨a, ha, hxa⟩ := hA x (by simpa using hx.mono_right hle)
    exact ⟨a, ha, hxa.clusterPt.mono hx⟩

alias ⟨IsCountablyCompact.seq_clusterPt,
  IsCountablyCompact.of_seq_clusterPt⟩ := isCountably

中文:
定理 isCountablyCompact_iff_seq_clusterPt
  证明: h (tendsto_principal.mpr hx)
  mpr hA f _ _ hle := by
    obtain ⟨x, hx⟩ := f.exists_seq_tendsto
    obtain ⟨a, ha, hxa⟩ := hA x (by simpa using hx.mono_right hle)
    exact ⟨a, ha, hxa.clusterPt.mono hx⟩

alias ⟨IsCountablyCompact.seq_clusterPt,
  IsCountablyCompact.of_seq_clusterPt⟩ := isCountably

Depends on / 依赖: tendsto_principal, tendsto_principal.mpr
-/
theorem isCountablyCompact_iff_seq_clusterPt :
    IsCountablyCompact A ↔
      forall x : Nat -> E, (forallᶠ n in atTop, x n in A) -> exists a in A, MapClusterPt a atTop x where
  mp h x hx := h (tendsto_principal.mpr hx)
  mpr hA f _ _ hle := by
    obtain ⟨x, hx⟩ := f.exists_seq_tendsto
    obtain ⟨a, ha, hxa⟩ := hA x (by simpa using hx.mono_right hle)
    exact ⟨a, ha, hxa.clusterPt.mono hx⟩

alias ⟨IsCountablyCompact.seq_clusterPt,
  IsCountablyCompact.of_seq_clusterPt⟩ := isCountablyCompact_iff_seq_clusterPt

/--
theorem `IsCountablyCompact.elim_directed_cover` / 定理 `IsCountablyCompact.elim_directed_cover`

English:
theorem IsCountablyCompact.elim_directed_cover
  statement: [Countable ι] [Nonempty ι]
  proof: by
  by_contra! h
  have hdir : Directed (· >= ·) fun i => 𝓟 (A \ U i) :=
fun i j => (hdU i j).imp fun _ ⟨hi, hj⟩ => ⟨principal_mono.mpr sdiff_subset_sdiff_right hi,
principal_mono.mpr sdiff_subset_sdiff_right hj⟩
  have : NeBot (⨅ i, 𝓟 (A \ U i)) :=
    iInf_neBot_of_directed' hdir fun i => (sdiff_

中文:
定理 IsCountablyCompact.elim_directed_cover
  结论: [Countable ι] [Nonempty ι]
  证明: by
  by_contra! h
  have hdir : Directed (· >= ·) fun i => 𝓟 (A \ U i) :=
fun i j => (hdU i j).imp fun _ ⟨hi, hj⟩ => ⟨principal_mono.mpr sdiff_subset_sdiff_right hi,
principal_mono.mpr sdiff_subset_sdiff_right hj⟩
  have : NeBot (⨅ i, 𝓟 (A \ U i)) :=
    iInf_neBot_of_directed' hdir fun i => (sdiff_

Depends on / 依赖: Directed, Nonempty, iInf_le_of_le, iInf_neBot_of_directed, mem_iUnion, mem_iUnion.mp, principal_mono, principal_mono.mpr, principal_neBot, sdiff_nonempty, sdiff_nonempty.mpr, sdiff_subset, sdiff_subset_sdiff_right
-/
theorem IsCountablyCompact.elim_directed_cover [Countable ι] [Nonempty ι]
    (hA : IsCountablyCompact A) (U : ι -> Set E) (hUo : forall i, IsOpen (U i))
    (hAU : A subseteq ⋃ i, U i) (hdU : Directed (· subseteq ·) U) : exists i, A subseteq U i := by
  by_contra! h
  have hdir : Directed (· >= ·) fun i => 𝓟 (A \ U i) :=
fun i j => (hdU i j).imp fun _ ⟨hi, hj⟩ => ⟨principal_mono.mpr sdiff_subset_sdiff_right hi,
principal_mono.mpr sdiff_subset_sdiff_right hj⟩
  have : NeBot (⨅ i, 𝓟 (A \ U i)) :=
    iInf_neBot_of_directed' hdir fun i => (sdiff_nonempty.mpr (h i)).principal_neBot
  have hle : (⨅ i, 𝓟 (A \ U i)) <= 𝓟 A :=
iInf_le_of_le ‹Nonempty ι›.some principal_mono.mpr sdiff_subset
  rcases hA hle with ⟨a, ha, hac⟩
  rcases mem_iUnion.mp (hAU ha) with ⟨k, hk⟩
  exact closure_minimal (fun _ hx => hx.2) (hUo k).isClosed_compl
    (hac.mono (iInf_le _ k)).mem_closure hk

/--
theorem `IsCountablyCompact.elim_finite_subcover` / 定理 `IsCountablyCompact.elim_finite_subcover`

English:
theorem IsCountablyCompact.elim_finite_subcover
  statement: (hA : IsCountablyCompact A) [Countable ι]
  proof: hA.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hAU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

中文:
定理 IsCountablyCompact.elim_finite_subcover
  结论: (hA : IsCountablyCompact A) [Countable ι]
  证明: hA.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hAU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

Depends on / 依赖: biUnion_subset_biUnion_left, directed_of_isDirected_le, elim_directed_cover, hA.elim_directed_cover, iUnion_eq_iUnion_finset, isOpen_biUnion
-/
theorem IsCountablyCompact.elim_finite_subcover (hA : IsCountablyCompact A) [Countable ι]
    {U : ι -> Set E} (hUo : forall i, IsOpen (U i)) (hAU : A subseteq ⋃ i, U i) :
    exists t : Finset ι, A subseteq ⋃ i in t, U i :=
  hA.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hAU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

/--
theorem `isCountablyCompact_iff_countable_open_cover` / 定理 `isCountablyCompact_iff_countable_open_cover`

English:
theorem isCountablyCompact_iff_countable_open_cover
  proof: hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    by_contra! hac
    let V : Nat -> Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
compl_subset_compl.2 closure_mono image_mono Ici_subset_Ici.2 hmn

中文:
定理 isCountablyCompact_iff_countable_open_cover
  证明: hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    by_contra! hac
    let V : Nat -> Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
compl_subset_compl.2 closure_mono image_mono Ici_subset_Ici.2 hmn

Depends on / 依赖: elim_finite_subcover, hA.elim_finite_subcover
-/
theorem isCountablyCompact_iff_countable_open_cover :
    IsCountablyCompact A ↔ forall (U : Nat -> Set E), (forall i, IsOpen (U i)) -> A subseteq ⋃ i, U i ->
        exists t : Finset Nat, A subseteq ⋃ i in t, U i where
  mp hA _ hUo hAU := hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    by_contra! hac
    let V : Nat -> Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
compl_subset_compl.2 closure_mono image_mono Ici_subset_Ici.2 hmn
    simp only [mapClusterPt_atTop_iff_forall_mem_closure, not_forall] at hac
    have hAV : A subseteq ⋃ n, V n := fun a haA => mem_iUnion.2 (hac a haA)
    obtain ⟨t, ht⟩ := h V (fun _ => isClosed_closure.isOpen_compl) hAV
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    let m := max N (t.sup id)
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hN m (le_max_left _ _)))
    have hxmV : x m in V m := hVmono ((Finset.le_sup hjt).trans (le_max_right _ _)) hjV
    exact hxmV (subset_closure ⟨m, mem_Ici.mpr le_rfl, rfl⟩)

/--
theorem `IsCountablyCompact.elim_finite_subcover_image` / 定理 `IsCountablyCompact.elim_finite_subcover_image`

English:
theorem IsCountablyCompact.elim_finite_subcover_image
  statement: (hA : IsCountablyCompact A)
  proof: by
  have := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) => hUo i i.prop) (by simpa using hAU)
  simp only [Subtype.forall', biUnion_eq_iUnion] at hUo hAU
  replace hb := hb.to_subtype
  obtain ⟨d, hd⟩ := hA.elim_finite_subcover hUo hAU
  refine ⟨Subtype.val '' (d : Set b)

中文:
定理 IsCountablyCompact.elim_finite_subcover_image
  结论: (hA : IsCountablyCompact A)
  证明: by
  have := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) => hUo i i.prop) (by simpa using hAU)
  simp only [Subtype.forall', biUnion_eq_iUnion] at hUo hAU
  replace hb := hb.to_subtype
  obtain ⟨d, hd⟩ := hA.elim_finite_subcover hUo hAU
  refine ⟨Subtype.val '' (d : Set b)

Depends on / 依赖: Subtype, Subtype.forall, Subtype.val, biUnion_eq_iUnion, biUnion_image, d.finite_toSet.image, elim_finite_subcover, finite_toSet, hA.elim_finite_subcover, hb.to_subtype, i.prop, replace, to_subtype
-/
theorem IsCountablyCompact.elim_finite_subcover_image (hA : IsCountablyCompact A)
    {b : Set ι} (hb : b.Countable) {U : ι -> Set E} (hUo : forall i in b, IsOpen (U i))
    (hAU : A subseteq ⋃ i in b, U i) : exists t subseteq b, t.Finite ∧ A subseteq ⋃ i in t, U i := by
  have := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) => hUo i i.prop) (by simpa using hAU)
  simp only [Subtype.forall', biUnion_eq_iUnion] at hUo hAU
  replace hb := hb.to_subtype
  obtain ⟨d, hd⟩ := hA.elim_finite_subcover hUo hAU
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/--
theorem `isCountablyCompact_iff_countable_open_cover'` / 定理 `isCountablyCompact_iff_countable_open_cover'`

English:
theorem isCountablyCompact_iff_countable_open_cover'
  proof: by
  simp [isCountablyCompact_iff_countable_open_cover, Finset.exists]

中文:
定理 isCountablyCompact_iff_countable_open_cover'
  证明: by
  simp [isCountablyCompact_iff_countable_open_cover, Finset.exists]

Depends on / 依赖: Finset, Finset.exists, isCountablyCompact_iff_countable_open_cover
-/
theorem isCountablyCompact_iff_countable_open_cover' :
    IsCountablyCompact A ↔ forall (U : Nat -> Set E), (forall i, IsOpen (U i)) -> A subseteq ⋃ i, U i ->
      exists t : Set Nat, t.Finite ∧ A subseteq ⋃ i in t, U i := by
  simp [isCountablyCompact_iff_countable_open_cover, Finset.exists]

/--
theorem `IsCompact.isCountablyCompact` / 定理 `IsCompact.isCountablyCompact`

English:
theorem IsCompact.isCountablyCompact
  given: (hA : IsCompact A)
  statement: IsCountablyCompact A
  proof: fun _ _ _ hle => hA hle

中文:
定理 IsCompact.isCountablyCompact
  条件: (hA : IsCompact A)
  结论: IsCountablyCompact A
  证明: fun _ _ _ hle => hA hle
-/
theorem IsCompact.isCountablyCompact (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ _ _ hle => hA hle

/--
Instance `instCompactSpaceCountablyCompactSpace` / 实例 `instCompactSpaceCountablyCompactSpace`

English:
instance instCompactSpaceCountablyCompactSpace
  body: isCompact_univ.isCountablyCompact

中文:
实例 instCompactSpaceCountablyCompactSpace
  定义体: isCompact_univ.isCountablyCompact

Depends on / 依赖: isCompact_univ, isCompact_univ.isCountablyCompact, isCountablyCompact
-/
instance instCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isCompact_univ.isCountablyCompact

/--
theorem `IsSeqCompact.isCountablyCompact` / 定理 `IsSeqCompact.isCountablyCompact`

English:
theorem IsSeqCompact.isCountablyCompact
  given: (hA : IsSeqCompact A)
  proof: IsCountablyCompact.of_seq_clusterPt fun x hx => by
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.subseq_of_frequently_in hx.frequently
  exact ⟨a, ha, hφa.mapClusterPt.of_comp hφ.tendsto_atTop⟩

中文:
定理 IsSeqCompact.isCountablyCompact
  条件: (hA : IsSeqCompact A)
  证明: IsCountablyCompact.of_seq_clusterPt fun x hx => by
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.subseq_of_frequently_in hx.frequently
  exact ⟨a, ha, hφa.mapClusterPt.of_comp hφ.tendsto_atTop⟩

Depends on / 依赖: IsCountablyCompact, IsCountablyCompact.of_seq_clusterPt, a.mapClusterPt.of_comp, frequently, hA.subseq_of_frequently_in, hx.frequently, mapClusterPt, of_comp, of_seq_clusterPt, subseq_of_frequently_in, tendsto_atTop
-/
theorem IsSeqCompact.isCountablyCompact (hA : IsSeqCompact A) :
    IsCountablyCompact A := IsCountablyCompact.of_seq_clusterPt fun x hx => by
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.subseq_of_frequently_in hx.frequently
  exact ⟨a, ha, hφa.mapClusterPt.of_comp hφ.tendsto_atTop⟩

/--
theorem `IsCountablyCompact.image` / 定理 `IsCountablyCompact.image`

English:
theorem IsCountablyCompact.image
  statement: (hA : IsCountablyCompact A)
  proof: by
  intro l hl_nebot hl_count hle
  have : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  have := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continu

中文:
定理 IsCountablyCompact.image
  结论: (hA : IsCountablyCompact A)
  证明: by
  intro l hl_nebot hl_count hle
  have : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  have := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continu

Depends on / 依赖: comap_inf_principal_neBot_of_image_mem, continuousAt, hf.continuousAt.inf, hl_count, hl_nebot, hx.mono, inf_le_left, inf_le_right, l.comap, le_principal_iff, le_principal_iff.mp, mem_image_of_mem, tendsto_comap
-/
theorem IsCountablyCompact.image (hA : IsCountablyCompact A)
    {f : E -> F} (hf : Continuous f) : IsCountablyCompact (f '' A) := by
  intro l hl_nebot hl_count hle
  have : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  have := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continuousAt.inf tendsto_comap).neBot⟩

/--
theorem `Topology.IsInducing.isCountablyCompact_iff` / 定理 `Topology.IsInducing.isCountablyCompact_iff`

English:
theorem Topology.IsInducing.isCountablyCompact_iff
  given: {f : E -> F} (hf : IsInducing f)
  proof: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

中文:
定理 Topology.IsInducing.isCountablyCompact_iff
  条件: {f : E -> F} (hf : IsInducing f)
  证明: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

Depends on / 依赖: ClusterPt, F_le, F_ne_bot, continuous, hf.continuous, hf.mapClusterPt_iff, hs.image, mapClusterPt_iff, map_mono, map_principal, trans_eq, x_in
-/
theorem Topology.IsInducing.isCountablyCompact_iff {f : E -> F} (hf : IsInducing f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/--
theorem `Topology.IsEmbedding.isCountablyCompact_iff` / 定理 `Topology.IsEmbedding.isCountablyCompact_iff`

English:
theorem Topology.IsEmbedding.isCountablyCompact_iff
  given: {f : E -> F} (hf : IsEmbedding f)
  proof: hf.isInducing.isCountablyCompact_iff

中文:
定理 Topology.IsEmbedding.isCountablyCompact_iff
  条件: {f : E -> F} (hf : IsEmbedding f)
  证明: hf.isInducing.isCountablyCompact_iff

Depends on / 依赖: hf.isInducing.isCountablyCompact_iff, isCountablyCompact_iff, isInducing
-/
theorem Topology.IsEmbedding.isCountablyCompact_iff {f : E -> F} (hf : IsEmbedding f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) :=
  hf.isInducing.isCountablyCompact_iff

/--
theorem `Subtype.isCountablyCompact_iff` / 定理 `Subtype.isCountablyCompact_iff`

English:
theorem Subtype.isCountablyCompact_iff
  given: {p : E -> Prop} {A : Set { x // p x }}
  proof: IsEmbedding.subtypeVal.isCountablyCompact_iff

中文:
定理 Subtype.isCountablyCompact_iff
  条件: {p : E -> 命题} {A : Set { x // p x }}
  证明: IsEmbedding.subtypeVal.isCountablyCompact_iff

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isCountablyCompact_iff, isCountablyCompact_iff, subtypeVal
-/
theorem Subtype.isCountablyCompact_iff {p : E -> Prop} {A : Set { x // p x }} :
    IsCountablyCompact A ↔ IsCountablyCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isCountablyCompact_iff

/--
theorem `isCountablyCompact_iff_isCountablyCompact_univ` / 定理 `isCountablyCompact_iff_isCountablyCompact_univ`

English:
theorem isCountablyCompact_iff_isCountablyCompact_univ
  proof: by
  rw [Subtype.isCountablyCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

中文:
定理 isCountablyCompact_iff_isCountablyCompact_univ
  证明: by
  rw [Subtype.isCountablyCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.isCountablyCompact_iff, Subtype.range_coe, image_univ, isCountablyCompact_iff, range_coe
-/
theorem isCountablyCompact_iff_isCountablyCompact_univ :
    IsCountablyCompact A ↔ IsCountablyCompact (univ : Set A) := by
  rw [Subtype.isCountablyCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

/--
theorem `isCountablyCompact_univ_iff` / 定理 `isCountablyCompact_univ_iff`

English:
theorem isCountablyCompact_univ_iff
  statement: IsCountablyCompact (univ : Set E) ↔ CountablyCompactSpace E
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
定理 isCountablyCompact_univ_iff
  结论: IsCountablyCompact (univ : Set E) ↔ CountablyCompactSpace E
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩
-/
theorem isCountablyCompact_univ_iff : IsCountablyCompact (univ : Set E) ↔ CountablyCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/--
theorem `isCountablyCompact_iff_countablyCompactSpace` / 定理 `isCountablyCompact_iff_countablyCompactSpace`

English:
theorem isCountablyCompact_iff_countablyCompactSpace
  proof: isCountablyCompact_iff_isCountablyCompact_univ.trans isCountablyCompact_univ_iff

中文:
定理 isCountablyCompact_iff_countablyCompactSpace
  证明: isCountablyCompact_iff_isCountablyCompact_univ.trans isCountablyCompact_univ_iff

Depends on / 依赖: isCountablyCompact_iff_isCountablyCompact_univ, isCountablyCompact_iff_isCountablyCompact_univ.trans, isCountablyCompact_univ_iff
-/
theorem isCountablyCompact_iff_countablyCompactSpace :
    IsCountablyCompact A ↔ CountablyCompactSpace A :=
  isCountablyCompact_iff_isCountablyCompact_univ.trans isCountablyCompact_univ_iff

/-- If a sequential space is countably compact, then it is sequentially compact. We follow the proof
in [kremsater1972sequential]. -/
instance (priority := 50) [SequentialSpace E] [CountablyCompactSpace E] :
    SeqCompactSpace E := by
  -- We prove by contradiction. If `E` is not sequentially compact, then there exists a sequence
  -- `x : ℕ → E` with no convergent subsequence.
  by_contra
  simp only [seqCompactSpace_iff, IsSeqCompact, mem_univ, not_forall,
    true_and, not_exists, not_and, exists_const] at this
  obtain ⟨x, hx⟩ := this
  -- Consider the set `A = ⋃ i, closure {x i}`. It is closed by `isClosed_of_not_tendsto` and thus
  -- countably compact.
  let A := ⋃ i, closure {x i}
  have : IsCountablyCompact A :=
    (isClosed_iUnion_closure_singleton_of_not_tendsto hx).isCountablyCompact
  -- We use the countably compactness of `A` to find a cluster point `a`. Eventually `a` does not
  -- belong to the closure of `{x n}` as `x` has no convergent subsequence, and this contradicts `a`
  -- being a cluster point.
  obtain ⟨a, ha⟩ : exists a in A, MapClusterPt a atTop x := by
    refine isCountablyCompact_iff_seq_clusterPt.1 this _ (.of_forall fun n => ?_)
exact mem_iUnion_of_mem n subset_closure mem_singleton (x n)
  obtain ⟨k, hk⟩ : exists k, forall n > k, a ∉ closure {x n} := by
    by_contra!
    obtain ⟨φ, hφ1, hφ2⟩ := Nat.exists_strictMono_subsequence this
    refine hx a φ hφ1 (tendsto_atTop_nhds.2 fun U ha hUo => ⟨0, fun n _ => ?_⟩)
    simpa using mem_closure_iff.1 (hφ2 n) U hUo ha
  have : a ∉ ⋃ i, closure {x (i + (k + 1))} := by
    simpa [← iUnion_ge_eq_iUnion_nat_add (fun n => closure {x n}) (k + 1)] using!
      fun i hi => hk i (Nat.lt_of_lt_of_eq hi rfl)
  apply this
  suffices h : closure (x '' Ici (k + 1)) subseteq ⋃ i, closure {x (i + (k + 1))} from
h mapClusterPt_atTop_iff_forall_mem_closure.1 ha.2 (k + 1)
  refine (IsClosed.closure_subset_iff
    (isClosed_iUnion_closure_singleton_of_not_tendsto fun l φ hφ => ?_)).2 ?_
  · exact hx l _ ((strictMono_id.add_const _).comp hφ)
  · simp only [image_eq_iUnion, mem_Ici, iUnion_ge_eq_iUnion_nat_add _ (k + 1)]
    exact iUnion_mono fun i => subset_closure

/--
theorem `Topology.IsInducing.isSeqCompact_iff` / 定理 `Topology.IsInducing.isSeqCompact_iff`

English:
theorem Topology.IsInducing.isSeqCompact_iff
  given: {f : E -> F} (hf : IsInducing f)
  proof: by
    choose y hy using hx
    obtain ⟨a, ha, ⟨φ, hφ⟩⟩ := hA (fun n => (hy n).1)
    refine ⟨f a, mem_image_of_mem f ha, φ, hφ.1, ?_⟩
    suffices f ∘ y ∘ φ = x ∘ φ from this ▸ (hf.continuous.tendsto a).comp hφ.2
    grind
  mpr hA x hx := by
    obtain ⟨fa, hfa, ⟨φ, hφ⟩⟩ := hA (fun n => mem_image_

中文:
定理 Topology.IsInducing.isSeqCompact_iff
  条件: {f : E -> F} (hf : IsInducing f)
  证明: by
    choose y hy using hx
    obtain ⟨a, ha, ⟨φ, hφ⟩⟩ := hA (fun n => (hy n).1)
    refine ⟨f a, mem_image_of_mem f ha, φ, hφ.1, ?_⟩
    suffices f ∘ y ∘ φ = x ∘ φ from this ▸ (hf.continuous.tendsto a).comp hφ.2
    grind
  mpr hA x hx := by
    obtain ⟨fa, hfa, ⟨φ, hφ⟩⟩ := hA (fun n => mem_image_

Depends on / 依赖: continuous, hf.continuous.tendsto, hf.tendsto_nhds_iff, mem_image_of_mem, tendsto, tendsto_nhds_iff
-/
theorem Topology.IsInducing.isSeqCompact_iff {f : E -> F} (hf : IsInducing f) :
    IsSeqCompact A ↔ IsSeqCompact (f '' A) where
  mp hA x hx := by
    choose y hy using hx
    obtain ⟨a, ha, ⟨φ, hφ⟩⟩ := hA (fun n => (hy n).1)
    refine ⟨f a, mem_image_of_mem f ha, φ, hφ.1, ?_⟩
    suffices f ∘ y ∘ φ = x ∘ φ from this ▸ (hf.continuous.tendsto a).comp hφ.2
    grind
  mpr hA x hx := by
    obtain ⟨fa, hfa, ⟨φ, hφ⟩⟩ := hA (fun n => mem_image_of_mem f (hx n))
    choose a ha using hfa
    exact ⟨a, ha.1, φ, hφ.1, hf.tendsto_nhds_iff.2 (ha.2 ▸ hφ.2)⟩

/--
theorem `Subtype.isSeqCompact_iff` / 定理 `Subtype.isSeqCompact_iff`

English:
theorem Subtype.isSeqCompact_iff
  given: {p : E -> Prop} {A : Set { x // p x }}
  proof: IsEmbedding.subtypeVal.isSeqCompact_iff

中文:
定理 Subtype.isSeqCompact_iff
  条件: {p : E -> 命题} {A : Set { x // p x }}
  证明: IsEmbedding.subtypeVal.isSeqCompact_iff

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isSeqCompact_iff, isSeqCompact_iff, subtypeVal
-/
theorem Subtype.isSeqCompact_iff {p : E -> Prop} {A : Set { x // p x }} :
    IsSeqCompact A ↔ IsSeqCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isSeqCompact_iff

/--
theorem `isSeqCompact_iff_isSeqCompact_univ` / 定理 `isSeqCompact_iff_isSeqCompact_univ`

English:
theorem isSeqCompact_iff_isSeqCompact_univ
  statement: IsSeqCompact A ↔ IsSeqCompact (univ : Set A)
  proof: by
  rw [Subtype.isSeqCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

中文:
定理 isSeqCompact_iff_isSeqCompact_univ
  结论: IsSeqCompact A ↔ IsSeqCompact (univ : Set A)
  证明: by
  rw [Subtype.isSeqCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.isSeqCompact_iff, Subtype.range_coe, image_univ, isSeqCompact_iff, range_coe
-/
theorem isSeqCompact_iff_isSeqCompact_univ : IsSeqCompact A ↔ IsSeqCompact (univ : Set A) := by
  rw [Subtype.isSeqCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

/--
theorem `isSeqCompact_univ_iff` / 定理 `isSeqCompact_univ_iff`

English:
theorem isSeqCompact_univ_iff
  statement: IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
定理 isSeqCompact_univ_iff
  结论: IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩
-/
theorem isSeqCompact_univ_iff : IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/--
theorem `isSeqCompact_iff_seqCompactSpace` / 定理 `isSeqCompact_iff_seqCompactSpace`

English:
theorem isSeqCompact_iff_seqCompactSpace
  statement: IsSeqCompact A ↔ SeqCompactSpace A
  proof: isSeqCompact_iff_isSeqCompact_univ.trans isSeqCompact_univ_iff

中文:
定理 isSeqCompact_iff_seqCompactSpace
  结论: IsSeqCompact A ↔ SeqCompactSpace A
  证明: isSeqCompact_iff_isSeqCompact_univ.trans isSeqCompact_univ_iff

Depends on / 依赖: isSeqCompact_iff_isSeqCompact_univ, isSeqCompact_iff_isSeqCompact_univ.trans, isSeqCompact_univ_iff
-/
theorem isSeqCompact_iff_seqCompactSpace : IsSeqCompact A ↔ SeqCompactSpace A :=
  isSeqCompact_iff_isSeqCompact_univ.trans isSeqCompact_univ_iff

/--
Instance `instSeqCompactSpaceCountablyCompactSpace` / 实例 `instSeqCompactSpaceCountablyCompactSpace`

English:
instance instSeqCompactSpaceCountablyCompactSpace
  body: isSeqCompact_univ.isCountablyCompact

中文:
实例 instSeqCompactSpaceCountablyCompactSpace
  定义体: isSeqCompact_univ.isCountablyCompact

Depends on / 依赖: isCountablyCompact, isSeqCompact_univ, isSeqCompact_univ.isCountablyCompact
-/
instance instSeqCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isSeqCompact_univ.isCountablyCompact

/--
theorem `IsCountablyCompact.isSeqCompact` / 定理 `IsCountablyCompact.isSeqCompact`

English:
theorem IsCountablyCompact.isSeqCompact
  statement: [FirstCountableTopology E]
  proof: have : CountablyCompactSpace A := isCountablyCompact_iff_countablyCompactSpace.1 hA
  isSeqCompact_iff_seqCompactSpace.2 inferInstance

中文:
定理 IsCountablyCompact.isSeqCompact
  结论: [FirstCountableTopology E]
  证明: have : CountablyCompactSpace A := isCountablyCompact_iff_countablyCompactSpace.1 hA
  isSeqCompact_iff_seqCompactSpace.2 inferInstance

Depends on / 依赖: CountablyCompactSpace, isCountablyCompact_iff_countablyCompactSpace, isSeqCompact_iff_seqCompactSpace
-/
theorem IsCountablyCompact.isSeqCompact [FirstCountableTopology E]
    (hA : IsCountablyCompact A) : IsSeqCompact A :=
  have : CountablyCompactSpace A := isCountablyCompact_iff_countablyCompactSpace.1 hA
  isSeqCompact_iff_seqCompactSpace.2 inferInstance

/--
Instance `instCountablyCompactSpaceSeqCompactSpace` / 实例 `instCountablyCompactSpaceSeqCompactSpace`

English:
instance instCountablyCompactSpaceSeqCompactSpace
  signature: {X : Type*} [TopologicalSpace X]
  body: CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact

中文:
实例 instCountablyCompactSpaceSeqCompactSpace
  签名: {X : 类型} [TopologicalSpace X]
  定义体: CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact

Depends on / 依赖: CountablyCompactSpace, CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact, isCountablyCompact_univ, isSeqCompact
-/
instance instCountablyCompactSpaceSeqCompactSpace {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CountablyCompactSpace X] : SeqCompactSpace X where
  isSeqCompact_univ := CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact

/--
theorem `isCountablyCompact_iff_isSeqCompact` / 定理 `isCountablyCompact_iff_isSeqCompact`

English:
theorem isCountablyCompact_iff_isSeqCompact
  given: [FirstCountableTopology E]
  proof: ⟨fun h => h.isSeqCompact, fun h => h.isCountablyCompact⟩

中文:
定理 isCountablyCompact_iff_isSeqCompact
  条件: [FirstCountableTopology E]
  证明: ⟨fun h => h.isSeqCompact, fun h => h.isCountablyCompact⟩

Depends on / 依赖: h.isCountablyCompact, h.isSeqCompact, isCountablyCompact, isSeqCompact
-/
theorem isCountablyCompact_iff_isSeqCompact [FirstCountableTopology E] :
    IsCountablyCompact A ↔ IsSeqCompact A :=
  ⟨fun h => h.isSeqCompact, fun h => h.isCountablyCompact⟩

/--
theorem `IsCountablyCompact.exists_accPt_of_infinite` / 定理 `IsCountablyCompact.exists_accPt_of_infinite`

English:
theorem IsCountablyCompact.exists_accPt_of_infinite
  proof: by
  let f := hB.natEmbedding
  let x : Nat -> E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ :=
    IsCountablyCompact.seq_clusterPt hA x (Eventually.of_forall (fun n => hBA (f n).2))
refine ⟨a, haA, accPt_iff_clusterPt.2 ClusterPt

中文:
定理 IsCountablyCompact.exists_accPt_of_infinite
  证明: by
  let f := hB.natEmbedding
  let x : Nat -> E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ :=
    IsCountablyCompact.seq_clusterPt hA x (Eventually.of_forall (fun n => hBA (f n).2))
refine ⟨a, haA, accPt_iff_clusterPt.2 ClusterPt

Depends on / 依赖: ClusterPt, ClusterPt.mono, Eventually, Eventually.of_forall, Function, Function.Injective, Injective, IsCountablyCompact, IsCountablyCompact.seq_clusterPt, Nat.cofinite_eq_atTop, Set.finite_singleton, Subtype, Subtype.val_injective.comp, accPt_iff_clusterPt, cofinite_eq_atTop, compl_mem_cofinite, f.injective, finite_singleton, hB.natEmbedding, hx_inj
-/
theorem IsCountablyCompact.exists_accPt_of_infinite
    (hA : IsCountablyCompact A) (hBA : B subseteq A) (hB : B.Infinite) :
    exists a in A, AccPt a (𝓟 B) := by
  let f := hB.natEmbedding
  let x : Nat -> E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ :=
    IsCountablyCompact.seq_clusterPt hA x (Eventually.of_forall (fun n => hBA (f n).2))
refine ⟨a, haA, accPt_iff_clusterPt.2 ClusterPt.mono hac le_inf ?_ ?_⟩
· exact tendsto_principal.mpr Nat.cofinite_eq_atTop ▸
      ((Set.finite_singleton a).preimage hx_inj.injOn).compl_mem_cofinite
· exact tendsto_principal.mpr Eventually.of_forall fun n => (f n).2

/--
theorem `isCountablyCompact_iff_infinite_subset_has_accPt` / 定理 `isCountablyCompact_iff_infinite_subset_has_accPt`

English:
theorem isCountablyCompact_iff_infinite_subset_has_accPt
  given: [T1Space E] {A : Set E}
  proof: hA.exists_accPt_of_infinite hBA hB
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    rw [← Nat.cofinite_eq_atTop] at hx ⊢
    by_cases! hfin : (Set.range x).Finite
    · -- Case 1: Finite range
      suffices exists a in range x inter A, MapClusterPt a cofinite x by aes

中文:
定理 isCountablyCompact_iff_infinite_subset_has_accPt
  条件: [T1Space E] {A : Set E}
  证明: hA.exists_accPt_of_infinite hBA hB
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    rw [← Nat.cofinite_eq_atTop] at hx ⊢
    by_cases! hfin : (Set.range x).Finite
    · -- Case 1: Finite range
      suffices exists a in range x inter A, MapClusterPt a cofinite x by aes

Depends on / 依赖: exists_accPt_of_infinite, hA.exists_accPt_of_infinite
-/
theorem isCountablyCompact_iff_infinite_subset_has_accPt [T1Space E] {A : Set E} :
    IsCountablyCompact A ↔ forall B subseteq A, B.Infinite -> exists a in A, AccPt a (𝓟 B) where
  mp hA _ hBA hB := hA.exists_accPt_of_infinite hBA hB
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    rw [← Nat.cofinite_eq_atTop] at hx ⊢
    by_cases! hfin : (Set.range x).Finite
    · -- Case 1: Finite range
      suffices exists a in range x inter A, MapClusterPt a cofinite x by aesop
.isCompact.exists_mapClusterPt_of_frequently exact hfin.inter_of_left A
        hx.frequently.mp (by simp)
    · -- Case 2: Infinite range
obtain ⟨a, haA, hacc⟩ := h (Set.range x inter A) inter_subset_right by
        rw [eventually_iff]; rw [mem_cofinite]; rw [compl_ofPred] at hx
        exact hfin.inter_of_finite_sdiff (hx.image x |>.subset (by grind))
      refine ⟨a, haA, ?_⟩
      simp_rw [mapClusterPt_iff_frequently, frequently_cofinite_iff_infinite]
.of_image x .mono (by grind) exact fun s hs => Infinite.of_accPt (hacc.nhds_inter hs)

/--
theorem `IsLindelof.isCompact` / 定理 `IsLindelof.isCompact`

English:
theorem IsLindelof.isCompact
  given: (hA : IsCountablyCompact A) (hl : IsLindelof A)
  proof: by
  refine isCompact_of_finite_subcover fun {ι} U hUo hAU => ?_
  by_cases! h : Nonempty ι
  · obtain ⟨f, hf⟩ := hl.indexed_countable_subcover U hUo hAU
    obtain ⟨t, ht⟩ := isCountablyCompact_iff_countable_open_cover.1 hA (U ∘ f)
      (fun n => hUo (f n)) hf
    classical
    exact ⟨t.image f, b

中文:
定理 IsLindelof.isCompact
  条件: (hA : IsCountablyCompact A) (hl : IsLindelof A)
  证明: by
  refine isCompact_of_finite_subcover fun {ι} U hUo hAU => ?_
  by_cases! h : Nonempty ι
  · obtain ⟨f, hf⟩ := hl.indexed_countable_subcover U hUo hAU
    obtain ⟨t, ht⟩ := isCountablyCompact_iff_countable_open_cover.1 hA (U ∘ f)
      (fun n => hUo (f n)) hf
    classical
    exact ⟨t.image f, b

Depends on / 依赖: Nonempty, classical, hl.indexed_countable_subcover, indexed_countable_subcover, isCompact_of_finite_subcover, isCountablyCompact_iff_countable_open_cover, t.image
-/
theorem IsLindelof.isCompact (hA : IsCountablyCompact A) (hl : IsLindelof A) :
    IsCompact A := by
  refine isCompact_of_finite_subcover fun {ι} U hUo hAU => ?_
  by_cases! h : Nonempty ι
  · obtain ⟨f, hf⟩ := hl.indexed_countable_subcover U hUo hAU
    obtain ⟨t, ht⟩ := isCountablyCompact_iff_countable_open_cover.1 hA (U ∘ f)
      (fun n => hUo (f n)) hf
    classical
    exact ⟨t.image f, by simp_all⟩
  · exact ⟨∅, by simp_all⟩

/--
theorem `LindelofSpace.compactSpace` / 定理 `LindelofSpace.compactSpace`

English:
theorem LindelofSpace.compactSpace
  statement: {X : Type*} [TopologicalSpace X]
  proof: isLindelof_univ.isCompact h.isCountablyCompact_univ

@[deprecated (since := "2026-05-19")]
alias LindelofSpace.CompactSpace := LindelofSpace.compactSpace

中文:
定理 LindelofSpace.compactSpace
  结论: {X : 类型} [TopologicalSpace X]
  证明: isLindelof_univ.isCompact h.isCountablyCompact_univ

@[deprecated (since := "2026-05-19")]
alias LindelofSpace.CompactSpace := LindelofSpace.compactSpace

Depends on / 依赖: h.isCountablyCompact_univ, isCompact, isCountablyCompact_univ, isLindelof_univ, isLindelof_univ.isCompact
-/
theorem LindelofSpace.compactSpace {X : Type*} [TopologicalSpace X]
    [LindelofSpace X] [h : CountablyCompactSpace X] : CompactSpace X where
  isCompact_univ := isLindelof_univ.isCompact h.isCountablyCompact_univ

@[deprecated (since := "2026-05-19")]
alias LindelofSpace.CompactSpace := LindelofSpace.compactSpace

/--
theorem `IsCountablyCompact.isCompact` / 定理 `IsCountablyCompact.isCompact`

English:
theorem IsCountablyCompact.isCompact
  statement: [HereditarilyLindelofSpace E]
  proof: (HereditarilyLindelofSpace.isLindelof A).isCompact hA

中文:
定理 IsCountablyCompact.isCompact
  结论: [HereditarilyLindelofSpace E]
  证明: (HereditarilyLindelofSpace.isLindelof A).isCompact hA

Depends on / 依赖: HereditarilyLindelofSpace, HereditarilyLindelofSpace.isLindelof, isCompact, isLindelof
-/
theorem IsCountablyCompact.isCompact [HereditarilyLindelofSpace E]
    (hA : IsCountablyCompact A) : IsCompact A :=
  (HereditarilyLindelofSpace.isLindelof A).isCompact hA

/--
theorem `IsCountablyCompact.union` / 定理 `IsCountablyCompact.union`

English:
theorem IsCountablyCompact.union
  given: (hA : IsCountablyCompact A) (hB : IsCountablyCompact B)
  proof: by
  rw [isCountablyCompact_iff_countable_open_cover'] at hA hB ⊢
  intro U hUo hAU
  obtain ⟨t₁, ht₁, hA_sub⟩ : exists (t₁ : Set Nat), t₁.Finite ∧ A subseteq ⋃ k in t₁, U k :=
    hA U hUo (subset_union_left.trans hAU)
  obtain ⟨t₂, ht₂, hB_sub⟩ : exists (t₂ : Set Nat), t₂.Finite ∧ B subseteq ⋃ k i

中文:
定理 IsCountablyCompact.union
  条件: (hA : IsCountablyCompact A) (hB : IsCountablyCompact B)
  证明: by
  rw [isCountablyCompact_iff_countable_open_cover'] at hA hB ⊢
  intro U hUo hAU
  obtain ⟨t₁, ht₁, hA_sub⟩ : exists (t₁ : Set Nat), t₁.Finite ∧ A subseteq ⋃ k in t₁, U k :=
    hA U hUo (subset_union_left.trans hAU)
  obtain ⟨t₂, ht₂, hB_sub⟩ : exists (t₂ : Set Nat), t₂.Finite ∧ B subseteq ⋃ k i

Depends on / 依赖: Finite, hA_sub, hB_sub, isCountablyCompact_iff_countable_open_cover, subset_union_left, subset_union_left.trans, subset_union_right, subset_union_right.trans, subseteq, union_subset_union
-/
theorem IsCountablyCompact.union (hA : IsCountablyCompact A) (hB : IsCountablyCompact B) :
    IsCountablyCompact (A union B) := by
  rw [isCountablyCompact_iff_countable_open_cover'] at hA hB ⊢
  intro U hUo hAU
  obtain ⟨t₁, ht₁, hA_sub⟩ : exists (t₁ : Set Nat), t₁.Finite ∧ A subseteq ⋃ k in t₁, U k :=
    hA U hUo (subset_union_left.trans hAU)
  obtain ⟨t₂, ht₂, hB_sub⟩ : exists (t₂ : Set Nat), t₂.Finite ∧ B subseteq ⋃ k in t₂, U k :=
    hB U hUo (subset_union_right.trans hAU)
  have h : (⋃ k in t₁, U k) union (⋃ k in t₂, U k) = ⋃ k in (t₁ union t₂), U k := by ext; aesop
  exact ⟨t₁ union t₂, ht₁.union ht₂, h ▸ union_subset_union hA_sub hB_sub⟩

/--
theorem `Finset.isCountablyCompact_biUnion` / 定理 `Finset.isCountablyCompact_biUnion`

English:
theorem Finset.isCountablyCompact_biUnion
  statement: (s : Finset ι) {f : ι -> Set E}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCountablyCompact_empty
  | @insert a s ha ih => simpa [Finset.biUnion_insert] using
(hf a (Finset.mem_insert_self a s)).union ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

中文:
定理 Finset.isCountablyCompact_biUnion
  结论: (s : Finset ι) {f : ι -> Set E}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCountablyCompact_empty
  | @insert a s ha ih => simpa [Finset.biUnion_insert] using
(hf a (Finset.mem_insert_self a s)).union ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

Depends on / 依赖: Finset, Finset.biUnion_insert, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, biUnion_insert, classical, induction_on, insert, isCountablyCompact_empty, mem_insert_of_mem, mem_insert_self
-/
theorem Finset.isCountablyCompact_biUnion (s : Finset ι) {f : ι -> Set E}
    (hf : forall i in s, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i in s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCountablyCompact_empty
  | @insert a s ha ih => simpa [Finset.biUnion_insert] using
(hf a (Finset.mem_insert_self a s)).union ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/--
theorem `Set.Finite.isCountablyCompact_biUnion` / 定理 `Set.Finite.isCountablyCompact_biUnion`

English:
theorem Set.Finite.isCountablyCompact_biUnion
  statement: {s : Set ι} {f : ι -> Set E} (hs : s.Finite)
  proof: by
  let s' : Finset ι := hs.toFinset
  have h1 : (⋃ i in s, f i) = (⋃ i in s', f i) := by simp [s']
  exact h1 ▸ Finset.isCountablyCompact_biUnion s' (fun i hi => hf i ((hs.mem_toFinset).mp hi))

中文:
定理 Set.Finite.isCountablyCompact_biUnion
  结论: {s : Set ι} {f : ι -> Set E} (hs : s.Finite)
  证明: by
  let s' : Finset ι := hs.toFinset
  have h1 : (⋃ i in s, f i) = (⋃ i in s', f i) := by simp [s']
  exact h1 ▸ Finset.isCountablyCompact_biUnion s' (fun i hi => hf i ((hs.mem_toFinset).mp hi))

Depends on / 依赖: Finset, Finset.isCountablyCompact_biUnion, hs.mem_toFinset, hs.toFinset, isCountablyCompact_biUnion, mem_toFinset, toFinset
-/
theorem Set.Finite.isCountablyCompact_biUnion {s : Set ι} {f : ι -> Set E} (hs : s.Finite)
    (hf : forall i in s, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ i in s, f i) := by
  let s' : Finset ι := hs.toFinset
  have h1 : (⋃ i in s, f i) = (⋃ i in s', f i) := by simp [s']
  exact h1 ▸ Finset.isCountablyCompact_biUnion s' (fun i hi => hf i ((hs.mem_toFinset).mp hi))

/--
theorem `Set.Finite.isCountablyCompact_sUnion` / 定理 `Set.Finite.isCountablyCompact_sUnion`

English:
theorem Set.Finite.isCountablyCompact_sUnion
  statement: {S : Set (Set E)} (hf : S.Finite)
  proof: by
  rw [sUnion_eq_biUnion]; exact hf.isCountablyCompact_biUnion hc

中文:
定理 Set.Finite.isCountablyCompact_sUnion
  结论: {S : Set (Set E)} (hf : S.Finite)
  证明: by
  rw [sUnion_eq_biUnion]; exact hf.isCountablyCompact_biUnion hc

Depends on / 依赖: hf.isCountablyCompact_biUnion, isCountablyCompact_biUnion, sUnion_eq_biUnion
-/
theorem Set.Finite.isCountablyCompact_sUnion {S : Set (Set E)} (hf : S.Finite)
    (hc : forall s in S, IsCountablyCompact s) :
    IsCountablyCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCountablyCompact_biUnion hc

/--
theorem `isCountablyCompact_iUnion` / 定理 `isCountablyCompact_iUnion`

English:
theorem isCountablyCompact_iUnion
  statement: {ι : Sort*} {f : ι -> Set E} [Finite ι]
  proof: (finite_range f).isCountablyCompact_sUnion forall_mem_range.2 h

中文:
定理 isCountablyCompact_iUnion
  结论: {ι : Sort*} {f : ι -> Set E} [Finite ι]
  证明: (finite_range f).isCountablyCompact_sUnion forall_mem_range.2 h

Depends on / 依赖: finite_range, forall_mem_range, isCountablyCompact_sUnion
-/
theorem isCountablyCompact_iUnion {ι : Sort*} {f : ι -> Set E} [Finite ι]
    (h : forall i, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i, f i) :=
(finite_range f).isCountablyCompact_sUnion forall_mem_range.2 h

end
