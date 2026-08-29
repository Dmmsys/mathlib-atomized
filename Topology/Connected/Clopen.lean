/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic

/-!
# Connected subsets and their relation to clopen sets

In this file we show how connected subsets of a topological space are intimately connected
to clopen sets.

## Main declarations

+ `IsClopen.biUnion_connectedComponent_eq`: a clopen set is the union of its connected components.
+ `PreconnectedSpace.induction₂`: an induction principle for preconnected spaces.
+ `ConnectedComponents`: The connected components of a topological space, as a quotient type.

-/

@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι -> Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/--
theorem `IsPreconnected.subset_isClopen` / 定理 `IsPreconnected.subset_isClopen`

English:
theorem IsPreconnected.subset_isClopen
  statement: {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
  proof: hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

中文:
定理 是预连通.subset_isClopen
  结论: {s t : 集合 α} (hs : 是预连通 s) (ht : IsClopen t)
  证明: hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

Depends on / 依赖: disjoint_compl_right, hs.subset_left_of_subset_union, ht.compl.isOpen, ht.isOpen, isOpen, subset_left_of_subset_union
-/
theorem IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s inter t).Nonempty) : s subseteq t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

/--
theorem `Sigma.isConnected_iff` / 定理 `Sigma.isConnected_iff`

English:
theorem Sigma.isConnected_iff
  given: [forall i, TopologicalSpace (X i)] {s : Set (Σ i, X i)}
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s subseteq range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

中文:
定理 依赖和类型.isConnected_iff
  条件: [对任意 i, 拓扑空间 (X i)] {s : 集合 (Σ i, X i)}
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s subseteq range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

Depends on / 依赖: Set.image_preimage_eq_of_subset, Sigma.mk, continuousOn, continuous_sigmaMk, continuous_sigmaMk.continuousOn, hs.isPreconnected.subset_isClopen, hs.nonempty, hs.preimage_of_isOpenMap, ht.image, image_preimage_eq_of_subset, isClopen_range_sigmaMk, isOpenMap_sigmaMk, isPreconnected, nonempty, preimage_of_isOpenMap, sigma_mk_injective, subset_isClopen, subseteq
-/
theorem Sigma.isConnected_iff [forall i, TopologicalSpace (X i)] {s : Set (Σ i, X i)} :
    IsConnected s ↔ exists i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s subseteq range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

/--
theorem `Sigma.isPreconnected_iff` / 定理 `Sigma.isPreconnected_iff`

English:
theorem Sigma.isPreconnected_iff
  statement: [hι : Nonempty ι] [forall i, TopologicalSpace (X i)]
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

中文:
定理 依赖和类型.isPreconnected_iff
  结论: [hι : 非空 ι] [对任意 i, 拓扑空间 (X i)]
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

Depends on / 依赖: Classical, Classical.choice, Set.image_empty, Sigma.isConnected_iff, choice, continuousOn, continuous_sigmaMk, continuous_sigmaMk.continuousOn, eq_empty_or_nonempty, ht.image, ht.isPreconnected, image_empty, isConnected_iff, isPreconnected, isPreconnected_empty, s.eq_empty_or_nonempty
-/
theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [forall i, TopologicalSpace (X i)]
    {s : Set (Σ i, X i)} : IsPreconnected s ↔ exists i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

/--
theorem `Sum.isConnected_iff` / 定理 `Sum.isConnected_iff`

English:
theorem Sum.isConnected_iff
  given: [TopologicalSpace β] {s : Set (α oplus β)}
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s subseteq range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s subseteq range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

中文:
定理 和.isConnected_iff
  条件: [拓扑空间 β] {s : 集合 (α oplus β)}
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s subseteq range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s subseteq range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

Depends on / 依赖: Or.inl, Or.inr, Sum.inl, Sum.inl_injective, Sum.inr, hs.isPreconnected.subset_isClopen, hs.nonempty, hs.preimage_o, hs.preimage_of_isOpenMap, image_preimage_eq_of_subset, inl_injective, isClopen_range_inl, isClopen_range_inr, isOpenMap_inl, isPreconnected, nonempty, preimage_o, preimage_of_isOpenMap, subset_isClopen, subseteq
-/
theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (α oplus β)} :
    IsConnected s ↔
      (exists t, IsConnected t ∧ s = Sum.inl '' t) ∨ exists t, IsConnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s subseteq range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s subseteq range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

/--
theorem `Sum.isPreconnected_iff` / 定理 `Sum.isPreconnected_iff`

English:
theorem Sum.isPreconnected_iff
  given: [TopologicalSpace β] {s : Set (α oplus β)}
  proof: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

中文:
定理 和.isPreconnected_iff
  条件: [拓扑空间 β] {s : 集合 (α oplus β)}
  证明: by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

Depends on / 依赖: Or.inl, Or.inr, Set.image_empty, Sum.isConnected_iff, continuousOn, continuous_inl, continuous_inl.continuousOn, continuous_inr, continuous_inr.continuousOn, eq_empty_or_nonempty, ht.image, ht.isPreconnected, image_empty, isConnected_iff, isPreconnected, isPreconnected_empty, s.eq_empty_or_nonempty
-/
theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (α oplus β)} :
    IsPreconnected s ↔
      (exists t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ exists t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

/--
theorem `Continuous.exists_lift_sigma` / 定理 `Continuous.exists_lift_sigma`

English:
theorem Continuous.exists_lift_sigma
  statement: [ConnectedSpace α] [forall i, TopologicalSpace (X i)]
  proof: by
  obtain ⟨i, hi⟩ : exists i, range f subseteq range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf

中文:
定理 连续.存在_lift_sigma
  结论: [连通空间 α] [对任意 i, 拓扑空间 (X i)]
  证明: by
  obtain ⟨i, hi⟩ : exists i, range f subseteq range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf

Depends on / 依赖: IsEmbedding, IsEmbedding.sigmaMk.continuous_iff, Sigma.isConnected_iff, continuous_iff, hs.trans_subset, image_subset_range, isConnected_iff, isConnected_range, range_subset_range_iff_exists_comp, sigmaMk, subseteq, trans_subset
-/
theorem Continuous.exists_lift_sigma [ConnectedSpace α] [forall i, TopologicalSpace (X i)]
    {f : α -> Σ i, X i} (hf : Continuous f) :
    exists (i : ι) (g : α -> X i), Continuous g ∧ f = Sigma.mk i ∘ g := by
  obtain ⟨i, hi⟩ : exists i, range f subseteq range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← IsEmbedding.sigmaMk.continuous_iff] at hf

/--
theorem `nonempty_inter` / 定理 `nonempty_inter`

English:
theorem nonempty_inter
  given: [PreconnectedSpace α] {s t : Set α}
  proof: by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

中文:
定理 nonempty_inter
  条件: [预连通空间 α] {s t : 集合 α}
  证明: by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.isPreconnected_univ, isPreconnected_univ, univ_inter, univ_subset_iff
-/
theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s -> IsOpen t -> s union t = univ -> s.Nonempty -> t.Nonempty -> (s inter t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

/--
theorem `isClopen_iff` / 定理 `isClopen_iff`

English:
theorem isClopen_iff
  given: [PreconnectedSpace α] {s : Set α}
  statement: IsClopen s ↔ s = ∅ ∨ s = univ
  proof: ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s.Nonempty ∧ sᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using h
      have ⟨_, h2, h3⟩ := nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) h1.1 h1.2
      h3 h2,
    by rintro (rfl | rfl); exacts [isClopen_empty, isClopen_univ]⟩

中文:
定理 isClopen_iff
  条件: [预连通空间 α] {s : 集合 α}
  结论: IsClopen s ↔ s = ∅ ∨ s = univ
  证明: ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s.Nonempty ∧ sᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using h
      have ⟨_, h2, h3⟩ := nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) h1.1 h1.2
      h3 h2,
    by rintro (rfl | rfl); exacts [isClopen_empty, isClopen_univ]⟩

Depends on / 依赖: Nonempty, by_contradiction, exacts, isClopen_empty, isClopen_univ, isOpen_compl, nonempty_iff_ne_empty, nonempty_inter, s.Nonempty, union_compl_self
-/
theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s.Nonempty ∧ sᶜ.Nonempty := by simpa [nonempty_iff_ne_empty] using h
      have ⟨_, h2, h3⟩ := nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) h1.1 h1.2
      h3 h2,
    by rintro (rfl | rfl); exacts [isClopen_empty, isClopen_univ]⟩

/--
theorem `IsClopen.eq_univ` / 定理 `IsClopen.eq_univ`

English:
theorem IsClopen.eq_univ
  given: [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty)
  proof: (isClopen_iff.mp h').resolve_left h.ne_empty

中文:
定理 IsClopen.eq_univ
  条件: [预连通空间 α] {s : 集合 α} (h' : IsClopen s) (h : s.非空)
  证明: (isClopen_iff.mp h').resolve_left h.ne_empty

Depends on / 依赖: h.ne_empty, isClopen_iff, isClopen_iff.mp, ne_empty, resolve_left
-/
theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty

open Set.Notation in
/--
lemma `isClopen_preimage_val` / 引理 `isClopen_preimage_val`

English:
lemma isClopen_preimage_val
  statement: {X : Type*} [TopologicalSpace X] {u v : Set X}
  proof: by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_comm _ (frontier u)]; rw [huv.inter_eq]; rw [union_empty]

中文:
引理 isClopen_preimage_val
  结论: {X : 类型} [拓扑空间 X] {u v : 集合 X}
  证明: by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_comm _ (frontier u)]; rw [huv.inter_eq]; rw [union_empty]

Depends on / 依赖: Subtype, Subtype.image_preimage_coe, Subtype.val, closure, closure_eq_self_union_frontier, frontier, huv.inter_eq, image_preimage_coe, image_val_injective, inter_comm, inter_eq, inter_union_distrib_left, isClosed_closure, isClosed_induced_iff, isClosed_induced_iff.mpr, isOpen_induced, union_empty
-/
lemma isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (v ↓inter u) := by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier]; rw [inter_union_distrib_left]; rw [inter_comm _ (frontier u)]; rw [huv.inter_eq]; rw [union_empty]

section disjoint_subsets

variable [PreconnectedSpace α]
  {s : ι -> Set α} (h_nonempty : forall i, (s i).Nonempty) (h_disj : Pairwise (Disjoint on s))
include h_nonempty h_disj

/--
lemma `subsingleton_of_disjoint_isClopen` / 引理 `subsingleton_of_disjoint_isClopen`

English:
lemma subsingleton_of_disjoint_isClopen
  proof: by
  rw [← not_nontrivial_iff_subsingleton]
  by_contra ⟨i, j, h_ne⟩
  replace h_ne : s i inter s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact (h_nonempty i).ne_empty hi
  · rw [hi, univ_inter] at h_ne
    exact (h_nonempty j).ne_empty h_ne

中文:
引理 subsingleton_of_disjoint_isClopen
  证明: by
  rw [← not_nontrivial_iff_subsingleton]
  by_contra ⟨i, j, h_ne⟩
  replace h_ne : s i inter s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact (h_nonempty i).ne_empty hi
  · rw [hi, univ_inter] at h_ne
    exact (h_nonempty j).ne_empty h_ne

Depends on / 依赖: bot_eq_empty, disjoint_iff_inf_le, eq_bot_iff, h_clopen, h_disj, h_ne, h_nonempty, inf_eq_inter, isClopen_iff, isClopen_iff.mp, ne_empty, not_nontrivial_iff_subsingleton, replace, univ_inter
-/
lemma subsingleton_of_disjoint_isClopen
    (h_clopen : forall i, IsClopen (s i)) :
    Subsingleton ι := by
  rw [← not_nontrivial_iff_subsingleton]
  by_contra ⟨i, j, h_ne⟩
  replace h_ne : s i inter s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  rcases isClopen_iff.mp (h_clopen i) with hi | hi
  · exact (h_nonempty i).ne_empty hi
  · rw [hi, univ_inter] at h_ne
    exact (h_nonempty j).ne_empty h_ne

/--
lemma `subsingleton_of_disjoint_isOpen_iUnion_eq_univ` / 引理 `subsingleton_of_disjoint_isOpen_iUnion_eq_univ`

English:
lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
  proof: by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isOpen_iUnion (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

中文:
引理 subsingleton_of_disjoint_isOpen_iUnion_eq_univ
  证明: by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isOpen_iUnion (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

Depends on / 依赖: compl_eq_univ_sdiff, eq_or_ne, h_Union, h_disj, h_ne, h_ne.symm, h_nonempty, h_open, iUnion_sdiff, isOpen_compl_iff, isOpen_iUnion, sdiff_eq_left, subsingleton_of_disjoint_isClopen
-/
lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    (h_open : forall i, IsOpen (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isOpen_iUnion (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

/--
lemma `subsingleton_of_disjoint_isClosed_iUnion_eq_univ` / 引理 `subsingleton_of_disjoint_isClosed_iUnion_eq_univ`

English:
lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ
  statement: [Finite ι]
  proof: by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isClosed_iUnion_of_finite (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

中文:
引理 subsingleton_of_disjoint_isClosed_iUnion_eq_univ
  结论: [有限 ι]
  证明: by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isClosed_iUnion_of_finite (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

Depends on / 依赖: compl_eq_univ_sdiff, eq_or_ne, h_Union, h_closed, h_disj, h_ne, h_ne.symm, h_nonempty, iUnion_sdiff, isClosed_compl_iff, isClosed_iUnion_of_finite, sdiff_eq_left, subsingleton_of_disjoint_isClopen
-/
lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι]
    (h_closed : forall i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i => ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff]; rw [compl_eq_univ_sdiff]; rw [← h_Union]; rw [iUnion_sdiff]
  refine isClosed_iUnion_of_finite (fun j => ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

end disjoint_subsets

/--
theorem `frontier_eq_empty_iff` / 定理 `frontier_eq_empty_iff`

English:
theorem frontier_eq_empty_iff
  given: [PreconnectedSpace α] {s : Set α}
  proof: isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

中文:
定理 frontier_eq_empty_iff
  条件: [预连通空间 α] {s : 集合 α}
  证明: isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

Depends on / 依赖: isClopen_iff, isClopen_iff_frontier_eq_empty, isClopen_iff_frontier_eq_empty.symm.trans
-/
theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

/--
theorem `nonempty_frontier_iff` / 定理 `nonempty_frontier_iff`

English:
theorem nonempty_frontier_iff
  given: [PreconnectedSpace α] {s : Set α}
  proof: by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

中文:
定理 nonempty_frontier_iff
  条件: [预连通空间 α] {s : 集合 α}
  证明: by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

Depends on / 依赖: frontier_eq_empty_iff, nonempty_iff_ne_empty, not_or
-/
theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s != univ := by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

/--
lemma `PreconnectedSpace.induction₂'` / 引理 `PreconnectedSpace.induction₂'`

English:
lemma PreconnectedSpace.induction₂'
  statement: [PreconnectedSpace α] (P : α -> α -> Prop)
  proof: by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz => ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h'.trans x t z h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz => ?_)
    filter_upwards [h z] with t ht
    exact h'.trans x z t hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y in u
  simp [D]

中文:
引理 预连通空间.induction₂'
  结论: [预连通空间 α] (P : α -> α -> 命题)
  证明: by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz => ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h'.trans x t z h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz => ?_)
    filter_upwards [h z] with t ht
    exact h'.trans x z t hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y in u
  simp [D]

Depends on / 依赖: IsClopen, IsClopen.eq_univ, IsClosed, IsOpen, Nonempty, Set.univ, eq_univ, filter_upwards, isClosed_iff_nhds, isOpen_iff_mem_nhds, mem_of_mem_nhds, u.Nonempty
-/
lemma PreconnectedSpace.induction₂' [PreconnectedSpace α] (P : α -> α -> Prop)
    (h : forall x, forallᶠ y in 𝓝 x, P x y ∧ P y x) (h' : IsTrans α P) (x y : α) :
    P x y := by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz => ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h'.trans x t z h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz => ?_)
    filter_upwards [h z] with t ht
    exact h'.trans x z t hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  change y in u
  simp [D]

/--
lemma `PreconnectedSpace.induction₂` / 引理 `PreconnectedSpace.induction₂`

English:
lemma PreconnectedSpace.induction₂
  statement: [PreconnectedSpace α] (P : α -> α -> Prop) [Std.Symm P]
  proof: by
  refine PreconnectedSpace.induction₂' P (fun z => ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, symm ha⟩

中文:
引理 预连通空间.induction₂
  结论: [预连通空间 α] (P : α -> α -> 命题) [Std.Symm P]
  证明: by
  refine PreconnectedSpace.induction₂' P (fun z => ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, symm ha⟩

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.induction, filter_upwards
-/
lemma PreconnectedSpace.induction₂ [PreconnectedSpace α] (P : α -> α -> Prop) [Std.Symm P]
    (h : forall x, forallᶠ y in 𝓝 x, P x y) (h' : IsTrans α P) (x y : α) : P x y := by
  refine PreconnectedSpace.induction₂' P (fun z => ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, symm ha⟩

/--
lemma `IsPreconnected.induction₂'` / 引理 `IsPreconnected.induction₂'`

English:
lemma IsPreconnected.induction₂'
  statement: {s : Set α} (hs : IsPreconnected s) (P : α -> α -> Prop)
  proof: by
  let Q : s -> s -> Prop := fun a b => P a b
  change Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · exact ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ => h' a b c ha hb hc⟩

中文:
引理 是预连通.induction₂'
  结论: {s : 集合 α} (hs : 是预连通 s) (P : α -> α -> 命题)
  证明: by
  let Q : s -> s -> Prop := fun a b => P a b
  change Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · exact ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ => h' a b c ha hb hc⟩

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.induction, Subtype, Subtype.preconnectedSpace, nhdsWithin_eq_map_subtype_coe, preconnectedSpace
-/
lemma IsPreconnected.induction₂' {s : Set α} (hs : IsPreconnected s) (P : α -> α -> Prop)
    (h : forall x in s, forallᶠ y in 𝓝[s] x, P x y ∧ P y x)
    (h' : forall x y z, x in s -> y in s -> z in s -> P x y -> P y z -> P x z)
    {x y : α} (hx : x in s) (hy : y in s) : P x y := by
  let Q : s -> s -> Prop := fun a b => P a b
  change Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · exact ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ => h' a b c ha hb hc⟩

/--
lemma `IsPreconnected.induction₂` / 引理 `IsPreconnected.induction₂`

English:
lemma IsPreconnected.induction₂
  statement: {s : Set α} (hs : IsPreconnected s) (P : α -> α -> Prop)
  proof: by
  apply hs.induction₂' P (fun z hz => ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

中文:
引理 是预连通.induction₂
  结论: {s : 集合 α} (hs : 是预连通 s) (P : α -> α -> 命题)
  证明: by
  apply hs.induction₂' P (fun z hz => ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

Depends on / 依赖: filter_upwards, hs.induction, self_mem_nhdsWithin
-/
lemma IsPreconnected.induction₂ {s : Set α} (hs : IsPreconnected s) (P : α -> α -> Prop)
    (h : forall x in s, forallᶠ y in 𝓝[s] x, P x y)
    (h' : forall x y z, x in s -> y in s -> z in s -> P x y -> P y z -> P x z)
    (h'' : forall x y, x in s -> y in s -> P x y -> P y x)
    {x y : α} (hx : x in s) (hy : y in s) : P x y := by
  apply hs.induction₂' P (fun z hz => ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

/--
theorem `isPreconnected_iff_subset_of_disjoint` / 定理 `isPreconnected_iff_subset_of_disjoint`

English:
theorem isPreconnected_iff_subset_of_disjoint
  given: {s : Set α}
  proof: by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

中文:
定理 isPreconnected_iff_subset_of_disjoint
  条件: {s : 集合 α}
  证明: by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

Depends on / 依赖: Set.not_nonempty_iff_eq_empty.mp, contrapose, not_nonempty_iff_eq_empty, not_subset, or_iff_not_imp_left, or_iff_not_imp_left.mp, or_iff_not_imp_right, or_iff_not_imp_right.mp, specialize
-/
theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      forall u v, IsOpen u -> IsOpen v -> s subseteq u union v -> s inter (u inter v) = ∅ -> s subseteq u ∨ s subseteq v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/--
theorem `isConnected_iff_sUnion_disjoint_open` / 定理 `isConnected_iff_sUnion_disjoint_open`

English:
theorem isConnected_iff_sUnion_disjoint_open
  given: {s : Set α}
  proof: by
  rw [IsConnected]; rw [isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

中文:
定理 isConnected_iff_sUnion_disjoint_open
  条件: {s : 集合 α}
  证明: by
  rw [IsConnected]; rw [isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

Depends on / 依赖: Finset, Finset.coe_insert, Finset.exists_mem_insert, Finset.forall_mem_insert, Finset.induction_on, IsConnected, absurd, coe_insert, exists_mem_insert, forall_cond_comm, forall_mem_insert, hne.not_subset_empty, imp_right, implies_true, induction_on, insert, isOpen_sUnion, isPreconnected_iff_subset_of_disjoint, not_subset_empty, sUnion_insert
-/
theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      forall U : Finset (Set α), (forall u v : Set α, u in U -> v in U -> (s inter (u inter v)).Nonempty -> u = v) ->
        (forall u in U, IsOpen u) -> (s subseteq ⋃₀ ↑U) -> exists u in U, s subseteq u := by
  rw [IsConnected]; rw [isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

/--
theorem `disjoint_or_subset_of_isClopen` / 定理 `disjoint_or_subset_of_isClopen`

English:
theorem disjoint_or_subset_of_isClopen
  given: {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
  proof: (disjoint_or_nonempty_inter s t).imp_right hs.subset_isClopen ht

中文:
定理 disjoint_or_subset_of_isClopen
  条件: {s t : 集合 α} (hs : 是预连通 s) (ht : IsClopen t)
  证明: (disjoint_or_nonempty_inter s t).imp_right hs.subset_isClopen ht

Depends on / 依赖: disjoint_or_nonempty_inter, hs.subset_isClopen, imp_right, subset_isClopen
-/
theorem disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s subseteq t :=
(disjoint_or_nonempty_inter s t).imp_right hs.subset_isClopen ht

/--
theorem `isPreconnected_iff_subset_of_disjoint_closed` / 定理 `isPreconnected_iff_subset_of_disjoint_closed`

English:
theorem isPreconnected_iff_subset_of_disjoint_closed
  proof: by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

中文:
定理 isPreconnected_iff_subset_of_disjoint_closed
  证明: by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

Depends on / 依赖: Set.not_nonempty_iff_eq_empty.mp, contrapose, isPreconnected_closed_iff, not_nonempty_iff_eq_empty, not_subset, or_iff_not_imp_left, or_iff_not_imp_left.mp, or_iff_not_imp_right, or_iff_not_imp_right.mp, specialize
-/
theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      forall u v, IsClosed u -> IsClosed v -> s subseteq u union v -> s inter (u inter v) = ∅ -> s subseteq u ∨ s subseteq v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp only [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x in v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y in u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    rcases h with h | h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/--
theorem `isPreconnected_iff_subset_of_fully_disjoint_closed` / 定理 `isPreconnected_iff_subset_of_fully_disjoint_closed`

English:
theorem isPreconnected_iff_subset_of_fully_disjoint_closed
  given: {s : Set α} (hs : IsClosed s)
  proof: by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq]; rw [inter_empty]
  have H1 := H (u inter s) (v inter s)
  rw [subset_inter_iff]; rw [subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

中文:
定理 isPreconnected_iff_subset_of_fully_disjoint_closed
  条件: {s : 集合 α} (hs : 是闭集 s)
  证明: by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq]; rw [inter_empty]
  have H1 := H (u inter s) (v inter s)
  rw [subset_inter_iff]; rw [subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

Depends on / 依赖: Subset, Subset.refl, Subset.rfl, and_true, disjoint_iff_inter_eq_empty, hu.inter, huv.inter_eq, hv.inter, inter_comm, inter_empty, inter_eq, inter_inter_distrib_right, isPreconnected_iff_subset_of_disjoint_closed, isPreconnected_iff_subset_of_disjoint_closed.trans, subset_inter, subset_inter_iff, union_inter_distrib_right
-/
theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      forall u v, IsClosed u -> IsClosed v -> s subseteq u union v -> Disjoint u v -> s subseteq u ∨ s subseteq v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq]; rw [inter_empty]
  have H1 := H (u inter s) (v inter s)
  rw [subset_inter_iff]; rw [subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

/--
lemma `IsClopen.isPreconnected_iff` / 引理 `IsClopen.isPreconnected_iff`

English:
lemma IsClopen.isPreconnected_iff
  given: {s : Set α} (hs : IsClopen s)
  proof: by
  refine ⟨?_, fun H a b ha hb hsab hsa hsb => ?_⟩
  · contrapose!
    rintro ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ H
    exact (H a b ha.isOpen hb.isOpen subset_rfl (by rwa [union_inter_cancel_left])
      (by rwa [union_inter_cancel_right])).ne_empty (by grind)
  · rw [nonempty_iff_ne_empty]
    intro h
    exact H (s inter a) (s inter b)
      (isClopen_inter_of_disjoint_cover_clopen' hs hsab ha hb (by grind))
      (isClopen_inter_of_disjoint_cover_clopen' hs (by grind) hb ha (by grind))
      hsa hsb (by grind [Set.disjoint_iff_inter_eq_empty]) (by grind)

中文:
引理 IsClopen.isPreconnected_iff
  条件: {s : 集合 α} (hs : IsClopen s)
  证明: by
  refine ⟨?_, fun H a b ha hb hsab hsa hsb => ?_⟩
  · contrapose!
    rintro ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ H
    exact (H a b ha.isOpen hb.isOpen subset_rfl (by rwa [union_inter_cancel_left])
      (by rwa [union_inter_cancel_right])).ne_empty (by grind)
  · rw [nonempty_iff_ne_empty]
    intro h
    exact H (s inter a) (s inter b)
      (isClopen_inter_of_disjoint_cover_clopen' hs hsab ha hb (by grind))
      (isClopen_inter_of_disjoint_cover_clopen' hs (by grind) hb ha (by grind))
      hsa hsb (by grind [Set.disjoint_iff_inter_eq_empty]) (by grind)

Depends on / 依赖: Set.disjoint_iff_inter_eq, contrapose, disjoint_iff_inter_eq, ha.isOpen, hb.isOpen, isClopen_inter_of_disjoint_cover_clopen, isOpen, ne_empty, nonempty_iff_ne_empty, subset_rfl, union_inter_cancel_left, union_inter_cancel_right
-/
lemma IsClopen.isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    IsPreconnected s ↔
      forall a b, IsClopen a -> IsClopen b -> a.Nonempty -> b.Nonempty -> Disjoint a b -> s != a union b := by
  refine ⟨?_, fun H a b ha hb hsab hsa hsb => ?_⟩
  · contrapose!
    rintro ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ H
    exact (H a b ha.isOpen hb.isOpen subset_rfl (by rwa [union_inter_cancel_left])
      (by rwa [union_inter_cancel_right])).ne_empty (by grind)
  · rw [nonempty_iff_ne_empty]
    intro h
    exact H (s inter a) (s inter b)
      (isClopen_inter_of_disjoint_cover_clopen' hs hsab ha hb (by grind))
      (isClopen_inter_of_disjoint_cover_clopen' hs (by grind) hb ha (by grind))
      hsa hsb (by grind [Set.disjoint_iff_inter_eq_empty]) (by grind)

/--
lemma `IsClopen.not_isPreconnected_iff` / 引理 `IsClopen.not_isPreconnected_iff`

English:
lemma IsClopen.not_isPreconnected_iff
  given: {s : Set α} (hs : IsClopen s)
  proof: by
  simp [hs.isPreconnected_iff]

中文:
引理 IsClopen.not_isPreconnected_iff
  条件: {s : 集合 α} (hs : IsClopen s)
  证明: by
  simp [hs.isPreconnected_iff]

Depends on / 依赖: hs.isPreconnected_iff, isPreconnected_iff
-/
lemma IsClopen.not_isPreconnected_iff {s : Set α} (hs : IsClopen s) :
    ¬ IsPreconnected s ↔
      exists a b, IsClopen a ∧ IsClopen b ∧ a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ s = a union b := by
  simp [hs.isPreconnected_iff]

/--
theorem `IsClopen.connectedComponent_subset` / 定理 `IsClopen.connectedComponent_subset`

English:
theorem IsClopen.connectedComponent_subset
  given: {x} (hs : IsClopen s) (hx : x in s)
  proof: isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

中文:
定理 IsClopen.connectedComponent_subset
  条件: {x} (hs : IsClopen s) (hx : x in s)
  证明: isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

Depends on / 依赖: isPreconnected_connectedComponent, isPreconnected_connectedComponent.subset_isClopen, mem_connectedComponent, subset_isClopen
-/
theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x in s) :
    connectedComponent x subseteq s :=
  isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

/--
theorem `connectedComponent_subset_iInter_isClopen` / 定理 `connectedComponent_subset_iInter_isClopen`

English:
theorem connectedComponent_subset_iInter_isClopen
  given: {x : α}
  proof: subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

中文:
定理 connectedComponent_subset_i整数er_isClopen
  条件: {x : α}
  证明: subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

Depends on / 依赖: connectedComponent_subset, subset_iInter
-/
theorem connectedComponent_subset_iInter_isClopen {x : α} :
    connectedComponent x subseteq ⋂ Z : { Z : Set α // IsClopen Z ∧ x in Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

/--
theorem `IsClopen.biUnion_connectedComponent_eq` / 定理 `IsClopen.biUnion_connectedComponent_eq`

English:
theorem IsClopen.biUnion_connectedComponent_eq
  given: {Z : Set α} (h : IsClopen Z)
  proof: Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

中文:
定理 IsClopen.biUnion_connectedComponent_eq
  条件: {Z : 集合 α} (h : IsClopen Z)
  证明: Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

Depends on / 依赖: Subset, Subset.antisymm, antisymm, connectedComponent_subset, h.connectedComponent_subset, mem_connectedComponent
-/
theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    ⋃ x in Z, connectedComponent x = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

open Set.Notation in
/--
lemma `IsClopen.biUnion_connectedComponentIn` / 引理 `IsClopen.biUnion_connectedComponentIn`

English:
lemma IsClopen.biUnion_connectedComponentIn
  statement: {X : Type*} [TopologicalSpace X] {u v : Set X}
  proof: by
  have := congr(((↑) : Set v -> Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
exact le_antisymm (iUnion_subset fun _ => le_rfl)
    iUnion_subset fun hx => subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

中文:
引理 IsClopen.biUnion_connectedComponentIn
  结论: {X : 类型} [拓扑空间 X] {u v : 集合 X}
  证明: by
  have := congr(((↑) : Set v -> Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
exact le_antisymm (iUnion_subset fun _ => le_rfl)
    iUnion_subset fun hx => subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

Depends on / 依赖: Subtype, Subtype.image_preimage_coe, biUnion_connectedComponent_eq, connectedComponentIn_eq_image, hu.biUnion_connectedComponent_eq.symm, iUnion_coe_set, iUnion_subset, image_preimage_coe, image_val_iUnion, inter_eq_right, inter_eq_right.mpr, le_antisymm, le_rfl, mem_preimage, nth_rw
-/
lemma IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsClopen (v ↓inter u)) (huv₁ : u subseteq v) :
    u = ⋃ x in u, connectedComponentIn v x := by
  have := congr(((↑) : Set v -> Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion,
    inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
exact le_antisymm (iUnion_subset fun _ => le_rfl)
    iUnion_subset fun hx => subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

/--
lemma `IsClopen.connectedComponentIn_eq` / 引理 `IsClopen.connectedComponentIn_eq`

English:
lemma IsClopen.connectedComponentIn_eq
  given: {U : Set α} (hU : IsClopen U) {x : α} (hx : x in U)
  proof: subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

中文:
引理 IsClopen.connectedComponentIn_eq
  条件: {U : 集合 α} (hU : IsClopen U) {x : α} (hx : x in U)
  证明: subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

Depends on / 依赖: connectedComponent_subset, hU.connectedComponent_subset, isPreconnected_connectedComponent, isPreconnected_connectedComponentIn, mem_connectedComponent, mem_connectedComponentIn, subset_antisymm, subset_connectedComponent, subset_connectedComponentIn
-/
lemma IsClopen.connectedComponentIn_eq {U : Set α} (hU : IsClopen U) {x : α} (hx : x in U) :
    connectedComponentIn U x = connectedComponent x :=
  subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

variable [TopologicalSpace β] {f : α -> β}

/--
theorem `Topology.IsCoinducing.isConnected_preimage_of_isClosed` / 定理 `Topology.IsCoinducing.isConnected_preimage_of_isClosed`

English:
theorem Topology.IsCoinducing.isConnected_preimage_of_isClosed
  proof: by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' in t | f ⁻¹' {t'} subseteq u }
  let T₂ := { t' in t | f ⁻¹' {t'} subseteq v }
  have fiber_decomp : forall t' in t, f ⁻¹' {t'} subseteq u ∨ f ⁻¹' {t'} subseteq v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq]; rw [inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t inter u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t inter v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t subseteq T₁ union T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u]; rw [T₂_v]; rw [disjoint_iff_inter_eq_empty]; rw [← inter_inter_distrib_left]; rw [uv_disj.inter_eq]; rw [inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t subseteq f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t subseteq f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

@[deprecated Topology.IsCoinducing.isConnected_preimage_of_isClosed (since := "2026-04-01")]

中文:
定理 拓扑.是余inducing.isConnected_preimage_of_isClosed
  证明: by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' in t | f ⁻¹' {t'} subseteq u }
  let T₂ := { t' in t | f ⁻¹' {t'} subseteq v }
  have fiber_decomp : forall t' in t, f ⁻¹' {t'} subseteq u ∨ f ⁻¹' {t'} subseteq v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq]; rw [inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t inter u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t inter v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t subseteq T₁ union T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u]; rw [T₂_v]; rw [disjoint_iff_inter_eq_empty]; rw [← inter_inter_distrib_left]; rw [uv_disj.inter_eq]; rw [inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t subseteq f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t subseteq f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

@[deprecated Topology.IsCoinducing.isConnected_preimage_of_isClosed (since := "2026-04-01")]
-/
theorem Topology.IsCoinducing.isConnected_preimage_of_isClosed
    (connected_fibers : forall t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) {t : Set β} (ht : IsClosed t) (ht' : IsConnected t) :
    IsConnected (f ⁻¹' t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' in t | f ⁻¹' {t'} subseteq u }
  let T₂ := { t' in t | f ⁻¹' {t'} subseteq v }
  have fiber_decomp : forall t' in t, f ⁻¹' {t'} subseteq u ∨ f ⁻¹' {t'} subseteq v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq]; rw [inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t inter u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t inter v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff]; rw [singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t subseteq T₁ union T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u]; rw [T₂_v]; rw [disjoint_iff_inter_eq_empty]; rw [← inter_inter_distrib_left]; rw [uv_disj.inter_eq]; rw [inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t subseteq f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t subseteq f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

@[deprecated Topology.IsCoinducing.isConnected_preimage_of_isClosed (since := "2026-04-01")]
/--
theorem `preimage_connectedComponent_connected` / 定理 `preimage_connectedComponent_connected`

English:
theorem preimage_connectedComponent_connected
  statement: (connected_fibers : forall t : β, IsConnected (f ⁻¹' {t}))
  proof: by
  apply hcl.isConnected_preimage_of_isClosed
  · exact isClosed_connectedComponent
  · exact isConnected_connectedComponent
  · exact connected_fibers

中文:
定理 preimage_connectedComponent_connected
  结论: (connected_fibers : 对任意 t : β, 是连通 (f ⁻¹' {t}))
  证明: by
  apply hcl.isConnected_preimage_of_isClosed
  · exact isClosed_connectedComponent
  · exact isConnected_connectedComponent
  · exact connected_fibers

Depends on / 依赖: connected_fibers, hcl.isConnected_preimage_of_isClosed, isClosed_connectedComponent, isConnected_connectedComponent, isConnected_preimage_of_isClosed
-/
theorem preimage_connectedComponent_connected (connected_fibers : forall t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) (t : β) :
    IsConnected (f ⁻¹' connectedComponent t) := by
  apply hcl.isConnected_preimage_of_isClosed
  · exact isClosed_connectedComponent
  · exact isConnected_connectedComponent
  · exact connected_fibers

/--
theorem `Topology.IsCoinducing.preimage_connectedComponent` / 定理 `Topology.IsCoinducing.preimage_connectedComponent`

English:
theorem Topology.IsCoinducing.preimage_connectedComponent
  statement: (hf : IsCoinducing f)
  proof: ((hf.isConnected_preimage_of_isClosed h_fibers isClosed_connectedComponent
    isConnected_connectedComponent).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)

中文:
定理 拓扑.是余inducing.preimage_connectedComponent
  结论: (hf : 是余inducing f)
  证明: ((hf.isConnected_preimage_of_isClosed h_fibers isClosed_connectedComponent
    isConnected_connectedComponent).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)

Depends on / 依赖: antisymm, continuous, h_fibers, hf.continuous.mapsTo_connectedComponent, hf.isConnected_preimage_of_isClosed, isClosed_connectedComponent, isConnected_connectedComponent, isConnected_preimage_of_isClosed, mapsTo_connectedComponent, mem_connectedComponent, subset_connectedComponent
-/
theorem Topology.IsCoinducing.preimage_connectedComponent (hf : IsCoinducing f)
    (h_fibers : forall y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f ⁻¹' connectedComponent (f a) = connectedComponent a :=
  ((hf.isConnected_preimage_of_isClosed h_fibers isClosed_connectedComponent
    isConnected_connectedComponent).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)

/--
lemma `Topology.IsCoinducing.image_connectedComponent` / 引理 `Topology.IsCoinducing.image_connectedComponent`

English:
lemma Topology.IsCoinducing.image_connectedComponent
  statement: {f : α -> β} (hf : IsCoinducing f)
  proof: by
  rw [← hf.preimage_connectedComponent h_fibers]; rw [image_preimage_eq _ fun y => (h_fibers y).nonempty]

中文:
引理 拓扑.是余inducing.image_connectedComponent
  结论: {f : α -> β} (hf : 是余inducing f)
  证明: by
  rw [← hf.preimage_connectedComponent h_fibers]; rw [image_preimage_eq _ fun y => (h_fibers y).nonempty]

Depends on / 依赖: h_fibers, hf.preimage_connectedComponent, image_preimage_eq, nonempty, preimage_connectedComponent
-/
lemma Topology.IsCoinducing.image_connectedComponent {f : α -> β} (hf : IsCoinducing f)
    (h_fibers : forall y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f '' connectedComponent a = connectedComponent (f a) := by
  rw [← hf.preimage_connectedComponent h_fibers]; rw [image_preimage_eq _ fun y => (h_fibers y).nonempty]

end Preconnected

section connectedComponentSetoid
/-- The setoid of connected components of a topological space -/
@[instance_reducible]
/--
Definition of `connectedComponentSetoid` / `connectedComponentSetoid` 的定义

English:
definition connectedComponentSetoid
  signature: (α : Type*) [TopologicalSpace α]
  body: ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

中文:
定义 connectedComponentSetoid
  签名: (α : 类型) [拓扑空间 α]
  定义体: ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

Depends on / 依赖: connectedComponent, h1.symm, h1.trans
-/
def connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

/--
Definition of `ConnectedComponents` / `ConnectedComponents` 的定义

English:
definition ConnectedComponents
  signature: (α : Type u) [TopologicalSpace α]
  body: Quotient (connectedComponentSetoid α)

中文:
定义 ConnectedComponents
  签名: (α : 类型u) [拓扑空间 α]
  定义体: Quotient (connectedComponentSetoid α)

Depends on / 依赖: Quotient, connectedComponentSetoid
-/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)

namespace ConnectedComponents

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : α -> ConnectedComponents α
  body: Quotient.mk''

中文:
定义 mk
  签名: : α -> ConnectedComponents α
  定义体: Quotient.mk''
-/
def mk : α -> ConnectedComponents α := Quotient.mk''

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC α (ConnectedComponents α)
  body: ⟨mk⟩

@[simp]

中文:
实例 :
  签名: CoeTC α (ConnectedComponents α)
  定义体: ⟨mk⟩

@[simp]
-/
instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {x y : α}
  proof: Quotient.eq''

中文:
定理 coe_eq_coe
  条件: {x y : α}
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''

/--
theorem `coe_ne_coe` / 定理 `coe_ne_coe`

English:
theorem coe_ne_coe
  given: {x y : α}
  proof: coe_eq_coe.not

中文:
定理 coe_ne_coe
  条件: {x y : α}
  证明: coe_eq_coe.not

Depends on / 依赖: coe_eq_coe, coe_eq_coe.not
-/
theorem coe_ne_coe {x y : α} :
    (x : ConnectedComponents α) != y ↔ connectedComponent x != connectedComponent y :=
  coe_eq_coe.not

/--
theorem `coe_eq_coe'` / 定理 `coe_eq_coe'`

English:
theorem coe_eq_coe'
  given: {x y : α}
  statement: (x : ConnectedComponents α) = y ↔ x in connectedComponent y
  proof: coe_eq_coe.trans connectedComponent_eq_iff_mem

中文:
定理 coe_eq_coe'
  条件: {x y : α}
  结论: (x : ConnectedComponents α) = y ↔ x in connectedComponent y
  证明: coe_eq_coe.trans connectedComponent_eq_iff_mem

Depends on / 依赖: coe_eq_coe, coe_eq_coe.trans, connectedComponent_eq_iff_mem
-/
theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x in connectedComponent y :=
  coe_eq_coe.trans connectedComponent_eq_iff_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (ConnectedComponents α)
  body: ⟨mk default⟩

中文:
实例 [可居
  签名: α] : 可居 (ConnectedComponents α)
  定义体: ⟨mk default⟩
-/
instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨mk default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (ConnectedComponents α)
  body: inferInstanceAs (TopologicalSpace (Quotient _))

中文:
实例 :
  签名: 拓扑空间 (ConnectedComponents α)
  定义体: inferInstanceAs (TopologicalSpace (Quotient _))

Depends on / 依赖: Quotient, TopologicalSpace
-/
instance : TopologicalSpace (ConnectedComponents α) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/--
theorem `surjective_coe` / 定理 `surjective_coe`

English:
theorem surjective_coe
  statement: Surjective (mk : α -> ConnectedComponents α)
  proof: Quot.mk_surjective

中文:
定理 surjective_coe
  结论: 满射 (mk : α -> ConnectedComponents α)
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem surjective_coe : Surjective (mk : α -> ConnectedComponents α) :=
  Quot.mk_surjective

/--
theorem `isQuotientMap_coe` / 定理 `isQuotientMap_coe`

English:
theorem isQuotientMap_coe
  statement: IsQuotientMap (mk : α -> ConnectedComponents α)
  proof: isQuotientMap_quot_mk

@[continuity]

中文:
定理 isQuotientMap_coe
  结论: 是商映射 (mk : α -> ConnectedComponents α)
  证明: isQuotientMap_quot_mk

@[continuity]

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_coe : IsQuotientMap (mk : α -> ConnectedComponents α) :=
  isQuotientMap_quot_mk

@[continuity]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous (mk : α -> ConnectedComponents α)
  proof: isQuotientMap_coe.continuous

@[simp]

中文:
定理 continuous_coe
  结论: 连续 (mk : α -> ConnectedComponents α)
  证明: isQuotientMap_coe.continuous

@[simp]

Depends on / 依赖: continuous, isQuotientMap_coe, isQuotientMap_coe.continuous
-/
theorem continuous_coe : Continuous (mk : α -> ConnectedComponents α) :=
  isQuotientMap_coe.continuous

@[simp]
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range (mk : α -> ConnectedComponents α) = univ
  proof: surjective_coe.range_eq

中文:
定理 range_coe
  结论: range (mk : α -> ConnectedComponents α) = univ
  证明: surjective_coe.range_eq

Depends on / 依赖: range_eq, surjective_coe, surjective_coe.range_eq
-/
theorem range_coe : range (mk : α -> ConnectedComponents α) = univ :=
  surjective_coe.range_eq

/--
lemma `nonempty_iff_nonempty` / 引理 `nonempty_iff_nonempty`

English:
lemma nonempty_iff_nonempty
  statement: Nonempty (ConnectedComponents α) ↔ Nonempty α
  proof: ⟨fun _ => ConnectedComponents.surjective_coe.nonempty, fun h => h.map ConnectedComponents.mk⟩

中文:
引理 nonempty_iff_nonempty
  结论: 非空 (ConnectedComponents α) ↔ 非空 α
  证明: ⟨fun _ => ConnectedComponents.surjective_coe.nonempty, fun h => h.map ConnectedComponents.mk⟩

Depends on / 依赖: ConnectedComponents, ConnectedComponents.mk, ConnectedComponents.surjective_coe.nonempty, h.map, nonempty, surjective_coe
-/
lemma nonempty_iff_nonempty : Nonempty (ConnectedComponents α) ↔ Nonempty α :=
  ⟨fun _ => ConnectedComponents.surjective_coe.nonempty, fun h => h.map ConnectedComponents.mk⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (ConnectedComponents α)
  body: by
  rwa [ConnectedComponents.nonempty_iff_nonempty]

中文:
实例 [非空
  签名: α] : 非空 (ConnectedComponents α)
  定义体: by
  rwa [ConnectedComponents.nonempty_iff_nonempty]

Depends on / 依赖: ConnectedComponents, ConnectedComponents.nonempty_iff_nonempty, nonempty_iff_nonempty
-/
instance [Nonempty α] : Nonempty (ConnectedComponents α) := by
  rwa [ConnectedComponents.nonempty_iff_nonempty]

/--
lemma `isEmpty_iff_isEmpty` / 引理 `isEmpty_iff_isEmpty`

English:
lemma isEmpty_iff_isEmpty
  statement: IsEmpty (ConnectedComponents α) ↔ IsEmpty α
  proof: by
  rw [← not_iff_not]; rw [not_isEmpty_iff]; rw [not_isEmpty_iff]; rw [nonempty_iff_nonempty]

中文:
引理 isEmpty_iff_isEmpty
  结论: 是空 (ConnectedComponents α) ↔ 是空 α
  证明: by
  rw [← not_iff_not]; rw [not_isEmpty_iff]; rw [not_isEmpty_iff]; rw [nonempty_iff_nonempty]

Depends on / 依赖: nonempty_iff_nonempty, not_iff_not, not_isEmpty_iff
-/
lemma isEmpty_iff_isEmpty : IsEmpty (ConnectedComponents α) ↔ IsEmpty α := by
  rw [← not_iff_not]; rw [not_isEmpty_iff]; rw [not_isEmpty_iff]; rw [nonempty_iff_nonempty]

/--
Instance `subsingleton` / 实例 `subsingleton`

English:
instance subsingleton
  signature: [PreconnectedSpace α]
  body: by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

中文:
实例 subsingleton
  签名: [预连通空间 α]
  定义体: by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

Depends on / 依赖: PreconnectedSpace, PreconnectedSpace.connectedComponent_eq_univ, coe_eq_coe, connectedComponent_eq_univ, simp_rw, surjective_coe
-/
instance subsingleton [PreconnectedSpace α] : Subsingleton (ConnectedComponents α) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

section

variable {ι : Type*} {U : ι -> Set α} (hclopen : forall i, IsClopen (U i))
  (hdisj : Pairwise (Disjoint on U)) (hunion : ⋃ i, U i = Set.univ)
  (hconn : forall i, IsPreconnected (U i))

include hclopen hdisj hunion in
/--
Definition of `equivOfIsClopen` / `equivOfIsClopen` 的定义

English:
definition equivOfIsClopen
  signature: : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i)
  body: by
  haveI heq {x : α} {i} (hx : x in U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx]; rw [(hclopen i).connectedComponentIn_eq hx]
refine .symm .ofBijective
      (fun ⟨i, x⟩ =>
        x.lift (ConnectedComponents.mk ∘ Subtype.val)
          (fun x y (hxy : connectedComponent x = connectedComponent y) => by
            simp [← heq x.2, ← heq y.2, hxy]))
      ⟨fun ⟨i, x⟩ ⟨j, y⟩ => ?_, fun x => ?_⟩
  · intro hxy
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    obtain rfl : i = j := by
      apply hdisj.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hclopen j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    simp [← Set.image_val_inj, heq, hxy]
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hunion x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl

@[simp]

中文:
定义 equivOfIsClopen
  签名: : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i)
  定义体: by
  haveI heq {x : α} {i} (hx : x in U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx]; rw [(hclopen i).connectedComponentIn_eq hx]
refine .symm .ofBijective
      (fun ⟨i, x⟩ =>
        x.lift (ConnectedComponents.mk ∘ Subtype.val)
          (fun x y (hxy : connectedComponent x = connectedComponent y) => by
            simp [← heq x.2, ← heq y.2, hxy]))
      ⟨fun ⟨i, x⟩ ⟨j, y⟩ => ?_, fun x => ?_⟩
  · intro hxy
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    obtain rfl : i = j := by
      apply hdisj.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hclopen j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    simp [← Set.image_val_inj, heq, hxy]
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hunion x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl

@[simp]

Depends on / 依赖: ConnectedComponents, ConnectedComponents.mk, ConnectedComponents.surjective_coe, Subtype, Subtype.val, connectedComponent, connectedComponentIn_eq, connectedComponentIn_eq_image, hclopen, ofBijective, surjective_coe, x.lift
-/
noncomputable def equivOfIsClopen : ConnectedComponents α ≃ Σ i, ConnectedComponents (U i) := by
  haveI heq {x : α} {i} (hx : x in U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx]; rw [(hclopen i).connectedComponentIn_eq hx]
refine .symm .ofBijective
      (fun ⟨i, x⟩ =>
        x.lift (ConnectedComponents.mk ∘ Subtype.val)
          (fun x y (hxy : connectedComponent x = connectedComponent y) => by
            simp [← heq x.2, ← heq y.2, hxy]))
      ⟨fun ⟨i, x⟩ ⟨j, y⟩ => ?_, fun x => ?_⟩
  · intro hxy
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    obtain rfl : i = j := by
      apply hdisj.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hclopen j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    simp [← Set.image_val_inj, heq, hxy]
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hunion x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl

@[simp]
/--
lemma `equivOfIsClopen_symm_mk` / 引理 `equivOfIsClopen_symm_mk`

English:
lemma equivOfIsClopen_symm_mk
  given: {i : ι} (x : U i)
  proof: rfl

中文:
引理 equivOfIsClopen_symm_mk
  条件: {i : ι} (x : U i)
  证明: rfl
-/
lemma equivOfIsClopen_symm_mk {i : ι} (x : U i) :
    (equivOfIsClopen hclopen hdisj hunion).symm ⟨i, .mk x⟩ = .mk x := rfl

/--
lemma `equivOfIsClopen_mk` / 引理 `equivOfIsClopen_mk`

English:
lemma equivOfIsClopen_mk
  given: {i : ι} (x : α) (hx : x in U i)
  proof: by
  apply (equivOfIsClopen hclopen hdisj hunion).symm.injective
  simp

include hclopen hdisj hunion in

中文:
引理 equivOfIsClopen_mk
  条件: {i : ι} (x : α) (hx : x in U i)
  证明: by
  apply (equivOfIsClopen hclopen hdisj hunion).symm.injective
  simp

include hclopen hdisj hunion in

Depends on / 依赖: equivOfIsClopen, hclopen, hunion, injective, symm.injective
-/
lemma equivOfIsClopen_mk {i : ι} (x : α) (hx : x in U i) :
    equivOfIsClopen hclopen hdisj hunion (.mk x) = ⟨i, .mk ⟨x, hx⟩⟩ := by
  apply (equivOfIsClopen hclopen hdisj hunion).symm.injective
  simp

include hclopen hdisj hunion in
/--
Definition of `equivOfIsClopenOfIsConnected` / `equivOfIsClopenOfIsConnected` 的定义

English:
definition equivOfIsClopenOfIsConnected
  signature: (hconn : forall i, IsConnected (U i))
  body: have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  letI _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)

中文:
定义 equivOfIsClopenOfIsConnected
  签名: (hconn : 对任意 i, 是连通 (U i))
  定义体: have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  letI _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)

Depends on / 依赖: ConnectedComponents, ConnectedSpace, Unique, equivOfIsClopen, hclopen, hunion, isConnected_iff_connectedSpace, isConnected_iff_connectedSpace.mp, nonempty_unique, sigmaUnique
-/
noncomputable def equivOfIsClopenOfIsConnected (hconn : forall i, IsConnected (U i)) :
    ConnectedComponents α ≃ ι :=
  have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  letI _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)

/--
lemma `equivOfIsClopenOfIsConnected_mk` / 引理 `equivOfIsClopenOfIsConnected_mk`

English:
lemma equivOfIsClopenOfIsConnected_mk
  statement: (hconn : forall i, IsConnected (U i)) {i : ι} (x : α)
  proof: by
  simp [equivOfIsClopenOfIsConnected, equivOfIsClopen_mk _ _ _ _ hx]

中文:
引理 equivOfIsClopenOfIsConnected_mk
  结论: (hconn : 对任意 i, 是连通 (U i)) {i : ι} (x : α)
  证明: by
  simp [equivOfIsClopenOfIsConnected, equivOfIsClopen_mk _ _ _ _ hx]

Depends on / 依赖: equivOfIsClopenOfIsConnected, equivOfIsClopen_mk
-/
lemma equivOfIsClopenOfIsConnected_mk (hconn : forall i, IsConnected (U i)) {i : ι} (x : α)
    (hx : x in U i) :
    equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn (.mk x) = i := by
  simp [equivOfIsClopenOfIsConnected, equivOfIsClopen_mk _ _ _ _ hx]

end

variable (α) in
/--
lemma `exists_fun_isClopen_of_infinite` / 引理 `exists_fun_isClopen_of_infinite`

English:
lemma exists_fun_isClopen_of_infinite
  given: [Infinite (ConnectedComponents α)] (n : Nat) (hn : 0 < n)
  proof: by
  cases isEmpty_or_nonempty α
  · exact (not_finite (ConnectedComponents α)).elim
  obtain (_ | n) := n
  · simp at hn
  clear hn
  induction n with
  | zero => exact ⟨![.univ], by simp [isClopen_univ, Set.iUnion_fin_add_one_eq_iUnion_succ]⟩
  | succ n IH =>
    obtain ⟨U, h₁, h₂, h₃, h₄⟩ := IH
    obtain ⟨i, hi⟩ : exists i, ¬ IsConnected (U i) := by
      simp_rw [isConnected_iff_connectedSpace, ← not_forall]
      exact fun _ => not_finite_iff_infinite.mpr ‹_› (.of_equiv _ (equivOfIsClopen h₁ h₃ h₄).symm)
    obtain ⟨U, rfl⟩ := (Equiv.piCongrLeft (fun _ => Set α) (Equiv.swap 0 i)).symm.surjective U
    cases U using Fin.consCases with | cons s U =>
    simp only [Equiv.piCongrLeft_symm_apply, Equiv.swap_apply_right, Fin.cons_zero] at *
    obtain ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ := (show IsClopen s by simpa using h₁ i)
.not_isPreconnected_iff.mp (mt (⟨by simpa using h₂ i, ·⟩) hi)
    refine ⟨Fin.cons a (Fin.cons b U), ?_, ?_, ?_, ?_⟩
    · simpa [Fin.forall_iff_succ, *] using fun x => h₁ (Equiv.swap 0 i (.succ x))
    · simpa [Fin.forall_iff_succ, *] using fun x => h₂ (Equiv.swap 0 i (.succ x))
    · have h₃' (j : _) : Disjoint (U j) a ∧ Disjoint (U j) b := by
        simpa [onFun] using h₃ ((Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j))
      simpa [Pairwise, Fin.forall_iff_succ, onFun, hab, disjoint_comm (a := a),
        disjoint_comm (a := b), h₃'] using
        h₃.comp_of_injective ((Equiv.swap 0 i).injective.comp (Fin.succ_injective _))
    · simpa [← union_assoc, (Equiv.surjective _).iUnion_comp] using h₄

中文:
引理 存在_fun_isClopen_of_infinite
  条件: [无限 (ConnectedComponents α)] (n : 自然数) (hn : 0 < n)
  证明: by
  cases isEmpty_or_nonempty α
  · exact (not_finite (ConnectedComponents α)).elim
  obtain (_ | n) := n
  · simp at hn
  clear hn
  induction n with
  | zero => exact ⟨![.univ], by simp [isClopen_univ, Set.iUnion_fin_add_one_eq_iUnion_succ]⟩
  | succ n IH =>
    obtain ⟨U, h₁, h₂, h₃, h₄⟩ := IH
    obtain ⟨i, hi⟩ : exists i, ¬ IsConnected (U i) := by
      simp_rw [isConnected_iff_connectedSpace, ← not_forall]
      exact fun _ => not_finite_iff_infinite.mpr ‹_› (.of_equiv _ (equivOfIsClopen h₁ h₃ h₄).symm)
    obtain ⟨U, rfl⟩ := (Equiv.piCongrLeft (fun _ => Set α) (Equiv.swap 0 i)).symm.surjective U
    cases U using Fin.consCases with | cons s U =>
    simp only [Equiv.piCongrLeft_symm_apply, Equiv.swap_apply_right, Fin.cons_zero] at *
    obtain ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ := (show IsClopen s by simpa using h₁ i)
.not_isPreconnected_iff.mp (mt (⟨by simpa using h₂ i, ·⟩) hi)
    refine ⟨Fin.cons a (Fin.cons b U), ?_, ?_, ?_, ?_⟩
    · simpa [Fin.forall_iff_succ, *] using fun x => h₁ (Equiv.swap 0 i (.succ x))
    · simpa [Fin.forall_iff_succ, *] using fun x => h₂ (Equiv.swap 0 i (.succ x))
    · have h₃' (j : _) : Disjoint (U j) a ∧ Disjoint (U j) b := by
        simpa [onFun] using h₃ ((Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j))
      simpa [Pairwise, Fin.forall_iff_succ, onFun, hab, disjoint_comm (a := a),
        disjoint_comm (a := b), h₃'] using
        h₃.comp_of_injective ((Equiv.swap 0 i).injective.comp (Fin.succ_injective _))
    · simpa [← union_assoc, (Equiv.surjective _).iUnion_comp] using h₄

Depends on / 依赖: ConnectedComponents, IsConnected, Set.iUnion_fin_add_one_eq_iUnion_succ, equivOfIsClopen, iUnion_fin_add_one_eq_iUnion_succ, isClopen_univ, isConnected_iff_connectedSpace, isEmpty_or_nonempty, not_finite, not_finite_iff_infinite, not_finite_iff_infinite.mpr, not_forall, of_equiv, simp_rw
-/
lemma exists_fun_isClopen_of_infinite [Infinite (ConnectedComponents α)] (n : Nat) (hn : 0 < n) :
    exists (U : Fin n -> Set α), (forall i, IsClopen (U i)) ∧ (forall i, (U i).Nonempty) ∧
      Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ := by
  cases isEmpty_or_nonempty α
  · exact (not_finite (ConnectedComponents α)).elim
  obtain (_ | n) := n
  · simp at hn
  clear hn
  induction n with
  | zero => exact ⟨![.univ], by simp [isClopen_univ, Set.iUnion_fin_add_one_eq_iUnion_succ]⟩
  | succ n IH =>
    obtain ⟨U, h₁, h₂, h₃, h₄⟩ := IH
    obtain ⟨i, hi⟩ : exists i, ¬ IsConnected (U i) := by
      simp_rw [isConnected_iff_connectedSpace, ← not_forall]
      exact fun _ => not_finite_iff_infinite.mpr ‹_› (.of_equiv _ (equivOfIsClopen h₁ h₃ h₄).symm)
    obtain ⟨U, rfl⟩ := (Equiv.piCongrLeft (fun _ => Set α) (Equiv.swap 0 i)).symm.surjective U
    cases U using Fin.consCases with | cons s U =>
    simp only [Equiv.piCongrLeft_symm_apply, Equiv.swap_apply_right, Fin.cons_zero] at *
    obtain ⟨a, b, ha, hb, ha', hb', hab, rfl⟩ := (show IsClopen s by simpa using h₁ i)
.not_isPreconnected_iff.mp (mt (⟨by simpa using h₂ i, ·⟩) hi)
    refine ⟨Fin.cons a (Fin.cons b U), ?_, ?_, ?_, ?_⟩
    · simpa [Fin.forall_iff_succ, *] using fun x => h₁ (Equiv.swap 0 i (.succ x))
    · simpa [Fin.forall_iff_succ, *] using fun x => h₂ (Equiv.swap 0 i (.succ x))
    · have h₃' (j : _) : Disjoint (U j) a ∧ Disjoint (U j) b := by
        simpa [onFun] using h₃ ((Equiv.swap 0 i).injective.ne (Fin.succ_ne_zero j))
      simpa [Pairwise, Fin.forall_iff_succ, onFun, hab, disjoint_comm (a := a),
        disjoint_comm (a := b), h₃'] using
        h₃.comp_of_injective ((Equiv.swap 0 i).injective.comp (Fin.succ_injective _))
    · simpa [← union_assoc, (Equiv.surjective _).iUnion_comp] using h₄

end ConnectedComponents

/--
theorem `connectedComponents_preimage_singleton` / 定理 `connectedComponents_preimage_singleton`

English:
theorem connectedComponents_preimage_singleton
  given: {x : α}
  proof: by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [ConnectedComponents.coe_eq_coe']

中文:
定理 connectedComponents_preimage_singleton
  条件: {x : α}
  证明: by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [ConnectedComponents.coe_eq_coe']

Depends on / 依赖: ConnectedComponents, ConnectedComponents.coe_eq_coe, coe_eq_coe, mem_preimage, mem_singleton_iff
-/
theorem connectedComponents_preimage_singleton {x : α} :
    (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedComponent x := by
  ext y
  rw [mem_preimage]; rw [mem_singleton_iff]; rw [ConnectedComponents.coe_eq_coe']

/--
theorem `connectedComponents_preimage_image` / 定理 `connectedComponents_preimage_image`

English:
theorem connectedComponents_preimage_image
  given: (U : Set α)
  proof: by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]

中文:
定理 connectedComponents_preimage_image
  条件: (U : 集合 α)
  证明: by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]

Depends on / 依赖: connectedComponents_preimage_singleton, image_eq_iUnion
-/
theorem connectedComponents_preimage_image (U : Set α) :
    (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x in U, connectedComponent x := by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]

/--
lemma `ConnectedComponents.discreteTopology_iff` / 引理 `ConnectedComponents.discreteTopology_iff`

English:
lemma ConnectedComponents.discreteTopology_iff
  proof: by
  simp_rw [discreteTopology_iff_isOpen_singleton, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

中文:
引理 ConnectedComponents.discreteTopology_iff
  证明: by
  simp_rw [discreteTopology_iff_isOpen_singleton, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

Depends on / 依赖: connectedComponents_preimage_singleton, discreteTopology_iff_isOpen_singleton, isOpen_preimage, isQuotientMap_coe, isQuotientMap_coe.isOpen_preimage, simp_rw, surjective_coe, surjective_coe.forall
-/
lemma ConnectedComponents.discreteTopology_iff :
    DiscreteTopology (ConnectedComponents α) ↔ forall x : α, IsOpen (connectedComponent x) := by
  simp_rw [discreteTopology_iff_isOpen_singleton, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

end connectedComponentSetoid

/--
theorem `isPreconnected_of_forall_constant` / 定理 `isPreconnected_of_forall_constant`

English:
theorem isPreconnected_of_forall_constant
  statement: {s : Set α}
  proof: by
  unfold IsPreconnected
  by_contra! ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_notMem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.notMem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

中文:
定理 isPreconnected_of_对任意_constant
  结论: {s : 集合 α}
  证明: by
  unfold IsPreconnected
  by_contra! ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_notMem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.notMem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

Depends on / 依赖: ContinuousOn, IsPreconnected, boolIndicator, continuousOn_boolIndicator_iff_isClopen, continuous_subtype_val, eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem.mp, isClosed_compl, mem_iff_boolIndicator, preimage, preimage_subtype_coe_eq_compl, u.boolIndicator, u.mem_iff_boolIndicator, u_op, u_op.preimage, v_op, v_op.preimage, x_in_s, x_in_u, y_in_s
-/
theorem isPreconnected_of_forall_constant {s : Set α}
    (hs : forall f : α -> Bool, ContinuousOn f s -> forall x in s, forall y in s, f x = f y) : IsPreconnected s := by
  unfold IsPreconnected
  by_contra! ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_notMem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.notMem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

/--
theorem `preconnectedSpace_of_forall_constant` / 定理 `preconnectedSpace_of_forall_constant`

English:
theorem preconnectedSpace_of_forall_constant
  proof: ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuousOn_univ.mp hf) x y⟩

中文:
定理 preconnectedSpace_of_对任意_constant
  证明: ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuousOn_univ.mp hf) x y⟩

Depends on / 依赖: continuousOn_univ, continuousOn_univ.mp, isPreconnected_of_forall_constant
-/
theorem preconnectedSpace_of_forall_constant
    (hs : forall f : α -> Bool, Continuous f -> forall x y, f x = f y) : PreconnectedSpace α :=
  ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuousOn_univ.mp hf) x y⟩

/--
theorem `preconnectedSpace_iff_clopen` / 定理 `preconnectedSpace_iff_clopen`

English:
theorem preconnectedSpace_iff_clopen
  proof: by
  refine ⟨fun _ _ => isClopen_iff.mp, fun h => ?_⟩
  refine preconnectedSpace_of_forall_constant fun f hf x y => ?_
  have : f ⁻¹' {false} = (f ⁻¹' {true})ᶜ := by
    rw [← Set.preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  obtain (h | h) := h _ ((isClopen_discrete {true}).preimage hf) <;> simp_all

中文:
定理 preconnectedSpace_iff_clopen
  证明: by
  refine ⟨fun _ _ => isClopen_iff.mp, fun h => ?_⟩
  refine preconnectedSpace_of_forall_constant fun f hf x y => ?_
  have : f ⁻¹' {false} = (f ⁻¹' {true})ᶜ := by
    rw [← Set.preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  obtain (h | h) := h _ ((isClopen_discrete {true}).preimage hf) <;> simp_all

Depends on / 依赖: Bool.compl_singleton, Bool.not_true, Set.preimage_compl, compl_singleton, isClopen_discrete, isClopen_iff, isClopen_iff.mp, not_true, preconnectedSpace_of_forall_constant, preimage, preimage_compl
-/
theorem preconnectedSpace_iff_clopen :
    PreconnectedSpace α ↔ forall s : Set α, IsClopen s -> s = ∅ ∨ s = Set.univ := by
  refine ⟨fun _ _ => isClopen_iff.mp, fun h => ?_⟩
  refine preconnectedSpace_of_forall_constant fun f hf x y => ?_
  have : f ⁻¹' {false} = (f ⁻¹' {true})ᶜ := by
    rw [← Set.preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  obtain (h | h) := h _ ((isClopen_discrete {true}).preimage hf) <;> simp_all

/--
theorem `connectedSpace_iff_clopen` / 定理 `connectedSpace_iff_clopen`

English:
theorem connectedSpace_iff_clopen
  proof: by
  rw [connectedSpace_iff_univ]; rw [IsConnected]; rw [← preconnectedSpace_iff_univ]; rw [preconnectedSpace_iff_clopen]; rw [Set.nonempty_iff_univ_nonempty]

中文:
定理 connectedSpace_iff_clopen
  证明: by
  rw [connectedSpace_iff_univ]; rw [IsConnected]; rw [← preconnectedSpace_iff_univ]; rw [preconnectedSpace_iff_clopen]; rw [Set.nonempty_iff_univ_nonempty]

Depends on / 依赖: IsConnected, Set.nonempty_iff_univ_nonempty, connectedSpace_iff_univ, nonempty_iff_univ_nonempty, preconnectedSpace_iff_clopen, preconnectedSpace_iff_univ
-/
theorem connectedSpace_iff_clopen :
    ConnectedSpace α ↔ Nonempty α ∧ forall s : Set α, IsClopen s -> s = ∅ ∨ s = Set.univ := by
  rw [connectedSpace_iff_univ]; rw [IsConnected]; rw [← preconnectedSpace_iff_univ]; rw [preconnectedSpace_iff_clopen]; rw [Set.nonempty_iff_univ_nonempty]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: α] : CompactSpace ConnectedComponents α
  body: Quotient.compactSpace

中文:
实例 [紧空间
  签名: α] : 紧空间 ConnectedComponents α
  定义体: Quotient.compactSpace

Depends on / 依赖: Quotient, Quotient.compactSpace, compactSpace
-/
instance [CompactSpace α] : CompactSpace ConnectedComponents α := Quotient.compactSpace
