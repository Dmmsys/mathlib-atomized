/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Tactic.TFAE

/-!
# Locally closed sets

## Main definitions

* `IsLocallyClosed`: Predicate saying that a set is locally closed

## Main results

* `isLocallyClosed_tfae`:
  A set `s` is locally closed if one of the equivalent conditions below hold
  1. It is the intersection of some open set and some closed set.
  2. The coborder `(closure s \ s)ᶜ` is open.
  3. `s` is closed in some neighborhood of `x` for all `x ∈ s`.
  4. Every `x ∈ s` has some open neighborhood `U` such that `U ∩ closure s ⊆ s`.
  5. `s` is open in the closure of `s`.

-/

public section

open Set Topology
open scoped Set.Notation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X -> Y}

/--
lemma `subset_coborder` / 引理 `subset_coborder`

English:
lemma subset_coborder
  proof: by
  rw [coborder]; rw [subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

中文:
引理 subset_coborder
  证明: by
  rw [coborder]; rw [subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

Depends on / 依赖: coborder, disjoint_sdiff_self_right, subset_compl_iff_disjoint_right
-/
lemma subset_coborder :
    s subseteq coborder s := by
  rw [coborder]; rw [subset_compl_iff_disjoint_right]
  exact disjoint_sdiff_self_right

/--
lemma `coborder_inter_closure` / 引理 `coborder_inter_closure`

English:
lemma coborder_inter_closure
  proof: by
  rw [coborder]; rw [← sdiff_eq_compl_inter]; rw [sdiff_sdiff_right_self]; rw [inter_eq_right]
  exact subset_closure

中文:
引理 coborder_inter_closure
  证明: by
  rw [coborder]; rw [← sdiff_eq_compl_inter]; rw [sdiff_sdiff_right_self]; rw [inter_eq_right]
  exact subset_closure

Depends on / 依赖: coborder, inter_eq_right, sdiff_eq_compl_inter, sdiff_sdiff_right_self, subset_closure
-/
lemma coborder_inter_closure :
    coborder s inter closure s = s := by
  rw [coborder]; rw [← sdiff_eq_compl_inter]; rw [sdiff_sdiff_right_self]; rw [inter_eq_right]
  exact subset_closure

/--
lemma `closure_inter_coborder` / 引理 `closure_inter_coborder`

English:
lemma closure_inter_coborder
  proof: by
  rw [inter_comm]; rw [coborder_inter_closure]

中文:
引理 closure_inter_coborder
  证明: by
  rw [inter_comm]; rw [coborder_inter_closure]

Depends on / 依赖: coborder_inter_closure, inter_comm
-/
lemma closure_inter_coborder :
    closure s inter coborder s = s := by
  rw [inter_comm]; rw [coborder_inter_closure]

/--
lemma `coborder_eq_union_frontier_compl` / 引理 `coborder_eq_union_frontier_compl`

English:
lemma coborder_eq_union_frontier_compl
  proof: by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [← sdiff_eq_compl_inter]; rw [← union_sdiff_right]; rw [union_comm]; rw [← closure_eq_self_union_frontier]

中文:
引理 coborder_eq_union_frontier_compl
  证明: by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [← sdiff_eq_compl_inter]; rw [← union_sdiff_right]; rw [union_comm]; rw [← closure_eq_self_union_frontier]

Depends on / 依赖: closure_eq_self_union_frontier, coborder, compl_compl, compl_eq_comm, compl_union, sdiff_eq_compl_inter, union_comm, union_sdiff_right
-/
lemma coborder_eq_union_frontier_compl :
    coborder s = s union (frontier s)ᶜ := by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [← sdiff_eq_compl_inter]; rw [← union_sdiff_right]; rw [union_comm]; rw [← closure_eq_self_union_frontier]

/--
lemma `coborder_eq_univ_iff` / 引理 `coborder_eq_univ_iff`

English:
lemma coborder_eq_univ_iff
  proof: by
  simp [coborder, sdiff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff

中文:
引理 coborder_eq_univ_iff
  证明: by
  simp [coborder, sdiff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff

Depends on / 依赖: closure_subset_iff_isClosed, coborder, sdiff_eq_empty
-/
lemma coborder_eq_univ_iff :
    coborder s = univ ↔ IsClosed s := by
  simp [coborder, sdiff_eq_empty, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.coborder_eq⟩ := coborder_eq_univ_iff

/--
lemma `coborder_eq_compl_frontier_iff` / 引理 `coborder_eq_compl_frontier_iff`

English:
lemma coborder_eq_compl_frontier_iff
  proof: by
  simp_rw [coborder_eq_union_frontier_compl, union_eq_right, subset_compl_iff_disjoint_left,
    disjoint_frontier_iff_isOpen]

中文:
引理 coborder_eq_compl_frontier_iff
  证明: by
  simp_rw [coborder_eq_union_frontier_compl, union_eq_right, subset_compl_iff_disjoint_left,
    disjoint_frontier_iff_isOpen]

Depends on / 依赖: coborder_eq_union_frontier_compl, disjoint_frontier_iff_isOpen, simp_rw, subset_compl_iff_disjoint_left, union_eq_right
-/
lemma coborder_eq_compl_frontier_iff :
    coborder s = (frontier s)ᶜ ↔ IsOpen s := by
  simp_rw [coborder_eq_union_frontier_compl, union_eq_right, subset_compl_iff_disjoint_left,
    disjoint_frontier_iff_isOpen]

/--
theorem `coborder_eq_union_closure_compl` / 定理 `coborder_eq_union_closure_compl`

English:
theorem coborder_eq_union_closure_compl
  given: {s : Set X}
  statement: coborder s = s union (closure s)ᶜ
  proof: by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [inter_comm]
  rfl

中文:
定理 coborder_eq_union_closure_compl
  条件: {s : 集合 X}
  结论: coborder s = s union (closure s)ᶜ
  证明: by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [inter_comm]
  rfl

Depends on / 依赖: coborder, compl_compl, compl_eq_comm, compl_union, inter_comm
-/
theorem coborder_eq_union_closure_compl {s : Set X} : coborder s = s union (closure s)ᶜ := by
  rw [coborder]; rw [compl_eq_comm]; rw [compl_union]; rw [compl_compl]; rw [inter_comm]
  rfl

/--
theorem `dense_coborder` / 定理 `dense_coborder`

English:
theorem dense_coborder
  given: {s : Set X}
  proof: by
  rw [dense_iff_closure_eq]; rw [coborder_eq_union_closure_compl]; rw [closure_union]; rw [← univ_subset_iff]
  refine _root_.subset_trans ?_ (union_subset_union_right _ (subset_closure))
  simp

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff

中文:
定理 dense_coborder
  条件: {s : 集合 X}
  证明: by
  rw [dense_iff_closure_eq]; rw [coborder_eq_union_closure_compl]; rw [closure_union]; rw [← univ_subset_iff]
  refine _root_.subset_trans ?_ (union_subset_union_right _ (subset_closure))
  simp

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff

Depends on / 依赖: _root_, _root_.subset_trans, closure_union, coborder_eq_union_closure_compl, dense_iff_closure_eq, subset_closure, subset_trans, union_subset_union_right, univ_subset_iff
-/
theorem dense_coborder {s : Set X} :
    Dense (coborder s) := by
  rw [dense_iff_closure_eq]; rw [coborder_eq_union_closure_compl]; rw [closure_union]; rw [← univ_subset_iff]
  refine _root_.subset_trans ?_ (union_subset_union_right _ (subset_closure))
  simp

alias ⟨_, IsOpen.coborder_eq⟩ := coborder_eq_compl_frontier_iff

/--
lemma `IsOpenMap.coborder_preimage_subset` / 引理 `IsOpenMap.coborder_preimage_subset`

English:
lemma IsOpenMap.coborder_preimage_subset
  given: (hf : IsOpenMap f) (s : Set Y)
  proof: by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.preimage_closure_subset_closure_preimage

中文:
引理 是开映射.coborder_preimage_subset
  条件: (hf : 是开映射 f) (s : 集合 Y)
  证明: by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.preimage_closure_subset_closure_preimage

Depends on / 依赖: coborder, compl_subset_compl, hf.preimage_closure_subset_closure_preimage, preimage_closure_subset_closure_preimage, preimage_compl, preimage_sdiff, sdiff_subset_sdiff_left
-/
lemma IsOpenMap.coborder_preimage_subset (hf : IsOpenMap f) (s : Set Y) :
    coborder (f ⁻¹' s) subseteq f ⁻¹' (coborder s) := by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.preimage_closure_subset_closure_preimage

/--
lemma `Continuous.preimage_coborder_subset` / 引理 `Continuous.preimage_coborder_subset`

English:
lemma Continuous.preimage_coborder_subset
  given: (hf : Continuous f) (s : Set Y)
  proof: by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.closure_preimage_subset s

中文:
引理 连续.preimage_coborder_subset
  条件: (hf : 连续 f) (s : 集合 Y)
  证明: by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.closure_preimage_subset s

Depends on / 依赖: closure_preimage_subset, coborder, compl_subset_compl, hf.closure_preimage_subset, preimage_compl, preimage_sdiff, sdiff_subset_sdiff_left
-/
lemma Continuous.preimage_coborder_subset (hf : Continuous f) (s : Set Y) :
    f ⁻¹' (coborder s) subseteq coborder (f ⁻¹' s) := by
  rw [coborder]; rw [coborder]; rw [preimage_compl]; rw [preimage_sdiff]; rw [compl_subset_compl]
  apply sdiff_subset_sdiff_left
  exact hf.closure_preimage_subset s

/--
lemma `coborder_preimage` / 引理 `coborder_preimage`

English:
lemma coborder_preimage
  given: (hf : IsOpenMap f) (hf' : Continuous f) (s : Set Y)
  proof: (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected

中文:
引理 coborder_preimage
  条件: (hf : 是开映射 f) (hf' : 连续 f) (s : 集合 Y)
  证明: (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected

Depends on / 依赖: antisymm, coborder_preimage_subset, hf.coborder_preimage_subset, preimage_coborder_subset
-/
lemma coborder_preimage (hf : IsOpenMap f) (hf' : Continuous f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' (coborder s) :=
  (hf.coborder_preimage_subset s).antisymm (hf'.preimage_coborder_subset s)

protected
/--
lemma `Topology.IsOpenEmbedding.coborder_preimage` / 引理 `Topology.IsOpenEmbedding.coborder_preimage`

English:
lemma Topology.IsOpenEmbedding.coborder_preimage
  given: (hf : IsOpenEmbedding f) (s : Set Y)
  proof: coborder_preimage hf.isOpenMap hf.continuous s

中文:
引理 拓扑.是开嵌入.coborder_preimage
  条件: (hf : 是开嵌入 f) (s : 集合 Y)
  证明: coborder_preimage hf.isOpenMap hf.continuous s

Depends on / 依赖: coborder_preimage, continuous, hf.continuous, hf.isOpenMap, isOpenMap
-/
lemma Topology.IsOpenEmbedding.coborder_preimage (hf : IsOpenEmbedding f) (s : Set Y) :
    coborder (f ⁻¹' s) = f ⁻¹' coborder s :=
  coborder_preimage hf.isOpenMap hf.continuous s

/--
lemma `isClosed_preimage_val_coborder` / 引理 `isClosed_preimage_val_coborder`

English:
lemma isClosed_preimage_val_coborder
  proof: by
  rw [isClosed_preimage_val]; rw [inter_eq_right.mpr subset_coborder]; rw [coborder_inter_closure]

中文:
引理 isClosed_preimage_val_coborder
  证明: by
  rw [isClosed_preimage_val]; rw [inter_eq_right.mpr subset_coborder]; rw [coborder_inter_closure]

Depends on / 依赖: coborder_inter_closure, inter_eq_right, inter_eq_right.mpr, isClosed_preimage_val, subset_coborder
-/
lemma isClosed_preimage_val_coborder :
    IsClosed (coborder s ↓inter s) := by
  rw [isClosed_preimage_val]; rw [inter_eq_right.mpr subset_coborder]; rw [coborder_inter_closure]

/--
lemma `IsLocallyClosed.inter` / 引理 `IsLocallyClosed.inter`

English:
lemma IsLocallyClosed.inter
  given: (hs : IsLocallyClosed s) (ht : IsLocallyClosed t)
  proof: by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩

中文:
引理 IsLocallyClosed.inter
  条件: (hs : IsLocallyClosed s) (ht : IsLocallyClosed t)
  证明: by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩

Depends on / 依赖: inter_inter_inter_comm
-/
lemma IsLocallyClosed.inter (hs : IsLocallyClosed s) (ht : IsLocallyClosed t) :
    IsLocallyClosed (s inter t) := by
  obtain ⟨U₁, Z₁, hU₁, hZ₁, rfl⟩ := hs
  obtain ⟨U₂, Z₂, hU₂, hZ₂, rfl⟩ := ht
  refine ⟨_, _, hU₁.inter hU₂, hZ₁.inter hZ₂, inter_inter_inter_comm U₁ Z₁ U₂ Z₂⟩

/--
lemma `IsLocallyClosed.preimage` / 引理 `IsLocallyClosed.preimage`

English:
lemma IsLocallyClosed.preimage
  statement: {s : Set Y} (hs : IsLocallyClosed s)
  proof: by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, preimage_inter⟩

nonrec

中文:
引理 IsLocallyClosed.原像
  结论: {s : 集合 Y} (hs : IsLocallyClosed s)
  证明: by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, preimage_inter⟩

nonrec

Depends on / 依赖: hU.preimage, hZ.preimage, preimage, preimage_inter
-/
lemma IsLocallyClosed.preimage {s : Set Y} (hs : IsLocallyClosed s)
    {f : X -> Y} (hf : Continuous f) :
    IsLocallyClosed (f ⁻¹' s) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hs
  exact ⟨_, _, hU.preimage hf, hZ.preimage hf, preimage_inter⟩

nonrec
/--
lemma `Topology.IsInducing.isLocallyClosed_iff` / 引理 `Topology.IsInducing.isLocallyClosed_iff`

English:
lemma Topology.IsInducing.isLocallyClosed_iff
  statement: {s : Set X}
  proof: by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

中文:
引理 拓扑.是Inducing.isLocallyClosed_iff
  结论: {s : 集合 X}
  证明: by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

Depends on / 依赖: IsLocallyClosed, hf.isClosed_iff, hf.isOpen_iff, isClosed_iff, isOpen_iff, simp_rw
-/
lemma Topology.IsInducing.isLocallyClosed_iff {s : Set X}
    {f : X -> Y} (hf : IsInducing f) :
    IsLocallyClosed s ↔ exists s' : Set Y, IsLocallyClosed s' ∧ f ⁻¹' s' = s := by
  simp_rw [IsLocallyClosed, hf.isOpen_iff, hf.isClosed_iff]
  constructor
  · rintro ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨U, Z, hU, hZ, rfl⟩, rfl⟩
    exact ⟨_, _, ⟨U, hU, rfl⟩, ⟨Z, hZ, rfl⟩, rfl⟩

/--
lemma `Topology.IsEmbedding.isLocallyClosed_iff` / 引理 `Topology.IsEmbedding.isLocallyClosed_iff`

English:
lemma Topology.IsEmbedding.isLocallyClosed_iff
  statement: {s : Set X}
  proof: by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]

中文:
引理 拓扑.是嵌入.isLocallyClosed_iff
  结论: {s : 集合 X}
  证明: by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]

Depends on / 依赖: eq_iff, hf.injective, hf.isInducing.isLocallyClosed_iff, image_injective, image_injective.mpr, image_preimage_eq_inter_range, injective, isInducing, isLocallyClosed_iff, simp_rw
-/
lemma Topology.IsEmbedding.isLocallyClosed_iff {s : Set X}
    {f : X -> Y} (hf : IsEmbedding f) :
    IsLocallyClosed s ↔ exists s' : Set Y, IsLocallyClosed s' ∧ s' inter range f = f '' s := by
  simp_rw [hf.isInducing.isLocallyClosed_iff,
    ← (image_injective.mpr hf.injective).eq_iff, image_preimage_eq_inter_range]

/--
lemma `IsLocallyClosed.image` / 引理 `IsLocallyClosed.image`

English:
lemma IsLocallyClosed.image
  statement: {s : Set X} (hs : IsLocallyClosed s)
  proof: by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

中文:
引理 IsLocallyClosed.像
  结论: {s : 集合 X} (hs : IsLocallyClosed s)
  证明: by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

Depends on / 依赖: hf.isLocallyClosed_iff.mp, ht.inter, image_preimage_eq_inter_range, isLocallyClosed_iff
-/
lemma IsLocallyClosed.image {s : Set X} (hs : IsLocallyClosed s)
    {f : X -> Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) :
    IsLocallyClosed (f '' s) := by
  obtain ⟨t, ht, rfl⟩ := hf.isLocallyClosed_iff.mp hs
  rw [image_preimage_eq_inter_range]
  exact ht.inter hf'

/--
lemma `isLocallyClosed_tfae` / 引理 `isLocallyClosed_tfae`

English:
lemma isLocallyClosed_tfae
  given: (s : Set X)
  proof: by
  tfae_have 1 -> 2 := by
    rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z union (frontier (U inter Z))ᶜ = univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← compl_subset_iff_union]; rw [compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono inter_subset_right)
    rw [cobord

中文:
引理 isLocallyClosed_tfae
  条件: (s : 集合 X)
  证明: by
  tfae_have 1 -> 2 := by
    rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z union (frontier (U inter Z))ᶜ = univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← compl_subset_iff_union]; rw [compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono inter_subset_right)
    rw [cobord

Depends on / 依赖: closure_eq, closure_mono, coborder, coborder_eq_union_frontier_compl, compl_subset_compl, compl_subset_iff_union, frontier, frontier_subset_closure, frontier_subset_closure.trans, h.mem_nhds, hU.union, hZ.closure_eq, inter_subset_right, inter_union_distrib_right, inter_univ, isClosed_frontier, isClosed_frontier.isOpen_compl, isClosed_preimage_val_co, isOpen_compl, mem_nhds
-/
lemma isLocallyClosed_tfae (s : Set X) :
    List.TFAE
    [ IsLocallyClosed s,
      IsOpen (coborder s),
      forall x in s, exists U in 𝓝 x, IsClosed (U ↓inter s),
      forall x in s, exists U, x in U ∧ IsOpen U ∧ U inter closure s subseteq s,
      IsOpen (closure s ↓inter s)] := by
  tfae_have 1 -> 2 := by
    rintro ⟨U, Z, hU, hZ, rfl⟩
    have : Z union (frontier (U inter Z))ᶜ = univ := by
      nth_rw 1 [← hZ.closure_eq]
      rw [← compl_subset_iff_union]; rw [compl_subset_compl]
      refine frontier_subset_closure.trans (closure_mono inter_subset_right)
    rw [coborder_eq_union_frontier_compl]; rw [inter_union_distrib_right]; rw [this]; rw [inter_univ]
    exact hU.union isClosed_frontier.isOpen_compl
  tfae_have 2 -> 3
  | h, x => (⟨coborder s, h.mem_nhds <| subset_coborder ·, isClosed_preimage_val_coborder⟩)
  tfae_have 3 -> 4
  | h, x, hx => by
    obtain ⟨t, ht, ht'⟩ := h x hx
    obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp ht
    rw [isClosed_preimage_val] at ht'
    exact ⟨U, hxU, hU, (subset_inter (inter_subset_left.trans hUt) (hU.inter_closure.trans
      (closure_mono <| inter_subset_inter hUt subset_rfl))).trans ht'⟩
  tfae_have 4 -> 5
  | H => by
    choose U hxU hU e using H
    refine ⟨⋃ x in s, U x ‹_›, isOpen_iUnion (isOpen_iUnion <| hU ·), ext fun x => ⟨?_, ?_⟩⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, ⟨_, ⟨hy, rfl⟩, hxU⟩⟩⟩
      exact e y hy ⟨hxU, x.2⟩
    · exact (subset_iUnion₂ _ _ <| hxU x ·)
  tfae_have 5 -> 1
  | H => by
    convert!
      H.isLocallyClosed.image IsInducing.subtypeVal
        (by simpa using isClosed_closure.isLocallyClosed)
    simpa using subset_closure
  tfae_finish

/--
lemma `isLocallyClosed_iff_isOpen_coborder` / 引理 `isLocallyClosed_iff_isOpen_coborder`

English:
lemma isLocallyClosed_iff_isOpen_coborder
  statement: IsLocallyClosed s ↔ IsOpen (coborder s)
  proof: (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

中文:
引理 isLocallyClosed_iff_isOpen_coborder
  结论: IsLocallyClosed s ↔ 是开集 (coborder s)
  证明: (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

Depends on / 依赖: isLocallyClosed_tfae
-/
lemma isLocallyClosed_iff_isOpen_coborder : IsLocallyClosed s ↔ IsOpen (coborder s) :=
  (isLocallyClosed_tfae s).out 0 1

alias ⟨IsLocallyClosed.isOpen_coborder, _⟩ := isLocallyClosed_iff_isOpen_coborder

/--
lemma `IsLocallyClosed.isOpen_preimage_val_closure` / 引理 `IsLocallyClosed.isOpen_preimage_val_closure`

English:
lemma IsLocallyClosed.isOpen_preimage_val_closure
  given: (hs : IsLocallyClosed s)
  proof: ((isLocallyClosed_tfae s).out 0 4).mp hs

中文:
引理 IsLocallyClosed.isOpen_preimage_val_closure
  条件: (hs : IsLocallyClosed s)
  证明: ((isLocallyClosed_tfae s).out 0 4).mp hs

Depends on / 依赖: isLocallyClosed_tfae
-/
lemma IsLocallyClosed.isOpen_preimage_val_closure (hs : IsLocallyClosed s) :
    IsOpen (closure s ↓inter s) :=
  ((isLocallyClosed_tfae s).out 0 4).mp hs
