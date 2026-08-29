/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Baire.Lemmas

/-!
# Further properties of homeomorphisms

This file proves further properties of homeomorphisms between topological spaces.
Pretty much every topological property is preserved under homeomorphisms.

-/

@[expose] public section

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*}

section

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

namespace Homeomorph

/--
theorem `secondCountableTopology` / 定理 `secondCountableTopology`

English:
theorem secondCountableTopology
  statement: [SecondCountableTopology Y]
  proof: h.isInducing.secondCountableTopology

中文:
定理 secondCountableTopology
  结论: [第二可数拓扑 Y]
  证明: h.isInducing.secondCountableTopology
-/
protected theorem secondCountableTopology [SecondCountableTopology Y]
    (h : X ≃ₜ Y) : SecondCountableTopology X :=
  h.isInducing.secondCountableTopology

/--
theorem `baireSpace` / 定理 `baireSpace`

English:
theorem baireSpace
  given: [BaireSpace X] (f : X ≃ₜ Y)
  statement: BaireSpace Y
  proof: f.isOpenQuotientMap.baireSpace

中文:
定理 baireSpace
  条件: [Baire空间 X] (f : X ≃ₜ Y)
  结论: Baire空间 Y
  证明: f.isOpenQuotientMap.baireSpace
-/
protected theorem baireSpace [BaireSpace X] (f : X ≃ₜ Y) : BaireSpace Y :=
  f.isOpenQuotientMap.baireSpace

/-- If `h : X → Y` is a homeomorphism, `h(s)` is compact iff `s` is. -/
@[simp]
/--
theorem `isCompact_image` / 定理 `isCompact_image`

English:
theorem isCompact_image
  given: {s : Set X} (h : X ≃ₜ Y)
  statement: IsCompact (h '' s) ↔ IsCompact s
  proof: h.isEmbedding.isCompact_iff.symm

中文:
定理 isCompact_image
  条件: {s : 集合 X} (h : X ≃ₜ Y)
  结论: 是紧集 (h '' s) ↔ 是紧集 s
  证明: h.isEmbedding.isCompact_iff.symm

Depends on / 依赖: h.isEmbedding.isCompact_iff.symm, isCompact_iff, isEmbedding
-/
theorem isCompact_image {s : Set X} (h : X ≃ₜ Y) : IsCompact (h '' s) ↔ IsCompact s :=
  h.isEmbedding.isCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is compact iff `s` is. -/
@[simp]
/--
theorem `isCompact_preimage` / 定理 `isCompact_preimage`

English:
theorem isCompact_preimage
  given: {s : Set Y} (h : X ≃ₜ Y)
  statement: IsCompact (h ⁻¹' s) ↔ IsCompact s
  proof: by
  rw [← image_symm]; exact h.symm.isCompact_image

中文:
定理 isCompact_preimage
  条件: {s : 集合 Y} (h : X ≃ₜ Y)
  结论: 是紧集 (h ⁻¹' s) ↔ 是紧集 s
  证明: by
  rw [← image_symm]; exact h.symm.isCompact_image

Depends on / 依赖: h.symm.isCompact_image, image_symm, isCompact_image
-/
theorem isCompact_preimage {s : Set Y} (h : X ≃ₜ Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm]; exact h.symm.isCompact_image

/-- If `h : X → Y` is a homeomorphism, `s` is σ-compact iff `h(s)` is. -/
@[simp]
/--
theorem `isSigmaCompact_image` / 定理 `isSigmaCompact_image`

English:
theorem isSigmaCompact_image
  given: {s : Set X} (h : X ≃ₜ Y)
  proof: h.isEmbedding.isSigmaCompact_iff.symm

中文:
定理 isSigmaCompact_image
  条件: {s : 集合 X} (h : X ≃ₜ Y)
  证明: h.isEmbedding.isSigmaCompact_iff.symm

Depends on / 依赖: h.isEmbedding.isSigmaCompact_iff.symm, isEmbedding, isSigmaCompact_iff
-/
theorem isSigmaCompact_image {s : Set X} (h : X ≃ₜ Y) :
    IsSigmaCompact (h '' s) ↔ IsSigmaCompact s :=
  h.isEmbedding.isSigmaCompact_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is σ-compact iff `s` is. -/
@[simp]
/--
theorem `isSigmaCompact_preimage` / 定理 `isSigmaCompact_preimage`

English:
theorem isSigmaCompact_preimage
  given: {s : Set Y} (h : X ≃ₜ Y)
  proof: by
  rw [← image_symm]; exact h.symm.isSigmaCompact_image

@[simp]

中文:
定理 isSigmaCompact_preimage
  条件: {s : 集合 Y} (h : X ≃ₜ Y)
  证明: by
  rw [← image_symm]; exact h.symm.isSigmaCompact_image

@[simp]

Depends on / 依赖: h.symm.isSigmaCompact_image, image_symm, isSigmaCompact_image
-/
theorem isSigmaCompact_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsSigmaCompact (h ⁻¹' s) ↔ IsSigmaCompact s := by
  rw [← image_symm]; exact h.symm.isSigmaCompact_image

@[simp]
/--
theorem `isPreconnected_image` / 定理 `isPreconnected_image`

English:
theorem isPreconnected_image
  given: {s : Set X} (h : X ≃ₜ Y)
  proof: ⟨fun hs => by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs => hs.image _ h.continuous.continuousOn⟩

@[simp]

中文:
定理 isPreconnected_image
  条件: {s : 集合 X} (h : X ≃ₜ Y)
  证明: ⟨fun hs => by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs => hs.image _ h.continuous.continuousOn⟩

@[simp]

Depends on / 依赖: continuous, continuousOn, h.continuous.continuousOn, h.symm.continuous.continuousOn, hs.image, image_symm, preimage_image
-/
theorem isPreconnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPreconnected (h '' s) ↔ IsPreconnected s :=
  ⟨fun hs => by simpa only [image_symm, preimage_image]
    using hs.image _ h.symm.continuous.continuousOn,
    fun hs => hs.image _ h.continuous.continuousOn⟩

@[simp]
/--
theorem `isPreconnected_preimage` / 定理 `isPreconnected_preimage`

English:
theorem isPreconnected_preimage
  given: {s : Set Y} (h : X ≃ₜ Y)
  proof: by
  rw [← image_symm]; rw [isPreconnected_image]

@[simp]

中文:
定理 isPreconnected_preimage
  条件: {s : 集合 Y} (h : X ≃ₜ Y)
  证明: by
  rw [← image_symm]; rw [isPreconnected_image]

@[simp]

Depends on / 依赖: image_symm, isPreconnected_image
-/
theorem isPreconnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPreconnected (h ⁻¹' s) ↔ IsPreconnected s := by
  rw [← image_symm]; rw [isPreconnected_image]

@[simp]
/--
theorem `isConnected_image` / 定理 `isConnected_image`

English:
theorem isConnected_image
  given: {s : Set X} (h : X ≃ₜ Y)
  proof: image_nonempty.and h.isPreconnected_image

@[simp]

中文:
定理 isConnected_image
  条件: {s : 集合 X} (h : X ≃ₜ Y)
  证明: image_nonempty.and h.isPreconnected_image

@[simp]

Depends on / 依赖: h.isPreconnected_image, image_nonempty, image_nonempty.and, isPreconnected_image
-/
theorem isConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsConnected (h '' s) ↔ IsConnected s :=
  image_nonempty.and h.isPreconnected_image

@[simp]
/--
theorem `isConnected_preimage` / 定理 `isConnected_preimage`

English:
theorem isConnected_preimage
  given: {s : Set Y} (h : X ≃ₜ Y)
  proof: by
  rw [← image_symm]; rw [isConnected_image]

中文:
定理 isConnected_preimage
  条件: {s : 集合 Y} (h : X ≃ₜ Y)
  证明: by
  rw [← image_symm]; rw [isConnected_image]

Depends on / 依赖: image_symm, isConnected_image
-/
theorem isConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsConnected (h ⁻¹' s) ↔ IsConnected s := by
  rw [← image_symm]; rw [isConnected_image]

/--
theorem `image_connectedComponentIn` / 定理 `image_connectedComponentIn`

English:
theorem image_connectedComponentIn
  given: {s : Set X} (h : X ≃ₜ Y) {x : X} (hx : x in s)
  proof: by
  refine (h.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  have := h.symm.continuous.continuousOn.image_connectedComponentIn_subset (mem_image_of_mem h hx)
  rwa [image_subset_iff, h.preimage_symm, h.image_symm, h.preimage_image, h.symm_apply_apply]
    at this

@[sim

中文:
定理 image_connectedComponentIn
  条件: {s : 集合 X} (h : X ≃ₜ Y) {x : X} (hx : x in s)
  证明: by
  refine (h.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  have := h.symm.continuous.continuousOn.image_connectedComponentIn_subset (mem_image_of_mem h hx)
  rwa [image_subset_iff, h.preimage_symm, h.image_symm, h.preimage_image, h.symm_apply_apply]
    at this

@[sim

Depends on / 依赖: antisymm, continuous, continuousOn, h.continuous.continuousOn.image_connectedComponentIn_subset, h.image_symm, h.preimage_image, h.preimage_symm, h.symm.continuous.continuousOn.image_connectedComponentIn_subset, h.symm_apply_apply, image_connectedComponentIn_subset, image_subset_iff, image_symm, mem_image_of_mem, preimage_image, preimage_symm, symm_apply_apply
-/
theorem image_connectedComponentIn {s : Set X} (h : X ≃ₜ Y) {x : X} (hx : x in s) :
    h '' connectedComponentIn s x = connectedComponentIn (h '' s) (h x) := by
  refine (h.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  have := h.symm.continuous.continuousOn.image_connectedComponentIn_subset (mem_image_of_mem h hx)
  rwa [image_subset_iff, h.preimage_symm, h.image_symm, h.preimage_image, h.symm_apply_apply]
    at this

@[simp]
/--
theorem `comap_cocompact` / 定理 `comap_cocompact`

English:
theorem comap_cocompact
  given: (h : X ≃ₜ Y)
  statement: comap h (cocompact Y) = cocompact X
  proof: (comap_cocompact_le h.continuous).antisymm
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩

@[simp]

中文:
定理 comap_cocompact
  条件: (h : X ≃ₜ Y)
  结论: comap h (cocompact Y) = cocompact X
  证明: (comap_cocompact_le h.continuous).antisymm
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩

@[simp]

Depends on / 依赖: Subset, Subset.rfl, antisymm, comap_cocompact_le, continuous, h.continuous, h.isCompact_preimage, hasBasis_cocompact, hasBasis_cocompact.comap, hasBasis_cocompact.le_basis_iff, isCompact_preimage, le_basis_iff
-/
theorem comap_cocompact (h : X ≃ₜ Y) : comap h (cocompact Y) = cocompact X :=
(comap_cocompact_le h.continuous).antisymm
    (hasBasis_cocompact.le_basis_iff (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩

@[simp]
/--
theorem `map_cocompact` / 定理 `map_cocompact`

English:
theorem map_cocompact
  given: (h : X ≃ₜ Y)
  statement: map h (cocompact X) = cocompact Y
  proof: by
  rw [← h.comap_cocompact]; rw [map_comap_of_surjective h.surjective]

中文:
定理 map_cocompact
  条件: (h : X ≃ₜ Y)
  结论: map h (cocompact X) = cocompact Y
  证明: by
  rw [← h.comap_cocompact]; rw [map_comap_of_surjective h.surjective]

Depends on / 依赖: comap_cocompact, h.comap_cocompact, h.surjective, map_comap_of_surjective, surjective
-/
theorem map_cocompact (h : X ≃ₜ Y) : map h (cocompact X) = cocompact Y := by
  rw [← h.comap_cocompact]; rw [map_comap_of_surjective h.surjective]

/--
theorem `compactSpace` / 定理 `compactSpace`

English:
theorem compactSpace
  given: [CompactSpace X] (h : X ≃ₜ Y)
  statement: CompactSpace Y where
  proof: h.symm.isCompact_preimage.2 isCompact_univ

中文:
定理 compactSpace
  条件: [紧空间 X] (h : X ≃ₜ Y)
  结论: 紧空间 Y where
  证明: h.symm.isCompact_preimage.2 isCompact_univ
-/
protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  isCompact_univ := h.symm.isCompact_preimage.2 isCompact_univ

/--
theorem `isDenseEmbedding` / 定理 `isDenseEmbedding`

English:
theorem isDenseEmbedding
  given: (h : X ≃ₜ Y)
  statement: IsDenseEmbedding h
  proof: { h.isEmbedding with dense := h.surjective.denseRange }

中文:
定理 isDenseEmbedding
  条件: (h : X ≃ₜ Y)
  结论: 是稠密嵌入 h
  证明: { h.isEmbedding with dense := h.surjective.denseRange }

Depends on / 依赖: denseRange, h.isEmbedding, h.surjective.denseRange, isEmbedding, surjective
-/
theorem isDenseEmbedding (h : X ≃ₜ Y) : IsDenseEmbedding h :=
  { h.isEmbedding with dense := h.surjective.denseRange }

/--
lemma `totallyDisconnectedSpace` / 引理 `totallyDisconnectedSpace`

English:
lemma totallyDisconnectedSpace
  given: (h : X ≃ₜ Y) [tdc : TotallyDisconnectedSpace X]
  proof: (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[simp]

中文:
引理 totallyDisconnectedSpace
  条件: (h : X ≃ₜ Y) [tdc : 全不连通空间 X]
  证明: (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[simp]
-/
protected lemma totallyDisconnectedSpace (h : X ≃ₜ Y) [tdc : TotallyDisconnectedSpace X] :
    TotallyDisconnectedSpace Y :=
  (totallyDisconnectedSpace_iff Y).mpr
    (h.range_coe ▸ ((IsEmbedding.isTotallyDisconnected_range h.isEmbedding).mpr tdc))

@[simp]
/--
theorem `map_punctured_nhds_eq` / 定理 `map_punctured_nhds_eq`

English:
theorem map_punctured_nhds_eq
  given: (h : X ≃ₜ Y) (x : X)
  statement: map h (𝓝[!=] x) = 𝓝[!=] (h x)
  proof: by
  convert! h.isEmbedding.map_nhdsWithin_eq ({ x }ᶜ) x
  rw [h.image_compl]; rw [Set.image_singleton]

@[simp]

中文:
定理 map_punctured_nhds_eq
  条件: (h : X ≃ₜ Y) (x : X)
  结论: map h (𝓝[!=] x) = 𝓝[!=] (h x)
  证明: by
  convert! h.isEmbedding.map_nhdsWithin_eq ({ x }ᶜ) x
  rw [h.image_compl]; rw [Set.image_singleton]

@[simp]

Depends on / 依赖: Set.image_singleton, convert, h.image_compl, h.isEmbedding.map_nhdsWithin_eq, image_compl, image_singleton, isEmbedding, map_nhdsWithin_eq
-/
theorem map_punctured_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝[!=] x) = 𝓝[!=] (h x) := by
  convert! h.isEmbedding.map_nhdsWithin_eq ({ x }ᶜ) x
  rw [h.image_compl]; rw [Set.image_singleton]

@[simp]
/--
theorem `comap_coclosedCompact` / 定理 `comap_coclosedCompact`

English:
theorem comap_coclosedCompact
  given: (h : X ≃ₜ Y)
  statement: comap h (coclosedCompact Y) = coclosedCompact X
  proof: (hasBasis_coclosedCompact.comap h).eq_of_same_basis by
    simpa [comp_def] using hasBasis_coclosedCompact.comp_surjective h.injective.preimage_surjective

@[simp]

中文:
定理 comap_coclosedCompact
  条件: (h : X ≃ₜ Y)
  结论: comap h (coclosedCompact Y) = coclosedCompact X
  证明: (hasBasis_coclosedCompact.comap h).eq_of_same_basis by
    simpa [comp_def] using hasBasis_coclosedCompact.comp_surjective h.injective.preimage_surjective

@[simp]

Depends on / 依赖: comp_def, comp_surjective, eq_of_same_basis, h.injective.preimage_surjective, hasBasis_coclosedCompact, hasBasis_coclosedCompact.comap, hasBasis_coclosedCompact.comp_surjective, injective, preimage_surjective
-/
theorem comap_coclosedCompact (h : X ≃ₜ Y) : comap h (coclosedCompact Y) = coclosedCompact X :=
(hasBasis_coclosedCompact.comap h).eq_of_same_basis by
    simpa [comp_def] using hasBasis_coclosedCompact.comp_surjective h.injective.preimage_surjective

@[simp]
/--
theorem `map_coclosedCompact` / 定理 `map_coclosedCompact`

English:
theorem map_coclosedCompact
  given: (h : X ≃ₜ Y)
  statement: map h (coclosedCompact X) = coclosedCompact Y
  proof: by
  rw [← h.comap_coclosedCompact]; rw [map_comap_of_surjective h.surjective]

中文:
定理 map_coclosedCompact
  条件: (h : X ≃ₜ Y)
  结论: map h (coclosedCompact X) = coclosedCompact Y
  证明: by
  rw [← h.comap_coclosedCompact]; rw [map_comap_of_surjective h.surjective]

Depends on / 依赖: comap_coclosedCompact, h.comap_coclosedCompact, h.surjective, map_comap_of_surjective, surjective
-/
theorem map_coclosedCompact (h : X ≃ₜ Y) : map h (coclosedCompact X) = coclosedCompact Y := by
  rw [← h.comap_coclosedCompact]; rw [map_comap_of_surjective h.surjective]

/--
theorem `locallyConnectedSpace` / 定理 `locallyConnectedSpace`

English:
theorem locallyConnectedSpace
  given: [i : LocallyConnectedSpace Y] (h : X ≃ₜ Y)
  proof: by
  have : forall x, (𝓝 x).HasBasis (fun s => IsOpen s ∧ h x in s ∧ IsConnected s)
      (h.symm '' ·) := fun x => by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs => ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuo

中文:
定理 locallyConnectedSpace
  条件: [i : 局部连通空间 Y] (h : X ≃ₜ Y)
  证明: by
  have : forall x, (𝓝 x).HasBasis (fun s => IsOpen s ∧ h x in s ∧ IsConnected s)
      (h.symm '' ·) := fun x => by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs => ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuo

Depends on / 依赖: HasBasis, IsConnected, IsOpen, continuous, continuousOn, h.symm, h.symm.continuous.continuousOn, h.symm_map_nhds_eq, locallyConnectedSpace_of_connected_bases, symm_map_nhds_eq
-/
theorem locallyConnectedSpace [i : LocallyConnectedSpace Y] (h : X ≃ₜ Y) :
    LocallyConnectedSpace X := by
  have : forall x, (𝓝 x).HasBasis (fun s => IsOpen s ∧ h x in s ∧ IsConnected s)
      (h.symm '' ·) := fun x => by
    rw [← h.symm_map_nhds_eq]
    exact (i.1 _).map _
  refine locallyConnectedSpace_of_connected_bases _ _ this fun _ _ hs => ?_
  exact hs.2.2.2.image _ h.symm.continuous.continuousOn

/--
theorem `locallyCompactSpace_iff` / 定理 `locallyCompactSpace_iff`

English:
theorem locallyCompactSpace_iff
  given: (h : X ≃ₜ Y)
  proof: by
  exact ⟨fun _ => h.symm.isOpenEmbedding.locallyCompactSpace,
    fun _ => h.isClosedEmbedding.locallyCompactSpace⟩

@[simp]

中文:
定理 locallyCompactSpace_iff
  条件: (h : X ≃ₜ Y)
  证明: by
  exact ⟨fun _ => h.symm.isOpenEmbedding.locallyCompactSpace,
    fun _ => h.isClosedEmbedding.locallyCompactSpace⟩

@[simp]

Depends on / 依赖: h.isClosedEmbedding.locallyCompactSpace, h.symm.isOpenEmbedding.locallyCompactSpace, isClosedEmbedding, isOpenEmbedding, locallyCompactSpace
-/
theorem locallyCompactSpace_iff (h : X ≃ₜ Y) :
    LocallyCompactSpace X ↔ LocallyCompactSpace Y := by
  exact ⟨fun _ => h.symm.isOpenEmbedding.locallyCompactSpace,
    fun _ => h.isClosedEmbedding.locallyCompactSpace⟩

@[simp]
/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z)
  proof: h.isInducing.continuousOn_iff.symm

中文:
定理 comp_continuousOn_iff
  条件: (h : X ≃ₜ Y) (f : Z -> X) (s : 集合 Z)
  证明: h.isInducing.continuousOn_iff.symm

Depends on / 依赖: continuousOn_iff, h.isInducing.continuousOn_iff.symm, isInducing
-/
theorem comp_continuousOn_iff (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.isInducing.continuousOn_iff.symm

/--
theorem `comp_continuousWithinAt_iff` / 定理 `comp_continuousWithinAt_iff`

English:
theorem comp_continuousWithinAt_iff
  given: (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z) (z : Z)
  proof: h.isInducing.continuousWithinAt_iff

中文:
定理 comp_continuousWithinAt_iff
  条件: (h : X ≃ₜ Y) (f : Z -> X) (s : 集合 Z) (z : Z)
  证明: h.isInducing.continuousWithinAt_iff

Depends on / 依赖: continuousWithinAt_iff, h.isInducing.continuousWithinAt_iff, isInducing
-/
theorem comp_continuousWithinAt_iff (h : X ≃ₜ Y) (f : Z -> X) (s : Set Z) (z : Z) :
    ContinuousWithinAt f s z ↔ ContinuousWithinAt (h ∘ f) s z :=
  h.isInducing.continuousWithinAt_iff

set_option backward.defeqAttrib.useBackward true in
/-- A homeomorphism `h : X ≃ₜ Y` lifts to a homeomorphism between subtypes corresponding to
predicates `p : X → Prop` and `q : Y → Prop` so long as `p = q ∘ h`. -/
@[simps!]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : forall x, p x ↔ q (h x))
  body: h.subtypeEquiv h_iff

@[simp]

中文:
定义 subtype
  签名: {p : X -> 命题} {q : Y -> 命题} (h : X ≃ₜ Y) (h_iff : 对任意 x, p x ↔ q (h x))
  定义体: h.subtypeEquiv h_iff

@[simp]

Depends on / 依赖: h.subtypeEquiv, h_iff, subtypeEquiv
-/
def subtype {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : forall x, p x ↔ q (h x)) :
    {x // p x} ≃ₜ {y // q y} where
  __ := h.subtypeEquiv h_iff

@[simp]
/--
lemma `subtype_toEquiv` / 引理 `subtype_toEquiv`

English:
lemma subtype_toEquiv
  given: {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : forall x, p x ↔ q (h x))
  proof: rfl

中文:
引理 subtype_toEquiv
  条件: {p : X -> 命题} {q : Y -> 命题} (h : X ≃ₜ Y) (h_iff : 对任意 x, p x ↔ q (h x))
  证明: rfl
-/
lemma subtype_toEquiv {p : X -> Prop} {q : Y -> Prop} (h : X ≃ₜ Y) (h_iff : forall x, p x ↔ q (h x)) :
    (h.subtype h_iff).toEquiv = h.toEquiv.subtypeEquiv h_iff :=
  rfl

/--
Definition of `sets` / `sets` 的定义

English:
abbreviation sets
  signature: {s : Set X} {t : Set Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t)
  body: h.subtype Set.ext_iff.mp h_eq

中文:
缩写 sets
  签名: {s : 集合 X} {t : 集合 Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t)
  定义体: h.subtype Set.ext_iff.mp h_eq

Depends on / 依赖: Set.ext_iff.mp, ext_iff, h.subtype, h_eq, subtype
-/
abbrev sets {s : Set X} {t : Set Y} (h : X ≃ₜ Y) (h_eq : s = h ⁻¹' t) : s ≃ₜ t :=
h.subtype Set.ext_iff.mp h_eq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `setCongr` / `setCongr` 的定义

English:
definition setCongr
  signature: {s t : Set X} (h : s = t)
  body: Equiv.setCongr h

中文:
定义 setCongr
  签名: {s t : 集合 X} (h : s = t)
  定义体: Equiv.setCongr h

Depends on / 依赖: Equiv.setCongr, setCongr
-/
def setCongr {s t : Set X} (h : s = t) : s ≃ₜ t where
  toEquiv := Equiv.setCongr h

section prod

variable (X Y W Z)

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: [Unique Y]
  body: Equiv.prodUnique X Y

中文:
定义 prodUnique
  签名: [唯一 Y]
  定义体: Equiv.prodUnique X Y

Depends on / 依赖: Equiv.prodUnique, prodUnique
-/
def prodUnique [Unique Y] :
    X × Y ≃ₜ X where
  toEquiv := Equiv.prodUnique X Y

/--
theorem `coe_prodUnique` / 定理 `coe_prodUnique`

English:
theorem coe_prodUnique
  given: [Unique Y]
  statement: ⇑(prodUnique X Y) = Prod.fst
  proof: rfl

中文:
定理 coe_prodUnique
  条件: [唯一 Y]
  结论: ⇑(prodUnique X Y) = 积类型.fst
  证明: rfl
-/
@[simp] theorem coe_prodUnique [Unique Y] : ⇑(prodUnique X Y) = Prod.fst := rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! symm_apply_snd]
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [Unique X]
  body: (prodComm _ _).trans (prodUnique Y X)

中文:
定义 uniqueProd
  签名: (X Y : 类型) [拓扑空间 X] [拓扑空间 Y] [唯一 X]
  定义体: (prodComm _ _).trans (prodUnique Y X)

Depends on / 依赖: prodComm, prodUnique
-/
def uniqueProd (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [Unique X] :
    X × Y ≃ₜ Y :=
  (prodComm _ _).trans (prodUnique Y X)

/--
theorem `coe_uniqueProd` / 定理 `coe_uniqueProd`

English:
theorem coe_uniqueProd
  given: [Unique X]
  statement: ⇑(uniqueProd X Y) = Prod.snd
  proof: rfl

中文:
定理 coe_uniqueProd
  条件: [唯一 X]
  结论: ⇑(uniqueProd X Y) = 积类型.snd
  证明: rfl
-/
@[simp] theorem coe_uniqueProd [Unique X] : ⇑(uniqueProd X Y) = Prod.snd := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sumPiEquivProdPi` / `sumPiEquivProdPi` 的定义

English:
definition sumPiEquivProdPi
  signature: (S T : Type*) (A : S oplus T -> Type*)
  body: Equiv.sumPiEquivProdPi _
continuous_invFun := continuous_pi by rintro (s | t) <;> dsimp <;> fun_prop

中文:
定义 sumPiEquivProdPi
  签名: (S T : 类型) (A : S oplus T -> 类型)
  定义体: Equiv.sumPiEquivProdPi _
continuous_invFun := continuous_pi by rintro (s | t) <;> dsimp <;> fun_prop

Depends on / 依赖: Equiv.sumPiEquivProdPi, sumPiEquivProdPi
-/
def sumPiEquivProdPi (S T : Type*) (A : S oplus T -> Type*)
    [forall st, TopologicalSpace (A st)] :
    (Π (st : S oplus T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
continuous_invFun := continuous_pi by rintro (s | t) <;> dsimp <;> fun_prop

/-- The product `Π t : α, f t` of a family of topological spaces is homeomorphic to the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
@[simps! -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: {α : Type*} [Unique α] (f : α -> Type*) [forall x, TopologicalSpace (f x)]
  body: (Equiv.piUnique f).toHomeomorphOfContinuousOpen (continuous_apply default) (isOpenMap_eval _)

中文:
定义 piUnique
  签名: {α : 类型} [唯一 α] (f : α -> 类型) [对任意 x, 拓扑空间 (f x)]
  定义体: (Equiv.piUnique f).toHomeomorphOfContinuousOpen (continuous_apply default) (isOpenMap_eval _)

Depends on / 依赖: Equiv.piUnique, continuous_apply, isOpenMap_eval, piUnique, toHomeomorphOfContinuousOpen
-/
def piUnique {α : Type*} [Unique α] (f : α -> Type*) [forall x, TopologicalSpace (f x)] :
    (Π t, f t) ≃ₜ f default :=
  (Equiv.piUnique f).toHomeomorphOfContinuousOpen (continuous_apply default) (isOpenMap_eval _)

end prod

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps +simpRhs toEquiv, simps! -isSimp apply]
/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
  body: continuous_pi e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]

中文:
定义 piCongrLeft
  签名: {ι ι' : 类型} {Y : ι' -> 类型} [对任意 j, 拓扑空间 (Y j)]
  定义体: continuous_pi e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]

Depends on / 依赖: Equiv.piCongrLeft, Equiv.piCongrLeft_apply_apply, Equiv.toFun_as_coe, Pi.continuous_precomp, continuous_apply, continuous_invFun, continuous_pi, continuous_precomp, e.forall_congr_right.mp, forall_congr_right, piCongrLeft, piCongrLeft_apply_apply, toEquiv, toFun_as_coe
-/
def piCongrLeft {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (forall i, Y (e i)) ≃ₜ forall j, Y j where
continuous_toFun := continuous_pi e.forall_congr_right.mp fun i => by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
/--
lemma `piCongrLeft_refl` / 引理 `piCongrLeft_refl`

English:
lemma piCongrLeft_refl
  given: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: rfl

@[simp]

中文:
引理 piCongrLeft_refl
  条件: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: rfl

@[simp]
-/
lemma piCongrLeft_refl {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (forall i, X i) :=
  rfl

@[simp]
/--
lemma `piCongrLeft_symm_apply` / 引理 `piCongrLeft_symm_apply`

English:
lemma piCongrLeft_symm_apply
  statement: {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
  proof: rfl

@[simp]

中文:
引理 piCongrLeft_symm_apply
  结论: {ι ι' : 类型} {Y : ι' -> 类型} [对任意 j, 拓扑空间 (Y j)]
  证明: rfl

@[simp]
-/
lemma piCongrLeft_symm_apply {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (Y := Y) e).symm = (· <| e ·) :=
  rfl

@[simp]
/--
lemma `piCongrLeft_apply_apply` / 引理 `piCongrLeft_apply_apply`

English:
lemma piCongrLeft_apply_apply
  statement: {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
  proof: Equiv.piCongrLeft_apply_apply ..

中文:
引理 piCongrLeft_apply_apply
  结论: {ι ι' : 类型} {Y : ι' -> 类型} [对任意 j, 拓扑空间 (Y j)]
  证明: Equiv.piCongrLeft_apply_apply ..

Depends on / 依赖: Equiv.piCongrLeft_apply_apply, piCongrLeft_apply_apply
-/
lemma piCongrLeft_apply_apply {ι ι' : Type*} {Y : ι' -> Type*} [forall j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') (x : forall i, Y (e i)) (i : ι) : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

set_option backward.defeqAttrib.useBackward true in
/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalSpace (Y₁ i)]
  body: Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]

中文:
定义 piCongrRight
  签名: {ι : 类型} {Y₁ Y₂ : ι -> 类型} [对任意 i, 拓扑空间 (Y₁ i)]
  定义体: Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]

Depends on / 依赖: Equiv.piCongrRight, piCongrRight, toEquiv
-/
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalSpace (Y₁ i)]
    [forall i, TopologicalSpace (Y₂ i)] (F : forall i, Y₁ i ≃ₜ Y₂ i) : (forall i, Y₁ i) ≃ₜ forall i, Y₂ i where
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
/--
theorem `piCongrRight_symm` / 定理 `piCongrRight_symm`

English:
theorem piCongrRight_symm
  statement: {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalSpace (Y₁ i)]
  proof: rfl

中文:
定理 piCongrRight_symm
  结论: {ι : 类型} {Y₁ Y₂ : ι -> 类型} [对任意 i, 拓扑空间 (Y₁ i)]
  证明: rfl
-/
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι -> Type*} [forall i, TopologicalSpace (Y₁ i)]
    [forall i, TopologicalSpace (Y₂ i)] (F : forall i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
/--
Definition of `piCongr` / `piCongr` 的定义

English:
definition piCongr
  signature: {ι₁ ι₂ : Type*} {Y₁ : ι₁ -> Type*} {Y₂ : ι₂ -> Type*}
  body: (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

中文:
定义 piCongr
  签名: {ι₁ ι₂ : 类型} {Y₁ : ι₁ -> 类型} {Y₂ : ι₂ -> 类型}
  定义体: (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

Depends on / 依赖: Homeomorph, Homeomorph.piCongrLeft, Homeomorph.piCongrRight, piCongrLeft, piCongrRight
-/
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ -> Type*} {Y₂ : ι₂ -> Type*}
    [forall i₁, TopologicalSpace (Y₁ i₁)] [forall i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : forall i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (forall i₁, Y₁ i₁) ≃ₜ forall i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

/--
Definition of `ulift.` / `ulift.` 的定义

English:
definition ulift.{u,
  signature: v} {X
  body: Equiv.ulift

中文:
定义 ulift.{u,
  签名: v} {X
  定义体: Equiv.ulift

Depends on / 依赖: Equiv.ulift
-/
def ulift.{u, v} {X : Type v} [TopologicalSpace X] : ULift.{u, v} X ≃ₜ X where
  toEquiv := Equiv.ulift

set_option backward.isDefEq.respectTransparency false in
/-- The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism. -/
@[simps!]
/--
Definition of `sumArrowHomeomorphProdArrow` / `sumArrowHomeomorphProdArrow` 的定义

English:
definition sumArrowHomeomorphProdArrow
  signature: {ι ι' : Type*}
  body: Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    dsimp [Equiv.sumArrowEquivProdArrow]
    fun_prop
  continuous_invFun := continuous_pi fun i => match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuo

中文:
定义 sumArrowHomeomorphProdArrow
  签名: {ι ι' : 类型}
  定义体: Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    dsimp [Equiv.sumArrowEquivProdArrow]
    fun_prop
  continuous_invFun := continuous_pi fun i => match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuo

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, sumArrowEquivProdArrow
-/
def sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι oplus ι' -> X) ≃ₜ (ι -> X) × (ι' -> X) where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    dsimp [Equiv.sumArrowEquivProdArrow]
    fun_prop
  continuous_invFun := continuous_pi fun i => match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

/--
theorem `_root_.Fin.appendEquiv_eq_homeomorph` / 定理 `_root_.Fin.appendEquiv_eq_homeomorph`

English:
theorem _root_.Fin.appendEquiv_eq_homeomorph
  given: (m n : Nat)
  statement: Fin.appendEquiv m n =
  proof: by
  apply Equiv.symm_bijective.injective
  ext x i <;> simp

@[fun_prop]

中文:
定理 _root_.有限集.appendEquiv_eq_homeomorph
  条件: (m n : 自然数)
  结论: 有限集.appendEquiv m n =
  证明: by
  apply Equiv.symm_bijective.injective
  ext x i <;> simp

@[fun_prop]
-/
private theorem _root_.Fin.appendEquiv_eq_homeomorph (m n : Nat) : Fin.appendEquiv m n =
    (sumArrowHomeomorphProdArrow.symm.trans
    (piCongrLeft (Y := fun _ => X) finSumFinEquiv)).toEquiv := by
  apply Equiv.symm_bijective.injective
  ext x i <;> simp

@[fun_prop]
/--
theorem `_root_.Fin.continuous_append` / 定理 `_root_.Fin.continuous_append`

English:
theorem _root_.Fin.continuous_append
  given: (m n : Nat)
  proof: by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_homeomorph]
  exact Homeomorph.continuous_toFun _

中文:
定理 _root_.有限集.continuous_append
  条件: (m n : 自然数)
  证明: by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_homeomorph]
  exact Homeomorph.continuous_toFun _

Depends on / 依赖: Continuous, Fin.appendEquiv, Fin.appendEquiv_eq_homeomorph, Homeomorph, Homeomorph.continuous_toFun, appendEquiv, appendEquiv_eq_homeomorph, continuous_toFun
-/
theorem _root_.Fin.continuous_append (m n : Nat) :
    Continuous fun (p : (Fin m -> X) × (Fin n -> X)) => Fin.append p.1 p.2 := by
  suffices Continuous (Fin.appendEquiv m n) by exact this
  rw [Fin.appendEquiv_eq_homeomorph]
  exact Homeomorph.continuous_toFun _

/-- The natural homeomorphism between `(Fin m → X) × (Fin n → X)` and `Fin (m + n) → X`.
`Fin.appendEquiv` as a homeomorphism -/
@[simps!]
/--
Definition of `_root_.Fin.appendHomeomorph` / `_root_.Fin.appendHomeomorph` 的定义

English:
definition _root_.Fin.appendHomeomorph
  signature: (m n : Nat)
  body: Fin.appendEquiv m n

@[simp]

中文:
定义 _root_.有限集.appendHomeomorph
  签名: (m n : 自然数)
  定义体: Fin.appendEquiv m n

@[simp]

Depends on / 依赖: Fin.appendEquiv, appendEquiv
-/
def _root_.Fin.appendHomeomorph (m n : Nat) : (Fin m -> X) × (Fin n -> X) ≃ₜ (Fin (m + n) -> X) where
  toEquiv := Fin.appendEquiv m n

@[simp]
/--
theorem `_root_.Fin.appendHomeomorph_toEquiv` / 定理 `_root_.Fin.appendHomeomorph_toEquiv`

English:
theorem _root_.Fin.appendHomeomorph_toEquiv
  given: (m n : Nat)
  proof: rfl

中文:
定理 _root_.有限集.appendHomeomorph_toEquiv
  条件: (m n : 自然数)
  证明: rfl

Depends on / 依赖: Fin.appendEquiv, appendEquiv, toEquiv
-/
theorem _root_.Fin.appendHomeomorph_toEquiv (m n : Nat) :
    (Fin.appendHomeomorph (X := X) m n).toEquiv = Fin.appendEquiv m n :=
  rfl

section Distrib

variable {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
@[simps! apply symm_apply toEquiv]
/--
Definition of `sigmaProdDistrib` / `sigmaProdDistrib` 的定义

English:
definition sigmaProdDistrib
  signature: : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y
  body: Homeomorph.symm
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

中文:
定义 sigmaProdDistrib
  签名: : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y
  定义体: Homeomorph.symm
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

Depends on / 依赖: Equiv.sigmaProdDistrib, Homeomorph, Homeomorph.symm, IsOpenMap, IsOpenMap.id, continuous_sigma, continuous_sigmaMk, continuous_sigmaMk.fst, continuous_snd, isOpenMap_sigma, isOpenMap_sigmaMk, isOpenMap_sigmaMk.prodMap, prodMap, prodMk, sigmaProdDistrib, symm.toHomeomorphOfContinuousOpen, toHomeomorphOfContinuousOpen
-/
def sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y :=
Homeomorph.symm
    (Equiv.sigmaProdDistrib X Y).symm.toHomeomorphOfContinuousOpen
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prodMk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

end Distrib

set_option backward.defeqAttrib.useBackward true in
/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (ι X : Type*) [Unique ι] [TopologicalSpace X]
  body: Equiv.funUnique ι X

中文:
定义 funUnique
  签名: (ι X : 类型) [唯一 ι] [拓扑空间 X]
  定义体: Equiv.funUnique ι X

Depends on / 依赖: Equiv.funUnique, funUnique
-/
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι -> X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X

/-- Homeomorphism between dependent functions `Π i : Fin 2, X i` and `X 0 × X 1`. -/
@[simps! -fullyApplied]
/--
Definition of `piFinTwo.` / `piFinTwo.` 的定义

English:
definition piFinTwo.{u}
  signature: (X : Fin 2 -> Type u) [forall i, TopologicalSpace (X i)]
  body: piFinTwoEquiv X

中文:
定义 piFinTwo.{u}
  签名: (X : 有限集 2 -> 类型u) [对任意 i, 拓扑空间 (X i)]
  定义体: piFinTwoEquiv X

Depends on / 依赖: piFinTwoEquiv
-/
def piFinTwo.{u} (X : Fin 2 -> Type u) [forall i, TopologicalSpace (X i)] : (forall i, X i) ≃ₜ X 0 × X 1 where
  toEquiv := piFinTwoEquiv X

/-- Homeomorphism between `X² = Fin 2 → X` and `X × X`. -/
@[simps! -fullyApplied]
/--
Definition of `finTwoArrow` / `finTwoArrow` 的定义

English:
definition finTwoArrow
  signature: : (Fin 2 -> X) ≃ₜ X × X
  body: { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

中文:
定义 finTwoArrow
  签名: : (有限集 2 -> X) ≃ₜ X × X
  定义体: { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

Depends on / 依赖: finTwoArrowEquiv, piFinTwo, toEquiv
-/
def finTwoArrow : (Fin 2 -> X) ≃ₜ X × X :=
  { piFinTwo fun _ => X with toEquiv := finTwoArrowEquiv X }

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (e : X ≃ₜ Y) (s : Set X)
  body: e.continuous.continuousOn.mapsToRestrict (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

中文:
定义 像
  签名: (e : X ≃ₜ Y) (s : 集合 X)
  定义体: e.continuous.continuousOn.mapsToRestrict (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

Depends on / 依赖: continuous, continuousOn, e.continuous.continuousOn.mapsToRestrict, mapsToRestrict, mapsTo_image
-/
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.mapsToRestrict (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! -fullyApplied]
/--
Definition of `Set.univ` / `Set.univ` 的定义

English:
definition Set.univ
  signature: (X : Type*) [TopologicalSpace X]
  body: Equiv.Set.univ X

中文:
定义 集合.univ
  签名: (X : 类型) [拓扑空间 X]
  定义体: Equiv.Set.univ X
-/
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
/--
Definition of `Set.prod` / `Set.prod` 的定义

English:
definition Set.prod
  signature: (s : Set X) (t : Set Y)
  body: Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prodMk continuous_subtype_val.snd').subtype_mk _

中文:
定义 集合.乘积
  签名: (s : 集合 X) (t : 集合 Y)
  定义体: Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prodMk continuous_subtype_val.snd').subtype_mk _
-/
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prodMk continuous_subtype_val.snd').subtype_mk _

section

variable {ι : Type*}

/-- The topological space `Π i, Y i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not. -/
@[simps!]
/--
Definition of `piEquivPiSubtypeProd` / `piEquivPiSubtypeProd` 的定义

English:
definition piEquivPiSubtypeProd
  signature: (p : ι -> Prop) (Y : ι -> Type*) [forall i, TopologicalSpace (Y i)]
  body: Equiv.piEquivPiSubtypeProd p Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]

中文:
定义 piEquivPiSubtypeProd
  签名: (p : ι -> 命题) (Y : ι -> 类型) [对任意 i, 拓扑空间 (Y i)]
  定义体: Equiv.piEquivPiSubtypeProd p Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]

Depends on / 依赖: Equiv.piEquivPiSubtypeProd, piEquivPiSubtypeProd
-/
def piEquivPiSubtypeProd (p : ι -> Prop) (Y : ι -> Type*) [forall i, TopologicalSpace (Y i)]
    [DecidablePred p] : (forall i, Y i) ≃ₜ (forall i : { x // p x }, Y i) × forall i : { x // ¬p x }, Y i where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]

variable [DecidableEq ι] (i : ι)

/-- A product of topological spaces can be split as the binary product of one of the spaces and
  the product of all the remaining spaces. -/
@[simps!]
/--
Definition of `piSplitAt` / `piSplitAt` 的定义

English:
definition piSplitAt
  signature: (Y : ι -> Type*) [forall j, TopologicalSpace (Y j)]
  body: Equiv.piSplitAt i Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd

中文:
定义 piSplitAt
  签名: (Y : ι -> 类型) [对任意 j, 拓扑空间 (Y j)]
  定义体: Equiv.piSplitAt i Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd

Depends on / 依赖: Equiv.piSplitAt, piSplitAt
-/
def piSplitAt (Y : ι -> Type*) [forall j, TopologicalSpace (Y j)] :
    (forall j, Y j) ≃ₜ Y i × forall j : { j // j != i }, Y j where
  toEquiv := Equiv.piSplitAt i Y
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs with h
      · subst h
        exact continuous_fst
      · exact (continuous_apply _).comp continuous_snd

variable (Y)

/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps!]
/--
Definition of `funSplitAt` / `funSplitAt` 的定义

English:
definition funSplitAt
  signature: : (ι -> Y) ≃ₜ Y × ({ j // j != i } -> Y)
  body: piSplitAt i _

中文:
定义 funSplitAt
  签名: : (ι -> Y) ≃ₜ Y × ({ j // j != i } -> Y)
  定义体: piSplitAt i _

Depends on / 依赖: piSplitAt
-/
def funSplitAt : (ι -> Y) ≃ₜ Y × ({ j // j != i } -> Y) :=
  piSplitAt i _

end

end Homeomorph

namespace Topology.IsEmbedding

/-- Homeomorphism given an embedding. -/
@[simps! apply_coe]
/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: {f : X -> Y} (hf : IsEmbedding f)
  body: .toHomeomorphOfIsInducing Equiv.ofInjective f hf.injective
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

@[simp]

中文:
定义 toHomeomorph
  签名: {f : X -> Y} (hf : 是嵌入 f)
  定义体: .toHomeomorphOfIsInducing Equiv.ofInjective f hf.injective
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

@[simp]

Depends on / 依赖: Equiv.ofInjective, IsInducing, IsInducing.subtypeVal.of_comp_iff.mp, hf.injective, hf.toIsInducing, injective, ofInjective, of_comp_iff, subtypeVal, toHomeomorphOfIsInducing, toIsInducing
-/
noncomputable def toHomeomorph {f : X -> Y} (hf : IsEmbedding f) :
    X ≃ₜ Set.range f :=
.toHomeomorphOfIsInducing Equiv.ofInjective f hf.injective
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

@[simp]
/--
lemma `toHomeomorph_symm_apply` / 引理 `toHomeomorph_symm_apply`

English:
lemma toHomeomorph_symm_apply
  given: {f : X -> Y} (hf : IsEmbedding f) (x : X)
  proof: hf.toHomeomorph.injective (by ext; simp)

中文:
引理 toHomeomorph_symm_apply
  条件: {f : X -> Y} (hf : 是嵌入 f) (x : X)
  证明: hf.toHomeomorph.injective (by ext; simp)

Depends on / 依赖: hf.toHomeomorph.injective, injective, toHomeomorph
-/
lemma toHomeomorph_symm_apply {f : X -> Y} (hf : IsEmbedding f) (x : X) :
    hf.toHomeomorph.symm ⟨f x, by simp⟩ = x :=
  hf.toHomeomorph.injective (by ext; simp)

/-- A surjective embedding is a homeomorphism. -/
@[simps! apply]
/--
Definition of `toHomeomorphOfSurjective` / `toHomeomorphOfSurjective` 的定义

English:
definition toHomeomorphOfSurjective
  signature: {f : X -> Y}
  body: .toHomeomorphOfIsInducing hf.toIsInducing Equiv.ofBijective f ⟨hf.injective, hsurj⟩

中文:
定义 toHomeomorphOfSurjective
  签名: {f : X -> Y}
  定义体: .toHomeomorphOfIsInducing hf.toIsInducing Equiv.ofBijective f ⟨hf.injective, hsurj⟩

Depends on / 依赖: Equiv.ofBijective, hf.injective, hf.toIsInducing, injective, ofBijective, toHomeomorphOfIsInducing, toIsInducing
-/
noncomputable def toHomeomorphOfSurjective {f : X -> Y}
    (hf : IsEmbedding f) (hsurj : Function.Surjective f) : X ≃ₜ Y :=
.toHomeomorphOfIsInducing hf.toIsInducing Equiv.ofBijective f ⟨hf.injective, hsurj⟩

/--
Definition of `homeomorphImage` / `homeomorphImage` 的定义

English:
definition homeomorphImage
  signature: {f : X -> Y} (hf : IsEmbedding f) (s : Set X)
  body: (hf.comp .subtypeVal).toHomeomorph.trans .setCongr by simp [Set.range_comp]

中文:
定义 homeomorphImage
  签名: {f : X -> Y} (hf : 是嵌入 f) (s : 集合 X)
  定义体: (hf.comp .subtypeVal).toHomeomorph.trans .setCongr by simp [Set.range_comp]

Depends on / 依赖: Set.range_comp, hf.comp, range_comp, setCongr, subtypeVal, toHomeomorph, toHomeomorph.trans
-/
noncomputable def homeomorphImage {f : X -> Y} (hf : IsEmbedding f) (s : Set X) : s ≃ₜ f '' s :=
(hf.comp .subtypeVal).toHomeomorph.trans .setCongr by simp [Set.range_comp]

/--
Definition of `homeomorphOfSubsetRange` / `homeomorphOfSubsetRange` 的定义

English:
definition homeomorphOfSubsetRange
  signature: {f : X -> Y} (hf : IsEmbedding f)
  body: .trans .setCongr Set.image_preimage_eq_of_subset hs hf.homeomorphImage (f ⁻¹' s)

@[simp]

中文:
定义 homeomorphOfSubsetRange
  签名: {f : X -> Y} (hf : 是嵌入 f)
  定义体: .trans .setCongr Set.image_preimage_eq_of_subset hs hf.homeomorphImage (f ⁻¹' s)

@[simp]

Depends on / 依赖: Set.image_preimage_eq_of_subset, hf.homeomorphImage, homeomorphImage, image_preimage_eq_of_subset, setCongr
-/
noncomputable def homeomorphOfSubsetRange {f : X -> Y} (hf : IsEmbedding f)
    {s : Set Y} (hs : s subseteq Set.range f) : (f ⁻¹' s) ≃ₜ s :=
.trans .setCongr Set.image_preimage_eq_of_subset hs hf.homeomorphImage (f ⁻¹' s)

@[simp]
/--
theorem `homeomorphOfSubsetRange_apply_coe` / 定理 `homeomorphOfSubsetRange_apply_coe`

English:
theorem homeomorphOfSubsetRange_apply_coe
  statement: {f : X -> Y} (hf : IsEmbedding f)
  proof: rfl

中文:
定理 homeomorphOfSubsetRange_apply_coe
  结论: {f : X -> Y} (hf : 是嵌入 f)
  证明: rfl
-/
theorem homeomorphOfSubsetRange_apply_coe {f : X -> Y} (hf : IsEmbedding f)
    {s : Set Y} (hs : s subseteq Set.range f) (x : f ⁻¹' s) :
    ↑(hf.homeomorphOfSubsetRange hs x) = f ↑x := rfl

end Topology.IsEmbedding

/--
lemma `Topology.IsEmbedding.uliftMap` / 引理 `Topology.IsEmbedding.uliftMap`

English:
lemma Topology.IsEmbedding.uliftMap
  given: {f : X -> Y} (hf : IsEmbedding f)
  proof: .comp Homeomorph.ulift.symm.isEmbedding (.comp hf <| Homeomorph.ulift.isEmbedding)

中文:
引理 拓扑.是嵌入.uliftMap
  条件: {f : X -> Y} (hf : 是嵌入 f)
  证明: .comp Homeomorph.ulift.symm.isEmbedding (.comp hf <| Homeomorph.ulift.isEmbedding)

Depends on / 依赖: Homeomorph, Homeomorph.ulift.isEmbedding, Homeomorph.ulift.symm.isEmbedding, isEmbedding
-/
lemma Topology.IsEmbedding.uliftMap {f : X -> Y} (hf : IsEmbedding f) :
    IsEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isEmbedding (.comp hf <| Homeomorph.ulift.isEmbedding)

/--
lemma `Topology.IsOpenEmbedding.uliftMap` / 引理 `Topology.IsOpenEmbedding.uliftMap`

English:
lemma Topology.IsOpenEmbedding.uliftMap
  given: {f : X -> Y} (hf : IsOpenEmbedding f)
  proof: .comp Homeomorph.ulift.symm.isOpenEmbedding (.comp hf <| Homeomorph.ulift.isOpenEmbedding)

中文:
引理 拓扑.是开嵌入.uliftMap
  条件: {f : X -> Y} (hf : 是开嵌入 f)
  证明: .comp Homeomorph.ulift.symm.isOpenEmbedding (.comp hf <| Homeomorph.ulift.isOpenEmbedding)

Depends on / 依赖: Homeomorph, Homeomorph.ulift.isOpenEmbedding, Homeomorph.ulift.symm.isOpenEmbedding, isOpenEmbedding
-/
lemma Topology.IsOpenEmbedding.uliftMap {f : X -> Y} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isOpenEmbedding (.comp hf <| Homeomorph.ulift.isOpenEmbedding)

/--
lemma `Topology.IsClosedEmbedding.uliftMap` / 引理 `Topology.IsClosedEmbedding.uliftMap`

English:
lemma Topology.IsClosedEmbedding.uliftMap
  given: {f : X -> Y} (hf : IsClosedEmbedding f)
  proof: .comp Homeomorph.ulift.symm.isClosedEmbedding (.comp hf <| Homeomorph.ulift.isClosedEmbedding)

中文:
引理 拓扑.是闭嵌入.uliftMap
  条件: {f : X -> Y} (hf : 是闭嵌入 f)
  证明: .comp Homeomorph.ulift.symm.isClosedEmbedding (.comp hf <| Homeomorph.ulift.isClosedEmbedding)

Depends on / 依赖: Homeomorph, Homeomorph.ulift.isClosedEmbedding, Homeomorph.ulift.symm.isClosedEmbedding, isClosedEmbedding
-/
lemma Topology.IsClosedEmbedding.uliftMap {f : X -> Y} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isClosedEmbedding (.comp hf <| Homeomorph.ulift.isClosedEmbedding)

end

namespace Continuous

variable [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `continuous_symm_of_equiv_compact_to_t2` / 定理 `continuous_symm_of_equiv_compact_to_t2`

English:
theorem continuous_symm_of_equiv_compact_to_t2
  statement: [CompactSpace X] [T2Space Y] {f : X ≃ Y}
  proof: by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage_symm] at hC'

中文:
定理 continuous_symm_of_equiv_compact_to_t2
  结论: [紧空间 X] [T2空间 Y] {f : X ≃ Y}
  证明: by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage_symm] at hC'

Depends on / 依赖: Equiv.image_eq_preimage_symm, IsClosed, continuous_iff_isClosed, hC.isCompact.image, image_eq_preimage_symm, isClosed, isCompact
-/
theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace X] [T2Space Y] {f : X ≃ Y}
    (hf : Continuous f) : Continuous f.symm := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.isCompact.image hf).isClosed
  rwa [Equiv.image_eq_preimage_symm] at hC'

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv]
/--
Definition of `homeoOfEquivCompactToT2` / `homeoOfEquivCompactToT2` 的定义

English:
definition homeoOfEquivCompactToT2
  signature: [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f)
  body: { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }

中文:
定义 homeoOfEquivCompactToT2
  签名: [紧空间 X] [T2空间 Y] {f : X ≃ Y} (hf : 连续 f)
  定义体: { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }

Depends on / 依赖: continuous_invFun, continuous_symm_of_equiv_compact_to_t2, continuous_toFun, hf.continuous_symm_of_equiv_compact_to_t2
-/
def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }

end Continuous

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {W : Type*} [TopologicalSpace W] {f : X -> Y}

namespace IsHomeomorph
variable (hf : IsHomeomorph f)
include hf

/--
lemma `isClosedMap` / 引理 `isClosedMap`

English:
lemma isClosedMap
  statement: IsClosedMap f
  proof: (hf.homeomorph f).isClosedMap

中文:
引理 isClosedMap
  结论: 是闭映射 f
  证明: (hf.homeomorph f).isClosedMap
-/
protected lemma isClosedMap : IsClosedMap f := (hf.homeomorph f).isClosedMap
/--
lemma `isInducing` / 引理 `isInducing`

English:
lemma isInducing
  statement: IsInducing f
  proof: (hf.homeomorph f).isInducing

中文:
引理 isInducing
  结论: 是Inducing f
  证明: (hf.homeomorph f).isInducing

Depends on / 依赖: hf.homeomorph, homeomorph, isInducing
-/
lemma isInducing : IsInducing f := (hf.homeomorph f).isInducing
/--
lemma `isQuotientMap` / 引理 `isQuotientMap`

English:
lemma isQuotientMap
  statement: IsQuotientMap f
  proof: (hf.homeomorph f).isQuotientMap

中文:
引理 isQuotientMap
  结论: 是商映射 f
  证明: (hf.homeomorph f).isQuotientMap

Depends on / 依赖: hf.homeomorph, homeomorph, isQuotientMap
-/
lemma isQuotientMap : IsQuotientMap f := (hf.homeomorph f).isQuotientMap
/--
lemma `isEmbedding` / 引理 `isEmbedding`

English:
lemma isEmbedding
  statement: IsEmbedding f
  proof: (hf.homeomorph f).isEmbedding

中文:
引理 isEmbedding
  结论: 是嵌入 f
  证明: (hf.homeomorph f).isEmbedding

Depends on / 依赖: hf.homeomorph, homeomorph, isEmbedding
-/
lemma isEmbedding : IsEmbedding f := (hf.homeomorph f).isEmbedding
/--
lemma `isOpenEmbedding` / 引理 `isOpenEmbedding`

English:
lemma isOpenEmbedding
  statement: IsOpenEmbedding f
  proof: (hf.homeomorph f).isOpenEmbedding

中文:
引理 isOpenEmbedding
  结论: 是开嵌入 f
  证明: (hf.homeomorph f).isOpenEmbedding

Depends on / 依赖: hf.homeomorph, homeomorph, isOpenEmbedding
-/
lemma isOpenEmbedding : IsOpenEmbedding f := (hf.homeomorph f).isOpenEmbedding
/--
lemma `isClosedEmbedding` / 引理 `isClosedEmbedding`

English:
lemma isClosedEmbedding
  statement: IsClosedEmbedding f
  proof: (hf.homeomorph f).isClosedEmbedding

中文:
引理 isClosedEmbedding
  结论: 是闭嵌入 f
  证明: (hf.homeomorph f).isClosedEmbedding

Depends on / 依赖: hf.homeomorph, homeomorph, isClosedEmbedding
-/
lemma isClosedEmbedding : IsClosedEmbedding f := (hf.homeomorph f).isClosedEmbedding
/--
lemma `isDenseEmbedding` / 引理 `isDenseEmbedding`

English:
lemma isDenseEmbedding
  statement: IsDenseEmbedding f
  proof: (hf.homeomorph f).isDenseEmbedding

中文:
引理 isDenseEmbedding
  结论: 是稠密嵌入 f
  证明: (hf.homeomorph f).isDenseEmbedding

Depends on / 依赖: hf.homeomorph, homeomorph, isDenseEmbedding
-/
lemma isDenseEmbedding : IsDenseEmbedding f := (hf.homeomorph f).isDenseEmbedding

end IsHomeomorph

/--
lemma `isHomeomorph_iff_exists_homeomorph` / 引理 `isHomeomorph_iff_exists_homeomorph`

English:
lemma isHomeomorph_iff_exists_homeomorph
  statement: IsHomeomorph f ↔ exists h : X ≃ₜ Y, h = f
  proof: ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

中文:
引理 isHomeomorph_iff_存在_homeomorph
  结论: 是同胚 f ↔ 存在 h : X ≃ₜ Y, h = f
  证明: ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

Depends on / 依赖: h.isHomeomorph, hf.homeomorph, homeomorph, isHomeomorph
-/
lemma isHomeomorph_iff_exists_homeomorph : IsHomeomorph f ↔ exists h : X ≃ₜ Y, h = f :=
  ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

/--
lemma `isHomeomorph_iff_exists_inverse` / 引理 `isHomeomorph_iff_exists_inverse`

English:
lemma isHomeomorph_iff_exists_inverse
  statement: IsHomeomorph f ↔ Continuous f ∧ exists g : Y -> X,
  proof: by
  refine ⟨fun hf => ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ => ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

中文:
引理 isHomeomorph_iff_存在_inverse
  结论: 是同胚 f ↔ 连续 f ∧ 存在 g : Y -> X,
  证明: by
  refine ⟨fun hf => ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ => ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

Depends on / 依赖: Homeomorph, Homeomorph.mk, continuous, continuous_invFun, h.continuous_invFun, h.left_inv, h.right_inv, h.symm, hf.continuous, hf.homeomorph, homeomorph, isHomeomorph, left_inv, right_inv
-/
lemma isHomeomorph_iff_exists_inverse : IsHomeomorph f ↔ Continuous f ∧ exists g : Y -> X,
    LeftInverse g f ∧ RightInverse g f ∧ Continuous g := by
  refine ⟨fun hf => ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ => ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

/--
theorem `Equiv.isHomeomorph_iff` / 定理 `Equiv.isHomeomorph_iff`

English:
theorem Equiv.isHomeomorph_iff
  given: (e : X ≃ Y)
  proof: by
  rw [e.continuous_symm_iff]
  exact ⟨fun h => ⟨h.continuous, h.isOpenMap⟩, fun ⟨hc, ho⟩ => ⟨hc, ho, e.bijective⟩⟩

中文:
定理 等价.isHomeomorph_iff
  条件: (e : X ≃ Y)
  证明: by
  rw [e.continuous_symm_iff]
  exact ⟨fun h => ⟨h.continuous, h.isOpenMap⟩, fun ⟨hc, ho⟩ => ⟨hc, ho, e.bijective⟩⟩

Depends on / 依赖: bijective, continuous, continuous_symm_iff, e.bijective, e.continuous_symm_iff, h.continuous, h.isOpenMap, isOpenMap
-/
theorem Equiv.isHomeomorph_iff (e : X ≃ Y) :
    IsHomeomorph e ↔ Continuous e ∧ Continuous e.symm := by
  rw [e.continuous_symm_iff]
  exact ⟨fun h => ⟨h.continuous, h.isOpenMap⟩, fun ⟨hc, ho⟩ => ⟨hc, ho, e.bijective⟩⟩

/--
lemma `isHomeomorph_iff_isEmbedding_surjective` / 引理 `isHomeomorph_iff_isEmbedding_surjective`

English:
lemma isHomeomorph_iff_isEmbedding_surjective
  statement: IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where
  proof: ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

中文:
引理 isHomeomorph_iff_isEmbedding_surjective
  结论: 是同胚 f ↔ 是嵌入 f ∧ 满射 f where
  证明: ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

Depends on / 依赖: hf.isEmbedding, hf.surjective, isEmbedding, surjective
-/
lemma isHomeomorph_iff_isEmbedding_surjective : IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where
  mp hf := ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

/--
lemma `isHomeomorph_iff_isQuotientMap_injective` / 引理 `isHomeomorph_iff_isQuotientMap_injective`

English:
lemma isHomeomorph_iff_isQuotientMap_injective
  given: {f : X -> Y}
  proof: by
  refine ⟨fun h => ⟨h.isQuotientMap, h.injective⟩,
    fun h => ⟨h.1.continuous, fun s hs => ?_, h.2, h.1.surjective⟩⟩
  rwa [← h.1.isOpen_preimage, Set.preimage_image_eq _ h.2]

中文:
引理 isHomeomorph_iff_isQuotientMap_injective
  条件: {f : X -> Y}
  证明: by
  refine ⟨fun h => ⟨h.isQuotientMap, h.injective⟩,
    fun h => ⟨h.1.continuous, fun s hs => ?_, h.2, h.1.surjective⟩⟩
  rwa [← h.1.isOpen_preimage, Set.preimage_image_eq _ h.2]

Depends on / 依赖: Set.preimage_image_eq, continuous, h.injective, h.isQuotientMap, injective, isOpen_preimage, isQuotientMap, preimage_image_eq, surjective
-/
lemma isHomeomorph_iff_isQuotientMap_injective {f : X -> Y} :
    IsHomeomorph f ↔ IsQuotientMap f ∧ Injective f := by
  refine ⟨fun h => ⟨h.isQuotientMap, h.injective⟩,
    fun h => ⟨h.1.continuous, fun s hs => ?_, h.2, h.1.surjective⟩⟩
  rwa [← h.1.isOpen_preimage, Set.preimage_image_eq _ h.2]

/--
lemma `isHomeomorph_iff_continuous_isClosedMap_bijective` / 引理 `isHomeomorph_iff_continuous_isClosedMap_bijective`

English:
lemma isHomeomorph_iff_continuous_isClosedMap_bijective
  statement: IsHomeomorph f ↔
  proof: ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

中文:
引理 isHomeomorph_iff_continuous_isClosedMap_bijective
  结论: 是同胚 f ↔
  证明: ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

Depends on / 依赖: bijective, continuous, hf.bijective, hf.continuous, hf.isClosedMap, hu.isClosed_compl, image_compl_eq, isClosedMap, isClosed_compl, isClosed_compl_iff
-/
lemma isHomeomorph_iff_continuous_isClosedMap_bijective : IsHomeomorph f ↔
    Continuous f ∧ IsClosedMap f ∧ Function.Bijective f :=
  ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

/--
lemma `isHomeomorph_iff_continuous_bijective` / 引理 `isHomeomorph_iff_continuous_bijective`

English:
lemma isHomeomorph_iff_continuous_bijective
  given: [CompactSpace X] [T2Space Y]
  proof: by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf => ?_
  rw [eq_true hf.isClosedMap]; rw [true_and]

中文:
引理 isHomeomorph_iff_continuous_bijective
  条件: [紧空间 X] [T2空间 Y]
  证明: by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf => ?_
  rw [eq_true hf.isClosedMap]; rw [true_and]

Depends on / 依赖: and_congr_right, eq_true, hf.isClosedMap, isClosedMap, isHomeomorph_iff_continuous_isClosedMap_bijective, true_and
-/
lemma isHomeomorph_iff_continuous_bijective [CompactSpace X] [T2Space Y] :
    IsHomeomorph f ↔ Continuous f ∧ Bijective f := by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf => ?_
  rw [eq_true hf.isClosedMap]; rw [true_and]

/--
lemma `IsHomeomorph.sumMap` / 引理 `IsHomeomorph.sumMap`

English:
lemma IsHomeomorph.sumMap
  given: {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph g)
  proof: ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩

中文:
引理 是同胚.sumMap
  条件: {g : Z -> W} (hf : 是同胚 f) (hg : 是同胚 g)
  证明: ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩

Depends on / 依赖: sumMap
-/
lemma IsHomeomorph.sumMap {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Sum.map f g) := ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩

/--
lemma `IsHomeomorph.prodMap` / 引理 `IsHomeomorph.prodMap`

English:
lemma IsHomeomorph.prodMap
  given: {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph g)
  proof: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩

中文:
引理 是同胚.prodMap
  条件: {g : Z -> W} (hf : 是同胚 f) (hg : 是同胚 g)
  证明: ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩

Depends on / 依赖: prodMap
-/
lemma IsHomeomorph.prodMap {g : Z -> W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Prod.map f g) := ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩

/--
lemma `IsHomeomorph.sigmaMap` / 引理 `IsHomeomorph.sigmaMap`

English:
lemma IsHomeomorph.sigmaMap
  statement: {ι κ : Type*} {X : ι -> Type*} {Y : κ -> Type*}
  proof: by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i => (hg i).1, hf.2.sigma_map fun i => (hg i).2⟩

中文:
引理 是同胚.sigmaMap
  结论: {ι κ : 类型} {X : ι -> 类型} {Y : κ -> 类型}
  证明: by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i => (hg i).1, hf.2.sigma_map fun i => (hg i).2⟩

Depends on / 依赖: isEmbedding_sigmaMap, isHomeomorph_iff_isEmbedding_surjective, sigma_map, simp_rw
-/
lemma IsHomeomorph.sigmaMap {ι κ : Type*} {X : ι -> Type*} {Y : κ -> Type*}
    [forall i, TopologicalSpace (X i)] [forall i, TopologicalSpace (Y i)] {f : ι -> κ}
    (hf : Bijective f) {g : (i : ι) -> X i -> Y (f i)} (hg : forall i, IsHomeomorph (g i)) :
    IsHomeomorph (Sigma.map f g) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i => (hg i).1, hf.2.sigma_map fun i => (hg i).2⟩

/--
lemma `IsHomeomorph.pi_map` / 引理 `IsHomeomorph.pi_map`

English:
lemma IsHomeomorph.pi_map
  statement: {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: (Homeomorph.piCongrRight fun i => (h i).homeomorph (f i)).isHomeomorph

中文:
引理 是同胚.pi_map
  结论: {ι : 类型} {X Y : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: (Homeomorph.piCongrRight fun i => (h i).homeomorph (f i)).isHomeomorph

Depends on / 依赖: Homeomorph, Homeomorph.piCongrRight, homeomorph, isHomeomorph, piCongrRight
-/
lemma IsHomeomorph.pi_map {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, TopologicalSpace (Y i)] {f : (i : ι) -> X i -> Y i} (h : forall i, IsHomeomorph (f i)) :
    IsHomeomorph (fun (x : forall i, X i) i => f i (x i)) :=
  (Homeomorph.piCongrRight fun i => (h i).homeomorph (f i)).isHomeomorph

/--
Definition of `Homeomorph.ofDiscrete` / `Homeomorph.ofDiscrete` 的定义

English:
definition Homeomorph.ofDiscrete
  signature: [DiscreteTopology X] [DiscreteTopology Y] (f : X ≃ Y)
  body: f

中文:
定义 同胚.ofDiscrete
  签名: [离散拓扑 X] [离散拓扑 Y] (f : X ≃ Y)
  定义体: f
-/
def Homeomorph.ofDiscrete [DiscreteTopology X] [DiscreteTopology Y] (f : X ≃ Y) : X ≃ₜ Y where
  toEquiv := f

/--
theorem `Equiv.isHomeomorph_of_discrete` / 定理 `Equiv.isHomeomorph_of_discrete`

English:
theorem Equiv.isHomeomorph_of_discrete
  statement: [DiscreteTopology X] [DiscreteTopology Y]
  proof: (Homeomorph.ofDiscrete f).isHomeomorph

中文:
定理 等价.isHomeomorph_of_discrete
  结论: [离散拓扑 X] [离散拓扑 Y]
  证明: (Homeomorph.ofDiscrete f).isHomeomorph

Depends on / 依赖: Homeomorph, Homeomorph.ofDiscrete, isHomeomorph, ofDiscrete
-/
theorem Equiv.isHomeomorph_of_discrete [DiscreteTopology X] [DiscreteTopology Y]
    (f : X ≃ Y) : IsHomeomorph f :=
  (Homeomorph.ofDiscrete f).isHomeomorph

section

/--
Definition of `Topology.IsCoinducing.connectedComponentsHomeomorph` / `Topology.IsCoinducing.connectedComponentsHomeomorph` 的定义

English:
definition Topology.IsCoinducing.connectedComponentsHomeomorph
  signature: {f : X -> Y}
  body: IsHomeomorph.homeomorph hf.continuous.connectedComponentsMap by
    have hbij := hf.connectedComponentsMap_bijective hf'
    exact ⟨hf.continuous.connectedComponentsMap_continuous,
      hf.connectedComponentsMap.isOpenMap_of_injective hbij.injective, hbij⟩

中文:
定义 拓扑.是余inducing.connectedComponentsHomeomorph
  签名: {f : X -> Y}
  定义体: IsHomeomorph.homeomorph hf.continuous.connectedComponentsMap by
    have hbij := hf.connectedComponentsMap_bijective hf'
    exact ⟨hf.continuous.connectedComponentsMap_continuous,
      hf.connectedComponentsMap.isOpenMap_of_injective hbij.injective, hbij⟩

Depends on / 依赖: IsHomeomorph, IsHomeomorph.homeomorph, connectedComponentsMap, connectedComponentsMap_bijective, connectedComponentsMap_continuous, continuous, hbij.injective, hf.connectedComponentsMap.isOpenMap_of_injective, hf.connectedComponentsMap_bijective, hf.continuous.connectedComponentsMap, hf.continuous.connectedComponentsMap_continuous, homeomorph, injective, isOpenMap_of_injective
-/
noncomputable def Topology.IsCoinducing.connectedComponentsHomeomorph {f : X -> Y}
    (hf : IsCoinducing f) (hf' : forall y, IsConnected (f ⁻¹' {y})) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y :=
IsHomeomorph.homeomorph hf.continuous.connectedComponentsMap by
    have hbij := hf.connectedComponentsMap_bijective hf'
    exact ⟨hf.continuous.connectedComponentsMap_continuous,
      hf.connectedComponentsMap.isOpenMap_of_injective hbij.injective, hbij⟩

variable {f : X -> Y} (hf : Topology.IsCoinducing f) (hf' : forall y, IsConnected (f ⁻¹' {y}))

@[simp]
/--
lemma `Topology.IsCoinducing.connectedComponentsHomeomorph_mk` / 引理 `Topology.IsCoinducing.connectedComponentsHomeomorph_mk`

English:
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_mk
  given: (x : X)
  proof: rfl

@[simp]

中文:
引理 拓扑.是余inducing.connectedComponentsHomeomorph_mk
  条件: (x : X)
  证明: rfl

@[simp]
-/
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_mk (x : X) :
    hf.connectedComponentsHomeomorph hf' (.mk x) = .mk (f x) :=
  rfl

@[simp]
/--
lemma `Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply` / 引理 `Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply`

English:
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply
  given: (x : X)
  proof: (hf.connectedComponentsHomeomorph hf').injective (by simp)

中文:
引理 拓扑.是余inducing.connectedComponentsHomeomorph_symm_mk_apply
  条件: (x : X)
  证明: (hf.connectedComponentsHomeomorph hf').injective (by simp)

Depends on / 依赖: connectedComponentsHomeomorph, hf.connectedComponentsHomeomorph, injective
-/
lemma Topology.IsCoinducing.connectedComponentsHomeomorph_symm_mk_apply (x : X) :
    (hf.connectedComponentsHomeomorph hf').symm (.mk (f x)) = .mk x :=
  (hf.connectedComponentsHomeomorph hf').injective (by simp)

end
