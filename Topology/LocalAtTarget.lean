/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Properties of maps that are local at the target or at the source.

We show that the following properties of continuous maps are local at the target :
- `Topology.IsInducing`
- `IsOpenMap`
- `IsClosedMap`
- `Topology.IsEmbedding`
- `Topology.IsOpenEmbedding`
- `Topology.IsClosedEmbedding`
- `GeneralizingMap`

We show that the following properties of continuous maps are local at the source:
- `IsOpenMap`
- `GeneralizingMap`

-/

public section

open Filter Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α -> β}
variable {ι : Type*} {U : ι -> Opens β}

/--
theorem `Set.restrictPreimage_isInducing` / 定理 `Set.restrictPreimage_isInducing`

English:
theorem Set.restrictPreimage_isInducing
  given: (s : Set β) (h : IsInducing f)
  proof: by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← @Filter.comap_comap _ _ _ _ _ f,
    Function.comp_apply] at h ⊢
  intro a
  rw [← h]; rw [← IsInducing.subtypeVal.nhds_eq_comap]

alias Topology.IsInducing.restrictPr

中文:
定理 Set.restrictPreimage_isInducing
  条件: (s : Set β) (h : IsInducing f)
  证明: by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← @Filter.comap_comap _ _ _ _ _ f,
    Function.comp_apply] at h ⊢
  intro a
  rw [← h]; rw [← IsInducing.subtypeVal.nhds_eq_comap]

alias Topology.IsInducing.restrictPr

Depends on / 依赖: Filter, Filter.comap_comap, Function, Function.comp_apply, IsInducing, IsInducing.subtypeVal.nhds_eq_comap, IsInducing.subtypeVal.of_comp_iff, MapsTo, MapsTo.coe_restrict, coe_restrict, comap_comap, comp_apply, domRestrict_eq, isInducing_iff_nhds, nhds_eq_comap, of_comp_iff, restrictPreimage, simp_rw, subtypeVal
-/
theorem Set.restrictPreimage_isInducing (s : Set β) (h : IsInducing f) :
    IsInducing (s.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← @Filter.comap_comap _ _ _ _ _ f,
    Function.comp_apply] at h ⊢
  intro a
  rw [← h]; rw [← IsInducing.subtypeVal.nhds_eq_comap]

alias Topology.IsInducing.restrictPreimage := Set.restrictPreimage_isInducing

/--
theorem `Set.restrictPreimage_isEmbedding` / 定理 `Set.restrictPreimage_isEmbedding`

English:
theorem Set.restrictPreimage_isEmbedding
  given: (s : Set β) (h : IsEmbedding f)
  proof: ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding

中文:
定理 Set.restrictPreimage_isEmbedding
  条件: (s : Set β) (h : IsEmbedding f)
  证明: ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding

Depends on / 依赖: restrictPreimage
-/
theorem Set.restrictPreimage_isEmbedding (s : Set β) (h : IsEmbedding f) :
    IsEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Topology.IsEmbedding.restrictPreimage := Set.restrictPreimage_isEmbedding

/--
theorem `Set.restrictPreimage_isOpenEmbedding` / 定理 `Set.restrictPreimage_isOpenEmbedding`

English:
theorem Set.restrictPreimage_isOpenEmbedding
  given: (s : Set β) (h : IsOpenEmbedding f)
  proof: ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

中文:
定理 Set.restrictPreimage_isOpenEmbedding
  条件: (s : Set β) (h : IsOpenEmbedding f)
  证明: ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

Depends on / 依赖: continuous_subtype_val, continuous_subtype_val.isOpen_preimage, h.isOpen_range, isOpen_preimage, isOpen_range, range_restrictPreimage, restrictPreimage, s.range_restrictPreimage
-/
theorem Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
    IsOpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias Topology.IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

/--
theorem `Set.restrictPreimage_isClosedEmbedding` / 定理 `Set.restrictPreimage_isClosedEmbedding`

English:
theorem Set.restrictPreimage_isClosedEmbedding
  given: (s : Set β) (h : IsClosedEmbedding f)
  proof: ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

中文:
定理 Set.restrictPreimage_isClosedEmbedding
  条件: (s : Set β) (h : IsClosedEmbedding f)
  证明: ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.isClosed_preimage, h.isClosed_range, isClosed_preimage, isClosed_range, range_restrictPreimage, restrictPreimage, s.range_restrictPreimage, subtypeVal
-/
theorem Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding f) :
    IsClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias Topology.IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

/--
theorem `IsClosedMap.restrictPreimage` / 定理 `IsClosedMap.restrictPreimage`

English:
theorem IsClosedMap.restrictPreimage
  given: (H : IsClosedMap f) (s : Set β)
  proof: by
  intro t
  suffices forall u, IsClosed u -> Subtype.val ⁻¹' u = t ->
    exists v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

中文:
定理 IsClosedMap.restrictPreimage
  条件: (H : IsClosedMap f) (s : Set β)
  证明: by
  intro t
  suffices forall u, IsClosed u -> Subtype.val ⁻¹' u = t ->
    exists v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

Depends on / 依赖: IsClosed, Subtype, Subtype.val, image_restrictPreimage, isClosed_induced_iff, restrictPreimage, s.restrictPreimage
-/
theorem IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) :
    IsClosedMap (s.restrictPreimage f) := by
  intro t
  suffices forall u, IsClosed u -> Subtype.val ⁻¹' u = t ->
    exists v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

/--
theorem `IsOpenMap.restrictPreimage` / 定理 `IsOpenMap.restrictPreimage`

English:
theorem IsOpenMap.restrictPreimage
  given: (H : IsOpenMap f) (s : Set β)
  proof: by
  intro t
  suffices forall u, IsOpen u -> Subtype.val ⁻¹' u = t ->
    exists v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

中文:
定理 IsOpenMap.restrictPreimage
  条件: (H : IsOpenMap f) (s : Set β)
  证明: by
  intro t
  suffices forall u, IsOpen u -> Subtype.val ⁻¹' u = t ->
    exists v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

Depends on / 依赖: IsOpen, Subtype, Subtype.val, image_restrictPreimage, isOpen_induced_iff, restrictPreimage, s.restrictPreimage
-/
theorem IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) :
    IsOpenMap (s.restrictPreimage f) := by
  intro t
  suffices forall u, IsOpen u -> Subtype.val ⁻¹' u = t ->
    exists v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

/--
lemma `GeneralizingMap.restrictPreimage` / 引理 `GeneralizingMap.restrictPreimage`

English:
lemma GeneralizingMap.restrictPreimage
  given: (H : GeneralizingMap f) (s : Set β)
  proof: by
  intro x y h
  obtain ⟨a, ha, hy⟩ := H (h.map <| continuous_subtype_val (p := (· in s)))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]

中文:
引理 GeneralizingMap.restrictPreimage
  条件: (H : GeneralizingMap f) (s : Set β)
  证明: by
  intro x y h
  obtain ⟨a, ha, hy⟩ := H (h.map <| continuous_subtype_val (p := (· in s)))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]

Depends on / 依赖: continuous_subtype_val, h.map, subtype_specializes_iff
-/
lemma GeneralizingMap.restrictPreimage (H : GeneralizingMap f) (s : Set β) :
    GeneralizingMap (s.restrictPreimage f) := by
  intro x y h
  obtain ⟨a, ha, hy⟩ := H (h.map <| continuous_subtype_val (p := (· in s)))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]

/--
lemma `IsProperMap.restrictPreimage` / 引理 `IsProperMap.restrictPreimage`

English:
lemma IsProperMap.restrictPreimage
  given: (H : IsProperMap f) (s : Set β)
  proof: by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage _, fun y => ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff]; rw [image_val_preimage_restrictPreimage]; rw [image_singleton]
  exact H.isCompact_preimage isCompact_singleto

中文:
引理 IsProperMap.restrictPreimage
  条件: (H : Is命题erMap f) (s : Set β)
  证明: by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage _, fun y => ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff]; rw [image_val_preimage_restrictPreimage]; rw [image_singleton]
  exact H.isCompact_preimage isCompact_singleto

Depends on / 依赖: H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage, H.isCompact_preimage, IsEmbedding, IsEmbedding.subtypeVal.isCompact_iff, continuous, image_singleton, image_val_preimage_restrictPreimage, isClosedMap, isCompact_iff, isCompact_preimage, isCompact_singleton, isProperMap_iff_isClosedMap_and_compact_fibers, restrictPreimage, subtypeVal
-/
lemma IsProperMap.restrictPreimage (H : IsProperMap f) (s : Set β) :
    IsProperMap (s.restrictPreimage f) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨H.continuous.restrictPreimage, H.isClosedMap.restrictPreimage _, fun y => ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff]; rw [image_val_preimage_restrictPreimage]; rw [image_singleton]
  exact H.isCompact_preimage isCompact_singleton

/--
lemma `IsOpenQuotientMap.restrictPreimage` / 引理 `IsOpenQuotientMap.restrictPreimage`

English:
lemma IsOpenQuotientMap.restrictPreimage
  given: (H : IsOpenQuotientMap f) (s : Set β)
  proof: ⟨H.surjective.restrictPreimage _, H.continuous.restrictPreimage, H.isOpenMap.restrictPreimage _⟩

中文:
引理 IsOpenQuotientMap.restrictPreimage
  条件: (H : IsOpenQuotientMap f) (s : Set β)
  证明: ⟨H.surjective.restrictPreimage _, H.continuous.restrictPreimage, H.isOpenMap.restrictPreimage _⟩

Depends on / 依赖: H.continuous.restrictPreimage, H.isOpenMap.restrictPreimage, H.surjective.restrictPreimage, continuous, isOpenMap, restrictPreimage, surjective
-/
lemma IsOpenQuotientMap.restrictPreimage (H : IsOpenQuotientMap f) (s : Set β) :
    IsOpenQuotientMap (s.restrictPreimage f) :=
  ⟨H.surjective.restrictPreimage _, H.continuous.restrictPreimage, H.isOpenMap.restrictPreimage _⟩

namespace TopologicalSpace.IsOpenCover

section LocalAtTarget

variable {U : ι -> Opens β} {s : Set β} (hU : IsOpenCover U)
include hU

/--
theorem `isOpen_iff_inter` / 定理 `isOpen_iff_inter`

English:
theorem isOpen_iff_inter
  proof: by
  constructor
  · exact fun H i => H.inter (U i).isOpen
  · intro H
    simpa [← inter_iUnion, hU.iSup_set_eq_univ] using isOpen_iUnion H

中文:
定理 isOpen_iff_inter
  证明: by
  constructor
  · exact fun H i => H.inter (U i).isOpen
  · intro H
    simpa [← inter_iUnion, hU.iSup_set_eq_univ] using isOpen_iUnion H

Depends on / 依赖: H.inter, hU.iSup_set_eq_univ, iSup_set_eq_univ, inter_iUnion, isOpen, isOpen_iUnion
-/
theorem isOpen_iff_inter :
    IsOpen s ↔ forall i, IsOpen (s inter U i) := by
  constructor
  · exact fun H i => H.inter (U i).isOpen
  · intro H
    simpa [← inter_iUnion, hU.iSup_set_eq_univ] using isOpen_iUnion H

/--
theorem `isOpen_iff_coe_preimage` / 定理 `isOpen_iff_coe_preimage`

English:
theorem isOpen_iff_coe_preimage
  proof: by
  simp [hU.isOpen_iff_inter (s := s), (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_preimage_eq_inter_range]

中文:
定理 isOpen_iff_coe_preimage
  证明: by
  simp [hU.isOpen_iff_inter (s := s), (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_preimage_eq_inter_range]

Depends on / 依赖: hU.isOpen_iff_inter, image_preimage_eq_inter_range, isOpenEmbedding_subtypeVal, isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, isOpen_iff_image_isOpen, isOpen_iff_inter
-/
theorem isOpen_iff_coe_preimage :
    IsOpen s ↔ forall i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  simp [hU.isOpen_iff_inter (s := s), (U _).2.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
    image_preimage_eq_inter_range]

/--
theorem `isClosed_iff_coe_preimage` / 定理 `isClosed_iff_coe_preimage`

English:
theorem isClosed_iff_coe_preimage
  given: {s : Set β}
  proof: by
  simpa using hU.isOpen_iff_coe_preimage (s := sᶜ)

中文:
定理 isClosed_iff_coe_preimage
  条件: {s : Set β}
  证明: by
  simpa using hU.isOpen_iff_coe_preimage (s := sᶜ)

Depends on / 依赖: hU.isOpen_iff_coe_preimage, isOpen_iff_coe_preimage
-/
theorem isClosed_iff_coe_preimage {s : Set β} :
    IsClosed s ↔ forall i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using hU.isOpen_iff_coe_preimage (s := sᶜ)

/--
theorem `isLocallyClosed_iff_coe_preimage` / 定理 `isLocallyClosed_iff_coe_preimage`

English:
theorem isLocallyClosed_iff_coe_preimage
  given: {s : Set β}
  proof: by
  have (i : _) : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s :=
    (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
  simp [isLocallyClosed_iff_isOpen_coborder, hU.isOpen_iff_coe_preimage, this]

中文:
定理 isLocallyClosed_iff_coe_preimage
  条件: {s : Set β}
  证明: by
  have (i : _) : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s :=
    (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
  simp [isLocallyClosed_iff_isOpen_coborder, hU.isOpen_iff_coe_preimage, this]

Depends on / 依赖: Subtype, Subtype.val, coborder, coborder_preimage, hU.isOpen_iff_coe_preimage, isLocallyClosed_iff_isOpen_coborder, isOpen, isOpen.isOpenEmbedding_subtypeVal.coborder_preimage, isOpenEmbedding_subtypeVal, isOpen_iff_coe_preimage
-/
theorem isLocallyClosed_iff_coe_preimage {s : Set β} :
    IsLocallyClosed s ↔ forall i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  have (i : _) : coborder ((↑) ⁻¹' s : Set (U i)) = Subtype.val ⁻¹' coborder s :=
    (U i).isOpen.isOpenEmbedding_subtypeVal.coborder_preimage _
  simp [isLocallyClosed_iff_isOpen_coborder, hU.isOpen_iff_coe_preimage, this]

/--
theorem `isOpenMap_iff_restrictPreimage` / 定理 `isOpenMap_iff_restrictPreimage`

English:
theorem isOpenMap_iff_restrictPreimage
  proof: by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isOpen_iff_coe_preimage]
  intro i
  convert! H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun 

中文:
定理 isOpenMap_iff_restrictPreimage
  证明: by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isOpen_iff_coe_preimage]
  intro i
  convert! H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun 

Depends on / 依赖: Subtype, Subtype.coe_inj, c.symm, coe_inj, continuous_subtype_val, convert, h.restrictPreimage, hU.isOpen_iff_coe_preimage, hs.preimage, isOpen_iff_coe_preimage, preimage, restrictPreimage
-/
theorem isOpenMap_iff_restrictPreimage :
    IsOpenMap f ↔ forall i, IsOpenMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isOpen_iff_coe_preimage]
  intro i
  convert! H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩

/--
theorem `isClosedMap_iff_restrictPreimage` / 定理 `isClosedMap_iff_restrictPreimage`

English:
theorem isClosedMap_iff_restrictPreimage
  proof: by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isClosed_iff_coe_preimage]
  intro i
  convert! H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun 

中文:
定理 isClosedMap_iff_restrictPreimage
  证明: by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isClosed_iff_coe_preimage]
  intro i
  convert! H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun 

Depends on / 依赖: Subtype, Subtype.coe_inj, c.symm, coe_inj, convert, eq_compl_comm, eq_compl_comm.mpr, h.restrictPreimage, hU.isClosed_iff_coe_preimage, isClosed_iff_coe_preimage, restrictPreimage
-/
theorem isClosedMap_iff_restrictPreimage :
    IsClosedMap f ↔ forall i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, fun H s hs => ?_⟩
  rw [hU.isClosed_iff_coe_preimage]
  intro i
  convert! H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (exists y, y in s ∧ f y = x) ↔ exists y, y in s ∧ f y in U i ∧ f y = x by simpa [← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, by tauto⟩

/--
theorem `isInducing_iff_restrictPreimage` / 定理 `isInducing_iff_restrictPreimage`

English:
theorem isInducing_iff_restrictPreimage
  given: (h : Continuous f)
  proof: by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← Filter.comap_comap]
  constructor
  · intro H i x
    rw [Function.comp_apply]; rw [← H]; rw [← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :

中文:
定理 isInducing_iff_restrictPreimage
  条件: (h : Continuous f)
  证明: by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← Filter.comap_comap]
  constructor
  · intro H i x
    rw [Function.comp_apply]; rw [← H]; rw [← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :

Depends on / 依赖: Filter, Filter.comap_comap, Function, Function.comp_apply, IsInducing, IsInducing.subtypeVal.nhds_eq_comap, IsInducing.subtypeVal.of_comp_iff, MapsTo, MapsTo.coe_restrict, Opens.mem_iSup.mp, coe_restrict, comap_comap, comp_apply, domRestrict_eq, hU.iSup_eq_top, iSup_eq_top, isInducing_iff_nhds, isOpenEmbedding_subtypeVal, map_nhds_eq, mem_iSup
-/
theorem isInducing_iff_restrictPreimage (h : Continuous f) :
    IsInducing f ↔ forall i, IsInducing ((U i).1.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, domRestrict_eq, ← Filter.comap_comap]
  constructor
  · intro H i x
    rw [Function.comp_apply]; rw [← H]; rw [← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x in iSup U by simp [hU.iSup_eq_top])
    simpa [← ((h.1 _ (U i).2).isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hi⟩, H i ⟨x, hi⟩,
      subtype_coe_map_comap] using preimage_mem_comap ((U i).2.mem_nhds hi)

/--
theorem `isEmbedding_iff_restrictPreimage` / 定理 `isEmbedding_iff_restrictPreimage`

English:
theorem isEmbedding_iff_restrictPreimage
  given: (h : Continuous f)
  proof: by
  simpa [isEmbedding_iff, forall_and] using and_congr (hU.isInducing_iff_restrictPreimage h)
    (injective_iff_injective_of_iUnion_eq_univ hU.iSup_set_eq_univ)

中文:
定理 isEmbedding_iff_restrictPreimage
  条件: (h : Continuous f)
  证明: by
  simpa [isEmbedding_iff, forall_and] using and_congr (hU.isInducing_iff_restrictPreimage h)
    (injective_iff_injective_of_iUnion_eq_univ hU.iSup_set_eq_univ)

Depends on / 依赖: and_congr, forall_and, hU.iSup_set_eq_univ, hU.isInducing_iff_restrictPreimage, iSup_set_eq_univ, injective_iff_injective_of_iUnion_eq_univ, isEmbedding_iff, isInducing_iff_restrictPreimage
-/
theorem isEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsEmbedding f ↔ forall i, IsEmbedding ((U i).1.restrictPreimage f) := by
  simpa [isEmbedding_iff, forall_and] using and_congr (hU.isInducing_iff_restrictPreimage h)
    (injective_iff_injective_of_iUnion_eq_univ hU.iSup_set_eq_univ)

/--
theorem `isOpenEmbedding_iff_restrictPreimage` / 定理 `isOpenEmbedding_iff_restrictPreimage`

English:
theorem isOpenEmbedding_iff_restrictPreimage
  given: (h : Continuous f)
  proof: by
  simp_rw [isOpenEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isOpen_iff_coe_preimage

中文:
定理 isOpenEmbedding_iff_restrictPreimage
  条件: (h : Continuous f)
  证明: by
  simp_rw [isOpenEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isOpen_iff_coe_preimage

Depends on / 依赖: and_congr, forall_and, hU.isEmbedding_iff_restrictPreimage, hU.isOpen_iff_coe_preimage, isEmbedding_iff_restrictPreimage, isOpenEmbedding_iff, isOpen_iff_coe_preimage, range_restrictPreimage, simp_rw
-/
theorem isOpenEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsOpenEmbedding f ↔ forall i, IsOpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isOpenEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isOpen_iff_coe_preimage

/--
theorem `isClosedEmbedding_iff_restrictPreimage` / 定理 `isClosedEmbedding_iff_restrictPreimage`

English:
theorem isClosedEmbedding_iff_restrictPreimage
  given: (h : Continuous f)
  proof: by
  simp_rw [isClosedEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isClosed_iff_coe_preimage

中文:
定理 isClosedEmbedding_iff_restrictPreimage
  条件: (h : Continuous f)
  证明: by
  simp_rw [isClosedEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isClosed_iff_coe_preimage

Depends on / 依赖: and_congr, forall_and, hU.isClosed_iff_coe_preimage, hU.isEmbedding_iff_restrictPreimage, isClosedEmbedding_iff, isClosed_iff_coe_preimage, isEmbedding_iff_restrictPreimage, range_restrictPreimage, simp_rw
-/
theorem isClosedEmbedding_iff_restrictPreimage (h : Continuous f) :
    IsClosedEmbedding f ↔ forall i, IsClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isClosedEmbedding_iff, forall_and]
  apply and_congr
  · exact hU.isEmbedding_iff_restrictPreimage h
  · simp_rw [range_restrictPreimage]
    exact hU.isClosed_iff_coe_preimage

/--
theorem `isHomeomorph_iff_restrictPreimage` / 定理 `isHomeomorph_iff_restrictPreimage`

English:
theorem isHomeomorph_iff_restrictPreimage
  given: (h : Continuous f)
  proof: by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective, forall_and,
    ← isEmbedding_iff_restrictPreimage hU h,
    surjective_iff_surjective_of_iUnion_eq_univ hU.iSup_set_eq_univ, Opens.carrier_eq_coe]

omit [TopologicalSpace α] in

中文:
定理 isHomeomorph_iff_restrictPreimage
  条件: (h : Continuous f)
  证明: by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective, forall_and,
    ← isEmbedding_iff_restrictPreimage hU h,
    surjective_iff_surjective_of_iUnion_eq_univ hU.iSup_set_eq_univ, Opens.carrier_eq_coe]

omit [TopologicalSpace α] in

Depends on / 依赖: Opens.carrier_eq_coe, carrier_eq_coe, forall_and, hU.iSup_set_eq_univ, iSup_set_eq_univ, isEmbedding_iff_restrictPreimage, isHomeomorph_iff_isEmbedding_surjective, simp_rw, surjective_iff_surjective_of_iUnion_eq_univ
-/
theorem isHomeomorph_iff_restrictPreimage (h : Continuous f) :
    IsHomeomorph f ↔ forall i, IsHomeomorph ((U i).1.restrictPreimage f) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective, forall_and,
    ← isEmbedding_iff_restrictPreimage hU h,
    surjective_iff_surjective_of_iUnion_eq_univ hU.iSup_set_eq_univ, Opens.carrier_eq_coe]

omit [TopologicalSpace α] in
/--
theorem `denseRange_iff_restrictPreimage` / 定理 `denseRange_iff_restrictPreimage`

English:
theorem denseRange_iff_restrictPreimage
  proof: by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, 

中文:
定理 denseRange_iff_restrictPreimage
  证明: by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, 

Depends on / 依赖: Opens.carrier_eq_coe, Set.range_restrictPreimage, Set.univ_subset_iff, SetLike, SetLike.coe_sort_coe, SetLike.mem_coe, Subtype, Subtype.range_coe_subtype, carrier_eq_coe, coe_sort_coe, continuous_subtype_val, denseRange_iff_closure_range, hU.iSup_set_eq_univ.symm, iSup_set_eq_univ, iUnion_subset_iff, iff_iff_eq, isOpenEmbedding_subtypeVal, isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage, isOpenMap, mem_coe
-/
theorem denseRange_iff_restrictPreimage :
    DenseRange f ↔ forall i, DenseRange ((U i).1.restrictPreimage f) := by
  simp_rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← (U _).2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
  simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe, preimage_eq_univ_iff,
    Subtype.range_coe_subtype, SetLike.mem_coe]
  rw [← iUnion_subset_iff]; rw [← Set.univ_subset_iff]; rw [iff_iff_eq]
  congr 1
  exact hU.iSup_set_eq_univ.symm

/--
lemma `generalizingMap_iff_restrictPreimage` / 引理 `generalizingMap_iff_restrictPreimage`

English:
lemma generalizingMap_iff_restrictPreimage
  proof: by
  refine ⟨fun hf i => hf.restrictPreimage _, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, 

中文:
引理 generalizingMap_iff_restrictPreimage
  证明: by
  refine ⟨fun hf i => hf.restrictPreimage _, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, 

Depends on / 依赖: exists_mem, hU.exists_mem, hf.restrictPreimage, restrictPreimage, stableUnderGeneralization, subtype_specializes_iff
-/
lemma generalizingMap_iff_restrictPreimage :
    GeneralizingMap f ↔ forall i, GeneralizingMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun hf i => hf.restrictPreimage _, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, ?_, congr(($heq).val)⟩
  rwa [subtype_specializes_iff] at ha

end LocalAtTarget

section LocalAtSource

variable {U : ι -> Opens α} (hU : IsOpenCover U)
include hU

/--
lemma `isOpenMap_iff_comp` / 引理 `isOpenMap_iff_comp`

English:
lemma isOpenMap_iff_comp
  statement: IsOpenMap f ↔ forall i, IsOpenMap (f ∘ ((↑) : U i -> α))
  proof: by
  refine ⟨fun hf i => hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf => ?_⟩
  intro V hV
  convert! isOpen_iUnion (fun i => hf i _ <| isOpen_induced hV)
  simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
    Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hU.

中文:
引理 isOpenMap_iff_comp
  结论: IsOpenMap f ↔ 对任意 i, IsOpenMap (f ∘ ((↑) : U i -> α))
  证明: by
  refine ⟨fun hf i => hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf => ?_⟩
  intro V hV
  convert! isOpen_iUnion (fun i => hf i _ <| isOpen_induced hV)
  simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
    Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hU.

Depends on / 依赖: Set.image_comp, Set.image_iUnion, Set.image_preimage_eq_inter_range, SetLike, SetLike.setOfPred_mem_eq, Subtype, Subtype.range_coe_subtype, convert, hU.iUnion_inter, hf.comp, iUnion_inter, image_comp, image_iUnion, image_preimage_eq_inter_range, isOpenEmbedding, isOpenMap, isOpen_iUnion, isOpen_induced, range_coe_subtype, setOfPred_mem_eq
-/
lemma isOpenMap_iff_comp : IsOpenMap f ↔ forall i, IsOpenMap (f ∘ ((↑) : U i -> α)) := by
  refine ⟨fun hf i => hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf => ?_⟩
  intro V hV
  convert! isOpen_iUnion (fun i => hf i _ <| isOpen_induced hV)
  simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
    Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hU.iUnion_inter]

/--
lemma `generalizingMap_iff_comp` / 引理 `generalizingMap_iff_comp`

English:
lemma generalizingMap_iff_comp
  proof: by
  refine ⟨fun hf i => ((U i).isOpenEmbedding'.generalizingMap).comp hf, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i -> α)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

中文:
引理 generalizingMap_iff_comp
  证明: by
  refine ⟨fun hf i => ((U i).isOpenEmbedding'.generalizingMap).comp hf, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i -> α)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

Depends on / 依赖: a.val, continuous, exists_mem, generalizingMap, hU.exists_mem, ha.map, isOpenEmbedding, replace
-/
lemma generalizingMap_iff_comp :
    GeneralizingMap f ↔ forall i, GeneralizingMap (f ∘ ((↑) : U i -> α)) := by
  refine ⟨fun hf i => ((U i).isOpenEmbedding'.generalizingMap).comp hf, fun hf => fun x y h => ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i -> α)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

end LocalAtSource

end TopologicalSpace.IsOpenCover


-- TODO : the lemma name does not match the content (there is no hypothesis `iSup_eq_top`!)
/--
theorem `isEmbedding_of_iSup_eq_top_of_preimage_subset_range` / 定理 `isEmbedding_of_iSup_eq_top_of_preimage_subset_range`

English:
theorem isEmbedding_of_iSup_eq_top_of_preimage_subset_range
  proof: by
  wlog hU' : iSup U = ⊤
  · let f₀ : X -> Set.range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
    suffices IsEmbedding f₀ from IsEmbedding.subtypeVal.comp this
    have hU'' : (⨆ i, (U i).comap ⟨Subtype.val, continuous_subtype_val⟩ :
        Opens (Set.range f)) = ⊤ := by
      rw [← top_le_iff]
      simpa 

中文:
定理 isEmbedding_of_iSup_eq_top_of_preimage_subset_range
  证明: by
  wlog hU' : iSup U = ⊤
  · let f₀ : X -> Set.range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
    suffices IsEmbedding f₀ from IsEmbedding.subtypeVal.comp this
    have hU'' : (⨆ i, (U i).comap ⟨Subtype.val, continuous_subtype_val⟩ :
        Opens (Set.range f)) = ⊤ := by
      rw [← top_le_iff]
      simpa 

Depends on / 依赖: IsEmbedding, IsEmbedding.of_comp, IsEmbedding.subtypeVal.comp, IsOpenCover, IsOpenCover.mk, Set.range, Set.range_subset_iff, SetLike, SetLike.le_def, Subtype, Subtype.val, continuous_subtype_val, fun_prop, le_def, of_comp, range_subset_iff, subtypeVal, top_le_iff
-/
theorem isEmbedding_of_iSup_eq_top_of_preimage_subset_range
    {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X -> Y) (h : Continuous f) {ι : Type*}
    (U : ι -> Opens Y) (hU : Set.range f subseteq (iSup U :))
    (V : ι -> Type*) [forall i, TopologicalSpace (V i)]
    (iV : forall i, V i -> X) (hiV : forall i, Continuous (iV i)) (hV : forall i, f ⁻¹' U i subseteq Set.range (iV i))
    (hV' : forall i, IsEmbedding (f ∘ iV i)) : IsEmbedding f := by
  wlog hU' : iSup U = ⊤
  · let f₀ : X -> Set.range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
    suffices IsEmbedding f₀ from IsEmbedding.subtypeVal.comp this
    have hU'' : (⨆ i, (U i).comap ⟨Subtype.val, continuous_subtype_val⟩ :
        Opens (Set.range f)) = ⊤ := by
      rw [← top_le_iff]
      simpa [Set.range_subset_iff, SetLike.le_def] using hU
    refine this _ ?_ _ ?_ V iV hiV ?_ ?_ hU''
    · fun_prop
    · rw [hU'']; simp
    · exact hV
    · exact fun i => IsEmbedding.of_comp (by fun_prop) continuous_subtype_val (hV' i)
  rw [(IsOpenCover.mk hU').isEmbedding_iff_restrictPreimage h]
  intro i
  let f' := (Subtype.val ∘ (f ⁻¹' U i).restrictPreimage (iV i))
  have : IsEmbedding f' :=
    IsEmbedding.subtypeVal.comp ((IsEmbedding.of_comp (hiV i) h (hV' _)).restrictPreimage _)
  have hf' : Set.range f' = f ⁻¹' U i := by
    simpa [f', Set.range_comp, Set.range_restrictPreimage] using hV i
  let e := this.toHomeomorph.trans (Homeomorph.setCongr hf')
  refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
  convert! ((hV' i).comp IsEmbedding.subtypeVal).comp e.symm.isEmbedding
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp
  rfl
