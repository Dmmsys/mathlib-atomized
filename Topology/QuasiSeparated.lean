/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.NoetherianSpace

/-!
# Quasi-separated spaces

A topological space is quasi-separated if the intersections of any pairs of compact open subsets
are still compact.
Notable examples include spectral spaces, Noetherian spaces, and Hausdorff spaces.

A non-example is the interval `[0, 1]` with doubled origin: the two copies of `[0, 1]` are compact
open subsets, but their intersection `(0, 1]` is not.

## Main results

- `IsQuasiSeparated`: A subset `s` of a topological space is quasi-separated if the intersections
  of any pairs of compact open subsets of `s` are still compact.
- `QuasiSeparatedSpace`: A topological space is quasi-separated if the intersections of any pairs
  of compact open subsets are still compact.
- `QuasiSeparatedSpace.of_isOpenEmbedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/

@[expose] public section

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α -> β}

/--
Definition of `IsQuasiSeparated` / `IsQuasiSeparated` 的定义

English:
definition IsQuasiSeparated
  signature: (s : Set α)
  body: forall U V : Set α, U subseteq s -> IsOpen U -> IsCompact U -> V subseteq s -> IsOpen V -> IsCompact V -> IsCompact (U inter V)

中文:
定义 IsQuasiSeparated
  签名: (s : 集合 α)
  定义体: forall U V : Set α, U subseteq s -> IsOpen U -> IsCompact U -> V subseteq s -> IsOpen V -> IsCompact V -> IsCompact (U inter V)

Depends on / 依赖: IsCompact, IsOpen, subseteq
-/
def IsQuasiSeparated (s : Set α) : Prop :=
  forall U V : Set α, U subseteq s -> IsOpen U -> IsCompact U -> V subseteq s -> IsOpen V -> IsCompact V -> IsCompact (U inter V)

/-- A topological space is quasi-separated if the intersections of any pairs of compact open
subsets are still compact. -/
@[mk_iff]
/--
Definition of `QuasiSeparatedSpace` / `QuasiSeparatedSpace` 的定义

English:
class QuasiSeparatedSpace
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (1):
    - inter_isCompact : forall U V : Set α, IsOpen U -> IsCompact U -> IsOpen V -> IsCompact V -> IsCompact (U inter V)

中文:
类 拟分离空间
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (1 个):
    - inter_isCompact : 对任意 U V : 集合 α, 是开集 U -> 是紧集 U -> 是开集 V -> 是紧集 V -> 是紧集 (U inter V)
-/
class QuasiSeparatedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of two open compact subsets of a quasi-separated space is compact. -/
  inter_isCompact :
    forall U V : Set α, IsOpen U -> IsCompact U -> IsOpen V -> IsCompact V -> IsCompact (U inter V)

/--
theorem `isQuasiSeparated_univ_iff` / 定理 `isQuasiSeparated_univ_iff`

English:
theorem isQuasiSeparated_univ_iff
  given: {α : Type*} [TopologicalSpace α]
  proof: by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]

中文:
定理 isQuasiSeparated_univ_iff
  条件: {α : 类型} [拓扑空间 α]
  证明: by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]

Depends on / 依赖: IsQuasiSeparated, quasiSeparatedSpace_iff
-/
theorem isQuasiSeparated_univ_iff {α : Type*} [TopologicalSpace α] :
    IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α := by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]

/--
theorem `isQuasiSeparated_univ` / 定理 `isQuasiSeparated_univ`

English:
theorem isQuasiSeparated_univ
  given: {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpace α]
  proof: isQuasiSeparated_univ_iff.mpr inferInstance

中文:
定理 isQuasiSeparated_univ
  条件: {α : 类型} [拓扑空间 α] [拟分离空间 α]
  证明: isQuasiSeparated_univ_iff.mpr inferInstance

Depends on / 依赖: isQuasiSeparated_univ_iff, isQuasiSeparated_univ_iff.mpr
-/
theorem isQuasiSeparated_univ {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpace α] :
    IsQuasiSeparated (Set.univ : Set α) :=
  isQuasiSeparated_univ_iff.mpr inferInstance

/--
theorem `IsQuasiSeparated.image_of_isEmbedding` / 定理 `IsQuasiSeparated.image_of_isEmbedding`

English:
theorem IsQuasiSeparated.image_of_isEmbedding
  statement: {s : Set α} (H : IsQuasiSeparated s)
  proof: by
  intro U V hU hU' hU'' hV hV' hV''
  convert!
    (H (f ⁻¹' U) (f ⁻¹' V) ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image
      h.continuous
  · symm
    rw [← Set.preimage_inter]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert! hU''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert! hV''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)

中文:
定理 IsQuasiSeparated.image_of_isEmbedding
  结论: {s : 集合 α} (H : IsQuasiSeparated s)
  证明: by
  intro U V hU hU' hU'' hV hV' hV''
  convert!
    (H (f ⁻¹' U) (f ⁻¹' V) ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image
      h.continuous
  · symm
    rw [← Set.preimage_inter]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert! hU''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert! hV''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)

Depends on / 依赖: Set.image_preimage_eq_inter_range, Set.image_subset_range, Set.inter, Set.inter_eq_left, Set.inter_subset_left.trans, Set.preimage_inter, Set.subset_univ, continuous, convert, h.continuous, h.injective.injOn.mem_image_iff, h.isCompact_iff, hU.trans, image_preimage_eq_inter_range, image_subset_range, injective, inter_eq_left, inter_subset_left, isCompact_iff, mem_image_iff
-/
theorem IsQuasiSeparated.image_of_isEmbedding {s : Set α} (H : IsQuasiSeparated s)
    (h : IsEmbedding f) : IsQuasiSeparated (f '' s) := by
  intro U V hU hU' hU'' hV hV' hV''
  convert!
    (H (f ⁻¹' U) (f ⁻¹' V) ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image
      h.continuous
  · symm
    rw [← Set.preimage_inter]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert! hU''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert! hV''
    rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)

/--
theorem `IsQuasiSeparated.of_subset` / 定理 `IsQuasiSeparated.of_subset`

English:
theorem IsQuasiSeparated.of_subset
  given: {s t : Set α} (ht : IsQuasiSeparated t) (h : s subseteq t)
  proof: by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''

中文:
定理 IsQuasiSeparated.of_subset
  条件: {s t : 集合 α} (ht : IsQuasiSeparated t) (h : s subseteq t)
  证明: by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''

Depends on / 依赖: hU.trans, hV.trans
-/
theorem IsQuasiSeparated.of_subset {s t : Set α} (ht : IsQuasiSeparated t) (h : s subseteq t) :
    IsQuasiSeparated s := by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''

/--
theorem `Topology.IsOpenEmbedding.isQuasiSeparated_iff` / 定理 `Topology.IsOpenEmbedding.isQuasiSeparated_iff`

English:
theorem Topology.IsOpenEmbedding.isQuasiSeparated_iff
  given: (h : IsOpenEmbedding f) {s : Set α}
  proof: by
  refine ⟨fun hs => hs.image_of_isEmbedding h.isEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.isEmbedding.isCompact_iff]; rw [Set.image_inter h.injective]
  exact
    H (f '' U) (f '' V) (image_mono hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (image_mono hV) (h.isOpenMap _ hV') (hV''.image h.continuous)

中文:
定理 拓扑.是开嵌入.isQuasiSeparated_iff
  条件: (h : 是开嵌入 f) {s : 集合 α}
  证明: by
  refine ⟨fun hs => hs.image_of_isEmbedding h.isEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.isEmbedding.isCompact_iff]; rw [Set.image_inter h.injective]
  exact
    H (f '' U) (f '' V) (image_mono hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (image_mono hV) (h.isOpenMap _ hV') (hV''.image h.continuous)

Depends on / 依赖: Set.image_inter, continuous, h.continuous, h.injective, h.isEmbedding, h.isEmbedding.isCompact_iff, h.isOpenMap, hs.image_of_isEmbedding, image_inter, image_mono, image_of_isEmbedding, injective, isCompact_iff, isEmbedding, isOpenMap
-/
theorem Topology.IsOpenEmbedding.isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} :
    IsQuasiSeparated s ↔ IsQuasiSeparated (f '' s) := by
  refine ⟨fun hs => hs.image_of_isEmbedding h.isEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.isEmbedding.isCompact_iff]; rw [Set.image_inter h.injective]
  exact
    H (f '' U) (f '' V) (image_mono hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (image_mono hV) (h.isOpenMap _ hV') (hV''.image h.continuous)

/--
lemma `Topology.IsOpenEmbedding.quasiSeparatedSpace` / 引理 `Topology.IsOpenEmbedding.quasiSeparatedSpace`

English:
lemma Topology.IsOpenEmbedding.quasiSeparatedSpace
  given: [QuasiSeparatedSpace β] (h : IsOpenEmbedding f)
  proof: by
  rw [← isQuasiSeparated_univ_iff]; rw [h.isQuasiSeparated_iff]
exact isQuasiSeparated_univ.of_subset Set.subset_univ _

中文:
引理 拓扑.是开嵌入.quasiSeparatedSpace
  条件: [拟分离空间 β] (h : 是开嵌入 f)
  证明: by
  rw [← isQuasiSeparated_univ_iff]; rw [h.isQuasiSeparated_iff]
exact isQuasiSeparated_univ.of_subset Set.subset_univ _

Depends on / 依赖: Set.subset_univ, h.isQuasiSeparated_iff, isQuasiSeparated_iff, isQuasiSeparated_univ, isQuasiSeparated_univ.of_subset, isQuasiSeparated_univ_iff, of_subset, subset_univ
-/
lemma Topology.IsOpenEmbedding.quasiSeparatedSpace [QuasiSeparatedSpace β] (h : IsOpenEmbedding f) :
    QuasiSeparatedSpace α := by
  rw [← isQuasiSeparated_univ_iff]; rw [h.isQuasiSeparated_iff]
exact isQuasiSeparated_univ.of_subset Set.subset_univ _

/--
theorem `isQuasiSeparated_iff_quasiSeparatedSpace` / 定理 `isQuasiSeparated_iff_quasiSeparatedSpace`

English:
theorem isQuasiSeparated_iff_quasiSeparatedSpace
  given: (s : Set α) (hs : IsOpen s)
  proof: by
  rw [← isQuasiSeparated_univ_iff]
  convert! (hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff (s := Set.univ)).symm
  simp

中文:
定理 isQuasiSeparated_iff_quasiSeparatedSpace
  条件: (s : 集合 α) (hs : 是开集 s)
  证明: by
  rw [← isQuasiSeparated_univ_iff]
  convert! (hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff (s := Set.univ)).symm
  simp

Depends on / 依赖: Set.univ, convert, hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff, isOpenEmbedding_subtypeVal, isQuasiSeparated_iff, isQuasiSeparated_univ_iff
-/
theorem isQuasiSeparated_iff_quasiSeparatedSpace (s : Set α) (hs : IsOpen s) :
    IsQuasiSeparated s ↔ QuasiSeparatedSpace s := by
  rw [← isQuasiSeparated_univ_iff]
  convert! (hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff (s := Set.univ)).symm
  simp

instance (priority := 100) T2Space.to_quasiSeparatedSpace [T2Space α] : QuasiSeparatedSpace α :=
  ⟨fun _ _ _ hU' _ hV' => hU'.inter hV'⟩

instance (priority := 100) NoetherianSpace.to_quasiSeparatedSpace [NoetherianSpace α] :
    QuasiSeparatedSpace α :=
  ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩

/--
lemma `QuasiSeparatedSpace.of_isTopologicalBasis` / 引理 `QuasiSeparatedSpace.of_isTopologicalBasis`

English:
lemma QuasiSeparatedSpace.of_isTopologicalBasis
  statement: {ι : Type*} {b : ι -> Set α}
  proof: by
    have aux := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b basis fun i => by
      simpa using isCompact_inter i i
    obtain ⟨s, hs, rfl⟩ := (aux _).1 ⟨hUcomp, hUopen⟩
    obtain ⟨t, ht, rfl⟩ := (aux _).1 ⟨hVcomp, hVopen⟩
    rw [iUnion₂_inter_iUnion₂]
    exact hs.isCompact_biUnion fun i hi => ht.isCompact_biUnion fun j hj => isCompact_inter ..

中文:
引理 拟分离空间.of_isTopologicalBasis
  结论: {ι : 类型} {b : ι -> 集合 α}
  证明: by
    have aux := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b basis fun i => by
      simpa using isCompact_inter i i
    obtain ⟨s, hs, rfl⟩ := (aux _).1 ⟨hUcomp, hUopen⟩
    obtain ⟨t, ht, rfl⟩ := (aux _).1 ⟨hVcomp, hVopen⟩
    rw [iUnion₂_inter_iUnion₂]
    exact hs.isCompact_biUnion fun i hi => ht.isCompact_biUnion fun j hj => isCompact_inter ..

Depends on / 依赖: hUcomp, hUopen, hVcomp, hVopen, hs.isCompact_biUnion, ht.isCompact_biUnion, isCompact_biUnion, isCompact_inter, isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis
-/
lemma QuasiSeparatedSpace.of_isTopologicalBasis {ι : Type*} {b : ι -> Set α}
    (basis : IsTopologicalBasis (range b)) (isCompact_inter : forall i j, IsCompact (b i inter b j)) :
    QuasiSeparatedSpace α where
  inter_isCompact U V hUopen hUcomp hVopen hVcomp := by
    have aux := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b basis fun i => by
      simpa using isCompact_inter i i
    obtain ⟨s, hs, rfl⟩ := (aux _).1 ⟨hUcomp, hUopen⟩
    obtain ⟨t, ht, rfl⟩ := (aux _).1 ⟨hVcomp, hVopen⟩
    rw [iUnion₂_inter_iUnion₂]
    exact hs.isCompact_biUnion fun i hi => ht.isCompact_biUnion fun j hj => isCompact_inter ..

section QuasiSeparatedSpace
variable [QuasiSeparatedSpace α] {U V : Set α}

/--
lemma `IsQuasiSeparated.of_quasiSeparatedSpace` / 引理 `IsQuasiSeparated.of_quasiSeparatedSpace`

English:
lemma IsQuasiSeparated.of_quasiSeparatedSpace
  given: (s : Set α)
  statement: IsQuasiSeparated s
  proof: isQuasiSeparated_univ.of_subset (Set.subset_univ _)

中文:
引理 IsQuasiSeparated.of_quasiSeparatedSpace
  条件: (s : 集合 α)
  结论: IsQuasiSeparated s
  证明: isQuasiSeparated_univ.of_subset (Set.subset_univ _)

Depends on / 依赖: Set.subset_univ, isQuasiSeparated_univ, isQuasiSeparated_univ.of_subset, of_subset, subset_univ
-/
lemma IsQuasiSeparated.of_quasiSeparatedSpace (s : Set α) : IsQuasiSeparated s :=
  isQuasiSeparated_univ.of_subset (Set.subset_univ _)

/--
lemma `QuasiSeparatedSpace.of_isOpenEmbedding` / 引理 `QuasiSeparatedSpace.of_isOpenEmbedding`

English:
lemma QuasiSeparatedSpace.of_isOpenEmbedding
  given: {f : β -> α} (h : IsOpenEmbedding f)
  proof: isQuasiSeparated_univ_iff.mp (h.isQuasiSeparated_iff.mpr <| .of_quasiSeparatedSpace _)

中文:
引理 拟分离空间.of_isOpenEmbedding
  条件: {f : β -> α} (h : 是开嵌入 f)
  证明: isQuasiSeparated_univ_iff.mp (h.isQuasiSeparated_iff.mpr <| .of_quasiSeparatedSpace _)

Depends on / 依赖: h.isQuasiSeparated_iff.mpr, isQuasiSeparated_iff, isQuasiSeparated_univ_iff, isQuasiSeparated_univ_iff.mp, of_quasiSeparatedSpace
-/
lemma QuasiSeparatedSpace.of_isOpenEmbedding {f : β -> α} (h : IsOpenEmbedding f) :
    QuasiSeparatedSpace β :=
  isQuasiSeparated_univ_iff.mp (h.isQuasiSeparated_iff.mpr <| .of_quasiSeparatedSpace _)

/--
lemma `IsCompact.inter_of_isOpen` / 引理 `IsCompact.inter_of_isOpen`

English:
lemma IsCompact.inter_of_isOpen
  statement: (hUcomp : IsCompact U) (hVcomp : IsCompact V) (hUopen : IsOpen U)
  proof: QuasiSeparatedSpace.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp

中文:
引理 是紧集.inter_of_isOpen
  结论: (hUcomp : 是紧集 U) (hVcomp : 是紧集 V) (hUopen : 是开集 U)
  证明: QuasiSeparatedSpace.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp

Depends on / 依赖: QuasiSeparatedSpace, QuasiSeparatedSpace.inter_isCompact, hUcomp, hUopen, hVcomp, hVopen, inter_isCompact
-/
lemma IsCompact.inter_of_isOpen (hUcomp : IsCompact U) (hVcomp : IsCompact V) (hUopen : IsOpen U)
    (hVopen : IsOpen V) : IsCompact (U inter V) :=
  QuasiSeparatedSpace.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp

/--
lemma `QuasiSeparatedSpace.isCompact_sInter_of_nonempty` / 引理 `QuasiSeparatedSpace.isCompact_sInter_of_nonempty`

English:
lemma QuasiSeparatedSpace.isCompact_sInter_of_nonempty
  statement: {s : Set (Set α)} (hf : s.Finite)
  proof: by
  wlog h : forall t in s, IsOpen t
  · let a := { t in s | IsOpen t }
    let b := { t in s | IsClosed t }
    have heq : s = a union b := subset_antisymm (by grind) (by grind)
    rw [heq]; rw [Set.sInter_union]
    simp only [not_forall] at h
    obtain ⟨t, ht, hno⟩ := h
    obtain (ha | ha) := a.eq_empty_or_nonempty
    · simp only [ha, Set.sInter_empty, Set.univ_inter]
      exact IsCompact.of_isClosed_subset (hc _ ht) (isClosed_sInter (by grind)) (by grind)
    · apply IsCompact.inter_right
      · apply this (hf.subset (by grind)) ha <;> grind
      · exact isClosed_sInter (by grind)
  revert hne
  induction s, hf using Set.Finite.induction_on with
  | empty => simp
  | insert ha hs ih =>
    rename_i s
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · grind
    · grind [IsCompact.inter_of_isOpen, hs.isOpen_sInter, Set.sInter_insert]

中文:
引理 拟分离空间.isCompact_s整数er_of_nonempty
  结论: {s : 集合 (集合 α)} (hf : s.有限)
  证明: by
  wlog h : forall t in s, IsOpen t
  · let a := { t in s | IsOpen t }
    let b := { t in s | IsClosed t }
    have heq : s = a union b := subset_antisymm (by grind) (by grind)
    rw [heq]; rw [Set.sInter_union]
    simp only [not_forall] at h
    obtain ⟨t, ht, hno⟩ := h
    obtain (ha | ha) := a.eq_empty_or_nonempty
    · simp only [ha, Set.sInter_empty, Set.univ_inter]
      exact IsCompact.of_isClosed_subset (hc _ ht) (isClosed_sInter (by grind)) (by grind)
    · apply IsCompact.inter_right
      · apply this (hf.subset (by grind)) ha <;> grind
      · exact isClosed_sInter (by grind)
  revert hne
  induction s, hf using Set.Finite.induction_on with
  | empty => simp
  | insert ha hs ih =>
    rename_i s
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · grind
    · grind [IsCompact.inter_of_isOpen, hs.isOpen_sInter, Set.sInter_insert]

Depends on / 依赖: IsClosed, IsCompact, IsCompact.inter_right, IsCompact.of_isClosed_subset, IsOpen, Set.sInter_empty, Set.sInter_union, Set.univ_inter, a.eq_empty_or_nonempty, eq_empty_or_nonempty, hf.subset, inter_right, isClosed_sInter, not_forall, of_isClosed_subset, sInter_empty, sInter_union, subset, subset_antisymm, univ_inter
-/
lemma QuasiSeparatedSpace.isCompact_sInter_of_nonempty {s : Set (Set α)} (hf : s.Finite)
    (hne : s.Nonempty) (ho : forall t in s, IsOpen t ∨ IsClosed t) (hc : forall t in s, IsCompact t) :
    IsCompact (⋂₀ s) := by
  wlog h : forall t in s, IsOpen t
  · let a := { t in s | IsOpen t }
    let b := { t in s | IsClosed t }
    have heq : s = a union b := subset_antisymm (by grind) (by grind)
    rw [heq]; rw [Set.sInter_union]
    simp only [not_forall] at h
    obtain ⟨t, ht, hno⟩ := h
    obtain (ha | ha) := a.eq_empty_or_nonempty
    · simp only [ha, Set.sInter_empty, Set.univ_inter]
      exact IsCompact.of_isClosed_subset (hc _ ht) (isClosed_sInter (by grind)) (by grind)
    · apply IsCompact.inter_right
      · apply this (hf.subset (by grind)) ha <;> grind
      · exact isClosed_sInter (by grind)
  revert hne
  induction s, hf using Set.Finite.induction_on with
  | empty => simp
  | insert ha hs ih =>
    rename_i s
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · grind
    · grind [IsCompact.inter_of_isOpen, hs.isOpen_sInter, Set.sInter_insert]

/--
lemma `QuasiSeparatedSpace.isCompact_sInter` / 引理 `QuasiSeparatedSpace.isCompact_sInter`

English:
lemma QuasiSeparatedSpace.isCompact_sInter
  statement: [CompactSpace α] {s : Set (Set α)} (hf : s.Finite)
  proof: by
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp [CompactSpace.isCompact_univ]
  · exact QuasiSeparatedSpace.isCompact_sInter_of_nonempty hf hne ho hc

中文:
引理 拟分离空间.isCompact_s整数er
  结论: [紧空间 α] {s : 集合 (集合 α)} (hf : s.有限)
  证明: by
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp [CompactSpace.isCompact_univ]
  · exact QuasiSeparatedSpace.isCompact_sInter_of_nonempty hf hne ho hc

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, QuasiSeparatedSpace, QuasiSeparatedSpace.isCompact_sInter_of_nonempty, eq_empty_or_nonempty, isCompact_sInter_of_nonempty, isCompact_univ, s.eq_empty_or_nonempty
-/
lemma QuasiSeparatedSpace.isCompact_sInter [CompactSpace α] {s : Set (Set α)} (hf : s.Finite)
    (ho : forall t in s, IsOpen t ∨ IsClosed t) (hc : forall t in s, IsCompact t) :
    IsCompact (⋂₀ s) := by
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp [CompactSpace.isCompact_univ]
  · exact QuasiSeparatedSpace.isCompact_sInter_of_nonempty hf hne ho hc

end QuasiSeparatedSpace

/--
lemma `quasiSeparatedSpace_congr` / 引理 `quasiSeparatedSpace_congr`

English:
lemma quasiSeparatedSpace_congr
  given: (e : α ≃ₜ β)
  statement: QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β where
  proof: .of_isOpenEmbedding e.symm.isOpenEmbedding
  mpr _ := .of_isOpenEmbedding e.isOpenEmbedding

中文:
引理 quasiSeparatedSpace_congr
  条件: (e : α ≃ₜ β)
  结论: 拟分离空间 α ↔ 拟分离空间 β where
  证明: .of_isOpenEmbedding e.symm.isOpenEmbedding
  mpr _ := .of_isOpenEmbedding e.isOpenEmbedding

Depends on / 依赖: e.symm.isOpenEmbedding, isOpenEmbedding, of_isOpenEmbedding
-/
lemma quasiSeparatedSpace_congr (e : α ≃ₜ β) : QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β where
  mp _ := .of_isOpenEmbedding e.symm.isOpenEmbedding
  mpr _ := .of_isOpenEmbedding e.isOpenEmbedding
