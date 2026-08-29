/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Bhavik Mehta, Daniel Weber, Stefan Kebekus
-/
module

public import Mathlib.Tactic.TautoSet
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Separation.Basic

/-!
# Discrete subsets of topological spaces

This file contains various additional properties of discrete subsets of topological spaces.

## Discreteness and compact sets

Given a topological space `X` together with a subset `s ⊆ X`, there are two distinct concepts of
"discreteness" which may hold. These are:
  (i) Every point of `s` is isolated (i.e., the subset topology induced on `s` is the discrete
      topology).
 (ii) Every compact subset of `X` meets `s` only finitely often (i.e., the inclusion map `s → X`
      tends to the cocompact filter along the cofinite filter on `s`).

When `s` is closed, the two conditions are equivalent provided `X` is locally compact and T1,
see `IsClosed.tendsto_coe_cofinite_iff`.

### Main statements

* `tendsto_cofinite_cocompact_iff`:
* `IsClosed.tendsto_coe_cofinite_iff`:

## Co-discrete open sets

We define the filter `Filter.codiscreteWithin S`, which is the supremum of all `𝓝[S \ {x}] x`.
This is the filter of all open codiscrete sets within S. We also define `Filter.codiscrete` as
`Filter.codiscreteWithin univ`, which is the filter of all open codiscrete sets in the space.

-/

@[expose] public section

open Set Filter Function Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X -> Y} {s : Set X}

/--
theorem `discreteTopology_subtype_iff` / 定理 `discreteTopology_subtype_iff`

English:
theorem discreteTopology_subtype_iff
  given: {S : Set Y}
  proof: by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

中文:
定理 discreteTopology_subtype_iff
  条件: {S : Set Y}
  证明: by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

Depends on / 依赖: SetCoe, SetCoe.forall, discreteTopology_iff_nhds_ne, nhds_ne_subtype_eq_bot_iff, simp_rw
-/
theorem discreteTopology_subtype_iff {S : Set Y} :
    DiscreteTopology S ↔ forall x in S, 𝓝[!=] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]

/--
theorem `isDiscrete_iff_nhdsNE` / 定理 `isDiscrete_iff_nhdsNE`

English:
theorem isDiscrete_iff_nhdsNE
  given: {S : Set Y}
  proof: by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff]

中文:
定理 isDiscrete_iff_nhdsNE
  条件: {S : Set Y}
  证明: by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff]

Depends on / 依赖: discreteTopology_subtype_iff, isDiscrete_iff_discreteTopology
-/
theorem isDiscrete_iff_nhdsNE {S : Set Y} :
    IsDiscrete S ↔ forall x in S, 𝓝[!=] x ⊓ 𝓟 S = ⊥ := by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff]

/--
lemma `discreteTopology_of_noAccPts` / 引理 `discreteTopology_of_noAccPts`

English:
lemma discreteTopology_of_noAccPts
  statement: {X : Type*} [TopologicalSpace X] {E : Set X}
  proof: by
  simpa [discreteTopology_subtype_iff, AccPt] using h

中文:
引理 discreteTopology_of_noAccPts
  结论: {X : 类型} [TopologicalSpace X] {E : Set X}
  证明: by
  simpa [discreteTopology_subtype_iff, AccPt] using h

Depends on / 依赖: discreteTopology_subtype_iff
-/
lemma discreteTopology_of_noAccPts {X : Type*} [TopologicalSpace X] {E : Set X}
    (h : forall x in E, ¬ AccPt x (𝓟 E)) : DiscreteTopology E := by
  simpa [discreteTopology_subtype_iff, AccPt] using h

/--
lemma `discreteTopology_subtype_iff'` / 引理 `discreteTopology_subtype_iff'`

English:
lemma discreteTopology_subtype_iff'
  given: {S : Set Y}
  proof: by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

中文:
引理 discreteTopology_subtype_iff'
  条件: {S : Set Y}
  证明: by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

Depends on / 依赖: Set.ext_iff, discreteTopology_iff_isOpen_singleton, ext_iff, isOpen_induced_iff
-/
lemma discreteTopology_subtype_iff' {S : Set Y} :
    DiscreteTopology S ↔ forall y in S, exists U : Set Y, IsOpen U ∧ U inter S = {y} := by
  simp [discreteTopology_iff_isOpen_singleton, isOpen_induced_iff, Set.ext_iff]
  grind

/--
theorem `isDiscrete_iff_forall_mem_exists_isOpen` / 定理 `isDiscrete_iff_forall_mem_exists_isOpen`

English:
theorem isDiscrete_iff_forall_mem_exists_isOpen
  given: {s : Set Y}
  proof: by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff']

@[deprecated (since := "2026-06-24")]
alias isDiscrete_iff_forall_exists_isOpen := isDiscrete_iff_forall_mem_exists_isOpen

中文:
定理 isDiscrete_iff_forall_mem_exists_isOpen
  条件: {s : Set Y}
  证明: by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff']

@[deprecated (since := "2026-06-24")]
alias isDiscrete_iff_forall_exists_isOpen := isDiscrete_iff_forall_mem_exists_isOpen

Depends on / 依赖: discreteTopology_subtype_iff, isDiscrete_iff_discreteTopology
-/
theorem isDiscrete_iff_forall_mem_exists_isOpen {s : Set Y} :
    IsDiscrete s ↔ forall y in s, exists u, IsOpen u ∧ u inter s = {y} := by
  rw [isDiscrete_iff_discreteTopology]; rw [discreteTopology_subtype_iff']

@[deprecated (since := "2026-06-24")]
alias isDiscrete_iff_forall_exists_isOpen := isDiscrete_iff_forall_mem_exists_isOpen

/--
theorem `isDiscrete_iff_forall_subset_exists_isOpen` / 定理 `isDiscrete_iff_forall_subset_exists_isOpen`

English:
theorem isDiscrete_iff_forall_subset_exists_isOpen
  given: {s : Set X}
  proof: by
  simp_rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isOpen,
    isOpen_induced_iff, ← image_eq_image (Subtype.val_injective), Subtype.image_preimage_coe,
    Subtype.forall_set_subtype (p := fun t => exists u, IsOpen u ∧ s inter u = t), inter_comm]

中文:
定理 isDiscrete_iff_forall_subset_exists_isOpen
  条件: {s : Set X}
  证明: by
  simp_rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isOpen,
    isOpen_induced_iff, ← image_eq_image (Subtype.val_injective), Subtype.image_preimage_coe,
    Subtype.forall_set_subtype (p := fun t => exists u, IsOpen u ∧ s inter u = t), inter_comm]

Depends on / 依赖: IsOpen, Subtype, Subtype.forall_set_subtype, Subtype.image_preimage_coe, Subtype.val_injective, discreteTopology_iff_forall_isOpen, forall_set_subtype, image_eq_image, image_preimage_coe, inter_comm, isDiscrete_iff_discreteTopology, isOpen_induced_iff, simp_rw, val_injective
-/
theorem isDiscrete_iff_forall_subset_exists_isOpen {s : Set X} :
    IsDiscrete s ↔ forall t subseteq s, exists u, IsOpen u ∧ u inter s = t := by
  simp_rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isOpen,
    isOpen_induced_iff, ← image_eq_image (Subtype.val_injective), Subtype.image_preimage_coe,
    Subtype.forall_set_subtype (p := fun t => exists u, IsOpen u ∧ s inter u = t), inter_comm]

/--
theorem `isDiscrete_iff_forall_mem_exists_isClosed` / 定理 `isDiscrete_iff_forall_mem_exists_isClosed`

English:
theorem isDiscrete_iff_forall_mem_exists_isClosed
  given: {S : Set X}
  proof: by
  rw [isDiscrete_iff_forall_subset_exists_isOpen]
  constructor <;> intro h s sS
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right
    exact ⟨Uᶜ, isClosed_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right


中文:
定理 isDiscrete_iff_forall_mem_exists_isClosed
  条件: {S : Set X}
  证明: by
  rw [isDiscrete_iff_forall_subset_exists_isOpen]
  constructor <;> intro h s sS
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right
    exact ⟨Uᶜ, isClosed_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right


Depends on / 依赖: Set.ext_iff, ext_iff, inter_subset_right, isClosed_compl_iff, isClosed_compl_iff.mpr, isDiscrete_iff_forall_subset_exists_isOpen, isOpen_compl_iff, isOpen_compl_iff.mpr, left_eq_inter, left_eq_inter.mpr
-/
theorem isDiscrete_iff_forall_mem_exists_isClosed {S : Set X} :
    IsDiscrete S ↔ forall s subseteq S, exists U, IsClosed U ∧ U inter S = s := by
  rw [isDiscrete_iff_forall_subset_exists_isOpen]
  constructor <;> intro h s sS
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right
    exact ⟨Uᶜ, isClosed_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩
  · obtain ⟨U, Uo, Us⟩ := h (sᶜ inter S) inter_subset_right
    exact ⟨Uᶜ, isOpen_compl_iff.mpr Uo, by rw [left_eq_inter.mpr sS]; simp_all [Set.ext_iff]⟩

/--
theorem `isClosed_of_subset_discrete_closed` / 定理 `isClosed_of_subset_discrete_closed`

English:
theorem isClosed_of_subset_discrete_closed
  statement: {s t : Set X} (sd : s subseteq t)
  proof: by
  obtain ⟨_, rp, rt⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp ht s sd
  rw [← rt]
  exact rp.inter tc

中文:
定理 isClosed_of_subset_discrete_closed
  结论: {s t : Set X} (sd : s subseteq t)
  证明: by
  obtain ⟨_, rp, rt⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp ht s sd
  rw [← rt]
  exact rp.inter tc

Depends on / 依赖: isDiscrete_iff_forall_mem_exists_isClosed, isDiscrete_iff_forall_mem_exists_isClosed.mp, rp.inter
-/
theorem isClosed_of_subset_discrete_closed {s t : Set X} (sd : s subseteq t)
    (ht : IsDiscrete t) (tc : IsClosed t) : IsClosed s := by
  obtain ⟨_, rp, rt⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp ht s sd
  rw [← rt]
  exact rp.inter tc

/--
lemma `Set.Subsingleton.isDiscrete` / 引理 `Set.Subsingleton.isDiscrete`

English:
lemma Set.Subsingleton.isDiscrete
  given: (hs : s.Subsingleton)
  statement: IsDiscrete s
  proof: have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩

中文:
引理 Set.Subsingleton.isDiscrete
  条件: (hs : s.Subsingleton)
  结论: IsDiscrete s
  证明: have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩

Depends on / 依赖: Set.subsingleton_coe, Subsingleton, subsingleton_coe
-/
lemma Set.Subsingleton.isDiscrete (hs : s.Subsingleton) : IsDiscrete s :=
  have : Subsingleton s := (Set.subsingleton_coe s).mpr hs
  ⟨inferInstance⟩

/--
lemma `isDiscrete_iff_nhdsWithin` / 引理 `isDiscrete_iff_nhdsWithin`

English:
lemma isDiscrete_iff_nhdsWithin
  statement: IsDiscrete s ↔ forall x in s, 𝓝[s] x = pure x
  proof: by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithi

中文:
引理 isDiscrete_iff_nhdsWithin
  结论: IsDiscrete s ↔ 对任意 x in s, 𝓝[s] x = pure x
  证明: by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithi

Depends on / 依赖: Filter, Filter.map_comap, Filter.map_injective, Subtype, Subtype.val_injective, discreteTopology_iff_isOpen_singleton, eq_iff, isDiscrete_iff_discreteTopology, isOpen_singleton_iff_nhds_eq_pure, map_comap, map_injective, nhdsWithin, nhds_induced, val_injective
-/
lemma isDiscrete_iff_nhdsWithin : IsDiscrete s ↔ forall x in s, 𝓝[s] x = pure x := by
  simp [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure, nhds_induced,
    ← (Filter.map_injective Subtype.val_injective).eq_iff,
    Filter.map_comap, nhdsWithin]

protected alias ⟨IsDiscrete.nhdsWithin, _⟩ := isDiscrete_iff_nhdsWithin

/--
lemma `IsDiscrete.of_nhdsWithin` / 引理 `IsDiscrete.of_nhdsWithin`

English:
lemma IsDiscrete.of_nhdsWithin
  given: (H : forall x in s, 𝓝[s] x <= pure x)
  statement: IsDiscrete s
  proof: isDiscrete_iff_nhdsWithin.mpr fun x hx => (H x hx).antisymm (pure_le_nhdsWithin hx)

中文:
引理 IsDiscrete.of_nhdsWithin
  条件: (H : 对任意 x in s, 𝓝[s] x <= pure x)
  结论: IsDiscrete s
  证明: isDiscrete_iff_nhdsWithin.mpr fun x hx => (H x hx).antisymm (pure_le_nhdsWithin hx)

Depends on / 依赖: antisymm, isDiscrete_iff_nhdsWithin, isDiscrete_iff_nhdsWithin.mpr, pure_le_nhdsWithin
-/
lemma IsDiscrete.of_nhdsWithin (H : forall x in s, 𝓝[s] x <= pure x) : IsDiscrete s :=
  isDiscrete_iff_nhdsWithin.mpr fun x hx => (H x hx).antisymm (pure_le_nhdsWithin hx)

/--
lemma `isDiscrete_univ_iff` / 引理 `isDiscrete_univ_iff`

English:
lemma isDiscrete_univ_iff
  statement: IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X
  proof: by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]

中文:
引理 isDiscrete_univ_iff
  结论: IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X
  证明: by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]

Depends on / 依赖: discreteTopology_iff_isOpen_singleton, isDiscrete_iff_nhdsWithin, isOpen_singleton_iff_nhds_eq_pure
-/
lemma isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X) ↔ DiscreteTopology X := by
  simp [isDiscrete_iff_nhdsWithin, discreteTopology_iff_isOpen_singleton,
    isOpen_singleton_iff_nhds_eq_pure]

/--
lemma `IsDiscrete.univ` / 引理 `IsDiscrete.univ`

English:
lemma IsDiscrete.univ
  given: [DiscreteTopology X]
  statement: IsDiscrete (Set.univ : Set X)
  proof: by
  rwa [isDiscrete_univ_iff]

中文:
引理 IsDiscrete.univ
  条件: [DiscreteTopology X]
  结论: IsDiscrete (Set.univ : Set X)
  证明: by
  rwa [isDiscrete_univ_iff]

Depends on / 依赖: isDiscrete_univ_iff
-/
lemma IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.univ : Set X) := by
  rwa [isDiscrete_univ_iff]

/--
lemma `IsDiscrete.image_of_isOpenMap` / 引理 `IsDiscrete.image_of_isOpenMap`

English:
lemma IsDiscrete.image_of_isOpenMap
  statement: (hs : IsDiscrete s) (hf : IsOpenMap f)
  proof: by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [nhdsWithin]; rw [nhdsWithin]; rw [map_inf hf']; rw [map_principal]
  grw [hf.nhds_le x]

中文:
引理 IsDiscrete.image_of_isOpenMap
  结论: (hs : IsDiscrete s) (hf : IsOpenMap f)
  证明: by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [nhdsWithin]; rw [nhdsWithin]; rw [map_inf hf']; rw [map_principal]
  grw [hf.nhds_le x]

Depends on / 依赖: hf.nhds_le, hs.nhdsWithin, map_inf, map_principal, map_pure, nhdsWithin, nhds_le, of_nhdsWithin
-/
lemma IsDiscrete.image_of_isOpenMap (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hf' : Function.Injective f) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [nhdsWithin]; rw [nhdsWithin]; rw [map_inf hf']; rw [map_principal]
  grw [hf.nhds_le x]

/--
lemma `IsDiscrete.image_of_isOpenMap_of_isOpen` / 引理 `IsDiscrete.image_of_isOpenMap_of_isOpen`

English:
lemma IsDiscrete.image_of_isOpenMap_of_isOpen
  statement: (hs : IsDiscrete s) (hf : IsOpenMap f)
  proof: by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x]; rw [hx]; rw [rfl⟩]; rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x

中文:
引理 IsDiscrete.image_of_isOpenMap_of_isOpen
  结论: (hs : IsDiscrete s) (hf : IsOpenMap f)
  证明: by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x]; rw [hx]; rw [rfl⟩]; rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x

Depends on / 依赖: hf.nhds_le, hs.nhdsWithin, map_pure, nhdsWithin, nhdsWithin_eq, nhds_le, of_nhdsWithin
-/
lemma IsDiscrete.image_of_isOpenMap_of_isOpen (hs : IsDiscrete s) (hf : IsOpenMap f)
    (hs' : IsOpen s) : IsDiscrete (f '' s) := by
  refine .of_nhdsWithin ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(hf _ hs').nhdsWithin_eq ⟨x]; rw [hx]; rw [rfl⟩]; rw [← map_pure]; rw [← hs.nhdsWithin x hx]; rw [hs'.nhdsWithin_eq hx]
  exact hf.nhds_le x

/--
lemma `IsOpenMap.isDiscrete_range` / 引理 `IsOpenMap.isDiscrete_range`

English:
lemma IsOpenMap.isDiscrete_range
  given: [DiscreteTopology X] (hf : IsOpenMap f)
  proof: by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ

中文:
引理 IsOpenMap.isDiscrete_range
  条件: [DiscreteTopology X] (hf : IsOpenMap f)
  证明: by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ

Depends on / 依赖: IsDiscrete, IsDiscrete.univ.image_of_isOpenMap_of_isOpen, image_of_isOpenMap_of_isOpen, isOpen_univ
-/
lemma IsOpenMap.isDiscrete_range [DiscreteTopology X] (hf : IsOpenMap f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image_of_isOpenMap_of_isOpen hf isOpen_univ

/--
lemma `IsDiscrete.image` / 引理 `IsDiscrete.image`

English:
lemma IsDiscrete.image
  given: (hs : IsDiscrete s) (hf : IsInducing f)
  statement: IsDiscrete (f '' s)
  proof: by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]

中文:
引理 IsDiscrete.image
  条件: (hs : IsDiscrete s) (hf : IsInducing f)
  结论: IsDiscrete (f '' s)
  证明: by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]

Depends on / 依赖: hf.map_nhdsWithin_eq, isDiscrete_iff_nhdsWithin, map_nhdsWithin_eq
-/
lemma IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing f) : IsDiscrete (f '' s) := by
  simp_all [isDiscrete_iff_nhdsWithin, ← hf.map_nhdsWithin_eq s]

/--
lemma `Topology.IsInducing.isDiscrete_range` / 引理 `Topology.IsInducing.isDiscrete_range`

English:
lemma Topology.IsInducing.isDiscrete_range
  given: [DiscreteTopology X] (hf : IsInducing f)
  proof: by
  simpa using IsDiscrete.univ.image hf

@[deprecated (since := "2026-03-30")] alias
IsEmbedding.isDiscrete_range := IsInducing.isDiscrete_range

中文:
引理 Topology.IsInducing.isDiscrete_range
  条件: [DiscreteTopology X] (hf : IsInducing f)
  证明: by
  simpa using IsDiscrete.univ.image hf

@[deprecated (since := "2026-03-30")] alias
IsEmbedding.isDiscrete_range := IsInducing.isDiscrete_range

Depends on / 依赖: IsDiscrete, IsDiscrete.univ.image
-/
lemma Topology.IsInducing.isDiscrete_range [DiscreteTopology X] (hf : IsInducing f) :
    IsDiscrete (Set.range f) := by
  simpa using IsDiscrete.univ.image hf

@[deprecated (since := "2026-03-30")] alias
IsEmbedding.isDiscrete_range := IsInducing.isDiscrete_range

/--
lemma `IsDiscrete.preimage` / 引理 `IsDiscrete.preimage`

English:
lemma IsDiscrete.preimage
  statement: {s : Set Y} (hs : IsDiscrete s)
  proof: by
  refine .of_nhdsWithin fun x hx => ?_
  rw [← map_le_map_iff hf']; rw [map_pure]; rw [← hs.nhdsWithin _ hx]; rw [← Tendsto]
  exact (hf.continuousWithinAt hx).tendsto_nhdsWithin (Set.mapsTo_preimage _ _)

中文:
引理 IsDiscrete.preimage
  结论: {s : Set Y} (hs : IsDiscrete s)
  证明: by
  refine .of_nhdsWithin fun x hx => ?_
  rw [← map_le_map_iff hf']; rw [map_pure]; rw [← hs.nhdsWithin _ hx]; rw [← Tendsto]
  exact (hf.continuousWithinAt hx).tendsto_nhdsWithin (Set.mapsTo_preimage _ _)

Depends on / 依赖: Set.mapsTo_preimage, Tendsto, continuousWithinAt, hf.continuousWithinAt, hs.nhdsWithin, map_le_map_iff, map_pure, mapsTo_preimage, nhdsWithin, of_nhdsWithin, tendsto_nhdsWithin
-/
lemma IsDiscrete.preimage {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s)) (hf' : Function.Injective f) :
    IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx => ?_
  rw [← map_le_map_iff hf']; rw [map_pure]; rw [← hs.nhdsWithin _ hx]; rw [← Tendsto]
  exact (hf.continuousWithinAt hx).tendsto_nhdsWithin (Set.mapsTo_preimage _ _)

/--
lemma `IsDiscrete.preimage'` / 引理 `IsDiscrete.preimage'`

English:
lemma IsDiscrete.preimage'
  statement: {s : Set Y} (hs : IsDiscrete s)
  proof: by
  refine .of_nhdsWithin fun x hx => ?_
  have h := ((H (f x)).nhdsWithin _ rfl).le
  grw [nhdsWithin, ← comap_pure, ← hs.nhdsWithin _ hx, ← (hf.continuousWithinAt hx
.tendsto_nhdsWithin fun _ => by exact id).le_comap, inf_eq_right.mpr nhdsWithin_le_nhds] at h
  exact h

中文:
引理 IsDiscrete.preimage'
  结论: {s : Set Y} (hs : IsDiscrete s)
  证明: by
  refine .of_nhdsWithin fun x hx => ?_
  have h := ((H (f x)).nhdsWithin _ rfl).le
  grw [nhdsWithin, ← comap_pure, ← hs.nhdsWithin _ hx, ← (hf.continuousWithinAt hx
.tendsto_nhdsWithin fun _ => by exact id).le_comap, inf_eq_right.mpr nhdsWithin_le_nhds] at h
  exact h

Depends on / 依赖: comap_pure, continuousWithinAt, hf.continuousWithinAt, hs.nhdsWithin, inf_eq_right, inf_eq_right.mpr, le_comap, nhdsWithin, nhdsWithin_le_nhds, of_nhdsWithin, tendsto_nhdsWithin
-/
lemma IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete s)
    (hf : ContinuousOn f (f ⁻¹' s))
    (H : forall x, IsDiscrete (f ⁻¹' {x})) : IsDiscrete (f ⁻¹' s) := by
  refine .of_nhdsWithin fun x hx => ?_
  have h := ((H (f x)).nhdsWithin _ rfl).le
  grw [nhdsWithin, ← comap_pure, ← hs.nhdsWithin _ hx, ← (hf.continuousWithinAt hx
.tendsto_nhdsWithin fun _ => by exact id).le_comap, inf_eq_right.mpr nhdsWithin_le_nhds] at h
  exact h

/--
lemma `IsDiscrete.eq_of_specializes` / 引理 `IsDiscrete.eq_of_specializes`

English:
lemma IsDiscrete.eq_of_specializes
  statement: (hs : IsDiscrete s)
  proof: by
  let := hs.1
  simpa only [← Topology.IsInducing.subtypeVal.specializes_iff, hab, Subtype.mk.injEq,
    true_iff] using specializes_iff_eq (X := s) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)

中文:
引理 IsDiscrete.eq_of_specializes
  结论: (hs : IsDiscrete s)
  证明: by
  let := hs.1
  simpa only [← Topology.IsInducing.subtypeVal.specializes_iff, hab, Subtype.mk.injEq,
    true_iff] using specializes_iff_eq (X := s) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)

Depends on / 依赖: IsInducing, Subtype, Subtype.mk.injEq, Topology, Topology.IsInducing.subtypeVal.specializes_iff, specializes_iff, specializes_iff_eq, subtypeVal, true_iff
-/
lemma IsDiscrete.eq_of_specializes (hs : IsDiscrete s)
    {a b : X} (hab : a ⤳ b) (ha : a in s) (hb : b in s) : a = b := by
  let := hs.1
  simpa only [← Topology.IsInducing.subtypeVal.specializes_iff, hab, Subtype.mk.injEq,
    true_iff] using specializes_iff_eq (X := s) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)

section cofinite_cocompact

omit [TopologicalSpace X] in
/--
lemma `tendsto_cofinite_cocompact_iff` / 引理 `tendsto_cofinite_cocompact_iff`

English:
lemma tendsto_cofinite_cocompact_iff
  proof: by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ => ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

中文:
引理 tendsto_cofinite_cocompact_iff
  证明: by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ => ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

Depends on / 依赖: eventually_cofinite, hasBasis_cocompact, hasBasis_cocompact.tendsto_right_iff, mem_compl_iff, not_not, preimage, tendsto_right_iff
-/
lemma tendsto_cofinite_cocompact_iff :
    Tendsto f cofinite (cocompact _) ↔ forall K, IsCompact K -> Set.Finite (f ⁻¹' K) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  refine forall₂_congr (fun K _ => ?_)
  simp only [mem_compl_iff, eventually_cofinite, not_not, preimage]

/--
lemma `Continuous.discrete_of_tendsto_cofinite_cocompact` / 引理 `Continuous.discrete_of_tendsto_cofinite_cocompact`

English:
lemma Continuous.discrete_of_tendsto_cofinite_cocompact
  statement: [T1Space X] [WeaklyLocallyCompactSpace Y]
  proof: by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun x => ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K in 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U subseteq K, hU₂ : IsOpen U, hU₃ : f x in U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f ⁻¹' U) :=
    Fin

中文:
引理 Continuous.discrete_of_tendsto_cofinite_cocompact
  结论: [T1Space X] [WeaklyLocallyCompactSpace Y]
  证明: by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun x => ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K in 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U subseteq K, hU₂ : IsOpen U, hU₃ : f x in U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f ⁻¹' U) :=
    Fin

Depends on / 依赖: Finite, Finite.subset, IsCompact, IsOpen, Set.Finite, discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, exists_compact_mem_nhds, isOpen_singleton_of_finite_mem_nhds, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, preimage, preimage_mono, subset, subseteq, tendsto_cofinite_cocompact_iff, tendsto_cofinite_cocompact_iff.mp
-/
lemma Continuous.discrete_of_tendsto_cofinite_cocompact [T1Space X] [WeaklyLocallyCompactSpace Y]
    (hf' : Continuous f) (hf : Tendsto f cofinite (cocompact _)) :
    DiscreteTopology X := by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun x => ?_)
  obtain ⟨K : Set Y, hK : IsCompact K, hK' : K in 𝓝 (f x)⟩ := exists_compact_mem_nhds (f x)
  obtain ⟨U : Set Y, hU₁ : U subseteq K, hU₂ : IsOpen U, hU₃ : f x in U⟩ := mem_nhds_iff.mp hK'
  have hU₄ : Set.Finite (f ⁻¹' U) :=
    Finite.subset (tendsto_cofinite_cocompact_iff.mp hf K hK) (preimage_mono hU₁)
  exact isOpen_singleton_of_finite_mem_nhds _ ((hU₂.preimage hf').mem_nhds hU₃) hU₄

/--
lemma `tendsto_cofinite_cocompact_of_discrete` / 引理 `tendsto_cofinite_cocompact_of_discrete`

English:
lemma tendsto_cofinite_cocompact_of_discrete
  statement: [DiscreteTopology X]
  proof: by
  convert! hf
  rw [cocompact_eq_cofinite X]

中文:
引理 tendsto_cofinite_cocompact_of_discrete
  结论: [DiscreteTopology X]
  证明: by
  convert! hf
  rw [cocompact_eq_cofinite X]

Depends on / 依赖: cocompact_eq_cofinite, convert
-/
lemma tendsto_cofinite_cocompact_of_discrete [DiscreteTopology X]
    (hf : Tendsto f (cocompact _) (cocompact _)) :
    Tendsto f cofinite (cocompact _) := by
  convert! hf
  rw [cocompact_eq_cofinite X]

/--
lemma `IsClosed.tendsto_coe_cofinite_of_isDiscrete` / 引理 `IsClosed.tendsto_coe_cofinite_of_isDiscrete`

English:
lemma IsClosed.tendsto_coe_cofinite_of_isDiscrete
  proof: haveI := hs'.to_subtype
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact

中文:
引理 IsClosed.tendsto_coe_cofinite_of_isDiscrete
  证明: haveI := hs'.to_subtype
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.tendsto_cocompact, isClosedEmbedding_subtypeVal, tendsto_cocompact, tendsto_cofinite_cocompact_of_discrete, to_subtype
-/
lemma IsClosed.tendsto_coe_cofinite_of_isDiscrete
    {s : Set X} (hs : IsClosed s) (hs' : IsDiscrete s) :
    Tendsto ((↑) : s -> X) cofinite (cocompact _) :=
  haveI := hs'.to_subtype
  tendsto_cofinite_cocompact_of_discrete hs.isClosedEmbedding_subtypeVal.tendsto_cocompact

/--
lemma `IsClosed.tendsto_coe_cofinite_iff` / 引理 `IsClosed.tendsto_coe_cofinite_iff`

English:
lemma IsClosed.tendsto_coe_cofinite_iff
  statement: [T1Space X] [WeaklyLocallyCompactSpace X]
  proof: ⟨fun h => ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact h⟩,
   fun hs' => hs.tendsto_coe_cofinite_of_isDiscrete hs'⟩

中文:
引理 IsClosed.tendsto_coe_cofinite_iff
  结论: [T1Space X] [WeaklyLocallyCompactSpace X]
  证明: ⟨fun h => ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact h⟩,
   fun hs' => hs.tendsto_coe_cofinite_of_isDiscrete hs'⟩

Depends on / 依赖: continuous_subtype_val, continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact, discrete_of_tendsto_cofinite_cocompact, hs.tendsto_coe_cofinite_of_isDiscrete, tendsto_coe_cofinite_of_isDiscrete
-/
lemma IsClosed.tendsto_coe_cofinite_iff [T1Space X] [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) :
    Tendsto ((↑) : s -> X) cofinite (cocompact _) ↔ IsDiscrete s :=
  ⟨fun h => ⟨continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact h⟩,
   fun hs' => hs.tendsto_coe_cofinite_of_isDiscrete hs'⟩

end cofinite_cocompact

section codiscrete_filter

/--
theorem `isClosed_and_discrete_iff` / 定理 `isClosed_and_discrete_iff`

English:
theorem isClosed_and_discrete_iff
  given: {S : Set X}
  proof: by
  rw [isDiscrete_iff_nhdsNE]; rw [isClosed_iff_clusterPt]; rw [← forall_and]
  congrm (forall x, ?_)
  rw [← not_imp_not]; rw [clusterPt_iff_not_disjoint]; rw [not_not]; rw [← disjoint_iff]
  constructor <;> intro H
  · by_cases hx : x in S
    exacts [H.2 hx, (H.1 hx).mono_left nhdsWithin_le_nhd

中文:
定理 isClosed_and_discrete_iff
  条件: {S : Set X}
  证明: by
  rw [isDiscrete_iff_nhdsNE]; rw [isClosed_iff_clusterPt]; rw [← forall_and]
  congrm (forall x, ?_)
  rw [← not_imp_not]; rw [clusterPt_iff_not_disjoint]; rw [not_not]; rw [← disjoint_iff]
  constructor <;> intro H
  · by_cases hx : x in S
    exacts [H.2 hx, (H.1 hx).mono_left nhdsWithin_le_nhd

Depends on / 依赖: clusterPt_iff_not_disjoint, congrm, disjoint_iff, exacts, forall_and, inf_assoc, isClosed_iff_clusterPt, isDiscrete_iff_nhdsNE, mono_left, nhdsWithin, nhdsWithin_le_nhds, not_imp_not, not_not
-/
theorem isClosed_and_discrete_iff {S : Set X} :
    IsClosed S ∧ IsDiscrete S ↔ forall x, Disjoint (𝓝[!=] x) (𝓟 S) := by
  rw [isDiscrete_iff_nhdsNE]; rw [isClosed_iff_clusterPt]; rw [← forall_and]
  congrm (forall x, ?_)
  rw [← not_imp_not]; rw [clusterPt_iff_not_disjoint]; rw [not_not]; rw [← disjoint_iff]
  constructor <;> intro H
  · by_cases hx : x in S
    exacts [H.2 hx, (H.1 hx).mono_left nhdsWithin_le_nhds]
  · refine ⟨fun hx => ?_, fun _ => H⟩
    simpa [disjoint_iff, nhdsWithin, inf_assoc, hx] using H

/--
Definition of `Filter.codiscreteWithin` / `Filter.codiscreteWithin` 的定义

English:
definition Filter.codiscreteWithin
  signature: (S : Set X)
  body: ⨆ x in S, 𝓝[S \ {x}] x

中文:
定义 Filter.codiscreteWithin
  签名: (S : Set X)
  定义体: ⨆ x in S, 𝓝[S \ {x}] x
-/
def Filter.codiscreteWithin (S : Set X) : Filter X := ⨆ x in S, 𝓝[S \ {x}] x

/--
lemma `mem_codiscreteWithin` / 引理 `mem_codiscreteWithin`

English:
lemma mem_codiscreteWithin
  given: {S T : Set X}
  proof: by
  simp only [codiscreteWithin, mem_iSup, mem_nhdsWithin, disjoint_principal_right, subset_def,
    Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
  congr! 7 with x - u y
  tauto

中文:
引理 mem_codiscreteWithin
  条件: {S T : Set X}
  证明: by
  simp only [codiscreteWithin, mem_iSup, mem_nhdsWithin, disjoint_principal_right, subset_def,
    Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
  congr! 7 with x - u y
  tauto

Depends on / 依赖: Set.mem_sdiff, codiscreteWithin, disjoint_principal_right, mem_compl_iff, mem_iSup, mem_inter_iff, mem_nhdsWithin, mem_sdiff, subset_def
-/
lemma mem_codiscreteWithin {S T : Set X} :
    S in codiscreteWithin T ↔ forall x in T, Disjoint (𝓝[!=] x) (𝓟 (T \ S)) := by
  simp only [codiscreteWithin, mem_iSup, mem_nhdsWithin, disjoint_principal_right, subset_def,
    Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
  congr! 7 with x - u y
  tauto

/--
theorem `mem_codiscreteWithin_iff_forall_mem_nhdsNE` / 定理 `mem_codiscreteWithin_iff_forall_mem_nhdsNE`

English:
theorem mem_codiscreteWithin_iff_forall_mem_nhdsNE
  given: {S T : Set X}
  proof: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff]

中文:
定理 mem_codiscreteWithin_iff_forall_mem_nhdsNE
  条件: {S T : Set X}
  证明: by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff]

Depends on / 依赖: Set.compl_sdiff, compl_sdiff, disjoint_principal_right, mem_codiscreteWithin, simp_rw
-/
theorem mem_codiscreteWithin_iff_forall_mem_nhdsNE {S T : Set X} :
    S in codiscreteWithin T ↔ forall x in T, S union Tᶜ in 𝓝[!=] x := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff]

/--
lemma `mem_codiscreteWithin_accPt` / 引理 `mem_codiscreteWithin_accPt`

English:
lemma mem_codiscreteWithin_accPt
  given: {S T : Set X}
  proof: by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

中文:
引理 mem_codiscreteWithin_accPt
  条件: {S T : Set X}
  证明: by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

Depends on / 依赖: disjoint_iff, mem_codiscreteWithin, not_neBot
-/
lemma mem_codiscreteWithin_accPt {S T : Set X} :
    S in codiscreteWithin T ↔ forall x in T, ¬AccPt x (𝓟 (T \ S)) := by
  simp only [mem_codiscreteWithin, disjoint_iff, AccPt, not_neBot]

/-- Any set is codiscrete within itself. -/
@[simp]
/--
theorem `Filter.self_mem_codiscreteWithin` / 定理 `Filter.self_mem_codiscreteWithin`

English:
theorem Filter.self_mem_codiscreteWithin
  given: (U : Set X)
  proof: by simp [mem_codiscreteWithin]

中文:
定理 Filter.self_mem_codiscreteWithin
  条件: (U : Set X)
  证明: by simp [mem_codiscreteWithin]

Depends on / 依赖: mem_codiscreteWithin
-/
theorem Filter.self_mem_codiscreteWithin (U : Set X) :
    U in Filter.codiscreteWithin U := by simp [mem_codiscreteWithin]

/-- If a set is codiscrete within `U`, then it is codiscrete within any subset of `U`. -/
@[gcongr]
/--
lemma `Filter.codiscreteWithin_mono` / 引理 `Filter.codiscreteWithin_mono`

English:
lemma Filter.codiscreteWithin_mono
  given: {U₁ U : Set X} (hU : U₁ subseteq U)
  proof: by
refine (biSup_mono hU).trans iSup₂_mono fun _ _ => ?_
  gcongr

@[deprecated (since := "2026-05-13")]
alias Filter.codiscreteWithin.mono := Filter.codiscreteWithin_mono

中文:
引理 Filter.codiscreteWithin_mono
  条件: {U₁ U : Set X} (hU : U₁ subseteq U)
  证明: by
refine (biSup_mono hU).trans iSup₂_mono fun _ _ => ?_
  gcongr

@[deprecated (since := "2026-05-13")]
alias Filter.codiscreteWithin.mono := Filter.codiscreteWithin_mono

Depends on / 依赖: biSup_mono
-/
lemma Filter.codiscreteWithin_mono {U₁ U : Set X} (hU : U₁ subseteq U) :
    codiscreteWithin U₁ <= codiscreteWithin U := by
refine (biSup_mono hU).trans iSup₂_mono fun _ _ => ?_
  gcongr

@[deprecated (since := "2026-05-13")]
alias Filter.codiscreteWithin.mono := Filter.codiscreteWithin_mono

/--
theorem `isDiscrete_of_codiscreteWithin` / 定理 `isDiscrete_of_codiscreteWithin`

English:
theorem isDiscrete_of_codiscreteWithin
  given: {U s : Set X} (h : sᶜ in Filter.codiscreteWithin U)
  proof: by
  rw [(by simp : ((s inter U) : Set X) = ((sᶜ union Uᶜ)ᶜ : Set X))]; rw [isDiscrete_iff_nhdsNE]
  simp_rw [← Filter.mem_iff_inf_principal_compl]
  simp_all [← Set.compl_sdiff, mem_codiscreteWithin]

中文:
定理 isDiscrete_of_codiscreteWithin
  条件: {U s : Set X} (h : sᶜ in Filter.codiscreteWithin U)
  证明: by
  rw [(by simp : ((s inter U) : Set X) = ((sᶜ union Uᶜ)ᶜ : Set X))]; rw [isDiscrete_iff_nhdsNE]
  simp_rw [← Filter.mem_iff_inf_principal_compl]
  simp_all [← Set.compl_sdiff, mem_codiscreteWithin]

Depends on / 依赖: Filter, Filter.mem_iff_inf_principal_compl, Set.compl_sdiff, compl_sdiff, isDiscrete_iff_nhdsNE, mem_codiscreteWithin, mem_iff_inf_principal_compl, simp_rw
-/
theorem isDiscrete_of_codiscreteWithin {U s : Set X} (h : sᶜ in Filter.codiscreteWithin U) :
    IsDiscrete (s inter U) := by
  rw [(by simp : ((s inter U) : Set X) = ((sᶜ union Uᶜ)ᶜ : Set X))]; rw [isDiscrete_iff_nhdsNE]
  simp_rw [← Filter.mem_iff_inf_principal_compl]
  simp_all [← Set.compl_sdiff, mem_codiscreteWithin]

/--
lemma `codiscreteWithin_iff_locallyEmptyComplementWithin` / 引理 `codiscreteWithin_iff_locallyEmptyComplementWithin`

English:
lemma codiscreteWithin_iff_locallyEmptyComplementWithin
  given: {s U : Set X}
  proof: by
  simp only [mem_codiscreteWithin, disjoint_principal_right]
  refine ⟨fun h z hz => ⟨(U \ s)ᶜ, h z hz, by simp⟩, fun h z hz => ?_⟩
  rw [← exists_mem_subset_iff]
  obtain ⟨t, h₁t, h₂t⟩ := h z hz
  use t, h₁t, (disjoint_iff_inter_eq_empty.mpr h₂t).subset_compl_right

中文:
引理 codiscreteWithin_iff_locallyEmptyComplementWithin
  条件: {s U : Set X}
  证明: by
  simp only [mem_codiscreteWithin, disjoint_principal_right]
  refine ⟨fun h z hz => ⟨(U \ s)ᶜ, h z hz, by simp⟩, fun h z hz => ?_⟩
  rw [← exists_mem_subset_iff]
  obtain ⟨t, h₁t, h₂t⟩ := h z hz
  use t, h₁t, (disjoint_iff_inter_eq_empty.mpr h₂t).subset_compl_right

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mpr, disjoint_principal_right, exists_mem_subset_iff, mem_codiscreteWithin, subset_compl_right
-/
lemma codiscreteWithin_iff_locallyEmptyComplementWithin {s U : Set X} :
    s in codiscreteWithin U ↔ forall z in U, exists t in 𝓝[!=] z, t inter (U \ s) = ∅ := by
  simp only [mem_codiscreteWithin, disjoint_principal_right]
  refine ⟨fun h z hz => ⟨(U \ s)ᶜ, h z hz, by simp⟩, fun h z hz => ?_⟩
  rw [← exists_mem_subset_iff]
  obtain ⟨t, h₁t, h₂t⟩ := h z hz
  use t, h₁t, (disjoint_iff_inter_eq_empty.mpr h₂t).subset_compl_right

/--
theorem `isClosed_sdiff_of_codiscreteWithin` / 定理 `isClosed_sdiff_of_codiscreteWithin`

English:
theorem isClosed_sdiff_of_codiscreteWithin
  statement: {s U : Set X} (hs : s in codiscreteWithin U)
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x in U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · tauto_set
    · specialize ha h₂a
 

中文:
定理 isClosed_sdiff_of_codiscreteWithin
  结论: {s U : Set X} (hs : s in codiscreteWithin U)
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x in U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · tauto_set
    · specialize ha h₂a
 

Depends on / 依赖: compl_mem_nhds, disjoint_principal_right, eventually_iff_exists_mem, eventually_nhdsWithin_iff, filter_upwards, hU.compl_mem_nhds, isOpen_compl_iff, isOpen_iff_eventually, mem_codiscreteWithin, specialize, tauto_set
-/
theorem isClosed_sdiff_of_codiscreteWithin {s U : Set X} (hs : s in codiscreteWithin U)
    (hU : IsClosed U) :
    IsClosed (U \ s) := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]
  intro x hx
  by_cases h₁x : x in U
  · rw [mem_codiscreteWithin] at hs
    filter_upwards [eventually_nhdsWithin_iff.1 (disjoint_principal_right.1 (hs x h₁x))]
    intro a ha
    by_cases h₂a : a = x
    · tauto_set
    · specialize ha h₂a
      tauto_set
  · rw [eventually_iff_exists_mem]
    use Uᶜ, hU.compl_mem_nhds h₁x
    intro y hy
    tauto_set

/--
theorem `nhdsNE_of_nhdsNE_sdiff_finite` / 定理 `nhdsNE_of_nhdsNE_sdiff_finite`

English:
theorem nhdsNE_of_nhdsNE_sdiff_finite
  statement: {X : Type*} [TopologicalSpace X] [T1Space X] {x : X}
  proof: by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_sdiff]
    exact s.toFinite.sdiff.isClosed.union (isClosed_compl_iff.2 ht)
  · tauto_set

中文:
定理 nhdsNE_of_nhdsNE_sdiff_finite
  结论: {X : 类型} [TopologicalSpace X] [T1Space X] {x : X}
  证明: by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_sdiff]
    exact s.toFinite.sdiff.isClosed.union (isClosed_compl_iff.2 ht)
  · tauto_set

Depends on / 依赖: compl_sdiff, isClosed, isClosed_compl_iff, mem_nhdsWithin, s.toFinite.sdiff.isClosed.union, tauto_set, toFinite
-/
theorem nhdsNE_of_nhdsNE_sdiff_finite {X : Type*} [TopologicalSpace X] [T1Space X] {x : X}
    {U s : Set X} (hU : U in 𝓝[!=] x) (hs : Finite s) :
    U \ s in 𝓝[!=] x := by
  rw [mem_nhdsWithin] at hU ⊢
  obtain ⟨t, ht, h₁ts, h₂ts⟩ := hU
  use t \ (s \ {x})
  constructor
  · rw [← isClosed_compl_iff, compl_sdiff]
    exact s.toFinite.sdiff.isClosed.union (isClosed_compl_iff.2 ht)
  · tauto_set

/--
theorem `codiscreteWithin_iff_locallyFiniteComplementWithin` / 定理 `codiscreteWithin_iff_locallyFiniteComplementWithin`

English:
theorem codiscreteWithin_iff_locallyFiniteComplementWithin
  given: [T1Space X] {s U : Set X}
  proof: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z in U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm,

中文:
定理 codiscreteWithin_iff_locallyFiniteComplementWithin
  条件: [T1Space X] {s U : Set X}
  证明: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z in U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm,

Depends on / 依赖: codiscreteWithin_iff_locallyEmptyComplementWithin, insert, insert_mem_nhds_iff, insert_mem_nhds_iff.mpr, inter_comm, inter_insert_of_mem, inter_insert_of_notMem, mem_nhdsWithin_of_mem_nhds, nhdsNE_of_nhdsNE_sdiff_finite
-/
theorem codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space X] {s U : Set X} :
    s in codiscreteWithin U ↔ forall z in U, exists t in 𝓝 z, Set.Finite (t inter (U \ s)) := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  constructor
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use insert z t, insert_mem_nhds_iff.mpr h₁t
    by_cases hz : z in U \ s
    · rw [inter_comm, inter_insert_of_mem hz, inter_comm, h₂t]
      simp
    · rw [inter_comm, inter_insert_of_notMem hz, inter_comm, h₂t]
      simp
  · intro h z h₁z
    obtain ⟨t, h₁t, h₂t⟩ := h z h₁z
    use t \ (t inter (U \ s)), nhdsNE_of_nhdsNE_sdiff_finite (mem_nhdsWithin_of_mem_nhds h₁t) h₂t
    simp

/--
theorem `Set.Subsingleton.mem_codiscreteWithin` / 定理 `Set.Subsingleton.mem_codiscreteWithin`

English:
theorem Set.Subsingleton.mem_codiscreteWithin
  statement: [T1Space X] {s t : Set X}
  proof: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop

中文:
定理 Set.Subsingleton.mem_codiscreteWithin
  结论: [T1Space X] {s t : Set X}
  证明: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop
-/
@[simp] theorem Set.Subsingleton.mem_codiscreteWithin [T1Space X] {s t : Set X}
    (h : Set.Subsingleton t) :
    s in codiscreteWithin t := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ t, nhdsNE_of_nhdsNE_sdiff_finite univ_mem h.finite, by aesop

/--
In a `T1Space`, complements of singleton sets are codiscrete within any set.
-/
@[simp]
/--
theorem `compl_singleton_mem_codiscreteWithin` / 定理 `compl_singleton_mem_codiscreteWithin`

English:
theorem compl_singleton_mem_codiscreteWithin
  statement: {X : Type*} [TopologicalSpace X] [T1Space X]
  proof: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ {x}
  exact ⟨nhdsNE_of_nhdsNE_sdiff_finite univ_mem Finite.of_subsingleton, by aesop⟩

中文:
定理 compl_singleton_mem_codiscreteWithin
  结论: {X : 类型} [TopologicalSpace X] [T1Space X]
  证明: by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ {x}
  exact ⟨nhdsNE_of_nhdsNE_sdiff_finite univ_mem Finite.of_subsingleton, by aesop⟩

Depends on / 依赖: Finite, Finite.of_subsingleton, codiscreteWithin_iff_locallyEmptyComplementWithin, nhdsNE_of_nhdsNE_sdiff_finite, of_subsingleton, univ_mem
-/
theorem compl_singleton_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (x : X) :
    {x}ᶜ in codiscreteWithin s := by
  rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
  intro z hz
  use univ \ {x}
  exact ⟨nhdsNE_of_nhdsNE_sdiff_finite univ_mem Finite.of_subsingleton, by aesop⟩

/--
theorem `compl_finite_mem_codiscreteWithin` / 定理 `compl_finite_mem_codiscreteWithin`

English:
theorem compl_finite_mem_codiscreteWithin
  statement: {X : Type*} [TopologicalSpace X] [T1Space X]
  proof: by
  apply h.induction_on (motive := fun t _ => tᶜ in codiscreteWithin s)
  · simp
  · intro τ t hτ h₁t h₂t
    have : (insert τ t)ᶜ = {τ}ᶜ inter tᶜ := by aesop
    simp_all

中文:
定理 compl_finite_mem_codiscreteWithin
  结论: {X : 类型} [TopologicalSpace X] [T1Space X]
  证明: by
  apply h.induction_on (motive := fun t _ => tᶜ in codiscreteWithin s)
  · simp
  · intro τ t hτ h₁t h₂t
    have : (insert τ t)ᶜ = {τ}ᶜ inter tᶜ := by aesop
    simp_all

Depends on / 依赖: codiscreteWithin, h.induction_on, induction_on, insert, motive
-/
theorem compl_finite_mem_codiscreteWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    {s t : Set X} (h : t.Finite) :
    tᶜ in codiscreteWithin s := by
  apply h.induction_on (motive := fun t _ => tᶜ in codiscreteWithin s)
  · simp
  · intro τ t hτ h₁t h₂t
    have : (insert τ t)ᶜ = {τ}ᶜ inter tᶜ := by aesop
    simp_all

/--
Definition of `Filter.codiscrete` / `Filter.codiscrete` 的定义

English:
definition Filter.codiscrete
  signature: (X : Type*) [TopologicalSpace X]
  body: codiscreteWithin Set.univ

中文:
定义 Filter.codiscrete
  签名: (X : 类型) [TopologicalSpace X]
  定义体: codiscreteWithin Set.univ

Depends on / 依赖: Set.univ, codiscreteWithin
-/
def Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X := codiscreteWithin Set.univ

/--
lemma `mem_codiscrete` / 引理 `mem_codiscrete`

English:
lemma mem_codiscrete
  given: {S : Set X}
  proof: by
  simp [codiscrete, mem_codiscreteWithin, compl_eq_univ_sdiff]

中文:
引理 mem_codiscrete
  条件: {S : Set X}
  证明: by
  simp [codiscrete, mem_codiscreteWithin, compl_eq_univ_sdiff]

Depends on / 依赖: codiscrete, compl_eq_univ_sdiff, mem_codiscreteWithin
-/
lemma mem_codiscrete {S : Set X} :
    S in codiscrete X ↔ forall x, Disjoint (𝓝[!=] x) (𝓟 Sᶜ) := by
  simp [codiscrete, mem_codiscreteWithin, compl_eq_univ_sdiff]

/--
lemma `Disjoint.eventually_nhdsWithin_specializes` / 引理 `Disjoint.eventually_nhdsWithin_specializes`

English:
lemma Disjoint.eventually_nhdsWithin_specializes
  proof: by
  obtain ⟨t, h₁t, h₂t⟩ := disjoint_cofinite_right.mp hs
  set S := {y in t inter s | ¬(y ⤳ p)}
  have hS_nhds (y) (hy : y in S) : (closure ({y} : Set X))ᶜ in 𝓝 p :=
isClosed_closure.isOpen_compl.mem_nhds by
      simpa [specializes_iff_mem_closure] using hy.2
  filter_upwards [h₁t, nhdsWithin_le_

中文:
引理 Disjoint.eventually_nhdsWithin_specializes
  证明: by
  obtain ⟨t, h₁t, h₂t⟩ := disjoint_cofinite_right.mp hs
  set S := {y in t inter s | ¬(y ⤳ p)}
  have hS_nhds (y) (hy : y in S) : (closure ({y} : Set X))ᶜ in 𝓝 p :=
isClosed_closure.isOpen_compl.mem_nhds by
      simpa [specializes_iff_mem_closure] using hy.2
  filter_upwards [h₁t, nhdsWithin_le_

Depends on / 依赖: biInter_mem, closure, contrapose, disjoint_cofinite_right, disjoint_cofinite_right.mp, filter_upwards, hS_nhds, isClosed_closure, isClosed_closure.isOpen_compl.mem_nhds, isOpen_compl, mem_nhds, nhdsWithin_le_nhds, self_mem_nhdsWithin, specializes_iff_mem_closure, subset, subset_closure, t.subset
-/
lemma Disjoint.eventually_nhdsWithin_specializes
    {p : X} {s : Set X} (hs : Disjoint (𝓝[s] p) cofinite) :
    forallᶠ x in 𝓝[s] p, x ⤳ p := by
  obtain ⟨t, h₁t, h₂t⟩ := disjoint_cofinite_right.mp hs
  set S := {y in t inter s | ¬(y ⤳ p)}
  have hS_nhds (y) (hy : y in S) : (closure ({y} : Set X))ᶜ in 𝓝 p :=
isClosed_closure.isOpen_compl.mem_nhds by
      simpa [specializes_iff_mem_closure] using hy.2
  filter_upwards [h₁t, nhdsWithin_le_nhds ((biInter_mem <| h₂t.subset (by grind)).mpr hS_nhds),
    self_mem_nhdsWithin] with x hxt hxS
  contrapose
  refine fun hxp hxf => mem_iInter₂.mp hxS x ⟨⟨hxt, hxf⟩, hxp⟩ ?_
  grind [subset_closure]

/--
lemma `Disjoint.nhdsWithin_eq_of_cofinite` / 引理 `Disjoint.nhdsWithin_eq_of_cofinite`

English:
lemma Disjoint.nhdsWithin_eq_of_cofinite
  proof: by
  apply le_antisymm
  · simpa using ⟨hs.eventually_nhdsWithin_specializes, self_mem_nhdsWithin⟩
  · rw [← inf_principal, nhdsWithin]
    gcongr
    rw [Filter.principal_le_iff]
    exact fun s hs x hx => mem_of_mem_nhds (hx hs)

中文:
引理 Disjoint.nhdsWithin_eq_of_cofinite
  证明: by
  apply le_antisymm
  · simpa using ⟨hs.eventually_nhdsWithin_specializes, self_mem_nhdsWithin⟩
  · rw [← inf_principal, nhdsWithin]
    gcongr
    rw [Filter.principal_le_iff]
    exact fun s hs x hx => mem_of_mem_nhds (hx hs)

Depends on / 依赖: Filter, Filter.principal_le_iff, eventually_nhdsWithin_specializes, hs.eventually_nhdsWithin_specializes, inf_principal, le_antisymm, mem_of_mem_nhds, nhdsWithin, principal_le_iff, self_mem_nhdsWithin
-/
lemma Disjoint.nhdsWithin_eq_of_cofinite
    {p : X} {s : Set X} (hs : Disjoint (𝓝[s] p) cofinite) :
    𝓝[s] p = 𝓟 ({x | x ⤳ p} inter s) := by
  apply le_antisymm
  · simpa using ⟨hs.eventually_nhdsWithin_specializes, self_mem_nhdsWithin⟩
  · rw [← inf_principal, nhdsWithin]
    gcongr
    rw [Filter.principal_le_iff]
    exact fun s hs x hx => mem_of_mem_nhds (hx hs)

/--
lemma `mem_codiscrete_accPt` / 引理 `mem_codiscrete_accPt`

English:
lemma mem_codiscrete_accPt
  given: {S : Set X}
  proof: by
  simp only [mem_codiscrete, disjoint_iff, AccPt, not_neBot]

中文:
引理 mem_codiscrete_accPt
  条件: {S : Set X}
  证明: by
  simp only [mem_codiscrete, disjoint_iff, AccPt, not_neBot]

Depends on / 依赖: disjoint_iff, mem_codiscrete, not_neBot
-/
lemma mem_codiscrete_accPt {S : Set X} :
    S in codiscrete X ↔ forall x, ¬AccPt x (𝓟 Sᶜ) := by
  simp only [mem_codiscrete, disjoint_iff, AccPt, not_neBot]

/--
lemma `mem_codiscrete'` / 引理 `mem_codiscrete'`

English:
lemma mem_codiscrete'
  given: {S : Set X}
  proof: by
  rw [mem_codiscrete]; rw [← isClosed_compl_iff]; rw [isClosed_and_discrete_iff]

中文:
引理 mem_codiscrete'
  条件: {S : Set X}
  证明: by
  rw [mem_codiscrete]; rw [← isClosed_compl_iff]; rw [isClosed_and_discrete_iff]

Depends on / 依赖: isClosed_and_discrete_iff, isClosed_compl_iff, mem_codiscrete
-/
lemma mem_codiscrete' {S : Set X} :
    S in codiscrete X ↔ IsOpen S ∧ IsDiscrete Sᶜ := by
  rw [mem_codiscrete]; rw [← isClosed_compl_iff]; rw [isClosed_and_discrete_iff]

/--
lemma `compl_mem_codiscrete_iff` / 引理 `compl_mem_codiscrete_iff`

English:
lemma compl_mem_codiscrete_iff
  given: {S : Set X}
  proof: by
  rw [mem_codiscrete]; rw [compl_compl]; rw [isClosed_and_discrete_iff]

中文:
引理 compl_mem_codiscrete_iff
  条件: {S : Set X}
  证明: by
  rw [mem_codiscrete]; rw [compl_compl]; rw [isClosed_and_discrete_iff]

Depends on / 依赖: compl_compl, isClosed_and_discrete_iff, mem_codiscrete
-/
lemma compl_mem_codiscrete_iff {S : Set X} :
    Sᶜ in codiscrete X ↔ IsClosed S ∧ IsDiscrete S := by
  rw [mem_codiscrete]; rw [compl_compl]; rw [isClosed_and_discrete_iff]

/--
lemma `codiscreteWithin_le_codiscrete_inf_principal` / 引理 `codiscreteWithin_le_codiscrete_inf_principal`

English:
lemma codiscreteWithin_le_codiscrete_inf_principal
  given: (s : Set X)
  proof: by
  simp [codiscrete, codiscreteWithin_mono]

中文:
引理 codiscreteWithin_le_codiscrete_inf_principal
  条件: (s : Set X)
  证明: by
  simp [codiscrete, codiscreteWithin_mono]

Depends on / 依赖: codiscrete, codiscreteWithin_mono
-/
lemma codiscreteWithin_le_codiscrete_inf_principal (s : Set X) :
    codiscreteWithin s <= codiscrete X ⊓ 𝓟 s := by
  simp [codiscrete, codiscreteWithin_mono]

/--
theorem `Topology.IsEmbedding.image_mem_codiscreteWithin` / 定理 `Topology.IsEmbedding.image_mem_codiscreteWithin`

English:
theorem Topology.IsEmbedding.image_mem_codiscreteWithin
  statement: {f : X -> Y} (hf : IsEmbedding f)
  proof: by
  simp only [mem_codiscreteWithin_accPt, forall_mem_image, accPt_principal_iff_clusterPt,
    ← hf.mapClusterPt_iff, MapClusterPt, map_principal, image_sdiff hf.injective, image_singleton]

中文:
定理 Topology.IsEmbedding.image_mem_codiscreteWithin
  结论: {f : X -> Y} (hf : IsEmbedding f)
  证明: by
  simp only [mem_codiscreteWithin_accPt, forall_mem_image, accPt_principal_iff_clusterPt,
    ← hf.mapClusterPt_iff, MapClusterPt, map_principal, image_sdiff hf.injective, image_singleton]

Depends on / 依赖: MapClusterPt, accPt_principal_iff_clusterPt, forall_mem_image, hf.injective, hf.mapClusterPt_iff, image_sdiff, image_singleton, injective, mapClusterPt_iff, map_principal, mem_codiscreteWithin_accPt
-/
theorem Topology.IsEmbedding.image_mem_codiscreteWithin {f : X -> Y} (hf : IsEmbedding f)
    {s t : Set X} : f '' s in codiscreteWithin (f '' t) ↔ s in codiscreteWithin t := by
  simp only [mem_codiscreteWithin_accPt, forall_mem_image, accPt_principal_iff_clusterPt,
    ← hf.mapClusterPt_iff, MapClusterPt, map_principal, image_sdiff hf.injective, image_singleton]

/--
theorem `Topology.IsEmbedding.image_mem_codiscreteWithin_range` / 定理 `Topology.IsEmbedding.image_mem_codiscreteWithin_range`

English:
theorem Topology.IsEmbedding.image_mem_codiscreteWithin_range
  statement: {f : X -> Y} (hf : IsEmbedding f)
  proof: by
  rw [← image_univ]; rw [hf.image_mem_codiscreteWithin]; rw [codiscrete]

中文:
定理 Topology.IsEmbedding.image_mem_codiscreteWithin_range
  结论: {f : X -> Y} (hf : IsEmbedding f)
  证明: by
  rw [← image_univ]; rw [hf.image_mem_codiscreteWithin]; rw [codiscrete]

Depends on / 依赖: codiscrete, hf.image_mem_codiscreteWithin, image_mem_codiscreteWithin, image_univ
-/
theorem Topology.IsEmbedding.image_mem_codiscreteWithin_range {f : X -> Y} (hf : IsEmbedding f)
    {s : Set X} : f '' s in codiscreteWithin (range f) ↔ s in codiscrete X := by
  rw [← image_univ]; rw [hf.image_mem_codiscreteWithin]; rw [codiscrete]

/--
lemma `mem_codiscrete_subtype_iff_mem_codiscreteWithin` / 引理 `mem_codiscrete_subtype_iff_mem_codiscreteWithin`

English:
lemma mem_codiscrete_subtype_iff_mem_codiscreteWithin
  given: {S : Set X} {U : Set S}
  proof: by
  simp [← Topology.IsEmbedding.subtypeVal.image_mem_codiscreteWithin_range]

@[simp]

中文:
引理 mem_codiscrete_subtype_iff_mem_codiscreteWithin
  条件: {S : Set X} {U : Set S}
  证明: by
  simp [← Topology.IsEmbedding.subtypeVal.image_mem_codiscreteWithin_range]

@[simp]

Depends on / 依赖: IsEmbedding, Topology, Topology.IsEmbedding.subtypeVal.image_mem_codiscreteWithin_range, image_mem_codiscreteWithin_range, subtypeVal
-/
lemma mem_codiscrete_subtype_iff_mem_codiscreteWithin {S : Set X} {U : Set S} :
    U in codiscrete S ↔ (↑) '' U in codiscreteWithin S := by
  simp [← Topology.IsEmbedding.subtypeVal.image_mem_codiscreteWithin_range]

@[simp]
/--
theorem `codiscreteWithin_eq_bot_iff` / 定理 `codiscreteWithin_eq_bot_iff`

English:
theorem codiscreteWithin_eq_bot_iff
  given: {S : Set X}
  statement: codiscreteWithin S = ⊥ ↔ IsDiscrete S
  proof: by
  simp [isDiscrete_iff_nhdsNE, codiscreteWithin, ← nhdsWithin_inter', Set.sdiff_eq, inter_comm]

中文:
定理 codiscreteWithin_eq_bot_iff
  条件: {S : Set X}
  结论: codiscreteWithin S = ⊥ ↔ IsDiscrete S
  证明: by
  simp [isDiscrete_iff_nhdsNE, codiscreteWithin, ← nhdsWithin_inter', Set.sdiff_eq, inter_comm]

Depends on / 依赖: Set.sdiff_eq, codiscreteWithin, inter_comm, isDiscrete_iff_nhdsNE, nhdsWithin_inter, sdiff_eq
-/
theorem codiscreteWithin_eq_bot_iff {S : Set X} : codiscreteWithin S = ⊥ ↔ IsDiscrete S := by
  simp [isDiscrete_iff_nhdsNE, codiscreteWithin, ← nhdsWithin_inter', Set.sdiff_eq, inter_comm]

section T1Space

variable [T1Space X]

/--
lemma `codiscrete_le_cofinite` / 引理 `codiscrete_le_cofinite`

English:
lemma codiscrete_le_cofinite
  statement: codiscrete X <= cofinite
  proof: by
  intro s hs
  rw [← compl_compl s]; rw [compl_mem_codiscrete_iff]
  exact ⟨hs.isClosed, hs.isDiscrete⟩

中文:
引理 codiscrete_le_cofinite
  结论: codiscrete X <= cofinite
  证明: by
  intro s hs
  rw [← compl_compl s]; rw [compl_mem_codiscrete_iff]
  exact ⟨hs.isClosed, hs.isDiscrete⟩

Depends on / 依赖: compl_compl, compl_mem_codiscrete_iff, hs.isClosed, hs.isDiscrete, isClosed, isDiscrete
-/
lemma codiscrete_le_cofinite : codiscrete X <= cofinite := by
  intro s hs
  rw [← compl_compl s]; rw [compl_mem_codiscrete_iff]
  exact ⟨hs.isClosed, hs.isDiscrete⟩

/--
lemma `Set.Finite.compl_mem_codiscrete` / 引理 `Set.Finite.compl_mem_codiscrete`

English:
lemma Set.Finite.compl_mem_codiscrete
  given: {S : Set X} (hs : S.Finite)
  statement: Sᶜ in codiscrete X
  proof: codiscrete_le_cofinite (by simpa)

中文:
引理 Set.Finite.compl_mem_codiscrete
  条件: {S : Set X} (hs : S.Finite)
  结论: Sᶜ in codiscrete X
  证明: codiscrete_le_cofinite (by simpa)

Depends on / 依赖: codiscrete_le_cofinite
-/
lemma Set.Finite.compl_mem_codiscrete {S : Set X} (hs : S.Finite) : Sᶜ in codiscrete X :=
  codiscrete_le_cofinite (by simpa)

/--
lemma `Set.Infinite.of_accPt` / 引理 `Set.Infinite.of_accPt`

English:
lemma Set.Infinite.of_accPt
  given: {S : Set X} {x : X} (h : AccPt x (𝓟 S))
  statement: S.Infinite
  proof: by
  intro hs
  have := hs.compl_mem_codiscrete
  rw [mem_codiscrete_accPt]; rw [compl_compl] at this
  exact this _ h

中文:
引理 Set.Infinite.of_accPt
  条件: {S : Set X} {x : X} (h : AccPt x (𝓟 S))
  结论: S.Infinite
  证明: by
  intro hs
  have := hs.compl_mem_codiscrete
  rw [mem_codiscrete_accPt]; rw [compl_compl] at this
  exact this _ h

Depends on / 依赖: compl_compl, compl_mem_codiscrete, hs.compl_mem_codiscrete, mem_codiscrete_accPt
-/
lemma Set.Infinite.of_accPt {S : Set X} {x : X} (h : AccPt x (𝓟 S)) : S.Infinite := by
  intro hs
  have := hs.compl_mem_codiscrete
  rw [mem_codiscrete_accPt]; rw [compl_compl] at this
  exact this _ h

end T1Space

namespace IsCompact

variable {K : Set X}

/--
theorem `finite_sdiff_of_mem_codiscreteWithin` / 定理 `finite_sdiff_of_mem_codiscreteWithin`

English:
theorem finite_sdiff_of_mem_codiscreteWithin
  given: (hK : IsCompact K) (hs : s in codiscreteWithin K)
  proof: by
  rw [mem_codiscreteWithin_accPt] at hs
  contrapose! hs
  exact Set.Infinite.exists_accPt_of_subset_isCompact hs hK (sep_subset _ _)

@[deprecated (since := "2026-06-03")]
alias finite_diff_of_mem_codiscreteWithin := finite_sdiff_of_mem_codiscreteWithin

中文:
定理 finite_sdiff_of_mem_codiscreteWithin
  条件: (hK : IsCompact K) (hs : s in codiscreteWithin K)
  证明: by
  rw [mem_codiscreteWithin_accPt] at hs
  contrapose! hs
  exact Set.Infinite.exists_accPt_of_subset_isCompact hs hK (sep_subset _ _)

@[deprecated (since := "2026-06-03")]
alias finite_diff_of_mem_codiscreteWithin := finite_sdiff_of_mem_codiscreteWithin

Depends on / 依赖: Infinite, Set.Infinite.exists_accPt_of_subset_isCompact, contrapose, exists_accPt_of_subset_isCompact, mem_codiscreteWithin_accPt, sep_subset
-/
theorem finite_sdiff_of_mem_codiscreteWithin (hK : IsCompact K) (hs : s in codiscreteWithin K) :
    (K \ s).Finite := by
  rw [mem_codiscreteWithin_accPt] at hs
  contrapose! hs
  exact Set.Infinite.exists_accPt_of_subset_isCompact hs hK (sep_subset _ _)

@[deprecated (since := "2026-06-03")]
alias finite_diff_of_mem_codiscreteWithin := finite_sdiff_of_mem_codiscreteWithin

/--
theorem `cofinite_inf_le_codiscreteWithin` / 定理 `cofinite_inf_le_codiscreteWithin`

English:
theorem cofinite_inf_le_codiscreteWithin
  given: (hK : IsCompact K)
  proof: by
  intro s hs
  simpa [mem_inf_principal, compl_ofPred] using! hK.finite_sdiff_of_mem_codiscreteWithin hs

中文:
定理 cofinite_inf_le_codiscreteWithin
  条件: (hK : IsCompact K)
  证明: by
  intro s hs
  simpa [mem_inf_principal, compl_ofPred] using! hK.finite_sdiff_of_mem_codiscreteWithin hs

Depends on / 依赖: compl_ofPred, finite_sdiff_of_mem_codiscreteWithin, hK.finite_sdiff_of_mem_codiscreteWithin, mem_inf_principal
-/
theorem cofinite_inf_le_codiscreteWithin (hK : IsCompact K) :
    cofinite ⊓ 𝓟 K <= codiscreteWithin K := by
  intro s hs
  simpa [mem_inf_principal, compl_ofPred] using! hK.finite_sdiff_of_mem_codiscreteWithin hs

/--
theorem `codiscreteWithin_eq` / 定理 `codiscreteWithin_eq`

English:
theorem codiscreteWithin_eq
  given: [T1Space X] (hK : IsCompact K)
  proof: by
  refine le_antisymm ?_ hK.cofinite_inf_le_codiscreteWithin
  grw [← codiscrete_le_cofinite]
  exact codiscreteWithin_le_codiscrete_inf_principal K

中文:
定理 codiscreteWithin_eq
  条件: [T1Space X] (hK : IsCompact K)
  证明: by
  refine le_antisymm ?_ hK.cofinite_inf_le_codiscreteWithin
  grw [← codiscrete_le_cofinite]
  exact codiscreteWithin_le_codiscrete_inf_principal K

Depends on / 依赖: codiscreteWithin_le_codiscrete_inf_principal, codiscrete_le_cofinite, cofinite_inf_le_codiscreteWithin, hK.cofinite_inf_le_codiscreteWithin, le_antisymm
-/
theorem codiscreteWithin_eq [T1Space X] (hK : IsCompact K) :
    codiscreteWithin K = cofinite ⊓ 𝓟 K := by
  refine le_antisymm ?_ hK.cofinite_inf_le_codiscreteWithin
  grw [← codiscrete_le_cofinite]
  exact codiscreteWithin_le_codiscrete_inf_principal K

end IsCompact

/--
theorem `cofinite_le_codiscrete` / 定理 `cofinite_le_codiscrete`

English:
theorem cofinite_le_codiscrete
  given: [CompactSpace X]
  statement: cofinite <= codiscrete X
  proof: by
  simpa using! isCompact_univ.cofinite_inf_le_codiscreteWithin

中文:
定理 cofinite_le_codiscrete
  条件: [CompactSpace X]
  结论: cofinite <= codiscrete X
  证明: by
  simpa using! isCompact_univ.cofinite_inf_le_codiscreteWithin

Depends on / 依赖: cofinite_inf_le_codiscreteWithin, isCompact_univ, isCompact_univ.cofinite_inf_le_codiscreteWithin
-/
theorem cofinite_le_codiscrete [CompactSpace X] : cofinite <= codiscrete X := by
  simpa using! isCompact_univ.cofinite_inf_le_codiscreteWithin

/--
theorem `codiscrete_eq_cofinite` / 定理 `codiscrete_eq_cofinite`

English:
theorem codiscrete_eq_cofinite
  given: [T1Space X] [CompactSpace X]
  statement: codiscrete X = cofinite
  proof: by
  simpa using! isCompact_univ.codiscreteWithin_eq

中文:
定理 codiscrete_eq_cofinite
  条件: [T1Space X] [CompactSpace X]
  结论: codiscrete X = cofinite
  证明: by
  simpa using! isCompact_univ.codiscreteWithin_eq

Depends on / 依赖: codiscreteWithin_eq, isCompact_univ, isCompact_univ.codiscreteWithin_eq
-/
theorem codiscrete_eq_cofinite [T1Space X] [CompactSpace X] : codiscrete X = cofinite := by
  simpa using! isCompact_univ.codiscreteWithin_eq

end codiscrete_filter

/-! ### Finite union of discrete closed sets -/

section discrete_union

/--
theorem `IsDiscrete.iUnion` / 定理 `IsDiscrete.iUnion`

English:
theorem IsDiscrete.iUnion
  statement: {ι : Sort*} [Finite ι] {s : ι -> Set X} (hs : forall i, IsDiscrete (s i))
  proof: by
  suffices (⋃ i, s i)ᶜ in codiscrete X from (compl_mem_codiscrete_iff.mp this).2
  simp [compl_mem_codiscrete_iff, *]

中文:
定理 IsDiscrete.iUnion
  结论: {ι : Sort*} [Finite ι] {s : ι -> Set X} (hs : 对任意 i, IsDiscrete (s i))
  证明: by
  suffices (⋃ i, s i)ᶜ in codiscrete X from (compl_mem_codiscrete_iff.mp this).2
  simp [compl_mem_codiscrete_iff, *]

Depends on / 依赖: codiscrete, compl_mem_codiscrete_iff, compl_mem_codiscrete_iff.mp
-/
theorem IsDiscrete.iUnion {ι : Sort*} [Finite ι] {s : ι -> Set X} (hs : forall i, IsDiscrete (s i))
    (hsc : forall i, IsClosed (s i)) : IsDiscrete (⋃ i, s i) := by
  suffices (⋃ i, s i)ᶜ in codiscrete X from (compl_mem_codiscrete_iff.mp this).2
  simp [compl_mem_codiscrete_iff, *]

/--
theorem `IsDiscrete.union` / 定理 `IsDiscrete.union`

English:
theorem IsDiscrete.union
  statement: {s t : Set X} (hs : IsDiscrete s) (ht : IsDiscrete t)
  proof: by
  rw [union_eq_iUnion]
  exact .iUnion (by simp [*]) (by simp [*])

中文:
定理 IsDiscrete.union
  结论: {s t : Set X} (hs : IsDiscrete s) (ht : IsDiscrete t)
  证明: by
  rw [union_eq_iUnion]
  exact .iUnion (by simp [*]) (by simp [*])

Depends on / 依赖: iUnion, union_eq_iUnion
-/
theorem IsDiscrete.union {s t : Set X} (hs : IsDiscrete s) (ht : IsDiscrete t)
    (hsc : IsClosed s) (ht : IsClosed t) : IsDiscrete (s union t) := by
  rw [union_eq_iUnion]
  exact .iUnion (by simp [*]) (by simp [*])

/--
theorem `IsDiscrete.biUnion` / 定理 `IsDiscrete.biUnion`

English:
theorem IsDiscrete.biUnion
  statement: {ι : Type*} {I : Set ι} {s : ι -> Set X} (hI : I.Finite)
  proof: by
  have := hI.to_subtype
  simp only [biUnion_eq_iUnion, Subtype.forall'] at *
  exact .iUnion hs hsc

中文:
定理 IsDiscrete.biUnion
  结论: {ι : 类型} {I : Set ι} {s : ι -> Set X} (hI : I.Finite)
  证明: by
  have := hI.to_subtype
  simp only [biUnion_eq_iUnion, Subtype.forall'] at *
  exact .iUnion hs hsc

Depends on / 依赖: Subtype, Subtype.forall, biUnion_eq_iUnion, hI.to_subtype, iUnion, to_subtype
-/
theorem IsDiscrete.biUnion {ι : Type*} {I : Set ι} {s : ι -> Set X} (hI : I.Finite)
    (hs : forall i in I, IsDiscrete (s i)) (hsc : forall i in I, IsClosed (s i)) :
    IsDiscrete (⋃ i in I, s i) := by
  have := hI.to_subtype
  simp only [biUnion_eq_iUnion, Subtype.forall'] at *
  exact .iUnion hs hsc

/--
theorem `IsDiscrete.biUnion_finset` / 定理 `IsDiscrete.biUnion_finset`

English:
theorem IsDiscrete.biUnion_finset
  statement: {ι : Type*} {I : Finset ι} {s : ι -> Set X}
  proof: .biUnion I.finite_toSet hs hsc

中文:
定理 IsDiscrete.biUnion_finset
  结论: {ι : 类型} {I : Finset ι} {s : ι -> Set X}
  证明: .biUnion I.finite_toSet hs hsc

Depends on / 依赖: I.finite_toSet, biUnion, finite_toSet
-/
theorem IsDiscrete.biUnion_finset {ι : Type*} {I : Finset ι} {s : ι -> Set X}
    (hs : forall i in I, IsDiscrete (s i)) (hsc : forall i in I, IsClosed (s i)) :
    IsDiscrete (⋃ i in I, s i) :=
  .biUnion I.finite_toSet hs hsc

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.union (since := "2026-05-13")]
/--
theorem `discreteTopology_union` / 定理 `discreteTopology_union`

English:
theorem discreteTopology_union
  statement: {S T : Set X} (hs : DiscreteTopology S) (ht : DiscreteTopology T)
  proof: by
  rw [← isDiscrete_iff_discreteTopology] at *
  exact hs.union ht hs' ht'

中文:
定理 discreteTopology_union
  结论: {S T : Set X} (hs : DiscreteTopology S) (ht : DiscreteTopology T)
  证明: by
  rw [← isDiscrete_iff_discreteTopology] at *
  exact hs.union ht hs' ht'

Depends on / 依赖: hs.union, isDiscrete_iff_discreteTopology
-/
theorem discreteTopology_union {S T : Set X} (hs : DiscreteTopology S) (ht : DiscreteTopology T)
    (hs' : IsClosed S) (ht' : IsClosed T) : DiscreteTopology ↑(S union T) := by
  rw [← isDiscrete_iff_discreteTopology] at *
  exact hs.union ht hs' ht'

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.biUnion_finset (since := "2026-05-13")]
/--
theorem `discreteTopology_biUnion_finset` / 定理 `discreteTopology_biUnion_finset`

English:
theorem discreteTopology_biUnion_finset
  statement: {ι : Type*} {I : Finset ι} {s : ι -> Set X}
  proof: by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .biUnion_finset hs hs'

中文:
定理 discreteTopology_biUnion_finset
  结论: {ι : 类型} {I : Finset ι} {s : ι -> Set X}
  证明: by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .biUnion_finset hs hs'

Depends on / 依赖: biUnion_finset, isDiscrete_iff_discreteTopology
-/
theorem discreteTopology_biUnion_finset {ι : Type*} {I : Finset ι} {s : ι -> Set X}
    (hs : forall i in I, DiscreteTopology (s i)) (hs' : forall i in I, IsClosed (s i)) :
    DiscreteTopology (⋃ i in I, s i) := by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .biUnion_finset hs hs'

/-- The union of finitely many discrete closed subsets is discrete. -/
@[deprecated IsDiscrete.iUnion (since := "2026-05-13")]
/--
theorem `discreteTopology_iUnion_finite` / 定理 `discreteTopology_iUnion_finite`

English:
theorem discreteTopology_iUnion_finite
  statement: {ι : Type*} [Finite ι] {s : ι -> Set X}
  proof: by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .iUnion hs hs'

中文:
定理 discreteTopology_iUnion_finite
  结论: {ι : 类型} [Finite ι] {s : ι -> Set X}
  证明: by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .iUnion hs hs'

Depends on / 依赖: iUnion, isDiscrete_iff_discreteTopology
-/
theorem discreteTopology_iUnion_finite {ι : Type*} [Finite ι] {s : ι -> Set X}
    (hs : forall i, DiscreteTopology (s i)) (hs' : forall i, IsClosed (s i)) :
    DiscreteTopology (⋃ i, s i) := by
  simp only [← isDiscrete_iff_discreteTopology] at *
  exact .iUnion hs hs'

end discrete_union
