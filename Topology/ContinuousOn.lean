/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.NhdsWithin

/-!
# Neighborhoods and continuity relative to a subset

This file develops API on the relative versions

* `ContinuousOn` of `Continuous`
* `ContinuousWithinAt` of `ContinuousAt`

related to continuity, which are defined in previous definition files.
Their basic properties studied in this file include the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

-/

public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ] {f g : α -> β} {s s' s₁ t : Set α} {x : α}

/-!
## `ContinuousWithinAt`
-/

/--
theorem `ContinuousWithinAt.tendsto` / 定理 `ContinuousWithinAt.tendsto`

English:
theorem ContinuousWithinAt.tendsto
  given: (h : ContinuousWithinAt f s x)
  proof: h

中文:
定理 ContinuousWithinAt.tendsto
  条件: (h : ContinuousWithinAt f s x)
  证明: h
-/
theorem ContinuousWithinAt.tendsto (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝 (f x)) :=
  h

/--
theorem `continuousWithinAt_univ` / 定理 `continuousWithinAt_univ`

English:
theorem continuousWithinAt_univ
  given: (f : α -> β) (x : α)
  proof: by
  rw [ContinuousAt]; rw [ContinuousWithinAt]; rw [nhdsWithin_univ]

@[simp]

中文:
定理 continuousWithinAt_univ
  条件: (f : α -> β) (x : α)
  证明: by
  rw [ContinuousAt]; rw [ContinuousWithinAt]; rw [nhdsWithin_univ]

@[simp]

Depends on / 依赖: ContinuousAt, ContinuousWithinAt, nhdsWithin_univ
-/
theorem continuousWithinAt_univ (f : α -> β) (x : α) :
    ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt]; rw [ContinuousWithinAt]; rw [nhdsWithin_univ]

@[simp]
/--
theorem `continuousOn_univ` / 定理 `continuousOn_univ`

English:
theorem continuousOn_univ
  given: {f : α -> β}
  statement: ContinuousOn f univ ↔ Continuous f
  proof: by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]

中文:
定理 continuousOn_univ
  条件: {f : α -> β}
  结论: ContinuousOn f univ ↔ 连续 f
  证明: by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]

Depends on / 依赖: ContinuousAt, ContinuousOn, ContinuousWithinAt, continuous_iff_continuousAt, nhdsWithin_univ
-/
theorem continuousOn_univ {f : α -> β} : ContinuousOn f univ ↔ Continuous f := by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]

/--
theorem `continuousWithinAt_iff_continuousAt_domRestrict` / 定理 `continuousWithinAt_iff_continuousAt_domRestrict`

English:
theorem continuousWithinAt_iff_continuousAt_domRestrict
  statement: (f : α -> β) {x : α} {s : Set α}
  proof: tendsto_nhdsWithin_iff_subtype h f _

@[deprecated (since := "2026-07-19")] alias continuousWithinAt_iff_continuousAt_restrict :=
  continuousWithinAt_iff_continuousAt_domRestrict

中文:
定理 continuousWithinAt_iff_continuousAt_domRestrict
  结论: (f : α -> β) {x : α} {s : 集合 α}
  证明: tendsto_nhdsWithin_iff_subtype h f _

@[deprecated (since := "2026-07-19")] alias continuousWithinAt_iff_continuousAt_restrict :=
  continuousWithinAt_iff_continuousAt_domRestrict

Depends on / 依赖: tendsto_nhdsWithin_iff_subtype
-/
theorem continuousWithinAt_iff_continuousAt_domRestrict (f : α -> β) {x : α} {s : Set α}
    (h : x in s) : ContinuousWithinAt f s x ↔ ContinuousAt (s.domRestrict f) ⟨x, h⟩ :=
  tendsto_nhdsWithin_iff_subtype h f _

@[deprecated (since := "2026-07-19")] alias continuousWithinAt_iff_continuousAt_restrict :=
  continuousWithinAt_iff_continuousAt_domRestrict

/--
theorem `ContinuousWithinAt.tendsto_nhdsWithin` / 定理 `ContinuousWithinAt.tendsto_nhdsWithin`

English:
theorem ContinuousWithinAt.tendsto_nhdsWithin
  statement: {t : Set β}
  proof: tendsto_inf.2 ⟨h, tendsto_principal.2 mem_inf_of_right mem_principal.2 ht⟩

中文:
定理 ContinuousWithinAt.tendsto_nhdsWithin
  结论: {t : 集合 β}
  证明: tendsto_inf.2 ⟨h, tendsto_principal.2 mem_inf_of_right mem_principal.2 ht⟩

Depends on / 依赖: mem_inf_of_right, mem_principal, tendsto_inf, tendsto_principal
-/
theorem ContinuousWithinAt.tendsto_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) :
    Tendsto f (𝓝[s] x) (𝓝[t] f x) :=
tendsto_inf.2 ⟨h, tendsto_principal.2 mem_inf_of_right mem_principal.2 ht⟩

/--
theorem `ContinuousWithinAt.tendsto_nhdsWithin_image` / 定理 `ContinuousWithinAt.tendsto_nhdsWithin_image`

English:
theorem ContinuousWithinAt.tendsto_nhdsWithin_image
  given: (h : ContinuousWithinAt f s x)
  proof: h.tendsto_nhdsWithin (mapsTo_image _ _)

中文:
定理 ContinuousWithinAt.tendsto_nhdsWithin_image
  条件: (h : ContinuousWithinAt f s x)
  证明: h.tendsto_nhdsWithin (mapsTo_image _ _)

Depends on / 依赖: h.tendsto_nhdsWithin, mapsTo_image, tendsto_nhdsWithin
-/
theorem ContinuousWithinAt.tendsto_nhdsWithin_image (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝[f '' s] f x) :=
  h.tendsto_nhdsWithin (mapsTo_image _ _)

/--
theorem `nhdsWithin_le_comap` / 定理 `nhdsWithin_le_comap`

English:
theorem nhdsWithin_le_comap
  given: (ctsf : ContinuousWithinAt f s x)
  proof: ctsf.tendsto_nhdsWithin_image.le_comap

中文:
定理 nhdsWithin_le_comap
  条件: (ctsf : ContinuousWithinAt f s x)
  证明: ctsf.tendsto_nhdsWithin_image.le_comap

Depends on / 依赖: ctsf.tendsto_nhdsWithin_image.le_comap, le_comap, tendsto_nhdsWithin_image
-/
theorem nhdsWithin_le_comap (ctsf : ContinuousWithinAt f s x) :
    𝓝[s] x <= comap f (𝓝[f '' s] f x) :=
  ctsf.tendsto_nhdsWithin_image.le_comap

/--
theorem `ContinuousWithinAt.preimage_mem_nhdsWithin` / 定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`

English:
theorem ContinuousWithinAt.preimage_mem_nhdsWithin
  statement: {t : Set β}
  proof: h ht

中文:
定理 ContinuousWithinAt.preimage_mem_nhdsWithin
  结论: {t : 集合 β}
  证明: h ht
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝[s] x :=
  h ht

/--
theorem `ContinuousWithinAt.preimage_mem_nhdsWithin'` / 定理 `ContinuousWithinAt.preimage_mem_nhdsWithin'`

English:
theorem ContinuousWithinAt.preimage_mem_nhdsWithin'
  statement: {t : Set β}
  proof: h.tendsto_nhdsWithin (mapsTo_image _ _) ht

中文:
定理 ContinuousWithinAt.preimage_mem_nhdsWithin'
  结论: {t : 集合 β}
  证明: h.tendsto_nhdsWithin (mapsTo_image _ _) ht

Depends on / 依赖: h.tendsto_nhdsWithin, mapsTo_image, tendsto_nhdsWithin
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin' {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t in 𝓝[f '' s] f x) : f ⁻¹' t in 𝓝[s] x :=
  h.tendsto_nhdsWithin (mapsTo_image _ _) ht

/--
theorem `ContinuousWithinAt.preimage_mem_nhdsWithin''` / 定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`

English:
theorem ContinuousWithinAt.preimage_mem_nhdsWithin''
  statement: {y : β} {s t : Set β}
  proof: by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)

中文:
定理 ContinuousWithinAt.preimage_mem_nhdsWithin''
  结论: {y : β} {s t : 集合 β}
  证明: by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)

Depends on / 依赖: h.preimage_mem_nhdsWithin, image_preimage_subset, nhdsWithin_mono, preimage_mem_nhdsWithin
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin'' {y : β} {s t : Set β}
    (h : ContinuousWithinAt f (f ⁻¹' s) x) (ht : t in 𝓝[s] y) (hxy : y = f x) :
    f ⁻¹' t in 𝓝[f ⁻¹' s] x := by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)

/--
theorem `continuousWithinAt_of_notMem_closure` / 定理 `continuousWithinAt_of_notMem_closure`

English:
theorem continuousWithinAt_of_notMem_closure
  given: (hx : x ∉ closure s)
  proof: by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot] at hx
  rw [ContinuousWithinAt]; rw [hx]
  exact tendsto_bot

中文:
定理 continuousWithinAt_of_notMem_closure
  条件: (hx : x ∉ closure s)
  证明: by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot] at hx
  rw [ContinuousWithinAt]; rw [hx]
  exact tendsto_bot

Depends on / 依赖: ContinuousWithinAt, mem_closure_iff_nhdsWithin_neBot, not_neBot, tendsto_bot
-/
theorem continuousWithinAt_of_notMem_closure (hx : x ∉ closure s) :
    ContinuousWithinAt f s x := by
  rw [mem_closure_iff_nhdsWithin_neBot]; rw [not_neBot] at hx
  rw [ContinuousWithinAt]; rw [hx]
  exact tendsto_bot


/--
theorem `continuousOn_iff` / 定理 `continuousOn_iff`

English:
theorem continuousOn_iff
  proof: by
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]

中文:
定理 continuousOn_iff
  证明: by
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]

Depends on / 依赖: ContinuousOn, ContinuousWithinAt, mem_nhdsWithin, tendsto_nhds
-/
theorem continuousOn_iff :
    ContinuousOn f s ↔
      forall x in s, forall t : Set β, IsOpen t -> f x in t -> exists u, IsOpen u ∧ x in u ∧ u inter s subseteq f ⁻¹' t := by
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]

/--
theorem `ContinuousOn.continuousWithinAt` / 定理 `ContinuousOn.continuousWithinAt`

English:
theorem ContinuousOn.continuousWithinAt
  given: (hf : ContinuousOn f s) (hx : x in s)
  proof: hf x hx

中文:
定理 ContinuousOn.continuousWithinAt
  条件: (hf : ContinuousOn f s) (hx : x in s)
  证明: hf x hx
-/
theorem ContinuousOn.continuousWithinAt (hf : ContinuousOn f s) (hx : x in s) :
    ContinuousWithinAt f s x :=
  hf x hx

/--
theorem `continuousOn_iff_continuous_domRestrict` / 定理 `continuousOn_iff_continuous_domRestrict`

English:
theorem continuousOn_iff_continuous_domRestrict
  proof: by
  rw [ContinuousOn]; rw [continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mpr (h ⟨x, xs⟩)

alias ⟨ContinuousOn.domRestrict, _⟩ :

中文:
定理 continuousOn_iff_continuous_domRestrict
  证明: by
  rw [ContinuousOn]; rw [continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mpr (h ⟨x, xs⟩)

alias ⟨ContinuousOn.domRestrict, _⟩ :

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff_continuousAt_domRestrict, continuous_iff_continuousAt
-/
theorem continuousOn_iff_continuous_domRestrict :
    ContinuousOn f s ↔ Continuous (s.domRestrict f) := by
  rw [ContinuousOn]; rw [continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mpr (h ⟨x, xs⟩)

alias ⟨ContinuousOn.domRestrict, _⟩ := continuousOn_iff_continuous_domRestrict

@[deprecated (since := "2026-07-19")]
alias continuousOn_iff_continuous_restrict := continuousOn_iff_continuous_domRestrict
@[deprecated (since := "2026-07-19")]
alias ContinuousOn.restrict := ContinuousOn.domRestrict

/--
theorem `ContinuousOn.mapsToRestrict` / 定理 `ContinuousOn.mapsToRestrict`

English:
theorem ContinuousOn.mapsToRestrict
  given: {t : Set β} (hf : ContinuousOn f s) (ht : MapsTo f s t)
  proof: hf.domRestrict.codRestrict _

中文:
定理 ContinuousOn.mapsToRestrict
  条件: {t : 集合 β} (hf : ContinuousOn f s) (ht : 映射到 f s t)
  证明: hf.domRestrict.codRestrict _

Depends on / 依赖: codRestrict, domRestrict, hf.domRestrict.codRestrict
-/
theorem ContinuousOn.mapsToRestrict {t : Set β} (hf : ContinuousOn f s) (ht : MapsTo f s t) :
    Continuous (ht.restrict f s t) :=
  hf.domRestrict.codRestrict _

/--
theorem `continuousOn_iff'` / 定理 `continuousOn_iff'`

English:
theorem continuousOn_iff'
  proof: by
  have : forall t, IsOpen (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isOpen_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨

中文:
定理 continuousOn_iff'
  证明: by
  have : forall t, IsOpen (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isOpen_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨

Depends on / 依赖: IsOpen, Set.domRestrict_eq, Set.inter_comm, Set.preimage_comp, Subtype, Subtype.preimage_coe_eq_preimage_coe_iff, continuousOn_iff_continuous_domRestrict, continuous_def, domRestrict, domRestrict_eq, eq_comm, inter_comm, isOpen_induced_iff, preimage_coe_eq_preimage_coe_iff, preimage_comp, s.domRestrict
-/
theorem continuousOn_iff' :
    ContinuousOn f s ↔ forall t : Set β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s := by
  have : forall t, IsOpen (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isOpen_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, by simpa only [Set.inter_comm, eq_comm] using useq⟩
  rw [continuousOn_iff_continuous_domRestrict]; rw [continuous_def]; simp only [this]

/--
theorem `ContinuousOn.mono_dom` / 定理 `ContinuousOn.mono_dom`

English:
theorem ContinuousOn.mono_dom
  statement: {α β : Type*} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
  proof: fun x hx _u hu =>
  map_mono (inf_le_inf_right _ <| nhds_mono h₁) (h₂ x hx hu)

中文:
定理 ContinuousOn.mono_dom
  结论: {α β : 类型} {t₁ t₂ : 拓扑空间 α} {t₃ : 拓扑空间 β}
  证明: fun x hx _u hu =>
  map_mono (inf_le_inf_right _ <| nhds_mono h₁) (h₂ x hx hu)
-/
theorem ContinuousOn.mono_dom {α β : Type*} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
    (h₁ : t₂ <= t₁) {s : Set α} {f : α -> β} (h₂ : @ContinuousOn α β t₁ t₃ f s) :
    @ContinuousOn α β t₂ t₃ f s := fun x hx _u hu =>
  map_mono (inf_le_inf_right _ <| nhds_mono h₁) (h₂ x hx hu)

/--
theorem `ContinuousOn.mono_rng` / 定理 `ContinuousOn.mono_rng`

English:
theorem ContinuousOn.mono_rng
  statement: {α β : Type*} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
  proof: fun x hx _u hu =>
h₂ x hx nhds_mono h₁ hu

中文:
定理 ContinuousOn.mono_rng
  结论: {α β : 类型} {t₁ : 拓扑空间 α} {t₂ t₃ : 拓扑空间 β}
  证明: fun x hx _u hu =>
h₂ x hx nhds_mono h₁ hu
-/
theorem ContinuousOn.mono_rng {α β : Type*} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
    (h₁ : t₂ <= t₃) {s : Set α} {f : α -> β} (h₂ : @ContinuousOn α β t₁ t₂ f s) :
    @ContinuousOn α β t₁ t₃ f s := fun x hx _u hu =>
h₂ x hx nhds_mono h₁ hu

/--
theorem `continuousOn_iff_isClosed` / 定理 `continuousOn_iff_isClosed`

English:
theorem continuousOn_iff_isClosed
  proof: by
  have : forall t, IsClosed (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsClosed u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isClosed_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm, Set.inter_comm s]
  r

中文:
定理 continuousOn_iff_isClosed
  证明: by
  have : forall t, IsClosed (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsClosed u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isClosed_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm, Set.inter_comm s]
  r

Depends on / 依赖: IsClosed, Set.domRestrict_eq, Set.inter_comm, Set.preimage_comp, Subtype, Subtype.preimage_coe_eq_preimage_coe_iff, continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed, domRestrict, domRestrict_eq, eq_comm, inter_comm, isClosed_induced_iff, preimage_coe_eq_preimage_coe_iff, preimage_comp, s.domRestrict
-/
theorem continuousOn_iff_isClosed :
    ContinuousOn f s ↔ forall t : Set β, IsClosed t -> exists u, IsClosed u ∧ f ⁻¹' t inter s = u inter s := by
  have : forall t, IsClosed (s.domRestrict f ⁻¹' t) ↔ exists u : Set α, IsClosed u ∧ f ⁻¹' t inter s = u inter s := by
    intro t
    rw [isClosed_induced_iff]; rw [Set.domRestrict_eq]; rw [Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm, Set.inter_comm s]
  rw [continuousOn_iff_continuous_domRestrict]; rw [continuous_iff_isClosed]; simp only [this]

/--
theorem `continuous_of_cover_nhds` / 定理 `continuous_of_cover_nhds`

English:
theorem continuous_of_cover_nhds
  statement: {ι : Sort*} {s : ι -> Set α}
  proof: continuous_iff_continuousAt.mpr fun x => let ⟨i, hi⟩ := hs x; by
    rw [ContinuousAt]; rw [← nhdsWithin_eq_nhds.2 hi]
    exact hf _ _ (mem_of_mem_nhds hi)

中文:
定理 continuous_of_cover_nhds
  结论: {ι : 类型层*} {s : ι -> 集合 α}
  证明: continuous_iff_continuousAt.mpr fun x => let ⟨i, hi⟩ := hs x; by
    rw [ContinuousAt]; rw [← nhdsWithin_eq_nhds.2 hi]
    exact hf _ _ (mem_of_mem_nhds hi)

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, mem_of_mem_nhds, nhdsWithin_eq_nhds
-/
theorem continuous_of_cover_nhds {ι : Sort*} {s : ι -> Set α}
    (hs : forall x : α, exists i, s i in 𝓝 x) (hf : forall i, ContinuousOn f (s i)) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x => let ⟨i, hi⟩ := hs x; by
    rw [ContinuousAt]; rw [← nhdsWithin_eq_nhds.2 hi]
    exact hf _ _ (mem_of_mem_nhds hi)

/--
theorem `continuousOn_empty` / 定理 `continuousOn_empty`

English:
theorem continuousOn_empty
  given: (f : α -> β)
  statement: ContinuousOn f ∅
  proof: fun _ => False.elim

@[simp]

中文:
定理 continuousOn_empty
  条件: (f : α -> β)
  结论: ContinuousOn f ∅
  证明: fun _ => False.elim

@[simp]
-/
@[simp] theorem continuousOn_empty (f : α -> β) : ContinuousOn f ∅ := fun _ => False.elim

@[simp]
/--
theorem `continuousOn_singleton` / 定理 `continuousOn_singleton`

English:
theorem continuousOn_singleton
  given: (f : α -> β) (a : α)
  statement: ContinuousOn f {a}
  proof: forall_eq.2 by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds

中文:
定理 continuousOn_singleton
  条件: (f : α -> β) (a : α)
  结论: ContinuousOn f {a}
  证明: forall_eq.2 by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds

Depends on / 依赖: ContinuousWithinAt, forall_eq, mem_of_mem_nhds, nhdsWithin_singleton, tendsto_pure_left
-/
theorem continuousOn_singleton (f : α -> β) (a : α) : ContinuousOn f {a} :=
forall_eq.2 by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds

/--
theorem `Set.Subsingleton.continuousOn` / 定理 `Set.Subsingleton.continuousOn`

English:
theorem Set.Subsingleton.continuousOn
  given: {s : Set α} (hs : s.Subsingleton) (f : α -> β)
  proof: hs.induction_on (continuousOn_empty f) (continuousOn_singleton f)

中文:
定理 集合.子单例.continuousOn
  条件: {s : 集合 α} (hs : s.子单例) (f : α -> β)
  证明: hs.induction_on (continuousOn_empty f) (continuousOn_singleton f)

Depends on / 依赖: continuousOn_empty, continuousOn_singleton, hs.induction_on, induction_on
-/
theorem Set.Subsingleton.continuousOn {s : Set α} (hs : s.Subsingleton) (f : α -> β) :
    ContinuousOn f s :=
  hs.induction_on (continuousOn_empty f) (continuousOn_singleton f)

/--
theorem `continuousOn_open_iff` / 定理 `continuousOn_open_iff`

English:
theorem continuousOn_open_iff
  given: (hs : IsOpen s)
  proof: by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm]; rw [hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine ⟨s inter f ⁻¹' t, h t ht, ?_⟩
    rw [@inter_comm _ s (f ⁻¹' t)]; rw [inter_assoc]; rw [inter_self]

中文:
定理 continuousOn_open_iff
  条件: (hs : 是开集 s)
  证明: by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm]; rw [hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine ⟨s inter f ⁻¹' t, h t ht, ?_⟩
    rw [@inter_comm _ s (f ⁻¹' t)]; rw [inter_assoc]; rw [inter_self]

Depends on / 依赖: IsOpen, IsOpen.inter, continuousOn_iff, inter_assoc, inter_comm, inter_self, u_open
-/
theorem continuousOn_open_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ forall t, IsOpen t -> IsOpen (s inter f ⁻¹' t) := by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm]; rw [hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine ⟨s inter f ⁻¹' t, h t ht, ?_⟩
    rw [@inter_comm _ s (f ⁻¹' t)]; rw [inter_assoc]; rw [inter_self]

/--
theorem `ContinuousOn.isOpen_inter_preimage` / 定理 `ContinuousOn.isOpen_inter_preimage`

English:
theorem ContinuousOn.isOpen_inter_preimage
  statement: {t : Set β}
  proof: (continuousOn_open_iff hs).1 hf t ht

中文:
定理 ContinuousOn.isOpen_inter_preimage
  结论: {t : 集合 β}
  证明: (continuousOn_open_iff hs).1 hf t ht

Depends on / 依赖: continuousOn_open_iff
-/
theorem ContinuousOn.isOpen_inter_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s inter f ⁻¹' t) :=
  (continuousOn_open_iff hs).1 hf t ht

/--
theorem `ContinuousOn.isOpen_preimage` / 定理 `ContinuousOn.isOpen_preimage`

English:
theorem ContinuousOn.isOpen_preimage
  statement: {t : Set β} (h : ContinuousOn f s)
  proof: by
  convert! (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm]; rw [inter_eq_self_of_subset_left hp]

中文:
定理 ContinuousOn.isOpen_preimage
  结论: {t : 集合 β} (h : ContinuousOn f s)
  证明: by
  convert! (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm]; rw [inter_eq_self_of_subset_left hp]

Depends on / 依赖: continuousOn_open_iff, convert, inter_comm, inter_eq_self_of_subset_left
-/
theorem ContinuousOn.isOpen_preimage {t : Set β} (h : ContinuousOn f s)
    (hs : IsOpen s) (hp : f ⁻¹' t subseteq s) (ht : IsOpen t) : IsOpen (f ⁻¹' t) := by
  convert! (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm]; rw [inter_eq_self_of_subset_left hp]

/--
theorem `ContinuousOn.preimage_isClosed_of_isClosed` / 定理 `ContinuousOn.preimage_isClosed_of_isClosed`

English:
theorem ContinuousOn.preimage_isClosed_of_isClosed
  statement: {t : Set β}
  proof: by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm]; rw [hu.2]
  apply IsClosed.inter hu.1 hs

中文:
定理 ContinuousOn.preimage_isClosed_of_isClosed
  结论: {t : 集合 β}
  证明: by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm]; rw [hu.2]
  apply IsClosed.inter hu.1 hs

Depends on / 依赖: IsClosed, IsClosed.inter, continuousOn_iff_isClosed, inter_comm
-/
theorem ContinuousOn.preimage_isClosed_of_isClosed {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s inter f ⁻¹' t) := by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm]; rw [hu.2]
  apply IsClosed.inter hu.1 hs

/--
theorem `ContinuousOn.preimage_interior_subset_interior_preimage` / 定理 `ContinuousOn.preimage_interior_subset_interior_preimage`

English:
theorem ContinuousOn.preimage_interior_subset_interior_preimage
  statement: {t : Set β}
  proof: calc
    s inter f ⁻¹' interior t subseteq interior (s inter f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.isOpen_inter_preimage hs isOpen_interior)
    _ = s inter interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]

中文:
定理 ContinuousOn.preimage_interior_subset_interior_preimage
  结论: {t : 集合 β}
  证明: calc
    s inter f ⁻¹' interior t subseteq interior (s inter f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.isOpen_inter_preimage hs isOpen_interior)
    _ = s inter interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]

Depends on / 依赖: Subset, Subset.refl, hf.isOpen_inter_preimage, hs.interior_eq, inter_subset_inter, interior, interior_eq, interior_inter, interior_maximal, interior_subset, isOpen_inter_preimage, isOpen_interior, preimage_mono, subseteq
-/
theorem ContinuousOn.preimage_interior_subset_interior_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) : s inter f ⁻¹' interior t subseteq s inter interior (f ⁻¹' t) :=
  calc
    s inter f ⁻¹' interior t subseteq interior (s inter f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.isOpen_inter_preimage hs isOpen_interior)
    _ = s inter interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]

/--
theorem `continuousOn_of_locally_continuousOn` / 定理 `continuousOn_of_locally_continuousOn`

English:
theorem continuousOn_of_locally_continuousOn
  proof: by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this

中文:
定理 continuousOn_of_locally_continuousOn
  证明: by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_restrict, open_t
-/
theorem continuousOn_of_locally_continuousOn
    (h : forall x in s, exists t, IsOpen t ∧ x in t ∧ ContinuousOn f (s inter t)) : ContinuousOn f s := by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this

/--
theorem `continuousOn_to_generateFrom_iff` / 定理 `continuousOn_to_generateFrom_iff`

English:
theorem continuousOn_to_generateFrom_iff
  given: {β : Type*} {T : Set (Set β)} {f : α -> β}
  proof: forall₂_congr fun x _ => by
    delta ContinuousWithinAt
    simp only [TopologicalSpace.nhds_generateFrom, tendsto_iInf, tendsto_principal, mem_ofPred_eq,
      and_imp]
    exact forall_congr' fun t => forall_comm

中文:
定理 continuousOn_to_generateFrom_iff
  条件: {β : 类型} {T : 集合 (集合 β)} {f : α -> β}
  证明: forall₂_congr fun x _ => by
    delta ContinuousWithinAt
    simp only [TopologicalSpace.nhds_generateFrom, tendsto_iInf, tendsto_principal, mem_ofPred_eq,
      and_imp]
    exact forall_congr' fun t => forall_comm

Depends on / 依赖: ContinuousWithinAt, TopologicalSpace, TopologicalSpace.nhds_generateFrom, and_imp, forall_comm, forall_congr, mem_ofPred_eq, nhds_generateFrom, tendsto_iInf, tendsto_principal
-/
theorem continuousOn_to_generateFrom_iff {β : Type*} {T : Set (Set β)} {f : α -> β} :
    @ContinuousOn α β _ (.generateFrom T) f s ↔ forall x in s, forall t in T, f x in t -> f ⁻¹' t in 𝓝[s] x :=
  forall₂_congr fun x _ => by
    delta ContinuousWithinAt
    simp only [TopologicalSpace.nhds_generateFrom, tendsto_iInf, tendsto_principal, mem_ofPred_eq,
      and_imp]
    exact forall_congr' fun t => forall_comm

/--
theorem `continuousOn_isOpen_of_generateFrom` / 定理 `continuousOn_isOpen_of_generateFrom`

English:
theorem continuousOn_isOpen_of_generateFrom
  statement: {β : Type*} {s : Set α} {T : Set (Set β)} {f : α -> β}
  proof: continuousOn_to_generateFrom_iff.2 fun _x hx t ht hxt => mem_nhdsWithin.2
    ⟨_, h t ht, ⟨hx, hxt⟩, fun _y hy => hy.1.2⟩

中文:
定理 continuousOn_isOpen_of_generateFrom
  结论: {β : 类型} {s : 集合 α} {T : 集合 (集合 β)} {f : α -> β}
  证明: continuousOn_to_generateFrom_iff.2 fun _x hx t ht hxt => mem_nhdsWithin.2
    ⟨_, h t ht, ⟨hx, hxt⟩, fun _y hy => hy.1.2⟩

Depends on / 依赖: continuousOn_to_generateFrom_iff, mem_nhdsWithin
-/
theorem continuousOn_isOpen_of_generateFrom {β : Type*} {s : Set α} {T : Set (Set β)} {f : α -> β}
    (h : forall t in T, IsOpen (s inter f ⁻¹' t)) :
    @ContinuousOn α β _ (.generateFrom T) f s :=
  continuousOn_to_generateFrom_iff.2 fun _x hx t ht hxt => mem_nhdsWithin.2
    ⟨_, h t ht, ⟨hx, hxt⟩, fun _y hy => hy.1.2⟩


/--
theorem `ContinuousWithinAt.mono` / 定理 `ContinuousWithinAt.mono`

English:
theorem ContinuousWithinAt.mono
  statement: (h : ContinuousWithinAt f t x)
  proof: h.mono_left (nhdsWithin_mono x hs)

中文:
定理 ContinuousWithinAt.mono
  结论: (h : ContinuousWithinAt f t x)
  证明: h.mono_left (nhdsWithin_mono x hs)

Depends on / 依赖: h.mono_left, mono_left, nhdsWithin_mono
-/
theorem ContinuousWithinAt.mono (h : ContinuousWithinAt f t x)
    (hs : s subseteq t) : ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_mono x hs)

/--
theorem `ContinuousWithinAt.mono_of_mem_nhdsWithin` / 定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`

English:
theorem ContinuousWithinAt.mono_of_mem_nhdsWithin
  given: (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x)
  proof: h.mono_left (nhdsWithin_le_of_mem hs)

中文:
定理 ContinuousWithinAt.mono_of_mem_nhdsWithin
  条件: (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x)
  证明: h.mono_left (nhdsWithin_le_of_mem hs)

Depends on / 依赖: h.mono_left, mono_left, nhdsWithin_le_of_mem
-/
theorem ContinuousWithinAt.mono_of_mem_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) :
    ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_le_of_mem hs)

/--
theorem `continuousWithinAt_congr_set` / 定理 `continuousWithinAt_congr_set`

English:
theorem continuousWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq.mpr h]

中文:
定理 continuousWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq.mpr h]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_eq_iff_eventuallyEq.mpr
-/
theorem continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq.mpr h]

/--
theorem `ContinuousWithinAt.congr_set` / 定理 `ContinuousWithinAt.congr_set`

English:
theorem ContinuousWithinAt.congr_set
  given: (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x] t)
  proof: (continuousWithinAt_congr_set h).1 hf

中文:
定理 ContinuousWithinAt.congr_set
  条件: (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x] t)
  证明: (continuousWithinAt_congr_set h).1 hf

Depends on / 依赖: continuousWithinAt_congr_set
-/
theorem ContinuousWithinAt.congr_set (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f t x :=
  (continuousWithinAt_congr_set h).1 hf

/--
theorem `continuousWithinAt_inter'` / 定理 `continuousWithinAt_inter'`

English:
theorem continuousWithinAt_inter'
  given: (h : t in 𝓝[s] x)
  proof: by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]

中文:
定理 continuousWithinAt_inter'
  条件: (h : t in 𝓝[s] x)
  证明: by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_restrict
-/
theorem continuousWithinAt_inter' (h : t in 𝓝[s] x) :
    ContinuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]

/--
theorem `continuousWithinAt_inter` / 定理 `continuousWithinAt_inter`

English:
theorem continuousWithinAt_inter
  given: (h : t in 𝓝 x)
  proof: by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]

中文:
定理 continuousWithinAt_inter
  条件: (h : t in 𝓝 x)
  证明: by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_restrict
-/
theorem continuousWithinAt_inter (h : t in 𝓝 x) :
    ContinuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]

/--
theorem `continuousWithinAt_union` / 定理 `continuousWithinAt_union`

English:
theorem continuousWithinAt_union
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]

中文:
定理 continuousWithinAt_union
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_union, tendsto_sup
-/
theorem continuousWithinAt_union :
    ContinuousWithinAt f (s union t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]

/--
theorem `ContinuousWithinAt.union` / 定理 `ContinuousWithinAt.union`

English:
theorem ContinuousWithinAt.union
  given: (hs : ContinuousWithinAt f s x) (ht : ContinuousWithinAt f t x)
  proof: continuousWithinAt_union.2 ⟨hs, ht⟩

@[simp]

中文:
定理 ContinuousWithinAt.union
  条件: (hs : ContinuousWithinAt f s x) (ht : ContinuousWithinAt f t x)
  证明: continuousWithinAt_union.2 ⟨hs, ht⟩

@[simp]

Depends on / 依赖: continuousWithinAt_union
-/
theorem ContinuousWithinAt.union (hs : ContinuousWithinAt f s x) (ht : ContinuousWithinAt f t x) :
    ContinuousWithinAt f (s union t) x :=
  continuousWithinAt_union.2 ⟨hs, ht⟩

@[simp]
/--
theorem `continuousWithinAt_singleton` / 定理 `continuousWithinAt_singleton`

English:
theorem continuousWithinAt_singleton
  statement: ContinuousWithinAt f {x} x
  proof: by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]

@[simp]

中文:
定理 continuousWithinAt_singleton
  结论: ContinuousWithinAt f {x} x
  证明: by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]

@[simp]

Depends on / 依赖: ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds
-/
theorem continuousWithinAt_singleton : ContinuousWithinAt f {x} x := by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]

@[simp]
/--
theorem `continuousWithinAt_insert_self` / 定理 `continuousWithinAt_insert_self`

English:
theorem continuousWithinAt_insert_self
  proof: by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton, true_and]

protected alias ⟨_, ContinuousWithinAt.insert⟩ := continuousWithinAt_insert_self

中文:
定理 continuousWithinAt_insert_self
  证明: by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton, true_and]

protected alias ⟨_, ContinuousWithinAt.insert⟩ := continuousWithinAt_insert_self

Depends on / 依赖: continuousWithinAt_singleton, continuousWithinAt_union, singleton_union, true_and
-/
theorem continuousWithinAt_insert_self :
    ContinuousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x := by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton, true_and]

protected alias ⟨_, ContinuousWithinAt.insert⟩ := continuousWithinAt_insert_self

/--
theorem `ContinuousWithinAt.sdiff_iff` / 定理 `ContinuousWithinAt.sdiff_iff`

English:
theorem ContinuousWithinAt.sdiff_iff
  proof: ⟨fun h => (h.union ht).mono by simp only [sdiff_union_self, subset_union_left], fun h =>
    h.mono sdiff_subset⟩

中文:
定理 ContinuousWithinAt.sdiff_iff
  证明: ⟨fun h => (h.union ht).mono by simp only [sdiff_union_self, subset_union_left], fun h =>
    h.mono sdiff_subset⟩

Depends on / 依赖: h.mono, h.union, sdiff_subset, sdiff_union_self, subset_union_left
-/
theorem ContinuousWithinAt.sdiff_iff
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x :=
⟨fun h => (h.union ht).mono by simp only [sdiff_union_self, subset_union_left], fun h =>
    h.mono sdiff_subset⟩

/-- See also `continuousWithinAt_sdiff_singleton` for the case of `s \ {y}`, but
requiring `T1Space α`. -/
@[simp]
/--
theorem `continuousWithinAt_sdiff_self` / 定理 `continuousWithinAt_sdiff_self`

English:
theorem continuousWithinAt_sdiff_self
  proof: continuousWithinAt_singleton.sdiff_iff

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_self := continuousWithinAt_sdiff_self

中文:
定理 continuousWithinAt_sdiff_self
  证明: continuousWithinAt_singleton.sdiff_iff

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_self := continuousWithinAt_sdiff_self

Depends on / 依赖: continuousWithinAt_singleton, continuousWithinAt_singleton.sdiff_iff, sdiff_iff
-/
theorem continuousWithinAt_sdiff_self :
    ContinuousWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_singleton.sdiff_iff

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_self := continuousWithinAt_sdiff_self

/--
lemma `continuousWithinAt_of_not_accPt` / 引理 `continuousWithinAt_of_not_accPt`

English:
lemma continuousWithinAt_of_not_accPt
  given: (h : ¬AccPt x (𝓟 s))
  statement: ContinuousWithinAt f s x
  proof: by
  rw [← continuousWithinAt_sdiff_self]
  simp_all [ContinuousWithinAt, AccPt, ← nhdsWithin_inter', Set.sdiff_eq, Set.inter_comm]

@[simp]

中文:
引理 continuousWithinAt_of_not_accPt
  条件: (h : ¬聚点 x (𝓟 s))
  结论: ContinuousWithinAt f s x
  证明: by
  rw [← continuousWithinAt_sdiff_self]
  simp_all [ContinuousWithinAt, AccPt, ← nhdsWithin_inter', Set.sdiff_eq, Set.inter_comm]

@[simp]

Depends on / 依赖: ContinuousWithinAt, Set.inter_comm, Set.sdiff_eq, continuousWithinAt_sdiff_self, inter_comm, nhdsWithin_inter, sdiff_eq
-/
lemma continuousWithinAt_of_not_accPt (h : ¬AccPt x (𝓟 s)) : ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_sdiff_self]
  simp_all [ContinuousWithinAt, AccPt, ← nhdsWithin_inter', Set.sdiff_eq, Set.inter_comm]

@[simp]
/--
theorem `continuousWithinAt_compl_self` / 定理 `continuousWithinAt_compl_self`

English:
theorem continuousWithinAt_compl_self
  proof: by
  rw [compl_eq_univ_sdiff]; rw [continuousWithinAt_sdiff_self]; rw [continuousWithinAt_univ]

中文:
定理 continuousWithinAt_compl_self
  证明: by
  rw [compl_eq_univ_sdiff]; rw [continuousWithinAt_sdiff_self]; rw [continuousWithinAt_univ]

Depends on / 依赖: compl_eq_univ_sdiff, continuousWithinAt_sdiff_self, continuousWithinAt_univ
-/
theorem continuousWithinAt_compl_self :
    ContinuousWithinAt f {x}ᶜ x ↔ ContinuousAt f x := by
  rw [compl_eq_univ_sdiff]; rw [continuousWithinAt_sdiff_self]; rw [continuousWithinAt_univ]

/--
lemma `continuousAt_of_not_accPt` / 引理 `continuousAt_of_not_accPt`

English:
lemma continuousAt_of_not_accPt
  given: (h : ¬AccPt x (𝓟 {x}ᶜ))
  statement: ContinuousAt f x
  proof: by
  rw [← continuousWithinAt_compl_self]
  exact continuousWithinAt_of_not_accPt h

中文:
引理 continuousAt_of_not_accPt
  条件: (h : ¬聚点 x (𝓟 {x}ᶜ))
  结论: ContinuousAt f x
  证明: by
  rw [← continuousWithinAt_compl_self]
  exact continuousWithinAt_of_not_accPt h

Depends on / 依赖: continuousWithinAt_compl_self, continuousWithinAt_of_not_accPt
-/
lemma continuousAt_of_not_accPt (h : ¬AccPt x (𝓟 {x}ᶜ)) : ContinuousAt f x := by
  rw [← continuousWithinAt_compl_self]
  exact continuousWithinAt_of_not_accPt h

/--
lemma `continuousAt_of_not_accPt_top` / 引理 `continuousAt_of_not_accPt_top`

English:
lemma continuousAt_of_not_accPt_top
  given: (h : ¬AccPt x ⊤)
  statement: ContinuousAt f x
  proof: continuousAt_of_not_accPt fun hh => h AccPt.mono hh (by simp)

中文:
引理 continuousAt_of_not_accPt_top
  条件: (h : ¬聚点 x ⊤)
  结论: ContinuousAt f x
  证明: continuousAt_of_not_accPt fun hh => h AccPt.mono hh (by simp)

Depends on / 依赖: AccPt.mono, continuousAt_of_not_accPt
-/
lemma continuousAt_of_not_accPt_top (h : ¬AccPt x ⊤) : ContinuousAt f x :=
continuousAt_of_not_accPt fun hh => h AccPt.mono hh (by simp)

/--
theorem `ContinuousOn.mono` / 定理 `ContinuousOn.mono`

English:
theorem ContinuousOn.mono
  given: (hf : ContinuousOn f s) (h : t subseteq s)
  proof: fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)

中文:
定理 ContinuousOn.mono
  条件: (hf : ContinuousOn f s) (h : t subseteq s)
  证明: fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)

Depends on / 依赖: mono_left, nhdsWithin_mono
-/
theorem ContinuousOn.mono (hf : ContinuousOn f s) (h : t subseteq s) :
    ContinuousOn f t := fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)

/--
theorem `antitone_continuousOn` / 定理 `antitone_continuousOn`

English:
theorem antitone_continuousOn
  given: {f : α -> β}
  statement: Antitone (ContinuousOn f)
  proof: fun _s _t hst hf =>
  hf.mono hst

中文:
定理 antitone_continuousOn
  条件: {f : α -> β}
  结论: 递减 (ContinuousOn f)
  证明: fun _s _t hst hf =>
  hf.mono hst
-/
theorem antitone_continuousOn {f : α -> β} : Antitone (ContinuousOn f) := fun _s _t hst hf =>
  hf.mono hst

/-!
## Relation between `ContinuousAt` and `ContinuousWithinAt`
-/

@[fun_prop]
/--
theorem `ContinuousAt.continuousWithinAt` / 定理 `ContinuousAt.continuousWithinAt`

English:
theorem ContinuousAt.continuousWithinAt
  given: (h : ContinuousAt f x)
  proof: ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)

中文:
定理 ContinuousAt.continuousWithinAt
  条件: (h : ContinuousAt f x)
  证明: ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.mono, continuousWithinAt_univ, subset_univ
-/
theorem ContinuousAt.continuousWithinAt (h : ContinuousAt f x) :
    ContinuousWithinAt f s x :=
  ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)

/--
theorem `continuousWithinAt_iff_continuousAt` / 定理 `continuousWithinAt_iff_continuousAt`

English:
theorem continuousWithinAt_iff_continuousAt
  given: (h : s in 𝓝 x)
  proof: by
  rw [← univ_inter s]; rw [continuousWithinAt_inter h]; rw [continuousWithinAt_univ]

中文:
定理 continuousWithinAt_iff_continuousAt
  条件: (h : s in 𝓝 x)
  证明: by
  rw [← univ_inter s]; rw [continuousWithinAt_inter h]; rw [continuousWithinAt_univ]

Depends on / 依赖: continuousWithinAt_inter, continuousWithinAt_univ, univ_inter
-/
theorem continuousWithinAt_iff_continuousAt (h : s in 𝓝 x) :
    ContinuousWithinAt f s x ↔ ContinuousAt f x := by
  rw [← univ_inter s]; rw [continuousWithinAt_inter h]; rw [continuousWithinAt_univ]

/--
theorem `ContinuousWithinAt.continuousAt` / 定理 `ContinuousWithinAt.continuousAt`

English:
theorem ContinuousWithinAt.continuousAt
  proof: (continuousWithinAt_iff_continuousAt hs).mp h

中文:
定理 ContinuousWithinAt.continuousAt
  证明: (continuousWithinAt_iff_continuousAt hs).mp h

Depends on / 依赖: continuousWithinAt_iff_continuousAt
-/
theorem ContinuousWithinAt.continuousAt
    (h : ContinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp h

/--
theorem `IsOpen.continuousOn_iff` / 定理 `IsOpen.continuousOn_iff`

English:
theorem IsOpen.continuousOn_iff
  given: (hs : IsOpen s)
  proof: forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds

中文:
定理 是开集.continuousOn_iff
  条件: (hs : 是开集 s)
  证明: forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds

Depends on / 依赖: continuousWithinAt_iff_continuousAt, hs.mem_nhds, mem_nhds
-/
theorem IsOpen.continuousOn_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ forall ⦃a⦄, a in s -> ContinuousAt f a :=
  forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds

/--
theorem `ContinuousOn.continuousAt` / 定理 `ContinuousOn.continuousAt`

English:
theorem ContinuousOn.continuousAt
  statement: (h : ContinuousOn f s)
  proof: (h x (mem_of_mem_nhds hx)).continuousAt hx

中文:
定理 ContinuousOn.continuousAt
  结论: (h : ContinuousOn f s)
  证明: (h x (mem_of_mem_nhds hx)).continuousAt hx

Depends on / 依赖: continuousAt, mem_of_mem_nhds
-/
theorem ContinuousOn.continuousAt (h : ContinuousOn f s)
    (hx : s in 𝓝 x) : ContinuousAt f x :=
  (h x (mem_of_mem_nhds hx)).continuousAt hx

/--
theorem `continuousOn_of_forall_continuousAt` / 定理 `continuousOn_of_forall_continuousAt`

English:
theorem continuousOn_of_forall_continuousAt
  given: (hcont : forall x in s, ContinuousAt f x)
  proof: fun x hx => (hcont x hx).continuousWithinAt

@[fun_prop]

中文:
定理 continuousOn_of_对任意_continuousAt
  条件: (hcont : 对任意 x in s, ContinuousAt f x)
  证明: fun x hx => (hcont x hx).continuousWithinAt

@[fun_prop]

Depends on / 依赖: continuousWithinAt
-/
theorem continuousOn_of_forall_continuousAt (hcont : forall x in s, ContinuousAt f x) :
    ContinuousOn f s := fun x hx => (hcont x hx).continuousWithinAt

@[fun_prop]
/--
theorem `Continuous.continuousOn` / 定理 `Continuous.continuousOn`

English:
theorem Continuous.continuousOn
  given: (h : Continuous f)
  statement: ContinuousOn f s
  proof: by
  rw [← continuousOn_univ] at h
  exact h.mono (subset_univ _)

@[fun_prop]

中文:
定理 连续.continuousOn
  条件: (h : 连续 f)
  结论: ContinuousOn f s
  证明: by
  rw [← continuousOn_univ] at h
  exact h.mono (subset_univ _)

@[fun_prop]

Depends on / 依赖: continuousOn_univ, h.mono, subset_univ
-/
theorem Continuous.continuousOn (h : Continuous f) : ContinuousOn f s := by
  rw [← continuousOn_univ] at h
  exact h.mono (subset_univ _)

@[fun_prop]
/--
theorem `Continuous.continuousWithinAt` / 定理 `Continuous.continuousWithinAt`

English:
theorem Continuous.continuousWithinAt
  given: (h : Continuous f)
  proof: h.continuousAt.continuousWithinAt

中文:
定理 连续.continuousWithinAt
  条件: (h : 连续 f)
  证明: h.continuousAt.continuousWithinAt

Depends on / 依赖: continuousAt, continuousWithinAt, h.continuousAt.continuousWithinAt
-/
theorem Continuous.continuousWithinAt (h : Continuous f) :
    ContinuousWithinAt f s x :=
  h.continuousAt.continuousWithinAt



/--
theorem `ContinuousOn.congr_mono` / 定理 `ContinuousOn.congr_mono`

English:
theorem ContinuousOn.congr_mono
  given: (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ subseteq s)
  proof: by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventuallyEq_nhdsWithin.symm

中文:
定理 ContinuousOn.congr_mono
  条件: (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ subseteq s)
  证明: by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventuallyEq_nhdsWithin.symm

Depends on / 依赖: A.congr, ContinuousWithinAt, eventuallyEq_nhdsWithin, eventuallyEq_nhdsWithin.symm
-/
theorem ContinuousOn.congr_mono (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ subseteq s) :
    ContinuousOn g s₁ := by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventuallyEq_nhdsWithin.symm

/--
theorem `ContinuousOn.congr` / 定理 `ContinuousOn.congr`

English:
theorem ContinuousOn.congr
  given: (h : ContinuousOn f s) (h' : EqOn g f s)
  proof: h.congr_mono h' (Subset.refl _)

中文:
定理 ContinuousOn.congr
  条件: (h : ContinuousOn f s) (h' : EqOn g f s)
  证明: h.congr_mono h' (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, congr_mono, h.congr_mono
-/
theorem ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn g f s) :
    ContinuousOn g s :=
  h.congr_mono h' (Subset.refl _)

/--
theorem `continuousOn_congr` / 定理 `continuousOn_congr`

English:
theorem continuousOn_congr
  given: (h' : EqOn g f s)
  proof: ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩

中文:
定理 continuousOn_congr
  条件: (h' : EqOn g f s)
  证明: ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, h.congr
-/
theorem continuousOn_congr (h' : EqOn g f s) :
    ContinuousOn g s ↔ ContinuousOn f s :=
  ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩

/--
theorem `Filter.EventuallyEq.congr_continuousWithinAt` / 定理 `Filter.EventuallyEq.congr_continuousWithinAt`

English:
theorem Filter.EventuallyEq.congr_continuousWithinAt
  given: (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x)
  proof: by
  rw [ContinuousWithinAt]; rw [hx]; rw [tendsto_congr' h]; rw [ContinuousWithinAt]

中文:
定理 滤子.EventuallyEq.congr_continuousWithinAt
  条件: (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x)
  证明: by
  rw [ContinuousWithinAt]; rw [hx]; rw [tendsto_congr' h]; rw [ContinuousWithinAt]

Depends on / 依赖: ContinuousWithinAt, tendsto_congr
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x := by
  rw [ContinuousWithinAt]; rw [hx]; rw [tendsto_congr' h]; rw [ContinuousWithinAt]

/--
theorem `ContinuousWithinAt.congr_of_eventuallyEq` / 定理 `ContinuousWithinAt.congr_of_eventuallyEq`

English:
theorem ContinuousWithinAt.congr_of_eventuallyEq
  proof: (h₁.congr_continuousWithinAt hx).2 h

中文:
定理 ContinuousWithinAt.congr_of_eventuallyEq
  证明: (h₁.congr_continuousWithinAt hx).2 h

Depends on / 依赖: congr_continuousWithinAt
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    ContinuousWithinAt g s x :=
  (h₁.congr_continuousWithinAt hx).2 h

/--
theorem `ContinuousWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `ContinuousWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem ContinuousWithinAt.congr_of_eventuallyEq_of_mem
  proof: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

中文:
定理 ContinuousWithinAt.congr_of_eventuallyEq_of_mem
  证明: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_of_mem_nhdsWithin
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq_of_mem
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : x in s) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

/--
theorem `Filter.EventuallyEq.congr_continuousWithinAt_of_mem` / 定理 `Filter.EventuallyEq.congr_continuousWithinAt_of_mem`

English:
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_mem
  given: (h : f =ᶠ[𝓝[s] x] g) (hx : x in s)
  proof: ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h.symm hx,
    fun h' => h'.congr_of_eventuallyEq_of_mem h hx⟩

中文:
定理 滤子.EventuallyEq.congr_continuousWithinAt_of_mem
  条件: (h : f =ᶠ[𝓝[s] x] g) (hx : x in s)
  证明: ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h.symm hx,
    fun h' => h'.congr_of_eventuallyEq_of_mem h hx⟩

Depends on / 依赖: congr_of_eventuallyEq_of_mem, h.symm
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_mem (h : f =ᶠ[𝓝[s] x] g) (hx : x in s) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' => h'.congr_of_eventuallyEq_of_mem h.symm hx,
    fun h' => h'.congr_of_eventuallyEq_of_mem h hx⟩

/--
theorem `ContinuousWithinAt.congr_of_eventuallyEq_insert` / 定理 `ContinuousWithinAt.congr_of_eventuallyEq_insert`

English:
theorem ContinuousWithinAt.congr_of_eventuallyEq_insert
  proof: h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)
    (mem_of_mem_nhdsWithin (mem_insert _ _) h₁ :)

中文:
定理 ContinuousWithinAt.congr_of_eventuallyEq_insert
  证明: h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)
    (mem_of_mem_nhdsWithin (mem_insert _ _) h₁ :)

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_insert, mem_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq_insert
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[insert x s] x] f) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)
    (mem_of_mem_nhdsWithin (mem_insert _ _) h₁ :)

/--
theorem `Filter.EventuallyEq.congr_continuousWithinAt_of_insert` / 定理 `Filter.EventuallyEq.congr_continuousWithinAt_of_insert`

English:
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_insert
  given: (h : f =ᶠ[𝓝[insert x s] x] g)
  proof: ⟨fun h' => h'.congr_of_eventuallyEq_insert h.symm,
    fun h' => h'.congr_of_eventuallyEq_insert h⟩

中文:
定理 滤子.EventuallyEq.congr_continuousWithinAt_of_insert
  条件: (h : f =ᶠ[𝓝[insert x s] x] g)
  证明: ⟨fun h' => h'.congr_of_eventuallyEq_insert h.symm,
    fun h' => h'.congr_of_eventuallyEq_insert h⟩

Depends on / 依赖: congr_of_eventuallyEq_insert, h.symm
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_insert (h : f =ᶠ[𝓝[insert x s] x] g) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' => h'.congr_of_eventuallyEq_insert h.symm,
    fun h' => h'.congr_of_eventuallyEq_insert h⟩

/--
theorem `ContinuousWithinAt.congr` / 定理 `ContinuousWithinAt.congr`

English:
theorem ContinuousWithinAt.congr
  statement: (h : ContinuousWithinAt f s x)
  proof: h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx

中文:
定理 ContinuousWithinAt.congr
  结论: (h : ContinuousWithinAt f s x)
  证明: h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_of_superset, self_mem_nhdsWithin
-/
theorem ContinuousWithinAt.congr (h : ContinuousWithinAt f s x)
    (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx

/--
theorem `continuousWithinAt_congr` / 定理 `continuousWithinAt_congr`

English:
theorem continuousWithinAt_congr
  given: (h₁ : forall y in s, g y = f y) (hx : g x = f x)
  proof: ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

中文:
定理 continuousWithinAt_congr
  条件: (h₁ : 对任意 y in s, g y = f y) (hx : g x = f x)
  证明: ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

Depends on / 依赖: hx.symm
-/
theorem continuousWithinAt_congr (h₁ : forall y in s, g y = f y) (hx : g x = f x) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

/--
theorem `ContinuousWithinAt.congr_of_mem` / 定理 `ContinuousWithinAt.congr_of_mem`

English:
theorem ContinuousWithinAt.congr_of_mem
  statement: (h : ContinuousWithinAt f s x)
  proof: h.congr h₁ (h₁ x hx)

中文:
定理 ContinuousWithinAt.congr_of_mem
  结论: (h : ContinuousWithinAt f s x)
  证明: h.congr h₁ (h₁ x hx)

Depends on / 依赖: h.congr
-/
theorem ContinuousWithinAt.congr_of_mem (h : ContinuousWithinAt f s x)
    (h₁ : forall y in s, g y = f y) (hx : x in s) : ContinuousWithinAt g s x :=
  h.congr h₁ (h₁ x hx)

/--
theorem `continuousWithinAt_congr_of_mem` / 定理 `continuousWithinAt_congr_of_mem`

English:
theorem continuousWithinAt_congr_of_mem
  given: (h₁ : forall y in s, g y = f y) (hx : x in s)
  proof: continuousWithinAt_congr h₁ (h₁ x hx)

中文:
定理 continuousWithinAt_congr_of_mem
  条件: (h₁ : 对任意 y in s, g y = f y) (hx : x in s)
  证明: continuousWithinAt_congr h₁ (h₁ x hx)

Depends on / 依赖: continuousWithinAt_congr
-/
theorem continuousWithinAt_congr_of_mem (h₁ : forall y in s, g y = f y) (hx : x in s) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr h₁ (h₁ x hx)

/--
theorem `ContinuousWithinAt.congr_of_insert` / 定理 `ContinuousWithinAt.congr_of_insert`

English:
theorem ContinuousWithinAt.congr_of_insert
  statement: (h : ContinuousWithinAt f s x)
  proof: h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

中文:
定理 ContinuousWithinAt.congr_of_insert
  结论: (h : ContinuousWithinAt f s x)
  证明: h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

Depends on / 依赖: h.congr, mem_insert, mem_insert_of_mem
-/
theorem ContinuousWithinAt.congr_of_insert (h : ContinuousWithinAt f s x)
    (h₁ : forall y in insert x s, g y = f y) : ContinuousWithinAt g s x :=
  h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

/--
theorem `continuousWithinAt_congr_of_insert` / 定理 `continuousWithinAt_congr_of_insert`

English:
theorem continuousWithinAt_congr_of_insert
  proof: continuousWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

中文:
定理 continuousWithinAt_congr_of_insert
  证明: continuousWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

Depends on / 依赖: continuousWithinAt_congr, mem_insert, mem_insert_of_mem
-/
theorem continuousWithinAt_congr_of_insert
    (h₁ : forall y in insert x s, g y = f y) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

/--
theorem `ContinuousWithinAt.congr_mono` / 定理 `ContinuousWithinAt.congr_mono`

English:
theorem ContinuousWithinAt.congr_mono
  proof: (h.mono h₁).congr h' hx

中文:
定理 ContinuousWithinAt.congr_mono
  证明: (h.mono h₁).congr h' hx

Depends on / 依赖: h.mono
-/
theorem ContinuousWithinAt.congr_mono
    (h : ContinuousWithinAt f s x) (h' : EqOn g f s₁) (h₁ : s₁ subseteq s) (hx : g x = f x) :
    ContinuousWithinAt g s₁ x :=
  (h.mono h₁).congr h' hx

/--
theorem `ContinuousAt.congr_of_eventuallyEq` / 定理 `ContinuousAt.congr_of_eventuallyEq`

English:
theorem ContinuousAt.congr_of_eventuallyEq
  given: (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f)
  proof: congr h (EventuallyEq.symm hg)

中文:
定理 ContinuousAt.congr_of_eventuallyEq
  条件: (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f)
  证明: congr h (EventuallyEq.symm hg)

Depends on / 依赖: EventuallyEq, EventuallyEq.symm
-/
theorem ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) :
    ContinuousAt g x :=
  congr h (EventuallyEq.symm hg)


/--
theorem `ContinuousWithinAt.comp` / 定理 `ContinuousWithinAt.comp`

English:
theorem ContinuousWithinAt.comp
  statement: {g : β -> γ} {t : Set β}
  proof: hg.tendsto.comp (hf.tendsto_nhdsWithin h)

中文:
定理 ContinuousWithinAt.comp
  结论: {g : β -> γ} {t : 集合 β}
  证明: hg.tendsto.comp (hf.tendsto_nhdsWithin h)

Depends on / 依赖: hf.tendsto_nhdsWithin, hg.tendsto.comp, tendsto, tendsto_nhdsWithin
-/
theorem ContinuousWithinAt.comp {g : β -> γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (hf.tendsto_nhdsWithin h)

/--
theorem `ContinuousWithinAt.comp_of_eq` / 定理 `ContinuousWithinAt.comp_of_eq`

English:
theorem ContinuousWithinAt.comp_of_eq
  statement: {g : β -> γ} {t : Set β} {y : β}
  proof: by
  subst hy; exact hg.comp hf h

中文:
定理 ContinuousWithinAt.comp_of_eq
  结论: {g : β -> γ} {t : 集合 β} {y : β}
  证明: by
  subst hy; exact hg.comp hf h

Depends on / 依赖: hg.comp
-/
theorem ContinuousWithinAt.comp_of_eq {g : β -> γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t)
    (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp hf h

/--
theorem `ContinuousWithinAt.comp_inter` / 定理 `ContinuousWithinAt.comp_inter`

English:
theorem ContinuousWithinAt.comp_inter
  statement: {g : β -> γ} {t : Set β}
  proof: hg.comp (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContinuousWithinAt.comp_inter
  结论: {g : β -> γ} {t : 集合 β}
  证明: hg.comp (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContinuousWithinAt.comp_inter {g : β -> γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (g ∘ f) (s inter f ⁻¹' t) x :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/--
theorem `ContinuousWithinAt.comp_inter_of_eq` / 定理 `ContinuousWithinAt.comp_inter_of_eq`

English:
theorem ContinuousWithinAt.comp_inter_of_eq
  statement: {g : β -> γ} {t : Set β} {y : β}
  proof: by
  subst hy; exact hg.comp_inter hf

中文:
定理 ContinuousWithinAt.comp_inter_of_eq
  结论: {g : β -> γ} {t : 集合 β} {y : β}
  证明: by
  subst hy; exact hg.comp_inter hf

Depends on / 依赖: comp_inter, hg.comp_inter
-/
theorem ContinuousWithinAt.comp_inter_of_eq {g : β -> γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) (s inter f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter hf

/--
theorem `ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin` / 定理 `ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin`

English:
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin
  statement: {g : β -> γ} {t : Set β}
  proof: hg.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf h)

中文:
定理 ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin
  结论: {g : β -> γ} {t : 集合 β}
  证明: hg.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf h)

Depends on / 依赖: hg.tendsto.comp, tendsto, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin {g : β -> γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t in 𝓝[s] x) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf h)

/--
theorem `ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq` / 定理 `ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq`

English:
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  statement: {g : β -> γ} {t : Set β} {y : β}
  proof: by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin hf h

中文:
定理 ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  结论: {g : β -> γ} {t : 集合 β} {y : β}
  证明: by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin hf h

Depends on / 依赖: comp_of_preimage_mem_nhdsWithin, hg.comp_of_preimage_mem_nhdsWithin
-/
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {g : β -> γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t in 𝓝[s] x)
    (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin hf h

/--
theorem `ContinuousWithinAt.comp_of_mem_nhdsWithin_image` / 定理 `ContinuousWithinAt.comp_of_mem_nhdsWithin_image`

English:
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image
  statement: {g : β -> γ} {t : Set β}
  proof: (hg.mono_of_mem_nhdsWithin hs).comp hf (mapsTo_image f s)

中文:
定理 ContinuousWithinAt.comp_of_mem_nhdsWithin_image
  结论: {g : β -> γ} {t : 集合 β}
  证明: (hg.mono_of_mem_nhdsWithin hs).comp hf (mapsTo_image f s)

Depends on / 依赖: hg.mono_of_mem_nhdsWithin, mapsTo_image, mono_of_mem_nhdsWithin
-/
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image {g : β -> γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x)
    (hs : t in 𝓝[f '' s] f x) : ContinuousWithinAt (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp hf (mapsTo_image f s)

/--
theorem `ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq` / 定理 `ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq`

English:
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq
  statement: {g : β -> γ} {t : Set β} {y : β}
  proof: by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image hf hs

中文:
定理 ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq
  结论: {g : β -> γ} {t : 集合 β} {y : β}
  证明: by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image hf hs

Depends on / 依赖: comp_of_mem_nhdsWithin_image, hg.comp_of_mem_nhdsWithin_image
-/
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq {g : β -> γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x)
    (hs : t in 𝓝[f '' s] y) (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image hf hs

/--
theorem `ContinuousAt.comp_continuousWithinAt` / 定理 `ContinuousAt.comp_continuousWithinAt`

English:
theorem ContinuousAt.comp_continuousWithinAt
  statement: {g : β -> γ}
  proof: hg.continuousWithinAt.comp hf (mapsTo_univ _ _)

中文:
定理 ContinuousAt.comp_continuousWithinAt
  结论: {g : β -> γ}
  证明: hg.continuousWithinAt.comp hf (mapsTo_univ _ _)
-/
@[fun_prop] theorem ContinuousAt.comp_continuousWithinAt {g : β -> γ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) s x :=
  hg.continuousWithinAt.comp hf (mapsTo_univ _ _)

/--
theorem `ContinuousAt.comp_continuousWithinAt_of_eq` / 定理 `ContinuousAt.comp_continuousWithinAt_of_eq`

English:
theorem ContinuousAt.comp_continuousWithinAt_of_eq
  statement: {g : β -> γ} {y : β}
  proof: by
  subst hy; exact hg.comp_continuousWithinAt hf

中文:
定理 ContinuousAt.comp_continuousWithinAt_of_eq
  结论: {g : β -> γ} {y : β}
  证明: by
  subst hy; exact hg.comp_continuousWithinAt hf

Depends on / 依赖: comp_continuousWithinAt, hg.comp_continuousWithinAt
-/
theorem ContinuousAt.comp_continuousWithinAt_of_eq {g : β -> γ} {y : β}
    (hg : ContinuousAt g y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_continuousWithinAt hf

/--
theorem `ContinuousOn.comp` / 定理 `ContinuousOn.comp`

English:
theorem ContinuousOn.comp
  statement: {g : β -> γ} {t : Set β} (hg : ContinuousOn g t)
  proof: fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h

中文:
定理 ContinuousOn.comp
  结论: {g : β -> γ} {t : 集合 β} (hg : ContinuousOn g t)
  证明: fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h
-/
theorem ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s := fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h

/-- Variant of `ContinuousOn.comp` using the form `fun y ↦ g (f y)` instead of `g ∘ f`. -/
@[fun_prop]
/--
theorem `ContinuousOn.comp'` / 定理 `ContinuousOn.comp'`

English:
theorem ContinuousOn.comp'
  statement: {g : β -> γ} {f : α -> β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
  proof: ContinuousOn.comp hg hf h

@[fun_prop]

中文:
定理 ContinuousOn.comp'
  结论: {g : β -> γ} {f : α -> β} {s : 集合 α} {t : 集合 β} (hg : ContinuousOn g t)
  证明: ContinuousOn.comp hg hf h

@[fun_prop]

Depends on / 依赖: ContinuousOn, ContinuousOn.comp
-/
theorem ContinuousOn.comp' {g : β -> γ} {f : α -> β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : Set.MapsTo f s t) : ContinuousOn (fun x => g (f x)) s :=
  ContinuousOn.comp hg hf h

@[fun_prop]
/--
theorem `ContinuousOn.comp_inter` / 定理 `ContinuousOn.comp_inter`

English:
theorem ContinuousOn.comp_inter
  statement: {g : β -> γ} {t : Set β} (hg : ContinuousOn g t)
  proof: hg.comp (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContinuousOn.comp_inter
  结论: {g : β -> γ} {t : 集合 β} (hg : ContinuousOn g t)
  证明: hg.comp (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContinuousOn.comp_inter {g : β -> γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s inter f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/--
theorem `Continuous.comp_continuousOn` / 定理 `Continuous.comp_continuousOn`

English:
theorem Continuous.comp_continuousOn
  statement: {g : β -> γ} {f : α -> β} {s : Set α} (hg : Continuous g)
  proof: hg.continuousOn.comp hf (mapsTo_univ _ _)

中文:
定理 连续.comp_continuousOn
  结论: {g : β -> γ} {f : α -> β} {s : 集合 α} (hg : 连续 g)
  证明: hg.continuousOn.comp hf (mapsTo_univ _ _)

Depends on / 依赖: continuousOn, hg.continuousOn.comp, mapsTo_univ
-/
theorem Continuous.comp_continuousOn {g : β -> γ} {f : α -> β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) s :=
  hg.continuousOn.comp hf (mapsTo_univ _ _)

/-- Variant of `Continuous.comp_continuousOn` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`. -/
@[fun_prop]
/--
theorem `Continuous.comp_continuousOn'` / 定理 `Continuous.comp_continuousOn'`

English:
theorem Continuous.comp_continuousOn'
  statement: {g : β -> γ} {f : α -> β} {s : Set α} (hg : Continuous g)
  proof: hg.comp_continuousOn hf

中文:
定理 连续.comp_continuousOn'
  结论: {g : β -> γ} {f : α -> β} {s : 集合 α} (hg : 连续 g)
  证明: hg.comp_continuousOn hf

Depends on / 依赖: comp_continuousOn, hg.comp_continuousOn
-/
theorem Continuous.comp_continuousOn' {g : β -> γ} {f : α -> β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (fun x => g (f x)) s :=
  hg.comp_continuousOn hf

/--
theorem `ContinuousOn.comp_continuous` / 定理 `ContinuousOn.comp_continuous`

English:
theorem ContinuousOn.comp_continuous
  statement: {g : β -> γ} {f : α -> β} {s : Set β} (hg : ContinuousOn g s)
  proof: by
  rw [← continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x

中文:
定理 ContinuousOn.comp_continuous
  结论: {g : β -> γ} {f : α -> β} {s : 集合 β} (hg : ContinuousOn g s)
  证明: by
  rw [← continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x

Depends on / 依赖: continuousOn_univ, hg.comp
-/
theorem ContinuousOn.comp_continuous {g : β -> γ} {f : α -> β} {s : Set β} (hg : ContinuousOn g s)
    (hf : Continuous f) (hs : forall x, f x in s) : Continuous (g ∘ f) := by
  rw [← continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x

/--
theorem `ContinuousOn.image_comp_continuous` / 定理 `ContinuousOn.image_comp_continuous`

English:
theorem ContinuousOn.image_comp_continuous
  statement: {g : β -> γ} {f : α -> β} {s : Set α}
  proof: hg.comp hf.continuousOn (s.mapsTo_image f)

中文:
定理 ContinuousOn.image_comp_continuous
  结论: {g : β -> γ} {f : α -> β} {s : 集合 α}
  证明: hg.comp hf.continuousOn (s.mapsTo_image f)

Depends on / 依赖: continuousOn, hf.continuousOn, hg.comp, mapsTo_image, s.mapsTo_image
-/
theorem ContinuousOn.image_comp_continuous {g : β -> γ} {f : α -> β} {s : Set α}
    (hg : ContinuousOn g (f '' s)) (hf : Continuous f) : ContinuousOn (g ∘ f) s :=
  hg.comp hf.continuousOn (s.mapsTo_image f)

/--
theorem `ContinuousAt.comp₂_continuousWithinAt` / 定理 `ContinuousAt.comp₂_continuousWithinAt`

English:
theorem ContinuousAt.comp₂_continuousWithinAt
  statement: {f : β × γ -> δ} {g : α -> β} {h : α -> γ} {x : α}
  proof: ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)

中文:
定理 ContinuousAt.comp₂_continuousWithinAt
  结论: {f : β × γ -> δ} {g : α -> β} {h : α -> γ} {x : α}
  证明: ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_continuousWithinAt, comp_continuousWithinAt, hg.prodMk_nhds, prodMk_nhds
-/
theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ -> δ} {g : α -> β} {h : α -> γ} {x : α}
    {s : Set α} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousWithinAt g s x)
    (hh : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x => f (g x, h x)) s x :=
  ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)

/--
theorem `ContinuousAt.comp₂_continuousWithinAt_of_eq` / 定理 `ContinuousAt.comp₂_continuousWithinAt_of_eq`

English:
theorem ContinuousAt.comp₂_continuousWithinAt_of_eq
  statement: {f : β × γ -> δ} {g : α -> β}
  proof: by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh

中文:
定理 ContinuousAt.comp₂_continuousWithinAt_of_eq
  结论: {f : β × γ -> δ} {g : α -> β}
  证明: by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh

Depends on / 依赖: hf.comp
-/
theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ -> δ} {g : α -> β}
    {h : α -> γ} {x : α} {s : Set α} {y : β × γ} (hf : ContinuousAt f y)
    (hg : ContinuousWithinAt g s x) (hh : ContinuousWithinAt h s x) (e : (g x, h x) = y) :
    ContinuousWithinAt (fun x => f (g x, h x)) s x := by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh


/--
theorem `ContinuousWithinAt.mem_closure_image` / 定理 `ContinuousWithinAt.mem_closure_image`

English:
theorem ContinuousWithinAt.mem_closure_image
  proof: haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
mem_closure_of_tendsto h mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)

中文:
定理 ContinuousWithinAt.mem_closure_image
  证明: haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
mem_closure_of_tendsto h mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)

Depends on / 依赖: mem_closure_iff_nhdsWithin_neBot, mem_closure_of_tendsto, mem_of_superset, self_mem_nhdsWithin, subset_preimage_image
-/
theorem ContinuousWithinAt.mem_closure_image
    (h : ContinuousWithinAt f s x) (hx : x in closure s) : f x in closure (f '' s) :=
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
mem_closure_of_tendsto h mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)

/--
theorem `ContinuousWithinAt.mem_closure` / 定理 `ContinuousWithinAt.mem_closure`

English:
theorem ContinuousWithinAt.mem_closure
  statement: {t : Set β}
  proof: closure_mono (image_subset_iff.2 ht) (h.mem_closure_image hx)

中文:
定理 ContinuousWithinAt.mem_closure
  结论: {t : 集合 β}
  证明: closure_mono (image_subset_iff.2 ht) (h.mem_closure_image hx)

Depends on / 依赖: closure_mono, h.mem_closure_image, image_subset_iff, mem_closure_image
-/
theorem ContinuousWithinAt.mem_closure {t : Set β}
    (h : ContinuousWithinAt f s x) (hx : x in closure s) (ht : MapsTo f s t) : f x in closure t :=
  closure_mono (image_subset_iff.2 ht) (h.mem_closure_image hx)

/--
theorem `Set.MapsTo.closure_of_continuousWithinAt` / 定理 `Set.MapsTo.closure_of_continuousWithinAt`

English:
theorem Set.MapsTo.closure_of_continuousWithinAt
  statement: {t : Set β}
  proof: fun x hx => (hc x hx).mem_closure hx h

中文:
定理 集合.映射到.closure_of_continuousWithinAt
  结论: {t : 集合 β}
  证明: fun x hx => (hc x hx).mem_closure hx h

Depends on / 依赖: mem_closure
-/
theorem Set.MapsTo.closure_of_continuousWithinAt {t : Set β}
    (h : MapsTo f s t) (hc : forall x in closure s, ContinuousWithinAt f s x) :
    MapsTo f (closure s) (closure t) := fun x hx => (hc x hx).mem_closure hx h

/--
theorem `Set.MapsTo.closure_of_continuousOn` / 定理 `Set.MapsTo.closure_of_continuousOn`

English:
theorem Set.MapsTo.closure_of_continuousOn
  statement: {t : Set β} (h : MapsTo f s t)
  proof: h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure

中文:
定理 集合.映射到.closure_of_continuousOn
  结论: {t : 集合 β} (h : 映射到 f s t)
  证明: h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure

Depends on / 依赖: closure_of_continuousWithinAt, h.closure_of_continuousWithinAt, subset_closure
-/
theorem Set.MapsTo.closure_of_continuousOn {t : Set β} (h : MapsTo f s t)
    (hc : ContinuousOn f (closure s)) : MapsTo f (closure s) (closure t) :=
  h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure

/--
theorem `ContinuousWithinAt.image_closure` / 定理 `ContinuousWithinAt.image_closure`

English:
theorem ContinuousWithinAt.image_closure
  proof: ((mapsTo_image f s).closure_of_continuousWithinAt hf).image_subset

中文:
定理 ContinuousWithinAt.image_closure
  证明: ((mapsTo_image f s).closure_of_continuousWithinAt hf).image_subset

Depends on / 依赖: closure_of_continuousWithinAt, image_subset, mapsTo_image
-/
theorem ContinuousWithinAt.image_closure
    (hf : forall x in closure s, ContinuousWithinAt f s x) : f '' closure s subseteq closure (f '' s) :=
  ((mapsTo_image f s).closure_of_continuousWithinAt hf).image_subset

/--
theorem `ContinuousOn.image_closure` / 定理 `ContinuousOn.image_closure`

English:
theorem ContinuousOn.image_closure
  given: (hf : ContinuousOn f (closure s))
  proof: ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure

中文:
定理 ContinuousOn.image_closure
  条件: (hf : ContinuousOn f (closure s))
  证明: ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.image_closure, image_closure, subset_closure
-/
theorem ContinuousOn.image_closure (hf : ContinuousOn f (closure s)) :
    f '' closure s subseteq closure (f '' s) :=
  ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure


/--
theorem `ContinuousWithinAt.prodMk` / 定理 `ContinuousWithinAt.prodMk`

English:
theorem ContinuousWithinAt.prodMk
  statement: {f : α -> β} {g : α -> γ} {s : Set α} {x : α}
  proof: hf.prodMk_nhds hg

@[fun_prop]

中文:
定理 ContinuousWithinAt.prodMk
  结论: {f : α -> β} {g : α -> γ} {s : 集合 α} {x : α}
  证明: hf.prodMk_nhds hg

@[fun_prop]

Depends on / 依赖: hf.prodMk_nhds, prodMk_nhds
-/
theorem ContinuousWithinAt.prodMk {f : α -> β} {g : α -> γ} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prodMk_nhds hg

@[fun_prop]
/--
theorem `ContinuousOn.prodMk` / 定理 `ContinuousOn.prodMk`

English:
theorem ContinuousOn.prodMk
  statement: {f : α -> β} {g : α -> γ} {s : Set α} (hf : ContinuousOn f s)
  proof: fun x hx =>
  (hf x hx).prodMk (hg x hx)

中文:
定理 ContinuousOn.prodMk
  结论: {f : α -> β} {g : α -> γ} {s : 集合 α} (hf : ContinuousOn f s)
  证明: fun x hx =>
  (hf x hx).prodMk (hg x hx)
-/
theorem ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

/--
theorem `continuousOn_fst` / 定理 `continuousOn_fst`

English:
theorem continuousOn_fst
  given: {s : Set (α × β)}
  statement: ContinuousOn Prod.fst s
  proof: continuous_fst.continuousOn

中文:
定理 continuousOn_fst
  条件: {s : 集合 (α × β)}
  结论: ContinuousOn 积类型.fst s
  证明: continuous_fst.continuousOn

Depends on / 依赖: continuousOn, continuous_fst, continuous_fst.continuousOn
-/
theorem continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.continuousOn

/--
theorem `continuousWithinAt_fst` / 定理 `continuousWithinAt_fst`

English:
theorem continuousWithinAt_fst
  given: {s : Set (α × β)} {p : α × β}
  statement: ContinuousWithinAt Prod.fst s p
  proof: continuous_fst.continuousWithinAt

@[fun_prop]

中文:
定理 continuousWithinAt_fst
  条件: {s : 集合 (α × β)} {p : α × β}
  结论: ContinuousWithinAt 积类型.fst s p
  证明: continuous_fst.continuousWithinAt

@[fun_prop]

Depends on / 依赖: continuousWithinAt, continuous_fst, continuous_fst.continuousWithinAt
-/
theorem continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.continuousWithinAt

@[fun_prop]
/--
theorem `ContinuousOn.fst` / 定理 `ContinuousOn.fst`

English:
theorem ContinuousOn.fst
  given: {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s)
  proof: continuous_fst.comp_continuousOn hf

中文:
定理 ContinuousOn.fst
  条件: {f : α -> β × γ} {s : 集合 α} (hf : ContinuousOn f s)
  证明: continuous_fst.comp_continuousOn hf

Depends on / 依赖: comp_continuousOn, continuous_fst, continuous_fst.comp_continuousOn
-/
theorem ContinuousOn.fst {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuousOn hf

/--
theorem `ContinuousWithinAt.fst` / 定理 `ContinuousWithinAt.fst`

English:
theorem ContinuousWithinAt.fst
  given: {f : α -> β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  proof: continuousAt_fst.comp_continuousWithinAt h

中文:
定理 ContinuousWithinAt.fst
  条件: {f : α -> β × γ} {s : 集合 α} {a : α} (h : ContinuousWithinAt f s a)
  证明: continuousAt_fst.comp_continuousWithinAt h

Depends on / 依赖: comp_continuousWithinAt, continuousAt_fst, continuousAt_fst.comp_continuousWithinAt
-/
theorem ContinuousWithinAt.fst {f : α -> β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuousAt_fst.comp_continuousWithinAt h

/--
theorem `continuousOn_snd` / 定理 `continuousOn_snd`

English:
theorem continuousOn_snd
  given: {s : Set (α × β)}
  statement: ContinuousOn Prod.snd s
  proof: continuous_snd.continuousOn

中文:
定理 continuousOn_snd
  条件: {s : 集合 (α × β)}
  结论: ContinuousOn 积类型.snd s
  证明: continuous_snd.continuousOn

Depends on / 依赖: continuousOn, continuous_snd, continuous_snd.continuousOn
-/
theorem continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.continuousOn

/--
theorem `continuousWithinAt_snd` / 定理 `continuousWithinAt_snd`

English:
theorem continuousWithinAt_snd
  given: {s : Set (α × β)} {p : α × β}
  statement: ContinuousWithinAt Prod.snd s p
  proof: continuous_snd.continuousWithinAt

@[fun_prop]

中文:
定理 continuousWithinAt_snd
  条件: {s : 集合 (α × β)} {p : α × β}
  结论: ContinuousWithinAt 积类型.snd s p
  证明: continuous_snd.continuousWithinAt

@[fun_prop]

Depends on / 依赖: continuousWithinAt, continuous_snd, continuous_snd.continuousWithinAt
-/
theorem continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.continuousWithinAt

@[fun_prop]
/--
theorem `ContinuousOn.snd` / 定理 `ContinuousOn.snd`

English:
theorem ContinuousOn.snd
  given: {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s)
  proof: continuous_snd.comp_continuousOn hf

中文:
定理 ContinuousOn.snd
  条件: {f : α -> β × γ} {s : 集合 α} (hf : ContinuousOn f s)
  证明: continuous_snd.comp_continuousOn hf

Depends on / 依赖: comp_continuousOn, continuous_snd, continuous_snd.comp_continuousOn
-/
theorem ContinuousOn.snd {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuousOn hf

/--
theorem `ContinuousWithinAt.snd` / 定理 `ContinuousWithinAt.snd`

English:
theorem ContinuousWithinAt.snd
  given: {f : α -> β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  proof: continuousAt_snd.comp_continuousWithinAt h

中文:
定理 ContinuousWithinAt.snd
  条件: {f : α -> β × γ} {s : 集合 α} {a : α} (h : ContinuousWithinAt f s a)
  证明: continuousAt_snd.comp_continuousWithinAt h

Depends on / 依赖: comp_continuousWithinAt, continuousAt_snd, continuousAt_snd.comp_continuousWithinAt
-/
theorem ContinuousWithinAt.snd {f : α -> β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuousAt_snd.comp_continuousWithinAt h

/--
theorem `continuousWithinAt_prod_iff` / 定理 `continuousWithinAt_prod_iff`

English:
theorem continuousWithinAt_prod_iff
  given: {f : α -> β × γ} {s : Set α} {x : α}
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prodMk h2⟩

中文:
定理 continuousWithinAt_prod_iff
  条件: {f : α -> β × γ} {s : 集合 α} {x : α}
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prodMk h2⟩

Depends on / 依赖: h.fst, h.snd, h1.prodMk, prodMk
-/
theorem continuousWithinAt_prod_iff {f : α -> β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prodMk h2⟩

/--
theorem `ContinuousWithinAt.prodMap` / 定理 `ContinuousWithinAt.prodMap`

English:
theorem ContinuousWithinAt.prodMap
  statement: {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set β} {x : α} {y : β}
  proof: .prodMk (hf.comp continuousWithinAt_fst mapsTo_fst_prod)
    (hg.comp continuousWithinAt_snd mapsTo_snd_prod)

中文:
定理 ContinuousWithinAt.prodMap
  结论: {f : α -> γ} {g : β -> δ} {s : 集合 α} {t : 集合 β} {x : α} {y : β}
  证明: .prodMk (hf.comp continuousWithinAt_fst mapsTo_fst_prod)
    (hg.comp continuousWithinAt_snd mapsTo_snd_prod)

Depends on / 依赖: continuousWithinAt_fst, continuousWithinAt_snd, hf.comp, hg.comp, mapsTo_fst_prod, mapsTo_snd_prod, prodMk
-/
theorem ContinuousWithinAt.prodMap {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) :=
  .prodMk (hf.comp continuousWithinAt_fst mapsTo_fst_prod)
    (hg.comp continuousWithinAt_snd mapsTo_snd_prod)

/--
theorem `ContinuousOn.prodMap` / 定理 `ContinuousOn.prodMap`

English:
theorem ContinuousOn.prodMap
  statement: {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
  proof: fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  (hf x hx).prodMap (hg y hy)

中文:
定理 ContinuousOn.prodMap
  结论: {f : α -> γ} {g : β -> δ} {s : 集合 α} {t : 集合 β} (hf : ContinuousOn f s)
  证明: fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  (hf x hx).prodMap (hg y hy)
-/
theorem ContinuousOn.prodMap {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) := fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  (hf x hx).prodMap (hg y hy)

/--
theorem `continuousWithinAt_prod_of_discrete_left` / 定理 `continuousWithinAt_prod_of_discrete_left`

English:
theorem continuousWithinAt_prod_of_discrete_left
  statement: [DiscreteTopology α]
  proof: by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl

中文:
定理 continuousWithinAt_prod_of_discrete_left
  结论: [离散拓扑 α]
  证明: by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl

Depends on / 依赖: ContinuousWithinAt, map_inf_principal_preimage, nhdsWithin, nhds_discrete, nhds_prod_eq, pure_prod, simp_rw, x.eta
-/
theorem continuousWithinAt_prod_of_discrete_left [DiscreteTopology α]
    {f : α × β -> γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨x.1, ·⟩) {b | (x.1, b) in s} x.2 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl

/--
theorem `continuousWithinAt_prod_of_discrete_right` / 定理 `continuousWithinAt_prod_of_discrete_right`

English:
theorem continuousWithinAt_prod_of_discrete_right
  statement: [DiscreteTopology β]
  proof: by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl

中文:
定理 continuousWithinAt_prod_of_discrete_right
  结论: [离散拓扑 β]
  证明: by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl

Depends on / 依赖: ContinuousWithinAt, map_inf_principal_preimage, nhdsWithin, nhds_discrete, nhds_prod_eq, prod_pure, simp_rw, x.eta
-/
theorem continuousWithinAt_prod_of_discrete_right [DiscreteTopology β]
    {f : α × β -> γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨·, x.2⟩) {a | (a, x.2) in s} x.1 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl

/--
theorem `continuousAt_prod_of_discrete_left` / 定理 `continuousAt_prod_of_discrete_left`

English:
theorem continuousAt_prod_of_discrete_left
  given: [DiscreteTopology α] {f : α × β -> γ} {x : α × β}
  proof: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left

中文:
定理 continuousAt_prod_of_discrete_left
  条件: [离散拓扑 α] {f : α × β -> γ} {x : α × β}
  证明: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left

Depends on / 依赖: continuousWithinAt_prod_of_discrete_left, continuousWithinAt_univ, simp_rw
-/
theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨x.1, ·⟩) x.2 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left

/--
theorem `continuousAt_prod_of_discrete_right` / 定理 `continuousAt_prod_of_discrete_right`

English:
theorem continuousAt_prod_of_discrete_right
  given: [DiscreteTopology β] {f : α × β -> γ} {x : α × β}
  proof: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right

中文:
定理 continuousAt_prod_of_discrete_right
  条件: [离散拓扑 β] {f : α × β -> γ} {x : α × β}
  证明: by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right

Depends on / 依赖: continuousWithinAt_prod_of_discrete_right, continuousWithinAt_univ, simp_rw
-/
theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨·, x.2⟩) x.1 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right

/--
theorem `continuousOn_prod_of_discrete_left` / 定理 `continuousOn_prod_of_discrete_left`

English:
theorem continuousOn_prod_of_discrete_left
  given: [DiscreteTopology α] {f : α × β -> γ} {s : Set (α × β)}
  proof: by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl

中文:
定理 continuousOn_prod_of_discrete_left
  条件: [离散拓扑 α] {f : α × β -> γ} {s : 集合 (α × β)}
  证明: by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl

Depends on / 依赖: ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left, simp_rw
-/
theorem continuousOn_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ forall a, ContinuousOn (f ⟨a, ·⟩) {b | (a, b) in s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl

/--
theorem `continuousOn_prod_of_discrete_right` / 定理 `continuousOn_prod_of_discrete_right`

English:
theorem continuousOn_prod_of_discrete_right
  given: [DiscreteTopology β] {f : α × β -> γ} {s : Set (α × β)}
  proof: by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_comm

中文:
定理 continuousOn_prod_of_discrete_right
  条件: [离散拓扑 β] {f : α × β -> γ} {s : 集合 (α × β)}
  证明: by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_comm

Depends on / 依赖: ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right, forall_comm, simp_rw
-/
theorem continuousOn_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ forall b, ContinuousOn (f ⟨·, b⟩) {a | (a, b) in s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_comm

/--
theorem `continuous_prod_of_discrete_left` / 定理 `continuous_prod_of_discrete_left`

English:
theorem continuous_prod_of_discrete_left
  given: [DiscreteTopology α] {f : α × β -> γ}
  proof: by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_left

中文:
定理 continuous_prod_of_discrete_left
  条件: [离散拓扑 α] {f : α × β -> γ}
  证明: by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_left

Depends on / 依赖: continuousOn_prod_of_discrete_left, continuousOn_univ, simp_rw
-/
theorem continuous_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} :
    Continuous f ↔ forall a, Continuous (f ⟨a, ·⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_left

/--
theorem `continuous_prod_of_discrete_right` / 定理 `continuous_prod_of_discrete_right`

English:
theorem continuous_prod_of_discrete_right
  given: [DiscreteTopology β] {f : α × β -> γ}
  proof: by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_right

中文:
定理 continuous_prod_of_discrete_right
  条件: [离散拓扑 β] {f : α × β -> γ}
  证明: by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_right

Depends on / 依赖: continuousOn_prod_of_discrete_right, continuousOn_univ, simp_rw
-/
theorem continuous_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} :
    Continuous f ↔ forall b, Continuous (f ⟨·, b⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_right

/--
theorem `isOpenMap_prod_of_discrete_left` / 定理 `isOpenMap_prod_of_discrete_left`

English:
theorem isOpenMap_prod_of_discrete_left
  given: [DiscreteTopology α] {f : α × β -> γ}
  proof: by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl

中文:
定理 isOpenMap_prod_of_discrete_left
  条件: [离散拓扑 α] {f : α × β -> γ}
  证明: by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl

Depends on / 依赖: Prod.forall, isOpenMap_iff_nhds_le, map_map, nhds_discrete, nhds_prod_eq, pure_prod, simp_rw
-/
theorem isOpenMap_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} :
    IsOpenMap f ↔ forall a, IsOpenMap (f ⟨a, ·⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl

/--
theorem `isOpenMap_prod_of_discrete_right` / 定理 `isOpenMap_prod_of_discrete_right`

English:
theorem isOpenMap_prod_of_discrete_right
  given: [DiscreteTopology β] {f : α × β -> γ}
  proof: by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_comm (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl

中文:
定理 isOpenMap_prod_of_discrete_right
  条件: [离散拓扑 β] {f : α × β -> γ}
  证明: by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_comm (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl

Depends on / 依赖: Prod.forall, forall_comm, isOpenMap_iff_nhds_le, map_map, nhds_discrete, nhds_prod_eq, prod_pure, simp_rw
-/
theorem isOpenMap_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} :
    IsOpenMap f ↔ forall b, IsOpenMap (f ⟨·, b⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_comm (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl

/--
theorem `ContinuousOn.uncurry_left` / 定理 `ContinuousOn.uncurry_left`

English:
theorem ContinuousOn.uncurry_left
  statement: {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (a : α) (ha : a in sα)
  proof: by
  let g : β -> γ := f.uncurry ∘ (fun b => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

中文:
定理 ContinuousOn.uncurry_left
  结论: {f : α -> β -> γ} {sα : 集合 α} {sβ : 集合 β} (a : α) (ha : a in sα)
  证明: by
  let g : β -> γ := f.uncurry ∘ (fun b => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

Depends on / 依赖: ContinuousOn, ContinuousOn.comp, ContinuousOn.congr, MapsTo, Set.MapsTo, f.uncurry, fun_prop, uncurry
-/
theorem ContinuousOn.uncurry_left {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (a : α) (ha : a in sα)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (f a) sβ := by
  let g : β -> γ := f.uncurry ∘ (fun b => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

/--
theorem `ContinuousOn.uncurry_right` / 定理 `ContinuousOn.uncurry_right`

English:
theorem ContinuousOn.uncurry_right
  statement: {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (b : β) (ha : b in sβ)
  proof: by
  let g : α -> γ := f.uncurry ∘ (fun a => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

中文:
定理 ContinuousOn.uncurry_right
  结论: {f : α -> β -> γ} {sα : 集合 α} {sβ : 集合 β} (b : β) (ha : b in sβ)
  证明: by
  let g : α -> γ := f.uncurry ∘ (fun a => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

Depends on / 依赖: ContinuousOn, ContinuousOn.comp, ContinuousOn.congr, MapsTo, Set.MapsTo, f.uncurry, fun_prop, uncurry
-/
theorem ContinuousOn.uncurry_right {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (b : β) (ha : b in sβ)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (fun a => f a b) sα := by
  let g : α -> γ := f.uncurry ∘ (fun a => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])


/--
theorem `continuousWithinAt_pi` / 定理 `continuousWithinAt_pi`

English:
theorem continuousWithinAt_pi
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: tendsto_pi_nhds

中文:
定理 continuousWithinAt_pi
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: tendsto_pi_nhds

Depends on / 依赖: tendsto_pi_nhds
-/
theorem continuousWithinAt_pi {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    {f : α -> forall i, X i} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ forall i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds

/--
theorem `continuousOn_pi` / 定理 `continuousOn_pi`

English:
theorem continuousOn_pi
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]

中文:
定理 continuousOn_pi
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]

Depends on / 依赖: tendsto_pi_nhds
-/
theorem continuousOn_pi {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    {f : α -> forall i, X i} {s : Set α} : ContinuousOn f s ↔ forall i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]
/--
theorem `continuousOn_pi'` / 定理 `continuousOn_pi'`

English:
theorem continuousOn_pi'
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: continuousOn_pi.2 hf

@[fun_prop]

中文:
定理 continuousOn_pi'
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: continuousOn_pi.2 hf

@[fun_prop]

Depends on / 依赖: continuousOn_pi
-/
theorem continuousOn_pi' {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    {f : α -> forall i, X i} {s : Set α} (hf : forall i, ContinuousOn (fun y => f y i) s) :
    ContinuousOn f s :=
  continuousOn_pi.2 hf

@[fun_prop]
/--
theorem `continuousOn_apply` / 定理 `continuousOn_apply`

English:
theorem continuousOn_apply
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: Continuous.continuousOn (continuous_apply i)

中文:
定理 continuousOn_apply
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: Continuous.continuousOn (continuous_apply i)

Depends on / 依赖: Continuous, Continuous.continuousOn, continuousOn, continuous_apply
-/
theorem continuousOn_apply {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    (i : ι) (s) : ContinuousOn (fun p : forall i, X i => p i) s :=
  Continuous.continuousOn (continuous_apply i)


/-!
## Specific functions
-/

@[fun_prop]
/--
theorem `continuousOn_const` / 定理 `continuousOn_const`

English:
theorem continuousOn_const
  given: {s : Set α} {c : β}
  statement: ContinuousOn (fun _ => c) s
  proof: continuous_const.continuousOn

@[fun_prop]

中文:
定理 continuousOn_const
  条件: {s : 集合 α} {c : β}
  结论: ContinuousOn (fun _ => c) s
  证明: continuous_const.continuousOn

@[fun_prop]

Depends on / 依赖: continuousOn, continuous_const, continuous_const.continuousOn
-/
theorem continuousOn_const {s : Set α} {c : β} : ContinuousOn (fun _ => c) s :=
  continuous_const.continuousOn

@[fun_prop]
/--
theorem `continuousWithinAt_const` / 定理 `continuousWithinAt_const`

English:
theorem continuousWithinAt_const
  given: {b : β} {s : Set α} {x : α}
  proof: continuous_const.continuousWithinAt

中文:
定理 continuousWithinAt_const
  条件: {b : β} {s : 集合 α} {x : α}
  证明: continuous_const.continuousWithinAt

Depends on / 依赖: continuousWithinAt, continuous_const, continuous_const.continuousWithinAt
-/
theorem continuousWithinAt_const {b : β} {s : Set α} {x : α} :
    ContinuousWithinAt (fun _ : α => b) s x :=
  continuous_const.continuousWithinAt

/--
theorem `continuousOn_id` / 定理 `continuousOn_id`

English:
theorem continuousOn_id
  given: {s : Set α}
  statement: ContinuousOn id s
  proof: continuous_id.continuousOn

@[fun_prop]

中文:
定理 continuousOn_id
  条件: {s : 集合 α}
  结论: ContinuousOn id s
  证明: continuous_id.continuousOn

@[fun_prop]

Depends on / 依赖: continuousOn, continuous_id, continuous_id.continuousOn
-/
theorem continuousOn_id {s : Set α} : ContinuousOn id s :=
  continuous_id.continuousOn

@[fun_prop]
/--
theorem `continuousOn_id'` / 定理 `continuousOn_id'`

English:
theorem continuousOn_id'
  given: (s : Set α)
  statement: ContinuousOn (fun x : α => x) s
  proof: continuousOn_id

中文:
定理 continuousOn_id'
  条件: (s : 集合 α)
  结论: ContinuousOn (fun x : α => x) s
  证明: continuousOn_id

Depends on / 依赖: continuousOn_id
-/
theorem continuousOn_id' (s : Set α) : ContinuousOn (fun x : α => x) s := continuousOn_id

/--
theorem `continuousWithinAt_id` / 定理 `continuousWithinAt_id`

English:
theorem continuousWithinAt_id
  given: {s : Set α} {x : α}
  statement: ContinuousWithinAt id s x
  proof: continuous_id.continuousWithinAt

中文:
定理 continuousWithinAt_id
  条件: {s : 集合 α} {x : α}
  结论: ContinuousWithinAt id s x
  证明: continuous_id.continuousWithinAt

Depends on / 依赖: continuousWithinAt, continuous_id, continuous_id.continuousWithinAt
-/
theorem continuousWithinAt_id {s : Set α} {x : α} : ContinuousWithinAt id s x :=
  continuous_id.continuousWithinAt

/--
theorem `ContinuousOn.iterate` / 定理 `ContinuousOn.iterate`

English:
theorem ContinuousOn.iterate
  statement: {f : α -> α} {s : Set α} (hcont : ContinuousOn f s)

中文:
定理 ContinuousOn.iterate
  结论: {f : α -> α} {s : 集合 α} (hcont : ContinuousOn f s)
-/
protected theorem ContinuousOn.iterate {f : α -> α} {s : Set α} (hcont : ContinuousOn f s)
    (hmaps : MapsTo f s s) : forall n, ContinuousOn (f^[n]) s
  | 0 => continuousOn_id
  | (n + 1) => (hcont.iterate hmaps n).comp hcont hmaps

section Fin
variable {n : Nat} {X : Fin (n + 1) -> Type*} [forall i, TopologicalSpace (X i)]

/--
theorem `ContinuousWithinAt.finCons` / 定理 `ContinuousWithinAt.finCons`

English:
theorem ContinuousWithinAt.finCons
  proof: hf.tendsto.finCons hg

中文:
定理 ContinuousWithinAt.finCons
  证明: hf.tendsto.finCons hg

Depends on / 依赖: finCons, hf.tendsto.finCons, tendsto
-/
theorem ContinuousWithinAt.finCons
    {f : α -> X 0} {g : α -> forall j : Fin n, X (Fin.succ j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.cons (f a) (g a)) s a :=
  hf.tendsto.finCons hg

/--
theorem `ContinuousOn.finCons` / 定理 `ContinuousOn.finCons`

English:
theorem ContinuousOn.finCons
  statement: {f : α -> X 0} {s : Set α} {g : α -> forall j : Fin n, X (Fin.succ j)}
  proof: fun a ha =>
  (hf a ha).finCons (hg a ha)

中文:
定理 ContinuousOn.finCons
  结论: {f : α -> X 0} {s : 集合 α} {g : α -> 对任意 j : 有限集 n, X (有限集.succ j)}
  证明: fun a ha =>
  (hf a ha).finCons (hg a ha)
-/
theorem ContinuousOn.finCons {f : α -> X 0} {s : Set α} {g : α -> forall j : Fin n, X (Fin.succ j)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.cons (f a) (g a)) s := fun a ha =>
  (hf a ha).finCons (hg a ha)

/--
theorem `ContinuousWithinAt.matrixVecCons` / 定理 `ContinuousWithinAt.matrixVecCons`

English:
theorem ContinuousWithinAt.matrixVecCons
  statement: {f : α -> β} {g : α -> Fin n -> β} {a : α} {s : Set α}
  proof: hf.tendsto.matrixVecCons hg

中文:
定理 ContinuousWithinAt.matrixVecCons
  结论: {f : α -> β} {g : α -> 有限集 n -> β} {a : α} {s : 集合 α}
  证明: hf.tendsto.matrixVecCons hg

Depends on / 依赖: hf.tendsto.matrixVecCons, matrixVecCons, tendsto
-/
theorem ContinuousWithinAt.matrixVecCons {f : α -> β} {g : α -> Fin n -> β} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Matrix.vecCons (f a) (g a)) s a :=
  hf.tendsto.matrixVecCons hg

/--
theorem `ContinuousOn.matrixVecCons` / 定理 `ContinuousOn.matrixVecCons`

English:
theorem ContinuousOn.matrixVecCons
  statement: {f : α -> β} {g : α -> Fin n -> β} {s : Set α}
  proof: fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)

中文:
定理 ContinuousOn.matrixVecCons
  结论: {f : α -> β} {g : α -> 有限集 n -> β} {s : 集合 α}
  证明: fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)
-/
theorem ContinuousOn.matrixVecCons {f : α -> β} {g : α -> Fin n -> β} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Matrix.vecCons (f a) (g a)) s := fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)

/--
theorem `ContinuousWithinAt.finSnoc` / 定理 `ContinuousWithinAt.finSnoc`

English:
theorem ContinuousWithinAt.finSnoc
  proof: hf.tendsto.finSnoc hg

中文:
定理 ContinuousWithinAt.finSnoc
  证明: hf.tendsto.finSnoc hg

Depends on / 依赖: finSnoc, hf.tendsto.finSnoc, tendsto
-/
theorem ContinuousWithinAt.finSnoc
    {f : α -> forall j : Fin n, X (Fin.castSucc j)} {g : α -> X (Fin.last _)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.snoc (f a) (g a)) s a :=
  hf.tendsto.finSnoc hg

/--
theorem `ContinuousOn.finSnoc` / 定理 `ContinuousOn.finSnoc`

English:
theorem ContinuousOn.finSnoc
  proof: fun a ha =>
  (hf a ha).finSnoc (hg a ha)

中文:
定理 ContinuousOn.finSnoc
  证明: fun a ha =>
  (hf a ha).finSnoc (hg a ha)
-/
theorem ContinuousOn.finSnoc
    {f : α -> forall j : Fin n, X (Fin.castSucc j)} {g : α -> X (Fin.last _)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.snoc (f a) (g a)) s := fun a ha =>
  (hf a ha).finSnoc (hg a ha)

/--
theorem `ContinuousWithinAt.finInsertNth` / 定理 `ContinuousWithinAt.finInsertNth`

English:
theorem ContinuousWithinAt.finInsertNth
  proof: hf.tendsto.finInsertNth i hg

中文:
定理 ContinuousWithinAt.finInsertNth
  证明: hf.tendsto.finInsertNth i hg

Depends on / 依赖: finInsertNth, hf.tendsto.finInsertNth, tendsto
-/
theorem ContinuousWithinAt.finInsertNth
    (i : Fin (n + 1)) {f : α -> X i} {g : α -> forall j : Fin n, X (i.succAbove j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.tendsto.finInsertNth i hg

/--
theorem `ContinuousOn.finInsertNth` / 定理 `ContinuousOn.finInsertNth`

English:
theorem ContinuousOn.finInsertNth
  proof: fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)

中文:
定理 ContinuousOn.finInsertNth
  证明: fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)
-/
theorem ContinuousOn.finInsertNth
    (i : Fin (n + 1)) {f : α -> X i} {g : α -> forall j : Fin n, X (i.succAbove j)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)

end Fin

/--
theorem `Set.LeftInvOn.map_nhdsWithin_eq` / 定理 `Set.LeftInvOn.map_nhdsWithin_eq`

English:
theorem Set.LeftInvOn.map_nhdsWithin_eq
  statement: {f : α -> β} {g : β -> α} {x : β} {s : Set β}
  proof: by
  apply le_antisymm
  · exact hg.tendsto_nhdsWithin (mapsTo_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.rightInvOn_image.eqOn.eventuallyEq_of_mem self_mem_nhdsWithin
    refine le_map_of_right_inverse A ?_
    simpa only [hx] using hf.tendsto_nhdsWithin (h.mapsTo (surjOn_image _

中文:
定理 集合.LeftInvOn.map_nhdsWithin_eq
  结论: {f : α -> β} {g : β -> α} {x : β} {s : 集合 β}
  证明: by
  apply le_antisymm
  · exact hg.tendsto_nhdsWithin (mapsTo_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.rightInvOn_image.eqOn.eventuallyEq_of_mem self_mem_nhdsWithin
    refine le_map_of_right_inverse A ?_
    simpa only [hx] using hf.tendsto_nhdsWithin (h.mapsTo (surjOn_image _

Depends on / 依赖: eventuallyEq_of_mem, h.mapsTo, h.rightInvOn_image.eqOn.eventuallyEq_of_mem, hf.tendsto_nhdsWithin, hg.tendsto_nhdsWithin, le_antisymm, le_map_of_right_inverse, mapsTo, mapsTo_image, rightInvOn_image, self_mem_nhdsWithin, surjOn_image, tendsto_nhdsWithin
-/
theorem Set.LeftInvOn.map_nhdsWithin_eq {f : α -> β} {g : β -> α} {x : β} {s : Set β}
    (h : LeftInvOn f g s) (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s) (g x))
    (hg : ContinuousWithinAt g s x) : map g (𝓝[s] x) = 𝓝[g '' s] g x := by
  apply le_antisymm
  · exact hg.tendsto_nhdsWithin (mapsTo_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.rightInvOn_image.eqOn.eventuallyEq_of_mem self_mem_nhdsWithin
    refine le_map_of_right_inverse A ?_
    simpa only [hx] using hf.tendsto_nhdsWithin (h.mapsTo (surjOn_image _ _))

/--
theorem `Function.LeftInverse.map_nhds_eq` / 定理 `Function.LeftInverse.map_nhds_eq`

English:
theorem Function.LeftInverse.map_nhds_eq
  statement: {f : α -> β} {g : β -> α} {x : β}
  proof: by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.leftInvOn univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuousWithinAt

中文:
定理 函数.左逆.map_nhds_eq
  结论: {f : α -> β} {g : β -> α} {x : β}
  证明: by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.leftInvOn univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuousWithinAt

Depends on / 依赖: continuousWithinAt, h.leftInvOn, hg.continuousWithinAt, image_univ, leftInvOn, map_nhdsWithin_eq, nhdsWithin_univ
-/
theorem Function.LeftInverse.map_nhds_eq {f : α -> β} {g : β -> α} {x : β}
    (h : Function.LeftInverse f g) (hf : ContinuousWithinAt f (range g) (g x))
    (hg : ContinuousAt g x) : map g (𝓝 x) = 𝓝[range g] g x := by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.leftInvOn univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuousWithinAt

/--
lemma `Topology.IsInducing.continuousWithinAt_iff` / 引理 `Topology.IsInducing.continuousWithinAt_iff`

English:
lemma Topology.IsInducing.continuousWithinAt_iff
  statement: {f : α -> β} {g : β -> γ} (hg : IsInducing g)
  proof: by
  simp_rw [ContinuousWithinAt, hg.tendsto_nhds_iff]; rfl

中文:
引理 拓扑.是Inducing.continuousWithinAt_iff
  结论: {f : α -> β} {g : β -> γ} (hg : 是Inducing g)
  证明: by
  simp_rw [ContinuousWithinAt, hg.tendsto_nhds_iff]; rfl

Depends on / 依赖: ContinuousWithinAt, hg.tendsto_nhds_iff, simp_rw, tendsto_nhds_iff
-/
lemma Topology.IsInducing.continuousWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g)
    {s : Set α} {x : α} : ContinuousWithinAt f s x ↔ ContinuousWithinAt (g ∘ f) s x := by
  simp_rw [ContinuousWithinAt, hg.tendsto_nhds_iff]; rfl

/--
lemma `Topology.IsInducing.continuousOn_iff` / 引理 `Topology.IsInducing.continuousOn_iff`

English:
lemma Topology.IsInducing.continuousOn_iff
  statement: {f : α -> β} {g : β -> γ} (hg : IsInducing g)
  proof: by
  simp_rw [ContinuousOn, hg.continuousWithinAt_iff]

中文:
引理 拓扑.是Inducing.continuousOn_iff
  结论: {f : α -> β} {g : β -> γ} (hg : 是Inducing g)
  证明: by
  simp_rw [ContinuousOn, hg.continuousWithinAt_iff]

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff, hg.continuousWithinAt_iff, simp_rw
-/
lemma Topology.IsInducing.continuousOn_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s := by
  simp_rw [ContinuousOn, hg.continuousWithinAt_iff]

/--
lemma `Topology.IsInducing.map_nhdsWithin_eq` / 引理 `Topology.IsInducing.map_nhdsWithin_eq`

English:
lemma Topology.IsInducing.map_nhdsWithin_eq
  given: {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α)
  proof: by
  ext; simp +contextual [mem_nhdsWithin_iff_eventually, hf.nhds_eq_comap, forall_comm (α := _ in _)]

中文:
引理 拓扑.是Inducing.map_nhdsWithin_eq
  条件: {f : α -> β} (hf : 是Inducing f) (s : 集合 α) (x : α)
  证明: by
  ext; simp +contextual [mem_nhdsWithin_iff_eventually, hf.nhds_eq_comap, forall_comm (α := _ in _)]

Depends on / 依赖: contextual, forall_comm, hf.nhds_eq_comap, mem_nhdsWithin_iff_eventually, nhds_eq_comap
-/
lemma Topology.IsInducing.map_nhdsWithin_eq {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x := by
  ext; simp +contextual [mem_nhdsWithin_iff_eventually, hf.nhds_eq_comap, forall_comm (α := _ in _)]

/--
lemma `Topology.IsInducing.continuousOn_image_iff` / 引理 `Topology.IsInducing.continuousOn_image_iff`

English:
lemma Topology.IsInducing.continuousOn_image_iff
  given: {g : β -> γ} {s : Set α} (hf : IsInducing f)
  proof: by
  simp [ContinuousOn, ContinuousWithinAt, ← hf.map_nhdsWithin_eq]

中文:
引理 拓扑.是Inducing.continuousOn_image_iff
  条件: {g : β -> γ} {s : 集合 α} (hf : 是Inducing f)
  证明: by
  simp [ContinuousOn, ContinuousWithinAt, ← hf.map_nhdsWithin_eq]

Depends on / 依赖: ContinuousOn, ContinuousWithinAt, hf.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
lemma Topology.IsInducing.continuousOn_image_iff {g : β -> γ} {s : Set α} (hf : IsInducing f) :
    ContinuousOn g (f '' s) ↔ ContinuousOn (g ∘ f) s := by
  simp [ContinuousOn, ContinuousWithinAt, ← hf.map_nhdsWithin_eq]

/--
lemma `Topology.IsEmbedding.continuousOn_iff` / 引理 `Topology.IsEmbedding.continuousOn_iff`

English:
lemma Topology.IsEmbedding.continuousOn_iff
  statement: {f : α -> β} {g : β -> γ} (hg : IsEmbedding g)
  proof: hg.isInducing.continuousOn_iff

中文:
引理 拓扑.是嵌入.continuousOn_iff
  结论: {f : α -> β} {g : β -> γ} (hg : 是嵌入 g)
  证明: hg.isInducing.continuousOn_iff

Depends on / 依赖: continuousOn_iff, hg.isInducing.continuousOn_iff, isInducing
-/
lemma Topology.IsEmbedding.continuousOn_iff {f : α -> β} {g : β -> γ} (hg : IsEmbedding g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s :=
  hg.isInducing.continuousOn_iff

/--
lemma `Topology.IsEmbedding.map_nhdsWithin_eq` / 引理 `Topology.IsEmbedding.map_nhdsWithin_eq`

English:
lemma Topology.IsEmbedding.map_nhdsWithin_eq
  given: {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α)
  proof: hf.isInducing.map_nhdsWithin_eq s x

中文:
引理 拓扑.是嵌入.map_nhdsWithin_eq
  条件: {f : α -> β} (hf : 是嵌入 f) (s : 集合 α) (x : α)
  证明: hf.isInducing.map_nhdsWithin_eq s x

Depends on / 依赖: hf.isInducing.map_nhdsWithin_eq, isInducing, map_nhdsWithin_eq
-/
lemma Topology.IsEmbedding.map_nhdsWithin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x :=
  hf.isInducing.map_nhdsWithin_eq s x

/--
theorem `Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq` / 定理 `Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq`

English:
theorem Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq
  statement: {f : α -> β} (hf : IsOpenEmbedding f)
  proof: by
  rw [hf.isEmbedding.map_nhdsWithin_eq]; rw [image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.isOpen_range
  rw [inter_assoc]; rw [inter_self]

中文:
定理 拓扑.是开嵌入.map_nhdsWithin_preimage_eq
  结论: {f : α -> β} (hf : 是开嵌入 f)
  证明: by
  rw [hf.isEmbedding.map_nhdsWithin_eq]; rw [image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.isOpen_range
  rw [inter_assoc]; rw [inter_self]

Depends on / 依赖: hf.isEmbedding.map_nhdsWithin_eq, hf.isOpen_range, image_preimage_eq_inter_range, inter_assoc, inter_self, isEmbedding, isOpen_range, map_nhdsWithin_eq, mem_range_self, nhdsWithin_eq_nhdsWithin
-/
theorem Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq {f : α -> β} (hf : IsOpenEmbedding f)
    (s : Set β) (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x := by
  rw [hf.isEmbedding.map_nhdsWithin_eq]; rw [image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.isOpen_range
  rw [inter_assoc]; rw [inter_self]

/--
theorem `Topology.IsQuotientMap.continuousOn_isOpen_iff` / 定理 `Topology.IsQuotientMap.continuousOn_isOpen_iff`

English:
theorem Topology.IsQuotientMap.continuousOn_isOpen_iff
  statement: {f : α -> β} {g : β -> γ} (h : IsQuotientMap f)
  proof: by
  simp only [continuousOn_iff_continuous_domRestrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl

中文:
定理 拓扑.是商映射.continuousOn_isOpen_iff
  结论: {f : α -> β} {g : β -> γ} (h : 是商映射 f)
  证明: by
  simp only [continuousOn_iff_continuous_domRestrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuous_iff, h.restrictPreimage_isOpen, restrictPreimage_isOpen
-/
theorem Topology.IsQuotientMap.continuousOn_isOpen_iff {f : α -> β} {g : β -> γ} (h : IsQuotientMap f)
    {s : Set β} (hs : IsOpen s) : ContinuousOn g s ↔ ContinuousOn (g ∘ f) (f ⁻¹' s) := by
  simp only [continuousOn_iff_continuous_domRestrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl

/--
theorem `IsOpenMap.continuousOn_image_of_leftInvOn` / 定理 `IsOpenMap.continuousOn_image_of_leftInvOn`

English:
theorem IsOpenMap.continuousOn_image_of_leftInvOn
  statement: {f : α -> β} {s : Set α}
  proof: by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t inter s), ?_, ?_⟩
  · rw [← image_domRestrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_mono inter_subset_right), hleft.image_inter']

中文:
定理 是开映射.continuousOn_image_of_leftInvOn
  结论: {f : α -> β} {s : 集合 α}
  证明: by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t inter s), ?_, ?_⟩
  · rw [← image_domRestrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_mono inter_subset_right), hleft.image_inter']

Depends on / 依赖: continuousOn_iff, continuous_subtype_val, hleft.image_inter, ht.preimage, image_domRestrict, image_inter, image_mono, inter_eq_self_of_subset_left, inter_subset_right, preimage
-/
theorem IsOpenMap.continuousOn_image_of_leftInvOn {f : α -> β} {s : Set α}
    (h : IsOpenMap (s.domRestrict f)) {finv : β -> α} (hleft : LeftInvOn finv f s) :
    ContinuousOn finv (f '' s) := by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t inter s), ?_, ?_⟩
  · rw [← image_domRestrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_mono inter_subset_right), hleft.image_inter']

/--
theorem `IsOpenMap.continuousOn_range_of_leftInverse` / 定理 `IsOpenMap.continuousOn_range_of_leftInverse`

English:
theorem IsOpenMap.continuousOn_range_of_leftInverse
  statement: {f : α -> β} (hf : IsOpenMap f) {finv : β -> α}
  proof: by
  rw [← image_univ]
  exact (hf.domRestrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x

中文:
定理 是开映射.continuousOn_range_of_leftInverse
  结论: {f : α -> β} (hf : 是开映射 f) {finv : β -> α}
  证明: by
  rw [← image_univ]
  exact (hf.domRestrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x

Depends on / 依赖: continuousOn_image_of_leftInvOn, domRestrict, hf.domRestrict, image_univ, isOpen_univ
-/
theorem IsOpenMap.continuousOn_range_of_leftInverse {f : α -> β} (hf : IsOpenMap f) {finv : β -> α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (range f) := by
  rw [← image_univ]
  exact (hf.domRestrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x

/--
lemma `ContinuousOn.union_continuousAt` / 引理 `ContinuousOn.union_continuousAt`

English:
lemma ContinuousOn.union_continuousAt
  statement: {f : α -> β} (s_op : IsOpen s)
  proof: continuousOn_of_forall_continuousAt fun _ hx => hx.elim
  (fun h => ContinuousWithinAt.continuousAt (continuousWithinAt hs h) <| IsOpen.mem_nhds s_op h)
  (ht _)

中文:
引理 ContinuousOn.union_continuousAt
  结论: {f : α -> β} (s_op : 是开集 s)
  证明: continuousOn_of_forall_continuousAt fun _ hx => hx.elim
  (fun h => ContinuousWithinAt.continuousAt (continuousWithinAt hs h) <| IsOpen.mem_nhds s_op h)
  (ht _)

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.continuousAt, IsOpen, IsOpen.mem_nhds, continuousAt, continuousOn_of_forall_continuousAt, continuousWithinAt, hx.elim, mem_nhds, s_op
-/
lemma ContinuousOn.union_continuousAt {f : α -> β} (s_op : IsOpen s)
    (hs : ContinuousOn f s) (ht : forall x in t, ContinuousAt f x) :
    ContinuousOn f (s union t) :=
continuousOn_of_forall_continuousAt fun _ hx => hx.elim
  (fun h => ContinuousWithinAt.continuousAt (continuousWithinAt hs h) <| IsOpen.mem_nhds s_op h)
  (ht _)

/--
theorem `ContinuousOn.union_of_isClosed` / 定理 `ContinuousOn.union_of_isClosed`

English:
theorem ContinuousOn.union_of_isClosed
  statement: {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
  proof: by
  classical
  refine fun x hx => .union ?_ ?_
  · refine if hx : x in s then hfs x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if hx : x in t then hft x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

中文:
定理 ContinuousOn.union_of_isClosed
  结论: {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
  证明: by
  classical
  refine fun x hx => .union ?_ ?_
  · refine if hx : x in s then hfs x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if hx : x in t then hft x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

Depends on / 依赖: classical, closure_eq, continuousWithinAt_of_notMem_closure, hs.closure_eq, ht.closure_eq
-/
theorem ContinuousOn.union_of_isClosed {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsClosed s) (ht : IsClosed t) : ContinuousOn f (s union t) := by
  classical
  refine fun x hx => .union ?_ ?_
  · refine if hx : x in s then hfs x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if hx : x in t then hft x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

/--
theorem `continuousOn_union_iff_of_isClosed` / 定理 `continuousOn_union_iff_of_isClosed`

English:
theorem continuousOn_union_iff_of_isClosed
  given: {f : α -> β} (hs : IsClosed s) (ht : IsClosed t)
  proof: ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isClosed h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isClosed := continuousOn_union_iff_of_isClosed

中文:
定理 continuousOn_union_iff_of_isClosed
  条件: {f : α -> β} (hs : 是闭集 s) (ht : 是闭集 t)
  证明: ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isClosed h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isClosed := continuousOn_union_iff_of_isClosed

Depends on / 依赖: h.left.union_of_isClosed, h.mono, h.right, s.subset_union_left, s.subset_union_right, subset_union_left, subset_union_right, union_of_isClosed
-/
theorem continuousOn_union_iff_of_isClosed {f : α -> β} (hs : IsClosed s) (ht : IsClosed t) :
    ContinuousOn f (s union t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isClosed h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isClosed := continuousOn_union_iff_of_isClosed

/--
theorem `ContinuousOn.union_of_isOpen` / 定理 `ContinuousOn.union_of_isOpen`

English:
theorem ContinuousOn.union_of_isOpen
  statement: {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
  proof: union_continuousAt hs hfs fun _ hx => ht.continuousOn_iff.mp hft hx

中文:
定理 ContinuousOn.union_of_isOpen
  结论: {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
  证明: union_continuousAt hs hfs fun _ hx => ht.continuousOn_iff.mp hft hx

Depends on / 依赖: continuousOn_iff, ht.continuousOn_iff.mp, union_continuousAt
-/
theorem ContinuousOn.union_of_isOpen {f : α -> β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsOpen s) (ht : IsOpen t) : ContinuousOn f (s union t) :=
  union_continuousAt hs hfs fun _ hx => ht.continuousOn_iff.mp hft hx

/--
theorem `continuousOn_union_iff_of_isOpen` / 定理 `continuousOn_union_iff_of_isOpen`

English:
theorem continuousOn_union_iff_of_isOpen
  given: {f : α -> β} (hs : IsOpen s) (ht : IsOpen t)
  proof: ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isOpen h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isOpen := continuousOn_union_iff_of_isOpen

中文:
定理 continuousOn_union_iff_of_isOpen
  条件: {f : α -> β} (hs : 是开集 s) (ht : 是开集 t)
  证明: ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isOpen h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isOpen := continuousOn_union_iff_of_isOpen

Depends on / 依赖: h.left.union_of_isOpen, h.mono, h.right, s.subset_union_left, s.subset_union_right, subset_union_left, subset_union_right, union_of_isOpen
-/
theorem continuousOn_union_iff_of_isOpen {f : α -> β} (hs : IsOpen s) (ht : IsOpen t) :
    ContinuousOn f (s union t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h => ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h => h.left.union_of_isOpen h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isOpen := continuousOn_union_iff_of_isOpen

/--
lemma `ContinuousOn.iUnion_of_isOpen` / 引理 `ContinuousOn.iUnion_of_isOpen`

English:
lemma ContinuousOn.iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set α}
  proof: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.continuousWithinAt exact (hf i).continuousAt ((hs i).mem_nhds hxsi)

中文:
引理 ContinuousOn.iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 α}
  证明: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.continuousWithinAt exact (hf i).continuousAt ((hs i).mem_nhds hxsi)

Depends on / 依赖: continuousAt, continuousWithinAt, mem_nhds
-/
lemma ContinuousOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set α}
    (hf : forall i : ι, ContinuousOn f (s i)) (hs : forall i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.continuousWithinAt exact (hf i).continuousAt ((hs i).mem_nhds hxsi)

/--
lemma `continuousOn_iUnion_iff_of_isOpen` / 引理 `continuousOn_iUnion_iff_of_isOpen`

English:
lemma continuousOn_iUnion_iff_of_isOpen
  statement: {ι : Type*} {s : ι -> Set α}
  proof: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContinuousOn.iUnion_of_isOpen h hs⟩

中文:
引理 continuousOn_iUnion_iff_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 α}
  证明: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContinuousOn.iUnion_of_isOpen h hs⟩

Depends on / 依赖: ContinuousOn, ContinuousOn.iUnion_of_isOpen, h.mono, iUnion_of_isOpen, subset_iUnion_of_subset
-/
lemma continuousOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set α}
    (hs : forall i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) ↔ forall i : ι, ContinuousOn f (s i) :=
⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContinuousOn.iUnion_of_isOpen h hs⟩

/--
lemma `continuous_of_continuousOn_iUnion_of_isOpen` / 引理 `continuous_of_continuousOn_iUnion_of_isOpen`

English:
lemma continuous_of_continuousOn_iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set α}
  proof: by
  rw [← continuousOn_univ]; rw [← hs']
  exact ContinuousOn.iUnion_of_isOpen hf hs

中文:
引理 continuous_of_continuousOn_iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 α}
  证明: by
  rw [← continuousOn_univ]; rw [← hs']
  exact ContinuousOn.iUnion_of_isOpen hf hs

Depends on / 依赖: ContinuousOn, ContinuousOn.iUnion_of_isOpen, continuousOn_univ, iUnion_of_isOpen
-/
lemma continuous_of_continuousOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set α}
    (hf : forall i : ι, ContinuousOn f (s i)) (hs : forall i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Continuous f := by
  rw [← continuousOn_univ]; rw [← hs']
  exact ContinuousOn.iUnion_of_isOpen hf hs

-- See `Continuous.tendsto_nhdsSet` for a special case.
/--
theorem `ContinuousOn.tendsto_nhdsSet` / 定理 `ContinuousOn.tendsto_nhdsSet`

English:
theorem ContinuousOn.tendsto_nhdsSet
  statement: {f : α -> β} {s s' : Set α} {t : Set β}
  proof: by
  obtain ⟨V, hV, hsV, hVs'⟩ := mem_nhdsSet_iff_exists.mp hs'
  refine ((hasBasis_nhdsSet s).tendsto_iff (hasBasis_nhdsSet t)).mpr fun U hU =>
    ⟨V inter f ⁻¹' U, ?_, fun _ => ?_⟩
  · exact ⟨(hf.mono hVs').isOpen_inter_preimage hV hU.1,
      subset_inter hsV (hst.mono Subset.rfl hU.2)⟩
  · intr

中文:
定理 ContinuousOn.tendsto_nhdsSet
  结论: {f : α -> β} {s s' : 集合 α} {t : 集合 β}
  证明: by
  obtain ⟨V, hV, hsV, hVs'⟩ := mem_nhdsSet_iff_exists.mp hs'
  refine ((hasBasis_nhdsSet s).tendsto_iff (hasBasis_nhdsSet t)).mpr fun U hU =>
    ⟨V inter f ⁻¹' U, ?_, fun _ => ?_⟩
  · exact ⟨(hf.mono hVs').isOpen_inter_preimage hV hU.1,
      subset_inter hsV (hst.mono Subset.rfl hU.2)⟩
  · intr

Depends on / 依赖: Subset, Subset.rfl, hasBasis_nhdsSet, hf.mono, hst.mono, isOpen_inter_preimage, mem_nhdsSet_iff_exists, mem_nhdsSet_iff_exists.mp, mem_of_mem_inter_right, mem_preimage, subset_inter, tendsto_iff
-/
theorem ContinuousOn.tendsto_nhdsSet {f : α -> β} {s s' : Set α} {t : Set β}
    (hf : ContinuousOn f s') (hs' : s' in 𝓝ˢ s) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) := by
  obtain ⟨V, hV, hsV, hVs'⟩ := mem_nhdsSet_iff_exists.mp hs'
  refine ((hasBasis_nhdsSet s).tendsto_iff (hasBasis_nhdsSet t)).mpr fun U hU =>
    ⟨V inter f ⁻¹' U, ?_, fun _ => ?_⟩
  · exact ⟨(hf.mono hVs').isOpen_inter_preimage hV hU.1,
      subset_inter hsV (hst.mono Subset.rfl hU.2)⟩
  · intro h
    rw [← mem_preimage]
    exact mem_of_mem_inter_right h

/--
theorem `Continuous.tendsto_nhdsSet` / 定理 `Continuous.tendsto_nhdsSet`

English:
theorem Continuous.tendsto_nhdsSet
  statement: {f : α -> β} {t : Set β} (hf : Continuous f)
  proof: hf.continuousOn.tendsto_nhdsSet univ_mem hst

中文:
定理 连续.tendsto_nhdsSet
  结论: {f : α -> β} {t : 集合 β} (hf : 连续 f)
  证明: hf.continuousOn.tendsto_nhdsSet univ_mem hst

Depends on / 依赖: continuousOn, hf.continuousOn.tendsto_nhdsSet, tendsto_nhdsSet, univ_mem
-/
theorem Continuous.tendsto_nhdsSet {f : α -> β} {t : Set β} (hf : Continuous f)
    (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
  hf.continuousOn.tendsto_nhdsSet univ_mem hst

/--
lemma `Continuous.tendsto_nhdsSet_nhds` / 引理 `Continuous.tendsto_nhdsSet_nhds`

English:
lemma Continuous.tendsto_nhdsSet_nhds
  proof: by
  rw [← nhdsSet_singleton]
  exact h.tendsto_nhdsSet h'

中文:
引理 连续.tendsto_nhdsSet_nhds
  证明: by
  rw [← nhdsSet_singleton]
  exact h.tendsto_nhdsSet h'

Depends on / 依赖: h.tendsto_nhdsSet, nhdsSet_singleton, tendsto_nhdsSet
-/
lemma Continuous.tendsto_nhdsSet_nhds
    {b : β} {f : α -> β} (h : Continuous f) (h' : EqOn f (fun _ => b) s) :
    Tendsto f (𝓝ˢ s) (𝓝 b) := by
  rw [← nhdsSet_singleton]
  exact h.tendsto_nhdsSet h'

/--
lemma `ContinuousOn.preimage_mem_nhdsSetWithin` / 引理 `ContinuousOn.preimage_mem_nhdsSetWithin`

English:
lemma ContinuousOn.preimage_mem_nhdsSetWithin
  statement: {f : α -> β} {s : Set α}
  proof: by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
· exact (inter_comm _ _).trans_subset (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc,

中文:
引理 ContinuousOn.preimage_mem_nhdsSetWithin
  结论: {f : α -> β} {s : 集合 α}
  证明: by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
· exact (inter_comm _ _).trans_subset (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc,

Depends on / 依赖: continuousOn_iff, inter_assoc, inter_comm, inter_subset_inter_left, inter_subset_left, inter_subset_right, inter_subset_right.trans, mem_nhdsSetWithin, preimage_inter, preimage_mono, trans_subset
-/
lemma ContinuousOn.preimage_mem_nhdsSetWithin {f : α -> β} {s : Set α}
    (hf : ContinuousOn f s) {t u t' : Set β} (h : u in 𝓝ˢ[t'] t) :
    f ⁻¹' u in 𝓝ˢ[s inter f ⁻¹' t'] (s inter f ⁻¹' t) := by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
· exact (inter_comm _ _).trans_subset (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc, ← hw.2, inter_comm _ s, inter_assoc, ← preimage_inter]
exact inter_subset_right.trans preimage_mono hv.2.2

/--
lemma `ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet` / 引理 `ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet`

English:
lemma ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
  statement: {f : α -> β} {s : Set α}
  proof: by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)

中文:
引理 ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
  结论: {f : α -> β} {s : 集合 α}
  证明: by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)

Depends on / 依赖: ContinuousOn, ContinuousOn.preimage_mem_nhdsSetWithin, preimage_mem_nhdsSetWithin
-/
lemma ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet {f : α -> β} {s : Set α}
    (hf : ContinuousOn f s) {t u : Set β} (h : u in 𝓝ˢ t) : f ⁻¹' u in 𝓝ˢ[s] (s inter f ⁻¹' t) := by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)

/--
lemma `Continuous.preimage_mem_nhdsSetWithin` / 引理 `Continuous.preimage_mem_nhdsSetWithin`

English:
lemma Continuous.preimage_mem_nhdsSetWithin
  statement: {f : α -> β} (hf : Continuous f) {s u s' : Set β}
  proof: by
  simpa using (hf.continuousOn (s := univ)).preimage_mem_nhdsSetWithin h

中文:
引理 连续.preimage_mem_nhdsSetWithin
  结论: {f : α -> β} (hf : 连续 f) {s u s' : 集合 β}
  证明: by
  simpa using (hf.continuousOn (s := univ)).preimage_mem_nhdsSetWithin h

Depends on / 依赖: continuousOn, hf.continuousOn, preimage_mem_nhdsSetWithin
-/
lemma Continuous.preimage_mem_nhdsSetWithin {f : α -> β} (hf : Continuous f) {s u s' : Set β}
    (h : u in 𝓝ˢ[s'] s) : f ⁻¹' u in 𝓝ˢ[f ⁻¹' s'] (f ⁻¹' s) := by
  simpa using (hf.continuousOn (s := univ)).preimage_mem_nhdsSetWithin h

/--
lemma `Continuous.preimage_mem_nhdsSet` / 引理 `Continuous.preimage_mem_nhdsSet`

English:
lemma Continuous.preimage_mem_nhdsSet
  statement: {f : α -> β} (hf : Continuous f) {s u : Set β}
  proof: by
  simpa [h] using hf.preimage_mem_nhdsSetWithin (s := s) (u := u) (s' := univ)

中文:
引理 连续.preimage_mem_nhdsSet
  结论: {f : α -> β} (hf : 连续 f) {s u : 集合 β}
  证明: by
  simpa [h] using hf.preimage_mem_nhdsSetWithin (s := s) (u := u) (s' := univ)

Depends on / 依赖: hf.preimage_mem_nhdsSetWithin, preimage_mem_nhdsSetWithin
-/
lemma Continuous.preimage_mem_nhdsSet {f : α -> β} (hf : Continuous f) {s u : Set β}
    (h : u in 𝓝ˢ s) : f ⁻¹' u in 𝓝ˢ (f ⁻¹' s) := by
  simpa [h] using hf.preimage_mem_nhdsSetWithin (s := s) (u := u) (s' := univ)
