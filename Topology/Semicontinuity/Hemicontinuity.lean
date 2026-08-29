/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.UniformSpace.Closeds
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Sequences

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/

public section

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α]
variable {f g : α -> Set β} {s : Set α} {x : α}

section facts

variable [TopologicalSpace β]


/--
lemma `upperHemicontinuousWithinAt_iff_forall_isOpen` / 引理 `upperHemicontinuousWithinAt_iff_forall_isOpen`

English:
lemma upperHemicontinuousWithinAt_iff_forall_isOpen
  proof: by
  rw [upperHemicontinuousWithinAt_iff]; rw [hasBasis_nhdsSet _ |>.forall_iff ?mono]
case mono => exact fun t₁ t₂ ht h => h.mp .of_forall fun x' => by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicont

中文:
引理 upperHemicontinuousWithinAt_iff_对任意_isOpen
  证明: by
  rw [upperHemicontinuousWithinAt_iff]; rw [hasBasis_nhdsSet _ |>.forall_iff ?mono]
case mono => exact fun t₁ t₂ ht h => h.mp .of_forall fun x' => by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicont

Depends on / 依赖: IsOpen, IsOpen.interior_eq, and_imp, contextual, forall_iff, h.mp, hasBasis_nhdsSet, interior_eq, of_forall, subset_interior_iff_mem_nhdsSet, upperHemicontinuousWithinAt_iff
-/
lemma upperHemicontinuousWithinAt_iff_forall_isOpen :
    UpperHemicontinuousWithinAt f s x ↔ forall u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝[s] x, f x' subseteq u := by
  rw [upperHemicontinuousWithinAt_iff]; rw [hasBasis_nhdsSet _ |>.forall_iff ?mono]
case mono => exact fun t₁ t₂ ht h => h.mp .of_forall fun x' => by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicontinuousWithinAt.forall_isOpen, UpperHemicontinuousWithinAt.of_forall_isOpen⟩ :=
  upperHemicontinuousWithinAt_iff_forall_isOpen

/--
lemma `upperHemicontinuousOn_iff_forall_isOpen` / 引理 `upperHemicontinuousOn_iff_forall_isOpen`

English:
lemma upperHemicontinuousOn_iff_forall_isOpen
  proof: by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=
  upperHemicontinuousOn_iff_forall_isOpen

中文:
引理 upperHemicontinuousOn_iff_对任意_isOpen
  证明: by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=
  upperHemicontinuousOn_iff_forall_isOpen

Depends on / 依赖: upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen
-/
lemma upperHemicontinuousOn_iff_forall_isOpen :
    UpperHemicontinuousOn f s ↔ forall x in s, forall u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝[s] x, f x' subseteq u := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=
  upperHemicontinuousOn_iff_forall_isOpen

/--
lemma `upperHemicontinuousAt_iff_forall_isOpen` / 引理 `upperHemicontinuousAt_iff_forall_isOpen`

English:
lemma upperHemicontinuousAt_iff_forall_isOpen
  proof: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=
  upperHemicontinuousAt_iff_forall_isOpen

中文:
引理 upperHemicontinuousAt_iff_对任意_isOpen
  证明: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=
  upperHemicontinuousAt_iff_forall_isOpen

Depends on / 依赖: Set.univ, upperHemicontinuousWithinAt_iff_forall_isOpen, upperHemicontinuousWithinAt_univ_iff
-/
lemma upperHemicontinuousAt_iff_forall_isOpen :
    UpperHemicontinuousAt f x ↔ forall u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝 x, f x' subseteq u := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=
  upperHemicontinuousAt_iff_forall_isOpen

/--
lemma `upperHemicontinuous_iff_forall_isOpen` / 引理 `upperHemicontinuous_iff_forall_isOpen`

English:
lemma upperHemicontinuous_iff_forall_isOpen
  proof: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=
  upperHemicontinuous_iff_forall_isOpen

中文:
引理 upperHemicontinuous_iff_对任意_isOpen
  证明: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=
  upperHemicontinuous_iff_forall_isOpen

Depends on / 依赖: upperHemicontinuousAt_iff_forall_isOpen, upperHemicontinuous_iff
-/
lemma upperHemicontinuous_iff_forall_isOpen :
    UpperHemicontinuous f ↔ forall x u, IsOpen u -> f x subseteq u -> forallᶠ x' in 𝓝 x, f x' subseteq u := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=
  upperHemicontinuous_iff_forall_isOpen


/--
lemma `upperHemicontinuousWithinAt_iff_preimage_Iic` / 引理 `upperHemicontinuousWithinAt_iff_preimage_Iic`

English:
lemma upperHemicontinuousWithinAt_iff_preimage_Iic
  proof: by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁]; rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ => ?_
  simp [hu.mem_nhdsSet, event

中文:
引理 upperHemicontinuousWithinAt_iff_preimage_Iic
  证明: by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁]; rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ => ?_
  simp [hu.mem_nhdsSet, event

Depends on / 依赖: eventually_iff, forall_iff, hasBasis_nhdsSet, hu.mem_nhdsSet, mem_nhdsSet, simp_rw, upperHemicontinuousWithinAt_iff
-/
lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁]; rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ => ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]

/--
lemma `upperHemicontinuousAt_iff_preimage_Iic` / 引理 `upperHemicontinuousAt_iff_preimage_Iic`

English:
lemma upperHemicontinuousAt_iff_preimage_Iic
  proof: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

中文:
引理 upperHemicontinuousAt_iff_preimage_Iic
  证明: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

Depends on / 依赖: upperHemicontinuousWithinAt_iff_preimage_Iic, upperHemicontinuousWithinAt_univ_iff
-/
lemma upperHemicontinuousAt_iff_preimage_Iic :
    UpperHemicontinuousAt f x ↔ forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝 x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

/--
lemma `upperHemicontinuousOn_iff_preimage_Iic` / 引理 `upperHemicontinuousOn_iff_preimage_Iic`

English:
lemma upperHemicontinuousOn_iff_preimage_Iic
  proof: by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

中文:
引理 upperHemicontinuousOn_iff_preimage_Iic
  证明: by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

Depends on / 依赖: upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic
-/
lemma upperHemicontinuousOn_iff_preimage_Iic :
    UpperHemicontinuousOn f s ↔ forall x in s, forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝[s] x := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

/--
lemma `upperHemicontinuous_iff_preimage_Iic` / 引理 `upperHemicontinuous_iff_preimage_Iic`

English:
lemma upperHemicontinuous_iff_preimage_Iic
  proof: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

中文:
引理 upperHemicontinuous_iff_preimage_Iic
  证明: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

Depends on / 依赖: upperHemicontinuousAt_iff_preimage_Iic, upperHemicontinuous_iff
-/
lemma upperHemicontinuous_iff_preimage_Iic :
    UpperHemicontinuous f ↔ forall x, forall u in 𝓝ˢ (f x), f ⁻¹' Iic u in 𝓝 x := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

/--
lemma `upperHemicontinuous_iff_isOpen_preimage_Iic` / 引理 `upperHemicontinuous_iff_isOpen_preimage_Iic`

English:
lemma upperHemicontinuous_iff_isOpen_preimage_Iic
  proof: by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' Iic _)]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff fun s t hst => by gcongr]
  simp [forall_comm (α := α)]

中文:
引理 upperHemicontinuous_iff_isOpen_preimage_Iic
  证明: by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' Iic _)]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff fun s t hst => by gcongr]
  simp [forall_comm (α := α)]

Depends on / 依赖: forall_comm, forall_iff, hasBasis_nhdsSet, isOpen_iff_mem_nhds, simp_rw, upperHemicontinuous_iff_preimage_Iic
-/
lemma upperHemicontinuous_iff_isOpen_preimage_Iic :
    UpperHemicontinuous f ↔ forall u, IsOpen u -> IsOpen (f ⁻¹' Iic u) := by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' Iic _)]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff fun s t hst => by gcongr]
  simp [forall_comm (α := α)]

/--
lemma `upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl` / 引理 `upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl`

English:
lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl
  proof: by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

中文:
引理 upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl
  证明: by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

Depends on / 依赖: compl_surjective, compl_surjective.forall, conv_rhs, isOpen_compl_iff, upperHemicontinuous_iff_isOpen_preimage_Iic
-/
lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl :
    UpperHemicontinuous f ↔ forall u, IsClosed u -> IsClosed (f ⁻¹' Iic uᶜ)ᶜ := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

/--
lemma `isClosedMap_iff_upperHemicontinuous` / 引理 `isClosedMap_iff_upperHemicontinuous`

English:
lemma isClosedMap_iff_upperHemicontinuous
  given: {f : α -> β}
  proof: by
  rw [isClosedMap_iff_kernImage]; rw [upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

中文:
引理 isClosedMap_iff_upperHemicontinuous
  条件: {f : α -> β}
  证明: by
  rw [isClosedMap_iff_kernImage]; rw [upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

Depends on / 依赖: isClosedMap_iff_kernImage, upperHemicontinuous_iff_isOpen_preimage_Iic
-/
lemma isClosedMap_iff_upperHemicontinuous {f : α -> β} :
    IsClosedMap f ↔ UpperHemicontinuous (f ⁻¹' {·}) := by
  rw [isClosedMap_iff_kernImage]; rw [upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

/--
lemma `lowerHemicontinuous_iff_isOpen_inter_nonempty` / 引理 `lowerHemicontinuous_iff_isOpen_inter_nonempty`

English:
lemma lowerHemicontinuous_iff_isOpen_inter_nonempty
  proof: by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_ofPred, Filter.Eventually]

中文:
引理 lowerHemicontinuous_iff_isOpen_inter_nonempty
  证明: by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_ofPred, Filter.Eventually]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, forall_comm, isOpen_iff_mem_nhds, lowerHemicontinuousAt_iff, lowerHemicontinuous_iff, mem_ofPred, simp_rw
-/
lemma lowerHemicontinuous_iff_isOpen_inter_nonempty :
    LowerHemicontinuous f ↔ forall u, IsOpen u -> IsOpen {x | (f x inter u).Nonempty} := by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_ofPred, Filter.Eventually]

/--
lemma `lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl` / 引理 `lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl`

English:
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl
  proof: by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x inter u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simpa [this] using lowerHemicontinuous_iff_isOpen_inter_nonempty

中文:
引理 lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl
  证明: by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x inter u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simpa [this] using lowerHemicontinuous_iff_isOpen_inter_nonempty

Depends on / 依赖: Nonempty, Set.Nonempty, Set.ext_iff, Set.mem_compl_iff, Set.not_subset, ext_iff, lowerHemicontinuous_iff_isOpen_inter_nonempty, mem_compl_iff, not_subset
-/
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ forall u, IsOpen u -> IsOpen (f ⁻¹' Iic uᶜ)ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x inter u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simpa [this] using lowerHemicontinuous_iff_isOpen_inter_nonempty

/--
lemma `lowerHemicontinuous_iff_isClosed_preimage_Iic` / 引理 `lowerHemicontinuous_iff_isClosed_preimage_Iic`

English:
lemma lowerHemicontinuous_iff_isClosed_preimage_Iic
  proof: by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

中文:
引理 lowerHemicontinuous_iff_isClosed_preimage_Iic
  证明: by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

Depends on / 依赖: compl_surjective, compl_surjective.forall, conv_rhs, isOpen_compl_iff, lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl
-/
lemma lowerHemicontinuous_iff_isClosed_preimage_Iic :
    LowerHemicontinuous f ↔ forall u, IsClosed u -> IsClosed (f ⁻¹' Iic u) := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

/--
lemma `isOpenMap_iff_lowerHemicontinuous` / 引理 `isOpenMap_iff_lowerHemicontinuous`

English:
lemma isOpenMap_iff_lowerHemicontinuous
  given: {f : α -> β}
  proof: by
  rw [isOpenMap_iff_kernImage]; rw [lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

中文:
引理 isOpenMap_iff_lowerHemicontinuous
  条件: {f : α -> β}
  证明: by
  rw [isOpenMap_iff_kernImage]; rw [lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

Depends on / 依赖: isOpenMap_iff_kernImage, lowerHemicontinuous_iff_isClosed_preimage_Iic
-/
lemma isOpenMap_iff_lowerHemicontinuous {f : α -> β} :
    IsOpenMap f ↔ LowerHemicontinuous (f ⁻¹' {·}) := by
  rw [isOpenMap_iff_kernImage]; rw [lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

section singleton_maps

/-! ### Singleton maps

Functions `f : α → β` are continuous if and only if they are lower hemicontinuous if and only if
they are upper hemicontinuous. This is in the sense that the map `g : α → Set β` given by
`g x = {f x}` is both lower or upper hemicontinuous.

This section also provides dot notation to access this fact for continuous functions.
-/

variable {f : α -> β} {s : Set α} {x : α}

/--
lemma `upperHemicontinuous_singleton_id` / 引理 `upperHemicontinuous_singleton_id`

English:
lemma upperHemicontinuous_singleton_id
  statement: UpperHemicontinuous ({·} : α -> Set α)
  proof: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]

中文:
引理 upperHemicontinuous_singleton_id
  结论: UpperHemicontinuous ({·} : α -> 集合 α)
  证明: by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]

Depends on / 依赖: upperHemicontinuousAt_iff, upperHemicontinuous_iff
-/
lemma upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α -> Set α) := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]

@[simp]
/--
lemma `upperHemicontinuousWithinAt_singleton_iff` / 引理 `upperHemicontinuousWithinAt_singleton_iff`

English:
lemma upperHemicontinuousWithinAt_singleton_iff
  proof: by
.comp hf refine ⟨?_, fun hf => upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exa

中文:
引理 upperHemicontinuousWithinAt_singleton_iff
  证明: by
.comp hf refine ⟨?_, fun hf => upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exa

Depends on / 依赖: ContinuousWithinAt, filter_upwards, mapsTo_image, mem_of_mem_nhds, nhdsSet_singleton, tendsto_iff_forall_eventually_mem, upperHemicontinuousWithinAt, upperHemicontinuousWithinAt_iff, upperHemicontinuous_singleton_id, upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt
-/
lemma upperHemicontinuousWithinAt_singleton_iff :
    UpperHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
.comp hf refine ⟨?_, fun hf => upperHemicontinuous_singleton_id.upperHemicontinuousWithinAt _ _
    (mapsTo_image _ _)⟩
  simp only [upperHemicontinuousWithinAt_iff, nhdsSet_singleton, ContinuousWithinAt,
    tendsto_iff_forall_eventually_mem]
  intro h t ht
  filter_upwards [h t ht] with x
  exact mem_of_mem_nhds

alias ⟨_, ContinuousWithinAt.upperHemicontinuousWithinAt⟩ :=
  upperHemicontinuousWithinAt_singleton_iff

@[simp]
/--
lemma `upperHemicontinuousAt_singleton_iff` / 引理 `upperHemicontinuousAt_singleton_iff`

English:
lemma upperHemicontinuousAt_singleton_iff
  proof: by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.upperHemicontinuousAt⟩ := upperHemicontinuousAt_singleton_iff

@[simp]

中文:
引理 upperHemicontinuousAt_singleton_iff
  证明: by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.upperHemicontinuousAt⟩ := upperHemicontinuousAt_singleton_iff

@[simp]

Depends on / 依赖: continuousWithinAt_univ, upperHemicontinuousWithinAt_univ_iff
-/
lemma upperHemicontinuousAt_singleton_iff :
    UpperHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← upperHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.upperHemicontinuousAt⟩ := upperHemicontinuousAt_singleton_iff

@[simp]
/--
lemma `upperHemicontinuousOn_singleton_iff` / 引理 `upperHemicontinuousOn_singleton_iff`

English:
lemma upperHemicontinuousOn_singleton_iff
  proof: forall₂_congr fun _ _ => upperHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.upperHemicontinuousOn⟩ := upperHemicontinuousOn_singleton_iff

@[simp]

中文:
引理 upperHemicontinuousOn_singleton_iff
  证明: forall₂_congr fun _ _ => upperHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.upperHemicontinuousOn⟩ := upperHemicontinuousOn_singleton_iff

@[simp]

Depends on / 依赖: upperHemicontinuousWithinAt_singleton_iff
-/
lemma upperHemicontinuousOn_singleton_iff :
    UpperHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
forall₂_congr fun _ _ => upperHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.upperHemicontinuousOn⟩ := upperHemicontinuousOn_singleton_iff

@[simp]
/--
lemma `upperHemicontinuous_singleton_iff` / 引理 `upperHemicontinuous_singleton_iff`

English:
lemma upperHemicontinuous_singleton_iff
  proof: by
  simp [← upperHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.upperHemicontinuous⟩ := upperHemicontinuous_singleton_iff

中文:
引理 upperHemicontinuous_singleton_iff
  证明: by
  simp [← upperHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.upperHemicontinuous⟩ := upperHemicontinuous_singleton_iff

Depends on / 依赖: upperHemicontinuousOn_univ_iff
-/
lemma upperHemicontinuous_singleton_iff :
    UpperHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← upperHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.upperHemicontinuous⟩ := upperHemicontinuous_singleton_iff

/--
lemma `lowerHemicontinuous_singleton_id` / 引理 `lowerHemicontinuous_singleton_id`

English:
lemma lowerHemicontinuous_singleton_id
  statement: LowerHemicontinuous ({·} : α -> Set α)
  proof: by
  intro x t ⟨ht, hne⟩
  filter_upwards [ht.mem_nhds (Set.singleton_inter_nonempty.mp hne)] with x' hx'
  exact ⟨ht, Set.singleton_inter_nonempty.mpr hx'⟩

@[simp]

中文:
引理 lowerHemicontinuous_singleton_id
  结论: LowerHemicontinuous ({·} : α -> 集合 α)
  证明: by
  intro x t ⟨ht, hne⟩
  filter_upwards [ht.mem_nhds (Set.singleton_inter_nonempty.mp hne)] with x' hx'
  exact ⟨ht, Set.singleton_inter_nonempty.mpr hx'⟩

@[simp]

Depends on / 依赖: Set.singleton_inter_nonempty.mp, Set.singleton_inter_nonempty.mpr, filter_upwards, ht.mem_nhds, mem_nhds, singleton_inter_nonempty
-/
lemma lowerHemicontinuous_singleton_id : LowerHemicontinuous ({·} : α -> Set α) := by
  intro x t ⟨ht, hne⟩
  filter_upwards [ht.mem_nhds (Set.singleton_inter_nonempty.mp hne)] with x' hx'
  exact ⟨ht, Set.singleton_inter_nonempty.mpr hx'⟩

@[simp]
/--
lemma `lowerHemicontinuousWithinAt_singleton_iff` / 引理 `lowerHemicontinuousWithinAt_singleton_iff`

English:
lemma lowerHemicontinuousWithinAt_singleton_iff
  proof: by
  refine ⟨?_, fun hf => (lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt _ _).comp
    hf (mapsTo_image _ _)⟩
  simp only [lowerHemicontinuousWithinAt_iff, Set.singleton_inter_nonempty,
    ContinuousWithinAt, tendsto_iff_forall_eventually_mem]
  intro h t ht
  obtain ⟨u, hut, huo, h

中文:
引理 lowerHemicontinuousWithinAt_singleton_iff
  证明: by
  refine ⟨?_, fun hf => (lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt _ _).comp
    hf (mapsTo_image _ _)⟩
  simp only [lowerHemicontinuousWithinAt_iff, Set.singleton_inter_nonempty,
    ContinuousWithinAt, tendsto_iff_forall_eventually_mem]
  intro h t ht
  obtain ⟨u, hut, huo, h

Depends on / 依赖: ContinuousWithinAt, Set.singleton_inter_nonempty, lowerHemicontinuousWithinAt, lowerHemicontinuousWithinAt_iff, lowerHemicontinuous_singleton_id, lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt, mapsTo_image, mem_nhds_iff, mem_nhds_iff.mp, singleton_inter_nonempty, tendsto_iff_forall_eventually_mem
-/
lemma lowerHemicontinuousWithinAt_singleton_iff :
    LowerHemicontinuousWithinAt ({f ·}) s x ↔ ContinuousWithinAt f s x := by
  refine ⟨?_, fun hf => (lowerHemicontinuous_singleton_id.lowerHemicontinuousWithinAt _ _).comp
    hf (mapsTo_image _ _)⟩
  simp only [lowerHemicontinuousWithinAt_iff, Set.singleton_inter_nonempty,
    ContinuousWithinAt, tendsto_iff_forall_eventually_mem]
  intro h t ht
  obtain ⟨u, hut, huo, hux⟩ := mem_nhds_iff.mp ht
  exact (h u huo hux).mono fun _ hx' => hut hx'

alias ⟨_, ContinuousWithinAt.lowerHemicontinuousWithinAt⟩ :=
  lowerHemicontinuousWithinAt_singleton_iff

@[simp]
/--
lemma `lowerHemicontinuousAt_singleton_iff` / 引理 `lowerHemicontinuousAt_singleton_iff`

English:
lemma lowerHemicontinuousAt_singleton_iff
  statement: LowerHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x
  proof: by
  simp [← lowerHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.lowerHemicontinuousAt⟩ := lowerHemicontinuousAt_singleton_iff

@[simp]

中文:
引理 lowerHemicontinuousAt_singleton_iff
  结论: LowerHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x
  证明: by
  simp [← lowerHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.lowerHemicontinuousAt⟩ := lowerHemicontinuousAt_singleton_iff

@[simp]

Depends on / 依赖: continuousWithinAt_univ, lowerHemicontinuousWithinAt_univ_iff
-/
lemma lowerHemicontinuousAt_singleton_iff : LowerHemicontinuousAt ({f ·}) x ↔ ContinuousAt f x := by
  simp [← lowerHemicontinuousWithinAt_univ_iff, continuousWithinAt_univ]

alias ⟨_, ContinuousAt.lowerHemicontinuousAt⟩ := lowerHemicontinuousAt_singleton_iff

@[simp]
/--
lemma `lowerHemicontinuousOn_singleton_iff` / 引理 `lowerHemicontinuousOn_singleton_iff`

English:
lemma lowerHemicontinuousOn_singleton_iff
  statement: LowerHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s
  proof: forall₂_congr fun _ _ => lowerHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.lowerHemicontinuousOn⟩ := lowerHemicontinuousOn_singleton_iff

@[simp]

中文:
引理 lowerHemicontinuousOn_singleton_iff
  结论: LowerHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s
  证明: forall₂_congr fun _ _ => lowerHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.lowerHemicontinuousOn⟩ := lowerHemicontinuousOn_singleton_iff

@[simp]

Depends on / 依赖: lowerHemicontinuousWithinAt_singleton_iff
-/
lemma lowerHemicontinuousOn_singleton_iff : LowerHemicontinuousOn ({f ·}) s ↔ ContinuousOn f s :=
forall₂_congr fun _ _ => lowerHemicontinuousWithinAt_singleton_iff

alias ⟨_, ContinuousOn.lowerHemicontinuousOn⟩ := lowerHemicontinuousOn_singleton_iff

@[simp]
/--
lemma `lowerHemicontinuous_singleton_iff` / 引理 `lowerHemicontinuous_singleton_iff`

English:
lemma lowerHemicontinuous_singleton_iff
  statement: LowerHemicontinuous ({f ·}) ↔ Continuous f
  proof: by
  simp [← lowerHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.lowerHemicontinuous⟩ := lowerHemicontinuous_singleton_iff

中文:
引理 lowerHemicontinuous_singleton_iff
  结论: LowerHemicontinuous ({f ·}) ↔ 连续 f
  证明: by
  simp [← lowerHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.lowerHemicontinuous⟩ := lowerHemicontinuous_singleton_iff

Depends on / 依赖: lowerHemicontinuousOn_univ_iff
-/
lemma lowerHemicontinuous_singleton_iff : LowerHemicontinuous ({f ·}) ↔ Continuous f := by
  simp [← lowerHemicontinuousOn_univ_iff]

alias ⟨_, Continuous.lowerHemicontinuous⟩ := lowerHemicontinuous_singleton_iff

end singleton_maps

/-! ### Union and intersection, and post-composition with the preimage map -/

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : α -> Set β} {s : Set α} {x : α}

/--
lemma `UpperHemicontinuousWithinAt.union` / 引理 `UpperHemicontinuousWithinAt.union`

English:
lemma UpperHemicontinuousWithinAt.union
  statement: (hf : UpperHemicontinuousWithinAt f s x)
  proof: by
  rw [upperHemicontinuousWithinAt_iff] at hf hg ⊢
  aesop

中文:
引理 UpperHemicontinuousWithinAt.union
  结论: (hf : UpperHemicontinuousWithinAt f s x)
  证明: by
  rw [upperHemicontinuousWithinAt_iff] at hf hg ⊢
  aesop

Depends on / 依赖: upperHemicontinuousWithinAt_iff
-/
lemma UpperHemicontinuousWithinAt.union (hf : UpperHemicontinuousWithinAt f s x)
    (hg : UpperHemicontinuousWithinAt g s x) :
    UpperHemicontinuousWithinAt (fun x => f x union g x) s x := by
  rw [upperHemicontinuousWithinAt_iff] at hf hg ⊢
  aesop

/--
lemma `UpperHemicontinuousOn.union` / 引理 `UpperHemicontinuousOn.union`

English:
lemma UpperHemicontinuousOn.union
  statement: (hf : UpperHemicontinuousOn f s)
  proof: by
  rw [upperHemicontinuousOn_iff] at hf hg ⊢
  exact fun x hx => (hf x hx).union (hg x hx)

中文:
引理 UpperHemicontinuousOn.union
  结论: (hf : UpperHemicontinuousOn f s)
  证明: by
  rw [upperHemicontinuousOn_iff] at hf hg ⊢
  exact fun x hx => (hf x hx).union (hg x hx)

Depends on / 依赖: upperHemicontinuousOn_iff
-/
lemma UpperHemicontinuousOn.union (hf : UpperHemicontinuousOn f s)
    (hg : UpperHemicontinuousOn g s) : UpperHemicontinuousOn (fun x => f x union g x) s := by
  rw [upperHemicontinuousOn_iff] at hf hg ⊢
  exact fun x hx => (hf x hx).union (hg x hx)

/--
lemma `UpperHemicontinuousAt.union` / 引理 `UpperHemicontinuousAt.union`

English:
lemma UpperHemicontinuousAt.union
  statement: (hf : UpperHemicontinuousAt f x)
  proof: by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.union hg

中文:
引理 UpperHemicontinuousAt.union
  结论: (hf : UpperHemicontinuousAt f x)
  证明: by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.union hg

Depends on / 依赖: hf.union, upperHemicontinuousWithinAt_univ_iff
-/
lemma UpperHemicontinuousAt.union (hf : UpperHemicontinuousAt f x)
    (hg : UpperHemicontinuousAt g x) :
    UpperHemicontinuousAt (fun x => f x union g x) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf hg ⊢
  exact hf.union hg

/--
lemma `UpperHemicontinuous.union` / 引理 `UpperHemicontinuous.union`

English:
lemma UpperHemicontinuous.union
  given: (hf : UpperHemicontinuous f) (hg : UpperHemicontinuous g)
  proof: by
  rw [upperHemicontinuous_iff] at hf hg ⊢
  exact fun x => (hf x).union (hg x)

中文:
引理 UpperHemicontinuous.union
  条件: (hf : UpperHemicontinuous f) (hg : UpperHemicontinuous g)
  证明: by
  rw [upperHemicontinuous_iff] at hf hg ⊢
  exact fun x => (hf x).union (hg x)

Depends on / 依赖: upperHemicontinuous_iff
-/
lemma UpperHemicontinuous.union (hf : UpperHemicontinuous f) (hg : UpperHemicontinuous g) :
    UpperHemicontinuous (fun x => f x union g x) := by
  rw [upperHemicontinuous_iff] at hf hg ⊢
  exact fun x => (hf x).union (hg x)

/--
lemma `UpperHemicontinuousWithinAt.inter` / 引理 `UpperHemicontinuousWithinAt.inter`

English:
lemma UpperHemicontinuousWithinAt.inter
  statement: (hf : UpperHemicontinuousWithinAt f s x)
  proof: by
  rw [upperHemicontinuousWithinAt_iff_forall_isOpen] at hf ⊢
  intro t ht_open ht
  specialize hf (t union uᶜ) (ht_open.union hu.isOpen_compl) (by grind)
  grind

中文:
引理 UpperHemicontinuousWithinAt.inter
  结论: (hf : UpperHemicontinuousWithinAt f s x)
  证明: by
  rw [upperHemicontinuousWithinAt_iff_forall_isOpen] at hf ⊢
  intro t ht_open ht
  specialize hf (t union uᶜ) (ht_open.union hu.isOpen_compl) (by grind)
  grind

Depends on / 依赖: ht_open, ht_open.union, hu.isOpen_compl, isOpen_compl, specialize, upperHemicontinuousWithinAt_iff_forall_isOpen
-/
lemma UpperHemicontinuousWithinAt.inter (hf : UpperHemicontinuousWithinAt f s x)
    {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousWithinAt (fun x => f x inter u) s x := by
  rw [upperHemicontinuousWithinAt_iff_forall_isOpen] at hf ⊢
  intro t ht_open ht
  specialize hf (t union uᶜ) (ht_open.union hu.isOpen_compl) (by grind)
  grind

/--
lemma `UpperHemicontinuousOn.inter` / 引理 `UpperHemicontinuousOn.inter`

English:
lemma UpperHemicontinuousOn.inter
  given: (hf : UpperHemicontinuousOn f s) {u : Set β} (hu : IsClosed u)
  proof: by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact (hf · · |>.inter hu)

中文:
引理 UpperHemicontinuousOn.inter
  条件: (hf : UpperHemicontinuousOn f s) {u : 集合 β} (hu : 是闭集 u)
  证明: by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact (hf · · |>.inter hu)

Depends on / 依赖: upperHemicontinuousOn_iff
-/
lemma UpperHemicontinuousOn.inter (hf : UpperHemicontinuousOn f s) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousOn (fun x => f x inter u) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact (hf · · |>.inter hu)

/--
lemma `UpperHemicontinuousAt.inter` / 引理 `UpperHemicontinuousAt.inter`

English:
lemma UpperHemicontinuousAt.inter
  given: (hf : UpperHemicontinuousAt f x) {u : Set β} (hu : IsClosed u)
  proof: by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

中文:
引理 UpperHemicontinuousAt.inter
  条件: (hf : UpperHemicontinuousAt f x) {u : 集合 β} (hu : 是闭集 u)
  证明: by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

Depends on / 依赖: hf.inter, upperHemicontinuousWithinAt_univ_iff
-/
lemma UpperHemicontinuousAt.inter (hf : UpperHemicontinuousAt f x) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuousAt (fun x => f x inter u) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hf.inter hu

/--
lemma `UpperHemicontinuous.inter` / 引理 `UpperHemicontinuous.inter`

English:
lemma UpperHemicontinuous.inter
  given: (hf : UpperHemicontinuous f) {u : Set β} (hu : IsClosed u)
  proof: by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).inter hu

中文:
引理 UpperHemicontinuous.inter
  条件: (hf : UpperHemicontinuous f) {u : 集合 β} (hu : 是闭集 u)
  证明: by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).inter hu

Depends on / 依赖: upperHemicontinuous_iff
-/
lemma UpperHemicontinuous.inter (hf : UpperHemicontinuous f) {u : Set β} (hu : IsClosed u) :
    UpperHemicontinuous (fun x => f x inter u) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).inter hu

section Inducing

variable {γ : Type*} [TopologicalSpace γ] {i : γ -> β}

/--
lemma `UpperHemicontinuousWithinAt.isInducing_comp` / 引理 `UpperHemicontinuousWithinAt.isInducing_comp`

English:
lemma UpperHemicontinuousWithinAt.isInducing_comp
  statement: (hf : UpperHemicontinuousWithinAt f s x)
  proof: by
  refine .of_forall_isOpen fun u hu hifu => ?_
  obtain ⟨v, hv, rfl⟩ := hi.isOpen_iff.mp hu
  simp_rw [← preimage_inter_range (s := f _), preimage_subset_preimage_iff inter_subset_right]
    at hifu ⊢
.forall_isOpen v hv hifu exact hf.inter h_cl

中文:
引理 UpperHemicontinuousWithinAt.isInducing_comp
  结论: (hf : UpperHemicontinuousWithinAt f s x)
  证明: by
  refine .of_forall_isOpen fun u hu hifu => ?_
  obtain ⟨v, hv, rfl⟩ := hi.isOpen_iff.mp hu
  simp_rw [← preimage_inter_range (s := f _), preimage_subset_preimage_iff inter_subset_right]
    at hifu ⊢
.forall_isOpen v hv hifu exact hf.inter h_cl

Depends on / 依赖: forall_isOpen, h_cl, hf.inter, hi.isOpen_iff.mp, inter_subset_right, isOpen_iff, of_forall_isOpen, preimage_inter_range, preimage_subset_preimage_iff, simp_rw
-/
lemma UpperHemicontinuousWithinAt.isInducing_comp (hf : UpperHemicontinuousWithinAt f s x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousWithinAt (fun x => i ⁻¹' (f x)) s x := by
  refine .of_forall_isOpen fun u hu hifu => ?_
  obtain ⟨v, hv, rfl⟩ := hi.isOpen_iff.mp hu
  simp_rw [← preimage_inter_range (s := f _), preimage_subset_preimage_iff inter_subset_right]
    at hifu ⊢
.forall_isOpen v hv hifu exact hf.inter h_cl

/--
lemma `UpperHemicontinuousOn.isInducing_comp` / 引理 `UpperHemicontinuousOn.isInducing_comp`

English:
lemma UpperHemicontinuousOn.isInducing_comp
  statement: (hf : UpperHemicontinuousOn f s)
  proof: by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact fun x hx => (hf x hx).isInducing_comp hi h_cl

中文:
引理 UpperHemicontinuousOn.isInducing_comp
  结论: (hf : UpperHemicontinuousOn f s)
  证明: by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact fun x hx => (hf x hx).isInducing_comp hi h_cl

Depends on / 依赖: h_cl, isInducing_comp, upperHemicontinuousOn_iff
-/
lemma UpperHemicontinuousOn.isInducing_comp (hf : UpperHemicontinuousOn f s)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousOn (fun x => i ⁻¹' (f x)) s := by
  rw [upperHemicontinuousOn_iff] at hf ⊢
  exact fun x hx => (hf x hx).isInducing_comp hi h_cl

/--
lemma `UpperHemicontinuousAt.isInducing_comp` / 引理 `UpperHemicontinuousAt.isInducing_comp`

English:
lemma UpperHemicontinuousAt.isInducing_comp
  statement: (hf : UpperHemicontinuousAt f x)
  proof: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
.isInducing_comp hi h_cl hf.upperHemicontinuousWithinAt (s := Set.univ)

中文:
引理 UpperHemicontinuousAt.isInducing_comp
  结论: (hf : UpperHemicontinuousAt f x)
  证明: by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
.isInducing_comp hi h_cl hf.upperHemicontinuousWithinAt (s := Set.univ)

Depends on / 依赖: Set.univ, h_cl, hf.upperHemicontinuousWithinAt, isInducing_comp, upperHemicontinuousWithinAt, upperHemicontinuousWithinAt_univ_iff
-/
lemma UpperHemicontinuousAt.isInducing_comp (hf : UpperHemicontinuousAt f x)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuousAt (fun x => i ⁻¹' (f x)) x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
.isInducing_comp hi h_cl hf.upperHemicontinuousWithinAt (s := Set.univ)

/--
lemma `UpperHemicontinuous.isInducing_comp` / 引理 `UpperHemicontinuous.isInducing_comp`

English:
lemma UpperHemicontinuous.isInducing_comp
  statement: (hf : UpperHemicontinuous f)
  proof: by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).isInducing_comp hi h_cl

中文:
引理 UpperHemicontinuous.isInducing_comp
  结论: (hf : UpperHemicontinuous f)
  证明: by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).isInducing_comp hi h_cl

Depends on / 依赖: h_cl, isInducing_comp, upperHemicontinuous_iff
-/
lemma UpperHemicontinuous.isInducing_comp (hf : UpperHemicontinuous f)
    (hi : IsInducing i) (h_cl : IsClosed (range i)) :
    UpperHemicontinuous (fun x => i ⁻¹' (f x)) := by
  rw [upperHemicontinuous_iff] at hf ⊢
  exact fun x => (hf x).isInducing_comp hi h_cl

end Inducing

/--
lemma `UpperHemicontinuous.isClosed_domain` / 引理 `UpperHemicontinuous.isClosed_domain`

English:
lemma UpperHemicontinuous.isClosed_domain
  given: (hf : UpperHemicontinuous f)
  proof: by
  simp only [← isOpen_compl_iff, compl_ofPred, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using! hf x ∅

中文:
引理 UpperHemicontinuous.isClosed_domain
  条件: (hf : UpperHemicontinuous f)
  证明: by
  simp only [← isOpen_compl_iff, compl_ofPred, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using! hf x ∅

Depends on / 依赖: compl_ofPred, empty_mem_iff_bot, isOpen_compl_iff, isOpen_iff_mem_nhds, nhdsSet_eq_bot_iff, not_nonempty_iff_eq_empty, simp_rw, upperHemicontinuousAt_iff, upperHemicontinuous_iff
-/
lemma UpperHemicontinuous.isClosed_domain (hf : UpperHemicontinuous f) :
    IsClosed {x | (f x).Nonempty} := by
  simp only [← isOpen_compl_iff, compl_ofPred, not_nonempty_iff_eq_empty, isOpen_iff_mem_nhds]
  intro x (hx : f x = ∅)
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff] at hf
  simpa [hx, empty_mem_iff_bot, nhdsSet_eq_bot_iff] using! hf x ∅

/-! ### Sequential characterizations -/

/--
lemma `UpperHemicontinuousAt.of_sequences` / 引理 `UpperHemicontinuousAt.of_sequences`

English:
lemma UpperHemicontinuousAt.of_sequences
  statement: {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
  proof: by
  refine .of_frequently fun t ht hft => ?_
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hft
  choose y hy using hfx
obtain ⟨y₀, hy₀, φ, hφ, hyφ⟩ := hK.subseq_of_frequently_in (x := y) by
    refine Eventually.frequently ?_
    filter_upwards [hx hf] with n hn
    exact hn (hy n).1
  s

中文:
引理 UpperHemicontinuousAt.of_sequences
  结论: {x₀ : α} [(𝓝 x₀).是余untablyGenerated]
  证明: by
  refine .of_frequently fun t ht hft => ?_
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hft
  choose y hy using hfx
obtain ⟨y₀, hy₀, φ, hφ, hyφ⟩ := hK.subseq_of_frequently_in (x := y) by
    refine Eventually.frequently ?_
    filter_upwards [hx hf] with n hn
    exact hn (hy n).1
  s

Depends on / 依赖: Eventually, Eventually.frequently, closure_eq, exists_seq_forall_of_frequently, filter_upwards, frequently, hK.subseq_of_frequently_in, ht.closure_eq, hx.comp, mem_closure_of_tendsto, of_forall, of_frequently, specialize, subseq_of_frequently_in, tendsto_atTop
-/
lemma UpperHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    {K : Set β} (hK : IsSeqCompact K) (hf : forallᶠ x in 𝓝 x₀, f x subseteq K)
    (h : forall x : Nat -> α, Tendsto x atTop (𝓝 x₀) ->
      forall y : Nat -> β, (forall n, y n in f (x n)) -> forall y₀, Tendsto y atTop (𝓝 y₀) -> y₀ in f x₀) :
    UpperHemicontinuousAt f x₀ := by
  refine .of_frequently fun t ht hft => ?_
  obtain ⟨x, hx, hfx⟩ := exists_seq_forall_of_frequently hft
  choose y hy using hfx
obtain ⟨y₀, hy₀, φ, hφ, hyφ⟩ := hK.subseq_of_frequently_in (x := y) by
    refine Eventually.frequently ?_
    filter_upwards [hx hf] with n hn
    exact hn (hy n).1
  specialize h (x ∘ φ) (hx.comp hφ.tendsto_atTop) (y ∘ φ) (fun n => (hy _).1) _ hyφ
exact ⟨y₀, h, ht.closure_eq ▸ mem_closure_of_tendsto hyφ .of_forall fun n => (hy _).2⟩

/--
lemma `UpperHemicontinuousAt.mem_of_tendsto` / 引理 `UpperHemicontinuousAt.mem_of_tendsto`

English:
lemma UpperHemicontinuousAt.mem_of_tendsto
  statement: {ι : Type*} [RegularSpace β] {x₀ : α}
  proof: by
  by_contra
obtain ⟨s, hs, t, ht, hst⟩ := Filter.disjoint_iff.mp RegularSpace.regular hf_closed this
  suffices existsᶠ n in l, y n in s by
    apply this
    filter_upwards [hy₀ ht] with n hn hyn
    exact hst.notMem_of_mem_left hyn hn
  apply hy.mp
  filter_upwards [hx (hf s hs)] with n hn hyn


中文:
引理 UpperHemicontinuousAt.mem_of_tendsto
  结论: {ι : 类型} [正则空间 β] {x₀ : α}
  证明: by
  by_contra
obtain ⟨s, hs, t, ht, hst⟩ := Filter.disjoint_iff.mp RegularSpace.regular hf_closed this
  suffices existsᶠ n in l, y n in s by
    apply this
    filter_upwards [hy₀ ht] with n hn hyn
    exact hst.notMem_of_mem_left hyn hn
  apply hy.mp
  filter_upwards [hx (hf s hs)] with n hn hyn


Depends on / 依赖: Filter, Filter.disjoint_iff.mp, RegularSpace, RegularSpace.regular, disjoint_iff, filter_upwards, hf_closed, hst.notMem_of_mem_left, hy.mp, interior_subset, mem_ofPred_eq, notMem_of_mem_left, preimage_ofPred_eq, regular, subset_interior_iff_mem_nhdsSet
-/
lemma UpperHemicontinuousAt.mem_of_tendsto {ι : Type*} [RegularSpace β] {x₀ : α}
    {l : Filter ι} (hf : UpperHemicontinuousAt f x₀) (hf_closed : IsClosed (f x₀))
    {x : ι -> α} (hx : Tendsto x l (𝓝 x₀))
    {y : ι -> β} (hy : existsᶠ n in l, y n in f (x n)) {y₀ : β} (hy₀ : Tendsto y l (𝓝 y₀)) :
    y₀ in f x₀ := by
  by_contra
obtain ⟨s, hs, t, ht, hst⟩ := Filter.disjoint_iff.mp RegularSpace.regular hf_closed this
  suffices existsᶠ n in l, y n in s by
    apply this
    filter_upwards [hy₀ ht] with n hn hyn
    exact hst.notMem_of_mem_left hyn hn
  apply hy.mp
  filter_upwards [hx (hf s hs)] with n hn hyn
  simp only [← subset_interior_iff_mem_nhdsSet, preimage_ofPred_eq, mem_ofPred_eq] at hn
exact interior_subset hn hyn

/--
lemma `LowerHemicontinuousAt.of_sequences` / 引理 `LowerHemicontinuousAt.of_sequences`

English:
lemma LowerHemicontinuousAt.of_sequences
  statement: {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
  proof: by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨y₀, hy₀f, hy₀U⟩
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨x, hx, hxU⟩ := exists_seq_forall_of_frequently hc
  obtain ⟨y, hy_mem, hy_lim⟩ := h x hx y₀ hy₀f
  obtain ⟨n, hn⟩ := (hy_lim.eventually (hU.mem_nhds hy₀U)).exists
  exact hxU

中文:
引理 LowerHemicontinuousAt.of_sequences
  结论: {x₀ : α} [(𝓝 x₀).是余untablyGenerated]
  证明: by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨y₀, hy₀f, hy₀U⟩
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨x, hx, hxU⟩ := exists_seq_forall_of_frequently hc
  obtain ⟨y, hy_mem, hy_lim⟩ := h x hx y₀ hy₀f
  obtain ⟨n, hn⟩ := (hy_lim.eventually (hU.mem_nhds hy₀U)).exists
  exact hxU

Depends on / 依赖: Filter, Filter.not_eventually, eventually, exists_seq_forall_of_frequently, hU.mem_nhds, hy_lim, hy_lim.eventually, hy_mem, lowerHemicontinuousAt_iff, mem_nhds, not_eventually
-/
lemma LowerHemicontinuousAt.of_sequences {x₀ : α} [(𝓝 x₀).IsCountablyGenerated]
    (h : forall x : Nat -> α, Tendsto x atTop (𝓝 x₀) ->
      forall y₀ in f x₀, exists y : Nat -> β, (forall n, y n in f (x n)) ∧ Tendsto y atTop (𝓝 y₀)) :
    LowerHemicontinuousAt f x₀ := by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨y₀, hy₀f, hy₀U⟩
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨x, hx, hxU⟩ := exists_seq_forall_of_frequently hc
  obtain ⟨y, hy_mem, hy_lim⟩ := h x hx y₀ hy₀f
  obtain ⟨n, hn⟩ := (hy_lim.eventually (hU.mem_nhds hy₀U)).exists
  exact hxU n ⟨y n, hy_mem n, hn⟩

/--
lemma `LowerHemicontinuousAt.exists_seq_tendsto` / 引理 `LowerHemicontinuousAt.exists_seq_tendsto`

English:
lemma LowerHemicontinuousAt.exists_seq_tendsto
  statement: {x₀ : α} (hf : LowerHemicontinuousAt f x₀)
  proof: by
  classical
  obtain ⟨U, hU, hUbasis⟩ := (nhds_basis_opens y₀).exists_antitone_subbasis
  have hev (k) : forallᶠ n in atTop, (f (x n) inter U k).Nonempty :=
hx.eventually (lowerHemicontinuousAt_iff.mp hf) (U k) (hU k).2 ⟨y₀, hy₀, (hU k).1⟩
  -- For each `n`, find the largest `k ≤ n` where `U k` i

中文:
引理 LowerHemicontinuousAt.存在_seq_tendsto
  结论: {x₀ : α} (hf : LowerHemicontinuousAt f x₀)
  证明: by
  classical
  obtain ⟨U, hU, hUbasis⟩ := (nhds_basis_opens y₀).exists_antitone_subbasis
  have hev (k) : forallᶠ n in atTop, (f (x n) inter U k).Nonempty :=
hx.eventually (lowerHemicontinuousAt_iff.mp hf) (U k) (hU k).2 ⟨y₀, hy₀, (hU k).1⟩
  -- For each `n`, find the largest `k ≤ n` where `U k` i

Depends on / 依赖: Nonempty, classical, eventually, exists_antitone_subbasis, hUbasis, hx.eventually, lowerHemicontinuousAt_iff, lowerHemicontinuousAt_iff.mp, nhds_basis_opens
-/
lemma LowerHemicontinuousAt.exists_seq_tendsto {x₀ : α} (hf : LowerHemicontinuousAt f x₀)
    {x : Nat -> α} (hx : Tendsto x atTop (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ in f x₀)
    [(𝓝 y₀).IsCountablyGenerated] :
    exists y : Nat -> β, (forallᶠ n in atTop, y n in f (x n)) ∧ Tendsto y atTop (𝓝 y₀) := by
  classical
  obtain ⟨U, hU, hUbasis⟩ := (nhds_basis_opens y₀).exists_antitone_subbasis
  have hev (k) : forallᶠ n in atTop, (f (x n) inter U k).Nonempty :=
hx.eventually (lowerHemicontinuousAt_iff.mp hf) (U k) (hU k).2 ⟨y₀, hy₀, (hU k).1⟩
  -- For each `n`, find the largest `k ≤ n` where `U k` intersects `f (x n)`.
  let g : Nat -> Nat := fun n => Nat.findGreatest (fun k => (f (x n) inter U k).Nonempty) n
  have key (n k) (hkn : k <= n) (hk : (f (x n) inter U k).Nonempty) : (f (x n) inter U (g n)).Nonempty :=
    Nat.findGreatest_spec (P := fun k => (f (x n) inter U k).Nonempty) hkn hk
  -- Define `y n` to be some element of `f (x n) ∩ U (g n)` (or be arbitrary)
  let y : Nat -> β := fun n => if h : (f (x n) inter U (g n)).Nonempty then h.some else y₀
  have hy (n) (h : (f (x n) inter U (g n)).Nonempty) : y n in f (x n) inter U (g n) := by
    simpa only [y, dif_pos h] using h.some_mem
  refine ⟨y, (hev 0).mono (by grind), ?_⟩
  -- Have to show for all `k`, eventually, all `y n ∈ U k`.
  rw [hUbasis.tendsto_right_iff]
  intro k _
  filter_upwards [hev k, eventually_ge_atTop k] with n hk hkn
  exact hUbasis.antitone (Nat.le_findGreatest hkn hk) (hy n (key n k hkn hk)).2

/--
lemma `LowerHemicontinuousAt.exists_subseq_tendsto` / 引理 `LowerHemicontinuousAt.exists_subseq_tendsto`

English:
lemma LowerHemicontinuousAt.exists_subseq_tendsto
  statement: {ι : Type*} {l : Filter ι} [l.NeBot]
  proof: by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto l
  obtain ⟨y, hy_mem, hy_lim⟩ := hf.exists_seq_tendsto (hx.comp hu) hy₀
  exact ⟨u, y, hu, hy_mem, hy_lim⟩

中文:
引理 LowerHemicontinuousAt.存在_subseq_tendsto
  结论: {ι : 类型} {l : 滤子 ι} [l.NeBot]
  证明: by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto l
  obtain ⟨y, hy_mem, hy_lim⟩ := hf.exists_seq_tendsto (hx.comp hu) hy₀
  exact ⟨u, y, hu, hy_mem, hy_lim⟩

Depends on / 依赖: Filter, Filter.exists_seq_tendsto, exists_seq_tendsto, hf.exists_seq_tendsto, hx.comp, hy_lim, hy_mem
-/
lemma LowerHemicontinuousAt.exists_subseq_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    [l.IsCountablyGenerated] {x₀ : α} (hf : LowerHemicontinuousAt f x₀) {x : ι -> α}
    (hx : Tendsto x l (𝓝 x₀)) {y₀ : β} (hy₀ : y₀ in f x₀) [(𝓝 y₀).IsCountablyGenerated] :
    exists (u : Nat -> ι) (y : Nat -> β), Tendsto u atTop l ∧
      (forallᶠ k in atTop, y k in f (x (u k))) ∧ Tendsto y atTop (𝓝 y₀) := by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto l
  obtain ⟨y, hy_mem, hy_lim⟩ := hf.exists_seq_tendsto (hx.comp hu) hy₀
  exact ⟨u, y, hu, hy_mem, hy_lim⟩



end facts

/-! ### Open lower sections -/

/--
lemma `hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl` / 引理 `hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl`

English:
lemma hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl
  proof: by
  have h (b : β) : (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b in f x} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff]
  simp_rw [h, hasOpenLowerSections_iff_isOpen]

中文:
引理 hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl
  证明: by
  have h (b : β) : (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b in f x} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff]
  simp_rw [h, hasOpenLowerSections_iff_isOpen]

Depends on / 依赖: Set.ext_iff, Set.mem_compl_iff, ext_iff, hasOpenLowerSections_iff_isOpen, mem_compl_iff, simp_rw
-/
lemma hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl :
    HasOpenLowerSections f ↔ forall b, IsOpen (f ⁻¹' Iic {b}ᶜ)ᶜ := by
  have h (b : β) : (f ⁻¹' (Iic {b}ᶜ))ᶜ = {x | b in f x} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff]
  simp_rw [h, hasOpenLowerSections_iff_isOpen]

/--
lemma `hasOpenLowerSections_iff_isClosed_preimage_Iic` / 引理 `hasOpenLowerSections_iff_isClosed_preimage_Iic`

English:
lemma hasOpenLowerSections_iff_isClosed_preimage_Iic
  proof: by
  simp_rw [← isOpen_compl_iff]
  exact hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl

中文:
引理 hasOpenLowerSections_iff_isClosed_preimage_Iic
  证明: by
  simp_rw [← isOpen_compl_iff]
  exact hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl

Depends on / 依赖: hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl, isOpen_compl_iff, simp_rw
-/
lemma hasOpenLowerSections_iff_isClosed_preimage_Iic :
    HasOpenLowerSections f ↔ forall b, IsClosed (f ⁻¹' Iic {b}ᶜ) := by
  simp_rw [← isOpen_compl_iff]
  exact hasOpenLowerSections_iff_isOpen_compl_preimage_Iic_compl

/-! ### Open Graphs -/

/--
lemma `LowerHemicontinuous.inter_hasOpenCGraph` / 引理 `LowerHemicontinuous.inter_hasOpenCGraph`

English:
lemma LowerHemicontinuous.inter_hasOpenCGraph
  statement: [TopologicalSpace β] {f g : α -> Set β}
  proof: by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg) x y hyg
  refine ⟨U inter {x' | (f x' inter (t inter V)).Nonempty}, ?_, hU.inter (hf _ 

中文:
引理 LowerHemicontinuous.inter_hasOpenCGraph
  结论: [拓扑空间 β] {f g : α -> 集合 β}
  证明: by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg) x y hyg
  refine ⟨U inter {x' | (f x' inter (t inter V)).Nonempty}, ?_, hU.inter (hf _ 

Depends on / 依赖: Nonempty, Set.mk_mem_prod, hU.inter, ht.inter, isOpen_iff_forall_mem_open, isOpen_prod_iff, isOpen_prod_iff.mp, lowerHemicontinuous_iff_isOpen_inter_nonempty, mk_mem_prod, simp_rw
-/
lemma LowerHemicontinuous.inter_hasOpenCGraph [TopologicalSpace β] {f g : α -> Set β}
    (hf : LowerHemicontinuous f) (hg : HasOpenCGraph g) :
    LowerHemicontinuous (fun x => f x inter g x) := by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg) x y hyg
  refine ⟨U inter {x' | (f x' inter (t inter V)).Nonempty}, ?_, hU.inter (hf _ (ht.inter hV)),
      ⟨hxU, y, hyf, hyt, hyV⟩⟩
  intro x' ⟨hx'U, z, hzf, hzt, hzV⟩
  exact ⟨z, ⟨hzf, hUV (Set.mk_mem_prod hx'U hzV)⟩, hzt⟩

/-! ### Uniform Limits

Like continuity, hemicontinuity is preserved under certain uniform limits, where the uniformity on
the target `Set β` is the Hausdorff uniformity. In this section, we prove this result for both
lower hemicontinuous and upper hemicontinuous limits.
-/

section limits

variable {ι : Type*} {F : ι -> α -> Set β} {l : Filter ι} [NeBot l]
variable [UniformSpace β]
open UniformSpace
attribute [local instance] UniformSpace.hausdorff

/--
theorem `TendstoUniformlyOn.lowerHemicontinuousOn` / 定理 `TendstoUniformlyOn.lowerHemicontinuousOn`

English:
theorem TendstoUniformlyOn.lowerHemicontinuousOn
  statement: (htendsto : TendstoUniformlyOn F f l s)
  proof: by
  rw [lowerHemicontinuousOn_iff]
  intro x₀ hx₀s
  rw [lowerHemicontinuousWithinAt_iff]
  intro V hV ⟨y₀, hy₀f, hy₀V⟩
  -- Obtain entourages W, U ∈ 𝓤 β with U ○ U ○ U ⊆ W
  obtain ⟨W, hW, hWsub⟩ := UniformSpace.mem_nhds_iff.mp (hV.mem_nhds hy₀V)
  obtain ⟨U₁, hU₁, hU₁sym, hU₁comp⟩ := comp_symm_me

中文:
定理 TendstoUniformlyOn.lowerHemicontinuousOn
  结论: (htendsto : TendstoUniformlyOn F f l s)
  证明: by
  rw [lowerHemicontinuousOn_iff]
  intro x₀ hx₀s
  rw [lowerHemicontinuousWithinAt_iff]
  intro V hV ⟨y₀, hy₀f, hy₀V⟩
  -- Obtain entourages W, U ∈ 𝓤 β with U ○ U ○ U ⊆ W
  obtain ⟨W, hW, hWsub⟩ := UniformSpace.mem_nhds_iff.mp (hV.mem_nhds hy₀V)
  obtain ⟨U₁, hU₁, hU₁sym, hU₁comp⟩ := comp_symm_me

Depends on / 依赖: lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff
-/
theorem TendstoUniformlyOn.lowerHemicontinuousOn (htendsto : TendstoUniformlyOn F f l s)
    (hF : forall n, LowerHemicontinuousOn (F n) s) : LowerHemicontinuousOn f s := by
  rw [lowerHemicontinuousOn_iff]
  intro x₀ hx₀s
  rw [lowerHemicontinuousWithinAt_iff]
  intro V hV ⟨y₀, hy₀f, hy₀V⟩
  -- Obtain entourages W, U ∈ 𝓤 β with U ○ U ○ U ⊆ W
  obtain ⟨W, hW, hWsub⟩ := UniformSpace.mem_nhds_iff.mp (hV.mem_nhds hy₀V)
  obtain ⟨U₁, hU₁, hU₁sym, hU₁comp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U, hU, hUsym, hUcomp⟩ := comp_symm_mem_uniformity_sets hU₁
  have hU_le_U₁ : U subseteq U₁ := fun _p hp => hUcomp ⟨_, refl_mem_uniformity hU, hp⟩
  -- Eventually, ⟨f x, F N x⟩ ∈ hausdorffEntourage U for all x ∈ s
  have hHU : hausdorffEntourage U in @uniformity (Set β) (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U, hU, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U) hHU).exists
  -- In which case, ⟨y₀, z₀⟩ ∈ U for some z₀ ∈ F N x₀
  obtain ⟨z₀, hz₀FN, hz₀y₀⟩ :=
    ((mem_hausdorffEntourage U (f x₀) (F N x₀)).mp (hN x₀ hx₀s)).1 hy₀f
  -- By lower hemicontinuity, a ball around z₀ intersects all x in a neighborhood of x₀
  obtain ⟨U', ⟨hU'mem, hU'open⟩, hU'sub⟩ := uniformity_hasBasis_open.mem_iff.mp hU
  have hmeet₀ : (F N x₀ inter ball z₀ U').Nonempty := ⟨z₀, hz₀FN, mem_ball_self z₀ hU'mem⟩
  have hSmeet : forallᶠ x in 𝓝[s] x₀, (F N x inter ball z₀ U').Nonempty :=
    lowerHemicontinuousWithinAt_iff.mp (hF _ _ hx₀s) _ (isOpen_ball _ hU'open) hmeet₀
  filter_upwards [hSmeet, self_mem_nhdsWithin] with x ⟨w, hwFN, hwball⟩ hx_s
  obtain ⟨v, hvf, hvw⟩ := ((mem_hausdorffEntourage U (f x) (F N x)).mp (hN x hx_s)).2 hwFN
exact ⟨v, hvf, hWsub hU₁comp
    ⟨w, hUcomp ⟨z₀, hz₀y₀, hU'sub hwball⟩, hU_le_U₁ (hUsym.symm _ _ hvw)⟩⟩

/--
theorem `TendstoUniformlyOn.upperHemicontinuousOn` / 定理 `TendstoUniformlyOn.upperHemicontinuousOn`

English:
theorem TendstoUniformlyOn.upperHemicontinuousOn
  statement: (htendsto : TendstoUniformlyOn F f l s)
  proof: by
  -- A function `f` is upper hemicontinuous at `x₀` if for all open `u` with `f x₀ ⊆ u`, then
  -- `f x ⊆ u` for all `x` near `x₀`
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀s u hu hx₀u
  -- Find an open entourage `U` such that `U ○ U.symm ⊆ u`
  obtain ⟨W, hW, _, hWu⟩ := lebesg

中文:
定理 TendstoUniformlyOn.upperHemicontinuousOn
  结论: (htendsto : TendstoUniformlyOn F f l s)
  证明: by
  -- A function `f` is upper hemicontinuous at `x₀` if for all open `u` with `f x₀ ⊆ u`, then
  -- `f x ⊆ u` for all `x` near `x₀`
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀s u hu hx₀u
  -- Find an open entourage `U` such that `U ○ U.symm ⊆ u`
  obtain ⟨W, hW, _, hWu⟩ := lebesg
-/
theorem TendstoUniformlyOn.upperHemicontinuousOn (htendsto : TendstoUniformlyOn F f l s)
      (hF : forall n, UpperHemicontinuousOn (F n) s) (hf_compact : forall x in s, IsCompact (f x)) :
    UpperHemicontinuousOn f s := by
  -- A function `f` is upper hemicontinuous at `x₀` if for all open `u` with `f x₀ ⊆ u`, then
  -- `f x ⊆ u` for all `x` near `x₀`
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀s u hu hx₀u
  -- Find an open entourage `U` such that `U ○ U.symm ⊆ u`
  obtain ⟨W, hW, _, hWu⟩ := lebesgue_number_of_compact_open (hf_compact x₀ hx₀s) hu hx₀u
  obtain ⟨V, hV, hVsym, hVcomp⟩ := comp_symm_mem_uniformity_sets hW
  obtain ⟨U, ⟨hUmem, hUopen⟩, hUsub⟩ := uniformity_hasBasis_open.mem_iff.mp hV
  -- Then choose a sufficiently large `N` such that `⟨f x, F N x⟩ ∈ hausdorffEntourage U`
  -- for all `x ∈ s`
  have hHU : hausdorffEntourage U in @uniformity _ (UniformSpace.hausdorff (α := β)) :=
    (mem_lift'_sets monotone_hausdorffEntourage).mpr ⟨U, hUmem, le_refl _⟩
  obtain ⟨N, hN⟩ := (htendsto (hausdorffEntourage U) hHU).exists
  have hFN_image : F N x₀ subseteq U.image (f x₀) := ((mem_hausdorffEntourage ..).mp (hN x₀ hx₀s)).2
  -- Upper hemicontinuity implies `F N x ⊆ U.image (f x₀)` for `x` near `x₀`
  simp_rw [upperHemicontinuousOn_iff] at hF
  have hFN_uhc : forallᶠ x in 𝓝[s] x₀, F N x subseteq U.image (f x₀) :=
    (hF N x₀ hx₀s).forall_isOpen _ hUopen.relImage hFN_image
  -- For such a nearby `x`, show `f x ⊆ u` by taking `y ∈ f x`,
  filter_upwards [hFN_uhc, self_mem_nhdsWithin] with x hFNx hx_s
  intro y hy
  -- finding a `z ∈ F N x` such that `(y, z) ∈ U` and then some `y₀ ∈ f x₀` such that `⟨y₀, z⟩ ∈ U`
  obtain ⟨z, hzFN, hyz⟩ := ((mem_hausdorffEntourage U (f x) (F N x)).mp (hN x hx_s)).1 hy
  obtain ⟨y₀, hy₀f, hy₀z⟩ := hFNx hzFN
  -- then use that `U ○ U.symm ⊆ u` to conclude
  exact hWu y₀ hy₀f (hVcomp ⟨z, hUsub hy₀z, hVsym.symm _ _ (hUsub hyz)⟩)

/--
theorem `TendstoUniformly.lowerHemicontinuous` / 定理 `TendstoUniformly.lowerHemicontinuous`

English:
theorem TendstoUniformly.lowerHemicontinuous
  statement: (htendsto : TendstoUniformly F f l)
  proof: by
  rw [← lowerHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.lowerHemicontinuousOn (fun n => (hF n).lowerHemicontinuousOn _)

中文:
定理 TendstoUniformly.lowerHemicontinuous
  结论: (htendsto : TendstoUniformly F f l)
  证明: by
  rw [← lowerHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.lowerHemicontinuousOn (fun n => (hF n).lowerHemicontinuousOn _)

Depends on / 依赖: htendsto, htendsto.tendstoUniformlyOn.lowerHemicontinuousOn, lowerHemicontinuousOn, lowerHemicontinuousOn_univ_iff, tendstoUniformlyOn
-/
theorem TendstoUniformly.lowerHemicontinuous (htendsto : TendstoUniformly F f l)
    (hF : forall n, LowerHemicontinuous (F n)) : LowerHemicontinuous f := by
  rw [← lowerHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.lowerHemicontinuousOn (fun n => (hF n).lowerHemicontinuousOn _)

/--
theorem `TendstoUniformly.upperHemicontinuous` / 定理 `TendstoUniformly.upperHemicontinuous`

English:
theorem TendstoUniformly.upperHemicontinuous
  statement: (htendsto : TendstoUniformly F f l)
  proof: by
  rw [← upperHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.upperHemicontinuousOn
    (fun n => (hF n).upperHemicontinuousOn _) (fun x _ => hf_compact x)

中文:
定理 TendstoUniformly.upperHemicontinuous
  结论: (htendsto : TendstoUniformly F f l)
  证明: by
  rw [← upperHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.upperHemicontinuousOn
    (fun n => (hF n).upperHemicontinuousOn _) (fun x _ => hf_compact x)

Depends on / 依赖: hf_compact, htendsto, htendsto.tendstoUniformlyOn.upperHemicontinuousOn, tendstoUniformlyOn, upperHemicontinuousOn, upperHemicontinuousOn_univ_iff
-/
theorem TendstoUniformly.upperHemicontinuous (htendsto : TendstoUniformly F f l)
    (hF : forall n, UpperHemicontinuous (F n)) (hf_compact : forall x, IsCompact (f x)) :
    UpperHemicontinuous f := by
  rw [← upperHemicontinuousOn_univ_iff]
  exact htendsto.tendstoUniformlyOn.upperHemicontinuousOn
    (fun n => (hF n).upperHemicontinuousOn _) (fun x _ => hf_compact x)

end limits
