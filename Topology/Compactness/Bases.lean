/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact

/-!
# Topological bases in compact sets and compact spaces
-/

public section

open Set TopologicalSpace

variable {X ι : Type*} [TopologicalSpace X]

/--
lemma `eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open` / 引理 `eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open`

English:
lemma eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
  statement: (b : ι -> Set X)
  proof: by
  obtain ⟨Y, f, e, hf⟩ := hb.open_eq_iUnion hUo
  choose f' hf' using hf
  have : b ∘ f' = f := funext hf'
  subst this
  obtain ⟨t, ht⟩ :=
    hUc.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
  classical
  refine ⟨t.image f', Set.toFinite _, le_antisymm ?

中文:
引理 eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
  结论: (b : ι -> 集合 X)
  证明: by
  obtain ⟨Y, f, e, hf⟩ := hb.open_eq_iUnion hUo
  choose f' hf' using hf
  have : b ∘ f' = f := funext hf'
  subst this
  obtain ⟨t, ht⟩ :=
    hUc.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
  classical
  refine ⟨t.image f', Set.toFinite _, le_antisymm ?

Depends on / 依赖: Finset, Finset.mem_imag, Set.Subset.trans, Set.iUnion, Set.iUnion_subset_iff, Set.mem_range_self, Set.toFinite, Subset, classical, elim_finite_subcover, hUc.elim_finite_subcover, hb.isOpen, hb.open_eq_iUnion, iUnion_subset_iff, isOpen, le_antisymm, mem_imag, mem_range_self, open_eq_iUnion, t.image
-/
lemma eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open (b : ι -> Set X)
    (hb : IsTopologicalBasis (Set.range b)) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    exists s : Set ι, s.Finite ∧ U = ⋃ i in s, b i := by
  obtain ⟨Y, f, e, hf⟩ := hb.open_eq_iUnion hUo
  choose f' hf' using hf
  have : b ∘ f' = f := funext hf'
  subst this
  obtain ⟨t, ht⟩ :=
    hUc.elim_finite_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) (by rw [e])
  classical
  refine ⟨t.image f', Set.toFinite _, le_antisymm ?_ ?_⟩
  · refine Set.Subset.trans ht ?_
    simp only [Set.iUnion_subset_iff]
    intro i hi
    simpa using subset_iUnion₂ (s := fun i _ => b (f' i)) i hi
  · apply Set.iUnion₂_subset
    rintro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    rw [e]
    exact Set.subset_iUnion (b ∘ f') j

/--
lemma `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open` / 引理 `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`

English:
lemma eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open
  statement: (b : Set (Set X))
  proof: by
  have hb' : b = range (fun i => i : b -> Set X) := by simp
  rw [hb'] at hb
  choose s hs hU using eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  have : Finite s := hs
  let _ : Fintype s := Fintype.ofFinite _
  use s.toFinset
  simp [hU]

中文:
引理 eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open
  结论: (b : 集合 (集合 X))
  证明: by
  have hb' : b = range (fun i => i : b -> Set X) := by simp
  rw [hb'] at hb
  choose s hs hU using eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  have : Finite s := hs
  let _ : Fintype s := Fintype.ofFinite _
  use s.toFinset
  simp [hU]

Depends on / 依赖: Finite, Fintype, Fintype.ofFinite, eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open, ofFinite, s.toFinset, toFinset
-/
lemma eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open (b : Set (Set X))
    (hb : IsTopologicalBasis b) (U : Set X) (hUc : IsCompact U) (hUo : IsOpen U) :
    exists s : Finset b, U = (s : Set b).sUnion := by
  have hb' : b = range (fun i => i : b -> Set X) := by simp
  rw [hb'] at hb
  choose s hs hU using eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  have : Finite s := hs
  let _ : Fintype s := Fintype.ofFinite _
  use s.toFinset
  simp [hU]

/--
theorem `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis` / 定理 `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis`

English:
theorem isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis
  statement: (b : ι -> Set X)
  proof: by
  constructor
  · exact fun ⟨h₁, h₂⟩ => eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U h₁ h₂
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

中文:
定理 isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis
  结论: (b : ι -> 集合 X)
  证明: by
  constructor
  · exact fun ⟨h₁, h₂⟩ => eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U h₁ h₂
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

Depends on / 依赖: Set.mem_range_self, eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open, hb.isOpen, hs.isCompact_biUnion, isCompact_biUnion, isOpen, isOpen_biUnion, mem_range_self
-/
theorem isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι -> Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : forall i, IsCompact (b i)) (U : Set X) :
    IsCompact U ∧ IsOpen U ↔ exists s : Set ι, s.Finite ∧ U = ⋃ i in s, b i := by
  constructor
  · exact fun ⟨h₁, h₂⟩ => eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U h₁ h₂
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isCompact_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)
