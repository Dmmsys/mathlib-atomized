/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definition of subcomplexes is in the file `Mathlib/Topology/CWComplex/Classical/Basic.lean`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

@[expose] public section

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.closedCell_subset_of_mem` / 引理 `RelCWComplex.Subcomplex.closedCell_subset_of_mem`

English:
lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem
  statement: [T2Space X] [RelCWComplex C D]
  proof: by
  rw [← closure_openCell_eq_closedCell]; rw [E.closed.closure_subset_iff]; rw [← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) => openCell (C := C) n j) ⟨i, hi⟩)

@[alias_in CWComplex.Subcomplex]

中文:
引理 RelCWComplex.子复形.closedCell_subset_of_mem
  结论: [T2空间 X] [RelCWComplex C D]
  证明: by
  rw [← closure_openCell_eq_closedCell]; rw [E.closed.closure_subset_iff]; rw [← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) => openCell (C := C) n j) ⟨i, hi⟩)

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: E.closed.closure_subset_iff, E.union, closed, closure_openCell_eq_closedCell, closure_subset_iff, openCell, subset_iUnion, subset_iUnion_of_subset, subset_union_of_subset_right
-/
lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : Nat} {i : cell C n} (hi : i in E.I n) :
    closedCell n i subseteq E := by
  rw [← closure_openCell_eq_closedCell]; rw [E.closed.closure_subset_iff]; rw [← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) => openCell (C := C) n j) ⟨i, hi⟩)

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.openCell_subset_of_mem` / 引理 `RelCWComplex.Subcomplex.openCell_subset_of_mem`

English:
lemma RelCWComplex.Subcomplex.openCell_subset_of_mem
  statement: [T2Space X] [RelCWComplex C D]
  proof: (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

@[alias_in CWComplex.Subcomplex]

中文:
引理 RelCWComplex.子复形.openCell_subset_of_mem
  结论: [T2空间 X] [RelCWComplex C D]
  证明: (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: closedCell_subset_of_mem, openCell_subset_closedCell
-/
lemma RelCWComplex.Subcomplex.openCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : Nat} {i : cell C n} (hi : i in E.I n) :
    openCell n i subseteq E :=
  (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.cellFrontier_subset_of_mem` / 引理 `RelCWComplex.Subcomplex.cellFrontier_subset_of_mem`

English:
lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem
  statement: [T2Space X] [RelCWComplex C D]
  proof: (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

中文:
引理 RelCWComplex.子复形.cellFrontier_subset_of_mem
  结论: [T2空间 X] [RelCWComplex C D]
  证明: (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

Depends on / 依赖: cellFrontier_subset_closedCell, closedCell_subset_of_mem
-/
lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : Nat} {i : cell C n} (hi : i in E.I n) :
    cellFrontier n i subseteq E :=
  (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

/--
lemma `RelCWComplex.Subcomplex.union_closedCell` / 引理 `RelCWComplex.Subcomplex.union_closedCell`

English:
lemma RelCWComplex.Subcomplex.union_closedCell
  given: [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
  proof: by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i => closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i => ?_
    exact openCell_subset_closedCell (C := C) n i

中文:
引理 RelCWComplex.子复形.union_closedCell
  条件: [T2空间 X] [RelCWComplex C D] (E : 子复形 C)
  证明: by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i => closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i => ?_
    exact openCell_subset_closedCell (C := C) n i

Depends on / 依赖: E.base_subset, E.union, base_subset, closedCell_subset_of_mem, openCell_subset_closedCell, subset_antisymm, union_subset, union_subset_union_right
-/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D union ⋃ (n : Nat) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i => closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i => ?_
    exact openCell_subset_closedCell (C := C) n i

/--
lemma `CWComplex.Subcomplex.union_closedCell` / 引理 `CWComplex.Subcomplex.union_closedCell`

English:
lemma CWComplex.Subcomplex.union_closedCell
  given: [T2Space X] [CWComplex C] (E : Subcomplex C)
  proof: (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

@[alias_in CWComplex.Subcomplex]

中文:
引理 CWComplex.子复形.union_closedCell
  条件: [T2空间 X] [CWComplex C] (E : 子复形 C)
  证明: (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

@[alias_in CWComplex.Subcomplex]
-/
lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : Nat) (j : E.I n), closedCell (C := C) n j = E :=
  (empty_union _).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem` / 引理 `RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem`

English:
lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem
  statement: [RelCWComplex C D]
  proof: by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ => disjoint_openCell_of_ne (by lia)⟩

中文:
引理 RelCWComplex.子复形.disjoint_openCell_subcomplex_of_not_mem
  结论: [RelCWComplex C D]
  证明: by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ => disjoint_openCell_of_ne (by lia)⟩

Depends on / 依赖: disjointBase, disjoint_iUnion_right, disjoint_openCell_of_ne, disjoint_union_right, simp_rw
-/
lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : Nat} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ => disjoint_openCell_of_ne (by lia)⟩

open scoped Classical in
/-- A subcomplex is again a CW complex. -/
@[simps]
/--
Instance `RelCWComplex.Subcomplex.instRelCWComplex` / 实例 `RelCWComplex.Subcomplex.instRelCWComplex`

English:
instance RelCWComplex.Subcomplex.instRelCWComplex
  signature: [T2Space X] [RelCWComplex C D]
  body: E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
.ne hne exact Function.injective_id.sigma_map (fun _ => Subtype.val_injective)
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m => Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j in E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x in (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
.notMem_of_mem_left hxj this exact E.disjoint_openCell_subcomplex_of_not_mem hj'
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j in E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E

中文:
实例 RelCWComplex.子复形.instRelCWComplex
  签名: [T2空间 X] [RelCWComplex C D]
  定义体: E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
.ne hne exact Function.injective_id.sigma_map (fun _ => Subtype.val_injective)
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m => Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j in E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x in (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
.notMem_of_mem_left hxj this exact E.disjoint_openCell_subcomplex_of_not_mem hj'
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j in E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E
-/
instance RelCWComplex.Subcomplex.instRelCWComplex [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) : RelCWComplex E D where
  cell n := E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
.ne hne exact Function.injective_id.sigma_map (fun _ => Subtype.val_injective)
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m => Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j in E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x in (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
.notMem_of_mem_left hxj this exact E.disjoint_openCell_subcomplex_of_not_mem hj'
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j in E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E

/--
Instance `CWComplex.Subcomplex.instCWComplex` / 实例 `CWComplex.Subcomplex.instCWComplex`

English:
instance CWComplex.Subcomplex.instCWComplex
  signature: [T2Space X] [CWComplex C] (E : Subcomplex C)
  body: RelCWComplex.toCWComplex (E : Set X)

@[simp]

中文:
实例 CWComplex.子复形.instCWComplex
  签名: [T2空间 X] [CWComplex C] (E : 子复形 C)
  定义体: RelCWComplex.toCWComplex (E : Set X)

@[simp]

Depends on / 依赖: RelCWComplex, RelCWComplex.toCWComplex, toCWComplex
-/
instance CWComplex.Subcomplex.instCWComplex [T2Space X] [CWComplex C] (E : Subcomplex C) :
    CWComplex (E : Set X) :=
  RelCWComplex.toCWComplex (E : Set X)

@[simp]
/--
lemma `CWComplex.Subcomplex.cell_def` / 引理 `CWComplex.Subcomplex.cell_def`

English:
lemma CWComplex.Subcomplex.cell_def
  statement: [T2Space X] [CWComplex C] (E : Subcomplex C)
  proof: rfl

@[simp]

中文:
引理 CWComplex.子复形.cell_def
  结论: [T2空间 X] [CWComplex C] (E : 子复形 C)
  证明: rfl

@[simp]
-/
lemma CWComplex.Subcomplex.cell_def [T2Space X] [CWComplex C] (E : Subcomplex C)
    (n : Nat) : cell (E : Set X) n = E.I (C := C) n :=
  rfl

@[simp]
/--
lemma `CWComplex.Subcomplex.map_def` / 引理 `CWComplex.Subcomplex.map_def`

English:
lemma CWComplex.Subcomplex.map_def
  statement: [T2Space X] [CWComplex C] (E : Subcomplex C) (n : Nat)
  proof: rfl

@[simp]

中文:
引理 CWComplex.子复形.map_def
  结论: [T2空间 X] [CWComplex C] (E : 子复形 C) (n : 自然数)
  证明: rfl

@[simp]
-/
lemma CWComplex.Subcomplex.map_def [T2Space X] [CWComplex C] (E : Subcomplex C) (n : Nat)
    (i : E.I n) : map (C := E) n i = map (C := C) n i :=
  rfl

@[simp]
/--
lemma `RelCWComplex.Subcomplex.openCell_eq` / 引理 `RelCWComplex.Subcomplex.openCell_eq`

English:
lemma RelCWComplex.Subcomplex.openCell_eq
  statement: [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : Nat)
  proof: by
  rfl

@[simp]

中文:
引理 RelCWComplex.子复形.openCell_eq
  结论: [T2空间 X] [RelCWComplex C D] (E : 子复形 C) (n : 自然数)
  证明: by
  rfl

@[simp]

Depends on / 依赖: openCell
-/
lemma RelCWComplex.Subcomplex.openCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : Nat)
    (i : E.I n) : openCell (C := E) n i = openCell n (i : cell C n) := by
  rfl

@[simp]
/--
lemma `RelCWComplex.Subcomplex.closedCell_eq` / 引理 `RelCWComplex.Subcomplex.closedCell_eq`

English:
lemma RelCWComplex.Subcomplex.closedCell_eq
  statement: [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
  proof: by
  rfl

@[simp]

中文:
引理 RelCWComplex.子复形.closedCell_eq
  结论: [T2空间 X] [RelCWComplex C D] (E : 子复形 C)
  证明: by
  rfl

@[simp]

Depends on / 依赖: closedCell
-/
lemma RelCWComplex.Subcomplex.closedCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : Nat) (i : E.I n) : closedCell (C := E) n i = closedCell n (i : cell C n) := by
  rfl

@[simp]
/--
lemma `RelCWComplex.Subcomplex.cellFrontier_eq` / 引理 `RelCWComplex.Subcomplex.cellFrontier_eq`

English:
lemma RelCWComplex.Subcomplex.cellFrontier_eq
  statement: [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
  proof: by
  rfl

@[alias_in CWComplex.Subcomplex]

中文:
引理 RelCWComplex.子复形.cellFrontier_eq
  结论: [T2空间 X] [RelCWComplex C D] (E : 子复形 C)
  证明: by
  rfl

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: cellFrontier
-/
lemma RelCWComplex.Subcomplex.cellFrontier_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : Nat) (i : E.I n) : cellFrontier (C := E) n i = cellFrontier n (i : cell C n) := by
  rfl

@[alias_in CWComplex.Subcomplex]
/--
Instance `RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType` / 实例 `RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType`

English:
instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType
  signature: [T2Space X]
  body: let _ := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

@[alias_in CWComplex.Subcomplex]

中文:
实例 RelCWComplex.子复形.finiteType_subcomplex_of_finiteType
  签名: [T2空间 X]
  定义体: let _ := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: FiniteType, FiniteType.finite_cell, Subtype, Subtype.finite, finite, finite_cell
-/
instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType [T2Space X]
    [RelCWComplex C D] [FiniteType C] (E : Subcomplex C) : FiniteType (E : Set X) where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

@[alias_in CWComplex.Subcomplex]
/--
Instance `RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional` / 实例 `RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional`

English:
instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
  body: by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

中文:
实例 RelCWComplex.子复形.finiteDimensional_subcomplex_of_finiteDimensional
  定义体: by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.eventually_isEmpty_cell, eventually_isEmpty_cell, filter_upwards, isEmpty_subtype
-/
instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

/-- A subcomplex of a finite CW complex is again finite. -/
@[alias_in CWComplex.Subcomplex]
/--
Instance `RelCWComplex.Subcomplex.finite_subcomplex_of_finite` / 实例 `RelCWComplex.Subcomplex.finite_subcomplex_of_finite`

English:
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite
  signature: [T2Space X] [RelCWComplex C D]
  body: finite_of_finiteDimensional_finiteType _

中文:
实例 RelCWComplex.子复形.finite_subcomplex_of_finite
  签名: [T2空间 X] [RelCWComplex C D]
  定义体: finite_of_finiteDimensional_finiteType _

Depends on / 依赖: finite_of_finiteDimensional_finiteType
-/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  finite_of_finiteDimensional_finiteType _

end Topology
