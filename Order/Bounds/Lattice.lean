/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Lattice.Image

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib/Data/Set/Lattice.lean`.

-/

public section

variable {α : Type*} [Preorder α] {ι : Sort*} {s : ι -> Set α}

open Set

@[to_dual]
/--
theorem `gc_upperBounds_lowerBounds` / 定理 `gc_upperBounds_lowerBounds`

English:
theorem gc_upperBounds_lowerBounds
  statement: GaloisConnection
  proof: by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T => forall₂_comm

@[to_dual (attr := simp)]

中文:
定理 gc_upperBounds_lowerBounds
  结论: GaloisConnection
  证明: by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T => forall₂_comm

@[to_dual (attr := simp)]

Depends on / 依赖: GaloisConnection, mem_lowerBounds, mem_upperBounds, subset_def
-/
theorem gc_upperBounds_lowerBounds : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α -> (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ -> Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T => forall₂_comm

@[to_dual (attr := simp)]
/--
theorem `upperBounds_iUnion` / 定理 `upperBounds_iUnion`

English:
theorem upperBounds_iUnion
  proof: gc_upperBounds_lowerBounds.l_iSup

@[to_dual]

中文:
定理 upperBounds_iUnion
  证明: gc_upperBounds_lowerBounds.l_iSup

@[to_dual]

Depends on / 依赖: gc_upperBounds_lowerBounds, gc_upperBounds_lowerBounds.l_iSup, l_iSup
-/
theorem upperBounds_iUnion :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i) :=
  gc_upperBounds_lowerBounds.l_iSup

@[to_dual]
/--
theorem `isLUB_iUnion_iff_of_isLUB` / 定理 `isLUB_iUnion_iff_of_isLUB`

English:
theorem isLUB_iUnion_iff_of_isLUB
  given: {u : ι -> α} (hs : forall i, IsLUB (s i) (u i)) (c : α)
  proof: by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

@[deprecated isGLB_iUnion_iff_of_isGLB (since := "2026-06-04")]

中文:
定理 isLUB_iUnion_iff_of_isLUB
  条件: {u : ι -> α} (hs : 对任意 i, IsLUB (s i) (u i)) (c : α)
  证明: by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

@[deprecated isGLB_iUnion_iff_of_isGLB (since := "2026-06-04")]

Depends on / 依赖: isLUB_congr, range_eq_iUnion, simp_rw, upperBounds_eq, upperBounds_iUnion, upperBounds_singleton
-/
theorem isLUB_iUnion_iff_of_isLUB {u : ι -> α} (hs : forall i, IsLUB (s i) (u i)) (c : α) :
    IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) c := by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

@[deprecated isGLB_iUnion_iff_of_isGLB (since := "2026-06-04")]
/--
theorem `isGLB_iUnion_iff_of_isLUB` / 定理 `isGLB_iUnion_iff_of_isLUB`

English:
theorem isGLB_iUnion_iff_of_isLUB
  given: {u : ι -> α} (hs : forall i, IsGLB (s i) (u i)) (c : α)
  proof: by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, (hs _).lowerBounds_eq]

中文:
定理 isGLB_iUnion_iff_of_isLUB
  条件: {u : ι -> α} (hs : 对任意 i, IsGLB (s i) (u i)) (c : α)
  证明: by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, (hs _).lowerBounds_eq]

Depends on / 依赖: isGLB_congr, lowerBounds_eq, lowerBounds_iUnion, lowerBounds_singleton, range_eq_iUnion, simp_rw
-/
theorem isGLB_iUnion_iff_of_isLUB {u : ι -> α} (hs : forall i, IsGLB (s i) (u i)) (c : α) :
    IsGLB (Set.range u) c ↔ IsGLB (⋃ i, s i) c := by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, (hs _).lowerBounds_eq]
