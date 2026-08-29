/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Totally Bounded sets and Convex Hulls

## Main statements

- `totallyBounded_convexHull`: The convex hull of a totally bounded set is totally bounded.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

convex, totally bounded
-/

public section

open Set Pointwise

variable {E : Type*} {s : Set E}
variable [AddCommGroup E] [Module Real E]
variable [UniformSpace E] [IsUniformAddGroup E] [LocallyConvexSpace Real E] [ContinuousSMul Real E]

/--
lemma `TotallyBounded.convexHull` / 引理 `TotallyBounded.convexHull`

English:
lemma TotallyBounded.convexHull
  given: (hs : TotallyBounded s)
  proof: by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at ⊢ hs
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, hV₁,hV₂, hV₃⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero Real E).mp ‹_› W hW₁
  obtain ⟨t, htf, hts⟩ := hs _ hV₁
  obtain ⟨t', htf', hts'⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (htf.isCompact_convexHull Real).totallyBounded _ hV₁
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  grw [hts, convexHull_add_subset, hV₂.convexHull_eq, hts', add_assoc, hV₃, add_subset_iff.mpr hW₂]

中文:
引理 全有界.convexHull
  条件: (hs : 全有界 s)
  证明: by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at ⊢ hs
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, hV₁,hV₂, hV₃⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero Real E).mp ‹_› W hW₁
  obtain ⟨t, htf, hts⟩ := hs _ hV₁
  obtain ⟨t', htf', hts'⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (htf.isCompact_convexHull Real).totallyBounded _ hV₁
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  grw [hts, convexHull_add_subset, hV₂.convexHull_eq, hts', add_assoc, hV₃, add_subset_iff.mpr hW₂]
-/
protected lemma TotallyBounded.convexHull (hs : TotallyBounded s) :
    TotallyBounded (convexHull Real s) := by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at ⊢ hs
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, hV₁,hV₂, hV₃⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero Real E).mp ‹_› W hW₁
  obtain ⟨t, htf, hts⟩ := hs _ hV₁
  obtain ⟨t', htf', hts'⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (htf.isCompact_convexHull Real).totallyBounded _ hV₁
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  grw [hts, convexHull_add_subset, hV₂.convexHull_eq, hts', add_assoc, hV₃, add_subset_iff.mpr hW₂]

/--
lemma `totallyBounded_convexHull` / 引理 `totallyBounded_convexHull`

English:
lemma totallyBounded_convexHull
  statement: TotallyBounded (convexHull Real s) ↔ TotallyBounded s where
  proof: .subset subset_convexHull ..
  mpr := .convexHull

中文:
引理 totallyBounded_convexHull
  结论: 全有界 (convexHull 实数 s) ↔ 全有界 s where
  证明: .subset subset_convexHull ..
  mpr := .convexHull
-/
@[simp] lemma totallyBounded_convexHull : TotallyBounded (convexHull Real s) ↔ TotallyBounded s where
mp := .subset subset_convexHull ..
  mpr := .convexHull
