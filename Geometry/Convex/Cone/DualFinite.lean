/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Duals of finitely generated cones

This file defines the notion of dually finitely generated cones. A cone is dually finitely
generated (or `DualFG` for short) if it is the dual of a finite set, or equivalently, of a
finitely generated cone. In geometric terms, a cone is dually finitely generated if it can
be written as the intersection of finitely many halfspaces. This is also known as an H-cone.
This is the counterpart to `FG` (finitely generated) which states that the cone is the conic hull
of a finite set, or a V-cone.

In finite dimensional vector spaces, `FG` is equivalent to `DualFG` by the Minkowski-Weyl theorem.
In this case, V- and H-cones are known as polyhedral cones.

## Main declarations

- `PointedCone.DualFG` expresses that a cone is the dual of a finite set.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M ->ₗ[R] N ->ₗ[R] R}

variable (p) in
/--
Definition of `DualFG` / `DualFG` 的定义

English:
definition DualFG
  signature: (C : PointedCone R N)
  body: exists s : Finset M, dual p s = C

中文:
定义 DualFG
  签名: (C : PointedCone R N)
  定义体: exists s : Finset M, dual p s = C

Depends on / 依赖: Finset
-/
def DualFG (C : PointedCone R N) : Prop := exists s : Finset M, dual p s = C

/--
lemma `DualFG.top` / 引理 `DualFG.top`

English:
lemma DualFG.top
  statement: DualFG p ⊤
  proof: ⟨∅, by simp⟩

中文:
引理 DualFG.top
  结论: DualFG p ⊤
  证明: ⟨∅, by simp⟩
-/
@[simp] protected lemma DualFG.top : DualFG p ⊤ := ⟨∅, by simp⟩

/--
lemma `DualFG.exists_fg_dual` / 引理 `DualFG.exists_fg_dual`

English:
lemma DualFG.exists_fg_dual
  given: {C : PointedCone R N} (hC : C.DualFG p)
  proof: by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

中文:
引理 DualFG.exists_fg_dual
  条件: {C : PointedCone R N} (hC : C.DualFG p)
  证明: by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

Depends on / 依赖: Submodule, Submodule.fg_span, fg_span, finite_toSet, s.finite_toSet
-/
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    exists D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/--
lemma `DualFG.iff_exists_fg_dual` / 引理 `DualFG.iff_exists_fg_dual`

English:
lemma DualFG.iff_exists_fg_dual
  given: {C : PointedCone R N}
  proof: h.exists_fg_dual
  mpr := by
    rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    use s; simp

中文:
引理 DualFG.iff_exists_fg_dual
  条件: {C : PointedCone R N}
  证明: h.exists_fg_dual
  mpr := by
    rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    use s; simp

Depends on / 依赖: exists_fg_dual, h.exists_fg_dual
-/
lemma DualFG.iff_exists_fg_dual {C : PointedCone R N} :
    C.DualFG p ↔ exists D : PointedCone R M, D.FG ∧ dual p D = C where
  mp h := h.exists_fg_dual
  mpr := by
    rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    use s; simp

/--
lemma `DualFG.id` / 引理 `DualFG.id`

English:
lemma DualFG.id
  given: {C : PointedCone R N} (hC : C.DualFG p)
  statement: C.DualFG .id
  proof: by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

中文:
引理 DualFG.id
  条件: {C : PointedCone R N} (hC : C.DualFG p)
  结论: C.DualFG .id
  证明: by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

Depends on / 依赖: Finset, Finset.image, classical
-/
lemma DualFG.id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id := by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

variable (p) in
/--
lemma `DualFG.dual_of_finset` / 引理 `DualFG.dual_of_finset`

English:
lemma DualFG.dual_of_finset
  given: (s : Finset M)
  statement: (dual p s).DualFG p
  proof: by use s

中文:
引理 DualFG.dual_of_finset
  条件: (s : Finset M)
  结论: (dual p s).DualFG p
  证明: by use s
-/
lemma DualFG.dual_of_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/--
lemma `DualFG.dual_of_finite` / 引理 `DualFG.dual_of_finite`

English:
lemma DualFG.dual_of_finite
  given: {s : Set M} (hs : s.Finite)
  statement: (dual p s).DualFG p
  proof: by
  use hs.toFinset
  rw [Set.Finite.coe_toFinset]

中文:
引理 DualFG.dual_of_finite
  条件: {s : Set M} (hs : s.Finite)
  结论: (dual p s).DualFG p
  证明: by
  use hs.toFinset
  rw [Set.Finite.coe_toFinset]

Depends on / 依赖: Finite, Set.Finite.coe_toFinset, coe_toFinset, hs.toFinset, toFinset
-/
lemma DualFG.dual_of_finite {s : Set M} (hs : s.Finite) : (dual p s).DualFG p := by
  use hs.toFinset
  rw [Set.Finite.coe_toFinset]

variable (p) in
/--
lemma `DualFG.dual_of_fg` / 引理 `DualFG.dual_of_fg`

English:
lemma DualFG.dual_of_fg
  given: {C : PointedCone R M} (hC : C.FG)
  statement: (dual p C).DualFG p
  proof: by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_hull]

alias FG.dual_dualfg := DualFG.dual_of_fg

中文:
引理 DualFG.dual_of_fg
  条件: {C : PointedCone R M} (hC : C.FG)
  结论: (dual p C).DualFG p
  证明: by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_hull]

alias FG.dual_dualfg := DualFG.dual_of_fg

Depends on / 依赖: dual_hull
-/
lemma DualFG.dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_hull]

alias FG.dual_dualfg := DualFG.dual_of_fg

/--
lemma `DualFG.inf` / 引理 `DualFG.inf`

English:
lemma DualFG.inf
  given: {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p)
  proof: by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S union T; rw [Finset.coe_union, dual_union]

中文:
引理 DualFG.inf
  条件: {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p)
  证明: by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S union T; rw [Finset.coe_union, dual_union]

Depends on / 依赖: Finset, Finset.coe_union, classical, coe_union, dual_union
-/
lemma DualFG.inf {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S union T; rw [Finset.coe_union, dual_union]

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
/--
lemma `DualFG.dual_dual_flip` / 引理 `DualFG.dual_dual_flip`

English:
lemma DualFG.dual_dual_flip
  given: {C : PointedCone R N} (hC : C.DualFG p)
  proof: by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

中文:
引理 DualFG.dual_dual_flip
  条件: {C : PointedCone R N} (hC : C.DualFG p)
  证明: by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

Depends on / 依赖: dual_dual_flip_dual, exists_fg_dual, hDualFG
-/
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
/--
lemma `DualFG.dual_flip_dual` / 引理 `DualFG.dual_flip_dual`

English:
lemma DualFG.dual_flip_dual
  given: {C : PointedCone R M} (hC : C.DualFG p.flip)
  proof: hC.dual_dual_flip

中文:
引理 DualFG.dual_flip_dual
  条件: {C : PointedCone R M} (hC : C.DualFG p.flip)
  证明: hC.dual_dual_flip

Depends on / 依赖: dual_dual_flip, hC.dual_dual_flip
-/
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone
