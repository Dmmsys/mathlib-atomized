/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Continuity

/-!
# Polygons

This file defines polygons in affine spaces.
For the special case `n = 3`, an interconversion is provided with `Affine.Triangle`.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a type `P`.

-/

@[expose] public section

open Set

/--
Definition of `Polygon` / `Polygon` 的定义

English:
structure Polygon
  parameters: (P : Type*) (n : Nat)
  axioms and operations (1):
    - vertices : Fin n -> P

中文:
结构 Polygon
  参数: (P : 类型) (n : 自然数)
  公理与运算 (1 个):
    - vertices : Fin n -> P
-/
structure Polygon (P : Type*) (n : Nat) where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n -> P

namespace Polygon

variable {R V P : Type*} {n : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Polygon P n) (fun _ => Fin n -> P)
  body: Polygon.vertices

中文:
实例 :
  签名: CoeFun (Polygon P n) (fun _ => Fin n -> P)
  定义体: Polygon.vertices

Depends on / 依赖: Polygon, Polygon.vertices, vertices
-/
instance : CoeFun (Polygon P n) (fun _ => Fin n -> P) where
  coe := Polygon.vertices

/--
Definition of `HasNondegenerateEdges` / `HasNondegenerateEdges` 的定义

English:
definition HasNondegenerateEdges
  signature: (poly : Polygon P n)
  body: forall i : Fin n, poly i != poly (finRotate n i)

中文:
定义 HasNondegenerateEdges
  签名: (poly : Polygon P n)
  定义体: forall i : Fin n, poly i != poly (finRotate n i)

Depends on / 依赖: finRotate
-/
def HasNondegenerateEdges (poly : Polygon P n) : Prop :=
  forall i : Fin n, poly i != poly (finRotate n i)

/--
theorem `HasNondegenerateEdges.two_le` / 定理 `HasNondegenerateEdges.two_le`

English:
theorem HasNondegenerateEdges.two_le
  statement: [NeZero n] {poly : Polygon P n}
  proof: by
  by_contra! hlt
  interval_cases n
  · simp_all only [neZero_zero_iff_false]
  · exact h 0 (by simp)

中文:
定理 HasNondegenerateEdges.two_le
  结论: [NeZero n] {poly : Polygon P n}
  证明: by
  by_contra! hlt
  interval_cases n
  · simp_all only [neZero_zero_iff_false]
  · exact h 0 (by simp)

Depends on / 依赖: interval_cases, neZero_zero_iff_false
-/
theorem HasNondegenerateEdges.two_le [NeZero n] {poly : Polygon P n}
    (h : poly.HasNondegenerateEdges) : 2 <= n := by
  by_contra! hlt
  interval_cases n
  · simp_all only [neZero_zero_iff_false]
  · exact h 0 (by simp)

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/--
Definition of `edgePath` / `edgePath` 的定义

English:
definition edgePath
  signature: (poly : Polygon P n) (i : Fin n)
  body: AffineMap.lineMap (poly i) (poly (finRotate n i))

中文:
定义 edgePath
  签名: (poly : Polygon P n) (i : Fin n)
  定义体: AffineMap.lineMap (poly i) (poly (finRotate n i))

Depends on / 依赖: AffineMap, AffineMap.lineMap, finRotate, lineMap
-/
def edgePath (poly : Polygon P n) (i : Fin n) : R ->ᵃ[R] P :=
  AffineMap.lineMap (poly i) (poly (finRotate n i))

variable (R) in
/--
Definition of `edgeSet` / `edgeSet` 的定义

English:
definition edgeSet
  signature: [PartialOrder R] (poly : Polygon P n) (i : Fin n)
  body: affineSegment R (poly i) (poly (finRotate n i))

中文:
定义 edgeSet
  签名: [PartialOrder R] (poly : Polygon P n) (i : Fin n)
  定义体: affineSegment R (poly i) (poly (finRotate n i))

Depends on / 依赖: affineSegment, finRotate
-/
def edgeSet [PartialOrder R] (poly : Polygon P n) (i : Fin n) : Set P :=
  affineSegment R (poly i) (poly (finRotate n i))

variable (R) in
/--
theorem `edgeSet_eq_image_edgePath` / 定理 `edgeSet_eq_image_edgePath`

English:
theorem edgeSet_eq_image_edgePath
  given: [PartialOrder R] (poly : Polygon P n) (i : Fin n)
  proof: rfl

中文:
定理 edgeSet_eq_image_edgePath
  条件: [PartialOrder R] (poly : Polygon P n) (i : Fin n)
  证明: rfl
-/
theorem edgeSet_eq_image_edgePath [PartialOrder R] (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet R i = poly.edgePath R i '' Icc (0 : R) 1 := rfl

variable (R) in
/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: [PartialOrder R] (poly : Polygon P n)
  body: ⋃ i, poly.edgeSet R i

中文:
定义 boundary
  签名: [PartialOrder R] (poly : Polygon P n)
  定义体: ⋃ i, poly.edgeSet R i

Depends on / 依赖: edgeSet, poly.edgeSet
-/
def boundary [PartialOrder R] (poly : Polygon P n) : Set P :=
  ⋃ i, poly.edgeSet R i

variable (R) in
/--
Definition of `HasNondegenerateVertices` / `HasNondegenerateVertices` 的定义

English:
definition HasNondegenerateVertices
  signature: [NeZero n] (poly : Polygon P n)
  body: forall i : Fin n, AffineIndependent R ![poly i, poly (i + 1), poly (i + 2)]

中文:
定义 HasNondegenerateVertices
  签名: [NeZero n] (poly : Polygon P n)
  定义体: forall i : Fin n, AffineIndependent R ![poly i, poly (i + 1), poly (i + 2)]

Depends on / 依赖: AffineIndependent
-/
def HasNondegenerateVertices [NeZero n] (poly : Polygon P n) : Prop :=
  forall i : Fin n, AffineIndependent R ![poly i, poly (i + 1), poly (i + 2)]

/--
theorem `HasNondegenerateVertices.hasNondegenerateEdges` / 定理 `HasNondegenerateVertices.hasNondegenerateEdges`

English:
theorem HasNondegenerateVertices.hasNondegenerateEdges
  statement: [NeZero n] [Nontrivial R]
  proof: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro i
  simpa using (h i).injective.ne (by decide : (0 : Fin 3) != 1)

中文:
定理 HasNondegenerateVertices.hasNondegenerateEdges
  结论: [NeZero n] [Nontrivial R]
  证明: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro i
  simpa using (h i).injective.ne (by decide : (0 : Fin 3) != 1)

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, NeZero, NeZero.ne, exists_eq_succ_of_ne_zero, injective, injective.ne
-/
theorem HasNondegenerateVertices.hasNondegenerateEdges [NeZero n] [Nontrivial R]
    {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : poly.HasNondegenerateEdges := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro i
  simpa using (h i).injective.ne (by decide : (0 : Fin 3) != 1)

/--
theorem `HasNondegenerateVertices.three_le` / 定理 `HasNondegenerateVertices.three_le`

English:
theorem HasNondegenerateVertices.three_le
  statement: [NeZero n] [Nontrivial R] {poly : Polygon P n}
  proof: by
  have := h.hasNondegenerateEdges.two_le
  by_contra! hlt
  interval_cases n
  exact (h 0).injective.ne (by decide : (0 : Fin 3) != 2) (by simp)

中文:
定理 HasNondegenerateVertices.three_le
  结论: [NeZero n] [Nontrivial R] {poly : Polygon P n}
  证明: by
  have := h.hasNondegenerateEdges.two_le
  by_contra! hlt
  interval_cases n
  exact (h 0).injective.ne (by decide : (0 : Fin 3) != 2) (by simp)

Depends on / 依赖: h.hasNondegenerateEdges.two_le, hasNondegenerateEdges, injective, injective.ne, interval_cases, two_le
-/
theorem HasNondegenerateVertices.three_le [NeZero n] [Nontrivial R] {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : 3 <= n := by
  have := h.hasNondegenerateEdges.two_le
  by_contra! hlt
  interval_cases n
  exact (h 0).injective.ne (by decide : (0 : Fin 3) != 2) (by simp)

end Polygon

/-! ### Interconversion with `Affine.Triangle` -/

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/--
Definition of `toPolygon` / `toPolygon` 的定义

English:
definition toPolygon
  signature: : Affine.Triangle R P ↪ Polygon P 3 where
  body: ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    apply_fun Polygon.vertices at h
    simp_all

@[simp]

中文:
定义 toPolygon
  签名: : Affine.Triangle R P ↪ Polygon P 3 where
  定义体: ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    apply_fun Polygon.vertices at h
    simp_all

@[simp]

Depends on / 依赖: points, t.points
-/
def toPolygon : Affine.Triangle R P ↪ Polygon P 3 where
  toFun t := ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    apply_fun Polygon.vertices at h
    simp_all

@[simp]
/--
lemma `toPolygon_vertices` / 引理 `toPolygon_vertices`

English:
lemma toPolygon_vertices
  given: (t : Affine.Triangle R P)
  statement: (t.toPolygon).vertices = t.points
  proof: rfl

中文:
引理 toPolygon_vertices
  条件: (t : Affine.Triangle R P)
  结论: (t.toPolygon).vertices = t.points
  证明: rfl
-/
lemma toPolygon_vertices (t : Affine.Triangle R P) : (t.toPolygon).vertices = t.points := rfl

end Affine.Triangle

namespace Polygon

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/--
Definition of `toTriangle` / `toTriangle` 的定义

English:
definition toTriangle
  signature: (p : Polygon P 3) (h : p.HasNondegenerateVertices R)
  body: ⟨p.vertices, by
    have : p.vertices = ![p.vertices 0, p.vertices 1, p.vertices 2] := List.ofFn_inj.mp rfl
    rw [this]
    apply h⟩

@[simp]

中文:
定义 toTriangle
  签名: (p : Polygon P 3) (h : p.HasNondegenerateVertices R)
  定义体: ⟨p.vertices, by
    have : p.vertices = ![p.vertices 0, p.vertices 1, p.vertices 2] := List.ofFn_inj.mp rfl
    rw [this]
    apply h⟩

@[simp]

Depends on / 依赖: List.ofFn_inj.mp, ofFn_inj, p.vertices, vertices
-/
def toTriangle (p : Polygon P 3) (h : p.HasNondegenerateVertices R) :
    Affine.Triangle R P :=
  ⟨p.vertices, by
    have : p.vertices = ![p.vertices 0, p.vertices 1, p.vertices 2] := List.ofFn_inj.mp rfl
    rw [this]
    apply h⟩

@[simp]
/--
lemma `toTriangle_points` / 引理 `toTriangle_points`

English:
lemma toTriangle_points
  given: (p : Polygon P 3) (h : p.HasNondegenerateVertices R)
  proof: rfl

中文:
引理 toTriangle_points
  条件: (p : Polygon P 3) (h : p.HasNondegenerateVertices R)
  证明: rfl
-/
lemma toTriangle_points (p : Polygon P 3) (h : p.HasNondegenerateVertices R) :
    (p.toTriangle R h).points = p.vertices := rfl

/-- Converting a 3-polygon to a triangle and back yields the original polygon. -/
@[simp]
/--
lemma `toTriangle_toPolygon` / 引理 `toTriangle_toPolygon`

English:
lemma toTriangle_toPolygon
  given: (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R)
  proof: by
  rfl

中文:
引理 toTriangle_toPolygon
  条件: (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R)
  证明: by
  rfl
-/
lemma toTriangle_toPolygon (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R) :
    (poly.toTriangle R h).toPolygon = poly := by
  rfl

end Polygon

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/--
theorem `toPolygon_hasNondegenerateVertices` / 定理 `toPolygon_hasNondegenerateVertices`

English:
theorem toPolygon_hasNondegenerateVertices
  given: (t : Affine.Triangle R P)
  proof: by
  have ht : t.points = ![t.points 0, t.points 1, t.points 2] := List.ofFn_inj.mp rfl
  have h : AffineIndependent R ![t.points 0, t.points 1, t.points 2] := by
    simpa [← ht] using t.independent
  intro i
  fin_cases i <;> dsimp
  exacts [h, h.comm_left.comm_right, h.comm_right.comm_left]

中文:
定理 toPolygon_hasNondegenerateVertices
  条件: (t : Affine.Triangle R P)
  证明: by
  have ht : t.points = ![t.points 0, t.points 1, t.points 2] := List.ofFn_inj.mp rfl
  have h : AffineIndependent R ![t.points 0, t.points 1, t.points 2] := by
    simpa [← ht] using t.independent
  intro i
  fin_cases i <;> dsimp
  exacts [h, h.comm_left.comm_right, h.comm_right.comm_left]

Depends on / 依赖: AffineIndependent, List.ofFn_inj.mp, comm_left, comm_right, exacts, fin_cases, h.comm_left.comm_right, h.comm_right.comm_left, independent, ofFn_inj, points, t.independent, t.points
-/
theorem toPolygon_hasNondegenerateVertices (t : Affine.Triangle R P) :
    t.toPolygon.HasNondegenerateVertices R := by
  have ht : t.points = ![t.points 0, t.points 1, t.points 2] := List.ofFn_inj.mp rfl
  have h : AffineIndependent R ![t.points 0, t.points 1, t.points 2] := by
    simpa [← ht] using t.independent
  intro i
  fin_cases i <;> dsimp
  exacts [h, h.comm_left.comm_right, h.comm_right.comm_left]

/-- Converting a triangle to a polygon and back yields the original triangle. -/
@[simp]
/--
lemma `toPolygon_toTriangle` / 引理 `toPolygon_toTriangle`

English:
lemma toPolygon_toTriangle
  given: (t : Affine.Triangle R P)
  proof: by
  rfl

中文:
引理 toPolygon_toTriangle
  条件: (t : Affine.Triangle R P)
  证明: by
  rfl
-/
lemma toPolygon_toTriangle (t : Affine.Triangle R P) :
    t.toPolygon.toTriangle R (toPolygon_hasNondegenerateVertices t) = t := by
  rfl

end Affine.Triangle
