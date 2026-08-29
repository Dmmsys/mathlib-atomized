/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Notation

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Interior and boundary of a manifold

Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `x ∈ M` is an interior point if, with `φ` being the preferred chart at `x`,
  `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `x ∈ M` is a boundary point if `(extChartAt I x) x ∈ frontier (range I)`.
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `ModelWithCorners.univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `ModelWithCorners.interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- `BoundarylessManifold.isInteriorPoint`: if `M` is boundaryless, every point is an interior point
- `ModelWithCorners.Boundaryless.boundary_eq_empty` and `of_boundary_eq_empty`:
  `M` is boundaryless if and only if its boundary is empty

- `isInteriorPoint_iff_of_mem_atlas`: a point is an interior point iff any given chart around it
  sends it to the interior of the model; that is, the notion of interior is independent of choices
  of charts
- `ModelWithCorners.isOpen_interior`, `ModelWithCorners.isClosed_boundary`: the interior is open and
  and the boundary is closed. This is currently only proven for C¹ manifolds.

- `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`: differentiable maps with surjective
  differential send interior points to interior points
- `IsLocalDiffeomorphAt.isInteriorPoint_iff` etc.: local diffeomorphisms preserve both the boundary
  and interior

- `ModelWithCorners.interior_open`: the interior of `u : Opens M` is the preimage of the interior
  of `M` under the inclusion
- `ModelWithCorners.boundary_open`: the boundary of `u : Opens M` is the preimage of the boundary
  of `M` under the inclusion
- `ModelWithCorners.BoundarylessManifold.open`: if `M` is boundaryless, so is `u : Opens M`

- `ModelWithCorners.interior_prod`: the interior of `M × N` is the product of the interiors
  of `M` and `N`.
- `ModelWithCorners.boundary_prod`: the boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
- `ModelWithCorners.BoundarylessManifold.prod`: if `M` and `N` are boundaryless, so is `M × N`

- `ModelWithCorners.interior_disjointUnion`: the interior of a disjoint union `M ⊔ M'`
  is the union of the interior of `M` and `M'`
- `ModelWithCorners.boundary_disjointUnion`: the boundary of a disjoint union `M ⊔ M'`
  is the union of the boundaries of `M` and `M'`
- `ModelWithCorners.boundaryless_disjointUnion`: if `M` and `M'` are boundaryless,
  so is their disjoint union `M ⊔ M'`

## Tags
manifold, interior, boundary

## TODO
- the interior of `M` is dense, the boundary nowhere dense
- the interior of `M` is a boundaryless manifold
- `boundary M` is a submanifold (possibly with boundary and corners):
  follows from the corresponding statement for the model with corners `I`;
  this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero
- generalise lemmas about C¹ manifolds with boundary to also hold for finite-dimensional topological
  manifolds; this will require e.g. the homology of spheres.
- submersions send interior points to interior points. This should be an easy consequence of
  `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv` once submersions are defined.

-/

@[expose] public section

open Set Function
open scoped Topology Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in
/--
Definition of `IsInteriorPoint` / `IsInteriorPoint` 的定义

English:
definition IsInteriorPoint
  signature: (x : M)
  body: extChartAt I x x in interior (range I)

中文:
定义 Is整数eriorPoint
  签名: (x : M)
  定义体: extChartAt I x x in interior (range I)

Depends on / 依赖: extChartAt, interior
-/
def IsInteriorPoint (x : M) := extChartAt I x x in interior (range I)

variable (I) in
/--
Definition of `IsBoundaryPoint` / `IsBoundaryPoint` 的定义

English:
definition IsBoundaryPoint
  signature: (x : M)
  body: extChartAt I x x in frontier (range I)

中文:
定义 IsBoundaryPoint
  签名: (x : M)
  定义体: extChartAt I x x in frontier (range I)

Depends on / 依赖: extChartAt, frontier
-/
def IsBoundaryPoint (x : M) := extChartAt I x x in frontier (range I)

variable (M) in
/--
Definition of `interior` / `interior` 的定义

English:
definition interior
  signature: : Set M
  body: { x : M | I.IsInteriorPoint x }

中文:
定义 interior
  签名: : 集合 M
  定义体: { x : M | I.IsInteriorPoint x }
-/
protected def interior : Set M := { x : M | I.IsInteriorPoint x }

/--
lemma `isInteriorPoint_iff` / 引理 `isInteriorPoint_iff`

English:
lemma isInteriorPoint_iff
  given: {x : M}
  proof: ⟨fun h => (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h => OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

中文:
引理 is整数eriorPoint_iff
  条件: {x : M}
  证明: ⟨fun h => (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h => OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.interior_extend_target_subset_interior_range, chartAt, interior_extend_target_subset_interior_range, mem_chart_target, mem_interior_extend_target
-/
lemma isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x in interior (extChartAt I x).target :=
  ⟨fun h => (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h => OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

variable (M) in
/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: : Set M
  body: { x : M | I.IsBoundaryPoint x }

中文:
定义 boundary
  签名: : 集合 M
  定义体: { x : M | I.IsBoundaryPoint x }
-/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

/--
lemma `isBoundaryPoint_iff` / 引理 `isBoundaryPoint_iff`

English:
lemma isBoundaryPoint_iff
  given: {x : M}
  statement: I.IsBoundaryPoint x ↔ extChartAt I x x in frontier (range I)
  proof: Iff.rfl

中文:
引理 isBoundaryPoint_iff
  条件: {x : M}
  结论: I.IsBoundaryPoint x ↔ extChartAt I x x in frontier (range I)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x in frontier (range I) :=
  Iff.rfl

/--
lemma `isInteriorPoint_or_isBoundaryPoint` / 引理 `isInteriorPoint_or_isBoundaryPoint`

English:
lemma isInteriorPoint_or_isBoundaryPoint
  given: (x : M)
  statement: I.IsInteriorPoint x ∨ I.IsBoundaryPoint x
  proof: by
  rw [IsInteriorPoint]; rw [or_iff_not_imp_left]; rw [I.isBoundaryPoint_iff]; rw [← closure_sdiff_interior]; rw [I.isClosed_range.closure_eq]; rw [mem_sdiff]
  exact fun h => ⟨mem_range_self _, h⟩

中文:
引理 is整数eriorPoint_or_isBoundaryPoint
  条件: (x : M)
  结论: I.Is整数eriorPoint x ∨ I.IsBoundaryPoint x
  证明: by
  rw [IsInteriorPoint]; rw [or_iff_not_imp_left]; rw [I.isBoundaryPoint_iff]; rw [← closure_sdiff_interior]; rw [I.isClosed_range.closure_eq]; rw [mem_sdiff]
  exact fun h => ⟨mem_range_self _, h⟩

Depends on / 依赖: I.isBoundaryPoint_iff, I.isClosed_range.closure_eq, IsInteriorPoint, closure_eq, closure_sdiff_interior, isBoundaryPoint_iff, isClosed_range, mem_range_self, mem_sdiff, or_iff_not_imp_left
-/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  rw [IsInteriorPoint]; rw [or_iff_not_imp_left]; rw [I.isBoundaryPoint_iff]; rw [← closure_sdiff_interior]; rw [I.isClosed_range.closure_eq]; rw [mem_sdiff]
  exact fun h => ⟨mem_range_self _, h⟩

/--
lemma `interior_union_boundary_eq_univ` / 引理 `interior_union_boundary_eq_univ`

English:
lemma interior_union_boundary_eq_univ
  statement: (I.interior M) union (I.boundary M) = (univ : Set M)
  proof: eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

中文:
引理 interior_union_boundary_eq_univ
  结论: (I.interior M) union (I.boundary M) = (univ : 集合 M)
  证明: eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

Depends on / 依赖: I.isInteriorPoint_or_isBoundaryPoint, eq_univ_of_forall, isInteriorPoint_or_isBoundaryPoint, mem_union
-/
lemma interior_union_boundary_eq_univ : (I.interior M) union (I.boundary M) = (univ : Set M) :=
  eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

/--
lemma `disjoint_interior_boundary` / 引理 `disjoint_interior_boundary`

English:
lemma disjoint_interior_boundary
  statement: Disjoint (I.interior M) (I.boundary M)
  proof: by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact ⟨h1, h2⟩

中文:
引理 disjoint_interior_boundary
  结论: Disjoint (I.interior M) (I.boundary M)
  证明: by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact ⟨h1, h2⟩
-/
lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact ⟨h1, h2⟩

/--
lemma `isInteriorPoint_iff_not_isBoundaryPoint` / 引理 `isInteriorPoint_iff_not_isBoundaryPoint`

English:
lemma isInteriorPoint_iff_not_isBoundaryPoint
  given: (x : M)
  proof: by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact h

中文:
引理 is整数eriorPoint_iff_not_isBoundaryPoint
  条件: (x : M)
  证明: by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact h

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mp, disjoint_interior_frontier, extChartAt, isInteriorPoint_or_isBoundaryPoint, mem_empty_iff_false, mem_inter_iff, or_iff_not_imp_right
-/
lemma isInteriorPoint_iff_not_isBoundaryPoint (x : M) :
    I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x := by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x)]; rw [← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier]; rw [mem_inter_iff]
  exact h

/--
lemma `isBoundaryPoint_iff_not_isInteriorPoint` / 引理 `isBoundaryPoint_iff_not_isInteriorPoint`

English:
lemma isBoundaryPoint_iff_not_isInteriorPoint
  given: (x : M)
  proof: by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

中文:
引理 isBoundaryPoint_iff_not_is整数eriorPoint
  条件: (x : M)
  证明: by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

Depends on / 依赖: isInteriorPoint_iff_not_isBoundaryPoint
-/
lemma isBoundaryPoint_iff_not_isInteriorPoint (x : M) :
    I.IsBoundaryPoint x ↔ ¬I.IsInteriorPoint x := by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

/--
lemma `compl_interior` / 引理 `compl_interior`

English:
lemma compl_interior
  statement: (I.interior M)ᶜ = I.boundary M
  proof: by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

中文:
引理 compl_interior
  结论: (I.interior M)ᶜ = I.boundary M
  证明: by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

Depends on / 依赖: I.disjoint_interior_boundary, I.interior_union_boundary_eq_univ, compl_unique, disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mp, disjoint_interior_boundary, interior_union_boundary_eq_univ
-/
lemma compl_interior : (I.interior M)ᶜ = I.boundary M := by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

/--
lemma `compl_boundary` / 引理 `compl_boundary`

English:
lemma compl_boundary
  statement: (I.boundary M)ᶜ = I.interior M
  proof: by
  rw [← compl_interior]; rw [compl_compl]

中文:
引理 compl_boundary
  结论: (I.boundary M)ᶜ = I.interior M
  证明: by
  rw [← compl_interior]; rw [compl_compl]

Depends on / 依赖: compl_compl, compl_interior
-/
lemma compl_boundary : (I.boundary M)ᶜ = I.interior M := by
  rw [← compl_interior]; rw [compl_compl]

/--
lemma `_root_.range_mem_nhds_isInteriorPoint` / 引理 `_root_.range_mem_nhds_isInteriorPoint`

English:
lemma _root_.range_mem_nhds_isInteriorPoint
  given: {x : M} (h : I.IsInteriorPoint x)
  proof: by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

中文:
引理 _root_.range_mem_nhds_is整数eriorPoint
  条件: {x : M} (h : I.Is整数eriorPoint x)
  证明: by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

Depends on / 依赖: interior, interior_subset, isOpen_interior, mem_nhds_iff
-/
lemma _root_.range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I in 𝓝 (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

/--
Definition of `_root_.BoundarylessManifold` / `_root_.BoundarylessManifold` 的定义

English:
class _root_.BoundarylessManifold
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  axioms and operations (1):
    - isInteriorPoint' : forall x : M, IsInteriorPoint I x

中文:
类 _root_.无边界流形
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜]
  公理与运算 (1 个):
    - isInteriorPoint' : 对任意 x : M, Is整数eriorPoint I x
-/
class _root_.BoundarylessManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  isInteriorPoint' : forall x : M, IsInteriorPoint I x

section Boundaryless
variable [I.Boundaryless]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundarylessManifold I M
  body: by
    let r := ((chartAt H x).isOpen_extend_target (I := I)).interior_eq
    have : extChartAt I x = (chartAt H x).extend I := rfl
    rw [← this] at r
    rw [isInteriorPoint_iff]; rw [r]
    exact PartialEquiv.map_source _ (mem_extChartAt_source _)

中文:
实例 :
  签名: 无边界流形 I M
  定义体: by
    let r := ((chartAt H x).isOpen_extend_target (I := I)).interior_eq
    have : extChartAt I x = (chartAt H x).extend I := rfl
    rw [← this] at r
    rw [isInteriorPoint_iff]; rw [r]
    exact PartialEquiv.map_source _ (mem_extChartAt_source _)

Depends on / 依赖: PartialEquiv, PartialEquiv.map_source, chartAt, extChartAt, extend, interior_eq, isInteriorPoint_iff, isOpen_extend_target, map_source, mem_extChartAt_source
-/
instance : BoundarylessManifold I M where
  isInteriorPoint' x := by
    let r := ((chartAt H x).isOpen_extend_target (I := I)).interior_eq
    have : extChartAt I x = (chartAt H x).extend I := rfl
    rw [← this] at r
    rw [isInteriorPoint_iff]; rw [r]
    exact PartialEquiv.map_source _ (mem_extChartAt_source _)

end Boundaryless

section BoundarylessManifold

/--
Instance `BoundarylessManifold.of_empty` / 实例 `BoundarylessManifold.of_empty`

English:
instance BoundarylessManifold.of_empty
  signature: [IsEmpty M]
  body: (IsEmpty.false x).elim

中文:
实例 无边界流形.of_empty
  签名: [是空 M]
  定义体: (IsEmpty.false x).elim

Depends on / 依赖: IsEmpty, IsEmpty.false
-/
instance BoundarylessManifold.of_empty [IsEmpty M] : BoundarylessManifold I M where
  isInteriorPoint' x := (IsEmpty.false x).elim

/--
lemma `_root_.BoundarylessManifold.isInteriorPoint` / 引理 `_root_.BoundarylessManifold.isInteriorPoint`

English:
lemma _root_.BoundarylessManifold.isInteriorPoint
  given: {x : M} [BoundarylessManifold I M]
  proof: BoundarylessManifold.isInteriorPoint' x

中文:
引理 _root_.无边界流形.is整数eriorPoint
  条件: {x : M} [无边界流形 I M]
  证明: BoundarylessManifold.isInteriorPoint' x

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, isInteriorPoint
-/
lemma _root_.BoundarylessManifold.isInteriorPoint {x : M} [BoundarylessManifold I M] :
    IsInteriorPoint I x := BoundarylessManifold.isInteriorPoint' x

/--
lemma `interior_eq_univ` / 引理 `interior_eq_univ`

English:
lemma interior_eq_univ
  given: [BoundarylessManifold I M]
  statement: I.interior M = univ
  proof: eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

中文:
引理 interior_eq_univ
  条件: [无边界流形 I M]
  结论: I.interior M = univ
  证明: eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, eq_univ_of_forall, isInteriorPoint
-/
lemma interior_eq_univ [BoundarylessManifold I M] : I.interior M = univ :=
  eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

/--
lemma `Boundaryless.boundary_eq_empty` / 引理 `Boundaryless.boundary_eq_empty`

English:
lemma Boundaryless.boundary_eq_empty
  given: [BoundarylessManifold I M]
  statement: I.boundary M = ∅
  proof: by
  rw [← I.compl_interior]; rw [I.interior_eq_univ]; rw [compl_empty_iff]

中文:
引理 无边界.boundary_eq_empty
  条件: [无边界流形 I M]
  结论: I.boundary M = ∅
  证明: by
  rw [← I.compl_interior]; rw [I.interior_eq_univ]; rw [compl_empty_iff]

Depends on / 依赖: I.compl_interior, I.interior_eq_univ, compl_empty_iff, compl_interior, interior_eq_univ
-/
lemma Boundaryless.boundary_eq_empty [BoundarylessManifold I M] : I.boundary M = ∅ := by
  rw [← I.compl_interior]; rw [I.interior_eq_univ]; rw [compl_empty_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundarylessManifold
  signature: I M] : IsEmpty (I.boundary M)
  body: isEmpty_coe_sort.mpr Boundaryless.boundary_eq_empty

中文:
实例 [无边界流形
  签名: I M] : 是空 (I.boundary M)
  定义体: isEmpty_coe_sort.mpr Boundaryless.boundary_eq_empty

Depends on / 依赖: Boundaryless, Boundaryless.boundary_eq_empty, boundary_eq_empty, isEmpty_coe_sort, isEmpty_coe_sort.mpr
-/
instance [BoundarylessManifold I M] : IsEmpty (I.boundary M) :=
  isEmpty_coe_sort.mpr Boundaryless.boundary_eq_empty

/--
lemma `Boundaryless.iff_boundary_eq_empty` / 引理 `Boundaryless.iff_boundary_eq_empty`

English:
lemma Boundaryless.iff_boundary_eq_empty
  statement: I.boundary M = ∅ ↔ BoundarylessManifold I M
  proof: by
  refine ⟨fun h => { isInteriorPoint' := ?_ }, fun a => boundary_eq_empty⟩
  intro x
  change x in I.interior M
  rw [← compl_interior]; rw [compl_empty_iff] at h
  rw [h]
  trivial

中文:
引理 无边界.iff_boundary_eq_empty
  结论: I.boundary M = ∅ ↔ 无边界流形 I M
  证明: by
  refine ⟨fun h => { isInteriorPoint' := ?_ }, fun a => boundary_eq_empty⟩
  intro x
  change x in I.interior M
  rw [← compl_interior]; rw [compl_empty_iff] at h
  rw [h]
  trivial

Depends on / 依赖: I.interior, boundary_eq_empty, compl_empty_iff, compl_interior, interior, isInteriorPoint
-/
lemma Boundaryless.iff_boundary_eq_empty : I.boundary M = ∅ ↔ BoundarylessManifold I M := by
  refine ⟨fun h => { isInteriorPoint' := ?_ }, fun a => boundary_eq_empty⟩
  intro x
  change x in I.interior M
  rw [← compl_interior]; rw [compl_empty_iff] at h
  rw [h]
  trivial

/--
lemma `Boundaryless.of_boundary_eq_empty` / 引理 `Boundaryless.of_boundary_eq_empty`

English:
lemma Boundaryless.of_boundary_eq_empty
  given: (h : I.boundary M = ∅)
  statement: BoundarylessManifold I M
  proof: (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

中文:
引理 无边界.of_boundary_eq_empty
  条件: (h : I.boundary M = ∅)
  结论: 无边界流形 I M
  证明: (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

Depends on / 依赖: Boundaryless, Boundaryless.iff_boundary_eq_empty, iff_boundary_eq_empty
-/
lemma Boundaryless.of_boundary_eq_empty (h : I.boundary M = ∅) : BoundarylessManifold I M :=
  (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

end BoundarylessManifold

section ChartIndependence

/--
lemma `_root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv` / 引理 `_root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv`

English:
lemma _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
  proof: by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : forall y, F (fderiv Real f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; pu

中文:
引理 _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
  证明: by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : forall y, F (fderiv Real f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; pu

Depends on / 依赖: contrapose, geometric_hahn_banach_open_point, hs.interior, interior, isOpen_interior
-/
lemma _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup H] [NormedSpace Real H]
    {f : E -> H} {x : E} (hf : DifferentiableAt Real f x) {u : Set E} (hu : u in 𝓝 x) {s : Set H}
    (hs : Convex Real s) (hs' : IsClosed s) (hs'' : (interior s).Nonempty) (hfus : Set.MapsTo f u s)
    (hfx : Function.Surjective (fderiv Real f x)) : f x in interior s := by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : forall y, F (fderiv Real f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; push Not
    refine ⟨f x - y, fun z => ne_of_apply_ne F ?_⟩
    rw [h z]; rw [F.map_sub]
    exact (sub_pos.2 <| hF _ hy).ne
  -- This follows from `F ∘ f` taking on a local maximum at `e.extend I x`.
  have hF' : MapsTo F s (Iic (F (f x))) := by
    rw [← hs'.closure_eq]; rw [← closure_Iio]; rw [← hs.closure_interior_eq_closure_of_nonempty_interior hs'']
    exact .closure hF F.continuous
have hFφ : IsLocalMax (F ∘ f) x := Filter.eventually_of_mem hu fun y hy => hF' hfus hy
  have h := hFφ.fderiv_eq_zero
  rw [fderiv_comp _ (by fun_prop) hf]; rw [ContinuousLinearMap.fderiv] at h
  exact DFunLike.congr_fun h

variable {n : WithTop Nat∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H} {x : M}

/--
lemma `mem_interior_range_of_mem_interior_range_of_mem_atlas` / 引理 `mem_interior_range_of_mem_interior_range_of_mem_atlas`

English:
lemma mem_interior_range_of_mem_interior_range_of_mem_atlas
  statement: (hn : n != 0)
  proof: by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.sou

中文:
引理 mem_interior_range_of_mem_interior_range_of_mem_atlas
  结论: (hn : n != 0)
  证明: by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.sou
-/
lemma mem_interior_range_of_mem_interior_range_of_mem_atlas (hn : n != 0)
    (he : e in atlas H M) (he' : e' in atlas H M) (hex : x in e.source) (hex' : x in e'.source)
    (hx : e.extend I x in interior (e.extend I).target) :
    e'.extend I x in interior (e'.extend I).target := by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) ->
      e'.extend I x in interior (range I) by
refine e'.mem_interior_extend_target (by simp [hex']) h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn (IsManifold.subset_maximalAtlas he)
(IsManifold.subset_maximalAtlas he') by simp [hex, hex']).surjective
  intro hφx'
  /- Reduce the situation to the real case, then apply
  `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`. -/
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  have hφx : φ.source in 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
exact e.extend_preimage_mem_nhds hex e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := Real)]; rw [(hφ.differentiableOn hn _ (by simp [φ]; rw [hex]; rw [hex'])).restrictScalars_fderivWithin (𝕜 := Real)
(uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ]; rw [hex]]
  replace hφ := ((hφ.restrict_scalars Real).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/--
lemma `mem_interior_range_iff_of_mem_atlas` / 引理 `mem_interior_range_iff_of_mem_atlas`

English:
lemma mem_interior_range_iff_of_mem_atlas
  statement: (hn : n != 0) (he : e in atlas H M) (he' : e' in atlas H M)
  proof: by
  constructor <;> apply mem_interior_range_of_mem_interior_range_of_mem_atlas hn <;> assumption

中文:
引理 mem_interior_range_iff_of_mem_atlas
  结论: (hn : n != 0) (he : e in atlas H M) (he' : e' in atlas H M)
  证明: by
  constructor <;> apply mem_interior_range_of_mem_interior_range_of_mem_atlas hn <;> assumption

Depends on / 依赖: mem_interior_range_of_mem_interior_range_of_mem_atlas
-/
lemma mem_interior_range_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (he' : e' in atlas H M)
    (hex : x in e.source) (hex' : x in e'.source) :
    e.extend I x in interior (e.extend I).target ↔
    e'.extend I x in interior (e'.extend I).target := by
  constructor <;> apply mem_interior_range_of_mem_interior_range_of_mem_atlas hn <;> assumption

/--
lemma `isInteriorPoint_iff_of_mem_atlas` / 引理 `isInteriorPoint_iff_of_mem_atlas`

English:
lemma isInteriorPoint_iff_of_mem_atlas
  given: (hn : n != 0) (he : e in atlas H M) (hx : x in e.source)
  proof: by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_atlas hn (chart_mem_atlas H x) he (mem_chart_source H x) hx

中文:
引理 is整数eriorPoint_iff_of_mem_atlas
  条件: (hn : n != 0) (he : e in atlas H M) (hx : x in e.source)
  证明: by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_atlas hn (chart_mem_atlas H x) he (mem_chart_source H x) hx

Depends on / 依赖: chart_mem_atlas, isInteriorPoint_iff, mem_chart_source, mem_interior_range_iff_of_mem_atlas
-/
lemma isInteriorPoint_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx : x in e.source) :
    I.IsInteriorPoint x ↔ e.extend I x in interior (e.extend I).target := by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_atlas hn (chart_mem_atlas H x) he (mem_chart_source H x) hx

/--
lemma `isBoundaryPoint_iff_of_mem_atlas` / 引理 `isBoundaryPoint_iff_of_mem_atlas`

English:
lemma isBoundaryPoint_iff_of_mem_atlas
  given: (hn : n != 0) (he : e in atlas H M) (hx : x in e.source)
  proof: by
  rw [← not_iff_not]; rw [← I.isInteriorPoint_iff_not_isBoundaryPoint]; rw [I.isInteriorPoint_iff_of_mem_atlas hn he hx]; rw [mem_interior_iff_notMem_frontier]
exact (e.extend I).mapsTo e.extend_source (I := I) ▸ hx

中文:
引理 isBoundaryPoint_iff_of_mem_atlas
  条件: (hn : n != 0) (he : e in atlas H M) (hx : x in e.source)
  证明: by
  rw [← not_iff_not]; rw [← I.isInteriorPoint_iff_not_isBoundaryPoint]; rw [I.isInteriorPoint_iff_of_mem_atlas hn he hx]; rw [mem_interior_iff_notMem_frontier]
exact (e.extend I).mapsTo e.extend_source (I := I) ▸ hx

Depends on / 依赖: I.isInteriorPoint_iff_not_isBoundaryPoint, I.isInteriorPoint_iff_of_mem_atlas, e.extend, e.extend_source, extend, extend_source, isInteriorPoint_iff_not_isBoundaryPoint, isInteriorPoint_iff_of_mem_atlas, mapsTo, mem_interior_iff_notMem_frontier, not_iff_not
-/
lemma isBoundaryPoint_iff_of_mem_atlas (hn : n != 0) (he : e in atlas H M) (hx : x in e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x in frontier (e.extend I).target := by
  rw [← not_iff_not]; rw [← I.isInteriorPoint_iff_not_isBoundaryPoint]; rw [I.isInteriorPoint_iff_of_mem_atlas hn he hx]; rw [mem_interior_iff_notMem_frontier]
exact (e.extend I).mapsTo e.extend_source (I := I) ▸ hx

/--
lemma `isOpen_interior` / 引理 `isOpen_interior`

English:
lemma isOpen_interior
  given: (hn : n != 0)
  statement: IsOpen (I.interior M)
  proof: by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x
    isOpen_interior, mem_chart_source H x, isInteriorPoint_iff.1 hx⟩
  exact fun y hy => (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).2 hy.2

中文:
引理 isOpen_interior
  条件: (hn : n != 0)
  结论: 是开集 (I.interior M)
  证明: by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x
    isOpen_interior, mem_chart_source H x, isInteriorPoint_iff.1 hx⟩
  exact fun y hy => (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).2 hy.2
-/
protected lemma isOpen_interior (hn : n != 0) : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x
    isOpen_interior, mem_chart_source H x, isInteriorPoint_iff.1 hx⟩
  exact fun y hy => (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).2 hy.2

/--
lemma `isClosed_boundary` / 引理 `isClosed_boundary`

English:
lemma isClosed_boundary
  given: (hn : n != 0)
  statement: IsClosed (I.boundary M)
  proof: by
  rw [← I.compl_interior]; rw [isClosed_compl_iff]
  exact I.isOpen_interior hn

中文:
引理 isClosed_boundary
  条件: (hn : n != 0)
  结论: 是闭集 (I.boundary M)
  证明: by
  rw [← I.compl_interior]; rw [isClosed_compl_iff]
  exact I.isOpen_interior hn
-/
protected lemma isClosed_boundary (hn : n != 0) : IsClosed (I.boundary M) := by
  rw [← I.compl_interior]; rw [isClosed_compl_iff]
  exact I.isOpen_interior hn

end ChartIndependence

end ModelWithCorners

/-! Interior and boundary are preserved under (local) diffeomorphisms. -/
section Diffeomorph

open ModelWithCorners

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop Nat∞}

/--
lemma `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv` / 引理 `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`

English:
lemma MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv
  statement: {f : M -> N} {x : M}
  proof: by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.rest

中文:
引理 MDifferentiableAt.is整数eriorPoint_of_surjective_mfderiv
  结论: {f : M -> N} {x : M}
  证明: by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.rest
-/
lemma MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv {f : M -> N} {x : M}
    (hf : MDiffAt f x) (hf' : Surjective (mfderiv% f x))
    (hx : I.IsInteriorPoint x) : I'.IsInteriorPoint (f x) := by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
  let _ : NormedSpace Real E' := NormedSpace.restrictScalars Real 𝕜 E'
  -- Write everything in terms of extended charts around `x` and `f x`.
  simp only [mfderiv, hf] at hf'
have hf'' := hf.differentiableWithinAt_writtenInExtChartAt.differentiableAt by
    simpa [← mem_interior_iff_mem_nhds] using! hx
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ <| by simp) hf''] at hf'
  /- Since `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x`
  over `𝕜`, it also is so over `ℝ`. -/
  replace hf' : Surjective (fderiv Real (writtenInExtChartAt I I' x f) (extChartAt I x x)) := by
    rwa [hf''.fderiv_restrictScalars (𝕜 := Real), ContinuousLinearMap.coe_restrictScalars']
  replace hf'' := hf''.restrictScalars Real
  /- The lemma is now essentially just `mem_interior_convex_of_surjective_fderiv`: because
  `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x` over `ℝ` and
  sends a neighbourhood of `x` (the region in which it could be written in the extended charts) to
  a closed convex set with nonempty interior (`I'.range`), it must send `x` to that interior. -/
  have := hf''.mem_interior_convex_of_surjective_fderiv (Filter.inter_mem ?_ ?_) I'.convex_range
    I'.isClosed_range I'.nonempty_interior (writtenInExtChartAt_mapsTo.mono_right ?_) hf'
  · simpa using! this
  · rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hx)]
    exact extChartAt_target_mem_nhdsWithin x
· exact extChartAt_preimage_mem_nhds hf.continuousAt.preimage_mem_nhds
      extChartAt_source_mem_nhds _
  · exact extChartAt_target_subset_range _

/--
lemma `IsLocalDiffeomorphAt.isInteriorPoint_iff` / 引理 `IsLocalDiffeomorphAt.isInteriorPoint_iff`

English:
lemma IsLocalDiffeomorphAt.isInteriorPoint_iff
  statement: (hn : n != 0) {f : M -> N} {x : M}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine (hf.mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).surjective
  · rw [← hf.localInverse_left_inv hf.localInverse_mem_target]
    refine (hf.localInverse_mdifferentiableAt hn).isInteri

中文:
引理 IsLocalDiffeomorphAt.is整数eriorPoint_iff
  结论: (hn : n != 0) {f : M -> N} {x : M}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine (hf.mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).surjective
  · rw [← hf.localInverse_left_inv hf.localInverse_mem_target]
    refine (hf.localInverse_mdifferentiableAt hn).isInteri

Depends on / 依赖: hf.localInverse_left_inv, hf.localInverse_mdifferentiableAt, hf.localInverse_mem_target, hf.mdifferentiableAt, hf.mfderivToContinuousLinearEquiv, isInteriorPoint_of_surjective_mfderiv, localInverse_left_inv, localInverse_mdifferentiableAt, localInverse_mem_target, mdifferentiableAt, mfderivToContinuousLinearEquiv, surjective, symm.surjective
-/
lemma IsLocalDiffeomorphAt.isInteriorPoint_iff (hn : n != 0) {f : M -> N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsInteriorPoint x ↔ I'.IsInteriorPoint (f x) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine (hf.mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).surjective
  · rw [← hf.localInverse_left_inv hf.localInverse_mem_target]
    refine (hf.localInverse_mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).symm.surjective

/--
lemma `IsLocalDiffeomorphAt.isBoundaryPoint_iff` / 引理 `IsLocalDiffeomorphAt.isBoundaryPoint_iff`

English:
lemma IsLocalDiffeomorphAt.isBoundaryPoint_iff
  statement: (hn : n != 0) {f : M -> N} {x : M}
  proof: by
  simp [isBoundaryPoint_iff_not_isInteriorPoint, hf.isInteriorPoint_iff hn]

中文:
引理 IsLocalDiffeomorphAt.isBoundaryPoint_iff
  结论: (hn : n != 0) {f : M -> N} {x : M}
  证明: by
  simp [isBoundaryPoint_iff_not_isInteriorPoint, hf.isInteriorPoint_iff hn]

Depends on / 依赖: hf.isInteriorPoint_iff, isBoundaryPoint_iff_not_isInteriorPoint, isInteriorPoint_iff
-/
lemma IsLocalDiffeomorphAt.isBoundaryPoint_iff (hn : n != 0) {f : M -> N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (f x) := by
  simp [isBoundaryPoint_iff_not_isInteriorPoint, hf.isInteriorPoint_iff hn]


/--
lemma `IsLocalDiffeomorphOn.preimage_interior_inter` / 引理 `IsLocalDiffeomorphOn.preimage_interior_inter`

English:
lemma IsLocalDiffeomorphOn.preimage_interior_inter
  statement: (hn : n != 0) {f : M -> N} {s : Set M}
  proof: by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isInteriorPoint_iff hn).symm

中文:
引理 IsLocalDiffeomorphOn.preimage_interior_inter
  结论: (hn : n != 0) {f : M -> N} {s : 集合 M}
  证明: by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isInteriorPoint_iff hn).symm

Depends on / 依赖: isInteriorPoint_iff
-/
lemma IsLocalDiffeomorphOn.preimage_interior_inter (hn : n != 0) {f : M -> N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.interior N inter s = I.interior M inter s := by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isInteriorPoint_iff hn).symm

/--
lemma `IsLocalDiffeomorphOn.preimage_boundary_inter` / 引理 `IsLocalDiffeomorphOn.preimage_boundary_inter`

English:
lemma IsLocalDiffeomorphOn.preimage_boundary_inter
  statement: (hn : n != 0) {f : M -> N} {s : Set M}
  proof: by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isBoundaryPoint_iff hn).symm

中文:
引理 IsLocalDiffeomorphOn.preimage_boundary_inter
  结论: (hn : n != 0) {f : M -> N} {s : 集合 M}
  证明: by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isBoundaryPoint_iff hn).symm

Depends on / 依赖: isBoundaryPoint_iff
-/
lemma IsLocalDiffeomorphOn.preimage_boundary_inter (hn : n != 0) {f : M -> N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.boundary N inter s = I.boundary M inter s := by
  ext x
  simpa using! fun hx => ((hf ⟨x, hx⟩).isBoundaryPoint_iff hn).symm

/--
lemma `IsLocalDiffeomorph.preimage_interior` / 引理 `IsLocalDiffeomorph.preimage_interior`

English:
lemma IsLocalDiffeomorph.preimage_interior
  statement: (hn : n != 0) {f : M -> N}
  proof: by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_interior_inter hn

中文:
引理 IsLocalDiffeomorph.preimage_interior
  结论: (hn : n != 0) {f : M -> N}
  证明: by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_interior_inter hn

Depends on / 依赖: hf.isLocalDiffeomorphOn, isLocalDiffeomorphOn, preimage_interior_inter
-/
lemma IsLocalDiffeomorph.preimage_interior (hn : n != 0) {f : M -> N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.interior N = I.interior M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_interior_inter hn

/--
lemma `IsLocalDiffeomorph.preimage_boundary` / 引理 `IsLocalDiffeomorph.preimage_boundary`

English:
lemma IsLocalDiffeomorph.preimage_boundary
  statement: (hn : n != 0) {f : M -> N}
  proof: by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_boundary_inter hn

中文:
引理 IsLocalDiffeomorph.preimage_boundary
  结论: (hn : n != 0) {f : M -> N}
  证明: by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_boundary_inter hn

Depends on / 依赖: hf.isLocalDiffeomorphOn, isLocalDiffeomorphOn, preimage_boundary_inter
-/
lemma IsLocalDiffeomorph.preimage_boundary (hn : n != 0) {f : M -> N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.boundary N = I.boundary M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_boundary_inter hn

/--
lemma `IsLocalDiffeomorph.boundarylessManifold` / 引理 `IsLocalDiffeomorph.boundarylessManifold`

English:
lemma IsLocalDiffeomorph.boundarylessManifold
  statement: (hn : n != 0) {f : M -> N}
  proof: by
  simp [← Boundaryless.iff_boundary_eq_empty, ← hf.preimage_boundary hn,
    Boundaryless.boundary_eq_empty]

中文:
引理 IsLocalDiffeomorph.boundarylessManifold
  结论: (hn : n != 0) {f : M -> N}
  证明: by
  simp [← Boundaryless.iff_boundary_eq_empty, ← hf.preimage_boundary hn,
    Boundaryless.boundary_eq_empty]

Depends on / 依赖: Boundaryless, Boundaryless.boundary_eq_empty, Boundaryless.iff_boundary_eq_empty, boundary_eq_empty, hf.preimage_boundary, iff_boundary_eq_empty, preimage_boundary
-/
lemma IsLocalDiffeomorph.boundarylessManifold (hn : n != 0) {f : M -> N}
    (hf : IsLocalDiffeomorph I I' n f) [BoundarylessManifold I' N] : BoundarylessManifold I M := by
  simp [← Boundaryless.iff_boundary_eq_empty, ← hf.preimage_boundary hn,
    Boundaryless.boundary_eq_empty]

/--
lemma `Diffeomorph.preimage_interior` / 引理 `Diffeomorph.preimage_interior`

English:
lemma Diffeomorph.preimage_interior
  given: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: Φ.isLocalDiffeomorph.preimage_interior hn

中文:
引理 微分同胚.preimage_interior
  条件: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: Φ.isLocalDiffeomorph.preimage_interior hn

Depends on / 依赖: isLocalDiffeomorph, isLocalDiffeomorph.preimage_interior, preimage_interior
-/
lemma Diffeomorph.preimage_interior (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.interior N = I.interior M :=
  Φ.isLocalDiffeomorph.preimage_interior hn

/--
lemma `Diffeomorph.preimage_boundary` / 引理 `Diffeomorph.preimage_boundary`

English:
lemma Diffeomorph.preimage_boundary
  given: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: Φ.isLocalDiffeomorph.preimage_boundary hn

中文:
引理 微分同胚.preimage_boundary
  条件: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: Φ.isLocalDiffeomorph.preimage_boundary hn

Depends on / 依赖: isLocalDiffeomorph, isLocalDiffeomorph.preimage_boundary, preimage_boundary
-/
lemma Diffeomorph.preimage_boundary (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.boundary N = I.boundary M :=
  Φ.isLocalDiffeomorph.preimage_boundary hn

/--
lemma `Diffeomorph.image_interior` / 引理 `Diffeomorph.image_interior`

English:
lemma Diffeomorph.image_interior
  given: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_interior hn).symm

中文:
引理 微分同胚.image_interior
  条件: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_interior hn).symm

Depends on / 依赖: eq_preimage_iff_image_eq, preimage_interior
-/
lemma Diffeomorph.image_interior (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.interior M = I'.interior N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_interior hn).symm

/--
lemma `Diffeomorph.image_boundary` / 引理 `Diffeomorph.image_boundary`

English:
lemma Diffeomorph.image_boundary
  given: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_boundary hn).symm

中文:
引理 微分同胚.image_boundary
  条件: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_boundary hn).symm

Depends on / 依赖: eq_preimage_iff_image_eq, preimage_boundary
-/
lemma Diffeomorph.image_boundary (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.boundary M = I'.boundary N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_boundary hn).symm

/--
lemma `Diffeomorph.boundarylessManifold` / 引理 `Diffeomorph.boundarylessManifold`

English:
lemma Diffeomorph.boundarylessManifold
  statement: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: Φ.symm.isLocalDiffeomorph.boundarylessManifold hn

中文:
引理 微分同胚.boundarylessManifold
  结论: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: Φ.symm.isLocalDiffeomorph.boundarylessManifold hn

Depends on / 依赖: boundarylessManifold, isLocalDiffeomorph, symm.isLocalDiffeomorph.boundarylessManifold
-/
lemma Diffeomorph.boundarylessManifold (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
    [BoundarylessManifold I M] : BoundarylessManifold I' N :=
  Φ.symm.isLocalDiffeomorph.boundarylessManifold hn

/--
lemma `Diffeomorph.boundarylessManifold_iff` / 引理 `Diffeomorph.boundarylessManifold_iff`

English:
lemma Diffeomorph.boundarylessManifold_iff
  given: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  proof: ⟨fun _ => Φ.boundarylessManifold hn, fun _ => Φ.symm.boundarylessManifold hn⟩

中文:
引理 微分同胚.boundarylessManifold_iff
  条件: (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
  证明: ⟨fun _ => Φ.boundarylessManifold hn, fun _ => Φ.symm.boundarylessManifold hn⟩

Depends on / 依赖: boundarylessManifold, symm.boundarylessManifold
-/
lemma Diffeomorph.boundarylessManifold_iff (hn : n != 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    BoundarylessManifold I M ↔ BoundarylessManifold I' N :=
  ⟨fun _ => Φ.boundarylessManifold hn, fun _ => Φ.symm.boundarylessManifold hn⟩

end Diffeomorph

namespace ModelWithCorners

/-! Interior and boundary of open subsets of a manifold. -/
section opens

open TopologicalSpace

/--
lemma `isInteriorPoint_iff_isInteriorPoint_val` / 引理 `isInteriorPoint_iff_isInteriorPoint_val`

English:
lemma isInteriorPoint_iff_isInteriorPoint_val
  given: {u : Opens M} {x : u}
  proof: by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using!
    fun _ _ => (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

中文:
引理 is整数eriorPoint_iff_is整数eriorPoint_val
  条件: {u : Opens M} {x : u}
  证明: by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using!
    fun _ _ => (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

Depends on / 依赖: I.isInteriorPoint_iff, OpenPartialHomeomorph, OpenPartialHomeomorph.subtypeRestr, chartAt, chartAt_eq, extend_preimage_mem_nhds, isInteriorPoint_iff, mem_chart_source, mem_interior_iff_mem_nhds, mem_nhds, subtypeRestr, u.chartAt_eq
-/
lemma isInteriorPoint_iff_isInteriorPoint_val {u : Opens M} {x : u} :
    I.IsInteriorPoint x ↔ I.IsInteriorPoint x.1 := by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using!
    fun _ _ => (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

/--
lemma `isBoundaryPoint_iff_isBoundaryPoint_val` / 引理 `isBoundaryPoint_iff_isBoundaryPoint_val`

English:
lemma isBoundaryPoint_iff_isBoundaryPoint_val
  given: {u : Opens M} {x : u}
  proof: by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

中文:
引理 isBoundaryPoint_iff_isBoundaryPoint_val
  条件: {u : Opens M} {x : u}
  证明: by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

Depends on / 依赖: I.isInteriorPoint_iff_isInteriorPoint_val, I.isInteriorPoint_iff_not_isBoundaryPoint, isInteriorPoint_iff_isInteriorPoint_val, isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not
-/
lemma isBoundaryPoint_iff_isBoundaryPoint_val {u : Opens M} {x : u} :
    I.IsBoundaryPoint x ↔ I.IsBoundaryPoint x.1 := by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

/--
lemma `interior_open` / 引理 `interior_open`

English:
lemma interior_open
  given: {u : Opens M}
  statement: I.interior u = (↑) ⁻¹' I.interior M
  proof: by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

中文:
引理 interior_open
  条件: {u : Opens M}
  结论: I.interior u = (↑) ⁻¹' I.interior M
  证明: by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

Depends on / 依赖: I.isInteriorPoint_iff_isInteriorPoint_val, isInteriorPoint_iff_isInteriorPoint_val
-/
lemma interior_open {u : Opens M} : I.interior u = (↑) ⁻¹' I.interior M := by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

/--
lemma `boundary_open` / 引理 `boundary_open`

English:
lemma boundary_open
  given: {u : Opens M}
  statement: I.boundary u = (↑) ⁻¹' I.boundary M
  proof: by
  simp [← I.compl_interior, I.interior_open]

中文:
引理 boundary_open
  条件: {u : Opens M}
  结论: I.boundary u = (↑) ⁻¹' I.boundary M
  证明: by
  simp [← I.compl_interior, I.interior_open]

Depends on / 依赖: I.compl_interior, I.interior_open, compl_interior, interior_open
-/
lemma boundary_open {u : Opens M} : I.boundary u = (↑) ⁻¹' I.boundary M := by
  simp [← I.compl_interior, I.interior_open]

/--
Instance `BoundarylessManifold.open` / 实例 `BoundarylessManifold.open`

English:
instance BoundarylessManifold.open
  signature: [BoundarylessManifold I M] (u : Opens M)
  body: ⟨fun _ => I.isInteriorPoint_iff_isInteriorPoint_val.2 BoundarylessManifold.isInteriorPoint⟩

中文:
实例 无边界流形.open
  签名: [无边界流形 I M] (u : Opens M)
  定义体: ⟨fun _ => I.isInteriorPoint_iff_isInteriorPoint_val.2 BoundarylessManifold.isInteriorPoint⟩

Depends on / 依赖: BoundarylessManifold, BoundarylessManifold.isInteriorPoint, I.isInteriorPoint_iff_isInteriorPoint_val, isInteriorPoint, isInteriorPoint_iff_isInteriorPoint_val
-/
instance BoundarylessManifold.open [BoundarylessManifold I M] (u : Opens M) :
    BoundarylessManifold I u :=
  ⟨fun _ => I.isInteriorPoint_iff_isInteriorPoint_val.2 BoundarylessManifold.isInteriorPoint⟩

end opens

/-! Interior and boundary of the product of two manifolds. -/
section prod

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'} {x : M} {y : N}

/--
lemma `interior_prod` / 引理 `interior_prod`

English:
lemma interior_prod
  proof: by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq]; rw [← range_prodMap]; rw [modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint]; rw [← a

中文:
引理 interior_prod
  证明: by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq]; rw [← range_prodMap]; rw [modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint]; rw [← a

Depends on / 依赖: I.prod, IsInteriorPoint, ModelWithCorners, ModelWithCorners.interior, Set.mem_prod.mp, interior, interior_prod_eq, mem_prod, modelWithCorners_prod_coe, range_prodMap, replace
-/
lemma interior_prod :
    (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interior N) := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq]; rw [← range_prodMap]; rw [modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint]; rw [← aux] at hp
    exact hp
  · change (I.prod J).IsInteriorPoint p
    rw [IsInteriorPoint]; rw [← aux]; rw [mem_prod]
    obtain h := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h
    exact h

/--
lemma `boundary_prod` / 引理 `boundary_prod`

English:
lemma boundary_prod
  proof: by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ union univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h]; rw [I.compl_interio

中文:
引理 boundary_prod
  证明: by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ union univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h]; rw [I.compl_interio

Depends on / 依赖: I.compl_interior, I.interior, I.prod, J.compl_interior, J.interior, boundary, compl_interior, compl_interior.symm, compl_prod_eq_union, interior, interior_prod, union_comm
-/
lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) union Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ union univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h]; rw [I.compl_interior]; rw [J.compl_interior]; rw [union_comm]
  rfl

/--
lemma `boundary_of_boundaryless_left` / 引理 `boundary_of_boundaryless_left`

English:
lemma boundary_of_boundaryless_left
  given: [BoundarylessManifold I M]
  proof: by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this]; rw [union_empty]

中文:
引理 boundary_of_boundaryless_left
  条件: [无边界流形 I M]
  证明: by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this]; rw [union_empty]

Depends on / 依赖: Boundaryless, Boundaryless.boundary_eq_empty, Set.empty_prod, Set.prod, boundary_eq_empty, boundary_prod, empty_prod, union_empty
-/
lemma boundary_of_boundaryless_left [BoundarylessManifold I M] :
    (I.prod J).boundary (M × N) = Set.prod (univ : Set M) (J.boundary N) := by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this]; rw [union_empty]

/--
lemma `boundary_of_boundaryless_right` / 引理 `boundary_of_boundaryless_right`

English:
lemma boundary_of_boundaryless_right
  given: [BoundarylessManifold J N]
  proof: by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this]; rw [empty_union]

中文:
引理 boundary_of_boundaryless_right
  条件: [无边界流形 J N]
  证明: by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this]; rw [empty_union]

Depends on / 依赖: Boundaryless, Boundaryless.boundary_eq_empty, Set.prod, Set.prod_empty, boundary_eq_empty, boundary_prod, empty_union, prod_empty
-/
lemma boundary_of_boundaryless_right [BoundarylessManifold J N] :
    (I.prod J).boundary (M × N) = Set.prod (I.boundary M) (univ : Set N) := by
  rw [boundary_prod]; rw [Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this]; rw [empty_union]

/--
Instance `BoundarylessManifold.prod` / 实例 `BoundarylessManifold.prod`

English:
instance BoundarylessManifold.prod
  signature: [BoundarylessManifold I M] [BoundarylessManifold J N]
  body: by
  apply Boundaryless.of_boundary_eq_empty
  simp only [boundary_prod, Boundaryless.boundary_eq_empty, union_empty_iff]
  -- These are simp lemmas, but `simp` does not apply them on its own:
  -- presumably because of the distinction between `Prod` and `ModelProd`
  exact ⟨Set.prod_empty, Set.empt

中文:
实例 无边界流形.乘积
  签名: [无边界流形 I M] [无边界流形 J N]
  定义体: by
  apply Boundaryless.of_boundary_eq_empty
  simp only [boundary_prod, Boundaryless.boundary_eq_empty, union_empty_iff]
  -- These are simp lemmas, but `simp` does not apply them on its own:
  -- presumably because of the distinction between `Prod` and `ModelProd`
  exact ⟨Set.prod_empty, Set.empt

Depends on / 依赖: Boundaryless, Boundaryless.boundary_eq_empty, Boundaryless.of_boundary_eq_empty, boundary_eq_empty, boundary_prod, of_boundary_eq_empty, union_empty_iff
-/
instance BoundarylessManifold.prod [BoundarylessManifold I M] [BoundarylessManifold J N] :
    BoundarylessManifold (I.prod J) (M × N) := by
  apply Boundaryless.of_boundary_eq_empty
  simp only [boundary_prod, Boundaryless.boundary_eq_empty, union_empty_iff]
  -- These are simp lemmas, but `simp` does not apply them on its own:
  -- presumably because of the distinction between `Prod` and `ModelProd`
  exact ⟨Set.prod_empty, Set.empty_prod⟩

end prod

/-! Interior and boundary of the disjoint union of two manifolds. -/
section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop Nat∞}

open Topology

/--
lemma `interiorPoint_inl` / 引理 `interiorPoint_inl`

English:
lemma interiorPoint_inl
  given: (x : M) (hx : I.IsInteriorPoint x)
  proof: by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

中文:
引理 interiorPoint_inl
  条件: (x : M) (hx : I.Is整数eriorPoint x)
  证明: by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inl, I.isInteriorPoint_iff, Sum.inl_injective.extend_apply, chartAt, extChartAt, extend_apply, inl_injective, isInteriorPoint_iff, sum_chartAt_inl
-/
lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inl x : M oplus M') := by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

/--
lemma `boundaryPoint_inl` / 引理 `boundaryPoint_inl`

English:
lemma boundaryPoint_inl
  given: (x : M) (hx : I.IsBoundaryPoint x)
  proof: by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

中文:
引理 boundaryPoint_inl
  条件: (x : M) (hx : I.IsBoundaryPoint x)
  证明: by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inl, I.isBoundaryPoint_iff, Sum.inl_injective.extend_apply, chartAt, extChartAt, extend_apply, inl_injective, isBoundaryPoint_iff, sum_chartAt_inl
-/
lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inl x : M oplus M') := by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

/--
lemma `interiorPoint_inr` / 引理 `interiorPoint_inr`

English:
lemma interiorPoint_inr
  given: (x : M') (hx : I.IsInteriorPoint x)
  proof: by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

中文:
引理 interiorPoint_inr
  条件: (x : M') (hx : I.Is整数eriorPoint x)
  证明: by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inr, I.isInteriorPoint_iff, Sum.inr_injective.extend_apply, chartAt, extChartAt, extend_apply, inr_injective, isInteriorPoint_iff, sum_chartAt_inr
-/
lemma interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inr x : M oplus M') := by
  rw [I.isInteriorPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

/--
lemma `boundaryPoint_inr` / 引理 `boundaryPoint_inr`

English:
lemma boundaryPoint_inr
  given: (x : M') (hx : I.IsBoundaryPoint x)
  proof: by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

中文:
引理 boundaryPoint_inr
  条件: (x : M') (hx : I.IsBoundaryPoint x)
  证明: by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inr, I.isBoundaryPoint_iff, Sum.inr_injective.extend_apply, chartAt, extChartAt, extend_apply, inr_injective, isBoundaryPoint_iff, sum_chartAt_inr
-/
lemma boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inr x : M oplus M') := by
  rw [I.isBoundaryPoint_iff]; rw [extChartAt]; rw [ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

-- Converse to the previous direction: if `x` were not an interior point,
-- it had to be a boundary point, hence `p` were a boundary point also, contradiction.
/--
lemma `isInteriorPoint_disjointUnion_left` / 引理 `isInteriorPoint_disjointUnion_left`

English:
lemma isInteriorPoint_disjointUnion_left
  statement: {p : M oplus M'} (hp : I.IsInteriorPoint p)
  proof: by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]

中文:
引理 is整数eriorPoint_disjointUnion_left
  结论: {p : M oplus M'} (hp : I.Is整数eriorPoint p)
  证明: by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]

Depends on / 依赖: boundaryPoint_inl, isInteriorPoint_iff_not_isBoundaryPoint
-/
lemma isInteriorPoint_disjointUnion_left {p : M oplus M'} (hp : I.IsInteriorPoint p)
    (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]

/--
lemma `isInteriorPoint_disjointUnion_right` / 引理 `isInteriorPoint_disjointUnion_right`

English:
lemma isInteriorPoint_disjointUnion_right
  statement: {p : M oplus M'} (hp : I.IsInteriorPoint p)
  proof: by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]

中文:
引理 is整数eriorPoint_disjointUnion_right
  结论: {p : M oplus M'} (hp : I.Is整数eriorPoint p)
  证明: by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]

Depends on / 依赖: boundaryPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint
-/
lemma isInteriorPoint_disjointUnion_right {p : M oplus M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]

/--
lemma `interior_disjointUnion` / 引理 `interior_disjointUnion`

English:
lemma interior_disjointUnion
  proof: by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]

中文:
引理 interior_disjointUnion
  证明: by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]
-/
lemma interior_disjointUnion :
    ModelWithCorners.interior (I := I) (M oplus M') =
      Sum.inl '' (ModelWithCorners.interior (I := I) M)
      union Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]

/--
lemma `boundary_disjointUnion` / 引理 `boundary_disjointUnion`

English:
lemma boundary_disjointUnion
  statement: ModelWithCorners.boundary (I := I) (M oplus M') =
  proof: by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]

中文:
引理 boundary_disjointUnion
  结论: 带角模型.boundary (I := I) (M oplus M') =
  证明: by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]
-/
lemma boundary_disjointUnion : ModelWithCorners.boundary (I := I) (M oplus M') =
      Sum.inl '' (ModelWithCorners.boundary (I := I) M)
      union Sum.inr '' (ModelWithCorners.boundary (I := I) M') := by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]

/--
Instance `boundaryless_disjointUnion` / 实例 `boundaryless_disjointUnion`

English:
instance boundaryless_disjointUnion
  body: by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM hM' ⊢
  simp [boundary_disjointUnion, hM, hM']

中文:
实例 boundaryless_disjointUnion
  定义体: by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM hM' ⊢
  simp [boundary_disjointUnion, hM, hM']

Depends on / 依赖: Boundaryless, Boundaryless.iff_boundary_eq_empty, boundary_disjointUnion, iff_boundary_eq_empty
-/
instance boundaryless_disjointUnion
    [hM : BoundarylessManifold I M] [hM' : BoundarylessManifold I M'] :
    BoundarylessManifold I (M oplus M') := by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM hM' ⊢
  simp [boundary_disjointUnion, hM, hM']

end disjointUnion

end ModelWithCorners
