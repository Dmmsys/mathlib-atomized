/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Order.UpperLower.Relative

/-!
# Simplicial complexes

In this file, we define simplicial complexes over `𝕜`-modules.
A (pre-) abstract simplicial complex is a downwards-closed collection of nonempty finite sets,
and a simplicial complex is such a collection identified with simplices
closed by inclusion (of vertices) and intersection (of underlying sets)
whose convex hulls "glue nicely", each finite set and its convex hull corresponding respectively
to the vertices and the underlying set of a simplex.

## Main declarations

* `SimplicialComplex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `SimplicialComplex.vertices`: The zero-dimensional faces of a simplicial complex.
* `SimplicialComplex.facets`: The maximal faces of a simplicial complex.

## Notation

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `SimplicialComplex.inter_subset_convexHull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `ConvexHull` has been ported.
-/

@[expose] public section


open Finset Set

variable (𝕜 E : Type*) [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull`. It is mostly useless, as
`Geometry.SimplicialComplex.convexHull_inter_convexHull` is enough for all purposes. -/
@[ext]
/--
Definition of `SimplicialComplex` / `SimplicialComplex` 的定义

English:
structure SimplicialComplex
  parameters: extends PreAbstractSimplicialComplex E
  extends: PreAbstractSimplicialComplex E
  axioms and operations (2):
    - indep : forall {s}, s in faces -> AffineIndependent 𝕜 ((↑) : s -> E)
    - inter_subset_convexHull : forall {s t}, s in faces -> t in faces -> convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subseteq convexHull 𝕜 (s inter t : Set E)

中文:
结构 SimplicialComplex
  参数: extends PreAbstractSimplicialComplex E
  继承: PreAbstractSimplicialComplex E
  公理与运算 (2 个):
    - indep : 对任意 {s}, s in faces -> AffineIndependent 𝕜 ((↑) : s -> E)
    - inter_subset_convexHull : 对任意 {s t}, s in faces -> t in faces -> convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subseteq convexHull 𝕜 (s inter t : Set E)
-/
structure SimplicialComplex extends PreAbstractSimplicialComplex E where
  /-- the vertices in each face are affine independent: this is an implementation detail -/
  indep : forall {s}, s in faces -> AffineIndependent 𝕜 ((↑) : s -> E)
  inter_subset_convexHull : forall {s t}, s in faces -> t in faces ->
    convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subseteq convexHull 𝕜 (s inter t : Set E)

namespace SimplicialComplex

variable {𝕜 E}
variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/--
lemma `nonempty_of_mem_faces` / 引理 `nonempty_of_mem_faces`

English:
lemma nonempty_of_mem_faces
  given: (hs : s in K.faces)
  statement: s.Nonempty
  proof: .1 K.isRelLowerSet_faces hs

中文:
引理 nonempty_of_mem_faces
  条件: (hs : s in K.faces)
  结论: s.Nonempty
  证明: .1 K.isRelLowerSet_faces hs

Depends on / 依赖: K.isRelLowerSet_faces, isRelLowerSet_faces
-/
lemma nonempty_of_mem_faces (hs : s in K.faces) : s.Nonempty :=
.1 K.isRelLowerSet_faces hs

/--
theorem `empty_notMem` / 定理 `empty_notMem`

English:
theorem empty_notMem
  statement: ∅ ∉ K.faces
  proof: fun h => by simpa using nonempty_of_mem_faces h

中文:
定理 empty_notMem
  结论: ∅ ∉ K.faces
  证明: fun h => by simpa using nonempty_of_mem_faces h

Depends on / 依赖: nonempty_of_mem_faces
-/
theorem empty_notMem : ∅ ∉ K.faces :=
  fun h => by simpa using nonempty_of_mem_faces h

/--
Definition of `space` / `space` 的定义

English:
definition space
  signature: (K : SimplicialComplex 𝕜 E)
  body: ⋃ s in K.faces, convexHull 𝕜 (s : Set E)

中文:
定义 space
  签名: (K : SimplicialComplex 𝕜 E)
  定义体: ⋃ s in K.faces, convexHull 𝕜 (s : Set E)

Depends on / 依赖: K.faces, convexHull
-/
def space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s in K.faces, convexHull 𝕜 (s : Set E)

/--
theorem `mem_space_iff` / 定理 `mem_space_iff`

English:
theorem mem_space_iff
  statement: x in K.space ↔ exists s in K.faces, x in convexHull 𝕜 (s : Set E)
  proof: by
  simp [space]

中文:
定理 mem_space_iff
  结论: x in K.space ↔ 存在 s in K.faces, x in convexHull 𝕜 (s : Set E)
  证明: by
  simp [space]
-/
theorem mem_space_iff : x in K.space ↔ exists s in K.faces, x in convexHull 𝕜 (s : Set E) := by
  simp [space]

/--
theorem `convexHull_subset_space` / 定理 `convexHull_subset_space`

English:
theorem convexHull_subset_space
  given: (hs : s in K.faces)
  statement: convexHull 𝕜 s subseteq K.space
  proof: by
  convert! subset_biUnion_of_mem hs
  rfl

中文:
定理 convexHull_subset_space
  条件: (hs : s in K.faces)
  结论: convexHull 𝕜 s subseteq K.space
  证明: by
  convert! subset_biUnion_of_mem hs
  rfl

Depends on / 依赖: convert, subset_biUnion_of_mem
-/
theorem convexHull_subset_space (hs : s in K.faces) : convexHull 𝕜 s subseteq K.space := by
  convert! subset_biUnion_of_mem hs
  rfl

/--
theorem `subset_space` / 定理 `subset_space`

English:
theorem subset_space
  given: (hs : s in K.faces)
  statement: (s : Set E) subseteq K.space
  proof: (subset_convexHull 𝕜 _).trans convexHull_subset_space hs

中文:
定理 subset_space
  条件: (hs : s in K.faces)
  结论: (s : Set E) subseteq K.space
  证明: (subset_convexHull 𝕜 _).trans convexHull_subset_space hs
-/
protected theorem subset_space (hs : s in K.faces) : (s : Set E) subseteq K.space :=
(subset_convexHull 𝕜 _).trans convexHull_subset_space hs

/--
theorem `convexHull_inter_convexHull` / 定理 `convexHull_inter_convexHull`

English:
theorem convexHull_inter_convexHull
  given: (hs : s in K.faces) (ht : t in K.faces)
  proof: (K.inter_subset_convexHull hs ht).antisymm
subset_inter (convexHull_mono Set.inter_subset_left)
      convexHull_mono Set.inter_subset_right

中文:
定理 convexHull_inter_convexHull
  条件: (hs : s in K.faces) (ht : t in K.faces)
  证明: (K.inter_subset_convexHull hs ht).antisymm
subset_inter (convexHull_mono Set.inter_subset_left)
      convexHull_mono Set.inter_subset_right

Depends on / 依赖: K.inter_subset_convexHull, Set.inter_subset_left, Set.inter_subset_right, antisymm, convexHull_mono, inter_subset_convexHull, inter_subset_left, inter_subset_right, subset_inter
-/
theorem convexHull_inter_convexHull (hs : s in K.faces) (ht : t in K.faces) :
    convexHull 𝕜 s inter convexHull 𝕜 t = convexHull 𝕜 (s inter t : Set E) :=
(K.inter_subset_convexHull hs ht).antisymm
subset_inter (convexHull_mono Set.inter_subset_left)
      convexHull_mono Set.inter_subset_right

/--
theorem `down_closed` / 定理 `down_closed`

English:
theorem down_closed
  given: {s t} (hs : s in K.faces) (hst : t subseteq s) (ht : t.Nonempty)
  statement: t in K.faces
  proof: (K.isRelLowerSet_faces hs).2 hst ht

中文:
定理 down_closed
  条件: {s t} (hs : s in K.faces) (hst : t subseteq s) (ht : t.Nonempty)
  结论: t in K.faces
  证明: (K.isRelLowerSet_faces hs).2 hst ht

Depends on / 依赖: K.isRelLowerSet_faces, isRelLowerSet_faces
-/
theorem down_closed {s t} (hs : s in K.faces) (hst : t subseteq s) (ht : t.Nonempty) : t in K.faces :=
  (K.isRelLowerSet_faces hs).2 hst ht

/--
theorem `disjoint_or_exists_inter_eq_convexHull` / 定理 `disjoint_or_exists_inter_eq_convexHull`

English:
theorem disjoint_or_exists_inter_eq_convexHull
  given: (hs : s in K.faces) (ht : t in K.faces)
  proof: by
  classical
  by_contra! h
  rw [not_disjoint_iff_nonempty_inter] at h
  refine h.2 (s inter t) (K.down_closed hs inter_subset_left ?_) ?_
  · simpa [← coe_inter] using convexHull_nonempty_iff.1 (h.1.mono (K.inter_subset_convexHull hs ht))
  · rw [coe_inter, convexHull_inter_convexHull hs ht]

中文:
定理 disjoint_or_exists_inter_eq_convexHull
  条件: (hs : s in K.faces) (ht : t in K.faces)
  证明: by
  classical
  by_contra! h
  rw [not_disjoint_iff_nonempty_inter] at h
  refine h.2 (s inter t) (K.down_closed hs inter_subset_left ?_) ?_
  · simpa [← coe_inter] using convexHull_nonempty_iff.1 (h.1.mono (K.inter_subset_convexHull hs ht))
  · rw [coe_inter, convexHull_inter_convexHull hs ht]

Depends on / 依赖: K.down_closed, K.inter_subset_convexHull, classical, coe_inter, convexHull_inter_convexHull, convexHull_nonempty_iff, down_closed, inter_subset_convexHull, inter_subset_left, not_disjoint_iff_nonempty_inter
-/
theorem disjoint_or_exists_inter_eq_convexHull (hs : s in K.faces) (ht : t in K.faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 t) ∨
      exists u in K.faces, convexHull 𝕜 (s : Set E) inter convexHull 𝕜 t = convexHull 𝕜 u := by
  classical
  by_contra! h
  rw [not_disjoint_iff_nonempty_inter] at h
  refine h.2 (s inter t) (K.down_closed hs inter_subset_left ?_) ?_
  · simpa [← coe_inter] using convexHull_nonempty_iff.1 (h.1.mono (K.inter_subset_convexHull hs ht))
  · rw [coe_inter, convexHull_inter_convexHull hs ht]

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps]
/--
Definition of `ofErase` / `ofErase` 的定义

English:
definition ofErase
  signature: (faces : Set (Finset E)) (indep : forall s in faces, AffineIndependent 𝕜 ((↑) : s -> E))
  body: faces \ {∅}
  indep hs := indep _ hs.1
  isRelLowerSet_faces := by
    have : faces \ {∅} = {f in faces | f.Nonempty} := by grind
    simpa only [this] using down_closed.isRelLowerSet_sep Finset.Nonempty
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1

中文:
定义 ofErase
  签名: (faces : Set (Finset E)) (indep : 对任意 s in faces, AffineIndependent 𝕜 ((↑) : s -> E))
  定义体: faces \ {∅}
  indep hs := indep _ hs.1
  isRelLowerSet_faces := by
    have : faces \ {∅} = {f in faces | f.Nonempty} := by grind
    simpa only [this] using down_closed.isRelLowerSet_sep Finset.Nonempty
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1
-/
def ofErase (faces : Set (Finset E)) (indep : forall s in faces, AffineIndependent 𝕜 ((↑) : s -> E))
    (down_closed : IsLowerSet faces)
    (inter_subset_convexHull : forallᵉ (s in faces) (t in faces),
      convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subseteq convexHull 𝕜 (s inter t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := faces \ {∅}
  indep hs := indep _ hs.1
  isRelLowerSet_faces := by
    have : faces \ {∅} = {f in faces | f.Nonempty} := by grind
    simpa only [this] using down_closed.isRelLowerSet_sep Finset.Nonempty
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
/--
Definition of `ofSubcomplex` / `ofSubcomplex` 的定义

English:
definition ofSubcomplex
  signature: (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces subseteq K.faces)
  body: { faces := faces
    indep := fun hs => K.indep (subset hs)
    isRelLowerSet_faces := K.isRelLowerSet_faces.mono_isLowerSet down_closed subset
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }

中文:
定义 ofSubcomplex
  签名: (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces subseteq K.faces)
  定义体: { faces := faces
    indep := fun hs => K.indep (subset hs)
    isRelLowerSet_faces := K.isRelLowerSet_faces.mono_isLowerSet down_closed subset
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }

Depends on / 依赖: K.indep, K.inter_subset_convexHull, K.isRelLowerSet_faces.mono_isLowerSet, down_closed, inter_subset_convexHull, isRelLowerSet_faces, mono_isLowerSet, subset
-/
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces subseteq K.faces)
    (down_closed : IsLowerSet faces) : SimplicialComplex 𝕜 E :=
  { faces := faces
    indep := fun hs => K.indep (subset hs)
    isRelLowerSet_faces := K.isRelLowerSet_faces.mono_isLowerSet down_closed subset
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }

/-! ### Vertices -/


/--
Definition of `vertices` / `vertices` 的定义

English:
definition vertices
  signature: (K : SimplicialComplex 𝕜 E)
  body: { x | {x} in K.faces }

中文:
定义 vertices
  签名: (K : SimplicialComplex 𝕜 E)
  定义体: { x | {x} in K.faces }

Depends on / 依赖: K.faces
-/
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} in K.faces }

/--
theorem `mem_vertices` / 定理 `mem_vertices`

English:
theorem mem_vertices
  statement: x in K.vertices ↔ {x} in K.faces
  proof: Iff.rfl

中文:
定理 mem_vertices
  结论: x in K.vertices ↔ {x} in K.faces
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_vertices : x in K.vertices ↔ {x} in K.faces := Iff.rfl

/--
theorem `vertices_eq` / 定理 `vertices_eq`

English:
theorem vertices_eq
  statement: K.vertices = ⋃ k in K.faces, (k : Set E)
  proof: by
  ext x
refine ⟨fun h => mem_biUnion h mem_coe.2 mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_nonempty _)

中文:
定理 vertices_eq
  结论: K.vertices = ⋃ k in K.faces, (k : Set E)
  证明: by
  ext x
refine ⟨fun h => mem_biUnion h mem_coe.2 mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_nonempty _)

Depends on / 依赖: Finset, Finset.singleton_subset_iff, K.down_closed, down_closed, mem_biUnion, mem_coe, mem_singleton_self, singleton_nonempty, singleton_subset_iff
-/
theorem vertices_eq : K.vertices = ⋃ k in K.faces, (k : Set E) := by
  ext x
refine ⟨fun h => mem_biUnion h mem_coe.2 mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_nonempty _)

/--
theorem `vertices_subset_space` / 定理 `vertices_subset_space`

English:
theorem vertices_subset_space
  statement: K.vertices subseteq K.space
  proof: vertices_eq.subset.trans iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)

中文:
定理 vertices_subset_space
  结论: K.vertices subseteq K.space
  证明: vertices_eq.subset.trans iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)

Depends on / 依赖: subset, subset_convexHull, vertices_eq, vertices_eq.subset.trans
-/
theorem vertices_subset_space : K.vertices subseteq K.space :=
vertices_eq.subset.trans iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)

/--
theorem `vertex_mem_convexHull_iff` / 定理 `vertex_mem_convexHull_iff`

English:
theorem vertex_mem_convexHull_iff
  given: (hx : x in K.vertices) (hs : s in K.faces)
  proof: by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h

中文:
定理 vertex_mem_convexHull_iff
  条件: (hx : x in K.vertices) (hs : s in K.faces)
  证明: by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h

Depends on / 依赖: Finset, Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_right, K.inter_subset_convexHull, classical, coe_empty, coe_inter, convexHull_empty, disjoint_iff_inter_eq_empty, disjoint_singleton_right, inter_subset_convexHull, subset_convexHull
-/
theorem vertex_mem_convexHull_iff (hx : x in K.vertices) (hs : s in K.faces) :
    x in convexHull 𝕜 (s : Set E) ↔ x in s := by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h

/--
theorem `face_subset_face_iff` / 定理 `face_subset_face_iff`

English:
theorem face_subset_face_iff
  given: (hs : s in K.faces) (ht : t in K.faces)
  proof: ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_nonempty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩

中文:
定理 face_subset_face_iff
  条件: (hs : s in K.faces) (ht : t in K.faces)
  证明: ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_nonempty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩

Depends on / 依赖: Finset, Finset.singleton_subset_iff, K.down_closed, convexHull_mono, down_closed, singleton_nonempty, singleton_subset_iff, subset_convexHull, vertex_mem_convexHull_iff
-/
theorem face_subset_face_iff (hs : s in K.faces) (ht : t in K.faces) :
    convexHull 𝕜 (s : Set E) subseteq convexHull 𝕜 ↑t ↔ s subseteq t :=
  ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_nonempty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩

/-! ### Facets -/


/--
Definition of `facets` / `facets` 的定义

English:
definition facets
  signature: (K : SimplicialComplex 𝕜 E)
  body: { s in K.faces | forall ⦃t⦄, t in K.faces -> s subseteq t -> s = t }

中文:
定义 facets
  签名: (K : SimplicialComplex 𝕜 E)
  定义体: { s in K.faces | forall ⦃t⦄, t in K.faces -> s subseteq t -> s = t }

Depends on / 依赖: K.faces, subseteq
-/
def facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s in K.faces | forall ⦃t⦄, t in K.faces -> s subseteq t -> s = t }

/--
theorem `mem_facets` / 定理 `mem_facets`

English:
theorem mem_facets
  statement: s in K.facets ↔ s in K.faces ∧ forall t in K.faces, s subseteq t -> s = t
  proof: mem_sep_iff

中文:
定理 mem_facets
  结论: s in K.facets ↔ s in K.faces ∧ 对任意 t in K.faces, s subseteq t -> s = t
  证明: mem_sep_iff

Depends on / 依赖: mem_sep_iff
-/
theorem mem_facets : s in K.facets ↔ s in K.faces ∧ forall t in K.faces, s subseteq t -> s = t :=
  mem_sep_iff

/--
theorem `facets_subset` / 定理 `facets_subset`

English:
theorem facets_subset
  statement: K.facets subseteq K.faces
  proof: fun _ hs => hs.1

中文:
定理 facets_subset
  结论: K.facets subseteq K.faces
  证明: fun _ hs => hs.1
-/
theorem facets_subset : K.facets subseteq K.faces := fun _ hs => hs.1

/--
theorem `not_facet_iff_subface` / 定理 `not_facet_iff_subface`

English:
theorem not_facet_iff_subface
  given: (hs : s in K.faces)
  statement: s ∉ K.facets ↔ exists t, t in K.faces ∧ s ⊂ t
  proof: by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push Not at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)

中文:
定理 not_facet_iff_subface
  条件: (hs : s in K.faces)
  结论: s ∉ K.facets ↔ 存在 t, t in K.faces ∧ s ⊂ t
  证明: by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push Not at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)

Depends on / 依赖: Subset, Subset.antisymm, Subset.refl, antisymm
-/
theorem not_facet_iff_subface (hs : s in K.faces) : s ∉ K.facets ↔ exists t, t in K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push Not at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/


-- `HasSSubset.SSubset.ne` would be handy here
variable (𝕜 E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (SimplicialComplex 𝕜 E)
  body: ⟨fun K L =>
    { faces := K.faces inter L.faces
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := K.isRelLowerSet_faces.inter L.isRelLowerSet_faces
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩

中文:
实例 :
  签名: Min (SimplicialComplex 𝕜 E)
  定义体: ⟨fun K L =>
    { faces := K.faces inter L.faces
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := K.isRelLowerSet_faces.inter L.isRelLowerSet_faces
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩

Depends on / 依赖: K.faces, K.indep, K.inter_subset_convexHull, K.isRelLowerSet_faces.inter, L.faces, L.isRelLowerSet_faces, inter_subset_convexHull, isRelLowerSet_faces
-/
instance : Min (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { faces := K.faces inter L.faces
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := K.isRelLowerSet_faces.inter L.isRelLowerSet_faces
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (SimplicialComplex 𝕜 E)
  body: { PartialOrder.lift (fun K => K.faces) (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

中文:
实例 :
  签名: SemilatticeInf (SimplicialComplex 𝕜 E)
  定义体: { PartialOrder.lift (fun K => K.faces) (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

Depends on / 依赖: K.faces, PartialOrder, PartialOrder.lift, SimplicialComplex, SimplicialComplex.ext, inf_le_left, inf_le_right, le_inf
-/
instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { PartialOrder.lift (fun K => K.faces) (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

/--
Instance `hasBot` / 实例 `hasBot`

English:
instance hasBot
  signature: : Bot (SimplicialComplex 𝕜 E)
  body: ⟨{ faces := ∅
      indep := fun hs => (Set.notMem_empty _ hs).elim
      isRelLowerSet_faces := isRelLowerSet_empty
      inter_subset_convexHull := fun hs => (Set.notMem_empty _ hs).elim }⟩

中文:
实例 hasBot
  签名: : Bot (SimplicialComplex 𝕜 E)
  定义体: ⟨{ faces := ∅
      indep := fun hs => (Set.notMem_empty _ hs).elim
      isRelLowerSet_faces := isRelLowerSet_empty
      inter_subset_convexHull := fun hs => (Set.notMem_empty _ hs).elim }⟩

Depends on / 依赖: Set.notMem_empty, inter_subset_convexHull, isRelLowerSet_empty, isRelLowerSet_faces, notMem_empty
-/
instance hasBot : Bot (SimplicialComplex 𝕜 E) :=
  ⟨{ faces := ∅
      indep := fun hs => (Set.notMem_empty _ hs).elim
      isRelLowerSet_faces := isRelLowerSet_empty
      inter_subset_convexHull := fun hs => (Set.notMem_empty _ hs).elim }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (SimplicialComplex 𝕜 E)
  body: { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }

中文:
实例 :
  签名: OrderBot (SimplicialComplex 𝕜 E)
  定义体: { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }

Depends on / 依赖: Set.empty_subset, SimplicialComplex, SimplicialComplex.hasBot, bot_le, empty_subset, hasBot
-/
instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SimplicialComplex 𝕜 E)
  body: ⟨⊥⟩

中文:
实例 :
  签名: Inhabited (SimplicialComplex 𝕜 E)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩

variable {𝕜 E}

/--
theorem `faces_bot` / 定理 `faces_bot`

English:
theorem faces_bot
  statement: (⊥ : SimplicialComplex 𝕜 E).faces = ∅
  proof: rfl

中文:
定理 faces_bot
  结论: (⊥ : SimplicialComplex 𝕜 E).faces = ∅
  证明: rfl
-/
theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅ := rfl

/--
theorem `space_bot` / 定理 `space_bot`

English:
theorem space_bot
  statement: (⊥ : SimplicialComplex 𝕜 E).space = ∅
  proof: Set.biUnion_empty _

中文:
定理 space_bot
  结论: (⊥ : SimplicialComplex 𝕜 E).space = ∅
  证明: Set.biUnion_empty _

Depends on / 依赖: Set.biUnion_empty, biUnion_empty
-/
theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅ :=
  Set.biUnion_empty _

/--
theorem `facets_bot` / 定理 `facets_bot`

English:
theorem facets_bot
  statement: (⊥ : SimplicialComplex 𝕜 E).facets = ∅
  proof: eq_empty_of_subset_empty facets_subset

中文:
定理 facets_bot
  结论: (⊥ : SimplicialComplex 𝕜 E).facets = ∅
  证明: eq_empty_of_subset_empty facets_subset

Depends on / 依赖: eq_empty_of_subset_empty, facets_subset
-/
theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅ :=
  eq_empty_of_subset_empty facets_subset

end SimplicialComplex

end Geometry
