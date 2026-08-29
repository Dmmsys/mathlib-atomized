/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
## (Unoriented) bordism theory

This file defines the beginnings of unoriented bordism theory. We define singular manifolds,
the building blocks of unoriented bordism groups. Future pull requests will define bordisms
and the bordism groups of a topological space, and prove these are abelian groups.

The basic notion of bordism theory is that of a bordism between smooth manifolds.
Two compact smooth `n`-dimensional manifolds `M` and `N` are **bordant** if there exists a smooth
**bordism** between them: this is a compact `n+1`-dimensional manifold `W` whose boundary is
(diffeomorphic to) the disjoint union `M ⊕ N`. Being bordant is an equivalence relation
(transitivity follows from the collar neighbourhood theorem). The set of equivalence classes has an
abelian group structure, with the group operation given as disjoint union of manifolds,
and is called the `n`-th (unoriented) bordism group.

This construction can be generalised one step further, to produce an extraordinary homology theory.
Given a topological space `X`, a **singular manifold** on `X` is a closed smooth manifold `M`
together with a continuous map `M → X`. (The word *singular* does not refer to singularities,
but is by analogy to singular chains in the definition of singular homology.)

Given two `n`-dimensional singular manifolds `s` and `t`, an (oriented) bordism between `s` and `t`
is a compact smooth `n+1`-dimensional manifold `W` whose boundary is (diffeomorphic to) the disjoint
union of `s` and `t`, together with a map `W → X` which restricts to the maps on `s` and `t`.
We call `s` and `t` bordant if there exists a bordism between them: again, this defines an
equivalence relation. The `n`-th bordism group of `X` is the set of bordism classes of
`n`-dimensional singular manifolds on `X`. If `X` is a single point, this recovers the bordism
groups from the preceding paragraph.

These absolute bordism groups can be generalised further to relative bordism groups, for each
topological pair `(X, A)`; in fact, these define an extra-ordinary homology theory.

## Main definitions

- **SingularManifold X k I**: a singular manifold on a topological space `X`, is a pair `(M, f)` of
  a closed `C^k`-manifold `M` modelled on `I` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝⁿ`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.
  If we wish to emphasize the model, we will speak of a singular `I`-manifold.
  To define a disjoint union of singular manifolds, we require their domains to be manifolds
  over the same model with corners: this is why we make the model explicit.

## Main results

- `SingularManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular manifolds. This will be used to define functoriality of bordism groups.
- `SingularManifold.comap`: if `(N, f)` is a singular manifold on `X`
  and `φ : M → N` is continuous, the `comap` of `(N, f)` and `φ`
  is the induced singular manifold `(M, f ∘ φ)` on `X`.
- `SingularManifold.empty`: the empty set `M`, viewed as a manifold,
  as a singular manifold over any space `X`.
- `SingularManifold.toPUnit`: a smooth manifold induces a singular manifold on the one-point space.
- `SingularManifold.prod`: the product of a singular `I`-manifold and a singular `J`-manifold
  on the one-point space, is a singular `I.prod J`-manifold on the one-point space.
- `SingularManifold.sum`: the disjoint union of two singular `I`-manifolds
  is a singular `I`-manifold.

## Implementation notes

* We choose a bundled design for singular manifolds (and also for bordisms): to construct the
  group structure on the set of bordism classes, having that be a type is useful.
* The underlying model with corners is a type parameter, as defining a disjoint union of singular
  manifolds requires their domains to be manifolds over the same model with corners.
  Thus, either we restrict to manifolds modelled over `𝓡n` (which we prefer not to),
  or the model must be a type parameter.
* Having `SingularManifold` contain the type `M` as explicit structure field is not ideal,
  as this adds a universe parameter to the structure. However, this is the best solution we found:
  we generally cannot have `M` live in the same universe as `X` (a common case is `X` being
  `PUnit`), and determining the universe of `M` from the universes of `E` and `H` would make
  `SingularManifold.map` painful to state (as that would require `ULift`ing `M`).

## TODO
- define bordisms and prove basic constructions (e.g. reflexivity, symmetry, transitivity)
  and operations (e.g. disjoint union, sum with the empty set)
- define the bordism relation and prove it is an equivalence relation
- define the unoriented bordism group (the set of bordism classes) and prove it is an abelian group
- for bordisms on a one-point space, define multiplication and prove the bordism ring structure
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular manifold, bordism, bordism group
-/

public section

open scoped Manifold
open Module Set

suppress_compilation

/--
Definition of `SingularManifold.` / `SingularManifold.` 的定义

English:
structure SingularManifold.{u}
  parameters: (X : Type*) [TopologicalSpace X] (k : WithTop Nat∞)
  axioms and operations (8):
    - M : Type u
    - [topSpaceM : TopologicalSpace M]
    - [chartedSpace : ChartedSpace H M]
    - [isManifold : IsManifold I k M]
    - [compactSpace : CompactSpace M]
    - [boundaryless : BoundarylessManifold I M]
    - f : M -> X
    - hf : Continuous f

中文:
结构 SingularManifold.{u}
  参数: (X : 类型) [TopologicalSpace X] (k : WithTop 自然数∞)
  公理与运算 (8 个):
    - M : 类型u
    - [topSpaceM : TopologicalSpace M]
    - [chartedSpace : ChartedSpace H M]
    - [isManifold : IsManifold I k M]
    - [compactSpace : CompactSpace M]
    - [boundaryless : BoundarylessManifold I M]
    - f : M -> X
    - hf : Continuous f
-/
structure SingularManifold.{u} (X : Type*) [TopologicalSpace X] (k : WithTop Nat∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [TopologicalSpace H] (I : ModelWithCorners Real E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M -> X
  hf : Continuous f

namespace SingularManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop Nat∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

instance {s : SingularManifold X k I} : TopologicalSpace s.M := s.topSpaceM

instance {s : SingularManifold X k I} : ChartedSpace H s.M := s.chartedSpace

instance {s : SingularManifold X k I} : IsManifold I k s.M := s.isManifold

instance {s : SingularManifold X k I} : CompactSpace s.M := s.compactSpace

instance {s : SingularManifold X k I} : BoundarylessManifold I s.M := s.boundaryless

-- This is part of proving functoriality of the bordism groups.
/--
Definition of `map.` / `map.` 的定义

English:
definition map.{u}
  signature: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop Nat∞}
  body: s.M
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp, mfld_simps]

中文:
定义 map.{u}
  签名: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop 自然数∞}
  定义体: s.M
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp, mfld_simps]
-/
@[expose] def map.{u} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop Nat∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [TopologicalSpace H] {I : ModelWithCorners Real E H} (s : SingularManifold.{u} X k I)
    {φ : X -> Y} (hφ : Continuous φ) : SingularManifold.{u} Y k I where
  M := s.M
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp, mfld_simps]
/--
lemma `map_f` / 引理 `map_f`

English:
lemma map_f
  given: (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 map_f
  条件: (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ)
  证明: rfl

@[simp, mfld_simps]
-/
lemma map_f (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

@[simp, mfld_simps]
/--
lemma `map_M` / 引理 `map_M`

English:
lemma map_M
  given: (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ)
  proof: rfl

中文:
引理 map_M
  条件: (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ)
  证明: rfl
-/
lemma map_M (s : SingularManifold X k I) {φ : X -> Y} (hφ : Continuous φ) :
    (s.map hφ).M = s.M :=
  rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: (s : SingularManifold X k I)
  proof: by
  simp [Function.comp_def]

中文:
引理 map_comp
  结论: (s : SingularManifold X k I)
  证明: by
  simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
lemma map_comp (s : SingularManifold X k I)
    {φ : X -> Y} {ψ : Y -> Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']

variable (M I) in
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : SingularManifold M k I where
  body: M
  f := id
  hf := continuous_id

中文:
定义 refl
  签名: : SingularManifold M k I where
  定义体: M
  f := id
  hf := continuous_id
-/
noncomputable def refl : SingularManifold M k I where
  M := M
  f := id
  hf := continuous_id

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (s : SingularManifold X k I)
  body: M
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]

中文:
定义 comap
  签名: (s : SingularManifold X k I)
  定义体: M
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]
-/
@[expose] noncomputable def comap (s : SingularManifold X k I)
    {φ : M -> s.M} (hφ : Continuous φ) : SingularManifold X k I where
  M := M
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]
/--
lemma `comap_M` / 引理 `comap_M`

English:
lemma comap_M
  given: (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ)
  proof: by
  rfl

@[simp, mfld_simps]

中文:
引理 comap_M
  条件: (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ)
  证明: by
  rfl

@[simp, mfld_simps]
-/
lemma comap_M (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ) :
    (s.comap hφ).M = M := by
  rfl

@[simp, mfld_simps]
/--
lemma `comap_f` / 引理 `comap_f`

English:
lemma comap_f
  given: (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ)
  proof: rfl

中文:
引理 comap_f
  条件: (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ)
  证明: rfl
-/
lemma comap_f (s : SingularManifold X k I) {φ : M -> s.M} (hφ : Continuous φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (X) in
/--
Definition of `empty.` / `empty.` 的定义

English:
definition empty.{u}
  signature: (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  body: M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x => (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]

中文:
定义 empty.{u}
  签名: (M : 类型u) [TopologicalSpace M] [ChartedSpace H M]
  定义体: M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x => (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]
-/
@[expose] def empty.{u} (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners Real E H) [IsManifold I k M] [IsEmpty M] : SingularManifold X k I where
  M := M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x => (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]
/--
lemma `empty_M` / 引理 `empty_M`

English:
lemma empty_M
  given: [IsEmpty M]
  statement: (empty X M I (k := k)).M = M
  proof: (rfl)

中文:
引理 empty_M
  条件: [IsEmpty M]
  结论: (empty X M I (k := k)).M = M
  证明: (rfl)
-/
lemma empty_M [IsEmpty M] : (empty X M I (k := k)).M = M := (rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: M] : IsEmpty (SingularManifold.empty X M I (k := k)).M
  body: inferInstanceAs IsEmpty M

中文:
实例 [IsEmpty
  签名: M] : IsEmpty (SingularManifold.empty X M I (k := k)).M
  定义体: inferInstanceAs IsEmpty M
-/
instance [IsEmpty M] : IsEmpty (SingularManifold.empty X M I (k := k)).M :=
inferInstanceAs IsEmpty M

variable (M I) in
/--
Definition of `toPUnit` / `toPUnit` 的定义

English:
definition toPUnit
  signature: : SingularManifold PUnit k I where
  body: M
  f := fun _ => PUnit.unit
  hf := continuous_const

中文:
定义 toPUnit
  签名: : SingularManifold PUnit k I where
  定义体: M
  f := fun _ => PUnit.unit
  hf := continuous_const
-/
@[expose] def toPUnit : SingularManifold PUnit k I where
  M := M
  f := fun _ => PUnit.unit
  hf := continuous_const

variable {I' : ModelWithCorners Real E' H'} [FiniteDimensional Real E']

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : SingularManifold PUnit k I) (t : SingularManifold PUnit k I')
  body: s.M × t.M
  f := fun _ => PUnit.unit
  hf := continuous_const

中文:
定义 prod
  签名: (s : SingularManifold PUnit k I) (t : SingularManifold PUnit k I')
  定义体: s.M × t.M
  f := fun _ => PUnit.unit
  hf := continuous_const
-/
@[expose] def prod (s : SingularManifold PUnit k I) (t : SingularManifold PUnit k I') :
    SingularManifold PUnit k (I.prod I') where
  M := s.M × t.M
  f := fun _ => PUnit.unit
  hf := continuous_const

variable (s t : SingularManifold X k I)

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (s t : SingularManifold X k I)
  body: s.M oplus t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]

中文:
定义 sum
  签名: (s t : SingularManifold X k I)
  定义体: s.M oplus t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]
-/
@[expose] def sum (s t : SingularManifold X k I) : SingularManifold X k I where
  M := s.M oplus t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]
/--
lemma `sum_M` / 引理 `sum_M`

English:
lemma sum_M
  given: (s t : SingularManifold X k I)
  statement: (s.sum t).M = (s.M oplus t.M)
  proof: (rfl)

@[simp, mfld_simps]

中文:
引理 sum_M
  条件: (s t : SingularManifold X k I)
  结论: (s.sum t).M = (s.M oplus t.M)
  证明: (rfl)

@[simp, mfld_simps]
-/
lemma sum_M (s t : SingularManifold X k I) : (s.sum t).M = (s.M oplus t.M) := (rfl)

@[simp, mfld_simps]
/--
lemma `sum_f` / 引理 `sum_f`

English:
lemma sum_f
  given: (s t : SingularManifold X k I)
  statement: (s.sum t).f = Sum.elim s.f t.f
  proof: (rfl)

中文:
引理 sum_f
  条件: (s t : SingularManifold X k I)
  结论: (s.sum t).f = Sum.elim s.f t.f
  证明: (rfl)
-/
lemma sum_f (s t : SingularManifold X k I) : (s.sum t).f = Sum.elim s.f t.f := (rfl)

end SingularManifold
