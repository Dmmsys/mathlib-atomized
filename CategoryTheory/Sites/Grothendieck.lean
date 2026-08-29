/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Copy
public import Mathlib.Data.Set.Subsingleton

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology

as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in
`Mathlib/CategoryTheory/Sites/Pretopology.lean`. The topology associated
to a topological space is defined in `Mathlib/CategoryTheory/Sites/Spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/

@[expose] public section


universe v₁ u₁ v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See also [nlab] or [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z4, wikidata Q1062242]
/--
Definition of `GrothendieckTopology` / `GrothendieckTopology` 的定义

English:
structure GrothendieckTopology
  parameters: where
  axioms and operations (4):
    - sieves : forall X : C, Set (Sieve X)
    - top_mem' : forall X, ⊤ in sieves X
    - pullback_stable' : forall ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S in sieves X -> S.pullback f in sieves Y
    - transitive' : forall ⦃X⦄ ⦃S : Sieve X⦄ (_ : S in sieves X) (R : Sieve X), (forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in sieves Y) -> R in sieves X

中文:
结构 Grothendieck拓扑
  参数: where
  公理与运算 (4 个):
    - sieves : 对任意 X : C, 集合 (筛 X)
    - top_mem' : 对任意 X, ⊤ in sieves X
    - pullback_stable' : 对任意 ⦃X Y : C⦄ ⦃S : 筛 X⦄ (f : Y ⟶ X), S in sieves X -> S.pullback f in sieves Y
    - transitive' : 对任意 ⦃X⦄ ⦃S : 筛 X⦄ (_ : S in sieves X) (R : 筛 X), (对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in sieves Y) -> R in sieves X
-/
structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
  which satisfy some axioms. -/
  sieves : forall X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
  Use `GrothendieckTopology.top_mem`. -/
  top_mem' : forall X, ⊤ in sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : forall ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S in sieves X -> S.pullback f in sieves Y
  /-- Transitivity of sieves in a Grothendieck topology. Use `GrothendieckTopology.transitive`. -/
  transitive' :
    forall ⦃X⦄ ⦃S : Sieve X⦄ (_ : S in sieves X) (R : Sieve X),
      (forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in sieves Y) -> R in sieves X

namespace GrothendieckTopology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DFunLike (GrothendieckTopology C) C (fun X => Set (Sieve X))
  body: sieves J X
  coe_injective J₁ J₂ h := by cases J₁; cases J₂; congr

中文:
实例 :
  签名: 依赖函数状 (Grothendieck拓扑 C) C (fun X => 集合 (筛 X))
  定义体: sieves J X
  coe_injective J₁ J₂ h := by cases J₁; cases J₂; congr

Depends on / 依赖: sieves
-/
instance : DFunLike (GrothendieckTopology C) C (fun X => Set (Sieve X)) where
  coe J X := sieves J X
  coe_injective J₁ J₂ h := by cases J₁; cases J₂; congr

variable {C}
variable {X Y : C} {S R : Sieve X}
variable (J : GrothendieckTopology C)

/-- An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂)
  statement: J₁ = J₂
  proof: DFunLike.coe_injective h

@[simp]

中文:
定理 ext
  条件: {J₁ J₂ : Grothendieck拓扑 C} (h : (J₁ : 对任意 X : C, 集合 (筛 X)) = J₂)
  结论: J₁ = J₂
  证明: DFunLike.coe_injective h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂ :=
  DFunLike.coe_injective h

@[simp]
/--
theorem `mem_sieves_iff_coe` / 定理 `mem_sieves_iff_coe`

English:
theorem mem_sieves_iff_coe
  statement: S in J.sieves X ↔ S in J X
  proof: Iff.rfl

中文:
定理 mem_sieves_iff_coe
  结论: S in J.sieves X ↔ S in J X
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_sieves_iff_coe : S in J.sieves X ↔ S in J X :=
  Iff.rfl

/-- Also known as the maximality axiom. -/
@[simp, grind .]
/--
theorem `top_mem` / 定理 `top_mem`

English:
theorem top_mem
  given: (X : C)
  statement: ⊤ in J X
  proof: J.top_mem' X

中文:
定理 top_mem
  条件: (X : C)
  结论: ⊤ in J X
  证明: J.top_mem' X

Depends on / 依赖: J.top_mem, top_mem
-/
theorem top_mem (X : C) : ⊤ in J X :=
  J.top_mem' X

/-- Also known as the stability axiom. -/
@[simp, grind .]
/--
theorem `pullback_stable` / 定理 `pullback_stable`

English:
theorem pullback_stable
  given: (f : Y ⟶ X) (hS : S in J X)
  statement: S.pullback f in J Y
  proof: J.pullback_stable' f hS

中文:
定理 pullback_stable
  条件: (f : Y ⟶ X) (hS : S in J X)
  结论: S.pullback f in J Y
  证明: J.pullback_stable' f hS

Depends on / 依赖: J.pullback_stable, pullback_stable
-/
theorem pullback_stable (f : Y ⟶ X) (hS : S in J X) : S.pullback f in J Y :=
  J.pullback_stable' f hS

variable {J} in
@[simp]
/--
lemma `pullback_mem_iff_of_isIso` / 引理 `pullback_mem_iff_of_isIso`

English:
lemma pullback_mem_iff_of_isIso
  given: {i : X ⟶ Y} [IsIso i] {S : Sieve Y}
  proof: by
  refine ⟨fun H => ?_, J.pullback_stable i⟩
  convert! J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp]; rw [IsIso.inv_hom_id]; rw [Sieve.pullback_id]

@[grind .]

中文:
引理 pullback_mem_iff_of_isIso
  条件: {i : X ⟶ Y} [是同构 i] {S : 筛 Y}
  证明: by
  refine ⟨fun H => ?_, J.pullback_stable i⟩
  convert! J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp]; rw [IsIso.inv_hom_id]; rw [Sieve.pullback_id]

@[grind .]

Depends on / 依赖: IsIso.inv_hom_id, J.pullback_stable, Sieve.pullback_comp, Sieve.pullback_id, convert, inv_hom_id, pullback_comp, pullback_id, pullback_stable
-/
lemma pullback_mem_iff_of_isIso {i : X ⟶ Y} [IsIso i] {S : Sieve Y} :
    S.pullback i in J _ ↔ S in J _ := by
  refine ⟨fun H => ?_, J.pullback_stable i⟩
  convert! J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp]; rw [IsIso.inv_hom_id]; rw [Sieve.pullback_id]

@[grind .]
/--
theorem `transitive` / 定理 `transitive`

English:
theorem transitive
  given: (hS : S in J X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y)
  proof: J.transitive' hS R h

中文:
定理 transitive
  条件: (hS : S in J X) (R : 筛 X) (h : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y)
  证明: J.transitive' hS R h

Depends on / 依赖: J.transitive, transitive
-/
theorem transitive (hS : S in J X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) :
    R in J X :=
  J.transitive' hS R h

/--
theorem `covering_of_eq_top` / 定理 `covering_of_eq_top`

English:
theorem covering_of_eq_top
  statement: S = ⊤ -> S in J X
  proof: fun h => h.symm ▸ J.top_mem X

中文:
定理 covering_of_eq_top
  结论: S = ⊤ -> S in J X
  证明: fun h => h.symm ▸ J.top_mem X

Depends on / 依赖: J.top_mem, h.symm, top_mem
-/
theorem covering_of_eq_top : S = ⊤ -> S in J X := fun h => h.symm ▸ J.top_mem X

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (J : GrothendieckTopology C) (s : forall X : C, Set (Sieve X)) (h : J.sieves = s)
  body: s
  top_mem' := h ▸ J.top_mem'
  pullback_stable' := h ▸ J.pullback_stable'
  transitive' := h ▸ J.transitive'

@[simp]

中文:
定义 copy
  签名: (J : Grothendieck拓扑 C) (s : 对任意 X : C, 集合 (筛 X)) (h : J.sieves = s)
  定义体: s
  top_mem' := h ▸ J.top_mem'
  pullback_stable' := h ▸ J.pullback_stable'
  transitive' := h ▸ J.transitive'

@[simp]
-/
def copy (J : GrothendieckTopology C) (s : forall X : C, Set (Sieve X)) (h : J.sieves = s) :
    GrothendieckTopology C where
  sieves := s
  top_mem' := h ▸ J.top_mem'
  pullback_stable' := h ▸ J.pullback_stable'
  transitive' := h ▸ J.transitive'

@[simp]
/--
theorem `sieves_copy` / 定理 `sieves_copy`

English:
theorem sieves_copy
  given: {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s}
  proof: rfl

@[simp]

中文:
定理 sieves_copy
  条件: {J : Grothendieck拓扑 C} {s : 对任意 X : C, 集合 (筛 X)} {h : J.sieves = s}
  证明: rfl

@[simp]
-/
theorem sieves_copy {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s} :
    (J.copy s h).sieves = s :=
  rfl

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s}
  proof: rfl

中文:
定理 coe_copy
  条件: {J : Grothendieck拓扑 C} {s : 对任意 X : C, 集合 (筛 X)} {h : J.sieves = s}
  证明: rfl
-/
theorem coe_copy {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s} :
    ⇑(J.copy s h) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s}
  proof: GrothendieckTopology.ext h.symm

中文:
定理 copy_eq
  条件: {J : Grothendieck拓扑 C} {s : 对任意 X : C, 集合 (筛 X)} {h : J.sieves = s}
  证明: GrothendieckTopology.ext h.symm

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.ext, h.symm
-/
theorem copy_eq {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s} :
    J.copy s h = J :=
  GrothendieckTopology.ext h.symm

/-- If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See also discussion after [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z5 "(2)"]
/--
theorem `superset_covering` / 定理 `superset_covering`

English:
theorem superset_covering
  given: (Hss : S <= R) (sjx : S in J X)
  statement: R in J X
  proof: by
  apply J.transitive sjx R fun Y f hf => _
  intro Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff]; rw [← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

中文:
定理 superset_covering
  条件: (Hss : S <= R) (sjx : S in J X)
  结论: R in J X
  证明: by
  apply J.transitive sjx R fun Y f hf => _
  intro Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff]; rw [← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

Depends on / 依赖: J.transitive, S.pullback_eq_top_of_mem, Sieve.pullback_monotone, covering_of_eq_top, pullback_eq_top_of_mem, pullback_monotone, top_le_iff, transitive
-/
theorem superset_covering (Hss : S <= R) (sjx : S in J X) : R in J X := by
  apply J.transitive sjx R fun Y f hf => _
  intro Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff]; rw [← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

/-- The intersection of two covering sieves is covering.

See also [MM92] Chapter III, Section 2, Definition 1 (iv). -/
@[stacks 00Z5 "(1)"]
/--
theorem `intersection_covering` / 定理 `intersection_covering`

English:
theorem intersection_covering
  given: (rj : R in J X) (sj : S in J X)
  statement: R ⊓ S in J X
  proof: by
  apply J.transitive rj _ fun Y f Hf => _
  intro Y f hf
  rw [Sieve.pullback_inter]; rw [R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]

中文:
定理 intersection_covering
  条件: (rj : R in J X) (sj : S in J X)
  结论: R ⊓ S in J X
  证明: by
  apply J.transitive rj _ fun Y f Hf => _
  intro Y f hf
  rw [Sieve.pullback_inter]; rw [R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]

Depends on / 依赖: J.transitive, R.pullback_eq_top_of_mem, Sieve.pullback_inter, pullback_eq_top_of_mem, pullback_inter, transitive
-/
theorem intersection_covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X := by
  apply J.transitive rj _ fun Y f Hf => _
  intro Y f hf
  rw [Sieve.pullback_inter]; rw [R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]
/--
theorem `intersection_covering_iff` / 定理 `intersection_covering_iff`

English:
theorem intersection_covering_iff
  statement: R ⊓ S in J X ↔ R in J X ∧ S in J X
  proof: ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

中文:
定理 intersection_covering_iff
  结论: R ⊓ S in J X ↔ R in J X ∧ S in J X
  证明: ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

Depends on / 依赖: J.superset_covering, inf_le_left, inf_le_right, intersection_covering, superset_covering
-/
theorem intersection_covering_iff : R ⊓ S in J X ↔ R in J X ∧ S in J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

/--
theorem `bind_covering` / 定理 `bind_covering`

English:
theorem bind_covering
  statement: {S : Sieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X)
  proof: J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

中文:
定理 bind_covering
  结论: {S : 筛 X} {R : 对任意 ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> 筛 Y} (hS : S in J X)
  证明: J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

Depends on / 依赖: J.transitive, Sieve.le_pullback_bind, le_pullback_bind, superset_covering, transitive
-/
theorem bind_covering {S : Sieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X)
    (hR : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in J Y) : Sieve.bind S R in J X :=
  J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

/--
lemma `bindOfArrows` / 引理 `bindOfArrows`

English:
lemma bindOfArrows
  statement: {ι : Type*} {X : C} {Z : ι -> C} {f : forall i, Z i ⟶ X} {R : forall i, Presieve (Z i)}
  proof: by
  refine J.superset_covering (Presieve.bind_ofArrows_le_bindOfArrows _ _ _) ?_
  exact J.bind_covering h fun _ _ _ => J.pullback_stable _ (hR _)

中文:
引理 bindOfArrows
  结论: {ι : 类型} {X : C} {Z : ι -> C} {f : 对任意 i, Z i ⟶ X} {R : 对任意 i, Presieve (Z i)}
  证明: by
  refine J.superset_covering (Presieve.bind_ofArrows_le_bindOfArrows _ _ _) ?_
  exact J.bind_covering h fun _ _ _ => J.pullback_stable _ (hR _)

Depends on / 依赖: J.bind_covering, J.pullback_stable, J.superset_covering, Presieve, Presieve.bind_ofArrows_le_bindOfArrows, bind_covering, bind_ofArrows_le_bindOfArrows, pullback_stable, superset_covering
-/
lemma bindOfArrows {ι : Type*} {X : C} {Z : ι -> C} {f : forall i, Z i ⟶ X} {R : forall i, Presieve (Z i)}
    (h : Sieve.ofArrows Z f in J X) (hR : forall i, Sieve.generate (R i) in J _) :
    Sieve.generate (Presieve.bindOfArrows Z f R) in J X := by
  refine J.superset_covering (Presieve.bind_ofArrows_le_bindOfArrows _ _ _) ?_
  exact J.bind_covering h fun _ _ _ => J.pullback_stable _ (hR _)

/--
Definition of `Covers` / `Covers` 的定义

English:
definition Covers
  signature: (S : Sieve X) (f : Y ⟶ X)
  body: S.pullback f in J Y

中文:
定义 Covers
  签名: (S : 筛 X) (f : Y ⟶ X)
  定义体: S.pullback f in J Y

Depends on / 依赖: S.pullback, pullback
-/
def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f in J Y

/--
theorem `covers_iff` / 定理 `covers_iff`

English:
theorem covers_iff
  given: (S : Sieve X) (f : Y ⟶ X)
  statement: J.Covers S f ↔ S.pullback f in J Y
  proof: Iff.rfl

中文:
定理 covers_iff
  条件: (S : 筛 X) (f : Y ⟶ X)
  结论: J.Covers S f ↔ S.pullback f in J Y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y :=
  Iff.rfl

/--
theorem `covering_iff_covers_id` / 定理 `covering_iff_covers_id`

English:
theorem covering_iff_covers_id
  given: (S : Sieve X)
  statement: S in J X ↔ J.Covers S (𝟙 X)
  proof: by simp [covers_iff]

中文:
定理 covering_iff_covers_id
  条件: (S : 筛 X)
  结论: S in J X ↔ J.Covers S (𝟙 X)
  证明: by simp [covers_iff]

Depends on / 依赖: covers_iff
-/
theorem covering_iff_covers_id (S : Sieve X) : S in J X ↔ J.Covers S (𝟙 X) := by simp [covers_iff]

/--
theorem `arrow_max` / 定理 `arrow_max`

English:
theorem arrow_max
  given: (f : Y ⟶ X) (S : Sieve X) (hf : S f)
  statement: J.Covers S f
  proof: by
  rw [Covers]; rw [(Sieve.mem_iff_pullback_eq_top f).1 hf]
  apply J.top_mem

中文:
定理 arrow_max
  条件: (f : Y ⟶ X) (S : 筛 X) (hf : S f)
  结论: J.Covers S f
  证明: by
  rw [Covers]; rw [(Sieve.mem_iff_pullback_eq_top f).1 hf]
  apply J.top_mem

Depends on / 依赖: Covers, J.top_mem, Sieve.mem_iff_pullback_eq_top, mem_iff_pullback_eq_top, top_mem
-/
theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [Covers]; rw [(Sieve.mem_iff_pullback_eq_top f).1 hf]
  apply J.top_mem

/--
theorem `arrow_stable` / 定理 `arrow_stable`

English:
theorem arrow_stable
  given: (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y)
  proof: by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

中文:
定理 arrow_stable
  条件: (f : Y ⟶ X) (S : 筛 X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y)
  证明: by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

Depends on / 依赖: Sieve.pullback_comp, covers_iff, pullback_comp
-/
theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) :
    J.Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

/--
theorem `arrow_trans` / 定理 `arrow_trans`

English:
theorem arrow_trans
  given: (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f)
  proof: by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg

中文:
定理 arrow_trans
  条件: (f : Y ⟶ X) (S R : 筛 X) (h : J.Covers S f)
  证明: by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg

Depends on / 依赖: J.transitive, Sieve.pullback_comp, pullback_comp, transitive
-/
theorem arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) :
    (forall {Z : C} (g : Z ⟶ X), S g -> J.Covers R g) -> J.Covers R f := by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg

/--
theorem `arrow_intersect` / 定理 `arrow_intersect`

English:
theorem arrow_intersect
  given: (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f)
  proof: by simpa [covers_iff] using And.intro hS hR

中文:
定理 arrow_intersect
  条件: (f : Y ⟶ X) (S R : 筛 X) (hS : J.Covers S f) (hR : J.Covers R f)
  证明: by simpa [covers_iff] using And.intro hS hR

Depends on / 依赖: And.intro, covers_iff
-/
theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) :
    J.Covers (S ⊓ R) f := by simpa [covers_iff] using And.intro hS hR

variable (C)

/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : GrothendieckTopology C where
  body: {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff]; rw [← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

中文:
定义 trivial
  签名: : Grothendieck拓扑 C where
  定义体: {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff]; rw [← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS
-/
def trivial : GrothendieckTopology C where
  sieves _ := {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff]; rw [← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

/--
Definition of `discrete` / `discrete` 的定义

English:
definition discrete
  signature: : GrothendieckTopology C where
  body: Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

中文:
定义 discrete
  签名: : Grothendieck拓扑 C where
  定义体: Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

Depends on / 依赖: Set.univ
-/
def discrete : GrothendieckTopology C where
  sieves _ := Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

variable {C}

/--
theorem `trivial_covering` / 定理 `trivial_covering`

English:
theorem trivial_covering
  statement: S in trivial C X ↔ S = ⊤
  proof: Set.mem_singleton_iff

@[stacks 00Z6]

中文:
定理 trivial_covering
  结论: S in trivial C X ↔ S = ⊤
  证明: Set.mem_singleton_iff

@[stacks 00Z6]

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem trivial_covering : S in trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff

@[stacks 00Z6]
/--
Instance `instLEGrothendieckTopology` / 实例 `instLEGrothendieckTopology`

English:
instance instLEGrothendieckTopology
  signature: : LE (GrothendieckTopology C) where
  body: (J₁ : forall X : C, Set (Sieve X)) <= (J₂ : forall X : C, Set (Sieve X))

中文:
实例 instLEGrothendieckTopology
  签名: : LE (Grothendieck拓扑 C) where
  定义体: (J₁ : forall X : C, Set (Sieve X)) <= (J₂ : forall X : C, Set (Sieve X))
-/
instance instLEGrothendieckTopology : LE (GrothendieckTopology C) where
  le J₁ J₂ := (J₁ : forall X : C, Set (Sieve X)) <= (J₂ : forall X : C, Set (Sieve X))

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {J₁ J₂ : GrothendieckTopology C}
  statement: J₁ <= J₂ ↔ (J₁ : forall X : C, Set (Sieve X)) <= J₂
  proof: Iff.rfl

@[stacks 00Z6]

中文:
定理 le_def
  条件: {J₁ J₂ : Grothendieck拓扑 C}
  结论: J₁ <= J₂ ↔ (J₁ : 对任意 X : C, 集合 (筛 X)) <= J₂
  证明: Iff.rfl

@[stacks 00Z6]

Depends on / 依赖: Iff.rfl
-/
theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ <= J₂ ↔ (J₁ : forall X : C, Set (Sieve X)) <= J₂ :=
  Iff.rfl

@[stacks 00Z6]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (GrothendieckTopology C)
  body: { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

@[stacks 00Z7]

中文:
实例 :
  签名: 偏序 (Grothendieck拓扑 C)
  定义体: { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

@[stacks 00Z7]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.ext, instLEGrothendieckTopology, le_antisymm, le_def, le_def.mpr, le_refl, le_rfl, le_trans
-/
instance : PartialOrder (GrothendieckTopology C) :=
  { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

@[stacks 00Z7]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (GrothendieckTopology C)
  body: { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

中文:
实例 :
  签名: 下确界集 (Grothendieck拓扑 C)
  定义体: { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

Depends on / 依赖: J.pullback_stable, J.transitive, pullback_stable, sieves, top_mem, transitive
-/
instance : InfSet (GrothendieckTopology C) where
  sInf T :=
    { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X)
  proof: by
  change S in sInf (sieves '' s) X ↔ _
  simp

@[stacks 00Z7]

中文:
引理 mem_sInf
  条件: (s : 集合 (Grothendieck拓扑 C)) {X : C} (S : 筛 X)
  证明: by
  change S in sInf (sieves '' s) X ↔ _
  simp

@[stacks 00Z7]

Depends on / 依赖: sieves
-/
lemma mem_sInf (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X) :
    S in sInf s X ↔ forall t in s, S in t X := by
  change S in sInf (sieves '' s) X ↔ _
  simp

@[stacks 00Z7]
/--
theorem `isGLB_sInf` / 定理 `isGLB_sInf`

English:
theorem isGLB_sInf
  given: (s : Set (GrothendieckTopology C))
  statement: IsGLB s (sInf s)
  proof: by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · rfl
  · exact _root_.isGLB_sInf _

中文:
定理 isGLB_sInf
  条件: (s : 集合 (Grothendieck拓扑 C))
  结论: IsGLB s (sInf s)
  证明: by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · rfl
  · exact _root_.isGLB_sInf _

Depends on / 依赖: IsGLB.of_image, _root_, _root_.isGLB_sInf, isGLB_sInf, of_image, sieves
-/
theorem isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s) := by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · rfl
  · exact _root_.isGLB_sInf _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (GrothendieckTopology C)
  body: fast_instance% CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact (completeLatticeOfInf _ isGLB_sInf).le_top (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact (completeLatticeOfInf _ isGLB_sInf).bot_le (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

中文:
实例 :
  签名: 完备格 (Grothendieck拓扑 C)
  定义体: fast_instance% CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact (completeLatticeOfInf _ isGLB_sInf).le_top (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact (completeLatticeOfInf _ isGLB_sInf).bot_le (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

Depends on / 依赖: CompleteLattice, CompleteLattice.copy, Set.mem_univ, bot_le, completeLatticeOfInf, covering_of_eq_top, discrete, fast_instance, isGLB_sInf, le_antisymm, le_top, mem_univ, trivial_covering
-/
instance : CompleteLattice (GrothendieckTopology C) :=
  fast_instance% CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact (completeLatticeOfInf _ isGLB_sInf).le_top (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact (completeLatticeOfInf _ isGLB_sInf).bot_le (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (GrothendieckTopology C)
  body: ⟨⊤⟩

@[simp]

中文:
实例 :
  签名: 可居 (Grothendieck拓扑 C)
  定义体: ⟨⊤⟩

@[simp]
-/
instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
/--
theorem `trivial_eq_bot` / 定理 `trivial_eq_bot`

English:
theorem trivial_eq_bot
  statement: trivial C = ⊥
  proof: rfl

@[simp]

中文:
定理 trivial_eq_bot
  结论: trivial C = ⊥
  证明: rfl

@[simp]
-/
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl

@[simp]
/--
theorem `discrete_eq_top` / 定理 `discrete_eq_top`

English:
theorem discrete_eq_top
  statement: discrete C = ⊤
  proof: rfl

@[simp]

中文:
定理 discrete_eq_top
  结论: discrete C = ⊤
  证明: rfl

@[simp]
-/
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl

@[simp]
/--
theorem `bot_covering` / 定理 `bot_covering`

English:
theorem bot_covering
  statement: S in (⊥ : GrothendieckTopology C) X ↔ S = ⊤
  proof: trivial_covering

@[simp]

中文:
定理 bot_covering
  结论: S in (⊥ : Grothendieck拓扑 C) X ↔ S = ⊤
  证明: trivial_covering

@[simp]

Depends on / 依赖: trivial_covering
-/
theorem bot_covering : S in (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering

@[simp]
/--
theorem `top_covering` / 定理 `top_covering`

English:
theorem top_covering
  statement: S in (⊤ : GrothendieckTopology C) X
  proof: ⟨⟩

中文:
定理 top_covering
  结论: S in (⊤ : Grothendieck拓扑 C) X
  证明: ⟨⟩
-/
theorem top_covering : S in (⊤ : GrothendieckTopology C) X :=
  ⟨⟩

/--
theorem `bot_covers` / 定理 `bot_covers`

English:
theorem bot_covers
  given: (S : Sieve X) (f : Y ⟶ X)
  statement: (⊥ : GrothendieckTopology C).Covers S f ↔ S f
  proof: by
  rw [covers_iff]; rw [bot_covering]; rw [← Sieve.mem_iff_pullback_eq_top]

@[simp]

中文:
定理 bot_covers
  条件: (S : 筛 X) (f : Y ⟶ X)
  结论: (⊥ : Grothendieck拓扑 C).Covers S f ↔ S f
  证明: by
  rw [covers_iff]; rw [bot_covering]; rw [← Sieve.mem_iff_pullback_eq_top]

@[simp]

Depends on / 依赖: Sieve.mem_iff_pullback_eq_top, bot_covering, covers_iff, mem_iff_pullback_eq_top
-/
theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff]; rw [bot_covering]; rw [← Sieve.mem_iff_pullback_eq_top]

@[simp]
/--
theorem `top_covers` / 定理 `top_covers`

English:
theorem top_covers
  given: (S : Sieve X) (f : Y ⟶ X)
  statement: (⊤ : GrothendieckTopology C).Covers S f
  proof: by
  simp [covers_iff]

中文:
定理 top_covers
  条件: (S : 筛 X) (f : Y ⟶ X)
  结论: (⊤ : Grothendieck拓扑 C).Covers S f
  证明: by
  simp [covers_iff]

Depends on / 依赖: covers_iff
-/
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [covers_iff]

/--
lemma `eq_top_iff` / 引理 `eq_top_iff`

English:
lemma eq_top_iff
  given: (J : GrothendieckTopology C)
  statement: J = ⊤ ↔ forall X, ⊥ in J X
  proof: by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  rw [_root_.eq_top_iff]
  intro X S _
  exact J.superset_covering bot_le (h X)

中文:
引理 eq_top_iff
  条件: (J : Grothendieck拓扑 C)
  结论: J = ⊤ ↔ 对任意 X, ⊥ in J X
  证明: by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  rw [_root_.eq_top_iff]
  intro X S _
  exact J.superset_covering bot_le (h X)

Depends on / 依赖: J.superset_covering, _root_, _root_.eq_top_iff, bot_le, eq_top_iff, superset_covering
-/
lemma eq_top_iff (J : GrothendieckTopology C) : J = ⊤ ↔ forall X, ⊥ in J X := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  rw [_root_.eq_top_iff]
  intro X S _
  exact J.superset_covering bot_le (h X)

/--
lemma `eq_top_of_isEmpty` / 引理 `eq_top_of_isEmpty`

English:
lemma eq_top_of_isEmpty
  given: [IsEmpty C] (J : GrothendieckTopology C)
  statement: J = ⊤
  proof: by
  rw [eq_top_iff]
  intro X
  exact IsEmpty.elim ‹IsEmpty C› X

@[simp]

中文:
引理 eq_top_of_isEmpty
  条件: [是空 C] (J : Grothendieck拓扑 C)
  结论: J = ⊤
  证明: by
  rw [eq_top_iff]
  intro X
  exact IsEmpty.elim ‹IsEmpty C› X

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.elim, eq_top_iff
-/
lemma eq_top_of_isEmpty [IsEmpty C] (J : GrothendieckTopology C) : J = ⊤ := by
  rw [eq_top_iff]
  intro X
  exact IsEmpty.elim ‹IsEmpty C› X

@[simp]
/--
lemma `bot_eq_top_iff_isEmpty` / 引理 `bot_eq_top_iff_isEmpty`

English:
lemma bot_eq_top_iff_isEmpty
  statement: (⊥ : GrothendieckTopology C) = ⊤ ↔ IsEmpty C
  proof: by
  refine ⟨fun h => ⟨fun X => ?_⟩, fun h => eq_top_of_isEmpty _⟩
  apply bot_ne_top (α := Sieve X)
  simp only [← GrothendieckTopology.bot_covering, h, top_covering]

@[simp]

中文:
引理 bot_eq_top_iff_isEmpty
  结论: (⊥ : Grothendieck拓扑 C) = ⊤ ↔ 是空 C
  证明: by
  refine ⟨fun h => ⟨fun X => ?_⟩, fun h => eq_top_of_isEmpty _⟩
  apply bot_ne_top (α := Sieve X)
  simp only [← GrothendieckTopology.bot_covering, h, top_covering]

@[simp]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.bot_covering, bot_covering, bot_ne_top, eq_top_of_isEmpty, top_covering
-/
lemma bot_eq_top_iff_isEmpty : (⊥ : GrothendieckTopology C) = ⊤ ↔ IsEmpty C := by
  refine ⟨fun h => ⟨fun X => ?_⟩, fun h => eq_top_of_isEmpty _⟩
  apply bot_ne_top (α := Sieve X)
  simp only [← GrothendieckTopology.bot_covering, h, top_covering]

@[simp]
/--
lemma `bot_lt_top_iff_nonempty` / 引理 `bot_lt_top_iff_nonempty`

English:
lemma bot_lt_top_iff_nonempty
  statement: (⊥ : GrothendieckTopology C) < ⊤ ↔ Nonempty C
  proof: by
  contrapose!
  simp

中文:
引理 bot_lt_top_iff_nonempty
  结论: (⊥ : Grothendieck拓扑 C) < ⊤ ↔ 非空 C
  证明: by
  contrapose!
  simp

Depends on / 依赖: contrapose
-/
lemma bot_lt_top_iff_nonempty : (⊥ : GrothendieckTopology C) < ⊤ ↔ Nonempty C := by
  contrapose!
  simp

/--
Definition of `dense` / `dense` 的定义

English:
definition dense
  signature: : GrothendieckTopology C where
  body: {S | forall {Y : C} (f : Y ⟶ X), exists (Z : _) (g : Z ⟶ Y), S (g ≫ f)}
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩

中文:
定义 dense
  签名: : Grothendieck拓扑 C where
  定义体: {S | forall {Y : C} (f : Y ⟶ X), exists (Z : _) (g : Z ⟶ Y), S (g ≫ f)}
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩
-/
def dense : GrothendieckTopology C where
  sieves X := {S | forall {Y : C} (f : Y ⟶ X), exists (Z : _) (g : Z ⟶ Y), S (g ≫ f)}
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩

/--
theorem `dense_covering` / 定理 `dense_covering`

English:
theorem dense_covering
  statement: S in dense X ↔ forall {Y} (f : Y ⟶ X), exists (Z : _) (g : Z ⟶ Y), S (g ≫ f)
  proof: Iff.rfl

中文:
定理 dense_covering
  结论: S in dense X ↔ 对任意 {Y} (f : Y ⟶ X), 存在 (Z : _) (g : Z ⟶ Y), S (g ≫ f)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem dense_covering : S in dense X ↔ forall {Y} (f : Y ⟶ X), exists (Z : _) (g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl

/--
Definition of `RightOreCondition` / `RightOreCondition` 的定义

English:
definition RightOreCondition
  signature: (C : Type u) [Category.{v} C]
  body: forall {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), exists (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

中文:
定义 RightOreCondition
  签名: (C : 类型u) [范畴.{v} C]
  定义体: forall {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), exists (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx
-/
def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  forall {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), exists (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

/--
theorem `right_ore_of_pullbacks` / 定理 `right_ore_of_pullbacks`

English:
theorem right_ore_of_pullbacks
  given: [Limits.HasPullbacks C]
  statement: RightOreCondition C
  proof: fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩

中文:
定理 right_ore_of_pullbacks
  条件: [Limits.有Pullbacks C]
  结论: RightOreCondition C
  证明: fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩
-/
theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩

/--
Definition of `atomic` / `atomic` 的定义

English:
definition atomic
  signature: (hro : RightOreCondition C)
  body: {S | exists (Y : _) (f : Y ⟶ X), S f}
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩

中文:
定义 atomic
  签名: (hro : RightOreCondition C)
  定义体: {S | exists (Y : _) (f : Y ⟶ X), S f}
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩
-/
def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  sieves X := {S | exists (Y : _) (f : Y ⟶ X), S f}
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩


/--
Definition of `Cover` / `Cover` 的定义

English:
definition Cover
  signature: (X : C)
  body: { S : Sieve X // S in J X }
deriving Preorder

中文:
定义 Cover
  签名: (X : C)
  定义体: { S : Sieve X // S in J X }
deriving Preorder
-/
def Cover (X : C) : Type max u v :=
  { S : Sieve X // S in J X }
deriving Preorder

namespace Cover

variable {J}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (J.Cover X) (Sieve X)
  body: ⟨fun S => S.1⟩

中文:
实例 :
  签名: CoeOut (J.Cover X) (筛 X)
  定义体: ⟨fun S => S.1⟩
-/
instance : CoeOut (J.Cover X) (Sieve X) := ⟨fun S => S.1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (J.Cover X) fun _ => forall ⦃Y⦄ (_ : Y ⟶ X), Prop
  body: ⟨fun S => (S : Sieve X)⟩

中文:
实例 :
  签名: CoeFun (J.Cover X) fun _ => 对任意 ⦃Y⦄ (_ : Y ⟶ X), 命题
  定义体: ⟨fun S => (S : Sieve X)⟩
-/
instance : CoeFun (J.Cover X) fun _ => forall ⦃Y⦄ (_ : Y ⟶ X), Prop := ⟨fun S => (S : Sieve X)⟩

/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (S : J.Cover X)
  statement: (S : Sieve X) in J X
  proof: S.2

@[ext]

中文:
定理 condition
  条件: (S : J.Cover X)
  结论: (S : 筛 X) in J X
  证明: S.2

@[ext]
-/
theorem condition (S : J.Cover X) : (S : Sieve X) in J X := S.2

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (S T : J.Cover X) (h : forall ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f)
  statement: S = T
  proof: Subtype.ext Sieve.ext h

中文:
定理 ext
  条件: (S T : J.Cover X) (h : 对任意 ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f)
  结论: S = T
  证明: Subtype.ext Sieve.ext h

Depends on / 依赖: Sieve.ext, Subtype, Subtype.ext
-/
theorem ext (S T : J.Cover X) (h : forall ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
Subtype.ext Sieve.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (J.Cover X)
  body: { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }

中文:
实例 :
  签名: 有顶序 (J.Cover X)
  定义体: { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }

Depends on / 依赖: J.Cover, J.top_mem, Preorder, le_top, top_mem
-/
instance : OrderTop (J.Cover X) :=
  { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (J.Cover X)
  body: { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }

中文:
实例 :
  签名: SemilatticeInf (J.Cover X)
  定义体: { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }

Depends on / 依赖: J.intersection_covering, Preorder, S.condition, T.condition, condition, inf_le_left, inf_le_right, intersection_covering, le_antisymm, le_inf
-/
instance : SemilatticeInf (J.Cover X) :=
  { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (J.Cover X)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (J.Cover X)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (J.Cover X) :=
  ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
/--
Definition of `Arrow` / `Arrow` 的定义

English:
structure Arrow
  parameters: (S : J.Cover X)
  axioms and operations (3):
    - Y : C
    - f : Y ⟶ X
    - hf : S f

中文:
结构 箭头
  参数: (S : J.Cover X)
  公理与运算 (3 个):
    - Y : C
    - f : Y ⟶ X
    - hf : S f
-/
structure Arrow (S : J.Cover X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f

/-- Relation between two elements in `S.arrow`, the data of which
involves a commutative square. -/
@[ext]
/--
Definition of `Arrow.Relation` / `Arrow.Relation` 的定义

English:
structure Arrow.Relation
  parameters: {S : J.Cover X} (I₁ I₂ : S.Arrow)
  axioms and operations (4):
    - Z : C
    - g₁ : Z ⟶ I₁.Y
    - g₂ : Z ⟶ I₂.Y
    - w : g₁ ≫ I₁.f = g₂ ≫ I₂.f  [default: by cat_disch]

中文:
结构 箭头.关系
  参数: {S : J.Cover X} (I₁ I₂ : S.箭头)
  公理与运算 (4 个):
    - Z : C
    - g₁ : Z ⟶ I₁.Y
    - g₂ : Z ⟶ I₂.Y
    - w : g₁ ≫ I₁.f = g₂ ≫ I₂.f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Arrow.Relation {S : J.Cover X} (I₁ I₂ : S.Arrow) where
  /-- The source of the arrows defining the relation. -/
  Z : C
  /-- The first arrow defining the relation. -/
  g₁ : Z ⟶ I₁.Y
  /-- The second arrow defining the relation. -/
  g₂ : Z ⟶ I₂.Y
  /-- The relation itself. -/
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by cat_disch

attribute [reassoc] Arrow.Relation.w

/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the arrow in `S.Arrow`
corresponding to `g ≫ I.f`. -/
@[simps]
/--
Definition of `Arrow.precomp` / `Arrow.precomp` 的定义

English:
definition Arrow.precomp
  signature: {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y)
  body: ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

中文:
定义 箭头.precomp
  签名: {S : J.Cover X} (I : S.箭头) {Z : C} (g : Z ⟶ I.Y)
  定义体: ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

Depends on / 依赖: I.hf, downward_closed
-/
def Arrow.precomp {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) : S.Arrow :=
  ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the obvious relation
from `I.precomp g` to `I`. -/
@[simps]
/--
Definition of `Arrow.precompRelation` / `Arrow.precompRelation` 的定义

English:
definition Arrow.precompRelation
  signature: {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y)
  body: (I.precomp g).Y
  g₁ := 𝟙 _
  g₂ := g

中文:
定义 箭头.precompRelation
  签名: {S : J.Cover X} (I : S.箭头) {Z : C} (g : Z ⟶ I.Y)
  定义体: (I.precomp g).Y
  g₁ := 𝟙 _
  g₂ := g

Depends on / 依赖: I.precomp, precomp
-/
def Arrow.precompRelation {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) :
    (I.precomp g).Relation I where
  Z := (I.precomp g).Y
  g₁ := 𝟙 _
  g₂ := g

/-- Map an `Arrow` along a refinement `S ⟶ T`. -/
@[simps]
/--
Definition of `Arrow.map` / `Arrow.map` 的定义

English:
definition Arrow.map
  signature: {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T)
  body: ⟨I.Y, I.f, f.le _ I.hf⟩

中文:
定义 箭头.map
  签名: {S T : J.Cover X} (I : S.箭头) (f : S ⟶ T)
  定义体: ⟨I.Y, I.f, f.le _ I.hf⟩

Depends on / 依赖: I.hf, f.le
-/
def Arrow.map {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T) : T.Arrow :=
  ⟨I.Y, I.f, f.le _ I.hf⟩

/-- Map an `Arrow.Relation` along a refinement `S ⟶ T`. -/
@[simps]
/--
Definition of `Arrow.Relation.map` / `Arrow.Relation.map` 的定义

English:
definition Arrow.Relation.map
  signature: {S T : J.Cover X} {I₁ I₂ : S.Arrow}
  body: { r with }

中文:
定义 箭头.关系.map
  签名: {S T : J.Cover X} {I₁ I₂ : S.箭头}
  定义体: { r with }
-/
def Arrow.Relation.map {S T : J.Cover X} {I₁ I₂ : S.Arrow}
    (r : I₁.Relation I₂) (f : S ⟶ T) : (I₁.map f).Relation (I₂.map f) :=
  { r with }

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (S : J.Cover X) (f : Y ⟶ X)
  body: ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

中文:
定义 pullback
  签名: (S : J.Cover X) (f : Y ⟶ X)
  定义体: ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

Depends on / 依赖: J.pullback_stable, S.condition, Sieve.pullback, condition, pullback, pullback_stable
-/
def pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y :=
  ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
/--
Definition of `Arrow.base` / `Arrow.base` 的定义

English:
definition Arrow.base
  signature: {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow)
  body: ⟨I.Y, I.f ≫ f, I.hf⟩

中文:
定义 箭头.base
  签名: {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).箭头)
  定义体: ⟨I.Y, I.f ≫ f, I.hf⟩

Depends on / 依赖: I.hf
-/
def Arrow.base {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow) : S.Arrow :=
  ⟨I.Y, I.f ≫ f, I.hf⟩

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Arrow.Relation.base` / `Arrow.Relation.base` 的定义

English:
definition Arrow.Relation.base
  body: { r with w := by simp [r.w_assoc] }

@[simp]

中文:
定义 箭头.关系.base
  定义体: { r with w := by simp [r.w_assoc] }

@[simp]

Depends on / 依赖: r.w_assoc, w_assoc
-/
def Arrow.Relation.base
    {f : Y ⟶ X} {S : J.Cover X} {I₁ I₂ : (S.pullback f).Arrow}
    (r : I₁.Relation I₂) : I₁.base.Relation I₂.base :=
  { r with w := by simp [r.w_assoc] }

@[simp]
/--
theorem `coe_pullback` / 定理 `coe_pullback`

English:
theorem coe_pullback
  given: {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X)
  proof: Iff.rfl

中文:
定理 coe_pullback
  条件: {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) :
    (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl

/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: (S : J.Cover X)
  body: eqToIso Cover.ext _ _ fun Y f => by simp

中文:
定义 pullbackId
  签名: (S : J.Cover X)
  定义体: eqToIso Cover.ext _ _ fun Y f => by simp

Depends on / 依赖: Cover.ext, eqToIso
-/
def pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S :=
eqToIso Cover.ext _ _ fun Y f => by simp

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X)
  body: eqToIso Cover.ext _ _ fun Y f => by simp

中文:
定义 pullbackComp
  签名: {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X)
  定义体: eqToIso Cover.ext _ _ fun Y f => by simp

Depends on / 依赖: Cover.ext, eqToIso
-/
def pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
eqToIso Cover.ext _ _ fun Y f => by simp

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y)
  body: ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

中文:
定义 bind
  签名: {X : C} (S : J.Cover X) (T : 对任意 I : S.箭头, J.Cover I.Y)
  定义体: ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

Depends on / 依赖: J.bind_covering, S.condition, Sieve.bind, bind_covering, condition
-/
def bind {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y) : J.Cover X :=
  ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

/--
Definition of `bindToBase` / `bindToBase` 的定义

English:
definition bindToBase
  signature: {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y)
  body: homOfLE by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

中文:
定义 bindToBase
  签名: {X : C} (S : J.Cover X) (T : 对任意 I : S.箭头, J.Cover I.Y)
  定义体: homOfLE by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

Depends on / 依赖: Sieve.downward_closed, downward_closed, homOfLE
-/
def bindToBase {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y) : S.bind T ⟶ S :=
homOfLE by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

/--
Definition of `Arrow.middle` / `Arrow.middle` 的定义

English:
definition Arrow.middle
  signature: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  body: I.hf.choose

中文:
定义 箭头.middle
  签名: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  定义体: I.hf.choose

Depends on / 依赖: I.hf.choose
-/
noncomputable def Arrow.middle {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : C :=
  I.hf.choose

/--
Definition of `Arrow.toMiddleHom` / `Arrow.toMiddleHom` 的定义

English:
definition Arrow.toMiddleHom
  signature: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  body: I.hf.choose_spec.choose

中文:
定义 箭头.toMiddleHom
  签名: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  定义体: I.hf.choose_spec.choose

Depends on / 依赖: I.hf.choose_spec.choose, choose_spec
-/
noncomputable def Arrow.toMiddleHom {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.Y ⟶ I.middle :=
  I.hf.choose_spec.choose

/--
Definition of `Arrow.fromMiddleHom` / `Arrow.fromMiddleHom` 的定义

English:
definition Arrow.fromMiddleHom
  signature: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  body: I.hf.choose_spec.choose_spec.choose

中文:
定义 箭头.fromMiddleHom
  签名: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  定义体: I.hf.choose_spec.choose_spec.choose

Depends on / 依赖: I.hf.choose_spec.choose_spec.choose, choose_spec
-/
noncomputable def Arrow.fromMiddleHom {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.middle ⟶ X :=
  I.hf.choose_spec.choose_spec.choose

/--
theorem `Arrow.from_middle_condition` / 定理 `Arrow.from_middle_condition`

English:
theorem Arrow.from_middle_condition
  statement: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  proof: I.hf.choose_spec.choose_spec.choose_spec.choose

中文:
定理 箭头.from_middle_condition
  结论: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  证明: I.hf.choose_spec.choose_spec.choose_spec.choose

Depends on / 依赖: I.hf.choose_spec.choose_spec.choose_spec.choose, choose_spec
-/
theorem Arrow.from_middle_condition {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S I.fromMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose

/--
Definition of `Arrow.fromMiddle` / `Arrow.fromMiddle` 的定义

English:
definition Arrow.fromMiddle
  signature: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  body: ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

中文:
定义 箭头.fromMiddle
  签名: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  定义体: ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

Depends on / 依赖: I.fromMiddleHom, I.from_middle_condition, fromMiddleHom, from_middle_condition
-/
noncomputable def Arrow.fromMiddle {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S.Arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

/--
theorem `Arrow.to_middle_condition` / 定理 `Arrow.to_middle_condition`

English:
theorem Arrow.to_middle_condition
  statement: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  proof: I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

中文:
定理 箭头.to_middle_condition
  结论: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  证明: I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

Depends on / 依赖: I.hf.choose_spec.choose_spec.choose_spec.choose_spec, choose_spec
-/
theorem Arrow.to_middle_condition {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle) I.toMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

/--
Definition of `Arrow.toMiddle` / `Arrow.toMiddle` 的定义

English:
definition Arrow.toMiddle
  signature: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  body: ⟨_, I.toMiddleHom, I.to_middle_condition⟩

中文:
定义 箭头.toMiddle
  签名: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  定义体: ⟨_, I.toMiddleHom, I.to_middle_condition⟩

Depends on / 依赖: I.toMiddleHom, I.to_middle_condition, toMiddleHom, to_middle_condition
-/
noncomputable def Arrow.toMiddle {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle).Arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩

/--
theorem `Arrow.middle_spec` / 定理 `Arrow.middle_spec`

English:
theorem Arrow.middle_spec
  statement: {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
  proof: I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

中文:
定理 箭头.middle_spec
  结论: {X : C} {S : J.Cover X} {T : 对任意 I : S.箭头, J.Cover I.Y}
  证明: I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

Depends on / 依赖: I.hf.choose_spec.choose_spec.choose_spec.choose_spec, choose_spec
-/
theorem Arrow.middle_spec {X : C} {S : J.Cover X} {T : forall I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
/--
Definition of `Relation` / `Relation` 的定义

English:
structure Relation
  parameters: (S : J.Cover X)
  axioms and operations (3):
    - {fst : S.Arrow}
    - {snd : S.Arrow}
    - r : fst.Relation snd

中文:
结构 关系
  参数: (S : J.Cover X)
  公理与运算 (3 个):
    - {fst : S.箭头}
    - {snd : S.箭头}
    - r : fst.关系 snd
-/
structure Relation (S : J.Cover X) where
  /-- The first arrow. -/
  {fst : S.Arrow}
  /-- The second arrow. -/
  {snd : S.Arrow}
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

/-- Constructor for `Cover.Relation` which takes as an input
`r : I₁.Relation I₂` with `I₁ I₂ : S.Arrow`. -/
@[simps]
/--
Definition of `Relation.mk'` / `Relation.mk'` 的定义

English:
definition Relation.mk'
  signature: {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd)
  body: fst
  snd := snd
  r := r

中文:
定义 关系.mk'
  签名: {S : J.Cover X} {fst snd : S.箭头} (r : fst.关系 snd)
  定义体: fst
  snd := snd
  r := r
-/
def Relation.mk' {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd) :
    S.Relation where
  fst := fst
  snd := snd
  r := r


/-- The shape of the multiequalizer diagrams associated to `S : J.Cover X`. -/
@[simps]
/--
Definition of `shape` / `shape` 的定义

English:
definition shape
  signature: (S : J.Cover X)
  body: S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

中文:
定义 shape
  签名: (S : J.Cover X)
  定义体: S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

Depends on / 依赖: S.Arrow
-/
def shape (S : J.Cover X) : Limits.MulticospanShape where
  L := S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

-- This is used extensively in `Plus.lean`, etc.
-- We place this definition here as it will be used in `Sheaf.lean` as well.
/-- To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`. -/
@[simps]
/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D)
  body: P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

中文:
定义 index
  签名: {D : 类型u₁} [范畴.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D)
  定义体: P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

Depends on / 依赖: Opposite, Opposite.op, P.obj
-/
def index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex S.shape D where
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `multifork` / `multifork` 的定义

English:
abbreviation multifork
  signature: {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D)
  body: Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])

中文:
缩写 multifork
  签名: {D : 类型u₁} [范畴.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D)
  定义体: Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])

Depends on / 依赖: I.f.op, I.r.w, Limits, Limits.Multifork.of, Multifork, Opposite, Opposite.op, P.map, P.map_comp, P.obj, map_comp, op_comp
-/
abbrev multifork {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])

/--
Definition of `toMultiequalizer` / `toMultiequalizer` 的定义

English:
abbreviation toMultiequalizer
  signature: {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
  body: Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [shape, index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

中文:
缩写 toMultiequalizer
  签名: {D : 类型u₁} [范畴.{v₁} D] (S : J.Cover X)
  定义体: Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [shape, index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

Depends on / 依赖: I.f.op, I.r.w, Limits, Limits.Multiequalizer.lift, Multiequalizer, P.map, P.map_comp, Relation, Relation.fst, Relation.snd, map_comp, op_comp
-/
noncomputable abbrev toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
    (P : Cᵒᵖ ⥤ D) [Limits.HasMultiequalizer (S.index P)] :
    P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [shape, index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

end Cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : Y ⟶ X)
  body: S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

中文:
定义 pullback
  签名: (f : Y ⟶ X)
  定义体: S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

Depends on / 依赖: S.pullback, pullback
-/
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: (X : C)
  body: NatIso.ofComponents fun S => S.pullbackId

中文:
定义 pullbackId
  签名: (X : C)
  定义体: NatIso.ofComponents fun S => S.pullbackId

Depends on / 依赖: NatIso, NatIso.ofComponents, S.pullbackId, ofComponents, pullbackId
-/
def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents fun S => S.pullbackId

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: NatIso.ofComponents fun S => S.pullbackComp f g

中文:
定义 pullbackComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: NatIso.ofComponents fun S => S.pullbackComp f g

Depends on / 依赖: NatIso, NatIso.ofComponents, S.pullbackComp, ofComponents, pullbackComp
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  NatIso.ofComponents fun S => S.pullbackComp f g

end GrothendieckTopology

end CategoryTheory
