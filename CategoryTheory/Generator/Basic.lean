/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `P : ObjectProperty C` is a separating set if the functors `C(G, -)`
    for `G` such that `P G` are collectively faithful, i.e., if
    `h ≫ f = h ≫ g` for all `h` with domain satisfying `P` implies `f = g`.
* We say that `P : ObjectProperty C` is a detecting set if the functors `C(G, -)`
    collectively reflect isomorphisms, i.e., if any `h` with domain satisfying `P`
    uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `IsSeparating`, `IsCoseparating`, `IsDetecting` and `IsCodetecting` on
  `ObjectProperty C`;
* show that equivalences of categories preserve these notions;
* show that separating and coseparating are dual notions;
* show that detecting and codetecting are dual notions;
* show that if `C` has equalizers, then detecting implies separating;
* show that if `C` has coequalizers, then codetecting implies coseparating;
* show that if `C` is balanced, then separating implies detecting and coseparating implies
  codetecting;
* show that `∅` is separating if and only if `∅` is coseparating if and only if `C` is thin;
* show that `∅` is detecting if and only if `∅` is codetecting if and only if `C` is a groupoid;
* define predicates `IsSeparator`, `IsCoseparator`, `IsDetector` and `IsCodetector` as the
  singleton counterparts to the definitions for sets above and restate the above results in this
  situation;
* show that `G` is a separator if and only if `coyoneda.obj (op G)` is faithful (and the dual);
* show that `G` is a detector if and only if `coyoneda.obj (op G)` reflects isomorphisms (and the
  dual);
* show that `C` is `WellPowered` if it admits small pullbacks and a detector;
* define corresponding typeclasses `HasSeparator`, `HasCoseparator`, `HasDetector`
  and `HasCodetector` on categories and prove analogous results for these.

## Examples

See the files `CategoryTheory.Generator.Presheaf` and `CategoryTheory.Generator.Sheaf`.

-/

@[expose] public section


universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/--
Definition of `IsSeparating` / `IsSeparating` 的定义

English:
definition IsSeparating
  signature: : Prop
  body: forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) -> f = g

中文:
定义 IsSeparating
  签名: : 命题
  定义体: forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) -> f = g
-/
def IsSeparating : Prop :=
  forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) -> f = g

/--
Definition of `IsCoseparating` / `IsCoseparating` 的定义

English:
definition IsCoseparating
  signature: : Prop
  body: forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : Y ⟶ G), f ≫ h = g ≫ h) -> f = g

中文:
定义 IsCoseparating
  签名: : 命题
  定义体: forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : Y ⟶ G), f ≫ h = g ≫ h) -> f = g
-/
def IsCoseparating : Prop :=
  forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall (G : C) (_ : P G) (h : Y ⟶ G), f ≫ h = g ≫ h) -> f = g

/--
Definition of `IsDetecting` / `IsDetecting` 的定义

English:
definition IsDetecting
  signature: : Prop
  body: forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : G ⟶ Y), exists! h' : G ⟶ X, h' ≫ f = h) -> IsIso f

中文:
定义 IsDetecting
  签名: : 命题
  定义体: forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : G ⟶ Y), exists! h' : G ⟶ X, h' ≫ f = h) -> IsIso f
-/
def IsDetecting : Prop :=
  forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : G ⟶ Y), exists! h' : G ⟶ X, h' ≫ f = h) -> IsIso f

/--
Definition of `IsCodetecting` / `IsCodetecting` 的定义

English:
definition IsCodetecting
  signature: : Prop
  body: forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : X ⟶ G), exists! h' : Y ⟶ G, f ≫ h' = h) -> IsIso f

中文:
定义 IsCodetecting
  签名: : 命题
  定义体: forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : X ⟶ G), exists! h' : Y ⟶ G, f ≫ h' = h) -> IsIso f
-/
def IsCodetecting : Prop :=
  forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G),
    forall (h : X ⟶ G), exists! h' : Y ⟶ G, f ≫ h' = h) -> IsIso f

section Equivalence

variable {P}

/--
lemma `IsSeparating.of_equivalence` / 引理 `IsSeparating.of_equivalence`

English:
lemma IsSeparating.of_equivalence
  proof: fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H _ (P.strictMap_obj _ hZ) h']))

中文:
引理 IsSeparating.of_equivalence
  证明: fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H _ (P.strictMap_obj _ hZ) h']))
-/
lemma IsSeparating.of_equivalence
    (h : IsSeparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsSeparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H _ (P.strictMap_obj _ hZ) h']))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsCoseparating.of_equivalence` / 引理 `IsCoseparating.of_equivalence`

English:
lemma IsCoseparating.of_equivalence
  proof: fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
      H _ (P.strictMap_obj _ hZ) h']))

中文:
引理 IsCoseparating.of_equivalence
  证明: fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
      H _ (P.strictMap_obj _ hZ) h']))
-/
lemma IsCoseparating.of_equivalence
    (h : IsCoseparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsCoseparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h => by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
      H _ (P.strictMap_obj _ hZ) h']))

end Equivalence

section Dual

/--
theorem `isSeparating_op_iff` / 定理 `isSeparating_op_iff`

English:
theorem isSeparating_op_iff
  statement: IsSeparating P.op ↔ IsCoseparating P
  proof: by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

中文:
定理 isSeparating_op_iff
  结论: IsSeparating P.op ↔ IsCoseparating P
  证明: by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, op_comp, op_inj, op_unop, unop_comp, unop_inj, unop_op
-/
theorem isSeparating_op_iff : IsSeparating P.op ↔ IsCoseparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

/--
theorem `isCoseparating_op_iff` / 定理 `isCoseparating_op_iff`

English:
theorem isCoseparating_op_iff
  statement: IsCoseparating P.op ↔ IsSeparating P
  proof: by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

中文:
定理 isCoseparating_op_iff
  结论: IsCoseparating P.op ↔ IsSeparating P
  证明: by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, op_comp, op_inj, op_unop, unop_comp, unop_inj, unop_op
-/
theorem isCoseparating_op_iff : IsCoseparating P.op ↔ IsSeparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _

/--
theorem `isCoseparating_unop_iff` / 定理 `isCoseparating_unop_iff`

English:
theorem isCoseparating_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  proof: P.unop.isSeparating_op_iff.symm

中文:
定理 isCoseparating_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  证明: P.unop.isSeparating_op_iff.symm

Depends on / 依赖: P.unop.isSeparating_op_iff.symm, isSeparating_op_iff
-/
theorem isCoseparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsCoseparating P.unop ↔ IsSeparating P :=
  P.unop.isSeparating_op_iff.symm

/--
theorem `isSeparating_unop_iff` / 定理 `isSeparating_unop_iff`

English:
theorem isSeparating_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  proof: P.unop.isCoseparating_op_iff.symm

中文:
定理 isSeparating_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  证明: P.unop.isCoseparating_op_iff.symm

Depends on / 依赖: P.unop.isCoseparating_op_iff.symm, isCoseparating_op_iff
-/
theorem isSeparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsSeparating P.unop ↔ IsCoseparating P :=
  P.unop.isCoseparating_op_iff.symm

/--
theorem `isDetecting_op_iff` / 定理 `isDetecting_op_iff`

English:
theorem isDetecting_op_iff
  statement: IsDetecting P.op ↔ IsCodetecting P
  proof: by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

中文:
定理 isDetecting_op_iff
  结论: IsDetecting P.op ↔ IsCodetecting P
  证明: by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, h.op, h.unop, isIso_op_iff, isIso_unop_iff, op_inj, t.op, t.unop, unop_inj
-/
theorem isDetecting_op_iff : IsDetecting P.op ↔ IsCodetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

/--
theorem `isCodetecting_op_iff` / 定理 `isCodetecting_op_iff`

English:
theorem isCodetecting_op_iff
  statement: IsCodetecting P.op ↔ IsDetecting P
  proof: by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

中文:
定理 isCodetecting_op_iff
  结论: IsCodetecting P.op ↔ IsDetecting P
  证明: by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, h.op, h.unop, isIso_op_iff, isIso_unop_iff, op_inj, t.op, t.unop, unop_inj
-/
theorem isCodetecting_op_iff : IsCodetecting P.op ↔ IsDetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)

/--
theorem `isDetecting_unop_iff` / 定理 `isDetecting_unop_iff`

English:
theorem isDetecting_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  statement: IsDetecting P.unop ↔ IsCodetecting P
  proof: P.unop.isCodetecting_op_iff.symm

中文:
定理 isDetecting_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  结论: IsDetecting P.unop ↔ IsCodetecting P
  证明: P.unop.isCodetecting_op_iff.symm

Depends on / 依赖: P.unop.isCodetecting_op_iff.symm, isCodetecting_op_iff
-/
theorem isDetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsDetecting P.unop ↔ IsCodetecting P :=
  P.unop.isCodetecting_op_iff.symm

/--
theorem `isCodetecting_unop_iff` / 定理 `isCodetecting_unop_iff`

English:
theorem isCodetecting_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  statement: IsCodetecting P.unop ↔ IsDetecting P
  proof: P.unop.isDetecting_op_iff.symm

中文:
定理 isCodetecting_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  结论: IsCodetecting P.unop ↔ IsDetecting P
  证明: P.unop.isDetecting_op_iff.symm

Depends on / 依赖: P.unop.isDetecting_op_iff.symm, isDetecting_op_iff
-/
theorem isCodetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsCodetecting P.unop ↔ IsDetecting P :=
  P.unop.isDetecting_op_iff.symm

end Dual

variable {P}

/--
theorem `IsDetecting.isSeparating` / 定理 `IsDetecting.isSeparating`

English:
theorem IsDetecting.isSeparating
  given: [HasEqualizers C] (hP : IsDetecting P)
  proof: fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := hP _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer

中文:
定理 IsDetecting.isSeparating
  条件: [HasEqualizers C] (hP : IsDetecting P)
  证明: fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := hP _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer
-/
theorem IsDetecting.isSeparating [HasEqualizers C] (hP : IsDetecting P) :
    IsSeparating P := fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := hP _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer

/--
theorem `IsCodetecting.isCoseparating` / 定理 `IsCodetecting.isCoseparating`

English:
theorem IsCodetecting.isCoseparating
  given: [HasCoequalizers C]
  proof: by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating

中文:
定理 IsCodetecting.isCoseparating
  条件: [HasCoequalizers C]
  证明: by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating

Depends on / 依赖: IsDetecting, IsDetecting.isSeparating, isDetecting_op_iff, isSeparating, isSeparating_op_iff
-/
theorem IsCodetecting.isCoseparating [HasCoequalizers C] :
    IsCodetecting P -> IsCoseparating P := by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating

/--
lemma `IsSeparating.mono_iff` / 引理 `IsSeparating.mono_iff`

English:
lemma IsSeparating.mono_iff
  given: (hP : IsSeparating P) {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun _ _ _ _ _ h => by simpa [cancel_mono] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [h]))⟩⟩

中文:
引理 IsSeparating.mono_iff
  条件: (hP : IsSeparating P) {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun _ _ _ _ _ h => by simpa [cancel_mono] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [h]))⟩⟩

Depends on / 依赖: cancel_mono
-/
lemma IsSeparating.mono_iff (hP : IsSeparating P) {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ forall (G : C) (_ : P G), forall (g₁ g₂ : G ⟶ X), g₁ ≫ f = g₂ ≫ f -> g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h => by simpa [cancel_mono] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [h]))⟩⟩

/--
lemma `IsCoseparating.epi_iff` / 引理 `IsCoseparating.epi_iff`

English:
lemma IsCoseparating.epi_iff
  given: (hP : IsCoseparating P) {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun _ _ _ _ _ h => by simpa [cancel_epi] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [reassoc_of% h]))⟩⟩

中文:
引理 IsCoseparating.epi_iff
  条件: (hP : IsCoseparating P) {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun _ _ _ _ _ h => by simpa [cancel_epi] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [reassoc_of% h]))⟩⟩

Depends on / 依赖: cancel_epi, reassoc_of
-/
lemma IsCoseparating.epi_iff (hP : IsCoseparating P) {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ forall (G : C) (_ : P G), forall (g₁ g₂ : Y ⟶ G), f ≫ g₁ = f ≫ g₂ -> g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h => by simpa [cancel_epi] using h,
    fun hf => ⟨fun g₁ g₂ h => hP _ _ (fun G hG h' => hf _ hG _ _ (by simp [reassoc_of% h]))⟩⟩

/--
theorem `IsSeparating.isDetecting` / 定理 `IsSeparating.isDetecting`

English:
theorem IsSeparating.isDetecting
  given: [Balanced C] (hP : IsSeparating P)
  proof: by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => hP _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _)]; rw [ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine hP _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc]; rw [hgh]; rw [Category.assoc]

中文:
定理 IsSeparating.isDetecting
  条件: [Balanced C] (hP : IsSeparating P)
  证明: by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => hP _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _)]; rw [ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine hP _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc]; rw [hgh]; rw [Category.assoc]

Depends on / 依赖: Category, Category.assoc, hgh.symm, isIso_iff_mono_and_epi
-/
theorem IsSeparating.isDetecting [Balanced C] (hP : IsSeparating P) :
    IsDetecting P := by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => hP _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _)]; rw [ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine hP _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc]; rw [hgh]; rw [Category.assoc]

/--
lemma `IsDetecting.isIso_iff_of_mono` / 引理 `IsDetecting.isIso_iff_of_mono`

English:
lemma IsDetecting.isIso_iff_of_mono
  statement: (hP : IsDetecting P)
  proof: by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f]; rw [h₁]; rw [h₂]

中文:
引理 IsDetecting.isIso_iff_of_mono
  结论: (hP : IsDetecting P)
  证明: by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f]; rw [h₁]; rw [h₂]

Depends on / 依赖: cancel_mono, existsUnique_of_exists_of_unique, isIso_iff_yoneda_map_bijective
-/
lemma IsDetecting.isIso_iff_of_mono (hP : IsDetecting P)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ forall (G : C) (_ : P G), Function.Surjective ((coyoneda.obj (op G)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f]; rw [h₁]; rw [h₂]

/--
lemma `IsCodetecting.isIso_iff_of_epi` / 引理 `IsCodetecting.isIso_iff_of_epi`

English:
lemma IsCodetecting.isIso_iff_of_epi
  statement: (hP : IsCodetecting P)
  proof: by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f]; rw [h₁]; rw [h₂]

中文:
引理 IsCodetecting.isIso_iff_of_epi
  结论: (hP : IsCodetecting P)
  证明: by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f]; rw [h₁]; rw [h₂]

Depends on / 依赖: cancel_epi, existsUnique_of_exists_of_unique, isIso_iff_coyoneda_map_bijective
-/
lemma IsCodetecting.isIso_iff_of_epi (hP : IsCodetecting P)
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsIso f ↔ forall (G : C) (_ : P G), Function.Surjective ((yoneda.obj G).map f.op) := by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g => existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f]; rw [h₁]; rw [h₂]

section

attribute [local instance] balanced_opposite

/--
theorem `IsCoseparating.isCodetecting` / 定理 `IsCoseparating.isCodetecting`

English:
theorem IsCoseparating.isCodetecting
  given: [Balanced C]
  proof: by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

中文:
定理 IsCoseparating.isCodetecting
  条件: [Balanced C]
  证明: by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

Depends on / 依赖: IsSeparating, IsSeparating.isDetecting, isDetecting, isDetecting_op_iff, isSeparating_op_iff
-/
theorem IsCoseparating.isCodetecting [Balanced C] :
    IsCoseparating P -> IsCodetecting P := by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

end

/--
theorem `isDetecting_iff_isSeparating` / 定理 `isDetecting_iff_isSeparating`

English:
theorem isDetecting_iff_isSeparating
  given: [HasEqualizers C] [Balanced C]
  proof: ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩

中文:
定理 isDetecting_iff_isSeparating
  条件: [HasEqualizers C] [Balanced C]
  证明: ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩

Depends on / 依赖: IsDetecting, IsDetecting.isSeparating, IsSeparating, IsSeparating.isDetecting, isDetecting, isSeparating
-/
theorem isDetecting_iff_isSeparating [HasEqualizers C] [Balanced C] :
    IsDetecting P ↔ IsSeparating P :=
  ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩

/--
theorem `isCodetecting_iff_isCoseparating` / 定理 `isCodetecting_iff_isCoseparating`

English:
theorem isCodetecting_iff_isCoseparating
  given: [HasCoequalizers C] [Balanced C]
  proof: ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

中文:
定理 isCodetecting_iff_isCoseparating
  条件: [HasCoequalizers C] [Balanced C]
  证明: ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

Depends on / 依赖: IsCodetecting, IsCodetecting.isCoseparating, IsCoseparating, IsCoseparating.isCodetecting, isCodetecting, isCoseparating
-/
theorem isCodetecting_iff_isCoseparating [HasCoequalizers C] [Balanced C] :
    IsCodetecting P ↔ IsCoseparating P :=
  ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

section Mono

/--
theorem `IsSeparating.of_le` / 定理 `IsSeparating.of_le`

English:
theorem IsSeparating.of_le
  given: (hP : IsSeparating P) {Q : ObjectProperty C} (h : P <= Q)
  proof: fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

中文:
定理 IsSeparating.of_le
  条件: (hP : IsSeparating P) {Q : ObjectProperty C} (h : P <= Q)
  证明: fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _
-/
theorem IsSeparating.of_le (hP : IsSeparating P) {Q : ObjectProperty C} (h : P <= Q) :
    IsSeparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

/--
theorem `IsCoseparating.of_le` / 定理 `IsCoseparating.of_le`

English:
theorem IsCoseparating.of_le
  given: (hP : IsCoseparating P) {Q : ObjectProperty C} (h : P <= Q)
  proof: fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

中文:
定理 IsCoseparating.of_le
  条件: (hP : IsCoseparating P) {Q : ObjectProperty C} (h : P <= Q)
  证明: fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _
-/
theorem IsCoseparating.of_le (hP : IsCoseparating P) {Q : ObjectProperty C} (h : P <= Q) :
    IsCoseparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _

/--
theorem `IsDetecting.of_le` / 定理 `IsDetecting.of_le`

English:
theorem IsDetecting.of_le
  given: (hP : IsDetecting P) {Q : ObjectProperty C} (h : P <= Q)
  proof: fun _ _ _ hf => hP _ fun _ hG _ => hf _ (h _ hG) _

中文:
定理 IsDetecting.of_le
  条件: (hP : IsDetecting P) {Q : ObjectProperty C} (h : P <= Q)
  证明: fun _ _ _ hf => hP _ fun _ hG _ => hf _ (h _ hG) _
-/
theorem IsDetecting.of_le (hP : IsDetecting P) {Q : ObjectProperty C} (h : P <= Q) :
    IsDetecting Q := fun _ _ _ hf => hP _ fun _ hG _ => hf _ (h _ hG) _

/--
theorem `IsCodetecting.of_le` / 定理 `IsCodetecting.of_le`

English:
theorem IsCodetecting.of_le
  given: (h𝒢 : IsCodetecting P) {Q : ObjectProperty C} (h : P <= Q)
  proof: fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h _ hG) _

中文:
定理 IsCodetecting.of_le
  条件: (h𝒢 : IsCodetecting P) {Q : ObjectProperty C} (h : P <= Q)
  证明: fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h _ hG) _
-/
theorem IsCodetecting.of_le (h𝒢 : IsCodetecting P) {Q : ObjectProperty C} (h : P <= Q) :
    IsCodetecting Q := fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h _ hG) _

end Mono

section Empty

/--
lemma `isThin_of_isSeparating_bot` / 引理 `isThin_of_isSeparating_bot`

English:
lemma isThin_of_isSeparating_bot
  given: (h : IsSeparating (⊥ : ObjectProperty C))
  proof: fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩

中文:
引理 isThin_of_isSeparating_bot
  条件: (h : IsSeparating (⊥ : ObjectProperty C))
  证明: fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩
-/
lemma isThin_of_isSeparating_bot (h : IsSeparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩

/--
lemma `isSeparating_bot_of_isThin` / 引理 `isSeparating_bot_of_isThin`

English:
lemma isSeparating_bot_of_isThin
  given: [Quiver.IsThin C]
  statement: IsSeparating (⊥ : ObjectProperty C)
  proof: fun _ _ _ _ _ => Subsingleton.elim _ _

中文:
引理 isSeparating_bot_of_isThin
  条件: [箭图.IsThin C]
  结论: IsSeparating (⊥ : ObjectProperty C)
  证明: fun _ _ _ _ _ => Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma isSeparating_bot_of_isThin [Quiver.IsThin C] : IsSeparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

/--
lemma `isThin_of_isCoseparating_bot` / 引理 `isThin_of_isCoseparating_bot`

English:
lemma isThin_of_isCoseparating_bot
  given: (h : IsCoseparating (⊥ : ObjectProperty C))
  proof: fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩

中文:
引理 isThin_of_isCoseparating_bot
  条件: (h : IsCoseparating (⊥ : ObjectProperty C))
  证明: fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩
-/
lemma isThin_of_isCoseparating_bot (h : IsCoseparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ => ⟨fun _ _ => h _ _ (by simp)⟩

/--
lemma `isCoseparating_bot_of_isThin` / 引理 `isCoseparating_bot_of_isThin`

English:
lemma isCoseparating_bot_of_isThin
  given: [Quiver.IsThin C]
  statement: IsCoseparating (⊥ : ObjectProperty C)
  proof: fun _ _ _ _ _ => Subsingleton.elim _ _

中文:
引理 isCoseparating_bot_of_isThin
  条件: [箭图.IsThin C]
  结论: IsCoseparating (⊥ : ObjectProperty C)
  证明: fun _ _ _ _ _ => Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma isCoseparating_bot_of_isThin [Quiver.IsThin C] : IsCoseparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

/--
lemma `isGroupoid_of_isDetecting_bot` / 引理 `isGroupoid_of_isDetecting_bot`

English:
lemma isGroupoid_of_isDetecting_bot
  given: (h : IsDetecting (⊥ : ObjectProperty C))
  proof: h _ (by simp)

中文:
引理 isGroupoid_of_isDetecting_bot
  条件: (h : IsDetecting (⊥ : ObjectProperty C))
  证明: h _ (by simp)
-/
lemma isGroupoid_of_isDetecting_bot (h : IsDetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)

/--
lemma `isDetecting_bot_of_isGroupoid` / 引理 `isDetecting_bot_of_isGroupoid`

English:
lemma isDetecting_bot_of_isGroupoid
  given: [IsGroupoid C]
  proof: fun _ _ _ _ => inferInstance

中文:
引理 isDetecting_bot_of_isGroupoid
  条件: [是群胚 C]
  证明: fun _ _ _ _ => inferInstance
-/
lemma isDetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsDetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ => inferInstance

/--
lemma `isGroupoid_of_isCodetecting_bot` / 引理 `isGroupoid_of_isCodetecting_bot`

English:
lemma isGroupoid_of_isCodetecting_bot
  given: (h : IsCodetecting (⊥ : ObjectProperty C))
  proof: h _ (by simp)

中文:
引理 isGroupoid_of_isCodetecting_bot
  条件: (h : IsCodetecting (⊥ : ObjectProperty C))
  证明: h _ (by simp)
-/
lemma isGroupoid_of_isCodetecting_bot (h : IsCodetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)

/--
lemma `isCodetecting_bot_of_isGroupoid` / 引理 `isCodetecting_bot_of_isGroupoid`

English:
lemma isCodetecting_bot_of_isGroupoid
  given: [IsGroupoid C]
  proof: fun _ _ _ _ => inferInstance

中文:
引理 isCodetecting_bot_of_isGroupoid
  条件: [是群胚 C]
  证明: fun _ _ _ _ => inferInstance
-/
lemma isCodetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsCodetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ => inferInstance

end Empty

/--
lemma `IsSeparating.mk_of_exists_epi` / 引理 `IsSeparating.mk_of_exists_epi`

English:
lemma IsSeparating.mk_of_exists_epi
  proof: by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, p, _⟩ := hP X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (c.inj i ≫ p))

中文:
引理 IsSeparating.mk_of_存在_epi
  证明: by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, p, _⟩ := hP X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (c.inj i ≫ p))

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, c.inj, cancel_epi, hom_ext
-/
lemma IsSeparating.mk_of_exists_epi
    (hP : forall (X : C), exists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), Epi p) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, p, _⟩ := hP X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (c.inj i ≫ p))

/--
lemma `IsCoseparating.mk_of_exists_mono` / 引理 `IsCoseparating.mk_of_exists_mono`

English:
lemma IsCoseparating.mk_of_exists_mono
  proof: by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, j, _⟩ := hP Y
  rw [← cancel_mono j]
  exact Fan.IsLimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (j ≫ c.proj i))

中文:
引理 IsCoseparating.mk_of_存在_mono
  证明: by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, j, _⟩ := hP Y
  rw [← cancel_mono j]
  exact Fan.IsLimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (j ≫ c.proj i))

Depends on / 依赖: Fan.IsLimit.hom_ext, IsLimit, c.proj, cancel_mono, hom_ext
-/
lemma IsCoseparating.mk_of_exists_mono
    (hP : forall (X : C), exists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i)) (c : Fan s) (_ : IsLimit c)
      (j : X ⟶ c.pt), Mono j) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, j, _⟩ := hP Y
  rw [← cancel_mono j]
  exact Fan.IsLimit.hom_ext hc _ _
    (fun i => by simpa using h _ (hs i) (j ≫ c.proj i))

/--
lemma `IsSeparating.mk_of_exists_colimitsOfShape` / 引理 `IsSeparating.mk_of_exists_colimitsOfShape`

English:
lemma IsSeparating.mk_of_exists_colimitsOfShape
  proof: by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP X
  exact p.isColimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

中文:
引理 IsSeparating.mk_of_存在_colimitsOfShape
  证明: by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP X
  exact p.isColimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

Depends on / 依赖: hom_ext, isColimit, p.isColimit.hom_ext, p.prop_diag_obj, prop_diag_obj
-/
lemma IsSeparating.mk_of_exists_colimitsOfShape
    (hP : forall (X : C), exists (J : Type w) (_ : Category.{w'} J), P.colimitsOfShape J X) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP X
  exact p.isColimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

/--
lemma `IsCoseparating.mk_of_exists_limitsOfShape` / 引理 `IsCoseparating.mk_of_exists_limitsOfShape`

English:
lemma IsCoseparating.mk_of_exists_limitsOfShape
  proof: by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  exact p.isLimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

中文:
引理 IsCoseparating.mk_of_存在_limitsOfShape
  证明: by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  exact p.isLimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

Depends on / 依赖: hom_ext, isLimit, p.isLimit.hom_ext, p.prop_diag_obj, prop_diag_obj
-/
lemma IsCoseparating.mk_of_exists_limitsOfShape
    (hP : forall (X : C), exists (J : Type w) (_ : Category.{w'} J), P.limitsOfShape J X) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  exact p.isLimit.hom_ext (fun j => h _ (p.prop_diag_obj _) _)

variable (P)

section

/--
Definition of `coproductFromFamily` / `coproductFromFamily` 的定义

English:
abbreviation coproductFromFamily
  signature: (X : C) (i : CostructuredArrow P.ι X)
  body: i.left.obj

中文:
缩写 coproductFromFamily
  签名: (X : C) (i : CostructuredArrow P.ι X)
  定义体: i.left.obj

Depends on / 依赖: i.left.obj
-/
abbrev coproductFromFamily (X : C) (i : CostructuredArrow P.ι X) : C := i.left.obj

variable (X : C)

variable [HasCoproduct (P.coproductFromFamily X)]

/--
Definition of `coproductFrom` / `coproductFrom` 的定义

English:
abbreviation coproductFrom
  signature: : ∐ (P.coproductFromFamily X) ⟶ X
  body: Sigma.desc (fun i => i.hom)

中文:
缩写 coproductFrom
  签名: : ∐ (P.coproductFromFamily X) ⟶ X
  定义体: Sigma.desc (fun i => i.hom)

Depends on / 依赖: Sigma.desc, i.hom
-/
noncomputable abbrev coproductFrom : ∐ (P.coproductFromFamily X) ⟶ X :=
  Sigma.desc (fun i => i.hom)

variable {X} in
/--
Definition of `ιCoproductFrom` / `ιCoproductFrom` 的定义

English:
abbreviation ιCoproductFrom
  signature: {Y : C} (f : Y ⟶ X) (hY : P Y)
  body: by
  exact Sigma.ι (P.coproductFromFamily X) (CostructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

中文:
缩写 ιCoproductFrom
  签名: {Y : C} (f : Y ⟶ X) (hY : P Y)
  定义体: by
  exact Sigma.ι (P.coproductFromFamily X) (CostructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, P.coproductFromFamily, coproductFromFamily
-/
noncomputable abbrev ιCoproductFrom {Y : C} (f : Y ⟶ X) (hY : P Y) :
    Y ⟶ ∐ (P.coproductFromFamily X) := by
  exact Sigma.ι (P.coproductFromFamily X) (CostructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/--
lemma `IsSeparating.epi_coproductFrom` / 引理 `IsSeparating.epi_coproductFrom`

English:
lemma IsSeparating.epi_coproductFrom
  statement: (hP : P.IsSeparating)
  proof: hP _ _ (fun G hG h => by simpa using P.ιCoproductFrom h hG ≫= huv)

中文:
引理 IsSeparating.epi_coproductFrom
  结论: (hP : P.IsSeparating)
  证明: hP _ _ (fun G hG h => by simpa using P.ιCoproductFrom h hG ≫= huv)
-/
lemma IsSeparating.epi_coproductFrom (hP : P.IsSeparating)
    (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    Epi (P.coproductFrom X) where
  left_cancellation u v huv :=
    hP _ _ (fun G hG h => by simpa using P.ιCoproductFrom h hG ≫= huv)

/--
theorem `isSeparating_iff_epi` / 定理 `isSeparating_iff_epi`

English:
theorem isSeparating_iff_epi
  proof: ⟨fun hP X => hP.epi_coproductFrom X,
    fun hP => IsSeparating.mk_of_exists_epi (fun X => ⟨_, P.coproductFromFamily X,
      fun i => i.left.2, _, colimit.isColimit _, _, hP X⟩)⟩

中文:
定理 isSeparating_iff_epi
  证明: ⟨fun hP X => hP.epi_coproductFrom X,
    fun hP => IsSeparating.mk_of_exists_epi (fun X => ⟨_, P.coproductFromFamily X,
      fun i => i.left.2, _, colimit.isColimit _, _, hP X⟩)⟩

Depends on / 依赖: IsSeparating, IsSeparating.mk_of_exists_epi, P.coproductFromFamily, colimit, colimit.isColimit, coproductFromFamily, epi_coproductFrom, hP.epi_coproductFrom, i.left, isColimit, mk_of_exists_epi
-/
theorem isSeparating_iff_epi
    [forall (X : C), HasCoproduct (P.coproductFromFamily X)] :
    IsSeparating P ↔ forall X : C, Epi (P.coproductFrom X) :=
  ⟨fun hP X => hP.epi_coproductFrom X,
    fun hP => IsSeparating.mk_of_exists_epi (fun X => ⟨_, P.coproductFromFamily X,
      fun i => i.left.2, _, colimit.isColimit _, _, hP X⟩)⟩

section

/--
Definition of `productToFamily` / `productToFamily` 的定义

English:
abbreviation productToFamily
  signature: (X : C) (i : StructuredArrow X P.ι)
  body: i.right.obj

中文:
缩写 productToFamily
  签名: (X : C) (i : 结构化箭头 X P.ι)
  定义体: i.right.obj

Depends on / 依赖: i.right.obj
-/
abbrev productToFamily (X : C) (i : StructuredArrow X P.ι) : C := i.right.obj

variable (X : C)

variable [HasProduct (P.productToFamily X)]

/--
Definition of `productTo` / `productTo` 的定义

English:
abbreviation productTo
  signature: : X ⟶ ∏ᶜ (P.productToFamily X)
  body: Pi.lift (fun i => i.hom)

中文:
缩写 productTo
  签名: : X ⟶ ∏ᶜ (P.productToFamily X)
  定义体: Pi.lift (fun i => i.hom)

Depends on / 依赖: Pi.lift, i.hom
-/
noncomputable abbrev productTo : X ⟶ ∏ᶜ (P.productToFamily X) :=
  Pi.lift (fun i => i.hom)

variable {X} in
/--
Definition of `πProductTo` / `πProductTo` 的定义

English:
abbreviation πProductTo
  signature: {Y : C} (f : X ⟶ Y) (hY : P Y)
  body: by
  exact Pi.π (P.productToFamily X) (StructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

中文:
缩写 πProductTo
  签名: {Y : C} (f : X ⟶ Y) (hY : P Y)
  定义体: by
  exact Pi.π (P.productToFamily X) (StructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

Depends on / 依赖: P.productToFamily, StructuredArrow, StructuredArrow.mk, productToFamily
-/
noncomputable abbrev πProductTo {Y : C} (f : X ⟶ Y) (hY : P Y) :
    ∏ᶜ (P.productToFamily X) ⟶ Y := by
  exact Pi.π (P.productToFamily X) (StructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/--
lemma `IsCoseparating.mono_productTo` / 引理 `IsCoseparating.mono_productTo`

English:
lemma IsCoseparating.mono_productTo
  statement: (hP : P.IsCoseparating)
  proof: hP _ _ (fun G hG h => by simpa using huv =≫ P.πProductTo h hG)

中文:
引理 IsCoseparating.mono_productTo
  结论: (hP : P.IsCoseparating)
  证明: hP _ _ (fun G hG h => by simpa using huv =≫ P.πProductTo h hG)

Depends on / 依赖: RegularMono, RegularMono.equalizer, equalizer, isRegularMono_of_regularMono
-/
lemma IsCoseparating.mono_productTo (hP : P.IsCoseparating)
    (X : C) [HasProduct (P.productToFamily X)] :
    Mono (P.productTo X) where
  right_cancellation u v huv :=
    hP _ _ (fun G hG h => by simpa using huv =≫ P.πProductTo h hG)

/--
theorem `isCoseparating_iff_mono` / 定理 `isCoseparating_iff_mono`

English:
theorem isCoseparating_iff_mono
  proof: ⟨fun hP X => hP.mono_productTo X,
    fun hP => IsCoseparating.mk_of_exists_mono (fun X => ⟨_, P.productToFamily X,
      fun i => i.right.2, _, limit.isLimit _, _, hP X⟩)⟩

中文:
定理 isCoseparating_iff_mono
  证明: ⟨fun hP X => hP.mono_productTo X,
    fun hP => IsCoseparating.mk_of_exists_mono (fun X => ⟨_, P.productToFamily X,
      fun i => i.right.2, _, limit.isLimit _, _, hP X⟩)⟩

Depends on / 依赖: IsCoseparating, IsCoseparating.mk_of_exists_mono, P.productToFamily, hP.mono_productTo, i.right, isLimit, limit.isLimit, mk_of_exists_mono, mono_productTo, productToFamily
-/
theorem isCoseparating_iff_mono
    [forall (X : C), HasProduct (P.productToFamily X)] :
    IsCoseparating P ↔ forall X : C, Mono (P.productTo X) :=
  ⟨fun hP X => hP.mono_productTo X,
    fun hP => IsCoseparating.mk_of_exists_mono (fun X => ⟨_, P.productToFamily X,
      fun i => i.right.2, _, limit.isLimit _, _, hP X⟩)⟩

end ObjectProperty

/--
theorem `hasInitial_of_isCoseparating` / 定理 `hasInitial_of_isCoseparating`

English:
theorem hasInitial_of_isCoseparating
  statement: [LocallySmall.{w} C] [WellPowered.{w} C]
  proof: by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasProductsOfShape_of_small C (Subtype P)
  have := fun A => hasProductsOfShape_of_small.{w} C (StructuredArrow A P.ι)
  let := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : Subtype P -> C)))
  suffices forall A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C)
  have := hP.mono_productTo
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s : ∏ᶜ (Subtype.val (p := P)) ⟶ ∏ᶜ P.productToFamily A :=
      Pi.lift (fun f => Pi.π Subtype.val ⟨f.right.obj, f.right.property⟩)
    exact Subobject.ofLEMk _
      (pullback.fst _ _ : pullback s (P.productTo A) ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices forall (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext
      simp⟩

中文:
定理 hasInitial_of_isCoseparating
  结论: [LocallySmall.{w} C] [良幂.{w} C]
  证明: by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasProductsOfShape_of_small C (Subtype P)
  have := fun A => hasProductsOfShape_of_small.{w} C (StructuredArrow A P.ι)
  let := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : Subtype P -> C)))
  suffices forall A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C)
  have := hP.mono_productTo
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s : ∏ᶜ (Subtype.val (p := P)) ⟶ ∏ᶜ P.productToFamily A :=
      Pi.lift (fun f => Pi.π Subtype.val ⟨f.right.obj, f.right.property⟩)
    exact Subobject.ofLEMk _
      (pullback.fst _ _ : pullback s (P.productTo A) ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices forall (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext
      simp⟩

Depends on / 依赖: IsSplitMono, StructuredArrow, Subobject, Subtype, Subtype.val, Unique, completeLatticeOfCompleteSemilatticeInf, hP.mono_productTo, hasFiniteLimits_of_hasLimitsOfSize, hasInitial_of_unique, hasProductsOfShape_of_small, mono_productTo
-/
theorem hasInitial_of_isCoseparating [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasLimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsCoseparating) : HasInitial C := by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasProductsOfShape_of_small C (Subtype P)
  have := fun A => hasProductsOfShape_of_small.{w} C (StructuredArrow A P.ι)
  let := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : Subtype P -> C)))
  suffices forall A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : Subtype P -> C))) : C)
  have := hP.mono_productTo
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s : ∏ᶜ (Subtype.val (p := P)) ⟶ ∏ᶜ P.productToFamily A :=
      Pi.lift (fun f => Pi.π Subtype.val ⟨f.right.obj, f.right.property⟩)
    exact Subobject.ofLEMk _
      (pullback.fst _ _ : pullback s (P.productTo A) ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices forall (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext
      simp⟩

/--
theorem `hasTerminal_of_isSeparating` / 定理 `hasTerminal_of_isSeparating`

English:
theorem hasTerminal_of_isSeparating
  statement: [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ]
  proof: by
  have : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating (P.isCoseparating_op_iff.2 hP)
  exact hasTerminal_of_hasInitial_op

中文:
定理 hasTerminal_of_isSeparating
  结论: [LocallySmall.{w} Cᵒᵖ] [良幂.{w} Cᵒᵖ]
  证明: by
  have : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating (P.isCoseparating_op_iff.2 hP)
  exact hasTerminal_of_hasInitial_op

Depends on / 依赖: HasInitial, P.isCoseparating_op_iff, hasInitial_of_isCoseparating, hasTerminal_of_hasInitial_op, isCoseparating_op_iff
-/
theorem hasTerminal_of_isSeparating [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ]
    [HasColimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsSeparating) : HasTerminal C := by
  have : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating (P.isCoseparating_op_iff.2 hP)
  exact hasTerminal_of_hasInitial_op

section WellPowered

namespace Subobject

/--
theorem `eq_of_le_of_isDetecting` / 定理 `eq_of_le_of_isDetecting`

English:
theorem eq_of_le_of_isDetecting
  statement: {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  proof: by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]

中文:
定理 eq_of_le_of_isDetecting
  结论: {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  证明: by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]

Depends on / 依赖: Category, Category.assoc, Factors, P.Factors, Q.arrow, Subobject, Subobject.ofLE, cancel_mono, factorThru, factorThru_arrow, factors_iff, le_antisymm, le_of_comm, ofLE_arrow
-/
theorem eq_of_le_of_isDetecting {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h₁ : P <= Q)
    (h₂ : forall (G : C) (_ : 𝒢 G), forall {f : G ⟶ X}, Q.Factors f -> P.Factors f) : P = Q := by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]

/--
theorem `inf_eq_of_isDetecting` / 定理 `inf_eq_of_isDetecting`

English:
theorem inf_eq_of_isDetecting
  statement: [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  proof: eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩

中文:
定理 inf_eq_of_isDetecting
  结论: [有Pullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  证明: eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩

Depends on / 依赖: _root_, _root_.inf_le_left, eq_of_le_of_isDetecting, inf_factors, inf_le_left
-/
theorem inf_eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : forall (G : C) (_ : 𝒢 G), forall {f : G ⟶ X}, P.Factors f -> Q.Factors f) :
    P ⊓ Q = P :=
  eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩

/--
theorem `eq_of_isDetecting` / 定理 `eq_of_isDetecting`

English:
theorem eq_of_isDetecting
  statement: [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  proof: calc
P = P ⊓ Q := Eq.symm inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

中文:
定理 eq_of_isDetecting
  结论: [有Pullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
  证明: calc
P = P ⊓ Q := Eq.symm inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

Depends on / 依赖: Eq.symm, inf_comm, inf_eq_of_isDetecting
-/
theorem eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : forall (G : C) (_ : 𝒢 G),
      forall {f : G ⟶ X}, P.Factors f ↔ Q.Factors f) : P = Q :=
  calc
P = P ⊓ Q := Eq.symm inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

end Subobject

/--
theorem `wellPowered_of_isDetecting` / 定理 `wellPowered_of_isDetecting`

English:
theorem wellPowered_of_isDetecting
  statement: [HasPullbacks C] {𝒢 : ObjectProperty C}
  proof: small_of_injective
    (f := fun P : Subobject X => { f : Σ G : Subtype 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)

中文:
定理 wellPowered_of_isDetecting
  结论: [有Pullbacks C] {𝒢 : ObjectProperty C}
  证明: small_of_injective
    (f := fun P : Subobject X => { f : Σ G : Subtype 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)

Depends on / 依赖: IsRegularMono, StrongMono, small_of_injective
-/
theorem wellPowered_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C}
    [ObjectProperty.Small.{w} 𝒢] [LocallySmall.{w} C]
    (h𝒢 : 𝒢.IsDetecting) : WellPowered.{w} C where
  subobject_small X := small_of_injective
    (f := fun P : Subobject X => { f : Σ G : Subtype 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)

end WellPowered

namespace StructuredArrow

variable (S : D) (T : C ⥤ D)

/--
theorem `isCoseparating_inverseImage_proj` / 定理 `isCoseparating_inverseImage_proj`

English:
theorem isCoseparating_inverseImage_proj
  given: {P : ObjectProperty C} (hP : P.IsCoseparating)
  proof: by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

中文:
定理 isCoseparating_inverseImage_proj
  条件: {P : ObjectProperty C} (hP : P.IsCoseparating)
  证明: by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

Depends on / 依赖: CommaMorphism, CommaMorphism.right, T.map, Y.hom, congr_arg
-/
theorem isCoseparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsCoseparating) :
    (P.inverseImage (proj S T)).IsCoseparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

end StructuredArrow

namespace CostructuredArrow

variable (S : C ⥤ D) (T : D)

/--
theorem `isSeparating_inverseImage_proj` / 定理 `isSeparating_inverseImage_proj`

English:
theorem isSeparating_inverseImage_proj
  given: {P : ObjectProperty C} (hP : P.IsSeparating)
  proof: by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

中文:
定理 isSeparating_inverseImage_proj
  条件: {P : ObjectProperty C} (hP : P.IsSeparating)
  证明: by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

Depends on / 依赖: CommaMorphism, CommaMorphism.left, S.map, X.hom, congr_arg
-/
theorem isSeparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsSeparating) :
    (P.inverseImage (proj S T)).IsSeparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

end CostructuredArrow

/--
Definition of `IsSeparator` / `IsSeparator` 的定义

English:
definition IsSeparator
  signature: (G : C)
  body: ObjectProperty.IsSeparating (.singleton G)

中文:
定义 IsSeparator
  签名: (G : C)
  定义体: ObjectProperty.IsSeparating (.singleton G)

Depends on / 依赖: IsSeparating, ObjectProperty, ObjectProperty.IsSeparating, SplitMonoCategory, regularMonoCategoryOfSplitMonoCategory, singleton
-/
def IsSeparator (G : C) : Prop :=
  ObjectProperty.IsSeparating (.singleton G)

/--
Definition of `IsCoseparator` / `IsCoseparator` 的定义

English:
definition IsCoseparator
  signature: (G : C)
  body: ObjectProperty.IsCoseparating (.singleton G)

中文:
定义 IsCoseparator
  签名: (G : C)
  定义体: ObjectProperty.IsCoseparating (.singleton G)

Depends on / 依赖: IsCoseparating, IsRegularMonoCategory, ObjectProperty, ObjectProperty.IsCoseparating, singleton, strongMonoCategory_of_regularMonoCategory
-/
def IsCoseparator (G : C) : Prop :=
  ObjectProperty.IsCoseparating (.singleton G)

/--
Definition of `IsDetector` / `IsDetector` 的定义

English:
definition IsDetector
  signature: (G : C)
  body: ObjectProperty.IsDetecting (.singleton G)

中文:
定义 IsDetector
  签名: (G : C)
  定义体: ObjectProperty.IsDetecting (.singleton G)

Depends on / 依赖: IsDetecting, ObjectProperty, ObjectProperty.IsDetecting, singleton
-/
def IsDetector (G : C) : Prop :=
  ObjectProperty.IsDetecting (.singleton G)

/--
Definition of `IsCodetector` / `IsCodetector` 的定义

English:
definition IsCodetector
  signature: (G : C)
  body: ObjectProperty.IsCodetecting (.singleton G)

中文:
定义 IsCodetector
  签名: (G : C)
  定义体: ObjectProperty.IsCodetecting (.singleton G)

Depends on / 依赖: IsCodetecting, ObjectProperty, ObjectProperty.IsCodetecting, singleton
-/
def IsCodetector (G : C) : Prop :=
  ObjectProperty.IsCodetecting (.singleton G)

section Equivalence

/--
theorem `IsSeparator.of_equivalence` / 定理 `IsSeparator.of_equivalence`

English:
theorem IsSeparator.of_equivalence
  given: {G : C} (h : IsSeparator G) (α : C ≌ D)
  proof: by
  simpa using! ObjectProperty.IsSeparating.of_equivalence h α

中文:
定理 IsSeparator.of_equivalence
  条件: {G : C} (h : IsSeparator G) (α : C ≌ D)
  证明: by
  simpa using! ObjectProperty.IsSeparating.of_equivalence h α

Depends on / 依赖: IsSeparating, ObjectProperty, ObjectProperty.IsSeparating.of_equivalence, of_equivalence
-/
theorem IsSeparator.of_equivalence {G : C} (h : IsSeparator G) (α : C ≌ D) :
    IsSeparator (α.functor.obj G) := by
  simpa using! ObjectProperty.IsSeparating.of_equivalence h α

/--
theorem `IsCoseparator.of_equivalence` / 定理 `IsCoseparator.of_equivalence`

English:
theorem IsCoseparator.of_equivalence
  given: {G : C} (h : IsCoseparator G) (α : C ≌ D)
  proof: by
  simpa using! ObjectProperty.IsCoseparating.of_equivalence h α

中文:
定理 IsCoseparator.of_equivalence
  条件: {G : C} (h : IsCoseparator G) (α : C ≌ D)
  证明: by
  simpa using! ObjectProperty.IsCoseparating.of_equivalence h α

Depends on / 依赖: IsCoseparating, ObjectProperty, ObjectProperty.IsCoseparating.of_equivalence, of_equivalence
-/
theorem IsCoseparator.of_equivalence {G : C} (h : IsCoseparator G) (α : C ≌ D) :
    IsCoseparator (α.functor.obj G) := by
  simpa using! ObjectProperty.IsCoseparating.of_equivalence h α

end Equivalence

section Dual

open ObjectProperty

/--
theorem `isSeparator_op_iff` / 定理 `isSeparator_op_iff`

English:
theorem isSeparator_op_iff
  given: (G : C)
  statement: IsSeparator (op G) ↔ IsCoseparator G
  proof: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_op_iff]; rw [op_singleton]

中文:
定理 isSeparator_op_iff
  条件: (G : C)
  结论: IsSeparator (op G) ↔ IsCoseparator G
  证明: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_op_iff]; rw [op_singleton]

Depends on / 依赖: IsCoseparator, IsSeparator, isSeparating_op_iff, op_singleton
-/
theorem isSeparator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G := by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_op_iff]; rw [op_singleton]

/--
theorem `isCoseparator_op_iff` / 定理 `isCoseparator_op_iff`

English:
theorem isCoseparator_op_iff
  given: (G : C)
  statement: IsCoseparator (op G) ↔ IsSeparator G
  proof: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_op_iff]; rw [op_singleton]

中文:
定理 isCoseparator_op_iff
  条件: (G : C)
  结论: IsCoseparator (op G) ↔ IsSeparator G
  证明: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_op_iff]; rw [op_singleton]

Depends on / 依赖: IsCoseparator, IsSeparator, isCoseparating_op_iff, op_singleton
-/
theorem isCoseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G := by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_op_iff]; rw [op_singleton]

/--
theorem `isCoseparator_unop_iff` / 定理 `isCoseparator_unop_iff`

English:
theorem isCoseparator_unop_iff
  given: (G : Cᵒᵖ)
  statement: IsCoseparator (unop G) ↔ IsSeparator G
  proof: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_unop_iff]; rw [unop_singleton]

中文:
定理 isCoseparator_unop_iff
  条件: (G : Cᵒᵖ)
  结论: IsCoseparator (unop G) ↔ IsSeparator G
  证明: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_unop_iff]; rw [unop_singleton]

Depends on / 依赖: IsCoseparator, IsSeparator, isCoseparating_unop_iff, unop_singleton
-/
theorem isCoseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G := by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isCoseparating_unop_iff]; rw [unop_singleton]

/--
theorem `isSeparator_unop_iff` / 定理 `isSeparator_unop_iff`

English:
theorem isSeparator_unop_iff
  given: (G : Cᵒᵖ)
  statement: IsSeparator (unop G) ↔ IsCoseparator G
  proof: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_unop_iff]; rw [unop_singleton]

中文:
定理 isSeparator_unop_iff
  条件: (G : Cᵒᵖ)
  结论: IsSeparator (unop G) ↔ IsCoseparator G
  证明: by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_unop_iff]; rw [unop_singleton]

Depends on / 依赖: IsCoseparator, IsSeparator, isSeparating_unop_iff, unop_singleton
-/
theorem isSeparator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G := by
  rw [IsSeparator]; rw [IsCoseparator]; rw [← isSeparating_unop_iff]; rw [unop_singleton]

/--
theorem `isDetector_op_iff` / 定理 `isDetector_op_iff`

English:
theorem isDetector_op_iff
  given: (G : C)
  statement: IsDetector (op G) ↔ IsCodetector G
  proof: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_op_iff]; rw [op_singleton]

中文:
定理 isDetector_op_iff
  条件: (G : C)
  结论: IsDetector (op G) ↔ IsCodetector G
  证明: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_op_iff]; rw [op_singleton]

Depends on / 依赖: IsCodetector, IsDetector, isDetecting_op_iff, op_singleton
-/
theorem isDetector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G := by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_op_iff]; rw [op_singleton]

/--
theorem `isCodetector_op_iff` / 定理 `isCodetector_op_iff`

English:
theorem isCodetector_op_iff
  given: (G : C)
  statement: IsCodetector (op G) ↔ IsDetector G
  proof: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_op_iff]; rw [op_singleton]

中文:
定理 isCodetector_op_iff
  条件: (G : C)
  结论: IsCodetector (op G) ↔ IsDetector G
  证明: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_op_iff]; rw [op_singleton]

Depends on / 依赖: IsCodetector, IsDetector, isCodetecting_op_iff, op_singleton
-/
theorem isCodetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G := by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_op_iff]; rw [op_singleton]

/--
theorem `isCodetector_unop_iff` / 定理 `isCodetector_unop_iff`

English:
theorem isCodetector_unop_iff
  given: (G : Cᵒᵖ)
  statement: IsCodetector (unop G) ↔ IsDetector G
  proof: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_unop_iff]; rw [unop_singleton]

中文:
定理 isCodetector_unop_iff
  条件: (G : Cᵒᵖ)
  结论: IsCodetector (unop G) ↔ IsDetector G
  证明: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_unop_iff]; rw [unop_singleton]

Depends on / 依赖: IsCodetector, IsDetector, isCodetecting_unop_iff, unop_singleton
-/
theorem isCodetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G := by
  rw [IsDetector]; rw [IsCodetector]; rw [← isCodetecting_unop_iff]; rw [unop_singleton]

/--
theorem `isDetector_unop_iff` / 定理 `isDetector_unop_iff`

English:
theorem isDetector_unop_iff
  given: (G : Cᵒᵖ)
  statement: IsDetector (unop G) ↔ IsCodetector G
  proof: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_unop_iff]; rw [unop_singleton]

中文:
定理 isDetector_unop_iff
  条件: (G : Cᵒᵖ)
  结论: IsDetector (unop G) ↔ IsCodetector G
  证明: by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_unop_iff]; rw [unop_singleton]

Depends on / 依赖: IsCodetector, IsDetector, isDetecting_unop_iff, unop_singleton
-/
theorem isDetector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G := by
  rw [IsDetector]; rw [IsCodetector]; rw [← isDetecting_unop_iff]; rw [unop_singleton]

end Dual

/--
theorem `IsDetector.isSeparator` / 定理 `IsDetector.isSeparator`

English:
theorem IsDetector.isSeparator
  given: [HasEqualizers C] {G : C}
  statement: IsDetector G -> IsSeparator G
  proof: ObjectProperty.IsDetecting.isSeparating

中文:
定理 IsDetector.isSeparator
  条件: [HasEqualizers C] {G : C}
  结论: IsDetector G -> IsSeparator G
  证明: ObjectProperty.IsDetecting.isSeparating

Depends on / 依赖: IsDetecting, ObjectProperty, ObjectProperty.IsDetecting.isSeparating, isSeparating
-/
theorem IsDetector.isSeparator [HasEqualizers C] {G : C} : IsDetector G -> IsSeparator G :=
  ObjectProperty.IsDetecting.isSeparating

/--
theorem `IsCodetector.isCoseparator` / 定理 `IsCodetector.isCoseparator`

English:
theorem IsCodetector.isCoseparator
  given: [HasCoequalizers C] {G : C}
  statement: IsCodetector G -> IsCoseparator G
  proof: ObjectProperty.IsCodetecting.isCoseparating

中文:
定理 IsCodetector.isCoseparator
  条件: [HasCoequalizers C] {G : C}
  结论: IsCodetector G -> IsCoseparator G
  证明: ObjectProperty.IsCodetecting.isCoseparating

Depends on / 依赖: IsCodetecting, ObjectProperty, ObjectProperty.IsCodetecting.isCoseparating, isCoseparating
-/
theorem IsCodetector.isCoseparator [HasCoequalizers C] {G : C} : IsCodetector G -> IsCoseparator G :=
  ObjectProperty.IsCodetecting.isCoseparating

/--
theorem `IsSeparator.isDetector` / 定理 `IsSeparator.isDetector`

English:
theorem IsSeparator.isDetector
  given: [Balanced C] {G : C}
  statement: IsSeparator G -> IsDetector G
  proof: ObjectProperty.IsSeparating.isDetecting

中文:
定理 IsSeparator.isDetector
  条件: [Balanced C] {G : C}
  结论: IsSeparator G -> IsDetector G
  证明: ObjectProperty.IsSeparating.isDetecting

Depends on / 依赖: IsSeparating, ObjectProperty, ObjectProperty.IsSeparating.isDetecting, isDetecting
-/
theorem IsSeparator.isDetector [Balanced C] {G : C} : IsSeparator G -> IsDetector G :=
  ObjectProperty.IsSeparating.isDetecting

/--
theorem `IsCoseparator.isCodetector` / 定理 `IsCoseparator.isCodetector`

English:
theorem IsCoseparator.isCodetector
  given: [Balanced C] {G : C}
  statement: IsCoseparator G -> IsCodetector G
  proof: ObjectProperty.IsCoseparating.isCodetecting

中文:
定理 IsCoseparator.isCodetector
  条件: [Balanced C] {G : C}
  结论: IsCoseparator G -> IsCodetector G
  证明: ObjectProperty.IsCoseparating.isCodetecting

Depends on / 依赖: IsCoseparating, ObjectProperty, ObjectProperty.IsCoseparating.isCodetecting, isCodetecting
-/
theorem IsCoseparator.isCodetector [Balanced C] {G : C} : IsCoseparator G -> IsCodetector G :=
  ObjectProperty.IsCoseparating.isCodetecting

/--
theorem `isSeparator_def` / 定理 `isSeparator_def`

English:
theorem isSeparator_def
  given: (G : C)
  proof: ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

中文:
定理 isSeparator_def
  条件: (G : C)
  证明: ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.singleton_iff, singleton_iff
-/
theorem isSeparator_def (G : C) :
    IsSeparator G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

/--
theorem `IsSeparator.def` / 定理 `IsSeparator.def`

English:
theorem IsSeparator.def
  given: {G : C}
  proof: (isSeparator_def _).1

中文:
定理 IsSeparator.def
  条件: {G : C}
  证明: (isSeparator_def _).1

Depends on / 依赖: isSeparator_def
-/
theorem IsSeparator.def {G : C} :
    IsSeparator G -> forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g :=
  (isSeparator_def _).1

/--
theorem `isCoseparator_def` / 定理 `isCoseparator_def`

English:
theorem isCoseparator_def
  given: (G : C)
  proof: ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

中文:
定理 isCoseparator_def
  条件: (G : C)
  证明: ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.singleton_iff, singleton_iff
-/
theorem isCoseparator_def (G : C) :
    IsCoseparator G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩

/--
theorem `IsCoseparator.def` / 定理 `IsCoseparator.def`

English:
theorem IsCoseparator.def
  given: {G : C}
  proof: (isCoseparator_def _).1

中文:
定理 IsCoseparator.def
  条件: {G : C}
  证明: (isCoseparator_def _).1

Depends on / 依赖: isCoseparator_def
-/
theorem IsCoseparator.def {G : C} :
    IsCoseparator G -> forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f = g :=
  (isCoseparator_def _).1

/--
theorem `isDetector_def` / 定理 `isDetector_def`

English:
theorem isDetector_def
  given: (G : C)
  proof: ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

中文:
定理 isDetector_def
  条件: (G : C)
  证明: ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.singleton_iff, coequalizerRegular, singleton_iff
-/
theorem isDetector_def (G : C) :
    IsDetector G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : G ⟶ Y, exists! h', h' ≫ f = h) -> IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

/--
theorem `IsDetector.def` / 定理 `IsDetector.def`

English:
theorem IsDetector.def
  given: {G : C}
  proof: (isDetector_def _).1

中文:
定理 IsDetector.def
  条件: {G : C}
  证明: (isDetector_def _).1

Depends on / 依赖: isDetector_def
-/
theorem IsDetector.def {G : C} :
    IsDetector G -> forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : G ⟶ Y, exists! h', h' ≫ f = h) -> IsIso f :=
  (isDetector_def _).1

/--
theorem `isCodetector_def` / 定理 `isCodetector_def`

English:
theorem isCodetector_def
  given: (G : C)
  proof: ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

中文:
定理 isCodetector_def
  条件: (G : C)
  证明: ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.singleton_iff, singleton_iff
-/
theorem isCodetector_def (G : C) :
    IsCodetector G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : X ⟶ G, exists! h', f ≫ h' = h) -> IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩

/--
theorem `IsCodetector.def` / 定理 `IsCodetector.def`

English:
theorem IsCodetector.def
  given: {G : C}
  proof: (isCodetector_def _).1

中文:
定理 IsCodetector.def
  条件: {G : C}
  证明: (isCodetector_def _).1

Depends on / 依赖: isCodetector_def
-/
theorem IsCodetector.def {G : C} :
    IsCodetector G -> forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : X ⟶ G, exists! h', f ≫ h' = h) -> IsIso f :=
  (isCodetector_def _).1

open ConcreteCategory

/--
theorem `isSeparator_iff_faithful_coyoneda_obj` / 定理 `isSeparator_iff_faithful_coyoneda_obj`

English:
theorem isSeparator_iff_faithful_coyoneda_obj
  given: (G : C)
  proof: ⟨fun hG => ⟨fun hfg => hG.def _ _ (congr_hom hfg)⟩, fun _ =>
    (isSeparator_def _).2 fun _ _ _ _ hfg => (coyoneda.obj (op G)).map_injective
      (by ext; apply hfg)⟩

中文:
定理 isSeparator_iff_faithful_coyoneda_obj
  条件: (G : C)
  证明: ⟨fun hG => ⟨fun hfg => hG.def _ _ (congr_hom hfg)⟩, fun _ =>
    (isSeparator_def _).2 fun _ _ _ _ hfg => (coyoneda.obj (op G)).map_injective
      (by ext; apply hfg)⟩

Depends on / 依赖: congr_hom, coyoneda, coyoneda.obj, hG.def, isSeparator_def, map_injective
-/
theorem isSeparator_iff_faithful_coyoneda_obj (G : C) :
    IsSeparator G ↔ (coyoneda.obj (op G)).Faithful :=
  ⟨fun hG => ⟨fun hfg => hG.def _ _ (congr_hom hfg)⟩, fun _ =>
    (isSeparator_def _).2 fun _ _ _ _ hfg => (coyoneda.obj (op G)).map_injective
      (by ext; apply hfg)⟩

/--
theorem `isCoseparator_iff_faithful_yoneda_obj` / 定理 `isCoseparator_iff_faithful_yoneda_obj`

English:
theorem isCoseparator_iff_faithful_yoneda_obj
  given: (G : C)
  statement: IsCoseparator G ↔ (yoneda.obj G).Faithful
  proof: ⟨fun hG => ⟨fun hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_hom hfg))⟩, fun _ =>
    (isCoseparator_def _).2 fun _ _ _ _ hfg =>
Quiver.Hom.op_inj (yoneda.obj G).map_injective (by ext; apply hfg)⟩

中文:
定理 isCoseparator_iff_faithful_yoneda_obj
  条件: (G : C)
  结论: IsCoseparator G ↔ (yoneda.obj G).忠实
  证明: ⟨fun hG => ⟨fun hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_hom hfg))⟩, fun _ =>
    (isCoseparator_def _).2 fun _ _ _ _ hfg =>
Quiver.Hom.op_inj (yoneda.obj G).map_injective (by ext; apply hfg)⟩

Depends on / 依赖: EffectiveEpi, IsRegularEpi, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, congr_hom, hG.def, isCoseparator_def, map_injective, op_inj, unop_inj, yoneda, yoneda.obj
-/
theorem isCoseparator_iff_faithful_yoneda_obj (G : C) : IsCoseparator G ↔ (yoneda.obj G).Faithful :=
  ⟨fun hG => ⟨fun hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_hom hfg))⟩, fun _ =>
    (isCoseparator_def _).2 fun _ _ _ _ hfg =>
Quiver.Hom.op_inj (yoneda.obj G).map_injective (by ext; apply hfg)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSeparator_iff_epi` / 定理 `isSeparator_iff_epi`

English:
theorem isSeparator_iff_epi
  given: (G : C) [forall A : C, HasCoproduct fun _ : G ⟶ A => G]
  proof: by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · have := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

中文:
定理 isSeparator_iff_epi
  条件: (G : C) [对任意 A : C, HasCoproduct fun _ : G ⟶ A => G]
  证明: by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · have := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

Depends on / 依赖: Sigma.desc, cancel_epi, colimit, colimit.hom_ext, hom_ext, isSeparator_def, j.as
-/
theorem isSeparator_iff_epi (G : C) [forall A : C, HasCoproduct fun _ : G ⟶ A => G] :
    IsSeparator G ↔ forall A : C, Epi (Sigma.desc fun f : G ⟶ A => f) := by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · have := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isCoseparator_iff_mono` / 定理 `isCoseparator_iff_mono`

English:
theorem isCoseparator_iff_mono
  given: (G : C) [forall A : C, HasProduct fun _ : A ⟶ G => G]
  proof: by
  rw [isCoseparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π _ i
  · have := h Y
    refine (cancel_mono (Pi.lift fun f : Y ⟶ G => f)).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as

中文:
定理 isCoseparator_iff_mono
  条件: (G : C) [对任意 A : C, HasProduct fun _ : A ⟶ G => G]
  证明: by
  rw [isCoseparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π _ i
  · have := h Y
    refine (cancel_mono (Pi.lift fun f : Y ⟶ G => f)).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as

Depends on / 依赖: Pi.lift, cancel_mono, hom_ext, isCoseparator_def, j.as, limit.hom_ext
-/
theorem isCoseparator_iff_mono (G : C) [forall A : C, HasProduct fun _ : A ⟶ G => G] :
    IsCoseparator G ↔ forall A : C, Mono (Pi.lift fun f : A ⟶ G => f) := by
  rw [isCoseparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π _ i
  · have := h Y
    refine (cancel_mono (Pi.lift fun f : Y ⟶ G => f)).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as

section ZeroMorphisms

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSeparator_of_isColimit_cofan` / 引理 `isSeparator_of_isColimit_cofan`

English:
lemma isSeparator_of_isColimit_cofan
  statement: {β : Type w} {f : β -> C}
  proof: by
  rw [isSeparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using c.inj b ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))

中文:
引理 isSeparator_of_isColimit_cofan
  结论: {β : 类型 w} {f : β -> C}
  证明: by
  rw [isSeparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using c.inj b ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))

Depends on / 依赖: Cofan.mk, Pi.single, c.inj, classical, hc.desc, isSeparator_def, single
-/
lemma isSeparator_of_isColimit_cofan {β : Type w} {f : β -> C}
    (hf : ObjectProperty.IsSeparating (.ofObj f)) {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt := by
  rw [isSeparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using c.inj b ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))

/--
lemma `isSeparator_iff_of_isColimit_cofan` / 引理 `isSeparator_iff_of_isColimit_cofan`

English:
lemma isSeparator_iff_of_isColimit_cofan
  statement: {β : Type w} {f : β -> C}
  proof: by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (c.inj _ ≫ g)

中文:
引理 isSeparator_iff_of_isColimit_cofan
  结论: {β : 类型 w} {f : β -> C}
  证明: by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (c.inj _ ≫ g)

Depends on / 依赖: b.as, c.inj, h.def, hc.hom_ext, hom_ext, isSeparator_of_isColimit_cofan
-/
lemma isSeparator_iff_of_isColimit_cofan {β : Type w} {f : β -> C}
    {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt ↔ ObjectProperty.IsSeparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (c.inj _ ≫ g)

/--
theorem `isSeparator_sigma` / 定理 `isSeparator_sigma`

English:
theorem isSeparator_sigma
  given: {β : Type w} (f : β -> C) [HasCoproduct f]
  proof: isSeparator_iff_of_isColimit_cofan (hc := colimit.isColimit _)

中文:
定理 isSeparator_sigma
  条件: {β : 类型 w} (f : β -> C) [HasCoproduct f]
  证明: isSeparator_iff_of_isColimit_cofan (hc := colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isSeparator_iff_of_isColimit_cofan
-/
theorem isSeparator_sigma {β : Type w} (f : β -> C) [HasCoproduct f] :
    IsSeparator (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj f) :=
  isSeparator_iff_of_isColimit_cofan (hc := colimit.isColimit _)

/--
theorem `isSeparator_coprod` / 定理 `isSeparator_coprod`

English:
theorem isSeparator_coprod
  given: (G H : C) [HasBinaryCoproduct G H]
  proof: by
  refine (isSeparator_iff_of_isColimit_cofan (coprodIsCoprod G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

中文:
定理 isSeparator_coprod
  条件: (G H : C) [HasBinaryCoproduct G H]
  证明: by
  refine (isSeparator_iff_of_isColimit_cofan (coprodIsCoprod G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

Depends on / 依赖: Iff.rfl, ObjectProperty, ObjectProperty.ofObj_iff, ObjectProperty.pair_iff, convert, coprodIsCoprod, exacts, isSeparator_iff_of_isColimit_cofan, ofObj_iff, pair_iff
-/
theorem isSeparator_coprod (G H : C) [HasBinaryCoproduct G H] :
    IsSeparator (G ⨿ H) ↔ ObjectProperty.IsSeparating (.pair G H) := by
  refine (isSeparator_iff_of_isColimit_cofan (coprodIsCoprod G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

/--
theorem `isSeparator_coprod_of_isSeparator_left` / 定理 `isSeparator_coprod_of_isSeparator_left`

English:
theorem isSeparator_coprod_of_isSeparator_left
  statement: (G H : C) [HasBinaryCoproduct G H]
  proof: (isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hG by simp

中文:
定理 isSeparator_coprod_of_isSeparator_left
  结论: (G H : C) [HasBinaryCoproduct G H]
  证明: (isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hG by simp

Depends on / 依赖: IsSeparating, ObjectProperty, ObjectProperty.IsSeparating.of_le, isSeparator_coprod, of_le
-/
theorem isSeparator_coprod_of_isSeparator_left (G H : C) [HasBinaryCoproduct G H]
    (hG : IsSeparator G) : IsSeparator (G ⨿ H) :=
(isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hG by simp

/--
theorem `isSeparator_coprod_of_isSeparator_right` / 定理 `isSeparator_coprod_of_isSeparator_right`

English:
theorem isSeparator_coprod_of_isSeparator_right
  statement: (G H : C) [HasBinaryCoproduct G H]
  proof: (isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hH by simp

中文:
定理 isSeparator_coprod_of_isSeparator_right
  结论: (G H : C) [HasBinaryCoproduct G H]
  证明: (isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hH by simp

Depends on / 依赖: IsRegularEpi, IsSeparating, IsSplitEpi, ObjectProperty, ObjectProperty.IsSeparating.of_le, isSeparator_coprod, of_le
-/
theorem isSeparator_coprod_of_isSeparator_right (G H : C) [HasBinaryCoproduct G H]
    (hH : IsSeparator H) : IsSeparator (G ⨿ H) :=
(isSeparator_coprod _ _).2 ObjectProperty.IsSeparating.of_le hH by simp

/--
theorem `ObjectProperty.IsSeparating.isSeparator_coproduct` / 定理 `ObjectProperty.IsSeparating.isSeparator_coproduct`

English:
theorem ObjectProperty.IsSeparating.isSeparator_coproduct
  proof: (isSeparator_sigma _).2 hS

中文:
定理 ObjectProperty.IsSeparating.isSeparator_coproduct
  证明: (isSeparator_sigma _).2 hS

Depends on / 依赖: isSeparator_sigma
-/
theorem ObjectProperty.IsSeparating.isSeparator_coproduct
    {β : Type w} {f : β -> C} [HasCoproduct f]
    (hS : ObjectProperty.IsSeparating (.ofObj f)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 hS

/--
theorem `isSeparator_sigma_of_isSeparator` / 定理 `isSeparator_sigma_of_isSeparator`

English:
theorem isSeparator_sigma_of_isSeparator
  statement: {β : Type w} (f : β -> C) [HasCoproduct f] (b : β)
  proof: (isSeparator_sigma _).2 ObjectProperty.IsSeparating.of_le hb by simp

中文:
定理 isSeparator_sigma_of_isSeparator
  结论: {β : 类型 w} (f : β -> C) [HasCoproduct f] (b : β)
  证明: (isSeparator_sigma _).2 ObjectProperty.IsSeparating.of_le hb by simp

Depends on / 依赖: IsSeparating, ObjectProperty, ObjectProperty.IsSeparating.of_le, isSeparator_sigma, of_le
-/
theorem isSeparator_sigma_of_isSeparator {β : Type w} (f : β -> C) [HasCoproduct f] (b : β)
    (hb : IsSeparator (f b)) : IsSeparator (∐ f) :=
(isSeparator_sigma _).2 ObjectProperty.IsSeparating.of_le hb by simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCoseparator_of_isLimit_fan` / 引理 `isCoseparator_of_isLimit_fan`

English:
lemma isCoseparator_of_isLimit_fan
  statement: {β : Type w} {f : β -> C}
  proof: by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

中文:
引理 isCoseparator_of_isLimit_fan
  结论: {β : 类型 w} {f : β -> C}
  证明: by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

Depends on / 依赖: Fan.mk, Pi.single, c.proj, classical, hc.lift, isCoseparator_def, single
-/
lemma isCoseparator_of_isLimit_fan {β : Type w} {f : β -> C}
    (hf : ObjectProperty.IsCoseparating (.ofObj f)) {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt := by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv => hf _ _ (fun _ h g => ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isCoseparator_iff_of_isLimit_fan` / 引理 `isCoseparator_iff_of_isLimit_fan`

English:
lemma isCoseparator_iff_of_isLimit_fan
  statement: {β : Type w} {f : β -> C}
  proof: by
  refine ⟨fun h X Y u v huv => ?_, fun h => isCoseparator_of_isLimit_fan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (g ≫ c.proj _)

中文:
引理 isCoseparator_iff_of_isLimit_fan
  结论: {β : 类型 w} {f : β -> C}
  证明: by
  refine ⟨fun h X Y u v huv => ?_, fun h => isCoseparator_of_isLimit_fan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (g ≫ c.proj _)

Depends on / 依赖: b.as, c.proj, h.def, hc.hom_ext, hom_ext, isCoseparator_of_isLimit_fan
-/
lemma isCoseparator_iff_of_isLimit_fan {β : Type w} {f : β -> C}
    {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt ↔ ObjectProperty.IsCoseparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isCoseparator_of_isLimit_fan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (g ≫ c.proj _)

/--
theorem `isCoseparator_pi` / 定理 `isCoseparator_pi`

English:
theorem isCoseparator_pi
  given: {β : Type w} (f : β -> C) [HasProduct f]
  proof: isCoseparator_iff_of_isLimit_fan (hc := limit.isLimit _)

中文:
定理 isCoseparator_pi
  条件: {β : 类型 w} (f : β -> C) [HasProduct f]
  证明: isCoseparator_iff_of_isLimit_fan (hc := limit.isLimit _)

Depends on / 依赖: isCoseparator_iff_of_isLimit_fan, isLimit, limit.isLimit
-/
theorem isCoseparator_pi {β : Type w} (f : β -> C) [HasProduct f] :
    IsCoseparator (∏ᶜ f) ↔ ObjectProperty.IsCoseparating (.ofObj f) :=
  isCoseparator_iff_of_isLimit_fan (hc := limit.isLimit _)

/--
theorem `isCoseparator_prod` / 定理 `isCoseparator_prod`

English:
theorem isCoseparator_prod
  given: (G H : C) [HasBinaryProduct G H]
  proof: by
  refine (isCoseparator_iff_of_isLimit_fan (prodIsProd G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

中文:
定理 isCoseparator_prod
  条件: (G H : C) [HasBinaryProduct G H]
  证明: by
  refine (isCoseparator_iff_of_isLimit_fan (prodIsProd G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

Depends on / 依赖: Iff.rfl, ObjectProperty, ObjectProperty.ofObj_iff, ObjectProperty.pair_iff, convert, exacts, isCoseparator_iff_of_isLimit_fan, ofObj_iff, pair_iff, prodIsProd
-/
theorem isCoseparator_prod (G H : C) [HasBinaryProduct G H] :
    IsCoseparator (G ⨯ H) ↔ ObjectProperty.IsCoseparating (.pair G H) := by
  refine (isCoseparator_iff_of_isLimit_fan (prodIsProd G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto

/--
theorem `isCoseparator_prod_of_isCoseparator_left` / 定理 `isCoseparator_prod_of_isCoseparator_left`

English:
theorem isCoseparator_prod_of_isCoseparator_left
  statement: (G H : C) [HasBinaryProduct G H]
  proof: (isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hG by simp

中文:
定理 isCoseparator_prod_of_isCoseparator_left
  结论: (G H : C) [HasBinaryProduct G H]
  证明: (isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hG by simp

Depends on / 依赖: IsCoseparating, ObjectProperty, ObjectProperty.IsCoseparating.of_le, isCoseparator_prod, of_le
-/
theorem isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H]
    (hG : IsCoseparator G) : IsCoseparator (G ⨯ H) :=
(isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hG by simp

/--
theorem `isCoseparator_prod_of_isCoseparator_right` / 定理 `isCoseparator_prod_of_isCoseparator_right`

English:
theorem isCoseparator_prod_of_isCoseparator_right
  statement: (G H : C) [HasBinaryProduct G H]
  proof: (isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hH by simp

中文:
定理 isCoseparator_prod_of_isCoseparator_right
  结论: (G H : C) [HasBinaryProduct G H]
  证明: (isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hH by simp

Depends on / 依赖: IsCoseparating, ObjectProperty, ObjectProperty.IsCoseparating.of_le, isCoseparator_prod, of_le
-/
theorem isCoseparator_prod_of_isCoseparator_right (G H : C) [HasBinaryProduct G H]
    (hH : IsCoseparator H) : IsCoseparator (G ⨯ H) :=
(isCoseparator_prod _ _).2 ObjectProperty.IsCoseparating.of_le hH by simp

/--
theorem `isCoseparator_pi_of_isCoseparator` / 定理 `isCoseparator_pi_of_isCoseparator`

English:
theorem isCoseparator_pi_of_isCoseparator
  statement: {β : Type w} (f : β -> C) [HasProduct f] (b : β)
  proof: (isCoseparator_pi _).2 ObjectProperty.IsCoseparating.of_le hb by simp

中文:
定理 isCoseparator_pi_of_isCoseparator
  结论: {β : 类型 w} (f : β -> C) [HasProduct f] (b : β)
  证明: (isCoseparator_pi _).2 ObjectProperty.IsCoseparating.of_le hb by simp

Depends on / 依赖: IsCoseparating, ObjectProperty, ObjectProperty.IsCoseparating.of_le, isCoseparator_pi, of_le
-/
theorem isCoseparator_pi_of_isCoseparator {β : Type w} (f : β -> C) [HasProduct f] (b : β)
    (hb : IsCoseparator (f b)) : IsCoseparator (∏ᶜ f) :=
(isCoseparator_pi _).2 ObjectProperty.IsCoseparating.of_le hb by simp

end ZeroMorphisms

/--
theorem `isDetector_iff_reflectsIsomorphisms_coyoneda_obj` / 定理 `isDetector_iff_reflectsIsomorphisms_coyoneda_obj`

English:
theorem isDetector_iff_reflectsIsomorphisms_coyoneda_obj
  given: (G : C)
  proof: by
  refine
    ⟨fun hG => ⟨fun f hf => hG.def _ fun h => ?_⟩, fun h =>
      (isDetector_def _).2 fun X Y f hf => ?_⟩
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
    exact hf h
  · suffices IsIso ((coyoneda.obj (op G)).map f) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

中文:
定理 isDetector_iff_reflectsIsomorphisms_coyoneda_obj
  条件: (G : C)
  证明: by
  refine
    ⟨fun hG => ⟨fun f hf => hG.def _ fun h => ?_⟩, fun h =>
      (isDetector_def _).2 fun X Y f hf => ?_⟩
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
    exact hf h
  · suffices IsIso ((coyoneda.obj (op G)).map f) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, bijective_iff_existsUnique, coyoneda, coyoneda.obj, hG.def, isDetector_def, isIso_iff_bijective, isIso_of_reflects_iso
-/
theorem isDetector_iff_reflectsIsomorphisms_coyoneda_obj (G : C) :
    IsDetector G ↔ (coyoneda.obj (op G)).ReflectsIsomorphisms := by
  refine
    ⟨fun hG => ⟨fun f hf => hG.def _ fun h => ?_⟩, fun h =>
      (isDetector_def _).2 fun X Y f hf => ?_⟩
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
    exact hf h
  · suffices IsIso ((coyoneda.obj (op G)).map f) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

/--
theorem `isCodetector_iff_reflectsIsomorphisms_yoneda_obj` / 定理 `isCodetector_iff_reflectsIsomorphisms_yoneda_obj`

English:
theorem isCodetector_iff_reflectsIsomorphisms_yoneda_obj
  given: (G : C)
  proof: by
  refine ⟨fun hG => ⟨fun f hf => ?_⟩, fun h => (isCodetector_def _).2 fun X Y f hf => ?_⟩
  · refine (isIso_unop_iff _).1 (hG.def _ ?_)
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
  · rw [← isIso_op_iff]
    suffices IsIso ((yoneda.obj G).map f.op) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

中文:
定理 isCodetector_iff_reflectsIsomorphisms_yoneda_obj
  条件: (G : C)
  证明: by
  refine ⟨fun hG => ⟨fun f hf => ?_⟩, fun h => (isCodetector_def _).2 fun X Y f hf => ?_⟩
  · refine (isIso_unop_iff _).1 (hG.def _ ?_)
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
  · rw [← isIso_op_iff]
    suffices IsIso ((yoneda.obj G).map f.op) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, bijective_iff_existsUnique, f.op, hG.def, isCodetector_def, isIso_iff_bijective, isIso_of_reflects_iso, isIso_op_iff, isIso_unop_iff, yoneda, yoneda.obj
-/
theorem isCodetector_iff_reflectsIsomorphisms_yoneda_obj (G : C) :
    IsCodetector G ↔ (yoneda.obj G).ReflectsIsomorphisms := by
  refine ⟨fun hG => ⟨fun f hf => ?_⟩, fun h => (isCodetector_def _).2 fun X Y f hf => ?_⟩
  · refine (isIso_unop_iff _).1 (hG.def _ ?_)
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
  · rw [← isIso_op_iff]
    suffices IsIso ((yoneda.obj G).map f.op) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]

/--
theorem `wellPowered_of_isDetector` / 定理 `wellPowered_of_isDetector`

English:
theorem wellPowered_of_isDetector
  given: [HasPullbacks C] (G : C) (hG : IsDetector G)
  proof: wellPowered_of_isDetecting hG

中文:
定理 wellPowered_of_isDetector
  条件: [有Pullbacks C] (G : C) (hG : IsDetector G)
  证明: wellPowered_of_isDetecting hG

Depends on / 依赖: wellPowered_of_isDetecting
-/
theorem wellPowered_of_isDetector [HasPullbacks C] (G : C) (hG : IsDetector G) :
    WellPowered.{v₁} C :=
  wellPowered_of_isDetecting hG

/--
theorem `wellPowered_of_isSeparator` / 定理 `wellPowered_of_isSeparator`

English:
theorem wellPowered_of_isSeparator
  given: [HasPullbacks C] [Balanced C] (G : C) (hG : IsSeparator G)
  proof: wellPowered_of_isDetecting hG.isDetector

中文:
定理 wellPowered_of_isSeparator
  条件: [有Pullbacks C] [Balanced C] (G : C) (hG : IsSeparator G)
  证明: wellPowered_of_isDetecting hG.isDetector

Depends on / 依赖: hG.isDetector, isDetector, wellPowered_of_isDetecting
-/
theorem wellPowered_of_isSeparator [HasPullbacks C] [Balanced C] (G : C) (hG : IsSeparator G) :
    WellPowered.{v₁} C := wellPowered_of_isDetecting hG.isDetector

section HasGenerator

section Definitions

variable (C)

/--
Definition of `HasSeparator` / `HasSeparator` 的定义

English:
class HasSeparator
  parameters: : Prop where
  axioms and operations (1):
    - hasSeparator : exists G : C, IsSeparator G

中文:
类 有Separator
  参数: : 命题 where
  公理与运算 (1 个):
    - hasSeparator : 存在 G : C, IsSeparator G
-/
class HasSeparator : Prop where
  hasSeparator : exists G : C, IsSeparator G

/--
Definition of `HasCoseparator` / `HasCoseparator` 的定义

English:
class HasCoseparator
  parameters: : Prop where
  axioms and operations (1):
    - hasCoseparator : exists G : C, IsCoseparator G

中文:
类 有余separator
  参数: : 命题 where
  公理与运算 (1 个):
    - hasCoseparator : 存在 G : C, IsCoseparator G
-/
class HasCoseparator : Prop where
  hasCoseparator : exists G : C, IsCoseparator G

/--
Definition of `HasDetector` / `HasDetector` 的定义

English:
class HasDetector
  parameters: : Prop where
  axioms and operations (1):
    - hasDetector : exists G : C, IsDetector G

中文:
类 有Detector
  参数: : 命题 where
  公理与运算 (1 个):
    - hasDetector : 存在 G : C, IsDetector G
-/
class HasDetector : Prop where
  hasDetector : exists G : C, IsDetector G

/--
Definition of `HasCodetector` / `HasCodetector` 的定义

English:
class HasCodetector
  parameters: : Prop where
  axioms and operations (1):
    - hasCodetector : exists G : C, IsCodetector G

中文:
类 有余detector
  参数: : 命题 where
  公理与运算 (1 个):
    - hasCodetector : 存在 G : C, IsCodetector G
-/
class HasCodetector : Prop where
  hasCodetector : exists G : C, IsCodetector G

end Definitions

section Choice

variable (C)

/--
Definition of `separator` / `separator` 的定义

English:
definition separator
  signature: [HasSeparator C]
  body: HasSeparator.hasSeparator.choose

中文:
定义 separator
  签名: [有Separator C]
  定义体: HasSeparator.hasSeparator.choose

Depends on / 依赖: HasSeparator, HasSeparator.hasSeparator.choose, SplitEpiCategory, hasSeparator, regularEpiCategoryOfSplitEpiCategory
-/
noncomputable def separator [HasSeparator C] : C := HasSeparator.hasSeparator.choose

/--
Definition of `coseparator` / `coseparator` 的定义

English:
definition coseparator
  signature: [HasCoseparator C]
  body: HasCoseparator.hasCoseparator.choose

中文:
定义 coseparator
  签名: [有余separator C]
  定义体: HasCoseparator.hasCoseparator.choose

Depends on / 依赖: HasCoseparator, HasCoseparator.hasCoseparator.choose, IsRegularEpiCategory, hasCoseparator, strongEpiCategory_of_regularEpiCategory
-/
noncomputable def coseparator [HasCoseparator C] : C := HasCoseparator.hasCoseparator.choose

/--
Definition of `detector` / `detector` 的定义

English:
definition detector
  signature: [HasDetector C]
  body: HasDetector.hasDetector.choose

中文:
定义 detector
  签名: [有Detector C]
  定义体: HasDetector.hasDetector.choose

Depends on / 依赖: HasDetector, HasDetector.hasDetector.choose, hasDetector
-/
noncomputable def detector [HasDetector C] : C := HasDetector.hasDetector.choose

/--
Definition of `codetector` / `codetector` 的定义

English:
definition codetector
  signature: [HasCodetector C]
  body: HasCodetector.hasCodetector.choose

中文:
定义 codetector
  签名: [有余detector C]
  定义体: HasCodetector.hasCodetector.choose

Depends on / 依赖: HasCodetector, HasCodetector.hasCodetector.choose, hasCodetector
-/
noncomputable def codetector [HasCodetector C] : C := HasCodetector.hasCodetector.choose

/--
theorem `isSeparator_separator` / 定理 `isSeparator_separator`

English:
theorem isSeparator_separator
  given: [HasSeparator C]
  statement: IsSeparator (separator C)
  proof: HasSeparator.hasSeparator.choose_spec

中文:
定理 isSeparator_separator
  条件: [有Separator C]
  结论: IsSeparator (separator C)
  证明: HasSeparator.hasSeparator.choose_spec

Depends on / 依赖: HasSeparator, HasSeparator.hasSeparator.choose_spec, choose_spec, hasSeparator
-/
theorem isSeparator_separator [HasSeparator C] : IsSeparator (separator C) :=
  HasSeparator.hasSeparator.choose_spec

/--
theorem `isDetector_separator` / 定理 `isDetector_separator`

English:
theorem isDetector_separator
  given: [Balanced C] [HasSeparator C]
  statement: IsDetector (separator C)
  proof: .isDetector isSeparator_separator C

中文:
定理 isDetector_separator
  条件: [Balanced C] [有Separator C]
  结论: IsDetector (separator C)
  证明: .isDetector isSeparator_separator C

Depends on / 依赖: isDetector, isSeparator_separator
-/
theorem isDetector_separator [Balanced C] [HasSeparator C] : IsDetector (separator C) :=
.isDetector isSeparator_separator C

/--
theorem `isCoseparator_coseparator` / 定理 `isCoseparator_coseparator`

English:
theorem isCoseparator_coseparator
  given: [HasCoseparator C]
  statement: IsCoseparator (coseparator C)
  proof: HasCoseparator.hasCoseparator.choose_spec

中文:
定理 isCoseparator_coseparator
  条件: [有余separator C]
  结论: IsCoseparator (coseparator C)
  证明: HasCoseparator.hasCoseparator.choose_spec

Depends on / 依赖: HasCoseparator, HasCoseparator.hasCoseparator.choose_spec, choose_spec, hasCoseparator
-/
theorem isCoseparator_coseparator [HasCoseparator C] : IsCoseparator (coseparator C) :=
  HasCoseparator.hasCoseparator.choose_spec

/--
theorem `isCodetector_coseparator` / 定理 `isCodetector_coseparator`

English:
theorem isCodetector_coseparator
  given: [Balanced C] [HasCoseparator C]
  statement: IsCodetector (coseparator C)
  proof: .isCodetector isCoseparator_coseparator C

中文:
定理 isCodetector_coseparator
  条件: [Balanced C] [有余separator C]
  结论: IsCodetector (coseparator C)
  证明: .isCodetector isCoseparator_coseparator C

Depends on / 依赖: isCodetector, isCoseparator_coseparator
-/
theorem isCodetector_coseparator [Balanced C] [HasCoseparator C] : IsCodetector (coseparator C) :=
.isCodetector isCoseparator_coseparator C

/--
theorem `isDetector_detector` / 定理 `isDetector_detector`

English:
theorem isDetector_detector
  given: [HasDetector C]
  statement: IsDetector (detector C)
  proof: HasDetector.hasDetector.choose_spec

中文:
定理 isDetector_detector
  条件: [有Detector C]
  结论: IsDetector (detector C)
  证明: HasDetector.hasDetector.choose_spec

Depends on / 依赖: HasDetector, HasDetector.hasDetector.choose_spec, choose_spec, hasDetector
-/
theorem isDetector_detector [HasDetector C] : IsDetector (detector C) :=
  HasDetector.hasDetector.choose_spec

/--
theorem `isSeparator_detector` / 定理 `isSeparator_detector`

English:
theorem isSeparator_detector
  given: [HasEqualizers C] [HasDetector C]
  statement: IsSeparator (detector C)
  proof: .isSeparator isDetector_detector C

中文:
定理 isSeparator_detector
  条件: [HasEqualizers C] [有Detector C]
  结论: IsSeparator (detector C)
  证明: .isSeparator isDetector_detector C

Depends on / 依赖: isDetector_detector, isSeparator
-/
theorem isSeparator_detector [HasEqualizers C] [HasDetector C] : IsSeparator (detector C) :=
.isSeparator isDetector_detector C

/--
theorem `isCodetector_codetector` / 定理 `isCodetector_codetector`

English:
theorem isCodetector_codetector
  given: [HasCodetector C]
  statement: IsCodetector (codetector C)
  proof: HasCodetector.hasCodetector.choose_spec

中文:
定理 isCodetector_codetector
  条件: [有余detector C]
  结论: IsCodetector (codetector C)
  证明: HasCodetector.hasCodetector.choose_spec

Depends on / 依赖: HasCodetector, HasCodetector.hasCodetector.choose_spec, choose_spec, hasCodetector
-/
theorem isCodetector_codetector [HasCodetector C] : IsCodetector (codetector C) :=
  HasCodetector.hasCodetector.choose_spec

/--
theorem `isCoseparator_codetector` / 定理 `isCoseparator_codetector`

English:
theorem isCoseparator_codetector
  given: [HasCoequalizers C] [HasCodetector C]
  proof: isCodetector_codetector C

中文:
定理 isCoseparator_codetector
  条件: [HasCoequalizers C] [有余detector C]
  证明: isCodetector_codetector C

Depends on / 依赖: isCodetector_codetector
-/
theorem isCoseparator_codetector [HasCoequalizers C] [HasCodetector C] :
.isCoseparator IsCoseparator (codetector C) := isCodetector_codetector C

end Choice

section Instances

/--
theorem `HasSeparator.hasDetector` / 定理 `HasSeparator.hasDetector`

English:
theorem HasSeparator.hasDetector
  given: [Balanced C] [HasSeparator C]
  statement: HasDetector C
  proof: ⟨_, isDetector_separator C⟩

中文:
定理 有Separator.hasDetector
  条件: [Balanced C] [有Separator C]
  结论: 有Detector C
  证明: ⟨_, isDetector_separator C⟩

Depends on / 依赖: isDetector_separator
-/
theorem HasSeparator.hasDetector [Balanced C] [HasSeparator C] : HasDetector C :=
  ⟨_, isDetector_separator C⟩

/--
theorem `HasDetector.hasSeparator` / 定理 `HasDetector.hasSeparator`

English:
theorem HasDetector.hasSeparator
  given: [HasEqualizers C] [HasDetector C]
  statement: HasSeparator C
  proof: ⟨_, isSeparator_detector C⟩

中文:
定理 有Detector.hasSeparator
  条件: [HasEqualizers C] [有Detector C]
  结论: 有Separator C
  证明: ⟨_, isSeparator_detector C⟩

Depends on / 依赖: isSeparator_detector
-/
theorem HasDetector.hasSeparator [HasEqualizers C] [HasDetector C] : HasSeparator C :=
  ⟨_, isSeparator_detector C⟩

/--
theorem `HasCoseparator.hasCodetector` / 定理 `HasCoseparator.hasCodetector`

English:
theorem HasCoseparator.hasCodetector
  given: [Balanced C] [HasCoseparator C]
  statement: HasCodetector C
  proof: ⟨_, isCodetector_coseparator C⟩

中文:
定理 有余separator.hasCodetector
  条件: [Balanced C] [有余separator C]
  结论: 有余detector C
  证明: ⟨_, isCodetector_coseparator C⟩

Depends on / 依赖: isCodetector_coseparator
-/
theorem HasCoseparator.hasCodetector [Balanced C] [HasCoseparator C] : HasCodetector C :=
  ⟨_, isCodetector_coseparator C⟩

/--
theorem `HasCodetector.hasCoseparator` / 定理 `HasCodetector.hasCoseparator`

English:
theorem HasCodetector.hasCoseparator
  given: [HasCoequalizers C] [HasCodetector C]
  statement: HasCoseparator C
  proof: ⟨_, isCoseparator_codetector C⟩

中文:
定理 有余detector.hasCoseparator
  条件: [HasCoequalizers C] [有余detector C]
  结论: 有余separator C
  证明: ⟨_, isCoseparator_codetector C⟩

Depends on / 依赖: isCoseparator_codetector
-/
theorem HasCodetector.hasCoseparator [HasCoequalizers C] [HasCodetector C] : HasCoseparator C :=
  ⟨_, isCoseparator_codetector C⟩

/--
Instance `HasDetector.wellPowered` / 实例 `HasDetector.wellPowered`

English:
instance HasDetector.wellPowered
  signature: [HasPullbacks C] [HasDetector C]
  body: wellPowered_of_isDetector _ isDetector_detector C

中文:
实例 有Detector.wellPowered
  签名: [有Pullbacks C] [有Detector C]
  定义体: wellPowered_of_isDetector _ isDetector_detector C

Depends on / 依赖: isDetector_detector, wellPowered_of_isDetector
-/
instance HasDetector.wellPowered [HasPullbacks C] [HasDetector C] : WellPowered.{v₁} C :=
wellPowered_of_isDetector _ isDetector_detector C

/--
Instance `HasSeparator.wellPowered` / 实例 `HasSeparator.wellPowered`

English:
instance HasSeparator.wellPowered
  signature: [HasPullbacks C] [Balanced C] [HasSeparator C]
  body: HasSeparator.hasDetector.wellPowered

中文:
实例 有Separator.wellPowered
  签名: [有Pullbacks C] [Balanced C] [有Separator C]
  定义体: HasSeparator.hasDetector.wellPowered

Depends on / 依赖: HasSeparator, HasSeparator.hasDetector.wellPowered, J.map, hasDetector, wellPowered
-/
instance HasSeparator.wellPowered [HasPullbacks C] [Balanced C] [HasSeparator C] :
    WellPowered.{v₁} C := HasSeparator.hasDetector.wellPowered

end Instances

section Equivalence

/--
theorem `HasSeparator.of_equivalence` / 定理 `HasSeparator.of_equivalence`

English:
theorem HasSeparator.of_equivalence
  given: [HasSeparator C] (α : C ≌ D)
  statement: HasSeparator D
  proof: .of_equivalence α⟩ ⟨α.functor.obj (separator C), isSeparator_separator C

中文:
定理 有Separator.of_equivalence
  条件: [有Separator C] (α : C ≌ D)
  结论: 有Separator D
  证明: .of_equivalence α⟩ ⟨α.functor.obj (separator C), isSeparator_separator C

Depends on / 依赖: functor, functor.obj, isSeparator_separator, of_equivalence, separator
-/
theorem HasSeparator.of_equivalence [HasSeparator C] (α : C ≌ D) : HasSeparator D :=
.of_equivalence α⟩ ⟨α.functor.obj (separator C), isSeparator_separator C

/--
theorem `HasCoseparator.of_equivalence` / 定理 `HasCoseparator.of_equivalence`

English:
theorem HasCoseparator.of_equivalence
  given: [HasCoseparator C] (α : C ≌ D)
  statement: HasCoseparator D
  proof: .of_equivalence α⟩ ⟨α.functor.obj (coseparator C), isCoseparator_coseparator C

中文:
定理 有余separator.of_equivalence
  条件: [有余separator C] (α : C ≌ D)
  结论: 有余separator D
  证明: .of_equivalence α⟩ ⟨α.functor.obj (coseparator C), isCoseparator_coseparator C

Depends on / 依赖: coseparator, functor, functor.obj, isCoseparator_coseparator, of_equivalence
-/
theorem HasCoseparator.of_equivalence [HasCoseparator C] (α : C ≌ D) : HasCoseparator D :=
.of_equivalence α⟩ ⟨α.functor.obj (coseparator C), isCoseparator_coseparator C

end Equivalence

section Dual

@[simp]
/--
theorem `hasSeparator_op_iff` / 定理 `hasSeparator_op_iff`

English:
theorem hasSeparator_op_iff
  statement: HasSeparator Cᵒᵖ ↔ HasCoseparator C
  proof: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCoseparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isSeparator_op_iff G).mpr hG⟩⟩

@[simp]

中文:
定理 hasSeparator_op_iff
  结论: 有Separator Cᵒᵖ ↔ 有余separator C
  证明: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCoseparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isSeparator_op_iff G).mpr hG⟩⟩

@[simp]

Depends on / 依赖: isCoseparator_unop_iff, isSeparator_op_iff
-/
theorem hasSeparator_op_iff : HasSeparator Cᵒᵖ ↔ HasCoseparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCoseparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isSeparator_op_iff G).mpr hG⟩⟩

@[simp]
/--
theorem `hasCoseparator_op_iff` / 定理 `hasCoseparator_op_iff`

English:
theorem hasCoseparator_op_iff
  statement: HasCoseparator Cᵒᵖ ↔ HasSeparator C
  proof: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isSeparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCoseparator_op_iff G).mpr hG⟩⟩

@[simp]

中文:
定理 hasCoseparator_op_iff
  结论: 有余separator Cᵒᵖ ↔ 有Separator C
  证明: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isSeparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCoseparator_op_iff G).mpr hG⟩⟩

@[simp]

Depends on / 依赖: isCoseparator_op_iff, isSeparator_unop_iff
-/
theorem hasCoseparator_op_iff : HasCoseparator Cᵒᵖ ↔ HasSeparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isSeparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCoseparator_op_iff G).mpr hG⟩⟩

@[simp]
/--
theorem `hasDetector_op_iff` / 定理 `hasDetector_op_iff`

English:
theorem hasDetector_op_iff
  statement: HasDetector Cᵒᵖ ↔ HasCodetector C
  proof: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCodetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isDetector_op_iff G).mpr hG⟩⟩

@[simp]

中文:
定理 hasDetector_op_iff
  结论: 有Detector Cᵒᵖ ↔ 有余detector C
  证明: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCodetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isDetector_op_iff G).mpr hG⟩⟩

@[simp]

Depends on / 依赖: isCodetector_unop_iff, isDetector_op_iff
-/
theorem hasDetector_op_iff : HasDetector Cᵒᵖ ↔ HasCodetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCodetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isDetector_op_iff G).mpr hG⟩⟩

@[simp]
/--
theorem `hasCodetector_op_iff` / 定理 `hasCodetector_op_iff`

English:
theorem hasCodetector_op_iff
  statement: HasCodetector Cᵒᵖ ↔ HasDetector C
  proof: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isDetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCodetector_op_iff G).mpr hG⟩⟩

中文:
定理 hasCodetector_op_iff
  结论: 有余detector Cᵒᵖ ↔ 有Detector C
  证明: ⟨fun ⟨G, hG⟩ => ⟨unop G, (isDetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCodetector_op_iff G).mpr hG⟩⟩

Depends on / 依赖: isCodetector_op_iff, isDetector_unop_iff
-/
theorem hasCodetector_op_iff : HasCodetector Cᵒᵖ ↔ HasDetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isDetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCodetector_op_iff G).mpr hG⟩⟩

/--
Instance `HasSeparator.hasCoseparator_op` / 实例 `HasSeparator.hasCoseparator_op`

English:
instance HasSeparator.hasCoseparator_op
  signature: [HasSeparator C]
  body: by simp [*]

中文:
实例 有Separator.hasCoseparator_op
  签名: [有Separator C]
  定义体: by simp [*]

Depends on / 依赖: leftSection, rightSection
-/
instance HasSeparator.hasCoseparator_op [HasSeparator C] : HasCoseparator Cᵒᵖ := by simp [*]
/--
theorem `HasSeparator.hasCoseparator_of_hasSeparator_op` / 定理 `HasSeparator.hasCoseparator_of_hasSeparator_op`

English:
theorem HasSeparator.hasCoseparator_of_hasSeparator_op
  given: [h : HasSeparator Cᵒᵖ]
  proof: by simp_all

中文:
定理 有Separator.hasCoseparator_of_hasSeparator_op
  条件: [h : 有Separator Cᵒᵖ]
  证明: by simp_all
-/
theorem HasSeparator.hasCoseparator_of_hasSeparator_op [h : HasSeparator Cᵒᵖ] :
    HasCoseparator C := by simp_all

/--
Instance `HasCoseparator.hasSeparator_op` / 实例 `HasCoseparator.hasSeparator_op`

English:
instance HasCoseparator.hasSeparator_op
  signature: [HasCoseparator C]
  body: by simp [*]

中文:
实例 有余separator.hasSeparator_op
  签名: [有余separator C]
  定义体: by simp [*]
-/
instance HasCoseparator.hasSeparator_op [HasCoseparator C] : HasSeparator Cᵒᵖ := by simp [*]
/--
theorem `HasCoseparator.hasSeparator_of_hasCoseparator_op` / 定理 `HasCoseparator.hasSeparator_of_hasCoseparator_op`

English:
theorem HasCoseparator.hasSeparator_of_hasCoseparator_op
  given: [HasCoseparator Cᵒᵖ]
  proof: by simp_all

中文:
定理 有余separator.hasSeparator_of_hasCoseparator_op
  条件: [有余separator Cᵒᵖ]
  证明: by simp_all
-/
theorem HasCoseparator.hasSeparator_of_hasCoseparator_op [HasCoseparator Cᵒᵖ] :
    HasSeparator C := by simp_all

/--
Instance `HasDetector.hasCodetector_op` / 实例 `HasDetector.hasCodetector_op`

English:
instance HasDetector.hasCodetector_op
  signature: [HasDetector C]
  body: by simp [*]

中文:
实例 有Detector.hasCodetector_op
  签名: [有Detector C]
  定义体: by simp [*]
-/
instance HasDetector.hasCodetector_op [HasDetector C] : HasCodetector Cᵒᵖ := by simp [*]
/--
theorem `HasDetector.hasCodetector_of_hasDetector_op` / 定理 `HasDetector.hasCodetector_of_hasDetector_op`

English:
theorem HasDetector.hasCodetector_of_hasDetector_op
  given: [HasDetector Cᵒᵖ]
  proof: by simp_all

中文:
定理 有Detector.hasCodetector_of_hasDetector_op
  条件: [有Detector Cᵒᵖ]
  证明: by simp_all
-/
theorem HasDetector.hasCodetector_of_hasDetector_op [HasDetector Cᵒᵖ] :
    HasCodetector C := by simp_all

/--
Instance `HasCodetector.hasDetector_op` / 实例 `HasCodetector.hasDetector_op`

English:
instance HasCodetector.hasDetector_op
  signature: [HasCodetector C]
  body: by simp [*]

中文:
实例 有余detector.hasDetector_op
  签名: [有余detector C]
  定义体: by simp [*]
-/
instance HasCodetector.hasDetector_op [HasCodetector C] : HasDetector Cᵒᵖ := by simp [*]
/--
theorem `HasCodetector.hasDetector_of_hasCodetector_op` / 定理 `HasCodetector.hasDetector_of_hasCodetector_op`

English:
theorem HasCodetector.hasDetector_of_hasCodetector_op
  given: [HasCodetector Cᵒᵖ]
  proof: by simp_all

中文:
定理 有余detector.hasDetector_of_hasCodetector_op
  条件: [有余detector Cᵒᵖ]
  证明: by simp_all
-/
theorem HasCodetector.hasDetector_of_hasCodetector_op [HasCodetector Cᵒᵖ] :
    HasDetector C := by simp_all

end Dual

end HasGenerator

end CategoryTheory
