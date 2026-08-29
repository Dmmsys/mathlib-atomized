/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.Algebra.Group.Shrink

/-!
# Shrinking a functor to `GrpCat`

For a functor `C ⥤ GrpCat.{w'}` with `w`-small image, we shrink to a functor `C ⥤ GrpCat.{w}`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

instance (F : C ⥤ GrpCat.{w'}) [forall X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
fun X => inferInstanceAs Small.{w} (F.obj X)

/-- A functor `F : C ⥤ GrpCat.{w'}` factors through `GrpCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
/--
Definition of `GrpCat.shrinkFunctor` / `GrpCat.shrinkFunctor` 的定义

English:
definition GrpCat.shrinkFunctor
  signature: (F : C ⥤ GrpCat.{w'}) [forall X, Small.{w} (F.obj X)]
  body: GrpCat.of (Shrink.{w} (F.obj X))
map {X Y} f := GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

中文:
定义 GrpCat.shrinkFunctor
  签名: (F : C ⥤ GrpCat.{w'}) [对任意 X, Small.{w} (F.obj X)]
  定义体: GrpCat.of (Shrink.{w} (F.obj X))
map {X Y} f := GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

Depends on / 依赖: F.obj, GrpCat, GrpCat.of, Shrink
-/
noncomputable def GrpCat.shrinkFunctor (F : C ⥤ GrpCat.{w'}) [forall X, Small.{w} (F.obj X)] :
    C ⥤ GrpCat.{w} where
  obj X := GrpCat.of (Shrink.{w} (F.obj X))
map {X Y} f := GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
/--
Definition of `GrpCat.shrinkFunctorMap` / `GrpCat.shrinkFunctorMap` 的定义

English:
definition GrpCat.shrinkFunctorMap
  signature: {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
  body: GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

中文:
定义 GrpCat.shrinkFunctorMap
  签名: {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
  定义体: GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

Depends on / 依赖: GrpCat, GrpCat.ofHom
-/
noncomputable def GrpCat.shrinkFunctorMap {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
    [forall X, Small.{w} (F.obj X)] [forall X, Small.{w} (G.obj X)] :
    GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G where
app X := GrpCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)
