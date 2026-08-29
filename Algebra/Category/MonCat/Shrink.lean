/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.Algebra.Group.Shrink

/-!
# Shrinking a functor to `MonCat`

For a functor `C ⥤ MonCat.{w'}` with `w`-small image, we shrink to a functor `C ⥤ MonCat.{w}`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

instance (F : C ⥤ MonCat.{w'}) [forall X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
fun X => inferInstanceAs Small.{w} (F.obj X)

/-- A functor `F : C ⥤ MonCat.{w'}` factors through `MonCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
/--
Definition of `MonCat.shrinkFunctor` / `MonCat.shrinkFunctor` 的定义

English:
definition MonCat.shrinkFunctor
  signature: (F : C ⥤ MonCat.{w'}) [forall X, Small.{w} (F.obj X)]
  body: MonCat.of (Shrink.{w} (F.obj X))
map {X Y} f := MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

中文:
定义 幺半群范畴.shrinkFunctor
  签名: (F : C ⥤ 幺半群范畴.{w'}) [对任意 X, Small.{w} (F.obj X)]
  定义体: MonCat.of (Shrink.{w} (F.obj X))
map {X Y} f := MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

Depends on / 依赖: F.obj, MonCat, MonCat.of, Shrink
-/
noncomputable def MonCat.shrinkFunctor (F : C ⥤ MonCat.{w'}) [forall X, Small.{w} (F.obj X)] :
    C ⥤ MonCat.{w} where
  obj X := MonCat.of (Shrink.{w} (F.obj X))
map {X Y} f := MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
/--
Definition of `MonCat.shrinkFunctorMap` / `MonCat.shrinkFunctorMap` 的定义

English:
definition MonCat.shrinkFunctorMap
  signature: {F G : C ⥤ MonCat.{w'}} (τ : F ⟶ G)
  body: MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

中文:
定义 幺半群范畴.shrinkFunctorMap
  签名: {F G : C ⥤ 幺半群范畴.{w'}} (τ : F ⟶ G)
  定义体: MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)

Depends on / 依赖: MonCat, MonCat.ofHom
-/
noncomputable def MonCat.shrinkFunctorMap {F G : C ⥤ MonCat.{w'}} (τ : F ⟶ G)
    [forall X, Small.{w} (F.obj X)] [forall X, Small.{w} (G.obj X)] :
    MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G where
app X := MonCat.ofHom
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)
