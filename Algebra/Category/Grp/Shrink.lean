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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
  fun X ↦ inferInstanceAs <| Small.{w} (F.obj X)

/-- A functor `F : C ⥤ GrpCat.{w'}` factors through `GrpCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
/-
**GrpCat.shrinkFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GrpCat.shrinkFunctor (F : C ⥤ GrpCat.{w'}) [forall X, Small.{w} (F.obj X)]
 : C ⥤ GrpCat.{w} where obj X
参数：F : C ⥤ GrpCat.{w'}；F.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ GrpCat.{w'}` factors through `GrpCat.{w}` if all the
monoids are `w`-small.
-/
noncomputable def GrpCat.shrinkFunctor (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ GrpCat.{w} where
  obj X := GrpCat.of (Shrink.{w} (F.obj X))
  map {X Y} f := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
/-
**GrpCat.shrinkFunctorMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GrpCat.shrinkFunctorMap {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G) [forall X, Sma
ll.{w} (F.obj X)] [forall X, Small.{w} (G.obj X)] : GrpCat.shrinkFunctor.{w} F ⟶
 GrpCat.shrinkFunctor.{w} G where app X
参数：τ : F ⟶ G；F.obj X；G.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w
} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to mo
noids.
-/
noncomputable def GrpCat.shrinkFunctorMap {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
    [∀ X, Small.{w} (F.obj X)] [∀ X, Small.{w} (G.obj X)] :
    GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G where
  app X := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)
