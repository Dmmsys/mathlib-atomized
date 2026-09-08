/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.Condensed.Light.TopCatAdjunction
public import Mathlib.Topology.Category.LightProfinite.Cartesian

/-!
# Functors from categories of topological spaces to light condensed sets

This file defines the embedding of the test objects (light profinite sets) into light condensed
sets.

## Main definitions

* `lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u}`
  is the yoneda sheaf functor.

-/

@[expose] public section

universe u v

open CategoryTheory Limits Functor

/-- The functor from `LightProfinite.{u}` to `LightCondSet.{u}` given by the Yoneda sheaf. -/
/-
**lightProfiniteToLightCondSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `LightProfinite.{u}` to `LightCondSet.{u}` given by the Yoneda 
sheaf.
-/
def lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u} :=
  (coherentTopology LightProfinite).yoneda

/-- Dot notation for the value of `lightProfiniteToLightCondSet`. -/
/-
**LightProfinite.toCondensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u}
参数：S : LightProfinite.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dot notation for the value of `lightProfiniteToLightCondSet`.
-/
abbrev LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u} :=
  lightProfiniteToLightCondSet.obj S

/-- `lightProfiniteToLightCondSet` is fully faithful. -/
/-
**lightProfiniteToLightCondSetFullyFaithful** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：lightProfiniteToLightCondSetFullyFaithful : lightProfiniteToLightCondSet.F
ullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lightProfiniteToLightCondSet` is fully faithful.
-/
abbrev lightProfiniteToLightCondSetFullyFaithful :
    lightProfiniteToLightCondSet.FullyFaithful :=
  (coherentTopology LightProfinite).yonedaFullyFaithful
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : lightProfiniteToLightCondSet.Full :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : lightProfiniteToLightCondSet.Faithful :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

set_option backward.isDefEq.respectTransparency.types false in
/--
The functor from `LightProfinite` to `LightCondSet` factors through `TopCat`.
-/
@[simps!]
/-
**lightProfiniteToLightCondSetIsoTopCatToLightCondSet** 是 Mathlib 中的一个定义，位于命名空间 
``。
形式化陈述：lightProfiniteToLightCondSetIsoTopCatToLightCondSet : lightProfiniteToLigh
tCondSet.{u} ≅ LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `LightProfinite` to `LightCondSet` factors through `TopCat`.
-/
noncomputable def lightProfiniteToLightCondSetIsoTopCatToLightCondSet :
    lightProfiniteToLightCondSet.{u} ≅ LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} :=
  dsimp% NatIso.ofComponents fun X ↦ FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _) <|
    NatIso.ofComponents fun S ↦ {
      hom := ↾fun f ↦ { toFun := f.hom }
      inv := ↾fun f ↦ InducedCategory.homMk (TopCat.ofHom f) }

/--
The functor from `LightProfinite` to `LightCondSet` preserves countable limits.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `LightProfinite` to `LightCondSet` preserves countable limits.
-/
instance {J : Type} [SmallCategory J] [CountableCategory J] : PreservesLimitsOfShape J
    lightProfiniteToLightCondSet.{u} :=
  haveI : Functor.IsRightAdjoint topCatToLightCondSet.{u} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimitsOfShape J LightProfinite.toTopCat.{u} :=
    inferInstanceAs (PreservesLimitsOfShape J (lightToProfinite ⋙ Profinite.toTopCat))
  preservesLimitsOfShape_of_natIso lightProfiniteToLightCondSetIsoTopCatToLightCondSet.symm

/--
The functor from `LightProfinite` to `LightCondSet` preserves finite limits.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `LightProfinite` to `LightCondSet` preserves finite limits.
-/
instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits _ := inferInstance

/--
The functor from `LightProfinite` to `LightCondSet` is monoidal with respect to the cartesian
monoidal structure.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `LightProfinite` to `LightCondSet` is monoidal with respect to 
the cartesian
monoidal structure.
-/
noncomputable instance : lightProfiniteToLightCondSet.{u}.Monoidal :=
  (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance |>.some
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u} :=
  inferInstanceAs <| PreservesFiniteCoproducts (coherentTopology _).yoneda
