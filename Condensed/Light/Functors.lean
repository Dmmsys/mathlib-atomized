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

/--
Definition of `lightProfiniteToLightCondSet` / `lightProfiniteToLightCondSet` 的定义

English:
definition lightProfiniteToLightCondSet
  signature: : LightProfinite.{u} ⥤ LightCondSet.{u}
  body: (coherentTopology LightProfinite).yoneda

中文:
定义 lightProfiniteToLightCondSet
  签名: : LightProfinite.{u} ⥤ LightCondSet.{u}
  定义体: (coherentTopology LightProfinite).yoneda

Depends on / 依赖: LightProfinite, coherentTopology, yoneda
-/
def lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u} :=
  (coherentTopology LightProfinite).yoneda

/--
Definition of `LightProfinite.toCondensed` / `LightProfinite.toCondensed` 的定义

English:
abbreviation LightProfinite.toCondensed
  signature: (S : LightProfinite.{u})
  body: lightProfiniteToLightCondSet.obj S

中文:
缩写 LightProfinite.toCondensed
  签名: (S : LightProfinite.{u})
  定义体: lightProfiniteToLightCondSet.obj S

Depends on / 依赖: lightProfiniteToLightCondSet, lightProfiniteToLightCondSet.obj
-/
abbrev LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u} :=
  lightProfiniteToLightCondSet.obj S

/--
Definition of `lightProfiniteToLightCondSetFullyFaithful` / `lightProfiniteToLightCondSetFullyFaithful` 的定义

English:
abbreviation lightProfiniteToLightCondSetFullyFaithful
  signature: :
  body: (coherentTopology LightProfinite).yonedaFullyFaithful

中文:
缩写 lightProfiniteToLightCondSetFullyFaithful
  签名: :
  定义体: (coherentTopology LightProfinite).yonedaFullyFaithful

Depends on / 依赖: LightProfinite, coherentTopology, yonedaFullyFaithful
-/
abbrev lightProfiniteToLightCondSetFullyFaithful :
    lightProfiniteToLightCondSet.FullyFaithful :=
  (coherentTopology LightProfinite).yonedaFullyFaithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightProfiniteToLightCondSet.Full
  body: inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full

中文:
实例 :
  签名: lightProfiniteToLightCondSet.满
  定义体: inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full

Depends on / 依赖: LightProfinite, coherentTopology, yoneda
-/
instance : lightProfiniteToLightCondSet.Full :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightProfiniteToLightCondSet.Faithful
  body: inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

中文:
实例 :
  签名: lightProfiniteToLightCondSet.忠实
  定义体: inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

Depends on / 依赖: Faithful, LightProfinite, coherentTopology, yoneda
-/
instance : lightProfiniteToLightCondSet.Faithful :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

set_option backward.isDefEq.respectTransparency.types false in
/--
The functor from `LightProfinite` to `LightCondSet` factors through `TopCat`.
-/
@[simps!]
/--
Definition of `lightProfiniteToLightCondSetIsoTopCatToLightCondSet` / `lightProfiniteToLightCondSetIsoTopCatToLightCondSet` 的定义

English:
definition lightProfiniteToLightCondSetIsoTopCatToLightCondSet
  signature: :
  body: dsimp% NatIso.ofComponents fun X => FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _)
    NatIso.ofComponents fun S => {
      hom := ↾fun f => { toFun := f.hom }
      inv := ↾fun f => InducedCategory.homMk (TopCat.ofHom f) }

中文:
定义 lightProfiniteToLightCondSetIsoTopCatToLightCondSet
  签名: :
  定义体: dsimp% NatIso.ofComponents fun X => FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _)
    NatIso.ofComponents fun S => {
      hom := ↾fun f => { toFun := f.hom }
      inv := ↾fun f => InducedCategory.homMk (TopCat.ofHom f) }

Depends on / 依赖: FullyFaithful, FullyFaithful.preimageIso, InducedCategory, InducedCategory.homMk, NatIso, NatIso.ofComponents, TopCat, TopCat.ofHom, f.hom, fullyFaithfulSheafToPresheaf, ofComponents, preimageIso
-/
noncomputable def lightProfiniteToLightCondSetIsoTopCatToLightCondSet :
    lightProfiniteToLightCondSet.{u} ≅ LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} :=
dsimp% NatIso.ofComponents fun X => FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _)
    NatIso.ofComponents fun S => {
      hom := ↾fun f => { toFun := f.hom }
      inv := ↾fun f => InducedCategory.homMk (TopCat.ofHom f) }

/--
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
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits lightProfiniteToLightCondSet.{u}
  body: inferInstance

中文:
实例 :
  签名: 保持FiniteLimits lightProfiniteToLightCondSet.{u}
  定义体: inferInstance
-/
instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightProfiniteToLightCondSet.{u}.Monoidal
  body: .some (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance

中文:
实例 :
  签名: lightProfiniteToLightCondSet.{u}.幺半群
  定义体: .some (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance

Depends on / 依赖: Functor, Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts, Monoidal, nonempty_monoidal_iff_preservesFiniteProducts
-/
noncomputable instance : lightProfiniteToLightCondSet.{u}.Monoidal :=
.some (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u}
  body: inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).yoneda

中文:
实例 :
  签名: 保持FiniteCoproducts lightProfiniteToLightCondSet.{u}
  定义体: inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).yoneda

Depends on / 依赖: PreservesFiniteCoproducts, coherentTopology, yoneda
-/
instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u} :=
inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).yoneda
