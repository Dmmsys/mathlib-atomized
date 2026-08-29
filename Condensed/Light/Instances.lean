/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# `HasSheafify` instances

In this file, we obtain a `HasSheafify (coherentTopology LightProfinite.{u}) (Type u)`
instance (and similarly for other concrete categories). These instances
are not obtained automatically because `LightProfinite.{u}` is a large category,
but as it is essentially small, the instances can be obtained using the results
in the file `Mathlib/CategoryTheory/Sites/Equivalence.lean`.

-/

public section

universe u u' v

open CategoryTheory Limits

namespace LightProfinite

variable (A : Type u') [Category.{u} A] [HasLimits A] [HasColimits A]
  {FA : A -> A -> Type v} {CA : A -> Type u}
  [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [PreservesFilteredColimits (forget A)]
  [PreservesLimits (forget A)] [(forget A).ReflectsIsomorphisms]

/--
Instance `hasSheafify` / 实例 `hasSheafify`

English:
instance hasSheafify
  signature: :
  body: hasSheafifyEssentiallySmallSite _ _

中文:
实例 hasSheafify
  签名: :
  定义体: hasSheafifyEssentiallySmallSite _ _

Depends on / 依赖: hasSheafifyEssentiallySmallSite
-/
instance hasSheafify :
    HasSheafify (coherentTopology LightProfinite.{u}) A :=
  hasSheafifyEssentiallySmallSite _ _

/--
Instance `hasSheafify_type` / 实例 `hasSheafify_type`

English:
instance hasSheafify_type
  signature: :
  body: hasSheafifyEssentiallySmallSite _ _

中文:
实例 hasSheafify_type
  签名: :
  定义体: hasSheafifyEssentiallySmallSite _ _

Depends on / 依赖: hasSheafifyEssentiallySmallSite
-/
instance hasSheafify_type :
    HasSheafify (coherentTopology LightProfinite.{u}) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (coherentTopology LightProfinite.{u}).WEqualsLocallyBijective A
  body: GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

中文:
实例 :
  签名: (coherentTopology LightProfinite.{u}).WEqualsLocallyBijective A
  定义体: GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall, WEqualsLocallyBijective, ofEssentiallySmall
-/
instance : (coherentTopology LightProfinite.{u}).WEqualsLocallyBijective A :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end LightProfinite
