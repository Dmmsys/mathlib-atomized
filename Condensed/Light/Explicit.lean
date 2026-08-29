/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Condensed.Light.Module
/-!

# The explicit sheaf condition for light condensed sets

We give an explicit description of light condensed sets:

* `LightCondensed.ofSheafLightProfinite`: A finite-product-preserving presheaf on `LightProfinite`,
  satisfying `EqualizerCondition`.

The property `EqualizerCondition` is defined in
`Mathlib/CategoryTheory/Sites/Coherent/RegularSheaves.lean` and it says that for any effective epi
`X ⟶ B` (in this case that is equivalent to being a continuous surjection), the presheaf `F`
exhibits `F(B)` as the equalizer of the two maps `F(X) ⇉ F(X ×_B X)`.

We also give variants for light condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

variable {A : Type*} [Category* A]

namespace LightCondensed

/--
The light condensed object associated to a presheaf on `LightProfinite` which preserves finite
products and satisfies the equalizer condition.
-/
@[simps]
/--
Definition of `ofSheafLightProfinite` / `ofSheafLightProfinite` 的定义

English:
definition ofSheafLightProfinite
  signature: (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
  body: F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

中文:
定义 ofSheafLightProfinite
  签名: (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
  定义体: F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩
-/
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : LightCondensed A where
  obj := F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

/--
The light condensed object associated to a presheaf on `LightProfinite` whose postcomposition with
the forgetful functor preserves finite products and satisfies the equalizer condition.
-/
@[simps]
/--
Definition of `ofSheafForgetLightProfinite` / `ofSheafForgetLightProfinite` 的定义

English:
definition ofSheafForgetLightProfinite
  body: F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

中文:
定义 ofSheafForgetLightProfinite
  定义体: F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩
-/
noncomputable def ofSheafForgetLightProfinite
    {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : LightCondensed A where
  obj := F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

/--
theorem `equalizerCondition` / 定理 `equalizerCondition`

English:
theorem equalizerCondition
  given: (X : LightCondensed A)
  statement: EqualizerCondition X.obj
  proof: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

中文:
定理 equalizerCondition
  条件: (X : LightCondensed A)
  结论: EqualizerCondition X.obj
  证明: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

Depends on / 依赖: X.obj, X.property, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
theorem equalizerCondition (X : LightCondensed A) : EqualizerCondition X.obj :=
.2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

/-- A light condensed object preserves finite products. -/
noncomputable instance (X : LightCondensed A) : PreservesFiniteProducts X.obj :=
.1 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

end LightCondensed

namespace LightCondSet

/--
Definition of `ofSheafLightProfinite` / `ofSheafLightProfinite` 的定义

English:
abbreviation ofSheafLightProfinite
  signature: (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
  body: LightCondensed.ofSheafLightProfinite F hF

中文:
缩写 ofSheafLightProfinite
  签名: (F : LightProfinite.{u}ᵒᵖ ⥤ 类型u)
  定义体: LightCondensed.ofSheafLightProfinite F hF

Depends on / 依赖: LightCondensed, LightCondensed.ofSheafLightProfinite, ofSheafLightProfinite
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

/--
Definition of `ofSheafLightProfinite` / `ofSheafLightProfinite` 的定义

English:
abbreviation ofSheafLightProfinite
  signature: (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
  body: LightCondensed.ofSheafLightProfinite F hF

中文:
缩写 ofSheafLightProfinite
  签名: (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
  定义体: LightCondensed.ofSheafLightProfinite F hF

Depends on / 依赖: LightCondensed, LightCondensed.ofSheafLightProfinite, ofSheafLightProfinite
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondMod.{u} R :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondMod

namespace LightCondAb

/--
Definition of `ofSheafLightProfinite` / `ofSheafLightProfinite` 的定义

English:
abbreviation ofSheafLightProfinite
  signature: (F : LightProfiniteᵒᵖ ⥤ ModuleCat Int)
  body: LightCondMod.ofSheafLightProfinite Int F hF

中文:
缩写 ofSheafLightProfinite
  签名: (F : LightProfiniteᵒᵖ ⥤ ModuleCat 整数)
  定义体: LightCondMod.ofSheafLightProfinite Int F hF

Depends on / 依赖: LightCondMod, LightCondMod.ofSheafLightProfinite, ofSheafLightProfinite
-/
noncomputable abbrev ofSheafLightProfinite (F : LightProfiniteᵒᵖ ⥤ ModuleCat Int)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondAb :=
  LightCondMod.ofSheafLightProfinite Int F hF

end LightCondAb
