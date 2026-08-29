/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!

# AB axioms in sheaf categories

If `J` is a Grothendieck topology on a small category `C : Type v`,
and `A : Type u₁` (with `Category.{v} A`) is a Grothendieck abelian category,
then `Sheaf J A` is a Grothendieck abelian category.

-/

public section

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits

namespace Sheaf

variable {C : Type u} {A : Type u₁} {K : Type u₂}
  [Category.{v} C] [Category.{v₁} A] [Category.{v₂} K]
  (J : GrothendieckTopology C)

section

/- The two instances in this section apply in very rare situations, as they assume
that the forgetful functor from sheaves to presheaves commutes with certain colimits.
This does apply for sheaves for the extensive topology --- condensed modules over a
ring are examples of such sheaves. -/

variable [HasWeakSheafify J A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: A] [HasColimitsOfShape K A] [HasExactColimitsOfShape K A]
  body: HasExactColimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

中文:
实例 [HasFiniteLimits
  签名: A] [HasColimitsOfShape K A] [HasExactColimitsOfShape K A]
  定义体: HasExactColimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

Depends on / 依赖: HasExactColimitsOfShape, HasExactColimitsOfShape.domain_of_functor, domain_of_functor, sheafToPresheaf
-/
instance [HasFiniteLimits A] [HasColimitsOfShape K A] [HasExactColimitsOfShape K A]
    [PreservesColimitsOfShape K (sheafToPresheaf J A)] : HasExactColimitsOfShape K (Sheaf J A) :=
  HasExactColimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: A] [HasLimitsOfShape K A] [HasExactLimitsOfShape K A]
  body: HasExactLimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

中文:
实例 [HasFiniteColimits
  签名: A] [HasLimitsOfShape K A] [HasExactLimitsOfShape K A]
  定义体: HasExactLimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

Depends on / 依赖: HasExactLimitsOfShape, HasExactLimitsOfShape.domain_of_functor, domain_of_functor, sheafToPresheaf
-/
instance [HasFiniteColimits A] [HasLimitsOfShape K A] [HasExactLimitsOfShape K A]
    [PreservesFiniteColimits (sheafToPresheaf J A)] : HasExactLimitsOfShape K (Sheaf J A) :=
  HasExactLimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

end

/--
Instance `hasFilteredColimitsOfSize` / 实例 `hasFilteredColimitsOfSize`

English:
instance hasFilteredColimitsOfSize
  body: by infer_instance

中文:
实例 hasFilteredColimitsOfSize
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance hasFilteredColimitsOfSize
    [HasSheafify J A] [HasFilteredColimitsOfSize.{v₂, u₂} A] :
    HasFilteredColimitsOfSize.{v₂, u₂} (Sheaf J A) where
  HasColimitsOfShape K := by infer_instance

/--
Instance `hasExactColimitsOfShape` / 实例 `hasExactColimitsOfShape`

English:
instance hasExactColimitsOfShape
  signature: [HasFiniteLimits A] [HasSheafify J A]
  body: (sheafificationAdjunction J A).hasExactColimitsOfShape K

中文:
实例 hasExactColimitsOfShape
  签名: [HasFiniteLimits A] [HasSheafify J A]
  定义体: (sheafificationAdjunction J A).hasExactColimitsOfShape K

Depends on / 依赖: hasExactColimitsOfShape, sheafificationAdjunction
-/
instance hasExactColimitsOfShape [HasFiniteLimits A] [HasSheafify J A]
    [HasColimitsOfShape K A] [HasExactColimitsOfShape K A] :
    HasExactColimitsOfShape K (Sheaf J A) :=
  (sheafificationAdjunction J A).hasExactColimitsOfShape K

/--
Instance `ab5ofSize` / 实例 `ab5ofSize`

English:
instance ab5ofSize
  signature: [HasFiniteLimits A] [HasSheafify J A]
  body: by infer_instance

中文:
实例 ab5ofSize
  签名: [HasFiniteLimits A] [HasSheafify J A]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance ab5ofSize [HasFiniteLimits A] [HasSheafify J A]
    [HasFilteredColimitsOfSize.{v₂, u₂} A] [AB5OfSize.{v₂, u₂} A] :
    AB5OfSize.{v₂, u₂} (Sheaf J A) where
  ofShape K _ _ := by infer_instance

instance {C : Type v} [SmallCategory.{v} C] (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] : IsGrothendieckAbelian.{v} (Sheaf J A) where

attribute [local instance] hasSheafifyEssentiallySmallSite in
/--
lemma `isGrothendieckAbelian_of_essentiallySmall` / 引理 `isGrothendieckAbelian_of_essentiallySmall`

English:
lemma isGrothendieckAbelian_of_essentiallySmall
  proof: IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

中文:
引理 isGrothendieckAbelian_of_essentiallySmall
  证明: IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

Depends on / 依赖: IsGrothendieckAbelian, IsGrothendieckAbelian.of_equivalence, equivSmallModel, inverse, inverse.sheafInducedTopologyEquivOfIsCoverDense, of_equivalence, sheafInducedTopologyEquivOfIsCoverDense
-/
lemma isGrothendieckAbelian_of_essentiallySmall
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{v} C]
    (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [forall (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] :
      IsGrothendieckAbelian.{v} (Sheaf J A) :=
  IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

end Sheaf

end CategoryTheory
