/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A Grothendieck category according to the Stacks project is an abelian category provided that it
has `AB5` and a separator. However, this definition is not invariant under equivalences of
categories. Therefore, if `C` is an abelian category, the class `IsGrothendieckAbelian.{w} C` has a
weaker definition that is also satisfied for categories that are merely equivalent to a
Grothendieck category in the former strict sense.

## Theorems

The invariance under equivalences of categories is established in
`IsGrothendieckAbelian.of_equivalence`.

In particular, `ShrinkHoms.isGrothendieckAbelian C` shows that `ShrinkHoms C` satisfies our
definition of a Grothendieck category after shrinking its hom sets, which coincides with the strict
definition in this case.

Relevant implications of `IsGrothendieckAbelian` are established in
`IsGrothendieckAbelian.hasLimits` and `IsGrothendieckAbelian.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

public section

namespace CategoryTheory

open Limits

universe w v u w₂ v₂ u₂
variable (C : Type u) [Category.{v} C] (D : Type u₂) [Category.{v₂} D]

/--
If `C` is an abelian category, we shall say that it satisfies `IsGrothendieckAbelian.{w} C`
if it is locally small (relative to `w`), has exact filtered colimits of size `w` (AB5) and has a
separator.
If `[Category.{v} C]` and `w = v`, this means that `C` satisfies `AB5` and has a separator;
general results about Grothendieck abelian categories can be
reduced to this case using the instance `ShrinkHoms.isGrothendieckAbelian` below.

The introduction of the auxiliary universe `w` shall be needed for certain
applications to categories of sheaves. That the present definition still preserves essential
properties of Grothendieck categories is ensured by `IsGrothendieckAbelian.of_equivalence`,
which shows that every instance for `C` implies an instance for `ShrinkHoms C` with hom sets in
`Type w`.
-/
@[stacks 079B, pp_with_univ]
/--
Definition of `IsGrothendieckAbelian` / `IsGrothendieckAbelian` 的定义

English:
class IsGrothendieckAbelian
  parameters: [Abelian C]
  axioms and operations (4):
    - locallySmall : LocallySmall.{w} C  [default: by infer_instance]
    - hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C  [default: by infer_instance]
    - ab5OfSize : AB5OfSize.{w, w} C  [default: by infer_instance]
    - hasSeparator : HasSeparator C  [default: by infer_instance]

中文:
类 是GrothendieckAbelian
  参数: [交换 C]
  公理与运算 (4 个):
    - locallySmall : LocallySmall.{w} C  [默认: by infer_instance]
    - hasFilteredColimitsOfSize : 有FilteredColimitsOfSize.{w, w} C  [默认: by infer_instance]
    - ab5OfSize : AB5OfSize.{w, w} C  [默认: by infer_instance]
    - hasSeparator : 有Separator C  [默认: by infer_instance]

Depends on / 依赖: AB5OfSize, HasFilteredColimitsOfSize, HasSeparator, ab5OfSize, hasFilteredColimitsOfSize, hasSeparator, infer_instance
-/
class IsGrothendieckAbelian [Abelian C] : Prop where
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C := by infer_instance
  ab5OfSize : AB5OfSize.{w, w} C := by infer_instance
  hasSeparator : HasSeparator C := by infer_instance

attribute [instance] IsGrothendieckAbelian.locallySmall
  IsGrothendieckAbelian.hasFilteredColimitsOfSize IsGrothendieckAbelian.ab5OfSize
  IsGrothendieckAbelian.hasSeparator

variable {C} {D} in
/--
theorem `IsGrothendieckAbelian.of_equivalence` / 定理 `IsGrothendieckAbelian.of_equivalence`

English:
theorem IsGrothendieckAbelian.of_equivalence
  statement: [Abelian C] [Abelian D]
  proof: by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α

中文:
定理 是GrothendieckAbelian.of_equivalence
  结论: [交换 C] [交换 D]
  证明: by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α

Depends on / 依赖: Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, HasExactColimitsOfShape, HasExactColimitsOfShape.of_codomain_equivalence, HasFilteredColimitsOfSize, HasSeparator, HasSeparator.of_equivalence, hasColimitsOfShape_of_equivalence, hasFilteredColimits, inverse, locallySmall_of_faithful, of_codomain_equivalence, of_equivalence
-/
theorem IsGrothendieckAbelian.of_equivalence [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{w} C] (α : C ≌ D) : IsGrothendieckAbelian.{w} D := by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α

/--
Instance `ShrinkHoms.isGrothendieckAbelian` / 实例 `ShrinkHoms.isGrothendieckAbelian`

English:
instance ShrinkHoms.isGrothendieckAbelian
  signature: [Abelian C] [IsGrothendieckAbelian.{w} C]
  body: IsGrothendieckAbelian.of_equivalence ShrinkHoms.equivalence C

中文:
实例 ShrinkHoms.isGrothendieckAbelian
  签名: [交换 C] [是GrothendieckAbelian.{w} C]
  定义体: IsGrothendieckAbelian.of_equivalence ShrinkHoms.equivalence C

Depends on / 依赖: IsGrothendieckAbelian, IsGrothendieckAbelian.of_equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, of_equivalence
-/
instance ShrinkHoms.isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
IsGrothendieckAbelian.of_equivalence ShrinkHoms.equivalence C

section Instances

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
Instance `IsGrothendieckAbelian.hasColimits` / 实例 `IsGrothendieckAbelian.hasColimits`

English:
instance IsGrothendieckAbelian.hasColimits
  signature: : HasColimitsOfSize.{w, w} C
  body: has_colimits_of_finite_and_filtered

中文:
实例 是GrothendieckAbelian.hasColimits
  签名: : 有余limitsOfSize.{w, w} C
  定义体: has_colimits_of_finite_and_filtered

Depends on / 依赖: has_colimits_of_finite_and_filtered
-/
instance IsGrothendieckAbelian.hasColimits : HasColimitsOfSize.{w, w} C :=
  has_colimits_of_finite_and_filtered

/--
Instance `IsGrothendieckAbelian.hasLimits` / 实例 `IsGrothendieckAbelian.hasLimits`

English:
instance IsGrothendieckAbelian.hasLimits
  signature: : HasLimitsOfSize.{w, w} C
  body: have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)

中文:
实例 是GrothendieckAbelian.hasLimits
  签名: : 有LimitsOfSize.{w, w} C
  定义体: have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)

Depends on / 依赖: Adjunction, Adjunction.has_limits_of_equivalence, HasLimits, ShrinkHoms, ShrinkHoms.equivalence, equivalence, functor, hasLimits_of_hasColimits_of_hasSeparator, has_limits_of_equivalence
-/
instance IsGrothendieckAbelian.hasLimits : HasLimitsOfSize.{w, w} C :=
  have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)

/--
Instance `IsGrothendieckAbelian.wellPowered` / 实例 `IsGrothendieckAbelian.wellPowered`

English:
instance IsGrothendieckAbelian.wellPowered
  signature: : WellPowered.{w} C
  body: wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C).symm

中文:
实例 是GrothendieckAbelian.wellPowered
  签名: : 良幂.{w} C
  定义体: wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C).symm

Depends on / 依赖: ShrinkHoms, ShrinkHoms.equivalence, equivalence, wellPowered_of_equiv
-/
instance IsGrothendieckAbelian.wellPowered : WellPowered.{w} C :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C).symm

/--
Instance `IsGrothendieckAbelian.ab4OfSize` / 实例 `IsGrothendieckAbelian.ab4OfSize`

English:
instance IsGrothendieckAbelian.ab4OfSize
  signature: : AB4OfSize.{w} C
  body: by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  apply AB4.of_AB5

中文:
实例 是GrothendieckAbelian.ab4OfSize
  签名: : AB4OfSize.{w} C
  定义体: by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  apply AB4.of_AB5

Depends on / 依赖: AB4.of_AB5, HasFiniteBiproducts, HasFiniteBiproducts.of_hasFiniteProducts, of_AB5, of_hasFiniteProducts
-/
instance IsGrothendieckAbelian.ab4OfSize : AB4OfSize.{w} C := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  apply AB4.of_AB5

end Instances

end CategoryTheory
