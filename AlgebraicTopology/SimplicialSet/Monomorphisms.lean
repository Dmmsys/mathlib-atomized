/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# Monomorphisms of simplicial sets

In this file, we show that the class of monomorphisms in `SSet` is stable
under coproducts, pushouts, filtered colimits and transfinite compositions.

-/

public section

universe v' u' u

open CategoryTheory Limits MorphismProperty

namespace SSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoproducts.{v'}
  signature: (Type u)] :
  body: inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))

中文:
实例 [HasCoproducts.{v'}
  签名: (类型u)] :
  定义体: inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))

Depends on / 依赖: IsStableUnderCoproducts, monomorphisms
-/
instance [HasCoproducts.{v'} (Type u)] :
    IsStableUnderCoproducts.{v'} (monomorphisms SSet.{u}) :=
  inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (monomorphisms SSet).IsStableUnderCobaseChange
  body: by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance

中文:
实例 :
  签名: (monomorphisms SSet).是StableUnderCobaseChange
  定义体: by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance

Depends on / 依赖: IsStableUnderCobaseChange, functorCategory_monomorphisms, infer_instance, monomorphisms
-/
instance : (monomorphisms SSet).IsStableUnderCobaseChange := by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u})
  body: by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance

example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infe

中文:
实例 :
  签名: MorphismProperty.是StableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u})
  定义体: by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance

example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infe

Depends on / 依赖: IsStableUnderColimitsOfShape, functorCategory_monomorphisms, infer_instance, monomorphisms
-/
instance : MorphismProperty.IsStableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance

example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infer_instance

end SSet
