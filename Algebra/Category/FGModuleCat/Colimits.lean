/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# `forget₂ (FGModuleCat K) (ModuleCat K)` creates all finite colimits.

And hence `FGModuleCat K` has all finite colimits.

-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {J : Type} [SmallCategory J] [FinCategory J] {k : Type u} [Ring k]

instance {J : Type} [Finite J] (Z : J -> ModuleCat.{v} k) [forall j, Module.Finite k (Z j)] :
    Module.Finite k (∐ fun j => Z j : ModuleCat.{v} k) := by
  classical
exact (Module.Finite.equiv_iff (ModuleCat.coprodIsoDirectSum Z).toLinearEquiv).mpr inferInstance

/-- Finite colimits of finite modules are finite, because we can realise them as quotients
of a finite coproduct. -/
instance (F : J ⥤ FGModuleCat k) :
    Module.Finite k (colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  have (j : J) : Module.Finite k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) :=
inferInstanceAs Module.Finite k (F.obj j)
  Module.Finite.of_surjective
    (colimitQuotientCoproduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k))).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite colimits. -/
@[instance_reducible]
/--
Definition of `forget₂CreatesColimit` / `forget₂CreatesColimit` 的定义

English:
definition forget₂CreatesColimit
  signature: (F : J ⥤ FGModuleCat k)
  body: createsColimitOfFullyFaithfulOfIso
    ⟨(colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

中文:
定义 forget₂CreatesColimit
  签名: (F : J ⥤ FGModuleCat k)
  定义体: createsColimitOfFullyFaithfulOfIso
    ⟨(colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

Depends on / 依赖: FGModuleCat, Iso.refl, ModuleCat, ModuleCat.isFG_iff, colimit, createsColimitOfFullyFaithfulOfIso, infer_instance, isFG_iff
-/
def forget₂CreatesColimit (F : J ⥤ FGModuleCat k) :
    CreatesColimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsColimitOfFullyFaithfulOfIso
    ⟨(colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  body: forget₂CreatesColimit F

中文:
实例 :
  签名: CreatesColimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  定义体: forget₂CreatesColimit F
-/
instance : CreatesColimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesColimit {F} := forget₂CreatesColimit F

instance (J : Type) [SmallCategory J] [FinCategory J] :
    HasColimitsOfShape J (FGModuleCat.{v} k) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteColimits (FGModuleCat.{v} k)
  body: inferInstance

中文:
实例 :
  签名: HasFiniteColimits (FGModuleCat.{v} k)
  定义体: inferInstance
-/
instance : HasFiniteColimits (FGModuleCat.{v} k) where
  out _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  body: inferInstance

中文:
实例 :
  签名: PreservesFiniteColimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  定义体: inferInstance
-/
instance : PreservesFiniteColimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteColimits _ _ _ := inferInstance

end FGModuleCat
