/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# `forget₂ (FGModuleCat K) (ModuleCat K)` creates all finite limits.

And hence `FGModuleCat K` has all finite limits.

## Future work
After generalising `FGModuleCat` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.

Analogous constructions for Noetherian modules.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {J : Type} [SmallCategory J] [FinCategory J]
variable {k : Type u} [Ring k]

instance {J : Type} [Finite J] (Z : J -> ModuleCat.{v} k) [forall j, Module.Finite k (Z j)] :
    Module.Finite k (∏ᶜ fun j => Z j : ModuleCat.{v} k) :=
  haveI : Module.Finite k (ModuleCat.of k (forall j, Z j)) := by unfold ModuleCat.of; infer_instance
  (Module.Finite.equiv_iff (ModuleCat.piIsoPi Z).toLinearEquiv).mpr inferInstance

variable [IsNoetherianRing k]

/-- Finite limits of finite-dimensional vector spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FGModuleCat k) :
    Module.Finite k (limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : forall j, Module.Finite k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) :=
inferInstanceAs forall j, Module.Finite k (F.obj j)
  Module.Finite.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k))).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite limits. -/
@[instance_reducible]
/--
Definition of `forget₂CreatesLimit` / `forget₂CreatesLimit` 的定义

English:
definition forget₂CreatesLimit
  signature: (F : J ⥤ FGModuleCat k)
  body: createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

中文:
定义 forget₂CreatesLimit
  签名: (F : J ⥤ FGModuleCat k)
  定义体: createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

Depends on / 依赖: FGModuleCat, Iso.refl, ModuleCat, ModuleCat.isFG_iff, createsLimitOfFullyFaithfulOfIso, infer_instance, isFG_iff
-/
def forget₂CreatesLimit (F : J ⥤ FGModuleCat k) :
    CreatesLimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  body: forget₂CreatesLimit F

中文:
实例 :
  签名: 创造形状极限 J (forget₂ (FGModuleCat k) (模范畴.{v} k))
  定义体: forget₂CreatesLimit F
-/
instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesLimit {F} := forget₂CreatesLimit F

instance (J : Type) [SmallCategory J] [FinCategory J] :
    HasLimitsOfShape J (FGModuleCat.{v} k) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteLimits (FGModuleCat.{v} k)
  body: inferInstance

中文:
实例 :
  签名: 有有限极限 (FGModuleCat.{v} k)
  定义体: inferInstance
-/
instance : HasFiniteLimits (FGModuleCat.{v} k) where
  out _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k))
  body: inferInstance

中文:
实例 :
  签名: 保持FiniteLimits (forget₂ (FGModuleCat k) (模范畴.{v} k))
  定义体: inferInstance
-/
instance : PreservesFiniteLimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteLimits _ _ _ := inferInstance

end FGModuleCat
