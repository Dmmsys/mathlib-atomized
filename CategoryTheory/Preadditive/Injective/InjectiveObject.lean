/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The full subcategory of injective objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable (C : Type u) [Category.{v} C]

/--
Definition of `InjectiveObject` / `InjectiveObject` 的定义

English:
abbreviation InjectiveObject
  signature: : Type u
  body: ObjectProperty.FullSubcategory (isInjective C)

中文:
缩写 InjectiveObject
  签名: : 类型u
  定义体: ObjectProperty.FullSubcategory (isInjective C)

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, isInjective
-/
abbrev InjectiveObject : Type u := ObjectProperty.FullSubcategory (isInjective C)

namespace InjectiveObject

instance (J : Type*) :
    ObjectProperty.IsClosedUnderLimitsOfShape (isInjective C) (Discrete J) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have (j : J) : Injective (p.diag.obj ⟨j⟩) := p.prop_diag_obj _
    exact ⟨fun q i _ => ⟨p.isLimit.lift (Cone.mk _
      (Discrete.natTrans (fun ⟨j⟩ => (Injective.factorThru (q ≫ p.π.app ⟨j⟩) i :)))),
        p.isLimit.hom_ext (fun ⟨j⟩ => by simp [p.isLimit.fac])⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteProducts
  signature: C] : HasFiniteProducts (InjectiveObject C) where
  body: inferInstance

中文:
实例 [HasFiniteProducts
  签名: C] : HasFiniteProducts (InjectiveObject C) where
  定义体: inferInstance
-/
instance [HasFiniteProducts C] : HasFiniteProducts (InjectiveObject C) where
  out _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] [HasFiniteProducts C] : HasFiniteBiproducts (InjectiveObject C)
  body: HasFiniteBiproducts.of_hasFiniteProducts

中文:
实例 [Preadditive
  签名: C] [HasFiniteProducts C] : HasFiniteBiproducts (InjectiveObject C)
  定义体: HasFiniteBiproducts.of_hasFiniteProducts

Depends on / 依赖: HasFiniteBiproducts, HasFiniteBiproducts.of_hasFiniteProducts, of_hasFiniteProducts
-/
instance [Preadditive C] [HasFiniteProducts C] : HasFiniteBiproducts (InjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] [HasBinaryBiproducts C] : HasBinaryBiproducts (InjectiveObject C)
  body: HasBinaryBiproducts.of_hasBinaryProducts

中文:
实例 [Preadditive
  签名: C] [HasBinaryBiproducts C] : HasBinaryBiproducts (InjectiveObject C)
  定义体: HasBinaryBiproducts.of_hasBinaryProducts

Depends on / 依赖: HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryProducts, of_hasBinaryProducts
-/
instance [Preadditive C] [HasBinaryBiproducts C] : HasBinaryBiproducts (InjectiveObject C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] [HasZeroObject C] : (isInjective C).ContainsZero where
  body: ⟨0, by simp [IsZero.iff_id_eq_zero], Injective.zero_injective⟩

中文:
实例 [HasZeroMorphisms
  签名: C] [HasZeroObject C] : (isInjective C).ContainsZero where
  定义体: ⟨0, by simp [IsZero.iff_id_eq_zero], Injective.zero_injective⟩

Depends on / 依赖: Injective, Injective.zero_injective, IsZero, IsZero.iff_id_eq_zero, iff_id_eq_zero, zero_injective
-/
instance [HasZeroMorphisms C] [HasZeroObject C] : (isInjective C).ContainsZero where
  exists_zero := ⟨0, by simp [IsZero.iff_id_eq_zero], Injective.zero_injective⟩

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : InjectiveObject C ⥤ C
  body: ObjectProperty.ι _

中文:
缩写 ι
  签名: : InjectiveObject C ⥤ C
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : InjectiveObject C) : Injective ((ι C).obj X) := X.2

instance (X : InjectiveObject C) : Injective X.obj := X.2

end InjectiveObject

end CategoryTheory
