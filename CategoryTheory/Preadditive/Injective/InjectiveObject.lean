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

/-- The full subcategory of injective objects in a category `C`. -/
/-
**CategoryTheory.InjectiveObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：InjectiveObject : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of injective objects in a category `C`.
-/
abbrev InjectiveObject : Type u := ObjectProperty.FullSubcategory (isInjective C)

namespace InjectiveObject

/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) :
    ObjectProperty.IsClosedUnderLimitsOfShape (isInjective C) (Discrete J) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have (j : J) : Injective (p.diag.obj ⟨j⟩) := p.prop_diag_obj _
    exact ⟨fun q i _ ↦ ⟨p.isLimit.lift (Cone.mk _
      (Discrete.natTrans (fun ⟨j⟩ ↦ (Injective.factorThru (q ≫ p.π.app ⟨j⟩) i :)))),
        p.isLimit.hom_ext (fun ⟨j⟩ ↦ by simp [p.isLimit.fac])⟩⟩
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteProducts C] : HasFiniteProducts (InjectiveObject C) where
  out _ := inferInstance
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] [HasFiniteProducts C] : HasFiniteBiproducts (InjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteProducts
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] [HasBinaryBiproducts C] : HasBinaryBiproducts (InjectiveObject C) :=
  HasBinaryBiproducts.of_hasBinaryProducts
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] [HasZeroObject C] : (isInjective C).ContainsZero where
  exists_zero := ⟨0, by simp [IsZero.iff_id_eq_zero], Injective.zero_injective⟩

/-- The inclusion `InjectiveObject C ⥤ C` of the full subcategory of
injective objects in `C`. -/
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.In
jectiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `InjectiveObject C ⥤ C` of the full subcategory of
injective objects in `C`.
-/
abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : InjectiveObject C) : Injective ((ι C).obj X) := X.2
/-
**CategoryTheory.InjectiveObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Inje
ctiveObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : InjectiveObject C) : Injective X.obj := X.2

end InjectiveObject

end CategoryTheory

