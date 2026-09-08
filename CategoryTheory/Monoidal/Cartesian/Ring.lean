/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Yoneda embedding of `RingCatObj C`

-/

@[expose] public section

open CategoryTheory MonObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

open scoped CommRingObj RingObj

/-- If `R` is a ring object, then `Hom(-, R)` is a presheaf of rings. -/
@[simps! obj]
/-
**CategoryTheory.yonedaRingObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaRingObj (R : C) [RingObj R] : Cᵒᵖ ⥤ RingCat.{v} where obj X
参数：R : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a ring object, then `Hom(-, R)` is a presheaf of rings.
-/
def yonedaRingObj (R : C) [RingObj R] : Cᵒᵖ ⥤ RingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := RingCat.ofHom
    { toFun x := f.unop ≫ x
      map_one' := by simp
      map_zero' := by simp
      map_mul' _ _ := MonObj.comp_mul _ _ _
      map_add' _ _ := AddMonObj.comp_add _ _ _ }

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.yonedaRingObj_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：yonedaRingObj_map_apply {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X
.unop ⟶ R) : dsimp% (yonedaRingObj R).map f x = f.unop ≫ x
参数：f : X ⟶ Y；x : X.unop ⟶ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaRingObj_map_apply {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `RingObjCat C` into presheaves of rings. -/
/-
**CategoryTheory.yonedaRing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaRing : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda embedding of `RingObjCat C` into presheaves of rings.
-/
def yonedaRing : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where
  obj R := yonedaRingObj R.X
  map f :=
    { app X := RingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

/-- If `R` is a commutative ring object, then `Hom(-, R)` is a presheaf of commutative rings. -/
@[simps obj]
/-
**CategoryTheory.yonedaCommRingObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where ob
j X
参数：R : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a commutative ring object, then `Hom(-, R)` is a presheaf of commutati
ve rings.
-/
def yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.yonedaCommRingObj_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：yonedaCommRingObj_map_apply {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y
) (x : X.unop ⟶ R) : dsimp% (yonedaCommRingObj R).map f x = f.unop ≫ x
参数：f : X ⟶ Y；x : X.unop ⟶ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaCommRingObj_map_apply {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaCommRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `CommRingObjCat C` into presheaves of commutative rings. -/
@[simps obj]
/-
**CategoryTheory.yonedaCommRing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaCommRing : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda embedding of `CommRingObjCat C` into presheaves of commutative rings.
-/
def yonedaCommRing : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where
  obj R := yonedaCommRingObj R.X
  map f :=
    { app X := CommRingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

@[simp]
/-
**CategoryTheory.yonedaCommRing_map_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：yonedaCommRing_map_app_apply {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂) {X :
 C} (x : X ⟶ R₁.X) : dsimp% (yonedaCommRing.map f).app _ x = x ≫ f.hom
参数：f : R₁ ⟶ R₂；x : X ⟶ R₁.X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaCommRing_map_app_apply {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂)
    {X : C} (x : X ⟶ R₁.X) :
    dsimp% (yonedaCommRing.map f).app _ x = x ≫ f.hom := rfl

end CategoryTheory

