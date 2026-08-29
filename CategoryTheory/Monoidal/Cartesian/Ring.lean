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
/--
Definition of `yonedaRingObj` / `yonedaRingObj` 的定义

English:
definition yonedaRingObj
  signature: (R : C) [RingObj R]
  body: .of (X.unop ⟶ R)
  map f := RingCat.ofHom
    { toFun x := f.unop ≫ x
      map_one' := by simp
      map_zero' := by simp
      map_mul' _ _ := MonObj.comp_mul _ _ _
      map_add' _ _ := AddMonObj.comp_add _ _ _ }

中文:
定义 yonedaRingObj
  签名: (R : C) [RingObj R]
  定义体: .of (X.unop ⟶ R)
  map f := RingCat.ofHom
    { toFun x := f.unop ≫ x
      map_one' := by simp
      map_zero' := by simp
      map_mul' _ _ := MonObj.comp_mul _ _ _
      map_add' _ _ := AddMonObj.comp_add _ _ _ }

Depends on / 依赖: X.unop
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
/--
lemma `yonedaRingObj_map_apply` / 引理 `yonedaRingObj_map_apply`

English:
lemma yonedaRingObj_map_apply
  given: {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R)
  proof: rfl

中文:
引理 yonedaRingObj_map_apply
  条件: {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R)
  证明: rfl
-/
lemma yonedaRingObj_map_apply {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `yonedaRing` / `yonedaRing` 的定义

English:
definition yonedaRing
  signature: : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where
  body: yonedaRingObj R.X
  map f :=
    { app X := RingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

中文:
定义 yonedaRing
  签名: : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where
  定义体: yonedaRingObj R.X
  map f :=
    { app X := RingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

Depends on / 依赖: yonedaRingObj
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
/--
Definition of `yonedaCommRingObj` / `yonedaCommRingObj` 的定义

English:
definition yonedaCommRingObj
  signature: (R : C) [CommRingObj R]
  body: .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

中文:
定义 yonedaCommRingObj
  签名: (R : C) [CommRingObj R]
  定义体: .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

Depends on / 依赖: X.unop
-/
def yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `yonedaCommRingObj_map_apply` / 引理 `yonedaCommRingObj_map_apply`

English:
lemma yonedaCommRingObj_map_apply
  given: {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R)
  proof: rfl

中文:
引理 yonedaCommRingObj_map_apply
  条件: {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R)
  证明: rfl
-/
lemma yonedaCommRingObj_map_apply {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaCommRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `CommRingObjCat C` into presheaves of commutative rings. -/
@[simps obj]
/--
Definition of `yonedaCommRing` / `yonedaCommRing` 的定义

English:
definition yonedaCommRing
  signature: : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where
  body: yonedaCommRingObj R.X
  map f :=
    { app X := CommRingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

@[simp]

中文:
定义 yonedaCommRing
  签名: : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where
  定义体: yonedaCommRingObj R.X
  map f :=
    { app X := CommRingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

@[simp]

Depends on / 依赖: yonedaCommRingObj
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
/--
lemma `yonedaCommRing_map_app_apply` / 引理 `yonedaCommRing_map_app_apply`

English:
lemma yonedaCommRing_map_app_apply
  statement: {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂)
  proof: rfl

中文:
引理 yonedaCommRing_map_app_apply
  结论: {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂)
  证明: rfl
-/
lemma yonedaCommRing_map_app_apply {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂)
    {X : C} (x : X ⟶ R₁.X) :
    dsimp% (yonedaCommRing.map f).app _ x = x ≫ f.hom := rfl

end CategoryTheory
