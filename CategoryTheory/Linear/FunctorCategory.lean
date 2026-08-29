/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Linear structure on functor categories

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Linear

variable {R : Type*} [Semiring R]
variable {C D : Type*} [Category* C] [Category* D] [Preadditive D] [Linear R D]

/--
Instance `functorCategoryLinear` / 实例 `functorCategoryLinear`

English:
instance functorCategoryLinear
  signature: : Linear R (C ⥤ D) where
  body: { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality := by
            intros
            rw [comp_smul]; rw [smul_comp]; rw [α.naturality] }
      one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul }
  smul_comp := by
    intros
    ext
    apply smul_comp
  comp_smul := by
    intros
    ext
    apply comp_smul

中文:
实例 functorCategoryLinear
  签名: : 线性 R (C ⥤ D) where
  定义体: { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality := by
            intros
            rw [comp_smul]; rw [smul_comp]; rw [α.naturality] }
      one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul }
  smul_comp := by
    intros
    ext
    apply smul_comp
  comp_smul := by
    intros
    ext
    apply comp_smul

Depends on / 依赖: add_smul, comp_smul, intros, mul_smul, naturality, one_smul, smul_add, smul_comp, smul_zero, zero_smul
-/
instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality := by
            intros
            rw [comp_smul]; rw [smul_comp]; rw [α.naturality] }
      one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul }
  smul_comp := by
    intros
    ext
    apply smul_comp
  comp_smul := by
    intros
    ext
    apply comp_smul

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
/--
Definition of `appLinearMap` / `appLinearMap` 的定义

English:
definition appLinearMap
  signature: (X : C)
  body: α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 appLinearMap
  签名: (X : C)
  定义体: α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
-/
def appLinearMap (X : C) : (F ⟶ G) ->ₗ[R] F.obj X ⟶ G.obj X where
  toFun α := α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `app_smul` / 定理 `app_smul`

English:
theorem app_smul
  given: (X : C) (r : R) (α : F ⟶ G)
  statement: (r • α).app X = r • α.app X
  proof: rfl

中文:
定理 app_smul
  条件: (X : C) (r : R) (α : F ⟶ G)
  结论: (r • α).app X = r • α.app X
  证明: rfl
-/
theorem app_smul (X : C) (r : R) (α : F ⟶ G) : (r • α).app X = r • α.app X :=
  rfl

end NatTrans

end CategoryTheory
