/-
Copyright (c) 2024 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Deriving `RigidCategory` instance for braided and left/right rigid categories.
-/

@[expose] public section

open CategoryTheory Category BraidedCategory MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] {X Y : C}

namespace CategoryTheory.BraidedCategory

set_option backward.privateInPublic true in
/-- `coevaluation_evaluation'` field of `ExactPairing Y X` in a braided category -/
/-
**CategoryTheory.BraidedCategory.coevaluation_evaluation_braided'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.BraidedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coevaluation_evaluation'` field of `ExactPairing Y X` in a braided category
-/
private theorem coevaluation_evaluation_braided' [inst : ExactPairing X Y] :
    X ◁ (η_ X Y ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ ε_ X Y) ▷ X
      = (ρ_ X).hom ≫ (λ_ X).inv := by
  /- Rearrange into _ = 𝟙 _ -/
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  /- Whitney trick transcribed: https://mathoverflow.net/a/162729/493261 -/
  calc
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (X ◁ (β_ Y X).inv ⊗≫ (β_ X Y).hom ▷ X) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      monoidal
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (𝟙 (X ⊗ X ⊗ Y) ⊗≫ (β_ X X).hom ▷ Y ⊗≫ X ◁ (β_ X Y).hom
          ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ 𝟙 ((Y ⊗ X) ⊗ X)) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      congr 3
      simp only [monoidalComp, MonoidalCoherence.assoc'_iso, MonoidalCoherence.whiskerRight_iso,
        MonoidalCoherence.refl_iso, whiskerRightIso_refl, Iso.refl_trans, Iso.symm_hom,
        MonoidalCoherence.assoc_iso, Iso.trans_refl, comp_id, id_comp]
      rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 5 rw [← IsIso.comp_inv_eq]
      simpa using yang_baxter X Y X
    _ = 𝟙 X ⊗≫ (X ◁ η_ X Y ≫ (β_ X (X ⊗ Y)).hom) ⊗≫ ((β_ (Y ⊗ X) X).inv ≫ ε_ X Y ▷ X) ⊗≫ 𝟙 X := by
      simp [monoidalComp, braiding_tensor_right_hom, braiding_tensor_left_inv]
    _ = _ := by
      rw [braiding_naturality_right, ← braiding_inv_naturality_right]
      simp [monoidalComp]

set_option backward.privateInPublic true in
/-- `evaluation_coevaluation'` field of `ExactPairing Y X` in a braided category -/
/-
**CategoryTheory.BraidedCategory.evaluation_coevaluation_braided'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.BraidedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`evaluation_coevaluation'` field of `ExactPairing Y X` in a braided category
-/
private theorem evaluation_coevaluation_braided' [inst : ExactPairing X Y] :
    (η_ X Y ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ ε_ X Y) =
      (λ_ Y).hom ≫ (ρ_ Y).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ ((β_ Y X).inv ▷ Y ⊗≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      monoidal
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ (𝟙 ((X ⊗ Y) ⊗ Y) ⊗≫ X ◁ (β_ Y Y).hom ⊗≫ (β_ X Y).hom ▷ Y
        ⊗≫ Y ◁ (β_ Y X).inv ⊗≫ (β_ Y Y).inv ▷ X ⊗≫ 𝟙 (Y ⊗ Y ⊗ X)) ⊗≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      congr 3
      on_goal 2 => simp [monoidalComp]
      simp only [monoidalComp, MonoidalCoherence.assoc_iso, MonoidalCoherence.whiskerRight_iso,
        MonoidalCoherence.refl_iso, whiskerRightIso_refl, Iso.trans_refl,
        MonoidalCoherence.assoc'_iso, Iso.refl_trans, Iso.symm_hom, comp_id, id_comp]
      iterate 2 rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 4 rw [← IsIso.comp_inv_eq]
      simpa using (yang_baxter Y X Y).symm
    _ = 𝟙 Y ⊗≫ (η_ X Y ▷ Y ≫ (β_ (X ⊗ Y) Y).hom) ⊗≫ ((β_ Y (Y ⊗ X)).inv ≫ Y ◁ ε_ X Y) ⊗≫ 𝟙 Y := by
      simp [monoidalComp, braiding_tensor_left_hom, braiding_tensor_right_inv]
    _ = _ := by
      rw [braiding_naturality_left, ← braiding_inv_naturality_left]
      simp [monoidalComp]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `X` and `Y` forms an exact pairing in a braided category, then so does `Y` and `X`
by composing the coevaluation and evaluation morphisms with associators. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.exactPairing_swap** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.BraidedCategory`。
形式化陈述：exactPairing_swap (X Y : C) [ExactPairing X Y] : ExactPairing Y X where co
evaluation'
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Monoidal.Rigid.Braided.0.CategoryTheory.
BraidedCategory.coevaluation_evaluation_braided'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   
[inst_2 : CategoryTheory.Braid…
· 使用定理 `_private.Mathlib.CategoryTheory.Monoidal.Rigid.Braided.0.CategoryTheory.
BraidedCategory.evaluation_coevaluation_braided'`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   
[inst_2 : CategoryTheory.Braid…

--- 原说明 ---
If `X` and `Y` forms an exact pairing in a braided category, then so does `Y` an
d `X`
by composing the coevaluation and evaluation morphisms with associators.
-/
def exactPairing_swap (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'

/-- If `X` has a right dual in a braided category, then it has a left dual. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.hasLeftDualOfHasRightDual** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：hasLeftDualOfHasRightDual [HasRightDual X] : HasLeftDual X where leftDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` has a right dual in a braided category, then it has a left dual.
-/
def hasLeftDualOfHasRightDual [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairing_swap X Xᘁ

/-- If `X` has a left dual in a braided category, then it has a right dual. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.hasRightDualOfHasLeftDual** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：hasRightDualOfHasLeftDual [HasLeftDual X] : HasRightDual X where rightDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` has a left dual in a braided category, then it has a right dual.
-/
def hasRightDualOfHasLeftDual [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairing_swap ᘁX X

/-- If a braided category is right-rigid, then it is left-rigid.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.leftRigidCategoryOfRightRigidCategory** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCa
tegory C where leftDual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a braided category is right-rigid, then it is left-rigid.
Not registered as an instance as this is not canonical enough.
-/
def leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCategory C where
  leftDual X := hasLeftDualOfHasRightDual (X := X)

/-- If a braided category is left-rigid, then it is right-rigid.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.rightRigidCategoryOfLeftRigidCategory** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCa
tegory C where rightDual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a braided category is left-rigid, then it is right-rigid.
Not registered as an instance as this is not canonical enough.
-/
def rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual (X := X)

/-- If `C` is a braided and right rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.rigidCategoryOfRightRigidCategory** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：rigidCategoryOfRightRigidCategory [RightRigidCategory C] : RigidCategory C
 where rightDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a braided and right rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough.
-/
def rigidCategoryOfRightRigidCategory [RightRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual X := hasLeftDualOfHasRightDual (X := X)

/-- If `C` is a braided and left rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/-
**CategoryTheory.BraidedCategory.rigidCategoryOfLeftRigidCategory** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.BraidedCategory`。
形式化陈述：rigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RigidCategory C w
here rightDual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a braided and left rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough.
-/
def rigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual (X := X)
  leftDual := inferInstance

end CategoryTheory.BraidedCategory

