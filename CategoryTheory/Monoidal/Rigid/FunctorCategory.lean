/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a right/left rigid category form a right/left rigid category.

(Using the pointwise monoidal structure on the functor category.)
-/

public section


noncomputable section

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C D : Type*} [Groupoid C] [Category* D] [MonoidalCategory D]

/-
**CategoryTheory.Monoidal.functorHasRightDual** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Monoidal`。
形式化陈述：functorHasRightDual [RightRigidCategory D] (F : C ⥤ D) : HasRightDual F wh
ere rightDual
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorHasRightDual [RightRigidCategory D] (F : C ⥤ D) : HasRightDual F where
  rightDual :=
    { obj := fun X => (F.obj X)ᘁ
      map := fun f => (F.map (inv f))ᘁ
      map_comp := fun f g => by simp [comp_rightAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Category.comp_id, Functor.map_inv, ← id_tensor_comp_tensor_id, Category.assoc,
              id_tensorHom, tensorHom_id,
              rightAdjointMate_comp_evaluation, ← MonoidalCategory.whiskerLeft_comp_assoc,
              IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp] }
      coevaluation' :=
        { app := fun _ => η_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Functor.map_inv, Category.id_comp, ← id_tensor_comp_tensor_id,
              id_tensorHom, tensorHom_id, ← Category.assoc,
              coevaluation_comp_rightAdjointMate, Category.assoc, ← comp_whiskerRight,
              IsIso.inv_hom_id, id_whiskerRight, Category.comp_id] } }
/-
**CategoryTheory.Monoidal.rightRigidFunctorCategory** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Monoidal`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Groupoid C]
 →       [inst_1 : CategoryTheory.Category.{v_1, u_2} D] →         [inst_2 : Cat
egoryTheory.MonoidalCategory D] →           [CategoryTheory.RightRigidCategory D
] → CategoryTheory.RightRigidCategory (CategoryTheory.Functor C D)
参数：CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where
/-
**CategoryTheory.Monoidal.functorHasLeftDual** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Monoidal`。
形式化陈述：functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
 leftDual
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorHasLeftDual [LeftRigidCategory D] (F : C ⥤ D) : HasLeftDual F where
  leftDual :=
    { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, leftAdjointMate_comp_evaluation] }
      coevaluation' :=
        { app := fun _ => η_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, coevaluation_comp_leftAdjointMate_assoc] } }
/-
**CategoryTheory.Monoidal.leftRigidFunctorCategory** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Monoidal`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Groupoid C]
 →       [inst_1 : CategoryTheory.Category.{v_1, u_2} D] →         [inst_2 : Cat
egoryTheory.MonoidalCategory D] →           [CategoryTheory.LeftRigidCategory D]
 → CategoryTheory.LeftRigidCategory (CategoryTheory.Functor C D)
参数：CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where
/-
**CategoryTheory.Monoidal.rigidFunctorCategory** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Monoidal`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Groupoid C]
 →       [inst_1 : CategoryTheory.Category.{v_1, u_2} D] →         [inst_2 : Cat
egoryTheory.MonoidalCategory D] →           [CategoryTheory.RigidCategory D] → C
ategoryTheory.RigidCategory (CategoryTheory.Functor C D)
参数：CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where

end CategoryTheory.Monoidal

