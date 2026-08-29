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

/--
Instance `functorHasRightDual` / 实例 `functorHasRightDual`

English:
instance functorHasRightDual
  signature: [RightRigidCategory D] (F : C ⥤ D)
  body: { obj := fun X => (F.obj X)ᘁ
      map := fun f => (F.map (inv f))ᘁ
      map_comp := fun f g => by simp [comp_rightAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Category.comp_id]; rw [Functor

中文:
实例 functorHasRightDual
  签名: [RightRigidCategory D] (F : C ⥤ D)
  定义体: { obj := fun X => (F.obj X)ᘁ
      map := fun f => (F.map (inv f))ᘁ
      map_comp := fun f g => by simp [comp_rightAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Category.comp_id]; rw [Functor

Depends on / 依赖: Category, Category.assoc, Category.comp_id, F.map, F.obj, Functor, Functor.map_inv, IsIso.hom_inv_id, MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_id, comp_id, comp_rightAdjointMate, evaluation, hom_inv_id, id_tensorHom, id_tensor_comp_tensor_id, map_comp, map_inv, naturality
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
            rw [Category.comp_id]; rw [Functor.map_inv]; rw [← id_tensor_comp_tensor_id]; rw [Category.assoc]; rw [id_tensorHom]; rw [tensorHom_id]; rw [rightAdjointMate_comp_evaluation]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [IsIso.hom_inv_id]; rw [MonoidalCategory.whiskerLeft_id]; rw [Category.id_comp] }
      coevaluation' :=
        { app := fun _ => η_ _ _
          naturality := fun X Y f => by
            dsimp
            rw [Functor.map_inv]; rw [Category.id_comp]; rw [← id_tensor_comp_tensor_id]; rw [id_tensorHom]; rw [tensorHom_id]; rw [← Category.assoc]; rw [coevaluation_comp_rightAdjointMate]; rw [Category.assoc]; rw [← comp_whiskerRight]; rw [IsIso.inv_hom_id]; rw [id_whiskerRight]; rw [Category.comp_id] } }

/--
Instance `rightRigidFunctorCategory` / 实例 `rightRigidFunctorCategory`

English:
instance rightRigidFunctorCategory
  signature: [RightRigidCategory D]

中文:
实例 rightRigidFunctorCategory
  签名: [RightRigidCategory D]
-/
instance rightRigidFunctorCategory [RightRigidCategory D] : RightRigidCategory (C ⥤ D) where

/--
Instance `functorHasLeftDual` / 实例 `functorHasLeftDual`

English:
instance functorHasLeftDual
  signature: [LeftRigidCategory D] (F : C ⥤ D)
  body: { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, leftAdjointMate_comp_evaluation]

中文:
实例 functorHasLeftDual
  签名: [LeftRigidCategory D] (F : C ⥤ D)
  定义体: { obj := fun X => ᘁ(F.obj X)
      map := fun f => ᘁ(F.map (inv f))
      map_comp := fun f g => by simp [comp_leftAdjointMate] }
  exact :=
    { evaluation' :=
        { app := fun _ => ε_ _ _
          naturality := fun X Y f => by
            simp [tensorHom_def, leftAdjointMate_comp_evaluation]

Depends on / 依赖: F.map, F.obj, coevaluation, coevaluation_comp_leftAdjointMate_assoc, comp_leftAdjointMate, evaluation, leftAdjointMate_comp_evaluation, map_comp, naturality, tensorHom_def
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

/--
Instance `leftRigidFunctorCategory` / 实例 `leftRigidFunctorCategory`

English:
instance leftRigidFunctorCategory
  signature: [LeftRigidCategory D]

中文:
实例 leftRigidFunctorCategory
  签名: [LeftRigidCategory D]
-/
instance leftRigidFunctorCategory [LeftRigidCategory D] : LeftRigidCategory (C ⥤ D) where

/--
Instance `rigidFunctorCategory` / 实例 `rigidFunctorCategory`

English:
instance rigidFunctorCategory
  signature: [RigidCategory D]

中文:
实例 rigidFunctorCategory
  签名: [RigidCategory D]
-/
instance rigidFunctorCategory [RigidCategory D] : RigidCategory (C ⥤ D) where

end CategoryTheory.Monoidal
