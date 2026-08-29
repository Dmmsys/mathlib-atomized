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
/--
theorem `coevaluation_evaluation_braided'` / 定理 `coevaluation_evaluation_braided'`

English:
theorem coevaluation_evaluation_braided'
  given: [inst : ExactPairing X Y]
  proof: by
  /- Rearrange into _ = 𝟙 _ -/
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  /- Whitney trick transcribed: https://mathoverflow.net/a/162729/493261 -/
  calc
    _ = 𝟙 X otimes≫ X ◁ η_ X Y otimes≫ (X ◁ (β_ Y X).inv otimes≫ (β_ X Y).hom ▷ X) otimes≫ ε_ X Y ▷ X otimes≫ 𝟙 X := by
      monoida

中文:
定理 coevaluation_evaluation_braided'
  条件: [inst : ExactPairing X Y]
  证明: by
  /- Rearrange into _ = 𝟙 _ -/
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  /- Whitney trick transcribed: https://mathoverflow.net/a/162729/493261 -/
  calc
    _ = 𝟙 X otimes≫ X ◁ η_ X Y otimes≫ (X ◁ (β_ Y X).inv otimes≫ (β_ X Y).hom ▷ X) otimes≫ ε_ X Y ▷ X otimes≫ 𝟙 X := by
      monoida
-/
private theorem coevaluation_evaluation_braided' [inst : ExactPairing X Y] :
    X ◁ (η_ X Y ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ ε_ X Y) ▷ X
      = (ρ_ X).hom ≫ (fun_ X).inv := by
  /- Rearrange into _ = 𝟙 _ -/
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  /- Whitney trick transcribed: https://mathoverflow.net/a/162729/493261 -/
  calc
    _ = 𝟙 X otimes≫ X ◁ η_ X Y otimes≫ (X ◁ (β_ Y X).inv otimes≫ (β_ X Y).hom ▷ X) otimes≫ ε_ X Y ▷ X otimes≫ 𝟙 X := by
      monoidal
    _ = 𝟙 X otimes≫ X ◁ η_ X Y otimes≫ (𝟙 (X otimes X otimes Y) otimes≫ (β_ X X).hom ▷ Y otimes≫ X ◁ (β_ X Y).hom
          otimes≫ (β_ Y X).inv ▷ X otimes≫ Y ◁ (β_ X X).inv otimes≫ 𝟙 ((Y otimes X) otimes X)) otimes≫ ε_ X Y ▷ X otimes≫ 𝟙 X := by
      congr 3
      simp only [monoidalComp, MonoidalCoherence.assoc'_iso, MonoidalCoherence.whiskerRight_iso,
        MonoidalCoherence.refl_iso, whiskerRightIso_refl, Iso.refl_trans, Iso.symm_hom,
        MonoidalCoherence.assoc_iso, Iso.trans_refl, comp_id, id_comp]
      rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 5 rw [← IsIso.comp_inv_eq]
      simpa using yang_baxter X Y X
    _ = 𝟙 X otimes≫ (X ◁ η_ X Y ≫ (β_ X (X otimes Y)).hom) otimes≫ ((β_ (Y otimes X) X).inv ≫ ε_ X Y ▷ X) otimes≫ 𝟙 X := by
      simp [monoidalComp, braiding_tensor_right_hom, braiding_tensor_left_inv]
    _ = _ := by
      rw [braiding_naturality_right]; rw [← braiding_inv_naturality_right]
      simp [monoidalComp]

set_option backward.privateInPublic true in
/--
theorem `evaluation_coevaluation_braided'` / 定理 `evaluation_coevaluation_braided'`

English:
theorem evaluation_coevaluation_braided'
  given: [inst : ExactPairing X Y]
  proof: by
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ ((β_ Y X).inv ▷ Y otimes≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y otimes≫ 𝟙 Y := by
      monoidal
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ (𝟙 ((X otimes Y) otimes Y) otimes≫ X ◁ (β_ Y Y).hom otimes≫ (β_ X Y).hom

中文:
定理 evaluation_coevaluation_braided'
  条件: [inst : ExactPairing X Y]
  证明: by
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ ((β_ Y X).inv ▷ Y otimes≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y otimes≫ 𝟙 Y := by
      monoidal
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ (𝟙 ((X otimes Y) otimes Y) otimes≫ X ◁ (β_ Y Y).hom otimes≫ (β_ X Y).hom
-/
private theorem evaluation_coevaluation_braided' [inst : ExactPairing X Y] :
    (η_ X Y ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ ε_ X Y) =
      (fun_ Y).hom ≫ (ρ_ Y).inv := by
  rw [Iso.eq_comp_inv]; rw [← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ ((β_ Y X).inv ▷ Y otimes≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y otimes≫ 𝟙 Y := by
      monoidal
    _ = 𝟙 Y otimes≫ η_ X Y ▷ Y otimes≫ (𝟙 ((X otimes Y) otimes Y) otimes≫ X ◁ (β_ Y Y).hom otimes≫ (β_ X Y).hom ▷ Y
        otimes≫ Y ◁ (β_ Y X).inv otimes≫ (β_ Y Y).inv ▷ X otimes≫ 𝟙 (Y otimes Y otimes X)) otimes≫ Y ◁ ε_ X Y otimes≫ 𝟙 Y := by
      congr 3
      on_goal 2 => simp [monoidalComp]
      simp only [monoidalComp, MonoidalCoherence.assoc_iso, MonoidalCoherence.whiskerRight_iso,
        MonoidalCoherence.refl_iso, whiskerRightIso_refl, Iso.trans_refl,
        MonoidalCoherence.assoc'_iso, Iso.refl_trans, Iso.symm_hom, comp_id, id_comp]
      iterate 2 rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 4 rw [← IsIso.comp_inv_eq]
      simpa using (yang_baxter Y X Y).symm
    _ = 𝟙 Y otimes≫ (η_ X Y ▷ Y ≫ (β_ (X otimes Y) Y).hom) otimes≫ ((β_ Y (Y otimes X)).inv ≫ Y ◁ ε_ X Y) otimes≫ 𝟙 Y := by
      simp [monoidalComp, braiding_tensor_left_hom, braiding_tensor_right_inv]
    _ = _ := by
      rw [braiding_naturality_left]; rw [← braiding_inv_naturality_left]
      simp [monoidalComp]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `X` and `Y` forms an exact pairing in a braided category, then so does `Y` and `X`
by composing the coevaluation and evaluation morphisms with associators. -/
@[instance_reducible]
/--
Definition of `exactPairing_swap` / `exactPairing_swap` 的定义

English:
definition exactPairing_swap
  signature: (X Y : C) [ExactPairing X Y]
  body: η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'

中文:
定义 exactPairing_swap
  签名: (X Y : C) [ExactPairing X Y]
  定义体: η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'
-/
def exactPairing_swap (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'

/-- If `X` has a right dual in a braided category, then it has a left dual. -/
@[instance_reducible]
/--
Definition of `hasLeftDualOfHasRightDual` / `hasLeftDualOfHasRightDual` 的定义

English:
definition hasLeftDualOfHasRightDual
  signature: [HasRightDual X]
  body: Xᘁ
  exact := exactPairing_swap X Xᘁ

中文:
定义 hasLeftDualOfHasRightDual
  签名: [HasRightDual X]
  定义体: Xᘁ
  exact := exactPairing_swap X Xᘁ
-/
def hasLeftDualOfHasRightDual [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairing_swap X Xᘁ

/-- If `X` has a left dual in a braided category, then it has a right dual. -/
@[instance_reducible]
/--
Definition of `hasRightDualOfHasLeftDual` / `hasRightDualOfHasLeftDual` 的定义

English:
definition hasRightDualOfHasLeftDual
  signature: [HasLeftDual X]
  body: ᘁX
  exact := exactPairing_swap ᘁX X

中文:
定义 hasRightDualOfHasLeftDual
  签名: [HasLeftDual X]
  定义体: ᘁX
  exact := exactPairing_swap ᘁX X
-/
def hasRightDualOfHasLeftDual [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairing_swap ᘁX X

/-- If a braided category is right-rigid, then it is left-rigid.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/--
Definition of `leftRigidCategoryOfRightRigidCategory` / `leftRigidCategoryOfRightRigidCategory` 的定义

English:
definition leftRigidCategoryOfRightRigidCategory
  signature: [RightRigidCategory C]
  body: hasLeftDualOfHasRightDual (X := X)

中文:
定义 leftRigidCategoryOfRightRigidCategory
  签名: [RightRigidCategory C]
  定义体: hasLeftDualOfHasRightDual (X := X)

Depends on / 依赖: hasLeftDualOfHasRightDual
-/
def leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCategory C where
  leftDual X := hasLeftDualOfHasRightDual (X := X)

/-- If a braided category is left-rigid, then it is right-rigid.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/--
Definition of `rightRigidCategoryOfLeftRigidCategory` / `rightRigidCategoryOfLeftRigidCategory` 的定义

English:
definition rightRigidCategoryOfLeftRigidCategory
  signature: [LeftRigidCategory C]
  body: hasRightDualOfHasLeftDual (X := X)

中文:
定义 rightRigidCategoryOfLeftRigidCategory
  签名: [LeftRigidCategory C]
  定义体: hasRightDualOfHasLeftDual (X := X)

Depends on / 依赖: hasRightDualOfHasLeftDual
-/
def rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual (X := X)

/-- If `C` is a braided and right rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/--
Definition of `rigidCategoryOfRightRigidCategory` / `rigidCategoryOfRightRigidCategory` 的定义

English:
definition rigidCategoryOfRightRigidCategory
  signature: [RightRigidCategory C]
  body: inferInstance
  leftDual X := hasLeftDualOfHasRightDual (X := X)

中文:
定义 rigidCategoryOfRightRigidCategory
  签名: [RightRigidCategory C]
  定义体: inferInstance
  leftDual X := hasLeftDualOfHasRightDual (X := X)
-/
def rigidCategoryOfRightRigidCategory [RightRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual X := hasLeftDualOfHasRightDual (X := X)

/-- If `C` is a braided and left rigid category, then it is a rigid category.
Not registered as an instance as this is not canonical enough. -/
@[instance_reducible]
/--
Definition of `rigidCategoryOfLeftRigidCategory` / `rigidCategoryOfLeftRigidCategory` 的定义

English:
definition rigidCategoryOfLeftRigidCategory
  signature: [LeftRigidCategory C]
  body: hasRightDualOfHasLeftDual (X := X)
  leftDual := inferInstance

中文:
定义 rigidCategoryOfLeftRigidCategory
  签名: [LeftRigidCategory C]
  定义体: hasRightDualOfHasLeftDual (X := X)
  leftDual := inferInstance

Depends on / 依赖: hasRightDualOfHasLeftDual
-/
def rigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual (X := X)
  leftDual := inferInstance

end CategoryTheory.BraidedCategory
