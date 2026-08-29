/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
/-!
# The braided and symmetric category structures on graded objects

In this file, we construct the braiding
`GradedObject.Monoidal.braiding : tensorObj X Y ≅ tensorObj Y X`
for two objects `X` and `Y` in `GradedObject I C`, when `I` is a commutative
additive monoid (and suitable coproducts exist in a braided category `C`).

When `C` is a braided category and suitable assumptions are made, we obtain the braided category
structure on `GradedObject I C` and show that it is symmetric if `C` is symmetric.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {I : Type*} [AddCommMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]

namespace GradedObject

namespace Monoidal

variable (X Y Z : GradedObject I C)

section Braided

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `braiding` / `braiding` 的定义

English:
definition braiding
  signature: [HasTensor X Y] [HasTensor Y X]
  body: tensorObjDesc (fun i j hij => (β_ _ _).hom ≫
    ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij))
  inv k := tensorObjDesc (fun i j hij => (β_ _ _).inv ≫
    ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij))

中文:
定义 braiding
  签名: [HasTensor X Y] [HasTensor Y X]
  定义体: tensorObjDesc (fun i j hij => (β_ _ _).hom ≫
    ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij))
  inv k := tensorObjDesc (fun i j hij => (β_ _ _).inv ≫
    ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij))

Depends on / 依赖: tensorObjDesc
-/
noncomputable def braiding [HasTensor X Y] [HasTensor Y X] : tensorObj X Y ≅ tensorObj Y X where
  hom k := tensorObjDesc (fun i j hij => (β_ _ _).hom ≫
    ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij))
  inv k := tensorObjDesc (fun i j hij => (β_ _ _).inv ≫
    ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij))

set_option backward.isDefEq.respectTransparency.types false in
variable {Y Z} in
/--
lemma `braiding_naturality_right` / 引理 `braiding_naturality_right`

English:
lemma braiding_naturality_right
  statement: [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] [HasTensor Z X]
  proof: by
  dsimp [braiding]
  cat_disch

中文:
引理 braiding_naturality_right
  结论: [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] [HasTensor Z X]
  证明: by
  dsimp [braiding]
  cat_disch

Depends on / 依赖: braiding, cat_disch
-/
lemma braiding_naturality_right [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] [HasTensor Z X]
    (f : Y ⟶ Z) :
    whiskerLeft X f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ whiskerRight f X := by
  dsimp [braiding]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
variable {X Y} in
/--
lemma `braiding_naturality_left` / 引理 `braiding_naturality_left`

English:
lemma braiding_naturality_left
  statement: [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [HasTensor Z X]
  proof: by
  dsimp [braiding]
  cat_disch

中文:
引理 braiding_naturality_left
  结论: [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [HasTensor Z X]
  证明: by
  dsimp [braiding]
  cat_disch

Depends on / 依赖: braiding, cat_disch
-/
lemma braiding_naturality_left [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [HasTensor Z X]
    (f : X ⟶ Y) :
    whiskerRight f Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ whiskerLeft Z f := by
  dsimp [braiding]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hexagon_forward` / 引理 `hexagon_forward`

English:
lemma hexagon_forward
  statement: [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z]
  proof: by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
    assoc, ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.id_tensorHom,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_right_ho

中文:
引理 hexagon_forward
  结论: [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z]
  证明: by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
    assoc, ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.id_tensorHom,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_right_ho

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality_assoc, BraidedCategory.braiding_tensor_right_hom, Iso.hom_inv_id_assoc, Iso.inv_hom_id_as, MonoidalCategory, MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, _associator_hom, _associator_hom_assoc, _eq_assoc, add_assoc, add_comm, braiding, braiding_naturality_assoc, braiding_tensor_right_hom, conv_lhs, hom_inv_id_assoc, id_tensorHom, inv_hom_id_as
-/
lemma hexagon_forward [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z]
    [HasTensor Z X] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)]
    [HasTensor (tensorObj Y X) Z] [HasTensor Y (tensorObj X Z)]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Y Z X] [HasGoodTensorTensor₂₃ Y Z X]
    [HasGoodTensor₁₂Tensor Y X Z] [HasGoodTensorTensor₂₃ Y X Z] :
    (associator X Y Z).hom ≫ (braiding X (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
      whiskerRight (braiding X Y).hom Z ≫ (associator Y X Z).hom ≫
        whiskerLeft Y (braiding X Z).hom := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
    assoc, ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.id_tensorHom,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_right_hom, assoc, assoc, assoc, assoc, Iso.hom_inv_id_assoc,
    MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq_assoc Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h]) _ rfl,
    ιTensorObj₃'_associator_hom, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.comp_tensor_id, assoc,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq_assoc Y X Z i₂ i₁ i₃ k
      (by rw [add_comm i₂ i₁, h]) (i₁ + i₂) (add_comm i₂ i₁),
    ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq Y X Z i₂ i₁ i₃ k (by rw [add_comm i₂ i₁, h]) _ rfl, assoc,
    ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.id_tensor_comp_assoc,
    ι_tensorObjDesc, MonoidalCategory.id_tensor_comp, assoc,
    ← MonoidalCategory.id_tensor_comp_assoc, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp, assoc,
    ← ιTensorObj₃_eq Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h])
      (i₁ + i₃) (add_comm _ _)]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hexagon_reverse` / 引理 `hexagon_reverse`

English:
lemma hexagon_reverse
  statement: [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
  proof: by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.tensorHom_id,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_left_hom

中文:
引理 hexagon_reverse
  结论: [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
  证明: by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.tensorHom_id,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_left_hom

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality_assoc, BraidedCategory.braiding_tensor_left_hom, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, add_assoc, add_comm, braiding, braiding_naturality_assoc, braiding_tensor_left_hom, conv_lhs, hom_inv_id_assoc, id_tensorHom, inv_hom_id_assoc, tensorHom_id
-/
lemma hexagon_reverse [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
    [HasTensor Z Y] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor Z (tensorObj X Y)] [HasTensor (tensorObj Z X) Y]
    [HasTensor X (tensorObj Z Y)] [HasTensor (tensorObj X Z) Y]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Z X Y] [HasGoodTensorTensor₂₃ Z X Y]
    [HasGoodTensor₁₂Tensor X Z Y] [HasGoodTensorTensor₂₃ X Z Y] :
    (associator X Y Z).inv ≫ (braiding (tensorObj X Y) Z).hom ≫ (associator Z X Y).inv =
      whiskerLeft X (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
        whiskerRight (braiding X Z).hom Y := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.tensorHom_id,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_left_hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.id_tensorHom,
    ← ιTensorObj₃_eq_assoc Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h]) _ rfl,
    ιTensorObj₃_associator_inv, Iso.hom_inv_id_assoc]
  conv_rhs => rw [ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.id_tensor_comp, assoc,
    MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom,
    ← ιTensorObj₃_eq_assoc X Z Y i₁ i₃ i₂ k
      (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) (i₂ + i₃) (add_comm _ _),
    ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq X Z Y i₁ i₃ i₂ k (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) _ rfl,
    assoc, ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_tensor_id_assoc,
    ι_tensorObjDesc, MonoidalCategory.comp_tensor_id, assoc,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h])
      (i₁ + i₃) (add_comm _ _)]

end Braided

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `symmetry` / 引理 `symmetry`

English:
lemma symmetry
  given: [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X]
  proof: by
  dsimp [braiding]
  cat_disch

中文:
引理 symmetry
  条件: [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X]
  证明: by
  dsimp [braiding]
  cat_disch

Depends on / 依赖: braiding, cat_disch
-/
lemma symmetry [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X] :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 _ := by
  dsimp [braiding]
  cat_disch

end Monoidal

section Instances

variable
  [forall (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [forall (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [forall (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [forall X₁, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).obj X₁)]
  [forall X₂, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [forall (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/--
Instance `braidedCategory` / 实例 `braidedCategory`

English:
instance braidedCategory
  signature: [BraidedCategory C]
  body: Monoidal.braiding X Y
  braiding_naturality_left _ _ := Monoidal.braiding_naturality_left _ _
  braiding_naturality_right _ _ _ _ := Monoidal.braiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.hexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.hexagon_reverse _ _ _

中文:
实例 braidedCategory
  签名: [BraidedCategory C]
  定义体: Monoidal.braiding X Y
  braiding_naturality_left _ _ := Monoidal.braiding_naturality_left _ _
  braiding_naturality_right _ _ _ _ := Monoidal.braiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.hexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.hexagon_reverse _ _ _

Depends on / 依赖: Monoidal, Monoidal.braiding, braiding
-/
noncomputable instance braidedCategory [BraidedCategory C] :
    BraidedCategory (GradedObject I C) where
  braiding X Y := Monoidal.braiding X Y
  braiding_naturality_left _ _ := Monoidal.braiding_naturality_left _ _
  braiding_naturality_right _ _ _ _ := Monoidal.braiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.hexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.hexagon_reverse _ _ _

/--
Instance `symmetricCategory` / 实例 `symmetricCategory`

English:
instance symmetricCategory
  signature: [SymmetricCategory C]
  body: Monoidal.symmetry _ _

中文:
实例 symmetricCategory
  签名: [SymmetricCategory C]
  定义体: Monoidal.symmetry _ _

Depends on / 依赖: Monoidal, Monoidal.symmetry, symmetry
-/
noncomputable instance symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (GradedObject I C) where
  symmetry _ _ := Monoidal.symmetry _ _

/-!
The braided/symmetric monoidal category structure on `GradedObject ℕ C` can
be inferred from the assumptions `[HasFiniteCoproducts C]`,
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]` and
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]`.
This requires importing `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`.
-/

end Instances

end GradedObject

end CategoryTheory
