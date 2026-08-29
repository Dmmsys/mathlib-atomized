/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Chosen finite products on sheaves

In this file, we put a `CartesianMonoidalCategory` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a `CartesianMonoidalCategory` instance.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Category Limits Sieve MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [CartesianMonoidalCategory A]

namespace Sheaf
variable (X Y : Sheaf J A)

/--
lemma `tensorProd_isSheaf` / 引理 `tensorProd_isSheaf`

English:
lemma tensorProd_isSheaf
  statement: Presheaf.IsSheaf J (X.obj otimes Y.obj)
  proof: by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

中文:
引理 tensorProd_isSheaf
  结论: Presheaf.IsSheaf J (X.obj otimes Y.obj)
  证明: by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

Depends on / 依赖: BinaryFan, BinaryFan.mk, Cone.postcompose, IsLimit, IsLimit.postcomposeInvEquiv, X.obj, Y.obj, invFun, isSheaf_of_isLimit, pairComp, postcompose, postcomposeInvEquiv, sheafToPresheaf, tensorProductIsBinaryProduct
-/
lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.obj otimes Y.obj) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

/--
lemma `tensorUnit_isSheaf` / 引理 `tensorUnit_isSheaf`

English:
lemma tensorUnit_isSheaf
  statement: Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A))
  proof: by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

中文:
引理 tensorUnit_isSheaf
  结论: Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A))
  证明: by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

Depends on / 依赖: Cone.postcompose, Functor, Functor.uniqueFromEmpty, IsLimit, IsLimit.postcomposeInvEquiv, asEmptyCone, invFun, isSheaf_of_isLimit, isTerminalTensorUnit, postcompose, postcomposeInvEquiv, uniqueFromEmpty
-/
lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsMonoidal (Presheaf.IsSheaf J (A := A))
  body: tensorUnit_isSheaf _
  prop_tensor F G hF hG := tensorProd_isSheaf J ⟨F, hF⟩ ⟨G, hG⟩

example : CartesianMonoidalCategory (Sheaf J A) :=
  inferInstance

中文:
实例 :
  签名: Object命题erty.IsMonoidal (Presheaf.IsSheaf J (A := A))
  定义体: tensorUnit_isSheaf _
  prop_tensor F G hF hG := tensorProd_isSheaf J ⟨F, hF⟩ ⟨G, hG⟩

example : CartesianMonoidalCategory (Sheaf J A) :=
  inferInstance
-/
instance : ObjectProperty.IsMonoidal (Presheaf.IsSheaf J (A := A)) where
  prop_unit := tensorUnit_isSheaf _
  prop_tensor F G hF hG := tensorProd_isSheaf J ⟨F, hF⟩ ⟨G, hG⟩

example : CartesianMonoidalCategory (Sheaf J A) :=
  inferInstance


/--
lemma `cartesianMonoidalCategoryFst_hom` / 引理 `cartesianMonoidalCategoryFst_hom`

English:
lemma cartesianMonoidalCategoryFst_hom
  statement: (fst X Y).hom = fst X.obj Y.obj
  proof: rfl

中文:
引理 cartesianMonoidalCategoryFst_hom
  结论: (fst X Y).hom = fst X.obj Y.obj
  证明: rfl
-/
@[simp] lemma cartesianMonoidalCategoryFst_hom : (fst X Y).hom = fst X.obj Y.obj := rfl
/--
lemma `cartesianMonoidalCategorySnd_hom` / 引理 `cartesianMonoidalCategorySnd_hom`

English:
lemma cartesianMonoidalCategorySnd_hom
  statement: (snd X Y).hom = snd X.obj Y.obj
  proof: rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryFst_val := cartesianMonoidalCategoryFst_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategorySnd_val := cartesianMonoidalCategorySnd_hom

中文:
引理 cartesianMonoidalCategorySnd_hom
  结论: (snd X Y).hom = snd X.obj Y.obj
  证明: rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryFst_val := cartesianMonoidalCategoryFst_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategorySnd_val := cartesianMonoidalCategorySnd_hom
-/
@[simp] lemma cartesianMonoidalCategorySnd_hom : (snd X Y).hom = snd X.obj Y.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryFst_val := cartesianMonoidalCategoryFst_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategorySnd_val := cartesianMonoidalCategorySnd_hom

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

/--
lemma `cartesianMonoidalCategoryLift_hom` / 引理 `cartesianMonoidalCategoryLift_hom`

English:
lemma cartesianMonoidalCategoryLift_hom
  statement: (lift f g).hom = lift f.hom g.hom
  proof: rfl

中文:
引理 cartesianMonoidalCategoryLift_hom
  结论: (lift f g).hom = lift f.hom g.hom
  证明: rfl
-/
@[simp] lemma cartesianMonoidalCategoryLift_hom : (lift f g).hom = lift f.hom g.hom := rfl
/--
lemma `cartesianMonoidalCategoryWhiskerLeft_hom` / 引理 `cartesianMonoidalCategoryWhiskerLeft_hom`

English:
lemma cartesianMonoidalCategoryWhiskerLeft_hom
  statement: (X ◁ f).hom = X.obj ◁ f.hom
  proof: rfl

中文:
引理 cartesianMonoidalCategoryWhiskerLeft_hom
  结论: (X ◁ f).hom = X.obj ◁ f.hom
  证明: rfl
-/
lemma cartesianMonoidalCategoryWhiskerLeft_hom : (X ◁ f).hom = X.obj ◁ f.hom := rfl
/--
lemma `cartesianMonoidalCategoryWhiskerRight_hom` / 引理 `cartesianMonoidalCategoryWhiskerRight_hom`

English:
lemma cartesianMonoidalCategoryWhiskerRight_hom
  statement: (f ▷ X).hom = f.hom ▷ X.obj
  proof: rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryLift_val := cartesianMonoidalCategoryLift_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerLeft_val := cartesianMonoidalCategoryWhiskerLeft_hom
@[deprecated (since := "2026-03-05")]
alias cartesi

中文:
引理 cartesianMonoidalCategoryWhiskerRight_hom
  结论: (f ▷ X).hom = f.hom ▷ X.obj
  证明: rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryLift_val := cartesianMonoidalCategoryLift_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerLeft_val := cartesianMonoidalCategoryWhiskerLeft_hom
@[deprecated (since := "2026-03-05")]
alias cartesi
-/
lemma cartesianMonoidalCategoryWhiskerRight_hom : (f ▷ X).hom = f.hom ▷ X.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryLift_val := cartesianMonoidalCategoryLift_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerLeft_val := cartesianMonoidalCategoryWhiskerLeft_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerRight_val := cartesianMonoidalCategoryWhiskerRight_hom

end Sheaf

open Functor.LaxMonoidal Functor.OplaxMonoidal

/--
lemma `sheafToPresheaf_ε` / 引理 `sheafToPresheaf_ε`

English:
lemma sheafToPresheaf_ε
  statement: ε (sheafToPresheaf J A) = 𝟙 _
  proof: rfl

中文:
引理 sheafToPresheaf_ε
  结论: ε (sheafToPresheaf J A) = 𝟙 _
  证明: rfl
-/
@[simp] lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
/--
lemma `sheafToPresheaf_η` / 引理 `sheafToPresheaf_η`

English:
lemma sheafToPresheaf_η
  statement: η (sheafToPresheaf J A) = 𝟙 _
  proof: rfl

中文:
引理 sheafToPresheaf_η
  结论: η (sheafToPresheaf J A) = 𝟙 _
  证明: rfl
-/
@[simp] lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}

/--
lemma `sheafToPresheaf_μ` / 引理 `sheafToPresheaf_μ`

English:
lemma sheafToPresheaf_μ
  given: (X Y : Sheaf J A)
  statement: μ (sheafToPresheaf J A) X Y = 𝟙 _
  proof: rfl

中文:
引理 sheafToPresheaf_μ
  条件: (X Y : Sheaf J A)
  结论: μ (sheafToPresheaf J A) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
/--
lemma `sheafToPresheaf_δ` / 引理 `sheafToPresheaf_δ`

English:
lemma sheafToPresheaf_δ
  given: (X Y : Sheaf J A)
  statement: δ (sheafToPresheaf J A) X Y = 𝟙 _
  proof: rfl

中文:
引理 sheafToPresheaf_δ
  条件: (X Y : Sheaf J A)
  结论: δ (sheafToPresheaf J A) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory
