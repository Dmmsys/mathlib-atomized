/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# If `D` is abelian, then the functor category `C ⥤ D` is also abelian.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

namespace Abelian

section

universe z w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{z} D] [Abelian D]

namespace FunctorCategory

variable {F G : C ⥤ D} (α : F ⟶ G) (X : C)

set_option backward.defeqAttrib.useBackward true in
/-- The abelian coimage in a functor category can be calculated componentwise. -/
@[simps!]
/--
Definition of `coimageObjIso` / `coimageObjIso` 的定义

English:
definition coimageObjIso
  signature: : (Abelian.coimage α).obj X ≅ Abelian.coimage (α.app X)
  body: PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by
        dsimp
        simp only [Category.comp_id, PreservesKernel.iso_hom]
        exact (kernelComparison_comp_ι _ ((evaluation C D).obj X)).symm)

中文:
定义 coimageObjIso
  签名: : (交换.coimage α).obj X ≅ 交换.coimage (α.app X)
  定义体: PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by
        dsimp
        simp only [Category.comp_id, PreservesKernel.iso_hom]
        exact (kernelComparison_comp_ι _ ((evaluation C D).obj X)).symm)

Depends on / 依赖: Category, Category.comp_id, Iso.refl, PreservesCokernel, PreservesCokernel.iso, PreservesKernel, PreservesKernel.iso, PreservesKernel.iso_hom, cokernel, cokernel.mapIso, comp_id, evaluation, iso_hom, mapIso
-/
def coimageObjIso : (Abelian.coimage α).obj X ≅ Abelian.coimage (α.app X) :=
  PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by
        dsimp
        simp only [Category.comp_id, PreservesKernel.iso_hom]
        exact (kernelComparison_comp_ι _ ((evaluation C D).obj X)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The abelian image in a functor category can be calculated componentwise. -/
@[simps!]
/--
Definition of `imageObjIso` / `imageObjIso` 的定义

English:
definition imageObjIso
  signature: : (Abelian.image α).obj X ≅ Abelian.image (α.app X)
  body: PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by
        apply (cancel_mono (PreservesCokernel.iso ((evaluation C D).obj X) α).inv).1
        simp only [Category.assoc, Iso.hom_inv_id]
        dsimp
    

中文:
定义 imageObjIso
  签名: : (交换.像 α).obj X ≅ 交换.像 (α.app X)
  定义体: PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by
        apply (cancel_mono (PreservesCokernel.iso ((evaluation C D).obj X) α).inv).1
        simp only [Category.assoc, Iso.hom_inv_id]
        dsimp
    

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Iso.hom_inv_id, Iso.refl, PreservesCokernel, PreservesCokernel.iso, PreservesCokernel.iso_inv, PreservesKernel, PreservesKernel.iso, cancel_mono, comp_id, evaluation, hom_inv_id, id_comp, iso_inv, kernel, kernel.mapIso, mapIso
-/
def imageObjIso : (Abelian.image α).obj X ≅ Abelian.image (α.app X) :=
  PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by
        apply (cancel_mono (PreservesCokernel.iso ((evaluation C D).obj X) α).inv).1
        simp only [Category.assoc, Iso.hom_inv_id]
        dsimp
        simp only [PreservesCokernel.iso_inv, Category.id_comp, Category.comp_id]
        exact (π_comp_cokernelComparison _ ((evaluation C D).obj X)).symm)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `coimageImageComparison_app` / 定理 `coimageImageComparison_app`

English:
theorem coimageImageComparison_app
  proof: by
  ext
  dsimp
  dsimp [imageObjIso, coimageObjIso, cokernel.map]
  simp only [coimage_image_factorisation, PreservesKernel.iso_hom, Category.assoc,
    kernel.lift_ι, Category.comp_id, PreservesCokernel.iso_inv,
    cokernel.π_desc_assoc, Category.id_comp]
  erw [kernelComparison_comp_ι _ ((evalu

中文:
定理 coimageImageComparison_app
  证明: by
  ext
  dsimp
  dsimp [imageObjIso, coimageObjIso, cokernel.map]
  simp only [coimage_image_factorisation, PreservesKernel.iso_hom, Category.assoc,
    kernel.lift_ι, Category.comp_id, PreservesCokernel.iso_inv,
    cokernel.π_desc_assoc, Category.id_comp]
  erw [kernelComparison_comp_ι _ ((evalu

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, PreservesCokernel, PreservesCokernel.iso_inv, PreservesKernel, PreservesKernel.iso_hom, coimageObjIso, coimage_image_factorisation, cokernel, cokernel.map, comp_id, conv_lhs, evaluation, id_comp, imageObjIso, iso_hom, iso_inv, kernel
-/
theorem coimageImageComparison_app :
    coimageImageComparison (α.app X) =
      (coimageObjIso α X).inv ≫ (coimageImageComparison α).app X ≫ (imageObjIso α X).hom := by
  ext
  dsimp
  dsimp [imageObjIso, coimageObjIso, cokernel.map]
  simp only [coimage_image_factorisation, PreservesKernel.iso_hom, Category.assoc,
    kernel.lift_ι, Category.comp_id, PreservesCokernel.iso_inv,
    cokernel.π_desc_assoc, Category.id_comp]
  erw [kernelComparison_comp_ι _ ((evaluation C D).obj X)]
  erw [π_comp_cokernelComparison_assoc _ ((evaluation C D).obj X)]
  conv_lhs => rw [← coimage_image_factorisation α]
  rfl

/--
theorem `coimageImageComparison_app'` / 定理 `coimageImageComparison_app'`

English:
theorem coimageImageComparison_app'
  proof: by
  simp only [coimageImageComparison_app, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.assoc,
    Category.comp_id]

中文:
定理 coimageImageComparison_app'
  证明: by
  simp only [coimageImageComparison_app, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.assoc,
    Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.hom_inv_id, Iso.hom_inv_id_assoc, coimageImageComparison_app, comp_id, hom_inv_id, hom_inv_id_assoc
-/
theorem coimageImageComparison_app' :
    (coimageImageComparison α).app X =
      (coimageObjIso α X).hom ≫ coimageImageComparison (α.app X) ≫ (imageObjIso α X).inv := by
  simp only [coimageImageComparison_app, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.assoc,
    Category.comp_id]

/--
Instance `functor_category_isIso_coimageImageComparison` / 实例 `functor_category_isIso_coimageImageComparison`

English:
instance functor_category_isIso_coimageImageComparison
  signature: :
  body: by
  have : forall X : C, IsIso ((Abelian.coimageImageComparison α).app X) := by
    intros
    rw [coimageImageComparison_app']
    infer_instance
  apply NatIso.isIso_of_isIso_app

中文:
实例 functor_category_isIso_coimageImageComparison
  签名: :
  定义体: by
  have : forall X : C, IsIso ((Abelian.coimageImageComparison α).app X) := by
    intros
    rw [coimageImageComparison_app']
    infer_instance
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: Abelian, Abelian.coimageImageComparison, NatIso, NatIso.isIso_of_isIso_app, coimageImageComparison, coimageImageComparison_app, infer_instance, intros, isIso_of_isIso_app
-/
instance functor_category_isIso_coimageImageComparison :
    IsIso (Abelian.coimageImageComparison α) := by
  have : forall X : C, IsIso ((Abelian.coimageImageComparison α).app X) := by
    intros
    rw [coimageImageComparison_app']
    infer_instance
  apply NatIso.isIso_of_isIso_app

end FunctorCategory

/--
Instance `functorCategoryAbelian` / 实例 `functorCategoryAbelian`

English:
instance functorCategoryAbelian
  signature: : Abelian (C ⥤ D)
  body: let _ : HasKernels (C ⥤ D) := inferInstance
  let _ : HasCokernels (C ⥤ D) := inferInstance
  Abelian.ofCoimageImageComparisonIsIso

中文:
实例 functorCategoryAbelian
  签名: : 交换 (C ⥤ D)
  定义体: let _ : HasKernels (C ⥤ D) := inferInstance
  let _ : HasCokernels (C ⥤ D) := inferInstance
  Abelian.ofCoimageImageComparisonIsIso

Depends on / 依赖: Abelian, Abelian.ofCoimageImageComparisonIsIso, HasCokernels, HasKernels, ofCoimageImageComparisonIsIso
-/
noncomputable instance functorCategoryAbelian : Abelian (C ⥤ D) :=
  let _ : HasKernels (C ⥤ D) := inferInstance
  let _ : HasCokernels (C ⥤ D) := inferInstance
  Abelian.ofCoimageImageComparisonIsIso

end

end Abelian

end CategoryTheory
