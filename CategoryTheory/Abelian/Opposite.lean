/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
# The opposite of an abelian category is abelian.
-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type*) [Category* C] [Abelian C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian Cᵒᵖ
  body: { normalMonoOfMono f := ⟨normalMonoOfNormalEpiUnop _ (normalEpiOfEpi f.unop)⟩
    normalEpiOfEpi f := ⟨normalEpiOfNormalMonoUnop _ (normalMonoOfMono f.unop)⟩ }

中文:
实例 :
  签名: 交换 Cᵒᵖ
  定义体: { normalMonoOfMono f := ⟨normalMonoOfNormalEpiUnop _ (normalEpiOfEpi f.unop)⟩
    normalEpiOfEpi f := ⟨normalEpiOfNormalMonoUnop _ (normalMonoOfMono f.unop)⟩ }

Depends on / 依赖: f.unop, normalEpiOfEpi, normalEpiOfNormalMonoUnop, normalMonoOfMono, normalMonoOfNormalEpiUnop
-/
instance : Abelian Cᵒᵖ :=
  { normalMonoOfMono f := ⟨normalMonoOfNormalEpiUnop _ (normalEpiOfEpi f.unop)⟩
    normalEpiOfEpi f := ⟨normalEpiOfNormalMonoUnop _ (normalMonoOfMono f.unop)⟩ }

section

variable {C}
variable {X Y : C} (f : X ⟶ Y) {A B : Cᵒᵖ} (g : A ⟶ B)

-- TODO: Generalize (this will work whenever f has a cokernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
/--
Definition of `kernelOpUnop` / `kernelOpUnop` 的定义

English:
definition kernelOpUnop
  signature: : (kernel f.op).unop ≅ cokernel f where
  body: (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
cokernel.desc f (kernel.ι f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  hom_inv_id := by
    rw [← unop_id]; rw [← (cokernel.desc f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

中文:
定义 kernelOpUnop
  签名: : (kernel f.op).unop ≅ cokernel f where
  定义体: (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
cokernel.desc f (kernel.ι f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  hom_inv_id := by
    rw [← unop_id]; rw [← (cokernel.desc f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

Depends on / 依赖: cokernel, f.op, kernel, kernel.lift, op_comp
-/
def kernelOpUnop : (kernel f.op).unop ≅ cokernel f where
  hom := (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
cokernel.desc f (kernel.ι f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  hom_inv_id := by
    rw [← unop_id]; rw [← (cokernel.desc f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

-- TODO: Generalize (this will work whenever f has a kernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
/--
Definition of `cokernelOpUnop` / `cokernelOpUnop` 的定义

English:
definition cokernelOpUnop
  signature: : (cokernel f.op).unop ≅ kernel f where
  body: kernel.lift f (cokernel.π f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id := by
    rw [← unop_id]; rw [← (kernel.lift f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

中文:
定义 cokernelOpUnop
  签名: : (cokernel f.op).unop ≅ kernel f where
  定义体: kernel.lift f (cokernel.π f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id := by
    rw [← unop_id]; rw [← (kernel.lift f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

Depends on / 依赖: cokernel, cokernel.desc, f.op, f.unop_op, hom_inv_id, inv_hom_id, kernel, kernel.lift, op_comp, unop_comp, unop_id, unop_op
-/
def cokernelOpUnop : (cokernel f.op).unop ≅ kernel f where
  hom :=
kernel.lift f (cokernel.π f.op).unop by
      rw [← f.unop_op]; rw [← unop_comp]; rw [f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id := by
    rw [← unop_id]; rw [← (kernel.lift f _ _).unop_op]; rw [← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
/--
Definition of `kernelUnopOp` / `kernelUnopOp` 的定义

English:
definition kernelUnopOp
  signature: : Opposite.op (kernel g.unop) ≅ cokernel g
  body: (cokernelOpUnop g.unop).op

中文:
定义 kernelUnopOp
  签名: : 对偶.op (kernel g.unop) ≅ cokernel g
  定义体: (cokernelOpUnop g.unop).op

Depends on / 依赖: cokernelOpUnop, g.unop
-/
def kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernelOpUnop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
/--
Definition of `cokernelUnopOp` / `cokernelUnopOp` 的定义

English:
definition cokernelUnopOp
  signature: : Opposite.op (cokernel g.unop) ≅ kernel g
  body: (kernelOpUnop g.unop).op

中文:
定义 cokernelUnopOp
  签名: : 对偶.op (cokernel g.unop) ≅ kernel g
  定义体: (kernelOpUnop g.unop).op

Depends on / 依赖: g.unop, kernelOpUnop
-/
def cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernelOpUnop g.unop).op

/--
theorem `cokernel.π_op` / 定理 `cokernel.π_op`

English:
theorem cokernel.π_op
  proof: by
  simp [cokernelOpUnop]

中文:
定理 cokernel.π_op
  证明: by
  simp [cokernelOpUnop]

Depends on / 依赖: cokernelOpUnop
-/
theorem cokernel.π_op :
    (cokernel.π f.op).unop =
      (cokernelOpUnop f).hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm := by
  simp [cokernelOpUnop]

/--
theorem `kernel.ι_op` / 定理 `kernel.ι_op`

English:
theorem kernel.ι_op
  proof: by
  simp [kernelOpUnop]

中文:
定理 kernel.ι_op
  证明: by
  simp [kernelOpUnop]

Depends on / 依赖: kernelOpUnop
-/
theorem kernel.ι_op :
    (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpUnop f).inv := by
  simp [kernelOpUnop]

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps!]
/--
Definition of `kernelOpOp` / `kernelOpOp` 的定义

English:
definition kernelOpOp
  signature: : kernel f.op ≅ Opposite.op (cokernel f)
  body: (kernelOpUnop f).op.symm

中文:
定义 kernelOpOp
  签名: : kernel f.op ≅ 对偶.op (cokernel f)
  定义体: (kernelOpUnop f).op.symm

Depends on / 依赖: kernelOpUnop, op.symm
-/
def kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernelOpUnop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps!]
/--
Definition of `cokernelOpOp` / `cokernelOpOp` 的定义

English:
definition cokernelOpOp
  signature: : cokernel f.op ≅ Opposite.op (kernel f)
  body: (cokernelOpUnop f).op.symm

中文:
定义 cokernelOpOp
  签名: : cokernel f.op ≅ 对偶.op (kernel f)
  定义体: (cokernelOpUnop f).op.symm

Depends on / 依赖: cokernelOpUnop, op.symm
-/
def cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernelOpUnop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
/--
Definition of `kernelUnopUnop` / `kernelUnopUnop` 的定义

English:
definition kernelUnopUnop
  signature: : kernel g.unop ≅ (cokernel g).unop
  body: (kernelUnopOp g).unop.symm

中文:
定义 kernelUnopUnop
  签名: : kernel g.unop ≅ (cokernel g).unop
  定义体: (kernelUnopOp g).unop.symm

Depends on / 依赖: kernelUnopOp, unop.symm
-/
def kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop :=
  (kernelUnopOp g).unop.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `kernel.ι_unop` / 定理 `kernel.ι_unop`

English:
theorem kernel.ι_unop
  proof: by
  simp

中文:
定理 kernel.ι_unop
  证明: by
  simp
-/
theorem kernel.ι_unop :
    (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `cokernel.π_unop` / 定理 `cokernel.π_unop`

English:
theorem cokernel.π_unop
  proof: by
  simp

中文:
定理 cokernel.π_unop
  证明: by
  simp
-/
theorem cokernel.π_unop :
    (cokernel.π g.unop).op =
      (cokernelUnopOp g).hom ≫ kernel.ι g ≫ eqToHom (Opposite.op_unop _).symm := by
  simp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
/--
Definition of `cokernelUnopUnop` / `cokernelUnopUnop` 的定义

English:
definition cokernelUnopUnop
  signature: : cokernel g.unop ≅ (kernel g).unop
  body: (cokernelUnopOp g).unop.symm

中文:
定义 cokernelUnopUnop
  签名: : cokernel g.unop ≅ (kernel g).unop
  定义体: (cokernelUnopOp g).unop.symm

Depends on / 依赖: cokernelUnopOp, unop.symm
-/
def cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernelUnopOp g).unop.symm

/--
Definition of `imageUnopOp` / `imageUnopOp` 的定义

English:
definition imageUnopOp
  signature: : Opposite.op (image g.unop) ≅ image g
  body: (Abelian.imageIsoImage _).op ≪≫
    (cokernelOpOp _).symm ≪≫
      cokernelIsoOfEq (cokernel.π_unop _) ≪≫
        cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ Abelian.coimageIsoImage' _

中文:
定义 imageUnopOp
  签名: : 对偶.op (像 g.unop) ≅ 像 g
  定义体: (Abelian.imageIsoImage _).op ≪≫
    (cokernelOpOp _).symm ≪≫
      cokernelIsoOfEq (cokernel.π_unop _) ≪≫
        cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ Abelian.coimageIsoImage' _

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, Abelian.imageIsoImage, L.obj, coimageIsoImage, cokernel, cokernelCompIsIso, cokernelEpiComp, cokernelIsoOfEq, cokernelOpOp, imageIsoImage, isIso_hom_app, isPointwiseLeftKanExtensionLeftKanExtensionUnit
-/
def imageUnopOp : Opposite.op (image g.unop) ≅ image g :=
  (Abelian.imageIsoImage _).op ≪≫
    (cokernelOpOp _).symm ≪≫
      cokernelIsoOfEq (cokernel.π_unop _) ≪≫
        cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ Abelian.coimageIsoImage' _

/--
Definition of `imageOpOp` / `imageOpOp` 的定义

English:
definition imageOpOp
  signature: : Opposite.op (image f) ≅ image f.op
  body: imageUnopOp f.op

中文:
定义 imageOpOp
  签名: : 对偶.op (像 f) ≅ 像 f.op
  定义体: imageUnopOp f.op

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, f.op, imageUnopOp, isIso_of_isIso_app
-/
def imageOpOp : Opposite.op (image f) ≅ image f.op :=
  imageUnopOp f.op

/--
Definition of `imageOpUnop` / `imageOpUnop` 的定义

English:
definition imageOpUnop
  signature: : (image f.op).unop ≅ image f
  body: (imageUnopOp f.op).unop

中文:
定义 imageOpUnop
  签名: : (像 f.op).unop ≅ 像 f
  定义体: (imageUnopOp f.op).unop

Depends on / 依赖: f.op, imageUnopOp
-/
def imageOpUnop : (image f.op).unop ≅ image f :=
  (imageUnopOp f.op).unop

/--
Definition of `imageUnopUnop` / `imageUnopUnop` 的定义

English:
definition imageUnopUnop
  signature: : (image g).unop ≅ image g.unop
  body: (imageUnopOp g).unop

中文:
定义 imageUnopUnop
  签名: : (像 g).unop ≅ 像 g.unop
  定义体: (imageUnopOp g).unop

Depends on / 依赖: imageUnopOp, infer_instance, lanAdjunction_unit
-/
def imageUnopUnop : (image g).unop ≅ image g.unop :=
  (imageUnopOp g).unop

/--
theorem `image_ι_op_comp_imageUnopOp_hom` / 定理 `image_ι_op_comp_imageUnopOp_hom`

English:
theorem image_ι_op_comp_imageUnopOp_hom
  proof: by
  simp only [imageUnopOp, Iso.trans, Iso.symm, Iso.op, cokernelOpOp_inv, cokernelEpiComp_hom,
    cokernelCompIsIso_hom, Abelian.coimageIsoImage'_hom, ← Category.assoc, ← op_comp]
  simp only [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι,
    Quiver.Hom.op_unop, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    cokernel.π_desc]
  simp only [eqToHom_refl]
  rw [IsIso.inv_id]; rw [Category.id_comp]

中文:
定理 image_ι_op_comp_imageUnopOp_hom
  证明: by
  simp only [imageUnopOp, Iso.trans, Iso.symm, Iso.op, cokernelOpOp_inv, cokernelEpiComp_hom,
    cokernelCompIsIso_hom, Abelian.coimageIsoImage'_hom, ← Category.assoc, ← op_comp]
  simp only [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι,
    Quiver.Hom.op_unop, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    cokernel.π_desc]
  simp only [eqToHom_refl]
  rw [IsIso.inv_id]; rw [Category.id_comp]

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, Abelian.imageIsoImage_hom_comp_image_, Category, Category.assoc, Category.id_comp, IsIso.inv_id, Iso.op, Iso.symm, Iso.trans, Quiver, Quiver.Hom.op_unop, _hom, coimageIsoImage, cokernel, cokernelCompIsIso_hom, cokernelEpiComp_hom, cokernelIsoOfEq_hom_comp_desc_assoc, cokernelOpOp_inv, eqToHom_refl
-/
theorem image_ι_op_comp_imageUnopOp_hom :
    (image.ι g.unop).op ≫ (imageUnopOp g).hom = factorThruImage g := by
  simp only [imageUnopOp, Iso.trans, Iso.symm, Iso.op, cokernelOpOp_inv, cokernelEpiComp_hom,
    cokernelCompIsIso_hom, Abelian.coimageIsoImage'_hom, ← Category.assoc, ← op_comp]
  simp only [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι,
    Quiver.Hom.op_unop, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    cokernel.π_desc]
  simp only [eqToHom_refl]
  rw [IsIso.inv_id]; rw [Category.id_comp]

/--
theorem `imageUnopOp_hom_comp_image_ι` / 定理 `imageUnopOp_hom_comp_image_ι`

English:
theorem imageUnopOp_hom_comp_image_ι
  proof: by
  simp only [← cancel_epi (image.ι g.unop).op, ← Category.assoc, image_ι_op_comp_imageUnopOp_hom,
    ← op_comp, image.fac, Quiver.Hom.op_unop]

中文:
定理 imageUnopOp_hom_comp_image_ι
  证明: by
  simp only [← cancel_epi (image.ι g.unop).op, ← Category.assoc, image_ι_op_comp_imageUnopOp_hom,
    ← op_comp, image.fac, Quiver.Hom.op_unop]

Depends on / 依赖: Category, Category.assoc, Quiver, Quiver.Hom.op_unop, cancel_epi, g.unop, image.fac, op_comp, op_unop
-/
theorem imageUnopOp_hom_comp_image_ι :
    (imageUnopOp g).hom ≫ image.ι g = (factorThruImage g.unop).op := by
  simp only [← cancel_epi (image.ι g.unop).op, ← Category.assoc, image_ι_op_comp_imageUnopOp_hom,
    ← op_comp, image.fac, Quiver.Hom.op_unop]

/--
theorem `factorThruImage_comp_imageUnopOp_inv` / 定理 `factorThruImage_comp_imageUnopOp_inv`

English:
theorem factorThruImage_comp_imageUnopOp_inv
  proof: by
  rw [Iso.comp_inv_eq]; rw [image_ι_op_comp_imageUnopOp_hom]

中文:
定理 factorThruImage_comp_imageUnopOp_inv
  证明: by
  rw [Iso.comp_inv_eq]; rw [image_ι_op_comp_imageUnopOp_hom]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem factorThruImage_comp_imageUnopOp_inv :
    factorThruImage g ≫ (imageUnopOp g).inv = (image.ι g.unop).op := by
  rw [Iso.comp_inv_eq]; rw [image_ι_op_comp_imageUnopOp_hom]

/--
theorem `imageUnopOp_inv_comp_op_factorThruImage` / 定理 `imageUnopOp_inv_comp_op_factorThruImage`

English:
theorem imageUnopOp_inv_comp_op_factorThruImage
  proof: by
  rw [Iso.inv_comp_eq]; rw [imageUnopOp_hom_comp_image_ι]

中文:
定理 imageUnopOp_inv_comp_op_factorThruImage
  证明: by
  rw [Iso.inv_comp_eq]; rw [imageUnopOp_hom_comp_image_ι]

Depends on / 依赖: Iso.inv_comp_eq, infer_instance, inv_comp_eq, ranCounit
-/
theorem imageUnopOp_inv_comp_op_factorThruImage :
    (imageUnopOp g).inv ≫ (factorThruImage g.unop).op = image.ι g := by
  rw [Iso.inv_comp_eq]; rw [imageUnopOp_hom_comp_image_ι]

end

end CategoryTheory

end
