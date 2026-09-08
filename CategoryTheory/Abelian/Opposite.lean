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

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.kernelOpUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：kernelOpUnop : (kernel f.op).unop ≅ cokernel f where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `f.op` is the opposite of `cokernel f`.
-/
def kernelOpUnop : (kernel f.op).unop ≅ cokernel f where
  hom := (kernel.lift f.op (cokernel.π f).op <| by simp [← op_comp]).unop
  inv :=
    cokernel.desc f (kernel.ι f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  hom_inv_id := by
    rw [← unop_id, ← (cokernel.desc f _ _).unop_op, ← unop_comp]
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
/-
**CategoryTheory.cokernelOpUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cokernelOpUnop : (cokernel f.op).unop ≅ kernel f where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `f.op` is the opposite of `kernel f`.
-/
def cokernelOpUnop : (cokernel f.op).unop ≅ kernel f where
  hom :=
    kernel.lift f (cokernel.π f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  inv := (cokernel.desc f.op (kernel.ι f).op <| by simp [← op_comp]).unop
  hom_inv_id := by
    rw [← unop_id, ← (kernel.lift f _ _).unop_op, ← unop_comp]
    congr 1
    ext
    simp [← op_comp]
  inv_hom_id := by
    ext
    simp [← unop_comp]

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
/-
**CategoryTheory.kernelUnopOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `g.unop` is the opposite of `cokernel g`.
-/
def kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernelOpUnop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
/-
**CategoryTheory.cokernelUnopOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `g.unop` is the opposite of `kernel g`.
-/
def cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernelOpUnop g.unop).op
/-
**CategoryTheory.cokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernel.π_op :
    (cokernel.π f.op).unop =
      (cokernelOpUnop f).hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm := by
  simp [cokernelOpUnop]
/-
**CategoryTheory.kernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernel.ι_op :
    (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpUnop f).inv := by
  simp [kernelOpUnop]

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps!]
/-
**CategoryTheory.kernelOpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `f.op` is the opposite of `cokernel f`.
-/
def kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernelOpUnop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps!]
/-
**CategoryTheory.cokernelOpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `f.op` is the opposite of `kernel f`.
-/
def cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernelOpUnop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps!]
/-
**CategoryTheory.kernelUnopUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `g.unop` is the opposite of `cokernel g`.
-/
def kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop :=
  (kernelUnopOp g).unop.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.kernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kernel.ι_unop :
    (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.cokernel.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cokernel.π_unop :
    (cokernel.π g.unop).op =
      (cokernelUnopOp g).hom ≫ kernel.ι g ≫ eqToHom (Opposite.op_unop _).symm := by
  simp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps!]
/-
**CategoryTheory.cokernelUnopUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `g.unop` is the opposite of `kernel g`.
-/
def cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernelUnopOp g).unop.symm

/-- The opposite of the image of `g.unop` is the image of `g`. -/
/-
**CategoryTheory.imageUnopOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：imageUnopOp : Opposite.op (image g.unop) ≅ image g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.cokernel.π_unop`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C] {A B : Cᵒᵖ}   (g : A 
⟶ B),   (CategoryThe…

--- 原说明 ---
The opposite of the image of `g.unop` is the image of `g`.
-/
def imageUnopOp : Opposite.op (image g.unop) ≅ image g :=
  (Abelian.imageIsoImage _).op ≪≫
    (cokernelOpOp _).symm ≪≫
      cokernelIsoOfEq (cokernel.π_unop _) ≪≫
        cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ Abelian.coimageIsoImage' _

/-- The opposite of the image of `f` is the image of `f.op`. -/
/-
**CategoryTheory.imageOpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：imageOpOp : Opposite.op (image f) ≅ image f.op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of the image of `f` is the image of `f.op`.
-/
def imageOpOp : Opposite.op (image f) ≅ image f.op :=
  imageUnopOp f.op

/-- The image of `f.op` is the opposite of the image of `f`. -/
/-
**CategoryTheory.imageOpUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：imageOpUnop : (image f.op).unop ≅ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `f.op` is the opposite of the image of `f`.
-/
def imageOpUnop : (image f.op).unop ≅ image f :=
  (imageUnopOp f.op).unop

/-- The image of `g` is the opposite of the image of `g.unop.` -/
/-
**CategoryTheory.imageUnopUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：imageUnopUnop : (image g).unop ≅ image g.unop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `g` is the opposite of the image of `g.unop.`
-/
def imageUnopUnop : (image g).unop ≅ image g.unop :=
  (imageUnopOp g).unop
/-
**CategoryTheory.image_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_ι_op_comp_imageUnopOp_hom :
    (image.ι g.unop).op ≫ (imageUnopOp g).hom = factorThruImage g := by
  simp only [imageUnopOp, Iso.trans, Iso.symm, Iso.op, cokernelOpOp_inv, cokernelEpiComp_hom,
    cokernelCompIsIso_hom, Abelian.coimageIsoImage'_hom, ← Category.assoc, ← op_comp]
  simp only [Category.assoc, Abelian.imageIsoImage_hom_comp_image_ι, kernel.lift_ι,
    Quiver.Hom.op_unop, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc,
    cokernel.π_desc]
  simp only [eqToHom_refl]
  rw [IsIso.inv_id, Category.id_comp]
/-
**CategoryTheory.imageUnopOp_hom_comp_image_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageUnopOp_hom_comp_image_ι :
    (imageUnopOp g).hom ≫ image.ι g = (factorThruImage g.unop).op := by
  simp only [← cancel_epi (image.ι g.unop).op, ← Category.assoc, image_ι_op_comp_imageUnopOp_hom,
    ← op_comp, image.fac, Quiver.Hom.op_unop]
/-
**CategoryTheory.factorThruImage_comp_imageUnopOp_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
形式化陈述：factorThruImage_comp_imageUnopOp_inv : factorThruImage g ≫ (imageUnopOp g)
.inv = (image.ι g.unop).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.image_ι_op_comp_imageUnopOp_hom`：image_ι_op_comp_imageUno
pOp_hom : (image.ι g.unop).op ≫ (imageUnopOp g).hom = factorThruImage g
-/
theorem factorThruImage_comp_imageUnopOp_inv :
    factorThruImage g ≫ (imageUnopOp g).inv = (image.ι g.unop).op := by
  rw [Iso.comp_inv_eq, image_ι_op_comp_imageUnopOp_hom]
/-
**CategoryTheory.imageUnopOp_inv_comp_op_factorThruImage** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory`。
形式化陈述：imageUnopOp_inv_comp_op_factorThruImage : (imageUnopOp g).inv ≫ (factorThr
uImage g.unop).op = image.ι g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.imageUnopOp_hom_comp_image_ι`：imageUnopOp_hom_comp_image_
ι : (imageUnopOp g).hom ≫ image.ι g = (factorThruImage g.unop).op
-/
theorem imageUnopOp_inv_comp_op_factorThruImage :
    (imageUnopOp g).inv ≫ (factorThruImage g.unop).op = image.ι g := by
  rw [Iso.inv_comp_eq, imageUnopOp_hom_comp_image_ι]

end

end CategoryTheory

end

