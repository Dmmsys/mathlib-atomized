/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Preserving images

In this file, we show that if a functor preserves spans and cospans, then it preserves images.
-/

@[expose] public section


noncomputable section

namespace CategoryTheory

namespace PreservesImage

open CategoryTheory

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [HasEqualizers A] [HasImages A]
variable [StrongEpiCategory B] [HasImages B]
variable (L : A ⥤ B)
variable [∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]
variable [∀ {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/-- If a functor preserves limit spans and colimit cospans, then it preserves images.
-/
@[simps!]
/-
**CategoryTheory.PreservesImage.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
eservesImage`。
形式化陈述：iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…

--- 原说明 ---
If a functor preserves limit spans and colimit cospans, then it preserves images
.
-/
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
      m := L.map <| Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
      e := L.map <| factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]
/-
**CategoryTheory.PreservesImage.factorThruImage_comp_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.PreservesImage`。
形式化陈述：factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) : factorThruImage (L.map f)
 ≫ (iso L f).hom = L.map (factorThruImage f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PreservesImage.iso_hom`：∀ {A : Type u₁} {B : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} A] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} B]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.image.fac_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).hom = L.map (factorThruImage f) := by simp

@[reassoc]
/-
**CategoryTheory.PreservesImage.hom_comp_map_image_** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.PreservesImage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).hom ≫ L.map (image.ι f) = image.ι (L.map f) := by rw [iso_hom, image.lift_fac]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.PreservesImage.inv_comp_image_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.PreservesImage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp

end PreservesImage

end CategoryTheory

