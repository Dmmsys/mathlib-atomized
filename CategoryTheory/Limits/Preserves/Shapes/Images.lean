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
variable [forall {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]
variable [forall {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/-- If a functor preserves limit spans and colimit cospans, then it preserves images.
-/
@[simps!]
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: {X Y : A} (f : X ⟶ Y)
  body: let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
m := L.map Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
e := L.map factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]

中文:
定义 iso
  签名: {X Y : A} (f : X ⟶ Y)
  定义体: let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
m := L.map Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
e := L.map factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, L.map, L.map_comp, L.obj, Limits, Limits.image, Limits.image.fac, StrongEpiMonoFactorisation, aux1.toMonoIsImage, e_strong_epi, factorThruImage, isImage, isoExt, m_mono, map_comp, preserves_epi_of_preservesColimit, preserves_mono_of_preservesLimit, strongEpi_of_epi
-/
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { I := L.obj (Limits.image f)
m := L.map Limits.image.ι _
      m_mono := preserves_mono_of_preservesLimit _ _
e := L.map factorThruImage _
      e_strong_epi := @strongEpi_of_epi B _ _ _ _ _ (preserves_epi_of_preservesColimit L _)
      fac := by rw [← L.map_comp, Limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]
/--
theorem `factorThruImage_comp_hom` / 定理 `factorThruImage_comp_hom`

English:
theorem factorThruImage_comp_hom
  given: {X Y : A} (f : X ⟶ Y)
  proof: by simp

@[reassoc]

中文:
定理 factorThruImage_comp_hom
  条件: {X Y : A} (f : X ⟶ Y)
  证明: by simp

@[reassoc]
-/
theorem factorThruImage_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).hom = L.map (factorThruImage f) := by simp

@[reassoc]
/--
theorem `hom_comp_map_image_ι` / 定理 `hom_comp_map_image_ι`

English:
theorem hom_comp_map_image_ι
  given: {X Y : A} (f : X ⟶ Y)
  proof: by rw [iso_hom, image.lift_fac]

中文:
定理 hom_comp_map_image_ι
  条件: {X Y : A} (f : X ⟶ Y)
  证明: by rw [iso_hom, image.lift_fac]

Depends on / 依赖: image.lift_fac, iso_hom, lift_fac
-/
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
    (iso L f).hom ≫ L.map (image.ι f) = image.ι (L.map f) := by rw [iso_hom, image.lift_fac]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `inv_comp_image_ι_map` / 定理 `inv_comp_image_ι_map`

English:
theorem inv_comp_image_ι_map
  given: {X Y : A} (f : X ⟶ Y)
  proof: by simp

中文:
定理 inv_comp_image_ι_map
  条件: {X Y : A} (f : X ⟶ Y)
  证明: by simp
-/
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
    (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by simp

end PreservesImage

end CategoryTheory
