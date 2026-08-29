/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Preservation of coimage-image comparisons

If a functor preserves kernels and cokernels, then it preserves abelian images, abelian coimages
and coimage-image comparisons.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {X Y : C} (f : X ⟶ Y)

section Images

variable [HasCokernel f] [HasKernel (cokernel.π f)] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F] [HasCokernel (F.map f)]
  [HasKernel (cokernel.π (F.map f))]

/--
Definition of `PreservesImage.iso` / `PreservesImage.iso` 的定义

English:
definition PreservesImage.iso
  signature: : F.obj (Abelian.image f) ≅ Abelian.image (F.map f)
  body: PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)

@[reassoc (attr := simp)]

中文:
定义 PreservesImage.iso
  签名: : F.obj (Abelian.image f) ≅ Abelian.image (F.map f)
  定义体: PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.refl, PreservesCokernel, PreservesCokernel.iso, PreservesKernel, PreservesKernel.iso, kernel, kernel.mapIso, mapIso
-/
def PreservesImage.iso : F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
  PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)

@[reassoc (attr := simp)]
/--
theorem `PreservesImage.iso_hom_ι` / 定理 `PreservesImage.iso_hom_ι`

English:
theorem PreservesImage.iso_hom_ι
  proof: by
  simp [iso]

@[reassoc (attr := simp)]

中文:
定理 PreservesImage.iso_hom_ι
  证明: by
  simp [iso]

@[reassoc (attr := simp)]
-/
theorem PreservesImage.iso_hom_ι :
    (PreservesImage.iso F f).hom ≫ Abelian.image.ι (F.map f) = F.map (Abelian.image.ι f) := by
  simp [iso]

@[reassoc (attr := simp)]
/--
theorem `PreservesImage.factorThruImage_iso_hom` / 定理 `PreservesImage.factorThruImage_iso_hom`

English:
theorem PreservesImage.factorThruImage_iso_hom
  proof: by
  ext; simp [iso]

@[reassoc (attr := simp)]

中文:
定理 PreservesImage.factorThruImage_iso_hom
  证明: by
  ext; simp [iso]

@[reassoc (attr := simp)]
-/
theorem PreservesImage.factorThruImage_iso_hom :
    F.map (Abelian.factorThruImage f) ≫ (PreservesImage.iso F f).hom =
      Abelian.factorThruImage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
/--
theorem `PreservesImage.iso_inv_ι` / 定理 `PreservesImage.iso_inv_ι`

English:
theorem PreservesImage.iso_inv_ι
  proof: by
  simp [iso]

@[reassoc (attr := simp)]

中文:
定理 PreservesImage.iso_inv_ι
  证明: by
  simp [iso]

@[reassoc (attr := simp)]
-/
theorem PreservesImage.iso_inv_ι :
    (PreservesImage.iso F f).inv ≫ F.map (Abelian.image.ι f) = Abelian.image.ι (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
/--
theorem `PreservesImage.factorThruImage_iso_inv` / 定理 `PreservesImage.factorThruImage_iso_inv`

English:
theorem PreservesImage.factorThruImage_iso_inv
  proof: by
  simp [Iso.comp_inv_eq]

中文:
定理 PreservesImage.factorThruImage_iso_inv
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem PreservesImage.factorThruImage_iso_inv :
    Abelian.factorThruImage (F.map f) ≫ (PreservesImage.iso F f).inv =
      F.map (Abelian.factorThruImage f) := by
  simp [Iso.comp_inv_eq]

end Images

section Coimages

variable [HasKernel f] [HasCokernel (kernel.ι f)] [PreservesLimit (parallelPair f 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F] [HasKernel (F.map f)]
  [HasCokernel (kernel.ι (F.map f))]

/--
Definition of `PreservesCoimage.iso` / `PreservesCoimage.iso` 的定义

English:
definition PreservesCoimage.iso
  signature: : F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f)
  body: PreservesCokernel.iso F _ ≪≫ cokernel.mapIso _ _ (PreservesKernel.iso F _) (Iso.refl _) (by simp)

@[reassoc (attr := simp)]

中文:
定义 PreservesCoimage.iso
  签名: : F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f)
  定义体: PreservesCokernel.iso F _ ≪≫ cokernel.mapIso _ _ (PreservesKernel.iso F _) (Iso.refl _) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.refl, PreservesCokernel, PreservesCokernel.iso, PreservesKernel, PreservesKernel.iso, cokernel, cokernel.mapIso, mapIso
-/
def PreservesCoimage.iso : F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f) :=
  PreservesCokernel.iso F _ ≪≫ cokernel.mapIso _ _ (PreservesKernel.iso F _) (Iso.refl _) (by simp)

@[reassoc (attr := simp)]
/--
theorem `PreservesCoimage.iso_hom_π` / 定理 `PreservesCoimage.iso_hom_π`

English:
theorem PreservesCoimage.iso_hom_π
  proof: by
  simp [iso]

@[reassoc (attr := simp)]

中文:
定理 PreservesCoimage.iso_hom_π
  证明: by
  simp [iso]

@[reassoc (attr := simp)]
-/
theorem PreservesCoimage.iso_hom_π :
    F.map (Abelian.coimage.π f) ≫ (PreservesCoimage.iso F f).hom = Abelian.coimage.π (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
/--
theorem `PreservesCoimage.factorThruCoimage_iso_inv` / 定理 `PreservesCoimage.factorThruCoimage_iso_inv`

English:
theorem PreservesCoimage.factorThruCoimage_iso_inv
  proof: by
  ext; simp [iso]

@[reassoc (attr := simp)]

中文:
定理 PreservesCoimage.factorThruCoimage_iso_inv
  证明: by
  ext; simp [iso]

@[reassoc (attr := simp)]
-/
theorem PreservesCoimage.factorThruCoimage_iso_inv :
    (PreservesCoimage.iso F f).inv ≫ F.map (Abelian.factorThruCoimage f) =
      Abelian.factorThruCoimage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
/--
theorem `PreservesCoimage.factorThruCoimage_iso_hom` / 定理 `PreservesCoimage.factorThruCoimage_iso_hom`

English:
theorem PreservesCoimage.factorThruCoimage_iso_hom
  proof: by
  simp [← Iso.eq_inv_comp]

@[reassoc (attr := simp)]

中文:
定理 PreservesCoimage.factorThruCoimage_iso_hom
  证明: by
  simp [← Iso.eq_inv_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
theorem PreservesCoimage.factorThruCoimage_iso_hom :
    (PreservesCoimage.iso F f).hom ≫ Abelian.factorThruCoimage (F.map f) =
      F.map (Abelian.factorThruCoimage f) := by
  simp [← Iso.eq_inv_comp]

@[reassoc (attr := simp)]
/--
theorem `PreservesCoimage.iso_inv_π` / 定理 `PreservesCoimage.iso_inv_π`

English:
theorem PreservesCoimage.iso_inv_π
  proof: by
  simp [Iso.comp_inv_eq]

中文:
定理 PreservesCoimage.iso_inv_π
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem PreservesCoimage.iso_inv_π :
    Abelian.coimage.π (F.map f) ≫ (PreservesCoimage.iso F f).inv = F.map (Abelian.coimage.π f) := by
  simp [Iso.comp_inv_eq]

end Coimages

variable [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
  [PreservesLimit (parallelPair f 0) F] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F]
  [HasKernel (cokernel.π (F.map f))] [HasCokernel (kernel.ι (F.map f))]

/--
theorem `PreservesCoimage.hom_coimageImageComparison` / 定理 `PreservesCoimage.hom_coimageImageComparison`

English:
theorem PreservesCoimage.hom_coimageImageComparison
  proof: by
  simp [← Functor.map_comp, ← Iso.eq_inv_comp, ← cancel_epi (Abelian.coimage.π (F.map f)),
    ← cancel_mono (Abelian.image.ι (F.map f))]

中文:
定理 PreservesCoimage.hom_coimageImageComparison
  证明: by
  simp [← Functor.map_comp, ← Iso.eq_inv_comp, ← cancel_epi (Abelian.coimage.π (F.map f)),
    ← cancel_mono (Abelian.image.ι (F.map f))]

Depends on / 依赖: Abelian, Abelian.coimage, Abelian.image, F.map, Functor, Functor.map_comp, Iso.eq_inv_comp, cancel_epi, cancel_mono, coimage, eq_inv_comp, map_comp
-/
theorem PreservesCoimage.hom_coimageImageComparison :
    (PreservesCoimage.iso F f).hom ≫ coimageImageComparison (F.map f) =
      F.map (coimageImageComparison f) ≫ (PreservesImage.iso F f).hom := by
  simp [← Functor.map_comp, ← Iso.eq_inv_comp, ← cancel_epi (Abelian.coimage.π (F.map f)),
    ← cancel_mono (Abelian.image.ι (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves coimage-image comparisons. -/
@[simps!]
/--
Definition of `PreservesCoimageImageComparison.iso` / `PreservesCoimageImageComparison.iso` 的定义

English:
definition PreservesCoimageImageComparison.iso
  signature: :
  body: Arrow.isoMk' _ _ (PreservesCoimage.iso F f) (PreservesImage.iso F f)
    (PreservesCoimage.hom_coimageImageComparison F f)

中文:
定义 PreservesCoimageImageComparison.iso
  签名: :
  定义体: Arrow.isoMk' _ _ (PreservesCoimage.iso F f) (PreservesImage.iso F f)
    (PreservesCoimage.hom_coimageImageComparison F f)

Depends on / 依赖: Arrow.isoMk, PreservesCoimage, PreservesCoimage.hom_coimageImageComparison, PreservesCoimage.iso, PreservesImage, PreservesImage.iso, hom_coimageImageComparison
-/
def PreservesCoimageImageComparison.iso :
    Arrow.mk (F.map (coimageImageComparison f)) ≅ Arrow.mk (coimageImageComparison (F.map f)) :=
  Arrow.isoMk' _ _ (PreservesCoimage.iso F f) (PreservesImage.iso F f)
    (PreservesCoimage.hom_coimageImageComparison F f)

end CategoryTheory.Abelian
