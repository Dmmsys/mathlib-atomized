/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : imageSubobject f ≤ kernelSubobject g`
(assuming the appropriate images and kernels exist).

`imageToKernel f g w` is the corresponding morphism between objects in `C`.

-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/--
theorem `image_le_kernel` / 定理 `image_le_kernel`

English:
theorem image_le_kernel
  given: (w : f ≫ g = 0)
  statement: imageSubobject f <= kernelSubobject g
  proof: imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

中文:
定理 image_le_kernel
  条件: (w : f ≫ g = 0)
  结论: imageSubobject f <= kernelSubobject g
  证明: imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.ofNullHomotopic, imageSubobject_le_mk, kernel, kernel.lift, leftHomologyMap, ofNullHomotopic
-/
theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f <= kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

/--
Definition of `imageToKernel` / `imageToKernel` 的定义

English:
definition imageToKernel
  signature: (w : f ≫ g = 0)
  body: Subobject.ofLE _ _ (image_le_kernel _ _ w)

中文:
定义 imageToKernel
  签名: (w : f ≫ g = 0)
  定义体: Subobject.ofLE _ _ (image_le_kernel _ _ w)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.ofNullHomotopic, Subobject, Subobject.ofLE, image_le_kernel, ofNullHomotopic, rightHomologyMap
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)

instance (w : f ≫ g = 0) : Mono (imageToKernel f g w) := by
  dsimp only [imageToKernel]
  infer_instance

/-- Prefer `imageToKernel`. -/
@[simp]
/--
theorem `subobject_ofLE_as_imageToKernel` / 定理 `subobject_ofLE_as_imageToKernel`

English:
theorem subobject_ofLE_as_imageToKernel
  given: (w : f ≫ g = 0) (h)
  proof: rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 subobject_ofLE_as_imageToKernel
  条件: (w : f ≫ g = 0) (h)
  证明: rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: _nullHomotopic, leftHomologyMap
-/
theorem subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) :
    Subobject.ofLE (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `imageToKernel_arrow` / 定理 `imageToKernel_arrow`

English:
theorem imageToKernel_arrow
  given: (w : f ≫ g = 0)
  proof: by
  simp [imageToKernel]

中文:
定理 imageToKernel_arrow
  条件: (w : f ≫ g = 0)
  证明: by
  simp [imageToKernel]

Depends on / 依赖: imageToKernel
-/
theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
/--
theorem `factorThruImageSubobject_comp_imageToKernel` / 定理 `factorThruImageSubobject_comp_imageToKernel`

English:
theorem factorThruImageSubobject_comp_imageToKernel
  given: (w : f ≫ g = 0)
  proof: by
  ext
  simp

中文:
定理 factorThruImageSubobject_comp_imageToKernel
  条件: (w : f ≫ g = 0)
  证明: by
  ext
  simp
-/
theorem factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w := by
  ext
  simp

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
/--
theorem `imageToKernel_zero_left` / 定理 `imageToKernel_zero_left`

English:
theorem imageToKernel_zero_left
  given: [HasKernels V] [HasZeroObject V] {w}
  proof: by
  ext
  simp

中文:
定理 imageToKernel_zero_left
  条件: [有Kernels V] [有ZeroObject V] {w}
  证明: by
  ext
  simp
-/
theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp

/--
theorem `imageToKernel_zero_right` / 定理 `imageToKernel_zero_right`

English:
theorem imageToKernel_zero_right
  given: [HasImages V] {w}
  proof: by
  simp

中文:
定理 imageToKernel_zero_right
  条件: [有Images V] {w}
  证明: by
  simp
-/
theorem imageToKernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w =
      (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow := by
  simp

section

variable [HasKernels V] [HasImages V]

/--
theorem `imageToKernel_comp_right` / 定理 `imageToKernel_comp_right`

English:
theorem imageToKernel_comp_right
  given: {D : V} (h : C ⟶ D) (w : f ≫ g = 0)
  proof: by
  ext
  simp

中文:
定理 imageToKernel_comp_right
  条件: {D : V} (h : C ⟶ D) (w : f ≫ g = 0)
  证明: by
  ext
  simp
-/
theorem imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h) (by simp [reassoc_of% w]) =
      imageToKernel f g w ≫ Subobject.ofLE _ _ (kernelSubobject_comp_le g h) := by
  ext
  simp

/--
theorem `imageToKernel_comp_left` / 定理 `imageToKernel_comp_left`

English:
theorem imageToKernel_comp_left
  given: {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0)
  proof: by
  ext
  simp

@[simp]

中文:
定理 imageToKernel_comp_left
  条件: {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0)
  证明: by
  ext
  simp

@[simp]
-/
theorem imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g (by simp [w]) =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g w := by
  ext
  simp

@[simp]
/--
theorem `imageToKernel_comp_mono` / 定理 `imageToKernel_comp_mono`

English:
theorem imageToKernel_comp_mono
  given: {D : V} (h : C ⟶ D) [Mono h] (w)
  proof: by
  ext
  simp

@[simp]

中文:
定理 imageToKernel_comp_mono
  条件: {D : V} (h : C ⟶ D) [单态射 h] (w)
  证明: by
  ext
  simp

@[simp]
-/
theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv := by
  ext
  simp

@[simp]
/--
theorem `imageToKernel_epi_comp` / 定理 `imageToKernel_epi_comp`

English:
theorem imageToKernel_epi_comp
  given: {Z : V} (h : Z ⟶ A) [Epi h] (w)
  proof: by
  ext
  simp

中文:
定理 imageToKernel_epi_comp
  条件: {Z : V} (h : Z ⟶ A) [满态射 h] (w)
  证明: by
  ext
  simp
-/
theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) := by
  ext
  simp

end

@[simp]
/--
theorem `imageToKernel_comp_hom_inv_comp` / 定理 `imageToKernel_comp_hom_inv_comp`

English:
theorem imageToKernel_comp_hom_inv_comp
  given: [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w)
  proof: by
  ext
  simp

中文:
定理 imageToKernel_comp_hom_inv_comp
  条件: [HasEqualizers V] [有Images V] {Z : V} {i : B ≅ Z} (w)
  证明: by
  ext
  simp
-/
theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv := by
  ext
  simp

open ZeroObject

/--
Instance `imageToKernel_epi_of_zero_of_mono` / 实例 `imageToKernel_epi_of_zero_of_mono`

English:
instance imageToKernel_epi_of_zero_of_mono
  signature: [HasKernels V] [HasZeroObject V] [Mono g]
  body: epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

中文:
实例 imageToKernel_epi_of_zero_of_mono
  签名: [有Kernels V] [有ZeroObject V] [单态射 g]
  定义体: epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

Depends on / 依赖: epi_of_target_iso_zero, kernel, kernel.ofMono, kernelSubobjectIso, ofMono
-/
instance imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi (imageToKernel (0 : A ⟶ B) g (by simp)) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

/--
Instance `imageToKernel_epi_of_epi_of_zero` / 实例 `imageToKernel_epi_of_epi_of_zero`

English:
instance imageToKernel_epi_of_epi_of_zero
  signature: [HasImages V] [Epi f]
  body: by
  simp only [imageToKernel_zero_right]
  have := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  infer_instance

中文:
实例 imageToKernel_epi_of_epi_of_zero
  签名: [有Images V] [满态射 f]
  定义体: by
  simp only [imageToKernel_zero_right]
  have := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  infer_instance

Depends on / 依赖: epi_image_of_epi, imageSubobject_arrow, imageToKernel_zero_right, infer_instance
-/
instance imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi (imageToKernel f (0 : B ⟶ C) (by simp)) := by
  simp only [imageToKernel_zero_right]
  have := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  infer_instance

end

section imageToKernel'

/-!
We provide a variant `imageToKernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

/--
Definition of `imageToKernel'` / `imageToKernel'` 的定义

English:
definition imageToKernel'
  signature: (w : f ≫ g = 0)
  body: kernel.lift g (image.ι f) by
    ext
    simpa using w

@[simp]

中文:
定义 imageToKernel'
  签名: (w : f ≫ g = 0)
  定义体: kernel.lift g (image.ι f) by
    ext
    simpa using w

@[simp]

Depends on / 依赖: kernel, kernel.lift
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
kernel.lift g (image.ι f) by
    ext
    simpa using w

@[simp]
/--
theorem `imageSubobjectIso_imageToKernel'` / 定理 `imageSubobjectIso_imageToKernel'`

English:
theorem imageSubobjectIso_imageToKernel'
  given: (w : f ≫ g = 0)
  proof: by
  ext
  simp [imageToKernel']

@[simp]

中文:
定理 imageSubobjectIso_imageToKernel'
  条件: (w : f ≫ g = 0)
  证明: by
  ext
  simp [imageToKernel']

@[simp]

Depends on / 依赖: imageToKernel
-/
theorem imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).hom ≫ imageToKernel' f g w =
      imageToKernel f g w ≫ (kernelSubobjectIso g).hom := by
  ext
  simp [imageToKernel']

@[simp]
/--
theorem `imageToKernel'_kernelSubobjectIso` / 定理 `imageToKernel'_kernelSubobjectIso`

English:
theorem imageToKernel'_kernelSubobjectIso
  given: (w : f ≫ g = 0)
  proof: by
  ext
  simp [imageToKernel']

中文:
定理 imageToKernel'_kernelSubobjectIso
  条件: (w : f ≫ g = 0)
  证明: by
  ext
  simp [imageToKernel']
-/
theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']

end imageToKernel'

end
