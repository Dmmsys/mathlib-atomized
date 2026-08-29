/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The abelian image and coimage.

In an abelian category we usually want the image of a morphism `f` to be defined as
`kernel (cokernel.π f)`, and the coimage to be defined as `cokernel (kernel.ι f)`.

We make these definitions here, as `Abelian.image f` and `Abelian.coimage f`
(without assuming the category is actually abelian),
and later relate these to the usual categorical notions when in an abelian category.

There is a canonical morphism `coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f`.
Later we show that this is always an isomorphism in an abelian category,
and conversely a category with (co)kernels and finite products in which this morphism
is always an isomorphism is an abelian category.
-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {P Q : C} (f : P ⟶ Q)

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/--
Definition of `image` / `image` 的定义

English:
abbreviation image
  signature: : C
  body: kernel (cokernel.π f)

中文:
缩写 image
  签名: : C
  定义体: kernel (cokernel.π f)
-/
protected abbrev image : C :=
  kernel (cokernel.π f)

/--
Definition of `image.ι` / `image.ι` 的定义

English:
abbreviation image.ι
  signature: : Abelian.image f ⟶ Q
  body: kernel.ι (cokernel.π f)

中文:
缩写 image.ι
  签名: : Abelian.image f ⟶ Q
  定义体: kernel.ι (cokernel.π f)
-/
protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)

/--
Definition of `factorThruImage` / `factorThruImage` 的定义

English:
abbreviation factorThruImage
  signature: : P ⟶ Abelian.image f
  body: kernel.lift (cokernel.π f) f cokernel.condition f

中文:
缩写 factorThruImage
  签名: : P ⟶ Abelian.image f
  定义体: kernel.lift (cokernel.π f) f cokernel.condition f
-/
protected abbrev factorThruImage : P ⟶ Abelian.image f :=
kernel.lift (cokernel.π f) f cokernel.condition f

/--
theorem `image.fac` / 定理 `image.fac`

English:
theorem image.fac
  statement: Abelian.factorThruImage f ≫ image.ι f = f
  proof: kernel.lift_ι _ _ _

中文:
定理 image.fac
  结论: Abelian.factorThruImage f ≫ image.ι f = f
  证明: kernel.lift_ι _ _ _
-/
protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _

/--
Instance `mono_factorThruImage` / 实例 `mono_factorThruImage`

English:
instance mono_factorThruImage
  signature: [Mono f]
  body: mono_of_mono_fac image.fac f

中文:
实例 mono_factorThruImage
  签名: [Mono f]
  定义体: mono_of_mono_fac image.fac f

Depends on / 依赖: image.fac, mono_of_mono_fac
-/
instance mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f) :=
mono_of_mono_fac image.fac f

end Image

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/--
Definition of `coimage` / `coimage` 的定义

English:
abbreviation coimage
  signature: : C
  body: cokernel (kernel.ι f)

中文:
缩写 coimage
  签名: : C
  定义体: cokernel (kernel.ι f)
-/
protected abbrev coimage : C :=
  cokernel (kernel.ι f)

/--
Definition of `coimage.π` / `coimage.π` 的定义

English:
abbreviation coimage.π
  signature: : P ⟶ Abelian.coimage f
  body: cokernel.π (kernel.ι f)

中文:
缩写 coimage.π
  签名: : P ⟶ Abelian.coimage f
  定义体: cokernel.π (kernel.ι f)
-/
protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)

/--
Definition of `factorThruCoimage` / `factorThruCoimage` 的定义

English:
abbreviation factorThruCoimage
  signature: : Abelian.coimage f ⟶ Q
  body: cokernel.desc (kernel.ι f) f kernel.condition f

中文:
缩写 factorThruCoimage
  签名: : Abelian.coimage f ⟶ Q
  定义体: cokernel.desc (kernel.ι f) f kernel.condition f
-/
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
cokernel.desc (kernel.ι f) f kernel.condition f

/--
theorem `coimage.fac` / 定理 `coimage.fac`

English:
theorem coimage.fac
  statement: coimage.π f ≫ Abelian.factorThruCoimage f = f
  proof: cokernel.π_desc _ _ _

中文:
定理 coimage.fac
  结论: coimage.π f ≫ Abelian.factorThruCoimage f = f
  证明: cokernel.π_desc _ _ _
-/
protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _

/--
Instance `epi_factorThruCoimage` / 实例 `epi_factorThruCoimage`

English:
instance epi_factorThruCoimage
  signature: [Epi f]
  body: epi_of_epi_fac coimage.fac f

中文:
实例 epi_factorThruCoimage
  签名: [Epi f]
  定义体: epi_of_epi_fac coimage.fac f

Depends on / 依赖: coimage, coimage.fac, epi_of_epi_fac
-/
instance epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f) :=
epi_of_epi_fac coimage.fac f

end Coimage

section Comparison

variable [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian. -/
@[stacks 0107]
/--
Definition of `coimageImageComparison` / `coimageImageComparison` 的定义

English:
definition coimageImageComparison
  signature: : Abelian.coimage f ⟶ Abelian.image f
  body: cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

中文:
定义 coimageImageComparison
  签名: : Abelian.coimage f ⟶ Abelian.image f
  定义体: cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

Depends on / 依赖: cokernel, cokernel.desc, kernel, kernel.lift
-/
def coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

/--
Definition of `coimageImageComparison'` / `coimageImageComparison'` 的定义

English:
definition coimageImageComparison'
  signature: : Abelian.coimage f ⟶ Abelian.image f
  body: kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)

中文:
定义 coimageImageComparison'
  签名: : Abelian.coimage f ⟶ Abelian.image f
  定义体: kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)

Depends on / 依赖: cokernel, cokernel.desc, kernel, kernel.lift
-/
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)

/--
theorem `coimageImageComparison_eq_coimageImageComparison'` / 定理 `coimageImageComparison_eq_coimageImageComparison'`

English:
theorem coimageImageComparison_eq_coimageImageComparison'
  proof: by
  ext
  simp [coimageImageComparison, coimageImageComparison']

@[reassoc (attr := simp)]

中文:
定理 coimageImageComparison_eq_coimageImageComparison'
  证明: by
  ext
  simp [coimageImageComparison, coimageImageComparison']

@[reassoc (attr := simp)]

Depends on / 依赖: coimageImageComparison
-/
theorem coimageImageComparison_eq_coimageImageComparison' :
    coimageImageComparison f = coimageImageComparison' f := by
  ext
  simp [coimageImageComparison, coimageImageComparison']

@[reassoc (attr := simp)]
/--
theorem `coimage_image_factorisation` / 定理 `coimage_image_factorisation`

English:
theorem coimage_image_factorisation
  statement: coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
  proof: by
  simp [coimageImageComparison]

中文:
定理 coimage_image_factorisation
  结论: coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
  证明: by
  simp [coimageImageComparison]

Depends on / 依赖: coimageImageComparison
-/
theorem coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f := by
  simp [coimageImageComparison]

end Comparison

variable [HasKernels C] [HasCokernels C]

set_option backward.defeqAttrib.useBackward true in
/-- The coimage-image comparison morphism is functorial. -/
@[simps! obj map]
/--
Definition of `coimageImageComparisonFunctor` / `coimageImageComparisonFunctor` 的定义

English:
definition coimageImageComparisonFunctor
  signature: : Arrow C ⥤ Arrow C where
  body: Arrow.mk (coimageImageComparison f.hom)
  map {f g} η := Arrow.homMk
    (cokernel.map _ _ (kernel.map _ _ η.left η.right (by simp)) η.left (by simp))
    (kernel.map _ _ η.right (cokernel.map _ _ η.left η.right (by simp)) (by simp)) (by cat_disch)

中文:
定义 coimageImageComparisonFunctor
  签名: : Arrow C ⥤ Arrow C where
  定义体: Arrow.mk (coimageImageComparison f.hom)
  map {f g} η := Arrow.homMk
    (cokernel.map _ _ (kernel.map _ _ η.left η.right (by simp)) η.left (by simp))
    (kernel.map _ _ η.right (cokernel.map _ _ η.left η.right (by simp)) (by simp)) (by cat_disch)

Depends on / 依赖: Arrow.mk, coimageImageComparison, f.hom
-/
def coimageImageComparisonFunctor : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (coimageImageComparison f.hom)
  map {f g} η := Arrow.homMk
    (cokernel.map _ _ (kernel.map _ _ η.left η.right (by simp)) η.left (by simp))
    (kernel.map _ _ η.right (cokernel.map _ _ η.left η.right (by simp)) (by simp)) (by cat_disch)

end CategoryTheory.Abelian
