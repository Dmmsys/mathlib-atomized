/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.TFAE

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* A short complex `S` is exact iff `imageSubobject S.f = kernelSubobject S.g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `Exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π f = 0` iff `Exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* A functor `F` such that for all `S`, we have `S.Exact → (S.map F).Exact` preserves both
  finite limits and colimits.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex C)

attribute [local instance] hasEqualizers_of_hasKernels

/--
theorem `exact_iff_epi_imageToKernel'` / 定理 `exact_iff_epi_imageToKernel'`

English:
theorem exact_iff_epi_imageToKernel'
  statement: S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero)
  proof: by
  rw [S.exact_iff_epi_kernel_lift]
  have : factorThruImage S.f ≫ imageToKernel' S.f S.g S.zero = kernel.lift S.g S.f S.zero := by
    simp only [← cancel_mono (kernel.ι _), kernel.lift_ι, imageToKernel',
      Category.assoc, image.fac]
  constructor
  · intro
    exact epi_of_epi_fac this
  · i

中文:
定理 exact_iff_epi_imageToKernel'
  结论: S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero)
  证明: by
  rw [S.exact_iff_epi_kernel_lift]
  have : factorThruImage S.f ≫ imageToKernel' S.f S.g S.zero = kernel.lift S.g S.f S.zero := by
    simp only [← cancel_mono (kernel.ι _), kernel.lift_ι, imageToKernel',
      Category.assoc, image.fac]
  constructor
  · intro
    exact epi_of_epi_fac this
  · i

Depends on / 依赖: Category, Category.assoc, S.exact_iff_epi_kernel_lift, S.zero, cancel_mono, epi_comp, epi_of_epi_fac, exact_iff_epi_kernel_lift, factorThruImage, image.fac, imageToKernel, kernel, kernel.lift, kernel.lift_
-/
theorem exact_iff_epi_imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero) := by
  rw [S.exact_iff_epi_kernel_lift]
  have : factorThruImage S.f ≫ imageToKernel' S.f S.g S.zero = kernel.lift S.g S.f S.zero := by
    simp only [← cancel_mono (kernel.ι _), kernel.lift_ι, imageToKernel',
      Category.assoc, image.fac]
  constructor
  · intro
    exact epi_of_epi_fac this
  · intro
    rw [← this]
    apply epi_comp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `exact_iff_epi_imageToKernel` / 定理 `exact_iff_epi_imageToKernel`

English:
theorem exact_iff_epi_imageToKernel
  statement: S.Exact ↔ Epi (imageToKernel S.f S.g S.zero)
  proof: by
  rw [S.exact_iff_epi_imageToKernel']
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (imageSubobjectIso S.f).symm (kernelSubobjectIso S.g).symm

中文:
定理 exact_iff_epi_imageToKernel
  结论: S.Exact ↔ Epi (imageToKernel S.f S.g S.zero)
  证明: by
  rw [S.exact_iff_epi_imageToKernel']
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (imageSubobjectIso S.f).symm (kernelSubobjectIso S.g).symm

Depends on / 依赖: Arrow.isoMk, MorphismProperty, MorphismProperty.epimorphisms, S.exact_iff_epi_imageToKernel, arrow_mk_iso_iff, epimorphisms, exact_iff_epi_imageToKernel, imageSubobjectIso, kernelSubobjectIso
-/
theorem exact_iff_epi_imageToKernel : S.Exact ↔ Epi (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel']
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (imageSubobjectIso S.f).symm (kernelSubobjectIso S.g).symm

/--
lemma `exact_iff_isIso_imageToKernel'` / 引理 `exact_iff_isIso_imageToKernel'`

English:
lemma exact_iff_isIso_imageToKernel'
  statement: S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero)
  proof: by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply Limits.kernel.lift_mono

中文:
引理 exact_iff_isIso_imageToKernel'
  结论: S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero)
  证明: by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply Limits.kernel.lift_mono

Depends on / 依赖: Limits, Limits.kernel.lift_mono, S.exact_iff_epi_imageToKernel, exact_iff_epi_imageToKernel, iff_and_self, isIso_iff_mono_and_epi, kernel, lift_mono
-/
lemma exact_iff_isIso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero) := by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply Limits.kernel.lift_mono

/--
theorem `exact_iff_isIso_imageToKernel` / 定理 `exact_iff_isIso_imageToKernel`

English:
theorem exact_iff_isIso_imageToKernel
  statement: S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero)
  proof: by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance

中文:
定理 exact_iff_isIso_imageToKernel
  结论: S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero)
  证明: by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance

Depends on / 依赖: S.exact_iff_epi_imageToKernel, exact_iff_epi_imageToKernel, infer_instance, isIso_of_mono_of_epi
-/
theorem exact_iff_isIso_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance

/--
lemma `Exact.isIso_imageToKernel` / 引理 `Exact.isIso_imageToKernel`

English:
lemma Exact.isIso_imageToKernel
  given: (hS : S.Exact)
  statement: IsIso (imageToKernel S.f S.g S.zero)
  proof: S.exact_iff_isIso_imageToKernel.1 hS

中文:
引理 Exact.isIso_imageToKernel
  条件: (hS : S.Exact)
  结论: IsIso (imageToKernel S.f S.g S.zero)
  证明: S.exact_iff_isIso_imageToKernel.1 hS

Depends on / 依赖: S.exact_iff_isIso_imageToKernel, exact_iff_isIso_imageToKernel
-/
lemma Exact.isIso_imageToKernel (hS : S.Exact) : IsIso (imageToKernel S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel.1 hS

/--
lemma `Exact.isIso_imageToKernel'` / 引理 `Exact.isIso_imageToKernel'`

English:
lemma Exact.isIso_imageToKernel'
  given: (hS : S.Exact)
  statement: IsIso (imageToKernel' S.f S.g S.zero)
  proof: S.exact_iff_isIso_imageToKernel'.1 hS

中文:
引理 Exact.isIso_imageToKernel'
  条件: (hS : S.Exact)
  结论: IsIso (imageToKernel' S.f S.g S.zero)
  证明: S.exact_iff_isIso_imageToKernel'.1 hS

Depends on / 依赖: Fintype, Fintype.ofEquiv, InducedCategory, InducedCategory.homEquiv.symm, S.exact_iff_isIso_imageToKernel, exact_iff_isIso_imageToKernel, homEquiv, ofEquiv
-/
lemma Exact.isIso_imageToKernel' (hS : S.Exact) : IsIso (imageToKernel' S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel'.1 hS

/--
theorem `exact_iff_image_eq_kernel` / 定理 `exact_iff_image_eq_kernel`

English:
theorem exact_iff_image_eq_kernel
  statement: S.Exact ↔ imageSubobject S.f = kernelSubobject S.g
  proof: by
  rw [exact_iff_isIso_imageToKernel]
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

中文:
定理 exact_iff_image_eq_kernel
  结论: S.Exact ↔ imageSubobject S.f = kernelSubobject S.g
  证明: by
  rw [exact_iff_isIso_imageToKernel]
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

Depends on / 依赖: S.zero, Subobject, Subobject.eq_of_comm, Subobject.ofLE, eq_of_comm, exact_iff_isIso_imageToKernel, h.ge, imageToKernel
-/
theorem exact_iff_image_eq_kernel : S.Exact ↔ imageSubobject S.f = kernelSubobject S.g := by
  rw [exact_iff_isIso_imageToKernel]
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exact_iff_of_forks` / 定理 `exact_iff_of_forks`

English:
theorem exact_iff_of_forks
  statement: {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelCofork S.f}
  proof: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero]
  let e₁ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hg
  let e₂ := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hf
  have : cg.ι ≫ cf.π = e₁.inv ≫ kernel.ι S.g ≫ cokernel.π S.f ≫ e₂.hom := by
    have eq₁ := IsLimit.conePoi

中文:
定理 exact_iff_of_forks
  结论: {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelCofork S.f}
  证明: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero]
  let e₁ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hg
  let e₂ := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hf
  have : cg.ι ≫ cf.π = e₁.inv ≫ kernel.ι S.g ≫ cokernel.π S.f ≫ e₂.hom := by
    have eq₁ := IsLimit.conePoi

Depends on / 依赖: Category, Category.assoc, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.conePointUniqueUpToIso_inv_comp, coconePointUniqueUpToIso, cokernel, cokernelIsCokernel, comp_coconePointUniqueUpToIso_hom, conePointUniqueUpToIso, conePointUniqueUpToIso_inv_comp, kernel, kernelIsKernel
-/
theorem exact_iff_of_forks {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelCofork S.f}
    (hf : IsColimit cf) : S.Exact ↔ cg.ι ≫ cf.π = 0 := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero]
  let e₁ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hg
  let e₂ := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hf
  have : cg.ι ≫ cf.π = e₁.inv ≫ kernel.ι S.g ≫ cokernel.π S.f ≫ e₂.hom := by
    have eq₁ := IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hg (.zero)
    have eq₂ := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hf (.one)
    dsimp at eq₁ eq₂
    rw [← eq₁]; rw [← eq₂]; rw [Category.assoc]
  rw [this]; rw [IsIso.comp_left_eq_zero e₁.inv]; rw [← Category.assoc]; rw [IsIso.comp_right_eq_zero _ e₂.hom]

variable {S}

/--
Definition of `Exact.isLimitImage` / `Exact.isLimitImage` 的定义

English:
definition Exact.isLimitImage
  signature: (h : S.Exact)
  body: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu => kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by simp)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift

中文:
定义 Exact.isLimitImage
  签名: (h : S.Exact)
  定义体: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu => kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by simp)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift

Depends on / 依赖: Abelian, Abelian.image, Category, Category.assoc, IsLimit, KernelFork, KernelFork.IsLimit.of, cancel_mono, cokernel, comp_zero, kernel, kernel.lift, kernel.lift_
-/
def Exact.isLimitImage (h : S.Exact) :
    IsLimit (KernelFork.ofι (Abelian.image.ι S.f)
      (Abelian.image_ι_comp_eq_zero S.zero) : KernelFork S.g) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu => kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by simp)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift_ι])

/--
Definition of `Exact.isLimitImage'` / `Exact.isLimitImage'` 的定义

English:
definition Exact.isLimitImage'
  signature: (h : S.Exact)
  body: IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm IsImage.lift_fac _ _

中文:
定义 Exact.isLimitImage'
  签名: (h : S.Exact)
  定义体: IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm IsImage.lift_fac _ _

Depends on / 依赖: Abelian, Abelian.imageIsoImage, IsImage, IsImage.lift_fac, IsKernel, IsKernel.isoKernel, h.isLimitImage, imageIsoImage, isLimitImage, isoKernel, lift_fac
-/
def Exact.isLimitImage' (h : S.Exact) :
    IsLimit (KernelFork.ofι (Limits.image.ι S.f)
      (image_ι_comp_eq_zero S.zero) : KernelFork S.g) :=
IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm IsImage.lift_fac _ _

/--
Definition of `Exact.isColimitCoimage` / `Exact.isColimitCoimage` 的定义

English:
definition Exact.isColimitCoimage
  signature: (h : S.Exact)
  body: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by simp) ?_
  intro _ _ _ _ hm
  ext
  rw [hm]; rw [cokernel.π_desc]

中文:
定义 Exact.isColimitCoimage
  签名: (h : S.Exact)
  定义体: by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by simp) ?_
  intro _ _ _ _ hm
  ext
  rw [hm]; rw [cokernel.π_desc]

Depends on / 依赖: Category, Category.assoc, CokernelCofork, CokernelCofork.IsColimit.of, IsColimit, cokernel, cokernel.desc, kernel, zero_comp
-/
def Exact.isColimitCoimage (h : S.Exact) :
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero) :
        CokernelCofork S.f) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by simp) ?_
  intro _ _ _ _ hm
  ext
  rw [hm]; rw [cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Exact.isColimitImage` / `Exact.isColimitImage` 的定义

English:
definition Exact.isColimitImage
  signature: (h : S.Exact)
  body: IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g)
(cancel_mono (Limits.image.ι S.g)).1 by simp

中文:
定义 Exact.isColimitImage
  签名: (h : S.Exact)
  定义体: IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g)
(cancel_mono (Limits.image.ι S.g)).1 by simp

Depends on / 依赖: Abelian, Abelian.coimageIsoImage, IsCokernel, IsCokernel.cokernelIso, Limits, Limits.image, cancel_mono, coimageIsoImage, cokernelIso, h.isColimitCoimage, isColimitCoimage
-/
def Exact.isColimitImage (h : S.Exact) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage S.g)
        (comp_factorThruImage_eq_zero S.zero)) :=
IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g)
(cancel_mono (Limits.image.ι S.g)).1 by simp

/--
theorem `exact_kernel` / 定理 `exact_kernel`

English:
theorem exact_kernel
  given: {X Y : C} (f : X ⟶ Y)
  proof: exact_of_f_is_kernel _ (kernelIsKernel f)

中文:
定理 exact_kernel
  条件: {X Y : C} (f : X ⟶ Y)
  证明: exact_of_f_is_kernel _ (kernelIsKernel f)

Depends on / 依赖: exact_of_f_is_kernel, kernelIsKernel
-/
theorem exact_kernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι f) f (by simp)).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)

/--
theorem `exact_cokernel` / 定理 `exact_cokernel`

English:
theorem exact_cokernel
  given: {X Y : C} (f : X ⟶ Y)
  proof: exact_of_g_is_cokernel _ (cokernelIsCokernel f)

中文:
定理 exact_cokernel
  条件: {X Y : C} (f : X ⟶ Y)
  证明: exact_of_g_is_cokernel _ (cokernelIsCokernel f)

Depends on / 依赖: cokernelIsCokernel, exact_of_g_is_cokernel
-/
theorem exact_cokernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (cokernel.π f) (by simp)).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

variable (S)

/--
theorem `exact_iff_exact_image_ι` / 定理 `exact_iff_exact_image_ι`

English:
theorem exact_iff_exact_image_ι
  proof: ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }

中文:
定理 exact_iff_exact_image_ι
  证明: ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }

Depends on / 依赖: Abelian, Abelian.factorThruImage, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, exact_iff_of_epi_of_isIso_of_mono, factorThruImage
-/
theorem exact_iff_exact_image_ι :
    S.Exact ↔ (ShortComplex.mk (Abelian.image.ι S.f) S.g
      (Abelian.image_ι_comp_eq_zero S.zero)).Exact :=
  ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }

/--
theorem `exact_iff_exact_coimage_π` / 定理 `exact_iff_exact_coimage_π`

English:
theorem exact_iff_exact_coimage_π
  proof: by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

中文:
定理 exact_iff_exact_coimage_π
  证明: by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

Depends on / 依赖: Abelian, Abelian.factorThruCoimage, Finite, Finite.of_equiv, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, discreteEquiv, discreteEquiv.symm, exact_iff_of_epi_of_isIso_of_mono, factorThruCoimage, of_equiv
-/
theorem exact_iff_exact_coimage_π :
    S.Exact ↔ (ShortComplex.mk S.f (Abelian.coimage.π S.g)
      (Abelian.comp_coimage_π_eq_zero S.zero)).Exact := by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

end ShortComplex

section

open List in
/--
theorem `Abelian.tfae_mono` / 定理 `Abelian.tfae_mono`

English:
theorem Abelian.tfae_mono
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: by
  tfae_have 2 -> 1 := mono_of_kernel_ι_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_mono f, kernel.condition, zero_comp]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_mono _ (by simp)
  tfae_finish

中文:
定理 Abelian.tfae_mono
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: by
  tfae_have 2 -> 1 := mono_of_kernel_ι_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_mono f, kernel.condition, zero_comp]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_mono _ (by simp)
  tfae_finish

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_mono, cancel_mono, condition, exact_iff_mono, kernel, kernel.condition, tfae_finish, tfae_have, zero_comp
-/
theorem Abelian.tfae_mono {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Mono f, kernel.ι f = 0, (ShortComplex.mk (0 : Z ⟶ X) f zero_comp).Exact] := by
  tfae_have 2 -> 1 := mono_of_kernel_ι_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_mono f, kernel.condition, zero_comp]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_mono _ (by simp)
  tfae_finish

open List in
/--
theorem `Abelian.tfae_epi` / 定理 `Abelian.tfae_epi`

English:
theorem Abelian.tfae_epi
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: by
  tfae_have 2 -> 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

中文:
定理 Abelian.tfae_epi
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: by
  tfae_have 2 -> 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_epi, cancel_epi, cokernel, cokernel.condition, comp_zero, condition, exact_iff_epi, tfae_finish, tfae_have
-/
theorem Abelian.tfae_epi {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Epi f, cokernel.π f = 0, (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).Exact] := by
  tfae_have 2 -> 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 -> 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

end

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflects_exact_of_faithful` / 引理 `reflects_exact_of_faithful`

English:
lemma reflects_exact_of_faithful
  given: [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact)
  proof: by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  apply F.zero_of_map_zero
  obtain ⟨k, hk⟩ :=
    kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
      (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
  obtain ⟨l, hl⟩ :=
    coker

中文:
引理 reflects_exact_of_faithful
  条件: [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact)
  证明: by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  apply F.zero_of_map_zero
  obtain ⟨k, hk⟩ :=
    kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
      (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
  obtain ⟨l, hl⟩ :=
    coker

Depends on / 依赖: Category, Category.assoc, CategoryTheory, CategoryTheory.Functor.map_zero, F.map, F.map_comp, F.zero_of_map_zero, FinCategory, FinCategory.mk, Fintype, Fintype.ofFinite, Functor, ShortComplex, ShortComplex.exact_iff_kernel_, cokernel, cokernel.condition, cokernel.desc, condition, kernel, kernel.condition
-/
lemma reflects_exact_of_faithful [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact) :
    S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  apply F.zero_of_map_zero
  obtain ⟨k, hk⟩ :=
    kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
      (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
  obtain ⟨l, hl⟩ :=
    cokernel.desc' (F.map S.f) (F.map (cokernel.π S.f))
      (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
  rw [F.map_comp]; rw [← hl]; rw [← hk]; rw [Category.assoc]; rw [reassoc_of% hS]; rw [zero_comp]; rw [comp_zero]

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [Abelian A] [Abelian B]
variable (L : A ⥤ B)

section

variable [L.PreservesZeroMorphisms]
variable (hL : forall (S : ShortComplex A), S.Exact -> (S.map L).Exact)
include hL

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
/--
theorem `preservesMonomorphisms_of_map_exact` / 定理 `preservesMonomorphisms_of_map_exact`

English:
theorem preservesMonomorphisms_of_map_exact
  statement: L.PreservesMonomorphisms where
  proof: by
    apply ((Abelian.tfae_mono (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_mono f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

中文:
定理 preservesMonomorphisms_of_map_exact
  结论: L.PreservesMonomorphisms where
  证明: by
    apply ((Abelian.tfae_mono (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_mono f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Abelian, Abelian.tfae_mono, Iso.refl, L.map, L.obj, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, exact_of_iso, tfae_mono
-/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_mono (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_mono f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `preservesEpimorphisms_of_map_exact` / 定理 `preservesEpimorphisms_of_map_exact`

English:
theorem preservesEpimorphisms_of_map_exact
  statement: L.PreservesEpimorphisms where
  proof: by
    apply ((Abelian.tfae_epi (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_epi f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

中文:
定理 preservesEpimorphisms_of_map_exact
  结论: L.PreservesEpimorphisms where
  证明: by
    apply ((Abelian.tfae_epi (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_epi f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Abelian, Abelian.tfae_epi, Iso.refl, L.map, L.obj, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, exact_of_iso, tfae_epi
-/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_epi (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_epi f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesHomology_of_map_exact` / 引理 `preservesHomology_of_map_exact`

English:
lemma preservesHomology_of_map_exact
  statement: L.PreservesHomology where
  proof: by
    have := preservesEpimorphisms_of_map_exact _ hL
    apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    apply (CokernelCofork.isColimitMapCoconeEquiv _ L).2
    have : Epi ((ShortComplex.mk _ _ (cokernel.condition f)).map L).g := by
      dsimp
      infer_instance
 

中文:
引理 preservesHomology_of_map_exact
  结论: L.PreservesHomology where
  证明: by
    have := preservesEpimorphisms_of_map_exact _ hL
    apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    apply (CokernelCofork.isColimitMapCoconeEquiv _ L).2
    have : Epi ((ShortComplex.mk _ _ (cokernel.condition f)).map L).g := by
      dsimp
      infer_instance
 

Depends on / 依赖: CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, ShortComplex, ShortComplex.exact_of_g_is_cokernel, ShortComplex.mk, cokernel, cokernel.condition, cokernelIsCokernel, condition, exact_of_g_is_cokernel, gIsCokernel, infer_instance, isColimitMapCoconeEquiv, preservesColimit_of_preserves_colimit_cocone, preservesEpimorphisms_of_map_exact, preservesKernels, preservesLimit, preservesMonomorphisms_of_map_exact
-/
lemma preservesHomology_of_map_exact : L.PreservesHomology where
  preservesCokernels X Y f := by
    have := preservesEpimorphisms_of_map_exact _ hL
    apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    apply (CokernelCofork.isColimitMapCoconeEquiv _ L).2
    have : Epi ((ShortComplex.mk _ _ (cokernel.condition f)).map L).g := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (cokernel.condition f))
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))).gIsCokernel
  preservesKernels X Y f := by
    have := preservesMonomorphisms_of_map_exact _ hL
    apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    apply (KernelFork.isLimitMapConeEquiv _ L).2
    have : Mono ((ShortComplex.mk _ _ (kernel.condition f)).map L).f := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (kernel.condition f))
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))).fIsKernel

end

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesHomology_of_preservesMonos_and_cokernels` / 引理 `preservesHomology_of_preservesMonos_and_cokernels`

English:
lemma preservesHomology_of_preservesMonos_and_cokernels
  statement: [PreservesZeroMorphisms L]
  proof: by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map L ⟶ S.map L :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := L.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp]; rw [← L.

中文:
引理 preservesHomology_of_preservesMonos_and_cokernels
  结论: [PreservesZeroMorphisms L]
  证明: by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map L ⟶ S.map L :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := L.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp]; rw [← L.

Depends on / 依赖: Abelian, Abelian.comp_coimage_, Abelian.factorThruCoimage, Category, Category.id_comp, CokernelCofork, CokernelCofork.mapIsColimit, L.map, L.map_comp, S.exact_iff_exact_coimage_, S.map, S.zero, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.exact_of_g_is_cokernel, ShortComplex.mk, cokernel, exact_iff_of_epi_of_isIso_of_mono, exact_of_g_is_cokernel, factorThruCoimage
-/
lemma preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map L ⟶ S.map L :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := L.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp]; rw [← L.map_comp]; rw [cokernel.π_desc] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
  apply ShortComplex.exact_of_g_is_cokernel
  exact CokernelCofork.mapIsColimit _ ((S.exact_iff_exact_coimage_π).1 hS).gIsCokernel L

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesHomology_of_preservesEpis_and_kernels` / 引理 `preservesHomology_of_preservesEpis_and_kernels`

English:
lemma preservesHomology_of_preservesEpis_and_kernels
  statement: [PreservesZeroMorphisms L]
  proof: by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : S.map L ⟶ (ShortComplex.mk _ _ (Abelian.image_ι_comp_eq_zero S.zero)).map L :=
    { τ₁ := L.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [← L.map_

中文:
引理 preservesHomology_of_preservesEpis_and_kernels
  结论: [PreservesZeroMorphisms L]
  证明: by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : S.map L ⟶ (ShortComplex.mk _ _ (Abelian.image_ι_comp_eq_zero S.zero)).map L :=
    { τ₁ := L.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [← L.map_

Depends on / 依赖: Abelian, Abelian.factorThruImage, Abelian.image_, Category, Category.comp_id, KernelFork, KernelFork.mapIsLimit, L.map, L.map_comp, S.exact_iff_exact_image_, S.map, S.zero, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.exact_of_f_is_kernel, ShortComplex.mk, comp_id, exact_iff_of_epi_of_isIso_of_mono, exact_of_f_is_kernel, fIsKernel
-/
lemma preservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [forall {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : S.map L ⟶ (ShortComplex.mk _ _ (Abelian.image_ι_comp_eq_zero S.zero)).map L :=
    { τ₁ := L.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id]; rw [← L.map_comp]; rw [kernel.lift_ι] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.mapIsLimit _ ((S.exact_iff_exact_image_ι).1 hS).fIsKernel L

end

end Functor

end CategoryTheory
