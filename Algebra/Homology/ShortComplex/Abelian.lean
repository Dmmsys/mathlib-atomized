/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Abelian categories have homology

In this file, it is shown that all short complexes `S` in abelian
categories have terms of type `S.HomologyData`.

The strategy of the proof is to study the morphism
`kernel.ι S.g ≫ cokernel.π S.f`. We show that there is a
`LeftHomologyData` for `S` for which the `H` field consists
of the coimage of `kernel.ι S.g ≫ cokernel.π S.f`, while
there is a `RightHomologyData` for which the `H` is the
image of `kernel.ι S.g ≫ cokernel.π S.f`. The fact that
these left and right homology data are compatible (i.e.
provide a `HomologyData`) is obtained by using the
coimage-image isomorphism in abelian categories.

We also provide a constructor `HomologyData.ofEpiMonoFactorisation`
which takes as an input an epi-mono factorization `kf.pt ⟶ H ⟶ cc.pt`
of `kf.ι ≫ cc.π` where `kf` is a limit kernel fork of `S.g` and
`cc` is a limit cokernel cofork of `S.f`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

namespace ShortComplex

/--
Definition of `abelianImageToKernel` / `abelianImageToKernel` 的定义

English:
definition abelianImageToKernel
  signature: : Abelian.image S.f ⟶ kernel S.g
  body: kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]

中文:
定义 abelianImageToKernel
  签名: : 交换.像 S.f ⟶ kernel S.g
  定义体: kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]

Depends on / 依赖: Abelian, Abelian.factorThruImage, Abelian.image, cancel_epi, comp_zero, factorThruImage, kernel, kernel.lift, kernel.lift_
-/
noncomputable def abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]
/--
lemma `abelianImageToKernel_comp_kernel_ι` / 引理 `abelianImageToKernel_comp_kernel_ι`

English:
lemma abelianImageToKernel_comp_kernel_ι
  proof: kernel.lift_ι _ _ _

中文:
引理 abelianImageToKernel_comp_kernel_ι
  证明: kernel.lift_ι _ _ _

Depends on / 依赖: kernel, kernel.lift_
-/
lemma abelianImageToKernel_comp_kernel_ι :
    S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f :=
  kernel.lift_ι _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.abelianImageToKernel
  body: mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc]

中文:
实例 :
  签名: 单态射 S.abelianImageToKernel
  定义体: mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc]

Depends on / 依赖: S.abelianImageToKernel_comp_kernel_, mono_of_mono_fac
-/
instance : Mono S.abelianImageToKernel :=
  mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc]
/--
lemma `abelianImageToKernel_comp_kernel_ι_comp_cokernel_π` / 引理 `abelianImageToKernel_comp_kernel_ι_comp_cokernel_π`

English:
lemma abelianImageToKernel_comp_kernel_ι_comp_cokernel_π
  proof: by
  simp

中文:
引理 abelianImageToKernel_comp_kernel_ι_comp_cokernel_π
  证明: by
  simp
-/
lemma abelianImageToKernel_comp_kernel_ι_comp_cokernel_π :
    S.abelianImageToKernel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  simp

/--
Definition of `abelianImageToKernelIsKernel` / `abelianImageToKernelIsKernel` 的定义

English:
definition abelianImageToKernelIsKernel
  signature: :
  body: KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
    (fun k hk => by simp only [← cancel_mono (kernel.ι S.g), assoc,
      abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])
    (fun k hk b hb => by simp only [← cancel_mono S.abelianImageToKernel,
      ← cancel_mono (kernel.ι S.g), hb, assoc, abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])

中文:
定义 abelianImageToKernelIsKernel
  签名: :
  定义体: KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
    (fun k hk => by simp only [← cancel_mono (kernel.ι S.g), assoc,
      abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])
    (fun k hk b hb => by simp only [← cancel_mono S.abelianImageToKernel,
      ← cancel_mono (kernel.ι S.g), hb, assoc, abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.of, S.abelianImageToKernel, abelianImageToKernel, cancel_mono, kernel, kernel.lift, kernel.lift_
-/
noncomputable def abelianImageToKernelIsKernel :
    IsLimit (KernelFork.ofι S.abelianImageToKernel
      S.abelianImageToKernel_comp_kernel_ι_comp_cokernel_π) :=
  KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
    (fun k hk => by simp only [← cancel_mono (kernel.ι S.g), assoc,
      abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])
    (fun k hk b hb => by simp only [← cancel_mono S.abelianImageToKernel,
      ← cancel_mono (kernel.ι S.g), hb, assoc, abelianImageToKernel_comp_kernel_ι, kernel.lift_ι])

namespace LeftHomologyData

/-- The canonical `LeftHomologyData` of a short complex `S` in an abelian category, for
which the `H` field is `Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)`. -/
@[simps]
/--
Definition of `ofAbelian` / `ofAbelian` 的定义

English:
definition ofAbelian
  signature: : S.LeftHomologyData
  body: by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = kernel.lift γ f' (by simp [γ, f']) ≫ kernel.ι γ := by rw [kernel.lift_ι]
  have wπ : f' ≫ cokernel.π (kernel.ι γ) = 0 := by
    rw [hf']
    simp only [assoc, cokernel.condition, comp_zero]
  let e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso S.abelianImageToKernelIsKernel (limit.isLimit _)
  have he : e.hom ≫ kernel.ι γ = S.abelianImageToKernel :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have fac : f' = Abelian.factorThruImage S.f ≫ e.hom ≫ kernel.ι γ := by
    rw [hf']; rw [he]
    simp only [γ, f', kernel.lift_ι, abelianImageToKernel, ← cancel_mono (kernel.ι S.g),
      assoc]
  have hπ : IsColimit (CokernelCofork.ofπ _ wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => cokernel.desc _ x (by
      simpa only [← cancel_epi e.hom, ← cancel_epi (Abelian.factorThruImage S.f),
        comp_zero, fac, assoc] using hx))
    (fun x hx => cokernel.π_desc _ _ _)
    (fun x hx b hb => coequalizer.hom_ext (by simp only [hb, cokernel.π_desc]))
  exact
    { K := kernel S.g,
      H := Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)
      i := kernel.ι _,
      π := cokernel.π _
      wi := kernel.condition _
      hi := kernelIsKernel _
      wπ := wπ
      hπ := hπ }

中文:
定义 ofAbelian
  签名: : S.LeftHomologyData
  定义体: by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = kernel.lift γ f' (by simp [γ, f']) ≫ kernel.ι γ := by rw [kernel.lift_ι]
  have wπ : f' ≫ cokernel.π (kernel.ι γ) = 0 := by
    rw [hf']
    simp only [assoc, cokernel.condition, comp_zero]
  let e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso S.abelianImageToKernelIsKernel (limit.isLimit _)
  have he : e.hom ≫ kernel.ι γ = S.abelianImageToKernel :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have fac : f' = Abelian.factorThruImage S.f ≫ e.hom ≫ kernel.ι γ := by
    rw [hf']; rw [he]
    simp only [γ, f', kernel.lift_ι, abelianImageToKernel, ← cancel_mono (kernel.ι S.g),
      assoc]
  have hπ : IsColimit (CokernelCofork.ofπ _ wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => cokernel.desc _ x (by
      simpa only [← cancel_epi e.hom, ← cancel_epi (Abelian.factorThruImage S.f),
        comp_zero, fac, assoc] using hx))
    (fun x hx => cokernel.π_desc _ _ _)
    (fun x hx b hb => coequalizer.hom_ext (by simp only [hb, cokernel.π_desc]))
  exact
    { K := kernel S.g,
      H := Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)
      i := kernel.ι _,
      π := cokernel.π _
      wi := kernel.condition _
      hi := kernelIsKernel _
      wπ := wπ
      hπ := hπ }

Depends on / 依赖: Abelian, Abelian.image, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.conePointUniqueUpToIso_hom_comp, S.abelianImageToKernel, S.abelianImageToKernelIsKernel, S.zero, abelianImageToKernel, abelianImageToKernelIsKernel, cokernel, cokernel.condition, comp_zero, condition, conePointUniqueUpToIso, conePointUniqueUpToIso_hom_comp, e.hom, isLimit, kernel, kernel.lift
-/
noncomputable def ofAbelian : S.LeftHomologyData := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = kernel.lift γ f' (by simp [γ, f']) ≫ kernel.ι γ := by rw [kernel.lift_ι]
  have wπ : f' ≫ cokernel.π (kernel.ι γ) = 0 := by
    rw [hf']
    simp only [assoc, cokernel.condition, comp_zero]
  let e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso S.abelianImageToKernelIsKernel (limit.isLimit _)
  have he : e.hom ≫ kernel.ι γ = S.abelianImageToKernel :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have fac : f' = Abelian.factorThruImage S.f ≫ e.hom ≫ kernel.ι γ := by
    rw [hf']; rw [he]
    simp only [γ, f', kernel.lift_ι, abelianImageToKernel, ← cancel_mono (kernel.ι S.g),
      assoc]
  have hπ : IsColimit (CokernelCofork.ofπ _ wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => cokernel.desc _ x (by
      simpa only [← cancel_epi e.hom, ← cancel_epi (Abelian.factorThruImage S.f),
        comp_zero, fac, assoc] using hx))
    (fun x hx => cokernel.π_desc _ _ _)
    (fun x hx b hb => coequalizer.hom_ext (by simp only [hb, cokernel.π_desc]))
  exact
    { K := kernel S.g,
      H := Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)
      i := kernel.ι _,
      π := cokernel.π _
      wi := kernel.condition _
      hi := kernelIsKernel _
      wπ := wπ
      hπ := hπ }

end LeftHomologyData

/--
Definition of `cokernelToAbelianCoimage` / `cokernelToAbelianCoimage` 的定义

English:
definition cokernelToAbelianCoimage
  signature: : cokernel S.f ⟶ Abelian.coimage S.g
  body: cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]

中文:
定义 cokernelToAbelianCoimage
  签名: : cokernel S.f ⟶ 交换.coimage S.g
  定义体: cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]

Depends on / 依赖: Abelian, Abelian.coimage, Abelian.factorThruCoimage, cancel_mono, coimage, cokernel, cokernel.desc, factorThruCoimage, zero_comp
-/
noncomputable def cokernelToAbelianCoimage : cokernel S.f ⟶ Abelian.coimage S.g :=
  cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]
/--
lemma `cokernel_π_comp_cokernelToAbelianCoimage` / 引理 `cokernel_π_comp_cokernelToAbelianCoimage`

English:
lemma cokernel_π_comp_cokernelToAbelianCoimage
  proof: cokernel.π_desc _ _ _

中文:
引理 cokernel_π_comp_cokernelToAbelianCoimage
  证明: cokernel.π_desc _ _ _

Depends on / 依赖: cokernel
-/
lemma cokernel_π_comp_cokernelToAbelianCoimage :
    cokernel.π S.f ≫ S.cokernelToAbelianCoimage = Abelian.coimage.π S.g :=
  cokernel.π_desc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.cokernelToAbelianCoimage
  body: epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage

中文:
实例 :
  签名: 满态射 S.cokernelToAbelianCoimage
  定义体: epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage

Depends on / 依赖: S.cokernel_, epi_of_epi_fac
-/
instance : Epi S.cokernelToAbelianCoimage :=
  epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage

/--
lemma `kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage` / 引理 `kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage`

English:
lemma kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage
  proof: by simp

中文:
引理 kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage
  证明: by simp
-/
lemma kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage :
    (kernel.ι S.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0 := by simp

/--
Definition of `cokernelToAbelianCoimageIsCokernel` / `cokernelToAbelianCoimageIsCokernel` 的定义

English:
definition cokernelToAbelianCoimageIsCokernel
  signature: :
  body: CokernelCofork.IsColimit.ofπ _ _
    (fun k hk => cokernel.desc _ (cokernel.π S.f ≫ k) (by simpa only [assoc] using hk))
    (fun k hk => by simp only [← cancel_epi (cokernel.π S.f),
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])
    (fun k hk b hb => by
      simp only [← cancel_epi S.cokernelToAbelianCoimage, ← cancel_epi (cokernel.π S.f), hb,
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])

中文:
定义 cokernelToAbelianCoimageIsCokernel
  签名: :
  定义体: CokernelCofork.IsColimit.ofπ _ _
    (fun k hk => cokernel.desc _ (cokernel.π S.f ≫ k) (by simpa only [assoc] using hk))
    (fun k hk => by simp only [← cancel_epi (cokernel.π S.f),
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])
    (fun k hk b hb => by
      simp only [← cancel_epi S.cokernelToAbelianCoimage, ← cancel_epi (cokernel.π S.f), hb,
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.of, IsColimit, S.cokernelToAbelianCoimage, cancel_epi, cokernel, cokernel.desc, cokernelToAbelianCoimage
-/
noncomputable def cokernelToAbelianCoimageIsCokernel :
    IsColimit (CokernelCofork.ofπ S.cokernelToAbelianCoimage
      S.kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun k hk => cokernel.desc _ (cokernel.π S.f ≫ k) (by simpa only [assoc] using hk))
    (fun k hk => by simp only [← cancel_epi (cokernel.π S.f),
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])
    (fun k hk b hb => by
      simp only [← cancel_epi S.cokernelToAbelianCoimage, ← cancel_epi (cokernel.π S.f), hb,
        cokernel_π_comp_cokernelToAbelianCoimage_assoc, cokernel.π_desc])

namespace RightHomologyData

/-- The canonical `RightHomologyData` of a short complex `S` in an abelian category, for
which the `H` field is `Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)`. -/
@[simps]
/--
Definition of `ofAbelian` / `ofAbelian` 的定义

English:
definition ofAbelian
  signature: : S.RightHomologyData
  body: by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let g' := cokernel.desc S.f S.g S.zero
  have hg' : g' = cokernel.π γ ≫ cokernel.desc γ g' (by simp [γ, g']) := by rw [cokernel.π_desc]
  have wι : kernel.ι (cokernel.π γ) ≫ g' = 0 := by rw [hg', kernel.condition_assoc, zero_comp]
  let e : cokernel γ ≅ Abelian.coimage S.g :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) S.cokernelToAbelianCoimageIsCokernel
  have he : cokernel.π γ ≫ e.hom = S.cokernelToAbelianCoimage :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one
  have fac : g' = cokernel.π γ ≫ e.hom ≫ Abelian.factorThruCoimage S.g := by
    rw [hg']; rw [reassoc_of% he]
    simp only [γ, g', cokernel.π_desc, ← cancel_epi (cokernel.π S.f),
      cokernel_π_comp_cokernelToAbelianCoimage_assoc]
  have hι : IsLimit (KernelFork.ofι _ wι) :=
    KernelFork.IsLimit.ofι _ _
      (fun x hx => kernel.lift _ x (by
        simpa only [← cancel_mono e.hom, ← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
          zero_comp, fac] using hx))
      (fun x hx => kernel.lift_ι _ _ _)
      (fun x hx b hb => equalizer.hom_ext (by simp only [hb, kernel.lift_ι]))
  exact
    { Q := cokernel S.f,
      H := Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)
      p := cokernel.π _
      ι := kernel.ι _
      wp := cokernel.condition _
      hp := cokernelIsCokernel _
      wι := wι
      hι := hι }

中文:
定义 ofAbelian
  签名: : S.RightHomologyData
  定义体: by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let g' := cokernel.desc S.f S.g S.zero
  have hg' : g' = cokernel.π γ ≫ cokernel.desc γ g' (by simp [γ, g']) := by rw [cokernel.π_desc]
  have wι : kernel.ι (cokernel.π γ) ≫ g' = 0 := by rw [hg', kernel.condition_assoc, zero_comp]
  let e : cokernel γ ≅ Abelian.coimage S.g :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) S.cokernelToAbelianCoimageIsCokernel
  have he : cokernel.π γ ≫ e.hom = S.cokernelToAbelianCoimage :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one
  have fac : g' = cokernel.π γ ≫ e.hom ≫ Abelian.factorThruCoimage S.g := by
    rw [hg']; rw [reassoc_of% he]
    simp only [γ, g', cokernel.π_desc, ← cancel_epi (cokernel.π S.f),
      cokernel_π_comp_cokernelToAbelianCoimage_assoc]
  have hι : IsLimit (KernelFork.ofι _ wι) :=
    KernelFork.IsLimit.ofι _ _
      (fun x hx => kernel.lift _ x (by
        simpa only [← cancel_mono e.hom, ← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
          zero_comp, fac] using hx))
      (fun x hx => kernel.lift_ι _ _ _)
      (fun x hx b hb => equalizer.hom_ext (by simp only [hb, kernel.lift_ι]))
  exact
    { Q := cokernel S.f,
      H := Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)
      p := cokernel.π _
      ι := kernel.ι _
      wp := cokernel.condition _
      hp := cokernelIsCokernel _
      wι := wι
      hι := hι }

Depends on / 依赖: Abelian, Abelian.coimage, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniq, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, S.cokernelToAbelianCoimage, S.cokernelToAbelianCoimageIsCokernel, S.zero, _assoc, cancel_epi, coconePointUniqueUpToIso, coimage, cokernel, cokernel.desc, cokernelToAbelianCoimage, cokernelToAbelianCoimageIsCokernel, colimit, colimit.isColimit
-/
noncomputable def ofAbelian : S.RightHomologyData := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let g' := cokernel.desc S.f S.g S.zero
  have hg' : g' = cokernel.π γ ≫ cokernel.desc γ g' (by simp [γ, g']) := by rw [cokernel.π_desc]
  have wι : kernel.ι (cokernel.π γ) ≫ g' = 0 := by rw [hg', kernel.condition_assoc, zero_comp]
  let e : cokernel γ ≅ Abelian.coimage S.g :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) S.cokernelToAbelianCoimageIsCokernel
  have he : cokernel.π γ ≫ e.hom = S.cokernelToAbelianCoimage :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one
  have fac : g' = cokernel.π γ ≫ e.hom ≫ Abelian.factorThruCoimage S.g := by
    rw [hg']; rw [reassoc_of% he]
    simp only [γ, g', cokernel.π_desc, ← cancel_epi (cokernel.π S.f),
      cokernel_π_comp_cokernelToAbelianCoimage_assoc]
  have hι : IsLimit (KernelFork.ofι _ wι) :=
    KernelFork.IsLimit.ofι _ _
      (fun x hx => kernel.lift _ x (by
        simpa only [← cancel_mono e.hom, ← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
          zero_comp, fac] using hx))
      (fun x hx => kernel.lift_ι _ _ _)
      (fun x hx b hb => equalizer.hom_ext (by simp only [hb, kernel.lift_ι]))
  exact
    { Q := cokernel S.f,
      H := Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)
      p := cokernel.π _
      ι := kernel.ι _
      wp := cokernel.condition _
      hp := cokernelIsCokernel _
      wι := wι
      hι := hι }

end RightHomologyData

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `HomologyData.ofAbelian` / `HomologyData.ofAbelian` 的定义

English:
definition HomologyData.ofAbelian
  signature: : S.HomologyData where
  body: LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)

中文:
定义 同调数据.ofAbelian
  签名: : S.同调数据 where
  定义体: LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofAbelian, ofAbelian
-/
noncomputable def HomologyData.ofAbelian : S.HomologyData where
  left := LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)

/--
Instance `_root_.CategoryTheory.categoryWithHomology_of_abelian` / 实例 `_root_.CategoryTheory.categoryWithHomology_of_abelian`

English:
instance _root_.CategoryTheory.categoryWithHomology_of_abelian
  signature: :
  body: HasHomology.mk' (HomologyData.ofAbelian S)

中文:
实例 _root_.范畴论.categoryWithHomology_of_abelian
  签名: :
  定义体: HasHomology.mk' (HomologyData.ofAbelian S)

Depends on / 依赖: HasHomology, HasHomology.mk, HomologyData, HomologyData.ofAbelian, ofAbelian
-/
instance _root_.CategoryTheory.categoryWithHomology_of_abelian :
    CategoryWithHomology C where
  hasHomology S := HasHomology.mk' (HomologyData.ofAbelian S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalMonoCategory (ShortComplex C)
  body: ⟨fun i _ => ⟨by
  refine NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimitOfIsLimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isLimitMapConeOfKernelForkOfι⟩⟩

中文:
实例 :
  签名: 是正规单态射范畴 (短复形 C)
  定义体: ⟨fun i _ => ⟨by
  refine NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimitOfIsLimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isLimitMapConeOfKernelForkOfι⟩⟩

Depends on / 依赖: Abelian, Abelian.isLimitMapConeOfKernelForkOf, NormalMono, NormalMono.mk, all_goals, cokernel, cokernel.condition, condition
-/
noncomputable instance : IsNormalMonoCategory (ShortComplex C) := ⟨fun i _ => ⟨by
  refine NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimitOfIsLimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isLimitMapConeOfKernelForkOfι⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalEpiCategory (ShortComplex C)
  body: ⟨fun p _ => ⟨by
  refine NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfIsColimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isColimitMapCoconeOfCokernelCoforkOfπ⟩⟩

中文:
实例 :
  签名: 是正规满态射范畴 (短复形 C)
  定义体: ⟨fun p _ => ⟨by
  refine NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfIsColimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isColimitMapCoconeOfCokernelCoforkOfπ⟩⟩

Depends on / 依赖: Abelian, Abelian.isColimitMapCoconeOfCokernelCoforkOf, NormalEpi, NormalEpi.mk, all_goals, condition, kernel, kernel.condition
-/
noncomputable instance : IsNormalEpiCategory (ShortComplex C) := ⟨fun p _ => ⟨by
  refine NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfIsColimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isColimitMapCoconeOfCokernelCoforkOfπ⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (ShortComplex C)

中文:
实例 :
  签名: 交换 (短复形 C)
-/
noncomputable instance : Abelian (ShortComplex C) where

attribute [local instance] strongEpi_of_epi

/--
Definition of `homologyIsoImageICyclesCompPOpcycles` / `homologyIsoImageICyclesCompPOpcycles` 的定义

English:
definition homologyIsoImageICyclesCompPOpcycles
  signature: :
  body: image.isoStrongEpiMono _ _ S.homology_π_ι

@[reassoc (attr := simp)]

中文:
定义 homologyIsoImageICyclesCompPOpcycles
  签名: :
  定义体: image.isoStrongEpiMono _ _ S.homology_π_ι

@[reassoc (attr := simp)]

Depends on / 依赖: S.homology_, image.isoStrongEpiMono, isoStrongEpiMono
-/
noncomputable def homologyIsoImageICyclesCompPOpcycles :
    S.homology ≅ image (S.iCycles ≫ S.pOpcycles) :=
  image.isoStrongEpiMono _ _ S.homology_π_ι

@[reassoc (attr := simp)]
/--
lemma `homologyIsoImageICyclesCompPOpcycles_ι` / 引理 `homologyIsoImageICyclesCompPOpcycles_ι`

English:
lemma homologyIsoImageICyclesCompPOpcycles_ι
  proof: image.isoStrongEpiMono_hom_comp_ι _ _ _

中文:
引理 homologyIsoImageICyclesCompPOpcycles_ι
  证明: image.isoStrongEpiMono_hom_comp_ι _ _ _

Depends on / 依赖: image.isoStrongEpiMono_hom_comp_
-/
lemma homologyIsoImageICyclesCompPOpcycles_ι :
    S.homologyIsoImageICyclesCompPOpcycles.hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      S.homologyι :=
  image.isoStrongEpiMono_hom_comp_ι _ _ _

namespace HomologyData

namespace ofEpiMonoFactorisation

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

/--
Definition of `isoImage` / `isoImage` 的定义

English:
definition isoImage
  signature: : H ≅ image (S.iCycles ≫ S.pOpcycles)
  body: by
  have : ((S.isoCyclesOfIsLimit hkf).inv ≫ π) ≫ ι ≫
    (S.isoOpcyclesOfIsColimit hcc).hom = S.iCycles ≫ S.pOpcycles := by
    simp [← reassoc_of% fac]
  exact image.isoStrongEpiMono _ _ this

@[reassoc (attr := simp)]

中文:
定义 isoImage
  签名: : H ≅ 像 (S.iCycles ≫ S.pOpcycles)
  定义体: by
  have : ((S.isoCyclesOfIsLimit hkf).inv ≫ π) ≫ ι ≫
    (S.isoOpcyclesOfIsColimit hcc).hom = S.iCycles ≫ S.pOpcycles := by
    simp [← reassoc_of% fac]
  exact image.isoStrongEpiMono _ _ this

@[reassoc (attr := simp)]

Depends on / 依赖: S.iCycles, S.isoCyclesOfIsLimit, S.isoOpcyclesOfIsColimit, S.pOpcycles, iCycles, image.isoStrongEpiMono, isoCyclesOfIsLimit, isoOpcyclesOfIsColimit, isoStrongEpiMono, pOpcycles, reassoc_of
-/
noncomputable def isoImage : H ≅ image (S.iCycles ≫ S.pOpcycles) := by
  have : ((S.isoCyclesOfIsLimit hkf).inv ≫ π) ≫ ι ≫
    (S.isoOpcyclesOfIsColimit hcc).hom = S.iCycles ≫ S.pOpcycles := by
    simp [← reassoc_of% fac]
  exact image.isoStrongEpiMono _ _ this

@[reassoc (attr := simp)]
/--
lemma `isoImage_ι` / 引理 `isoImage_ι`

English:
lemma isoImage_ι
  proof: by
  apply image.isoStrongEpiMono_hom_comp_ι
  simp [← reassoc_of% fac]

中文:
引理 isoImage_ι
  证明: by
  apply image.isoStrongEpiMono_hom_comp_ι
  simp [← reassoc_of% fac]

Depends on / 依赖: image.isoStrongEpiMono_hom_comp_, reassoc_of
-/
lemma isoImage_ι :
    (isoImage S hkf hcc fac).hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  apply image.isoStrongEpiMono_hom_comp_ι
  simp [← reassoc_of% fac]

/--
Definition of `isoHomology` / `isoHomology` 的定义

English:
definition isoHomology
  signature: : H ≅ S.homology
  body: isoImage S hkf hcc fac ≪≫ S.homologyIsoImageICyclesCompPOpcycles.symm

@[reassoc (attr := simp)]

中文:
定义 isoHomology
  签名: : H ≅ S.homology
  定义体: isoImage S hkf hcc fac ≪≫ S.homologyIsoImageICyclesCompPOpcycles.symm

@[reassoc (attr := simp)]

Depends on / 依赖: S.homologyIsoImageICyclesCompPOpcycles.symm, homologyIsoImageICyclesCompPOpcycles, isoImage
-/
noncomputable def isoHomology : H ≅ S.homology :=
  isoImage S hkf hcc fac ≪≫ S.homologyIsoImageICyclesCompPOpcycles.symm

@[reassoc (attr := simp)]
/--
lemma `π_comp_isoHomology_hom` / 引理 `π_comp_isoHomology_hom`

English:
lemma π_comp_isoHomology_hom
  proof: by
  dsimp [isoHomology]
  simp [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom),
    ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    ← reassoc_of% fac]

@[reassoc (attr := simp)]

中文:
引理 π_comp_isoHomology_hom
  证明: by
  dsimp [isoHomology]
  simp [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom),
    ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    ← reassoc_of% fac]

@[reassoc (attr := simp)]

Depends on / 依赖: S.homologyIsoImageICyclesCompPOpcycles.hom, S.iCycles, S.pOpcycles, cancel_mono, homologyIsoImageICyclesCompPOpcycles, iCycles, isoHomology, pOpcycles, reassoc_of
-/
lemma π_comp_isoHomology_hom :
    π ≫ (isoHomology S hkf hcc fac).hom = (S.isoCyclesOfIsLimit hkf).hom ≫ S.homologyπ := by
  dsimp [isoHomology]
  simp [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom),
    ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    ← reassoc_of% fac]

@[reassoc (attr := simp)]
/--
lemma `isoHomology_hom_comp_ι` / 引理 `isoHomology_hom_comp_ι`

English:
lemma isoHomology_hom_comp_ι
  proof: by
  simp [← cancel_epi S.homologyπ, ← cancel_epi (S.isoCyclesOfIsLimit hkf).hom,
    ← π_comp_isoHomology_hom_assoc S hkf hcc fac, ← fac]

中文:
引理 isoHomology_hom_comp_ι
  证明: by
  simp [← cancel_epi S.homologyπ, ← cancel_epi (S.isoCyclesOfIsLimit hkf).hom,
    ← π_comp_isoHomology_hom_assoc S hkf hcc fac, ← fac]

Depends on / 依赖: S.homology, S.isoCyclesOfIsLimit, cancel_epi, isoCyclesOfIsLimit
-/
lemma isoHomology_hom_comp_ι :
    (isoHomology S hkf hcc fac).inv ≫ ι = S.homologyι ≫ (S.isoOpcyclesOfIsColimit hcc).inv := by
  simp [← cancel_epi S.homologyπ, ← cancel_epi (S.isoCyclesOfIsLimit hkf).hom,
    ← π_comp_isoHomology_hom_assoc S hkf hcc fac, ← fac]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `f'_eq` / 引理 `f'_eq`

English:
lemma f'_eq
  proof: by
  have := Fork.IsLimit.mono hkf
  simp [← cancel_mono kf.ι]

中文:
引理 f'_eq
  证明: by
  have := Fork.IsLimit.mono hkf
  simp [← cancel_mono kf.ι]

Depends on / 依赖: Fork.IsLimit.mono, IsLimit, cancel_mono
-/
lemma f'_eq :
    hkf.lift (KernelFork.ofι S.f S.zero) =
      S.toCycles ≫ (S.isoCyclesOfIsLimit hkf).inv := by
  have := Fork.IsLimit.mono hkf
  simp [← cancel_mono kf.ι]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `g'_eq` / 引理 `g'_eq`

English:
lemma g'_eq
  statement: hcc.desc (CokernelCofork.ofπ S.g S.zero) =
  proof: by
  have := Cofork.IsColimit.epi hcc
  simp [← cancel_epi cc.π]

@[reassoc (attr := simp)]

中文:
引理 g'_eq
  结论: hcc.desc (余核余叉.ofπ S.g S.zero) =
  证明: by
  have := Cofork.IsColimit.epi hcc
  simp [← cancel_epi cc.π]

@[reassoc (attr := simp)]

Depends on / 依赖: Cofork, Cofork.IsColimit.epi, IsColimit, cancel_epi
-/
lemma g'_eq : hcc.desc (CokernelCofork.ofπ S.g S.zero) =
    (S.isoOpcyclesOfIsColimit hcc).hom ≫ S.fromOpcycles := by
  have := Cofork.IsColimit.epi hcc
  simp [← cancel_epi cc.π]

@[reassoc (attr := simp)]
/--
lemma `homologyπ_isoHomology_inv` / 引理 `homologyπ_isoHomology_inv`

English:
lemma homologyπ_isoHomology_inv
  proof: by
  simp only [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 homologyπ_isoHomology_inv
  证明: by
  simp only [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, isoHomology
-/
lemma homologyπ_isoHomology_inv :
    S.homologyπ ≫ (isoHomology S hkf hcc fac).inv = (S.isoCyclesOfIsLimit hkf).inv ≫ π := by
  simp only [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `isoHomology_inv_homologyι` / 引理 `isoHomology_inv_homologyι`

English:
lemma isoHomology_inv_homologyι
  proof: by
  rw [← cancel_mono (S.isoOpcyclesOfIsColimit hcc).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← isoHomology_hom_comp_ι S hkf hcc fac]; rw [Iso.hom_inv_id_assoc]

中文:
引理 isoHomology_inv_homologyι
  证明: by
  rw [← cancel_mono (S.isoOpcyclesOfIsColimit hcc).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← isoHomology_hom_comp_ι S hkf hcc fac]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, S.isoOpcyclesOfIsColimit, cancel_mono, comp_id, hom_inv_id, hom_inv_id_assoc, isoOpcyclesOfIsColimit
-/
lemma isoHomology_inv_homologyι :
    (isoHomology S hkf hcc fac).hom ≫ S.homologyι =
    ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  rw [← cancel_mono (S.isoOpcyclesOfIsColimit hcc).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← isoHomology_hom_comp_ι S hkf hcc fac]; rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`.
This is the left homology data expressing `H` as the homology of `S`. -/
@[simps]
/--
Definition of `leftHomologyData` / `leftHomologyData` 的定义

English:
definition leftHomologyData
  signature: : S.LeftHomologyData where
  body: kf.pt
  H := H
  i := kf.ι
  π := π
  wi := KernelFork.condition kf
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := by
    dsimp
    rw [← cancel_mono (isoHomology S hkf hcc fac).hom]; rw [assoc]; rw [assoc]; rw [id_comp]; rw [π_comp_isoHomology_hom]; rw [zero_comp]; rw [f'_eq]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [toCycles_comp_homologyπ]
  hπ := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsCokernel
    · exact parallelPair.ext (Iso.refl _) (S.isoCyclesOfIsLimit hkf)
    · exact Cofork.ext (isoHomology S hkf hcc fac) (by simp [Cofork.π])

中文:
定义 leftHomologyData
  签名: : S.LeftHomologyData where
  定义体: kf.pt
  H := H
  i := kf.ι
  π := π
  wi := KernelFork.condition kf
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := by
    dsimp
    rw [← cancel_mono (isoHomology S hkf hcc fac).hom]; rw [assoc]; rw [assoc]; rw [id_comp]; rw [π_comp_isoHomology_hom]; rw [zero_comp]; rw [f'_eq]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [toCycles_comp_homologyπ]
  hπ := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsCokernel
    · exact parallelPair.ext (Iso.refl _) (S.isoCyclesOfIsLimit hkf)
    · exact Cofork.ext (isoHomology S hkf hcc fac) (by simp [Cofork.π])

Depends on / 依赖: kf.pt
-/
noncomputable def leftHomologyData : S.LeftHomologyData where
  K := kf.pt
  H := H
  i := kf.ι
  π := π
  wi := KernelFork.condition kf
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := by
    dsimp
    rw [← cancel_mono (isoHomology S hkf hcc fac).hom]; rw [assoc]; rw [assoc]; rw [id_comp]; rw [π_comp_isoHomology_hom]; rw [zero_comp]; rw [f'_eq]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [toCycles_comp_homologyπ]
  hπ := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsCokernel
    · exact parallelPair.ext (Iso.refl _) (S.isoCyclesOfIsLimit hkf)
    · exact Cofork.ext (isoHomology S hkf hcc fac) (by simp [Cofork.π])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] g'_eq in
/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`.
This is the right homology data expressing `H` as the homology of `S`. -/
@[simps]
/--
Definition of `rightHomologyData` / `rightHomologyData` 的定义

English:
definition rightHomologyData
  signature: : S.RightHomologyData where
  body: cc.pt
  H := H
  p := cc.π
  ι := ι
  wp := CokernelCofork.condition cc
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := by
    dsimp
    rw [id_comp]; rw [g'_eq]; rw [← cancel_epi (isoHomology S hkf hcc fac).inv]; rw [comp_zero]; rw [isoHomology_hom_comp_ι_assoc]; rw [Iso.inv_hom_id_assoc]; rw [homologyι_comp_fromOpcycles]
  hι := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsKernel
    · exact parallelPair.ext (S.isoOpcyclesOfIsColimit hcc) (Iso.refl _)
    · exact Fork.ext (isoHomology S hkf hcc fac) (by simp [Fork.ι])

中文:
定义 rightHomologyData
  签名: : S.RightHomologyData where
  定义体: cc.pt
  H := H
  p := cc.π
  ι := ι
  wp := CokernelCofork.condition cc
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := by
    dsimp
    rw [id_comp]; rw [g'_eq]; rw [← cancel_epi (isoHomology S hkf hcc fac).inv]; rw [comp_zero]; rw [isoHomology_hom_comp_ι_assoc]; rw [Iso.inv_hom_id_assoc]; rw [homologyι_comp_fromOpcycles]
  hι := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsKernel
    · exact parallelPair.ext (S.isoOpcyclesOfIsColimit hcc) (Iso.refl _)
    · exact Fork.ext (isoHomology S hkf hcc fac) (by simp [Fork.ι])

Depends on / 依赖: cc.pt
-/
noncomputable def rightHomologyData : S.RightHomologyData where
  Q := cc.pt
  H := H
  p := cc.π
  ι := ι
  wp := CokernelCofork.condition cc
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := by
    dsimp
    rw [id_comp]; rw [g'_eq]; rw [← cancel_epi (isoHomology S hkf hcc fac).inv]; rw [comp_zero]; rw [isoHomology_hom_comp_ι_assoc]; rw [Iso.inv_hom_id_assoc]; rw [homologyι_comp_fromOpcycles]
  hι := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2 S.homologyIsKernel
    · exact parallelPair.ext (S.isoOpcyclesOfIsColimit hcc) (Iso.refl _)
    · exact Fork.ext (isoHomology S hkf hcc fac) (by simp [Fork.ι])

end ofEpiMonoFactorisation

set_option backward.defeqAttrib.useBackward true in
/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`.
This is the homology data expressing `H` as the homology of `S`. -/
@[simps]
/--
Definition of `ofEpiMonoFactorisation` / `ofEpiMonoFactorisation` 的定义

English:
definition ofEpiMonoFactorisation
  signature: {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  body: ofEpiMonoFactorisation.leftHomologyData S hkf hcc fac
  right := ofEpiMonoFactorisation.rightHomologyData S hkf hcc fac
  iso := Iso.refl _

中文:
定义 ofEpiMonoFactorisation
  签名: {kf : 核叉 S.g} {cc : 余核余叉 S.f}
  定义体: ofEpiMonoFactorisation.leftHomologyData S hkf hcc fac
  right := ofEpiMonoFactorisation.rightHomologyData S hkf hcc fac
  iso := Iso.refl _

Depends on / 依赖: leftHomologyData, ofEpiMonoFactorisation, ofEpiMonoFactorisation.leftHomologyData
-/
noncomputable def ofEpiMonoFactorisation {kf : KernelFork S.g} {cc : CokernelCofork S.f}
    (hkf : IsLimit kf) (hcc : IsColimit cc) {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
    (fac : kf.ι ≫ cc.π = π ≫ ι) [Epi π] [Mono ι] :
    S.HomologyData where
  left := ofEpiMonoFactorisation.leftHomologyData S hkf hcc fac
  right := ofEpiMonoFactorisation.rightHomologyData S hkf hcc fac
  iso := Iso.refl _

end HomologyData

end ShortComplex

end CategoryTheory
