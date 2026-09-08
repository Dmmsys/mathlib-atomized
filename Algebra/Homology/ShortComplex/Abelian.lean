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

/-- The canonical morphism `Abelian.image S.f ⟶ kernel S.g` for a short complex `S`
in an abelian category. -/
/-
**CategoryTheory.ShortComplex.abelianImageToKernel** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `Abelian.image S.f ⟶ kernel S.g` for a short complex `S`
in an abelian category.
-/
noncomputable def abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.abelianImageToKernel_comp_kernel_** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abelianImageToKernel_comp_kernel_ι :
    S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f :=
  kernel.lift_ι _ _ _
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono S.abelianImageToKernel :=
  mono_of_mono_fac S.abelianImageToKernel_comp_kernel_ι

@[reassoc]
/-
**CategoryTheory.ShortComplex.abelianImageToKernel_comp_kernel_** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abelianImageToKernel_comp_kernel_ι_comp_cokernel_π :
    S.abelianImageToKernel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  simp

/-- `Abelian.image S.f` is the kernel of `kernel.ι S.g ≫ cokernel.π S.f` -/
/-
**CategoryTheory.ShortComplex.abelianImageToKernelIsKernel** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：abelianImageToKernelIsKernel : IsLimit (KernelFork.ofι S.abelianImageToKer
nel S.abelianImageToKernel_comp_kernel_ι_comp_cokernel_π)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.abelianImageToKernel_comp_kernel_ι_comp_coke
rnel_π`：abelianImageToKernel_comp_kernel_ι_comp_cokernel_π : S.abelianImageToKer
nel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0

--- 原说明 ---
`Abelian.image S.f` is the kernel of `kernel.ι S.g ≫ cokernel.π S.f`
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
/-
**CategoryTheory.ShortComplex.LeftHomologyData.ofAbelian** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ShortComplex.LeftHomologyData`。
形式化陈述：ofAbelian : S.LeftHomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.abelianImageToKernel_comp_kernel_ι_comp_coke
rnel_π`：abelianImageToKernel_comp_kernel_ι_comp_cokernel_π : S.abelianImageToKer
nel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0

--- 原说明 ---
The canonical `LeftHomologyData` of a short complex `S` in an abelian category, 
for
which the `H` field is `Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)`.
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
    rw [hf', he]
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

/-- The canonical morphism `cokernel S.f ⟶ Abelian.coimage S.g` for a short complex `S`
in an abelian category. -/
/-
**CategoryTheory.ShortComplex.cokernelToAbelianCoimage** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：cokernelToAbelianCoimage : cokernel S.f ⟶ Abelian.coimage S.g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `cokernel S.f ⟶ Abelian.coimage S.g` for a short complex 
`S`
in an abelian category.
-/
noncomputable def cokernelToAbelianCoimage : cokernel S.f ⟶ Abelian.coimage S.g :=
  cokernel.desc S.f (Abelian.coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g), assoc,
      cokernel.π_desc, zero, zero_comp])

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.cokernel_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cokernel_π_comp_cokernelToAbelianCoimage :
    cokernel.π S.f ≫ S.cokernelToAbelianCoimage = Abelian.coimage.π S.g :=
  cokernel.π_desc _ _ _
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi S.cokernelToAbelianCoimage :=
  epi_of_epi_fac S.cokernel_π_comp_cokernelToAbelianCoimage
/-
**CategoryTheory.ShortComplex.kernel_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage :
    (kernel.ι S.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0 := by simp

/-- `Abelian.coimage S.g` is the cokernel of `kernel.ι S.g ≫ cokernel.π S.f` -/
/-
**CategoryTheory.ShortComplex.cokernelToAbelianCoimageIsCokernel** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：cokernelToAbelianCoimageIsCokernel : IsColimit (CokernelCofork.ofπ S.coker
nelToAbelianCoimage S.kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.kernel_ι_comp_cokernel_π_comp_cokernelToAbel
ianCoimage`：kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage : (kernel.ι S
.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0

--- 原说明 ---
`Abelian.coimage S.g` is the cokernel of `kernel.ι S.g ≫ cokernel.π S.f`
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
/-
**CategoryTheory.ShortComplex.RightHomologyData.ofAbelian** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.ShortComplex.RightHomologyData`。
形式化陈述：ofAbelian : S.RightHomologyData
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.kernel_ι_comp_cokernel_π_comp_cokernelToAbel
ianCoimage`：kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage : (kernel.ι S
.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0

--- 原说明 ---
The canonical `RightHomologyData` of a short complex `S` in an abelian category,
 for
which the `H` field is `Abelian.image (kernel.ι S.g ≫ cokernel.π S.f)`.
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
    rw [hg', reassoc_of% he]
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
/-- The canonical `HomologyData` of a short complex `S` in an abelian category. -/
/-
**CategoryTheory.ShortComplex.HomologyData.ofAbelian** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] → (S : CategoryTheory.ShortComplex C) → S.HomologyDat
a
参数：S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `HomologyData` of a short complex `S` in an abelian category.
-/
noncomputable def HomologyData.ofAbelian : S.HomologyData where
  left := LeftHomologyData.ofAbelian S
  right := RightHomologyData.ofAbelian S
  iso := Abelian.coimageIsoImage (kernel.ι S.g ≫ cokernel.π S.f)
/-
**CategoryTheory.ShortComplex._root_.CategoryTheory.categoryWithHomology_of_abel
ian** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.CategoryTheory.categoryWithHomology_of_abelian :
    CategoryWithHomology C where
  hasHomology S := HasHomology.mk' (HomologyData.ofAbelian S)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalMonoCategory (ShortComplex C) := ⟨fun i _ => ⟨by
  refine NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (isLimitOfIsLimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isLimitMapConeOfKernelForkOfι⟩⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalEpiCategory (ShortComplex C) := ⟨fun p _ => ⟨by
  refine NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfIsColimitπ _ ?_ ?_ ?_)
  all_goals apply Abelian.isColimitMapCoconeOfCokernelCoforkOfπ⟩⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (ShortComplex C) where

attribute [local instance] strongEpi_of_epi

/-- The homology of a short complex `S` in an abelian category identifies to
the image of `S.iCycles ≫ S.pOpcycles : S.cycles ⟶ S.opcycles`. -/
/-
**CategoryTheory.ShortComplex.homologyIsoImageICyclesCompPOpcycles** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：homologyIsoImageICyclesCompPOpcycles : S.homology ≅ image (S.iCycles ≫ S.p
Opcycles)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …

--- 原说明 ---
The homology of a short complex `S` in an abelian category identifies to
the image of `S.iCycles ≫ S.pOpcycles : S.cycles ⟶ S.opcycles`.
-/
noncomputable def homologyIsoImageICyclesCompPOpcycles :
    S.homology ≅ image (S.iCycles ≫ S.pOpcycles) :=
  image.isoStrongEpiMono _ _ S.homology_π_ι

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.homologyIsoImageICyclesCompPOpcycles_** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`,
then `H` identifies to the image of `S.iCycles ≫ S.pOpcycles : S.cycles ⟶ S.opcycles`. -/
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoImage** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactoris
ation`。
形式化陈述：isoImage : H ≅ image (S.iCycles ≫ S.pOpcycles)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …

--- 原说明 ---
Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ c
c.pt`,
then `H` identifies to the image of `S.iCycles ≫ S.pOpcycles : S.cycles ⟶ S.opcy
cles`.
-/
noncomputable def isoImage : H ≅ image (S.iCycles ≫ S.pOpcycles) := by
  have : ((S.isoCyclesOfIsLimit hkf).inv ≫ π) ≫ ι ≫
    (S.isoOpcyclesOfIsColimit hcc).hom = S.iCycles ≫ S.pOpcycles := by
    simp [← reassoc_of% fac]
  exact image.isoStrongEpiMono _ _ this

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoImage_** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactori
sation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoImage_ι :
    (isoImage S hkf hcc fac).hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  apply image.isoStrongEpiMono_hom_comp_ι
  simp [← reassoc_of% fac]

/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`,
then `H` identifies to the homology of `S`. -/
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFacto
risation`。
形式化陈述：isoHomology : H ≅ S.homology
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ c
c.pt`,
then `H` identifies to the homology of `S`.
-/
noncomputable def isoHomology : H ≅ S.homology :=
  isoImage S hkf hcc fac ≪≫ S.homologyIsoImageICyclesCompPOpcycles.symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_isoHomology_hom :
    π ≫ (isoHomology S hkf hcc fac).hom = (S.isoCyclesOfIsLimit hkf).hom ≫ S.homologyπ := by
  dsimp [isoHomology]
  simp [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom),
    ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    ← reassoc_of% fac]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology_ho
m_comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEp
iMonoFactorisation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomology_hom_comp_ι :
    (isoHomology S hkf hcc fac).inv ≫ ι = S.homologyι ≫ (S.isoOpcyclesOfIsColimit hcc).inv := by
  simp [← cancel_epi S.homologyπ, ← cancel_epi (S.isoCyclesOfIsLimit hkf).hom,
    ← π_comp_isoHomology_hom_assoc S hkf hcc fac, ← fac]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.f'_eq** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisati
on`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   (S : CategoryTheory.ShortComplex C) {kf : CategoryTheory.Li
mits.KernelFork S.g}   (hkf : CategoryTheory.Limits.IsLimit kf),   hkf.lift (Cat
egoryTheory.Limits.KernelFork.ofι S.f ⋯) =     CategoryTheory.CategoryStruct.com
p S.toCycles (S.isoCyclesOfIsLimit hkf).inv
参数：S : CategoryTheory.ShortComplex C；hkf : CategoryTheory.Limits.IsLimit kf；Cate
goryTheory.Limits.KernelFork.ofι S.f ⋯；S.isoCyclesOfIsLimit hkf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.mono`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.For
k f g}   (hs : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.isoCyclesOfIsLimit_inv_ι`：isoCyclesOfIsLimit
_inv_ι : (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma f'_eq :
    hkf.lift (KernelFork.ofι S.f S.zero) =
      S.toCycles ≫ (S.isoCyclesOfIsLimit hkf).inv := by
  have := Fork.IsLimit.mono hkf
  simp [← cancel_mono kf.ι]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.g'_eq** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisati
on`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   (S : CategoryTheory.ShortComplex C) {cc : CategoryTheory.Li
mits.CokernelCofork S.f}   (hcc : CategoryTheory.Limits.IsColimit cc),   hcc.des
c (CategoryTheory.Limits.CokernelCofork.ofπ S.g ⋯) =     CategoryTheory.Category
Struct.comp (S.isoOpcyclesOfIsColimit hcc).hom S.fromOpcycles
参数：S : CategoryTheory.ShortComplex C；hcc : CategoryTheory.Limits.IsColimit cc；Ca
tegoryTheory.Limits.CokernelCofork.ofπ S.g ⋯；S.isoOpcyclesOfIsColimit hcc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.epi`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Cofork f g}   (hs : CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.π_isoOpcyclesOfIsColimit_hom_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   (S : CategoryTheory.Sho…
· 使用引理 `CategoryTheory.ShortComplex.p_fromOpcycles`：p_fromOpcycles : S.pOpcycles
 ≫ S.fromOpcycles = S.g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma g'_eq : hcc.desc (CokernelCofork.ofπ S.g S.zero) =
    (S.isoOpcyclesOfIsColimit hcc).hom ≫ S.fromOpcycles := by
  have := Cofork.IsColimit.epi hcc
  simp [← cancel_epi cc.π]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.homology** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactoris
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_isoHomology_inv :
    S.homologyπ ≫ (isoHomology S hkf hcc fac).inv = (S.isoCyclesOfIsLimit hkf).inv ≫ π := by
  simp only [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology_in
v_homology** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.o
fEpiMonoFactorisation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoHomology_inv_homologyι :
    (isoHomology S hkf hcc fac).hom ≫ S.homologyι =
    ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  rw [← cancel_mono (S.isoOpcyclesOfIsColimit hcc).inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, ← isoHomology_hom_comp_ι S hkf hcc fac, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ cc.pt`.
This is the left homology data expressing `H` as the homology of `S`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.leftHomologyDa
ta** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMono
Factorisation`。
形式化陈述：leftHomologyData : S.LeftHomologyData where K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ c
c.pt`.
This is the left homology data expressing `H` as the homology of `S`.
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
    rw [← cancel_mono (isoHomology S hkf hcc fac).hom, assoc, assoc, id_comp,
      π_comp_isoHomology_hom, zero_comp, f'_eq,
      assoc, Iso.inv_hom_id_assoc, toCycles_comp_homologyπ]
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
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.rightHomologyD
ata** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData.ofEpiMon
oFactorisation`。
形式化陈述：rightHomologyData : S.RightHomologyData where Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ c
c.pt`.
This is the right homology data expressing `H` as the homology of `S`.
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
    rw [id_comp, g'_eq, ← cancel_epi (isoHomology S hkf hcc fac).inv, comp_zero,
      isoHomology_hom_comp_ι_assoc, Iso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
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
/-
**CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.ShortComplex.HomologyData`。
形式化陈述：ofEpiMonoFactorisation {kf : KernelFork S.g} {cc : CokernelCofork S.f} (hk
f : IsLimit kf) (hcc : IsColimit cc) {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt} (fa
c : kf.ι ≫ cc.π = π ≫ ι) [Epi π] [Mono ι] : S.HomologyData where left
参数：hkf : IsLimit kf；hcc : IsColimit cc；fac : kf.ι ≫ cc.π = π ≫ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be a short complex in an abelian category. Let `kf` be a
limit kernel fork of `S.g` and `cc` a limit cokernel cofork of `S.f`.
Let `kf.pt ⟶ H ⟶ cc.pt` be an epi-mono factorization of `kf.ι ≫ cc.π : kf.pt ⟶ c
c.pt`.
This is the homology data expressing `H` as the homology of `S`.
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

