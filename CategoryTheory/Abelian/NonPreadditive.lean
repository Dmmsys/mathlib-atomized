/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Every NonPreadditiveAbelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with finite products,
kernels and cokernels, and in which every monomorphism and epimorphism is normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. Even more remarkably,
since abelian categories admit exactly one preadditive structure (see
`subsingleton_preadditive_of_hasBinaryBiproducts`), the construction manages to exactly
reconstruct any natural preadditive structure the category may have.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

section

universe v u

variable (C : Type u) [Category.{v} C]

/--
Definition of `NonPreadditiveAbelian` / `NonPreadditiveAbelian` 的定义

English:
class NonPreadditiveAbelian
  parameters: extends HasZeroMorphisms C, IsNormalMonoCategory C,
  extends: HasZeroMorphisms C, IsNormalMonoCategory C, 
  axioms and operations (5):
    - [has_zero_object : HasZeroObject C]
    - [has_kernels : HasKernels C]
    - [has_cokernels : HasCokernels C]
    - [has_finite_products : HasFiniteProducts C]
    - [has_finite_coproducts : HasFiniteCoproducts C]

中文:
类 NonPreadditiveAbelian
  参数: extends HasZeroMorphisms C, IsNormalMonoCategory C,
  继承: HasZeroMorphisms C, IsNormalMonoCategory C, 
  公理与运算 (5 个):
    - [has_zero_object : HasZeroObject C]
    - [has_kernels : HasKernels C]
    - [has_cokernels : HasCokernels C]
    - [has_finite_products : HasFiniteProducts C]
    - [has_finite_coproducts : HasFiniteCoproducts C]
-/
class NonPreadditiveAbelian extends HasZeroMorphisms C, IsNormalMonoCategory C,
    IsNormalEpiCategory C where
  [has_zero_object : HasZeroObject C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]
  [has_finite_products : HasFiniteProducts C]
  [has_finite_coproducts : HasFiniteCoproducts C]

attribute [instance] NonPreadditiveAbelian.has_zero_object

attribute [instance] NonPreadditiveAbelian.has_kernels

attribute [instance] NonPreadditiveAbelian.has_cokernels

attribute [instance] NonPreadditiveAbelian.has_finite_products

attribute [instance] NonPreadditiveAbelian.has_finite_coproducts

end

end CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [NonPreadditiveAbelian C]

namespace CategoryTheory.NonPreadditiveAbelian

section Factor

variable {P Q : C} (f : P ⟶ Q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (Abelian.factorThruImage f)
  body: let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
  NormalMonoCategory.epi_of_zero_cancel
  _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) => by
  -- Since C is abelian, u :

中文:
实例 :
  签名: Epi (Abelian.factorThruImage f)
  定义体: let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
  NormalMonoCategory.epi_of_zero_cancel
  _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) => by
  -- Since C is abelian, u :

Depends on / 依赖: Abelian, Abelian.factorThruImage, Abelian.image, cokernel, factorThruImage, kernel
-/
instance : Epi (Abelian.factorThruImage f) :=
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
  NormalMonoCategory.epi_of_zero_cancel
  _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) => by
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i
  have hu := normalMonoOfMono u
  let h := hu.g
  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg
  have fh : f ≫ h = 0 :=
    calc
      f ≫ h = (p ≫ i) ≫ h := (Abelian.image.fac f).symm ▸ rfl
      _ = ((t ≫ kernel.ι g) ≫ i) ≫ h := ht ▸ rfl
      _ = t ≫ u ≫ h := by simp only [u, Category.assoc]
      _ = t ≫ 0 := hu.w ▸ rfl
      _ = 0 := HasZeroMorphisms.comp_zero _ _
  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh
  have hih : i ≫ h = 0 :=
    calc
      i ≫ h = i ≫ cokernel.π f ≫ l := hl ▸ rfl
      _ = 0 ≫ l := by rw [← Category.assoc, kernel.condition]
      _ = 0 := zero_comp
  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := NormalMono.lift' u i hih
  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i := by rw [Category.assoc, hs, Category.id_comp]
  have : Epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs')
  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact zero_of_epi_comp _ (kernel.condition g)

/--
Instance `isIso_factorThruImage` / 实例 `isIso_factorThruImage`

English:
instance isIso_factorThruImage
  signature: [Mono f]
  body: isIso_of_mono_of_epi Abelian.factorThruImage f

中文:
实例 isIso_factorThruImage
  签名: [Mono f]
  定义体: isIso_of_mono_of_epi Abelian.factorThruImage f

Depends on / 依赖: Abelian, Abelian.factorThruImage, factorThruImage, isIso_of_mono_of_epi
-/
instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) :=
isIso_of_mono_of_epi Abelian.factorThruImage f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (Abelian.factorThruCoimage f)
  body: let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) => by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    h

中文:
实例 :
  签名: Mono (Abelian.factorThruCoimage f)
  定义体: let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) => by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    h

Depends on / 依赖: Abelian, Abelian.coimage, Abelian.factorThruCoimage, NormalEpiCategory, NormalEpiCategory.mono_of_cancel_zero, coimage, cokernel, factorThruCoimage, kernel, mono_of_cancel_zero
-/
instance : Mono (Abelian.factorThruCoimage f) :=
  let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) => by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    have hu := normalEpiOfEpi u
    let h := hu.g
    -- By hypothesis, i factors through the cokernel of g via some t.
    obtain ⟨t, ht⟩ := cokernel.desc' g i hgi
    have hf : h ≫ f = 0 :=
      calc
        h ≫ f = h ≫ p ≫ i := (Abelian.coimage.fac f).symm ▸ rfl
        _ = h ≫ p ≫ cokernel.π g ≫ t := ht ▸ rfl
        _ = h ≫ u ≫ t := by simp only [u, Category.assoc]
        _ = 0 ≫ t := by rw [← Category.assoc, hu.w]
        _ = 0 := zero_comp
    -- h factors through the kernel of f via some l.
    obtain ⟨l, hl⟩ := kernel.lift' f h hf
    have hhp : h ≫ p = 0 :=
      calc
        h ≫ p = (l ≫ kernel.ι f) ≫ p := hl ▸ rfl
        _ = l ≫ 0 := by rw [Category.assoc, cokernel.condition]
        _ = 0 := comp_zero
    -- p factors through u = coker h via some s.
    obtain ⟨s, hs⟩ := NormalEpi.desc' u p hhp
    have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I := by rw [← Category.assoc, hs, Category.comp_id]
    have : Mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs')
    -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
    exact zero_of_comp_mono _ (cokernel.condition g)

/--
Instance `isIso_factorThruCoimage` / 实例 `isIso_factorThruCoimage`

English:
instance isIso_factorThruCoimage
  signature: [Epi f]
  body: isIso_of_mono_of_epi _

中文:
实例 isIso_factorThruCoimage
  签名: [Epi f]
  定义体: isIso_of_mono_of_epi _

Depends on / 依赖: isIso_of_mono_of_epi
-/
instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) :=
  isIso_of_mono_of_epi _

end Factor

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `epiIsCokernelOfKernel` / `epiIsCokernelOfKernel` 的定义

English:
definition epiIsCokernelOfKernel
  signature: [Epi f] (s : Fork f 0) (h : IsLimit s)
  body: IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)

中文:
定义 epiIsCokernelOfKernel
  签名: [Epi f] (s : Fork f 0) (h : IsLimit s)
  定义体: IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)

Depends on / 依赖: Abelian, Abelian.coimage.fac, Abelian.factorThruCoimage, ConeMorphism, ConeMorphism.w, IsCokernel, IsCokernel.cokernelIso, IsLimit, Limits, Limits.IsLimit.conePointUniqueUpToIso, Limits.IsLimit.uniqueUpToIso, coimage, cokernel, cokernel.ofIsoComp, cokernelIso, conePointUniqueUpToIso, factorThruCoimage, isLimit, limit.isLimit, ofIsoComp
-/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `monoIsKernelOfCokernel` / `monoIsKernelOfCokernel` 的定义

English:
definition monoIsKernelOfCokernel
  signature: [Mono f] (s : Cofork f 0) (h : IsColimit s)
  body: IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)

中文:
定义 monoIsKernelOfCokernel
  签名: [Mono f] (s : Cofork f 0) (h : IsColimit s)
  定义体: IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)

Depends on / 依赖: Abelian, Abelian.factorThruImage, Abelian.image.fac, CoconeMorphism, CoconeMorphism.w, IsColimit, IsKernel, IsKernel.isoKernel, Limits, Limits.IsColimit.coconePointUniqueUpToIso, Limits.IsColimit.uniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, factorThruImage, isColimit, isoKernel, kernel, kernel.ofCompIso, ofCompIso
-/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)

end CokernelOfKernel

section

/--
Definition of `r` / `r` 的定义

English:
abbreviation r
  signature: (A : C)
  body: prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

中文:
缩写 r
  签名: (A : C)
  定义体: prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

Depends on / 依赖: cokernel, prod.lift
-/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

/--
Instance `mono_Δ` / 实例 `mono_Δ`

English:
instance mono_Δ
  signature: {A : C}
  body: mono_of_mono_fac prod.lift_fst _ _

中文:
实例 mono_Δ
  签名: {A : C}
  定义体: mono_of_mono_fac prod.lift_fst _ _

Depends on / 依赖: lift_fst, mono_of_mono_fac, prod.lift_fst
-/
instance mono_Δ {A : C} : Mono (diag A) :=
mono_of_mono_fac prod.lift_fst _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `mono_r` / 实例 `mono_r`

English:
instance mono_r
  signature: {A : C}
  body: by
  let hl : IsLimit (KernelFork.ofι (diag A) (cokernel.condition (diag A))) :=
    monoIsKernelOfCokernel _ (colimit.isColimit _)
  apply NormalEpiCategory.mono_of_cancel_zero
  intro Z x hx
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [Category.assoc]; rw 

中文:
实例 mono_r
  签名: {A : C}
  定义体: by
  let hl : IsLimit (KernelFork.ofι (diag A) (cokernel.condition (diag A))) :=
    monoIsKernelOfCokernel _ (colimit.isColimit _)
  apply NormalEpiCategory.mono_of_cancel_zero
  intro Z x hx
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [Category.assoc]; rw 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, IsLimit, KernelFork, KernelFork.IsLimit.lift, KernelFork.of, Limits, Limits.prod.lift_snd, NormalEpiCategory, NormalEpiCategory.mono_of_cancel_zero, cokernel, cokernel.condition, colimit, colimit.isColimit, comp_id, condition, isColimit, lift_snd, monoIsKernelOfCokernel
-/
instance mono_r {A : C} : Mono (r A) := by
  let hl : IsLimit (KernelFork.ofι (diag A) (cokernel.condition (diag A))) :=
    monoIsKernelOfCokernel _ (colimit.isColimit _)
  apply NormalEpiCategory.mono_of_cancel_zero
  intro Z x hx
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [Category.assoc]; rw [hx]
  obtain ⟨y, hy⟩ := KernelFork.IsLimit.lift' hl _ hxx
  rw [KernelFork.ι_ofι] at hy
  have hyy : y = 0 := by
    erw [← Category.comp_id y, ← Limits.prod.lift_snd (𝟙 A) (𝟙 A), ← Category.assoc, hy,
      Category.assoc, prod.lift_snd, HasZeroMorphisms.comp_zero]
  have : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
  apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
  rw [← hy]; rw [hyy]; rw [zero_comp]; rw [zero_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `epi_r` / 实例 `epi_r`

English:
instance epi_r
  signature: {A : C}
  body: by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ Limits.prod.snd = 0 := prod.lift_snd _ _
  let hp1 : IsLimit (KernelFork.ofι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) := by
    refine Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ Limits.prod.fst) ?_ ?_
    · intro s
      apply Limits.prod.hom_ext <;> simp
    · in

中文:
实例 epi_r
  签名: {A : C}
  定义体: by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ Limits.prod.snd = 0 := prod.lift_snd _ _
  let hp1 : IsLimit (KernelFork.ofι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) := by
    refine Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ Limits.prod.fst) ?_ ?_
    · intro s
      apply Limits.prod.hom_ext <;> simp
    · in

Depends on / 依赖: CokernelCof, Fork.IsLimit.mk, IsColimit, IsLimit, KernelFork, KernelFork.of, Limits, Limits.prod.fst, Limits.prod.hom_ext, Limits.prod.snd, cancel_mono, convert, hom_ext, lift_fst, lift_snd, mono_of_mono_fac, prod.lift, prod.lift_fst, prod.lift_snd
-/
instance epi_r {A : C} : Epi (r A) := by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ Limits.prod.snd = 0 := prod.lift_snd _ _
  let hp1 : IsLimit (KernelFork.ofι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) := by
    refine Fork.IsLimit.mk _ (fun s => Fork.ι s ≫ Limits.prod.fst) ?_ ?_
    · intro s
      apply Limits.prod.hom_ext <;> simp
    · intro s m h
      have : Mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
      apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
      convert! h
      apply Limits.prod.hom_ext <;> simp
  let hp2 : IsColimit (CokernelCofork.ofπ (Limits.prod.snd : A ⨯ A ⟶ A) hlp) :=
    epiIsCokernelOfKernel _ hp1
  apply NormalMonoCategory.epi_of_zero_cancel
  intro Z z hz
  have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0 := by rw [← Category.assoc, hz]
  obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hp2 _ h
  rw [CokernelCofork.π_ofπ] at ht
  have htt : t = 0 := by
    rw [← Category.id_comp t]
    change 𝟙 A ≫ t = 0
    rw [← Limits.prod.lift_snd (𝟙 A) (𝟙 A)]; rw [Category.assoc]; rw [ht]; rw [← Category.assoc]; rw [cokernel.condition]; rw [zero_comp]
  apply (cancel_epi (cokernel.π (diag A))).1
  rw [← ht]; rw [htt]; rw [comp_zero]; rw [comp_zero]

/--
Instance `isIso_r` / 实例 `isIso_r`

English:
instance isIso_r
  signature: {A : C}
  body: isIso_of_mono_of_epi _

中文:
实例 isIso_r
  签名: {A : C}
  定义体: isIso_of_mono_of_epi _

Depends on / 依赖: isIso_of_mono_of_epi
-/
instance isIso_r {A : C} : IsIso (r A) :=
  isIso_of_mono_of_epi _

/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: {A : C}
  body: cokernel.π (diag A) ≫ inv (r A)

中文:
缩写 σ
  签名: {A : C}
  定义体: cokernel.π (diag A) ≫ inv (r A)

Depends on / 依赖: cokernel
-/
abbrev σ {A : C} : A ⨯ A ⟶ A :=
  cokernel.π (diag A) ≫ inv (r A)

end

@[reassoc]
/--
theorem `diag_σ` / 定理 `diag_σ`

English:
theorem diag_σ
  given: {X : C}
  statement: diag X ≫ σ = 0
  proof: by rw [cokernel.condition_assoc, zero_comp]

@[reassoc (attr := simp)]

中文:
定理 diag_σ
  条件: {X : C}
  结论: diag X ≫ σ = 0
  证明: by rw [cokernel.condition_assoc, zero_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: cokernel, cokernel.condition_assoc, condition_assoc, zero_comp
-/
theorem diag_σ {X : C} : diag X ≫ σ = 0 := by rw [cokernel.condition_assoc, zero_comp]

@[reassoc (attr := simp)]
/--
theorem `lift_σ` / 定理 `lift_σ`

English:
theorem lift_σ
  given: {X : C}
  statement: prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X
  proof: by rw [← Category.assoc, IsIso.hom_inv_id]

@[reassoc]

中文:
定理 lift_σ
  条件: {X : C}
  结论: prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X
  证明: by rw [← Category.assoc, IsIso.hom_inv_id]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, IsIso.hom_inv_id, hom_inv_id
-/
theorem lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X := by rw [← Category.assoc, IsIso.hom_inv_id]

@[reassoc]
/--
theorem `lift_map` / 定理 `lift_map`

English:
theorem lift_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by simp

中文:
定理 lift_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by simp
-/
theorem lift_map {X Y : C} (f : X ⟶ Y) :
    prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 := by simp

/--
Definition of `isColimitσ` / `isColimitσ` 的定义

English:
definition isColimitσ
  signature: {X : C}
  body: cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [Iso.symm_hom, asIso_inv])

中文:
定义 isColimitσ
  签名: {X : C}
  定义体: cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [Iso.symm_hom, asIso_inv])

Depends on / 依赖: Iso.symm_hom, asIso_inv, cokernel, cokernel.cokernelIso, cokernelIso, symm_hom
-/
def isColimitσ {X : C} : IsColimit (CokernelCofork.ofπ (σ : X ⨯ X ⟶ X) diag_σ) :=
  cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [Iso.symm_hom, asIso_inv])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `σ_comp` / 定理 `σ_comp`

English:
theorem σ_comp
  given: {X Y : C} (f : X ⟶ Y)
  statement: σ ≫ f = Limits.prod.map f f ≫ σ
  proof: by
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' isColimitσ (Limits.prod.map f f ≫ σ) (by
      rw [prod.diag_map_assoc]; rw [diag_σ]; rw [comp_zero])
  suffices hfg : f = g by rw [← hg, Cofork.π_ofπ, hfg]
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, Category.comp_id]
    _ = 

中文:
定理 σ_comp
  条件: {X Y : C} (f : X ⟶ Y)
  结论: σ ≫ f = Limits.prod.map f f ≫ σ
  证明: by
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' isColimitσ (Limits.prod.map f f ≫ σ) (by
      rw [prod.diag_map_assoc]; rw [diag_σ]; rw [comp_zero])
  suffices hfg : f = g by rw [← hg, Cofork.π_ofπ, hfg]
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, Category.comp_id]
    _ = 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Cofork, CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, Limits, Limits.prod.map, comp_id, comp_zero, diag_map_assoc, id_comp, lift_map_assoc, prod.diag_map_assoc, prod.lift
-/
theorem σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = Limits.prod.map f f ≫ σ := by
  obtain ⟨g, hg⟩ :=
    CokernelCofork.IsColimit.desc' isColimitσ (Limits.prod.map f f ≫ σ) (by
      rw [prod.diag_map_assoc]; rw [diag_σ]; rw [comp_zero])
  suffices hfg : f = g by rw [← hg, Cofork.π_ofπ, hfg]
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, Category.comp_id]
    _ = prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f ≫ σ := by rw [lift_map_assoc]
    _ = prod.lift (𝟙 X) 0 ≫ σ ≫ g := by rw [← hg, CokernelCofork.π_ofπ]
    _ = g := by rw [← Category.assoc, lift_σ, Category.id_comp]

section

-- We write `f - g` for `prod.lift f g ≫ σ`.
/-- Subtraction of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/--
Definition of `hasSub` / `hasSub` 的定义

English:
definition hasSub
  signature: {X Y : C}
  body: ⟨fun f g => prod.lift f g ≫ σ⟩

中文:
定义 hasSub
  签名: {X Y : C}
  定义体: ⟨fun f g => prod.lift f g ≫ σ⟩

Depends on / 依赖: prod.lift
-/
def hasSub {X Y : C} : Sub (X ⟶ Y) :=
  ⟨fun f g => prod.lift f g ≫ σ⟩

attribute [local instance] hasSub

-- We write `-f` for `0 - f`.
/-- Negation of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/--
Definition of `hasNeg` / `hasNeg` 的定义

English:
definition hasNeg
  signature: {X Y : C}
  body: fun f => 0 - f

中文:
定义 hasNeg
  签名: {X Y : C}
  定义体: fun f => 0 - f
-/
def hasNeg {X Y : C} : Neg (X ⟶ Y) where
  neg := fun f => 0 - f

attribute [local instance] hasNeg

-- We write `f + g` for `f - (-g)`.
/-- Addition of morphisms in a `NonPreadditiveAbelian` category. -/
@[instance_reducible]
/--
Definition of `hasAdd` / `hasAdd` 的定义

English:
definition hasAdd
  signature: {X Y : C}
  body: ⟨fun f g => f - -g⟩

中文:
定义 hasAdd
  签名: {X Y : C}
  定义体: ⟨fun f g => f - -g⟩
-/
def hasAdd {X Y : C} : Add (X ⟶ Y) :=
  ⟨fun f g => f - -g⟩

attribute [local instance] hasAdd

/--
theorem `sub_def` / 定理 `sub_def`

English:
theorem sub_def
  given: {X Y : C} (a b : X ⟶ Y)
  statement: a - b = prod.lift a b ≫ σ
  proof: rfl

中文:
定理 sub_def
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: a - b = prod.lift a b ≫ σ
  证明: rfl
-/
theorem sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ := rfl

/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: {X Y : C} (a b : X ⟶ Y)
  statement: a + b = a - -b
  proof: rfl

中文:
定理 add_def
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: a + b = a - -b
  证明: rfl
-/
theorem add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - -b := rfl

/--
theorem `neg_def` / 定理 `neg_def`

English:
theorem neg_def
  given: {X Y : C} (a : X ⟶ Y)
  statement: -a = 0 - a
  proof: rfl

中文:
定理 neg_def
  条件: {X Y : C} (a : X ⟶ Y)
  结论: -a = 0 - a
  证明: rfl
-/
theorem neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a := rfl

/--
theorem `sub_zero` / 定理 `sub_zero`

English:
theorem sub_zero
  given: {X Y : C} (a : X ⟶ Y)
  statement: a - 0 = a
  proof: by
  rw [sub_def]
  conv_lhs =>
    congr; congr; rw [← Category.comp_id a]
    case a.g => rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift]; rw [Category.assoc]; rw [lift_σ]; rw [Category.comp_id]

中文:
定理 sub_zero
  条件: {X Y : C} (a : X ⟶ Y)
  结论: a - 0 = a
  证明: by
  rw [sub_def]
  conv_lhs =>
    congr; congr; rw [← Category.comp_id a]
    case a.g => rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift]; rw [Category.assoc]; rw [lift_σ]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, comp_id, comp_lift, conv_lhs, prod.comp_lift, sub_def
-/
theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a := by
  rw [sub_def]
  conv_lhs =>
    congr; congr; rw [← Category.comp_id a]
    case a.g => rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift]; rw [Category.assoc]; rw [lift_σ]; rw [Category.comp_id]

/--
theorem `sub_self` / 定理 `sub_self`

English:
theorem sub_self
  given: {X Y : C} (a : X ⟶ Y)
  statement: a - a = 0
  proof: by
  rw [sub_def]; rw [← Category.comp_id a]; rw [← prod.comp_lift]; rw [Category.assoc]; rw [diag_σ]; rw [comp_zero]

中文:
定理 sub_self
  条件: {X Y : C} (a : X ⟶ Y)
  结论: a - a = 0
  证明: by
  rw [sub_def]; rw [← Category.comp_id a]; rw [← prod.comp_lift]; rw [Category.assoc]; rw [diag_σ]; rw [comp_zero]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, comp_id, comp_lift, comp_zero, prod.comp_lift, sub_def
-/
theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 := by
  rw [sub_def]; rw [← Category.comp_id a]; rw [← prod.comp_lift]; rw [Category.assoc]; rw [diag_σ]; rw [comp_zero]

/--
theorem `lift_sub_lift` / 定理 `lift_sub_lift`

English:
theorem lift_sub_lift
  given: {X Y : C} (a b c d : X ⟶ Y)
  proof: by
  simp only [sub_def]
  ext
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]

中文:
定理 lift_sub_lift
  条件: {X Y : C} (a b c d : X ⟶ Y)
  证明: by
  simp only [sub_def]
  ext
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]

Depends on / 依赖: Category, Category.assoc, lift_fst, lift_map_assoc, lift_snd, prod.lift_fst, prod.lift_map_assoc, prod.lift_snd, sub_def
-/
theorem lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) :
    prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) := by
  simp only [sub_def]
  ext
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]

/--
theorem `sub_sub_sub` / 定理 `sub_sub_sub`

English:
theorem sub_sub_sub
  given: {X Y : C} (a b c d : X ⟶ Y)
  statement: a - c - (b - d) = a - b - (c - d)
  proof: by
  rw [sub_def]; rw [← lift_sub_lift]; rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [prod.lift_map_assoc]; rfl

中文:
定理 sub_sub_sub
  条件: {X Y : C} (a b c d : X ⟶ Y)
  结论: a - c - (b - d) = a - b - (c - d)
  证明: by
  rw [sub_def]; rw [← lift_sub_lift]; rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [prod.lift_map_assoc]; rfl

Depends on / 依赖: Category, Category.assoc, lift_map_assoc, lift_sub_lift, prod.lift_map_assoc, sub_def
-/
theorem sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) := by
  rw [sub_def]; rw [← lift_sub_lift]; rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [prod.lift_map_assoc]; rfl

/--
theorem `neg_sub` / 定理 `neg_sub`

English:
theorem neg_sub
  given: {X Y : C} (a b : X ⟶ Y)
  statement: -a - b = -b - a
  proof: by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]

中文:
定理 neg_sub
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: -a - b = -b - a
  证明: by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]

Depends on / 依赖: conv_lhs, neg_def, sub_sub_sub, sub_zero
-/
theorem neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a := by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]

/--
theorem `neg_neg` / 定理 `neg_neg`

English:
theorem neg_neg
  given: {X Y : C} (a : X ⟶ Y)
  statement: - -a = a
  proof: by
  rw [neg_def]; rw [neg_def]
  conv_lhs =>
    congr; rw [← sub_self a]
  rw [sub_sub_sub]; rw [sub_zero]; rw [sub_self]; rw [sub_zero]

中文:
定理 neg_neg
  条件: {X Y : C} (a : X ⟶ Y)
  结论: - -a = a
  证明: by
  rw [neg_def]; rw [neg_def]
  conv_lhs =>
    congr; rw [← sub_self a]
  rw [sub_sub_sub]; rw [sub_zero]; rw [sub_self]; rw [sub_zero]

Depends on / 依赖: conv_lhs, neg_def, sub_self, sub_sub_sub, sub_zero
-/
theorem neg_neg {X Y : C} (a : X ⟶ Y) : - -a = a := by
  rw [neg_def]; rw [neg_def]
  conv_lhs =>
    congr; rw [← sub_self a]
  rw [sub_sub_sub]; rw [sub_zero]; rw [sub_self]; rw [sub_zero]

/--
theorem `add_comm` / 定理 `add_comm`

English:
theorem add_comm
  given: {X Y : C} (a b : X ⟶ Y)
  statement: a + b = b + a
  proof: by
  rw [add_def]
  conv_lhs => rw [← neg_neg a]
  rw [neg_def]; rw [neg_def]; rw [neg_def]; rw [sub_sub_sub]
  conv_lhs =>
    congr
    next => skip
    rw [← neg_def]; rw [neg_sub]
  rw [sub_sub_sub]; rw [add_def]; rw [← neg_def]; rw [neg_neg b]; rw [neg_def]

中文:
定理 add_comm
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: a + b = b + a
  证明: by
  rw [add_def]
  conv_lhs => rw [← neg_neg a]
  rw [neg_def]; rw [neg_def]; rw [neg_def]; rw [sub_sub_sub]
  conv_lhs =>
    congr
    next => skip
    rw [← neg_def]; rw [neg_sub]
  rw [sub_sub_sub]; rw [add_def]; rw [← neg_def]; rw [neg_neg b]; rw [neg_def]

Depends on / 依赖: add_def, conv_lhs, neg_def, neg_neg, neg_sub, sub_sub_sub
-/
theorem add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a := by
  rw [add_def]
  conv_lhs => rw [← neg_neg a]
  rw [neg_def]; rw [neg_def]; rw [neg_def]; rw [sub_sub_sub]
  conv_lhs =>
    congr
    next => skip
    rw [← neg_def]; rw [neg_sub]
  rw [sub_sub_sub]; rw [add_def]; rw [← neg_def]; rw [neg_neg b]; rw [neg_def]

/--
theorem `add_neg` / 定理 `add_neg`

English:
theorem add_neg
  given: {X Y : C} (a b : X ⟶ Y)
  statement: a + -b = a - b
  proof: by rw [add_def, neg_neg]

中文:
定理 add_neg
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: a + -b = a - b
  证明: by rw [add_def, neg_neg]

Depends on / 依赖: add_def, neg_neg
-/
theorem add_neg {X Y : C} (a b : X ⟶ Y) : a + -b = a - b := by rw [add_def, neg_neg]

/--
theorem `add_neg_cancel` / 定理 `add_neg_cancel`

English:
theorem add_neg_cancel
  given: {X Y : C} (a : X ⟶ Y)
  statement: a + -a = 0
  proof: by rw [add_neg, sub_self]

中文:
定理 add_neg_cancel
  条件: {X Y : C} (a : X ⟶ Y)
  结论: a + -a = 0
  证明: by rw [add_neg, sub_self]

Depends on / 依赖: add_neg, sub_self
-/
theorem add_neg_cancel {X Y : C} (a : X ⟶ Y) : a + -a = 0 := by rw [add_neg, sub_self]

/--
theorem `neg_add_cancel` / 定理 `neg_add_cancel`

English:
theorem neg_add_cancel
  given: {X Y : C} (a : X ⟶ Y)
  statement: -a + a = 0
  proof: by rw [add_comm, add_neg_cancel]

中文:
定理 neg_add_cancel
  条件: {X Y : C} (a : X ⟶ Y)
  结论: -a + a = 0
  证明: by rw [add_comm, add_neg_cancel]

Depends on / 依赖: add_comm, add_neg_cancel
-/
theorem neg_add_cancel {X Y : C} (a : X ⟶ Y) : -a + a = 0 := by rw [add_comm, add_neg_cancel]

/--
theorem `neg_sub'` / 定理 `neg_sub'`

English:
theorem neg_sub'
  given: {X Y : C} (a b : X ⟶ Y)
  statement: -(a - b) = -a + b
  proof: by
  rw [neg_def]; rw [neg_def]
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  rw [sub_sub_sub]; rw [add_def]; rw [neg_def]

中文:
定理 neg_sub'
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: -(a - b) = -a + b
  证明: by
  rw [neg_def]; rw [neg_def]
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  rw [sub_sub_sub]; rw [add_def]; rw [neg_def]

Depends on / 依赖: add_def, conv_lhs, neg_def, sub_self, sub_sub_sub
-/
theorem neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = -a + b := by
  rw [neg_def]; rw [neg_def]
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  rw [sub_sub_sub]; rw [add_def]; rw [neg_def]

/--
theorem `neg_add` / 定理 `neg_add`

English:
theorem neg_add
  given: {X Y : C} (a b : X ⟶ Y)
  statement: -(a + b) = -a - b
  proof: by rw [add_def, neg_sub', add_neg]

中文:
定理 neg_add
  条件: {X Y : C} (a b : X ⟶ Y)
  结论: -(a + b) = -a - b
  证明: by rw [add_def, neg_sub', add_neg]

Depends on / 依赖: add_def, add_neg, neg_sub
-/
theorem neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = -a - b := by rw [add_def, neg_sub', add_neg]

/--
theorem `sub_add` / 定理 `sub_add`

English:
theorem sub_add
  given: {X Y : C} (a b c : X ⟶ Y)
  statement: a - b + c = a - (b - c)
  proof: by
  rw [add_def]; rw [neg_def]; rw [sub_sub_sub]; rw [sub_zero]

中文:
定理 sub_add
  条件: {X Y : C} (a b c : X ⟶ Y)
  结论: a - b + c = a - (b - c)
  证明: by
  rw [add_def]; rw [neg_def]; rw [sub_sub_sub]; rw [sub_zero]

Depends on / 依赖: add_def, infer_instance, lanUnit, neg_def, sub_sub_sub, sub_zero
-/
theorem sub_add {X Y : C} (a b c : X ⟶ Y) : a - b + c = a - (b - c) := by
  rw [add_def]; rw [neg_def]; rw [sub_sub_sub]; rw [sub_zero]

/--
theorem `add_assoc` / 定理 `add_assoc`

English:
theorem add_assoc
  given: {X Y : C} (a b c : X ⟶ Y)
  statement: a + b + c = a + (b + c)
  proof: by
  conv_lhs =>
    congr; rw [add_def]
  rw [sub_add]; rw [← add_neg]; rw [neg_sub']; rw [neg_neg]

中文:
定理 add_assoc
  条件: {X Y : C} (a b c : X ⟶ Y)
  结论: a + b + c = a + (b + c)
  证明: by
  conv_lhs =>
    congr; rw [add_def]
  rw [sub_add]; rw [← add_neg]; rw [neg_sub']; rw [neg_neg]

Depends on / 依赖: add_def, add_neg, conv_lhs, neg_neg, neg_sub, sub_add
-/
theorem add_assoc {X Y : C} (a b c : X ⟶ Y) : a + b + c = a + (b + c) := by
  conv_lhs =>
    congr; rw [add_def]
  rw [sub_add]; rw [← add_neg]; rw [neg_sub']; rw [neg_neg]

/--
theorem `add_zero` / 定理 `add_zero`

English:
theorem add_zero
  given: {X Y : C} (a : X ⟶ Y)
  statement: a + 0 = a
  proof: by rw [add_def, neg_def, sub_self, sub_zero]

中文:
定理 add_zero
  条件: {X Y : C} (a : X ⟶ Y)
  结论: a + 0 = a
  证明: by rw [add_def, neg_def, sub_self, sub_zero]

Depends on / 依赖: add_def, neg_def, sub_self, sub_zero
-/
theorem add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a := by rw [add_def, neg_def, sub_self, sub_zero]

/--
theorem `comp_sub` / 定理 `comp_sub`

English:
theorem comp_sub
  given: {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z)
  statement: f ≫ (g - h) = f ≫ g - f ≫ h
  proof: by
  rw [sub_def]; rw [← Category.assoc]; rw [prod.comp_lift]; rw [sub_def]

中文:
定理 comp_sub
  条件: {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z)
  结论: f ≫ (g - h) = f ≫ g - f ≫ h
  证明: by
  rw [sub_def]; rw [← Category.assoc]; rw [prod.comp_lift]; rw [sub_def]

Depends on / 依赖: Category, Category.assoc, comp_lift, prod.comp_lift, sub_def
-/
theorem comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h := by
  rw [sub_def]; rw [← Category.assoc]; rw [prod.comp_lift]; rw [sub_def]

/--
theorem `sub_comp` / 定理 `sub_comp`

English:
theorem sub_comp
  given: {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z)
  statement: (f - g) ≫ h = f ≫ h - g ≫ h
  proof: by
  rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [← Category.assoc]; rw [prod.lift_map]; rw [sub_def]

中文:
定理 sub_comp
  条件: {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z)
  结论: (f - g) ≫ h = f ≫ h - g ≫ h
  证明: by
  rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [← Category.assoc]; rw [prod.lift_map]; rw [sub_def]

Depends on / 依赖: Category, Category.assoc, lift_map, prod.lift_map, sub_def
-/
theorem sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h := by
  rw [sub_def]; rw [Category.assoc]; rw [σ_comp]; rw [← Category.assoc]; rw [prod.lift_map]; rw [sub_def]

/--
theorem `comp_add` / 定理 `comp_add`

English:
theorem comp_add
  given: (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z)
  statement: f ≫ (g + h) = f ≫ g + f ≫ h
  proof: by
  rw [add_def]; rw [comp_sub]; rw [neg_def]; rw [comp_sub]; rw [comp_zero]; rw [add_def]; rw [neg_def]

中文:
定理 comp_add
  条件: (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z)
  结论: f ≫ (g + h) = f ≫ g + f ≫ h
  证明: by
  rw [add_def]; rw [comp_sub]; rw [neg_def]; rw [comp_sub]; rw [comp_zero]; rw [add_def]; rw [neg_def]

Depends on / 依赖: add_def, comp_sub, comp_zero, neg_def
-/
theorem comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  rw [add_def]; rw [comp_sub]; rw [neg_def]; rw [comp_sub]; rw [comp_zero]; rw [add_def]; rw [neg_def]

/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z)
  statement: (f + g) ≫ h = f ≫ h + g ≫ h
  proof: by
  rw [add_def]; rw [sub_comp]; rw [neg_def]; rw [sub_comp]; rw [zero_comp]; rw [add_def]; rw [neg_def]

中文:
定理 add_comp
  条件: (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z)
  结论: (f + g) ≫ h = f ≫ h + g ≫ h
  证明: by
  rw [add_def]; rw [sub_comp]; rw [neg_def]; rw [sub_comp]; rw [zero_comp]; rw [add_def]; rw [neg_def]

Depends on / 依赖: add_def, neg_def, sub_comp, zero_comp
-/
theorem add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  rw [add_def]; rw [sub_comp]; rw [neg_def]; rw [sub_comp]; rw [zero_comp]; rw [add_def]; rw [neg_def]

/-- Every `NonPreadditiveAbelian` category is preadditive. -/
@[instance_reducible]
/--
Definition of `preadditive` / `preadditive` 的定义

English:
definition preadditive
  signature: : Preadditive C where
  body: { add_assoc := add_assoc
      zero_add := neg_neg
      add_zero := add_zero
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg f g := (add_neg f g).symm
      add_comm := add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := add_comp
  comp_add := comp_add

中文:
定义 preadditive
  签名: : Preadditive C where
  定义体: { add_assoc := add_assoc
      zero_add := neg_neg
      add_zero := add_zero
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg f g := (add_neg f g).symm
      add_comm := add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := add_comp
  comp_add := comp_add

Depends on / 依赖: add_assoc, add_comm, add_comp, add_neg, add_zero, comp_add, neg_add_cancel, neg_neg, nsmulRec, sub_eq_add_neg, zero_add, zsmulRec
-/
def preadditive : Preadditive C where
  homGroup X Y :=
    { add_assoc := add_assoc
      zero_add := neg_neg
      add_zero := add_zero
      neg_add_cancel := neg_add_cancel
      sub_eq_add_neg f g := (add_neg f g).symm
      add_comm := add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := add_comp
  comp_add := comp_add

end

end CategoryTheory.NonPreadditiveAbelian
