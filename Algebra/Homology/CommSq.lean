/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

Consider a commutative square in a preadditive category:

```
X₁ ⟶ X₂
| |
v v
X₃ ⟶ X₄
```

In this file, we show that this is a pushout square iff the object `X₄`
identifies to the cokernel of the difference map `X₁ ⟶ X₂ ⊞ X₃`
via the obvious map `X₂ ⊞ X₃ ⟶ X₄`.

Similarly, it is a pullback square iff the object `X₁`
identifies to the kernel of the difference map `X₂ ⊞ X₃ ⟶ X₄`
via the obvious map `X₁ ⟶ X₂ ⊞ X₃`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

section Pushout

variable {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}
/--
Definition of `CommSq.cokernelCofork` / `CommSq.cokernelCofork` 的定义

English:
abbreviation CommSq.cokernelCofork
  signature: (sq : CommSq f g inl inr)
  body: CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])

中文:
缩写 交换Sq.cokernelCofork
  签名: (sq : 交换Sq f g inl inr)
  定义体: CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])

Depends on / 依赖: CokernelCofork, CokernelCofork.of, biprod, biprod.desc, sq.w
-/
noncomputable abbrev CommSq.cokernelCofork (sq : CommSq f g inl inr) :
    CokernelCofork (biprod.lift f (-g)) :=
  CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])

/-- The short complex attached to the cokernel cofork of a commutative square. -/
@[simps]
/--
Definition of `CommSq.shortComplex` / `CommSq.shortComplex` 的定义

English:
definition CommSq.shortComplex
  signature: (sq : CommSq f g inl inr)
  body: biprod.lift f (-g)
  g := biprod.desc inl inr
  zero := by simp [sq.w]

中文:
定义 交换Sq.shortComplex
  签名: (sq : 交换Sq f g inl inr)
  定义体: biprod.lift f (-g)
  g := biprod.desc inl inr
  zero := by simp [sq.w]

Depends on / 依赖: biprod, biprod.lift
-/
noncomputable def CommSq.shortComplex (sq : CommSq f g inl inr) : ShortComplex C where
  f := biprod.lift f (-g)
  g := biprod.desc inl inr
  zero := by simp [sq.w]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `CommSq.isColimitEquivIsColimitCokernelCofork` / `CommSq.isColimitEquivIsColimitCokernelCofork` 的定义

English:
definition CommSq.isColimitEquivIsColimitCokernelCofork
  signature: (sq : CommSq f g inl inr)
  body: Cofork.IsColimit.mk _
      (fun s => PushoutCocone.IsColimit.desc h
        (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
          rw [← sub_eq_zero]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.sub_comp]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
   

中文:
定义 交换Sq.isColimitEquivIsColimitCokernelCofork
  签名: (sq : 交换Sq f g inl inr)
  定义体: Cofork.IsColimit.mk _
      (fun s => PushoutCocone.IsColimit.desc h
        (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
          rw [← sub_eq_zero]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.sub_comp]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
   

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, Preadditive, Preadditive.sub_comp, PushoutCocone, PushoutCocone.IsColimit.desc, PushoutCocone.IsColimit.hom_ext, PushoutCocone.IsColimit.inl_desc, PushoutCocone.IsColimit.inr_desc, biprod, biprod.inl, biprod.inl_desc_assoc, biprod.inr, biprod.inr_desc_assoc, cat_disch, condition, convert, hom_ext, inl_desc
-/
noncomputable def CommSq.isColimitEquivIsColimitCokernelCofork (sq : CommSq f g inl inr) :
    IsColimit (PushoutCocone.mk _ _ sq.w) ≃ IsColimit sq.cokernelCofork where
  toFun h :=
    Cofork.IsColimit.mk _
      (fun s => PushoutCocone.IsColimit.desc h
        (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
          rw [← sub_eq_zero]; rw [← assoc]; rw [← assoc]; rw [← Preadditive.sub_comp]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
        · simp only [biprod.inl_desc_assoc]
          apply PushoutCocone.IsColimit.inl_desc h
        · simp only [biprod.inr_desc_assoc]
          apply PushoutCocone.IsColimit.inr_desc h)
      (fun s m hm => by
        apply PushoutCocone.IsColimit.hom_ext h
        · replace hm := biprod.inl ≫= hm
          dsimp at hm ⊢
          simp only [biprod.inl_desc_assoc] at hm
          rw [hm]
          symm
          apply PushoutCocone.IsColimit.inl_desc h
        · replace hm := biprod.inr ≫= hm
          dsimp at hm ⊢
          simp only [biprod.inr_desc_assoc] at hm
          rw [hm]
          symm
          apply PushoutCocone.IsColimit.inr_desc h)
  invFun h :=
    PushoutCocone.IsColimit.mk _
      (fun s => h.desc (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
          (by simp [s.condition])))
      (fun s => by simpa using biprod.inl ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s => by simpa using biprod.inr ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s m hm₁ hm₂ => by
        apply Cofork.IsColimit.hom_ext h
        convert!
          (h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr) (by simp [s.condition])) .one).symm
        cat_disch)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `IsPushout.isColimitCokernelCofork` / `IsPushout.isColimitCokernelCofork` 的定义

English:
definition IsPushout.isColimitCokernelCofork
  signature: (h : IsPushout f g inl inr)
  body: h.isColimitEquivIsColimitCokernelCofork h.isColimit

中文:
定义 是推出.isColimitCokernelCofork
  签名: (h : 是推出 f g inl inr)
  定义体: h.isColimitEquivIsColimitCokernelCofork h.isColimit

Depends on / 依赖: h.isColimit, h.isColimitEquivIsColimitCokernelCofork, isColimit, isColimitEquivIsColimitCokernelCofork
-/
noncomputable def IsPushout.isColimitCokernelCofork (h : IsPushout f g inl inr) :
    IsColimit h.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsPushout.epi_shortComplex_g` / 引理 `IsPushout.epi_shortComplex_g`

English:
lemma IsPushout.epi_shortComplex_g
  given: (h : IsPushout f g inl inr)
  proof: by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

中文:
引理 是推出.epi_shortComplex_g
  条件: (h : 是推出 f g inl inr)
  证明: by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, Preadditive, Preadditive.epi_iff_cancel_zero, epi_iff_cancel_zero, h.isColimitCokernelCofork, hom_ext, isColimitCokernelCofork
-/
lemma IsPushout.epi_shortComplex_g (h : IsPushout f g inl inr) :
    Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

end Pushout

section Pullback

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

/--
Definition of `CommSq.kernelFork` / `CommSq.kernelFork` 的定义

English:
abbreviation CommSq.kernelFork
  signature: (sq : CommSq fst snd f g)
  body: KernelFork.ofι (biprod.lift fst snd) (by simp [sq.w])

中文:
缩写 交换Sq.kernelFork
  签名: (sq : 交换Sq fst snd f g)
  定义体: KernelFork.ofι (biprod.lift fst snd) (by simp [sq.w])

Depends on / 依赖: KernelFork, KernelFork.of, biprod, biprod.lift, sq.w
-/
noncomputable abbrev CommSq.kernelFork (sq : CommSq fst snd f g) :
    KernelFork (biprod.desc f (-g)) :=
  KernelFork.ofι (biprod.lift fst snd) (by simp [sq.w])

/-- The short complex attached to the kernel fork of a commutative square.
(This is similar to `CommSq.shortComplex`, but with different signs.) -/
@[simps]
/--
Definition of `CommSq.shortComplex'` / `CommSq.shortComplex'` 的定义

English:
definition CommSq.shortComplex'
  signature: (sq : CommSq fst snd f g)
  body: biprod.lift fst snd
  g := biprod.desc f (-g)
  zero := by simp [sq.w]

中文:
定义 交换Sq.shortComplex'
  签名: (sq : 交换Sq fst snd f g)
  定义体: biprod.lift fst snd
  g := biprod.desc f (-g)
  zero := by simp [sq.w]

Depends on / 依赖: biprod, biprod.lift
-/
noncomputable def CommSq.shortComplex' (sq : CommSq fst snd f g) : ShortComplex C where
  f := biprod.lift fst snd
  g := biprod.desc f (-g)
  zero := by simp [sq.w]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `CommSq.isLimitEquivIsLimitKernelFork` / `CommSq.isLimitEquivIsLimitKernelFork` 的定义

English:
definition CommSq.isLimitEquivIsLimitKernelFork
  signature: (sq : CommSq fst snd f g)
  body: Fork.IsLimit.mk _
      (fun s => PullbackCone.IsLimit.lift h
        (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) (by
          rw [← sub_eq_zero]; rw [assoc]; rw [assoc]; rw [← Preadditive.comp_sub]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
        · simp

中文:
定义 交换Sq.isLimitEquivIsLimitKernelFork
  签名: (sq : 交换Sq fst snd f g)
  定义体: Fork.IsLimit.mk _
      (fun s => PullbackCone.IsLimit.lift h
        (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) (by
          rw [← sub_eq_zero]; rw [assoc]; rw [assoc]; rw [← Preadditive.comp_sub]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
        · simp

Depends on / 依赖: Fork.IsLimit.mk, IsLimit, Preadditive, Preadditive.comp_sub, PullbackCone, PullbackCone.IsLimit.hom_ext, PullbackCone.IsLimit.lift, PullbackCone.IsLimit.lift_fst, PullbackCone.IsLimit.lift_snd, biprod, biprod.fst, biprod.lift_fst, biprod.lift_snd, biprod.snd, cat_disch, comp_sub, condition, convert, hom_ext, infer_instance
-/
noncomputable def CommSq.isLimitEquivIsLimitKernelFork (sq : CommSq fst snd f g) :
    IsLimit (PullbackCone.mk _ _ sq.w) ≃ IsLimit sq.kernelFork where
  toFun h :=
    Fork.IsLimit.mk _
      (fun s => PullbackCone.IsLimit.lift h
        (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) (by
          rw [← sub_eq_zero]; rw [assoc]; rw [assoc]; rw [← Preadditive.comp_sub]
          convert! s.condition <;> cat_disch))
      (fun s => by
        dsimp
        ext
        · simp only [assoc, biprod.lift_fst]
          apply PullbackCone.IsLimit.lift_fst h
        · simp only [assoc, biprod.lift_snd]
          apply PullbackCone.IsLimit.lift_snd h)
      (fun s m hm => by
        apply PullbackCone.IsLimit.hom_ext h
        · replace hm := hm =≫ biprod.fst
          dsimp at hm ⊢
          simp only [assoc, biprod.lift_fst] at hm
          rw [hm]
          symm
          apply PullbackCone.IsLimit.lift_fst h
        · replace hm := hm =≫ biprod.snd
          dsimp at hm ⊢
          simp only [assoc, biprod.lift_snd] at hm
          rw [hm]
          symm
          apply PullbackCone.IsLimit.lift_snd h)
  invFun h :=
    PullbackCone.IsLimit.mk _
      (fun s => h.lift (KernelFork.ofι (biprod.lift s.fst s.snd)
          (by simp [s.condition])))
      (fun s => by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.fst)
      (fun s => by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.snd)
      (fun s m hm₁ hm₂ => by
        apply Fork.IsLimit.hom_ext h
        convert!
          (h.fac (KernelFork.ofι (biprod.lift s.fst s.snd) (by simp [s.condition])) .zero).symm
        cat_disch)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `IsPullback.isLimitKernelFork` / `IsPullback.isLimitKernelFork` 的定义

English:
definition IsPullback.isLimitKernelFork
  signature: (h : IsPullback fst snd f g)
  body: h.isLimitEquivIsLimitKernelFork h.isLimit

中文:
定义 是拉回.isLimitKernelFork
  签名: (h : 是拉回 fst snd f g)
  定义体: h.isLimitEquivIsLimitKernelFork h.isLimit

Depends on / 依赖: h.isLimit, h.isLimitEquivIsLimitKernelFork, isLimit, isLimitEquivIsLimitKernelFork
-/
noncomputable def IsPullback.isLimitKernelFork (h : IsPullback fst snd f g) :
    IsLimit h.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsPullback.mono_shortComplex'_f` / 引理 `IsPullback.mono_shortComplex'_f`

English:
lemma IsPullback.mono_shortComplex'_f
  given: (h : IsPullback fst snd f g)
  proof: by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

中文:
引理 是拉回.mono_shortComplex'_f
  条件: (h : 是拉回 fst snd f g)
  证明: by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, Preadditive, Preadditive.mono_iff_cancel_zero, h.isLimitKernelFork, hom_ext, isLimitKernelFork, mono_iff_cancel_zero
-/
lemma IsPullback.mono_shortComplex'_f (h : IsPullback fst snd f g) :
    Mono h.shortComplex'.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

end Pullback

end CategoryTheory
