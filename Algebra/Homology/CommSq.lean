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
|    |
v    v
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
/-- The cokernel cofork attached to a commutative square in a preadditive category. -/
/-
**CategoryTheory.CommSq.cokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.CommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {f : X₁ ⟶ X₂} →  
           {g : X₁ ⟶ X₃} →               {inl : X₂ ⟶ X₄} →                 {inr 
: X₃ ⟶ X₄} →                   CategoryTheory.CommSq f g inl inr →              
       CategoryTheory.Limits.CokernelCofork (CategoryTheory.Limits.biprod.lift f
 (-g))
参数：CategoryTheory.Limits.biprod.lift f (-g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel cofork attached to a commutative square in a preadditive category.
-/
noncomputable abbrev CommSq.cokernelCofork (sq : CommSq f g inl inr) :
    CokernelCofork (biprod.lift f (-g)) :=
  CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])

/-- The short complex attached to the cokernel cofork of a commutative square. -/
@[simps]
/-
**CategoryTheory.CommSq.shortComplex** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
ommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [Catego
ryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {f : X₁ ⟶ X₂} →           
  {g : X₁ ⟶ X₃} →               {inl : X₂ ⟶ X₄} → {inr : X₃ ⟶ X₄} → CategoryTheo
ry.CommSq f g inl inr → CategoryTheory.ShortComplex C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex attached to the cokernel cofork of a commutative square.
-/
noncomputable def CommSq.shortComplex (sq : CommSq f g inl inr) : ShortComplex C where
  f := biprod.lift f (-g)
  g := biprod.desc inl inr
  zero := by simp [sq.w]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel. -/
/-
**CategoryTheory.CommSq.isColimitEquivIsColimitCokernelCofork** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {f : X₁ ⟶ X₂} →  
           {g : X₁ ⟶ X₃} →               {inl : X₂ ⟶ X₄} →                 {inr 
: X₃ ⟶ X₄} →                   (sq : CategoryTheory.CommSq f g inl inr) →       
              CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.PushoutCoco
ne.mk inl inr ⋯) ≃                       CategoryTheory.Limits.IsColimit sq.coke
rnelCofork
参数：sq : CategoryTheory.CommSq f g inl inr；CategoryTheory.Limits.PushoutCocone.mk
 inl inr ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel.
-/
noncomputable def CommSq.isColimitEquivIsColimitCokernelCofork (sq : CommSq f g inl inr) :
    IsColimit (PushoutCocone.mk _ _ sq.w) ≃ IsColimit sq.cokernelCofork where
  toFun h :=
    Cofork.IsColimit.mk _
      (fun s ↦ PushoutCocone.IsColimit.desc h
        (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) (by
          rw [← sub_eq_zero, ← assoc, ← assoc, ← Preadditive.sub_comp]
          convert! s.condition <;> cat_disch))
      (fun s ↦ by
        dsimp
        ext
        · simp only [biprod.inl_desc_assoc]
          apply PushoutCocone.IsColimit.inl_desc h
        · simp only [biprod.inr_desc_assoc]
          apply PushoutCocone.IsColimit.inr_desc h)
      (fun s m hm ↦ by
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
      (fun s ↦ h.desc (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
          (by simp [s.condition])))
      (fun s ↦ by simpa using biprod.inl ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s ↦ by simpa using biprod.inr ≫=
                h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr)
                  (by simp [s.condition])) .one)
      (fun s m hm₁ hm₂ ↦ by
        apply Cofork.IsColimit.hom_ext h
        convert!
          (h.fac (CokernelCofork.ofπ (biprod.desc s.inl s.inr) (by simp [s.condition])) .one).symm
        cat_disch)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The colimit cokernel cofork attached to a pushout square. -/
/-
**CategoryTheory.IsPushout.isColimitCokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.IsPushout`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {f : X₁ ⟶ X₂} →  
           {g : X₁ ⟶ X₃} →               {inl : X₂ ⟶ X₄} →                 {inr 
: X₃ ⟶ X₄} →                   (h : CategoryTheory.IsPushout f g inl inr) → Cate
goryTheory.Limits.IsColimit ⋯.cokernelCofork
参数：h : CategoryTheory.IsPushout f g inl inr。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…

--- 原说明 ---
The colimit cokernel cofork attached to a pushout square.
-/
noncomputable def IsPushout.isColimitCokernelCofork (h : IsPushout f g inl inr) :
    IsColimit h.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPushout.epi_shortComplex_g** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {X₁ X₂ X₃ X₄ : C}   [inst_2 : CategoryTheory.Limits
.HasBinaryBiproduct X₂ X₃] {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃
 ⟶ X₄}   (h : CategoryTheory.IsPushout f g inl inr), CategoryTheory.Epi ⋯.shortC
omplex.g
参数：h : CategoryTheory.IsPushout f g inl inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.epi_iff_cancel_zero`：epi_iff_cancel_zero {P Q
 : C} (f : P ⟶ Q) : Epi f ↔ forall (R : C) (g : Q ⟶ R), f ≫ g = 0 -> g = 0
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.shortComplex_g`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {X₁ X₂ X₃ X
₄ : C}   [inst_2 : Categor…
-/
lemma IsPushout.epi_shortComplex_g (h : IsPushout f g inl inr) :
    Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCofork (by simpa using hb)

end Pushout

section Pullback

variable {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}

/-- The kernel fork attached to a commutative square in a preadditive category. -/
/-
**CategoryTheory.CommSq.kernelFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {fst : X₁ ⟶ X₂} →
             {snd : X₁ ⟶ X₃} →               {f : X₂ ⟶ X₄} →                 {g 
: X₃ ⟶ X₄} →                   CategoryTheory.CommSq fst snd f g →              
       CategoryTheory.Limits.KernelFork (CategoryTheory.Limits.biprod.desc f (-g
))
参数：CategoryTheory.Limits.biprod.desc f (-g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel fork attached to a commutative square in a preadditive category.
-/
noncomputable abbrev CommSq.kernelFork (sq : CommSq fst snd f g) :
    KernelFork (biprod.desc f (-g)) :=
  KernelFork.ofι (biprod.lift fst snd) (by simp [sq.w])

/-- The short complex attached to the kernel fork of a commutative square.
(This is similar to `CommSq.shortComplex`, but with different signs.) -/
@[simps]
/-
**CategoryTheory.CommSq.shortComplex'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
CommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [Catego
ryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {fst : X₁ ⟶ X₂} →         
    {snd : X₁ ⟶ X₃} →               {f : X₂ ⟶ X₄} → {g : X₃ ⟶ X₄} → CategoryTheo
ry.CommSq fst snd f g → CategoryTheory.ShortComplex C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex attached to the kernel fork of a commutative square.
(This is similar to `CommSq.shortComplex`, but with different signs.)
-/
noncomputable def CommSq.shortComplex' (sq : CommSq fst snd f g) : ShortComplex C where
  f := biprod.lift fst snd
  g := biprod.desc f (-g)
  zero := by simp [sq.w]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel. -/
/-
**CategoryTheory.CommSq.isLimitEquivIsLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {fst : X₁ ⟶ X₂} →
             {snd : X₁ ⟶ X₃} →               {f : X₂ ⟶ X₄} →                 {g 
: X₃ ⟶ X₄} →                   (sq : CategoryTheory.CommSq fst snd f g) →       
              CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.PullbackCone.
mk fst snd ⋯) ≃                       CategoryTheory.Limits.IsLimit sq.kernelFor
k
参数：sq : CategoryTheory.CommSq fst snd f g；CategoryTheory.Limits.PullbackCone.mk 
fst snd ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel.
-/
noncomputable def CommSq.isLimitEquivIsLimitKernelFork (sq : CommSq fst snd f g) :
    IsLimit (PullbackCone.mk _ _ sq.w) ≃ IsLimit sq.kernelFork where
  toFun h :=
    Fork.IsLimit.mk _
      (fun s ↦ PullbackCone.IsLimit.lift h
        (s.ι ≫ biprod.fst) (s.ι ≫ biprod.snd) (by
          rw [← sub_eq_zero, assoc, assoc, ← Preadditive.comp_sub]
          convert! s.condition <;> cat_disch))
      (fun s ↦ by
        dsimp
        ext
        · simp only [assoc, biprod.lift_fst]
          apply PullbackCone.IsLimit.lift_fst h
        · simp only [assoc, biprod.lift_snd]
          apply PullbackCone.IsLimit.lift_snd h)
      (fun s m hm ↦ by
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
      (fun s ↦ h.lift (KernelFork.ofι (biprod.lift s.fst s.snd)
          (by simp [s.condition])))
      (fun s ↦ by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.fst)
      (fun s ↦ by simpa using h.fac (KernelFork.ofι (biprod.lift s.fst s.snd)
        (by simp [s.condition])) .zero =≫ biprod.snd)
      (fun s m hm₁ hm₂ ↦ by
        apply Fork.IsLimit.hom_ext h
        convert!
          (h.fac (KernelFork.ofι (biprod.lift s.fst s.snd) (by simp [s.condition])) .zero).symm
        cat_disch)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The limit kernel fork attached to a pullback square. -/
/-
**CategoryTheory.IsPullback.isLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.IsPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X₁ X₂ X₃ X₄ : C} →         [inst_2
 : CategoryTheory.Limits.HasBinaryBiproduct X₂ X₃] →           {fst : X₁ ⟶ X₂} →
             {snd : X₁ ⟶ X₃} →               {f : X₂ ⟶ X₄} →                 {g 
: X₃ ⟶ X₄} → (h : CategoryTheory.IsPullback fst snd f g) → CategoryTheory.Limits
.IsLimit ⋯.kernelFork
参数：h : CategoryTheory.IsPullback fst snd f g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…

--- 原说明 ---
The limit kernel fork attached to a pullback square.
-/
noncomputable def IsPullback.isLimitKernelFork (h : IsPullback fst snd f g) :
    IsLimit h.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsPullback.mono_shortComplex'_f** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {X₁ X₂ X₃ X₄ : C}   [inst_2 : CategoryTheory.Limits
.HasBinaryBiproduct X₂ X₃] {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃} {f : X₂ ⟶ X₄} {g : X₃
 ⟶ X₄}   (h : CategoryTheory.IsPullback fst snd f g), CategoryTheory.Mono ⋯.shor
tComplex'.f
参数：h : CategoryTheory.IsPullback fst snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.mono_iff_cancel_zero`：mono_iff_cancel_zero {Q
 R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.shortComplex'_f`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {X₁ X₂ X₃ 
X₄ : C}   [inst_2 : Categor…
-/
lemma IsPullback.mono_shortComplex'_f (h : IsPullback fst snd f g) :
    Mono h.shortComplex'.f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro _ b hb
  exact Fork.IsLimit.hom_ext h.isLimitKernelFork (by simpa using hb)

end Pullback

end CategoryTheory

