/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Weak kernels

These are weak equalizers for functors of the form `parallelPair f 0`.

If the category is preadditive, then weak equalizers exist if and only if weak kernels exist.
(See `hasWeakEqualizer_of_hasWeakKernel` and `hasWeakKernel_of_hasWeakEqualizer`.)

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroMorphisms C] {X Y : C} (f g : X ⟶ Y)

/-- A morphism `f` has a weak kernel if the functor `ParallelPair f 0` has a weak limit. -/
/-
**CategoryTheory.Limits.HasWeakKernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：HasWeakKernel : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f` has a weak kernel if the functor `ParallelPair f 0` has a weak li
mit.
-/
abbrev HasWeakKernel : Prop :=
  HasWeakLimit (parallelPair f 0)

variable (C) in
/-- `HasWeakKernels` represents the existence of weak kernels for every morphism. -/
/-
**CategoryTheory.Limits.HasWeakKernels** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasWeakKernels : Prop where hasWeakLimit : forall {X Y : C} (f : X ⟶ Y), H
asWeakKernel f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasWeakKernels` represents the existence of weak kernels for every morphism.
-/
class HasWeakKernels : Prop where
  hasWeakLimit : ∀ {X Y : C} (f : X ⟶ Y), HasWeakKernel f := by infer_instance

attribute [instance 100] HasWeakKernels.hasWeakLimit

/-- If a category has kernels, then it has weak kernels. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category has kernels, then it has weak kernels.
-/
instance (priority := 100) HasWeakKernelsOfHasKernels [HasKernels C] :
    HasWeakKernels C where

section

variable [HasWeakKernel f]

/-- The weak kernel of a morphism. -/
/-
**CategoryTheory.Limits.weakKernel** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：weakKernel : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak kernel of a morphism.
-/
abbrev weakKernel : C :=
  weakEqualizer f 0

/-- The map from `weakKernel f` into the source of `f`. -/
/-
**CategoryTheory.Limits.weakKernel.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `weakKernel f` into the source of `f`.
-/
abbrev weakKernel.ι : weakKernel f ⟶ X :=
  weakEqualizer.ι f 0

@[simp]
/-
**CategoryTheory.Limits.weakEqualizer_as_weakKernel** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：weakEqualizer_as_weakKernel : weakEqualizer.ι f 0 = weakKernel.ι f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakEqualizer_as_weakKernel : weakEqualizer.ι f 0 = weakKernel.ι f := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.weakKernel.condition** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.weakKernel`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   {X Y : C} (f : X ⟶ Y) [inst_2 : Categ
oryTheory.Limits.HasWeakKernel f],   CategoryTheory.CategoryStruct.comp (Categor
yTheory.Limits.weakKernel.ι f) f = 0
参数：f : X ⟶ Y；CategoryTheory.Limits.weakKernel.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.KernelFork.condition`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
 {X Y : C}   {f : X ⟶ Y} (s : Ca…
-/
theorem weakKernel.condition : weakKernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The weak kernel built from `weakKernel.ι f` is weakly limiting. -/
/-
**CategoryTheory.Limits.weakKernelIsWeakKernel** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：weakKernelIsWeakKernel : IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKern
el.condition f).trans comp_zero.symm))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak kernel built from `weakKernel.ι f` is weakly limiting.
-/
def weakKernelIsWeakKernel :
    IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKernel.condition f).trans comp_zero.symm)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through
`weakKernel.ι f` via `weakKernel.lift : W ⟶ weakKernel f`. -/
/-
**CategoryTheory.Limits.weakKernel.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.weakKernel`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f 
: X ⟶ Y) →           [inst_2 : CategoryTheory.Limits.HasWeakKernel f] →         
    {W : C} →               (k : W ⟶ X) → CategoryTheory.CategoryStruct.comp k f
 = 0 → (W ⟶ CategoryTheory.Limits.weakKernel f)
参数：f : X ⟶ Y；k : W ⟶ X；W ⟶ CategoryTheory.Limits.weakKernel f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through
`weakKernel.ι f` via `weakKernel.lift : W ⟶ weakKernel f`.
-/
abbrev weakKernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ weakKernel f :=
  (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.weakKernel.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakKernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    weakKernel.lift f k h ≫ weakKernel.ι f = k :=
  (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ weakKernel f`
such that `l ≫ weakKernel.ι f = k`. -/
/-
**CategoryTheory.Limits.weakKernel.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.weakKernel`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {X Y : C} →         (f 
: X ⟶ Y) →           [inst_2 : CategoryTheory.Limits.HasWeakKernel f] →         
    {W : C} →               (k : W ⟶ X) →                 CategoryTheory.Categor
yStruct.comp k f = 0 →                   { l // CategoryTheory.CategoryStruct.co
mp l (CategoryTheory.Limits.weakKernel.ι f) = k }
参数：f : X ⟶ Y；k : W ⟶ X；CategoryTheory.Limits.weakKernel.ι f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.weakKernel.lift_ι`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {X Y : C} (f : X ⟶ Y) […

--- 原说明 ---
Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ weak
Kernel f`
such that `l ≫ weakKernel.ι f = k`.
-/
def weakKernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ weakKernel f // l ≫ weakKernel.ι f = k } :=
  ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

end

end Limits

namespace Preadditive

variable [Preadditive C] {X Y : C} {f g : X ⟶ Y}

/-- A weak kernel of `f - g` is a weak equalizer of `f` and `g`. -/
/-
**CategoryTheory.Preadditive.isWeakLimitForkOfKernelFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Preadditive`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X Y : C} →         {f g : X ⟶ Y} →
           {c : CategoryTheory.Limits.KernelFork (f - g)} →             Category
Theory.Limits.IsWeakLimit c →               CategoryTheory.Limits.IsWeakLimit (C
ategoryTheory.Preadditive.forkOfKernelFork c)
参数：f - g；CategoryTheory.Preadditive.forkOfKernelFork c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak kernel of `f - g` is a weak equalizer of `f` and `g`.
-/
def isWeakLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsWeakLimit c) :
    IsWeakLimit (forkOfKernelFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]
/-
**CategoryTheory.Preadditive.isWeakLimitForkOfKernelFork_lift** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Preadditive`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {X Y : C}   {f g : X ⟶ Y} {c : CategoryTheory.Limit
s.KernelFork (f - g)} (i : CategoryTheory.Limits.IsWeakLimit c)   (s : CategoryT
heory.Limits.Fork f g),   (CategoryTheory.Preadditive.isWeakLimitForkOfKernelFor
k i).lift s =     i.lift (CategoryTheory.Preadditive.kernelForkOfFork s)
参数：f - g；i : CategoryTheory.Limits.IsWeakLimit c；s : CategoryTheory.Limits.Fork 
f g；CategoryTheory.Preadditive.isWeakLimitForkOfKernelFork i；CategoryTheory.Prea
dditive.kernelForkOfFork s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isWeakLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsWeakLimit c)
    (s : Fork f g) : (isWeakLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

/-- A weak equalizer of `f` and `g` is a weak kernel of `f - g`. -/
/-
**CategoryTheory.Preadditive.isWeakLimitKernelForkOfFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Preadditive`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {X Y : C} →         {f g : X ⟶ Y} →
           {c : CategoryTheory.Limits.Fork f g} →             CategoryTheory.Lim
its.IsWeakLimit c →               CategoryTheory.Limits.IsWeakLimit (CategoryThe
ory.Preadditive.kernelForkOfFork c)
参数：CategoryTheory.Preadditive.kernelForkOfFork c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak equalizer of `f` and `g` is a weak kernel of `f - g`.
-/
def isWeakLimitKernelForkOfFork {c : Fork f g} (i : IsWeakLimit c) :
    IsWeakLimit (kernelForkOfFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

variable (f g)

/-- A preadditive category has a weak equalizer for `f` and `g` if it has a weak
kernel for `f - g`. -/
/-
**CategoryTheory.Preadditive.hasWeakEqualizer_of_hasWeakKernel** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Preadditive`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {X Y : C}   (f g : X ⟶ Y) [CategoryTheory.Limits.Ha
sWeakKernel (f - g)], CategoryTheory.Limits.HasWeakEqualizer f g
参数：f g : X ⟶ Y；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasWeakLimit.mk`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…
· 使用定理 `CategoryTheory.Limits.weakEqualizer.condition`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f g : X ⟶ Y)   [inst_1 : Catego
ryTheory.Limits.HasWeakEqualizer f …

--- 原说明 ---
A preadditive category has a weak equalizer for `f` and `g` if it has a weak
kernel for `f - g`.
-/
theorem hasWeakEqualizer_of_hasWeakKernel [HasWeakKernel (f - g)] : HasWeakEqualizer f g :=
  HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

/-- A preadditive category has a weak kernel for `f - g` if it has a weak equalizer
for `f` and `g`. -/
/-
**CategoryTheory.Preadditive.hasWeakKernel_of_hasWeakEqualizer** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Preadditive`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C] {X Y : C}   (f g : X ⟶ Y) [CategoryTheory.Limits.Ha
sWeakEqualizer f g], CategoryTheory.Limits.HasWeakKernel (f - g)
参数：f g : X ⟶ Y；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasWeakLimit.mk`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…

--- 原说明 ---
A preadditive category has a weak kernel for `f - g` if it has a weak equalizer
for `f` and `g`.
-/
theorem hasWeakKernel_of_hasWeakEqualizer [HasWeakEqualizer f g] : HasWeakKernel (f - g) :=
  HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

/-- If a preadditive category has all weak kernels, then it also has all weak equalizers. -/
/-
**CategoryTheory.Preadditive.hasWeakEqualizers_of_hasWeakKernels** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Preadditive`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [CategoryTheory.Limits.HasWeakKernels C], Categor
yTheory.Limits.HasWeakEqualizers C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.hasWeakEqualizer_of_hasWeakKernel`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C] {X Y : C}   (f g : X ⟶ Y) [CategoryTh…
· 使用定理 `CategoryTheory.Limits.HasWeakKernels.hasWeakLimit`：∀ {C : Type u_1} {ins
t : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C}   [self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasWeakEqualizers_of_hasWeakLimit_parallelPair`：ha
sWeakEqualizers_of_hasWeakLimit_parallelPair [forall {X Y : C} {f g : X ⟶ Y}, Ha
sWeakLimit (parallelPair f g)] : HasWeakEqualizers C where…

--- 原说明 ---
If a preadditive category has all weak kernels, then it also has all weak equali
zers.
-/
theorem hasWeakEqualizers_of_hasWeakKernels [HasWeakKernels C] : HasWeakEqualizers C :=
  have {X Y : C} (f g : X ⟶ Y) := hasWeakEqualizer_of_hasWeakKernel f g
  hasWeakEqualizers_of_hasWeakLimit_parallelPair C

end Preadditive

end CategoryTheory

