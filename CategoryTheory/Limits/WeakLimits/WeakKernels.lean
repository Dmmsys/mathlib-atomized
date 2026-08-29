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

/--
Definition of `HasWeakKernel` / `HasWeakKernel` 的定义

English:
abbreviation HasWeakKernel
  signature: : Prop
  body: HasWeakLimit (parallelPair f 0)

中文:
缩写 HasWeakKernel
  签名: : 命题
  定义体: HasWeakLimit (parallelPair f 0)

Depends on / 依赖: HasWeakLimit, parallelPair
-/
abbrev HasWeakKernel : Prop :=
  HasWeakLimit (parallelPair f 0)

variable (C) in
/--
Definition of `HasWeakKernels` / `HasWeakKernels` 的定义

English:
class HasWeakKernels
  parameters: : Prop where
  axioms and operations (1):
    - hasWeakLimit : forall {X Y : C} (f : X ⟶ Y), HasWeakKernel f  [default: by infer_instance]

中文:
类 HasWeakKernels
  参数: : 命题 where
  公理与运算 (1 个):
    - hasWeakLimit : 对任意 {X Y : C} (f : X ⟶ Y), HasWeakKernel f  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasWeakKernels : Prop where
  hasWeakLimit : forall {X Y : C} (f : X ⟶ Y), HasWeakKernel f := by infer_instance

attribute [instance 100] HasWeakKernels.hasWeakLimit

/-- If a category has kernels, then it has weak kernels. -/
instance (priority := 100) HasWeakKernelsOfHasKernels [HasKernels C] :
    HasWeakKernels C where

section

variable [HasWeakKernel f]

/--
Definition of `weakKernel` / `weakKernel` 的定义

English:
abbreviation weakKernel
  signature: : C
  body: weakEqualizer f 0

中文:
缩写 weakKernel
  签名: : C
  定义体: weakEqualizer f 0

Depends on / 依赖: weakEqualizer
-/
abbrev weakKernel : C :=
  weakEqualizer f 0

/--
Definition of `weakKernel.ι` / `weakKernel.ι` 的定义

English:
abbreviation weakKernel.ι
  signature: : weakKernel f ⟶ X
  body: weakEqualizer.ι f 0

@[simp]

中文:
缩写 weakKernel.ι
  签名: : weakKernel f ⟶ X
  定义体: weakEqualizer.ι f 0

@[simp]

Depends on / 依赖: weakEqualizer
-/
abbrev weakKernel.ι : weakKernel f ⟶ X :=
  weakEqualizer.ι f 0

@[simp]
/--
theorem `weakEqualizer_as_weakKernel` / 定理 `weakEqualizer_as_weakKernel`

English:
theorem weakEqualizer_as_weakKernel
  statement: weakEqualizer.ι f 0 = weakKernel.ι f
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 weakEqualizer_as_weakKernel
  结论: weakEqualizer.ι f 0 = weakKernel.ι f
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem weakEqualizer_as_weakKernel : weakEqualizer.ι f 0 = weakKernel.ι f := rfl

@[reassoc (attr := simp)]
/--
theorem `weakKernel.condition` / 定理 `weakKernel.condition`

English:
theorem weakKernel.condition
  statement: weakKernel.ι f ≫ f = 0
  proof: KernelFork.condition _

中文:
定理 weakKernel.condition
  结论: weakKernel.ι f ≫ f = 0
  证明: KernelFork.condition _

Depends on / 依赖: KernelFork, KernelFork.condition, condition
-/
theorem weakKernel.condition : weakKernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `weakKernelIsWeakKernel` / `weakKernelIsWeakKernel` 的定义

English:
definition weakKernelIsWeakKernel
  signature: :
  body: IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

中文:
定义 weakKernelIsWeakKernel
  签名: :
  定义体: IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

Depends on / 依赖: F.preservesColimitsOfShape_of_isCardinalAccessible, Fork.ext, G.preservesColimitsOfShape_of_isCardinalAccessible, IsWeakLimit, IsWeakLimit.ofIsoWeakLimit, Iso.refl, isWeakLimit, ofIsoWeakLimit, preservesColimitsOfShape_of_isCardinalAccessible, weakLimit, weakLimit.isWeakLimit
-/
def weakKernelIsWeakKernel :
    IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKernel.condition f).trans comp_zero.symm)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

/--
Definition of `weakKernel.lift` / `weakKernel.lift` 的定义

English:
abbreviation weakKernel.lift
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  body: (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]

中文:
缩写 weakKernel.lift
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  定义体: (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.IsEventuallyConstantFrom.isColimitOfIsIso, IsEventuallyConstantFrom, KernelFork, KernelFork.of, h.nonempty.some, infer_instance, isColimitOfIsIso, isFiltered_of_isCardinalFiltered, mapCocone, nonempty, preserves, preservesColimit, weakKernelIsWeakKernel
-/
abbrev weakKernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ weakKernel f :=
  (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
/--
theorem `weakKernel.lift_ι` / 定理 `weakKernel.lift_ι`

English:
theorem weakKernel.lift_ι
  given: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  proof: (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

中文:
定理 weakKernel.lift_ι
  条件: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  证明: (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

Depends on / 依赖: KernelFork, KernelFork.of, WalkingParallelPair, WalkingParallelPair.zero, weakKernelIsWeakKernel
-/
theorem weakKernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    weakKernel.lift f k h ≫ weakKernel.ι f = k :=
  (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

/--
Definition of `weakKernel.lift'` / `weakKernel.lift'` 的定义

English:
definition weakKernel.lift'
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  body: ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

中文:
定义 weakKernel.lift'
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = 0)
  定义体: ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

Depends on / 依赖: Fact.out, IsAccessible, IsAccessible.exists_cardinal, IsRegular, exists_cardinal, isAccessible_of_isCardinalAccessible, isCardinalAccessible_of_le, iteInduction, weakKernel, weakKernel.lift, weakKernel.lift_
-/
def weakKernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ weakKernel f // l ≫ weakKernel.ι f = k } :=
  ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

end

end Limits

namespace Preadditive

variable [Preadditive C] {X Y : C} {f g : X ⟶ Y}

/--
Definition of `isWeakLimitForkOfKernelFork` / `isWeakLimitForkOfKernelFork` 的定义

English:
definition isWeakLimitForkOfKernelFork
  signature: {c : KernelFork (f - g)} (i : IsWeakLimit c)
  body: Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]

中文:
定义 isWeakLimitForkOfKernelFork
  签名: {c : KernelFork (f - g)} (i : IsWeakLimit c)
  定义体: Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]

Depends on / 依赖: Cardinal, Cardinal.aleph0, Cardinal.aleph0.IsRegular, Cardinal.fact_isRegular_aleph0, Fork.IsWeakLimit.mk, IsRegular, IsWeakLimit, aleph0, fact_isRegular_aleph0, i.fac, i.lift, kernelForkOfFork
-/
def isWeakLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsWeakLimit c) :
    IsWeakLimit (forkOfKernelFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]
/--
theorem `isWeakLimitForkOfKernelFork_lift` / 定理 `isWeakLimitForkOfKernelFork_lift`

English:
theorem isWeakLimitForkOfKernelFork_lift
  statement: {c : KernelFork (f - g)} (i : IsWeakLimit c)
  proof: rfl

中文:
定理 isWeakLimitForkOfKernelFork_lift
  结论: {c : KernelFork (f - g)} (i : IsWeakLimit c)
  证明: rfl
-/
theorem isWeakLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsWeakLimit c)
    (s : Fork f g) : (isWeakLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

/--
Definition of `isWeakLimitKernelForkOfFork` / `isWeakLimitKernelForkOfFork` 的定义

English:
definition isWeakLimitKernelForkOfFork
  signature: {c : Fork f g} (i : IsWeakLimit c)
  body: Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

中文:
定义 isWeakLimitKernelForkOfFork
  签名: {c : Fork f g} (i : IsWeakLimit c)
  定义体: Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

Depends on / 依赖: Fork.IsWeakLimit.mk, IsWeakLimit, forkOfKernelFork, i.fac, i.lift
-/
def isWeakLimitKernelForkOfFork {c : Fork f g} (i : IsWeakLimit c) :
    IsWeakLimit (kernelForkOfFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

variable (f g)

/--
theorem `hasWeakEqualizer_of_hasWeakKernel` / 定理 `hasWeakEqualizer_of_hasWeakKernel`

English:
theorem hasWeakEqualizer_of_hasWeakKernel
  given: [HasWeakKernel (f - g)]
  statement: HasWeakEqualizer f g
  proof: HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

中文:
定理 hasWeakEqualizer_of_hasWeakKernel
  条件: [HasWeakKernel (f - g)]
  结论: HasWeakEqualizer f g
  证明: HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

Depends on / 依赖: HasWeakLimit, HasWeakLimit.mk, X.property, forkOfKernelFork, isWeakLimit, isWeakLimitForkOfKernelFork, property, weakEqualizerIsWeakEqualizer
-/
theorem hasWeakEqualizer_of_hasWeakKernel [HasWeakKernel (f - g)] : HasWeakEqualizer f g :=
  HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

/--
theorem `hasWeakKernel_of_hasWeakEqualizer` / 定理 `hasWeakKernel_of_hasWeakEqualizer`

English:
theorem hasWeakKernel_of_hasWeakEqualizer
  given: [HasWeakEqualizer f g]
  statement: HasWeakKernel (f - g)
  proof: HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

中文:
定理 hasWeakKernel_of_hasWeakEqualizer
  条件: [HasWeakEqualizer f g]
  结论: HasWeakKernel (f - g)
  证明: HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

Depends on / 依赖: HasWeakLimit, HasWeakLimit.mk, infer_instance, isWeakLimit, isWeakLimitKernelForkOfFork, kernelForkOfFork, parallelPair, weakEqualizer, weakEqualizer.fork, weakLimit, weakLimit.isWeakLimit
-/
theorem hasWeakKernel_of_hasWeakEqualizer [HasWeakEqualizer f g] : HasWeakKernel (f - g) :=
  HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

/--
theorem `hasWeakEqualizers_of_hasWeakKernels` / 定理 `hasWeakEqualizers_of_hasWeakKernels`

English:
theorem hasWeakEqualizers_of_hasWeakKernels
  given: [HasWeakKernels C]
  statement: HasWeakEqualizers C
  proof: have {X Y : C} (f g : X ⟶ Y) := hasWeakEqualizer_of_hasWeakKernel f g
  hasWeakEqualizers_of_hasWeakLimit_parallelPair C

中文:
定理 hasWeakEqualizers_of_hasWeakKernels
  条件: [HasWeakKernels C]
  结论: HasWeakEqualizers C
  证明: have {X Y : C} (f g : X ⟶ Y) := hasWeakEqualizer_of_hasWeakKernel f g
  hasWeakEqualizers_of_hasWeakLimit_parallelPair C

Depends on / 依赖: hasWeakEqualizer_of_hasWeakKernel, hasWeakEqualizers_of_hasWeakLimit_parallelPair
-/
theorem hasWeakEqualizers_of_hasWeakKernels [HasWeakKernels C] : HasWeakEqualizers C :=
  have {X Y : C} (f g : X ⟶ Y) := hasWeakEqualizer_of_hasWeakKernel f g
  hasWeakEqualizers_of_hasWeakLimit_parallelPair C

end Preadditive

end CategoryTheory
