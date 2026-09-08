/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# (Co)kernels in functor categories
-/

@[expose] public section

namespace CategoryTheory.Limits
universe u
variable (C : Type*) [Category.{u} C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel inclusion is itself a kernel in the functor category. -/
/-
**CategoryTheory.Limits.kerIsKernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：kerIsKernel [HasKernels C] : IsLimit (KernelFork.ofι (ker.ι C) (ker.condit
ion C))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ker.condition`：∀ (C : Type u) [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   [ins
t_2 : CategoryTheory.Limi…

--- 原说明 ---
The kernel inclusion is itself a kernel in the functor category.
-/
noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
  evaluationJointlyReflectsLimits _ fun f ↦ (KernelFork.isLimitMapConeEquiv ..).2 <|
    (kernelIsKernel f.hom).ofIsoLimit <| Fork.ext <| .refl _

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel projection is itself a cokernel in the functor category. -/
/-
**CategoryTheory.Limits.cokerIsCokernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：cokerIsCokernel [HasCokernels C] : IsColimit (CokernelCofork.ofπ (coker.π 
C) (coker.condition C))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coker.condition`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   [i
nst_2 : CategoryTheory.Limi…

--- 原说明 ---
The cokernel projection is itself a cokernel in the functor category.
-/
noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
  evaluationJointlyReflectsColimits _ fun f ↦ (CokernelCofork.isColimitMapCoconeEquiv ..).2 <|
    (cokernelIsCokernel f.hom).ofIsoColimit <| Cofork.ext <| .refl _

end CategoryTheory.Limits

