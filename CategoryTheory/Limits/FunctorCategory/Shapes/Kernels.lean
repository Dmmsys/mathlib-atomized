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
/--
Definition of `kerIsKernel` / `kerIsKernel` 的定义

English:
definition kerIsKernel
  signature: [HasKernels C]
  body: evaluationJointlyReflectsLimits _ fun f => (KernelFork.isLimitMapConeEquiv ..).2
(kernelIsKernel f.hom).ofIsoLimit Fork.ext .refl _

中文:
定义 kerIsKernel
  签名: [HasKernels C]
  定义体: evaluationJointlyReflectsLimits _ fun f => (KernelFork.isLimitMapConeEquiv ..).2
(kernelIsKernel f.hom).ofIsoLimit Fork.ext .refl _

Depends on / 依赖: Fork.ext, KernelFork, KernelFork.isLimitMapConeEquiv, evaluationJointlyReflectsLimits, f.hom, isLimitMapConeEquiv, kernelIsKernel, ofIsoLimit
-/
noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
evaluationJointlyReflectsLimits _ fun f => (KernelFork.isLimitMapConeEquiv ..).2
(kernelIsKernel f.hom).ofIsoLimit Fork.ext .refl _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cokerIsCokernel` / `cokerIsCokernel` 的定义

English:
definition cokerIsCokernel
  signature: [HasCokernels C]
  body: evaluationJointlyReflectsColimits _ fun f => (CokernelCofork.isColimitMapCoconeEquiv ..).2
(cokernelIsCokernel f.hom).ofIsoColimit Cofork.ext .refl _

中文:
定义 cokerIsCokernel
  签名: [HasCokernels C]
  定义体: evaluationJointlyReflectsColimits _ fun f => (CokernelCofork.isColimitMapCoconeEquiv ..).2
(cokernelIsCokernel f.hom).ofIsoColimit Cofork.ext .refl _

Depends on / 依赖: Cofork, Cofork.ext, CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, cokernelIsCokernel, evaluationJointlyReflectsColimits, f.hom, isColimitMapCoconeEquiv, ofIsoColimit
-/
noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
evaluationJointlyReflectsColimits _ fun f => (CokernelCofork.isColimitMapCoconeEquiv ..).2
(cokernelIsCokernel f.hom).ofIsoColimit Cofork.ext .refl _

end CategoryTheory.Limits
