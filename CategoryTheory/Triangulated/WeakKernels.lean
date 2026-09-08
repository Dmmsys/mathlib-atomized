/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels

/-!
# Weak kernels in pretriangulated categories

We prove that pretriangulated categories have weak kernels: if `f : X ⟶ Y` is a morphism in
a pretriangulated category and if we complete it to a distinguished triangle
`Z ⟶ X ⟶ Y ⟶ Z⟦1⟧`, then the first morphism `Z ⟶ Y` of that triangle is a weak kernel of `f`.

TODO: Weak cokernels.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Pretriangulated

open Limits Category Preadditive Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- If `T` is a distinguished triangle, then `T.mor₁` defines a kernel fork for `T.mor₂`. -/
/-
**CategoryTheory.Pretriangulated.kernelForkOfDistTriangle** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：kernelForkOfDistTriangle (T : Triangle C) (dT : T in distTriang C) : Kerne
lFork T.mor₂
参数：T : Triangle C；dT : T in distTriang C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`：comp_distTria
ng_mor_zero₁₂ (T) (H : T in distTriang C) : T.mor₁ ≫ T.mor₂ = 0

--- 原说明 ---
If `T` is a distinguished triangle, then `T.mor₁` defines a kernel fork for `T.m
or₂`.
-/
def kernelForkOfDistTriangle (T : Triangle C) (dT : T ∈ distTriang C) :
    KernelFork T.mor₂ := KernelFork.ofι T.mor₁ (comp_distTriang_mor_zero₁₂ _ dT)

/-- If `T` is a distinguished triangle, then the kernel fork for `T.mor₂` defined in
`kernelForkOfDistTriangle` is a weak kernel fork. -/
/-
**CategoryTheory.Pretriangulated.isWeakLimitKernelForkOfDistTriangle** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：isWeakLimitKernelForkOfDistTriangle (T : Triangle C) (dT : T in distTriang
 C) : IsWeakLimit (kernelForkOfDistTriangle _ dT)
参数：T : Triangle C；dT : T in distTriang C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `T` is a distinguished triangle, then the kernel fork for `T.mor₂` defined in
`kernelForkOfDistTriangle` is a weak kernel fork.
-/
def isWeakLimitKernelForkOfDistTriangle (T : Triangle C) (dT : T ∈ distTriang C) :
    IsWeakLimit (kernelForkOfDistTriangle _ dT) :=
  Fork.IsWeakLimit.mk' _
    (fun s ↦ ⟨_, (T.coyoneda_exact₂ dT _ (KernelFork.condition s)).choose_spec.symm⟩)

/-- A pretriangulated category has weak kernels. -/
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pretriangulated category has weak kernels.
-/
instance : HasWeakKernels C where
  hasWeakLimit f := ⟨by
    obtain ⟨K, i, p, h⟩ := distinguished_cocone_triangle₁ f
    exact ⟨_, isWeakLimitKernelForkOfDistTriangle _ h⟩⟩

end CategoryTheory.Pretriangulated

