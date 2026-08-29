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

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall n : Int, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/--
Definition of `kernelForkOfDistTriangle` / `kernelForkOfDistTriangle` 的定义

English:
definition kernelForkOfDistTriangle
  signature: (T : Triangle C) (dT : T in distTriang C)
  body: KernelFork.ofι T.mor₁ (comp_distTriang_mor_zero₁₂ _ dT)

中文:
定义 kernelForkOfDistTriangle
  签名: (T : Triangle C) (dT : T in distTriang C)
  定义体: KernelFork.ofι T.mor₁ (comp_distTriang_mor_zero₁₂ _ dT)

Depends on / 依赖: KernelFork, KernelFork.of, T.mor
-/
def kernelForkOfDistTriangle (T : Triangle C) (dT : T in distTriang C) :
    KernelFork T.mor₂ := KernelFork.ofι T.mor₁ (comp_distTriang_mor_zero₁₂ _ dT)

/--
Definition of `isWeakLimitKernelForkOfDistTriangle` / `isWeakLimitKernelForkOfDistTriangle` 的定义

English:
definition isWeakLimitKernelForkOfDistTriangle
  signature: (T : Triangle C) (dT : T in distTriang C)
  body: Fork.IsWeakLimit.mk' _
    (fun s => ⟨_, (T.coyoneda_exact₂ dT _ (KernelFork.condition s)).choose_spec.symm⟩)

中文:
定义 isWeakLimitKernelForkOfDistTriangle
  签名: (T : Triangle C) (dT : T in distTriang C)
  定义体: Fork.IsWeakLimit.mk' _
    (fun s => ⟨_, (T.coyoneda_exact₂ dT _ (KernelFork.condition s)).choose_spec.symm⟩)

Depends on / 依赖: Fork.IsWeakLimit.mk, IsWeakLimit, KernelFork, KernelFork.condition, T.coyoneda_exact, choose_spec, choose_spec.symm, condition
-/
def isWeakLimitKernelForkOfDistTriangle (T : Triangle C) (dT : T in distTriang C) :
    IsWeakLimit (kernelForkOfDistTriangle _ dT) :=
  Fork.IsWeakLimit.mk' _
    (fun s => ⟨_, (T.coyoneda_exact₂ dT _ (KernelFork.condition s)).choose_spec.symm⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasWeakKernels C
  body: ⟨by
    obtain ⟨K, i, p, h⟩ := distinguished_cocone_triangle₁ f
    exact ⟨_, isWeakLimitKernelForkOfDistTriangle _ h⟩⟩

中文:
实例 :
  签名: HasWeakKernels C
  定义体: ⟨by
    obtain ⟨K, i, p, h⟩ := distinguished_cocone_triangle₁ f
    exact ⟨_, isWeakLimitKernelForkOfDistTriangle _ h⟩⟩

Depends on / 依赖: isWeakLimitKernelForkOfDistTriangle
-/
instance : HasWeakKernels C where
  hasWeakLimit f := ⟨by
    obtain ⟨K, i, p, h⟩ := distinguished_cocone_triangle₁ f
    exact ⟨_, isWeakLimitKernelForkOfDistTriangle _ h⟩⟩

end CategoryTheory.Pretriangulated
