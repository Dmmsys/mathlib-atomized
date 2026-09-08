/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Manifold differentiability of the Jacobi theta function

In this file we reformulate differentiability of the Jacobi theta function in terms of manifold
differentiability.

## TODO

Prove smoothness (in terms of `Smooth`).
-/

public section


open scoped UpperHalfPlane Manifold

/-
**mdifferentiable_jacobiTheta** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `DifferentiableAt.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `differentiableAt_jacobiTheta`：differentiableAt_jacobiTheta {τ : Complex}
 (hτ : 0 < im τ) : DifferentiableAt Complex jacobiTheta τ
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `UpperHalfPlane.mdifferentiable_coe`：mdifferentiable_coe : MDiff ((↑) : ℍ
 -> Complex)
-/
theorem mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
