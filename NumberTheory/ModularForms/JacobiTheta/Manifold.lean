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

/--
theorem `mdifferentiable_jacobiTheta` / 定理 `mdifferentiable_jacobiTheta`

English:
theorem mdifferentiable_jacobiTheta
  statement: MDiff (jacobiTheta ∘ (↑) : ℍ -> Complex)
  proof: fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe

中文:
定理 mdifferentiable_jacobiTheta
  结论: MDiff (jacobiTheta ∘ (↑) : ℍ -> 复形)
  证明: fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe

Depends on / 依赖: differentiableAt_jacobiTheta, mdifferentiableAt, mdifferentiableAt.comp, mdifferentiable_coe
-/
theorem mdifferentiable_jacobiTheta : MDiff (jacobiTheta ∘ (↑) : ℍ -> Complex) :=
  fun τ => (differentiableAt_jacobiTheta τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
