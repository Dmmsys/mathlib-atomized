/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Quadratic Algebra

We prove that the expression for the norm of an element in a quadratic algebra comes from looking at
the endomorphism defined by left multiplication by that element and taking its determinant.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The norm of an element in a quadratic algebra is the determinant of the endomorphism defined by
left multiplication by that element. -/
@[simp]
/--
theorem `det_toLinearMap_eq_norm` / 定理 `det_toLinearMap_eq_norm`

English:
theorem det_toLinearMap_eq_norm
  given: (z : QuadraticAlgebra R a b)
  proof: by
  rw [← LinearMap.det_toMatrix <| basis ..]
  have : !![z.re, a * z.im; z.im, z.re + b * z.im].det = z.norm := by
    simp [norm]
    ring
  convert! this
.mp apply LinearEquiv.eq_symm_apply _
  ext1 w
.repr.injective apply basis ..
  apply DFunLike.coe_injective
  rw [LinearMap.toMatrix_symm]; r

中文:
定理 det_toLinearMap_eq_norm
  条件: (z : 二次代数 R a b)
  证明: by
  rw [← LinearMap.det_toMatrix <| basis ..]
  have : !![z.re, a * z.im; z.im, z.re + b * z.im].det = z.norm := by
    simp [norm]
    ring
  convert! this
.mp apply LinearEquiv.eq_symm_apply _
  ext1 w
.repr.injective apply basis ..
  apply DFunLike.coe_injective
  rw [LinearMap.toMatrix_symm]; r

Depends on / 依赖: DFunLike, DFunLike.coe_injective, LinearEquiv, LinearEquiv.eq_symm_apply, LinearMap, LinearMap.det_toMatrix, LinearMap.toMatrix_symm, Matrix, Matrix.repr_toLin, coe_injective, convert, det_toMatrix, eq_symm_apply, fin_cases, injective, repr.injective, repr_toLin, toMatrix_symm, z.im, z.norm
-/
theorem det_toLinearMap_eq_norm (z : QuadraticAlgebra R a b) :
    (DistribSMul.toLinearMap R (QuadraticAlgebra R a b) z).det = z.norm := by
  rw [← LinearMap.det_toMatrix <| basis ..]
  have : !![z.re, a * z.im; z.im, z.re + b * z.im].det = z.norm := by
    simp [norm]
    ring
  convert! this
.mp apply LinearEquiv.eq_symm_apply _
  ext1 w
.repr.injective apply basis ..
  apply DFunLike.coe_injective
  rw [LinearMap.toMatrix_symm]; rw [Matrix.repr_toLin]
  ext i
  fin_cases i
    <;> simp
    <;> ring

end QuadraticAlgebra
