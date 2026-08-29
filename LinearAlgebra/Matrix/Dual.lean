/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dual space, linear maps and matrices.

This file contains some results about matrices and dual spaces.

## Tags

matrix, linear map, transpose, dual
-/

@[expose] public section

open Matrix Module

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type*} [CommSemiring K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

@[simp]
/--
theorem `LinearMap.toMatrix_transpose` / 定理 `LinearMap.toMatrix_transpose`

English:
theorem LinearMap.toMatrix_transpose
  given: (u : V₁ ->ₗ[K] V₂)
  proof: by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

@[simp]

中文:
定理 LinearMap.toMatrix_transpose
  条件: (u : V₁ ->ₗ[K] V₂)
  证明: by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

@[simp]
-/
theorem LinearMap.toMatrix_transpose (u : V₁ ->ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R := K) u) =
      (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

@[simp]
/--
theorem `Matrix.toLin_transpose` / 定理 `Matrix.toLin_transpose`

English:
theorem Matrix.toLin_transpose
  given: (M : Matrix ι₁ ι₂ K)
  statement: Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
  proof: by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  rw [LinearMap.toMatrix_toLin]; rw [LinearMap.toMatrix_transpose]; rw [LinearMap.toMatrix_toLin]

中文:
定理 Matrix.toLin_transpose
  条件: (M : Matrix ι₁ ι₂ K)
  结论: Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
  证明: by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  rw [LinearMap.toMatrix_toLin]; rw [LinearMap.toMatrix_transpose]; rw [LinearMap.toMatrix_toLin]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_toLin, LinearMap.toMatrix_transpose, Matrix, Matrix.toLin, dualBasis, injective, toMatrix, toMatrix_toLin, toMatrix_transpose
-/
theorem Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
    Module.Dual.transpose (R := K) (Matrix.toLin B₂ B₁ M) := by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  rw [LinearMap.toMatrix_toLin]; rw [LinearMap.toMatrix_transpose]; rw [LinearMap.toMatrix_toLin]

end Transpose

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `dotProductEquiv` / `dotProductEquiv` 的定义

English:
definition dotProductEquiv
  signature: (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]
  body: ⟨⟨dotProduct v, dotProduct_add v⟩, fun t => dotProduct_smul t v⟩
  map_add' v w := by ext; simp
  map_smul' t v := by ext; simp
  invFun f i := f (LinearMap.single R _ i 1)
  left_inv v := by simp
  right_inv f := by ext; simp

中文:
定义 dotProductEquiv
  签名: (R n : 类型) [CommSemiring R] [Fintype n] [DecidableEq n]
  定义体: ⟨⟨dotProduct v, dotProduct_add v⟩, fun t => dotProduct_smul t v⟩
  map_add' v w := by ext; simp
  map_smul' t v := by ext; simp
  invFun f i := f (LinearMap.single R _ i 1)
  left_inv v := by simp
  right_inv f := by ext; simp
-/
@[simps] def dotProductEquiv (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n] :
    (n -> R) ≃ₗ[R] Module.Dual R (n -> R) where
  toFun v := ⟨⟨dotProduct v, dotProduct_add v⟩, fun t => dotProduct_smul t v⟩
  map_add' v w := by ext; simp
  map_smul' t v := by ext; simp
  invFun f i := f (LinearMap.single R _ i 1)
  left_inv v := by simp
  right_inv f := by ext; simp
