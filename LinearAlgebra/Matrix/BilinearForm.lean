/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Bilinear form

This file defines the conversion between bilinear forms and matrices.

## Main definitions

* `Matrix.toBilin` given a basis define a bilinear form
* `Matrix.toBilin'` define the bilinear form on `n → R`
* `BilinForm.toMatrix`: calculate the matrix coefficients of a bilinear form
* `BilinForm.toMatrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notation

In this file we use the following type variables:
- `M₁` is a module over the commutative semiring `R₁`,
- `M₂` is a module over the commutative ring `R₂`.

## Tags

bilinear form, bilin form, BilinearForm, matrix, basis

-/

@[expose] public section

open LinearMap (BilinForm)
open Module

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]
variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

section Matrix

variable {n o : Type*}

open Finset LinearMap Matrix

open Matrix

/--
Definition of `Matrix.toBilin'Aux` / `Matrix.toBilin'Aux` 的定义

English:
definition Matrix.toBilin'Aux
  signature: [Fintype n] (M : Matrix n n R₁)
  body: Matrix.toLinearMap₂'Aux _ _ M

中文:
定义 Matrix.toBilin'Aux
  签名: [Fintype n] (M : Matrix n n R₁)
  定义体: Matrix.toLinearMap₂'Aux _ _ M

Depends on / 依赖: Matrix, Matrix.toLinearMap
-/
def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₁) : BilinForm R₁ (n -> R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M

/--
theorem `Matrix.toBilin'Aux_single` / 定理 `Matrix.toBilin'Aux_single`

English:
theorem Matrix.toBilin'Aux_single
  given: [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n)
  proof: Matrix.toLinearMap₂'Aux_single _ _ _ _ _

中文:
定理 Matrix.toBilin'Aux_single
  条件: [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n)
  证明: Matrix.toLinearMap₂'Aux_single _ _ _ _ _
-/
theorem Matrix.toBilin'Aux_single [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n) :
    M.toBilin'Aux (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ _ _ _

/--
Definition of `LinearMap.BilinForm.toMatrixAux` / `LinearMap.BilinForm.toMatrixAux` 的定义

English:
definition LinearMap.BilinForm.toMatrixAux
  signature: (b : n -> M₁)
  body: LinearMap.toMatrix₂Aux R₁ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrixAux := LinearMap.BilinForm.toMatrixAux

@[simp]

中文:
定义 LinearMap.BilinForm.toMatrixAux
  签名: (b : n -> M₁)
  定义体: LinearMap.toMatrix₂Aux R₁ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrixAux := LinearMap.BilinForm.toMatrixAux

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
def LinearMap.BilinForm.toMatrixAux (b : n -> M₁) : BilinForm R₁ M₁ ->ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂Aux R₁ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrixAux := LinearMap.BilinForm.toMatrixAux

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrixAux_apply` / 定理 `LinearMap.BilinForm.toMatrixAux_apply`

English:
theorem LinearMap.BilinForm.toMatrixAux_apply
  given: (B : BilinForm R₁ M₁) (b : n -> M₁) (i j : n)
  proof: LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

中文:
定理 LinearMap.BilinForm.toMatrixAux_apply
  条件: (B : BilinForm R₁ M₁) (b : n -> M₁) (i j : n)
  证明: LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₁ M₁) (b : n -> M₁) (i j : n) :
    BilinForm.toMatrixAux b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

variable [Fintype n] [Fintype o]

/--
theorem `LinearMap.toBilin'Aux_toMatrixAux` / 定理 `LinearMap.toBilin'Aux_toMatrixAux`

English:
theorem LinearMap.toBilin'Aux_toMatrixAux
  given: [DecidableEq n] (B₂ : BilinForm R₁ (n -> R₁))
  proof: by
  rw [BilinForm.toMatrixAux]; rw [Matrix.toBilin'Aux]; rw [toLinearMap₂'Aux_toMatrix₂Aux]

@[deprecated (since := "2026-01-16")] alias toBilin'Aux_toMatrixAux :=
  LinearMap.toBilin'Aux_toMatrixAux

中文:
定理 LinearMap.toBilin'Aux_toMatrixAux
  条件: [DecidableEq n] (B₂ : BilinForm R₁ (n -> R₁))
  证明: by
  rw [BilinForm.toMatrixAux]; rw [Matrix.toBilin'Aux]; rw [toLinearMap₂'Aux_toMatrix₂Aux]

@[deprecated (since := "2026-01-16")] alias toBilin'Aux_toMatrixAux :=
  LinearMap.toBilin'Aux_toMatrixAux

Depends on / 依赖: BilinForm, BilinForm.toMatrixAux, Matrix, Matrix.toBilin, toBilin, toMatrixAux
-/
theorem LinearMap.toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₁ (n -> R₁)) :
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (fun j => Pi.single j 1) B₂) = B₂ := by
  rw [BilinForm.toMatrixAux]; rw [Matrix.toBilin'Aux]; rw [toLinearMap₂'Aux_toMatrix₂Aux]

@[deprecated (since := "2026-01-16")] alias toBilin'Aux_toMatrixAux :=
  LinearMap.toBilin'Aux_toMatrixAux

section ToMatrix'

/-! ### `ToMatrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/


variable [DecidableEq n] [DecidableEq o]

/--
Definition of `LinearMap.BilinForm.toMatrix'` / `LinearMap.BilinForm.toMatrix'` 的定义

English:
definition LinearMap.BilinForm.toMatrix'
  signature: : BilinForm R₁ (n -> R₁) ≃ₗ[R₁] Matrix n n R₁
  body: LinearMap.toMatrix₂' R₁

中文:
定义 LinearMap.BilinForm.toMatrix'
  签名: : BilinForm R₁ (n -> R₁) ≃ₗ[R₁] Matrix n n R₁
  定义体: LinearMap.toMatrix₂' R₁

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
def LinearMap.BilinForm.toMatrix' : BilinForm R₁ (n -> R₁) ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂' R₁

/--
Definition of `Matrix.toBilin'` / `Matrix.toBilin'` 的定义

English:
definition Matrix.toBilin'
  signature: : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ (n -> R₁)
  body: BilinForm.toMatrix'.symm

@[simp]

中文:
定义 Matrix.toBilin'
  签名: : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ (n -> R₁)
  定义体: BilinForm.toMatrix'.symm

@[simp]
-/
def Matrix.toBilin' : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ (n -> R₁) :=
  BilinForm.toMatrix'.symm

@[simp]
/--
theorem `Matrix.toBilin'Aux_eq` / 定理 `Matrix.toBilin'Aux_eq`

English:
theorem Matrix.toBilin'Aux_eq
  given: (M : Matrix n n R₁)
  statement: Matrix.toBilin'Aux M = Matrix.toBilin' M
  proof: rfl

中文:
定理 Matrix.toBilin'Aux_eq
  条件: (M : Matrix n n R₁)
  结论: Matrix.toBilin'Aux M = Matrix.toBilin' M
  证明: rfl
-/
theorem Matrix.toBilin'Aux_eq (M : Matrix n n R₁) : Matrix.toBilin'Aux M = Matrix.toBilin' M :=
  rfl

/--
theorem `Matrix.toBilin'_apply` / 定理 `Matrix.toBilin'_apply`

English:
theorem Matrix.toBilin'_apply
  given: (M : Matrix n n R₁) (x y : n -> R₁)
  proof: (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

中文:
定理 Matrix.toBilin'_apply
  条件: (M : Matrix n n R₁) (x y : n -> R₁)
  证明: (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])
-/
theorem Matrix.toBilin'_apply (M : Matrix n n R₁) (x y : n -> R₁) :
    Matrix.toBilin' M x y = ∑ i, ∑ j, x i * M i j * y j :=
  (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

/--
theorem `Matrix.toBilin'_apply'` / 定理 `Matrix.toBilin'_apply'`

English:
theorem Matrix.toBilin'_apply'
  given: (M : Matrix n n R₁) (v w : n -> R₁)
  proof: Matrix.toLinearMap₂'_apply' _ _ _

@[simp]

中文:
定理 Matrix.toBilin'_apply'
  条件: (M : Matrix n n R₁) (v w : n -> R₁)
  证明: Matrix.toLinearMap₂'_apply' _ _ _

@[simp]
-/
theorem Matrix.toBilin'_apply' (M : Matrix n n R₁) (v w : n -> R₁) :
    Matrix.toBilin' M v w = v ⬝ᵥ M *ᵥ w := Matrix.toLinearMap₂'_apply' _ _ _

@[simp]
/--
theorem `Matrix.toBilin'_single` / 定理 `Matrix.toBilin'_single`

English:
theorem Matrix.toBilin'_single
  given: (M : Matrix n n R₁) (i j : n)
  proof: by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

@[simp]

中文:
定理 Matrix.toBilin'_single
  条件: (M : Matrix n n R₁) (i j : n)
  证明: by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

@[simp]
-/
theorem Matrix.toBilin'_single (M : Matrix n n R₁) (i j : n) :
    Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrix'_symm` / 定理 `LinearMap.BilinForm.toMatrix'_symm`

English:
theorem LinearMap.BilinForm.toMatrix'_symm
  proof: rfl

@[simp]

中文:
定理 LinearMap.BilinForm.toMatrix'_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.BilinForm.toMatrix'_symm :
    (BilinForm.toMatrix'.symm : Matrix n n R₁ ≃ₗ[R₁] _) = Matrix.toBilin' :=
  rfl

@[simp]
/--
theorem `Matrix.toBilin'_symm` / 定理 `Matrix.toBilin'_symm`

English:
theorem Matrix.toBilin'_symm
  proof: BilinForm.toMatrix'.symm_symm

@[simp]

中文:
定理 Matrix.toBilin'_symm
  证明: BilinForm.toMatrix'.symm_symm

@[simp]
-/
theorem Matrix.toBilin'_symm :
    (Matrix.toBilin'.symm : _ ≃ₗ[R₁] Matrix n n R₁) = BilinForm.toMatrix' :=
  BilinForm.toMatrix'.symm_symm

@[simp]
/--
theorem `Matrix.toBilin'_toMatrix'` / 定理 `Matrix.toBilin'_toMatrix'`

English:
theorem Matrix.toBilin'_toMatrix'
  given: (B : BilinForm R₁ (n -> R₁))
  proof: Matrix.toBilin'.apply_symm_apply B

中文:
定理 Matrix.toBilin'_toMatrix'
  条件: (B : BilinForm R₁ (n -> R₁))
  证明: Matrix.toBilin'.apply_symm_apply B
-/
theorem Matrix.toBilin'_toMatrix' (B : BilinForm R₁ (n -> R₁)) :
    Matrix.toBilin' (BilinForm.toMatrix' B) = B :=
  Matrix.toBilin'.apply_symm_apply B

namespace LinearMap

@[simp]
/--
theorem `BilinForm.toMatrix'_toBilin'` / 定理 `BilinForm.toMatrix'_toBilin'`

English:
theorem BilinForm.toMatrix'_toBilin'
  given: (M : Matrix n n R₁)
  proof: (LinearMap.toMatrix₂' R₁).apply_symm_apply M

@[simp]

中文:
定理 BilinForm.toMatrix'_toBilin'
  条件: (M : Matrix n n R₁)
  证明: (LinearMap.toMatrix₂' R₁).apply_symm_apply M

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, apply_symm_apply
-/
theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₁) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M :=
  (LinearMap.toMatrix₂' R₁).apply_symm_apply M

@[simp]
/--
theorem `BilinForm.toMatrix'_apply` / 定理 `BilinForm.toMatrix'_apply`

English:
theorem BilinForm.toMatrix'_apply
  given: (B : BilinForm R₁ (n -> R₁)) (i j : n)
  proof: LinearMap.toMatrix₂'_apply _ _ _

@[simp]

中文:
定理 BilinForm.toMatrix'_apply
  条件: (B : BilinForm R₁ (n -> R₁)) (i j : n)
  证明: LinearMap.toMatrix₂'_apply _ _ _

@[simp]
-/
theorem BilinForm.toMatrix'_apply (B : BilinForm R₁ (n -> R₁)) (i j : n) :
    BilinForm.toMatrix' B i j = B (Pi.single i 1) (Pi.single j 1) :=
  LinearMap.toMatrix₂'_apply _ _ _

@[simp]
/--
theorem `BilinForm.toMatrix'_comp` / 定理 `BilinForm.toMatrix'_comp`

English:
theorem BilinForm.toMatrix'_comp
  given: (B : BilinForm R₁ (n -> R₁)) (l r : (o -> R₁) ->ₗ[R₁] n -> R₁)
  proof: B.toMatrix₂'_compl₁₂ _ _

中文:
定理 BilinForm.toMatrix'_comp
  条件: (B : BilinForm R₁ (n -> R₁)) (l r : (o -> R₁) ->ₗ[R₁] n -> R₁)
  证明: B.toMatrix₂'_compl₁₂ _ _
-/
theorem BilinForm.toMatrix'_comp (B : BilinForm R₁ (n -> R₁)) (l r : (o -> R₁) ->ₗ[R₁] n -> R₁) :
    (B.comp l r).toMatrix' = l.toMatrix'ᵀ * B.toMatrix' * r.toMatrix' :=
  B.toMatrix₂'_compl₁₂ _ _

/--
theorem `BilinForm.toMatrix'_compLeft` / 定理 `BilinForm.toMatrix'_compLeft`

English:
theorem BilinForm.toMatrix'_compLeft
  given: (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁)
  proof: B.toMatrix₂'_comp _

中文:
定理 BilinForm.toMatrix'_compLeft
  条件: (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁)
  证明: B.toMatrix₂'_comp _
-/
theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁) :
    (B.compLeft f).toMatrix' = f.toMatrix'ᵀ * B.toMatrix' :=
  B.toMatrix₂'_comp _

/--
theorem `BilinForm.toMatrix'_compRight` / 定理 `BilinForm.toMatrix'_compRight`

English:
theorem BilinForm.toMatrix'_compRight
  given: (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁)
  proof: B.toMatrix₂'_compl₂ _

中文:
定理 BilinForm.toMatrix'_compRight
  条件: (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁)
  证明: B.toMatrix₂'_compl₂ _
-/
theorem BilinForm.toMatrix'_compRight (B : BilinForm R₁ (n -> R₁)) (f : (n -> R₁) ->ₗ[R₁] n -> R₁) :
    (B.compRight f).toMatrix' = B.toMatrix' * f.toMatrix' :=
  B.toMatrix₂'_compl₂ _

/--
theorem `BilinForm.mul_toMatrix'_mul` / 定理 `BilinForm.mul_toMatrix'_mul`

English:
theorem BilinForm.mul_toMatrix'_mul
  statement: (B : BilinForm R₁ (n -> R₁)) (M : Matrix o n R₁)
  proof: B.mul_toMatrix₂'_mul _ _

中文:
定理 BilinForm.mul_toMatrix'_mul
  结论: (B : BilinForm R₁ (n -> R₁)) (M : Matrix o n R₁)
  证明: B.mul_toMatrix₂'_mul _ _

Depends on / 依赖: B.mul_toMatrix, _mul
-/
theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₁ (n -> R₁)) (M : Matrix o n R₁)
    (N : Matrix n o R₁) : M * B.toMatrix' * N = (B.comp (Mᵀ).toLin' N.toLin').toMatrix' :=
  B.mul_toMatrix₂'_mul _ _

/--
theorem `BilinForm.mul_toMatrix'` / 定理 `BilinForm.mul_toMatrix'`

English:
theorem BilinForm.mul_toMatrix'
  given: (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁)
  proof: LinearMap.mul_toMatrix' B _

中文:
定理 BilinForm.mul_toMatrix'
  条件: (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁)
  证明: LinearMap.mul_toMatrix' B _
-/
theorem BilinForm.mul_toMatrix' (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁) :
    M * B.toMatrix' = (B.compLeft (Mᵀ).toLin').toMatrix' :=
  LinearMap.mul_toMatrix' B _

/--
theorem `BilinForm.toMatrix'_mul` / 定理 `BilinForm.toMatrix'_mul`

English:
theorem BilinForm.toMatrix'_mul
  given: (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁)
  proof: B.toMatrix₂'_mul _

中文:
定理 BilinForm.toMatrix'_mul
  条件: (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁)
  证明: B.toMatrix₂'_mul _
-/
theorem BilinForm.toMatrix'_mul (B : BilinForm R₁ (n -> R₁)) (M : Matrix n n R₁) :
    BilinForm.toMatrix' B * M = BilinForm.toMatrix' (B.compRight (Matrix.toLin' M)) :=
  B.toMatrix₂'_mul _

end LinearMap

/--
theorem `Matrix.toBilin'_comp` / 定理 `Matrix.toBilin'_comp`

English:
theorem Matrix.toBilin'_comp
  given: (M : Matrix n n R₁) (P Q : Matrix n o R₁)
  proof: BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])

中文:
定理 Matrix.toBilin'_comp
  条件: (M : Matrix n n R₁) (P Q : Matrix n o R₁)
  证明: BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])
-/
theorem Matrix.toBilin'_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    M.toBilin'.comp P.toLin' Q.toLin' = (Pᵀ * M * Q).toBilin' :=
  BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])

end ToMatrix'

section ToMatrix

/-! ### `ToMatrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [DecidableEq n] (b : Basis n R₁ M₁)

/--
Definition of `LinearMap.BilinForm.toMatrix` / `LinearMap.BilinForm.toMatrix` 的定义

English:
definition LinearMap.BilinForm.toMatrix
  signature: : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁
  body: LinearMap.toMatrix₂ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrix := LinearMap.BilinForm.toMatrix

中文:
定义 LinearMap.BilinForm.toMatrix
  签名: : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁
  定义体: LinearMap.toMatrix₂ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrix := LinearMap.BilinForm.toMatrix

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
noncomputable def LinearMap.BilinForm.toMatrix : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂ b b

@[deprecated (since := "2026-01-16")] alias BilinForm.toMatrix := LinearMap.BilinForm.toMatrix

/--
Definition of `Matrix.toBilin` / `Matrix.toBilin` 的定义

English:
definition Matrix.toBilin
  signature: : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁
  body: (LinearMap.BilinForm.toMatrix b).symm

@[simp]

中文:
定义 Matrix.toBilin
  签名: : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁
  定义体: (LinearMap.BilinForm.toMatrix b).symm

@[simp]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.toMatrix, toMatrix
-/
noncomputable def Matrix.toBilin : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁ :=
  (LinearMap.BilinForm.toMatrix b).symm

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrix_apply` / 定理 `LinearMap.BilinForm.toMatrix_apply`

English:
theorem LinearMap.BilinForm.toMatrix_apply
  given: (B : BilinForm R₁ M₁) (i j : n)
  proof: LinearMap.toMatrix₂_apply _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_apply := LinearMap.BilinForm.toMatrix_apply

中文:
定理 LinearMap.BilinForm.toMatrix_apply
  条件: (B : BilinForm R₁ M₁) (i j : n)
  证明: LinearMap.toMatrix₂_apply _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_apply := LinearMap.BilinForm.toMatrix_apply

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_apply (B : BilinForm R₁ M₁) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂_apply _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_apply := LinearMap.BilinForm.toMatrix_apply

/--
theorem `LinearMap.BilinForm.dotProduct_toMatrix_mulVec` / 定理 `LinearMap.BilinForm.dotProduct_toMatrix_mulVec`

English:
theorem LinearMap.BilinForm.dotProduct_toMatrix_mulVec
  given: (B : BilinForm R₁ M₁) (x y : n -> R₁)
  proof: dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.dotProduct_toMatrix_mulVec := LinearMap.BilinForm.dotProduct_toMatrix_mulVec

中文:
定理 LinearMap.BilinForm.dotProduct_toMatrix_mulVec
  条件: (B : BilinForm R₁ M₁) (x y : n -> R₁)
  证明: dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.dotProduct_toMatrix_mulVec := LinearMap.BilinForm.dotProduct_toMatrix_mulVec
-/
theorem LinearMap.BilinForm.dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : n -> R₁) :
    x ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ y = B (b.equivFun.symm x) (b.equivFun.symm y) :=
  dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.dotProduct_toMatrix_mulVec := LinearMap.BilinForm.dotProduct_toMatrix_mulVec

/--
lemma `LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec` / 引理 `LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec`

English:
lemma LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
  given: (B : BilinForm R₁ M₁) (x y : M₁)
  proof: apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.apply_eq_dotProduct_toMatrix_mulVec :=
  LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec

@[simp]

中文:
引理 LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
  条件: (B : BilinForm R₁ M₁) (x y : M₁)
  证明: apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.apply_eq_dotProduct_toMatrix_mulVec :=
  LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec

@[simp]
-/
lemma LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : M₁) :
    B x y = (b.repr x) ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ (b.repr y) :=
  apply_eq_dotProduct_toMatrix₂_mulVec b b B x y

@[deprecated (since := "2026-01-16")]
alias BilinForm.apply_eq_dotProduct_toMatrix_mulVec :=
  LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec

@[simp]
/--
theorem `Matrix.toBilin_apply` / 定理 `Matrix.toBilin_apply`

English:
theorem Matrix.toBilin_apply
  given: (M : Matrix n n R₁) (x y : M₁)
  proof: (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

中文:
定理 Matrix.toBilin_apply
  条件: (M : Matrix n n R₁) (x y : M₁)
  证明: (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

Depends on / 依赖: Matrix, Matrix.toLinearMap, mul_comm, mul_left_comm, smul_eq_mul
-/
theorem Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁) :
    Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j :=
  (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

-- Not a `simp` lemma since `BilinForm.toMatrix` needs an extra argument
/--
theorem `LinearMap.BilinForm.toMatrixAux_eq` / 定理 `LinearMap.BilinForm.toMatrixAux_eq`

English:
theorem LinearMap.BilinForm.toMatrixAux_eq
  given: (B : BilinForm R₁ M₁)
  proof: LinearMap.toMatrix₂Aux_eq _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinearForm.toMatrixAux_eq := LinearMap.BilinForm.toMatrixAux_eq

@[simp]

中文:
定理 LinearMap.BilinForm.toMatrixAux_eq
  条件: (B : BilinForm R₁ M₁)
  证明: LinearMap.toMatrix₂Aux_eq _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinearForm.toMatrixAux_eq := LinearMap.BilinForm.toMatrixAux_eq

@[simp]

Depends on / 依赖: BilinForm, BilinForm.toMatrix, toMatrix
-/
theorem LinearMap.BilinForm.toMatrixAux_eq (B : BilinForm R₁ M₁) :
    BilinForm.toMatrixAux (R₁ := R₁) b B = BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂Aux_eq _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinearForm.toMatrixAux_eq := LinearMap.BilinForm.toMatrixAux_eq

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrix_symm` / 定理 `LinearMap.BilinForm.toMatrix_symm`

English:
theorem LinearMap.BilinForm.toMatrix_symm
  statement: (BilinForm.toMatrix b).symm = Matrix.toBilin b
  proof: rfl

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_symm := LinearMap.BilinForm.toMatrix_symm

@[simp]

中文:
定理 LinearMap.BilinForm.toMatrix_symm
  结论: (BilinForm.toMatrix b).symm = Matrix.toBilin b
  证明: rfl

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_symm := LinearMap.BilinForm.toMatrix_symm

@[simp]
-/
theorem LinearMap.BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.toBilin b :=
  rfl

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_symm := LinearMap.BilinForm.toMatrix_symm

@[simp]
/--
theorem `Matrix.toBilin_symm` / 定理 `Matrix.toBilin_symm`

English:
theorem Matrix.toBilin_symm
  statement: (Matrix.toBilin b).symm = LinearMap.BilinForm.toMatrix b
  proof: (LinearMap.BilinForm.toMatrix b).symm_symm

中文:
定理 Matrix.toBilin_symm
  结论: (Matrix.toBilin b).symm = LinearMap.BilinForm.toMatrix b
  证明: (LinearMap.BilinForm.toMatrix b).symm_symm

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.toMatrix, symm_symm, toMatrix
-/
theorem Matrix.toBilin_symm : (Matrix.toBilin b).symm = LinearMap.BilinForm.toMatrix b :=
  (LinearMap.BilinForm.toMatrix b).symm_symm

/--
theorem `Matrix.toBilin_basisFun` / 定理 `Matrix.toBilin_basisFun`

English:
theorem Matrix.toBilin_basisFun
  statement: Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin'
  proof: by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]

中文:
定理 Matrix.toBilin_basisFun
  结论: Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin'
  证明: by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]

Depends on / 依赖: Function, Function.comp_apply, Pi.basisFun_repr, _apply, basisFun_repr, coe_comp, coe_single, comp_apply, toBilin, toBilin_apply
-/
theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin' := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]

/--
theorem `LinearMap.BilinForm.toMatrix_basisFun` / 定理 `LinearMap.BilinForm.toMatrix_basisFun`

English:
theorem LinearMap.BilinForm.toMatrix_basisFun
  proof: by
  rw [BilinForm.toMatrix]; rw [BilinForm.toMatrix']; rw [LinearMap.toMatrix₂_basisFun]

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_basisFun := LinearMap.BilinForm.toMatrix_basisFun

@[simp]

中文:
定理 LinearMap.BilinForm.toMatrix_basisFun
  证明: by
  rw [BilinForm.toMatrix]; rw [BilinForm.toMatrix']; rw [LinearMap.toMatrix₂_basisFun]

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_basisFun := LinearMap.BilinForm.toMatrix_basisFun

@[simp]

Depends on / 依赖: BilinForm, BilinForm.toMatrix, LinearMap, LinearMap.toMatrix, toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_basisFun :
    BilinForm.toMatrix (Pi.basisFun R₁ n) = BilinForm.toMatrix' := by
  rw [BilinForm.toMatrix]; rw [BilinForm.toMatrix']; rw [LinearMap.toMatrix₂_basisFun]

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_basisFun := LinearMap.BilinForm.toMatrix_basisFun

@[simp]
/--
theorem `Matrix.toBilin_toMatrix` / 定理 `Matrix.toBilin_toMatrix`

English:
theorem Matrix.toBilin_toMatrix
  given: (B : BilinForm R₁ M₁)
  proof: (Matrix.toBilin b).apply_symm_apply B

@[simp]

中文:
定理 Matrix.toBilin_toMatrix
  条件: (B : BilinForm R₁ M₁)
  证明: (Matrix.toBilin b).apply_symm_apply B

@[simp]

Depends on / 依赖: Matrix, Matrix.toBilin, apply_symm_apply, toBilin
-/
theorem Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
    Matrix.toBilin b (B.toMatrix b) = B :=
  (Matrix.toBilin b).apply_symm_apply B

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrix_toBilin` / 定理 `LinearMap.BilinForm.toMatrix_toBilin`

English:
theorem LinearMap.BilinForm.toMatrix_toBilin
  given: (M : Matrix n n R₁)
  proof: (BilinForm.toMatrix b).apply_symm_apply M

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_toBilin := LinearMap.BilinForm.toMatrix_toBilin

中文:
定理 LinearMap.BilinForm.toMatrix_toBilin
  条件: (M : Matrix n n R₁)
  证明: (BilinForm.toMatrix b).apply_symm_apply M

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_toBilin := LinearMap.BilinForm.toMatrix_toBilin

Depends on / 依赖: BilinForm, BilinForm.toMatrix, apply_symm_apply, toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_toBilin (M : Matrix n n R₁) :
    BilinForm.toMatrix b (Matrix.toBilin b M) = M :=
  (BilinForm.toMatrix b).apply_symm_apply M

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_toBilin := LinearMap.BilinForm.toMatrix_toBilin

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']
variable (c : Basis o R₁ M₂')
variable [DecidableEq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
/--
theorem `LinearMap.BilinForm.toMatrix_comp` / 定理 `LinearMap.BilinForm.toMatrix_comp`

English:
theorem LinearMap.BilinForm.toMatrix_comp
  given: (B : BilinForm R₁ M₁) (l r : M₂' ->ₗ[R₁] M₁)
  proof: LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_comp := LinearMap.BilinForm.toMatrix_comp

中文:
定理 LinearMap.BilinForm.toMatrix_comp
  条件: (B : BilinForm R₁ M₁) (l r : M₂' ->ₗ[R₁] M₁)
  证明: LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_comp := LinearMap.BilinForm.toMatrix_comp

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_comp (B : BilinForm R₁ M₁) (l r : M₂' ->ₗ[R₁] M₁) :
    BilinForm.toMatrix c (B.comp l r) =
      (LinearMap.toMatrix c b l)ᵀ * BilinForm.toMatrix b B * LinearMap.toMatrix c b r :=
  LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_comp := LinearMap.BilinForm.toMatrix_comp

/--
theorem `LinearMap.BilinForm.toMatrix_compLeft` / 定理 `LinearMap.BilinForm.toMatrix_compLeft`

English:
theorem LinearMap.BilinForm.toMatrix_compLeft
  given: (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁)
  proof: LinearMap.toMatrix₂_comp _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compLeft := LinearMap.BilinForm.toMatrix_compLeft

中文:
定理 LinearMap.BilinForm.toMatrix_compLeft
  条件: (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁)
  证明: LinearMap.toMatrix₂_comp _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compLeft := LinearMap.BilinForm.toMatrix_compLeft

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_compLeft (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂_comp _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compLeft := LinearMap.BilinForm.toMatrix_compLeft

/--
theorem `LinearMap.BilinForm.toMatrix_compRight` / 定理 `LinearMap.BilinForm.toMatrix_compRight`

English:
theorem LinearMap.BilinForm.toMatrix_compRight
  given: (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁)
  proof: LinearMap.toMatrix₂_compl₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compRight := LinearMap.BilinForm.toMatrix_compRight

@[simp]

中文:
定理 LinearMap.BilinForm.toMatrix_compRight
  条件: (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁)
  证明: LinearMap.toMatrix₂_compl₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compRight := LinearMap.BilinForm.toMatrix_compRight

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_compRight (B : BilinForm R₁ M₁) (f : M₁ ->ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B * LinearMap.toMatrix b b f :=
  LinearMap.toMatrix₂_compl₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_compRight := LinearMap.BilinForm.toMatrix_compRight

@[simp]
/--
theorem `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix` / 定理 `LinearMap.BilinForm.toMatrix_mul_basis_toMatrix`

English:
theorem LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
  given: (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁)
  proof: LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul_basis_toMatrix := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix

中文:
定理 LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
  条件: (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁)
  证明: LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul_basis_toMatrix := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁) :
    (b.toMatrix c)ᵀ * BilinForm.toMatrix b B * b.toMatrix c = BilinForm.toMatrix c B :=
  LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _ _ B

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul_basis_toMatrix := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix

/--
theorem `LinearMap.BilinForm.mul_toMatrix_mul` / 定理 `LinearMap.BilinForm.mul_toMatrix_mul`

English:
theorem LinearMap.BilinForm.mul_toMatrix_mul
  statement: (B : BilinForm R₁ M₁) (M : Matrix o n R₁)
  proof: LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix_mul := LinearMap.BilinForm.mul_toMatrix_mul

中文:
定理 LinearMap.BilinForm.mul_toMatrix_mul
  结论: (B : BilinForm R₁ M₁) (M : Matrix o n R₁)
  证明: LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix_mul := LinearMap.BilinForm.mul_toMatrix_mul

Depends on / 依赖: LinearMap, LinearMap.mul_toMatrix
-/
theorem LinearMap.BilinForm.mul_toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix o n R₁)
    (N : Matrix n o R₁) :
    M * BilinForm.toMatrix b B * N =
      BilinForm.toMatrix c (B.comp (Matrix.toLin c b Mᵀ) (Matrix.toLin c b N)) :=
  LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix_mul := LinearMap.BilinForm.mul_toMatrix_mul

/--
theorem `LinearMap.BilinForm.mul_toMatrix` / 定理 `LinearMap.BilinForm.mul_toMatrix`

English:
theorem LinearMap.BilinForm.mul_toMatrix
  given: (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
  proof: LinearMap.mul_toMatrix₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix := LinearMap.BilinForm.mul_toMatrix

中文:
定理 LinearMap.BilinForm.mul_toMatrix
  条件: (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
  证明: LinearMap.mul_toMatrix₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix := LinearMap.BilinForm.mul_toMatrix

Depends on / 依赖: LinearMap, LinearMap.mul_toMatrix
-/
theorem LinearMap.BilinForm.mul_toMatrix (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b b Mᵀ)) :=
  LinearMap.mul_toMatrix₂ _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.mul_toMatrix := LinearMap.BilinForm.mul_toMatrix

/--
theorem `LinearMap.BilinForm.toMatrix_mul` / 定理 `LinearMap.BilinForm.toMatrix_mul`

English:
theorem LinearMap.BilinForm.toMatrix_mul
  given: (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
  proof: LinearMap.toMatrix₂_mul _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul := LinearMap.BilinForm.toMatrix_mul

中文:
定理 LinearMap.BilinForm.toMatrix_mul
  条件: (B : BilinForm R₁ M₁) (M : Matrix n n R₁)
  证明: LinearMap.toMatrix₂_mul _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul := LinearMap.BilinForm.toMatrix_mul

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem LinearMap.BilinForm.toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    BilinForm.toMatrix b B * M = BilinForm.toMatrix b (B.compRight (Matrix.toLin b b M)) :=
  LinearMap.toMatrix₂_mul _ _ _ B _

@[deprecated (since := "2026-01-16")]
alias BilinForm.toMatrix_mul := LinearMap.BilinForm.toMatrix_mul

/--
theorem `Matrix.toBilin_comp` / 定理 `Matrix.toBilin_comp`

English:
theorem Matrix.toBilin_comp
  given: (M : Matrix n n R₁) (P Q : Matrix n o R₁)
  proof: by
  ext x y
  rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [toMatrix₂_symm]; rw [toMatrix₂_symm]; rw [← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp

@[simp]

中文:
定理 Matrix.toBilin_comp
  条件: (M : Matrix n n R₁) (P Q : Matrix n o R₁)
  证明: by
  ext x y
  rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [toMatrix₂_symm]; rw [toMatrix₂_symm]; rw [← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp

@[simp]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.toMatrix, Matrix, Matrix.toBilin, Matrix.toLinearMap, toBilin, toMatrix
-/
theorem Matrix.toBilin_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    (Matrix.toBilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ * M * Q) := by
  ext x y
  rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [Matrix.toBilin]; rw [LinearMap.BilinForm.toMatrix]; rw [toMatrix₂_symm]; rw [toMatrix₂_symm]; rw [← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp

@[simp]
/--
lemma `LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm` / 引理 `LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm`

English:
lemma LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm
  given: {B : BilinForm R₁ M₁}
  proof: by
  simp [isSymm_iff, IsSymm.ext_iff, isSymm_iff_eq_flip, ext_iff_basis b, eq_comm]

@[simp]

中文:
引理 LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm
  条件: {B : BilinForm R₁ M₁}
  证明: by
  simp [isSymm_iff, IsSymm.ext_iff, isSymm_iff_eq_flip, ext_iff_basis b, eq_comm]

@[simp]

Depends on / 依赖: IsSymm, IsSymm.ext_iff, eq_comm, ext_iff, ext_iff_basis, isSymm_iff, isSymm_iff_eq_flip
-/
lemma LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm {B : BilinForm R₁ M₁} :
    (B.toMatrix b).IsSymm ↔ B.IsSymm := by
  simp [isSymm_iff, IsSymm.ext_iff, isSymm_iff_eq_flip, ext_iff_basis b, eq_comm]

@[simp]
/--
lemma `Matrix.isSymm_toBilin_iff_isSymm` / 引理 `Matrix.isSymm_toBilin_iff_isSymm`

English:
lemma Matrix.isSymm_toBilin_iff_isSymm
  given: {M : Matrix n n R₁}
  statement: (M.toBilin b).IsSymm ↔ M.IsSymm
  proof: by
  simp [← (M.toBilin b).isSymm_toMatrix_iff_isSymm b]

@[simp]

中文:
引理 Matrix.isSymm_toBilin_iff_isSymm
  条件: {M : Matrix n n R₁}
  结论: (M.toBilin b).IsSymm ↔ M.IsSymm
  证明: by
  simp [← (M.toBilin b).isSymm_toMatrix_iff_isSymm b]

@[simp]

Depends on / 依赖: M.toBilin, isSymm_toMatrix_iff_isSymm, toBilin
-/
lemma Matrix.isSymm_toBilin_iff_isSymm {M : Matrix n n R₁} : (M.toBilin b).IsSymm ↔ M.IsSymm := by
  simp [← (M.toBilin b).isSymm_toMatrix_iff_isSymm b]

@[simp]
/--
lemma `LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm` / 引理 `LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm`

English:
lemma LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm
  given: {B : BilinForm R₁ (n -> R₁)}
  proof: B.isSymm_toMatrix_iff_isSymm (Pi.basisFun R₁ n)

@[simp]

中文:
引理 LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm
  条件: {B : BilinForm R₁ (n -> R₁)}
  证明: B.isSymm_toMatrix_iff_isSymm (Pi.basisFun R₁ n)

@[simp]

Depends on / 依赖: B.isSymm_toMatrix_iff_isSymm, Pi.basisFun, basisFun, isSymm_toMatrix_iff_isSymm
-/
lemma LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm {B : BilinForm R₁ (n -> R₁)} :
    B.toMatrix'.IsSymm ↔ B.IsSymm :=
  B.isSymm_toMatrix_iff_isSymm (Pi.basisFun R₁ n)

@[simp]
/--
lemma `Matrix.isSymm_toBilin'_iff_isSymm` / 引理 `Matrix.isSymm_toBilin'_iff_isSymm`

English:
lemma Matrix.isSymm_toBilin'_iff_isSymm
  given: {M : Matrix n n R₁}
  statement: M.toBilin'.IsSymm ↔ M.IsSymm
  proof: by
  simp [← M.toBilin'.isSymm_toMatrix'_iff_isSymm]

中文:
引理 Matrix.isSymm_toBilin'_iff_isSymm
  条件: {M : Matrix n n R₁}
  结论: M.toBilin'.IsSymm ↔ M.IsSymm
  证明: by
  simp [← M.toBilin'.isSymm_toMatrix'_iff_isSymm]

Depends on / 依赖: M.toBilin, _iff_isSymm, isSymm_toMatrix, toBilin
-/
lemma Matrix.isSymm_toBilin'_iff_isSymm {M : Matrix n n R₁} : M.toBilin'.IsSymm ↔ M.IsSymm := by
  simp [← M.toBilin'.isSymm_toMatrix'_iff_isSymm]

end ToMatrix

end Matrix

section MatrixAdjoints

open Matrix

variable {n : Type*} [Fintype n]
variable (b : Basis n R₂ M₂)
variable (J J₃ A A' : Matrix n n R₂)

/--
theorem `Matrix.isAdjointPair_equiv'` / 定理 `Matrix.isAdjointPair_equiv'`

English:
theorem Matrix.isAdjointPair_equiv'
  given: [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P)
  proof: Matrix.isAdjointPair_equiv _ _ _ _ h

中文:
定理 Matrix.isAdjointPair_equiv'
  条件: [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P)
  证明: Matrix.isAdjointPair_equiv _ _ _ _ h

Depends on / 依赖: Matrix, Matrix.isAdjointPair_equiv, isAdjointPair_equiv
-/
theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔
      J.IsAdjointPair J (P * A * P⁻¹) (P * A' * P⁻¹) :=
  Matrix.isAdjointPair_equiv _ _ _ _ h

variable [DecidableEq n]

/--
theorem `mem_pairSelfAdjointMatricesSubmodule'` / 定理 `mem_pairSelfAdjointMatricesSubmodule'`

English:
theorem mem_pairSelfAdjointMatricesSubmodule'
  proof: by
  simp only [mem_pairSelfAdjointMatricesSubmodule]

中文:
定理 mem_pairSelfAdjointMatricesSubmodule'
  证明: by
  simp only [mem_pairSelfAdjointMatricesSubmodule]

Depends on / 依赖: mem_pairSelfAdjointMatricesSubmodule
-/
theorem mem_pairSelfAdjointMatricesSubmodule' :
    A in pairSelfAdjointMatricesSubmodule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A := by
  simp only [mem_pairSelfAdjointMatricesSubmodule]

/--
Definition of `selfAdjointMatricesSubmodule'` / `selfAdjointMatricesSubmodule'` 的定义

English:
definition selfAdjointMatricesSubmodule'
  signature: : Submodule R₂ (Matrix n n R₂)
  body: pairSelfAdjointMatricesSubmodule J J

中文:
定义 selfAdjointMatricesSubmodule'
  签名: : Submodule R₂ (Matrix n n R₂)
  定义体: pairSelfAdjointMatricesSubmodule J J

Depends on / 依赖: pairSelfAdjointMatricesSubmodule
-/
def selfAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule J J

/--
theorem `mem_selfAdjointMatricesSubmodule'` / 定理 `mem_selfAdjointMatricesSubmodule'`

English:
theorem mem_selfAdjointMatricesSubmodule'
  proof: by
  simp only [mem_selfAdjointMatricesSubmodule]

中文:
定理 mem_selfAdjointMatricesSubmodule'
  证明: by
  simp only [mem_selfAdjointMatricesSubmodule]

Depends on / 依赖: mem_selfAdjointMatricesSubmodule
-/
theorem mem_selfAdjointMatricesSubmodule' :
    A in selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A := by
  simp only [mem_selfAdjointMatricesSubmodule]

/--
Definition of `skewAdjointMatricesSubmodule'` / `skewAdjointMatricesSubmodule'` 的定义

English:
definition skewAdjointMatricesSubmodule'
  signature: : Submodule R₂ (Matrix n n R₂)
  body: pairSelfAdjointMatricesSubmodule (-J) J

中文:
定义 skewAdjointMatricesSubmodule'
  签名: : Submodule R₂ (Matrix n n R₂)
  定义体: pairSelfAdjointMatricesSubmodule (-J) J

Depends on / 依赖: pairSelfAdjointMatricesSubmodule
-/
def skewAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule (-J) J

/--
theorem `mem_skewAdjointMatricesSubmodule'` / 定理 `mem_skewAdjointMatricesSubmodule'`

English:
theorem mem_skewAdjointMatricesSubmodule'
  proof: by
  simp only [mem_skewAdjointMatricesSubmodule]

中文:
定理 mem_skewAdjointMatricesSubmodule'
  证明: by
  simp only [mem_skewAdjointMatricesSubmodule]

Depends on / 依赖: mem_skewAdjointMatricesSubmodule
-/
theorem mem_skewAdjointMatricesSubmodule' :
    A in skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A := by
  simp only [mem_skewAdjointMatricesSubmodule]

end MatrixAdjoints

namespace LinearMap

namespace BilinForm

section Det

open Matrix

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/--
theorem `_root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin` / 定理 `_root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin`

English:
theorem _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin
  statement: {M : Matrix ι ι R₁}
  proof: (nondegenerate_congr_iff b.equivFun.symm).symm

中文:
定理 _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin
  结论: {M : Matrix ι ι R₁}
  证明: (nondegenerate_congr_iff b.equivFun.symm).symm

Depends on / 依赖: b.equivFun.symm, equivFun, nondegenerate_congr_iff
-/
theorem _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin {M : Matrix ι ι R₁}
    (b : Basis ι R₁ M₁) : M.toBilin'.Nondegenerate ↔ (Matrix.toBilin b M).Nondegenerate :=
  (nondegenerate_congr_iff b.equivFun.symm).symm


/--
theorem `_root_.Matrix.Nondegenerate.toBilin'` / 定理 `_root_.Matrix.Nondegenerate.toBilin'`

English:
theorem _root_.Matrix.Nondegenerate.toBilin'
  given: {M : Matrix ι ι R₂} (h : M.Nondegenerate)
  proof: h.toLinearMap₂'

@[simp]

中文:
定理 _root_.Matrix.Nondegenerate.toBilin'
  条件: {M : Matrix ι ι R₂} (h : M.Nondegenerate)
  证明: h.toLinearMap₂'

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.Nondegenerate.toBilin' {M : Matrix ι ι R₂} (h : M.Nondegenerate) :
    M.toBilin'.Nondegenerate :=
  h.toLinearMap₂'

@[simp]
/--
theorem `_root_.Matrix.nondegenerate_toBilin'_iff` / 定理 `_root_.Matrix.nondegenerate_toBilin'_iff`

English:
theorem _root_.Matrix.nondegenerate_toBilin'_iff
  given: {M : Matrix ι ι R₂}
  proof: Matrix.nondegenerate_toLinearMap₂'_iff

中文:
定理 _root_.Matrix.nondegenerate_toBilin'_iff
  条件: {M : Matrix ι ι R₂}
  证明: Matrix.nondegenerate_toLinearMap₂'_iff
-/
theorem _root_.Matrix.nondegenerate_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.Nondegenerate ↔ M.Nondegenerate :=
  Matrix.nondegenerate_toLinearMap₂'_iff

/--
theorem `_root_.Matrix.Nondegenerate.toBilin` / 定理 `_root_.Matrix.Nondegenerate.toBilin`

English:
theorem _root_.Matrix.Nondegenerate.toBilin
  statement: {M : Matrix ι ι R₂} (h : M.Nondegenerate)
  proof: h.toLinearMap₂ b b

@[simp]

中文:
定理 _root_.Matrix.Nondegenerate.toBilin
  结论: {M : Matrix ι ι R₂} (h : M.Nondegenerate)
  证明: h.toLinearMap₂ b b

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.Nondegenerate.toBilin {M : Matrix ι ι R₂} (h : M.Nondegenerate)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).Nondegenerate :=
  h.toLinearMap₂ b b

@[simp]
/--
theorem `_root_.Matrix.nondegenerate_toBilin_iff` / 定理 `_root_.Matrix.nondegenerate_toBilin_iff`

English:
theorem _root_.Matrix.nondegenerate_toBilin_iff
  given: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  proof: Matrix.nondegenerate_toLinearMap₂_iff b b

中文:
定理 _root_.Matrix.nondegenerate_toBilin_iff
  条件: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  证明: Matrix.nondegenerate_toLinearMap₂_iff b b

Depends on / 依赖: Matrix, Matrix.nondegenerate_toLinearMap
-/
theorem _root_.Matrix.nondegenerate_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).Nondegenerate ↔ M.Nondegenerate :=
  Matrix.nondegenerate_toLinearMap₂_iff b b


/--
theorem `_root_.Matrix.SeparatingLeft.toBilin'` / 定理 `_root_.Matrix.SeparatingLeft.toBilin'`

English:
theorem _root_.Matrix.SeparatingLeft.toBilin'
  given: {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
  proof: h.toLinearMap₂'

@[simp]

中文:
定理 _root_.Matrix.SeparatingLeft.toBilin'
  条件: {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
  证明: h.toLinearMap₂'

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.SeparatingLeft.toBilin' {M : Matrix ι ι R₂} (h : M.SeparatingLeft) :
    M.toBilin'.SeparatingLeft :=
  h.toLinearMap₂'

@[simp]
/--
theorem `_root_.Matrix.separatingLeft_toBilin'_iff` / 定理 `_root_.Matrix.separatingLeft_toBilin'_iff`

English:
theorem _root_.Matrix.separatingLeft_toBilin'_iff
  given: {M : Matrix ι ι R₂}
  proof: Matrix.separatingLeft_toLinearMap₂'_iff

中文:
定理 _root_.Matrix.separatingLeft_toBilin'_iff
  条件: {M : Matrix ι ι R₂}
  证明: Matrix.separatingLeft_toLinearMap₂'_iff

Depends on / 依赖: Matrix, Matrix.separatingLeft_toLinearMap, _iff
-/
theorem _root_.Matrix.separatingLeft_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.SeparatingLeft ↔ M.SeparatingLeft :=
  Matrix.separatingLeft_toLinearMap₂'_iff

/--
theorem `_root_.Matrix.SeparatingLeft.toBilin` / 定理 `_root_.Matrix.SeparatingLeft.toBilin`

English:
theorem _root_.Matrix.SeparatingLeft.toBilin
  statement: {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
  proof: h.toLinearMap₂ b b

@[simp]

中文:
定理 _root_.Matrix.SeparatingLeft.toBilin
  结论: {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
  证明: h.toLinearMap₂ b b

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.SeparatingLeft.toBilin {M : Matrix ι ι R₂} (h : M.SeparatingLeft)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).SeparatingLeft :=
  h.toLinearMap₂ b b

@[simp]
/--
theorem `_root_.Matrix.separatingLeft_toBilin_iff` / 定理 `_root_.Matrix.separatingLeft_toBilin_iff`

English:
theorem _root_.Matrix.separatingLeft_toBilin_iff
  given: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  proof: Matrix.separatingLeft_toLinearMap₂_iff b b

中文:
定理 _root_.Matrix.separatingLeft_toBilin_iff
  条件: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  证明: Matrix.separatingLeft_toLinearMap₂_iff b b

Depends on / 依赖: Matrix, Matrix.separatingLeft_toLinearMap
-/
theorem _root_.Matrix.separatingLeft_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).SeparatingLeft ↔ M.SeparatingLeft :=
  Matrix.separatingLeft_toLinearMap₂_iff b b


/--
theorem `_root_.Matrix.SeparatingRight.toBilin'` / 定理 `_root_.Matrix.SeparatingRight.toBilin'`

English:
theorem _root_.Matrix.SeparatingRight.toBilin'
  given: {M : Matrix ι ι R₂} (h : M.SeparatingRight)
  proof: h.toLinearMap₂'

@[simp]

中文:
定理 _root_.Matrix.SeparatingRight.toBilin'
  条件: {M : Matrix ι ι R₂} (h : M.SeparatingRight)
  证明: h.toLinearMap₂'

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.SeparatingRight.toBilin' {M : Matrix ι ι R₂} (h : M.SeparatingRight) :
    M.toBilin'.SeparatingRight :=
  h.toLinearMap₂'

@[simp]
/--
theorem `_root_.Matrix.separatingRight_toBilin'_iff` / 定理 `_root_.Matrix.separatingRight_toBilin'_iff`

English:
theorem _root_.Matrix.separatingRight_toBilin'_iff
  given: {M : Matrix ι ι R₂}
  proof: Matrix.separatingRight_toLinearMap₂'_iff

中文:
定理 _root_.Matrix.separatingRight_toBilin'_iff
  条件: {M : Matrix ι ι R₂}
  证明: Matrix.separatingRight_toLinearMap₂'_iff

Depends on / 依赖: Matrix, Matrix.separatingRight_toLinearMap, _iff
-/
theorem _root_.Matrix.separatingRight_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.SeparatingRight ↔ M.SeparatingRight :=
  Matrix.separatingRight_toLinearMap₂'_iff

/--
theorem `_root_.Matrix.SeparatingRight.toBilin` / 定理 `_root_.Matrix.SeparatingRight.toBilin`

English:
theorem _root_.Matrix.SeparatingRight.toBilin
  statement: {M : Matrix ι ι R₂} (h : M.SeparatingRight)
  proof: h.toLinearMap₂ b b

@[simp]

中文:
定理 _root_.Matrix.SeparatingRight.toBilin
  结论: {M : Matrix ι ι R₂} (h : M.SeparatingRight)
  证明: h.toLinearMap₂ b b

@[simp]

Depends on / 依赖: h.toLinearMap
-/
theorem _root_.Matrix.SeparatingRight.toBilin {M : Matrix ι ι R₂} (h : M.SeparatingRight)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).SeparatingRight :=
  h.toLinearMap₂ b b

@[simp]
/--
theorem `_root_.Matrix.separatingRight_toBilin_iff` / 定理 `_root_.Matrix.separatingRight_toBilin_iff`

English:
theorem _root_.Matrix.separatingRight_toBilin_iff
  given: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  proof: Matrix.separatingRight_toLinearMap₂_iff b b

中文:
定理 _root_.Matrix.separatingRight_toBilin_iff
  条件: {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂)
  证明: Matrix.separatingRight_toLinearMap₂_iff b b

Depends on / 依赖: Matrix, Matrix.separatingRight_toLinearMap
-/
theorem _root_.Matrix.separatingRight_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).SeparatingRight ↔ M.SeparatingRight :=
  Matrix.separatingRight_toLinearMap₂_iff b b

/-! Lemmas transferring nondegeneracy between a bilinear form and its associated matrix

These are just aliases of lemmas about `LinearMap.toMatrix₂` specialized to the cases where the
left and right spaces are the same.
-/

@[simp]
/--
theorem `nondegenerate_toMatrix'_iff` / 定理 `nondegenerate_toMatrix'_iff`

English:
theorem nondegenerate_toMatrix'_iff
  given: {B : BilinForm R₂ (ι -> R₂)}
  proof: LinearMap.nondegenerate_toMatrix₂'_iff

中文:
定理 nondegenerate_toMatrix'_iff
  条件: {B : BilinForm R₂ (ι -> R₂)}
  证明: LinearMap.nondegenerate_toMatrix₂'_iff

Depends on / 依赖: B.Nondegenerate, Nondegenerate
-/
theorem nondegenerate_toMatrix'_iff {B : BilinForm R₂ (ι -> R₂)} :
    B.toMatrix'.Nondegenerate (m := ι) ↔ B.Nondegenerate :=
  LinearMap.nondegenerate_toMatrix₂'_iff

/--
theorem `Nondegenerate.toMatrix'` / 定理 `Nondegenerate.toMatrix'`

English:
theorem Nondegenerate.toMatrix'
  given: {B : BilinForm R₂ (ι -> R₂)} (h : B.Nondegenerate)
  proof: h.toMatrix₂'

@[simp]

中文:
定理 Nondegenerate.toMatrix'
  条件: {B : BilinForm R₂ (ι -> R₂)} (h : B.Nondegenerate)
  证明: h.toMatrix₂'

@[simp]

Depends on / 依赖: h.toMatrix
-/
theorem Nondegenerate.toMatrix' {B : BilinForm R₂ (ι -> R₂)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate :=
  h.toMatrix₂'

@[simp]
/--
theorem `nondegenerate_toMatrix_iff` / 定理 `nondegenerate_toMatrix_iff`

English:
theorem nondegenerate_toMatrix_iff
  given: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  proof: (Matrix.nondegenerate_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

中文:
定理 nondegenerate_toMatrix_iff
  条件: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  证明: (Matrix.nondegenerate_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, Matrix, Matrix.nondegenerate_toBilin_iff, Matrix.toBilin_toMatrix, nondegenerate_toBilin_iff, symm.trans, toBilin_toMatrix
-/
theorem nondegenerate_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate ↔ B.Nondegenerate :=
(Matrix.nondegenerate_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

/--
theorem `Nondegenerate.toMatrix` / 定理 `Nondegenerate.toMatrix`

English:
theorem Nondegenerate.toMatrix
  given: {B : BilinForm R₂ M₂} (h : B.Nondegenerate) (b : Basis ι R₂ M₂)
  proof: (nondegenerate_toMatrix_iff b).mpr h

@[simp]

中文:
定理 Nondegenerate.toMatrix
  条件: {B : BilinForm R₂ M₂} (h : B.Nondegenerate) (b : Basis ι R₂ M₂)
  证明: (nondegenerate_toMatrix_iff b).mpr h

@[simp]

Depends on / 依赖: nondegenerate_toMatrix_iff
-/
theorem Nondegenerate.toMatrix {B : BilinForm R₂ M₂} (h : B.Nondegenerate) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h

@[simp]
/--
theorem `separatingLeft_toMatrix'_iff` / 定理 `separatingLeft_toMatrix'_iff`

English:
theorem separatingLeft_toMatrix'_iff
  given: {B : BilinForm R₂ (ι -> R₂)}
  proof: Matrix.separatingLeft_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

中文:
定理 separatingLeft_toMatrix'_iff
  条件: {B : BilinForm R₂ (ι -> R₂)}
  证明: Matrix.separatingLeft_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

Depends on / 依赖: B.SeparatingLeft, SeparatingLeft
-/
theorem separatingLeft_toMatrix'_iff {B : BilinForm R₂ (ι -> R₂)} :
    B.toMatrix'.SeparatingLeft (m := ι) ↔ B.SeparatingLeft :=
Matrix.separatingLeft_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

/--
theorem `SeparatingLeft.toMatrix'` / 定理 `SeparatingLeft.toMatrix'`

English:
theorem SeparatingLeft.toMatrix'
  given: {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingLeft)
  proof: separatingLeft_toMatrix'_iff.mpr h

@[simp]

中文:
定理 SeparatingLeft.toMatrix'
  条件: {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingLeft)
  证明: separatingLeft_toMatrix'_iff.mpr h

@[simp]

Depends on / 依赖: _iff, _iff.mpr, separatingLeft_toMatrix
-/
theorem SeparatingLeft.toMatrix' {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingLeft) :
    B.toMatrix'.SeparatingLeft :=
  separatingLeft_toMatrix'_iff.mpr h

@[simp]
/--
theorem `separatingLeft_toMatrix_iff` / 定理 `separatingLeft_toMatrix_iff`

English:
theorem separatingLeft_toMatrix_iff
  given: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  proof: (Matrix.separatingLeft_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

中文:
定理 separatingLeft_toMatrix_iff
  条件: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  证明: (Matrix.separatingLeft_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, Matrix, Matrix.separatingLeft_toBilin_iff, Matrix.toBilin_toMatrix, separatingLeft_toBilin_iff, symm.trans, toBilin_toMatrix
-/
theorem separatingLeft_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingLeft ↔ B.SeparatingLeft :=
(Matrix.separatingLeft_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

/--
theorem `SeparatingLeft.toMatrix` / 定理 `SeparatingLeft.toMatrix`

English:
theorem SeparatingLeft.toMatrix
  given: {B : BilinForm R₂ M₂} (h : B.SeparatingLeft) (b : Basis ι R₂ M₂)
  proof: (separatingLeft_toMatrix_iff b).mpr h

@[simp]

中文:
定理 SeparatingLeft.toMatrix
  条件: {B : BilinForm R₂ M₂} (h : B.SeparatingLeft) (b : Basis ι R₂ M₂)
  证明: (separatingLeft_toMatrix_iff b).mpr h

@[simp]

Depends on / 依赖: separatingLeft_toMatrix_iff
-/
theorem SeparatingLeft.toMatrix {B : BilinForm R₂ M₂} (h : B.SeparatingLeft) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingLeft :=
  (separatingLeft_toMatrix_iff b).mpr h

@[simp]
/--
theorem `separatingRight_toMatrix'_iff` / 定理 `separatingRight_toMatrix'_iff`

English:
theorem separatingRight_toMatrix'_iff
  given: {B : BilinForm R₂ (ι -> R₂)}
  proof: Matrix.separatingRight_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

中文:
定理 separatingRight_toMatrix'_iff
  条件: {B : BilinForm R₂ (ι -> R₂)}
  证明: Matrix.separatingRight_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

Depends on / 依赖: B.SeparatingRight, SeparatingRight
-/
theorem separatingRight_toMatrix'_iff {B : BilinForm R₂ (ι -> R₂)} :
    B.toMatrix'.SeparatingRight (m := ι) ↔ B.SeparatingRight :=
Matrix.separatingRight_toBilin'_iff.symm.trans (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

/--
theorem `SeparatingRight.toMatrix'` / 定理 `SeparatingRight.toMatrix'`

English:
theorem SeparatingRight.toMatrix'
  given: {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingRight)
  proof: separatingRight_toMatrix'_iff.mpr h

@[simp]

中文:
定理 SeparatingRight.toMatrix'
  条件: {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingRight)
  证明: separatingRight_toMatrix'_iff.mpr h

@[simp]

Depends on / 依赖: _iff, _iff.mpr, separatingRight_toMatrix
-/
theorem SeparatingRight.toMatrix' {B : BilinForm R₂ (ι -> R₂)} (h : B.SeparatingRight) :
    B.toMatrix'.SeparatingRight :=
  separatingRight_toMatrix'_iff.mpr h

@[simp]
/--
theorem `separatingRight_toMatrix_iff` / 定理 `separatingRight_toMatrix_iff`

English:
theorem separatingRight_toMatrix_iff
  given: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  proof: (Matrix.separatingRight_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

中文:
定理 separatingRight_toMatrix_iff
  条件: {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂)
  证明: (Matrix.separatingRight_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, Matrix, Matrix.separatingRight_toBilin_iff, Matrix.toBilin_toMatrix, separatingRight_toBilin_iff, symm.trans, toBilin_toMatrix
-/
theorem separatingRight_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingRight ↔ B.SeparatingRight :=
(Matrix.separatingRight_toBilin_iff b).symm.trans (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

/--
theorem `SeparatingRight.toMatrix` / 定理 `SeparatingRight.toMatrix`

English:
theorem SeparatingRight.toMatrix
  given: {B : BilinForm R₂ M₂} (h : B.SeparatingRight) (b : Basis ι R₂ M₂)
  proof: (separatingRight_toMatrix_iff b).mpr h

中文:
定理 SeparatingRight.toMatrix
  条件: {B : BilinForm R₂ M₂} (h : B.SeparatingRight) (b : Basis ι R₂ M₂)
  证明: (separatingRight_toMatrix_iff b).mpr h

Depends on / 依赖: separatingRight_toMatrix_iff
-/
theorem SeparatingRight.toMatrix {B : BilinForm R₂ M₂} (h : B.SeparatingRight) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).SeparatingRight :=
  (separatingRight_toMatrix_iff b).mpr h



/--
theorem `nondegenerate_toBilin'_iff_det_ne_zero` / 定理 `nondegenerate_toBilin'_iff_det_ne_zero`

English:
theorem nondegenerate_toBilin'_iff_det_ne_zero
  given: {M : Matrix ι ι A}
  proof: by
  rw [Matrix.nondegenerate_toBilin'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

中文:
定理 nondegenerate_toBilin'_iff_det_ne_zero
  条件: {M : Matrix ι ι A}
  证明: by
  rw [Matrix.nondegenerate_toBilin'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

Depends on / 依赖: Matrix, Matrix.nondegenerate_iff_det_ne_zero, Matrix.nondegenerate_toBilin, _iff, nondegenerate_iff_det_ne_zero, nondegenerate_toBilin
-/
theorem nondegenerate_toBilin'_iff_det_ne_zero {M : Matrix ι ι A} :
    M.toBilin'.Nondegenerate ↔ M.det != 0 := by
  rw [Matrix.nondegenerate_toBilin'_iff]; rw [Matrix.nondegenerate_iff_det_ne_zero]

/--
theorem `nondegenerate_toBilin'_of_det_ne_zero'` / 定理 `nondegenerate_toBilin'_of_det_ne_zero'`

English:
theorem nondegenerate_toBilin'_of_det_ne_zero'
  given: (M : Matrix ι ι A) (h : M.det != 0)
  proof: nondegenerate_toBilin'_iff_det_ne_zero.mpr h

中文:
定理 nondegenerate_toBilin'_of_det_ne_zero'
  条件: (M : Matrix ι ι A) (h : M.det != 0)
  证明: nondegenerate_toBilin'_iff_det_ne_zero.mpr h
-/
theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det != 0) :
    M.toBilin'.Nondegenerate :=
  nondegenerate_toBilin'_iff_det_ne_zero.mpr h

/--
theorem `nondegenerate_iff_det_ne_zero` / 定理 `nondegenerate_iff_det_ne_zero`

English:
theorem nondegenerate_iff_det_ne_zero
  given: {B : BilinForm A M₂} (b : Basis ι A M₂)
  proof: by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix_iff]

中文:
定理 nondegenerate_iff_det_ne_zero
  条件: {B : BilinForm A M₂} (b : Basis ι A M₂)
  证明: by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix_iff]

Depends on / 依赖: Matrix, Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff
-/
theorem nondegenerate_iff_det_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) :
    B.Nondegenerate ↔ (BilinForm.toMatrix b B).det != 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]; rw [nondegenerate_toMatrix_iff]

/--
theorem `nondegenerate_of_det_ne_zero` / 定理 `nondegenerate_of_det_ne_zero`

English:
theorem nondegenerate_of_det_ne_zero
  given: (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det != 0)
  proof: (nondegenerate_iff_det_ne_zero b).mpr h

中文:
定理 nondegenerate_of_det_ne_zero
  条件: (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det != 0)
  证明: (nondegenerate_iff_det_ne_zero b).mpr h

Depends on / 依赖: nondegenerate_iff_det_ne_zero
-/
theorem nondegenerate_of_det_ne_zero (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det != 0) :
    B₃.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h

end Det

section LeftRight

variable [IsDomain R₂] [Module.Free R₂ M₂] [Module.Finite R₂ M₂] {B : BilinForm R₂ M₂}

/--
lemma `Nondegenerate.ofSeparatingLeft` / 引理 `Nondegenerate.ofSeparatingLeft`

English:
lemma Nondegenerate.ofSeparatingLeft
  given: (hB : SeparatingLeft B)
  statement: B.Nondegenerate
  proof: by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R₂ M₂
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  rwa [← BilinForm.nondegenerate_toMatrix_iff b, Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.separatingLe

中文:
引理 Nondegenerate.ofSeparatingLeft
  条件: (hB : SeparatingLeft B)
  结论: B.Nondegenerate
  证明: by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R₂ M₂
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  rwa [← BilinForm.nondegenerate_toMatrix_iff b, Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.separatingLe

Depends on / 依赖: BilinForm, BilinForm.nondegenerate_toMatrix_iff, Classical, Classical.decEq, DecidableEq, Finite, Fintype, Fintype.ofFinite, Matrix, Matrix.nondegenerate_iff_det_ne_zero, Matrix.separatingLeft_iff_det_ne_zero, Module, Module.Finite.finite_basis, Module.Free.exists_basis, exists_basis, finite_basis, nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff, ofFinite, separatingLeft_iff_det_ne_zero
-/
lemma Nondegenerate.ofSeparatingLeft (hB : SeparatingLeft B) : B.Nondegenerate := by
  obtain ⟨ι, b⟩ := Module.Free.exists_basis R₂ M₂
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have : DecidableEq ι := Classical.decEq ι
  rwa [← BilinForm.nondegenerate_toMatrix_iff b, Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.separatingLeft_iff_det_ne_zero, separatingLeft_toMatrix_iff]

/--
lemma `Nondegenerate.ofSeparatingRight` / 引理 `Nondegenerate.ofSeparatingRight`

English:
lemma Nondegenerate.ofSeparatingRight
  given: (hB : B.SeparatingRight)
  statement: B.Nondegenerate
  proof: nondegenerate_flip_iff.mp .ofSeparatingLeft hB

中文:
引理 Nondegenerate.ofSeparatingRight
  条件: (hB : B.SeparatingRight)
  结论: B.Nondegenerate
  证明: nondegenerate_flip_iff.mp .ofSeparatingLeft hB

Depends on / 依赖: nondegenerate_flip_iff, nondegenerate_flip_iff.mp, ofSeparatingLeft
-/
lemma Nondegenerate.ofSeparatingRight (hB : B.SeparatingRight) : B.Nondegenerate :=
nondegenerate_flip_iff.mp .ofSeparatingLeft hB

/--
lemma `nondegenerate_iff_ker_eq_bot` / 引理 `nondegenerate_iff_ker_eq_bot`

English:
lemma nondegenerate_iff_ker_eq_bot
  statement: B.Nondegenerate ↔ B.ker = ⊥
  proof: by
  refine ⟨Nondegenerate.ker_eq_bot, fun h => .ofSeparatingLeft ?_⟩
  rwa [separatingLeft_iff_ker_eq_bot]

中文:
引理 nondegenerate_iff_ker_eq_bot
  结论: B.Nondegenerate ↔ B.ker = ⊥
  证明: by
  refine ⟨Nondegenerate.ker_eq_bot, fun h => .ofSeparatingLeft ?_⟩
  rwa [separatingLeft_iff_ker_eq_bot]

Depends on / 依赖: Nondegenerate, Nondegenerate.ker_eq_bot, ker_eq_bot, ofSeparatingLeft, separatingLeft_iff_ker_eq_bot
-/
lemma nondegenerate_iff_ker_eq_bot : B.Nondegenerate ↔ B.ker = ⊥ := by
  refine ⟨Nondegenerate.ker_eq_bot, fun h => .ofSeparatingLeft ?_⟩
  rwa [separatingLeft_iff_ker_eq_bot]

end LeftRight

end BilinForm

end LinearMap
