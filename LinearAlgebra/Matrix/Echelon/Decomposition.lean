/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Echelon decomposition certificates

`Echelon.Decomposition A` certifies an echelon decomposition of the matrix `A`.

## Main definitions

- `Echelon.Decomposition`: the certificate structure.

## Main results

- `Echelon.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.

## Tags

matrix, echelon form
-/

public section

variable
  {m : Type*} [Fintype m] [LinearOrder m]
  {n : Type*} [Fintype n] [LinearOrder n]
  {R : Type*} [CommRing R] [IsDomain R]

namespace Echelon

open scoped Finset

/--
Definition of `Decomposition` / `Decomposition` 的定义

English:
structure Decomposition
  parameters: (A : Matrix m n R)
  axioms and operations (6):
    - L : Matrix m m R
    - σ : Equiv.Perm m
    - pivot : m -> WithTop n
    - isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
    - L_lowerTriangular : L.IsLowerTriangular
    - L_diag_ne_zero((i : m)) : L.diag i != 0

中文:
结构 分解
  参数: (A : 矩阵 m n R)
  公理与运算 (6 个):
    - L : 矩阵 m m R
    - σ : 等价.置换 m
    - pivot : m -> WithTop n
    - isPivotedBy : (L * (A.submatrix σ id)).是PivotedBy pivot
    - L_lowerTriangular : L.IsLowerTriangular
    - L_diag_ne_zero((i : m)) : L.diag i != 0
-/
structure Decomposition (A : Matrix m n R) where
  /-- The transformation matrix. -/
  L : Matrix m m R
  /-- The row permutation on the rows of `A`. -/
  σ : Equiv.Perm m
  /-- The pivot of the resulting echelon form. -/
  pivot : m -> WithTop n
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : m) : L.diag i != 0

/--
theorem `Decomposition.rank_eq` / 定理 `Decomposition.rank_eq`

English:
theorem Decomposition.rank_eq
  given: {A : Matrix m n R} (cert : Decomposition A)
  proof: by
  rw [← cert.isPivotedBy.rank_eq]; rw [cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

中文:
定理 分解.rank_eq
  条件: {A : 矩阵 m n R} (cert : 分解 A)
  证明: by
  rw [← cert.isPivotedBy.rank_eq]; rw [cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

Depends on / 依赖: A.rank_submatrix, L_diag_ne_zero, L_lowerTriangular, cert.L.rank_mul_eq_right_of_isLowerTriangular, cert.L_diag_ne_zero, cert.L_lowerTriangular, cert.isPivotedBy.rank_eq, isPivotedBy, rank_eq, rank_mul_eq_right_of_isLowerTriangular, rank_submatrix
-/
theorem Decomposition.rank_eq {A : Matrix m n R} (cert : Decomposition A) :
    A.rank = #{i | cert.pivot i != ⊤} := by
  rw [← cert.isPivotedBy.rank_eq]; rw [cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

end Echelon
