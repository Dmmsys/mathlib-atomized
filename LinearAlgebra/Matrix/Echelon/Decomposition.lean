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

/-- A certificate of an echelon form decomposition of `A`, certifying that
`L * (A.submatrix σ id)` is in echelon form by providing a pivot, where `L`
is lower triangular with nonzero diagonal, and `σ` the permutation on the rows
of `A`.
This version does not store the final echelon form itself as it can be computed
by the data enclosed.
-/
/-
**Echelon.Decomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `Echelon`。
形式化陈述：{m : Type u_1} →   [Fintype m] →     [LinearOrder m] →       {n : Type u_2
} → [LinearOrder n] → {R : Type u_3} → [CommRing R] → Matrix m n R → Type (max (
max u_1 u_2) u_3)
参数：max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A certificate of an echelon form decomposition of `A`, certifying that
`L * (A.submatrix σ id)` is in echelon form by providing a pivot, where `L`
is lower triangular with nonzero diagonal, and `σ` the permutation on the rows
of `A`.
This version does not store the final echelon form itself as it can be computed
by the data enclosed.
-/
structure Decomposition (A : Matrix m n R) where
  /-- The transformation matrix. -/
  L : Matrix m m R
  /-- The row permutation on the rows of `A`. -/
  σ : Equiv.Perm m
  /-- The pivot of the resulting echelon form. -/
  pivot : m → WithTop n
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : m) : L.diag i ≠ 0
/-
**Echelon.Decomposition.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Echelon.Decomposition
`。
形式化陈述：∀ {m : Type u_1} [inst : Fintype m] [inst_1 : LinearOrder m] {n : Type u_2
} [inst_2 : Fintype n]   [inst_3 : LinearOrder n] {R : Type u_3} [inst_4 : CommR
ing R] [IsDomain R] {A : Matrix m n R}   (cert : Echelon.Decomposition A), A.ran
k = {i | cert.pivot i ≠ ⊤}.card
参数：cert : Echelon.Decomposition A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsPivotedBy.rank_eq`：rank_eq (hA : A.IsPivotedBy l) : A.rank = #{
i | l i != ⊤}
· 使用定理 `Echelon.Decomposition.isPivotedBy`：∀ {m : Type u_1} [inst : Fintype m] [
inst_1 : LinearOrder m] {n : Type u_2} [inst_2 : LinearOrder n] {R : Type u_3}  
 [inst_3 : CommRing R] …
· 使用引理 `Matrix.rank_mul_eq_right_of_isLowerTriangular`：rank_mul_eq_right_of_isLo
werTriangular {R : Type*} [CommRing R] [IsDomain R] [Fintype m] [LinearOrder m] 
(A : Matrix m m R) (B : Matrix m n …
· 使用定理 `Echelon.Decomposition.L_lowerTriangular`：∀ {m : Type u_1} [inst : Fintyp
e m] [inst_1 : LinearOrder m] {n : Type u_2} [inst_2 : LinearOrder n] {R : Type 
u_3}   [inst_3 : CommRing R] …
· 使用定理 `Echelon.Decomposition.L_diag_ne_zero`：∀ {m : Type u_1} [inst : Fintype m
] [inst_1 : LinearOrder m] {n : Type u_2} [inst_2 : LinearOrder n] {R : Type u_3
}   [inst_3 : CommRing R] …
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Matrix.rank_submatrix`：rank_submatrix [Fintype n₀] [CommSemiring R] (A :
 Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) : rank (A.submatrix em en) = rank A
-/
theorem Decomposition.rank_eq {A : Matrix m n R} (cert : Decomposition A) :
    A.rank = #{i | cert.pivot i ≠ ⊤} := by
  rw [← cert.isPivotedBy.rank_eq,
    cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

end Echelon

