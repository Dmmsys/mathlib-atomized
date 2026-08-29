/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.PosDef

/-! # LDL decomposition

This file proves the LDL-decomposition of matrices: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

* `LDL.lower` is the lower triangular matrix `L`.
* `LDL.lowerInv` is the inverse of the lower triangular matrix `L`.
* `LDL.diag` is the diagonal matrix `D`.

## Main result

* `LDL.lower_conj_diag` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lowerInv_triangular`.

-/

@[expose] public section

open Module

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]

section set_options

set_option quotPrecheck false
local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y)

open Matrix InnerProductSpace

open scoped ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

/--
Definition of `LDL.lowerInv` / `LDL.lowerInv` 的定义

English:
definition LDL.lowerInv
  signature: : Matrix n n 𝕜
  body: @gramSchmidt 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)

中文:
定义 LDL.lowerInv
  签名: : 矩阵 n n 𝕜
  定义体: @gramSchmidt 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)

Depends on / 依赖: Pi.basisFun, basisFun, gramSchmidt, hS.transpose, hS.transpose.posSemidef, posSemidef, toInnerProductSpace, toNormedAddCommGroup, transpose
-/
noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)

/--
theorem `LDL.lowerInv_eq_gramSchmidtBasis` / 定理 `LDL.lowerInv_eq_gramSchmidtBasis`

English:
theorem LDL.lowerInv_eq_gramSchmidtBasis
  proof: by
  let := (Sᵀ.toNormedAddCommGroup hS.transpose)
  let := (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
  ext i j
  rw [LDL.lowerInv]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [coe_gramSchmidtBasis]
  rfl

中文:
定理 LDL.lowerInv_eq_gramSchmidtBasis
  证明: by
  let := (Sᵀ.toNormedAddCommGroup hS.transpose)
  let := (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
  ext i j
  rw [LDL.lowerInv]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [coe_gramSchmidtBasis]
  rfl

Depends on / 依赖: Basis.coePiBasisFun.toMatrix_eq_transpose, LDL.lowerInv, coePiBasisFun, coe_gramSchmidtBasis, hS.transpose, hS.transpose.posSemidef, lowerInv, posSemidef, toInnerProductSpace, toMatrix_eq_transpose, toNormedAddCommGroup, transpose
-/
theorem LDL.lowerInv_eq_gramSchmidtBasis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
            (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)))ᵀ := by
  let := (Sᵀ.toNormedAddCommGroup hS.transpose)
  let := (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
  ext i j
  rw [LDL.lowerInv]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [coe_gramSchmidtBasis]
  rfl

/--
Instance `LDL.invertibleLowerInv` / 实例 `LDL.invertibleLowerInv`

English:
instance LDL.invertibleLowerInv
  signature: : Invertible (LDL.lowerInv hS)
  body: by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
        (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n))
  infer_instance

中文:
实例 LDL.invertibleLowerInv
  签名: : 可逆 (LDL.lowerInv hS)
  定义体: by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
        (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n))
  infer_instance

Depends on / 依赖: Basis.invertibleToMatrix, LDL.lowerInv_eq_gramSchmidtBasis, Pi.basisFun, basisFun, gramSchmidtBasis, hS.transpose, hS.transpose.posSemidef, infer_instance, invertibleToMatrix, lowerInv_eq_gramSchmidtBasis, posSemidef, toInnerProductSpace, toNormedAddCommGroup, transpose
-/
noncomputable instance LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS) := by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
        (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n))
  infer_instance

/--
theorem `LDL.lowerInv_orthogonal` / 定理 `LDL.lowerInv_orthogonal`

English:
theorem LDL.lowerInv_orthogonal
  given: {i j : n} (h₀ : i != j)
  proof: @gramSchmidt_orthogonal 𝕜 _ _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) _ _ _ _ _ _ _ h₀

中文:
定理 LDL.lowerInv_orthogonal
  条件: {i j : n} (h₀ : i != j)
  证明: @gramSchmidt_orthogonal 𝕜 _ _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) _ _ _ _ _ _ _ h₀

Depends on / 依赖: gramSchmidt_orthogonal, hS.transpose, hS.transpose.posSemidef, posSemidef, toInnerProductSpace, toNormedAddCommGroup, transpose
-/
theorem LDL.lowerInv_orthogonal {i j : n} (h₀ : i != j) :
    ⟪LDL.lowerInv hS i, Sᵀ *ᵥ LDL.lowerInv hS j⟫ₑ = 0 :=
  @gramSchmidt_orthogonal 𝕜 _ _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) _ _ _ _ _ _ _ h₀

/--
Definition of `LDL.diagEntries` / `LDL.diagEntries` 的定义

English:
definition LDL.diagEntries
  signature: : n -> 𝕜
  body: fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ

中文:
定义 LDL.diagEntries
  签名: : n -> 𝕜
  定义体: fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ
-/
noncomputable def LDL.diagEntries : n -> 𝕜 := fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ

/--
Definition of `LDL.diag` / `LDL.diag` 的定义

English:
definition LDL.diag
  signature: : Matrix n n 𝕜
  body: Matrix.diagonal (LDL.diagEntries hS)

中文:
定义 LDL.diag
  签名: : 矩阵 n n 𝕜
  定义体: Matrix.diagonal (LDL.diagEntries hS)

Depends on / 依赖: LDL.diagEntries, Matrix, Matrix.diagonal, diagEntries, diagonal
-/
noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)

/--
theorem `LDL.lowerInv_triangular` / 定理 `LDL.lowerInv_triangular`

English:
theorem LDL.lowerInv_triangular
  given: {i j : n} (hij : i < j)
  statement: LDL.lowerInv hS i j = 0
  proof: by
  rw [← @gramSchmidt_triangular 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
      (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ i j hij (Pi.basisFun 𝕜 n)]; rw [Pi.basisFun_repr]; rw [LDL.lowerInv]

中文:
定理 LDL.lowerInv_triangular
  条件: {i j : n} (hij : i < j)
  结论: LDL.lowerInv hS i j = 0
  证明: by
  rw [← @gramSchmidt_triangular 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
      (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ i j hij (Pi.basisFun 𝕜 n)]; rw [Pi.basisFun_repr]; rw [LDL.lowerInv]

Depends on / 依赖: LDL.lowerInv, Pi.basisFun, Pi.basisFun_repr, basisFun, basisFun_repr, gramSchmidt_triangular, hS.transpose, hS.transpose.posSemidef, lowerInv, posSemidef, toInnerProductSpace, toNormedAddCommGroup, transpose
-/
theorem LDL.lowerInv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [← @gramSchmidt_triangular 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
      (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ i j hij (Pi.basisFun 𝕜 n)]; rw [Pi.basisFun_repr]; rw [LDL.lowerInv]

/--
theorem `LDL.diag_eq_lowerInv_conj` / 定理 `LDL.diag_eq_lowerInv_conj`

English:
theorem LDL.diag_eq_lowerInv_conj
  statement: LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ
  proof: by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_toLp_toLp, star_star, hij,
      diagonal_apply_eq, Matrix.mul_assoc, dotProduct_comm]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose]; rw [transpose_map]; rw [transpose_transpose]; rw [dotProduct_mulVec]; rw [(LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm]; rw [← inner_conj_symm]; rw [mulVec_transpose]; rw [EuclideanSpace.inner_toLp_toLp]; rw [← RCLike.star_def]; rw [←
      star_dotProduct_star]; rw [star_star]
    rfl

中文:
定理 LDL.diag_eq_lowerInv_conj
  结论: LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ
  证明: by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_toLp_toLp, star_star, hij,
      diagonal_apply_eq, Matrix.mul_assoc, dotProduct_comm]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose]; rw [transpose_map]; rw [transpose_transpose]; rw [dotProduct_mulVec]; rw [(LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm]; rw [← inner_conj_symm]; rw [mulVec_transpose]; rw [EuclideanSpace.inner_toLp_toLp]; rw [← RCLike.star_def]; rw [←
      star_dotProduct_star]; rw [star_star]
    rfl

Depends on / 依赖: EuclideanSpace, EuclideanSpace.inner_toLp_toLp, LDL.diag, LDL.lowerInv_orthogonal, Matrix, Matrix.mul_assoc, conjTranspose, diagEntries, diagonal_apply_eq, diagonal_apply_ne, dotProduct_comm, dotProduct_mulVec, h.symm, inner_conj_symm, inner_toLp_toLp, lowerInv_orthogonal, mulVec_transpose, mul_assoc, mul_mul_apply, not_false_iff
-/
theorem LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ := by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_toLp_toLp, star_star, hij,
      diagonal_apply_eq, Matrix.mul_assoc, dotProduct_comm]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose]; rw [transpose_map]; rw [transpose_transpose]; rw [dotProduct_mulVec]; rw [(LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm]; rw [← inner_conj_symm]; rw [mulVec_transpose]; rw [EuclideanSpace.inner_toLp_toLp]; rw [← RCLike.star_def]; rw [←
      star_dotProduct_star]; rw [star_star]
    rfl

/--
Definition of `LDL.lower` / `LDL.lower` 的定义

English:
definition LDL.lower
  body: (LDL.lowerInv hS)⁻¹

中文:
定义 LDL.lower
  定义体: (LDL.lowerInv hS)⁻¹

Depends on / 依赖: LDL.lowerInv, lowerInv
-/
noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹

/--
theorem `LDL.lower_conj_diag` / 定理 `LDL.lower_conj_diag`

English:
theorem LDL.lower_conj_diag
  statement: LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S
  proof: by
  rw [LDL.lower]; rw [conjTranspose_nonsing_inv]; rw [Matrix.mul_assoc]; rw [Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS)]; rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS

中文:
定理 LDL.lower_conj_diag
  结论: LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S
  证明: by
  rw [LDL.lower]; rw [conjTranspose_nonsing_inv]; rw [Matrix.mul_assoc]; rw [Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS)]; rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS

Depends on / 依赖: LDL.diag_eq_lowerInv_conj, LDL.lower, LDL.lowerInv, Matrix, Matrix.inv_mul_eq_iff_eq_mul_of_invertible, Matrix.mul_assoc, Matrix.mul_inv_eq_iff_eq_mul_of_invertible, conjTranspose_nonsing_inv, diag_eq_lowerInv_conj, inv_mul_eq_iff_eq_mul_of_invertible, lowerInv, mul_assoc, mul_inv_eq_iff_eq_mul_of_invertible
-/
theorem LDL.lower_conj_diag : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S := by
  rw [LDL.lower]; rw [conjTranspose_nonsing_inv]; rw [Matrix.mul_assoc]; rw [Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS)]; rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS

end set_options
