/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerBasis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.

This also includes some miscellaneous results about `minpoly` on matrices.
-/

public section


noncomputable section

open Matrix Module Polynomial

universe u v w

variable {R : Type u} [CommRing R]
variable {n : Type v} [DecidableEq n] [Fintype n]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace Matrix

variable (M : Matrix n n R)

@[simp]
/--
theorem `minpoly_toLin'` / 定理 `minpoly_toLin'`

English:
theorem minpoly_toLin'
  statement: minpoly R (toLin' M) = minpoly R M
  proof: minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

@[simp]

中文:
定理 minpoly_toLin'
  结论: minpoly R (toLin' M) = minpoly R M
  证明: minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

@[simp]

Depends on / 依赖: Matrix, algEquiv_eq, minpoly, minpoly.algEquiv_eq, toLinAlgEquiv
-/
theorem minpoly_toLin' : minpoly R (toLin' M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

@[simp]
/--
theorem `minpoly_toLin` / 定理 `minpoly_toLin`

English:
theorem minpoly_toLin
  given: (b : Basis n R N) (M : Matrix n n R)
  proof: minpoly.algEquiv_eq (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M

中文:
定理 minpoly_toLin
  条件: (b : 基 n R N) (M : 矩阵 n n R)
  证明: minpoly.algEquiv_eq (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M

Depends on / 依赖: Matrix, algEquiv_eq, minpoly, minpoly.algEquiv_eq, toLinAlgEquiv
-/
theorem minpoly_toLin (b : Basis n R N) (M : Matrix n n R) :
    minpoly R (toLin b b M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  statement: IsIntegral R M
  proof: ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

中文:
定理 is整数egral
  结论: 是整 R M
  证明: ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

Depends on / 依赖: M.charpoly, aeval_self_charpoly, charpoly, charpoly_monic
-/
theorem isIntegral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

/--
theorem `minpoly_dvd_charpoly` / 定理 `minpoly_dvd_charpoly`

English:
theorem minpoly_dvd_charpoly
  given: {K : Type*} [Field K] (M : Matrix n n K)
  statement: minpoly K M ∣ M.charpoly
  proof: minpoly.dvd _ _ (aeval_self_charpoly M)

中文:
定理 minpoly_dvd_charpoly
  条件: {K : 类型} [域 K] (M : 矩阵 n n K)
  结论: minpoly K M ∣ M.charpoly
  证明: minpoly.dvd _ _ (aeval_self_charpoly M)

Depends on / 依赖: aeval_self_charpoly, minpoly, minpoly.dvd
-/
theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

end Matrix

namespace LinearMap

@[simp]
/--
theorem `minpoly_toMatrix'` / 定理 `minpoly_toMatrix'`

English:
theorem minpoly_toMatrix'
  given: (f : (n -> R) ->ₗ[R] n -> R)
  statement: minpoly R (toMatrix' f) = minpoly R f
  proof: minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

@[simp]

中文:
定理 minpoly_toMatrix'
  条件: (f : (n -> R) ->ₗ[R] n -> R)
  结论: minpoly R (toMatrix' f) = minpoly R f
  证明: minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

@[simp]

Depends on / 依赖: Matrix, algEquiv_eq, minpoly, minpoly.algEquiv_eq, toMatrixAlgEquiv
-/
theorem minpoly_toMatrix' (f : (n -> R) ->ₗ[R] n -> R) : minpoly R (toMatrix' f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

@[simp]
/--
theorem `minpoly_toMatrix` / 定理 `minpoly_toMatrix`

English:
theorem minpoly_toMatrix
  given: (b : Basis n R N) (f : N ->ₗ[R] N)
  proof: minpoly.algEquiv_eq (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f

中文:
定理 minpoly_toMatrix
  条件: (b : 基 n R N) (f : N ->ₗ[R] N)
  证明: minpoly.algEquiv_eq (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f

Depends on / 依赖: Matrix, algEquiv_eq, minpoly, minpoly.algEquiv_eq, toMatrixAlgEquiv
-/
theorem minpoly_toMatrix (b : Basis n R N) (f : N ->ₗ[R] N) :
    minpoly R (toMatrix b b f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f

end LinearMap

section PowerBasis

open Algebra

/--
theorem `charpoly_leftMulMatrix` / 定理 `charpoly_leftMulMatrix`

English:
theorem charpoly_leftMulMatrix
  given: {S : Type*} [Ring S] [Algebra R S] (h : PowerBasis R S)
  proof: by
  cases subsingleton_or_nontrivial R; · subsingleton
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (G := S) (leftMulMatrix _)).mp
      (leftMulMatrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply]; rw [aeval_self_charpoly]
  refine fun q hq 

中文:
定理 charpoly_leftMulMatrix
  条件: {S : 类型} [环 S] [代数 R S] (h : PowerBasis R S)
  证明: by
  cases subsingleton_or_nontrivial R; · subsingleton
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (G := S) (leftMulMatrix _)).mp
      (leftMulMatrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply]; rw [aeval_self_charpoly]
  refine fun q hq 

Depends on / 依赖: Fintype, Fintype.card_fin, Matrix, Matrix.charpoly_degree_eq_dim, Polynomial, Polynomial.aeval_algHom_apply, aeval_algHom_apply, aeval_self_charpoly, card_fin, charpoly_degree_eq_dim, charpoly_monic, contrapose, dim_le_degree_of_root, h.basis, h.dim_le_degree_of_root, h.gen, injective_iff_map_eq_zero, leftMulMatrix, leftMulMatrix_injective, minpoly
-/
theorem charpoly_leftMulMatrix {S : Type*} [Ring S] [Algebra R S] (h : PowerBasis R S) :
    (leftMulMatrix h.basis h.gen).charpoly = minpoly R h.gen := by
  cases subsingleton_or_nontrivial R; · subsingleton
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (G := S) (leftMulMatrix _)).mp
      (leftMulMatrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply]; rw [aeval_self_charpoly]
  refine fun q hq => or_iff_not_imp_left.2 fun h0 => ?_
  rw [Matrix.charpoly_degree_eq_dim]; rw [Fintype.card_fin] at hq
  contrapose! hq; exact h.dim_le_degree_of_root h0 hq

end PowerBasis
