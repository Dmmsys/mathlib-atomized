/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Reindexed basis

This file introduces an equivalence between the set of embeddings of `K` into `ℂ` and the
index set of the chosen basis of the ring of integers of `K`.

## Tags

house, number field, algebraic number
-/

public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

/--
Definition of `equivReindex` / `equivReindex` 的定义

English:
abbreviation equivReindex
  signature: : (K ->+* Complex) ≃ ChooseBasisIndex Int (𝓞 K)
  body: Fintype.equivOfCardEq by
    rw [Embeddings.card]; rw [← finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]

中文:
缩写 equivReindex
  签名: : (K ->+* 复形) ≃ ChooseBasisIndex 整数 (𝓞 K)
  定义体: Fintype.equivOfCardEq by
    rw [Embeddings.card]; rw [← finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]

Depends on / 依赖: Embeddings, Embeddings.card, Fintype, Fintype.equivOfCardEq, RingOfIntegers, RingOfIntegers.rank, equivOfCardEq, finrank_eq_card_chooseBasisIndex
-/
abbrev equivReindex : (K ->+* Complex) ≃ ChooseBasisIndex Int (𝓞 K) :=
Fintype.equivOfCardEq by
    rw [Embeddings.card]; rw [← finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]

/--
Definition of `basisMatrix` / `basisMatrix` 的定义

English:
abbreviation basisMatrix
  signature: : Matrix (K ->+* Complex) (K ->+* Complex) Complex
  body: (Matrix.of fun i => latticeBasis K (equivReindex K i))

中文:
缩写 basisMatrix
  签名: : 矩阵 (K ->+* 复形) (K ->+* 复形) 复形
  定义体: (Matrix.of fun i => latticeBasis K (equivReindex K i))

Depends on / 依赖: Matrix, Matrix.of, equivReindex, latticeBasis
-/
abbrev basisMatrix : Matrix (K ->+* Complex) (K ->+* Complex) Complex :=
  (Matrix.of fun i => latticeBasis K (equivReindex K i))

/--
theorem `basisMatrix_eq_embeddingsMatrixReindex` / 定理 `basisMatrix_eq_embeddingsMatrixReindex`

English:
theorem basisMatrix_eq_embeddingsMatrixReindex
  proof: by
  ext; simp [Algebra.embeddingsMatrixReindex]

中文:
定理 basisMatrix_eq_embeddingsMatrixReindex
  证明: by
  ext; simp [Algebra.embeddingsMatrixReindex]

Depends on / 依赖: Algebra, Algebra.embeddingsMatrixReindex, embeddingsMatrixReindex
-/
theorem basisMatrix_eq_embeddingsMatrixReindex :
    basisMatrix K = Algebra.embeddingsMatrixReindex Rat Complex
      (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K Complex) := by
  ext; simp [Algebra.embeddingsMatrixReindex]

open ComplexConjugate in
/--
theorem `conj_basisMatrix` / 定理 `conj_basisMatrix`

English:
theorem conj_basisMatrix
  proof: by
  ext; simp

中文:
定理 conj_basisMatrix
  证明: by
  ext; simp
-/
theorem conj_basisMatrix :
    (basisMatrix K).map conj = (basisMatrix K).reindex (Equiv.refl _)
      (ComplexEmbedding.involutive_conjugate K).toPerm := by
  ext; simp

/--
theorem `det_of_basisMatrix_non_zero` / 定理 `det_of_basisMatrix_non_zero`

English:
theorem det_of_basisMatrix_non_zero
  given: [DecidableEq (K ->+* Complex)]
  statement: (basisMatrix K).det != 0
  proof: by
  rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← pow_ne_zero_iff two_ne_zero]
  convert!
    (map_ne_zero_iff _ (algebraMap Rat Complex).injective).mpr
      (Algebra.discr_not_zero_of_basis Rat (integralBasis K))
  rw [← Algebra.discr_reindex Rat (integralBasis K) (equivReindex K).symm]
  ex

中文:
定理 det_of_basisMatrix_non_zero
  条件: [DecidableEq (K ->+* 复形)]
  结论: (basisMatrix K).det != 0
  证明: by
  rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← pow_ne_zero_iff two_ne_zero]
  convert!
    (map_ne_zero_iff _ (algebraMap Rat Complex).injective).mpr
      (Algebra.discr_not_zero_of_basis Rat (integralBasis K))
  rw [← Algebra.discr_reindex Rat (integralBasis K) (equivReindex K).symm]
  ex

Depends on / 依赖: Algebra, Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_not_zero_of_basis, Algebra.discr_reindex, RingHom, RingHom.equivRatAlgHom, algebraMap, basisMatrix_eq_embeddingsMatrixReindex, convert, discr_eq_det_embeddingsMatrixReindex_pow_two, discr_not_zero_of_basis, discr_reindex, equivRatAlgHom, equivReindex, injective, integralBasis, map_ne_zero_iff, pow_ne_zero_iff, two_ne_zero
-/
theorem det_of_basisMatrix_non_zero [DecidableEq (K ->+* Complex)] : (basisMatrix K).det != 0 := by
  rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← pow_ne_zero_iff two_ne_zero]
  convert!
    (map_ne_zero_iff _ (algebraMap Rat Complex).injective).mpr
      (Algebra.discr_not_zero_of_basis Rat (integralBasis K))
  rw [← Algebra.discr_reindex Rat (integralBasis K) (equivReindex K).symm]
  exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Rat Complex
    (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K Complex)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: (K ->+* Complex)] : Invertible (basisMatrix K)
  body: invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

中文:
实例 [DecidableEq
  签名: (K ->+* 复形)] : 可逆 (basisMatrix K)
  定义体: invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

Depends on / 依赖: invertibleOfIsUnitDet
-/
instance [DecidableEq (K ->+* Complex)] : Invertible (basisMatrix K) := invertibleOfIsUnitDet _
    (Ne.isUnit (det_of_basisMatrix_non_zero K))

variable {K}

/--
theorem `canonicalEmbedding_eq_basisMatrix_mulVec` / 定理 `canonicalEmbedding_eq_basisMatrix_mulVec`

English:
theorem canonicalEmbedding_eq_basisMatrix_mulVec
  given: (α : K)
  proof: by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α)]; rw [← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_app

中文:
定理 canonicalEmbedding_eq_basisMatrix_mulVec
  条件: (α : K)
  证明: by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α)]; rw [← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_app

Depends on / 依赖: Basis.repr_reindex, Equiv.sum_comp, Equiv.symm_symm, Finsupp, Finsupp.mapDomain_equiv_apply, Fintype, Fintype.sum_apply, Pi.smul_apply, canonicalEmbedding, canonicalEmbedding.integralBasis_repr_apply, dotProduct, equivReindex, integralBasis_repr_apply, latticeBasis, mapDomain_equiv_apply, mulVec, mul_comm, of_apply, repr_reindex, smul_apply
-/
theorem canonicalEmbedding_eq_basisMatrix_mulVec (α : K) :
    canonicalEmbedding K α = (basisMatrix K).transpose.mulVec
      (fun i => (((integralBasis K).reindex (equivReindex K).symm).repr α i : Complex)) := by
  ext i
  rw [← (latticeBasis K).sum_repr (canonicalEmbedding K α)]; rw [← Equiv.sum_comp (equivReindex K)]
  simp only [canonicalEmbedding.integralBasis_repr_apply, mulVec, dotProduct,
    transpose_apply, of_apply, Fintype.sum_apply, mul_comm, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Pi.smul_apply, smul_eq_mul]

/--
theorem `inverse_basisMatrix_mulVec_eq_repr` / 定理 `inverse_basisMatrix_mulVec_eq_repr`

English:
theorem inverse_basisMatrix_mulVec_eq_repr
  given: [DecidableEq (K ->+* Complex)] (α : 𝓞 K)
  proof: fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

中文:
定理 inverse_basisMatrix_mulVec_eq_repr
  条件: [DecidableEq (K ->+* 复形)] (α : 𝓞 K)
  证明: fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

Depends on / 依赖: algebraMap, canonicalEmbedding_eq_basisMatrix_mulVec, inv_mulVec_eq_vec
-/
theorem inverse_basisMatrix_mulVec_eq_repr [DecidableEq (K ->+* Complex)] (α : 𝓞 K) :
    forall i, ((basisMatrix K).transpose)⁻¹.mulVec (fun j =>
      canonicalEmbedding K (algebraMap (𝓞 K) K α) j) i =
      ((integralBasis K).reindex (equivReindex K).symm).repr α i := fun i => by
  rw [inv_mulVec_eq_vec (canonicalEmbedding_eq_basisMatrix_mulVec ((algebraMap (𝓞 K) K) α))]

end

end NumberField
