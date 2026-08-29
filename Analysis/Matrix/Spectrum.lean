/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Spectral theory of Hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem -/

@[expose] public section

open WithLp

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A B : Matrix n n 𝕜}

/--
lemma `finite_real_spectrum` / 引理 `finite_real_spectrum`

English:
lemma finite_real_spectrum
  given: [DecidableEq n]
  statement: (spectrum Real A).Finite
  proof: by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective Real 𝕜).injOn

中文:
引理 finite_real_spectrum
  条件: [DecidableEq n]
  结论: (spectrum 实数 A).Finite
  证明: by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective Real 𝕜).injOn

Depends on / 依赖: A.finite_spectrum.preimage, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, finite_spectrum, preimage, preimage_algebraMap, spectrum, spectrum.preimage_algebraMap
-/
lemma finite_real_spectrum [DecidableEq n] : (spectrum Real A).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective Real 𝕜).injOn

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: n] : Finite (spectrum Real A)
  body: A.finite_real_spectrum

中文:
实例 [DecidableEq
  签名: n] : Finite (spectrum 实数 A)
  定义体: A.finite_real_spectrum

Depends on / 依赖: A.finite_real_spectrum, finite_real_spectrum
-/
instance [DecidableEq n] : Finite (spectrum Real A) := A.finite_real_spectrum

/--
theorem `spectrum_toLpLin` / 定理 `spectrum_toLpLin`

English:
theorem spectrum_toLpLin
  given: [DecidableEq n] (p : ENNReal)
  proof: AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _

中文:
定理 spectrum_toLpLin
  条件: [DecidableEq n] (p : ENN实数)
  证明: AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _

Depends on / 依赖: AlgEquiv, AlgEquiv.spectrum_eq, Matrix, Matrix.toLinAlgEquiv, PiLp.basisFun, basisFun, spectrum_eq, toLinAlgEquiv
-/
theorem spectrum_toLpLin [DecidableEq n] (p : ENNReal) :
    spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _

/-- The spectrum of a matrix `A` coincides with the spectrum of `toEuclideanLin A`. -/
@[deprecated spectrum_toLpLin (since := "2026-01-21")]
/--
theorem `spectrum_toEuclideanLin` / 定理 `spectrum_toEuclideanLin`

English:
theorem spectrum_toEuclideanLin
  given: [DecidableEq n]
  statement: spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A
  proof: spectrum_toLpLin 2

中文:
定理 spectrum_toEuclideanLin
  条件: [DecidableEq n]
  结论: spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A
  证明: spectrum_toLpLin 2

Depends on / 依赖: spectrum_toLpLin
-/
theorem spectrum_toEuclideanLin [DecidableEq n] : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  spectrum_toLpLin 2

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

/--
Definition of `eigenvalues₀` / `eigenvalues₀` 的定义

English:
definition eigenvalues₀
  signature: : Fin (Fintype.card n) -> Real
  body: (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace

中文:
定义 eigenvalues₀
  签名: : Fin (Fintype.card n) -> 实数
  定义体: (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace

Depends on / 依赖: eigenvalues, finrank_euclideanSpace, isSymmetric_toEuclideanLin_iff, isSymmetric_toEuclideanLin_iff.mpr
-/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) -> Real :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace

/--
lemma `eigenvalues₀_antitone` / 引理 `eigenvalues₀_antitone`

English:
lemma eigenvalues₀_antitone
  statement: Antitone hA.eigenvalues₀
  proof: LinearMap.IsSymmetric.eigenvalues_antitone ..

中文:
引理 eigenvalues₀_antitone
  结论: Antitone hA.eigenvalues₀
  证明: LinearMap.IsSymmetric.eigenvalues_antitone ..

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.IsSymmetric.eigenvalues_antitone, eigenvalues_antitone
-/
lemma eigenvalues₀_antitone : Antitone hA.eigenvalues₀ :=
  LinearMap.IsSymmetric.eigenvalues_antitone ..

/--
Definition of `eigenvalues` / `eigenvalues` 的定义

English:
definition eigenvalues
  signature: : n -> Real
  body: fun i =>
hA.eigenvalues₀ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

中文:
定义 eigenvalues
  签名: : n -> 实数
  定义体: fun i =>
hA.eigenvalues₀ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
-/
noncomputable def eigenvalues : n -> Real := fun i =>
hA.eigenvalues₀ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/--
Definition of `eigenvectorBasis` / `eigenvectorBasis` 的定义

English:
definition eigenvectorBasis
  signature: : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)
  body: ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

中文:
定义 eigenvectorBasis
  签名: : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)
  定义体: ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.equivOfCardEq, card_fin, eigenvectorBasis, equivOfCardEq, finrank_euclideanSpace, isSymmetric_toEuclideanLin_iff, isSymmetric_toEuclideanLin_iff.mpr, reindex
-/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))

/--
lemma `mulVec_eigenvectorBasis` / 引理 `mulVec_eigenvectorBasis`

English:
lemma mulVec_eigenvectorBasis
  given: (j : n)
  proof: by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toLpLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using!
      congr(⇑$((isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

中文:
引理 mulVec_eigenvectorBasis
  条件: (j : n)
  证明: by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toLpLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using!
      congr(⇑$((isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.equivOfCardEq, OrthonormalBasis, OrthonormalBasis.reindex_apply, RCLike, RCLike.real_smul_eq_coe_smul, apply_eigenvectorBasis, card_fin, eigenvectorBasis, equivOfCardEq, finrank_euclideanSpace, isSymmetric_toEuclideanLin_iff, isSymmetric_toEuclideanLin_iff.mpr, real_smul_eq_coe_smul, reindex_apply, toLpLin_apply
-/
lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toLpLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using!
      congr(⇑$((isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/--
theorem `eigenvalues_mem_spectrum_real` / 定理 `eigenvalues_mem_spectrum_real`

English:
theorem eigenvalues_mem_spectrum_real
  given: (i : n)
  statement: hA.eigenvalues i in spectrum Real A
  proof: by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← Matrix.spectrum_toLpLin 2]
.mem_spectrum exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _

中文:
定理 eigenvalues_mem_spectrum_real
  条件: (i : n)
  结论: hA.eigenvalues i in spectrum 实数 A
  证明: by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← Matrix.spectrum_toLpLin 2]
.mem_spectrum exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.IsSymmetric.hasEigenvalue_eigenvalues, Matrix, Matrix.spectrum_toLpLin, hasEigenvalue_eigenvalues, mem_spectrum, of_algebraMap_mem, spectrum, spectrum.of_algebraMap_mem, spectrum_toLpLin
-/
theorem eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i in spectrum Real A := by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← Matrix.spectrum_toLpLin 2]
.mem_spectrum exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _

/--
Definition of `eigenvectorUnitary` / `eigenvectorUnitary` 的定义

English:
definition eigenvectorUnitary
  signature: {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
  body: ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩

中文:
定义 eigenvectorUnitary
  签名: {𝕜 : 类型} [RCLike 𝕜] {n : 类型}
  定义体: ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, basisFun, eigenvectorBasis, hA.eigenvectorBasis, toBasis, toBasis.toMatrix, toMatrix, toMatrix_orthonormalBasis_mem_unitary
-/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
  ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩

/--
lemma `eigenvectorUnitary_coe` / 引理 `eigenvectorUnitary_coe`

English:
lemma eigenvectorUnitary_coe
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: rfl

@[simp]

中文:
引理 eigenvectorUnitary_coe
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [Fintype n]
  证明: rfl

@[simp]
-/
lemma eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    eigenvectorUnitary hA =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

@[simp]
/--
theorem `eigenvectorUnitary_transpose_apply` / 定理 `eigenvectorUnitary_transpose_apply`

English:
theorem eigenvectorUnitary_transpose_apply
  given: (j : n)
  proof: rfl

@[simp]

中文:
定理 eigenvectorUnitary_transpose_apply
  条件: (j : n)
  证明: rfl

@[simp]
-/
theorem eigenvectorUnitary_transpose_apply (j : n) :
    (eigenvectorUnitary hA)ᵀ j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
/--
theorem `eigenvectorUnitary_col_eq` / 定理 `eigenvectorUnitary_col_eq`

English:
theorem eigenvectorUnitary_col_eq
  given: (j : n)
  proof: rfl

@[simp]

中文:
定理 eigenvectorUnitary_col_eq
  条件: (j : n)
  证明: rfl

@[simp]
-/
theorem eigenvectorUnitary_col_eq (j : n) :
    Matrix.col (eigenvectorUnitary hA) j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
/--
theorem `eigenvectorUnitary_apply` / 定理 `eigenvectorUnitary_apply`

English:
theorem eigenvectorUnitary_apply
  given: (i j : n)
  proof: rfl

中文:
定理 eigenvectorUnitary_apply
  条件: (i j : n)
  证明: rfl
-/
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl

/--
theorem `eigenvectorUnitary_mulVec` / 定理 `eigenvectorUnitary_mulVec`

English:
theorem eigenvectorUnitary_mulVec
  given: (j : n)
  proof: by
  simp_rw [mulVec_single_one, eigenvectorUnitary_col_eq]

中文:
定理 eigenvectorUnitary_mulVec
  条件: (j : n)
  证明: by
  simp_rw [mulVec_single_one, eigenvectorUnitary_col_eq]

Depends on / 依赖: eigenvectorUnitary_col_eq, mulVec_single_one, simp_rw
-/
theorem eigenvectorUnitary_mulVec (j : n) :
    eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j) := by
  simp_rw [mulVec_single_one, eigenvectorUnitary_col_eq]

/--
theorem `star_eigenvectorUnitary_mulVec` / 定理 `star_eigenvectorUnitary_mulVec`

English:
theorem star_eigenvectorUnitary_mulVec
  given: (j : n)
  proof: by
  rw [← eigenvectorUnitary_mulVec]; rw [mulVec_mulVec]; rw [Unitary.coe_star_mul_self]; rw [one_mulVec]

中文:
定理 star_eigenvectorUnitary_mulVec
  条件: (j : n)
  证明: by
  rw [← eigenvectorUnitary_mulVec]; rw [mulVec_mulVec]; rw [Unitary.coe_star_mul_self]; rw [one_mulVec]

Depends on / 依赖: Unitary, Unitary.coe_star_mul_self, coe_star_mul_self, eigenvectorUnitary_mulVec, mulVec_mulVec, one_mulVec
-/
theorem star_eigenvectorUnitary_mulVec (j : n) :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) = Pi.single j 1 := by
  rw [← eigenvectorUnitary_mulVec]; rw [mulVec_mulVec]; rw [Unitary.coe_star_mul_self]; rw [one_mulVec]

open Unitary

/--
theorem `conjStarAlgAut_star_eigenvectorUnitary` / 定理 `conjStarAlgAut_star_eigenvectorUnitary`

English:
theorem conjStarAlgAut_star_eigenvectorUnitary
  proof: by
apply Matrix.toEuclideanLin.injective (EuclideanSpace.basisFun n 𝕜).toBasis.ext fun i => ?_
  simp only [conjStarAlgAut_star_apply, toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← mulVec_mulVec,
    eigenvectorUnitary_mulVec, ← mulVec_mulVec, mu

中文:
定理 conjStarAlgAut_star_eigenvectorUnitary
  证明: by
apply Matrix.toEuclideanLin.injective (EuclideanSpace.basisFun n 𝕜).toBasis.ext fun i => ?_
  simp only [conjStarAlgAut_star_apply, toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← mulVec_mulVec,
    eigenvectorUnitary_mulVec, ← mulVec_mulVec, mu

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, EuclideanSpace.basisFun_apply, Function, Function.comp_apply, Matrix, Matrix.diagonal_mulVec_single, Matrix.toEuclideanLin.injective, OrthonormalBasis, OrthonormalBasis.coe_toBasis, PiLp.ofLp_single, PiLp.toLp_single, RCLike, RCLike.real_smul_eq_coe_smul, WithLp, WithLp.toLp_smul, basisFun, basisFun_apply, coe_toBasis, comp_apply
-/
theorem conjStarAlgAut_star_eigenvectorUnitary :
    conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) A =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
apply Matrix.toEuclideanLin.injective (EuclideanSpace.basisFun n 𝕜).toBasis.ext fun i => ?_
  simp only [conjStarAlgAut_star_apply, toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← mulVec_mulVec,
    eigenvectorUnitary_mulVec, ← mulVec_mulVec, mulVec_eigenvectorBasis,
    Matrix.diagonal_mulVec_single, mulVec_smul, star_eigenvectorUnitary_mulVec,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, PiLp.toLp_single,
    Function.comp_apply, mul_one]
  apply PiLp.ext fun j => ?_
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/--
theorem `spectral_theorem` / 定理 `spectral_theorem`

English:
theorem spectral_theorem
  proof: by
  rw [← conjStarAlgAut_star_eigenvectorUnitary]; rw [← conjStarAlgAut_mul_apply]
  simp

中文:
定理 spectral_theorem
  证明: by
  rw [← conjStarAlgAut_star_eigenvectorUnitary]; rw [← conjStarAlgAut_mul_apply]
  simp

Depends on / 依赖: conjStarAlgAut_mul_apply, conjStarAlgAut_star_eigenvectorUnitary
-/
theorem spectral_theorem :
    A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
  rw [← conjStarAlgAut_star_eigenvectorUnitary]; rw [← conjStarAlgAut_mul_apply]
  simp

/--
theorem `eigenvalues_eq` / 定理 `eigenvalues_eq`

English:
theorem eigenvalues_eq
  given: (i : n)
  proof: by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

中文:
定理 eigenvalues_eq
  条件: (i : n)
  证明: by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.inner_eq_star_dotProduct, RCLike, RCLike.one_re, RCLike.smul_re, algebraMap, algebraMap.coe_one, coe_one, dotProduct_comm, eigenvectorBasis, hA.eigenvectorBasis.orthonormal, inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, mulVec_eigenvectorBasis, mul_one, one_pow, one_re, orthonormal, smul_dotProduct, smul_re
-/
theorem eigenvalues_eq (i : n) :
    (hA.eigenvalues i) = RCLike.re (dotProduct (star ⇑(hA.eigenvectorBasis i))
    (A *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

open Polynomial in
/--
lemma `charpoly_eq` / 引理 `charpoly_eq`

English:
lemma charpoly_eq
  statement: A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜))
  proof: by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

中文:
引理 charpoly_eq
  结论: A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜))
  证明: by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

Depends on / 依赖: charpoly_diagonal, charpoly_mul_comm, conjStarAlgAut_apply, conv_lhs, hA.spectral_theorem, mul_assoc, spectral_theorem
-/
lemma charpoly_eq : A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜)) := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/--
lemma `roots_charpoly_eq_eigenvalues` / 引理 `roots_charpoly_eq_eigenvalues`

English:
lemma roots_charpoly_eq_eigenvalues
  proof: by
  rw [hA.charpoly_eq]; rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

中文:
引理 roots_charpoly_eq_eigenvalues
  证明: by
  rw [hA.charpoly_eq]; rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff, Polynomial, Polynomial.X_sub_C_ne_zero, Polynomial.roots_prod, X_sub_C_ne_zero, charpoly_eq, hA.charpoly_eq, prod_ne_zero_iff, roots_prod
-/
lemma roots_charpoly_eq_eigenvalues :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
  rw [hA.charpoly_eq]; rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `roots_charpoly_eq_eigenvalues₀` / 引理 `roots_charpoly_eq_eigenvalues₀`

English:
lemma roots_charpoly_eq_eigenvalues₀
  proof: by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [← Multiset.map_map, eigenvalues, ← Function.comp_apply (f := hA.eigenvalues₀)]
  simp

中文:
引理 roots_charpoly_eq_eigenvalues₀
  证明: by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [← Multiset.map_map, eigenvalues, ← Function.comp_apply (f := hA.eigenvalues₀)]
  simp

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.map_map, comp_apply, eigenvalues, hA.eigenvalues, hA.roots_charpoly_eq_eigenvalues, map_map, roots_charpoly_eq_eigenvalues
-/
lemma roots_charpoly_eq_eigenvalues₀ :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues₀) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [← Multiset.map_map, eigenvalues, ← Function.comp_apply (f := hA.eigenvalues₀)]
  simp

/--
lemma `sort_roots_charpoly_eq_eigenvalues₀` / 引理 `sort_roots_charpoly_eq_eigenvalues₀`

English:
lemma sort_roots_charpoly_eq_eigenvalues₀
  proof: by
  simp_rw [hA.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (eigenvalues₀_antitone hA).sortedGE_o

中文:
引理 sort_roots_charpoly_eq_eigenvalues₀
  证明: by
  simp_rw [hA.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (eigenvalues₀_antitone hA).sortedGE_o

Depends on / 依赖: Fin.univ_val_map, Function, Function.comp_def, List.map_ofFn, List.mergeSort_of_pairwise, List.sortedGE_iff_pairwise, Multiset, Multiset.coe_sort, Multiset.map_coe, RCLike, RCLike.ofReal_re, coe_sort, comp_def, decide_eq_true_eq, hA.roots_charpoly_eq_eigenvalues, map_coe, map_ofFn, mergeSort_of_pairwise, ofReal_re, simp_rw
-/
lemma sort_roots_charpoly_eq_eigenvalues₀ :
    (A.charpoly.roots.map RCLike.re).sort (· >= ·) = List.ofFn hA.eigenvalues₀ := by
  simp_rw [hA.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (eigenvalues₀_antitone hA).sortedGE_ofFn

/--
lemma `eigenvalues_eq_eigenvalues_iff` / 引理 `eigenvalues_eq_eigenvalues_iff`

English:
lemma eigenvalues_eq_eigenvalues_iff
  proof: by
  constructor <;> intro h
  · rw [hA.charpoly_eq, hB.charpoly_eq, h]
  · suffices hA.eigenvalues₀ = hB.eigenvalues₀ by unfold eigenvalues; rw [this]
    simp_rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues₀, h]

中文:
引理 eigenvalues_eq_eigenvalues_iff
  证明: by
  constructor <;> intro h
  · rw [hA.charpoly_eq, hB.charpoly_eq, h]
  · suffices hA.eigenvalues₀ = hB.eigenvalues₀ by unfold eigenvalues; rw [this]
    simp_rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues₀, h]

Depends on / 依赖: List.ofFn_inj, charpoly_eq, eigenvalues, hA.charpoly_eq, hA.eigenvalues, hB.charpoly_eq, hB.eigenvalues, ofFn_inj, simp_rw
-/
lemma eigenvalues_eq_eigenvalues_iff :
    hA.eigenvalues = hB.eigenvalues ↔ A.charpoly = B.charpoly := by
  constructor <;> intro h
  · rw [hA.charpoly_eq, hB.charpoly_eq, h]
  · suffices hA.eigenvalues₀ = hB.eigenvalues₀ by unfold eigenvalues; rw [this]
    simp_rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues₀, h]

/--
theorem `splits_charpoly` / 定理 `splits_charpoly`

English:
theorem splits_charpoly
  given: (hA : A.IsHermitian)
  statement: A.charpoly.Splits
  proof: Polynomial.splits_iff_card_roots.mpr (by simp [hA.roots_charpoly_eq_eigenvalues])

中文:
定理 splits_charpoly
  条件: (hA : A.IsHermitian)
  结论: A.charpoly.Splits
  证明: Polynomial.splits_iff_card_roots.mpr (by simp [hA.roots_charpoly_eq_eigenvalues])

Depends on / 依赖: Polynomial, Polynomial.splits_iff_card_roots.mpr, hA.roots_charpoly_eq_eigenvalues, roots_charpoly_eq_eigenvalues, splits_iff_card_roots
-/
theorem splits_charpoly (hA : A.IsHermitian) : A.charpoly.Splits :=
  Polynomial.splits_iff_card_roots.mpr (by simp [hA.roots_charpoly_eq_eigenvalues])

/--
theorem `det_eq_prod_eigenvalues` / 定理 `det_eq_prod_eigenvalues`

English:
theorem det_eq_prod_eigenvalues
  statement: det A = ∏ i, (hA.eigenvalues i : 𝕜)
  proof: by
  simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

中文:
定理 det_eq_prod_eigenvalues
  结论: det A = ∏ i, (hA.eigenvalues i : 𝕜)
  证明: by
  simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

Depends on / 依赖: det_eq_prod_roots_charpoly_of_splits, hA.roots_charpoly_eq_eigenvalues, hA.splits_charpoly, roots_charpoly_eq_eigenvalues, splits_charpoly
-/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

/--
lemma `rank_eq_rank_diagonal` / 引理 `rank_eq_rank_diagonal`

English:
lemma rank_eq_rank_diagonal
  statement: A.rank = (diagonal hA.eigenvalues).rank
  proof: by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← coe_star]
  simp [-isUnit_iff_ne_zero, -coe_star, rank_diagonal]

中文:
引理 rank_eq_rank_diagonal
  结论: A.rank = (diagonal hA.eigenvalues).rank
  证明: by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← coe_star]
  simp [-isUnit_iff_ne_zero, -coe_star, rank_diagonal]

Depends on / 依赖: coe_star, conjStarAlgAut_apply, conv_lhs, hA.spectral_theorem, isUnit_iff_ne_zero, rank_diagonal, spectral_theorem
-/
lemma rank_eq_rank_diagonal : A.rank = (diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← coe_star]
  simp [-isUnit_iff_ne_zero, -coe_star, rank_diagonal]

/--
lemma `rank_eq_card_non_zero_eigs` / 引理 `rank_eq_card_non_zero_eigs`

English:
lemma rank_eq_card_non_zero_eigs
  statement: A.rank = Fintype.card {i // hA.eigenvalues i != 0}
  proof: by
  rw [rank_eq_rank_diagonal hA]; rw [Matrix.rank_diagonal]

中文:
引理 rank_eq_card_non_zero_eigs
  结论: A.rank = Fintype.card {i // hA.eigenvalues i != 0}
  证明: by
  rw [rank_eq_rank_diagonal hA]; rw [Matrix.rank_diagonal]

Depends on / 依赖: Matrix, Matrix.rank_diagonal, rank_diagonal, rank_eq_rank_diagonal
-/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i != 0} := by
  rw [rank_eq_rank_diagonal hA]; rw [Matrix.rank_diagonal]

/--
theorem `spectrum_eq_image_range` / 定理 `spectrum_eq_image_range`

English:
theorem spectrum_eq_image_range
  proof: Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem]
  simp

中文:
定理 spectrum_eq_image_range
  证明: Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem]
  simp

Depends on / 依赖: Set.ext, conv_lhs, hA.spectral_theorem, spectral_theorem
-/
theorem spectrum_eq_image_range :
    spectrum 𝕜 A = RCLike.ofReal '' Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem]
  simp

/--
theorem `spectrum_real_eq_range_eigenvalues` / 定理 `spectrum_real_eq_range_eigenvalues`

English:
theorem spectrum_real_eq_range_eigenvalues
  proof: Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem, ← spectrum.algebraMap_mem_iff 𝕜]
  simp

中文:
定理 spectrum_real_eq_range_eigenvalues
  证明: Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem, ← spectrum.algebraMap_mem_iff 𝕜]
  simp

Depends on / 依赖: Set.ext, algebraMap_mem_iff, conv_lhs, hA.spectral_theorem, spectral_theorem, spectrum, spectrum.algebraMap_mem_iff
-/
theorem spectrum_real_eq_range_eigenvalues :
    spectrum Real A = Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem, ← spectrum.algebraMap_mem_iff 𝕜]
  simp

/--
theorem `eigenvalues_eq_zero_iff` / 定理 `eigenvalues_eq_zero_iff`

English:
theorem eigenvalues_eq_zero_iff
  proof: by
  refine ⟨fun h => ?_, fun h => by ext; simp [h, eigenvalues_eq]⟩
  rw [hA.spectral_theorem]; rw [h]; rw [Pi.comp_zero]; rw [RCLike.ofReal_zero]; rw [Function.const_zero]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [map_zero]

中文:
定理 eigenvalues_eq_zero_iff
  证明: by
  refine ⟨fun h => ?_, fun h => by ext; simp [h, eigenvalues_eq]⟩
  rw [hA.spectral_theorem]; rw [h]; rw [Pi.comp_zero]; rw [RCLike.ofReal_zero]; rw [Function.const_zero]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [map_zero]

Depends on / 依赖: Function, Function.const_zero, Pi.comp_zero, Pi.zero_def, RCLike, RCLike.ofReal_zero, comp_zero, const_zero, diagonal_zero, eigenvalues_eq, hA.spectral_theorem, map_zero, ofReal_zero, spectral_theorem, zero_def
-/
theorem eigenvalues_eq_zero_iff :
    hA.eigenvalues = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by ext; simp [h, eigenvalues_eq]⟩
  rw [hA.spectral_theorem]; rw [h]; rw [Pi.comp_zero]; rw [RCLike.ofReal_zero]; rw [Function.const_zero]; rw [Pi.zero_def]; rw [diagonal_zero]; rw [map_zero]

end DecidableEq

/--
lemma `exists_eigenvector_of_ne_zero` / 引理 `exists_eigenvector_of_ne_zero`

English:
lemma exists_eigenvector_of_ne_zero
  given: (hA : IsHermitian A) (h_ne : A != 0)
  proof: by
  classical
  have : hA.eigenvalues != 0 := by
    contrapose h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ => 0),
      diagonal_zero, map_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
exact ⟨_, _, hi,

中文:
引理 exists_eigenvector_of_ne_zero
  条件: (hA : IsHermitian A) (h_ne : A != 0)
  证明: by
  classical
  have : hA.eigenvalues != 0 := by
    contrapose h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ => 0),
      diagonal_zero, map_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
exact ⟨_, _, hi,

Depends on / 依赖: Function, Function.const, Function.ne_iff.mp, Pi.comp_zero, RCLike, RCLike.ofReal_zero, classical, comp_zero, contrapose, diagonal_zero, eigenvalues, eigenvectorBasis, hA.eigenvalues, hA.eigenvectorBasis.orthonormal.ne_zero, hA.mulVec_eigenvectorBasis, hA.spectral_theorem, h_ne, map_zero, mulVec_eigenvectorBasis, ne_iff
-/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A != 0) :
    exists (v : n -> 𝕜) (t : Real), t != 0 ∧ v != 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues != 0 := by
    contrapose h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ => 0),
      diagonal_zero, map_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
exact ⟨_, _, hi, (ofLp_eq_zero 2).ne.2 hA.eigenvectorBasis.orthonormal.ne_zero i,
    hA.mulVec_eigenvectorBasis i⟩

/--
theorem `trace_eq_sum_eigenvalues` / 定理 `trace_eq_sum_eigenvalues`

English:
theorem trace_eq_sum_eigenvalues
  given: [DecidableEq n] (hA : A.IsHermitian)
  proof: by
  simp [trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

中文:
定理 trace_eq_sum_eigenvalues
  条件: [DecidableEq n] (hA : A.IsHermitian)
  证明: by
  simp [trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

Depends on / 依赖: hA.roots_charpoly_eq_eigenvalues, hA.splits_charpoly, roots_charpoly_eq_eigenvalues, splits_charpoly, trace_eq_sum_roots_charpoly_of_splits
-/
theorem trace_eq_sum_eigenvalues [DecidableEq n] (hA : A.IsHermitian) :
    A.trace = ∑ i, (hA.eigenvalues i : 𝕜) := by
  simp [trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

end IsHermitian

end Matrix
