/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hermitian matrices over ℝ and ℂ

This file proves that Hermitian matrices over ℝ and ℂ are exactly the ones whose corresponding
linear map is self-adjoint.

## Tags

self-adjoint matrix, hermitian matrix
-/

public section

-- TODO:
-- assert_not_exists MonoidAlgebra

open RCLike

namespace Matrix

variable {𝕜 m n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜]

/--
lemma `IsHermitian.coe_re_apply_self` / 引理 `IsHermitian.coe_re_apply_self`

English:
lemma IsHermitian.coe_re_apply_self
  given: (h : A.IsHermitian) (i : n)
  statement: (re (A i i) : 𝕜) = A i i
  proof: by
  rw [← conj_eq_iff_re]; rw [← star_def]; rw [← conjTranspose_apply]; rw [h.eq]

中文:
引理 IsHermitian.coe_re_apply_self
  条件: (h : A.IsHermitian) (i : n)
  结论: (re (A i i) : 𝕜) = A i i
  证明: by
  rw [← conj_eq_iff_re]; rw [← star_def]; rw [← conjTranspose_apply]; rw [h.eq]

Depends on / 依赖: conjTranspose_apply, conj_eq_iff_re, h.eq, star_def
-/
lemma IsHermitian.coe_re_apply_self (h : A.IsHermitian) (i : n) : (re (A i i) : 𝕜) = A i i := by
  rw [← conj_eq_iff_re]; rw [← star_def]; rw [← conjTranspose_apply]; rw [h.eq]

/--
lemma `IsHermitian.coe_re_diag` / 引理 `IsHermitian.coe_re_diag`

English:
lemma IsHermitian.coe_re_diag
  given: (h : A.IsHermitian)
  statement: (fun i => (re (A.diag i) : 𝕜)) = A.diag
  proof: funext h.coe_re_apply_self

中文:
引理 IsHermitian.coe_re_diag
  条件: (h : A.IsHermitian)
  结论: (fun i => (re (A.diag i) : 𝕜)) = A.diag
  证明: funext h.coe_re_apply_self

Depends on / 依赖: coe_re_apply_self, h.coe_re_apply_self
-/
lemma IsHermitian.coe_re_diag (h : A.IsHermitian) : (fun i => (re (A.diag i) : 𝕜)) = A.diag :=
  funext h.coe_re_apply_self

/-- A matrix is Hermitian iff the corresponding linear map with an orthonormal basis is
symmetric. -/
@[simp]
/--
lemma `isSymmetric_toLin_iff` / 引理 `isSymmetric_toLin_iff`

English:
lemma isSymmetric_toLin_iff
  statement: [Fintype n] [DecidableEq n] {E : Type*}
  proof: by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  refine ⟨fun h => ?_, fun h _ _ => by rw [h.eq]⟩
  simpa using! (LinearMap.ext fun x => ext_inner_right _ (h x)).symm

中文:
引理 isSymmetric_toLin_iff
  结论: [有限类型 n] [DecidableEq n] {E : 类型}
  证明: by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  refine ⟨fun h => ?_, fun h _ _ => by rw [h.eq]⟩
  simpa using! (LinearMap.ext fun x => ext_inner_right _ (h x)).symm

Depends on / 依赖: FiniteDimensional, IsSymmetric, LinearMap, LinearMap.IsSymmetric, LinearMap.adjoint_inner_left, LinearMap.ext, adjoint_inner_left, b.toBasis.finiteDimensional_of_finite, ext_inner_right, finiteDimensional_of_finite, h.eq, simp_rw, toBasis, toLin_conjTranspose
-/
lemma isSymmetric_toLin_iff [Fintype n] [DecidableEq n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis n 𝕜 E) :
    (A.toLin b.toBasis b.toBasis).IsSymmetric ↔ A.IsHermitian := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  refine ⟨fun h => ?_, fun h _ _ => by rw [h.eq]⟩
  simpa using! (LinearMap.ext fun x => ext_inner_right _ (h x)).symm

/-- A matrix is Hermitian iff the corresponding linear map on the Euclidean space is
symmetric. -/
@[simp]
/--
lemma `isSymmetric_toEuclideanLin_iff` / 引理 `isSymmetric_toEuclideanLin_iff`

English:
lemma isSymmetric_toEuclideanLin_iff
  given: [Fintype n] [DecidableEq n]
  proof: isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

@[deprecated isSymmetric_toEuclideanLin_iff "use isSymmetric_toEuclideanLin_iff.symm"
  (since := "2026-03-30")]

中文:
引理 isSymmetric_toEuclideanLin_iff
  条件: [有限类型 n] [DecidableEq n]
  证明: isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

@[deprecated isSymmetric_toEuclideanLin_iff "use isSymmetric_toEuclideanLin_iff.symm"
  (since := "2026-03-30")]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, basisFun, isSymmetric_toLin_iff
-/
lemma isSymmetric_toEuclideanLin_iff [Fintype n] [DecidableEq n] :
    A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian :=
  isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

@[deprecated isSymmetric_toEuclideanLin_iff "use isSymmetric_toEuclideanLin_iff.symm"
  (since := "2026-03-30")]
/--
lemma `isHermitian_iff_isSymmetric` / 引理 `isHermitian_iff_isSymmetric`

English:
lemma isHermitian_iff_isSymmetric
  given: [Fintype n] [DecidableEq n]
  proof: isSymmetric_toEuclideanLin_iff.symm

中文:
引理 isHermitian_iff_isSymmetric
  条件: [有限类型 n] [DecidableEq n]
  证明: isSymmetric_toEuclideanLin_iff.symm

Depends on / 依赖: isSymmetric_toEuclideanLin_iff, isSymmetric_toEuclideanLin_iff.symm
-/
lemma isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.symm

/--
lemma `IsHermitian.im_star_dotProduct_mulVec_self` / 引理 `IsHermitian.im_star_dotProduct_mulVec_self`

English:
lemma IsHermitian.im_star_dotProduct_mulVec_self
  given: [Fintype n] (hA : A.IsHermitian) (x : n -> 𝕜)
  proof: by
  classical
  simpa [dotProduct_comm] using! (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

中文:
引理 IsHermitian.im_star_dotProduct_mulVec_self
  条件: [有限类型 n] (hA : A.IsHermitian) (x : n -> 𝕜)
  证明: by
  classical
  simpa [dotProduct_comm] using! (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

Depends on / 依赖: classical, dotProduct_comm, im_inner_self_apply, isSymmetric_toEuclideanLin_iff, isSymmetric_toEuclideanLin_iff.mpr
-/
lemma IsHermitian.im_star_dotProduct_mulVec_self [Fintype n] (hA : A.IsHermitian) (x : n -> 𝕜) :
     RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0 := by
  classical
  simpa [dotProduct_comm] using! (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

end Matrix

/-- A linear map is symmetric iff the corresponding matrix with an orthonormal basis is
Hermitian. -/
@[simp]
/--
lemma `LinearMap.isHermitian_toMatrix_iff` / 引理 `LinearMap.isHermitian_toMatrix_iff`

English:
lemma LinearMap.isHermitian_toMatrix_iff
  statement: {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  proof: by
  rw [← Matrix.isSymmetric_toLin_iff b]; rw [Matrix.toLin_toMatrix]

中文:
引理 线性映射.isHermitian_toMatrix_iff
  结论: {n 𝕜 E : 类型} [有限类型 n] [DecidableEq n] [RCLike 𝕜]
  证明: by
  rw [← Matrix.isSymmetric_toLin_iff b]; rw [Matrix.toLin_toMatrix]

Depends on / 依赖: Matrix, Matrix.isSymmetric_toLin_iff, Matrix.toLin_toMatrix, isSymmetric_toLin_iff, toLin_toMatrix
-/
lemma LinearMap.isHermitian_toMatrix_iff {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E ->ₗ[𝕜] E} (b : OrthonormalBasis n 𝕜 E) :
    (f.toMatrix b.toBasis b.toBasis).IsHermitian ↔ f.IsSymmetric := by
  rw [← Matrix.isSymmetric_toLin_iff b]; rw [Matrix.toLin_toMatrix]
