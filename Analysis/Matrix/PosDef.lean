/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spectrum of positive (semi)definite matrices

This file proves that eigenvalues of positive (semi)definite matrices are (nonnegative) positive.

## Main definitions

* `Matrix.toInnerProductSpace`: the pre-inner product space on `n → 𝕜` induced by a
  positive semi-definite matrix `M`, and is given by `⟪x, y⟫ = xᴴMy`.

-/

@[expose] public section

open WithLp Matrix Unitary
open scoped ComplexOrder

namespace Matrix
variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜] {A : Matrix n n 𝕜}

/-! ### Positive semidefinite matrices -/

/--
lemma `IsHermitian.posSemidef_iff_eigenvalues_nonneg` / 引理 `IsHermitian.posSemidef_iff_eigenvalues_nonneg`

English:
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg
  given: [DecidableEq n] (hA : IsHermitian A)
  proof: by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

中文:
引理 IsHermitian.posSemidef_iff_eigenvalues_nonneg
  条件: [DecidableEq n] (hA : IsHermitian A)
  证明: by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

Depends on / 依赖: Pi.le_def, conv_lhs, hA.spectral_theorem, isUnit_coe, isUnit_coe.posSemidef_star_right_conjugate_iff, le_def, posSemidef_diagonal_iff, posSemidef_star_right_conjugate_iff, spectral_theorem
-/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] (hA : IsHermitian A) :
    PosSemidef A ↔ 0 <= hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

namespace PosSemidef

/--
lemma `eigenvalues_nonneg` / 引理 `eigenvalues_nonneg`

English:
lemma eigenvalues_nonneg
  given: [DecidableEq n] (hA : A.PosSemidef) (i : n)
  statement: 0 <= hA.1.eigenvalues i
  proof: hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _

中文:
引理 eigenvalues_nonneg
  条件: [DecidableEq n] (hA : A.PosSemidef) (i : n)
  结论: 0 <= hA.1.eigenvalues i
  证明: hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _

Depends on / 依赖: hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp, isHermitian, posSemidef_iff_eigenvalues_nonneg
-/
lemma eigenvalues_nonneg [DecidableEq n] (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i :=
  hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _

/--
lemma `re_dotProduct_nonneg` / 引理 `re_dotProduct_nonneg`

English:
lemma re_dotProduct_nonneg
  given: (hA : A.PosSemidef) (x : n -> 𝕜)
  statement: 0 <= RCLike.re (star x ⬝ᵥ (A *ᵥ x))
  proof: .1 RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _)

中文:
引理 re_dotProduct_nonneg
  条件: (hA : A.PosSemidef) (x : n -> 𝕜)
  结论: 0 <= RCLike.re (star x ⬝ᵥ (A *ᵥ x))
  证明: .1 RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _)

Depends on / 依赖: RCLike, RCLike.nonneg_iff.mp, dotProduct_mulVec_nonneg, hA.dotProduct_mulVec_nonneg, nonneg_iff
-/
lemma re_dotProduct_nonneg (hA : A.PosSemidef) (x : n -> 𝕜) : 0 <= RCLike.re (star x ⬝ᵥ (A *ᵥ x)) :=
.1 RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _)

/--
lemma `det_nonneg` / 引理 `det_nonneg`

English:
lemma det_nonneg
  given: [DecidableEq n] (hA : A.PosSemidef)
  statement: 0 <= A.det
  proof: by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ => by simpa using hA.eigenvalues_nonneg i

中文:
引理 det_nonneg
  条件: [DecidableEq n] (hA : A.PosSemidef)
  结论: 0 <= A.det
  证明: by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ => by simpa using hA.eigenvalues_nonneg i

Depends on / 依赖: Finset, Finset.prod_nonneg, det_eq_prod_eigenvalues, eigenvalues_nonneg, hA.eigenvalues_nonneg, hA.isHermitian.det_eq_prod_eigenvalues, isHermitian, prod_nonneg
-/
lemma det_nonneg [DecidableEq n] (hA : A.PosSemidef) : 0 <= A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ => by simpa using hA.eigenvalues_nonneg i

/--
lemma `trace_eq_zero_iff` / 引理 `trace_eq_zero_iff`

English:
lemma trace_eq_zero_iff
  given: (hA : A.PosSemidef)
  statement: A.trace = 0 ↔ A = 0
  proof: by
  classical
  conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self,
    one_mul, trace_diagonal, Finset.sum_eq_zero_iff_of_nonneg (by simp [hA.eigenvalues_nonneg])]
  simp [← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff]

中文:
引理 trace_eq_zero_iff
  条件: (hA : A.PosSemidef)
  结论: A.trace = 0 ↔ A = 0
  证明: by
  classical
  conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self,
    one_mul, trace_diagonal, Finset.sum_eq_zero_iff_of_nonneg (by simp [hA.eigenvalues_nonneg])]
  simp [← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff]

Depends on / 依赖: Finset, Finset.sum_eq_zero_iff_of_nonneg, classical, coe_star_mul_self, conjStarAlgAut_apply, conv_lhs, eigenvalues_eq_zero_iff, eigenvalues_nonneg, funext_iff, hA.eigenvalues_nonneg, hA.isHermitian.eigenvalues_eq_zero_iff, isHermitian, one_mul, spectral_theorem, sum_eq_zero_iff_of_nonneg, trace_diagonal, trace_mul_cycle
-/
lemma trace_eq_zero_iff (hA : A.PosSemidef) : A.trace = 0 ↔ A = 0 := by
  classical
  conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self,
    one_mul, trace_diagonal, Finset.sum_eq_zero_iff_of_nonneg (by simp [hA.eigenvalues_nonneg])]
  simp [← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff]

end PosSemidef

/--
lemma `eigenvalues_conjTranspose_mul_self_nonneg` / 引理 `eigenvalues_conjTranspose_mul_self_nonneg`

English:
lemma eigenvalues_conjTranspose_mul_self_nonneg
  given: (A : Matrix m n 𝕜) [DecidableEq n] (i : n)
  proof: (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

中文:
引理 eigenvalues_conjTranspose_mul_self_nonneg
  条件: (A : 矩阵 m n 𝕜) [DecidableEq n] (i : n)
  证明: (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

Depends on / 依赖: eigenvalues_nonneg, posSemidef_conjTranspose_mul_self
-/
lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 <= (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

/--
lemma `eigenvalues_self_mul_conjTranspose_nonneg` / 引理 `eigenvalues_self_mul_conjTranspose_nonneg`

English:
lemma eigenvalues_self_mul_conjTranspose_nonneg
  given: (A : Matrix m n 𝕜) [DecidableEq m] (i : m)
  proof: (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

中文:
引理 eigenvalues_self_mul_conjTranspose_nonneg
  条件: (A : 矩阵 m n 𝕜) [DecidableEq m] (i : m)
  证明: (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

Depends on / 依赖: eigenvalues_nonneg, posSemidef_self_mul_conjTranspose
-/
lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 <= (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-! ### Positive definite matrices -/

/--
lemma `IsHermitian.posDef_iff_eigenvalues_pos` / 引理 `IsHermitian.posDef_iff_eigenvalues_pos`

English:
lemma IsHermitian.posDef_iff_eigenvalues_pos
  given: [DecidableEq n] (hA : A.IsHermitian)
  proof: by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

中文:
引理 IsHermitian.posDef_iff_eigenvalues_pos
  条件: [DecidableEq n] (hA : A.IsHermitian)
  证明: by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

Depends on / 依赖: conv_lhs, hA.spectral_theorem, isUnit_coe, isUnit_coe.posDef_star_right_conjugate_iff, posDef_star_right_conjugate_iff, spectral_theorem
-/
lemma IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] (hA : A.IsHermitian) :
    A.PosDef ↔ forall i, 0 < hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

namespace PosDef

/--
lemma `re_dotProduct_pos` / 引理 `re_dotProduct_pos`

English:
lemma re_dotProduct_pos
  given: (hA : A.PosDef) {x : n -> 𝕜} (hx : x != 0)
  proof: RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)

中文:
引理 re_dotProduct_pos
  条件: (hA : A.PosDef) {x : n -> 𝕜} (hx : x != 0)
  证明: RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)

Depends on / 依赖: RCLike, RCLike.pos_iff.mp, dotProduct_mulVec_pos, hA.dotProduct_mulVec_pos, pos_iff
-/
lemma re_dotProduct_pos (hA : A.PosDef) {x : n -> 𝕜} (hx : x != 0) :
.1 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)

/--
lemma `eigenvalues_pos` / 引理 `eigenvalues_pos`

English:
lemma eigenvalues_pos
  given: [DecidableEq n] (hA : A.PosDef) (i : n)
  statement: 0 < hA.1.eigenvalues i
  proof: hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i

中文:
引理 eigenvalues_pos
  条件: [DecidableEq n] (hA : A.PosDef) (i : n)
  结论: 0 < hA.1.eigenvalues i
  证明: hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i

Depends on / 依赖: hA.isHermitian.posDef_iff_eigenvalues_pos.mp, isHermitian, posDef_iff_eigenvalues_pos
-/
lemma eigenvalues_pos [DecidableEq n] (hA : A.PosDef) (i : n) : 0 < hA.1.eigenvalues i :=
  hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i

/--
lemma `det_pos` / 引理 `det_pos`

English:
lemma det_pos
  given: [DecidableEq n] (hA : A.PosDef)
  statement: 0 < det A
  proof: by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hA.eigenvalues_pos i

中文:
引理 det_pos
  条件: [DecidableEq n] (hA : A.PosDef)
  结论: 0 < det A
  证明: by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hA.eigenvalues_pos i

Depends on / 依赖: Finset, Finset.prod_pos, det_eq_prod_eigenvalues, eigenvalues_pos, hA.eigenvalues_pos, hA.isHermitian.det_eq_prod_eigenvalues, isHermitian, prod_pos
-/
lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hA.eigenvalues_pos i

end PosDef

set_option backward.privateInPublic true in
/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toSeminormedAddCommGroup`, `Matrix.toNormedAddCommGroup`,
and `Matrix.toInnerProductSpace`. -/
@[instance_reducible]
/--
Definition of `PosSemidef.preInnerProductSpace` / `PosSemidef.preInnerProductSpace` 的定义

English:
definition PosSemidef.preInnerProductSpace
  signature: {M : Matrix n n 𝕜} (hM : M.PosSemidef)
  body: (M *ᵥ y) ⬝ᵥ star x
  conj_inner_symm x y := by
    rw [dotProduct_comm]; rw [star_dotProduct]; rw [starRingEnd_apply]; rw [star_star]; rw [star_mulVec]; rw [dotProduct_comm (M *ᵥ y)]; rw [dotProduct_mulVec]; rw [hM.isHermitian.eq]
  re_inner_nonneg x := dotProduct_comm _ (star x) ▸ hM.re_dotProduct_nonneg x
  add_left := by simp only [star_add, dotProduct_add, forall_const]
  smul_left _ _ _ := by rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul]

中文:
定义 PosSemidef.preInnerProductSpace
  签名: {M : 矩阵 n n 𝕜} (hM : M.PosSemidef)
  定义体: (M *ᵥ y) ⬝ᵥ star x
  conj_inner_symm x y := by
    rw [dotProduct_comm]; rw [star_dotProduct]; rw [starRingEnd_apply]; rw [star_star]; rw [star_mulVec]; rw [dotProduct_comm (M *ᵥ y)]; rw [dotProduct_mulVec]; rw [hM.isHermitian.eq]
  re_inner_nonneg x := dotProduct_comm _ (star x) ▸ hM.re_dotProduct_nonneg x
  add_left := by simp only [star_add, dotProduct_add, forall_const]
  smul_left _ _ _ := by rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul]
-/
private def PosSemidef.preInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (n -> 𝕜) where
  inner x y := (M *ᵥ y) ⬝ᵥ star x
  conj_inner_symm x y := by
    rw [dotProduct_comm]; rw [star_dotProduct]; rw [starRingEnd_apply]; rw [star_star]; rw [star_mulVec]; rw [dotProduct_comm (M *ᵥ y)]; rw [dotProduct_mulVec]; rw [hM.isHermitian.eq]
  re_inner_nonneg x := dotProduct_comm _ (star x) ▸ hM.re_dotProduct_nonneg x
  add_left := by simp only [star_add, dotProduct_add, forall_const]
  smul_left _ _ _ := by rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `toSeminormedAddCommGroup` / `toSeminormedAddCommGroup` 的定义

English:
abbreviation toSeminormedAddCommGroup
  signature: (M : Matrix n n 𝕜) (hM : M.PosSemidef)
  body: @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.preInnerProductSpace

中文:
缩写 toSeminormedAddCommGroup
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosSemidef)
  定义体: @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.preInnerProductSpace

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toSeminormedAddCommGroup, hM.preInnerProductSpace, preInnerProductSpace, toSeminormedAddCommGroup
-/
noncomputable abbrev toSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (n -> 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.preInnerProductSpace

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `toNormedAddCommGroup` / `toNormedAddCommGroup` 的定义

English:
abbreviation toNormedAddCommGroup
  signature: (M : Matrix n n 𝕜) (hM : M.PosDef)
  body: @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
  { __ := hM.posSemidef.preInnerProductSpace
    definite x (hx : _ ⬝ᵥ _ = 0) := by
      by_contra! h
      simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h }

中文:
缩写 toNormedAddCommGroup
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosDef)
  定义体: @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
  { __ := hM.posSemidef.preInnerProductSpace
    definite x (hx : _ ⬝ᵥ _ = 0) := by
      by_contra! h
      simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h }

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toNormedAddCommGroup, definite, dotProduct_comm, hM.posSemidef.preInnerProductSpace, hM.re_dotProduct_pos, lt_irrefl, posSemidef, preInnerProductSpace, re_dotProduct_pos, toNormedAddCommGroup
-/
noncomputable abbrev toNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n -> 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
  { __ := hM.posSemidef.preInnerProductSpace
    definite x (hx : _ ⬝ᵥ _ = 0) := by
      by_contra! h
      simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h }

/-- A positive semi-definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
@[instance_reducible]
/--
Definition of `toInnerProductSpace` / `toInnerProductSpace` 的定义

English:
definition toInnerProductSpace
  signature: (M : Matrix n n 𝕜) (hM : M.PosSemidef)
  body: InnerProductSpace.ofCore _

中文:
定义 toInnerProductSpace
  签名: (M : 矩阵 n n 𝕜) (hM : M.PosSemidef)
  定义体: InnerProductSpace.ofCore _

Depends on / 依赖: InnerProductSpace, InnerProductSpace.ofCore, ofCore
-/
def toInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n -> 𝕜) _ (M.toSeminormedAddCommGroup hM) :=
  InnerProductSpace.ofCore _

end Matrix
