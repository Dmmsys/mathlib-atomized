/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Permutation matrices

This file defines the matrix associated with a permutation

## Main definitions

- `Equiv.Perm.permMatrix`: the permutation matrix associated with an `Equiv.Perm`

## Main results

- `Matrix.det_permutation`: the determinant is the sign of the permutation
- `Matrix.trace_permutation`: the trace is the number of fixed points of the permutation

-/

@[expose] public section

open Equiv

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable (R) in
/--
Definition of `Equiv.Perm.permMatrix` / `Equiv.Perm.permMatrix` 的定义

English:
abbreviation Equiv.Perm.permMatrix
  signature: [Zero R] [One R]
  body: σ.toPEquiv.toMatrix

中文:
缩写 等价.置换.permMatrix
  签名: [零 R] [幺 R]
  定义体: σ.toPEquiv.toMatrix

Depends on / 依赖: toMatrix, toPEquiv, toPEquiv.toMatrix
-/
abbrev Equiv.Perm.permMatrix [Zero R] [One R] : Matrix n n R :=
  σ.toPEquiv.toMatrix

namespace Matrix

/--
lemma `permMatrix_refl` / 引理 `permMatrix_refl`

English:
lemma permMatrix_refl
  given: [Zero R] [One R]
  statement: Equiv.Perm.permMatrix R (.refl n) = 1
  proof: by
  simp [← Matrix.ext_iff, Matrix.one_apply]

@[simp]

中文:
引理 permMatrix_refl
  条件: [零 R] [幺 R]
  结论: 等价.置换.permMatrix R (.refl n) = 1
  证明: by
  simp [← Matrix.ext_iff, Matrix.one_apply]

@[simp]
-/
@[simp] lemma permMatrix_refl [Zero R] [One R] : Equiv.Perm.permMatrix R (.refl n) = 1 := by
  simp [← Matrix.ext_iff, Matrix.one_apply]

@[simp]
/--
lemma `permMatrix_one` / 引理 `permMatrix_one`

English:
lemma permMatrix_one
  given: [Zero R] [One R]
  statement: (1 : Equiv.Perm n).permMatrix R = 1
  proof: permMatrix_refl

@[simp]

中文:
引理 permMatrix_one
  条件: [零 R] [幺 R]
  结论: (1 : 等价.置换 n).permMatrix R = 1
  证明: permMatrix_refl

@[simp]

Depends on / 依赖: permMatrix_refl
-/
lemma permMatrix_one [Zero R] [One R] : (1 : Equiv.Perm n).permMatrix R = 1 :=
  permMatrix_refl

@[simp]
/--
lemma `transpose_permMatrix` / 引理 `transpose_permMatrix`

English:
lemma transpose_permMatrix
  given: [Zero R] [One R]
  statement: (σ.permMatrix R).transpose = (σ⁻¹).permMatrix R
  proof: by
  rw [← PEquiv.toMatrix_symm]; rw [← Equiv.toPEquiv_symm]; rw [← Equiv.Perm.inv_def]

@[simp]

中文:
引理 transpose_permMatrix
  条件: [零 R] [幺 R]
  结论: (σ.permMatrix R).transpose = (σ⁻¹).permMatrix R
  证明: by
  rw [← PEquiv.toMatrix_symm]; rw [← Equiv.toPEquiv_symm]; rw [← Equiv.Perm.inv_def]

@[simp]

Depends on / 依赖: Equiv.Perm.inv_def, Equiv.toPEquiv_symm, PEquiv, PEquiv.toMatrix_symm, inv_def, toMatrix_symm, toPEquiv_symm
-/
lemma transpose_permMatrix [Zero R] [One R] : (σ.permMatrix R).transpose = (σ⁻¹).permMatrix R := by
  rw [← PEquiv.toMatrix_symm]; rw [← Equiv.toPEquiv_symm]; rw [← Equiv.Perm.inv_def]

@[simp]
/--
lemma `conjTranspose_permMatrix` / 引理 `conjTranspose_permMatrix`

English:
lemma conjTranspose_permMatrix
  given: [NonAssocSemiring R] [StarRing R]
  proof: by
  simp only [conjTranspose, transpose_permMatrix, map]
  aesop

中文:
引理 conjTranspose_permMatrix
  条件: [非结合半环 R] [对合环 R]
  证明: by
  simp only [conjTranspose, transpose_permMatrix, map]
  aesop

Depends on / 依赖: conjTranspose, transpose_permMatrix
-/
lemma conjTranspose_permMatrix [NonAssocSemiring R] [StarRing R] :
    (σ.permMatrix R).conjTranspose = (σ⁻¹).permMatrix R := by
  simp only [conjTranspose, transpose_permMatrix, map]
  aesop

variable [Fintype n]

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
/--
theorem `det_permutation` / 定理 `det_permutation`

English:
theorem det_permutation
  given: [CommRing R]
  statement: det (σ.permMatrix R) = Perm.sign σ
  proof: by
  rw [← Matrix.mul_one (σ.permMatrix R)]; rw [PEquiv.toMatrix_toPEquiv_mul]; rw [det_permute]; rw [det_one]; rw [mul_one]

中文:
定理 det_permutation
  条件: [交换环 R]
  结论: det (σ.permMatrix R) = 置换.sign σ
  证明: by
  rw [← Matrix.mul_one (σ.permMatrix R)]; rw [PEquiv.toMatrix_toPEquiv_mul]; rw [det_permute]; rw [det_one]; rw [mul_one]

Depends on / 依赖: Matrix, Matrix.mul_one, PEquiv, PEquiv.toMatrix_toPEquiv_mul, det_one, det_permute, mul_one, permMatrix, toMatrix_toPEquiv_mul
-/
theorem det_permutation [CommRing R] : det (σ.permMatrix R) = Perm.sign σ := by
  rw [← Matrix.mul_one (σ.permMatrix R)]; rw [PEquiv.toMatrix_toPEquiv_mul]; rw [det_permute]; rw [det_one]; rw [mul_one]

/--
theorem `trace_permutation` / 定理 `trace_permutation`

English:
theorem trace_permutation
  given: [AddCommMonoidWithOne R]
  proof: by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]

中文:
定理 trace_permutation
  条件: [加法交换带幺幺半群 R]
  证明: by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]

Depends on / 依赖: Function, Function.IsFixedPt, Function.fixedPoints, IsFixedPt, Set.ncard_coe_finset, fixedPoints, ncard_coe_finset, toPEquiv_apply
-/
theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]

/--
lemma `permMatrix_mulVec` / 引理 `permMatrix_mulVec`

English:
lemma permMatrix_mulVec
  given: {v : n -> R} [CommRing R]
  proof: by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]

中文:
引理 permMatrix_mulVec
  条件: {v : n -> R} [交换环 R]
  证明: by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]

Depends on / 依赖: Equiv.eq_symm_apply, Function, Function.update, Pi.single, eq_symm_apply, mulVec_eq_sum, single, update
-/
lemma permMatrix_mulVec {v : n -> R} [CommRing R] :
    σ.permMatrix R *ᵥ v = v ∘ σ := by
  ext j
  simp [mulVec_eq_sum, Pi.single, Function.update, Equiv.eq_symm_apply]

/--
lemma `vecMul_permMatrix` / 引理 `vecMul_permMatrix`

English:
lemma vecMul_permMatrix
  given: {v : n -> R} [CommRing R]
  proof: by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq σ]

@[simp]

中文:
引理 vecMul_permMatrix
  条件: {v : n -> R} [交换环 R]
  证明: by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq σ]

@[simp]

Depends on / 依赖: Equiv.symm_apply_eq, Function, Function.update, Pi.single, single, symm_apply_eq, update, vecMul_eq_sum
-/
lemma vecMul_permMatrix {v : n -> R} [CommRing R] :
    v ᵥ* σ.permMatrix R = v ∘ σ.symm := by
  ext j
  simp [vecMul_eq_sum, Pi.single, Function.update, ← Equiv.symm_apply_eq σ]

@[simp]
/--
lemma `permMatrix_mul` / 引理 `permMatrix_mul`

English:
lemma permMatrix_mul
  given: [NonAssocSemiring R]
  proof: by
  rw [Perm.permMatrix]; rw [Perm.mul_def]; rw [toPEquiv_trans]; rw [PEquiv.toMatrix_trans]

中文:
引理 permMatrix_mul
  条件: [非结合半环 R]
  证明: by
  rw [Perm.permMatrix]; rw [Perm.mul_def]; rw [toPEquiv_trans]; rw [PEquiv.toMatrix_trans]

Depends on / 依赖: PEquiv, PEquiv.toMatrix_trans, Perm.mul_def, Perm.permMatrix, mul_def, permMatrix, toMatrix_trans, toPEquiv_trans
-/
lemma permMatrix_mul [NonAssocSemiring R] :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  rw [Perm.permMatrix]; rw [Perm.mul_def]; rw [toPEquiv_trans]; rw [PEquiv.toMatrix_trans]

/-- `permMatrix` as a homomorphism. -/
@[simps]
/--
Definition of `permMatrixHom` / `permMatrixHom` 的定义

English:
definition permMatrixHom
  signature: [NonAssocSemiring R]
  body: σ⁻¹.permMatrix R
  map_one' := permMatrix_one
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permMatrix_mul]

中文:
定义 permMatrixHom
  签名: [非结合半环 R]
  定义体: σ⁻¹.permMatrix R
  map_one' := permMatrix_one
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permMatrix_mul]

Depends on / 依赖: MeasurableSpace, SeparatesPoints, Subtype, Subtype.separatesPoints, permMatrix, separatesPoints
-/
def permMatrixHom [NonAssocSemiring R] : Perm n ->* Matrix n n R where
  toFun σ := σ⁻¹.permMatrix R
  map_one' := permMatrix_one
  map_mul' σ τ := by rw [_root_.mul_inv_rev, permMatrix_mul]

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/--
theorem `permMatrix_l2_opNorm_le` / 定理 `permMatrix_l2_opNorm_le`

English:
theorem permMatrix_l2_opNorm_le
  statement: ‖σ.permMatrix 𝕜‖ <= 1
  proof: ContinuousLinearMap.opNorm_le_bound _ (by simp) by
    simp [EuclideanSpace.norm_eq, toLpLin_apply, permMatrix_mulVec,
      σ.sum_comp _ (fun i => ‖_‖ ^ 2)]

中文:
定理 permMatrix_l2_opNorm_le
  结论: ‖σ.permMatrix 𝕜‖ <= 1
  证明: ContinuousLinearMap.opNorm_le_bound _ (by simp) by
    simp [EuclideanSpace.norm_eq, toLpLin_apply, permMatrix_mulVec,
      σ.sum_comp _ (fun i => ‖_‖ ^ 2)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, EuclideanSpace, EuclideanSpace.norm_eq, MeasurableSpace, Subtype, Subtype.countablySeparated, countablySeparated, norm_eq, opNorm_le_bound, permMatrix_mulVec, sum_comp, toLpLin_apply
-/
theorem permMatrix_l2_opNorm_le : ‖σ.permMatrix 𝕜‖ <= 1 :=
ContinuousLinearMap.opNorm_le_bound _ (by simp) by
    simp [EuclideanSpace.norm_eq, toLpLin_apply, permMatrix_mulVec,
      σ.sum_comp _ (fun i => ‖_‖ ^ 2)]

/--
theorem `permMatrix_l2_opNorm_eq` / 定理 `permMatrix_l2_opNorm_eq`

English:
theorem permMatrix_l2_opNorm_eq
  given: [Nonempty n]
  statement: ‖σ.permMatrix 𝕜‖ = 1
  proof: le_antisymm (permMatrix_l2_opNorm_le σ) by
    inhabit n
    simpa [EuclideanSpace.norm_eq, permMatrix_mulVec, ← Equiv.eq_symm_apply σ, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

中文:
定理 permMatrix_l2_opNorm_eq
  条件: [非空 n]
  结论: ‖σ.permMatrix 𝕜‖ = 1
  证明: le_antisymm (permMatrix_l2_opNorm_le σ) by
    inhabit n
    simpa [EuclideanSpace.norm_eq, permMatrix_mulVec, ← Equiv.eq_symm_apply σ, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

Depends on / 依赖: Equiv.eq_symm_apply, EuclideanSpace, EuclideanSpace.norm_eq, MeasurableSpace, Pi.single, WithLp, WithLp.toLp, apply_ite, eq_symm_apply, inhabit, l2_opNorm_mulVec, le_antisymm, norm_eq, permMatrix, permMatrix_l2_opNorm_le, permMatrix_mulVec, separatesPoints_of_measurableSingletonClass, single
-/
theorem permMatrix_l2_opNorm_eq [Nonempty n] : ‖σ.permMatrix 𝕜‖ = 1 :=
le_antisymm (permMatrix_l2_opNorm_le σ) by
    inhabit n
    simpa [EuclideanSpace.norm_eq, permMatrix_mulVec, ← Equiv.eq_symm_apply σ, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

end Matrix
