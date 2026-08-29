/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Miscellaneous results about determinant

In this file, we collect various formulas about determinant of matrices.
-/

public section

assert_not_exists TwoSidedIdeal

namespace Matrix

variable {R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det` / 定理 `submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det`

English:
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det
  statement: {n : Nat}
  proof: by
  suffices forall j, (M.submatrix (Fin.succAbove j) id).det =
      Int.negOnePow j • (M.submatrix (Fin.succAbove 0) id).det by
    rw [this j₁]; rw [this j₂]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [sub_add_cancel]
  intro j
  induction j using Fin.induction with
  | zero => rw [Fin.val_ze

中文:
定理 submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det
  结论: {n : 自然数}
  证明: by
  suffices forall j, (M.submatrix (Fin.succAbove j) id).det =
      Int.negOnePow j • (M.submatrix (Fin.succAbove 0) id).det by
    rw [this j₁]; rw [this j₂]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [sub_add_cancel]
  intro j
  induction j using Fin.induction with
  | zero => rw [Fin.val_ze

Depends on / 依赖: Fin.induction, Fin.succAbove, Fin.val_succ, Fin.val_zero, Int.negOnePow, Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_zero, M.submatrix, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Units.neg_smul, cast_add, cast_one, cast_zero, h_ind, negOnePow, negOnePow_add, negOnePow_succ
-/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin n) R) (hv : ∑ j, M j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix (Fin.succAbove j₁) id).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix (Fin.succAbove j₂) id).det := by
  suffices forall j, (M.submatrix (Fin.succAbove j) id).det =
      Int.negOnePow j • (M.submatrix (Fin.succAbove 0) id).det by
    rw [this j₁]; rw [this j₂]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [sub_add_cancel]
  intro j
  induction j using Fin.induction with
  | zero => rw [Fin.val_zero, Nat.cast_zero, Int.negOnePow_zero, one_smul]
  | succ i h_ind =>
      rw [Fin.val_succ]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Int.negOnePow_succ]; rw [Units.neg_smul]; rw [← neg_eq_iff_eq_neg]; rw [← neg_one_smul R]; rw [← det_updateRow_sum (M.submatrix i.succ.succAbove id) i (fun _ => -1)]; rw [← Fin.val_castSucc i]; rw [← h_ind]
      congr
      ext a b
      simp_rw [neg_one_smul, updateRow_apply, Finset.sum_neg_distrib, Pi.neg_apply,
        Finset.sum_apply, submatrix_apply, id_eq]
      split_ifs with h
      · replace hv := congr_fun hv b
        rw [Fin.sum_univ_succAbove _ i.succ]; rw [Pi.add_apply]; rw [Finset.sum_apply] at hv
        rwa [h, Fin.succAbove_castSucc_self, neg_eq_iff_add_eq_zero, add_comm]
      · obtain h | h := ne_iff_lt_or_gt.mp h
        · rw [Fin.succAbove_castSucc_of_lt _ _ h,
            Fin.succAbove_of_succ_le _ _ (Fin.succ_lt_succ_iff.mpr h).le]
        · rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'` / 定理 `submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'`

English:
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
  statement: {n : Nat}
  proof: by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]

中文:
定理 submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
  结论: {n : 自然数}
  证明: by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]

Depends on / 依赖: Finset, Finset.sum_apply, M.transpose, Pi.zero_apply, det_transpose, simp_rw, submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det, sum_apply, transpose, transpose_apply, transpose_submatrix, transpose_transpose, zero_apply
-/
theorem submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det' {n : Nat}
    (M : Matrix (Fin n) (Fin (n + 1)) R) (hv : forall i, ∑ j, M i j = 0) (j₁ j₂ : Fin (n + 1)) :
    (M.submatrix id (Fin.succAbove j₁)).det =
      Int.negOnePow (j₁ - j₂) • (M.submatrix id (Fin.succAbove j₂)).det := by
  rw [← det_transpose]; rw [transpose_submatrix]; rw [submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det M.transpose ?_ j₁ j₂]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]
  ext
  simp_rw [Finset.sum_apply, transpose_apply, hv, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `det_eq_sum_column_mul_submatrix_succAbove_succAbove_det` / 定理 `det_eq_sum_column_mul_submatrix_succAbove_succAbove_det`

English:
theorem det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
  statement: {n : Nat}
  proof: by
  rw [← one_smul R M.det]; rw [← Matrix.det_updateRow_sum _ i₀ (fun _ => 1)]; rw [Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv 

中文:
定理 det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
  结论: {n : 自然数}
  证明: by
  rw [← one_smul R M.det]; rw [← Matrix.det_updateRow_sum _ i₀ (fun _ => 1)]; rw [Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv 

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_const_zero, Fintype, Fintype.sum_eq_add_sum_subtype_ne, M.det, Matrix, Matrix.det_succ_row, Matrix.det_updateRow_sum, add_zero, conv_lhs, det_succ_row, det_updateRow_sum, i.prop, if_true, mul_zero, one_smul, submatrix_updateRow_succAbove, sum_apply, sum_const_zero
-/
theorem det_eq_sum_column_mul_submatrix_succAbove_succAbove_det {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : forall j != j₀, ∑ i, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : Nat) *
      (∑ i, M i j₀) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← one_smul R M.det]; rw [← Matrix.det_updateRow_sum _ i₀ (fun _ => 1)]; rw [Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv _ i.prop]; rw [mul_zero]; rw [zero_mul]
  simp [Finset.sum_const_zero, add_zero]

/--
theorem `det_eq_sum_row_mul_submatrix_succAbove_succAbove_det` / 定理 `det_eq_sum_row_mul_submatrix_succAbove_succAbove_det`

English:
theorem det_eq_sum_row_mul_submatrix_succAbove_succAbove_det
  statement: {n : Nat}
  proof: by
  rw [← det_transpose]; rw [det_eq_sum_column_mul_submatrix_succAbove_succAbove_det _ j₀ i₀
    (by simpa using hv)]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]; rw [add_comm]
  simp_rw [transpose_apply]

中文:
定理 det_eq_sum_row_mul_submatrix_succAbove_succAbove_det
  结论: {n : 自然数}
  证明: by
  rw [← det_transpose]; rw [det_eq_sum_column_mul_submatrix_succAbove_succAbove_det _ j₀ i₀
    (by simpa using hv)]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]; rw [add_comm]
  simp_rw [transpose_apply]

Depends on / 依赖: add_comm, det_eq_sum_column_mul_submatrix_succAbove_succAbove_det, det_transpose, simp_rw, transpose_apply, transpose_submatrix, transpose_transpose
-/
theorem det_eq_sum_row_mul_submatrix_succAbove_succAbove_det {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : forall i != i₀, ∑ j, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : Nat) *
      (∑ j, M i₀ j) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← det_transpose]; rw [det_eq_sum_column_mul_submatrix_succAbove_succAbove_det _ j₀ i₀
    (by simpa using hv)]; rw [← det_transpose]; rw [transpose_submatrix]; rw [transpose_transpose]; rw [add_comm]
  simp_rw [transpose_apply]

end Matrix
