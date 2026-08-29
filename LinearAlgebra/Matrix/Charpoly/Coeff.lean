/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Slava Naprienko
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `Matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `Matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `Matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.
- `Matrix.coeff_det_one_add_X_smul_eq_sum_minors` proves that the k-th coefficient of
  `det (1 + X • M)` equals the sum of all k×k principal minors of M.
- `Matrix.charpoly_coeff_eq_sum_minors` expresses the coefficients of the characteristic
  polynomial as signed sums of principal minors.
- `Matrix.charpolyRev` the reverse of the characteristic polynomial.
- `Matrix.reverse_charpoly` characterises the reverse of the characteristic polynomial.

-/

@[expose] public section


noncomputable section

universe u v w z

open Finset Matrix Polynomial
open scoped Ring

variable {R : Type u} [CommRing R]
variable {n G : Type v} [DecidableEq n] [Fintype n]
variable {α β : Type v} [DecidableEq α]
variable {M : Matrix n n R}

namespace Matrix

/--
theorem `charmatrix_apply_natDegree` / 定理 `charmatrix_apply_natDegree`

English:
theorem charmatrix_apply_natDegree
  given: [Nontrivial R] (i j : n)
  proof: by
  by_cases h : i = j <;> simp [h]

中文:
定理 charmatrix_apply_natDegree
  条件: [Nontrivial R] (i j : n)
  证明: by
  by_cases h : i = j <;> simp [h]
-/
theorem charmatrix_apply_natDegree [Nontrivial R] (i j : n) :
    (charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases h : i = j <;> simp [h]

/--
theorem `charmatrix_apply_natDegree_le` / 定理 `charmatrix_apply_natDegree_le`

English:
theorem charmatrix_apply_natDegree_le
  given: (i j : n)
  proof: by
  split_ifs with h <;> simp [h, natDegree_X_le]

中文:
定理 charmatrix_apply_natDegree_le
  条件: (i j : n)
  证明: by
  split_ifs with h <;> simp [h, natDegree_X_le]

Depends on / 依赖: natDegree_X_le, split_ifs
-/
theorem charmatrix_apply_natDegree_le (i j : n) :
    (charmatrix M i j).natDegree <= ite (i = j) 1 0 := by
  split_ifs with h <;> simp [h, natDegree_X_le]

variable (M)

/--
theorem `charpoly_sub_diagonal_degree_lt` / 定理 `charpoly_sub_diagonal_degree_lt`

English:
theorem charpoly_sub_diagonal_degree_lt
  proof: by
  rw [charpoly]; rw [det_apply']; rw [← insert_erase (mem_univ (Equiv.refl n))]; rw [sum_insert (notMem_erase (Equiv.refl n) univ)]; rw [add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← me

中文:
定理 charpoly_sub_diagonal_degree_lt
  证明: by
  rw [charpoly]; rw [det_apply']; rw [← insert_erase (mem_univ (Equiv.refl n))]; rw [sum_insert (notMem_erase (Equiv.refl n) univ)]; rw [add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← me

Depends on / 依赖: C_eq_intCast, C_mul, Equiv.Perm.sign, Equiv.Perm.sign_refl, Equiv.coe_refl, Equiv.refl, Fintype, Fintype.card, Int.cast_one, Submodule, Submodule.smul_mem, Submodule.sum_mem, Units.val_one, add_comm, add_sub_cancel_right, cast_one, charmatrix_apply_eq, charpoly, coe_refl, degreeLT
-/
theorem charpoly_sub_diagonal_degree_lt :
    (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1) := by
  rw [charpoly]; rw [det_apply']; rw [← insert_erase (mem_univ (Equiv.refl n))]; rw [sum_insert (notMem_erase (Equiv.refl n) univ)]; rw [add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← mem_degreeLT]
  apply Submodule.sum_mem (degreeLT R (Fintype.card n - 1))
  intro c hc; rw [← C_eq_intCast, C_mul']
  apply Submodule.smul_mem (degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  rw [mem_degreeLT]
  apply lt_of_le_of_lt degree_le_natDegree _
  rw [Nat.cast_lt]
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_trans (Polynomial.natDegree_prod_le univ fun i : n => charmatrix M (c i) i) _
  rw [card_eq_sum_ones]; rw [sum_filter]; apply sum_le_sum
  intros
  apply charmatrix_apply_natDegree_le

/--
theorem `charpoly_coeff_eq_prod_coeff_of_le` / 定理 `charpoly_coeff_eq_prod_coeff_of_le`

English:
theorem charpoly_coeff_eq_prod_coeff_of_le
  given: {k : Nat} (h : Fintype.card n - 1 <= k)
  proof: by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h

@[simp]

中文:
定理 charpoly_coeff_eq_prod_coeff_of_le
  条件: {k : 自然数} (h : Fintype.card n - 1 <= k)
  证明: by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h

@[simp]

Depends on / 依赖: Nat.cast_le, Polynomial, Polynomial.coeff_eq_zero_of_degree_lt, cast_le, charpoly_sub_diagonal_degree_lt, coeff_eq_zero_of_degree_lt, coeff_sub, eq_of_sub_eq_zero, lt_of_lt_of_le
-/
theorem charpoly_coeff_eq_prod_coeff_of_le {k : Nat} (h : Fintype.card n - 1 <= k) :
    M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k := by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h

@[simp]
/--
theorem `charpoly_degree_eq_dim` / 定理 `charpoly_degree_eq_dim`

English:
theorem charpoly_degree_eq_dim
  given: [Nontrivial R] (M : Matrix n n R)
  proof: by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n]; rw [(X - C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degr

中文:
定理 charpoly_degree_eq_dim
  条件: [Nontrivial R] (M : Matrix n n R)
  证明: by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n]; rw [(X - C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degr

Depends on / 依赖: Fintype, Fintype.card, M.charpoly, charpoly, det_eq_one_of_card_eq_zero, sub_add_cancel
-/
theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n]; rw [(X - C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h)]; rw [natDegree_prod']
    · simp_rw [natDegree_X_sub_C]
      rw [← Finset.card_univ]; rw [sum_const]; rw [smul_eq_mul]; rw [mul_one]
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  · exact h1
  rw [h1]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

/--
theorem `charpoly_natDegree_eq_dim` / 定理 `charpoly_natDegree_eq_dim`

English:
theorem charpoly_natDegree_eq_dim
  given: [Nontrivial R] (M : Matrix n n R)
  proof: natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

中文:
定理 charpoly_natDegree_eq_dim
  条件: [Nontrivial R] (M : Matrix n n R)
  证明: natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)
-/
@[simp] theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.natDegree = Fintype.card n :=
  natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

/--
theorem `charpoly_monic` / 定理 `charpoly_monic`

English:
theorem charpoly_monic
  given: (M : Matrix n n R)
  statement: M.charpoly.Monic
  proof: by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n]; rw [

中文:
定理 charpoly_monic
  条件: (M : Matrix n n R)
  结论: M.charpoly.Monic
  证明: by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n]; rw [

Depends on / 依赖: Fintype, Fintype.card, M.charpoly, Nat.cast_lt, cast_lt, charpoly, charpoly_degree_eq_dim, charpoly_sub_diagonal_degree_lt, degree_neg, det_eq_one_of_card_eq_zero, leadingCoeff_add_of_degree_lt, lt_trans, monic_X_sub_C, monic_one, monic_prod_of_monic, neg_sub, nontriviality, sub_add_cancel
-/
theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n]; rw [(X - C (M i i))) M.charpoly] at mon
  rw [Monic] at *
  rwa [leadingCoeff_add_of_degree_lt] at mon
  rw [charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [degree_neg]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

/--
theorem `trace_eq_neg_charpoly_coeff` / 定理 `trace_eq_neg_charpoly_coeff`

English:
theorem trace_eq_neg_charpoly_coeff
  given: [Nonempty n] (M : Matrix n n R)
  proof: by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl]; rw [Fintype.card]; rw [prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos]; rw [neg_neg]; rw [trace]
  simp_rw [diag_apply]

中文:
定理 trace_eq_neg_charpoly_coeff
  条件: [Nonempty n] (M : Matrix n n R)
  证明: by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl]; rw [Fintype.card]; rw [prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos]; rw [neg_neg]; rw [trace]
  simp_rw [diag_apply]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_pos, card_pos, charpoly_coeff_eq_prod_coeff_of_le, diag_apply, le_rfl, neg_neg, prod_X_sub_C_coeff_card_pred, simp_rw
-/
theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl]; rw [Fintype.card]; rw [prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos]; rw [neg_neg]; rw [trace]
  simp_rw [diag_apply]

/--
theorem `trace_eq_neg_charpoly_nextCoeff` / 定理 `trace_eq_neg_charpoly_nextCoeff`

English:
theorem trace_eq_neg_charpoly_nextCoeff
  given: (M : Matrix n n R)
  statement: M.trace = -M.charpoly.nextCoeff
  proof: by
  cases isEmpty_or_nonempty n
  · simp [nextCoeff]
  nontriviality
  simp [trace_eq_neg_charpoly_coeff, nextCoeff]

中文:
定理 trace_eq_neg_charpoly_nextCoeff
  条件: (M : Matrix n n R)
  结论: M.trace = -M.charpoly.nextCoeff
  证明: by
  cases isEmpty_or_nonempty n
  · simp [nextCoeff]
  nontriviality
  simp [trace_eq_neg_charpoly_coeff, nextCoeff]

Depends on / 依赖: isEmpty_or_nonempty, nextCoeff, nontriviality, trace_eq_neg_charpoly_coeff
-/
theorem trace_eq_neg_charpoly_nextCoeff (M : Matrix n n R) : M.trace = -M.charpoly.nextCoeff := by
  cases isEmpty_or_nonempty n
  · simp [nextCoeff]
  nontriviality
  simp [trace_eq_neg_charpoly_coeff, nextCoeff]

/--
theorem `det_eq_sign_charpoly_coeff` / 定理 `det_eq_sign_charpoly_coeff`

English:
theorem det_eq_sign_charpoly_coeff
  given: (M : Matrix n n R)
  proof: by
  rw [coeff_zero_eq_eval_zero]; rw [charpoly]; rw [eval_det]; rw [matPolyEquiv_charmatrix]; rw [← det_smul]
  simp

中文:
定理 det_eq_sign_charpoly_coeff
  条件: (M : Matrix n n R)
  证明: by
  rw [coeff_zero_eq_eval_zero]; rw [charpoly]; rw [eval_det]; rw [matPolyEquiv_charmatrix]; rw [← det_smul]
  simp

Depends on / 依赖: charpoly, coeff_zero_eq_eval_zero, det_smul, eval_det, matPolyEquiv_charmatrix
-/
theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero]; rw [charpoly]; rw [eval_det]; rw [matPolyEquiv_charmatrix]; rw [← det_smul]
  simp

/--
lemma `derivative_det_one_add_X_smul_aux` / 引理 `derivative_det_one_add_X_smul_aux`

English:
lemma derivative_det_one_add_X_smul_aux
  given: {n} (M : Matrix (Fin n) (Fin n) R)
  proof: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero]; rw [map_sum]; rw [eval_finsetSum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
     

中文:
引理 derivative_det_one_add_X_smul_aux
  条件: {n} (M : Matrix (Fin n) (Fin n) R)
  证明: by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero]; rw [map_sum]; rw [eval_finsetSum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
     

Depends on / 依赖: Fin.val_zero, Finset, Finset.sum_eq_single, Pi.add_apply, Pi.smul_apply, X_mul_C, add_apply, add_zero, derivative_C, derivative_X, derivative_mul, det_succ_row_zero, eval_C, eval_X, eval_add, eval_det_add_X_smul, eval_finsetSum, eval_mul, eval_neg, eval_one
-/
lemma derivative_det_one_add_X_smul_aux {n} (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero]; rw [map_sum]; rw [eval_finsetSum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0]; rw [eval_zero]; rw [mul_zero]
        intro j
        rw [submatrix_apply]; rw [Fin.succAbove_of_castSucc_lt]; rw [one_apply_ne]
        · exact (bne_iff_ne (a := Fin.succ j) (b := Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H => (H <| Finset.mem_univ _).elim

/--
lemma `derivative_det_one_add_X_smul` / 引理 `derivative_det_one_add_X_smul`

English:
lemma derivative_det_one_add_X_smul
  given: (M : Matrix n n R)
  proof: by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert! derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    

中文:
引理 derivative_det_one_add_X_smul
  条件: (M : Matrix n n R)
  证明: by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert! derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    

Depends on / 依赖: Fintype, Fintype.equivFin, Matrix, Matrix.det_reindexLinearEquiv_self, Matrix.reindexLinearEquiv, coe_reindexLinearEquiv, convert, derivative_det_one_add_X_smul_aux, det_reindexLinearEquiv_self, diag_apply, equivFin, map_add, reindexLinearEquiv, reindex_apply, simp_rw, submatrix_apply, sum_comp, symm.sum_comp
-/
lemma derivative_det_one_add_X_smul (M : Matrix n n R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert! derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    simp_rw [e, coe_reindexLinearEquiv, reindex_apply, diag_apply, submatrix_apply]

/--
lemma `coeff_det_one_add_X_smul_one` / 引理 `coeff_det_one_add_X_smul_one`

English:
lemma coeff_det_one_add_X_smul_one
  given: (M : Matrix n n R)
  proof: by
  simp only [← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]

中文:
引理 coeff_det_one_add_X_smul_one
  条件: (M : Matrix n n R)
  证明: by
  simp only [← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]

Depends on / 依赖: Nat.cast_zero, cast_zero, coeff_derivative, coeff_zero_eq_eval_zero, derivative_det_one_add_X_smul, mul_one, zero_add
-/
lemma coeff_det_one_add_X_smul_one (M : Matrix n n R) :
    (det (1 + (X : R[X]) • M.map C)).coeff 1 = trace M := by
  simp only [← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]

/--
lemma `det_one_add_X_smul` / 引理 `det_one_add_X_smul`

English:
lemma det_one_add_X_smul
  given: (M : Matrix n n R)
  proof: by
  rw [Algebra.smul_def (trace M)]; rw [← C_eq_algebraMap]; rw [pow_two]; rw [← mul_assoc]; rw [add_assoc]; rw [← add_mul]; rw [← coeff_det_one_add_X_smul_one]; rw [← coeff_divX]; rw [add_comm (C _)]; rw [divX_mul_X_add]; rw [add_comm (1 : R[X]), ← C.map_one]
  convert! (divX_mul_X_add _).symm
  r

中文:
引理 det_one_add_X_smul
  条件: (M : Matrix n n R)
  证明: by
  rw [Algebra.smul_def (trace M)]; rw [← C_eq_algebraMap]; rw [pow_two]; rw [← mul_assoc]; rw [add_assoc]; rw [← add_mul]; rw [← coeff_det_one_add_X_smul_one]; rw [← coeff_divX]; rw [add_comm (C _)]; rw [divX_mul_X_add]; rw [add_comm (1 : R[X]), ← C.map_one]
  convert! (divX_mul_X_add _).symm
  r

Depends on / 依赖: Algebra, Algebra.smul_def, C.map_one, C_eq_algebraMap, add_assoc, add_comm, add_mul, coeff_det_one_add_X_smul_one, coeff_divX, coeff_zero_eq_eval_zero, convert, det_one, divX_mul_X_add, eval_det_add_X_smul, eval_one, map_one, mul_assoc, pow_two, smul_def
-/
lemma det_one_add_X_smul (M : Matrix n n R) :
    det (1 + (X : R[X]) • M.map C) =
      (1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2 := by
  rw [Algebra.smul_def (trace M)]; rw [← C_eq_algebraMap]; rw [pow_two]; rw [← mul_assoc]; rw [add_assoc]; rw [← add_mul]; rw [← coeff_det_one_add_X_smul_one]; rw [← coeff_divX]; rw [add_comm (C _)]; rw [divX_mul_X_add]; rw [add_comm (1 : R[X]), ← C.map_one]
  convert! (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero]; rw [eval_det_add_X_smul]; rw [det_one]; rw [eval_one]

/--
lemma `det_one_add_smul` / 引理 `det_one_add_smul`

English:
lemma det_one_add_smul
  given: (r : R) (M : Matrix n n R)
  proof: by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

中文:
引理 det_one_add_smul
  条件: (r : R) (M : Matrix n n R)
  证明: by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

Depends on / 依赖: Matrix, Matrix.det_one_add_X_smul, congr_arg, det_one_add_X_smul, eval_det, smul_eq_mul_diagonal
-/
lemma det_one_add_smul (r : R) (M : Matrix n n R) :
    det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

/--
lemma `charpoly_of_card_eq_two` / 引理 `charpoly_of_card_eq_two`

English:
lemma charpoly_of_card_eq_two
  given: [Nontrivial R] (hn : Fintype.card n = 2)
  proof: by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; lia
  ext i
  by_cases hi : i in Finset.range 3
  · fin_cases hi
    · simp [det_eq_sign_charpoly_coeff, hn]
    · simp [trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charp

中文:
引理 charpoly_of_card_eq_two
  条件: [Nontrivial R] (hn : Fintype.card n = 2)
  证明: by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; lia
  ext i
  by_cases hi : i in Finset.range 3
  · fin_cases hi
    · simp [det_eq_sign_charpoly_coeff, hn]
    · simp [trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charp

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, Fintype, Fintype.card_pos_iff, M.charpoly.coeff, M.charpoly_monic.leadingCoeff, Nat.succ_le_iff, Nonempty, card_pos_iff, charpoly, charpoly_monic, charpoly_natDegree_eq_dim, coeff_C, coeff_X, coeff_eq_zero_of_natDegr, det_eq_sign_charpoly_coeff, fin_cases, leadingCoeff, mem_range
-/
lemma charpoly_of_card_eq_two [Nontrivial R] (hn : Fintype.card n = 2) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; lia
  ext i
  by_cases hi : i in Finset.range 3
  · fin_cases hi
    · simp [det_eq_sign_charpoly_coeff, hn]
    · simp [trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charpoly_monic.leadingCoeff
  · rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hi
    suffices M.charpoly.coeff i = 0 by
      simpa [show i != 2 by lia, show 1 != i by lia, show i != 0 by lia, coeff_X, coeff_C]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [charpoly_natDegree_eq_dim, hn] using hi

/--
lemma `charpoly_fin_two` / 引理 `charpoly_fin_two`

English:
lemma charpoly_fin_two
  given: [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R)
  proof: M.charpoly_of_card_eq_two Fintype.card_fin _

中文:
引理 charpoly_fin_two
  条件: [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R)
  证明: M.charpoly_of_card_eq_two Fintype.card_fin _

Depends on / 依赖: Fintype, Fintype.card_fin, M.charpoly_of_card_eq_two, card_fin, charpoly_of_card_eq_two
-/
lemma charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det :=
M.charpoly_of_card_eq_two Fintype.card_fin _

end Matrix

/--
theorem `matPolyEquiv_eq_X_pow_sub_C` / 定理 `matPolyEquiv_eq_X_pow_sub_C`

English:
theorem matPolyEquiv_eq_X_pow_sub_C
  given: {K : Type*} (k : Nat) [CommRing K] (M : Matrix n n K)
  proof: by
  ext m i j
  rw [coeff_sub]; rw [coeff_C]; rw [matPolyEquiv_coeff_apply]; rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [AlgHom.coe_toRingHom]; rw [coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    sp

中文:
定理 matPolyEquiv_eq_X_pow_sub_C
  条件: {K : 类型} (k : 自然数) [CommRing K] (M : Matrix n n K)
  证明: by
  ext m i j
  rw [coeff_sub]; rw [coeff_C]; rw [matPolyEquiv_coeff_apply]; rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [AlgHom.coe_toRingHom]; rw [coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    sp

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Matrix, Matrix.map_apply, RingHom, RingHom.mapMatrix_apply, charmatrix_apply_eq, charmatrix_apply_ne, coe_toRingHom, coeff_C, coeff_X_pow, coeff_neg, coeff_sub, expand_C, expand_X, mapMatrix_apply, map_apply, map_neg, map_sub, matPolyEquiv_coeff_apply
-/
theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : Nat) [CommRing K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] ->+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  ext m i j
  rw [coeff_sub]; rw [coeff_C]; rw [matPolyEquiv_coeff_apply]; rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [AlgHom.coe_toRingHom]; rw [coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp
  · rw [charmatrix_apply_ne _ _ _ hij, map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;> simp_all

namespace Matrix

/--
theorem `aeval_eq_aeval_mod_charpoly` / 定理 `aeval_eq_aeval_mod_charpoly`

English:
theorem aeval_eq_aeval_mod_charpoly
  given: (M : Matrix n n R) (p : R[X])
  proof: (aeval_modByMonic_eq_self_of_root M.aeval_self_charpoly).symm

中文:
定理 aeval_eq_aeval_mod_charpoly
  条件: (M : Matrix n n R) (p : R[X])
  证明: (aeval_modByMonic_eq_self_of_root M.aeval_self_charpoly).symm

Depends on / 依赖: M.aeval_self_charpoly, aeval_modByMonic_eq_self_of_root, aeval_self_charpoly
-/
theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) :
    aeval M p = aeval M (p %ₘ M.charpoly) :=
  (aeval_modByMonic_eq_self_of_root M.aeval_self_charpoly).symm

/--
theorem `pow_eq_aeval_mod_charpoly` / 定理 `pow_eq_aeval_mod_charpoly`

English:
theorem pow_eq_aeval_mod_charpoly
  given: (M : Matrix n n R) (k : Nat)
  proof: by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

中文:
定理 pow_eq_aeval_mod_charpoly
  条件: (M : Matrix n n R) (k : 自然数)
  证明: by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

Depends on / 依赖: aeval_X, aeval_eq_aeval_mod_charpoly, map_pow
-/
theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : Nat) :
    M ^ k = aeval M (X ^ k %ₘ M.charpoly) := by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

section Ideal

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_charpoly_mem_ideal_pow` / 定理 `coeff_charpoly_mem_ideal_pow`

English:
theorem coeff_charpoly_mem_ideal_pow
  given: {I : Ideal R} (h : forall i j, M i j in I) (k : Nat)
  proof: by
  delta charpoly
  rw [Matrix.det_apply]; rw [finsetSum_coeff]
  apply sum_mem
  rintro c -
  rw [coeff_smul]; rw [Submodule.smul_mem_iff']
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  rw [← this]
  apply coeff_prod_mem_ideal_pow_tsub
  rintr

中文:
定理 coeff_charpoly_mem_ideal_pow
  条件: {I : Ideal R} (h : 对任意 i j, M i j in I) (k : 自然数)
  证明: by
  delta charpoly
  rw [Matrix.det_apply]; rw [finsetSum_coeff]
  apply sum_mem
  rintro c -
  rw [coeff_smul]; rw [Submodule.smul_mem_iff']
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  rw [← this]
  apply coeff_prod_mem_ideal_pow_tsub
  rintr

Depends on / 依赖: Finset, Finset.sum_const, Fintype, Fintype.card, Matrix, Matrix.det_apply, Submodule, Submodule.smul_mem_iff, add_comm, card_univ, charmatrix_apply, charpoly, coeff_C_zero, coeff_X_mul_zero, coeff_prod_mem_ideal_pow_tsub, coeff_smul, coeff_sub, det_apply, finsetSum_coeff, mul_one
-/
theorem coeff_charpoly_mem_ideal_pow {I : Ideal R} (h : forall i j, M i j in I) (k : Nat) :
    M.charpoly.coeff k in I ^ (Fintype.card n - k) := by
  delta charpoly
  rw [Matrix.det_apply]; rw [finsetSum_coeff]
  apply sum_mem
  rintro c -
  rw [coeff_smul]; rw [Submodule.smul_mem_iff']
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  rw [← this]
  apply coeff_prod_mem_ideal_pow_tsub
  rintro i - (_ | k)
  · rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, ← smul_one_eq_diagonal, smul_apply,
      smul_eq_mul, coeff_X_mul_zero, coeff_C_zero, zero_sub, neg_mem_iff]
    exact h (c i) i
  · rw [add_comm, tsub_self_add, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

end Ideal

section reverse

open LaurentPolynomial hiding C

/--
Definition of `charpolyRev` / `charpolyRev` 的定义

English:
definition charpolyRev
  signature: (M : Matrix n n R)
  body: det (1 - (X : R[X]) • M.map C)

中文:
定义 charpolyRev
  签名: (M : Matrix n n R)
  定义体: det (1 - (X : R[X]) • M.map C)

Depends on / 依赖: M.map
-/
def charpolyRev (M : Matrix n n R) : R[X] := det (1 - (X : R[X]) • M.map C)

/--
lemma `reverse_charpoly` / 引理 `reverse_charpoly`

English:
lemma reverse_charpoly
  given: (M : Matrix n n R)
  proof: by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : t

中文:
引理 reverse_charpoly
  条件: (M : Matrix n n R)
  证明: by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : t

Depends on / 依赖: AlgHom, AlgHom.map_det, LaurentPolynomial, LaurentPolynomial.C, M.charpoly, M.charpolyRev, M.map, T_add, T_zero, charmatrix, charpoly, charpolyRev, map_det, map_sub, neg_add_cancel, nontriviality, scalar, smul_eq_diagonal_mul, t_inv, toLaurentAlg
-/
lemma reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = M.charpolyRev := by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : toLaurentAlg M.charpoly = p := by
    simp [p, t, charpoly, charmatrix, AlgHom.map_det, map_sub]
  have hq : toLaurentAlg M.charpolyRev = q := by
    simp [q, t, charpolyRev, AlgHom.map_det, map_sub, smul_eq_diagonal_mul]
  suffices t_inv ^ Fintype.card n * p = invert q by
    apply toLaurent_injective
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : Int), ← T_pow, map_pow, invert_T, mul_comm]
  rw [← det_smul]; rw [smul_sub]; rw [scalar_apply]; rw [← diagonal_smul]; rw [Pi.smul_def]; rw [smul_eq_mul]; rw [ht]; rw [diagonal_one]; rw [invert.map_det]
  simp [t_inv, map_sub, map_one, map_mul, t, smul_eq_diagonal_mul]

/--
theorem `charpoly_inv` / 定理 `charpoly_inv`

English:
theorem charpoly_inv
  given: (A : Matrix n n R) (h : IsUnit A)
  proof: by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C (A⁻¹ * A).det * (scalar n X - C.mapMatrix A⁻¹).det := by simp
  _ = C A⁻¹.det * C A.det * (scalar n X - C.mapMatrix A⁻¹).det := by rw [det_mul]; simp
  _ = C A⁻¹.det * (C A.det * (scalar n X - C.m

中文:
定理 charpoly_inv
  条件: (A : Matrix n n R) (h : IsUnit A)
  证明: by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C (A⁻¹ * A).det * (scalar n X - C.mapMatrix A⁻¹).det := by simp
  _ = C A⁻¹.det * C A.det * (scalar n X - C.mapMatrix A⁻¹).det := by rw [det_mul]; simp
  _ = C A⁻¹.det * (C A.det * (scalar n X - C.m

Depends on / 依赖: A.det, C.mapMatrix, Invertible, RingHom, RingHom.map_det, det_mul, h.invertible, invertible, mapMatrix, map_det, map_mul, mul_sub, scalar
-/
theorem charpoly_inv (A : Matrix n n R) (h : IsUnit A) :
    A⁻¹.charpoly = (-1) ^ Fintype.card n * C A.det⁻¹ʳ * A.charpolyRev := by
  have : Invertible A := h.invertible
  calc
  _ = (scalar n X - C.mapMatrix A⁻¹).det := rfl
  _ = C (A⁻¹ * A).det * (scalar n X - C.mapMatrix A⁻¹).det := by simp
  _ = C A⁻¹.det * C A.det * (scalar n X - C.mapMatrix A⁻¹).det := by rw [det_mul]; simp
  _ = C A⁻¹.det * (C A.det * (scalar n X - C.mapMatrix A⁻¹).det) := by ac_rfl
  _ = C A⁻¹.det * (C.mapMatrix A * (scalar n X - C.mapMatrix A⁻¹)).det := by simp [RingHom.map_det]
  _ = C A⁻¹.det * (C.mapMatrix A * scalar n X - 1).det := by rw [mul_sub, ← map_mul]; simp
  _ = C A⁻¹.det * ((-1) ^ Fintype.card n * (1 - scalar n X * C.mapMatrix A).det) := by
    rw [← neg_sub]; rw [det_neg]; rw [det_one_sub_mul_comm]
  _ = _ := by simp [charpolyRev, smul_eq_diagonal_mul]; ac_rfl

/--
lemma `eval_charpolyRev` / 引理 `eval_charpolyRev`

English:
lemma eval_charpolyRev
  proof: by
  rw [charpolyRev]; rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij, one_apply]
  congr

中文:
引理 eval_charpolyRev
  证明: by
  rw [charpolyRev]; rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij, one_apply]
  congr
-/
@[simp] lemma eval_charpolyRev :
    eval 0 M.charpolyRev = 1 := by
  rw [charpolyRev]; rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij, one_apply]
  congr

/--
lemma `coeff_charpolyRev_eq_neg_trace` / 引理 `coeff_charpolyRev_eq_neg_trace`

English:
lemma coeff_charpolyRev_eq_neg_trace
  given: (M : Matrix n n R)
  proof: by
  nontriviality R
  cases isEmpty_or_nonempty n
  · simp [charpolyRev, coeff_one]
  · simp [trace_eq_neg_charpoly_coeff M, ← M.reverse_charpoly, nextCoeff]

中文:
引理 coeff_charpolyRev_eq_neg_trace
  条件: (M : Matrix n n R)
  证明: by
  nontriviality R
  cases isEmpty_or_nonempty n
  · simp [charpolyRev, coeff_one]
  · simp [trace_eq_neg_charpoly_coeff M, ← M.reverse_charpoly, nextCoeff]
-/
@[simp] lemma coeff_charpolyRev_eq_neg_trace (M : Matrix n n R) :
    coeff M.charpolyRev 1 = - trace M := by
  nontriviality R
  cases isEmpty_or_nonempty n
  · simp [charpolyRev, coeff_one]
  · simp [trace_eq_neg_charpoly_coeff M, ← M.reverse_charpoly, nextCoeff]

/--
lemma `isUnit_charpolyRev_of_isNilpotent` / 引理 `isUnit_charpolyRev_of_isNilpotent`

English:
lemma isUnit_charpolyRev_of_isNilpotent
  given: (hM : IsNilpotent M)
  proof: by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert! one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply]; rw [smul_pow]; rw [← map_pow]; rw [hk]; rw [map_zero]; rw [smul_zero]; rw [sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R :=

中文:
引理 isUnit_charpolyRev_of_isNilpotent
  条件: (hM : IsNilpotent M)
  证明: by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert! one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply]; rw [smul_pow]; rw [← map_pow]; rw [hk]; rw [map_zero]; rw [smul_zero]; rw [sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R :=

Depends on / 依赖: C.mapMatrix_apply, M.map, convert, detMonoidHom, det_one, isUnit_of_dvd_one, mapMatrix_apply, map_dvd, map_pow, map_zero, one_sub_dvd_one_sub_pow, replace, smul_pow, smul_zero, sub_zero
-/
lemma isUnit_charpolyRev_of_isNilpotent (hM : IsNilpotent M) :
    IsUnit M.charpolyRev := by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert! one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply]; rw [smul_pow]; rw [← map_pow]; rw [hk]; rw [map_zero]; rw [smul_zero]; rw [sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R := R[X]) (n := n)]
  exact map_dvd detMonoidHom hk

/--
lemma `isNilpotent_trace_of_isNilpotent` / 引理 `isNilpotent_trace_of_isNilpotent`

English:
lemma isNilpotent_trace_of_isNilpotent
  given: (hM : IsNilpotent M)
  proof: by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero

中文:
引理 isNilpotent_trace_of_isNilpotent
  条件: (hM : IsNilpotent M)
  证明: by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero

Depends on / 依赖: IsNilpotent, charpolyRev, isEmpty_or_nonempty, isUnit_charpolyRev_of_isNilpotent, isUnit_iff_coeff_isUnit_isNilpotent, isUnit_iff_coeff_isUnit_isNilpotent.mp, one_ne_zero
-/
lemma isNilpotent_trace_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (trace M) := by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero

/--
lemma `isNilpotent_charpoly_sub_pow_of_isNilpotent` / 引理 `isNilpotent_charpoly_sub_pow_of_isNilpotent`

English:
lemma isNilpotent_charpoly_sub_pow_of_isNilpotent
  given: (hM : IsNilpotent M)
  proof: by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = X * (p /ₘ X) := by
    conv_lhs => rw [← modByMonic_add_div p X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X 

中文:
引理 isNilpotent_charpoly_sub_pow_of_isNilpotent
  条件: (hM : IsNilpotent M)
  证明: by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = X * (p /ₘ X) := by
    conv_lhs => rw [← modByMonic_add_div p X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X 

Depends on / 依赖: Fintype, Fintype.card, IsNilpotent, M.charpoly, M.charpoly.natDegree, M.charpolyRev, M.reverse_charpoly, Polynomial, Polynomial.isUnit_iff, charpoly, charpolyRev, conv_lhs, isNilpotent_reflect_iff, isUnit_charpolyRev_of_isNilpotent, isUnit_iff, le_trans, modByMonic_X, modByMonic_add_div, natDegree, natDegree_sub_le
-/
lemma isNilpotent_charpoly_sub_pow_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (M.charpoly - X ^ (Fintype.card n)) := by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = X * (p /ₘ X) := by
    conv_lhs => rw [← modByMonic_add_div p X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X ^ (Fintype.card n)).natDegree <= M.charpoly.natDegree :=
    le_trans (natDegree_sub_le _ _) (by simp)
  rw [← isNilpotent_reflect_iff aux]; rw [reflect_sub]; rw [← reverse]; rw [M.reverse_charpoly]
  simpa [p, hp]

/--
lemma `det_piecewise_one_eq_submatrix_det` / 引理 `det_piecewise_one_eq_submatrix_det`

English:
lemma det_piecewise_one_eq_submatrix_det
  proof: by
  let e := Equiv.sumCompl (fun x => x in s)
  let +generalize A : Matrix n n R := Matrix.of (s.piecewise M (1 : Matrix n n R))
  rw [← Matrix.det_submatrix_equiv_self e A]
  have h_blocks : A.submatrix e e =
      Matrix.fromBlocks
        (M.submatrix Subtype.val Subtype.val)
        (M.submatri

中文:
引理 det_piecewise_one_eq_submatrix_det
  证明: by
  let e := Equiv.sumCompl (fun x => x in s)
  let +generalize A : Matrix n n R := Matrix.of (s.piecewise M (1 : Matrix n n R))
  rw [← Matrix.det_submatrix_equiv_self e A]
  have h_blocks : A.submatrix e e =
      Matrix.fromBlocks
        (M.submatrix Subtype.val Subtype.val)
        (M.submatri

Depends on / 依赖: A.submatrix, Equiv.sumCompl, Finset, Finset.piecewise, M.submatrix, Matrix, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks, Matrix.of, Matrix.one_a, Subtype, Subtype.val, det_submatrix_equiv_self, fromBlocks, generalize, h_blocks, i.prop, if_neg, if_pos, one_a
-/
lemma det_piecewise_one_eq_submatrix_det
    (M : Matrix n n R) (s : Finset n) :
    det (Matrix.of <| s.piecewise M.row (1 : Matrix n n R).row) =
    (M.submatrix (↑) (↑) : Matrix s s R).det := by
  let e := Equiv.sumCompl (fun x => x in s)
  let +generalize A : Matrix n n R := Matrix.of (s.piecewise M (1 : Matrix n n R))
  rw [← Matrix.det_submatrix_equiv_self e A]
  have h_blocks : A.submatrix e e =
      Matrix.fromBlocks
        (M.submatrix Subtype.val Subtype.val)
        (M.submatrix Subtype.val Subtype.val) 0 1 := by
    ext (i | i) (j | j) <;> dsimp [A, e]
    · simp only [Finset.piecewise, if_pos i.prop]
    · simp only [Finset.piecewise, if_pos i.prop]
    · simp only [Finset.piecewise, if_neg i.prop]
      exact Matrix.one_apply_ne (fun h => i.prop (h ▸ j.prop))
    · simp only [Finset.piecewise, if_neg i.prop, Matrix.one_apply, Subtype.ext_iff]
  rw [h_blocks]; rw [Matrix.det_fromBlocks_zero₂₁]; rw [Matrix.det_one]; rw [mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coeff_det_one_add_X_smul_eq_sum_minors` / 定理 `coeff_det_one_add_X_smul_eq_sum_minors`

English:
theorem coeff_det_one_add_X_smul_eq_sum_minors
  proof: by
  simp only [det]
  let D := (detRowAlternating : (n -> R[X]) [⋀^n]->ₗ[R[X]] R[X])
  rw [add_comm]
  change (D (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i)).coeff k = _
  conv_lhs => rw [show (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i) =
      (fun i => ((X : R[

中文:
定理 coeff_det_one_add_X_smul_eq_sum_minors
  证明: by
  simp only [det]
  let D := (detRowAlternating : (n -> R[X]) [⋀^n]->ₗ[R[X]] R[X])
  rw [add_comm]
  change (D (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i)).coeff k = _
  conv_lhs => rw [show (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i) =
      (fun i => ((X : R[

Depends on / 依赖: D.map_add_univ, Finset, M.map, Matrix, add_comm, conv_lhs, detRowAlternating, h_map, map_add_univ, piecewise, s.piecewise
-/
theorem coeff_det_one_add_X_smul_eq_sum_minors
    (M : Matrix n n R) (k : Nat) :
    (det (1 + (X : R[X]) • M.map C)).coeff k =
    ∑ s in Finset.univ.powersetCard k,
      (M.submatrix (Subtype.val : s -> n) (Subtype.val : s -> n)).det := by
  simp only [det]
  let D := (detRowAlternating : (n -> R[X]) [⋀^n]->ₗ[R[X]] R[X])
  rw [add_comm]
  change (D (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i)).coeff k = _
  conv_lhs => rw [show (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i) =
      (fun i => ((X : R[X]) • M.map C) i) + (fun i => (1 : Matrix n n R[X]) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  have h_map : forall s : Finset n,
        (s.piecewise (fun i => (M.map C) i)
          (fun i => (1 : Matrix n n R[X]) i) : Matrix n n R[X]) =
        Matrix.map (s.piecewise M (1 : Matrix n n R)) C := by
      intro s; ext i j
      simp only [Finset.piecewise, Matrix.map_apply]
      split_ifs with h <;> simp [Matrix.one_apply]
  have h_det : forall s : Finset n,
      D (s.piecewise (fun i => (M.map C) i)
        (fun i => (1 : Matrix n n R[X]) i)) =
      C (det (s.piecewise M (1 : Matrix n n R))) := by
    intro s; change det _ = _
    rw [h_map]; exact (RingHom.map_det C _).symm
  calc (∑ s : Finset n, D (Finset.piecewise s (fun i => ((X : R[X]) • M.map C) i)
            (fun i => (1 : Matrix n n R[X]) i))).coeff k
      _ = (∑ s : Finset n, (X : R[X]) ^ s.card •
            D (s.piecewise (fun i => (M.map C) i)
              (fun i => (1 : Matrix n n R[X]) i))).coeff k := by
        congr 2 with s
        have h_smul : s.piecewise (fun i => ((X : R[X]) • M.map C) i)
            (fun i => (1 : Matrix n n R[X]) i) =
            fun i => (if i in s then (X : R[X]) else 1) •
              s.piecewise (fun i => (M.map C) i) (fun i => (1 : Matrix n n R[X]) i) i := by
          funext i j
          simp only [piecewise, Pi.smul_apply, smul_eq_mul, ite_mul, one_mul]
          split_ifs <;> rfl
        rw [h_smul]; rw [D.map_smul_univ]
        congr 1
        simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      _ = ∑ s : Finset n, ((X : R[X]) ^ s.card •
            D (Finset.piecewise s (fun i => (M.map C) i)
              (fun i => (1 : Matrix n n R[X]) i))).coeff k := by
        simp only [Polynomial.finsetSum_coeff]
      _ = _ := by
        simp_rw [h_det, smul_eq_mul, mul_comm (X ^ _) (C _)]
        simp_rw [C_mul_X_pow_eq_monomial, coeff_monomial]
        rw [← Finset.sum_filter]
        have h_set : Finset.univ.filter (fun s : Finset n => s.card = k) =
            Finset.univ.powersetCard k := by
          ext s; simp [Finset.mem_powersetCard]
        rw [h_set]
        exact Finset.sum_congr rfl fun s _ => det_piecewise_one_eq_submatrix_det M s

/--
theorem `charpoly_coeff_eq_sum_minors` / 定理 `charpoly_coeff_eq_sum_minors`

English:
theorem charpoly_coeff_eq_sum_minors
  proof: by
  nontriviality R
  have hnd := M.charpoly_natDegree_eq_dim
  have hrev : M.charpoly.coeff (Fintype.card n - k) = M.charpoly.reverse.coeff k := by
    simp [Polynomial.coeff_reverse, hnd, hk]
  rw [hrev]; rw [M.reverse_charpoly]
  have hcharpolyRev : M.charpolyRev = det (1 + (X : R[X]) • (-M).map

中文:
定理 charpoly_coeff_eq_sum_minors
  证明: by
  nontriviality R
  have hnd := M.charpoly_natDegree_eq_dim
  have hrev : M.charpoly.coeff (Fintype.card n - k) = M.charpoly.reverse.coeff k := by
    simp [Polynomial.coeff_reverse, hnd, hk]
  rw [hrev]; rw [M.reverse_charpoly]
  have hcharpolyRev : M.charpolyRev = det (1 + (X : R[X]) • (-M).map

Depends on / 依赖: Fintype, Fintype.card, M.charpoly.coeff, M.charpoly.reverse.coeff, M.charpolyRev, M.charpoly_natDegree_eq_dim, M.reverse_charpoly, Matrix, Matrix.map_neg, Pi.neg_apply, Polynomial, Polynomial.coeff_reverse, charpoly, charpolyRev, charpoly_natDegree_eq_dim, coeff_det_one_add_X_smul_eq_sum_minors, coeff_reverse, hcharpolyRev, map_neg, neg_apply
-/
theorem charpoly_coeff_eq_sum_minors
    (M : Matrix n n R) (k : Nat) (hk : k <= Fintype.card n) :
    M.charpoly.coeff (Fintype.card n - k) =
    (-1) ^ k * ∑ s in Finset.univ.powersetCard k,
      (M.submatrix (Subtype.val : s -> n) (Subtype.val : s -> n)).det := by
  nontriviality R
  have hnd := M.charpoly_natDegree_eq_dim
  have hrev : M.charpoly.coeff (Fintype.card n - k) = M.charpoly.reverse.coeff k := by
    simp [Polynomial.coeff_reverse, hnd, hk]
  rw [hrev]; rw [M.reverse_charpoly]
  have hcharpolyRev : M.charpolyRev = det (1 + (X : R[X]) • (-M).map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M]; rw [smul_neg]
  rw [hcharpolyRev]; rw [coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [submatrix_neg, Pi.neg_apply, det_neg, Fintype.card_coe, mul_sum]
  exact Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_powersetCard.mp hs).2]

end reverse

end Matrix
