/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.RowCol
/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.permanent`, and some of its properties.

## Main definitions

* `Matrix.permanent`: the permanent of a square matrix, as a sum over permutations

-/

@[expose] public section

open Equiv Fintype Finset

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/--
Definition of `permanent` / `permanent` 的定义

English:
definition permanent
  signature: (M : Matrix n n R)
  body: ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]

中文:
定义 permanent
  签名: (M : 矩阵 n n R)
  定义体: ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]
-/
def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]
/--
theorem `permanent_diagonal` / 定理 `permanent_diagonal`

English:
theorem permanent_diagonal
  given: {d : n -> R}
  statement: permanent (diagonal d) = ∏ i, d i
  proof: by
  refine (sum_eq_single 1 (fun σ _ hσ => ?_) (fun h => (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]

中文:
定理 permanent_diagonal
  条件: {d : n -> R}
  结论: permanent (diagonal d) = ∏ i, d i
  证明: by
  refine (sum_eq_single 1 (fun σ _ hσ => ?_) (fun h => (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]

Depends on / 依赖: Equiv.ext, Finset, Finset.prod_eq_zero, Perm.one_apply, diagonal_apply_eq, if_neg, mem_univ, not_forall, not_forall.mp, one_apply, prod_eq_zero, sum_eq_single
-/
theorem permanent_diagonal {d : n -> R} : permanent (diagonal d) = ∏ i, d i := by
  refine (sum_eq_single 1 (fun σ _ hσ => ?_) (fun h => (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]
/--
theorem `permanent_zero` / 定理 `permanent_zero`

English:
theorem permanent_zero
  given: [Nonempty n]
  statement: permanent (0 : Matrix n n R) = 0
  proof: by simp [permanent]

@[simp]

中文:
定理 permanent_zero
  条件: [非空 n]
  结论: permanent (0 : 矩阵 n n R) = 0
  证明: by simp [permanent]

@[simp]

Depends on / 依赖: permanent
-/
theorem permanent_zero [Nonempty n] : permanent (0 : Matrix n n R) = 0 := by simp [permanent]

@[simp]
/--
theorem `permanent_one` / 定理 `permanent_one`

English:
theorem permanent_one
  statement: permanent (1 : Matrix n n R) = 1
  proof: by
  rw [← diagonal_one]; simp [-diagonal_one]

中文:
定理 permanent_one
  结论: permanent (1 : 矩阵 n n R) = 1
  证明: by
  rw [← diagonal_one]; simp [-diagonal_one]

Depends on / 依赖: Countable, CountablyGenerated, MeasurableSpace, diagonal_one
-/
theorem permanent_one : permanent (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one]; simp [-diagonal_one]

/--
theorem `permanent_isEmpty` / 定理 `permanent_isEmpty`

English:
theorem permanent_isEmpty
  given: [IsEmpty n] {A : Matrix n n R}
  statement: permanent A = 1
  proof: by simp [permanent]

中文:
定理 permanent_isEmpty
  条件: [是空 n] {A : 矩阵 n n R}
  结论: permanent A = 1
  证明: by simp [permanent]

Depends on / 依赖: permanent
-/
theorem permanent_isEmpty [IsEmpty n] {A : Matrix n n R} : permanent A = 1 := by simp [permanent]

/--
theorem `permanent_eq_one_of_card_eq_zero` / 定理 `permanent_eq_one_of_card_eq_zero`

English:
theorem permanent_eq_one_of_card_eq_zero
  given: {A : Matrix n n R} (h : card n = 0)
  statement: permanent A = 1
  proof: haveI : IsEmpty n := card_eq_zero_iff.mp h
  permanent_isEmpty

中文:
定理 permanent_eq_one_of_card_eq_zero
  条件: {A : 矩阵 n n R} (h : card n = 0)
  结论: permanent A = 1
  证明: haveI : IsEmpty n := card_eq_zero_iff.mp h
  permanent_isEmpty

Depends on / 依赖: IsEmpty, card_eq_zero_iff, card_eq_zero_iff.mp, permanent_isEmpty
-/
theorem permanent_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : permanent A = 1 :=
  haveI : IsEmpty n := card_eq_zero_iff.mp h
  permanent_isEmpty

/-- If `n` has only one element, the permanent of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
/--
theorem `permanent_unique` / 定理 `permanent_unique`

English:
theorem permanent_unique
  given: {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R)
  proof: by simp [permanent, univ_unique]

中文:
定理 permanent_unique
  条件: {n : 类型} [唯一 n] [DecidableEq n] [有限类型 n] (A : 矩阵 n n R)
  证明: by simp [permanent, univ_unique]

Depends on / 依赖: permanent, univ_unique
-/
theorem permanent_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    permanent A = A default default := by simp [permanent, univ_unique]

/--
theorem `permanent_eq_elem_of_subsingleton` / 定理 `permanent_eq_elem_of_subsingleton`

English:
theorem permanent_eq_elem_of_subsingleton
  given: [Subsingleton n] (A : Matrix n n R) (k : n)
  proof: by
  have := uniqueOfSubsingleton k
  convert! permanent_unique A

中文:
定理 permanent_eq_elem_of_subsingleton
  条件: [子单例 n] (A : 矩阵 n n R) (k : n)
  证明: by
  have := uniqueOfSubsingleton k
  convert! permanent_unique A

Depends on / 依赖: convert, permanent_unique, uniqueOfSubsingleton
-/
theorem permanent_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    permanent A = A k k := by
  have := uniqueOfSubsingleton k
  convert! permanent_unique A

/--
theorem `permanent_eq_elem_of_card_eq_one` / 定理 `permanent_eq_elem_of_card_eq_one`

English:
theorem permanent_eq_elem_of_card_eq_one
  given: {A : Matrix n n R} (h : card n = 1) (k : n)
  proof: haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  permanent_eq_elem_of_subsingleton _ _

中文:
定理 permanent_eq_elem_of_card_eq_one
  条件: {A : 矩阵 n n R} (h : card n = 1) (k : n)
  证明: haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  permanent_eq_elem_of_subsingleton _ _

Depends on / 依赖: Subsingleton, card_le_one_iff_subsingleton, card_le_one_iff_subsingleton.mp, h.le, permanent_eq_elem_of_subsingleton
-/
theorem permanent_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : n) :
    permanent A = A k k :=
  haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  permanent_eq_elem_of_subsingleton _ _

/-- Transposing a matrix preserves the permanent. -/
@[simp]
/--
theorem `permanent_transpose` / 定理 `permanent_transpose`

English:
theorem permanent_transpose
  given: (M : Matrix n n R)
  statement: Mᵀ.permanent = M.permanent
  proof: by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

中文:
定理 permanent_transpose
  条件: (M : 矩阵 n n R)
  结论: Mᵀ.permanent = M.permanent
  证明: by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

Depends on / 依赖: Fintype, Fintype.prod_equiv, bijective, inv_involutive, inv_involutive.bijective, prod_equiv, sum_bijective
-/
theorem permanent_transpose (M : Matrix n n R) : Mᵀ.permanent = M.permanent := by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

/--
theorem `permanent_permute_cols` / 定理 `permanent_permute_cols`

English:
theorem permanent_permute_cols
  given: (σ : Perm n) (M : Matrix n n R)
  proof: (Group.mulLeft_bijective σ).sum_comp fun τ => ∏ i : n, M (τ i) i

中文:
定理 permanent_permute_cols
  条件: (σ : 置换 n) (M : 矩阵 n n R)
  证明: (Group.mulLeft_bijective σ).sum_comp fun τ => ∏ i : n, M (τ i) i

Depends on / 依赖: Group.mulLeft_bijective, mulLeft_bijective, sum_comp
-/
theorem permanent_permute_cols (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).permanent = M.permanent :=
  (Group.mulLeft_bijective σ).sum_comp fun τ => ∏ i : n, M (τ i) i

/--
theorem `permanent_permute_rows` / 定理 `permanent_permute_rows`

English:
theorem permanent_permute_rows
  given: (σ : Perm n) (M : Matrix n n R)
  proof: by
  rw [← permanent_transpose]; rw [transpose_submatrix]; rw [permanent_permute_cols]; rw [permanent_transpose]

@[simp]

中文:
定理 permanent_permute_rows
  条件: (σ : 置换 n) (M : 矩阵 n n R)
  证明: by
  rw [← permanent_transpose]; rw [transpose_submatrix]; rw [permanent_permute_cols]; rw [permanent_transpose]

@[simp]

Depends on / 依赖: permanent_permute_cols, permanent_transpose, transpose_submatrix
-/
theorem permanent_permute_rows (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).permanent = M.permanent := by
  rw [← permanent_transpose]; rw [transpose_submatrix]; rw [permanent_permute_cols]; rw [permanent_transpose]

@[simp]
/--
theorem `permanent_smul` / 定理 `permanent_smul`

English:
theorem permanent_smul
  given: (M : Matrix n n R) (c : R)
  proof: by
  simp only [permanent, smul_apply, smul_eq_mul, Finset.mul_sum]
  congr
  ext
  rw [mul_comm]
  conv in ∏ _, c * _ => simp [mul_comm c];
  exact prod_mul_pow_card.symm

@[simp]

中文:
定理 permanent_smul
  条件: (M : 矩阵 n n R) (c : R)
  证明: by
  simp only [permanent, smul_apply, smul_eq_mul, Finset.mul_sum]
  congr
  ext
  rw [mul_comm]
  conv in ∏ _, c * _ => simp [mul_comm c];
  exact prod_mul_pow_card.symm

@[simp]

Depends on / 依赖: Finset, Finset.mul_sum, mul_comm, mul_sum, permanent, prod_mul_pow_card, prod_mul_pow_card.symm, smul_apply, smul_eq_mul
-/
theorem permanent_smul (M : Matrix n n R) (c : R) :
    permanent (c • M) = c ^ Fintype.card n * permanent M := by
  simp only [permanent, smul_apply, smul_eq_mul, Finset.mul_sum]
  congr
  ext
  rw [mul_comm]
  conv in ∏ _, c * _ => simp [mul_comm c];
  exact prod_mul_pow_card.symm

@[simp]
/--
theorem `permanent_updateCol_smul` / 定理 `permanent_updateCol_smul`

English:
theorem permanent_updateCol_smul
  given: (M : Matrix n n R) (j : n) (c : R) (u : n -> R)
  proof: by
  simp only [permanent, ← mul_prod_erase _ _ (mem_univ j), updateCol_self, Pi.smul_apply,
    smul_eq_mul, mul_sum, ← mul_assoc]
  congr 1 with p
  rw [Finset.prod_congr rfl (fun i hi => ?_)]
  simp only [ne_eq, ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

@[simp]

中文:
定理 permanent_updateCol_smul
  条件: (M : 矩阵 n n R) (j : n) (c : R) (u : n -> R)
  证明: by
  simp only [permanent, ← mul_prod_erase _ _ (mem_univ j), updateCol_self, Pi.smul_apply,
    smul_eq_mul, mul_sum, ← mul_assoc]
  congr 1 with p
  rw [Finset.prod_congr rfl (fun i hi => ?_)]
  simp only [ne_eq, ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

@[simp]

Depends on / 依赖: Finset, Finset.prod_congr, Pi.smul_apply, mem_univ, mul_assoc, mul_prod_erase, mul_sum, ne_eq, ne_of_mem_erase, not_false_eq_true, permanent, prod_congr, smul_apply, smul_eq_mul, updateCol_ne, updateCol_self
-/
theorem permanent_updateCol_smul (M : Matrix n n R) (j : n) (c : R) (u : n -> R) :
    permanent (updateCol M j <| c • u) = c * permanent (updateCol M j u) := by
  simp only [permanent, ← mul_prod_erase _ _ (mem_univ j), updateCol_self, Pi.smul_apply,
    smul_eq_mul, mul_sum, ← mul_assoc]
  congr 1 with p
  rw [Finset.prod_congr rfl (fun i hi => ?_)]
  simp only [ne_eq, ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

@[simp]
/--
theorem `permanent_updateRow_smul` / 定理 `permanent_updateRow_smul`

English:
theorem permanent_updateRow_smul
  given: (M : Matrix n n R) (j : n) (c : R) (u : n -> R)
  proof: by
  rw [← permanent_transpose]; rw [← updateCol_transpose]; rw [permanent_updateCol_smul]; rw [updateCol_transpose]; rw [permanent_transpose]

中文:
定理 permanent_updateRow_smul
  条件: (M : 矩阵 n n R) (j : n) (c : R) (u : n -> R)
  证明: by
  rw [← permanent_transpose]; rw [← updateCol_transpose]; rw [permanent_updateCol_smul]; rw [updateCol_transpose]; rw [permanent_transpose]

Depends on / 依赖: permanent_transpose, permanent_updateCol_smul, updateCol_transpose
-/
theorem permanent_updateRow_smul (M : Matrix n n R) (j : n) (c : R) (u : n -> R) :
    permanent (updateRow M j <| c • u) = c * permanent (updateRow M j u) := by
  rw [← permanent_transpose]; rw [← updateCol_transpose]; rw [permanent_updateCol_smul]; rw [updateCol_transpose]; rw [permanent_transpose]

end Matrix
