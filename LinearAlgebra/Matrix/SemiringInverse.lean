/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.Sign

import Mathlib.Algebra.Module.End
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Nonsingular inverses over semirings

This file proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/

@[expose] public section

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : Intˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

/--
Definition of `detp` / `detp` 的定义

English:
definition detp
  signature: : R
  body: ∑ σ in ofSign s, ∏ k, A k (σ k)

中文:
定义 detp
  签名: : R
  定义体: ∑ σ in ofSign s, ∏ k, A k (σ k)

Depends on / 依赖: ofSign
-/
def detp : R := ∑ σ in ofSign s, ∏ k, A k (σ k)

/--
lemma `detp_transpose` / 引理 `detp_transpose`

English:
lemma detp_transpose
  statement: A.transpose.detp s = A.detp s
  proof: sum_equiv (.inv _) (by simp) fun σ _ => prod_equiv σ (by simp) (by simp)

中文:
引理 detp_transpose
  结论: A.transpose.detp s = A.detp s
  证明: sum_equiv (.inv _) (by simp) fun σ _ => prod_equiv σ (by simp) (by simp)
-/
@[simp] lemma detp_transpose : A.transpose.detp s = A.detp s :=
  sum_equiv (.inv _) (by simp) fun σ _ => prod_equiv σ (by simp) (by simp)

/--
lemma `detp_zero` / 引理 `detp_zero`

English:
lemma detp_zero
  given: [Nonempty n]
  statement: (0 : Matrix n n R).detp s = 0
  proof: by simp [detp]

@[simp]

中文:
引理 detp_zero
  条件: [非空 n]
  结论: (0 : 矩阵 n n R).detp s = 0
  证明: by simp [detp]

@[simp]
-/
@[simp] lemma detp_zero [Nonempty n] : (0 : Matrix n n R).detp s = 0 := by simp [detp]

@[simp]
/--
lemma `detp_one_diagonal` / 引理 `detp_one_diagonal`

English:
lemma detp_one_diagonal
  given: (d : n -> R)
  statement: detp 1 (diagonal d) = ∏ i, d i
  proof: by
  rw [detp]; rw [sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]

中文:
引理 detp_one_diagonal
  条件: (d : n -> R)
  结论: detp 1 (diagonal d) = ∏ i, d i
  证明: by
  rw [detp]; rw [sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]

Depends on / 依赖: Perm.ext_iff.mpr, diagonal_apply_ne, ext_iff, mem_univ, not_forall, not_forall.mp, ofSign, prod_eq_zero, sum_eq_single_of_mem
-/
lemma detp_one_diagonal (d : n -> R) : detp 1 (diagonal d) = ∏ i, d i := by
  rw [detp]; rw [sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
/--
lemma `detp_one_one` / 引理 `detp_one_one`

English:
lemma detp_one_one
  statement: detp 1 (1 : Matrix n n R) = 1
  proof: by
  rw [← diagonal_one]; rw [detp_one_diagonal]; rw [prod_const_one]

@[simp]

中文:
引理 detp_one_one
  结论: detp 1 (1 : 矩阵 n n R) = 1
  证明: by
  rw [← diagonal_one]; rw [detp_one_diagonal]; rw [prod_const_one]

@[simp]

Depends on / 依赖: detp_one_diagonal, diagonal_one, prod_const_one
-/
lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one]; rw [detp_one_diagonal]; rw [prod_const_one]

@[simp]
/--
lemma `detp_neg_one_diagonal` / 引理 `detp_neg_one_diagonal`

English:
lemma detp_neg_one_diagonal
  given: (d : n -> R)
  statement: detp (-1) (diagonal d) = 0
  proof: by
  rw [detp]; rw [sum_eq_zero]
  intro σ hσ
  have hσ1 : σ != 1 := by
    contrapose hσ
    rw [hσ]; rw [mem_ofSign]; rw [sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]

中文:
引理 detp_neg_one_diagonal
  条件: (d : n -> R)
  结论: detp (-1) (diagonal d) = 0
  证明: by
  rw [detp]; rw [sum_eq_zero]
  intro σ hσ
  have hσ1 : σ != 1 := by
    contrapose hσ
    rw [hσ]; rw [mem_ofSign]; rw [sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]

Depends on / 依赖: Perm.ext_iff.mpr, contrapose, diagonal_apply_ne, ext_iff, mem_ofSign, mem_univ, not_forall, not_forall.mp, prod_eq_zero, sign_one, sum_eq_zero
-/
lemma detp_neg_one_diagonal (d : n -> R) : detp (-1) (diagonal d) = 0 := by
  rw [detp]; rw [sum_eq_zero]
  intro σ hσ
  have hσ1 : σ != 1 := by
    contrapose hσ
    rw [hσ]; rw [mem_ofSign]; rw [sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
/--
lemma `detp_neg_one_one` / 引理 `detp_neg_one_one`

English:
lemma detp_neg_one_one
  statement: detp (-1) (1 : Matrix n n R) = 0
  proof: by
  rw [← diagonal_one]; rw [detp_neg_one_diagonal]

中文:
引理 detp_neg_one_one
  结论: detp (-1) (1 : 矩阵 n n R) = 0
  证明: by
  rw [← diagonal_one]; rw [detp_neg_one_diagonal]

Depends on / 依赖: detp_neg_one_diagonal, diagonal_one
-/
lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [← diagonal_one]; rw [detp_neg_one_diagonal]

/--
lemma `detp_one_of_isEmpty` / 引理 `detp_one_of_isEmpty`

English:
lemma detp_one_of_isEmpty
  given: [IsEmpty n]
  statement: A.detp 1 = 1
  proof: by
  rw [detp]; rw [sum_unique_nonempty _ _ ⟨1]; rw [_⟩] <;> simp

中文:
引理 detp_one_of_isEmpty
  条件: [是空 n]
  结论: A.detp 1 = 1
  证明: by
  rw [detp]; rw [sum_unique_nonempty _ _ ⟨1]; rw [_⟩] <;> simp
-/
@[simp] lemma detp_one_of_isEmpty [IsEmpty n] : A.detp 1 = 1 := by
  rw [detp]; rw [sum_unique_nonempty _ _ ⟨1]; rw [_⟩] <;> simp

/--
lemma `detp_neg_one_of_isEmpty` / 引理 `detp_neg_one_of_isEmpty`

English:
lemma detp_neg_one_of_isEmpty
  given: [IsEmpty n]
  statement: A.detp (-1) = 0
  proof: by
  rw [detp]; rw [ofSign]; rw [univ_unique]
  convert sum_empty
  simp +decide

中文:
引理 detp_neg_one_of_isEmpty
  条件: [是空 n]
  结论: A.detp (-1) = 0
  证明: by
  rw [detp]; rw [ofSign]; rw [univ_unique]
  convert sum_empty
  simp +decide
-/
@[simp] lemma detp_neg_one_of_isEmpty [IsEmpty n] : A.detp (-1) = 0 := by
  rw [detp]; rw [ofSign]; rw [univ_unique]
  convert sum_empty
  simp +decide

/--
lemma `detp_submatrix_equiv_equiv` / 引理 `detp_submatrix_equiv_equiv`

English:
lemma detp_submatrix_equiv_equiv
  given: (f g : m ≃ n)
  proof: sum_equiv (equivCongr f g) (by simp) fun _ _ => prod_equiv f (by simp) fun _ _ => by simp

中文:
引理 detp_submatrix_equiv_equiv
  条件: (f g : m ≃ n)
  证明: sum_equiv (equivCongr f g) (by simp) fun _ _ => prod_equiv f (by simp) fun _ _ => by simp
-/
@[simp] lemma detp_submatrix_equiv_equiv (f g : m ≃ n) :
    (A.submatrix f g).detp s = A.detp (s * sign (f.symm.trans g)) :=
  sum_equiv (equivCongr f g) (by simp) fun _ _ => prod_equiv f (by simp) fun _ _ => by simp

/--
lemma `detp_submatrix_equiv_self` / 引理 `detp_submatrix_equiv_self`

English:
lemma detp_submatrix_equiv_self
  given: (e : m ≃ n)
  statement: (A.submatrix e e).detp s = A.detp s
  proof: by
  simp

中文:
引理 detp_submatrix_equiv_self
  条件: (e : m ≃ n)
  结论: (A.submatrix e e).detp s = A.detp s
  证明: by
  simp
-/
lemma detp_submatrix_equiv_self (e : m ≃ n) : (A.submatrix e e).detp s = A.detp s := by
  simp

/--
lemma `detp_smul` / 引理 `detp_smul`

English:
lemma detp_smul
  given: (c : R)
  statement: (c • A).detp s = c ^ Fintype.card n * A.detp s
  proof: by
  simp [detp, Finset.mul_sum, Finset.prod_mul_distrib]

中文:
引理 detp_smul
  条件: (c : R)
  结论: (c • A).detp s = c ^ 有限类型.card n * A.detp s
  证明: by
  simp [detp, Finset.mul_sum, Finset.prod_mul_distrib]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.prod_mul_distrib, mul_sum, prod_mul_distrib
-/
lemma detp_smul (c : R) : (c • A).detp s = c ^ Fintype.card n * A.detp s := by
  simp [detp, Finset.mul_sum, Finset.prod_mul_distrib]

/--
lemma `detp_map` / 引理 `detp_map`

English:
lemma detp_map
  given: {S : Type*} [CommSemiring S] (f : R ->+* S)
  proof: by simp [detp]

中文:
引理 detp_map
  条件: {S : 类型} [交换半环 S] (f : R ->+* S)
  证明: by simp [detp]
-/
lemma detp_map {S : Type*} [CommSemiring S] (f : R ->+* S) :
    (A.map f).detp s = f (A.detp s) := by simp [detp]

/--
Definition of `IsDetpBalanced` / `IsDetpBalanced` 的定义

English:
definition IsDetpBalanced
  signature: (a b : R)
  body: a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1)

中文:
定义 IsDetpBalanced
  签名: (a b : R)
  定义体: a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1)

Depends on / 依赖: A.detp
-/
def IsDetpBalanced (a b : R) : Prop :=
  a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1)

/--
lemma `IsDetpBalanced.refl` / 引理 `IsDetpBalanced.refl`

English:
lemma IsDetpBalanced.refl
  given: (a : R)
  statement: A.IsDetpBalanced a a
  proof: rfl

中文:
引理 IsDetpBalanced.refl
  条件: (a : R)
  结论: A.IsDetpBalanced a a
  证明: rfl
-/
lemma IsDetpBalanced.refl (a : R) : A.IsDetpBalanced a a := rfl

variable {A} {a b c : R}

/--
lemma `IsDetpBalanced.of_eq` / 引理 `IsDetpBalanced.of_eq`

English:
lemma IsDetpBalanced.of_eq
  given: (eq : A.detp 1 = A.detp (-1))
  statement: A.IsDetpBalanced a b
  proof: by
  rw [IsDetpBalanced]; rw [eq]; rw [add_comm]

中文:
引理 IsDetpBalanced.of_eq
  条件: (eq : A.detp 1 = A.detp (-1))
  结论: A.IsDetpBalanced a b
  证明: by
  rw [IsDetpBalanced]; rw [eq]; rw [add_comm]

Depends on / 依赖: IsDetpBalanced, add_comm
-/
lemma IsDetpBalanced.of_eq (eq : A.detp 1 = A.detp (-1)) : A.IsDetpBalanced a b := by
  rw [IsDetpBalanced]; rw [eq]; rw [add_comm]

/--
lemma `IsDetpBalanced.symm` / 引理 `IsDetpBalanced.symm`

English:
lemma IsDetpBalanced.symm
  statement: A.IsDetpBalanced a b -> A.IsDetpBalanced b a
  proof: Eq.symm

中文:
引理 IsDetpBalanced.symm
  结论: A.IsDetpBalanced a b -> A.IsDetpBalanced b a
  证明: Eq.symm

Depends on / 依赖: Eq.symm
-/
lemma IsDetpBalanced.symm : A.IsDetpBalanced a b -> A.IsDetpBalanced b a := Eq.symm

/--
lemma `IsDetpBalanced_comm` / 引理 `IsDetpBalanced_comm`

English:
lemma IsDetpBalanced_comm
  statement: A.IsDetpBalanced a b ↔ A.IsDetpBalanced b a
  proof: Eq.comm

中文:
引理 IsDetpBalanced_comm
  结论: A.IsDetpBalanced a b ↔ A.IsDetpBalanced b a
  证明: Eq.comm

Depends on / 依赖: Eq.comm
-/
lemma IsDetpBalanced_comm : A.IsDetpBalanced a b ↔ A.IsDetpBalanced b a := Eq.comm

/--
lemma `IsDetpBalanced.trans` / 引理 `IsDetpBalanced.trans`

English:
lemma IsDetpBalanced.trans
  statement: [IsCancelAdd R]
  proof: by
  rw [IsDetpBalanced] at *
  apply add_left_cancel (a := b * detp 1 A + b * detp (-1) A)
  convert congr($hab + $hbc) using 1 <;> abel

中文:
引理 IsDetpBalanced.trans
  结论: [是消去加法 R]
  证明: by
  rw [IsDetpBalanced] at *
  apply add_left_cancel (a := b * detp 1 A + b * detp (-1) A)
  convert congr($hab + $hbc) using 1 <;> abel

Depends on / 依赖: IsDetpBalanced, add_left_cancel, convert
-/
lemma IsDetpBalanced.trans [IsCancelAdd R]
    (hab : A.IsDetpBalanced a b) (hbc : A.IsDetpBalanced b c) :
    A.IsDetpBalanced a c := by
  rw [IsDetpBalanced] at *
  apply add_left_cancel (a := b * detp 1 A + b * detp (-1) A)
  convert congr($hab + $hbc) using 1 <;> abel

/--
lemma `IsDetpBalanced.mul_add_mul_eq` / 引理 `IsDetpBalanced.mul_add_mul_eq`

English:
lemma IsDetpBalanced.mul_add_mul_eq
  given: (h : A.IsDetpBalanced a b) (s t : Intˣ)
  proof: by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]

中文:
引理 IsDetpBalanced.mul_add_mul_eq
  条件: (h : A.IsDetpBalanced a b) (s t : 整数ˣ)
  证明: by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]

Depends on / 依赖: Int.units_eq_one_or, add_comm, units_eq_one_or
-/
lemma IsDetpBalanced.mul_add_mul_eq (h : A.IsDetpBalanced a b) (s t : Intˣ) :
    a * A.detp s + b * A.detp t = b * A.detp s + a * A.detp t := by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]

/--
lemma `isDetpBalanced_transpose_iff` / 引理 `isDetpBalanced_transpose_iff`

English:
lemma isDetpBalanced_transpose_iff
  statement: Aᵀ.IsDetpBalanced a b ↔ A.IsDetpBalanced a b
  proof: by
  simp [IsDetpBalanced]

alias ⟨IsDetpBalanced.of_transpose, IsDetpBalanced.transpose⟩ := isDetpBalanced_transpose_iff

中文:
引理 isDetpBalanced_transpose_iff
  结论: Aᵀ.IsDetpBalanced a b ↔ A.IsDetpBalanced a b
  证明: by
  simp [IsDetpBalanced]

alias ⟨IsDetpBalanced.of_transpose, IsDetpBalanced.transpose⟩ := isDetpBalanced_transpose_iff
-/
@[simp] lemma isDetpBalanced_transpose_iff : Aᵀ.IsDetpBalanced a b ↔ A.IsDetpBalanced a b := by
  simp [IsDetpBalanced]

alias ⟨IsDetpBalanced.of_transpose, IsDetpBalanced.transpose⟩ := isDetpBalanced_transpose_iff

/--
lemma `IsDetpBalanced.submatrix_equiv` / 引理 `IsDetpBalanced.submatrix_equiv`

English:
lemma IsDetpBalanced.submatrix_equiv
  given: (e₁ e₂ : m ≃ n) (h : A.IsDetpBalanced a b)
  proof: by
  simp_rw [IsDetpBalanced, detp_submatrix_equiv_equiv]
  apply h.mul_add_mul_eq

中文:
引理 IsDetpBalanced.submatrix_equiv
  条件: (e₁ e₂ : m ≃ n) (h : A.IsDetpBalanced a b)
  证明: by
  simp_rw [IsDetpBalanced, detp_submatrix_equiv_equiv]
  apply h.mul_add_mul_eq

Depends on / 依赖: IsDetpBalanced, detp_submatrix_equiv_equiv, h.mul_add_mul_eq, mul_add_mul_eq, simp_rw
-/
lemma IsDetpBalanced.submatrix_equiv (e₁ e₂ : m ≃ n) (h : A.IsDetpBalanced a b) :
    (A.submatrix e₁ e₂).IsDetpBalanced a b := by
  simp_rw [IsDetpBalanced, detp_submatrix_equiv_equiv]
  apply h.mul_add_mul_eq

/--
lemma `isDetpBalanced_submatrix_equiv_iff` / 引理 `isDetpBalanced_submatrix_equiv_iff`

English:
lemma isDetpBalanced_submatrix_equiv_iff
  given: {e₁ e₂ : m ≃ n}
  proof: by simpa using h.submatrix_equiv e₁.symm e₂.symm
  mpr := (·.submatrix_equiv ..)

中文:
引理 isDetpBalanced_submatrix_equiv_iff
  条件: {e₁ e₂ : m ≃ n}
  证明: by simpa using h.submatrix_equiv e₁.symm e₂.symm
  mpr := (·.submatrix_equiv ..)
-/
@[simp] lemma isDetpBalanced_submatrix_equiv_iff {e₁ e₂ : m ≃ n} :
    (A.submatrix e₁ e₂).IsDetpBalanced a b ↔ A.IsDetpBalanced a b where
  mp h := by simpa using h.submatrix_equiv e₁.symm e₂.symm
  mpr := (·.submatrix_equiv ..)

/--
lemma `IsDetpBalanced.smul` / 引理 `IsDetpBalanced.smul`

English:
lemma IsDetpBalanced.smul
  given: (h : A.IsDetpBalanced a b) (c : R)
  proof: by
  simp_rw [IsDetpBalanced, detp_smul, ← mul_assoc, mul_comm _ (c ^ _), mul_assoc,
    ← mul_add, h.mul_add_mul_eq]

中文:
引理 IsDetpBalanced.smul
  条件: (h : A.IsDetpBalanced a b) (c : R)
  证明: by
  simp_rw [IsDetpBalanced, detp_smul, ← mul_assoc, mul_comm _ (c ^ _), mul_assoc,
    ← mul_add, h.mul_add_mul_eq]

Depends on / 依赖: IsDetpBalanced, detp_smul, h.mul_add_mul_eq, mul_add, mul_add_mul_eq, mul_assoc, mul_comm, simp_rw
-/
lemma IsDetpBalanced.smul (h : A.IsDetpBalanced a b) (c : R) :
    (c • A).IsDetpBalanced a b := by
  simp_rw [IsDetpBalanced, detp_smul, ← mul_assoc, mul_comm _ (c ^ _), mul_assoc,
    ← mul_add, h.mul_add_mul_eq]

variable (A) in
/--
Definition of `Nonsingular` / `Nonsingular` 的定义

English:
definition Nonsingular
  signature: : Prop
  body: forall a b : R, A.IsDetpBalanced a b -> a = b

中文:
定义 非奇异
  签名: : 命题
  定义体: forall a b : R, A.IsDetpBalanced a b -> a = b

Depends on / 依赖: A.IsDetpBalanced, IsDetpBalanced
-/
def Nonsingular : Prop := forall a b : R, A.IsDetpBalanced a b -> a = b

/--
lemma `Nonsingular.eq_of_IsDetpBalanced` / 引理 `Nonsingular.eq_of_IsDetpBalanced`

English:
lemma Nonsingular.eq_of_IsDetpBalanced
  given: (hA : A.Nonsingular) (hAd : A.IsDetpBalanced a b)
  proof: hA a b hAd

中文:
引理 非奇异.eq_of_IsDetpBalanced
  条件: (hA : A.非奇异) (hAd : A.IsDetpBalanced a b)
  证明: hA a b hAd
-/
lemma Nonsingular.eq_of_IsDetpBalanced (hA : A.Nonsingular) (hAd : A.IsDetpBalanced a b) :
    a = b := hA a b hAd

/--
lemma `IsDetpBalanced.eq_of_nonsingular` / 引理 `IsDetpBalanced.eq_of_nonsingular`

English:
lemma IsDetpBalanced.eq_of_nonsingular
  given: (hA : A.IsDetpBalanced a b) (hAn : A.Nonsingular)
  proof: hAn.eq_of_IsDetpBalanced hA

中文:
引理 IsDetpBalanced.eq_of_nonsingular
  条件: (hA : A.IsDetpBalanced a b) (hAn : A.非奇异)
  证明: hAn.eq_of_IsDetpBalanced hA

Depends on / 依赖: eq_of_IsDetpBalanced, hAn.eq_of_IsDetpBalanced
-/
lemma IsDetpBalanced.eq_of_nonsingular (hA : A.IsDetpBalanced a b) (hAn : A.Nonsingular) :
    a = b := hAn.eq_of_IsDetpBalanced hA

/--
lemma `nonsingular_one` / 引理 `nonsingular_one`

English:
lemma nonsingular_one
  statement: (1 : Matrix n n R).Nonsingular
  proof: fun a b h => by simpa [IsDetpBalanced] using h

中文:
引理 nonsingular_one
  结论: (1 : 矩阵 n n R).非奇异
  证明: fun a b h => by simpa [IsDetpBalanced] using h
-/
@[simp] lemma nonsingular_one : (1 : Matrix n n R).Nonsingular :=
  fun a b h => by simpa [IsDetpBalanced] using h

variable (A) in
/--
lemma `Nonsingular.of_isEmpty` / 引理 `Nonsingular.of_isEmpty`

English:
lemma Nonsingular.of_isEmpty
  given: [IsEmpty n]
  statement: A.Nonsingular
  proof: by
  simp [Nonsingular, IsDetpBalanced]

中文:
引理 非奇异.of_isEmpty
  条件: [是空 n]
  结论: A.非奇异
  证明: by
  simp [Nonsingular, IsDetpBalanced]
-/
@[simp] lemma Nonsingular.of_isEmpty [IsEmpty n] : A.Nonsingular := by
  simp [Nonsingular, IsDetpBalanced]

/--
lemma `nonsingular_transpose_iff` / 引理 `nonsingular_transpose_iff`

English:
lemma nonsingular_transpose_iff
  statement: Aᵀ.Nonsingular ↔ A.Nonsingular
  proof: by simp [Nonsingular]

alias ⟨Nonsingular.of_transpose, Nonsingular.transpose⟩ := nonsingular_transpose_iff

中文:
引理 nonsingular_transpose_iff
  结论: Aᵀ.非奇异 ↔ A.非奇异
  证明: by simp [Nonsingular]

alias ⟨Nonsingular.of_transpose, Nonsingular.transpose⟩ := nonsingular_transpose_iff
-/
@[simp] lemma nonsingular_transpose_iff : Aᵀ.Nonsingular ↔ A.Nonsingular := by simp [Nonsingular]

alias ⟨Nonsingular.of_transpose, Nonsingular.transpose⟩ := nonsingular_transpose_iff

/--
lemma `nonsingular_submatrix_equiv_iff` / 引理 `nonsingular_submatrix_equiv_iff`

English:
lemma nonsingular_submatrix_equiv_iff
  given: {e₁ e₂ : m ≃ n}
  proof: by simp [Nonsingular]

alias ⟨_, Nonsingular.submatrix_equiv⟩ := nonsingular_submatrix_equiv_iff

中文:
引理 nonsingular_submatrix_equiv_iff
  条件: {e₁ e₂ : m ≃ n}
  证明: by simp [Nonsingular]

alias ⟨_, Nonsingular.submatrix_equiv⟩ := nonsingular_submatrix_equiv_iff
-/
@[simp] lemma nonsingular_submatrix_equiv_iff {e₁ e₂ : m ≃ n} :
    (A.submatrix e₁ e₂).Nonsingular ↔ A.Nonsingular := by simp [Nonsingular]

alias ⟨_, Nonsingular.submatrix_equiv⟩ := nonsingular_submatrix_equiv_iff

/--
lemma `detp_eq_of_row_eq` / 引理 `detp_eq_of_row_eq`

English:
lemma detp_eq_of_row_eq
  statement: {p q : n} (hpq : p != q) (hrow : A.row p = A.row q)
  proof: by
  have : A.detp 1 = A.detp (-1) := sum_equiv (.mulRight <| swap p q) (by simp [hpq])
    fun _ _ => prod_equiv (swap p q) (by simp) (by aesop (add simp row))
  obtain rfl | rfl := Int.units_eq_one_or s <;>
  obtain rfl | rfl := Int.units_eq_one_or t <;>
  first | rfl | rw [this]

中文:
引理 detp_eq_of_row_eq
  结论: {p q : n} (hpq : p != q) (hrow : A.row p = A.row q)
  证明: by
  have : A.detp 1 = A.detp (-1) := sum_equiv (.mulRight <| swap p q) (by simp [hpq])
    fun _ _ => prod_equiv (swap p q) (by simp) (by aesop (add simp row))
  obtain rfl | rfl := Int.units_eq_one_or s <;>
  obtain rfl | rfl := Int.units_eq_one_or t <;>
  first | rfl | rw [this]

Depends on / 依赖: A.detp, Int.units_eq_one_or, mulRight, prod_equiv, sum_equiv, units_eq_one_or
-/
lemma detp_eq_of_row_eq {p q : n} (hpq : p != q) (hrow : A.row p = A.row q)
    (s : Intˣ := 1) (t : Intˣ := -1) : A.detp s = A.detp t := by
  have : A.detp 1 = A.detp (-1) := sum_equiv (.mulRight <| swap p q) (by simp [hpq])
    fun _ _ => prod_equiv (swap p q) (by simp) (by aesop (add simp row))
  obtain rfl | rfl := Int.units_eq_one_or s <;>
  obtain rfl | rfl := Int.units_eq_one_or t <;>
  first | rfl | rw [this]

/--
lemma `detp_eq_of_col_eq` / 引理 `detp_eq_of_col_eq`

English:
lemma detp_eq_of_col_eq
  statement: {p q : n} (hpq : p != q) (hcol : A.col p = A.col q)
  proof: by
  simpa using detp_eq_of_row_eq (A := Aᵀ) hpq hcol s t

中文:
引理 detp_eq_of_col_eq
  结论: {p q : n} (hpq : p != q) (hcol : A.col p = A.col q)
  证明: by
  simpa using detp_eq_of_row_eq (A := Aᵀ) hpq hcol s t

Depends on / 依赖: A.detp, detp_eq_of_row_eq
-/
lemma detp_eq_of_col_eq {p q : n} (hpq : p != q) (hcol : A.col p = A.col q)
    (s : Intˣ := 1) (t : Intˣ := -1) : A.detp s = A.detp t := by
  simpa using detp_eq_of_row_eq (A := Aᵀ) hpq hcol s t

/--
lemma `detp_eq_of_row_eq_zero` / 引理 `detp_eq_of_row_eq_zero`

English:
lemma detp_eq_of_row_eq_zero
  given: {p : n} (hrow : A.row p = 0)
  statement: A.detp s = 0
  proof: sum_eq_zero fun _ _ => prod_eq_zero (mem_univ p) congr($hrow _)

中文:
引理 detp_eq_of_row_eq_zero
  条件: {p : n} (hrow : A.row p = 0)
  结论: A.detp s = 0
  证明: sum_eq_zero fun _ _ => prod_eq_zero (mem_univ p) congr($hrow _)

Depends on / 依赖: mem_univ, prod_eq_zero, sum_eq_zero
-/
lemma detp_eq_of_row_eq_zero {p : n} (hrow : A.row p = 0) : A.detp s = 0 :=
  sum_eq_zero fun _ _ => prod_eq_zero (mem_univ p) congr($hrow _)

/--
lemma `detp_eq_of_col_eq_zero` / 引理 `detp_eq_of_col_eq_zero`

English:
lemma detp_eq_of_col_eq_zero
  given: {p : n} (hcol : A.col p = 0)
  statement: A.detp s = 0
  proof: by
  simpa using detp_eq_of_row_eq_zero (A := Aᵀ) s hcol

中文:
引理 detp_eq_of_col_eq_zero
  条件: {p : n} (hcol : A.col p = 0)
  结论: A.detp s = 0
  证明: by
  simpa using detp_eq_of_row_eq_zero (A := Aᵀ) s hcol

Depends on / 依赖: detp_eq_of_row_eq_zero
-/
lemma detp_eq_of_col_eq_zero {p : n} (hcol : A.col p = 0) : A.detp s = 0 := by
  simpa using detp_eq_of_row_eq_zero (A := Aᵀ) s hcol

/--
lemma `IsDetpBalanced.submatrix_of_card_le` / 引理 `IsDetpBalanced.submatrix_of_card_le`

English:
lemma IsDetpBalanced.submatrix_of_card_le
  statement: {a b : R} (h : A.IsDetpBalanced a b)
  proof: by
  by_cases hf : f.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hf
    exact .of_eq (detp_eq_of_row_eq ne <| by ext; simp [eq])
  by_cases hg : g.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hg
    exact .of_eq (detp_eq_of_col_eq ne <| by ext; simp [eq])
let f' := Equiv.ofBijective f (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, (Fintype.card_le_of_injective f hf).antisymm le⟩
let g' := Equiv.ofBijective g (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hg, (Fintype.card_le_of_injective g hg).antisymm le⟩
  rwa [show f = f' by rfl, show g = g' by rfl, isDetpBalanced_submatrix_equiv_iff]

中文:
引理 IsDetpBalanced.submatrix_of_card_le
  结论: {a b : R} (h : A.IsDetpBalanced a b)
  证明: by
  by_cases hf : f.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hf
    exact .of_eq (detp_eq_of_row_eq ne <| by ext; simp [eq])
  by_cases hg : g.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hg
    exact .of_eq (detp_eq_of_col_eq ne <| by ext; simp [eq])
let f' := Equiv.ofBijective f (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, (Fintype.card_le_of_injective f hf).antisymm le⟩
let g' := Equiv.ofBijective g (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hg, (Fintype.card_le_of_injective g hg).antisymm le⟩
  rwa [show f = f' by rfl, show g = g' by rfl, isDetpBalanced_submatrix_equiv_iff]

Depends on / 依赖: Equiv.ofBijective, Fintype, Fintype.bijective_iff_injective_and, Fintype.bijective_iff_injective_and_card, Fintype.card_le_of_injective, Function, Function.not_injective_iff.mp, Injective, antisymm, bijective_iff_injective_and, bijective_iff_injective_and_card, card_le_of_injective, detp_eq_of_col_eq, detp_eq_of_row_eq, f.Injective, g.Injective, not_injective_iff, ofBijective, of_eq
-/
lemma IsDetpBalanced.submatrix_of_card_le {a b : R} (h : A.IsDetpBalanced a b)
    (le : Fintype.card n <= Fintype.card m) (f g : m -> n) :
    (A.submatrix f g).IsDetpBalanced a b := by
  by_cases hf : f.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hf
    exact .of_eq (detp_eq_of_row_eq ne <| by ext; simp [eq])
  by_cases hg : g.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hg
    exact .of_eq (detp_eq_of_col_eq ne <| by ext; simp [eq])
let f' := Equiv.ofBijective f (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, (Fintype.card_le_of_injective f hf).antisymm le⟩
let g' := Equiv.ofBijective g (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hg, (Fintype.card_le_of_injective g hg).antisymm le⟩
  rwa [show f = f' by rfl, show g = g' by rfl, isDetpBalanced_submatrix_equiv_iff]

variable (A)

/--
Definition of `adjp` / `adjp` 的定义

English:
definition adjp
  signature: : Matrix n n R
  body: of fun i j => ∑ σ in (ofSign s).filter (· j = i), ∏ k in {j}ᶜ, A k (σ k)

中文:
定义 adjp
  签名: : 矩阵 n n R
  定义体: of fun i j => ∑ σ in (ofSign s).filter (· j = i), ∏ k in {j}ᶜ, A k (σ k)

Depends on / 依赖: filter, ofSign
-/
def adjp : Matrix n n R :=
  of fun i j => ∑ σ in (ofSign s).filter (· j = i), ∏ k in {j}ᶜ, A k (σ k)

/--
lemma `adjp_apply` / 引理 `adjp_apply`

English:
lemma adjp_apply
  given: (i j : n)
  proof: rfl

中文:
引理 adjp_apply
  条件: (i j : n)
  证明: rfl
-/
lemma adjp_apply (i j : n) :
    adjp s A i j = ∑ σ in (ofSign s).filter (· j = i), ∏ k in {j}ᶜ, A k (σ k) :=
  rfl

/--
lemma `adjp_transpose` / 引理 `adjp_transpose`

English:
lemma adjp_transpose
  statement: A.transpose.adjp s = (A.adjp s).transpose
  proof: ext fun _ _ => sum_equiv (.inv _) (by aesop) fun σ hσ => prod_equiv σ (by aesop) (by simp)

中文:
引理 adjp_transpose
  结论: A.transpose.adjp s = (A.adjp s).transpose
  证明: ext fun _ _ => sum_equiv (.inv _) (by aesop) fun σ hσ => prod_equiv σ (by aesop) (by simp)

Depends on / 依赖: prod_equiv, sum_equiv
-/
lemma adjp_transpose : A.transpose.adjp s = (A.adjp s).transpose :=
  ext fun _ _ => sum_equiv (.inv _) (by aesop) fun σ hσ => prod_equiv σ (by aesop) (by simp)

/--
lemma `adjp_none_right` / 引理 `adjp_none_right`

English:
lemma adjp_none_right
  given: (A : Matrix (Option n) (Option n) R) (i : Option n)
  proof: by
  rw [adjp]; rw [of_apply]; rw [detp]
  convert sum_image (g := fun σ => decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    exact ⟨fun _ => ⟨σ.removeNone, by rw [← optionCongr_sign]; aesop⟩, by aesop⟩
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]

中文:
引理 adjp_none_right
  条件: (A : 矩阵 (选项类型 n) (选项类型 n) R) (i : 选项类型 n)
  证明: by
  rw [adjp]; rw [of_apply]; rw [detp]
  convert sum_image (g := fun σ => decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    exact ⟨fun _ => ⟨σ.removeNone, by rw [← optionCongr_sign]; aesop⟩, by aesop⟩
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]
-/
private lemma adjp_none_right (A : Matrix (Option n) (Option n) R) (i : Option n) :
    A.adjp s i none = (A.submatrix some <| swap none i ∘ some).detp (sign (swap none i) * s) := by
  rw [adjp]; rw [of_apply]; rw [detp]
  convert sum_image (g := fun σ => decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    exact ⟨fun _ => ⟨σ.removeNone, by rw [← optionCongr_sign]; aesop⟩, by aesop⟩
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]

/--
lemma `adjp_none_none` / 引理 `adjp_none_none`

English:
lemma adjp_none_none
  given: (A : Matrix (Option n) (Option n) R)
  proof: by
  simp [adjp_none_right]

中文:
引理 adjp_none_none
  条件: (A : 矩阵 (选项类型 n) (选项类型 n) R)
  证明: by
  simp [adjp_none_right]

Depends on / 依赖: adjp_none_right
-/
lemma adjp_none_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s none none = (A.submatrix some some).detp s := by
  simp [adjp_none_right]

/--
lemma `adjp_some_none` / 引理 `adjp_some_none`

English:
lemma adjp_some_none
  given: (A : Matrix (Option n) (Option n) R)
  proof: by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop

中文:
引理 adjp_some_none
  条件: (A : 矩阵 (选项类型 n) (选项类型 n) R)
  证明: by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop

Depends on / 依赖: adjp_none_right
-/
lemma adjp_some_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).detp (-s) := by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop

/--
lemma `adjp_none_some` / 引理 `adjp_none_some`

English:
lemma adjp_none_some
  given: (A : Matrix (Option n) (Option n) R)
  proof: by
  rw [← detp_transpose]; simp [← A.transpose.adjp_some_none, adjp_transpose]

中文:
引理 adjp_none_some
  条件: (A : 矩阵 (选项类型 n) (选项类型 n) R)
  证明: by
  rw [← detp_transpose]; simp [← A.transpose.adjp_some_none, adjp_transpose]

Depends on / 依赖: A.transpose.adjp_some_none, adjp_some_none, adjp_transpose, detp_transpose, transpose
-/
lemma adjp_none_some (A : Matrix (Option n) (Option n) R) :
    A.adjp s none (some i) = (A.submatrix (Function.update some i none) some).detp (-s) := by
  rw [← detp_transpose]; simp [← A.transpose.adjp_some_none, adjp_transpose]

/--
theorem `detp_mul` / 定理 `detp_mul`

English:
theorem detp_mul
  proof: by
  have hf {s t} {σ : Perm n} (hσ : σ in ofSign s) :
      ofSign (t * s) = (ofSign t).map (mulRightEmbedding σ) := by
    ext τ
    simp_rw [mem_map, mulRightEmbedding_apply, ← eq_mul_inv_iff_mul_eq, exists_eq_right,
      mem_ofSign, map_mul, map_inv, mul_inv_eq_iff_eq_mul, mem_ofSign.mp hσ]
  have h {s t} : detp s A * detp t B =
      ∑ σ in ofSign s, ∑ τ in ofSign (t * s), ∏ k, A k (σ k) * B (σ k) (τ k) := by
    simp_rw [detp, sum_mul_sum, prod_mul_distrib]
    refine sum_congr rfl fun σ hσ => ?_
    simp_rw [hf hσ, sum_map, mulRightEmbedding_apply, Perm.mul_apply]
    exact sum_congr rfl fun τ hτ => (congr_arg (_ * ·) (Equiv.prod_comp σ _).symm)
  let ι : Perm n ↪ (n -> n) := ⟨_, coe_fn_injective⟩
  have hι {σ x} : ι σ x = σ x := rfl
  let bij : Finset (n -> n) := (disjUnion (ofSign 1) (ofSign (-1)) ofSign_disjoint).map ι
  replace h (s) : detp s (A * B) =
      ∑ σ in bijᶜ, ∑ τ in ofSign s, ∏ i : n, A i (σ i) * B (σ i) (τ i) +
        (detp 1 A * detp s B + detp (-1) A * detp (-s) B) := by
    simp_rw [h, neg_mul_neg, mul_one, detp, mul_apply, prod_univ_sum, Fintype.piFinset_univ]
    rw [sum_comm]; rw [← sum_compl_add_sum bij]; rw [sum_map]; rw [sum_disjUnion]
    simp_rw [hι]
  rw [h]; rw [h]; rw [neg_neg]; rw [add_assoc]
  conv_rhs => rw [add_assoc]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (add_comm _ _)
  replace hσ : ¬ Function.Injective σ := by
    contrapose hσ
    rw [notMem_compl]; rw [mem_map]; rw [ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one]; rw [hf (mem_ofSign.mpr (sign_swap hij))]; rw [sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ => congr_arg (_ * ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]

中文:
定理 detp_mul
  证明: by
  have hf {s t} {σ : Perm n} (hσ : σ in ofSign s) :
      ofSign (t * s) = (ofSign t).map (mulRightEmbedding σ) := by
    ext τ
    simp_rw [mem_map, mulRightEmbedding_apply, ← eq_mul_inv_iff_mul_eq, exists_eq_right,
      mem_ofSign, map_mul, map_inv, mul_inv_eq_iff_eq_mul, mem_ofSign.mp hσ]
  have h {s t} : detp s A * detp t B =
      ∑ σ in ofSign s, ∑ τ in ofSign (t * s), ∏ k, A k (σ k) * B (σ k) (τ k) := by
    simp_rw [detp, sum_mul_sum, prod_mul_distrib]
    refine sum_congr rfl fun σ hσ => ?_
    simp_rw [hf hσ, sum_map, mulRightEmbedding_apply, Perm.mul_apply]
    exact sum_congr rfl fun τ hτ => (congr_arg (_ * ·) (Equiv.prod_comp σ _).symm)
  let ι : Perm n ↪ (n -> n) := ⟨_, coe_fn_injective⟩
  have hι {σ x} : ι σ x = σ x := rfl
  let bij : Finset (n -> n) := (disjUnion (ofSign 1) (ofSign (-1)) ofSign_disjoint).map ι
  replace h (s) : detp s (A * B) =
      ∑ σ in bijᶜ, ∑ τ in ofSign s, ∏ i : n, A i (σ i) * B (σ i) (τ i) +
        (detp 1 A * detp s B + detp (-1) A * detp (-s) B) := by
    simp_rw [h, neg_mul_neg, mul_one, detp, mul_apply, prod_univ_sum, Fintype.piFinset_univ]
    rw [sum_comm]; rw [← sum_compl_add_sum bij]; rw [sum_map]; rw [sum_disjUnion]
    simp_rw [hι]
  rw [h]; rw [h]; rw [neg_neg]; rw [add_assoc]
  conv_rhs => rw [add_assoc]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (add_comm _ _)
  replace hσ : ¬ Function.Injective σ := by
    contrapose hσ
    rw [notMem_compl]; rw [mem_map]; rw [ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one]; rw [hf (mem_ofSign.mpr (sign_swap hij))]; rw [sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ => congr_arg (_ * ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]

Depends on / 依赖: eq_mul_inv_iff_mul_eq, exists_eq_right, map_inv, map_mul, mem_map, mem_ofSign, mem_ofSign.mp, mulRightEmbedding, mulRightEmbedding_apply, mul_inv_eq_iff_eq_mul, ofSign, prod_mul_distrib, simp_rw, sum_congr, sum_map, sum_mul_sum
-/
theorem detp_mul :
    detp 1 (A * B) + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) =
      detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A * detp (-1) B) := by
  have hf {s t} {σ : Perm n} (hσ : σ in ofSign s) :
      ofSign (t * s) = (ofSign t).map (mulRightEmbedding σ) := by
    ext τ
    simp_rw [mem_map, mulRightEmbedding_apply, ← eq_mul_inv_iff_mul_eq, exists_eq_right,
      mem_ofSign, map_mul, map_inv, mul_inv_eq_iff_eq_mul, mem_ofSign.mp hσ]
  have h {s t} : detp s A * detp t B =
      ∑ σ in ofSign s, ∑ τ in ofSign (t * s), ∏ k, A k (σ k) * B (σ k) (τ k) := by
    simp_rw [detp, sum_mul_sum, prod_mul_distrib]
    refine sum_congr rfl fun σ hσ => ?_
    simp_rw [hf hσ, sum_map, mulRightEmbedding_apply, Perm.mul_apply]
    exact sum_congr rfl fun τ hτ => (congr_arg (_ * ·) (Equiv.prod_comp σ _).symm)
  let ι : Perm n ↪ (n -> n) := ⟨_, coe_fn_injective⟩
  have hι {σ x} : ι σ x = σ x := rfl
  let bij : Finset (n -> n) := (disjUnion (ofSign 1) (ofSign (-1)) ofSign_disjoint).map ι
  replace h (s) : detp s (A * B) =
      ∑ σ in bijᶜ, ∑ τ in ofSign s, ∏ i : n, A i (σ i) * B (σ i) (τ i) +
        (detp 1 A * detp s B + detp (-1) A * detp (-s) B) := by
    simp_rw [h, neg_mul_neg, mul_one, detp, mul_apply, prod_univ_sum, Fintype.piFinset_univ]
    rw [sum_comm]; rw [← sum_compl_add_sum bij]; rw [sum_map]; rw [sum_disjUnion]
    simp_rw [hι]
  rw [h]; rw [h]; rw [neg_neg]; rw [add_assoc]
  conv_rhs => rw [add_assoc]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ => ?_) (add_comm _ _)
  replace hσ : ¬ Function.Injective σ := by
    contrapose hσ
    rw [notMem_compl]; rw [mem_map]; rw [ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one]; rw [hf (mem_ofSign.mpr (sign_swap hij))]; rw [sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ => congr_arg (_ * ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]

/--
theorem `mul_adjp_apply_eq` / 定理 `mul_adjp_apply_eq`

English:
theorem mul_adjp_apply_eq
  statement: (A * adjp s A) i i = detp s A
  proof: by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ => ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx => sum_congr rfl fun σ hσ => ?_
  rw [← prod_mul_prod_compl ({i} : Finset n)]; rw [prod_singleton]; rw [(mem_filter.mp hσ).2]

中文:
定理 mul_adjp_apply_eq
  结论: (A * adjp s A) i i = detp s A
  证明: by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ => ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx => sum_congr rfl fun σ hσ => ?_
  rw [← prod_mul_prod_compl ({i} : Finset n)]; rw [prod_singleton]; rw [(mem_filter.mp hσ).2]

Depends on / 依赖: Finset, adjp_apply, filter_true, mem_filter, mem_filter.mp, mem_univ, mul_apply, mul_sum, ofSign, prod_mul_prod_compl, prod_singleton, simp_rw, sum_congr, sum_fiberwise_eq_sum_filter
-/
theorem mul_adjp_apply_eq : (A * adjp s A) i i = detp s A := by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ => ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx => sum_congr rfl fun σ hσ => ?_
  rw [← prod_mul_prod_compl ({i} : Finset n)]; rw [prod_singleton]; rw [(mem_filter.mp hσ).2]

/--
theorem `mul_adjp_apply_ne` / 定理 `mul_adjp_apply_ne`

English:
theorem mul_adjp_apply_ne
  given: (h : i != j)
  statement: (A * adjp 1 A) i j = (A * adjp (-1) A) i j
  proof: by
  let A' : Matrix n n R := A.updateRow j (A i)
  have h' s : (A * adjp s A) i j = (A' * adjp s A') j j := sum_congr rfl fun _ _ =>
congr_arg₂ (· * ·) (by simp [A']) sum_congr rfl fun σ hσ => prod_congr rfl fun _ _ => by aesop
  simp_rw [h', mul_adjp_apply_eq]
  apply detp_eq_of_row_eq h
  simp [A', Matrix.row_apply', h]

中文:
定理 mul_adjp_apply_ne
  条件: (h : i != j)
  结论: (A * adjp 1 A) i j = (A * adjp (-1) A) i j
  证明: by
  let A' : Matrix n n R := A.updateRow j (A i)
  have h' s : (A * adjp s A) i j = (A' * adjp s A') j j := sum_congr rfl fun _ _ =>
congr_arg₂ (· * ·) (by simp [A']) sum_congr rfl fun σ hσ => prod_congr rfl fun _ _ => by aesop
  simp_rw [h', mul_adjp_apply_eq]
  apply detp_eq_of_row_eq h
  simp [A', Matrix.row_apply', h]

Depends on / 依赖: A.updateRow, Matrix, Matrix.row_apply, detp_eq_of_row_eq, mul_adjp_apply_eq, prod_congr, row_apply, simp_rw, sum_congr, updateRow
-/
theorem mul_adjp_apply_ne (h : i != j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i j := by
  let A' : Matrix n n R := A.updateRow j (A i)
  have h' s : (A * adjp s A) i j = (A' * adjp s A') j j := sum_congr rfl fun _ _ =>
congr_arg₂ (· * ·) (by simp [A']) sum_congr rfl fun σ hσ => prod_congr rfl fun _ _ => by aesop
  simp_rw [h', mul_adjp_apply_eq]
  apply detp_eq_of_row_eq h
  simp [A', Matrix.row_apply', h]

/--
theorem `adjp_mul_apply_eq` / 定理 `adjp_mul_apply_eq`

English:
theorem adjp_mul_apply_eq
  statement: (adjp s A * A) i i = detp s A
  proof: by
  rw [← detp_transpose]; rw [← mul_adjp_apply_eq _ _ i]; rw [adjp_transpose]; rw [← transpose_mul]; rw [transpose_apply]

中文:
定理 adjp_mul_apply_eq
  结论: (adjp s A * A) i i = detp s A
  证明: by
  rw [← detp_transpose]; rw [← mul_adjp_apply_eq _ _ i]; rw [adjp_transpose]; rw [← transpose_mul]; rw [transpose_apply]

Depends on / 依赖: adjp_transpose, detp_transpose, mul_adjp_apply_eq, transpose_apply, transpose_mul
-/
theorem adjp_mul_apply_eq : (adjp s A * A) i i = detp s A := by
  rw [← detp_transpose]; rw [← mul_adjp_apply_eq _ _ i]; rw [adjp_transpose]; rw [← transpose_mul]; rw [transpose_apply]

/--
theorem `adjp_mul_apply_ne` / 定理 `adjp_mul_apply_ne`

English:
theorem adjp_mul_apply_ne
  given: (h : i != j)
  statement: (adjp 1 A * A) i j = (adjp (-1) A * A) i j
  proof: by
  simp_rw [← transpose_apply (_ * _) j i, transpose_mul,
    ← adjp_transpose, mul_adjp_apply_ne _ _ _ h.symm]

中文:
定理 adjp_mul_apply_ne
  条件: (h : i != j)
  结论: (adjp 1 A * A) i j = (adjp (-1) A * A) i j
  证明: by
  simp_rw [← transpose_apply (_ * _) j i, transpose_mul,
    ← adjp_transpose, mul_adjp_apply_ne _ _ _ h.symm]

Depends on / 依赖: adjp_transpose, h.symm, mul_adjp_apply_ne, simp_rw, transpose_apply, transpose_mul
-/
theorem adjp_mul_apply_ne (h : i != j) : (adjp 1 A * A) i j = (adjp (-1) A * A) i j := by
  simp_rw [← transpose_apply (_ * _) j i, transpose_mul,
    ← adjp_transpose, mul_adjp_apply_ne _ _ _ h.symm]

/--
theorem `mul_adjp_add_detp` / 定理 `mul_adjp_add_detp`

English:
theorem mul_adjp_add_detp
  statement: A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1
  proof: by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

中文:
定理 mul_adjp_add_detp
  结论: A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1
  证明: by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

Depends on / 依赖: add_apply, add_comm, eq_or_ne, mul_adjp_apply_eq, mul_adjp_apply_ne, mul_one, mul_zero, one_apply_eq, one_apply_ne, simp_rw, smul_apply, smul_eq_mul
-/
theorem mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

/--
lemma `detp_option_expand_row_none` / 引理 `detp_option_expand_row_none`

English:
lemma detp_option_expand_row_none
  given: (A : Matrix (Option n) (Option n) R)
  proof: by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

中文:
引理 detp_option_expand_row_none
  条件: (A : 矩阵 (选项类型 n) (选项类型 n) R)
  证明: by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

Depends on / 依赖: A.mul_adjp_apply_eq, Fintype, Fintype.sum_option, adjp_none_none, adjp_some_none, mul_adjp_apply_eq, mul_apply, simp_rw, sum_option
-/
lemma detp_option_expand_row_none (A : Matrix (Option n) (Option n) R) :
    A.detp s = A none none * (A.submatrix some some).detp s +
      ∑ k : n, A none (some k) * (A.submatrix some (Function.update some k none)).detp (-s) := by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

variable {A B}

/--
theorem `isAddUnit_mul` / 定理 `isAddUnit_mul`

English:
theorem isAddUnit_mul
  given: {d : n -> R} (hAB : A * B = diagonal d) (i j k : n) (hij : i != j)
  proof: by
  revert k
  rw [← IsAddUnit.sum_univ_iff]; rw [← mul_apply]; rw [hAB]; rw [diagonal_apply_ne _ hij]
  exact isAddUnit_zero

中文:
定理 isAddUnit_mul
  条件: {d : n -> R} (hAB : A * B = diagonal d) (i j k : n) (hij : i != j)
  证明: by
  revert k
  rw [← IsAddUnit.sum_univ_iff]; rw [← mul_apply]; rw [hAB]; rw [diagonal_apply_ne _ hij]
  exact isAddUnit_zero

Depends on / 依赖: IsAddUnit, IsAddUnit.sum_univ_iff, diagonal_apply_ne, isAddUnit_zero, mul_apply, revert, sum_univ_iff
-/
theorem isAddUnit_mul {d : n -> R} (hAB : A * B = diagonal d) (i j k : n) (hij : i != j) :
    IsAddUnit (A i k * B k j) := by
  revert k
  rw [← IsAddUnit.sum_univ_iff]; rw [← mul_apply]; rw [hAB]; rw [diagonal_apply_ne _ hij]
  exact isAddUnit_zero

/--
theorem `isAddUnit_detp_mul_detp` / 定理 `isAddUnit_detp_mul_detp`

English:
theorem isAddUnit_detp_mul_detp
  given: {d : n -> R} (hAB : A * B = diagonal d)
  proof: by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A * detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one]; rw [eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Perm.mul_apply, Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm]; rw [← Equiv.prod_comp σ]; rw [mul_comm]; rw [← prod_mul_distrib]; rw [← mul_prod_erase univ _ (mem_univ k)]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _

中文:
定理 isAddUnit_detp_mul_detp
  条件: {d : n -> R} (hAB : A * B = diagonal d)
  证明: by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A * detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one]; rw [eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Perm.mul_apply, Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm]; rw [← Equiv.prod_comp σ]; rw [mul_comm]; rw [← prod_mul_distrib]; rw [← mul_prod_erase univ _ (mem_univ k)]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _

Depends on / 依赖: Equiv.ext_iff, Equiv.prod_comp, IsAddUnit, IsAddUnit.sum_iff, Perm.mul_apply, Perm.one_apply, eq_comm, eq_inv_iff_mul_eq_one, ext_iff, mem_ofSign, mul_apply, mul_comm, ne_eq, ne_of_apply_ne, not_forall, one_apply, prod_comp, replace, sign_inv, simp_rw
-/
theorem isAddUnit_detp_mul_detp {d : n -> R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) := by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A * detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one]; rw [eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Perm.mul_apply, Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm]; rw [← Equiv.prod_comp σ]; rw [mul_comm]; rw [← prod_mul_distrib]; rw [← mul_prod_erase univ _ (mem_univ k)]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _

/--
theorem `isAddUnit_detp_smul_mul_adjp` / 定理 `isAddUnit_detp_smul_mul_adjp`

English:
theorem isAddUnit_detp_smul_mul_adjp
  given: {d : n -> R} (hAB : A * B = diagonal d)
  proof: by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A • (B * adjp t B)) from
    (h (by decide)).add (h (by decide))
  intro s t h
  rw [isAddUnit_iff]
  intro i j
  simp_rw [smul_apply, smul_eq_mul, mul_apply, detp, adjp_apply, mul_sum, sum_mul,
    IsAddUnit.sum_iff]
  intro k hk σ hσ τ hτ
  rw [mem_filter] at hσ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ.1]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one] at h
  obtain ⟨l, hl1, hl2⟩ := exists_mem_ne (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
  rw [mem_support]; rw [ne_comm] at hl1
  rw [ne_eq]; rw [← mem_singleton]; rw [← mem_compl] at hl2
  rw [← prod_mul_prod_compl {τ⁻¹ j}]; rw [mul_mul_mul_comm]; rw [mul_comm]; rw [← smul_eq_mul]
  apply IsAddUnit.smul_right
  have h0 : forall k, k in ({τ⁻¹ j} : Finset n)ᶜ ↔ τ k in ({j} : Finset n)ᶜ := by
    simp [inv_def, eq_symm_apply]
  rw [← prod_equiv τ h0 fun _ _ => rfl]; rw [← prod_mul_distrib]; rw [← mul_prod_erase _ _ hl2]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB l (σ (τ l)) (τ l) hl1).smul_right _

中文:
定理 isAddUnit_detp_smul_mul_adjp
  条件: {d : n -> R} (hAB : A * B = diagonal d)
  证明: by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A • (B * adjp t B)) from
    (h (by decide)).add (h (by decide))
  intro s t h
  rw [isAddUnit_iff]
  intro i j
  simp_rw [smul_apply, smul_eq_mul, mul_apply, detp, adjp_apply, mul_sum, sum_mul,
    IsAddUnit.sum_iff]
  intro k hk σ hσ τ hτ
  rw [mem_filter] at hσ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ.1]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one] at h
  obtain ⟨l, hl1, hl2⟩ := exists_mem_ne (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
  rw [mem_support]; rw [ne_comm] at hl1
  rw [ne_eq]; rw [← mem_singleton]; rw [← mem_compl] at hl2
  rw [← prod_mul_prod_compl {τ⁻¹ j}]; rw [mul_mul_mul_comm]; rw [mul_comm]; rw [← smul_eq_mul]
  apply IsAddUnit.smul_right
  have h0 : forall k, k in ({τ⁻¹ j} : Finset n)ᶜ ↔ τ k in ({j} : Finset n)ᶜ := by
    simp [inv_def, eq_symm_apply]
  rw [← prod_equiv τ h0 fun _ _ => rfl]; rw [← prod_mul_distrib]; rw [← mul_prod_erase _ _ hl2]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB l (σ (τ l)) (τ l) hl1).smul_right _

Depends on / 依赖: IsAddUnit, IsAddUnit.sum_iff, adjp_apply, eq_comm, eq_inv_iff_mul_eq_one, exists_mem, isAddUnit_iff, mem_filter, mem_ofSign, mul_apply, mul_sum, ne_eq, ne_of_apply_ne, replace, sign_inv, simp_rw, smul_apply, smul_eq_mul, sum_iff, sum_mul
-/
theorem isAddUnit_detp_smul_mul_adjp {d : n -> R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B)) := by
  suffices h : forall {s t}, s != t -> IsAddUnit (detp s A • (B * adjp t B)) from
    (h (by decide)).add (h (by decide))
  intro s t h
  rw [isAddUnit_iff]
  intro i j
  simp_rw [smul_apply, smul_eq_mul, mul_apply, detp, adjp_apply, mul_sum, sum_mul,
    IsAddUnit.sum_iff]
  intro k hk σ hσ τ hτ
  rw [mem_filter] at hσ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ.1]; rw [← hτ]; rw [← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq]; rw [eq_comm]; rw [eq_inv_iff_mul_eq_one] at h
  obtain ⟨l, hl1, hl2⟩ := exists_mem_ne (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
  rw [mem_support]; rw [ne_comm] at hl1
  rw [ne_eq]; rw [← mem_singleton]; rw [← mem_compl] at hl2
  rw [← prod_mul_prod_compl {τ⁻¹ j}]; rw [mul_mul_mul_comm]; rw [mul_comm]; rw [← smul_eq_mul]
  apply IsAddUnit.smul_right
  have h0 : forall k, k in ({τ⁻¹ j} : Finset n)ᶜ ↔ τ k in ({j} : Finset n)ᶜ := by
    simp [inv_def, eq_symm_apply]
  rw [← prod_equiv τ h0 fun _ _ => rfl]; rw [← prod_mul_distrib]; rw [← mul_prod_erase _ _ hl2]; rw [← smul_eq_mul]
  exact (isAddUnit_mul hAB l (σ (τ l)) (τ l) hl1).smul_right _

/--
theorem `detp_smul_add_adjp` / 定理 `detp_smul_add_adjp`

English:
theorem detp_smul_add_adjp
  given: (hAB : A * B = 1)
  proof: by
  have key := congr(A * $(mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, Matrix.mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

中文:
定理 detp_smul_add_adjp
  条件: (hAB : A * B = 1)
  证明: by
  have key := congr(A * $(mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, Matrix.mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

Depends on / 依赖: Matrix, Matrix.mul_smul, add_comm, eq_comm, mul_add, mul_adjp_add_detp, mul_assoc, mul_one, mul_smul, one_mul, simp_rw
-/
theorem detp_smul_add_adjp (hAB : A * B = 1) :
    detp 1 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B := by
  have key := congr(A * $(mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, Matrix.mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

/--
theorem `detp_smul_adjp` / 定理 `detp_smul_adjp`

English:
theorem detp_smul_adjp
  given: (hAB : A * B = 1)
  proof: by
  have h0 := detp_mul A B
  rw [hAB]; rw [detp_one_one]; rw [detp_neg_one_one]; rw [zero_add] at h0
  have h := detp_smul_add_adjp hAB
  replace h := congr(detp 1 A • $h + detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h

中文:
定理 detp_smul_adjp
  条件: (hAB : A * B = 1)
  证明: by
  have h0 := detp_mul A B
  rw [hAB]; rw [detp_one_one]; rw [detp_neg_one_one]; rw [zero_add] at h0
  have h := detp_smul_add_adjp hAB
  replace h := congr(detp 1 A • $h + detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h

Depends on / 依赖: add_add_add_comm, add_assoc, add_comm, add_right_inj, add_smul, detp_mul, detp_neg_one_one, detp_one_one, detp_smul_add_adjp, h.symm, isAddUnit_detp_mul_detp, one_smul, replace, smul_add, smul_right, smul_smul, zero_add
-/
theorem detp_smul_adjp (hAB : A * B = 1) :
    A + (detp 1 A • adjp (-1) B + detp (-1) A • adjp 1 B) =
      detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B := by
  have h0 := detp_mul A B
  rw [hAB]; rw [detp_one_one]; rw [detp_neg_one_one]; rw [zero_add] at h0
  have h := detp_smul_add_adjp hAB
  replace h := congr(detp 1 A • $h + detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h

instance (priority := low) instIsStablyFiniteRingOfCommSemiring : IsStablyFiniteRing R := by
  refine ⟨fun n => ⟨fun {A B} hAB => ?_⟩⟩
  have h0 := detp_mul A B
  rw [hAB]; rw [detp_one_one]; rw [detp_neg_one_one]; rw [zero_add] at h0
  replace h := congr(B * $(detp_smul_adjp hAB))
  simp only [mul_add, Matrix.mul_smul] at h
  replace h := congr($h + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) • 1)
  simp_rw [add_smul, ← smul_smul] at h
  rwa [add_assoc, add_add_add_comm, ← smul_add, ← smul_add,
    add_add_add_comm, ← smul_add, ← smul_add, smul_add, smul_add,
    mul_adjp_add_detp, smul_add, ← mul_adjp_add_detp, smul_add, ← smul_add, ← smul_add,
    add_add_add_comm, smul_smul, smul_smul, ← add_smul, ← h0,
    add_smul, one_smul, ← add_assoc _ 1, add_comm _ 1, add_assoc,
    smul_add, smul_add, add_add_add_comm, smul_smul, smul_smul, ← add_smul,
    ((isAddUnit_detp_smul_mul_adjp hAB).add
      ((isAddUnit_detp_mul_detp hAB).smul_right _)).add_left_inj] at h

end Matrix
