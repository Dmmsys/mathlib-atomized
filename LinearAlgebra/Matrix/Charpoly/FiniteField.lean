/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Results on characteristic polynomials and traces over finite fields.
-/

public section


noncomputable section

open Polynomial Matrix

open scoped Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

@[simp]
/--
theorem `FiniteField.Matrix.charpoly_pow_card` / 定理 `FiniteField.Matrix.charpoly_pow_card`

English:
theorem FiniteField.Matrix.charpoly_pow_card
  given: {K : Type*} [Field K] [Fintype K] (M : Matrix n n K)
  proof: by
  cases (isEmpty_or_nonempty n).symm
  · obtain ⟨p, hp⟩ := CharP.exists K
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    dsimp at hk; rw [hk]
    apply (frobenius_inj K[X] p).iterate k
    repeat' rw [iterate_frobenius (R := K[X])]; rw [← hk]
    rw

中文:
定理 FiniteField.矩阵.charpoly_pow_card
  条件: {K : 类型} [域 K] [有限类型 K] (M : 矩阵 n n K)
  证明: by
  cases (isEmpty_or_nonempty n).symm
  · obtain ⟨p, hp⟩ := CharP.exists K
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    dsimp at hk; rw [hk]
    apply (frobenius_inj K[X] p).iterate k
    repeat' rw [iterate_frobenius (R := K[X])]; rw [← hk]
    rw

Depends on / 依赖: AlgHom, AlgHom.map_det, CharP.exists, FiniteField, FiniteField.card, FiniteField.expand_card, Matrix, charpoly, coe_detMonoidHom, congr_arg, detMonoidHom, expand_card, frobenius_inj, injective, isEmpty_or_nonempty, iterate, iterate_frobenius, map_det, map_pow, matPolyEq
-/
theorem FiniteField.Matrix.charpoly_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    (M ^ Fintype.card K).charpoly = M.charpoly := by
  cases (isEmpty_or_nonempty n).symm
  · obtain ⟨p, hp⟩ := CharP.exists K
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    dsimp at hk; rw [hk]
    apply (frobenius_inj K[X] p).iterate k
    repeat' rw [iterate_frobenius (R := K[X])]; rw [← hk]
    rw [← FiniteField.expand_card]
    unfold charpoly
    rw [AlgHom.map_det]; rw [← coe_detMonoidHom]; rw [← (detMonoidHom : Matrix n n K[X] ->* K[X]).map_pow]
    apply congr_arg det
    refine matPolyEquiv.injective ?_
    rw [map_pow]; rw [matPolyEquiv_charmatrix]; rw [hk]; rw [sub_pow_char_pow_of_commute]; rw [← C_pow]
    · exact (id (matPolyEquiv_eq_X_pow_sub_C (p ^ k) M) :)
    · exact (C M).commute_X
  · exact congr_arg _ (Subsingleton.elim _ _)

@[simp]
/--
theorem `ZMod.charpoly_pow_card` / 定理 `ZMod.charpoly_pow_card`

English:
theorem ZMod.charpoly_pow_card
  given: {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p))
  proof: by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [ZMod.card] at h

中文:
定理 ZMod.charpoly_pow_card
  条件: {p : 自然数} [Fact p.素] (M : 矩阵 n n (ZMod p))
  证明: by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [ZMod.card] at h

Depends on / 依赖: FiniteField, FiniteField.Matrix.charpoly_pow_card, Matrix, ZMod.card, charpoly_pow_card
-/
theorem ZMod.charpoly_pow_card {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    (M ^ p).charpoly = M.charpoly := by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [ZMod.card] at h

/--
theorem `FiniteField.trace_pow_card` / 定理 `FiniteField.trace_pow_card`

English:
theorem FiniteField.trace_pow_card
  given: {K : Type*} [Field K] [Fintype K] (M : Matrix n n K)
  proof: by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [FiniteField.Matrix.charpoly_pow_card]; rw [FiniteField.pow_card]

中文:
定理 FiniteField.trace_pow_card
  条件: {K : 类型} [域 K] [有限类型 K] (M : 矩阵 n n K)
  证明: by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [FiniteField.Matrix.charpoly_pow_card]; rw [FiniteField.pow_card]

Depends on / 依赖: FiniteField, FiniteField.Matrix.charpoly_pow_card, FiniteField.pow_card, Matrix, Matrix.trace, Matrix.trace_eq_neg_charpoly_coeff, charpoly_pow_card, isEmpty_or_nonempty, pow_card, trace_eq_neg_charpoly_coeff
-/
theorem FiniteField.trace_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    trace (M ^ Fintype.card K) = trace M ^ Fintype.card K := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [Matrix.trace_eq_neg_charpoly_coeff]; rw [FiniteField.Matrix.charpoly_pow_card]; rw [FiniteField.pow_card]

/--
theorem `ZMod.trace_pow_card` / 定理 `ZMod.trace_pow_card`

English:
theorem ZMod.trace_pow_card
  given: {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p))
  proof: by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h

中文:
定理 ZMod.trace_pow_card
  条件: {p : 自然数} [Fact p.素] (M : 矩阵 n n (ZMod p))
  证明: by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h

Depends on / 依赖: FiniteField, FiniteField.trace_pow_card, ZMod.card, trace_pow_card
-/
theorem ZMod.trace_pow_card {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    trace (M ^ p) = trace M ^ p := by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h
