/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Euclidean
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Absolute value on polynomials over a finite field.

Let `𝔽_q` be a finite field of cardinality `q`, then the map sending a polynomial `p`
to `q ^ degree p` (where `q ^ degree 0 = 0`) is an absolute value.

## Main definitions

* `Polynomial.cardPowDegree` is an absolute value on `𝔽_q[t]`, the ring of
  polynomials over a finite field of cardinality `q`, mapping a polynomial `p`
  to `q ^ degree p` (where `q ^ degree 0 = 0`)

## Main results
* `Polynomial.cardPowDegree_isEuclidean`: `cardPowDegree` respects the
  Euclidean domain structure on the ring of polynomials

-/

@[expose] public section


namespace Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

open AbsoluteValue

open Polynomial

/--
Definition of `cardPowDegree` / `cardPowDegree` 的定义

English:
definition cardPowDegree
  signature: : AbsoluteValue Fq[X] Int
  body: have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  letI := Classical.decEq Fq
  { toFun := fun p => if p = 0 then 0 else (Fintype.card Fq : Int) ^ p.natDeg

中文:
定义 cardPowDegree
  签名: : 绝对值 Fq[X] 整数
  定义体: have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  letI := Classical.decEq Fq
  { toFun := fun p => if p = 0 then 0 else (Fintype.card Fq : Int) ^ p.natDeg

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.card, Fintype.card_pos_iff.mpr, Int.natCast_nonneg, Int.natCast_pos.mpr, absurd, add_le, card_pos, card_pos_iff, contrapose, eq_zero, ite_eq_left_iff, ite_eq_left_iff.trans, natCast_nonneg, natCast_pos, natDegree, nonneg, p.natDegree
-/
noncomputable def cardPowDegree : AbsoluteValue Fq[X] Int :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  letI := Classical.decEq Fq
  { toFun := fun p => if p = 0 then 0 else (Fintype.card Fq : Int) ^ p.natDegree
    nonneg' := fun p => by
      split_ifs
      · rfl
      exact pow_nonneg (Int.natCast_nonneg _) _
    eq_zero' := fun p =>
      ite_eq_left_iff.trans
        ⟨fun h => by
          contrapose! h
          exact ⟨h, (pow_pos _).ne'⟩, absurd⟩
    add_le' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      by_cases hpq : p + q = 0
      · simp only [hpq, hp, hq, if_true, if_false]
        exact add_nonneg (pow_pos _).le (pow_pos _).le
      simp only [hpq, hp, hq, if_false]
      exact le_trans (pow_right_mono₀ (by lia) (Polynomial.natDegree_add_le _ _)) (by grind)
    map_mul' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      have hpq : p * q != 0 := mul_ne_zero hp hq
      simp only [hpq, hp, hq, if_false, Polynomial.natDegree_mul hp hq, pow_add] }

/--
theorem `cardPowDegree_apply` / 定理 `cardPowDegree_apply`

English:
theorem cardPowDegree_apply
  given: [DecidableEq Fq] (p : Fq[X])
  proof: by
  simp [cardPowDegree]

@[simp]

中文:
定理 cardPowDegree_apply
  条件: [DecidableEq Fq] (p : Fq[X])
  证明: by
  simp [cardPowDegree]

@[simp]

Depends on / 依赖: cardPowDegree
-/
theorem cardPowDegree_apply [DecidableEq Fq] (p : Fq[X]) :
    cardPowDegree p = if p = 0 then 0 else (Fintype.card Fq : Int) ^ natDegree p := by
  simp [cardPowDegree]

@[simp]
/--
theorem `cardPowDegree_zero` / 定理 `cardPowDegree_zero`

English:
theorem cardPowDegree_zero
  statement: cardPowDegree (0 : Fq[X]) = 0
  proof: rfl

@[simp]

中文:
定理 cardPowDegree_zero
  结论: cardPowDegree (0 : Fq[X]) = 0
  证明: rfl

@[simp]
-/
theorem cardPowDegree_zero : cardPowDegree (0 : Fq[X]) = 0 := rfl

@[simp]
/--
theorem `cardPowDegree_nonzero` / 定理 `cardPowDegree_nonzero`

English:
theorem cardPowDegree_nonzero
  given: (p : Fq[X]) (hp : p != 0)
  proof: if_neg hp

中文:
定理 cardPowDegree_nonzero
  条件: (p : Fq[X]) (hp : p != 0)
  证明: if_neg hp

Depends on / 依赖: if_neg
-/
theorem cardPowDegree_nonzero (p : Fq[X]) (hp : p != 0) :
    cardPowDegree p = (Fintype.card Fq : Int) ^ p.natDegree :=
  if_neg hp

/--
theorem `cardPowDegree_isEuclidean` / 定理 `cardPowDegree_isEuclidean`

English:
theorem cardPowDegree_isEuclidean
  statement: IsEuclidean (cardPowDegree : AbsoluteValue Fq[X] Int)
  proof: have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      change cardPowDegree p < cardPowDegree q ↔ de

中文:
定理 cardPowDegree_isEuclidean
  结论: 是Euclidean (cardPowDegree : 绝对值 Fq[X] 整数)
  证明: have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      change cardPowDegree p < cardPowDegree q ↔ de

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_pos_iff.mpr, Int.natCast_pos.mpr, bot_lt_iff_ne_bot, cardPowDegree, cardPowDegree_apply, card_pos, card_pos_iff, classical, degree, degree_eq_bot, degree_zero, lt_self_iff_false, map_lt_map_iff, natCast_pos, not_false_iff, pow_pos, split_ifs
-/
theorem cardPowDegree_isEuclidean : IsEuclidean (cardPowDegree : AbsoluteValue Fq[X] Int) :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : forall n, 0 < (Fintype.card Fq : Int) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      change cardPowDegree p < cardPowDegree q ↔ degree p < degree q
      simp only [cardPowDegree_apply]
      split_ifs with hp hq hq
      · simp only [hp, hq, lt_self_iff_false]
      · simp only [hp, hq, degree_zero, Ne, bot_lt_iff_ne_bot, degree_eq_bot, pow_pos,
          not_false_iff]
      · simp only [hq, degree_zero, not_lt_bot, (pow_pos _).not_gt]
      · rw [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt, pow_lt_pow_iff_right₀]
        exact mod_cast @Fintype.one_lt_card Fq _ _ }

end Polynomial
