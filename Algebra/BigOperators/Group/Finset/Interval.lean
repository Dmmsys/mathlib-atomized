/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Data.Int.Interval

/-!
# Sums/products over integer intervals

This file contains some lemmas about sums and products over integer intervals `Ixx`.

-/

public section

namespace Finset

@[to_additive]
/--
lemma `prod_Icc_of_even_eq_range` / 引理 `prod_Icc_of_even_eq_range`

English:
lemma prod_Icc_of_even_eq_range
  given: {α : Type*} [CommGroup α] {f : Int -> α} (hf : f.Even) (N : Nat)
  proof: by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Icc_succ_succ]; rw [prod_union (by simp)]; rw [prod_pair (by lia)]; rw [ih]; rw [prod_range_succ _ (N + 1)]; rw [hf]; rw [← pow_two]; rw [div_mul_eq_mul_div]; rw [← mul_pow]; rw [Nat.cast_succ]

@[to_additive]

中文:
引理 prod_Icc_of_even_eq_range
  条件: {α : 类型} [交换群 α] {f : 整数 -> α} (hf : f.Even) (N : 自然数)
  证明: by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Icc_succ_succ]; rw [prod_union (by simp)]; rw [prod_pair (by lia)]; rw [ih]; rw [prod_range_succ _ (N + 1)]; rw [hf]; rw [← pow_two]; rw [div_mul_eq_mul_div]; rw [← mul_pow]; rw [Nat.cast_succ]

@[to_additive]

Depends on / 依赖: Icc_succ_succ, Nat.cast_add, Nat.cast_one, Nat.cast_succ, cast_add, cast_one, cast_succ, div_mul_eq_mul_div, mul_pow, pow_two, prod_pair, prod_range_succ, prod_union
-/
lemma prod_Icc_of_even_eq_range {α : Type*} [CommGroup α] {f : Int -> α} (hf : f.Even) (N : Nat) :
    ∏ m in Icc (-N : Int) N, f m = (∏ m in range (N + 1), f m) ^ 2 / f 0 := by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Icc_succ_succ]; rw [prod_union (by simp)]; rw [prod_pair (by lia)]; rw [ih]; rw [prod_range_succ _ (N + 1)]; rw [hf]; rw [← pow_two]; rw [div_mul_eq_mul_div]; rw [← mul_pow]; rw [Nat.cast_succ]

@[to_additive]
/--
lemma `prod_Icc_eq_prod_Ico_mul` / 引理 `prod_Icc_eq_prod_Ico_mul`

English:
lemma prod_Icc_eq_prod_Ico_mul
  statement: {α : Type*} [CommMonoid α] (f : Int -> α) {l u : Int}
  proof: by
  simp [Icc_eq_cons_Ico h, mul_comm]

@[to_additive]

中文:
引理 prod_Icc_eq_prod_Ico_mul
  结论: {α : 类型} [交换幺半群 α] (f : 整数 -> α) {l u : 整数}
  证明: by
  simp [Icc_eq_cons_Ico h, mul_comm]

@[to_additive]

Depends on / 依赖: Icc_eq_cons_Ico, mul_comm
-/
lemma prod_Icc_eq_prod_Ico_mul {α : Type*} [CommMonoid α] (f : Int -> α) {l u : Int}
    (h : l <= u) : ∏ m in Icc l u, f m = (∏ m in Ico l u, f m) * f u := by
  simp [Icc_eq_cons_Ico h, mul_comm]

@[to_additive]
/--
lemma `prod_Icc_succ_eq_mul_endpoints` / 引理 `prod_Icc_succ_eq_mul_endpoints`

English:
lemma prod_Icc_succ_eq_mul_endpoints
  given: {R : Type*} [CommGroup R] (f : Int -> R) {N : Nat}
  proof: by
  induction N
  · rw [Icc_succ_succ]
    grind
  · rw [Icc_succ_succ, prod_union (by simp)]
    grind

@[to_additive]

中文:
引理 prod_Icc_succ_eq_mul_endpoints
  条件: {R : 类型} [交换群 R] (f : 整数 -> R) {N : 自然数}
  证明: by
  induction N
  · rw [Icc_succ_succ]
    grind
  · rw [Icc_succ_succ, prod_union (by simp)]
    grind

@[to_additive]

Depends on / 依赖: Icc_succ_succ, prod_union
-/
lemma prod_Icc_succ_eq_mul_endpoints {R : Type*} [CommGroup R] (f : Int -> R) {N : Nat} :
    ∏ m in Icc (-(N + 1) : Int) (N + 1), f m =
    f (N + 1) * f (-(N + 1) : Int) * ∏ m in Icc (-N : Int) N, f m := by
  induction N
  · rw [Icc_succ_succ]
    grind
  · rw [Icc_succ_succ, prod_union (by simp)]
    grind

@[to_additive]
/--
lemma `prod_Ico_int_div` / 引理 `prod_Ico_int_div`

English:
lemma prod_Ico_int_div
  given: (b : Nat) {α : Type*} [CommGroup α] (f : Int -> α)
  proof: by
  induction b with
  | zero => simp
  | succ b ihb =>
    simp only [Nat.cast_add_one, Ico_succ_succ]
    rw [prod_union (by simp)]; rw [prod_insert (by grind)]; rw [prod_singleton]; rw [ihb]; rw [← mul_assoc]; rw [mul_div]
    simp [mul_comm, mul_div, ← mul_assoc]

中文:
引理 prod_Ico_int_div
  条件: (b : 自然数) {α : 类型} [交换群 α] (f : 整数 -> α)
  证明: by
  induction b with
  | zero => simp
  | succ b ihb =>
    simp only [Nat.cast_add_one, Ico_succ_succ]
    rw [prod_union (by simp)]; rw [prod_insert (by grind)]; rw [prod_singleton]; rw [ihb]; rw [← mul_assoc]; rw [mul_div]
    simp [mul_comm, mul_div, ← mul_assoc]

Depends on / 依赖: Ico_succ_succ, Nat.cast_add_one, cast_add_one, mul_assoc, mul_comm, mul_div, prod_insert, prod_singleton, prod_union
-/
lemma prod_Ico_int_div (b : Nat) {α : Type*} [CommGroup α] (f : Int -> α) :
    ∏ n in Ico (-b : Int) b, f n / f (n + 1) = f (-b) / f b := by
  induction b with
  | zero => simp
  | succ b ihb =>
    simp only [Nat.cast_add_one, Ico_succ_succ]
    rw [prod_union (by simp)]; rw [prod_insert (by grind)]; rw [prod_singleton]; rw [ihb]; rw [← mul_assoc]; rw [mul_div]
    simp [mul_comm, mul_div, ← mul_assoc]

end Finset
