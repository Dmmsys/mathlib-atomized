/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prime elements in rings

This file contains lemmas about prime elements of commutative rings.
-/

public section


section CancelCommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R]

open Finset

/--
theorem `mul_eq_mul_prime_prod` / 定理 `mul_eq_mul_prime_prod`

English:
theorem mul_eq_mul_prime_prod
  statement: {α : Type*} [DecidableEq α] {x y a : R} {s : Finset α} {p : α -> R}
  proof: by
  induction s using Finset.induction generalizing x y a with
  | empty => exact ⟨∅, ∅, x, y, by simp [hx]⟩
  | insert i s his ih =>
    rw [prod_insert his]; rw [← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi => hp i (mem_insert_of_mem hi)) hx 

中文:
定理 mul_eq_mul_prime_prod
  结论: {α : 类型} [DecidableEq α] {x y a : R} {s : 有限集 α} {p : α -> R}
  证明: by
  induction s using Finset.induction generalizing x y a with
  | empty => exact ⟨∅, ∅, x, y, by simp [hx]⟩
  | insert i s his ih =>
    rw [prod_insert his]; rw [← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi => hp i (mem_insert_of_mem hi)) hx 

Depends on / 依赖: Finset, Finset.induction, generalizing, insert, mem_insert_of_mem, mem_insert_self, mem_union_left, mem_union_right, mul_assoc, prod_insert
-/
theorem mul_eq_mul_prime_prod {α : Type*} [DecidableEq α] {x y a : R} {s : Finset α} {p : α -> R}
    (hp : forall i in s, Prime (p i)) (hx : x * y = a * ∏ i in s, p i) :
    exists (t u : Finset α) (b c : R),
      t union u = s ∧ Disjoint t u ∧ a = b * c ∧ (x = b * ∏ i in t, p i) ∧ y = c * ∏ i in u, p i := by
  induction s using Finset.induction generalizing x y a with
  | empty => exact ⟨∅, ∅, x, y, by simp [hx]⟩
  | insert i s his ih =>
    rw [prod_insert his]; rw [← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi => hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩
    have hit : i ∉ t := fun hit => his (htus ▸ mem_union_left _ hit)
    have hiu : i ∉ u := fun hiu => his (htus ▸ mem_union_right _ hiu)
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : p i ∣ b ∨ p i ∣ c := hpi.dvd_or_dvd ⟨a, by rw [← hbc, mul_comm]⟩
    · rw [mul_assoc, mul_comm a, mul_right_inj' hpi.ne_zero] at hbc
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus], disjoint_insert_left.2 ⟨hiu, htu⟩, by
          simp [hbc, prod_insert hit, mul_comm, mul_left_comm]⟩
    · rw [← mul_assoc, mul_right_comm b, mul_left_inj' hpi.ne_zero] at hbc
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus], disjoint_insert_right.2 ⟨hit, htu⟩, by
          simp [← hbc, prod_insert hiu, mul_comm, mul_left_comm]⟩

/--
theorem `mul_eq_mul_prime_pow` / 定理 `mul_eq_mul_prime_pow`

English:
theorem mul_eq_mul_prime_pow
  given: {x y a p : R} {n : Nat} (hp : Prime p) (hx : x * y = a * p ^ n)
  proof: by
  rcases mul_eq_mul_prime_prod (fun _ _ => hp)
    (show x * y = a * (range n).prod fun _ => p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨#t, #u, b, c, by rw [← card_union_of_disjoint htu, htus, card_range], by simp⟩

中文:
定理 mul_eq_mul_prime_pow
  条件: {x y a p : R} {n : 自然数} (hp : 素 p) (hx : x * y = a * p ^ n)
  证明: by
  rcases mul_eq_mul_prime_prod (fun _ _ => hp)
    (show x * y = a * (range n).prod fun _ => p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨#t, #u, b, c, by rw [← card_union_of_disjoint htu, htus, card_range], by simp⟩

Depends on / 依赖: card_range, card_union_of_disjoint, mul_eq_mul_prime_prod
-/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : Nat} (hp : Prime p) (hx : x * y = a * p ^ n) :
    exists (i j : Nat) (b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j := by
  rcases mul_eq_mul_prime_prod (fun _ _ => hp)
    (show x * y = a * (range n).prod fun _ => p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨#t, #u, b, c, by rw [← card_union_of_disjoint htu, htus, card_range], by simp⟩

end CancelCommMonoidWithZero

section CommRing

variable {α : Type*} [CommRing α]

/--
theorem `Prime.neg` / 定理 `Prime.neg`

English:
theorem Prime.neg
  given: {p : α} (hp : Prime p)
  statement: Prime (-p)
  proof: by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩

中文:
定理 素.neg
  条件: {p : α} (hp : 素 p)
  结论: 素 (-p)
  证明: by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩

Depends on / 依赖: IsUnit, IsUnit.neg_iff, neg_dvd, neg_iff, neg_ne_zero, neg_ne_zero.mpr
-/
theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩

/--
theorem `Prime.abs` / 定理 `Prime.abs`

English:
theorem Prime.abs
  given: [LinearOrder α] {p : α} (hp : Prime p)
  statement: Prime (abs p)
  proof: by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg

中文:
定理 素.abs
  条件: [线性序 α] {p : α} (hp : 素 p)
  结论: 素 (abs p)
  证明: by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg

Depends on / 依赖: abs_choice, hp.neg
-/
theorem Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p) := by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg

end CommRing
