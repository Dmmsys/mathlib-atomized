/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!
# Radical of a polynomial

This file proves some theorems on `radical` and `divRadical` of polynomials.
See `Mathlib.RingTheory.Radical.Basic` for the definition of `radical` and `divRadical`.
-/

public section

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

variable {k : Type*} [Field k] [DecidableEq k]

/--
theorem `degree_radical_le` / 定理 `degree_radical_le`

English:
theorem degree_radical_le
  given: {a : k[X]} (h : a != 0)
  statement: (radical a).degree <= a.degree
  proof: degree_le_of_dvd radical_dvd_self h

中文:
定理 degree_radical_le
  条件: {a : k[X]} (h : a != 0)
  结论: (radical a).degree <= a.degree
  证明: degree_le_of_dvd radical_dvd_self h

Depends on / 依赖: degree_le_of_dvd, radical_dvd_self
-/
theorem degree_radical_le {a : k[X]} (h : a != 0) : (radical a).degree <= a.degree :=
  degree_le_of_dvd radical_dvd_self h

/--
theorem `natDegree_radical_le` / 定理 `natDegree_radical_le`

English:
theorem natDegree_radical_le
  given: {a : k[X]}
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  · exact natDegree_le_of_dvd radical_dvd_self ha

中文:
定理 natDegree_radical_le
  条件: {a : k[X]}
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  · exact natDegree_le_of_dvd radical_dvd_self ha

Depends on / 依赖: natDegree_le_of_dvd, radical_dvd_self
-/
theorem natDegree_radical_le {a : k[X]} :
    (radical a).natDegree <= a.natDegree := by
  by_cases ha : a = 0
  · simp [ha]
  · exact natDegree_le_of_dvd radical_dvd_self ha

/--
theorem `divRadical_dvd_derivative` / 定理 `divRadical_dvd_derivative`

English:
theorem divRadical_dvd_derivative
  given: (a : k[X])
  statement: divRadical a ∣ derivative a
  proof: by
  induction a using induction_on_coprime
  · case h0 =>
    rw [derivative_zero]
    apply dvd_zero
  · case h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  · case hpr p i hp =>
    cases i
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    · case succ i =>
      rw [← mul_dvd_mul_iff_left radical_ne_zero]; rw [radical_mul_divRadical]; rw [radical_pow_of_prime hp i.succ_ne_zero]; rw [derivative_pow_succ]; rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm]; rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ]; rw [mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero)]; rw [dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    case hcp x y hpxy hx hy =>
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_mul hc]; rw [derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y)) (mul_dvd_mul (divRadical_dvd_self x) hy)

中文:
定理 divRadical_dvd_derivative
  条件: (a : k[X])
  结论: divRadical a ∣ derivative a
  证明: by
  induction a using induction_on_coprime
  · case h0 =>
    rw [derivative_zero]
    apply dvd_zero
  · case h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  · case hpr p i hp =>
    cases i
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    · case succ i =>
      rw [← mul_dvd_mul_iff_left radical_ne_zero]; rw [radical_mul_divRadical]; rw [radical_pow_of_prime hp i.succ_ne_zero]; rw [derivative_pow_succ]; rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm]; rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ]; rw [mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero)]; rw [dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    case hcp x y hpxy hx hy =>
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_mul hc]; rw [derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y)) (mul_dvd_mul (divRadical_dvd_self x) hy)

Depends on / 依赖: derivative_one, derivative_pow_succ, derivative_zero, divRadical_isUnit, dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, dvd_zero, i.succ_ne_zero, induction_on_coprime, mul_assoc, mul_comm, mul_dvd_mul_iff_left, pow_succ, pow_zero, radical_mul_divRadical, radical_ne_zero, radical_pow_of_prime, succ_ne_zero
-/
theorem divRadical_dvd_derivative (a : k[X]) : divRadical a ∣ derivative a := by
  induction a using induction_on_coprime
  · case h0 =>
    rw [derivative_zero]
    apply dvd_zero
  · case h1 a ha =>
    exact (divRadical_isUnit ha).dvd
  · case hpr p i hp =>
    cases i
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    · case succ i =>
      rw [← mul_dvd_mul_iff_left radical_ne_zero]; rw [radical_mul_divRadical]; rw [radical_pow_of_prime hp i.succ_ne_zero]; rw [derivative_pow_succ]; rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      rw [mul_comm]; rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      rw [pow_succ]; rw [mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero)]; rw [dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    case hcp x y hpxy hx hy =>
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy hpx hpy)
    rw [divRadical_mul hc]; rw [derivative_mul]
    exact dvd_add (mul_dvd_mul hx (divRadical_dvd_self y)) (mul_dvd_mul (divRadical_dvd_self x) hy)

/--
theorem `divRadical_dvd_wronskian_left` / 定理 `divRadical_dvd_wronskian_left`

English:
theorem divRadical_dvd_wronskian_left
  given: (a b : k[X])
  statement: divRadical a ∣ wronskian a b
  proof: by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

中文:
定理 divRadical_dvd_wronskian_left
  条件: (a b : k[X])
  结论: divRadical a ∣ wronskian a b
  证明: by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

Depends on / 依赖: divRadical_dvd_derivative, divRadical_dvd_self, dvd_mul_of_dvd_left, dvd_sub, wronskian
-/
theorem divRadical_dvd_wronskian_left (a b : k[X]) : divRadical a ∣ wronskian a b := by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact divRadical_dvd_derivative a

/--
theorem `divRadical_dvd_wronskian_right` / 定理 `divRadical_dvd_wronskian_right`

English:
theorem divRadical_dvd_wronskian_right
  given: (a b : k[X])
  statement: divRadical b ∣ wronskian a b
  proof: by
  rw [← wronskian_neg_eq]; rw [dvd_neg]
  exact divRadical_dvd_wronskian_left _ _

中文:
定理 divRadical_dvd_wronskian_right
  条件: (a b : k[X])
  结论: divRadical b ∣ wronskian a b
  证明: by
  rw [← wronskian_neg_eq]; rw [dvd_neg]
  exact divRadical_dvd_wronskian_left _ _

Depends on / 依赖: divRadical_dvd_wronskian_left, dvd_neg, wronskian_neg_eq
-/
theorem divRadical_dvd_wronskian_right (a b : k[X]) : divRadical b ∣ wronskian a b := by
  rw [← wronskian_neg_eq]; rw [dvd_neg]
  exact divRadical_dvd_wronskian_left _ _
