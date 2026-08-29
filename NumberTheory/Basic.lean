/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/

public section


section

open Ideal Ideal.Quotient

/--
theorem `dvd_sub_pow_of_dvd_sub` / 定理 `dvd_sub_pow_of_dvd_sub`

English:
theorem dvd_sub_pow_of_dvd_sub
  statement: {R : Type*} [CommRing R] {p : Nat} {a b : R} (h : (p : R) ∣ a - b)
  proof: by
  induction k with
  | zero => rwa [pow_one, pow_zero, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ p k]; rw [pow_mul]; rw [pow_mul]; rw [← geom_sum₂_mul]; rw [pow_succ']
    refine mul_dvd_mul ?_ ih
    let f : R ->+* R ⧸ span {(p : R)} := mk (span {(p : R)})
    have hf : forall r : R, (

中文:
定理 dvd_sub_pow_of_dvd_sub
  结论: {R : 类型} [CommRing R] {p : 自然数} {a b : R} (h : (p : R) ∣ a - b)
  证明: by
  induction k with
  | zero => rwa [pow_one, pow_zero, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ p k]; rw [pow_mul]; rw [pow_mul]; rw [← geom_sum₂_mul]; rw [pow_succ']
    refine mul_dvd_mul ?_ ih
    let f : R ->+* R ⧸ span {(p : R)} := mk (span {(p : R)})
    have hf : forall r : R, (

Depends on / 依赖: RingHom, RingHom.map_geom_sum, eq_zero_iff_mem, map_pow, map_sub, mem_span_singleton, mul_dvd_mul, pow_mul, pow_one, pow_succ, pow_zero, sub_eq_zero
-/
theorem dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : Nat} {a b : R} (h : (p : R) ∣ a - b)
    (k : Nat) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction k with
  | zero => rwa [pow_one, pow_zero, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ p k]; rw [pow_mul]; rw [pow_mul]; rw [← geom_sum₂_mul]; rw [pow_succ']
    refine mul_dvd_mul ?_ ih
    let f : R ->+* R ⧸ span {(p : R)} := mk (span {(p : R)})
    have hf : forall r : R, (p : R) ∣ r ↔ f r = 0 := fun r => by rw [eq_zero_iff_mem, mem_span_singleton]
    rw [hf]; rw [map_sub]; rw [sub_eq_zero] at h
    rw [hf]; rw [RingHom.map_geom_sum₂]; rw [map_pow]; rw [map_pow]; rw [h]; rw [geom_sum₂_self]; rw [mul_eq_zero_of_left]
    rw [← map_natCast f]; rw [eq_zero_iff_mem]; rw [mem_span_singleton]

end
