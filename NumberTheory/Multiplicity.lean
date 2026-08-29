/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen, Mantas Bakšys
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-!
# Multiplicity in Number Theory

This file contains results in number theory relating to multiplicity.

## Main statements

* `multiplicity.Int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* [Wikipedia, *Lifting-the-exponent lemma*](https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma)
-/

public section


open Ideal Ideal.Quotient Finset

variable {R : Type*} {n : Nat}

section CommRing

variable [CommRing R] {a b x y : R}

/--
theorem `dvd_geom_sum₂_iff_of_dvd_sub` / 定理 `dvd_geom_sum₂_iff_of_dvd_sub`

English:
theorem dvd_geom_sum₂_iff_of_dvd_sub
  given: {x y p : R} (h : p ∣ x - y)
  proof: by
  rw [← mem_span_singleton]; rw [← Ideal.Quotient.eq] at h
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    map_mul, map_pow, map_natCast]

中文:
定理 dvd_geom_sum₂_iff_of_dvd_sub
  条件: {x y p : R} (h : p ∣ x - y)
  证明: by
  rw [← mem_span_singleton]; rw [← Ideal.Quotient.eq] at h
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    map_mul, map_pow, map_natCast]

Depends on / 依赖: Ideal.Quotient.eq, Quotient, RingHom, RingHom.map_geom_sum, eq_zero_iff_mem, map_mul, map_natCast, map_pow, mem_span_singleton
-/
theorem dvd_geom_sum₂_iff_of_dvd_sub {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * y ^ (n - 1) := by
  rw [← mem_span_singleton]; rw [← Ideal.Quotient.eq] at h
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    map_mul, map_pow, map_natCast]

/--
theorem `dvd_geom_sum₂_iff_of_dvd_sub'` / 定理 `dvd_geom_sum₂_iff_of_dvd_sub'`

English:
theorem dvd_geom_sum₂_iff_of_dvd_sub'
  given: {x y p : R} (h : p ∣ x - y)
  proof: by
  rw [geom_sum₂_comm]; rw [dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right

中文:
定理 dvd_geom_sum₂_iff_of_dvd_sub'
  条件: {x y p : R} (h : p ∣ x - y)
  证明: by
  rw [geom_sum₂_comm]; rw [dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right

Depends on / 依赖: h.neg_right, neg_right
-/
theorem dvd_geom_sum₂_iff_of_dvd_sub' {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * x ^ (n - 1) := by
  rw [geom_sum₂_comm]; rw [dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right

/--
theorem `dvd_geom_sum₂_self` / 定理 `dvd_geom_sum₂_self`

English:
theorem dvd_geom_sum₂_self
  given: {x y : R} (h : ↑n ∣ x - y)
  proof: (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)

中文:
定理 dvd_geom_sum₂_self
  条件: {x y : R} (h : ↑n ∣ x - y)
  证明: (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)

Depends on / 依赖: dvd_mul_right
-/
theorem dvd_geom_sum₂_self {x y : R} (h : ↑n ∣ x - y) :
    ↑n ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
  (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)

/--
theorem `sq_dvd_add_pow_sub_sub` / 定理 `sq_dvd_add_pow_sub_sub`

English:
theorem sq_dvd_add_pow_sub_sub
  given: (p x : R) (n : Nat)
  proof: by
  rcases n with - | n
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, mul_zero]
  · simp only [add_pow, sum_range_succ, add_tsub_cancel_left, pow_one, Nat.choose_succ_self_right,
      Nat.cast_succ, tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_zero, zero_add,
   

中文:
定理 sq_dvd_add_pow_sub_sub
  条件: (p x : R) (n : 自然数)
  证明: by
  rcases n with - | n
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, mul_zero]
  · simp only [add_pow, sum_range_succ, add_tsub_cancel_left, pow_one, Nat.choose_succ_self_right,
      Nat.cast_succ, tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_zero, zero_add,
   

Depends on / 依赖: Finset, Finset.dvd_sum, Nat.cast_succ, Nat.cast_zero, Nat.choose_self, Nat.choose_succ_self_right, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, add_pow, add_tsub_cancel_left, cast_succ, cast_zero, choose_self, choose_succ_self_right, convert, dvd_sum, dvd_zero, mul_one, mul_zero, pow_dvd_p
-/
theorem sq_dvd_add_pow_sub_sub (p x : R) (n : Nat) :
    p ^ 2 ∣ (x + p) ^ n - x ^ (n - 1) * p * n - x ^ n := by
  rcases n with - | n
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, mul_zero]
  · simp only [add_pow, sum_range_succ, add_tsub_cancel_left, pow_one, Nat.choose_succ_self_right,
      Nat.cast_succ, tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_zero, zero_add,
      Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    suffices p ^ 2 ∣ ∑ i in range n, x ^ i * p ^ (n + 1 - i) * ↑((n + 1).choose i) by
      convert! this; abel
    apply Finset.dvd_sum
    intro y hy
    calc
      p ^ 2 ∣ p ^ (n + 1 - y) :=
        pow_dvd_pow p (le_tsub_of_add_le_left (by linarith [Finset.mem_range.mp hy]))
      _ ∣ x ^ y * p ^ (n + 1 - y) * ↑((n + 1).choose y) :=
        dvd_mul_of_dvd_left (dvd_mul_left _ _) _

/--
theorem `not_dvd_geom_sum₂` / 定理 `not_dvd_geom_sum₂`

English:
theorem not_dvd_geom_sum₂
  given: {p : R} (hp : Prime p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n)
  proof: fun h =>
hx
hp.dvd_of_dvd_pow (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn

中文:
定理 not_dvd_geom_sum₂
  条件: {p : R} (hp : 素 p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n)
  证明: fun h =>
hx
hp.dvd_of_dvd_pow (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn
-/
theorem not_dvd_geom_sum₂ {p : R} (hp : Prime p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
    ¬p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i) := fun h =>
hx
hp.dvd_of_dvd_pow (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn

variable {p : Nat} (a b)

/--
theorem `odd_sq_dvd_geom_sum₂_sub` / 定理 `odd_sq_dvd_geom_sum₂_sub`

English:
theorem odd_sq_dvd_geom_sum₂_sub
  given: (hp : Odd p)
  proof: by
  have h1 : forall (i : Nat),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_

中文:
定理 odd_sq_dvd_geom_sum₂_sub
  条件: (hp : Odd p)
  证明: by
  have h1 : forall (i : Nat),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_

Depends on / 依赖: Finset, Ideal.Quotient.eq, Ideal.Quotient.mk, Quotient, dvd_mul_right, mem_span_singleton, mul_pow, simp_rw, sq_dvd_add_pow_sub_sub, sub_sub
-/
theorem odd_sq_dvd_geom_sum₂_sub (hp : Odd p) :
    (p : R) ^ 2 ∣ (∑ i in range p, (a + p * b) ^ i * a ^ (p - 1 - i)) - p * a ^ (p - 1) := by
  have h1 : forall (i : Nat),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_dvd_add_pow_sub_sub (↑p * b) a i, ← sub_sub]
  simp_rw [← mem_span_singleton, ← Ideal.Quotient.eq] at *
  let s : R := (p : R) ^ 2
  calc
    (Ideal.Quotient.mk (span {s})) (∑ i in range p, (a + (p : R) * b) ^ i * a ^ (p - 1 - i)) =
        ∑ i in Finset.range p,
        mk (span {s}) ((a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) * a ^ (p - 1 - i)) := by
      simp_rw [s, RingHom.map_geom_sum₂, ← map_pow, h1, ← map_mul]
    _ =
        mk (span {s})
            (∑ x in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ x in Finset.range p, a ^ (x + (p - 1 - x))) := by
      ring_nf
      simp_rw [← map_sum, sum_add_distrib, map_add]
    _ =
        mk (span {s})
            (∑ x in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ _x in Finset.range p, a ^ (p - 1)) := by
      rw [add_right_inj]
      have : forall (x : Nat), (hx : x in range p) -> a ^ (x + (p - 1 - x)) = a ^ (p - 1) := by
        intro x hx
        rw [← Nat.add_sub_assoc _ x]; rw [Nat.add_sub_cancel_left]
        exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hx)
      rw [Finset.sum_congr rfl this]
    _ =
        mk (span {s})
            (∑ x in Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ =
        mk (span {s}) (↑p * b * ∑ x in Finset.range p, a ^ (p - 2) * x) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_add]
      rw [Finset.sum_congr rfl]
      rintro (⟨⟩ | ⟨x⟩) hx
      · rw [Nat.cast_zero, mul_zero, mul_zero]
      · have : x.succ - 1 + (p - 1 - x.succ) = p - 2 := by
          rw [← Nat.add_sub_assoc (Nat.le_sub_one_of_lt (Finset.mem_range.mp hx))]
          exact congr_arg Nat.pred (Nat.add_sub_cancel_left _ _)
        rw [this]
        ring1
    _ = mk (span {s}) (↑p * a ^ (p - 1)) := by
      have : Finset.sum (range p) (fun (x : Nat) => (x : R)) =
          ((Finset.sum (range p) (fun (x : Nat) => (x : Nat)))) := by simp only [Nat.cast_sum]
      simp only [add_eq_right, ← Finset.mul_sum, this]
      norm_cast
      simp only [Finset.sum_range_id]
      norm_cast
      simp only [Nat.cast_mul, map_mul,
          Nat.mul_div_assoc p (even_iff_two_dvd.mp (Nat.Odd.sub_odd hp odd_one))]
      ring_nf
      rw [mul_assoc]; rw [mul_assoc]
      refine mul_eq_zero_of_left ?_ _
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      simp [s]

section IntegralDomain

variable [IsDomain R]

/--
theorem `emultiplicity_pow_sub_pow_of_prime` / 定理 `emultiplicity_pow_sub_pow_of_prime`

English:
theorem emultiplicity_pow_sub_pow_of_prime
  statement: {p : R} (hp : Prime p) {x y : R}
  proof: by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn)]; rw [zero_add]

中文:
定理 emultiplicity_pow_sub_pow_of_prime
  结论: {p : R} (hp : 素 p) {x y : R}
  证明: by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn)]; rw [zero_add]

Depends on / 依赖: emultiplicity_eq_zero, emultiplicity_mul, zero_add
-/
theorem emultiplicity_pow_sub_pow_of_prime {p : R} (hp : Prime p) {x y : R}
    (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : ¬p ∣ n) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) := by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn)]; rw [zero_add]

variable (hp : Prime (p : R)) (hp1 : Odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx

/--
theorem `emultiplicity_geom_sum₂_eq_one` / 定理 `emultiplicity_geom_sum₂_eq_one`

English:
theorem emultiplicity_geom_sum₂_eq_one
  proof: by
  rw [← Nat.cast_one]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one]
    exact dvd_geom_sum₂_self hxy
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  obtain ⟨k, hk⟩ := hxy
  rw [one_add_one_eq_two]; rw [eq_add_of_sub_eq' hk]
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ 

中文:
定理 emultiplicity_geom_sum₂_eq_one
  证明: by
  rw [← Nat.cast_one]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one]
    exact dvd_geom_sum₂_self hxy
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  obtain ⟨k, hk⟩ := hxy
  rw [one_add_one_eq_two]; rw [eq_add_of_sub_eq' hk]
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ 

Depends on / 依赖: Nat.cast_one, cast_one, dvd_iff_dvd_of_dvd_sub, dvd_of_dvd_pow, emultiplicity_eq_coe, eq_add_of_sub_eq, hp.dvd_of_dvd_pow, hp.ne_zero, mul_dvd_mul_iff_left, ne_zero, one_add_one_eq_two, pow_one, pow_two
-/
theorem emultiplicity_geom_sum₂_eq_one :
    emultiplicity (↑p) (∑ i in range p, x ^ i * y ^ (p - 1 - i)) = 1 := by
  rw [← Nat.cast_one]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one]
    exact dvd_geom_sum₂_self hxy
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  obtain ⟨k, hk⟩ := hxy
  rw [one_add_one_eq_two]; rw [eq_add_of_sub_eq' hk]
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1)).mp ?_
  rw [pow_two]; rw [mul_dvd_mul_iff_left hp.ne_zero]
  exact mt hp.dvd_of_dvd_pow hx

/--
theorem `emultiplicity_pow_prime_sub_pow_prime` / 定理 `emultiplicity_pow_prime_sub_pow_prime`

English:
theorem emultiplicity_pow_prime_sub_pow_prime
  proof: by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_geom_sum₂_eq_one hp hp1 hxy hx]; rw [add_comm]

中文:
定理 emultiplicity_pow_prime_sub_pow_prime
  证明: by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_geom_sum₂_eq_one hp hp1 hxy hx]; rw [add_comm]

Depends on / 依赖: add_comm, emultiplicity_mul
-/
theorem emultiplicity_pow_prime_sub_pow_prime :
    emultiplicity (↑p) (x ^ p - y ^ p) = emultiplicity (↑p) (x - y) + 1 := by
  rw [← geom_sum₂_mul]; rw [emultiplicity_mul hp]; rw [emultiplicity_geom_sum₂_eq_one hp hp1 hxy hx]; rw [add_comm]

/--
theorem `emultiplicity_pow_prime_pow_sub_pow_prime_pow` / 定理 `emultiplicity_pow_prime_pow_sub_pow_prime_pow`

English:
theorem emultiplicity_pow_prime_pow_sub_pow_prime_pow
  given: (a : Nat)
  proof: by
  induction a with
  | zero => rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
  | succ a h_ind =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [← add_assoc]; rw [← h_ind]; rw [pow_succ]; rw [pow_mul]; rw [pow_mul]
    apply emultiplicity_pow_prime_sub_pow_prime hp hp1
    · rw [← geom_s

中文:
定理 emultiplicity_pow_prime_pow_sub_pow_prime_pow
  条件: (a : 自然数)
  证明: by
  induction a with
  | zero => rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
  | succ a h_ind =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [← add_assoc]; rw [← h_ind]; rw [pow_succ]; rw [pow_mul]; rw [pow_mul]
    apply emultiplicity_pow_prime_sub_pow_prime hp hp1
    · rw [← geom_s

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero, cast_add, cast_one, cast_zero, dvd_mul_of_dvd_right, dvd_of_dvd_pow, emultiplicity_pow_prime_sub_pow_prime, h_ind, hp.dvd_of_dvd_pow, pow_mul, pow_one, pow_succ, pow_zero
-/
theorem emultiplicity_pow_prime_pow_sub_pow_prime_pow (a : Nat) :
    emultiplicity (↑p) (x ^ p ^ a - y ^ p ^ a) = emultiplicity (↑p) (x - y) + a := by
  induction a with
  | zero => rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
  | succ a h_ind =>
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [← add_assoc]; rw [← h_ind]; rw [pow_succ]; rw [pow_mul]; rw [pow_mul]
    apply emultiplicity_pow_prime_sub_pow_prime hp hp1
    · rw [← geom_sum₂_mul]
      exact dvd_mul_of_dvd_right hxy _
    · exact fun h => hx (hp.dvd_of_dvd_pow h)

end IntegralDomain

section LiftingTheExponent

variable (hp : Nat.Prime p) (hp1 : Odd p)
include hp hp1

/--
theorem `Int.emultiplicity_pow_sub_pow` / 定理 `Int.emultiplicity_pow_sub_pow`

English:
theorem Int.emultiplicity_pow_sub_pow
  given: {x y : Int} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : Nat)
  proof: by
  rcases n with - | n
  · simp only [emultiplicity_zero, add_top, pow_zero, sub_self]
  have h : FiniteMultiplicity _ _ := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, 

中文:
定理 整数.emultiplicity_pow_sub_pow
  条件: {x y : 整数} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : 自然数)
  证明: by
  rcases n with - | n
  · simp only [emultiplicity_zero, add_top, pow_zero, sub_self]
  have h : FiniteMultiplicity _ _ := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, 

Depends on / 依赖: FiniteMultiplicity, Nat.finiteMultiplicity_iff.mpr, Nat.prime_iff_prime_int, Nat.succ_eq_add_one, add_top, conv_lhs, emultiplicity_eq, emultiplicity_eq_coe, emultiplicity_eq_coe.mp, emultiplicity_eq_multiplicity, emultiplicity_pow_prime_pow_sub_pow_prime_pow, emultiplicity_pow_sub_pow_of_prime, emultiplicity_zero, finiteMultiplicity_iff, h.emultiplicity_eq, h.emultiplicity_eq_multiplicity, hp.ne_one, n.succ_pos, ne_one, pow_mul
-/
theorem Int.emultiplicity_pow_sub_pow {x y : Int} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : Nat) :
    emultiplicity (↑p) (x ^ n - y ^ n) = emultiplicity (↑p) (x - y) + emultiplicity p n := by
  rcases n with - | n
  · simp only [emultiplicity_zero, add_top, pow_zero, sub_self]
  have h : FiniteMultiplicity _ _ := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  conv_lhs => rw [hk, pow_mul, pow_mul]
  rw [Nat.prime_iff_prime_int] at hp
  rw [emultiplicity_pow_sub_pow_of_prime hp]; rw [emultiplicity_pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx]; rw [h.emultiplicity_eq_multiplicity]
  · rw [← geom_sum₂_mul]
    exact dvd_mul_of_dvd_right hxy
  · exact fun h => hx (hp.dvd_of_dvd_pow h)
  · rw [Int.natCast_dvd_natCast]
    rintro ⟨c, rfl⟩
    refine hpn ⟨c, ?_⟩
    rwa [pow_succ, mul_assoc]

/--
theorem `Int.emultiplicity_pow_add_pow` / 定理 `Int.emultiplicity_pow_add_pow`

English:
theorem Int.emultiplicity_pow_add_pow
  statement: {x y : Int} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x)
  proof: by
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add]; rw [← sub_neg_eq_add]; rw [← Odd.neg_pow hn]
  exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n

中文:
定理 整数.emultiplicity_pow_add_pow
  结论: {x y : 整数} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x)
  证明: by
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add]; rw [← sub_neg_eq_add]; rw [← Odd.neg_pow hn]
  exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n

Depends on / 依赖: Int.emultiplicity_pow_sub_pow, Odd.neg_pow, emultiplicity_pow_sub_pow, neg_pow, sub_neg_eq_add
-/
theorem Int.emultiplicity_pow_add_pow {x y : Int} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x)
    {n : Nat} (hn : Odd n) :
    emultiplicity (↑p) (x ^ n + y ^ n) = emultiplicity (↑p) (x + y) + emultiplicity p n := by
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add]; rw [← sub_neg_eq_add]; rw [← Odd.neg_pow hn]
  exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n

/--
theorem `Nat.emultiplicity_pow_sub_pow` / 定理 `Nat.emultiplicity_pow_sub_pow`

English:
theorem Nat.emultiplicity_pow_sub_pow
  given: {x y : Nat} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : Nat)
  proof: by
  obtain hyx | hyx := le_total y x
  · iterate 2 rw [← Int.natCast_emultiplicity]
    rw [Int.ofNat_sub (Nat.pow_le_pow_left hyx n)]
    rw [← Int.natCast_dvd_natCast] at hxy hx
    rw [Int.natCast_sub hyx] at *
    push_cast at *
    exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
  · simp o

中文:
定理 自然数.emultiplicity_pow_sub_pow
  条件: {x y : 自然数} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : 自然数)
  证明: by
  obtain hyx | hyx := le_total y x
  · iterate 2 rw [← Int.natCast_emultiplicity]
    rw [Int.ofNat_sub (Nat.pow_le_pow_left hyx n)]
    rw [← Int.natCast_dvd_natCast] at hxy hx
    rw [Int.natCast_sub hyx] at *
    push_cast at *
    exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
  · simp o

Depends on / 依赖: Int.emultiplicity_pow_sub_pow, Int.natCast_dvd_natCast, Int.natCast_emultiplicity, Int.natCast_sub, Int.ofNat_sub, Nat.pow_le_pow_left, Nat.sub_eq_zero_iff_le.mpr, emultiplicity_pow_sub_pow, emultiplicity_zero, iterate, le_total, natCast_dvd_natCast, natCast_emultiplicity, natCast_sub, ofNat_sub, pow_le_pow_left, sub_eq_zero_iff_le, top_add
-/
theorem Nat.emultiplicity_pow_sub_pow {x y : Nat} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : Nat) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) + emultiplicity p n := by
  obtain hyx | hyx := le_total y x
  · iterate 2 rw [← Int.natCast_emultiplicity]
    rw [Int.ofNat_sub (Nat.pow_le_pow_left hyx n)]
    rw [← Int.natCast_dvd_natCast] at hxy hx
    rw [Int.natCast_sub hyx] at *
    push_cast at *
    exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
  · simp only [Nat.sub_eq_zero_iff_le.mpr (Nat.pow_le_pow_left hyx n), emultiplicity_zero,
    Nat.sub_eq_zero_iff_le.mpr hyx, top_add]

/--
theorem `Nat.emultiplicity_pow_add_pow` / 定理 `Nat.emultiplicity_pow_add_pow`

English:
theorem Nat.emultiplicity_pow_add_pow
  statement: {x y : Nat} (hxy : p ∣ x + y) (hx : ¬p ∣ x)
  proof: by
  iterate 2 rw [← Int.natCast_emultiplicity]
  rw [← Int.natCast_dvd_natCast] at hxy hx
  push_cast at *
  exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

中文:
定理 自然数.emultiplicity_pow_add_pow
  结论: {x y : 自然数} (hxy : p ∣ x + y) (hx : ¬p ∣ x)
  证明: by
  iterate 2 rw [← Int.natCast_emultiplicity]
  rw [← Int.natCast_dvd_natCast] at hxy hx
  push_cast at *
  exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

Depends on / 依赖: Int.emultiplicity_pow_add_pow, Int.natCast_dvd_natCast, Int.natCast_emultiplicity, emultiplicity_pow_add_pow, iterate, natCast_dvd_natCast, natCast_emultiplicity
-/
theorem Nat.emultiplicity_pow_add_pow {x y : Nat} (hxy : p ∣ x + y) (hx : ¬p ∣ x)
    {n : Nat} (hn : Odd n) :
    emultiplicity p (x ^ n + y ^ n) = emultiplicity p (x + y) + emultiplicity p n := by
  iterate 2 rw [← Int.natCast_emultiplicity]
  rw [← Int.natCast_dvd_natCast] at hxy hx
  push_cast at *
  exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

end LiftingTheExponent

end CommRing

/--
theorem `pow_two_pow_sub_pow_two_pow` / 定理 `pow_two_pow_sub_pow_two_pow`

English:
theorem pow_two_pow_sub_pow_two_pow
  given: [CommRing R] {x y : R} (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul]
  | succ d hd =>
    suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this]; rw [hd]; rw [Finset.prod_range_succ]; rw [← mul_assoc]; rw [mul_comm 

中文:
定理 pow_two_pow_sub_pow_two_pow
  条件: [交换环 R] {x y : R} (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul]
  | succ d hd =>
    suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this]; rw [hd]; rw [Finset.prod_range_succ]; rw [← mul_assoc]; rw [mul_comm 

Depends on / 依赖: Finset, Finset.prod_range_succ, Nat.succ_eq_add_one, d.succ, mul_assoc, mul_comm, one_mul, pow_one, pow_zero, prod_empty, prod_range_succ, range_zero, succ_eq_add_one
-/
theorem pow_two_pow_sub_pow_two_pow [CommRing R] {x y : R} (n : Nat) :
    x ^ 2 ^ n - y ^ 2 ^ n = (∏ i in Finset.range n, (x ^ 2 ^ i + y ^ 2 ^ i)) * (x - y) := by
  induction n with
  | zero => simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul]
  | succ d hd =>
    suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this]; rw [hd]; rw [Finset.prod_range_succ]; rw [← mul_assoc]; rw [mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)]
    rw [Nat.succ_eq_add_one]
    ring

/--
theorem `Int.sq_mod_four_eq_one_of_odd` / 定理 `Int.sq_mod_four_eq_one_of_odd`

English:
theorem Int.sq_mod_four_eq_one_of_odd
  given: {x : Int}
  statement: Odd x -> x ^ 2 % 4 = 1
  proof: by
  intro hx
  unfold Odd at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  rw [add_assoc]; rw [← add_mul]; rw [Int.add_mul_emod_self_right]
  decide

中文:
定理 整数.sq_mod_four_eq_one_of_odd
  条件: {x : 整数}
  结论: Odd x -> x ^ 2 % 4 = 1
  证明: by
  intro hx
  unfold Odd at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  rw [add_assoc]; rw [← add_mul]; rw [Int.add_mul_emod_self_right]
  decide

Depends on / 依赖: Int.add_mul_emod_self_right, add_assoc, add_mul, add_mul_emod_self_right, ring_nf
-/
theorem Int.sq_mod_four_eq_one_of_odd {x : Int} : Odd x -> x ^ 2 % 4 = 1 := by
  intro hx
  unfold Odd at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  rw [add_assoc]; rw [← add_mul]; rw [Int.add_mul_emod_self_right]
  decide

/--
lemma `Int.eight_dvd_sq_sub_one_of_odd` / 引理 `Int.eight_dvd_sq_sub_one_of_odd`

English:
lemma Int.eight_dvd_sq_sub_one_of_odd
  given: {k : Int} (hk : Odd k)
  statement: 8 ∣ k ^ 2 - 1
  proof: by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

中文:
引理 整数.eight_dvd_sq_sub_one_of_odd
  条件: {k : 整数} (hk : Odd k)
  结论: 8 ∣ k ^ 2 - 1
  证明: by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

Depends on / 依赖: four_ne_zero, mul_dvd_mul_iff_left, two_dvd_mul_add_one
-/
lemma Int.eight_dvd_sq_sub_one_of_odd {k : Int} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

/--
lemma `Nat.eight_dvd_sq_sub_one_of_odd` / 引理 `Nat.eight_dvd_sq_sub_one_of_odd`

English:
lemma Nat.eight_dvd_sq_sub_one_of_odd
  given: {k : Nat} (hk : Odd k)
  statement: 8 ∣ k ^ 2 - 1
  proof: by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by grind
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

中文:
引理 自然数.eight_dvd_sq_sub_one_of_odd
  条件: {k : 自然数} (hk : Odd k)
  结论: 8 ∣ k ^ 2 - 1
  证明: by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by grind
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

Depends on / 依赖: four_ne_zero, mul_dvd_mul_iff_left, two_dvd_mul_add_one
-/
lemma Nat.eight_dvd_sq_sub_one_of_odd {k : Nat} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by grind
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)

/--
theorem `Int.two_pow_two_pow_add_two_pow_two_pow` / 定理 `Int.two_pow_two_pow_add_two_pow_two_pow`

English:
theorem Int.two_pow_two_pow_add_two_pow_two_pow
  given: {x y : Int} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : Nat)
  proof: by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [pow_one, ← even_iff_two

中文:
定理 整数.two_pow_two_pow_add_two_pow_two_pow
  条件: {x y : 整数} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : 自然数)
  证明: by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [pow_one, ← even_iff_two

Depends on / 依赖: Int.dvd_iff_emod_eq_zero, Int.not_even_iff_odd, add_odd, dvd_iff_emod_eq_zero, dvd_trans, emultiplicity_eq_coe, emultiplicity_eq_coe.mpr, even_iff_two_dvd, even_iff_two_dvd.mpr, hx_odd, hx_odd.pow.add_odd, hx_odd.sub_even, hxy_even, hy_odd, hy_odd.pow, not_even_iff_odd, pow_one, sub_even
-/
theorem Int.two_pow_two_pow_add_two_pow_two_pow {x y : Int} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : Nat) :
    emultiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : Nat) := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [pow_one, ← even_iff_two_dvd]
    exact hx_odd.pow.add_odd hy_odd.pow
  rcases i with - | i
  · grind
  suffices forall x : Int, Odd x -> x ^ 2 ^ (i + 1) % 4 = 1 by
    rw [show (2 ^ (1 + 1) : Int) = 4 by simp]; rw [Int.dvd_iff_emod_eq_zero]; rw [Int.add_emod]; rw [this _ hx_odd]; rw [this _ hy_odd]
    decide
  intro x hx
  rw [pow_succ']; rw [mul_comm]; rw [pow_mul]; rw [Int.sq_mod_four_eq_one_of_odd hx.pow]

/--
theorem `Int.two_pow_two_pow_sub_pow_two_pow` / 定理 `Int.two_pow_two_pow_sub_pow_two_pow`

English:
theorem Int.two_pow_two_pow_sub_pow_two_pow
  given: {x y : Int} (n : Nat) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x)
  proof: by
  simp only [pow_two_pow_sub_pow_two_pow n, emultiplicity_mul Int.prime_two,
    Finset.emultiplicity_prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]

中文:
定理 整数.two_pow_two_pow_sub_pow_two_pow
  条件: {x y : 整数} (n : 自然数) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x)
  证明: by
  simp only [pow_two_pow_sub_pow_two_pow n, emultiplicity_mul Int.prime_two,
    Finset.emultiplicity_prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]

Depends on / 依赖: Finset, Finset.card_range, Finset.emultiplicity_prod, Finset.sum_const, Int.prime_two, Int.two_pow_two_pow_add_two_pow_two_pow, Nat.cast_one, add_comm, card_range, cast_one, emultiplicity_mul, emultiplicity_prod, nsmul_one, pow_two_pow_sub_pow_two_pow, prime_two, sum_const, two_pow_two_pow_add_two_pow_two_pow
-/
theorem Int.two_pow_two_pow_sub_pow_two_pow {x y : Int} (n : Nat) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ 2 ^ n - y ^ 2 ^ n) = emultiplicity 2 (x - y) + n := by
  simp only [pow_two_pow_sub_pow_two_pow n, emultiplicity_mul Int.prime_two,
    Finset.emultiplicity_prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]

/--
theorem `Int.two_pow_sub_pow'` / 定理 `Int.two_pow_sub_pow'`

English:
theorem Int.two_pow_sub_pow'
  given: {x y : Int} (n : Nat) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x)
  proof: by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  rcases n with - | n
  · simp only [pow_zero, sub_self, emultiplicity_zer

中文:
定理 整数.two_pow_sub_pow'
  条件: {x y : 整数} (n : 自然数) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x)
  证明: by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  rcases n with - | n
  · simp only [pow_zero, sub_self, emultiplicity_zer

Depends on / 依赖: FiniteMultiplicity, Int.not_even_iff_odd, Int.ofNat_zero, Nat.finiteMultiplicity_iff.mpr, Nat.succ_eq_add_one, add_top, dvd_trans, emultiplicity_eq_coe, emultiplicity_eq_coe.mp, emultiplicity_eq_mu, emultiplicity_zero, even_iff_two_dvd, even_iff_two_dvd.mpr, finiteMultiplicity_iff, h.emultiplicity_eq_mu, hx_odd, hx_odd.sub_even, hxy_even, hy_odd, n.succ
-/
theorem Int.two_pow_sub_pow' {x y : Int} (n : Nat) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 : Int) n := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  rcases n with - | n
  · simp only [pow_zero, sub_self, emultiplicity_zero, Int.ofNat_zero, add_top]
  have h : FiniteMultiplicity 2 n.succ := Nat.finiteMultiplicity_iff.mpr ⟨by simp, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  rw [hk]; rw [pow_mul]; rw [pow_mul]; rw [emultiplicity_pow_sub_pow_of_prime]; rw [Int.two_pow_two_pow_sub_pow_two_pow _ hxy hx]; rw [← hk]
  · norm_cast
    rw [h.emultiplicity_eq_multiplicity]
  · exact Int.prime_two
  · simpa only [even_iff_two_dvd] using hx_odd.pow.sub_odd hy_odd.pow
  · simpa only [even_iff_two_dvd, ← Int.not_even_iff_odd] using hx_odd.pow
  norm_cast
  contrapose hpn
  rw [pow_succ]
  conv_rhs => rw [hk]
  exact mul_dvd_mul_left _ hpn

/--
theorem `Int.two_pow_sub_pow` / 定理 `Int.two_pow_sub_pow`

English:
theorem Int.two_pow_sub_pow
  given: {x y : Int} {n : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n)
  proof: by
  have hy : Odd y := by
    rw [← even_iff_two_dvd]; rw [Int.not_even_iff_odd] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert! Even.add_odd hxy hx
    abel
  obtain ⟨d, rfl⟩ := hn
  simp only [← two_mul, pow_mul]
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
 

中文:
定理 整数.two_pow_sub_pow
  条件: {x y : 整数} {n : 自然数} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n)
  证明: by
  have hy : Odd y := by
    rw [← even_iff_two_dvd]; rw [Int.not_even_iff_odd] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert! Even.add_odd hxy hx
    abel
  obtain ⟨d, rfl⟩ := hn
  simp only [← two_mul, pow_mul]
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
 

Depends on / 依赖: Even.add_odd, Int.dvd_iff_emod_eq_zero, Int.not_even_iff_odd, Int.sq_mod_four_eq_one_of_odd, Int.sub_emod, Int.two_pow_su, add_odd, convert, dvd_iff_emod_eq_zero, even_iff_two_dvd, even_iff_two_dvd.mpr, even_neg, not_even_iff_odd, not_false_iff, pow_mul, replace, sq_mod_four_eq_one_of_odd, sub_emod, two_mul, two_pow_su
-/
theorem Int.two_pow_sub_pow {x y : Int} {n : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity (2 : Int) n := by
  have hy : Odd y := by
    rw [← even_iff_two_dvd]; rw [Int.not_even_iff_odd] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert! Even.add_odd hxy hx
    abel
  obtain ⟨d, rfl⟩ := hn
  simp only [← two_mul, pow_mul]
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
    rw [Int.dvd_iff_emod_eq_zero]; rw [Int.sub_emod]; rw [Int.sq_mod_four_eq_one_of_odd _]; rw [Int.sq_mod_four_eq_one_of_odd hy]
    · simp
    · simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]
  rw [Int.two_pow_sub_pow' d hxy4 _]; rw [sq_sub_sq]; rw [← Int.ofNat_mul_ofNat]; rw [emultiplicity_mul Int.prime_two]; rw [emultiplicity_mul Int.prime_two]
  · suffices emultiplicity (2 : Int) ↑(2 : Nat) = 1 by rw [this, add_comm 1, ← add_assoc]
    norm_cast
    rw [FiniteMultiplicity.emultiplicity_self]
    rw [Nat.finiteMultiplicity_iff]
    decide
  · rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    apply Odd.pow
    simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]

/--
theorem `Nat.two_pow_sub_pow` / 定理 `Nat.two_pow_sub_pow`

English:
theorem Nat.two_pow_sub_pow
  given: {x y : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} (hn : Even n)
  proof: by
  obtain hyx | hyx := le_total y x
  · iterate 3 rw [← Int.natCast_emultiplicity]
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_left' hyx _), Int.natCast_add,
      Int.natCast_pow]
    rw [← Int.natCast_dvd_natCast] at hx
    rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub hyx] a

中文:
定理 自然数.two_pow_sub_pow
  条件: {x y : 自然数} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : 自然数} (hn : Even n)
  证明: by
  obtain hyx | hyx := le_total y x
  · iterate 3 rw [← Int.natCast_emultiplicity]
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_left' hyx _), Int.natCast_add,
      Int.natCast_pow]
    rw [← Int.natCast_dvd_natCast] at hx
    rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub hyx] a

Depends on / 依赖: Int.natCast_add, Int.natCast_dvd_natCast, Int.natCast_emultiplicity, Int.natCast_pow, Int.ofNat_sub, Int.two_pow_sub_pow, Nat.sub_eq_zero_iff_le.mpr, add_t, convert, emultiplicity_zero, iterate, le_total, natCast_add, natCast_dvd_natCast, natCast_emultiplicity, natCast_pow, ofNat_sub, pow_le_pow_left, sub_eq_zero_iff_le, top_add
-/
theorem Nat.two_pow_sub_pow {x y : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity 2 n := by
  obtain hyx | hyx := le_total y x
  · iterate 3 rw [← Int.natCast_emultiplicity]
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_left' hyx _), Int.natCast_add,
      Int.natCast_pow]
    rw [← Int.natCast_dvd_natCast] at hx
    rw [← Int.natCast_dvd_natCast]; rw [Int.ofNat_sub hyx] at hxy
    convert! Int.two_pow_sub_pow hxy hx hn using 2
    rw [← Int.natCast_emultiplicity]
    rfl
  · simp only [Nat.sub_eq_zero_iff_le.mpr hyx,
      Nat.sub_eq_zero_iff_le.mpr (pow_le_pow_left' hyx n), emultiplicity_zero,
      top_add, add_top]

namespace padicValNat

variable {x y : Nat}

/--
theorem `pow_two_sub_pow` / 定理 `pow_two_sub_pow`

English:
theorem pow_two_sub_pow
  statement: (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} (hn : n != 0)
  proof: by
  simp only [← Nat.cast_inj (R := Nat∞), Nat.cast_add]
  iterate 4 rw [padicValNat_eq_emultiplicity]
  · exact Nat.two_pow_sub_pow hxy hx hneven
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · lia
  · simp [← Nat.pos_iff_ne_zero, tsub_pos_iff_lt, Nat.pow_lt_pow_left hyx hn]

中文:
定理 pow_two_sub_pow
  结论: (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : 自然数} (hn : n != 0)
  证明: by
  simp only [← Nat.cast_inj (R := Nat∞), Nat.cast_add]
  iterate 4 rw [padicValNat_eq_emultiplicity]
  · exact Nat.two_pow_sub_pow hxy hx hneven
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · lia
  · simp [← Nat.pos_iff_ne_zero, tsub_pos_iff_lt, Nat.pow_lt_pow_left hyx hn]

Depends on / 依赖: Nat.cast_add, Nat.cast_inj, Nat.pos_iff_ne_zero, Nat.pow_lt_pow_left, Nat.sub_ne_zero_of_lt, Nat.two_pow_sub_pow, cast_add, cast_inj, hneven, iterate, padicValNat_eq_emultiplicity, pos_iff_ne_zero, pow_lt_pow_left, sub_ne_zero_of_lt, tsub_pos_iff_lt, two_pow_sub_pow
-/
theorem pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} (hn : n != 0)
    (hneven : Even n) :
    padicValNat 2 (x ^ n - y ^ n) + 1 =
      padicValNat 2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n := by
  simp only [← Nat.cast_inj (R := Nat∞), Nat.cast_add]
  iterate 4 rw [padicValNat_eq_emultiplicity]
  · exact Nat.two_pow_sub_pow hxy hx hneven
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · lia
  · simp [← Nat.pos_iff_ne_zero, tsub_pos_iff_lt, Nat.pow_lt_pow_left hyx hn]

/--
theorem `pow_two_sub_one` / 定理 `pow_two_sub_one`

English:
theorem pow_two_sub_one
  given: {x n : Nat} (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n)
  proof: by
  simpa using pow_two_sub_pow h1x (by grind) hx hn hneven

中文:
定理 pow_two_sub_one
  条件: {x n : 自然数} (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n)
  证明: by
  simpa using pow_two_sub_pow h1x (by grind) hx hn hneven

Depends on / 依赖: hneven, pow_two_sub_pow
-/
theorem pow_two_sub_one {x n : Nat} (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n) :
    padicValNat 2 (x ^ n - 1) + 1 = padicValNat 2 (x + 1) +
    padicValNat 2 (x - 1) + padicValNat 2 n := by
  simpa using pow_two_sub_pow h1x (by grind) hx hn hneven

/--
lemma `pow_two_sub_one_ge` / 引理 `pow_two_sub_one_ge`

English:
lemma pow_two_sub_one_ge
  given: (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n)
  proof: by
  have : padicValNat 2 ((x + 1) * (x - 1)) >= 3 := by
    refine (padicValNat_dvd_iff_le (by grind [mul_ne_zero])).mp ?_
    simp [← Nat.pow_two_sub_pow_two x 1]
    grind [Nat.eight_dvd_sq_sub_one_of_odd]
  have := pow_two_sub_one h1x hx hn hneven
  grind [← padicValNat.mul]

中文:
引理 pow_two_sub_one_ge
  条件: (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n)
  证明: by
  have : padicValNat 2 ((x + 1) * (x - 1)) >= 3 := by
    refine (padicValNat_dvd_iff_le (by grind [mul_ne_zero])).mp ?_
    simp [← Nat.pow_two_sub_pow_two x 1]
    grind [Nat.eight_dvd_sq_sub_one_of_odd]
  have := pow_two_sub_one h1x hx hn hneven
  grind [← padicValNat.mul]

Depends on / 依赖: Nat.eight_dvd_sq_sub_one_of_odd, Nat.pow_two_sub_pow_two, eight_dvd_sq_sub_one_of_odd, hneven, mul_ne_zero, padicValNat, padicValNat.mul, padicValNat_dvd_iff_le, pow_two_sub_one, pow_two_sub_pow_two
-/
lemma pow_two_sub_one_ge (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n) :
    padicValNat 2 n + 2 <= padicValNat 2 (x ^ n - 1) := by
  have : padicValNat 2 ((x + 1) * (x - 1)) >= 3 := by
    refine (padicValNat_dvd_iff_le (by grind [mul_ne_zero])).mp ?_
    simp [← Nat.pow_two_sub_pow_two x 1]
    grind [Nat.eight_dvd_sq_sub_one_of_odd]
  have := pow_two_sub_one h1x hx hn hneven
  grind [← padicValNat.mul]

variable {p : Nat} [hp : Fact p.Prime] (hp1 : Odd p)
include hp hp1

/--
theorem `pow_sub_pow` / 定理 `pow_sub_pow`

English:
theorem pow_sub_pow
  given: (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : n != 0)
  proof: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_sub_pow hp.out hp1 hxy hx n
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx hn)

中文:
定理 pow_sub_pow
  条件: (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : 自然数} (hn : n != 0)
  证明: by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_sub_pow hp.out hp1 hxy hx n
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx hn)

Depends on / 依赖: Nat.cast_add, Nat.cast_inj, Nat.emultiplicity_pow_sub_pow, Nat.pow_lt_pow_left, Nat.sub_ne_zero_of_lt, cast_add, cast_inj, emultiplicity_pow_sub_pow, hp.out, iterate, padicValNat_eq_emultiplicity, pow_lt_pow_left, sub_ne_zero_of_lt
-/
theorem pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : n != 0) :
    padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p n := by
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_sub_pow hp.out hp1 hxy hx n
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx hn)

/--
theorem `pow_add_pow` / 定理 `pow_add_pow`

English:
theorem pow_add_pow
  given: (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : Nat} (hn : Odd n)
  proof: by
  rcases y with - | y
  · contradiction
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_add_pow hp.out hp1 hxy hx hn
  · exact (Odd.pos hn).ne'
  · simp
  · exact (Nat.lt_add_left _ (pow_pos y.succ_pos _)).ne'

中文:
定理 pow_add_pow
  条件: (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : 自然数} (hn : Odd n)
  证明: by
  rcases y with - | y
  · contradiction
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_add_pow hp.out hp1 hxy hx hn
  · exact (Odd.pos hn).ne'
  · simp
  · exact (Nat.lt_add_left _ (pow_pos y.succ_pos _)).ne'

Depends on / 依赖: Nat.cast_add, Nat.cast_inj, Nat.emultiplicity_pow_add_pow, Nat.lt_add_left, Odd.pos, cast_add, cast_inj, emultiplicity_pow_add_pow, hp.out, iterate, lt_add_left, padicValNat_eq_emultiplicity, pow_pos, succ_pos, y.succ_pos
-/
theorem pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : Nat} (hn : Odd n) :
    padicValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n := by
  rcases y with - | y
  · contradiction
  rw [← Nat.cast_inj (R := Nat∞)]; rw [Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_add_pow hp.out hp1 hxy hx hn
  · exact (Odd.pos hn).ne'
  · simp
  · exact (Nat.lt_add_left _ (pow_pos y.succ_pos _)).ne'

end padicValNat
