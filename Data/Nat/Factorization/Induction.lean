/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Data.Nat.Factorization.Defs

/-!
# Induction principles involving factorizations
-/

@[expose] public section

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : Nat}

/-! ## Definitions -/


/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_elim]
/--
Definition of `recOnPrimePow` / `recOnPrimePow` 的定义

English:
definition recOnPrimePow
  signature: {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)
  body: Nat.strongRec fun n =>
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _

中文:
定义 recOnPrimePow
  签名: {motive : 自然数 -> 类型层*} (zero : motive 0) (one : motive 1)
  定义体: Nat.strongRec fun n =>
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _

Depends on / 依赖: Nat.div_lt_of_lt_mul, Nat.dvd_div_iff_mul, Nat.mul_div_cancel, Nat.strongRec, convert, div_lt_of_lt_mul, dvd_div_iff_mul, factorization, factorization_pos_of_dvd, hp.factorization_pos_of_dvd, minFac, minFac_dvd, minFac_prime, mul_div_cancel, ordProj_dvd, prime_pow_mul, strongRec, succ_ne_zero, succ_succ_ne_one
-/
def recOnPrimePow {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)
    (prime_pow_mul : forall a p n : Nat, p.Prime -> ¬p ∣ a -> 0 < n -> motive a -> motive (p ^ n * a)) :
    forall a, motive a :=
  Nat.strongRec fun n =>
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _
      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd
      convert! prime_pow_mul ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1
      · rw [Nat.mul_div_cancel' hpt]
      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
      · simp [htp.ne', hp.one_lt]

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/--
Definition of `recOnPosPrimePosCoprime` / `recOnPosPrimePosCoprime` 的定义

English:
definition recOnPosPrimePosCoprime
  signature: {motive : Nat -> Sort*}
  body: recOnPrimePow zero one by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact prime_pow p n hp' hn
    refine coprime (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_
      (prime_pow _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (

中文:
定义 recOnPosPrimePosCoprime
  签名: {motive : 自然数 -> 类型层*}
  定义体: recOnPrimePow zero one by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact prime_pow p n hp' hn
    refine coprime (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_
      (prime_pow _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (

Depends on / 依赖: Prime.coprime_iff_not_dvd, contrapose, coprime, coprime_iff_not_dvd, hn.ne, le_self_pow, lt_of_le_of_ne, lt_one_iff, mul_one, one_lt, one_lt.trans_le, prime_pow, recOnPrimePow, trans_le
-/
def recOnPosPrimePosCoprime {motive : Nat -> Sort*}
    (prime_pow : forall p n : Nat, Prime p -> 0 < n -> motive (p ^ n))
    (zero : motive 0) (one : motive 1)
    (coprime : forall a b, 1 < a -> 1 < b -> Coprime a b -> motive a -> motive b -> motive (a * b)) :
    forall a, motive a :=
recOnPrimePow zero one by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact prime_pow p n hp' hn
    refine coprime (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_
      (prime_pow _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]
    · simpa [hn, Prime.coprime_iff_not_dvd hp']

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/--
Definition of `recOnPrimeCoprime` / `recOnPrimeCoprime` 的定义

English:
definition recOnPrimeCoprime
  signature: {motive : Nat -> Sort*} (zero : motive 0)
  body: recOnPosPrimePosCoprime (fun p n h _ => prime_pow p n h) zero (prime_pow 2 0 prime_two) coprime

中文:
定义 recOnPrimeCoprime
  签名: {motive : 自然数 -> 类型层*} (zero : motive 0)
  定义体: recOnPosPrimePosCoprime (fun p n h _ => prime_pow p n h) zero (prime_pow 2 0 prime_two) coprime

Depends on / 依赖: coprime, prime_pow, prime_two, recOnPosPrimePosCoprime
-/
def recOnPrimeCoprime {motive : Nat -> Sort*} (zero : motive 0)
    (prime_pow : forall p n : Nat, Prime p -> motive (p ^ n))
    (coprime : forall a b, 1 < a -> 1 < b -> Coprime a b -> motive a -> motive b -> motive (a * b)) :
    forall a, motive a :=
  recOnPosPrimePosCoprime (fun p n h _ => prime_pow p n h) zero (prime_pow 2 0 prime_two) coprime

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/--
Definition of `recOnMul` / `recOnMul` 的定义

English:
definition recOnMul
  signature: {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)
  body: recOnPrimeCoprime zero
    (fun p n hp' => Nat.rec one (fun _ ih => mul _ _ ih (prime p hp')) n)
    (fun a b _ _ _ => mul a b)

中文:
定义 recOnMul
  签名: {motive : 自然数 -> 类型层*} (zero : motive 0) (one : motive 1)
  定义体: recOnPrimeCoprime zero
    (fun p n hp' => Nat.rec one (fun _ ih => mul _ _ ih (prime p hp')) n)
    (fun a b _ _ _ => mul a b)

Depends on / 依赖: Nat.rec, recOnPrimeCoprime
-/
def recOnMul {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1)
    (prime : forall p, Prime p -> motive p)
    (mul : forall a b, motive a -> motive b -> motive (a * b)) : forall a, motive a :=
  recOnPrimeCoprime zero
    (fun p n hp' => Nat.rec one (fun _ ih => mul _ _ ih (prime p hp')) n)
    (fun a b _ _ _ => mul a b)

/--
lemma `_root_.induction_on_primes` / 引理 `_root_.induction_on_primes`

English:
lemma _root_.induction_on_primes
  statement: {motive : Nat -> Prop} (zero : motive 0) (one : motive 1)
  proof: by
  refine recOnPrimePow zero one ?_
  rintro a p n hp - - ha
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ']; rw [mul_assoc]
    exact prime_mul _ _ hp ih

中文:
引理 _root_.induction_on_primes
  结论: {motive : 自然数 -> 命题} (zero : motive 0) (one : motive 1)
  证明: by
  refine recOnPrimePow zero one ?_
  rintro a p n hp - - ha
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ']; rw [mul_assoc]
    exact prime_mul _ _ hp ih

Depends on / 依赖: mul_assoc, pow_succ, prime_mul, recOnPrimePow
-/
lemma _root_.induction_on_primes {motive : Nat -> Prop} (zero : motive 0) (one : motive 1)
    (prime_mul : forall p a : Nat, p.Prime -> motive a -> motive (p * a)) : forall n, motive n := by
  refine recOnPrimePow zero one ?_
  rintro a p n hp - - ha
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ']; rw [mul_assoc]
    exact prime_mul _ _ hp ih

/--
lemma `prime_composite_induction` / 引理 `prime_composite_induction`

English:
lemma prime_composite_induction
  statement: {motive : Nat -> Prop} (zero : motive 0) (one : motive 1)
  proof: by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

中文:
引理 prime_composite_induction
  结论: {motive : 自然数 -> 命题} (zero : motive 0) (one : motive 1)
  证明: by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

Depends on / 依赖: a.one_lt_succ_succ, composite, hp.two_le, induction_on_primes, one_lt_succ_succ, two_le
-/
lemma prime_composite_induction {motive : Nat -> Prop} (zero : motive 0) (one : motive 1)
    (prime : forall p : Nat, p.Prime -> motive p)
    (composite : forall a, 2 <= a -> motive a -> forall b, 2 <= b -> motive b -> motive (a * b))
    (n : Nat) : motive n := by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

/-! ## Lemmas on multiplicative functions -/

/--
theorem `multiplicative_factorization` / 定理 `multiplicative_factorization`

English:
theorem multiplicative_factorization
  statement: {β : Type*} [CommMonoid β] (f : Nat -> β)
  proof: by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
  · simp
  · rintro -
    rw [factorization_one]; rw [hf]
    simp
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab]; rw [ha (left_ne_zero_of_mul hab_pos)]; r

中文:
定理 multiplicative_factorization
  结论: {β : 类型} [交换幺半群 β] (f : 自然数 -> β)
  证明: by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
  · simp
  · rintro -
    rw [factorization_one]; rw [hf]
    simp
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab]; rw [ha (left_ne_zero_of_mul hab_pos)]; r

Depends on / 依赖: Finsupp, Finsupp.prod_single_index, Nat.recOnPosPrimePosCoprime, Prime.factorization_pow, disjoint_primeFactors, factorization_mul_of_coprime, factorization_one, factorization_pow, h_mult, hab.disjoint_primeFactors, hab_pos, left_ne_zero_of_mul, prod_add_index_of_disjoint, prod_single_index, recOnPosPrimePosCoprime, right_ne_zero_of_mul
-/
theorem multiplicative_factorization {β : Type*} [CommMonoid β] (f : Nat -> β)
    (h_mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y) (hf : f 1 = 1) :
    forall {n : Nat}, n != 0 -> f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
  · simp
  · rintro -
    rw [factorization_one]; rw [hf]
    simp
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab]; rw [ha (left_ne_zero_of_mul hab_pos)]; rw [hb (right_ne_zero_of_mul hab_pos)]; rw [factorization_mul_of_coprime hab]; rw [← prod_add_index_of_disjoint]
    exact hab.disjoint_primeFactors

/--
theorem `multiplicative_factorization'` / 定理 `multiplicative_factorization'`

English:
theorem multiplicative_factorization'
  statement: {β : Type*} [CommMonoid β] (f : Nat -> β)
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact multiplicative_factorization _ h_mult hf1 hn

中文:
定理 multiplicative_factorization'
  结论: {β : 类型} [交换幺半群 β] (f : 自然数 -> β)
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact multiplicative_factorization _ h_mult hf1 hn

Depends on / 依赖: eq_or_ne, h_mult, multiplicative_factorization
-/
theorem multiplicative_factorization' {β : Type*} [CommMonoid β] (f : Nat -> β)
    (h_mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
    f n = n.factorization.prod fun p k => f (p ^ k) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact multiplicative_factorization _ h_mult hf1 hn

end Nat
