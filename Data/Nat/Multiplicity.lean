/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.Choose.Factorization

/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `Nat.Prime.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n / p + ... + n / p ^ b` for any `b` such that `n / p ^ (b + 1) = 0`. See `padicValNat_factorial`
  for this result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial` for a related result.
* `Nat.Prime.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.Prime.multiplicity_choose`: Kummer's Theorem. The multiplicity of `p` in `n.choose k` is the
  number of carries when `k` and `n - k` are added in base `p`. See `padicValNat_choose` for the
  same result but stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` for a related result.

## Other declarations

* `Nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `Nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `Nat.Prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `Prime` and `Nat.Prime`.

## TODO

Derive results from the corresponding ones `Mathlib.Data.Nat.Factorization.Multiplicity`

## Tags

Legendre, p-adic
-/

public section

open Finset

namespace Nat

/--
theorem `emultiplicity_eq_card_pow_dvd` / 定理 `emultiplicity_eq_card_pow_dvd`

English:
theorem emultiplicity_eq_card_pow_dvd
  given: {m n b : Nat} (hm : m != 1) (hn : 0 < n) (hb : log m n < b)
  proof: have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    emultiplicity m n = #(Ico 1 <| multiplicity m n + 1) := by
      simp [fin.emultiplicity_eq_multiplicity]
    _ = #{i in Ico 1 b | m ^ i ∣ n} :=
congr_arg _
congr_arg card
          Finset.ext fun i => by
            simp only [mem_Ico, Na

中文:
定理 emultiplicity_eq_card_pow_dvd
  条件: {m n b : 自然数} (hm : m != 1) (hn : 0 < n) (hb : log m n < b)
  证明: have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    emultiplicity m n = #(Ico 1 <| multiplicity m n + 1) := by
      simp [fin.emultiplicity_eq_multiplicity]
    _ = #{i in Ico 1 b | m ^ i ∣ n} :=
congr_arg _
congr_arg card
          Finset.ext fun i => by
            simp only [mem_Ico, Na

Depends on / 依赖: Finset, Finset.ext, Nat.finiteMultiplicity_iff, Nat.lt_succ_iff, and_assoc, and_congr_right_iff, congr_arg, emultiplicity, emultiplicity_eq_multiplicity, exacts, fin.emultiplicity_eq_multiplicity, fin.pow_dvd_iff_le_multiplicity, finiteMultiplicity_iff, hn.ne, iff_and_self, lt_succ_iff, mem_Ico, mem_filter, multiplicity, pow_dvd_iff_le_multiplicity
-/
theorem emultiplicity_eq_card_pow_dvd {m n b : Nat} (hm : m != 1) (hn : 0 < n) (hb : log m n < b) :
    emultiplicity m n = #{i in Ico 1 b | m ^ i ∣ n} :=
  have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    emultiplicity m n = #(Ico 1 <| multiplicity m n + 1) := by
      simp [fin.emultiplicity_eq_multiplicity]
    _ = #{i in Ico 1 b | m ^ i ∣ n} :=
congr_arg _
congr_arg card
          Finset.ext fun i => by
            simp only [mem_Ico, Nat.lt_succ_iff,
              fin.pow_dvd_iff_le_multiplicity, mem_filter,
              and_assoc, and_congr_right_iff, iff_and_self]
            intro hi h
            rw [← fin.pow_dvd_iff_le_multiplicity] at h
            rcases m with - | m
            · rw [zero_pow, zero_dvd_iff] at h
              exacts [(hn.ne' h).elim, one_le_iff_ne_zero.1 hi]
            refine LE.le.trans_lt ?_ hb
            exact le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
                (le_of_dvd hn h)

namespace Prime

/--
theorem `emultiplicity_one` / 定理 `emultiplicity_one`

English:
theorem emultiplicity_one
  given: {p : Nat} (hp : p.Prime)
  statement: emultiplicity p 1 = 0
  proof: emultiplicity_of_one_right hp.prime.not_isUnit

中文:
定理 emultiplicity_one
  条件: {p : 自然数} (hp : p.Prime)
  结论: emultiplicity p 1 = 0
  证明: emultiplicity_of_one_right hp.prime.not_isUnit

Depends on / 依赖: emultiplicity_of_one_right, hp.prime.not_isUnit, not_isUnit
-/
theorem emultiplicity_one {p : Nat} (hp : p.Prime) : emultiplicity p 1 = 0 :=
  emultiplicity_of_one_right hp.prime.not_isUnit

/--
theorem `emultiplicity_mul` / 定理 `emultiplicity_mul`

English:
theorem emultiplicity_mul
  given: {p m n : Nat} (hp : p.Prime)
  proof: _root_.emultiplicity_mul hp.prime

中文:
定理 emultiplicity_mul
  条件: {p m n : 自然数} (hp : p.Prime)
  证明: _root_.emultiplicity_mul hp.prime

Depends on / 依赖: _root_, _root_.emultiplicity_mul, emultiplicity_mul, hp.prime
-/
theorem emultiplicity_mul {p m n : Nat} (hp : p.Prime) :
    emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n :=
  _root_.emultiplicity_mul hp.prime

/--
theorem `emultiplicity_pow` / 定理 `emultiplicity_pow`

English:
theorem emultiplicity_pow
  given: {p m n : Nat} (hp : p.Prime)
  proof: _root_.emultiplicity_pow hp.prime

中文:
定理 emultiplicity_pow
  条件: {p m n : 自然数} (hp : p.Prime)
  证明: _root_.emultiplicity_pow hp.prime

Depends on / 依赖: _root_, _root_.emultiplicity_pow, emultiplicity_pow, hp.prime
-/
theorem emultiplicity_pow {p m n : Nat} (hp : p.Prime) :
    emultiplicity p (m ^ n) = n * emultiplicity p m :=
  _root_.emultiplicity_pow hp.prime

/--
theorem `emultiplicity_self` / 定理 `emultiplicity_self`

English:
theorem emultiplicity_self
  given: {p : Nat} (hp : p.Prime)
  statement: emultiplicity p p = 1
  proof: (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, hp.pos⟩).emultiplicity_self

中文:
定理 emultiplicity_self
  条件: {p : 自然数} (hp : p.Prime)
  结论: emultiplicity p p = 1
  证明: (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, hp.pos⟩).emultiplicity_self

Depends on / 依赖: Nat.finiteMultiplicity_iff, emultiplicity_self, finiteMultiplicity_iff, hp.ne_one, hp.pos, ne_one
-/
theorem emultiplicity_self {p : Nat} (hp : p.Prime) : emultiplicity p p = 1 :=
  (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, hp.pos⟩).emultiplicity_self

/--
theorem `emultiplicity_pow_self` / 定理 `emultiplicity_pow_self`

English:
theorem emultiplicity_pow_self
  given: {p n : Nat} (hp : p.Prime)
  statement: emultiplicity p (p ^ n) = n
  proof: _root_.emultiplicity_pow_self hp.ne_zero hp.prime.not_isUnit n

中文:
定理 emultiplicity_pow_self
  条件: {p n : 自然数} (hp : p.Prime)
  结论: emultiplicity p (p ^ n) = n
  证明: _root_.emultiplicity_pow_self hp.ne_zero hp.prime.not_isUnit n

Depends on / 依赖: _root_, _root_.emultiplicity_pow_self, emultiplicity_pow_self, hp.ne_zero, hp.prime.not_isUnit, ne_zero, not_isUnit
-/
theorem emultiplicity_pow_self {p n : Nat} (hp : p.Prime) : emultiplicity p (p ^ n) = n :=
  _root_.emultiplicity_pow_self hp.ne_zero hp.prime.not_isUnit n

/--
theorem `emultiplicity_factorial` / 定理 `emultiplicity_factorial`

English:
theorem emultiplicity_factorial
  given: {p : Nat} (hp : p.Prime)
  proof: by
        rw [factorial_succ]; rw [hp.emultiplicity_mul]; rw [add_comm]
      _ = (∑ i in Ico 1 b, n / p ^ i : Nat) + #{i in Ico 1 b | p ^ i ∣ n + 1} := by
        rw [emultiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [←
          emultiplicity_eq_card_pow_dvd hp.ne_one (s

中文:
定理 emultiplicity_factorial
  条件: {p : 自然数} (hp : p.Prime)
  证明: by
        rw [factorial_succ]; rw [hp.emultiplicity_mul]; rw [add_comm]
      _ = (∑ i in Ico 1 b, n / p ^ i : Nat) + #{i in Ico 1 b | p ^ i ∣ n + 1} := by
        rw [emultiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [←
          emultiplicity_eq_card_pow_dvd hp.ne_one (s

Depends on / 依赖: Finset, Finset.sum_congr, Nat.s, add_comm, congr_arg, emultiplicity_eq_card_pow_dvd, emultiplicity_factorial, emultiplicity_mul, factorial_succ, hp.emultiplicity_mul, hp.ne_one, le_succ, log_mono_right, ne_one, succ_pos, sum_add_distrib, sum_boole, sum_congr, trans_lt
-/
theorem emultiplicity_factorial {p : Nat} (hp : p.Prime) :
    forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in Ico 1 b, n / p ^ i : Nat)
  | 0, b, _ => by simp [Ico, hp.emultiplicity_one]
  | n + 1, b, hb =>
    calc
      emultiplicity p (n + 1)! = emultiplicity p n ! + emultiplicity p (n + 1) := by
        rw [factorial_succ]; rw [hp.emultiplicity_mul]; rw [add_comm]
      _ = (∑ i in Ico 1 b, n / p ^ i : Nat) + #{i in Ico 1 b | p ^ i ∣ n + 1} := by
        rw [emultiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]; rw [←
          emultiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i in Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : Nat) := by
        rw [sum_add_distrib]; rw [sum_boole]
        simp
      _ = (∑ i in Ico 1 b, (n + 1) / p ^ i : Nat) :=
congr_arg _ Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/--
theorem `sub_one_mul_multiplicity_factorial` / 定理 `sub_one_mul_multiplicity_factorial`

English:
theorem sub_one_mul_multiplicity_factorial
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  simp only [multiplicity_eq_of_emultiplicity_eq_some <|
emultiplicity_factorial hp lt_succ_of_lt Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

中文:
定理 sub_one_mul_multiplicity_factorial
  条件: {n p : 自然数} (hp : p.Prime)
  证明: by
  simp only [multiplicity_eq_of_emultiplicity_eq_some <|
emultiplicity_factorial hp lt_succ_of_lt Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

Depends on / 依赖: Finset, Finset.sum_Ico_add, Ico_zero_eq_range, Nat.lt_add_one, emultiplicity_factorial, lt_add_one, lt_succ_of_lt, multiplicity_eq_of_emultiplicity_eq_some, sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, sum_Ico_add
-/
theorem sub_one_mul_multiplicity_factorial {n p : Nat} (hp : p.Prime) :
    (p - 1) * multiplicity p n ! =
    n - (p.digits n).sum := by
  simp only [multiplicity_eq_of_emultiplicity_eq_some <|
emultiplicity_factorial hp lt_succ_of_lt Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `emultiplicity_factorial_mul_succ` / 定理 `emultiplicity_factorial_mul_succ`

English:
theorem emultiplicity_factorial_mul_succ
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  have hp' := hp.prime
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have hm : emultiplicity p (p * n)! != ⊤ := by
    rw [Ne]; rw [emultiplicity_eq_top]; r

中文:
定理 emultiplicity_factorial_mul_succ
  条件: {n p : 自然数} (hp : p.Prime)
  证明: by
  have hp' := hp.prime
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have hm : emultiplicity p (p * n)! != ⊤ := by
    rw [Ne]; rw [emultiplicity_eq_top]; r

Depends on / 依赖: Classical, Classical.not_not, Nat.finiteMultiplicity_iff, Nat.le_add_left, emultiplicity, emultiplicity_eq_top, emultiplicity_eq_zer, factorial_pos, finiteMultiplicity_iff, hp.ne_one, hp.prime, hp.two_le, le_add_left, ne_one, not_not, revert, two_le
-/
theorem emultiplicity_factorial_mul_succ {n p : Nat} (hp : p.Prime) :
    emultiplicity p (p * (n + 1))! = emultiplicity p (p * n)! + emultiplicity p (n + 1) + 1 := by
  have hp' := hp.prime
  have h0 : 2 <= p := hp.two_le
  have h1 : 1 <= p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 <= p * (n + 1) := by linarith
  have h3 : p * n + 1 <= p * (n + 1) + 1 := by lia
  have hm : emultiplicity p (p * n)! != ⊤ := by
    rw [Ne]; rw [emultiplicity_eq_top]; rw [Classical.not_not]; rw [Nat.finiteMultiplicity_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  have h4 : forall m in Ico (p * n + 1) (p * (n + 1)), emultiplicity p m = 0 := by
    intro m hm
    rw [emultiplicity_eq_zero]; rw [not_dvd_iff_lt_mul_succ _ hp.pos]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, Finset.emultiplicity_prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  intro h
  rw [WithTop.add_left_inj h]; rw [sum_Ico_succ_top h2]; rw [hp.emultiplicity_mul]; rw [hp.emultiplicity_self]; rw [sum_congr rfl h4]; rw [sum_const_zero]; rw [zero_add]; rw [add_comm 1]

/--
theorem `emultiplicity_factorial_mul` / 定理 `emultiplicity_factorial_mul`

English:
theorem emultiplicity_factorial_mul
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [hp, emultiplicity_factorial_mul_succ, ih, factorial_succ, emultiplicity_mul,
      cast_add, cast_one, ← add_assoc]
    congr 1
    rw [add_comm]; rw [add_assoc]

中文:
定理 emultiplicity_factorial_mul
  条件: {n p : 自然数} (hp : p.Prime)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [hp, emultiplicity_factorial_mul_succ, ih, factorial_succ, emultiplicity_mul,
      cast_add, cast_one, ← add_assoc]
    congr 1
    rw [add_comm]; rw [add_assoc]

Depends on / 依赖: add_assoc, add_comm, cast_add, cast_one, emultiplicity_factorial_mul_succ, emultiplicity_mul, factorial_succ
-/
theorem emultiplicity_factorial_mul {n p : Nat} (hp : p.Prime) :
    emultiplicity p (p * n)! = emultiplicity p n ! + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [hp, emultiplicity_factorial_mul_succ, ih, factorial_succ, emultiplicity_mul,
      cast_add, cast_one, ← add_assoc]
    congr 1
    rw [add_comm]; rw [add_assoc]

/--
theorem `multiplicity_factorial_pow` / 定理 `multiplicity_factorial_pow`

English:
theorem multiplicity_factorial_pow
  given: {n p : Nat} (hp : p.Prime)
  proof: by
  rw [← ENat.natCast_inj]; rw [← (Nat.finiteMultiplicity_iff.2
      ⟨hp.ne_one]; rw [(p ^ n).factorial_pos⟩).emultiplicity_eq_multiplicity]
  induction n with
  | zero => simp [hp.emultiplicity_one]
  | succ n h =>
    rw [pow_succ']; rw [hp.emultiplicity_factorial_mul]; rw [h]; rw [Finset.sum_r

中文:
定理 multiplicity_factorial_pow
  条件: {n p : 自然数} (hp : p.Prime)
  证明: by
  rw [← ENat.natCast_inj]; rw [← (Nat.finiteMultiplicity_iff.2
      ⟨hp.ne_one]; rw [(p ^ n).factorial_pos⟩).emultiplicity_eq_multiplicity]
  induction n with
  | zero => simp [hp.emultiplicity_one]
  | succ n h =>
    rw [pow_succ']; rw [hp.emultiplicity_factorial_mul]; rw [h]; rw [Finset.sum_r

Depends on / 依赖: ENat.natCast_add, ENat.natCast_inj, Finset, Finset.sum_range_succ, Nat.finiteMultiplicity_iff, emultiplicity_eq_multiplicity, emultiplicity_factorial_mul, emultiplicity_one, factorial_pos, finiteMultiplicity_iff, hp.emultiplicity_factorial_mul, hp.emultiplicity_one, hp.ne_one, natCast_add, natCast_inj, ne_one, pow_succ, sum_range_succ
-/
theorem multiplicity_factorial_pow {n p : Nat} (hp : p.Prime) :
    multiplicity p (p ^ n).factorial = ∑ i in Finset.range n, p ^ i := by
  rw [← ENat.natCast_inj]; rw [← (Nat.finiteMultiplicity_iff.2
      ⟨hp.ne_one]; rw [(p ^ n).factorial_pos⟩).emultiplicity_eq_multiplicity]
  induction n with
  | zero => simp [hp.emultiplicity_one]
  | succ n h =>
    rw [pow_succ']; rw [hp.emultiplicity_factorial_mul]; rw [h]; rw [Finset.sum_range_succ]; rw [ENat.natCast_add]

/--
theorem `pow_dvd_factorial_iff` / 定理 `pow_dvd_factorial_iff`

English:
theorem pow_dvd_factorial_iff
  given: {p : Nat} {n r b : Nat} (hp : p.Prime) (hbn : log p n < b)
  proof: by
  rw [← ENat.natCast_le_natCast]; rw [← hp.emultiplicity_factorial hbn]; rw [pow_dvd_iff_le_emultiplicity]

中文:
定理 pow_dvd_factorial_iff
  条件: {p : 自然数} {n r b : 自然数} (hp : p.Prime) (hbn : log p n < b)
  证明: by
  rw [← ENat.natCast_le_natCast]; rw [← hp.emultiplicity_factorial hbn]; rw [pow_dvd_iff_le_emultiplicity]

Depends on / 依赖: ENat.natCast_le_natCast, emultiplicity_factorial, hp.emultiplicity_factorial, natCast_le_natCast, pow_dvd_iff_le_emultiplicity
-/
theorem pow_dvd_factorial_iff {p : Nat} {n r b : Nat} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r <= ∑ i in Ico 1 b, n / p ^ i := by
  rw [← ENat.natCast_le_natCast]; rw [← hp.emultiplicity_factorial hbn]; rw [pow_dvd_iff_le_emultiplicity]

/--
theorem `emultiplicity_factorial_le_div_pred` / 定理 `emultiplicity_factorial_le_div_pred`

English:
theorem emultiplicity_factorial_le_div_pred
  given: {p : Nat} (hp : p.Prime) (n : Nat)
  proof: by
  rw [hp.emultiplicity_factorial (lt_succ_self _)]
  apply WithTop.coe_mono
  exact Nat.geom_sum_Ico_le hp.two_le _ _

中文:
定理 emultiplicity_factorial_le_div_pred
  条件: {p : 自然数} (hp : p.Prime) (n : 自然数)
  证明: by
  rw [hp.emultiplicity_factorial (lt_succ_self _)]
  apply WithTop.coe_mono
  exact Nat.geom_sum_Ico_le hp.two_le _ _

Depends on / 依赖: Nat.geom_sum_Ico_le, WithTop, WithTop.coe_mono, coe_mono, emultiplicity_factorial, geom_sum_Ico_le, hp.emultiplicity_factorial, hp.two_le, lt_succ_self, two_le
-/
theorem emultiplicity_factorial_le_div_pred {p : Nat} (hp : p.Prime) (n : Nat) :
    emultiplicity p n ! <= (n / (p - 1) : Nat) := by
  rw [hp.emultiplicity_factorial (lt_succ_self _)]
  apply WithTop.coe_mono
  exact Nat.geom_sum_Ico_le hp.two_le _ _

/--
theorem `emultiplicity_choose'` / 定理 `emultiplicity_choose'`

English:
theorem emultiplicity_choose'
  given: {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) < b)
  proof: by
  have h₁ :
      emultiplicity p (choose (n + k) k) + emultiplicity p (k ! * n !) =
        #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + emultiplicity p (k ! * n !) := by
    rw [← hp.emultiplicity_mul]; rw [← mul_assoc]
    have := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_fa

中文:
定理 emultiplicity_choose'
  条件: {p n k b : 自然数} (hp : p.Prime) (hnb : log p (n + k) < b)
  证明: by
  have h₁ :
      emultiplicity p (choose (n + k) k) + emultiplicity p (k ! * n !) =
        #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + emultiplicity p (k ! * n !) := by
    rw [← hp.emultiplicity_mul]; rw [← mul_assoc]
    have := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_fa

Depends on / 依赖: add_tsub_cancel_right, choose_mul_factorial_mul_factorial, emultiplicity, emultiplicity_factorial, emultiplicity_mul, hp.emultiplicity_factorial, hp.emultiplicity_mul, le_add_left, log_mon, log_mono_right, mul_assoc, trans_lt
-/
theorem emultiplicity_choose' {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) < b) :
    emultiplicity p (choose (n + k) k) = #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} := by
  have h₁ :
      emultiplicity p (choose (n + k) k) + emultiplicity p (k ! * n !) =
        #{i in Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} + emultiplicity p (k ! * n !) := by
    rw [← hp.emultiplicity_mul]; rw [← mul_assoc]
    have := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [this]; rw [hp.emultiplicity_factorial hnb]; rw [hp.emultiplicity_mul]; rw [hp.emultiplicity_factorial ((log_mono_right (le_add_left k n)).trans_lt hnb)]; rw [hp.emultiplicity_factorial ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb))]; rw [multiplicity_choose_aux hp (le_add_left k n)]
    simp [add_comm]
  refine WithTop.add_right_cancel ?_ h₁
  apply finiteMultiplicity_iff_emultiplicity_ne_top.1
  exact Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, mul_pos (factorial_pos k) (factorial_pos n)⟩

/--
theorem `emultiplicity_choose` / 定理 `emultiplicity_choose`

English:
theorem emultiplicity_choose
  given: {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : log p n < b)
  proof: by
  have := Nat.sub_add_cancel hkn
  convert! @emultiplicity_choose' p (n - k) k b hp _
  · rw [this]
  exact this.symm ▸ hnb

中文:
定理 emultiplicity_choose
  条件: {p n k b : 自然数} (hp : p.Prime) (hkn : k <= n) (hnb : log p n < b)
  证明: by
  have := Nat.sub_add_cancel hkn
  convert! @emultiplicity_choose' p (n - k) k b hp _
  · rw [this]
  exact this.symm ▸ hnb

Depends on / 依赖: Nat.sub_add_cancel, convert, emultiplicity_choose, sub_add_cancel, this.symm
-/
theorem emultiplicity_choose {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : log p n < b) :
    emultiplicity p (choose n k) = #{i in Ico 1 b | p ^ i <= k % p ^ i + (n - k) % p ^ i} := by
  have := Nat.sub_add_cancel hkn
  convert! @emultiplicity_choose' p (n - k) k b hp _
  · rw [this]
  exact this.symm ▸ hnb

/--
theorem `emultiplicity_le_emultiplicity_choose_add` / 定理 `emultiplicity_le_emultiplicity_choose_add`

English:
theorem emultiplicity_le_emultiplicity_choose_add
  given: {p : Nat} (hp : p.Prime)

中文:
定理 emultiplicity_le_emultiplicity_choose_add
  条件: {p : 自然数} (hp : p.Prime)
-/
theorem emultiplicity_le_emultiplicity_choose_add {p : Nat} (hp : p.Prime) :
    forall n k : Nat, emultiplicity p n <= emultiplicity p (choose n k) + emultiplicity p k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    rw [← hp.emultiplicity_mul]
    refine emultiplicity_le_emultiplicity_of_dvd_right ?_
    rw [← add_one_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : Nat}

/--
theorem `emultiplicity_choose_prime_pow_add_emultiplicity` / 定理 `emultiplicity_choose_prime_pow_add_emultiplicity`

English:
theorem emultiplicity_choose_prime_pow_add_emultiplicity
  statement: (hp : p.Prime) (hkn : k <= p ^ n)
  proof: le_antisymm
    (by
      have hdisj :
        Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
          {i in Ico 1 n.succ | p ^ i ∣ k} := by
        simp +contextual [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [emultiplicity_

中文:
定理 emultiplicity_choose_prime_pow_add_emultiplicity
  结论: (hp : p.Prime) (hkn : k <= p ^ n)
  证明: le_antisymm
    (by
      have hdisj :
        Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
          {i in Ico 1 n.succ | p ^ i ∣ k} := by
        simp +contextual [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [emultiplicity_

Depends on / 依赖: Disjoint, Nat.cast_add, Nat.mod_lt, WithTop, WithTop.coe_mono, bot_lt, card_union_of_disjoint, cast_add, coe_mono, contextual, disjoint_right, dvd_iff_mod_eq_zero, emultiplicity_choose, emultiplicity_eq_card_pow_dvd, filter, hk0.bot_lt, hp.one_lt, hp.pos, le_antisymm, log_mono_right
-/
theorem emultiplicity_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k <= p ^ n)
    (hk0 : k != 0) : emultiplicity p (choose (p ^ n) k) + emultiplicity p k = n :=
  le_antisymm
    (by
      have hdisj :
        Disjoint {i in Ico 1 n.succ | p ^ i <= k % p ^ i + (p ^ n - k) % p ^ i}
          {i in Ico 1 n.succ | p ^ i ∣ k} := by
        simp +contextual [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [emultiplicity_choose hp hkn (lt_succ_self _)]; rw [emultiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn))]; rw [← Nat.cast_add]
      apply WithTop.coe_mono
      rw [log_pow hp.one_lt]; rw [← card_union_of_disjoint hdisj]; rw [filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le
        fun x => p ^ x <= k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
    (by rw [← hp.emultiplicity_pow_self]; exact emultiplicity_le_emultiplicity_choose_add hp _ _)

/--
theorem `emultiplicity_choose_prime_pow` / 定理 `emultiplicity_choose_prime_pow`

English:
theorem emultiplicity_choose_prime_pow
  given: {p n k : Nat} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0)
  proof: by
  push_cast
  rw [← emultiplicity_choose_prime_pow_add_emultiplicity hp hkn hk0]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [Nat.pos_of_ne_zero hk0⟩).emultiplicity_eq_multiplicity]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [choose_pos hkn⟩).emultiplicity_eq_multiplicity]
  norm_cast
  rw

中文:
定理 emultiplicity_choose_prime_pow
  条件: {p n k : 自然数} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0)
  证明: by
  push_cast
  rw [← emultiplicity_choose_prime_pow_add_emultiplicity hp hkn hk0]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [Nat.pos_of_ne_zero hk0⟩).emultiplicity_eq_multiplicity]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [choose_pos hkn⟩).emultiplicity_eq_multiplicity]
  norm_cast
  rw

Depends on / 依赖: Nat.add_sub_cancel_right, Nat.pos_of_ne_zero, add_sub_cancel_right, choose_pos, emultiplicity_choose_prime_pow_add_emultiplicity, emultiplicity_eq_multiplicity, finiteMultiplicity_iff, hp.ne_one, ne_one, pos_of_ne_zero
-/
theorem emultiplicity_choose_prime_pow {p n k : Nat} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0) :
    emultiplicity p (choose (p ^ n) k) = ↑(n - multiplicity p k) := by
  push_cast
  rw [← emultiplicity_choose_prime_pow_add_emultiplicity hp hkn hk0]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [Nat.pos_of_ne_zero hk0⟩).emultiplicity_eq_multiplicity]; rw [(finiteMultiplicity_iff.2 ⟨hp.ne_one]; rw [choose_pos hkn⟩).emultiplicity_eq_multiplicity]
  norm_cast
  rw [Nat.add_sub_cancel_right]

/--
theorem `dvd_choose_pow` / 定理 `dvd_choose_pow`

English:
theorem dvd_choose_pow
  given: (hp : Prime p) (hk : k != 0) (hkp : k != p ^ n)
  statement: p ∣ (p ^ n).choose k
  proof: by
  obtain hkp | hkp := hkp.symm.lt_or_gt
  · simp [choose_eq_zero_of_lt hkp]
refine emultiplicity_ne_zero.1 fun h => hkp.not_ge Nat.le_of_dvd hk.bot_lt ?_
  have H := hp.emultiplicity_choose_prime_pow_add_emultiplicity hkp.le hk
  rw [h]; rw [zero_add]; rw [emultiplicity_eq_coe] at H
  exact H.1

中文:
定理 dvd_choose_pow
  条件: (hp : Prime p) (hk : k != 0) (hkp : k != p ^ n)
  结论: p ∣ (p ^ n).choose k
  证明: by
  obtain hkp | hkp := hkp.symm.lt_or_gt
  · simp [choose_eq_zero_of_lt hkp]
refine emultiplicity_ne_zero.1 fun h => hkp.not_ge Nat.le_of_dvd hk.bot_lt ?_
  have H := hp.emultiplicity_choose_prime_pow_add_emultiplicity hkp.le hk
  rw [h]; rw [zero_add]; rw [emultiplicity_eq_coe] at H
  exact H.1

Depends on / 依赖: Nat.le_of_dvd, bot_lt, choose_eq_zero_of_lt, emultiplicity_choose_prime_pow_add_emultiplicity, emultiplicity_eq_coe, emultiplicity_ne_zero, hk.bot_lt, hkp.le, hkp.not_ge, hkp.symm.lt_or_gt, hp.emultiplicity_choose_prime_pow_add_emultiplicity, le_of_dvd, lt_or_gt, not_ge, zero_add
-/
theorem dvd_choose_pow (hp : Prime p) (hk : k != 0) (hkp : k != p ^ n) : p ∣ (p ^ n).choose k := by
  obtain hkp | hkp := hkp.symm.lt_or_gt
  · simp [choose_eq_zero_of_lt hkp]
refine emultiplicity_ne_zero.1 fun h => hkp.not_ge Nat.le_of_dvd hk.bot_lt ?_
  have H := hp.emultiplicity_choose_prime_pow_add_emultiplicity hkp.le hk
  rw [h]; rw [zero_add]; rw [emultiplicity_eq_coe] at H
  exact H.1

/--
theorem `dvd_choose_pow_iff` / 定理 `dvd_choose_pow_iff`

English:
theorem dvd_choose_pow_iff
  given: (hp : Prime p)
  statement: p ∣ (p ^ n).choose k ↔ k != 0 ∧ k != p ^ n
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simp [hp.ne_one] at h

中文:
定理 dvd_choose_pow_iff
  条件: (hp : Prime p)
  结论: p ∣ (p ^ n).choose k ↔ k != 0 ∧ k != p ^ n
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simp [hp.ne_one] at h

Depends on / 依赖: dvd_choose_pow, hp.ne_one, ne_one
-/
theorem dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k != 0 ∧ k != p ^ n := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simp [hp.ne_one] at h

end Prime

/--
theorem `emultiplicity_two_factorial_lt` / 定理 `emultiplicity_two_factorial_lt`

English:
theorem emultiplicity_two_factorial_lt
  statement: forall {n : Nat} (_ : n != 0), emultiplicity 2 n ! < n
  proof: by
  have h2 := prime_two.prime
  refine binaryRec ?_ ?_
· exact fun h => False.elim h rfl
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn
      simp only [ne_eq, bit_eq_zero_iff, true_and, Bool.not_eq_false] at h
      simp only [bit, h, cond_true, mul_zero, zero_add, factorial_one]
     

中文:
定理 emultiplicity_two_factorial_lt
  结论: 对任意 {n : 自然数} (_ : n != 0), emultiplicity 2 n ! < n
  证明: by
  have h2 := prime_two.prime
  refine binaryRec ?_ ?_
· exact fun h => False.elim h rfl
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn
      simp only [ne_eq, bit_eq_zero_iff, true_and, Bool.not_eq_false] at h
      simp only [bit, h, cond_true, mul_zero, zero_add, factorial_one]
     

Depends on / 依赖: Bool.not_eq_false, False.elim, Ne.sym, Prime.emultiplicity_one, WithTop, WithTop.add_lt_add_right, add_lt_add_right, binaryRec, bit_eq_zero_iff, cond_true, emultiplicity, emultiplicity_factorial_mul, emultiplicity_one, factorial_one, mul_zero, ne_eq, not_eq_false, prime_two, prime_two.emultiplicity_factorial_mul, prime_two.prime
-/
theorem emultiplicity_two_factorial_lt : forall {n : Nat} (_ : n != 0), emultiplicity 2 n ! < n := by
  have h2 := prime_two.prime
  refine binaryRec ?_ ?_
· exact fun h => False.elim h rfl
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn
      simp only [ne_eq, bit_eq_zero_iff, true_and, Bool.not_eq_false] at h
      simp only [bit, h, cond_true, mul_zero, zero_add, factorial_one]
      rw [Prime.emultiplicity_one]
      · exact zero_lt_one
      · decide
    have : emultiplicity 2 (2 * n)! < (2 * n : Nat) := by
      rw [prime_two.emultiplicity_factorial_mul]
      rw [two_mul]
      push_cast
      apply WithTop.add_lt_add_right _ (ih hn)
      exact Ne.symm nofun
    cases b
    · simpa
    · suffices emultiplicity 2 (2 * n + 1) + emultiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [emultiplicity_mul, h2, prime_two, bit, factorial]
      rw [emultiplicity_eq_zero.2 (two_not_dvd_two_mul_add_one n)]; rw [zero_add]
      refine this.trans ?_
      exact mod_cast lt_succ_self _

end Nat
