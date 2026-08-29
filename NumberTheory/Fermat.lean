/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LucasPrimality

/-!
# Fermat numbers

The Fermat numbers are a sequence of natural numbers defined as `Nat.fermatNumber n = 2^(2^n) + 1`,
for all natural numbers `n`.

## Main theorems

- `Nat.coprime_fermatNumber_fermatNumber`: two distinct Fermat numbers are coprime.
- `Nat.pepin_primality`: For 0 < n, Fermat number Fₙ is prime if `3 ^ (2 ^ (2 ^ n - 1)) = -1 mod Fₙ`
- `fermat_primeFactors_one_lt`: For 1 < n, Prime factors the Fermat number Fₙ are of
  form `k * 2 ^ (n + 2) + 1`.
-/

@[expose] public section

open Function

namespace Nat

open Finset Nat ZMod

/--
Definition of `fermatNumber` / `fermatNumber` 的定义

English:
definition fermatNumber
  signature: (n : Nat)
  body: 2 ^ (2 ^ n) + 1

中文:
定义 fermatNumber
  签名: (n : 自然数)
  定义体: 2 ^ (2 ^ n) + 1
-/
def fermatNumber (n : Nat) : Nat := 2 ^ (2 ^ n) + 1

/--
theorem `fermatNumber_zero` / 定理 `fermatNumber_zero`

English:
theorem fermatNumber_zero
  statement: fermatNumber 0 = 3
  proof: rfl

中文:
定理 fermatNumber_zero
  结论: fermatNumber 0 = 3
  证明: rfl
-/
@[simp] theorem fermatNumber_zero : fermatNumber 0 = 3 := rfl
/--
theorem `fermatNumber_one` / 定理 `fermatNumber_one`

English:
theorem fermatNumber_one
  statement: fermatNumber 1 = 5
  proof: rfl

中文:
定理 fermatNumber_one
  结论: fermatNumber 1 = 5
  证明: rfl
-/
@[simp] theorem fermatNumber_one : fermatNumber 1 = 5 := rfl
/--
theorem `fermatNumber_two` / 定理 `fermatNumber_two`

English:
theorem fermatNumber_two
  statement: fermatNumber 2 = 17
  proof: rfl

中文:
定理 fermatNumber_two
  结论: fermatNumber 2 = 17
  证明: rfl
-/
@[simp] theorem fermatNumber_two : fermatNumber 2 = 17 := rfl

/--
theorem `fermatNumber_strictMono` / 定理 `fermatNumber_strictMono`

English:
theorem fermatNumber_strictMono
  statement: StrictMono fermatNumber
  proof: by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, Nat.pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]

中文:
定理 fermatNumber_strictMono
  结论: 严格递增 fermatNumber
  证明: by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, Nat.pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]

Depends on / 依赖: Nat.pow_lt_pow_iff_right, add_lt_add_iff_right, fermatNumber, imp_self, one_lt_two, pow_lt_pow_iff_right
-/
theorem fermatNumber_strictMono : StrictMono fermatNumber := by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, Nat.pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]

/--
lemma `fermatNumber_mono` / 引理 `fermatNumber_mono`

English:
lemma fermatNumber_mono
  statement: Monotone fermatNumber
  proof: fermatNumber_strictMono.monotone

中文:
引理 fermatNumber_mono
  结论: 递增 fermatNumber
  证明: fermatNumber_strictMono.monotone

Depends on / 依赖: fermatNumber_strictMono, fermatNumber_strictMono.monotone, monotone
-/
lemma fermatNumber_mono : Monotone fermatNumber := fermatNumber_strictMono.monotone
/--
lemma `fermatNumber_injective` / 引理 `fermatNumber_injective`

English:
lemma fermatNumber_injective
  statement: Injective fermatNumber
  proof: fermatNumber_strictMono.injective

中文:
引理 fermatNumber_injective
  结论: 单射 fermatNumber
  证明: fermatNumber_strictMono.injective

Depends on / 依赖: fermatNumber_strictMono, fermatNumber_strictMono.injective, injective
-/
lemma fermatNumber_injective : Injective fermatNumber := fermatNumber_strictMono.injective

/--
lemma `three_le_fermatNumber` / 引理 `three_le_fermatNumber`

English:
lemma three_le_fermatNumber
  given: (n : Nat)
  statement: 3 <= fermatNumber n
  proof: fermatNumber_mono n.zero_le

中文:
引理 three_le_fermatNumber
  条件: (n : 自然数)
  结论: 3 <= fermatNumber n
  证明: fermatNumber_mono n.zero_le

Depends on / 依赖: fermatNumber_mono, n.zero_le, zero_le
-/
lemma three_le_fermatNumber (n : Nat) : 3 <= fermatNumber n := fermatNumber_mono n.zero_le
/--
lemma `two_lt_fermatNumber` / 引理 `two_lt_fermatNumber`

English:
lemma two_lt_fermatNumber
  given: (n : Nat)
  statement: 2 < fermatNumber n
  proof: three_le_fermatNumber _

中文:
引理 two_lt_fermatNumber
  条件: (n : 自然数)
  结论: 2 < fermatNumber n
  证明: three_le_fermatNumber _

Depends on / 依赖: three_le_fermatNumber
-/
lemma two_lt_fermatNumber (n : Nat) : 2 < fermatNumber n := three_le_fermatNumber _

/--
lemma `fermatNumber_ne_one` / 引理 `fermatNumber_ne_one`

English:
lemma fermatNumber_ne_one
  given: (n : Nat)
  statement: fermatNumber n != 1
  proof: by have := three_le_fermatNumber n; lia

中文:
引理 fermatNumber_ne_one
  条件: (n : 自然数)
  结论: fermatNumber n != 1
  证明: by have := three_le_fermatNumber n; lia

Depends on / 依赖: three_le_fermatNumber
-/
lemma fermatNumber_ne_one (n : Nat) : fermatNumber n != 1 := by have := three_le_fermatNumber n; lia

/--
theorem `odd_fermatNumber` / 定理 `odd_fermatNumber`

English:
theorem odd_fermatNumber
  given: (n : Nat)
  statement: Odd (fermatNumber n)
  proof: (even_two.pow_of_ne_zero (pow_pos two_pos n).ne').add_one

中文:
定理 odd_fermatNumber
  条件: (n : 自然数)
  结论: Odd (fermatNumber n)
  证明: (even_two.pow_of_ne_zero (pow_pos two_pos n).ne').add_one

Depends on / 依赖: add_one, even_two, even_two.pow_of_ne_zero, pow_of_ne_zero, pow_pos, two_pos
-/
theorem odd_fermatNumber (n : Nat) : Odd (fermatNumber n) :=
  (even_two.pow_of_ne_zero (pow_pos two_pos n).ne').add_one

/--
theorem `prod_fermatNumber` / 定理 `prod_fermatNumber`

English:
theorem prod_fermatNumber
  given: (n : Nat)
  statement: ∏ k in range n, fermatNumber k = fermatNumber n - 2
  proof: by
  induction n with | zero => rfl | succ n hn =>
  rw [prod_range_succ]; rw [hn]; rw [fermatNumber]; rw [fermatNumber]; rw [mul_comm]; rw [(show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by lia)]; rw [← sq_sub_sq]
  ring_nf
  lia

中文:
定理 prod_fermatNumber
  条件: (n : 自然数)
  结论: ∏ k in range n, fermatNumber k = fermatNumber n - 2
  证明: by
  induction n with | zero => rfl | succ n hn =>
  rw [prod_range_succ]; rw [hn]; rw [fermatNumber]; rw [fermatNumber]; rw [mul_comm]; rw [(show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by lia)]; rw [← sq_sub_sq]
  ring_nf
  lia

Depends on / 依赖: fermatNumber, mul_comm, prod_range_succ, ring_nf, sq_sub_sq
-/
theorem prod_fermatNumber (n : Nat) : ∏ k in range n, fermatNumber k = fermatNumber n - 2 := by
  induction n with | zero => rfl | succ n hn =>
  rw [prod_range_succ]; rw [hn]; rw [fermatNumber]; rw [fermatNumber]; rw [mul_comm]; rw [(show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by lia)]; rw [← sq_sub_sq]
  ring_nf
  lia

/--
theorem `fermatNumber_eq_prod_add_two` / 定理 `fermatNumber_eq_prod_add_two`

English:
theorem fermatNumber_eq_prod_add_two
  given: (n : Nat)
  proof: by
  rw [prod_fermatNumber]; rw [Nat.sub_add_cancel]
exact le_of_lt two_lt_fermatNumber _

中文:
定理 fermatNumber_eq_prod_add_two
  条件: (n : 自然数)
  证明: by
  rw [prod_fermatNumber]; rw [Nat.sub_add_cancel]
exact le_of_lt two_lt_fermatNumber _

Depends on / 依赖: Nat.sub_add_cancel, le_of_lt, prod_fermatNumber, sub_add_cancel, two_lt_fermatNumber
-/
theorem fermatNumber_eq_prod_add_two (n : Nat) :
    fermatNumber n = ∏ k in range n, fermatNumber k + 2 := by
  rw [prod_fermatNumber]; rw [Nat.sub_add_cancel]
exact le_of_lt two_lt_fermatNumber _

/--
theorem `fermatNumber_succ` / 定理 `fermatNumber_succ`

English:
theorem fermatNumber_succ
  given: (n : Nat)
  statement: fermatNumber (n + 1) = (fermatNumber n - 1) ^ 2 + 1
  proof: by
  rw [fermatNumber]; rw [pow_succ]; rw [mul_comm]; rw [pow_mul']; rw [fermatNumber]; rw [add_tsub_cancel_right]

中文:
定理 fermatNumber_succ
  条件: (n : 自然数)
  结论: fermatNumber (n + 1) = (fermatNumber n - 1) ^ 2 + 1
  证明: by
  rw [fermatNumber]; rw [pow_succ]; rw [mul_comm]; rw [pow_mul']; rw [fermatNumber]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, fermatNumber, mul_comm, pow_mul, pow_succ
-/
theorem fermatNumber_succ (n : Nat) : fermatNumber (n + 1) = (fermatNumber n - 1) ^ 2 + 1 := by
  rw [fermatNumber]; rw [pow_succ]; rw [mul_comm]; rw [pow_mul']; rw [fermatNumber]; rw [add_tsub_cancel_right]

/--
theorem `two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq` / 定理 `two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq`

English:
theorem two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq
  given: (n : Nat)
  proof: by
  simp only [fermatNumber, add_tsub_cancel_right]
  have : 0 <= 1 + 2 ^ (2 ^ n * 4) := le_add_left _ _
  ring_nf
  lia

中文:
定理 two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq
  条件: (n : 自然数)
  证明: by
  simp only [fermatNumber, add_tsub_cancel_right]
  have : 0 <= 1 + 2 ^ (2 ^ n * 4) := le_add_left _ _
  ring_nf
  lia

Depends on / 依赖: add_tsub_cancel_right, fermatNumber, le_add_left, ring_nf
-/
theorem two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq (n : Nat) :
    2 * (fermatNumber n - 1) ^ 2 <= (fermatNumber (n + 1)) ^ 2 := by
  simp only [fermatNumber, add_tsub_cancel_right]
  have : 0 <= 1 + 2 ^ (2 ^ n * 4) := le_add_left _ _
  ring_nf
  lia

/--
theorem `fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq` / 定理 `fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq`

English:
theorem fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq
  given: (n : Nat)
  proof: by
  simp only [fermatNumber, add_sub_self_right]
  rw [← add_sub_self_right (2 ^ 2 ^ (n + 2) + 1) <| 2 * 2 ^ 2 ^ (n + 1)]
  ring_nf

中文:
定理 fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq
  条件: (n : 自然数)
  证明: by
  simp only [fermatNumber, add_sub_self_right]
  rw [← add_sub_self_right (2 ^ 2 ^ (n + 2) + 1) <| 2 * 2 ^ 2 ^ (n + 1)]
  ring_nf

Depends on / 依赖: add_sub_self_right, fermatNumber, ring_nf
-/
theorem fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : Nat) :
    fermatNumber (n + 2) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  simp only [fermatNumber, add_sub_self_right]
  rw [← add_sub_self_right (2 ^ 2 ^ (n + 2) + 1) <| 2 * 2 ^ 2 ^ (n + 1)]
  ring_nf

end Nat

open Nat

/--
theorem `Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq` / 定理 `Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq`

English:
theorem Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq
  given: (n : Nat)
  proof: by
  rw [Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq]; rw [Nat.cast_sub two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq n]
  simp only [fermatNumber, push_cast, add_tsub_cancel_right]

中文:
定理 整数.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq
  条件: (n : 自然数)
  证明: by
  rw [Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq]; rw [Nat.cast_sub two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq n]
  simp only [fermatNumber, push_cast, add_tsub_cancel_right]

Depends on / 依赖: Nat.cast_sub, Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq, add_tsub_cancel_right, cast_sub, fermatNumber, fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq, two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq
-/
theorem Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : Nat) :
    (fermatNumber (n + 2) : Int) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  rw [Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq]; rw [Nat.cast_sub two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq n]
  simp only [fermatNumber, push_cast, add_tsub_cancel_right]

namespace Nat

open Finset
/--
theorem `coprime_fermatNumber_fermatNumber` / 定理 `coprime_fermatNumber_fermatNumber`

English:
theorem coprime_fermatNumber_fermatNumber
  given: {m n : Nat} (hmn : m != n)
  proof: by
  wlog hmn' : m < n
  · simpa only [coprime_comm] using this hmn.symm (by lia)
  let d := (fermatNumber m).gcd (fermatNumber n)
  have h_n : d ∣ fermatNumber n := gcd_dvd_right ..
  have h_m : d ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_left _ _).trans <| dvd_prod_of_mem _
 mem_range.mpr hmn').mp <| 

中文:
定理 coprime_fermatNumber_fermatNumber
  条件: {m n : 自然数} (hmn : m != n)
  证明: by
  wlog hmn' : m < n
  · simpa only [coprime_comm] using this hmn.symm (by lia)
  let d := (fermatNumber m).gcd (fermatNumber n)
  have h_n : d ∣ fermatNumber n := gcd_dvd_right ..
  have h_m : d ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_left _ _).trans <| dvd_prod_of_mem _
 mem_range.mpr hmn').mp <| 

Depends on / 依赖: Nat.dvd_add_right, coprime_comm, dvd_add_right, dvd_prime, dvd_prod_of_mem, fermatNumber, fermatNumber_eq_prod_add_two, gcd_dvd_left, gcd_dvd_right, h_two, hmn.symm, mem_range, mem_range.mpr, not_two_dvd_nat, odd_fermatNumber, prime_two, resolve_right
-/
theorem coprime_fermatNumber_fermatNumber {m n : Nat} (hmn : m != n) :
    Coprime (fermatNumber m) (fermatNumber n) := by
  wlog hmn' : m < n
  · simpa only [coprime_comm] using this hmn.symm (by lia)
  let d := (fermatNumber m).gcd (fermatNumber n)
  have h_n : d ∣ fermatNumber n := gcd_dvd_right ..
  have h_m : d ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_left _ _).trans <| dvd_prod_of_mem _
 mem_range.mpr hmn').mp <| fermatNumber_eq_prod_add_two _ ▸ h_n
  refine ((dvd_prime prime_two).mp h_m).resolve_right fun h_two => ?_
  exact (odd_fermatNumber _).not_two_dvd_nat (h_two ▸ h_n)

/--
lemma `pairwise_coprime_fermatNumber` / 引理 `pairwise_coprime_fermatNumber`

English:
lemma pairwise_coprime_fermatNumber
  proof: fun _m _n => coprime_fermatNumber_fermatNumber

中文:
引理 pairwise_coprime_fermatNumber
  证明: fun _m _n => coprime_fermatNumber_fermatNumber

Depends on / 依赖: coprime_fermatNumber_fermatNumber
-/
lemma pairwise_coprime_fermatNumber :
    Pairwise fun m n => Coprime (fermatNumber m) (fermatNumber n) :=
  fun _m _n => coprime_fermatNumber_fermatNumber

open ZMod

/--
theorem `pow_of_pow_add_prime` / 定理 `pow_of_pow_add_prime`

English:
theorem pow_of_pow_add_prime
  given: {a n : Nat} (ha : 1 < a) (hn : n != 0) (hP : (a ^ n + 1).Prime)
  proof: by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow]; rw [hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne']; rw [add_left_inj]; rw

中文:
定理 pow_of_pow_add_prime
  条件: {a n : 自然数} (ha : 1 < a) (hn : n != 0) (hP : (a ^ n + 1).素)
  证明: by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow]; rw [hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne']; rw [add_left_inj]; rw

Depends on / 依赖: Nat.lt_add_right, add_left_inj, dvd_iff_eq, exists_eq_two_pow_mul_odd, hP.dvd_iff_eq, hm.nat_add_dvd_pow_add_pow, lt_add_right, mul_one, nat_add_dvd_pow_add_pow, one_lt_pow, one_pow, pow_eq_self_iff, pow_mul, pow_ne_zero, replace, two_ne_zero
-/
theorem pow_of_pow_add_prime {a n : Nat} (ha : 1 < a) (hn : n != 0) (hP : (a ^ n + 1).Prime) :
    exists m : Nat, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow]; rw [hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne']; rw [add_left_inj]; rw [pow_eq_self_iff ha] at h
  rw [h]; rw [mul_one]

/--
lemma `pepin_primality` / 引理 `pepin_primality`

English:
lemma pepin_primality
  given: (n : Nat) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n)))
  proof: by
  have := Fact.mk (two_lt_fermatNumber n)
  unfold fermatNumber at h this
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq

中文:
引理 pepin_primality
  条件: (n : 自然数) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n)))
  证明: by
  have := Fact.mk (two_lt_fermatNumber n)
  unfold fermatNumber at h this
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq

Depends on / 依赖: Fact.mk, Nat.add_sub_cancel, Nat.mul_div_cancel, Nat.one_le_two_pow, Nat.prime_dvd_prime_iff_eq, Nat.sub_add_cancel, add_sub_cancel, dvd_of_dvd_pow, fermatNumber, hp1.dvd_of_dvd_pow, lucas_primality, mul_div_cancel, neg_one_sq, one_le_two_pow, pow_mul, pow_succ, prime_dvd_prime_iff_eq, prime_two, sub_add_cancel, two_lt_fermatNumber
-/
lemma pepin_primality (n : Nat) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  have := Fact.mk (two_lt_fermatNumber n)
  unfold fermatNumber at h this
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq]
  · intro p hp1 hp2
    rw [Nat.add_sub_cancel]; rw [(Nat.prime_dvd_prime_iff_eq hp1 prime_two).mp (hp1.dvd_of_dvd_pow hp2)]; rw [key]; rw [pow_succ]; rw [Nat.mul_div_cancel _ two_pos]; rw [← pow_succ]; rw [← key]; rw [h]
    exact neg_one_ne_one

/--
lemma `pepin_primality'` / 引理 `pepin_primality'`

English:
lemma pepin_primality'
  given: (n : Nat) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n)))
  proof: by
  apply pepin_primality
  rw [← h]
  congr
  rw [fermatNumber]; rw [add_tsub_cancel_right]; rw [Nat.pow_div Nat.one_le_two_pow Nat.zero_lt_two]

中文:
引理 pepin_primality'
  条件: (n : 自然数) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n)))
  证明: by
  apply pepin_primality
  rw [← h]
  congr
  rw [fermatNumber]; rw [add_tsub_cancel_right]; rw [Nat.pow_div Nat.one_le_two_pow Nat.zero_lt_two]

Depends on / 依赖: Nat.one_le_two_pow, Nat.pow_div, Nat.zero_lt_two, add_tsub_cancel_right, fermatNumber, one_le_two_pow, pepin_primality, pow_div, zero_lt_two
-/
lemma pepin_primality' (n : Nat) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  apply pepin_primality
  rw [← h]
  congr
  rw [fermatNumber]; rw [add_tsub_cancel_right]; rw [Nat.pow_div Nat.one_le_two_pow Nat.zero_lt_two]


/--
lemma `fermat_primeFactors_one_lt` / 引理 `fermat_primeFactors_one_lt`

English:
lemma fermat_primeFactors_one_lt
  statement: (n p : Nat) (hn : 1 < n) (hp : p.Prime)
  proof: by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p != 2 := by
    exact (even_two.pow_of_ne_zero <| pow_ne_zero n two_ne_zero).add_one.ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_

中文:
引理 fermat_primeFactors_one_lt
  结论: (n p : 自然数) (hn : 1 < n) (hp : p.素)
  证明: by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p != 2 := by
    exact (even_two.pow_of_ne_zero <| pow_ne_zero n two_ne_zero).add_one.ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_

Depends on / 依赖: Fact.mk, Nat.exists_eq_add_of_le, Or.inl, a.val, add_assoc, add_one, add_one.ne_two_of_dvd_nat, even_two, even_two.pow_of_ne_zero, exists_eq_add_of_le, exists_sq_eq_two_iff, mod_add_mod, mul_assoc, mul_mod, ne_two_of_dvd_nat, p.Prime, pow_add, pow_ne_zero, pow_of_ne_zero, pow_pow_
-/
lemma fermat_primeFactors_one_lt (n p : Nat) (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ fermatNumber n) :
    exists k, p = k * 2 ^ (n + 2) + 1 := by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p != 2 := by
    exact (even_two.pow_of_ne_zero <| pow_ne_zero n two_ne_zero).add_one.ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [add_assoc]; rw [pow_add]; rw [← mul_assoc]; rw [← mod_add_mod]; rw [mul_mod]
    simp
  obtain ⟨a, ha⟩ := (exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  suffices h : p ∣ a.val ^ (2 ^ (n + 1)) + 1 by
    exact pow_pow_add_primeFactors_one_lt hp hp2 h
  rw [fermatNumber] at hpdvd
  rw [← natCast_eq_zero_iff]; rw [Nat.cast_add _ 1]; rw [Nat.cast_one]; rw [Nat.cast_pow] at hpdvd ⊢
  rwa [natCast_val, ZMod.cast_id, pow_succ', pow_mul, sq, ← ha]


-- TODO: move to NumberTheory.Mersenne, once we have that.
/-!
### Primality of Mersenne numbers `Mₙ = a ^ n - 1`
-/

/--
theorem `prime_of_pow_sub_one_prime` / 定理 `prime_of_pow_sub_one_prime`

English:
theorem prime_of_pow_sub_one_prime
  given: {a n : Nat} (hn1 : n != 1) (hP : (a ^ n - 1).Prime)
  proof: by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n != 0 := fun h => (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    let h := Nat.sub_dvd_pow_sub_pow a 1 n
    rw [on

中文:
定理 prime_of_pow_sub_one_prime
  条件: {a n : 自然数} (hn1 : n != 1) (hP : (a ^ n - 1).素)
  证明: by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n != 0 := fun h => (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    let h := Nat.sub_dvd_pow_sub_pow a 1 n
    rw [on

Depends on / 依赖: Nat.one_lt_pow_iff, Nat.prime_def.mpr, Nat.sub_dvd_pow_sub_pow, Nat.sub_eq_iff_eq_add, Nat.sub_one_cancel, contrapose, dvd_iff_eq, eq_comm, hP.dvd_iff_eq, hP.pos, ha1.le, one_lt_pow_iff, one_pos, one_pos.trans, one_pow, pow_eq_self_iff, pow_pos, prime_def, sub_dvd_pow_sub_pow, sub_eq_iff_eq_add
-/
theorem prime_of_pow_sub_one_prime {a n : Nat} (hn1 : n != 1) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n != 0 := fun h => (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    let h := Nat.sub_dvd_pow_sub_pow a 1 n
    rw [one_pow]; rw [hP.dvd_iff_eq (mt (Nat.sub_eq_iff_eq_add ha1.le).mp hn1)]; rw [eq_comm] at h
    exact (pow_eq_self_iff ha1).mp (Nat.sub_one_cancel ha0 (pow_pos ha0 n) h).symm
  subst ha2
  refine ⟨rfl, Nat.prime_def.mpr ⟨(two_le_iff n).mpr ⟨hn0, hn1⟩, fun d hdn => ?_⟩⟩
  have hinj : forall x y, 2 ^ x - 1 = 2 ^ y - 1 -> x = y :=
    fun x y h => Nat.pow_right_injective le_rfl (sub_one_cancel (pow_pos ha0 x) (pow_pos ha0 y) h)
  let h := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 (n / d)
  rw [one_pow]; rw [← pow_mul]; rw [Nat.mul_div_cancel' hdn] at h
  exact (hP.eq_one_or_self_of_dvd (2 ^ d - 1) h).imp (hinj d 1) (hinj d n)

end Nat
