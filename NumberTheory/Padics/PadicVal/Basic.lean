/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Int

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.

## Notation

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
  quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
  greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in
  the language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem. Taking (`p - 1`) times
  the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
  of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
  `Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for
  the same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
  `p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum
  of the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section


universe u

open Nat Rat
open scoped Finset

namespace padicValNat

variable {p : Nat}

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValNat p p` is `1`. -/
alias self := padicValNat_base

/--
theorem `eq_zero_of_not_dvd` / 定理 `eq_zero_of_not_dvd`

English:
theorem eq_zero_of_not_dvd
  given: {n : Nat} (h : ¬p ∣ n)
  statement: padicValNat p n = 0
  proof: eq_zero_iff.2 Or.inr Or.inr h

中文:
定理 eq_zero_of_not_dvd
  条件: {n : 自然数} (h : ¬p ∣ n)
  结论: padicVal自然数 p n = 0
  证明: eq_zero_iff.2 Or.inr Or.inr h

Depends on / 依赖: Or.inr, eq_zero_iff
-/
theorem eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n) : padicValNat p n = 0 :=
eq_zero_iff.2 Or.inr Or.inr h

end padicValNat

/--
Definition of `padicValInt` / `padicValInt` 的定义

English:
definition padicValInt
  signature: (p : Nat) (z : Int)
  body: padicValNat p z.natAbs

中文:
定义 padicVal整数
  签名: (p : 自然数) (z : 整数)
  定义体: padicValNat p z.natAbs

Depends on / 依赖: natAbs, padicValNat, z.natAbs
-/
def padicValInt (p : Nat) (z : Int) : Nat :=
  padicValNat p z.natAbs

namespace padicValInt

variable {p : Nat}

/--
theorem `of_ne_one_ne_zero` / 定理 `of_ne_one_ne_zero`

English:
theorem of_ne_one_ne_zero
  given: {z : Int} (hp : p != 1) (hz : z != 0)
  proof: by
  rw [padicValInt]; rw [padicValNat_def' hp (Int.natAbs_ne_zero.mpr hz)]
  apply Int.multiplicity_natAbs

中文:
定理 of_ne_one_ne_zero
  条件: {z : 整数} (hp : p != 1) (hz : z != 0)
  证明: by
  rw [padicValInt]; rw [padicValNat_def' hp (Int.natAbs_ne_zero.mpr hz)]
  apply Int.multiplicity_natAbs

Depends on / 依赖: Int.multiplicity_natAbs, Int.natAbs_ne_zero.mpr, multiplicity_natAbs, natAbs_ne_zero, padicValInt, padicValNat_def
-/
theorem of_ne_one_ne_zero {z : Int} (hp : p != 1) (hz : z != 0) :
    padicValInt p z = multiplicity (p : Int) z := by
  rw [padicValInt]; rw [padicValNat_def' hp (Int.natAbs_ne_zero.mpr hz)]
  apply Int.multiplicity_natAbs

/-- `padicValInt p 0` is `0` for any `p`. -/
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: padicValInt p 0 = 0
  proof: by simp [padicValInt]

中文:
定理 zero
  结论: padicVal整数 p 0 = 0
  证明: by simp [padicValInt]
-/
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]

/-- `padicValInt p 1` is `0` for any `p`. -/
@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: padicValInt p 1 = 0
  proof: by simp [padicValInt]

中文:
定理 one
  结论: padicVal整数 p 1 = 0
  证明: by simp [padicValInt]
-/
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp]
/--
theorem `of_nat` / 定理 `of_nat`

English:
theorem of_nat
  given: {n : Nat}
  statement: padicValInt p n = padicValNat p n
  proof: by simp [padicValInt]

中文:
定理 of_nat
  条件: {n : 自然数}
  结论: padicVal整数 p n = padicVal自然数 p n
  证明: by simp [padicValInt]

Depends on / 依赖: padicValInt
-/
theorem of_nat {n : Nat} : padicValInt p n = padicValNat p n := by simp [padicValInt]

/--
theorem `self` / 定理 `self`

English:
theorem self
  given: (hp : 1 < p)
  statement: padicValInt p p = 1
  proof: by simp [padicValNat.self hp]

@[simp]

中文:
定理 self
  条件: (hp : 1 < p)
  结论: padicVal整数 p p = 1
  证明: by simp [padicValNat.self hp]

@[simp]

Depends on / 依赖: padicValNat, padicValNat.self
-/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]

@[simp]
/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {z : Int}
  statement: padicValInt p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : Int) ∣ z
  proof: by
  rw [padicValInt]; rw [padicValNat.eq_zero_iff]; rw [Int.natAbs_eq_zero]; rw [← Int.ofNat_dvd_left]

中文:
定理 eq_zero_iff
  条件: {z : 整数}
  结论: padicVal整数 p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : 整数) ∣ z
  证明: by
  rw [padicValInt]; rw [padicValNat.eq_zero_iff]; rw [Int.natAbs_eq_zero]; rw [← Int.ofNat_dvd_left]

Depends on / 依赖: Int.natAbs_eq_zero, Int.ofNat_dvd_left, eq_zero_iff, natAbs_eq_zero, ofNat_dvd_left, padicValInt, padicValNat, padicValNat.eq_zero_iff
-/
theorem eq_zero_iff {z : Int} : padicValInt p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : Int) ∣ z := by
  rw [padicValInt]; rw [padicValNat.eq_zero_iff]; rw [Int.natAbs_eq_zero]; rw [← Int.ofNat_dvd_left]

/--
theorem `eq_zero_of_not_dvd` / 定理 `eq_zero_of_not_dvd`

English:
theorem eq_zero_of_not_dvd
  given: {z : Int} (h : ¬(p : Int) ∣ z)
  statement: padicValInt p z = 0
  proof: by
  simp [h]

中文:
定理 eq_zero_of_not_dvd
  条件: {z : 整数} (h : ¬(p : 整数) ∣ z)
  结论: padicVal整数 p z = 0
  证明: by
  simp [h]
-/
theorem eq_zero_of_not_dvd {z : Int} (h : ¬(p : Int) ∣ z) : padicValInt p z = 0 := by
  simp [h]

end padicValInt

/--
Definition of `padicValRat` / `padicValRat` 的定义

English:
definition padicValRat
  signature: (p : Nat) (q : Rat)
  body: padicValInt p q.num - padicValNat p q.den

中文:
定义 padicValRat
  签名: (p : 自然数) (q : 有理数)
  定义体: padicValInt p q.num - padicValNat p q.den

Depends on / 依赖: padicValInt, padicValNat, q.den, q.num
-/
def padicValRat (p : Nat) (q : Rat) : Int :=
  padicValInt p q.num - padicValNat p q.den

/--
lemma `padicValRat_def` / 引理 `padicValRat_def`

English:
lemma padicValRat_def
  given: (p : Nat) (q : Rat)
  proof: rfl

中文:
引理 padicValRat_def
  条件: (p : 自然数) (q : 有理数)
  证明: rfl
-/
lemma padicValRat_def (p : Nat) (q : Rat) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl

namespace padicValRat

variable {p : Nat}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (q : Rat)
  statement: padicValRat p (-q) = padicValRat p q
  proof: by
  simp [padicValRat, padicValInt]

中文:
定理 neg
  条件: (q : 有理数)
  结论: padicValRat p (-q) = padicValRat p q
  证明: by
  simp [padicValRat, padicValInt]
-/
protected theorem neg (q : Rat) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]

/-- `padicValRat p 0` is `0` for any `p`. -/
@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: padicValRat p 0 = 0
  proof: by simp [padicValRat]

中文:
定理 zero
  结论: padicValRat p 0 = 0
  证明: by simp [padicValRat]
-/
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]

/-- `padicValRat p 1` is `0` for any `p`. -/
@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: padicValRat p 1 = 0
  proof: by simp [padicValRat]

中文:
定理 one
  结论: padicValRat p 1 = 0
  证明: by simp [padicValRat]
-/
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
/--
theorem `of_int` / 定理 `of_int`

English:
theorem of_int
  given: {z : Int}
  statement: padicValRat p z = padicValInt p z
  proof: by simp [padicValRat]

中文:
定理 of_int
  条件: {z : 整数}
  结论: padicValRat p z = padicVal整数 p z
  证明: by simp [padicValRat]

Depends on / 依赖: padicValRat
-/
theorem of_int {z : Int} : padicValRat p z = padicValInt p z := by simp [padicValRat]

/--
theorem `of_int_multiplicity` / 定理 `of_int_multiplicity`

English:
theorem of_int_multiplicity
  given: {z : Int} (hp : p != 1) (hz : z != 0)
  proof: by
  rw [of_int]; rw [padicValInt.of_ne_one_ne_zero hp hz]

中文:
定理 of_int_multiplicity
  条件: {z : 整数} (hp : p != 1) (hz : z != 0)
  证明: by
  rw [of_int]; rw [padicValInt.of_ne_one_ne_zero hp hz]

Depends on / 依赖: of_int, of_ne_one_ne_zero, padicValInt, padicValInt.of_ne_one_ne_zero
-/
theorem of_int_multiplicity {z : Int} (hp : p != 1) (hz : z != 0) :
    padicValRat p (z : Rat) = multiplicity (p : Int) z := by
  rw [of_int]; rw [padicValInt.of_ne_one_ne_zero hp hz]

/--
theorem `multiplicity_sub_multiplicity` / 定理 `multiplicity_sub_multiplicity`

English:
theorem multiplicity_sub_multiplicity
  given: {q : Rat} (hp : p != 1) (hq : q != 0)
  proof: by
  rw [padicValRat]; rw [padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq)]; rw [padicValNat_def' hp q.den_ne_zero]

中文:
定理 multiplicity_sub_multiplicity
  条件: {q : 有理数} (hp : p != 1) (hq : q != 0)
  证明: by
  rw [padicValRat]; rw [padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq)]; rw [padicValNat_def' hp q.den_ne_zero]

Depends on / 依赖: Rat.num_ne_zero, den_ne_zero, num_ne_zero, of_ne_one_ne_zero, padicValInt, padicValInt.of_ne_one_ne_zero, padicValNat_def, padicValRat, q.den_ne_zero
-/
theorem multiplicity_sub_multiplicity {q : Rat} (hp : p != 1) (hq : q != 0) :
    padicValRat p q = multiplicity (p : Int) q.num - multiplicity p q.den := by
  rw [padicValRat]; rw [padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq)]; rw [padicValNat_def' hp q.den_ne_zero]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
/--
theorem `of_nat` / 定理 `of_nat`

English:
theorem of_nat
  given: {n : Nat}
  statement: padicValRat p n = padicValNat p n
  proof: by simp [padicValRat]

中文:
定理 of_nat
  条件: {n : 自然数}
  结论: padicValRat p n = padicVal自然数 p n
  证明: by simp [padicValRat]

Depends on / 依赖: padicValRat
-/
theorem of_nat {n : Nat} : padicValRat p n = padicValNat p n := by simp [padicValRat]

/--
theorem `self` / 定理 `self`

English:
theorem self
  given: (hp : 1 < p)
  statement: padicValRat p p = 1
  proof: by simp [hp]

中文:
定理 self
  条件: (hp : 1 < p)
  结论: padicValRat p p = 1
  证明: by simp [hp]
-/
theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]

end padicValRat

section padicValNat

variable {p : Nat}

/--
theorem `zero_le_padicValRat_of_nat` / 定理 `zero_le_padicValRat_of_nat`

English:
theorem zero_le_padicValRat_of_nat
  given: (n : Nat)
  statement: 0 <= padicValRat p n
  proof: by simp

中文:
定理 zero_le_padicValRat_of_nat
  条件: (n : 自然数)
  结论: 0 <= padicValRat p n
  证明: by simp
-/
theorem zero_le_padicValRat_of_nat (n : Nat) : 0 <= padicValRat p n := by simp

/-- `padicValRat` coincides with `padicValNat`. -/
@[norm_cast]
/--
theorem `padicValRat_of_nat` / 定理 `padicValRat_of_nat`

English:
theorem padicValRat_of_nat
  given: (n : Nat)
  statement: ↑(padicValNat p n) = padicValRat p n
  proof: by simp

@[simp]

中文:
定理 padicValRat_of_nat
  条件: (n : 自然数)
  结论: ↑(padicVal自然数 p n) = padicValRat p n
  证明: by simp

@[simp]
-/
theorem padicValRat_of_nat (n : Nat) : ↑(padicValNat p n) = padicValRat p n := by simp

@[simp]
/--
theorem `padicValNat_self` / 定理 `padicValNat_self`

English:
theorem padicValNat_self
  given: [Fact p.Prime]
  statement: padicValNat p p = 1
  proof: by
  rw [padicValNat_def (@Fact.out p.Prime).ne_zero]
  simp

中文:
定理 padicVal自然数_self
  条件: [Fact p.素]
  结论: padicVal自然数 p p = 1
  证明: by
  rw [padicValNat_def (@Fact.out p.Prime).ne_zero]
  simp

Depends on / 依赖: Fact.out, ne_zero, p.Prime, padicValNat_def
-/
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).ne_zero]
  simp

/--
theorem `one_le_padicValNat_of_dvd` / 定理 `one_le_padicValNat_of_dvd`

English:
theorem one_le_padicValNat_of_dvd
  given: {n : Nat} [hp : Fact p.Prime] (hn : n != 0) (div : p ∣ n)
  proof: by
  rwa [← ENat.natCast_le_natCast, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

中文:
定理 one_le_padicVal自然数_of_dvd
  条件: {n : 自然数} [hp : Fact p.素] (hn : n != 0) (div : p ∣ n)
  证明: by
  rwa [← ENat.natCast_le_natCast, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

Depends on / 依赖: ENat.natCast_le_natCast, natCast_le_natCast, padicValNat_eq_emultiplicity, pow_dvd_iff_le_emultiplicity, pow_one
-/
theorem one_le_padicValNat_of_dvd {n : Nat} [hp : Fact p.Prime] (hn : n != 0) (div : p ∣ n) :
    1 <= padicValNat p n := by
  rwa [← ENat.natCast_le_natCast, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

/--
theorem `dvd_iff_padicValNat_ne_zero` / 定理 `dvd_iff_padicValNat_ne_zero`

English:
theorem dvd_iff_padicValNat_ne_zero
  given: {p n : Nat} [Fact p.Prime] (hn0 : n != 0)
  proof: ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩

中文:
定理 dvd_iff_padicVal自然数_ne_zero
  条件: {p n : 自然数} [Fact p.素] (hn0 : n != 0)
  证明: ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩

Depends on / 依赖: Classical, Classical.not_not, eq_zero_of_not_dvd, not_not, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, one_le_padicValNat_of_dvd, padicValNat, padicValNat.eq_zero_of_not_dvd
-/
theorem dvd_iff_padicValNat_ne_zero {p n : Nat} [Fact p.Prime] (hn0 : n != 0) :
    p ∣ n ↔ padicValNat p n != 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩

end padicValNat

namespace padicValRat

variable {p : Nat} [hp : Fact p.Prime]

/--
theorem `finite_int_prime_iff` / 定理 `finite_int_prime_iff`

English:
theorem finite_int_prime_iff
  given: {a : Int}
  statement: FiniteMultiplicity (p : Int) a ↔ a != 0
  proof: by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

中文:
定理 finite_int_prime_iff
  条件: {a : 整数}
  结论: FiniteMultiplicity (p : 整数) a ↔ a != 0
  证明: by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

Depends on / 依赖: Int.finiteMultiplicity_iff, finiteMultiplicity_iff, ne_one
-/
theorem finite_int_prime_iff {a : Int} : FiniteMultiplicity (p : Int) a ↔ a != 0 := by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

/--
theorem `defn` / 定理 `defn`

English:
theorem defn
  statement: (p : Nat) [hp : Fact p.Prime] {q : Rat} {n d : Int} (hqz : q != 0)
  proof: by
  have hd : d != 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]; rw [multiplicity_mul (Nat.prime_iff_prime_in

中文:
定理 defn
  结论: (p : 自然数) [hp : Fact p.素] {q : 有理数} {n d : 整数} (hqz : q != 0)
  证明: by
  have hd : d != 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]; rw [multiplicity_mul (Nat.prime_iff_prime_in
-/
protected theorem defn (p : Nat) [hp : Fact p.Prime] {q : Rat} {n d : Int} (hqz : q != 0)
    (qdf : q = n /. d) :
    padicValRat p q = multiplicity (p : Int) n - multiplicity (p : Int) d := by
  have hd : d != 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]; rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]
  · rw [Nat.cast_add, Nat.cast_add]
    simp_rw [Int.natCast_multiplicity p q.den]
    ring
  · simpa [finite_int_prime_iff, hc2] using hd
  · simpa [finite_int_prime_iff, hqz, hc2] using hd

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {q r : Rat} (hq : q != 0) (hr : r != 0)
  proof: by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat]; rw [Rat.mkRat_eq_divInt]; rw [Nat.cast_mul]
  have hq' : q.num /. q.den != 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den != 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : Int) := Nat.prim

中文:
定理 mul
  条件: {q r : 有理数} (hq : q != 0) (hr : r != 0)
  证明: by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat]; rw [Rat.mkRat_eq_divInt]; rw [Nat.cast_mul]
  have hq' : q.num /. q.den != 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den != 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : Int) := Nat.prim
-/
protected theorem mul {q r : Rat} (hq : q != 0) (hr : r != 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat]; rw [Rat.mkRat_eq_divInt]; rw [Nat.cast_mul]
  have hq' : q.num /. q.den != 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den != 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : Int) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← q.num_divInt_den]; rw [padicValRat.defn p hq']; rw [← r.num_divInt_den]; rw [padicValRat.defn p hr']
  rw [multiplicity_mul hp']; rw [multiplicity_mul hp']; rw [Nat.cast_add]; rw [Nat.cast_add]
  · ring
  · simp [finite_int_prime_iff]
  · simp [finite_int_prime_iff, hq, hr]

/-- A rewrite lemma for `padicValRat p (q^k)`. -/
@[simp]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (q : Rat) {k : Nat}
  proof: by
  obtain rfl | hq := eq_or_ne q 0
  · cases k <;> simp
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]

中文:
定理 pow
  条件: (q : 有理数) {k : 自然数}
  证明: by
  obtain rfl | hq := eq_or_ne q 0
  · cases k <;> simp
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]
-/
protected theorem pow (q : Rat) {k : Nat} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  obtain rfl | hq := eq_or_ne q 0
  · cases k <;> simp
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]

/-- A rewrite lemma for `padicValRat p (q⁻¹)`. -/
@[simp]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: (q : Rat)
  statement: padicValRat p q⁻¹ = -padicValRat p q
  proof: by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

@[simp]

中文:
定理 inv
  条件: (q : 有理数)
  结论: padicValRat p q⁻¹ = -padicValRat p q
  证明: by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

@[simp]
-/
protected theorem inv (q : Rat) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

@[simp]
/--
theorem `zpow` / 定理 `zpow`

English:
theorem zpow
  given: (q : Rat) {k : Int}
  proof: by
  induction k using Int.negInduction <;> simp

中文:
定理 zpow
  条件: (q : 有理数) {k : 整数}
  证明: by
  induction k using Int.negInduction <;> simp
-/
protected theorem zpow (q : Rat) {k : Int} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k using Int.negInduction <;> simp

/--
theorem `div` / 定理 `div`

English:
theorem div
  given: {q r : Rat} (hq : q != 0) (hr : r != 0)
  proof: by
  rw [div_eq_mul_inv]; rw [padicValRat.mul hq (inv_ne_zero hr)]; rw [padicValRat.inv r]; rw [sub_eq_add_neg]

中文:
定理 div
  条件: {q r : 有理数} (hq : q != 0) (hr : r != 0)
  证明: by
  rw [div_eq_mul_inv]; rw [padicValRat.mul hq (inv_ne_zero hr)]; rw [padicValRat.inv r]; rw [sub_eq_add_neg]
-/
protected theorem div {q r : Rat} (hq : q != 0) (hr : r != 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv]; rw [padicValRat.mul hq (inv_ne_zero hr)]; rw [padicValRat.inv r]; rw [sub_eq_add_neg]

/--
theorem `padicValRat_le_padicValRat_iff` / 定理 `padicValRat_le_padicValRat_iff`

English:
theorem padicValRat_le_padicValRat_iff
  statement: {n₁ n₂ d₁ d₂ : Int} (hn₁ : n₁ != 0) (hn₂ : n₂ != 0)
  proof: by
  have hf1 : FiniteMultiplicity (p : Int) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : Int) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl]; rw [pa

中文:
定理 padicValRat_le_padicValRat_iff
  结论: {n₁ n₂ d₁ d₂ : 整数} (hn₁ : n₁ != 0) (hn₂ : n₂ != 0)
  证明: by
  have hf1 : FiniteMultiplicity (p : Int) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : Int) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl]; rw [pa

Depends on / 依赖: FiniteMultiplicity, Nat.prime_iff_prime_int, Rat.divInt_ne_zero_of_ne_zero, add_c, add_sub_assoc, divInt_ne_zero_of_ne_zero, finite_int_prime_iff, le_sub_iff_add_le, mul_ne_zero, multiplicity_mul, padicValRat, padicValRat.defn, prime_iff_prime_int, sub_le_iff_le_add
-/
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : Int} (hn₁ : n₁ != 0) (hn₂ : n₂ != 0)
    (hd₁ : d₁ != 0) (hd₂ : d₂ != 0) :
    padicValRat p (n₁ /. d₁) <= padicValRat p (n₂ /. d₂) ↔
      forall n : Nat, (p : Int) ^ n ∣ n₁ * d₂ -> (p : Int) ^ n ∣ n₂ * d₁ := by
  have hf1 : FiniteMultiplicity (p : Int) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : Int) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl]; rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl]; rw [sub_le_iff_le_add']; rw [←
      add_sub_assoc]; rw [le_sub_iff_add_le]
    norm_cast
    rw [← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf1]; rw [add_comm]; rw [← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf2]; rw [hf1.multiplicity_le_multiplicity_iff hf2]

/--
theorem `le_padicValRat_add_of_le` / 定理 `le_padicValRat_add_of_le`

English:
theorem le_padicValRat_add_of_le
  statement: {q r : Rat} (hqr : q + r != 0)
  proof: if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num != 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : Int) != 0 := mod_cast Rat.den_nz _
      have hrn : r.num != 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : Int) != 0 := 

中文:
定理 le_padicValRat_add_of_le
  结论: {q r : 有理数} (hqr : q + r != 0)
  证明: if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num != 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : Int) != 0 := mod_cast Rat.den_nz _
      have hrn : r.num != 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : Int) != 0 := 

Depends on / 依赖: Rat.add_num_den, Rat.den_nz, Rat.mk_num_ne_zero_of_ne_zero, Rat.num_ne_zero, add_num_den, conv_lhs, den_nz, mk_num_ne_zero_of_ne_zero, mod_cast, num_div, num_ne_zero, q.den, q.num, q.num_div, r.den, r.num
-/
theorem le_padicValRat_add_of_le {q r : Rat} (hqr : q + r != 0)
    (h : padicValRat p q <= padicValRat p r) : padicValRat p q <= padicValRat p (q + r) :=
  if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num != 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : Int) != 0 := mod_cast Rat.den_nz _
      have hrn : r.num != 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : Int) != 0 := mod_cast Rat.den_nz _
      have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
      have hqrd : q.num * r.den + q.den * r.num != 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← q.num_divInt_den]
      rw [hqreq]; rw [padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd)]; rw [←
        emultiplicity_le_emultiplicity_iff]; rw [mul_left_comm]; rw [emultiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]; rw [add_mul]
      rw [← q.num_divInt_den]; rw [← r.num_divInt_den]; rw [padicValRat_le_padicValRat_iff hqn hrn hqd hrd]; rw [←
        emultiplicity_le_emultiplicity_iff] at h
      calc
        _ <= min (emultiplicity ↑p (q.num * r.den * q.den))
                (emultiplicity ↑p (q.den * r.num * q.den)) :=
          le_min
            (by rw [emultiplicity_mul (a := _ * _) (Nat.prime_iff_prime_int.1 hp.1), add_comm])
            (by grw [mul_assoc, emultiplicity_mul (b := _ * _) (Nat.prime_iff_prime_int.1 hp.1), h])
        _ <= _ := min_le_emultiplicity_add

/--
theorem `min_le_padicValRat_add` / 定理 `min_le_padicValRat_add`

English:
theorem min_le_padicValRat_add
  given: {q r : Rat} (hqr : q + r != 0)
  proof: (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)

中文:
定理 min_le_padicValRat_add
  条件: {q r : 有理数} (hqr : q + r != 0)
  证明: (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)

Depends on / 依赖: add_comm, le_padicValRat_add_of_le, le_total, min_eq_left, min_eq_right, padicValRat
-/
theorem min_le_padicValRat_add {q r : Rat} (hqr : q + r != 0) :
    min (padicValRat p q) (padicValRat p r) <= padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)

/--
lemma `add_eq_min` / 引理 `add_eq_min`

English:
lemma add_eq_min
  statement: {q r : Rat} (hqr : q + r != 0) (hq : q != 0) (hr : r != 0)
  proof: by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right]; rw [padicValRat.neg] at h2 h3
  rw 

中文:
引理 add_eq_min
  结论: {q r : 有理数} (hqr : q + r != 0) (hq : q != 0) (hr : r != 0)
  证明: by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right]; rw [padicValRat.neg] at h2 h3
  rw 

Depends on / 依赖: add_comm, add_neg_cancel_right, min_le_padicValRat_add, ne_of_eq_of_ne, padicValRat, padicValRat.neg
-/
lemma add_eq_min {q r : Rat} (hqr : q + r != 0) (hq : q != 0) (hr : r != 0)
    (hval : padicValRat p q != padicValRat p r) :
    padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right]; rw [padicValRat.neg] at h2 h3
  rw [add_comm] at h3
  omega

/--
lemma `add_eq_of_lt` / 引理 `add_eq_of_lt`

English:
lemma add_eq_of_lt
  statement: {q r : Rat} (hqr : q + r != 0)
  proof: by
  rw [add_eq_min hqr hq hr (ne_of_lt hval)]; rw [min_eq_left (le_of_lt hval)]

中文:
引理 add_eq_of_lt
  结论: {q r : 有理数} (hqr : q + r != 0)
  证明: by
  rw [add_eq_min hqr hq hr (ne_of_lt hval)]; rw [min_eq_left (le_of_lt hval)]

Depends on / 依赖: add_eq_min, le_of_lt, min_eq_left, ne_of_lt
-/
lemma add_eq_of_lt {q r : Rat} (hqr : q + r != 0)
    (hq : q != 0) (hr : r != 0) (hval : padicValRat p q < padicValRat p r) :
    padicValRat p (q + r) = padicValRat p q := by
  rw [add_eq_min hqr hq hr (ne_of_lt hval)]; rw [min_eq_left (le_of_lt hval)]

/--
lemma `lt_add_of_lt` / 引理 `lt_add_of_lt`

English:
lemma lt_add_of_lt
  statement: {q r₁ r₂ : Rat} (hqr : r₁ + r₂ != 0)
  proof: lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)

中文:
引理 lt_add_of_lt
  结论: {q r₁ r₂ : 有理数} (hqr : r₁ + r₂ != 0)
  证明: lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)

Depends on / 依赖: lt_min, lt_of_lt_of_le, min_le_padicValRat_add, padicValRat, padicValRat.min_le_padicValRat_add
-/
lemma lt_add_of_lt {q r₁ r₂ : Rat} (hqr : r₁ + r₂ != 0)
    (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
    padicValRat p q < padicValRat p (r₁ + r₂) :=
  lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)

/--
lemma `self_pow_inv` / 引理 `self_pow_inv`

English:
lemma self_pow_inv
  given: (r : Nat)
  statement: padicValRat p ((p : Rat) ^ r)⁻¹ = -r
  proof: by
  rw [padicValRat.inv]; rw [neg_inj]; rw [padicValRat.pow p]; rw [padicValRat.self hp.elim.one_lt]; rw [mul_one]

中文:
引理 self_pow_inv
  条件: (r : 自然数)
  结论: padicValRat p ((p : 有理数) ^ r)⁻¹ = -r
  证明: by
  rw [padicValRat.inv]; rw [neg_inj]; rw [padicValRat.pow p]; rw [padicValRat.self hp.elim.one_lt]; rw [mul_one]

Depends on / 依赖: hp.elim.one_lt, mul_one, neg_inj, one_lt, padicValRat, padicValRat.inv, padicValRat.pow, padicValRat.self
-/
lemma self_pow_inv (r : Nat) : padicValRat p ((p : Rat) ^ r)⁻¹ = -r := by
  rw [padicValRat.inv]; rw [neg_inj]; rw [padicValRat.pow p]; rw [padicValRat.self hp.elim.one_lt]; rw [mul_one]

/--
theorem `sum_pos_of_pos` / 定理 `sum_pos_of_pos`

English:
theorem sum_pos_of_pos
  statement: {n : Nat} {F : Nat -> Rat} (hF : forall i, i < n -> 0 < padicValRat p (F i))
  proof: by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x in Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min

中文:
定理 sum_pos_of_pos
  结论: {n : 自然数} {F : 自然数 -> 有理数} (hF : 对任意 i, i < n -> 0 < padicValRat p (F i))
  证明: by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x in Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min

Depends on / 依赖: False.elim, Finset, Finset.range, Finset.sum_range_succ, lt_add_one, lt_min, lt_of_lt_of_le, lt_trans, min_le_padicValRat_add, sum_range_succ, zero_add
-/
theorem sum_pos_of_pos {n : Nat} {F : Nat -> Rat} (hF : forall i, i < n -> 0 < padicValRat p (F i))
    (hn0 : ∑ i in Finset.range n, F i != 0) : 0 < padicValRat p (∑ i in Finset.range n, F i) := by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x in Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min (hd (fun i hi => ?_) h) (hF d (lt_add_one _))
      exact hF _ (lt_trans hi (lt_add_one _))

/--
theorem `lt_sum_of_lt` / 定理 `lt_sum_of_lt`

English:
theorem lt_sum_of_lt
  statement: {p j : Nat} [hp : Fact (Nat.Prime p)] {F : Nat -> Rat} {S : Finset Nat}
  proof: by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert]; rw [Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset

中文:
定理 lt_sum_of_lt
  结论: {p j : 自然数} [hp : Fact (自然数.素 p)] {F : 自然数 -> 有理数} {S : 有限集 自然数}
  证明: by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert]; rw [Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.cons_eq_insert, Finset.mem_insert, Finset.sum_insert, Finset.sum_pos, Finset.sum_singleton, Nonempty, Or.inr, add_pos, cons_eq_insert, cons_induction, lt_add_of_lt, mem_insert, ne_of_gt, padicValRat, padicValRat.lt_add_of_lt, singleton, sum_insert, sum_pos
-/
theorem lt_sum_of_lt {p j : Nat} [hp : Fact (Nat.Prime p)] {F : Nat -> Rat} {S : Finset Nat}
    (hS : S.Nonempty) (hF : forall i, i in S -> padicValRat p (F j) < padicValRat p (F i))
    (hn1 : forall i : Nat, 0 < F i) : padicValRat p (F j) < padicValRat p (∑ i in S, F i) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert]; rw [Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert, Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace padicValNat

variable {p a b : Nat} [hp : Fact p.Prime]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: a != 0 -> b != 0 -> padicValNat p (a * b) = padicValNat p a + padicValNat p b
  proof: mod_cast padicValRat.mul (p := p) (q := a) (r := b)

中文:
定理 mul
  结论: a != 0 -> b != 0 -> padicVal自然数 p (a * b) = padicVal自然数 p a + padicVal自然数 p b
  证明: mod_cast padicValRat.mul (p := p) (q := a) (r := b)
-/
protected theorem mul : a != 0 -> b != 0 -> padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
  mod_cast padicValRat.mul (p := p) (q := a) (r := b)

/--
theorem `div_of_dvd` / 定理 `div_of_dvd`

English:
theorem div_of_dvd
  given: (h : b ∣ a)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm]; rw [k.mul_div_cancel hb.bot_lt]; rw [padicValNat.mul hk hb]; rw [Nat.add_sub_cancel]

中文:
定理 div_of_dvd
  条件: (h : b ∣ a)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm]; rw [k.mul_div_cancel hb.bot_lt]; rw [padicValNat.mul hk hb]; rw [Nat.add_sub_cancel]
-/
protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm]; rw [k.mul_div_cancel hb.bot_lt]; rw [padicValNat.mul hk hb]; rw [Nat.add_sub_cancel]

/--
theorem `div` / 定理 `div`

English:
theorem div
  given: (dvd : p ∣ b)
  statement: padicValNat p (b / p) = padicValNat p b - 1
  proof: by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat_self]

中文:
定理 div
  条件: (dvd : p ∣ b)
  结论: padicVal自然数 p (b / p) = padicVal自然数 p b - 1
  证明: by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat_self]
-/
protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat_self]

/-- A version of `padicValRat.pow` for `padicValNat`. -/
@[simp]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (a n : Nat)
  statement: padicValNat p (a ^ n) = n * padicValNat p a
  proof: by
  simpa only [← @Nat.cast_inj Int, push_cast] using padicValRat.pow a

中文:
定理 pow
  条件: (a n : 自然数)
  结论: padicVal自然数 p (a ^ n) = n * padicVal自然数 p a
  证明: by
  simpa only [← @Nat.cast_inj Int, push_cast] using padicValRat.pow a
-/
protected theorem pow (a n : Nat) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simpa only [← @Nat.cast_inj Int, push_cast] using padicValRat.pow a

/--
theorem `prime_pow` / 定理 `prime_pow`

English:
theorem prime_pow
  given: (n : Nat)
  statement: padicValNat p (p ^ n) = n
  proof: by
  rw [padicValNat.pow p]; rw [padicValNat_self]; rw [mul_one]

中文:
定理 prime_pow
  条件: (n : 自然数)
  结论: padicVal自然数 p (p ^ n) = n
  证明: by
  rw [padicValNat.pow p]; rw [padicValNat_self]; rw [mul_one]
-/
protected theorem prime_pow (n : Nat) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow p]; rw [padicValNat_self]; rw [mul_one]

/--
theorem `div_pow` / 定理 `div_pow`

English:
theorem div_pow
  given: (dvd : p ^ a ∣ b)
  statement: padicValNat p (b / p ^ a) = padicValNat p b - a
  proof: by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat.prime_pow]

中文:
定理 div_pow
  条件: (dvd : p ^ a ∣ b)
  结论: padicVal自然数 p (b / p ^ a) = padicVal自然数 p b - a
  证明: by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat.prime_pow]
-/
protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd]; rw [padicValNat.prime_pow]

/--
theorem `div'` / 定理 `div'`

English:
theorem div'
  given: {m : Nat} (cpm : Coprime p m) {b : Nat} (dvd : m ∣ b)
  proof: by
  rw [padicValNat.div_of_dvd dvd]; rw [eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm)]; rw [Nat.sub_zero]

中文:
定理 div'
  条件: {m : 自然数} (cpm : Coprime p m) {b : 自然数} (dvd : m ∣ b)
  证明: by
  rw [padicValNat.div_of_dvd dvd]; rw [eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm)]; rw [Nat.sub_zero]
-/
protected theorem div' {m : Nat} (cpm : Coprime p m) {b : Nat} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd]; rw [eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm)]; rw [Nat.sub_zero]

end padicValNat

section padicValNat

variable {p : Nat}

/--
theorem `dvd_of_one_le_padicValNat` / 定理 `dvd_of_one_le_padicValNat`

English:
theorem dvd_of_one_le_padicValNat
  given: {n : Nat} (hp : 1 <= padicValNat p n)
  statement: p ∣ n
  proof: by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

中文:
定理 dvd_of_one_le_padicVal自然数
  条件: {n : 自然数} (hp : 1 <= padicVal自然数 p n)
  结论: p ∣ n
  证明: by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

Depends on / 依赖: eq_zero_of_not_dvd, lt_irrefl, lt_of_lt_of_le, padicValNat, padicValNat.eq_zero_of_not_dvd, zero_lt_one
-/
theorem dvd_of_one_le_padicValNat {n : Nat} (hp : 1 <= padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

/--
theorem `padicValNat_dvd_iff_le_of_ne_one` / 定理 `padicValNat_dvd_iff_le_of_ne_one`

English:
theorem padicValNat_dvd_iff_le_of_ne_one
  given: {p : Nat} (hp : p != 1) {a n : Nat} (ha : a != 0)
  proof: by
  rw [pow_dvd_iff_le_emultiplicity]; rw [← padicValNat_eq_emultiplicity_of_ne_one hp ha]; rw [Nat.cast_le]

中文:
定理 padicVal自然数_dvd_iff_le_of_ne_one
  条件: {p : 自然数} (hp : p != 1) {a n : 自然数} (ha : a != 0)
  证明: by
  rw [pow_dvd_iff_le_emultiplicity]; rw [← padicValNat_eq_emultiplicity_of_ne_one hp ha]; rw [Nat.cast_le]

Depends on / 依赖: Nat.cast_le, cast_le, padicValNat_eq_emultiplicity_of_ne_one, pow_dvd_iff_le_emultiplicity
-/
theorem padicValNat_dvd_iff_le_of_ne_one {p : Nat} (hp : p != 1) {a n : Nat} (ha : a != 0) :
    p ^ n ∣ a ↔ n <= padicValNat p a := by
  rw [pow_dvd_iff_le_emultiplicity]; rw [← padicValNat_eq_emultiplicity_of_ne_one hp ha]; rw [Nat.cast_le]

/--
theorem `padicValNat_dvd_iff_le` / 定理 `padicValNat_dvd_iff_le`

English:
theorem padicValNat_dvd_iff_le
  given: [hp : Fact p.Prime] {a n : Nat} (ha : a != 0)
  proof: padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha

中文:
定理 padicVal自然数_dvd_iff_le
  条件: [hp : Fact p.素] {a n : 自然数} (ha : a != 0)
  证明: padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha

Depends on / 依赖: hp.out.ne_one, ne_one, padicValNat_dvd_iff_le_of_ne_one
-/
theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : Nat} (ha : a != 0) :
    p ^ n ∣ a ↔ n <= padicValNat p a :=
  padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha

/--
theorem `padicValNat_dvd_iff_of_ne_one` / 定理 `padicValNat_dvd_iff_of_ne_one`

English:
theorem padicValNat_dvd_iff_of_ne_one
  given: {p : Nat} (hp : p != 1) (n a : Nat)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha, or_iff_right ha]

中文:
定理 padicVal自然数_dvd_iff_of_ne_one
  条件: {p : 自然数} (hp : p != 1) (n a : 自然数)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha, or_iff_right ha]

Depends on / 依赖: Or.inl, dvd_zero, eq_or_ne, iff_of_true, or_iff_right, padicValNat_dvd_iff_le_of_ne_one
-/
theorem padicValNat_dvd_iff_of_ne_one {p : Nat} (hp : p != 1) (n a : Nat) :
    p ^ n ∣ a ↔ a = 0 ∨ n <= padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha, or_iff_right ha]

/--
theorem `padicValNat_dvd_iff` / 定理 `padicValNat_dvd_iff`

English:
theorem padicValNat_dvd_iff
  given: (n : Nat) [hp : Fact p.Prime] (a : Nat)
  proof: padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a

中文:
定理 padicVal自然数_dvd_iff
  条件: (n : 自然数) [hp : Fact p.素] (a : 自然数)
  证明: padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a

Depends on / 依赖: hp.out.ne_one, ne_one, padicValNat_dvd_iff_of_ne_one
-/
theorem padicValNat_dvd_iff (n : Nat) [hp : Fact p.Prime] (a : Nat) :
    p ^ n ∣ a ↔ a = 0 ∨ n <= padicValNat p a :=
  padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a

/--
theorem `pow_succ_padicValNat_not_dvd` / 定理 `pow_succ_padicValNat_not_dvd`

English:
theorem pow_succ_padicValNat_not_dvd
  given: {n : Nat} [hp : Fact p.Prime] (hn : n != 0)
  proof: by
  rw [padicValNat_dvd_iff_le hn]; rw [not_le]
  exact Nat.lt_succ_self _

中文:
定理 pow_succ_padicVal自然数_not_dvd
  条件: {n : 自然数} [hp : Fact p.素] (hn : n != 0)
  证明: by
  rw [padicValNat_dvd_iff_le hn]; rw [not_le]
  exact Nat.lt_succ_self _

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, not_le, padicValNat_dvd_iff_le
-/
theorem pow_succ_padicValNat_not_dvd {n : Nat} [hp : Fact p.Prime] (hn : n != 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn]; rw [not_le]
  exact Nat.lt_succ_self _

/--
theorem `padicValNat_primes` / 定理 `padicValNat_primes`

English:
theorem padicValNat_primes
  given: {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne : p != q)
  proof: @padicValNat.eq_zero_of_not_dvd p q
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne

中文:
定理 padicVal自然数_primes
  条件: {q : 自然数} [hp : Fact p.素] [hq : Fact q.素] (ne : p != q)
  证明: @padicValNat.eq_zero_of_not_dvd p q
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne

Depends on / 依赖: Iff.symm, eq_zero_of_not_dvd, not_congr, padicValNat, padicValNat.eq_zero_of_not_dvd, prime_dvd_prime_iff_eq
-/
theorem padicValNat_primes {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne : p != q) :
    padicValNat p q = 0 :=
@padicValNat.eq_zero_of_not_dvd p q
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne

/--
theorem `padicValNat_prime_prime_pow` / 定理 `padicValNat_prime_prime_pow`

English:
theorem padicValNat_prime_prime_pow
  statement: {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
  proof: by
  rw [padicValNat.pow _]; rw [padicValNat_primes ne]; rw [mul_zero]

中文:
定理 padicVal自然数_prime_prime_pow
  结论: {q : 自然数} [hp : Fact p.素] [hq : Fact q.素]
  证明: by
  rw [padicValNat.pow _]; rw [padicValNat_primes ne]; rw [mul_zero]

Depends on / 依赖: mul_zero, padicValNat, padicValNat.pow, padicValNat_primes
-/
theorem padicValNat_prime_prime_pow {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : Nat) (ne : p != q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _]; rw [padicValNat_primes ne]; rw [mul_zero]

/--
theorem `padicValNat_mul_pow_left` / 定理 `padicValNat_mul_pow_left`

English:
theorem padicValNat_mul_pow_left
  statement: {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
  proof: by
  rw [padicValNat.mul (NeZero.ne' (p ^ n)).symm (NeZero.ne' (q ^ m)).symm]; rw [padicValNat.prime_pow]; rw [padicValNat_prime_prime_pow m ne]; rw [add_zero]

中文:
定理 padicVal自然数_mul_pow_left
  结论: {q : 自然数} [hp : Fact p.素] [hq : Fact q.素]
  证明: by
  rw [padicValNat.mul (NeZero.ne' (p ^ n)).symm (NeZero.ne' (q ^ m)).symm]; rw [padicValNat.prime_pow]; rw [padicValNat_prime_prime_pow m ne]; rw [add_zero]

Depends on / 依赖: NeZero, NeZero.ne, add_zero, padicValNat, padicValNat.mul, padicValNat.prime_pow, padicValNat_prime_prime_pow, prime_pow
-/
theorem padicValNat_mul_pow_left {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : Nat) (ne : p != q) : padicValNat p (p ^ n * q ^ m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p ^ n)).symm (NeZero.ne' (q ^ m)).symm]; rw [padicValNat.prime_pow]; rw [padicValNat_prime_prime_pow m ne]; rw [add_zero]

/--
theorem `padicValNat_mul_pow_right` / 定理 `padicValNat_mul_pow_right`

English:
theorem padicValNat_mul_pow_right
  statement: {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
  proof: by
  rw [mul_comm (p ^ n) (q ^ m)]
  exact padicValNat_mul_pow_left m n ne

中文:
定理 padicVal自然数_mul_pow_right
  结论: {q : 自然数} [hp : Fact p.素] [hq : Fact q.素]
  证明: by
  rw [mul_comm (p ^ n) (q ^ m)]
  exact padicValNat_mul_pow_left m n ne

Depends on / 依赖: mul_comm, padicValNat_mul_pow_left
-/
theorem padicValNat_mul_pow_right {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : Nat) (ne : q != p) : padicValNat q (p ^ n * q ^ m) = m := by
  rw [mul_comm (p ^ n) (q ^ m)]
  exact padicValNat_mul_pow_left m n ne

/--
lemma `padicValNat_le_nat_log` / 引理 `padicValNat_le_nat_log`

English:
lemma padicValNat_le_nat_log
  given: (n : Nat)
  statement: padicValNat p n <= Nat.log p n
  proof: by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)

中文:
引理 padicVal自然数_le_nat_log
  条件: (n : 自然数)
  结论: padicVal自然数 p n <= 自然数.log p n
  证明: by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)

Depends on / 依赖: Nat.le_log_of_pow_le, le_log_of_pow_le, le_of_dvd, n.succ_pos, one_lt_succ_succ, p.one_lt_succ_succ, pow_padicValNat_dvd, succ_pos
-/
lemma padicValNat_le_nat_log (n : Nat) : padicValNat p n <= Nat.log p n := by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)

/--
lemma `padicValNat_add_le_self` / 引理 `padicValNat_add_le_self`

English:
lemma padicValNat_add_le_self
  given: {a : Nat} [hp : Fact p.Prime] (ha : p < a)
  proof: by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have : padicValNat p k < k := by calc
      _ <= log p k := padicValNat_le_nat_log k
      _ < _ := log_lt_self p (by lia)
    rw [hk]; rw [padicValNat.mul (by lia) (by lia)]; rw [padicValNat_self]
    calc
      _ <= p + k := by lia
      _ 

中文:
引理 padicVal自然数_add_le_self
  条件: {a : 自然数} [hp : Fact p.素] (ha : p < a)
  证明: by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have : padicValNat p k < k := by calc
      _ <= log p k := padicValNat_le_nat_log k
      _ < _ := log_lt_self p (by lia)
    rw [hk]; rw [padicValNat.mul (by lia) (by lia)]; rw [padicValNat_self]
    calc
      _ <= p + k := by lia
      _ 

Depends on / 依赖: Nat.add_le_mul, add_le_mul, eq_zero_of_not_dvd, hp.out.two_le, log_lt_self, padicValNat, padicValNat.eq_zero_of_not_dvd, padicValNat.mul, padicValNat_le_nat_log, padicValNat_self, two_le
-/
lemma padicValNat_add_le_self {a : Nat} [hp : Fact p.Prime] (ha : p < a) :
    padicValNat p a + p <= a := by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have : padicValNat p k < k := by calc
      _ <= log p k := padicValNat_le_nat_log k
      _ < _ := log_lt_self p (by lia)
    rw [hk]; rw [padicValNat.mul (by lia) (by lia)]; rw [padicValNat_self]
    calc
      _ <= p + k := by lia
      _ <= _ := Nat.add_le_mul hp.out.two_le (by lia)
  · rw [padicValNat.eq_zero_of_not_dvd dvd]
    lia

/--
lemma `nat_log_eq_padicValNat_iff` / 引理 `nat_log_eq_padicValNat_iff`

English:
lemma nat_log_eq_padicValNat_iff
  given: {n : Nat} [hp : Fact (Nat.Prime p)] (hn : n != 0)
  proof: by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out]; rw [by lia⟩)]; rw [and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

中文:
引理 nat_log_eq_padicVal自然数_iff
  条件: {n : 自然数} [hp : Fact (自然数.素 p)] (hn : n != 0)
  证明: by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out]; rw [by lia⟩)]; rw [and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

Depends on / 依赖: Nat.Prime.one_lt, Nat.le_of_dvd, Nat.log_eq_iff, Nat.pos_iff_ne_zero.mpr, Or.inr, and_iff_right_iff_imp, le_of_dvd, log_eq_iff, one_lt, pos_iff_ne_zero, pow_padicValNat_dvd
-/
lemma nat_log_eq_padicValNat_iff {n : Nat} [hp : Fact (Nat.Prime p)] (hn : n != 0) :
    Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out]; rw [by lia⟩)]; rw [and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

/--
lemma `Nat.log_ne_padicValNat_succ` / 引理 `Nat.log_ne_padicValNat_succ`

English:
lemma Nat.log_ne_padicValNat_succ
  given: {n : Nat} (hn : n != 0)
  statement: log 2 n != padicValNat 2 (n + 1)
  proof: by
  rw [Ne]; rw [log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff]; rw [← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff]; rw [Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  -- TODO(kmill): Why is this `p := 2` necess

中文:
引理 自然数.log_ne_padicVal自然数_succ
  条件: {n : 自然数} (hn : n != 0)
  结论: log 2 n != padicVal自然数 2 (n + 1)
  证明: by
  rw [Ne]; rw [log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff]; rw [← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff]; rw [Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  -- TODO(kmill): Why is this `p := 2` necess

Depends on / 依赖: Nat.lt_add_one_iff, Nat.pow_succ, add_one_le_iff, log_eq_iff, lt_add_one_iff, lt_of_le_of_ne, mul_one, not_dvd_of_lt_of_lt_mul_succ, pow_padicValNat_dvd, pow_succ
-/
lemma Nat.log_ne_padicValNat_succ {n : Nat} (hn : n != 0) : log 2 n != padicValNat 2 (n + 1) := by
  rw [Ne]; rw [log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff]; rw [← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff]; rw [Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  -- TODO(kmill): Why is this `p := 2` necessary?
  exact pow_succ_padicValNat_not_dvd (p := 2) n.succ_ne_zero ∘ dvd_of_eq

/--
lemma `Nat.max_log_padicValNat_succ_eq_log_succ` / 引理 `Nat.max_log_padicValNat_succ_eq_log_succ`

English:
lemma Nat.max_log_padicValNat_succ_eq_log_succ
  given: (n : Nat) [hp : Fact p.Prime]
  proof: by
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff]; rw [or_iff_not_imp_left]; rw [not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p 

中文:
引理 自然数.max_log_padicVal自然数_succ_eq_log_succ
  条件: (n : 自然数) [hp : Fact p.素]
  证明: by
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff]; rw [or_iff_not_imp_left]; rw [not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p 

Depends on / 依赖: add_one_le_iff, add_one_le_iff.mpr, hp.out.one_lt, le_antisymm, le_log_of_pow_le, le_max_iff, lt_pow_of_log_lt, max_le, n.succ_ne_zero, not_le, one_lt, or_iff_not_imp_left, padicValNat, padicValNat.prime_pow, padicValNat_le_nat_log, pow_log_le_add_one, pow_log_le_self, prime_pow, replace, succ_ne_zero
-/
lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : Nat) [hp : Fact p.Prime] :
    max (log p n) (padicValNat p (n + 1)) = log p (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff]; rw [or_iff_not_imp_left]; rw [not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p n.succ_ne_zero)
  rw [h]; rw [padicValNat.prime_pow]; rw [← h]

/--
theorem `range_pow_padicValNat_subset_divisors` / 定理 `range_pow_padicValNat_subset_divisors`

English:
theorem range_pow_padicValNat_subset_divisors
  given: {n : Nat} (hn : n != 0)
  proof: by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by lia).trans pow_padicValNat_dvd, hn⟩

中文:
定理 range_pow_padicVal自然数_subset_divisors
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by lia).trans pow_padicValNat_dvd, hn⟩

Depends on / 依赖: Finset, Finset.mem_image, Finset.mem_range, Nat.mem_divisors, mem_divisors, mem_image, mem_range, pow_dvd_pow, pow_padicValNat_dvd
-/
theorem range_pow_padicValNat_subset_divisors {n : Nat} (hn : n != 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) subseteq n.divisors := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by lia).trans pow_padicValNat_dvd, hn⟩

/--
theorem `range_pow_padicValNat_subset_divisors'` / 定理 `range_pow_padicValNat_subset_divisors'`

English:
theorem range_pow_padicValNat_subset_divisors'
  given: {n : Nat} [hp : Fact p.Prime]
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase]; rw [Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.

中文:
定理 range_pow_padicVal自然数_subset_divisors'
  条件: {n : 自然数} [hp : Fact p.素]
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase]; rw [Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.

Depends on / 依赖: Finset, Finset.mem_erase, Finset.mem_image, Finset.mem_range, Nat.mem_divisors, Nat.one_lt_pow, eq_or_ne, hp.out.one_lt, k.succ_ne_zero, mem_divisors, mem_erase, mem_image, mem_range, one_lt, one_lt_pow, pow_dvd_pow, pow_padicValNat_dvd, succ_le_iff, succ_ne_zero
-/
theorem range_pow_padicValNat_subset_divisors' {n : Nat} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) subseteq n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase]; rw [Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'

/--
theorem `padicValNat_factorial_mul` / 定理 `padicValNat_factorial_mul`

English:
theorem padicValNat_factorial_mul
  given: (n : Nat) [hp : Fact p.Prime]
  proof: by
  apply Nat.cast_injective (R := Nat∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n)]; rw [Nat.cast_add]; rw [padicValNat_eq_emultiplicity factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

中文:
定理 padicVal自然数_factorial_mul
  条件: (n : 自然数) [hp : Fact p.素]
  证明: by
  apply Nat.cast_injective (R := Nat∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n)]; rw [Nat.cast_add]; rw [padicValNat_eq_emultiplicity factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

Depends on / 依赖: Nat.cast_add, Nat.cast_injective, Prime.emultiplicity_factorial_mul, cast_add, cast_injective, emultiplicity_factorial_mul, factorial_ne_zero, hp.out, padicValNat_eq_emultiplicity
-/
theorem padicValNat_factorial_mul (n : Nat) [hp : Fact p.Prime] :
    padicValNat p (p * n)! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := Nat∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n)]; rw [Nat.cast_add]; rw [padicValNat_eq_emultiplicity factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

/--
theorem `padicValNat_eq_zero_of_mem_Ioo` / 定理 `padicValNat_eq_zero_of_mem_Ioo`

English:
theorem padicValNat_eq_zero_of_mem_Ioo
  statement: {m k : Nat}
  proof: padicValNat.eq_zero_of_not_dvd not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2

中文:
定理 padicVal自然数_eq_zero_of_mem_Ioo
  结论: {m k : 自然数}
  证明: padicValNat.eq_zero_of_not_dvd not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2

Depends on / 依赖: eq_zero_of_not_dvd, not_dvd_of_lt_of_lt_mul_succ, padicValNat, padicValNat.eq_zero_of_not_dvd
-/
theorem padicValNat_eq_zero_of_mem_Ioo {m k : Nat}
    (hm : m in Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0 :=
padicValNat.eq_zero_of_not_dvd not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2

/--
theorem `padicValNat_factorial_mul_add` / 定理 `padicValNat_factorial_mul_add`

English:
theorem padicValNat_factorial_mul_add
  given: {n : Nat} (m : Nat) [hp : Fact p.Prime] (h : n < p)
  proof: by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ]; rw [factorial_succ]; rw [padicValNat.mul (succ_ne_zero (p * m + n)) factorial_ne_zero (p * m + _)]; rw [hn lt_of_succ_lt h]; rw [← add_succ]; rw [padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n

中文:
定理 padicVal自然数_factorial_mul_add
  条件: {n : 自然数} (m : 自然数) [hp : Fact p.素] (h : n < p)
  证明: by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ]; rw [factorial_succ]; rw [padicValNat.mul (succ_ne_zero (p * m + n)) factorial_ne_zero (p * m + _)]; rw [hn lt_of_succ_lt h]; rw [← add_succ]; rw [padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n

Depends on / 依赖: Nat.lt_add_of_pos_right, Nat.mul_add, Nat.mul_one, add_lt_add_iff_left, add_succ, add_zero, factorial_ne_zero, factorial_succ, lt_add_of_pos_right, lt_of_succ_lt, mul_add, mul_one, padicValNat, padicValNat.mul, padicValNat_eq_zero_of_mem_Ioo, succ_ne_zero, succ_pos, zero_add
-/
theorem padicValNat_factorial_mul_add {n : Nat} (m : Nat) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n)! = padicValNat p (p * m)! := by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ]; rw [factorial_succ]; rw [padicValNat.mul (succ_ne_zero (p * m + n)) factorial_ne_zero (p * m + _)]; rw [hn lt_of_succ_lt h]; rw [← add_succ]; rw [padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n)]; rw [(Nat.mul_add _ _ _▸ Nat.mul_one _ ▸ ((add_lt_add_iff_left (p * m)).mpr h))⟩]; rw [zero_add]

/--
theorem `padicValNat_mul_div_factorial` / 定理 `padicValNat_mul_div_factorial`

English:
theorem padicValNat_mul_div_factorial
  given: (n : Nat) [hp : Fact p.Prime]
  proof: by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm

中文:
定理 padicVal自然数_mul_div_factorial
  条件: (n : 自然数) [hp : Fact p.素]
  证明: by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm
-/
@[simp] theorem padicValNat_mul_div_factorial (n : Nat) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm

/--
theorem `padicValNat_factorial` / 定理 `padicValNat_factorial`

English:
theorem padicValNat_factorial
  given: {n b : Nat} [hp : Fact p.Prime] (hnb : log p n < b)
  proof: by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

中文:
定理 padicVal自然数_factorial
  条件: {n b : 自然数} [hp : Fact p.素] (hnb : log p n < b)
  证明: by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

Depends on / 依赖: Prime.emultiplicity_factorial, emultiplicity_factorial, factorial_ne_zero, hp.out, padicValNat_eq_emultiplicity
-/
theorem padicValNat_factorial {n b : Nat} [hp : Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i in Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

/--
theorem `sub_one_mul_padicValNat_factorial` / 定理 `sub_one_mul_padicValNat_factorial`

English:
theorem sub_one_mul_padicValNat_factorial
  given: [hp : Fact p.Prime] (n : Nat)
  proof: by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt_add_one (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one]; rw [← Finset.sum_Ico_add' _ 0 _ 1]; rw [Ico_zero_eq_range]; rw [← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]; rw [Nat.succ_eq_add_one]

中文:
定理 sub_one_mul_padicVal自然数_factorial
  条件: [hp : Fact p.素] (n : 自然数)
  证明: by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt_add_one (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one]; rw [← Finset.sum_Ico_add' _ 0 _ 1]; rw [Ico_zero_eq_range]; rw [← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]; rw [Nat.succ_eq_add_one]

Depends on / 依赖: Finset, Finset.sum_Ico_add, Ico_zero_eq_range, Nat.succ_eq_add_one, lt_add_one, lt_succ_of_lt, nth_rw, padicValNat_factorial, sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, succ_eq_add_one, sum_Ico_add, zero_add
-/
theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : Nat) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt_add_one (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one]; rw [← Finset.sum_Ico_add' _ 0 _ 1]; rw [Ico_zero_eq_range]; rw [← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]; rw [Nat.succ_eq_add_one]

variable (p)

/--
theorem `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` / 定理 `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`

English:
theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero
  given: [hp : Fact p.Prime] {n : Nat} (hn : n != 0)
  proof: by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n != [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

中文:
定理 sub_one_mul_padicVal自然数_factorial_lt_of_ne_zero
  条件: [hp : Fact p.素] {n : 自然数} (hn : n != 0)
  证明: by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n != [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

Depends on / 依赖: List.getLast_mem, List.sum_pos_iff_exists_pos_nat.mpr, Nat.digits_ne_nil_iff_ne_zero.mpr, Nat.getLast_digit_ne_zero, Nat.pos_of_ne_zero, Nat.sub_lt_self, digit_sum_le, digits, digits_ne_nil_iff_ne_zero, getLast_digit_ne_zero, getLast_mem, p.digits, pos_of_ne_zero, sub_lt_self, sub_one_mul_padicValNat_factorial, sum_pos_iff_exists_pos_nat
-/
theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : Nat} (hn : n != 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n != [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

/--
theorem `padicValNat_factorial_lt_of_ne_zero` / 定理 `padicValNat_factorial_lt_of_ne_zero`

English:
theorem padicValNat_factorial_lt_of_ne_zero
  given: [hp : Fact p.Prime] {n : Nat} (hn : n != 0)
  proof: by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

中文:
定理 padicVal自然数_factorial_lt_of_ne_zero
  条件: [hp : Fact p.素] {n : 自然数} (hn : n != 0)
  证明: by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

Depends on / 依赖: Nat.Prime.one_lt, conv_lhs, hp.elim, le_sub_one_of_lt, lt_of_le_of_lt, one_lt, one_mul, padicValNat, sub_one_mul_padicValNat_factorial_lt_of_ne_zero
-/
theorem padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : Nat} (hn : n != 0) :
    padicValNat p n.factorial < n := by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

/--
theorem `padicValNat_factorial_le` / 定理 `padicValNat_factorial_le`

English:
theorem padicValNat_factorial_le
  given: [hp : Fact p.Prime] (n : Nat)
  statement: padicValNat p n.factorial <= n
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

中文:
定理 padicVal自然数_factorial_le
  条件: [hp : Fact p.素] (n : 自然数)
  结论: padicVal自然数 p n.factorial <= n
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

Depends on / 依赖: le_of_lt, padicValNat_factorial_lt_of_ne_zero
-/
theorem padicValNat_factorial_le [hp : Fact p.Prime] (n : Nat) : padicValNat p n.factorial <= n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

variable {p}

/--
theorem `padicValNat_choose` / 定理 `padicValNat_choose`

English:
theorem padicValNat_choose
  given: {n k b : Nat} [hp : Fact p.Prime] (hkn : k <= n) (hnb : log p n < b)
  proof: by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

中文:
定理 padicVal自然数_choose
  条件: {n k b : 自然数} [hp : Fact p.素] (hkn : k <= n) (hnb : log p n < b)
  证明: by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

Depends on / 依赖: Prime.emultiplicity_choose, choose_ne_zero, emultiplicity_choose, hp.out, padicValNat_eq_emultiplicity
-/
theorem padicValNat_choose {n k b : Nat} [hp : Fact p.Prime] (hkn : k <= n) (hnb : log p n < b) :
    padicValNat p (choose n k) = #{i in Finset.Ico 1 b | p ^ i <= k % p ^ i + (n - k) % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

/--
theorem `padicValNat_choose'` / 定理 `padicValNat_choose'`

English:
theorem padicValNat_choose'
  given: {n k b : Nat} [hp : Fact p.Prime] (hnb : log p (n + k) < b)
  proof: by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

中文:
定理 padicVal自然数_choose'
  条件: {n k b : 自然数} [hp : Fact p.素] (hnb : log p (n + k) < b)
  证明: by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

Depends on / 依赖: Nat.le_add_left, Prime.emultiplicity_choose, choose_ne_zero, emultiplicity_choose, hp.out, le_add_left, padicValNat_eq_emultiplicity
-/
theorem padicValNat_choose' {n k b : Nat} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
    padicValNat p (choose (n + k) k) = #{i in Finset.Ico 1 b | p ^ i <= k % p ^ i + n % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

/--
theorem `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` / 定理 `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`

English:
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
  given: {k n : Nat} [hp : Fact p.Prime]
  proof: by
  have h : k <= n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h]; rw [Nat.mul_sub_left_distrib]; rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]; rw [Nat.mul_add]
 

中文:
定理 sub_one_mul_padicVal自然数_choose_eq_sub_sum_digits'
  条件: {k n : 自然数} [hp : Fact p.素]
  证明: by
  have h : k <= n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h]; rw [Nat.mul_sub_left_distrib]; rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]; rw [Nat.mul_add]
 

Depends on / 依赖: Nat.add_sub_assoc, Nat.add_sub_cancel, Nat.choose_eq_factorial_div_factorial, Nat.le_add_left, Nat.mul_add, Nat.mul_sub_left_distrib, Nat.sub_add_comm, Nat.sub_r, Nat.sub_sub, add_sub_assoc, add_sub_cancel, choose_eq_factorial_div_factorial, digit_sum_le, div_of_dvd, factorial_mul_factorial_dvd_factorial, factorial_ne_zero, le_add_left, mul_add, mul_sub_left_distrib, padicValNat
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : Nat} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k <= n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h]; rw [Nat.mul_sub_left_distrib]; rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]; rw [Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k]; rw [Nat.add_sub_cancel n k]; rw [← Nat.add_sub_assoc <|
      digit_sum_le p n]; rw [Nat.sub_sub (k + n)]; rw [← Nat.sub_right_comm]; rw [Nat.sub_sub]; rw [sub_add_eq]; rw [add_comm]; rw [tsub_tsub_assoc (Nat.le_refl (k + n)) (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k))]; rw [Nat.sub_self (k + n)]; rw [zero_add]; rw [add_comm]

/--
theorem `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` / 定理 `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`

English:
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits
  statement: {k n : Nat} [hp : Fact p.Prime]
  proof: by
  convert! @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals lia

中文:
定理 sub_one_mul_padicVal自然数_choose_eq_sub_sum_digits
  结论: {k n : 自然数} [hp : Fact p.素]
  证明: by
  convert! @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals lia

Depends on / 依赖: all_goals, convert, sub_one_mul_padicValNat_choose_eq_sub_sum_digits
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : Nat} [hp : Fact p.Prime]
    (h : k <= n) : (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  convert! @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals lia

end padicValNat

section padicValInt

variable {p : Nat}

/--
theorem `padicValInt_dvd_iff_of_ne_one` / 定理 `padicValInt_dvd_iff_of_ne_one`

English:
theorem padicValInt_dvd_iff_of_ne_one
  given: (hp : p != 1) (n : Nat) (a : Int)
  proof: by
  rw [padicValInt]; rw [← Int.natAbs_eq_zero]; rw [← padicValNat_dvd_iff_of_ne_one hp]; rw [← Int.natCast_dvd]; rw [Int.natCast_pow]

中文:
定理 padicVal整数_dvd_iff_of_ne_one
  条件: (hp : p != 1) (n : 自然数) (a : 整数)
  证明: by
  rw [padicValInt]; rw [← Int.natAbs_eq_zero]; rw [← padicValNat_dvd_iff_of_ne_one hp]; rw [← Int.natCast_dvd]; rw [Int.natCast_pow]

Depends on / 依赖: Int.natAbs_eq_zero, Int.natCast_dvd, Int.natCast_pow, natAbs_eq_zero, natCast_dvd, natCast_pow, padicValInt, padicValNat_dvd_iff_of_ne_one
-/
theorem padicValInt_dvd_iff_of_ne_one (hp : p != 1) (n : Nat) (a : Int) :
    (p : Int) ^ n ∣ a ↔ a = 0 ∨ n <= padicValInt p a := by
  rw [padicValInt]; rw [← Int.natAbs_eq_zero]; rw [← padicValNat_dvd_iff_of_ne_one hp]; rw [← Int.natCast_dvd]; rw [Int.natCast_pow]

/--
theorem `padicValInt_dvd_iff` / 定理 `padicValInt_dvd_iff`

English:
theorem padicValInt_dvd_iff
  given: [hp : Fact p.Prime] (n : Nat) (a : Int)
  proof: padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a

中文:
定理 padicVal整数_dvd_iff
  条件: [hp : Fact p.素] (n : 自然数) (a : 整数)
  证明: padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a

Depends on / 依赖: hp.out.ne_one, ne_one, padicValInt_dvd_iff_of_ne_one
-/
theorem padicValInt_dvd_iff [hp : Fact p.Prime] (n : Nat) (a : Int) :
    (p : Int) ^ n ∣ a ↔ a = 0 ∨ n <= padicValInt p a :=
  padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a

/--
theorem `padicValInt_dvd` / 定理 `padicValInt_dvd`

English:
theorem padicValInt_dvd
  given: (a : Int)
  statement: (p : Int) ^ padicValInt p a ∣ a
  proof: by
  by_cases hp : p = 1
  · rw [hp, Nat.cast_one, one_pow]; exact one_dvd _
  rw [padicValInt_dvd_iff_of_ne_one hp]
  exact Or.inr le_rfl

中文:
定理 padicVal整数_dvd
  条件: (a : 整数)
  结论: (p : 整数) ^ padicVal整数 p a ∣ a
  证明: by
  by_cases hp : p = 1
  · rw [hp, Nat.cast_one, one_pow]; exact one_dvd _
  rw [padicValInt_dvd_iff_of_ne_one hp]
  exact Or.inr le_rfl

Depends on / 依赖: Nat.cast_one, Or.inr, cast_one, le_rfl, one_dvd, one_pow, padicValInt_dvd_iff_of_ne_one
-/
theorem padicValInt_dvd (a : Int) : (p : Int) ^ padicValInt p a ∣ a := by
  by_cases hp : p = 1
  · rw [hp, Nat.cast_one, one_pow]; exact one_dvd _
  rw [padicValInt_dvd_iff_of_ne_one hp]
  exact Or.inr le_rfl

/--
theorem `padicValInt_self` / 定理 `padicValInt_self`

English:
theorem padicValInt_self
  given: [hp : Fact p.Prime]
  statement: padicValInt p p = 1
  proof: padicValInt.self hp.out.one_lt

中文:
定理 padicVal整数_self
  条件: [hp : Fact p.素]
  结论: padicVal整数 p p = 1
  证明: padicValInt.self hp.out.one_lt

Depends on / 依赖: hp.out.one_lt, one_lt, padicValInt, padicValInt.self
-/
theorem padicValInt_self [hp : Fact p.Prime] : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt

/--
theorem `padicValInt.mul` / 定理 `padicValInt.mul`

English:
theorem padicValInt.mul
  given: [hp : Fact p.Prime] {a b : Int} (ha : a != 0) (hb : b != 0)
  proof: by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul]; rw [padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]

中文:
定理 padicVal整数.mul
  条件: [hp : Fact p.素] {a b : 整数} (ha : a != 0) (hb : b != 0)
  证明: by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul]; rw [padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]

Depends on / 依赖: Int.natAbs_mul, Int.natAbs_ne_zero, natAbs_mul, natAbs_ne_zero, padicValInt, padicValNat, padicValNat.mul, simp_rw
-/
theorem padicValInt.mul [hp : Fact p.Prime] {a b : Int} (ha : a != 0) (hb : b != 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul]; rw [padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]

/--
theorem `padicValInt_mul_eq_succ` / 定理 `padicValInt_mul_eq_succ`

English:
theorem padicValInt_mul_eq_succ
  given: [hp : Fact p.Prime] (a : Int) (ha : a != 0)
  proof: by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

中文:
定理 padicVal整数_mul_eq_succ
  条件: [hp : Fact p.素] (a : 整数) (ha : a != 0)
  证明: by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

Depends on / 依赖: Int.natCast_ne_zero.mpr, hp.out.ne_zero, natCast_ne_zero, ne_zero, of_nat, padicValInt, padicValInt.mul, padicValInt.of_nat, padicValNat_self
-/
theorem padicValInt_mul_eq_succ [hp : Fact p.Prime] (a : Int) (ha : a != 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

end padicValInt
