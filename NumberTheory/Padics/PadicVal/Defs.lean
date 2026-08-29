/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.Nat.Factors

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.
-/

@[expose] public section

assert_not_exists Field

universe u

open Nat

variable {p : Nat}

/--
theorem `padicValNat_eq_emultiplicity_of_ne_one` / 定理 `padicValNat_eq_emultiplicity_of_ne_one`

English:
theorem padicValNat_eq_emultiplicity_of_ne_one
  given: (hp : p != 1) {n : Nat} (hn : n != 0)
  proof: by
  rw [eq_comm]; rw [emultiplicity_eq_coe]; rw [pow_dvd_iff_le_padicValNat hp hn]; rw [pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]

中文:
定理 padicValNat_eq_emultiplicity_of_ne_one
  条件: (hp : p != 1) {n : 自然数} (hn : n != 0)
  证明: by
  rw [eq_comm]; rw [emultiplicity_eq_coe]; rw [pow_dvd_iff_le_padicValNat hp hn]; rw [pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]

Depends on / 依赖: emultiplicity_eq_coe, eq_comm, pow_dvd_iff_le_padicValNat
-/
theorem padicValNat_eq_emultiplicity_of_ne_one (hp : p != 1) {n : Nat} (hn : n != 0) :
    padicValNat p n = emultiplicity p n := by
  rw [eq_comm]; rw [emultiplicity_eq_coe]; rw [pow_dvd_iff_le_padicValNat hp hn]; rw [pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]
/--
theorem `Nat.toNat_emultiplicity` / 定理 `Nat.toNat_emultiplicity`

English:
theorem Nat.toNat_emultiplicity
  given: (p n : Nat)
  statement: (emultiplicity p n).toNat = padicValNat p n
  proof: by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← padicValNat_eq_emultiplicity_of_ne_one, *]

中文:
定理 Nat.toNat_emultiplicity
  条件: (p n : 自然数)
  结论: (emultiplicity p n).to自然数 = padicVal自然数 p n
  证明: by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← padicValNat_eq_emultiplicity_of_ne_one, *]

Depends on / 依赖: eq_or_ne, padicValNat_eq_emultiplicity_of_ne_one
-/
theorem Nat.toNat_emultiplicity (p n : Nat) : (emultiplicity p n).toNat = padicValNat p n := by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← padicValNat_eq_emultiplicity_of_ne_one, *]

/--
theorem `padicValNat_def'` / 定理 `padicValNat_def'`

English:
theorem padicValNat_def'
  given: {n : Nat} (hp : p != 1) (hn : n != 0)
  proof: .symm multiplicity_eq_of_emultiplicity_eq_some .symm
    padicValNat_eq_emultiplicity_of_ne_one hp hn

中文:
定理 padicValNat_def'
  条件: {n : 自然数} (hp : p != 1) (hn : n != 0)
  证明: .symm multiplicity_eq_of_emultiplicity_eq_some .symm
    padicValNat_eq_emultiplicity_of_ne_one hp hn

Depends on / 依赖: multiplicity_eq_of_emultiplicity_eq_some, padicValNat_eq_emultiplicity_of_ne_one
-/
theorem padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0) :
    padicValNat p n = multiplicity p n :=
.symm multiplicity_eq_of_emultiplicity_eq_some .symm
    padicValNat_eq_emultiplicity_of_ne_one hp hn

/--
theorem `padicValNat_def` / 定理 `padicValNat_def`

English:
theorem padicValNat_def
  given: [hp : Fact p.Prime] {n : Nat} (hn : n != 0)
  proof: padicValNat_def' hp.out.ne_one hn

中文:
定理 padicValNat_def
  条件: [hp : Fact p.Prime] {n : 自然数} (hn : n != 0)
  证明: padicValNat_def' hp.out.ne_one hn

Depends on / 依赖: hp.out.ne_one, ne_one, padicValNat_def
-/
theorem padicValNat_def [hp : Fact p.Prime] {n : Nat} (hn : n != 0) :
    padicValNat p n = multiplicity p n :=
  padicValNat_def' hp.out.ne_one hn

/--
theorem `padicValNat_eq_emultiplicity` / 定理 `padicValNat_eq_emultiplicity`

English:
theorem padicValNat_eq_emultiplicity
  given: [hp : Fact p.Prime] {n : Nat} (hn : n != 0)
  proof: padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

中文:
定理 padicValNat_eq_emultiplicity
  条件: [hp : Fact p.Prime] {n : 自然数} (hn : n != 0)
  证明: padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

Depends on / 依赖: hp.out.ne_one, ne_one, padicValNat_eq_emultiplicity_of_ne_one
-/
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : Nat} (hn : n != 0) :
    padicValNat p n = emultiplicity p n :=
  padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

namespace padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_emultiplicity := padicValNat_eq_emultiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_multiplicity := padicValNat_def'

@[deprecated padicValNat_zero_right (since := "2026-03-15")]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: padicValNat p 0 = 0
  proof: padicValNat_zero_right p

@[deprecated padicValNat_one_right (since := "2026-03-15")]

中文:
定理 zero
  结论: padicVal自然数 p 0 = 0
  证明: padicValNat_zero_right p

@[deprecated padicValNat_one_right (since := "2026-03-15")]
-/
protected theorem zero : padicValNat p 0 = 0 := padicValNat_zero_right p

@[deprecated padicValNat_one_right (since := "2026-03-15")]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: padicValNat p 1 = 0
  proof: padicValNat_one_right p

@[simp]

中文:
定理 one
  结论: padicVal自然数 p 1 = 0
  证明: padicValNat_one_right p

@[simp]
-/
protected theorem one : padicValNat p 1 = 0 := padicValNat_one_right p

@[simp]
/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {n : Nat}
  statement: padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n
  proof: by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
.not .symm simpa [*] using pow_dvd_iff_le_padicValNat (k := 1) hp₁ hn₀

中文:
定理 eq_zero_iff
  条件: {n : 自然数}
  结论: padicVal自然数 p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n
  证明: by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
.not .symm simpa [*] using pow_dvd_iff_le_padicValNat (k := 1) hp₁ hn₀

Depends on / 依赖: eq_or_ne, pow_dvd_iff_le_padicValNat
-/
theorem eq_zero_iff {n : Nat} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
.not .symm simpa [*] using pow_dvd_iff_le_padicValNat (k := 1) hp₁ hn₀

end padicValNat

open List

/--
theorem `le_emultiplicity_iff_replicate_subperm_primeFactorsList` / 定理 `le_emultiplicity_iff_replicate_subperm_primeFactorsList`

English:
theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList
  statement: {a b : Nat} {n : Nat} (ha : a.Prime)
  proof: (replicate_subperm_primeFactorsList_iff ha hb).trans
.symm pow_dvd_iff_le_emultiplicity

中文:
定理 le_emultiplicity_iff_replicate_subperm_primeFactorsList
  结论: {a b : 自然数} {n : 自然数} (ha : a.Prime)
  证明: (replicate_subperm_primeFactorsList_iff ha hb).trans
.symm pow_dvd_iff_le_emultiplicity

Depends on / 依赖: pow_dvd_iff_le_emultiplicity, replicate_subperm_primeFactorsList_iff
-/
theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : Nat} {n : Nat} (ha : a.Prime)
    (hb : b != 0) :
    ↑n <= emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
.symm pow_dvd_iff_le_emultiplicity

/--
theorem `le_padicValNat_iff_replicate_subperm_primeFactorsList` / 定理 `le_padicValNat_iff_replicate_subperm_primeFactorsList`

English:
theorem le_padicValNat_iff_replicate_subperm_primeFactorsList
  statement: {a b : Nat} {n : Nat} (ha : a.Prime)
  proof: by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb]; rw [Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one]; rw [Nat.pos_of_ne_zero hb⟩
.emultiplicity_eq_multiplicity]; rw [← padicValNat_def' ha.ne_one hb]; rw [Nat.cast_le]

中文:
定理 le_padicValNat_iff_replicate_subperm_primeFactorsList
  结论: {a b : 自然数} {n : 自然数} (ha : a.Prime)
  证明: by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb]; rw [Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one]; rw [Nat.pos_of_ne_zero hb⟩
.emultiplicity_eq_multiplicity]; rw [← padicValNat_def' ha.ne_one hb]; rw [Nat.cast_le]

Depends on / 依赖: Nat.cast_le, Nat.finiteMultiplicity_iff, Nat.pos_of_ne_zero, cast_le, emultiplicity_eq_multiplicity, finiteMultiplicity_iff, ha.ne_one, le_emultiplicity_iff_replicate_subperm_primeFactorsList, ne_one, padicValNat_def, pos_of_ne_zero
-/
theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : Nat} {n : Nat} (ha : a.Prime)
    (hb : b != 0) :
    n <= padicValNat a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb]; rw [Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one]; rw [Nat.pos_of_ne_zero hb⟩
.emultiplicity_eq_multiplicity]; rw [← padicValNat_def' ha.ne_one hb]; rw [Nat.cast_le]
