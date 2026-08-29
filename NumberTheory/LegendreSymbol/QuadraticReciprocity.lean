/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Quadratic reciprocity.

## Main results

We prove the law of quadratic reciprocity, see `legendreSym.quadratic_reciprocity` and
`legendreSym.quadratic_reciprocity'`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` and
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

We also prove the supplementary laws that give conditions for when `2` or `-2`
is a square modulo a prime `p`:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2` and
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Implementation notes

The proofs use results for quadratic characters on arbitrary finite fields
from `NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`, which in turn are based on
properties of quadratic Gauss sums as provided by `NumberTheory.LegendreSymbol.GaussSum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/

public section


open Nat

section Values

variable {p : Nat} [Fact p.Prime]

open ZMod

/-!
### The value of the Legendre symbol at `2` and `-2`

See `jacobiSym.at_two` and `jacobiSym.at_neg_two` for the corresponding statements
for the Jacobi symbol.
-/


namespace legendreSym

/--
theorem `at_two` / 定理 `at_two`

English:
theorem at_two
  given: (hp : p != 2)
  statement: legendreSym p 2 = χ₈ p
  proof: by
  have : (2 : ZMod p) = (2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

中文:
定理 at_two
  条件: (hp : p != 2)
  结论: legendreSym p 2 = χ₈ p
  证明: by
  have : (2 : ZMod p) = (2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

Depends on / 依赖: legendreSym, quadraticChar_two, ringChar_zmod_n, substr
-/
theorem at_two (hp : p != 2) : legendreSym p 2 = χ₈ p := by
  have : (2 : ZMod p) = (2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

/--
theorem `at_neg_two` / 定理 `at_neg_two`

English:
theorem at_neg_two
  given: (hp : p != 2)
  statement: legendreSym p (-2) = χ₈' p
  proof: by
  have : (-2 : ZMod p) = (-2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_neg_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

中文:
定理 at_neg_two
  条件: (hp : p != 2)
  结论: legendreSym p (-2) = χ₈' p
  证明: by
  have : (-2 : ZMod p) = (-2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_neg_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

Depends on / 依赖: legendreSym, quadraticChar_neg_two, ringChar_zmod_n, substr
-/
theorem at_neg_two (hp : p != 2) : legendreSym p (-2) = χ₈' p := by
  have : (-2 : ZMod p) = (-2 : Int) := by norm_cast
  rw [legendreSym]; rw [← this]; rw [quadraticChar_neg_two ((ringChar_zmod_n p).substr hp)]; rw [card p]

end legendreSym

namespace ZMod

/--
theorem `exists_sq_eq_two_iff` / 定理 `exists_sq_eq_two_iff`

English:
theorem exists_sq_eq_two_iff
  given: (hp : p != 2)
  statement: IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7
  proof: by
  rw [FiniteField.isSquare_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

中文:
定理 exists_sq_eq_two_iff
  条件: (hp : p != 2)
  结论: IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7
  证明: by
  rw [FiniteField.isSquare_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

Depends on / 依赖: Fact.out, FiniteField, FiniteField.isSquare_two_iff, Prime.mod_two_eq_one_iff_ne_two, isSquare_two_iff, mod_two_eq_one_iff_ne_two
-/
theorem exists_sq_eq_two_iff (hp : p != 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  rw [FiniteField.isSquare_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

/--
theorem `exists_sq_eq_neg_two_iff` / 定理 `exists_sq_eq_neg_two_iff`

English:
theorem exists_sq_eq_neg_two_iff
  given: (hp : p != 2)
  statement: IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3
  proof: by
  rw [FiniteField.isSquare_neg_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

中文:
定理 exists_sq_eq_neg_two_iff
  条件: (hp : p != 2)
  结论: IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3
  证明: by
  rw [FiniteField.isSquare_neg_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

Depends on / 依赖: Fact.out, FiniteField, FiniteField.isSquare_neg_two_iff, Prime.mod_two_eq_one_iff_ne_two, isSquare_neg_two_iff, mod_two_eq_one_iff_ne_two
-/
theorem exists_sq_eq_neg_two_iff (hp : p != 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff]; rw [card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

end ZMod

end Values

section Reciprocity

/-!
### The Law of Quadratic Reciprocity

See `jacobiSym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
for the Jacobi symbol.
-/


variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

namespace legendreSym

open ZMod

/--
theorem `quadratic_reciprocity` / 定理 `quadratic_reciprocity`

English:
theorem quadratic_reciprocity
  given: (hp : p != 2) (hq : q != 2) (hpq : p != q)
  proof: by
  have hp₁ := (Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left hp
  have hq₁ := (Prime.eq_two_or_odd <| @Fact.out q.Prime _).resolve_left hq
  have hq₂ : ringChar (ZMod q) != 2 := (ringChar_zmod_n q).substr hq
  have h :=
    quadraticChar_odd_prime ((ringChar_zmod_n p).substr hp) hq ((r

中文:
定理 quadratic_reciprocity
  条件: (hp : p != 2) (hq : q != 2) (hpq : p != q)
  证明: by
  have hp₁ := (Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left hp
  have hq₁ := (Prime.eq_two_or_odd <| @Fact.out q.Prime _).resolve_left hq
  have hq₂ : ringChar (ZMod q) != 2 := (ringChar_zmod_n q).substr hq
  have h :=
    quadraticChar_odd_prime ((ringChar_zmod_n p).substr hp) hq ((r

Depends on / 依赖: Fact.out, Prime.eq_two_or_odd, eq_two_or_odd, p.Prime, q.Prime, quadraticChar_odd_prime, resolve_left, ringChar, ringChar_zmod_n, substr
-/
theorem quadratic_reciprocity (hp : p != 2) (hq : q != 2) (hpq : p != q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  have hp₁ := (Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left hp
  have hq₁ := (Prime.eq_two_or_odd <| @Fact.out q.Prime _).resolve_left hq
  have hq₂ : ringChar (ZMod q) != 2 := (ringChar_zmod_n q).substr hq
  have h :=
    quadraticChar_odd_prime ((ringChar_zmod_n p).substr hp) hq ((ringChar_zmod_n p).substr hpq)
  rw [card p] at h
  have nc : forall n r : Nat, ((n : Int) : ZMod r) = n := fun n r => by norm_cast
  have nc' : (((-1) ^ (p / 2) : Int) : ZMod q) = (-1) ^ (p / 2) := by norm_cast
  rw [legendreSym]; rw [legendreSym]; rw [nc]; rw [nc]; rw [h]; rw [map_mul]; rw [mul_rotate']; rw [mul_comm (p / 2)]; rw [← pow_two]; rw [quadraticChar_sq_one (prime_ne_zero q p hpq.symm)]; rw [mul_one]; rw [pow_mul]; rw [χ₄_eq_neg_one_pow hp₁]; rw [nc']; rw [map_pow]; rw [quadraticChar_neg_one hq₂]; rw [card q]; rw [χ₄_eq_neg_one_pow hq₁]

/--
theorem `quadratic_reciprocity'` / 定理 `quadratic_reciprocity'`

English:
theorem quadratic_reciprocity'
  given: (hp : p != 2) (hq : q != 2)
  proof: by
  rcases eq_or_ne p q with rfl | h
  · rw [(eq_zero_iff p p).mpr (mod_cast natCast_self p), mul_zero]
  · have qr := congr_arg (· * legendreSym p q) (quadratic_reciprocity hp hq h)
    have : ((q : Int) : ZMod p) != 0 := mod_cast prime_ne_zero p q h
    simpa only [mul_assoc, ← pow_two, sq_one p 

中文:
定理 quadratic_reciprocity'
  条件: (hp : p != 2) (hq : q != 2)
  证明: by
  rcases eq_or_ne p q with rfl | h
  · rw [(eq_zero_iff p p).mpr (mod_cast natCast_self p), mul_zero]
  · have qr := congr_arg (· * legendreSym p q) (quadratic_reciprocity hp hq h)
    have : ((q : Int) : ZMod p) != 0 := mod_cast prime_ne_zero p q h
    simpa only [mul_assoc, ← pow_two, sq_one p 

Depends on / 依赖: congr_arg, eq_or_ne, eq_zero_iff, legendreSym, mod_cast, mul_assoc, mul_one, mul_zero, natCast_self, pow_two, prime_ne_zero, quadratic_reciprocity, sq_one
-/
theorem quadratic_reciprocity' (hp : p != 2) (hq : q != 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q := by
  rcases eq_or_ne p q with rfl | h
  · rw [(eq_zero_iff p p).mpr (mod_cast natCast_self p), mul_zero]
  · have qr := congr_arg (· * legendreSym p q) (quadratic_reciprocity hp hq h)
    have : ((q : Int) : ZMod p) != 0 := mod_cast prime_ne_zero p q h
    simpa only [mul_assoc, ← pow_two, sq_one p this, mul_one] using qr

/--
theorem `quadratic_reciprocity_one_mod_four` / 定理 `quadratic_reciprocity_one_mod_four`

English:
theorem quadratic_reciprocity_one_mod_four
  given: (hp : p % 4 = 1) (hq : q != 2)
  proof: by
  rw [quadratic_reciprocity'
      ((Prime.mod_two_eq_one_iff_ne_two Fact.out).mp (odd_of_mod_four_eq_one hp)) hq]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four hp]; rw [one_pow]; rw [one_mul]

中文:
定理 quadratic_reciprocity_one_mod_four
  条件: (hp : p % 4 = 1) (hq : q != 2)
  证明: by
  rw [quadratic_reciprocity'
      ((Prime.mod_two_eq_one_iff_ne_two Fact.out).mp (odd_of_mod_four_eq_one hp)) hq]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four hp]; rw [one_pow]; rw [one_mul]

Depends on / 依赖: Fact.out, Prime.mod_two_eq_one_iff_ne_two, mod_two_eq_one_iff_ne_two, neg_one_pow_div_two_of_one_mod_four, odd_of_mod_four_eq_one, one_mul, one_pow, pow_mul, quadratic_reciprocity
-/
theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q != 2) :
    legendreSym q p = legendreSym p q := by
  rw [quadratic_reciprocity'
      ((Prime.mod_two_eq_one_iff_ne_two Fact.out).mp (odd_of_mod_four_eq_one hp)) hq]; rw [pow_mul]; rw [neg_one_pow_div_two_of_one_mod_four hp]; rw [one_pow]; rw [one_mul]

/--
theorem `quadratic_reciprocity_three_mod_four` / 定理 `quadratic_reciprocity_three_mod_four`

English:
theorem quadratic_reciprocity_three_mod_four
  given: (hp : p % 4 = 3) (hq : q % 4 = 3)
  proof: by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity']; rw [pow_mul]; rw [nop hp]; rw [nop hq]; rw [neg_one_mul] <;>
  rwa [← Prime.mod_two_eq_one_iff_ne_two Fact.out, odd_of_mod_four_eq_three]

中文:
定理 quadratic_reciprocity_three_mod_four
  条件: (hp : p % 4 = 3) (hq : q % 4 = 3)
  证明: by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity']; rw [pow_mul]; rw [nop hp]; rw [nop hq]; rw [neg_one_mul] <;>
  rwa [← Prime.mod_two_eq_one_iff_ne_two Fact.out, odd_of_mod_four_eq_three]

Depends on / 依赖: Fact.out, Prime.mod_two_eq_one_iff_ne_two, mod_two_eq_one_iff_ne_two, neg_one_mul, neg_one_pow_div_two_of_three_mod_four, odd_of_mod_four_eq_three, pow_mul, quadratic_reciprocity
-/
theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity']; rw [pow_mul]; rw [nop hp]; rw [nop hq]; rw [neg_one_mul] <;>
  rwa [← Prime.mod_two_eq_one_iff_ne_two Fact.out, odd_of_mod_four_eq_three]

end legendreSym

namespace ZMod

open legendreSym

/--
theorem `exists_sq_eq_prime_iff_of_mod_four_eq_one` / 定理 `exists_sq_eq_prime_iff_of_mod_four_eq_one`

English:
theorem exists_sq_eq_prime_iff_of_mod_four_eq_one
  given: (hp1 : p % 4 = 1) (hq1 : q != 2)
  proof: by
  rcases eq_or_ne p q with rfl | h
  · rfl
  · rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
      quadratic_reciprocity_one_mod_four hp1 hq1]

中文:
定理 exists_sq_eq_prime_iff_of_mod_four_eq_one
  条件: (hp1 : p % 4 = 1) (hq1 : q != 2)
  证明: by
  rcases eq_or_ne p q with rfl | h
  · rfl
  · rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
      quadratic_reciprocity_one_mod_four hp1 hq1]

Depends on / 依赖: eq_one_iff, eq_or_ne, h.symm, prime_ne_zero, quadratic_reciprocity_one_mod_four
-/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q != 2) :
    IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q) := by
  rcases eq_or_ne p q with rfl | h
  · rfl
  · rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
      quadratic_reciprocity_one_mod_four hp1 hq1]

/--
theorem `exists_sq_eq_prime_iff_of_mod_four_eq_three` / 定理 `exists_sq_eq_prime_iff_of_mod_four_eq_three`

English:
theorem exists_sq_eq_prime_iff_of_mod_four_eq_three
  statement: (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
  proof: by
  rw [← eq_one_iff' p (prime_ne_zero p q hpq)]; rw [← eq_neg_one_iff' q]; rw [quadratic_reciprocity_three_mod_four hp3 hq3]; rw [neg_inj]

中文:
定理 exists_sq_eq_prime_iff_of_mod_four_eq_three
  结论: (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
  证明: by
  rw [← eq_one_iff' p (prime_ne_zero p q hpq)]; rw [← eq_neg_one_iff' q]; rw [quadratic_reciprocity_three_mod_four hp3 hq3]; rw [neg_inj]

Depends on / 依赖: eq_neg_one_iff, eq_one_iff, neg_inj, prime_ne_zero, quadratic_reciprocity_three_mod_four
-/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    (hpq : p != q) : IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q) := by
  rw [← eq_one_iff' p (prime_ne_zero p q hpq)]; rw [← eq_neg_one_iff' q]; rw [quadratic_reciprocity_three_mod_four hp3 hq3]; rw [neg_inj]

end ZMod

end Reciprocity
