/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Legendre symbol

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendreSym p a`.
Note the order of arguments! The advantage of this form is that then `legendreSym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendreSym.at_neg_one` and `ZMod.exists_sq_eq_neg_one_iff` for `-1`.

See `NumberTheory.LegendreSymbol.QuadraticReciprocity` for the conditions when `2` and `-2`
are squares:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2`,
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section


open Nat

section Euler

namespace ZMod

variable (p : Nat) [Fact p.Prime]

/--
theorem `euler_criterion_units` / 定理 `euler_criterion_units`

English:
theorem euler_criterion_units
  given: (x : (ZMod p)ˣ)
  statement: (exists y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1
  proof: by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (exists y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

中文:
定理 euler_criterion_units
  条件: (x : (ZMod p)ˣ)
  结论: (存在 y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1
  证明: by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (exists y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

Depends on / 依赖: FiniteField, FiniteField.unit_isSquare_iff, IsSquare, eq_comm, eq_iff_true_of_subsingleton, exists_const, isSquare_iff_exists_sq, ringChar_zmod_n, simp_rw, unit_isSquare_iff
-/
theorem euler_criterion_units (x : (ZMod p)ˣ) : (exists y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (exists y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

/--
theorem `euler_criterion` / 定理 `euler_criterion`

English:
theorem euler_criterion
  given: {a : ZMod p} (ha : a != 0)
  statement: IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1
  proof: by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by
      rintro rfl
      simp [mul_zero, ne_eq] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

中文:
定理 euler_criterion
  条件: {a : ZMod p} (ha : a != 0)
  结论: IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1
  证明: by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by
      rintro rfl
      simp [mul_zero, ne_eq] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

Depends on / 依赖: Units.ext_iff, Units.mk0, Units.val_mk0, Units.val_mul, euler_criterion_units, ext_iff, hy.symm, iff_congr, mul_zero, ne_eq, val_mk0, val_mul
-/
theorem euler_criterion {a : ZMod p} (ha : a != 0) : IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1 := by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by
      rintro rfl
      simp [mul_zero, ne_eq] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pow_div_two_eq_neg_one_or_one` / 定理 `pow_div_two_eq_neg_one_or_one`

English:
theorem pow_div_two_eq_neg_one_or_one
  given: {a : ZMod p} (ha : a != 0)
  proof: by
  rcases Prime.eq_two_or_odd (@Fact.out p.Prime _) with rfl | hp_odd
  · revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff]; rw [← pow_add]; rw [← two_mul]; rw [two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

中文:
定理 pow_div_two_eq_neg_one_or_one
  条件: {a : ZMod p} (ha : a != 0)
  证明: by
  rcases Prime.eq_two_or_odd (@Fact.out p.Prime _) with rfl | hp_odd
  · revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff]; rw [← pow_add]; rw [← two_mul]; rw [two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

Depends on / 依赖: Fact.out, Prime.eq_two_or_odd, eq_two_or_odd, fin_cases, hp_odd, mul_self_eq_one_iff, p.Prime, pow_add, pow_card_sub_one_eq_one, revert, two_mul, two_mul_odd_div_two
-/
theorem pow_div_two_eq_neg_one_or_one {a : ZMod p} (ha : a != 0) :
    a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  rcases Prime.eq_two_or_odd (@Fact.out p.Prime _) with rfl | hp_odd
  · revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff]; rw [← pow_add]; rw [← two_mul]; rw [two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

end ZMod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/


open ZMod

variable (p : Nat) [Fact p.Prime]

/--
Definition of `legendreSym` / `legendreSym` 的定义

English:
definition legendreSym
  signature: (a : Int)
  body: quadraticChar (ZMod p) a

中文:
定义 legendreSym
  签名: (a : 整数)
  定义体: quadraticChar (ZMod p) a

Depends on / 依赖: quadraticChar
-/
def legendreSym (a : Int) : Int :=
  quadraticChar (ZMod p) a

namespace legendreSym

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_pow` / 定理 `eq_pow`

English:
theorem eq_pow
  given: (a : Int)
  statement: (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2)
  proof: by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym]; rw [quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert! quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm

中文:
定理 eq_pow
  条件: (a : 整数)
  结论: (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2)
  证明: by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym]; rw [quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert! quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm

Depends on / 依赖: Fact.out, Nat.div_pos, div_pos, eq_or_ne, legendreSym, p.Prime, quadraticChar_zero, ringChar, ringChar_zmod_n, succ_pos, symm.trans, two_le, zero_pow
-/
theorem eq_pow (a : Int) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym]; rw [quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert! quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm

/--
theorem `eq_one_or_neg_one` / 定理 `eq_one_or_neg_one`

English:
theorem eq_one_or_neg_one
  given: {a : Int} (ha : (a : ZMod p) != 0)
  proof: quadraticChar_dichotomy ha

中文:
定理 eq_one_or_neg_one
  条件: {a : 整数} (ha : (a : ZMod p) != 0)
  证明: quadraticChar_dichotomy ha

Depends on / 依赖: quadraticChar_dichotomy
-/
theorem eq_one_or_neg_one {a : Int} (ha : (a : ZMod p) != 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadraticChar_dichotomy ha

/--
theorem `eq_neg_one_iff_not_one` / 定理 `eq_neg_one_iff_not_one`

English:
theorem eq_neg_one_iff_not_one
  given: {a : Int} (ha : (a : ZMod p) != 0)
  proof: quadraticChar_eq_neg_one_iff_not_one ha

中文:
定理 eq_neg_one_iff_not_one
  条件: {a : 整数} (ha : (a : ZMod p) != 0)
  证明: quadraticChar_eq_neg_one_iff_not_one ha

Depends on / 依赖: quadraticChar_eq_neg_one_iff_not_one
-/
theorem eq_neg_one_iff_not_one {a : Int} (ha : (a : ZMod p) != 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadraticChar_eq_neg_one_iff_not_one ha

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: (a : Int)
  statement: legendreSym p a = 0 ↔ (a : ZMod p) = 0
  proof: quadraticChar_eq_zero_iff

@[simp]

中文:
定理 eq_zero_iff
  条件: (a : 整数)
  结论: legendreSym p a = 0 ↔ (a : ZMod p) = 0
  证明: quadraticChar_eq_zero_iff

@[simp]

Depends on / 依赖: quadraticChar_eq_zero_iff
-/
theorem eq_zero_iff (a : Int) : legendreSym p a = 0 ↔ (a : ZMod p) = 0 :=
  quadraticChar_eq_zero_iff

@[simp]
/--
theorem `at_zero` / 定理 `at_zero`

English:
theorem at_zero
  statement: legendreSym p 0 = 0
  proof: by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]

中文:
定理 at_zero
  结论: legendreSym p 0 = 0
  证明: by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]

Depends on / 依赖: Int.cast_zero, MulChar, MulChar.map_zero, cast_zero, legendreSym, map_zero
-/
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]
/--
theorem `at_one` / 定理 `at_one`

English:
theorem at_one
  statement: legendreSym p 1 = 1
  proof: by rw [legendreSym, Int.cast_one, MulChar.map_one]

中文:
定理 at_one
  结论: legendreSym p 1 = 1
  证明: by rw [legendreSym, Int.cast_one, MulChar.map_one]

Depends on / 依赖: Int.cast_one, MulChar, MulChar.map_one, cast_one, legendreSym, map_one
-/
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (a b : Int)
  statement: legendreSym p (a * b) = legendreSym p a * legendreSym p b
  proof: by
  simp [legendreSym, Int.cast_mul, map_mul]

中文:
定理 mul
  条件: (a b : 整数)
  结论: legendreSym p (a * b) = legendreSym p a * legendreSym p b
  证明: by
  simp [legendreSym, Int.cast_mul, map_mul]
-/
protected theorem mul (a b : Int) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : Int ->*₀ Int where
  body: legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

中文:
定义 hom
  签名: : 整数 ->*₀ 整数 where
  定义体: legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

Depends on / 依赖: legendreSym
-/
def hom : Int ->*₀ Int where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

/--
theorem `sq_one` / 定理 `sq_one`

English:
theorem sq_one
  given: {a : Int} (ha : (a : ZMod p) != 0)
  statement: legendreSym p a ^ 2 = 1
  proof: quadraticChar_sq_one ha

中文:
定理 sq_one
  条件: {a : 整数} (ha : (a : ZMod p) != 0)
  结论: legendreSym p a ^ 2 = 1
  证明: quadraticChar_sq_one ha

Depends on / 依赖: quadraticChar_sq_one
-/
theorem sq_one {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p a ^ 2 = 1 :=
  quadraticChar_sq_one ha

/--
theorem `sq_one'` / 定理 `sq_one'`

English:
theorem sq_one'
  given: {a : Int} (ha : (a : ZMod p) != 0)
  statement: legendreSym p (a ^ 2) = 1
  proof: by
  dsimp only [legendreSym]
  rw [Int.cast_pow]
  exact quadraticChar_sq_one' ha

中文:
定理 sq_one'
  条件: {a : 整数} (ha : (a : ZMod p) != 0)
  结论: legendreSym p (a ^ 2) = 1
  证明: by
  dsimp only [legendreSym]
  rw [Int.cast_pow]
  exact quadraticChar_sq_one' ha

Depends on / 依赖: Int.cast_pow, cast_pow, legendreSym, quadraticChar_sq_one
-/
theorem sq_one' {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p (a ^ 2) = 1 := by
  dsimp only [legendreSym]
  rw [Int.cast_pow]
  exact quadraticChar_sq_one' ha

/--
theorem `mod` / 定理 `mod`

English:
theorem mod
  given: (a : Int)
  statement: legendreSym p a = legendreSym p (a % p)
  proof: by
  simp only [legendreSym, intCast_mod]

中文:
定理 mod
  条件: (a : 整数)
  结论: legendreSym p a = legendreSym p (a % p)
  证明: by
  simp only [legendreSym, intCast_mod]
-/
protected theorem mod (a : Int) : legendreSym p a = legendreSym p (a % p) := by
  simp only [legendreSym, intCast_mod]

/--
theorem `eq_one_iff` / 定理 `eq_one_iff`

English:
theorem eq_one_iff
  given: {a : Int} (ha0 : (a : ZMod p) != 0)
  statement: legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
  proof: quadraticChar_one_iff_isSquare ha0

中文:
定理 eq_one_iff
  条件: {a : 整数} (ha0 : (a : ZMod p) != 0)
  结论: legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
  证明: quadraticChar_one_iff_isSquare ha0

Depends on / 依赖: quadraticChar_one_iff_isSquare
-/
theorem eq_one_iff {a : Int} (ha0 : (a : ZMod p) != 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p) :=
  quadraticChar_one_iff_isSquare ha0

/--
theorem `eq_one_iff'` / 定理 `eq_one_iff'`

English:
theorem eq_one_iff'
  given: {a : Nat} (ha0 : (a : ZMod p) != 0)
  proof: by
  rw [eq_one_iff]
  · norm_cast
  · exact mod_cast ha0

中文:
定理 eq_one_iff'
  条件: {a : 自然数} (ha0 : (a : ZMod p) != 0)
  证明: by
  rw [eq_one_iff]
  · norm_cast
  · exact mod_cast ha0

Depends on / 依赖: eq_one_iff, mod_cast
-/
theorem eq_one_iff' {a : Nat} (ha0 : (a : ZMod p) != 0) :
    legendreSym p a = 1 ↔ IsSquare (a : ZMod p) := by
  rw [eq_one_iff]
  · norm_cast
  · exact mod_cast ha0

/--
theorem `eq_neg_one_iff` / 定理 `eq_neg_one_iff`

English:
theorem eq_neg_one_iff
  given: {a : Int}
  statement: legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
  proof: quadraticChar_neg_one_iff_not_isSquare

中文:
定理 eq_neg_one_iff
  条件: {a : 整数}
  结论: legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
  证明: quadraticChar_neg_one_iff_not_isSquare

Depends on / 依赖: quadraticChar_neg_one_iff_not_isSquare
-/
theorem eq_neg_one_iff {a : Int} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) :=
  quadraticChar_neg_one_iff_not_isSquare

/--
theorem `eq_neg_one_iff'` / 定理 `eq_neg_one_iff'`

English:
theorem eq_neg_one_iff'
  given: {a : Nat}
  statement: legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
  proof: by
  rw [eq_neg_one_iff]; norm_cast

中文:
定理 eq_neg_one_iff'
  条件: {a : 自然数}
  结论: legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
  证明: by
  rw [eq_neg_one_iff]; norm_cast

Depends on / 依赖: eq_neg_one_iff
-/
theorem eq_neg_one_iff' {a : Nat} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [eq_neg_one_iff]; norm_cast

/--
theorem `card_sqrts` / 定理 `card_sqrts`

English:
theorem card_sqrts
  given: (hp : p != 2) (a : Int)
  proof: quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a

中文:
定理 card_sqrts
  条件: (hp : p != 2) (a : 整数)
  证明: quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a

Depends on / 依赖: quadraticChar_card_sqrts, ringChar_zmod_n, substr
-/
theorem card_sqrts (hp : p != 2) (a : Int) :
    ↑{x : ZMod p | x ^ 2 = a}.toFinset.card = legendreSym p a + 1 :=
  quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a

end legendreSym

end Legendre

section QuadraticForm

/-!
### Applications to binary quadratic forms
-/


namespace legendreSym

/--
theorem `eq_one_of_sq_sub_mul_sq_eq_zero` / 定理 `eq_one_of_sq_sub_mul_sq_eq_zero`

English:
theorem eq_one_of_sq_sub_mul_sq_eq_zero
  statement: {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0)
  proof: by
  apply_fun (· * y⁻¹ ^ 2) at hxy
  simp only [zero_mul] at hxy
  rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2)]; rw [mul_inv_cancel₀ hy]; rw [one_pow]; rw [mul_one]; rw [sub_eq_zero]; rw [pow_two] at hxy
  exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩

中文:
定理 eq_one_of_sq_sub_mul_sq_eq_zero
  结论: {p : 自然数} [Fact p.素] {a : 整数} (ha : (a : ZMod p) != 0)
  证明: by
  apply_fun (· * y⁻¹ ^ 2) at hxy
  simp only [zero_mul] at hxy
  rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2)]; rw [mul_inv_cancel₀ hy]; rw [one_pow]; rw [mul_one]; rw [sub_eq_zero]; rw [pow_two] at hxy
  exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩

Depends on / 依赖: apply_fun, eq_one_iff, hxy.symm, mul_one, one_pow, pow_two, sub_eq_zero, zero_mul
-/
theorem eq_one_of_sq_sub_mul_sq_eq_zero {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0)
    {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  apply_fun (· * y⁻¹ ^ 2) at hxy
  simp only [zero_mul] at hxy
  rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2)]; rw [mul_inv_cancel₀ hy]; rw [one_pow]; rw [mul_one]; rw [sub_eq_zero]; rw [pow_two] at hxy
  exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩

/--
theorem `eq_one_of_sq_sub_mul_sq_eq_zero'` / 定理 `eq_one_of_sq_sub_mul_sq_eq_zero'`

English:
theorem eq_one_of_sq_sub_mul_sq_eq_zero'
  statement: {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0)
  proof: by
  have hy : y != 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_zero_iff] at hxy
    exact hx hxy
  exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy

中文:
定理 eq_one_of_sq_sub_mul_sq_eq_zero'
  结论: {p : 自然数} [Fact p.素] {a : 整数} (ha : (a : ZMod p) != 0)
  证明: by
  have hy : y != 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_zero_iff] at hxy
    exact hx hxy
  exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy

Depends on / 依赖: eq_one_of_sq_sub_mul_sq_eq_zero, mul_zero, sq_eq_zero_iff, sub_zero, two_ne_zero, zero_pow
-/
theorem eq_one_of_sq_sub_mul_sq_eq_zero' {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0)
    {x y : ZMod p} (hx : x != 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  have hy : y != 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero]; rw [mul_zero]; rw [sub_zero]; rw [sq_eq_zero_iff] at hxy
    exact hx hxy
  exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy

/--
theorem `eq_zero_mod_of_eq_neg_one` / 定理 `eq_zero_mod_of_eq_neg_one`

English:
theorem eq_zero_mod_of_eq_neg_one
  statement: {p : Nat} [Fact p.Prime] {a : Int} (h : legendreSym p a = -1)
  proof: by
  have ha : (a : ZMod p) != 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  rcases imp_iff_or_not.mp (not_and'.mp hf) with hx | hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h

中文:
定理 eq_zero_mod_of_eq_neg_one
  结论: {p : 自然数} [Fact p.素] {a : 整数} (h : legendreSym p a = -1)
  证明: by
  have ha : (a : ZMod p) != 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  rcases imp_iff_or_not.mp (not_and'.mp hf) with hx | hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h

Depends on / 依赖: CharZero, CharZero.eq_neg_self_iff, eq_neg_self_iff, eq_one_of_sq_sub_mul_sq_eq_zero, eq_zero_iff, imp_iff_or_not, imp_iff_or_not.mp, not_and, one_ne_zero
-/
theorem eq_zero_mod_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : legendreSym p a = -1)
    {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have ha : (a : ZMod p) != 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  rcases imp_iff_or_not.mp (not_and'.mp hf) with hx | hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h

/--
theorem `prime_dvd_of_eq_neg_one` / 定理 `prime_dvd_of_eq_neg_one`

English:
theorem prime_dvd_of_eq_neg_one
  statement: {p : Nat} [Fact p.Prime] {a : Int} (h : legendreSym p a = -1) {x y : Int}
  proof: by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy

中文:
定理 prime_dvd_of_eq_neg_one
  结论: {p : 自然数} [Fact p.素] {a : 整数} (h : legendreSym p a = -1) {x y : 整数}
  证明: by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy

Depends on / 依赖: ZMod.intCast_zmod_eq_zero_iff_dvd, eq_zero_mod_of_eq_neg_one, intCast_zmod_eq_zero_iff_dvd, simp_rw
-/
theorem prime_dvd_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : legendreSym p a = -1) {x y : Int}
    (hxy : (p : Int) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y := by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy

end legendreSym

end QuadraticForm

section Values

/-!
### The value of the Legendre symbol at `-1`

See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/


variable {p : Nat} [Fact p.Prime]

open ZMod

/--
theorem `legendreSym.at_neg_one` / 定理 `legendreSym.at_neg_one`

English:
theorem legendreSym.at_neg_one
  given: (hp : p != 2)
  statement: legendreSym p (-1) = χ₄ p
  proof: by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]

中文:
定理 legendreSym.at_neg_one
  条件: (hp : p != 2)
  结论: legendreSym p (-1) = χ₄ p
  证明: by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]

Depends on / 依赖: Int.cast_neg, Int.cast_one, cast_neg, cast_one, legendreSym, quadraticChar_neg_one, ringChar_zmod_n, substr
-/
theorem legendreSym.at_neg_one (hp : p != 2) : legendreSym p (-1) = χ₄ p := by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]

/--
theorem `legendreSym.at_neg` / 定理 `legendreSym.at_neg`

English:
theorem legendreSym.at_neg
  given: (hp : p != 2) (a : Int)
  statement: legendreSym p (-a) = χ₄ p * legendreSym p a
  proof: by
  rw [neg_eq_neg_one_mul]; rw [legendreSym.mul p (-1) a]; rw [legendreSym.at_neg_one hp]

中文:
定理 legendreSym.at_neg
  条件: (hp : p != 2) (a : 整数)
  结论: legendreSym p (-a) = χ₄ p * legendreSym p a
  证明: by
  rw [neg_eq_neg_one_mul]; rw [legendreSym.mul p (-1) a]; rw [legendreSym.at_neg_one hp]

Depends on / 依赖: at_neg_one, legendreSym, legendreSym.at_neg_one, legendreSym.mul, neg_eq_neg_one_mul
-/
theorem legendreSym.at_neg (hp : p != 2) (a : Int) : legendreSym p (-a) = χ₄ p * legendreSym p a := by
  rw [neg_eq_neg_one_mul]; rw [legendreSym.mul p (-1) a]; rw [legendreSym.at_neg_one hp]

namespace ZMod

/--
theorem `exists_sq_eq_neg_one_iff` / 定理 `exists_sq_eq_neg_one_iff`

English:
theorem exists_sq_eq_neg_one_iff
  statement: IsSquare (-1 : ZMod p) ↔ p % 4 != 3
  proof: by
  rw [FiniteField.isSquare_neg_one_iff]; rw [card p]

中文:
定理 存在_sq_eq_neg_one_iff
  结论: IsSquare (-1 : ZMod p) ↔ p % 4 != 3
  证明: by
  rw [FiniteField.isSquare_neg_one_iff]; rw [card p]

Depends on / 依赖: FiniteField, FiniteField.isSquare_neg_one_iff, isSquare_neg_one_iff
-/
theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 != 3 := by
  rw [FiniteField.isSquare_neg_one_iff]; rw [card p]

/--
theorem `mod_four_ne_three_of_sq_eq_neg_one` / 定理 `mod_four_ne_three_of_sq_eq_neg_one`

English:
theorem mod_four_ne_three_of_sq_eq_neg_one
  given: {y : ZMod p} (hy : y ^ 2 = -1)
  statement: p % 4 != 3
  proof: exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

中文:
定理 mod_four_ne_three_of_sq_eq_neg_one
  条件: {y : ZMod p} (hy : y ^ 2 = -1)
  结论: p % 4 != 3
  证明: exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

Depends on / 依赖: exists_sq_eq_neg_one_iff, pow_two
-/
theorem mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 != 3 :=
  exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

/--
theorem `mod_four_ne_three_of_sq_eq_neg_sq'` / 定理 `mod_four_ne_three_of_sq_eq_neg_sq'`

English:
theorem mod_four_ne_three_of_sq_eq_neg_sq'
  given: {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 = -y ^ 2)
  proof: @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2 at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)

中文:
定理 mod_four_ne_three_of_sq_eq_neg_sq'
  条件: {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 = -y ^ 2)
  证明: @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2 at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)

Depends on / 依赖: apply_fun, div_pow, div_self, mod_four_ne_three_of_sq_eq_neg_one, neg_div, one_pow
-/
theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 != 3 :=
  @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2 at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)

/--
theorem `mod_four_ne_three_of_sq_eq_neg_sq` / 定理 `mod_four_ne_three_of_sq_eq_neg_sq`

English:
theorem mod_four_ne_three_of_sq_eq_neg_sq
  given: {x y : ZMod p} (hx : x != 0) (hxy : x ^ 2 = -y ^ 2)
  proof: mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

中文:
定理 mod_four_ne_three_of_sq_eq_neg_sq
  条件: {x y : ZMod p} (hx : x != 0) (hxy : x ^ 2 = -y ^ 2)
  证明: mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

Depends on / 依赖: mod_four_ne_three_of_sq_eq_neg_sq, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mpr
-/
theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : ZMod p} (hx : x != 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 != 3 :=
  mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

end ZMod

end Values
