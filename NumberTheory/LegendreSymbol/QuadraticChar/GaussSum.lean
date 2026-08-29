/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# Quadratic characters of finite fields

Further facts relying on Gauss sums.

-/

public section


/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/--
theorem `quadraticChar_two` / 定理 `quadraticChar_two`

English:
theorem quadraticChar_two
  given: [DecidableEq F] (hF : ringChar F != 2)
  proof: IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))

中文:
定理 quadraticChar_two
  条件: [DecidableEq F] (hF : ringChar F != 2)
  证明: IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))

Depends on / 依赖: FiniteField, FiniteField.two_pow_card, IsQuadratic, IsQuadratic.eq_of_eq_coe, eq_of_eq_coe, quadraticChar_eq_pow_of_char_ne_two, quadraticChar_isQuadratic, two_pow_card
-/
theorem quadraticChar_two [DecidableEq F] (hF : ringChar F != 2) :
    quadraticChar F 2 = χ₈ (Fintype.card F) :=
  IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))

/--
theorem `FiniteField.isSquare_two_iff` / 定理 `FiniteField.isSquare_two_iff`

English:
theorem FiniteField.isSquare_two_iff
  proof: by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (Ring.two_ne_zero hF)]; rw [quadraticCh

中文:
定理 FiniteField.isSquare_two_iff
  证明: by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (Ring.two_ne_zero hF)]; rw [quadraticCh

Depends on / 依赖: FiniteField, FiniteField.even_card_of_char_two, FiniteField.isSquare_of_char_two, FiniteField.odd_card_of_char_ne_two, Ring.two_ne_zero, classical, even_card_of_char_two, isSquare_of_char_two, odd_card_of_char_ne_two, quadraticChar_one_iff_isSquare, quadraticChar_two, ringChar, true_iff, two_ne_zero
-/
theorem FiniteField.isSquare_two_iff :
    IsSquare (2 : F) ↔ Fintype.card F % 8 != 3 ∧ Fintype.card F % 8 != 5 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (Ring.two_ne_zero hF)]; rw [quadraticChar_two hF]; rw [χ₈_nat_eq_if_mod_eight]
    lia

/--
theorem `quadraticChar_neg_two` / 定理 `quadraticChar_neg_two`

English:
theorem quadraticChar_neg_two
  given: [DecidableEq F] (hF : ringChar F != 2)
  proof: by
  rw [(by simp : (-2 : F) = -1 * 2)]; rw [map_mul]; rw [χ₈'_eq_χ₄_mul_χ₈]; rw [quadraticChar_neg_one hF]; rw [quadraticChar_two hF]; rw [@cast_natCast _ (ZMod 4) _ _ _ (by decide : 4 ∣ 8)]

中文:
定理 quadraticChar_neg_two
  条件: [DecidableEq F] (hF : ringChar F != 2)
  证明: by
  rw [(by simp : (-2 : F) = -1 * 2)]; rw [map_mul]; rw [χ₈'_eq_χ₄_mul_χ₈]; rw [quadraticChar_neg_one hF]; rw [quadraticChar_two hF]; rw [@cast_natCast _ (ZMod 4) _ _ _ (by decide : 4 ∣ 8)]

Depends on / 依赖: cast_natCast, map_mul, quadraticChar_neg_one, quadraticChar_two
-/
theorem quadraticChar_neg_two [DecidableEq F] (hF : ringChar F != 2) :
    quadraticChar F (-2) = χ₈' (Fintype.card F) := by
  rw [(by simp : (-2 : F) = -1 * 2)]; rw [map_mul]; rw [χ₈'_eq_χ₄_mul_χ₈]; rw [quadraticChar_neg_one hF]; rw [quadraticChar_two hF]; rw [@cast_natCast _ (ZMod 4) _ _ _ (by decide : 4 ∣ 8)]

/--
theorem `FiniteField.isSquare_neg_two_iff` / 定理 `FiniteField.isSquare_neg_two_iff`

English:
theorem FiniteField.isSquare_neg_two_iff
  proof: by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Ring.two_ne_zero hF))

中文:
定理 FiniteField.isSquare_neg_two_iff
  证明: by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Ring.two_ne_zero hF))

Depends on / 依赖: FiniteField, FiniteField.even_card_of_char_two, FiniteField.isSquare_of_char_two, FiniteField.odd_card_of_char_ne_two, Ring.two_ne_zero, _nat_eq_if_mod_eight, classical, even_card_of_char_two, isSquare_of_char_two, neg_ne_zero, neg_ne_zero.mpr, odd_card_of_char_ne_two, quadraticChar_neg_two, quadraticChar_one_iff_isSquare, ringChar, true_iff, two_ne_zero
-/
theorem FiniteField.isSquare_neg_two_iff :
    IsSquare (-2 : F) ↔ Fintype.card F % 8 != 5 ∧ Fintype.card F % 8 != 7 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Ring.two_ne_zero hF))]; rw [quadraticChar_neg_two hF]; rw [χ₈'_nat_eq_if_mod_eight]
    lia

/--
theorem `quadraticChar_card_card` / 定理 `quadraticChar_card_card`

English:
theorem quadraticChar_card_card
  statement: [DecidableEq F] (hF : ringChar F != 2) {F' : Type*} [Field F']
  proof: by
  let χ := (quadraticChar F).ringHomComp (algebraMap Int F')
  have hχ₁ : χ != 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char

中文:
定理 quadraticChar_card_card
  结论: [DecidableEq F] (hF : ringChar F != 2) {F' : 类型} [Field F']
  证明: by
  let χ := (quadraticChar F).ringHomComp (algebraMap Int F')
  have hχ₁ : χ != 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char

Depends on / 依赖: Char.card_pow_card, Int.cast_neg, Int.cast_one, IsQuadratic, IsQuadratic.eq_of_eq_coe, Ring.neg_one_ne_one_of_char_ne_two, algebraMap, card_pow_card, cast_neg, cast_one, eq_intCast, eq_of_eq_coe, ne_one_iff, ne_one_iff.mpr, neg_one_ne_one_of_char_ne_two, quadraticChar, quadraticChar_eq_pow_of_char_ne_two, quadraticChar_exists_neg_one, quadraticChar_i, quadraticChar_isQuadratic
-/
theorem quadraticChar_card_card [DecidableEq F] (hF : ringChar F != 2) {F' : Type*} [Field F']
    [Fintype F'] [DecidableEq F'] (hF' : ringChar F' != 2) (h : ringChar F' != ringChar F) :
    quadraticChar F (Fintype.card F') =
    quadraticChar F' (quadraticChar F (-1) * Fintype.card F) := by
  let χ := (quadraticChar F).ringHomComp (algebraMap Int F')
  have hχ₁ : χ != 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char_ne_two hF'
  have h := Char.card_pow_card hχ₁ ((quadraticChar_isQuadratic F).comp _) h hF'
  rw [← quadraticChar_eq_pow_of_char_ne_two' hF'] at h
  exact (IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F')
    (quadraticChar_isQuadratic F) hF' h).symm

/--
theorem `quadraticChar_odd_prime` / 定理 `quadraticChar_odd_prime`

English:
theorem quadraticChar_odd_prime
  statement: [DecidableEq F] (hF : ringChar F != 2) {p : Nat} [Fact p.Prime]
  proof: by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h

中文:
定理 quadraticChar_odd_prime
  结论: [DecidableEq F] (hF : ringChar F != 2) {p : 自然数} [Fact p.Prime]
  证明: by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h

Depends on / 依赖: ne_of_eq_of_ne, quadraticChar_card_card, quadraticChar_neg_one, ringChar_zmod_n
-/
theorem quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F != 2) {p : Nat} [Fact p.Prime]
    (hp₁ : p != 2) (hp₂ : ringChar F != p) :
    quadraticChar F p = quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) := by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h

/--
theorem `FiniteField.isSquare_odd_prime_iff` / 定理 `FiniteField.isSquare_odd_prime_iff`

English:
theorem FiniteField.isSquare_odd_prime_iff
  statement: (hF : ringChar F != 2) {p : Nat} [Fact p.Prime]
  proof: by
  classical
  rcases eq_or_ne (ringChar F) p with rfl | hFp
  · obtain ⟨q, hq, hq'⟩ := FiniteField.card F (ringChar F)
    simp [hq']
  · rwa [← Iff.not_left quadraticChar_neg_one_iff_not_isSquare, quadraticChar_odd_prime hF hp]

中文:
定理 FiniteField.isSquare_odd_prime_iff
  结论: (hF : ringChar F != 2) {p : 自然数} [Fact p.Prime]
  证明: by
  classical
  rcases eq_or_ne (ringChar F) p with rfl | hFp
  · obtain ⟨q, hq, hq'⟩ := FiniteField.card F (ringChar F)
    simp [hq']
  · rwa [← Iff.not_left quadraticChar_neg_one_iff_not_isSquare, quadraticChar_odd_prime hF hp]

Depends on / 依赖: FiniteField, FiniteField.card, Iff.not_left, classical, eq_or_ne, not_left, quadraticChar_neg_one_iff_not_isSquare, quadraticChar_odd_prime, ringChar
-/
theorem FiniteField.isSquare_odd_prime_iff (hF : ringChar F != 2) {p : Nat} [Fact p.Prime]
    (hp : p != 2) :
    IsSquare (p : F) ↔ quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) != -1 := by
  classical
  rcases eq_or_ne (ringChar F) p with rfl | hFp
  · obtain ⟨q, hq, hq'⟩ := FiniteField.card F (ringChar F)
    simp [hq']
  · rwa [← Iff.not_left quadraticChar_neg_one_iff_not_isSquare, quadraticChar_odd_prime hF hp]

end SpecialValues
