/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/

public section


/--
theorem `isUnit_iff_not_dvd_char_of_ringChar_ne_zero` / 定理 `isUnit_iff_not_dvd_char_of_ringChar_ne_zero`

English:
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero
  statement: (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime]
  proof: by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.Prime := Fact.out
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr]; rw [← mul_assoc]; rw [mul_comm p]; rw [mul_assoc] at hq
   

中文:
定理 isUnit_iff_not_dvd_char_of_ringChar_ne_zero
  结论: (R : 类型) [交换环 R] (p : 自然数) [Fact p.素]
  证明: by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.Prime := Fact.out
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr]; rw [← mul_assoc]; rw [mul_comm p]; rw [mul_assoc] at hq
   

Depends on / 依赖: CharP.cast_eq_zero, Fact.out, IsUnit, IsUnit.exists_left_inv, Nat.Prime.not_dvd_one, apply_fun, cast_eq_zero, coprime_iff_not_dvd, exists_left_inv, hp.coprime_iff_not_dvd.mpr, isCoprime, mul_assoc, mul_comm, mul_one, ne_eq, not_dvd_one, nth_rw, p.Prime, ringChar, ringChar.dvd
-/
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime]
    (hR : ringChar R != 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.Prime := Fact.out
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr]; rw [← mul_assoc]; rw [mul_comm p]; rw [mul_assoc] at hq
      nth_rw 1 [← mul_one (ringChar R)] at hq
      exact Nat.Prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩
    simp_all only [ne_eq]
    grind [ringChar.dvd]
  · intro h
    rcases (hp.coprime_iff_not_dvd.mpr h).isCoprime with ⟨a, b, hab⟩
    apply_fun ((↑) : Int -> R) at hab
    push_cast at hab
    rw [hch]; rw [mul_zero]; rw [add_zero]; rw [mul_comm] at hab
    exact .of_mul_eq_one a hab

/--
theorem `isUnit_iff_not_dvd_char` / 定理 `isUnit_iff_not_dvd_char`

English:
theorem isUnit_iff_not_dvd_char
  given: (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime] [Finite R]
  proof: isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p CharP.char_ne_zero_of_finite R (ringChar R)

中文:
定理 isUnit_iff_not_dvd_char
  条件: (R : 类型) [交换环 R] (p : 自然数) [Fact p.素] [有限 R]
  证明: isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p CharP.char_ne_zero_of_finite R (ringChar R)

Depends on / 依赖: CharP.char_ne_zero_of_finite, char_ne_zero_of_finite, f.hom, isUnit_iff_not_dvd_char_of_ringChar_ne_zero, ringChar
-/
theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p CharP.char_ne_zero_of_finite R (ringChar R)

/--
theorem `prime_dvd_char_iff_dvd_card` / 定理 `prime_dvd_char_iff_dvd_card`

English:
theorem prime_dvd_char_iff_dvd_card
  given: {R : Type*} [CommRing R] [Fintype R] (p : Nat) [Fact p.Prime]
  proof: by
  refine
    ⟨fun h =>
h.trans
Int.natCast_dvd_natCast.mp
(CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zer

中文:
定理 prime_dvd_char_iff_dvd_card
  条件: {R : 类型} [交换环 R] [有限类型 R] (p : 自然数) [Fact p.素]
  证明: by
  refine
    ⟨fun h =>
h.trans
Int.natCast_dvd_natCast.mp
(CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zer

Depends on / 依赖: AddMonoid, AddMonoid.ad, CharP.intCast_eq_zero_iff, Fintype, Fintype.card, Int.natCast_dvd_natCast.mp, IsUnit, IsUnit.exists_left_inv, Nat.cast_card_eq_zero, addOrderOf_nsmul_eq_zero, apply_fun, cast_card_eq_zero, exists_left_inv, exists_prime_addOrderOf_dvd_card, h.trans, intCast_eq_zero_iff, isUnit_iff_not_dvd_char, mod_cast, mul_assoc, mul_zero
-/
theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : Nat) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine
    ⟨fun h =>
h.trans
Int.natCast_dvd_natCast.mp
(CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zero r
  rw [hr]; rw [nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u at hr₁
  rw [mul_zero]; rw [← mul_assoc]; rw [hu]; rw [one_mul] at hr₁
  exact mt AddMonoid.addOrderOf_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one Fact.out)) hr₁

/--
theorem `not_isUnit_prime_of_dvd_card` / 定理 `not_isUnit_prime_of_dvd_card`

English:
theorem not_isUnit_prime_of_dvd_card
  statement: {R : Type*} [CommRing R] [Fintype R] {p : Nat} [Fact p.Prime]
  proof: mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

中文:
定理 not_isUnit_prime_of_dvd_card
  结论: {R : 类型} [交换环 R] [有限类型 R] {p : 自然数} [Fact p.素]
  证明: mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

Depends on / 依赖: Classical, Classical.not_not.mpr, isUnit_iff_not_dvd_char, not_not, prime_dvd_char_iff_dvd_card
-/
theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] {p : Nat} [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

/--
lemma `charP_of_card_eq_prime` / 引理 `charP_of_card_eq_prime`

English:
lemma charP_of_card_eq_prime
  statement: {R : Type*} [NonAssocRing R] [Fintype R] {p : Nat} [hp : Fact p.Prime]
  proof: have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)

中文:
引理 charP_of_card_eq_prime
  结论: {R : 类型} [非结合环 R] [有限类型 R] {p : 自然数} [hp : Fact p.素]
  证明: have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)

Depends on / 依赖: CharP.charP_iff_prime_eq_zero, Fintype, Fintype.one_lt_card_iff_nontrivial, Nat.cast_card_eq_zero, cast_card_eq_zero, charP_iff_prime_eq_zero, one_lt, one_lt_card_iff_nontrivial
-/
lemma charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] {p : Nat} [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p :=
  have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)

/--
lemma `charP_of_card_eq_prime_pow` / 引理 `charP_of_card_eq_prime_pow`

English:
lemma charP_of_card_eq_prime_pow
  statement: {R : Type*} [CommRing R] [IsDomain R] [Fintype R] {p f : Nat}
  proof: have hf : f != 0 := fun h0 => not_subsingleton R
Fintype.card_le_one_iff_subsingleton.mp by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)

中文:
引理 charP_of_card_eq_prime_pow
  结论: {R : 类型} [交换环 R] [是整环 R] [有限类型 R] {p f : 自然数}
  证明: have hf : f != 0 := fun h0 => not_subsingleton R
Fintype.card_le_one_iff_subsingleton.mp by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)

Depends on / 依赖: CharP.charP_iff_prime_eq_zero, Fintype, Fintype.card_le_one_iff_subsingleton.mp, Nat.cast_card_eq_zero, card_le_one_iff_subsingleton, cast_card_eq_zero, charP_iff_prime_eq_zero, hR.le, hp.out, not_subsingleton
-/
lemma charP_of_card_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype R] {p f : Nat}
    [hp : Fact p.Prime] (hR : Fintype.card R = p ^ f) : CharP R p :=
have hf : f != 0 := fun h0 => not_subsingleton R
Fintype.card_le_one_iff_subsingleton.mp by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)
