/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Univariate polynomials form a domain

## Main results

* `Polynomial.instNoZeroDivisors`: `R[X]` has no zero divisors if `R` does not
* `Polynomial.instDomain`: `R[X]` is a domain if `R` is
-/

public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/--
lemma `natDegree_mul` / 引理 `natDegree_mul`

English:
lemma natDegree_mul
  given: (hp : p != 0) (hq : q != 0)
  statement: (p * q).natDegree = p.natDegree + q.natDegree
  proof: by
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero hp hq)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree hq]; rw [degree_mul]

omit [NoZeroDivisors R] in

中文:
引理 natDegree_mul
  条件: (hp : p != 0) (hq : q != 0)
  结论: (p * q).natDegree = p.natDegree + q.natDegree
  证明: by
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero hp hq)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree hq]; rw [degree_mul]

omit [NoZeroDivisors R] in

Depends on / 依赖: Nat.cast_add, Nat.cast_inj, WithBot, cast_add, cast_inj, degree_eq_natDegree, degree_mul, mul_ne_zero
-/
lemma natDegree_mul (hp : p != 0) (hq : q != 0) : (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [← Nat.cast_inj (R := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero hp hq)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree hp]; rw [← degree_eq_natDegree hq]; rw [degree_mul]

omit [NoZeroDivisors R] in
variable (p) in
/--
lemma `natDegree_smul` / 引理 `natDegree_smul`

English:
lemma natDegree_smul
  statement: {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module.IsTorsionFree S R]
  proof: by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simp only [coeff_smul]
      apply smul_ne_zero ha
      simp [hp]

@[simp]

中文:
引理 natDegree_smul
  结论: {S : 类型} [半环 S] [是整环 S] [模 S R] [模.是无挠 S R]
  证明: by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simp only [coeff_smul]
      apply smul_ne_zero ha
      simp [hp]

@[simp]

Depends on / 依赖: coeff_smul, le_refl, natDegree_eq_of_le_of_coeff_ne_zero, natDegree_smul_le, smul_ne_zero, smul_zero
-/
lemma natDegree_smul {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module.IsTorsionFree S R]
    {a : S} (ha : a != 0) : (a • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simp only [coeff_smul]
      apply smul_ne_zero ha
      simp [hp]

@[simp]
/--
lemma `natDegree_pow` / 引理 `natDegree_pow`

English:
lemma natDegree_pow
  given: (p : R[X]) (n : Nat)
  statement: natDegree (p ^ n) = n * natDegree p
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
exact natDegree_pow' by
    rw [← leadingCoeff_pow]; rw [Ne]; rw [leadingCoeff_eq_zero]; exact pow_ne_zero _ hp

中文:
引理 natDegree_pow
  条件: (p : R[X]) (n : 自然数)
  结论: natDegree (p ^ n) = n * natDegree p
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
exact natDegree_pow' by
    rw [← leadingCoeff_pow]; rw [Ne]; rw [leadingCoeff_eq_zero]; exact pow_ne_zero _ hp

Depends on / 依赖: eq_or_ne, leadingCoeff_eq_zero, leadingCoeff_pow, natDegree_pow, pow_ne_zero
-/
lemma natDegree_pow (p : R[X]) (n : Nat) : natDegree (p ^ n) = n * natDegree p := by
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
exact natDegree_pow' by
    rw [← leadingCoeff_pow]; rw [Ne]; rw [leadingCoeff_eq_zero]; exact pow_ne_zero _ hp

/--
lemma `natDegree_le_of_dvd` / 引理 `natDegree_le_of_dvd`

English:
lemma natDegree_le_of_dvd
  given: (h1 : p ∣ q) (h2 : q != 0)
  statement: p.natDegree <= q.natDegree
  proof: by
  obtain ⟨q, rfl⟩ := h1
  rw [mul_ne_zero_iff] at h2
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _

中文:
引理 natDegree_le_of_dvd
  条件: (h1 : p ∣ q) (h2 : q != 0)
  结论: p.natDegree <= q.natDegree
  证明: by
  obtain ⟨q, rfl⟩ := h1
  rw [mul_ne_zero_iff] at h2
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _

Depends on / 依赖: Nat.le_add_right, le_add_right, mul_ne_zero_iff, natDegree_mul
-/
lemma natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0) : p.natDegree <= q.natDegree := by
  obtain ⟨q, rfl⟩ := h1
  rw [mul_ne_zero_iff] at h2
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _

/--
lemma `degree_le_of_dvd` / 引理 `degree_le_of_dvd`

English:
lemma degree_le_of_dvd
  given: (h1 : p ∣ q) (h2 : q != 0)
  statement: degree p <= degree q
  proof: by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2

中文:
引理 degree_le_of_dvd
  条件: (h1 : p ∣ q) (h2 : q != 0)
  结论: degree p <= degree q
  证明: by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2

Depends on / 依赖: degree_le_mul_left, mul_ne_zero_iff
-/
lemma degree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0) : degree p <= degree q := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2

/--
lemma `eq_zero_of_dvd_of_degree_lt` / 引理 `eq_zero_of_dvd_of_degree_lt`

English:
lemma eq_zero_of_dvd_of_degree_lt
  given: (h₁ : p ∣ q) (h₂ : degree q < degree p)
  statement: q = 0
  proof: by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (degree_le_of_dvd h₁ hc)

中文:
引理 eq_zero_of_dvd_of_degree_lt
  条件: (h₁ : p ∣ q) (h₂ : degree q < degree p)
  结论: q = 0
  证明: by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (degree_le_of_dvd h₁ hc)

Depends on / 依赖: degree_le_of_dvd, lt_iff_not_ge, lt_iff_not_ge.mp
-/
lemma eq_zero_of_dvd_of_degree_lt (h₁ : p ∣ q) (h₂ : degree q < degree p) : q = 0 := by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (degree_le_of_dvd h₁ hc)

/--
lemma `eq_zero_of_dvd_of_natDegree_lt` / 引理 `eq_zero_of_dvd_of_natDegree_lt`

English:
lemma eq_zero_of_dvd_of_natDegree_lt
  given: (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p)
  proof: by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (natDegree_le_of_dvd h₁ hc)

中文:
引理 eq_zero_of_dvd_of_natDegree_lt
  条件: (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p)
  证明: by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (natDegree_le_of_dvd h₁ hc)

Depends on / 依赖: lt_iff_not_ge, lt_iff_not_ge.mp, natDegree_le_of_dvd
-/
lemma eq_zero_of_dvd_of_natDegree_lt (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) :
    q = 0 := by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (natDegree_le_of_dvd h₁ hc)

/--
lemma `not_dvd_of_degree_lt` / 引理 `not_dvd_of_degree_lt`

English:
lemma not_dvd_of_degree_lt
  given: (h0 : q != 0) (hl : q.degree < p.degree)
  statement: ¬p ∣ q
  proof: by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)

中文:
引理 not_dvd_of_degree_lt
  条件: (h0 : q != 0) (hl : q.degree < p.degree)
  结论: ¬p ∣ q
  证明: by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)

Depends on / 依赖: eq_zero_of_dvd_of_degree_lt, hcontra
-/
lemma not_dvd_of_degree_lt (h0 : q != 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)

/--
lemma `not_dvd_of_natDegree_lt` / 引理 `not_dvd_of_natDegree_lt`

English:
lemma not_dvd_of_natDegree_lt
  given: (h0 : q != 0) (hl : q.natDegree < p.natDegree)
  proof: by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)

中文:
引理 not_dvd_of_natDegree_lt
  条件: (h0 : q != 0) (hl : q.natDegree < p.natDegree)
  证明: by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)

Depends on / 依赖: eq_zero_of_dvd_of_natDegree_lt, hcontra
-/
lemma not_dvd_of_natDegree_lt (h0 : q != 0) (hl : q.natDegree < p.natDegree) :
    ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)

/--
lemma `natDegree_sub_eq_of_prod_eq` / 引理 `natDegree_sub_eq_of_prod_eq`

English:
lemma natDegree_sub_eq_of_prod_eq
  statement: {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0)
  proof: by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← natDegree_mul hp₁ hq₂]; rw [← natDegree_mul hp₂ hq₁]; rw [h_eq]

中文:
引理 natDegree_sub_eq_of_prod_eq
  结论: {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0)
  证明: by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← natDegree_mul hp₁ hq₂]; rw [← natDegree_mul hp₂ hq₁]; rw [h_eq]

Depends on / 依赖: h_eq, natDegree_mul, sub_eq_sub_iff_add_eq_add
-/
lemma natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0)
    (hp₂ : p₂ != 0) (hq₂ : q₂ != 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : Int) - q₁.natDegree = (p₂.natDegree : Int) - q₂.natDegree := by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← natDegree_mul hp₁ hq₂]; rw [← natDegree_mul hp₂ hq₁]; rw [h_eq]

end Semiring

end Polynomial
