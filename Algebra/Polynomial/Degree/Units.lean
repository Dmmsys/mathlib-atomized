/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Degree of polynomials that are units
-/

public section

noncomputable section

open Finsupp Finset Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : Nat}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/--
lemma `natDegree_eq_zero_of_isUnit` / 引理 `natDegree_eq_zero_of_isUnit`

English:
lemma natDegree_eq_zero_of_isUnit
  given: (h : IsUnit p)
  statement: natDegree p = 0
  proof: by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact this.1

中文:
引理 natDegree_eq_zero_of_isUnit
  条件: (h : IsUnit p)
  结论: natDegree p = 0
  证明: by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact this.1

Depends on / 依赖: add_eq_zero, eq_comm, exists_right_inv, h.exists_right_inv, left_ne_zero_of_mul_eq_one, natDegree_mul, natDegree_one, nontriviality, right_ne_zero_of_mul_eq_one
-/
lemma natDegree_eq_zero_of_isUnit (h : IsUnit p) : natDegree p = 0 := by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := natDegree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq]; rw [natDegree_one]; rw [eq_comm]; rw [add_eq_zero] at this
  exact this.1

/--
lemma `degree_eq_zero_of_isUnit` / 引理 `degree_eq_zero_of_isUnit`

English:
lemma degree_eq_zero_of_isUnit
  given: [Nontrivial R] (h : IsUnit p)
  statement: degree p = 0
  proof: (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

@[simp]

中文:
引理 degree_eq_zero_of_isUnit
  条件: [Nontrivial R] (h : IsUnit p)
  结论: degree p = 0
  证明: (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

@[simp]

Depends on / 依赖: antisymm, h.ne_zero, natDegree_eq_zero_iff_degree_le_zero, natDegree_eq_zero_iff_degree_le_zero.mp, natDegree_eq_zero_of_isUnit, ne_zero, zero_le_degree_iff, zero_le_degree_iff.mpr
-/
lemma degree_eq_zero_of_isUnit [Nontrivial R] (h : IsUnit p) : degree p = 0 :=
  (natDegree_eq_zero_iff_degree_le_zero.mp <| natDegree_eq_zero_of_isUnit h).antisymm
    (zero_le_degree_iff.mpr h.ne_zero)

@[simp]
/--
lemma `degree_coe_units` / 引理 `degree_coe_units`

English:
lemma degree_coe_units
  given: [Nontrivial R] (u : R[X]ˣ)
  statement: degree (u : R[X]) = 0
  proof: degree_eq_zero_of_isUnit ⟨u, rfl⟩

中文:
引理 degree_coe_units
  条件: [Nontrivial R] (u : R[X]ˣ)
  结论: degree (u : R[X]) = 0
  证明: degree_eq_zero_of_isUnit ⟨u, rfl⟩

Depends on / 依赖: degree_eq_zero_of_isUnit
-/
lemma degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_isUnit ⟨u, rfl⟩

/--
lemma `isUnit_iff` / 引理 `isUnit_iff`

English:
lemma isUnit_iff
  statement: IsUnit p ↔ exists r : R, IsUnit r ∧ C r = p
  proof: ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩

中文:
引理 isUnit_iff
  结论: IsUnit p ↔ 存在 r : R, IsUnit r ∧ C r = p
  证明: ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩

Depends on / 依赖: eq_C_of_natDegree_eq_zero, h.symm, isUnit_C, natDegree_eq_zero_of_isUnit, p.coeff
-/
lemma isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ C r = p :=
  ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩

/--
lemma `not_isUnit_of_degree_pos` / 引理 `not_isUnit_of_degree_pos`

English:
lemma not_isUnit_of_degree_pos
  given: (p : R[X]) (hpl : 0 < p.degree)
  statement: ¬ IsUnit p
  proof: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl

中文:
引理 not_isUnit_of_degree_pos
  条件: (p : R[X]) (hpl : 0 < p.degree)
  结论: ¬ IsUnit p
  证明: by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl

Depends on / 依赖: Subsingleton, Subsingleton.elim, degree_eq_zero_of_isUnit, subsingleton_or_nontrivial
-/
lemma not_isUnit_of_degree_pos (p : R[X]) (hpl : 0 < p.degree) : ¬ IsUnit p := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim p 0] at hpl
  intro h
  simp [degree_eq_zero_of_isUnit h] at hpl

/--
lemma `not_isUnit_of_natDegree_pos` / 引理 `not_isUnit_of_natDegree_pos`

English:
lemma not_isUnit_of_natDegree_pos
  given: (p : R[X]) (hpl : 0 < p.natDegree)
  statement: ¬ IsUnit p
  proof: not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

中文:
引理 not_isUnit_of_natDegree_pos
  条件: (p : R[X]) (hpl : 0 < p.natDegree)
  结论: ¬ IsUnit p
  证明: not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

Depends on / 依赖: natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mp, not_isUnit_of_degree_pos
-/
lemma not_isUnit_of_natDegree_pos (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p :=
  not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

/--
lemma `natDegree_coe_units` / 引理 `natDegree_coe_units`

English:
lemma natDegree_coe_units
  given: (u : R[X]ˣ)
  statement: natDegree (u : R[X]) = 0
  proof: by
  nontriviality R
  exact natDegree_eq_of_degree_eq_some (degree_coe_units u)

中文:
引理 natDegree_coe_units
  条件: (u : R[X]ˣ)
  结论: natDegree (u : R[X]) = 0
  证明: by
  nontriviality R
  exact natDegree_eq_of_degree_eq_some (degree_coe_units u)
-/
@[simp] lemma natDegree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 := by
  nontriviality R
  exact natDegree_eq_of_degree_eq_some (degree_coe_units u)

/--
theorem `coeff_coe_units_zero_ne_zero` / 定理 `coeff_coe_units_zero_ne_zero`

English:
theorem coeff_coe_units_zero_ne_zero
  given: [Nontrivial R] (u : R[X]ˣ)
  statement: coeff (u : R[X]) 0 != 0
  proof: by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff]; rw [Ne]; rw [leadingCoeff_eq_zero]
  exact Units.ne_zero _

中文:
定理 coeff_coe_units_zero_ne_zero
  条件: [Nontrivial R] (u : R[X]ˣ)
  结论: coeff (u : R[X]) 0 != 0
  证明: by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff]; rw [Ne]; rw [leadingCoeff_eq_zero]
  exact Units.ne_zero _

Depends on / 依赖: DistribSMul, Units.ne_zero, instDistribSMul, leadingCoeff, leadingCoeff_eq_zero, natDegree_coe_units, ne_zero
-/
theorem coeff_coe_units_zero_ne_zero [Nontrivial R] (u : R[X]ˣ) : coeff (u : R[X]) 0 != 0 := by
  conv in 0 => rw [← natDegree_coe_units u]
  rw [← leadingCoeff]; rw [Ne]; rw [leadingCoeff_eq_zero]
  exact Units.ne_zero _

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

/--
lemma `Monic.C_dvd_iff_isUnit` / 引理 `Monic.C_dvd_iff_isUnit`

English:
lemma Monic.C_dvd_iff_isUnit
  given: {a : R}
  statement: C a ∣ p ↔ IsUnit a where
  proof: isUnit_iff_dvd_one.mpr hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map C).dvd

中文:
引理 Monic.C_dvd_iff_isUnit
  条件: {a : R}
  结论: C a ∣ p ↔ IsUnit a where
  证明: isUnit_iff_dvd_one.mpr hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map C).dvd

Depends on / 依赖: C_dvd_iff_dvd_coeff, coeff_natDegree, hp.coeff_natDegree, isUnit_iff_dvd_one, isUnit_iff_dvd_one.mpr, natDegree, p.natDegree
-/
lemma Monic.C_dvd_iff_isUnit {a : R} : C a ∣ p ↔ IsUnit a where
mp h := isUnit_iff_dvd_one.mpr hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map C).dvd

/--
lemma `Monic.degree_pos_of_not_isUnit` / 引理 `Monic.degree_pos_of_not_isUnit`

English:
lemma Monic.degree_pos_of_not_isUnit
  given: (hu : ¬IsUnit p)
  statement: 0 < degree p
  proof: hp.degree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

中文:
引理 Monic.degree_pos_of_not_isUnit
  条件: (hu : ¬IsUnit p)
  结论: 0 < degree p
  证明: hp.degree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

Depends on / 依赖: DistribSMul, degree_pos, hp.degree_pos.mpr, instDistribSMul, isUnit_one
-/
lemma Monic.degree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < degree p :=
  hp.degree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

/--
lemma `Monic.natDegree_pos_of_not_isUnit` / 引理 `Monic.natDegree_pos_of_not_isUnit`

English:
lemma Monic.natDegree_pos_of_not_isUnit
  given: (hu : ¬IsUnit p)
  statement: 0 < natDegree p
  proof: hp.natDegree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

中文:
引理 Monic.natDegree_pos_of_not_isUnit
  条件: (hu : ¬IsUnit p)
  结论: 0 < natDegree p
  证明: hp.natDegree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

Depends on / 依赖: hp.natDegree_pos.mpr, isUnit_one, natDegree_pos
-/
lemma Monic.natDegree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < natDegree p :=
  hp.natDegree_pos.mpr fun hp' => (hp' ▸ hu) isUnit_one

/--
lemma `degree_pos_of_not_isUnit_of_dvd_monic` / 引理 `degree_pos_of_not_isUnit_of_dvd_monic`

English:
lemma degree_pos_of_not_isUnit_of_dvd_monic
  given: (ha : ¬IsUnit a) (hap : a ∣ p)
  statement: 0 < degree a
  proof: by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

中文:
引理 degree_pos_of_not_isUnit_of_dvd_monic
  条件: (ha : ¬IsUnit a) (hap : a ∣ p)
  结论: 0 < degree a
  证明: by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

Depends on / 依赖: C_dvd_iff_isUnit, Polynomial, Polynomial.eq_C_of_degree_le_zero, contrapose, eq_C_of_degree_le_zero, hp.C_dvd_iff_isUnit, isUnit_C
-/
lemma degree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a := by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

/--
lemma `natDegree_pos_of_not_isUnit_of_dvd_monic` / 引理 `natDegree_pos_of_not_isUnit_of_dvd_monic`

English:
lemma natDegree_pos_of_not_isUnit_of_dvd_monic
  given: (ha : ¬IsUnit a) (hap : a ∣ p)
  statement: 0 < natDegree a
  proof: natDegree_pos_iff_degree_pos.mpr degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

中文:
引理 natDegree_pos_of_not_isUnit_of_dvd_monic
  条件: (ha : ¬IsUnit a) (hap : a ∣ p)
  结论: 0 < natDegree a
  证明: natDegree_pos_iff_degree_pos.mpr degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

Depends on / 依赖: degree_pos_of_not_isUnit_of_dvd_monic, natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mpr
-/
lemma natDegree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < natDegree a :=
natDegree_pos_iff_degree_pos.mpr degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

end CommSemiring

end Polynomial
