/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Uthaiwat, Oliver Nash
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotency in polynomial rings.

This file is a place for results related to nilpotency in (single-variable) polynomial rings.

## Main results:
* `Polynomial.isNilpotent_iff`
* `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`

-/

public section

namespace Polynomial

variable {R : Type*} {r : R}

section Semiring

variable [Semiring R] {P : R[X]}

/--
lemma `isNilpotent_C_mul_pow_X_of_isNilpotent` / 引理 `isNilpotent_C_mul_pow_X_of_isNilpotent`

English:
lemma isNilpotent_C_mul_pow_X_of_isNilpotent
  given: (n : Nat) (hnil : IsNilpotent r)
  proof: by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow]; rw [hm]; rw [C_0]

中文:
引理 isNilpotent_C_mul_pow_X_of_isNilpotent
  条件: (n : 自然数) (hnil : 是幂零 r)
  证明: by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow]; rw [hm]; rw [C_0]

Depends on / 依赖: C_pow, Commute, Commute.isNilpotent_mul_right, commute_X_pow, isNilpotent_mul_right
-/
lemma isNilpotent_C_mul_pow_X_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow]; rw [hm]; rw [C_0]

/--
lemma `isNilpotent_pow_X_mul_C_of_isNilpotent` / 引理 `isNilpotent_pow_X_mul_C_of_isNilpotent`

English:
lemma isNilpotent_pow_X_mul_C_of_isNilpotent
  given: (n : Nat) (hnil : IsNilpotent r)
  proof: by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil

中文:
引理 isNilpotent_pow_X_mul_C_of_isNilpotent
  条件: (n : 自然数) (hnil : 是幂零 r)
  证明: by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil

Depends on / 依赖: commute_X_pow, isNilpotent_C_mul_pow_X_of_isNilpotent
-/
lemma isNilpotent_pow_X_mul_C_of_isNilpotent (n : Nat) (hnil : IsNilpotent r) :
    IsNilpotent (X ^ n * (C r)) := by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil

/--
lemma `isNilpotent_monomial_iff` / 引理 `isNilpotent_monomial_iff`

English:
lemma isNilpotent_monomial_iff
  given: {n : Nat}
  proof: exists_congr fun k => by simp

中文:
引理 isNilpotent_monomial_iff
  条件: {n : 自然数}
  证明: exists_congr fun k => by simp
-/
@[simp] lemma isNilpotent_monomial_iff {n : Nat} :
    IsNilpotent (monomial (R := R) n r) ↔ IsNilpotent r :=
  exists_congr fun k => by simp

/--
lemma `isNilpotent_C_iff` / 引理 `isNilpotent_C_iff`

English:
lemma isNilpotent_C_iff
  proof: exists_congr fun k => by simpa only [← C_pow] using C_eq_zero

中文:
引理 isNilpotent_C_iff
  证明: exists_congr fun k => by simpa only [← C_pow] using C_eq_zero
-/
@[simp] lemma isNilpotent_C_iff :
    IsNilpotent (C r) ↔ IsNilpotent r :=
  exists_congr fun k => by simpa only [← C_pow] using C_eq_zero

/--
lemma `isNilpotent_X_mul_iff` / 引理 `isNilpotent_X_mul_iff`

English:
lemma isNilpotent_X_mul_iff
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rwa [Commute.isNilpotent_mul_left_iff (commute_X P) (by simp)] at h
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩

中文:
引理 isNilpotent_X_mul_iff
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rwa [Commute.isNilpotent_mul_left_iff (commute_X P) (by simp)] at h
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩
-/
@[simp] lemma isNilpotent_X_mul_iff :
    IsNilpotent (X * P) ↔ IsNilpotent P := by
  refine ⟨fun h => ?_, ?_⟩
  · rwa [Commute.isNilpotent_mul_left_iff (commute_X P) (by simp)] at h
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩

/--
lemma `isNilpotent_mul_X_iff` / 引理 `isNilpotent_mul_X_iff`

English:
lemma isNilpotent_mul_X_iff
  proof: by
  rw [← commute_X P]
  exact isNilpotent_X_mul_iff

中文:
引理 isNilpotent_mul_X_iff
  证明: by
  rw [← commute_X P]
  exact isNilpotent_X_mul_iff

Depends on / 依赖: IsTopologicalRing, IsTopologicalRing.toIsSemitopologicalRing, toIsSemitopologicalRing
-/
@[simp] lemma isNilpotent_mul_X_iff :
    IsNilpotent (P * X) ↔ IsNilpotent P := by
  rw [← commute_X P]
  exact isNilpotent_X_mul_iff

end Semiring

section CommRing

variable [CommRing R] {P : R[X]}

/--
lemma `isNilpotent_iff` / 引理 `isNilpotent_iff`

English:
lemma isNilpotent_iff
  proof: by
  refine
    ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i => ?_) (fun p _ hnp hpX i => ?_), fun h => ?_⟩
  · rw [← sum_monomial_eq P]
    exact isNilpotent_sum (fun i _ => by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q => coeff q 0) hk
    rcases i with - | i
    · simpa [hp₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hp
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
  · rcases i with - | i
    · simp
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i

中文:
引理 isNilpotent_iff
  证明: by
  refine
    ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i => ?_) (fun p _ hnp hpX i => ?_), fun h => ?_⟩
  · rw [← sum_monomial_eq P]
    exact isNilpotent_sum (fun i _ => by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q => coeff q 0) hk
    rcases i with - | i
    · simpa [hp₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hp
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
  · rcases i with - | i
    · simp
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i

Depends on / 依赖: IsTopologicalSemiring, IsTopologicalSemiring.toIsSemitopologicalSemiring, toIsSemitopologicalSemiring
-/
protected lemma isNilpotent_iff :
    IsNilpotent P ↔ forall i, IsNilpotent (coeff P i) := by
  refine
    ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i => ?_) (fun p _ hnp hpX i => ?_), fun h => ?_⟩
  · rw [← sum_monomial_eq P]
    exact isNilpotent_sum (fun i _ => by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q => coeff q 0) hk
    rcases i with - | i
    · simpa [hp₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hp
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
  · rcases i with - | i
    · simp
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i

/--
lemma `isNilpotent_reflect_iff` / 引理 `isNilpotent_reflect_iff`

English:
lemma isNilpotent_reflect_iff
  given: {P : R[X]} {N : Nat} (hN : P.natDegree <= N)
  proof: by
  simp only [Polynomial.isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h i => ?_⟩ <;> rcases le_or_gt i N with hi | hi
  · simpa [tsub_tsub_cancel_of_le hi] using h (N - i)
  · simp [coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hN hi]
  · simpa [hi, revAt_le] using h (N - i)
  · simpa [revAt_eq_self_of_lt hi] using h i

中文:
引理 isNilpotent_reflect_iff
  条件: {P : R[X]} {N : 自然数} (hN : P.natDegree <= N)
  证明: by
  simp only [Polynomial.isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h i => ?_⟩ <;> rcases le_or_gt i N with hi | hi
  · simpa [tsub_tsub_cancel_of_le hi] using h (N - i)
  · simp [coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hN hi]
  · simpa [hi, revAt_le] using h (N - i)
  · simpa [revAt_eq_self_of_lt hi] using h i

Depends on / 依赖: IsSemitopologicalRing, IsSemitopologicalRing.toIsTopologicalAddGroup, NonUnitalNonAssocRing, toIsTopologicalAddGroup
-/
@[simp] lemma isNilpotent_reflect_iff {P : R[X]} {N : Nat} (hN : P.natDegree <= N) :
    IsNilpotent (reflect N P) ↔ IsNilpotent P := by
  simp only [Polynomial.isNilpotent_iff]
  refine ⟨fun h i => ?_, fun h i => ?_⟩ <;> rcases le_or_gt i N with hi | hi
  · simpa [tsub_tsub_cancel_of_le hi] using h (N - i)
  · simp [coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hN hi]
  · simpa [hi, revAt_le] using h (N - i)
  · simpa [revAt_eq_self_of_lt hi] using h i

/--
lemma `isNilpotent_reverse_iff` / 引理 `isNilpotent_reverse_iff`

English:
lemma isNilpotent_reverse_iff
  proof: isNilpotent_reflect_iff (le_refl _)

中文:
引理 isNilpotent_reverse_iff
  证明: isNilpotent_reflect_iff (le_refl _)
-/
@[simp] lemma isNilpotent_reverse_iff :
    IsNilpotent P.reverse ↔ IsNilpotent P :=
  isNilpotent_reflect_iff (le_refl _)

/--
theorem `isUnit_of_coeff_isUnit_isNilpotent` / 定理 `isUnit_of_coeff_isUnit_isNilpotent`

English:
theorem isUnit_of_coeff_isUnit_isNilpotent
  statement: (hunit : IsUnit (P.coeff 0))
  proof: by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with | _ k hind
  by_cases hdeg : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C
  set P₁ := P.eraseLead with hP₁
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P]; rw [← C_mul_X_pow_eq_monomial]; rw [← hP₁]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg)
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine hind P₁.natDegree ?_ ?_ (fun i hi => ?_) rfl
  · simp_rw [P₁, ← h, hdeg₂]
  · simp_rw [P₁, eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases! H : i <= P₁.natDegree
    · simp_rw [P₁, eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    · simp_rw [coeff_eq_zero_of_natDegree_lt H, IsNilpotent.zero]

中文:
定理 isUnit_of_coeff_isUnit_isNilpotent
  结论: (hunit : 是单位 (P.coeff 0))
  证明: by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with | _ k hind
  by_cases hdeg : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C
  set P₁ := P.eraseLead with hP₁
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P]; rw [← C_mul_X_pow_eq_monomial]; rw [← hP₁]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg)
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine hind P₁.natDegree ?_ ?_ (fun i hi => ?_) rfl
  · simp_rw [P₁, ← h, hdeg₂]
  · simp_rw [P₁, eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases! H : i <= P₁.natDegree
    · simp_rw [P₁, eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    · simp_rw [coeff_eq_zero_of_natDegree_lt H, IsNilpotent.zero]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Commute, Commute.all, DiscreteTopology, DiscreteTopology.topologicalSemiring, IsNilpotent, IsNilpotent.isUnit_add_left_of_commute, IsUnit, Nat.strong_induction_on, P.eraseL, P.eraseLead, P.natDegree, TopologicalSpace, eq_C_of_natDegree_eq_zero, eraseL, eraseLead, eraseLead_add_monomial_natDegree_leadingCoeff, generalizing, hunit.map, isNilpotent_C_mul_pow_X_of_isNilpotent
-/
theorem isUnit_of_coeff_isUnit_isNilpotent (hunit : IsUnit (P.coeff 0))
    (hnil : forall i, i != 0 -> IsNilpotent (P.coeff i)) : IsUnit P := by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with | _ k hind
  by_cases hdeg : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C
  set P₁ := P.eraseLead with hP₁
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P]; rw [← C_mul_X_pow_eq_monomial]; rw [← hP₁]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg)
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine hind P₁.natDegree ?_ ?_ (fun i hi => ?_) rfl
  · simp_rw [P₁, ← h, hdeg₂]
  · simp_rw [P₁, eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases! H : i <= P₁.natDegree
    · simp_rw [P₁, eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    · simp_rw [coeff_eq_zero_of_natDegree_lt H, IsNilpotent.zero]

/--
theorem `coeff_isUnit_isNilpotent_of_isUnit` / 定理 `coeff_isUnit_isNilpotent_of_isUnit`

English:
theorem coeff_isUnit_isNilpotent_of_isUnit
  given: (hunit : IsUnit P)
  proof: by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  · refine .of_mul_eq_one (Q.coeff 0) ?_
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h
  · intro n hn
    rw [nilpotent_iff_mem_prime]
    intro I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff]; rw [← degree_mul]; rw [← map_mul]; rw [hQ]; rw [map_one]; rw [degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine coeff_eq_zero_of_degree_lt ?_
      rw [hPQ.1]
      exact WithBot.coe_pos.2 hn.bot_lt
    rw [coe_mapRingHom]; rw [coeff_map]; rw [← RingHom.mem_ker]; rw [Ideal.mk_ker] at hcoeff
    exact hcoeff

中文:
定理 coeff_isUnit_isNilpotent_of_isUnit
  条件: (hunit : 是单位 P)
  证明: by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  · refine .of_mul_eq_one (Q.coeff 0) ?_
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h
  · intro n hn
    rw [nilpotent_iff_mem_prime]
    intro I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff]; rw [← degree_mul]; rw [← map_mul]; rw [hQ]; rw [map_one]; rw [degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine coeff_eq_zero_of_degree_lt ?_
      rw [hPQ.1]
      exact WithBot.coe_pos.2 hn.bot_lt
    rw [coe_mapRingHom]; rw [coeff_map]; rw [← RingHom.mem_ker]; rw [Ideal.mk_ker] at hcoeff
    exact hcoeff

Depends on / 依赖: DiscreteTopology, DiscreteTopology.topologicalRing, Ideal.Quotient.mk, IsUnit, IsUnit.exists_right_inv, Nat.WithBot.add_eq_zero_iff, Q.coeff, Quotient, TopologicalSpace, WithBot, add_eq_zero_iff, coeff_eq_zero_of_degree_lt, coeff_one_zero, degree, degree_mul, degree_one, exists_right_inv, hcoeff, mapRingHom, map_mul
-/
theorem coeff_isUnit_isNilpotent_of_isUnit (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (forall i, i != 0 -> IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  · refine .of_mul_eq_one (Q.coeff 0) ?_
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h
  · intro n hn
    rw [nilpotent_iff_mem_prime]
    intro I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff]; rw [← degree_mul]; rw [← map_mul]; rw [hQ]; rw [map_one]; rw [degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine coeff_eq_zero_of_degree_lt ?_
      rw [hPQ.1]
      exact WithBot.coe_pos.2 hn.bot_lt
    rw [coe_mapRingHom]; rw [coeff_map]; rw [← RingHom.mem_ker]; rw [Ideal.mk_ker] at hcoeff
    exact hcoeff

/--
theorem `isUnit_iff_coeff_isUnit_isNilpotent` / 定理 `isUnit_iff_coeff_isUnit_isNilpotent`

English:
theorem isUnit_iff_coeff_isUnit_isNilpotent
  proof: ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩

中文:
定理 isUnit_iff_coeff_isUnit_isNilpotent
  证明: ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩

Depends on / 依赖: coeff_isUnit_isNilpotent_of_isUnit, isUnit_of_coeff_isUnit_isNilpotent
-/
theorem isUnit_iff_coeff_isUnit_isNilpotent :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (forall i, i != 0 -> IsNilpotent (P.coeff i)) :=
  ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩

/--
lemma `isUnit_C_add_X_mul_iff` / 引理 `isUnit_C_add_X_mul_iff`

English:
lemma isUnit_C_add_X_mul_iff
  proof: by
  have : forall i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    ← Polynomial.isNilpotent_iff]

中文:
引理 isUnit_C_add_X_mul_iff
  证明: by
  have : forall i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    ← Polynomial.isNilpotent_iff]
-/
@[simp] lemma isUnit_C_add_X_mul_iff :
    IsUnit (C r + X * P) ↔ IsUnit r ∧ IsNilpotent P := by
  have : forall i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    ← Polynomial.isNilpotent_iff]

/--
lemma `isUnit_iff'` / 引理 `isUnit_iff'`

English:
lemma isUnit_iff'
  proof: by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P X]
  simp [modByMonic_X]

中文:
引理 isUnit_iff'
  证明: by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P X]
  simp [modByMonic_X]

Depends on / 依赖: conv_lhs, modByMonic_X, modByMonic_add_div
-/
lemma isUnit_iff' :
    IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X) := by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P X]
  simp [modByMonic_X]

/--
theorem `not_isUnit_of_natDegree_pos_of_isReduced` / 定理 `not_isUnit_of_natDegree_pos_of_isReduced`

English:
theorem not_isUnit_of_natDegree_pos_of_isReduced
  statement: [IsReduced R] (p : R[X])
  proof: by
  simp only [ne_eq, isNilpotent_iff_eq_zero, not_and, not_forall, exists_prop,
    Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  intro _
  refine ⟨p.natDegree, hpl.ne', ?_⟩
  contrapose! hpl
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at hpl
  simp [hpl]

中文:
定理 not_isUnit_of_natDegree_pos_of_isReduced
  结论: [是既约 R] (p : R[X])
  证明: by
  simp only [ne_eq, isNilpotent_iff_eq_zero, not_and, not_forall, exists_prop,
    Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  intro _
  refine ⟨p.natDegree, hpl.ne', ?_⟩
  contrapose! hpl
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at hpl
  simp [hpl]

Depends on / 依赖: Polynomial, Polynomial.isUnit_iff_coeff_isUnit_isNilpotent, coeff_natDegree, contrapose, exists_prop, hpl.ne, isNilpotent_iff_eq_zero, isUnit_iff_coeff_isUnit_isNilpotent, leadingCoeff_eq_zero, natDegree, ne_eq, not_and, not_forall, p.natDegree
-/
theorem not_isUnit_of_natDegree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.natDegree) : ¬ IsUnit p := by
  simp only [ne_eq, isNilpotent_iff_eq_zero, not_and, not_forall, exists_prop,
    Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  intro _
  refine ⟨p.natDegree, hpl.ne', ?_⟩
  contrapose! hpl
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at hpl
  simp [hpl]

/--
theorem `not_isUnit_of_degree_pos_of_isReduced` / 定理 `not_isUnit_of_degree_pos_of_isReduced`

English:
theorem not_isUnit_of_degree_pos_of_isReduced
  statement: [IsReduced R] (p : R[X])
  proof: not_isUnit_of_natDegree_pos_of_isReduced _ (natDegree_pos_iff_degree_pos.mpr hpl)

中文:
定理 not_isUnit_of_degree_pos_of_isReduced
  结论: [是既约 R] (p : R[X])
  证明: not_isUnit_of_natDegree_pos_of_isReduced _ (natDegree_pos_iff_degree_pos.mpr hpl)

Depends on / 依赖: natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mpr, not_isUnit_of_natDegree_pos_of_isReduced
-/
theorem not_isUnit_of_degree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.degree) : ¬ IsUnit p :=
  not_isUnit_of_natDegree_pos_of_isReduced _ (natDegree_pos_iff_degree_pos.mpr hpl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (C : _ ->+* Polynomial R)
  body: by simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]

中文:
实例 :
  签名: 是Local态射 (C : _ ->+* 多项式 R)
  定义体: by simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]

Depends on / 依赖: coeff_C, contextual, isUnit_iff_coeff_isUnit_isNilpotent
-/
instance : IsLocalHom (C : _ ->+* Polynomial R) where
  map_nonunit := by simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (algebraMap R (Polynomial R))
  body: inferInstanceAs (IsLocalHom C)

中文:
实例 :
  签名: 是Local态射 (algebraMap R (多项式 R))
  定义体: inferInstanceAs (IsLocalHom C)

Depends on / 依赖: IsLocalHom
-/
instance : IsLocalHom (algebraMap R (Polynomial R)) :=
  inferInstanceAs (IsLocalHom C)

end CommRing

section CommAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {a b : S}

/--
lemma `isNilpotent_aeval_sub_of_isNilpotent_sub` / 引理 `isNilpotent_aeval_sub_of_isNilpotent_sub`

English:
lemma isNilpotent_aeval_sub_of_isNilpotent_sub
  given: (h : IsNilpotent (a - b))
  proof: by
  simp only [← eval_map_algebraMap]
  have ⟨c, hc⟩ := evalSubFactor (map (algebraMap R S) P) a b
  exact hc ▸ (Commute.all _ _).isNilpotent_mul_left h

中文:
引理 isNilpotent_aeval_sub_of_isNilpotent_sub
  条件: (h : 是幂零 (a - b))
  证明: by
  simp only [← eval_map_algebraMap]
  have ⟨c, hc⟩ := evalSubFactor (map (algebraMap R S) P) a b
  exact hc ▸ (Commute.all _ _).isNilpotent_mul_left h

Depends on / 依赖: Commute, Commute.all, algebraMap, evalSubFactor, eval_map_algebraMap, isNilpotent_mul_left
-/
lemma isNilpotent_aeval_sub_of_isNilpotent_sub (h : IsNilpotent (a - b)) :
    IsNilpotent (aeval a P - aeval b P) := by
  simp only [← eval_map_algebraMap]
  have ⟨c, hc⟩ := evalSubFactor (map (algebraMap R S) P) a b
  exact hc ▸ (Commute.all _ _).isNilpotent_mul_left h

variable {P}

/--
lemma `isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub` / 引理 `isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub`

English:
lemma isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
  proof: by
  rw [← add_sub_cancel (aeval b P) (aeval a P)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ hb (Commute.all _ _)
  exact isNilpotent_aeval_sub_of_isNilpotent_sub P hab

中文:
引理 isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
  证明: by
  rw [← add_sub_cancel (aeval b P) (aeval a P)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ hb (Commute.all _ _)
  exact isNilpotent_aeval_sub_of_isNilpotent_sub P hab

Depends on / 依赖: Commute, Commute.all, IsNilpotent, IsNilpotent.isUnit_add_left_of_commute, add_sub_cancel, isNilpotent_aeval_sub_of_isNilpotent_sub, isUnit_add_left_of_commute
-/
lemma isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
    (hb : IsUnit (aeval b P)) (hab : IsNilpotent (a - b)) :
    IsUnit (aeval a P) := by
  rw [← add_sub_cancel (aeval b P) (aeval a P)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ hb (Commute.all _ _)
  exact isNilpotent_aeval_sub_of_isNilpotent_sub P hab

end CommAlgebra

end Polynomial
