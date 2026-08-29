/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.Basic


/-!
# Basic lemmas on valuations that are trivial over a base ring

This file contains additional results about `Valuation.IsTrivialOn` which is defined in
`Mathlib.RingTheory.Valuation.Basic`.

In what follows, we consider a `A`-algebra `B` and a valuation `v` over `B` which is trivial on `A`.

## Main results
* `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`: Let `p` be a polynomial
  over `A` evaluated at an element `w` of `B` for which `1 < v w`.
  We have the equality `v (p.aeval w) = v w ^ p.natDegree`.
* `Valuation.transcendental_of_ne_one`: If `y : B` is such that `y ≠ 0` and `v y ≠ 1`,
  then it is transcendental over `A`.
  Note that, in particular, this means that any non zero element of the
  maximal ideal of `v.valuationSubring` is transcendental over `A`.
-/

@[expose] public section

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [CommSemiring A]
variable {B : Type*} [Ring B] [Algebra A B] {v : Valuation B Γ} [hv : v.IsTrivialOn A]

namespace Polynomial

/--
lemma `valuation_aeval_monomial_eq_valuation_pow` / 引理 `valuation_aeval_monomial_eq_valuation_pow`

English:
lemma valuation_aeval_monomial_eq_valuation_pow
  given: (w : B) (n : Nat) {a : A} (ha : a != 0)
  proof: by
  simp [← C_mul_X_pow_eq_monomial, map_mul, map_pow, one_mul, hv.eq_one a ha]

中文:
引理 valuation_aeval_monomial_eq_valuation_pow
  条件: (w : B) (n : 自然数) {a : A} (ha : a != 0)
  证明: by
  simp [← C_mul_X_pow_eq_monomial, map_mul, map_pow, one_mul, hv.eq_one a ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, eq_one, hv.eq_one, map_mul, map_pow, one_mul
-/
lemma valuation_aeval_monomial_eq_valuation_pow (w : B) (n : Nat) {a : A} (ha : a != 0) :
    v ((monomial n a).aeval w) = (v w) ^ n := by
  simp [← C_mul_X_pow_eq_monomial, map_mul, map_pow, one_mul, hv.eq_one a ha]

/--
theorem `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X` / 定理 `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`

English:
theorem valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
  statement: (w : B) (hpos : 1 < v w)
  proof: by
  rw [← valuation_aeval_monomial_eq_valuation_pow _ _ (leadingCoeff_ne_zero.mpr hp)]
  nth_rw 1 [as_sum_range p, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, map_pow, aeval_X, coeff_natDegree]
  by_cases h0 : (p.coeff i) = 0
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      h0, pow_pos (lt_of_le_of_lt zero_le_one hpos) p.natDegree]
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      hv.eq_one _ h0, pow_lt_pow_right₀ hpos hi]

中文:
定理 valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
  结论: (w : B) (hpos : 1 < v w)
  证明: by
  rw [← valuation_aeval_monomial_eq_valuation_pow _ _ (leadingCoeff_ne_zero.mpr hp)]
  nth_rw 1 [as_sum_range p, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, map_pow, aeval_X, coeff_natDegree]
  by_cases h0 : (p.coeff i) = 0
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      h0, pow_pos (lt_of_le_of_lt zero_le_one hpos) p.natDegree]
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      hv.eq_one _ h0, pow_lt_pow_right₀ hpos hi]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Finset, Finset.mem_range, Finset.mem_sdiff, Finset.mem_singleton, Nat.lt_add_one_iff, Valuation, Valuation.map_sum_eq_of_lt, aeval_C, aeval_X, as_sum_range, coeff_natDegree, eq_one, hv.eq_one, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, lt_add_one_iff, lt_iff_le_and_ne, lt_of_le_o
-/
theorem valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (w : B) (hpos : 1 < v w)
    {p : Polynomial A} (hp : p != 0) : v (p.aeval w) = v w ^ p.natDegree := by
  rw [← valuation_aeval_monomial_eq_valuation_pow _ _ (leadingCoeff_ne_zero.mpr hp)]
  nth_rw 1 [as_sum_range p, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, map_pow, aeval_X, coeff_natDegree]
  by_cases h0 : (p.coeff i) = 0
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      h0, pow_pos (lt_of_le_of_lt zero_le_one hpos) p.natDegree]
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      hv.eq_one _ h0, pow_lt_pow_right₀ hpos hi]

end Polynomial

end Ring

section Field

variable (A : Type*) [CommRing A]
variable {K : Type*} [Field K] [Algebra A K] {v : Valuation K Γ} [hv : v.IsTrivialOn A]

open Polynomial

/--
theorem `Valuation.transcendental_of_ne_one` / 定理 `Valuation.transcendental_of_ne_one`

English:
theorem Valuation.transcendental_of_ne_one
  given: (y : K) (h0 : y != 0) (hy : v y != 1)
  proof: by
  wlog! hlt : 1 < v y generalizing y
  · rw [Transcendental, ← IsAlgebraic.inv_iff]
    apply this _ (by simpa) (by simpa)
    rw [← val_lt_one_iff _ h0]
    exact lt_of_le_of_ne hlt hy
  simp_all only [ne_eq, Transcendental]
  by_contra!
  replace ⟨p, hpnt, hp⟩ : IsAlgebraic A y := .algebraMap this
  suffices v y ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt] <;> simp_all

中文:
定理 赋值.transcendental_of_ne_one
  条件: (y : K) (h0 : y != 0) (hy : v y != 1)
  证明: by
  wlog! hlt : 1 < v y generalizing y
  · rw [Transcendental, ← IsAlgebraic.inv_iff]
    apply this _ (by simpa) (by simpa)
    rw [← val_lt_one_iff _ h0]
    exact lt_of_le_of_ne hlt hy
  simp_all only [ne_eq, Transcendental]
  by_contra!
  replace ⟨p, hpnt, hp⟩ : IsAlgebraic A y := .algebraMap this
  suffices v y ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt] <;> simp_all

Depends on / 依赖: IsAlgebraic, IsAlgebraic.inv_iff, Transcendental, algebraMap, generalizing, inv_iff, lt_of_le_of_ne, natDegree, ne_eq, p.natDegree, replace, val_lt_one_iff, valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
-/
theorem Valuation.transcendental_of_ne_one (y : K) (h0 : y != 0) (hy : v y != 1) :
    Transcendental A y := by
  wlog! hlt : 1 < v y generalizing y
  · rw [Transcendental, ← IsAlgebraic.inv_iff]
    apply this _ (by simpa) (by simpa)
    rw [← val_lt_one_iff _ h0]
    exact lt_of_le_of_ne hlt hy
  simp_all only [ne_eq, Transcendental]
  by_contra!
  replace ⟨p, hpnt, hp⟩ : IsAlgebraic A y := .algebraMap this
  suffices v y ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt] <;> simp_all

end Field
