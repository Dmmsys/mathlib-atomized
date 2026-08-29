/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem (`num_dvd_of_is_root` and `den_dvd_of_is_root`)
for a unique factorization domain `A`
with localization `S`, states that the roots of `p : A[X]` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leadingCoeff`.
The corollary is the integral root theorem `isInteger_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

* https://en.wikipedia.org/wiki/Rational_root_theorem
-/

public section


open scoped Polynomial

section ScaleRoots

variable {A K R S : Type*} [CommRing A] [Field K] [CommRing R] [CommRing S]
variable {M : Submonoid A} [Algebra A S] [IsLocalization M S] [Algebra A K] [IsFractionRing A K]

open Finsupp IsFractionRing IsLocalization Polynomial

/--
theorem `scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero` / 定理 `scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero`

English:
theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero
  statement: {p : A[X]} {r : A} {s : M}
  proof: by
  convert! scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  funext
  rw [aeval_def]; rw [mk'_spec' _ r s]

中文:
定理 scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero
  结论: {p : A[X]} {r : A} {s : M}
  证明: by
  convert! scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  funext
  rw [aeval_def]; rw [mk'_spec' _ r s]

Depends on / 依赖: _spec, aeval_def, algebraMap, convert
-/
theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : A[X]} {r : A} {s : M}
    (hr : aeval (mk' S r s) p = 0) : aeval (algebraMap A S r) (scaleRoots p s) = 0 := by
  convert! scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  funext
  rw [aeval_def]; rw [mk'_spec' _ r s]

variable [IsDomain A]

/--
theorem `num_isRoot_scaleRoots_of_aeval_eq_zero` / 定理 `num_isRoot_scaleRoots_of_aeval_eq_zero`

English:
theorem num_isRoot_scaleRoots_of_aeval_eq_zero
  statement: [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
  proof: by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero ?_
  rw [mk'_num_den]
  exact hr

中文:
定理 num_isRoot_scaleRoots_of_aeval_eq_zero
  结论: [唯一分解幺半群 A] {p : A[X]} {x : K}
  证明: by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero ?_
  rw [mk'_num_den]
  exact hr

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, _eq_zero, _num_den, injective, scaleRoots_aeval_eq_zero_of_aeval_mk
-/
theorem num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
    (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (num A x) := by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero ?_
  rw [mk'_num_den]
  exact hr

end ScaleRoots

section RationalRootTheorem

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]
variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial UniqueFactorizationMonoid

/--
theorem `num_dvd_of_is_root` / 定理 `num_dvd_of_is_root`

English:
theorem num_dvd_of_is_root
  given: {p : A[X]} {r : K} (hr : aeval r p = 0)
  statement: num A r ∣ p.coeff 0
  proof: by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots] at this
    have inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · simp_all [nonZeroDivisors.coe_ne_zero]
    · refine dvd_of_dvd_mul_left_of_no_prime_factors hr ?_ this
      intro q dvd_n

中文:
定理 num_dvd_of_is_root
  条件: {p : A[X]} {r : K} (hr : aeval r p = 0)
  结论: num A r ∣ p.coeff 0
  证明: by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots] at this
    have inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · simp_all [nonZeroDivisors.coe_ne_zero]
    · refine dvd_of_dvd_mul_left_of_no_prime_factors hr ?_ this
      intro q dvd_n

Depends on / 依赖: Classical, Classical.propDecidable, coe_ne_zero, coeff_scaleRoots, convert, dvd_denom_pow, dvd_num, dvd_of_dvd_mul_left_of_no_prime_factors, dvd_of_dvd_pow, dvd_term_of_isRoot_of_dvd_terms, hq.dvd_of_dvd_pow, hq.not_isUnit, mul_one, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, not_isUnit, num_den_reduced, num_isRoot_scaleRoots_of_aeval_eq_zero, pow_zero, propDecidable
-/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : num A r ∣ p.coeff 0 := by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots] at this
    have inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · simp_all [nonZeroDivisors.coe_ne_zero]
    · refine dvd_of_dvd_mul_left_of_no_prime_factors hr ?_ this
      intro q dvd_num dvd_denom_pow hq
      apply hq.not_isUnit
      exact num_den_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow)
  convert! dvd_term_of_isRoot_of_dvd_terms 0 (num_isRoot_scaleRoots_of_aeval_eq_zero hr) _
  · rw [pow_zero, mul_one]
  intro j hj
  apply dvd_mul_of_dvd_right
  convert! pow_dvd_pow (num A r) (Nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj))
  exact (pow_one _).symm

/--
theorem `den_dvd_of_is_root` / 定理 `den_dvd_of_is_root`

English:
theorem den_dvd_of_is_root
  given: {p : A[X]} {r : K} (hr : aeval r p = 0)
  proof: by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) ?_
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_isUnit
    exact num_den_reduced A r (hq.dvd_of_dvd_po

中文:
定理 den_dvd_of_is_root
  条件: {p : A[X]} {r : K} (hr : aeval r p = 0)
  证明: by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) ?_
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_isUnit
    exact num_den_reduced A r (hq.dvd_of_dvd_po

Depends on / 依赖: coeff_scaleRoots, coeff_scaleRoots_natDegree, dvd_den, dvd_mul_of_dvd_rig, dvd_num_pow, dvd_of_dvd_mul_left_of_no_prime_factors, dvd_of_dvd_pow, dvd_term_of_isRoot_of_dvd_terms, hq.dvd_of_dvd_pow, hq.not_isUnit, leadingCoeff, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, natDegree, not_isUnit, num_den_reduced, num_isRoot_scaleRoots_of_aeval_eq_zero, p.leadingCoeff, p.natDegree
-/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) ?_
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_isUnit
    exact num_den_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_den
  rw [← coeff_scaleRoots_natDegree]
  apply dvd_term_of_isRoot_of_dvd_terms _ (num_isRoot_scaleRoots_of_aeval_eq_zero hr)
  intro j hj
  by_cases! h : j < p.natDegree
  · rw [coeff_scaleRoots]
    refine (dvd_mul_of_dvd_right ?_ _).mul_right _
    convert! pow_dvd_pow (den A r : A) (Nat.succ_le_iff.mpr (lt_tsub_iff_left.mpr _))
    · exact (pow_one _).symm
    simpa using h
  rw [← natDegree_scaleRoots p (den A r)] at *
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h hj.symm)]; rw [zero_mul]
  exact dvd_zero _

/--
theorem `isInteger_of_is_root_of_monic` / 定理 `isInteger_of_is_root_of_monic`

English:
theorem isInteger_of_is_root_of_monic
  given: {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0)
  proof: isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))

中文:
定理 is整数eger_of_is_root_of_monic
  条件: {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0)
  证明: isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))

Depends on / 依赖: den_dvd_of_is_root, isInteger_of_isUnit_den, isUnit_of_dvd_one
-/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    IsInteger A r :=
  isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))

/--
theorem `exists_integer_of_is_root_of_monic` / 定理 `exists_integer_of_is_root_of_monic`

English:
theorem exists_integer_of_is_root_of_monic
  given: {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0)
  proof: by
  /- I tried deducing this from above by unwrapping IsInteger,
    but the divisibility condition is annoying -/
  obtain ⟨inv, h_inv⟩ := hp ▸ den_dvd_of_is_root hr
  use num A r * inv, ?_
  · have h : inv ∣ 1 := ⟨den A r, by simpa [mul_comm] using h_inv⟩
    simpa using mul_dvd_mul (num_dvd_of_i

中文:
定理 存在_integer_of_is_root_of_monic
  条件: {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0)
  证明: by
  /- I tried deducing this from above by unwrapping IsInteger,
    but the divisibility condition is annoying -/
  obtain ⟨inv, h_inv⟩ := hp ▸ den_dvd_of_is_root hr
  use num A r * inv, ?_
  · have h : inv ∣ 1 := ⟨den A r, by simpa [mul_comm] using h_inv⟩
    simpa using mul_dvd_mul (num_dvd_of_i
-/
theorem exists_integer_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    exists r' : A, r = algebraMap A K r' ∧ r' ∣ p.coeff 0 := by
  /- I tried deducing this from above by unwrapping IsInteger,
    but the divisibility condition is annoying -/
  obtain ⟨inv, h_inv⟩ := hp ▸ den_dvd_of_is_root hr
  use num A r * inv, ?_
  · have h : inv ∣ 1 := ⟨den A r, by simpa [mul_comm] using h_inv⟩
    simpa using mul_dvd_mul (num_dvd_of_is_root hr) h
  · have d_ne_zero : algebraMap A K (den A r) != 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).prop
    nth_rw 1 [← mk'_num_den' A r]
    rw [div_eq_iff d_ne_zero]; rw [map_mul]; rw [mul_assoc]; rw [mul_comm ((algebraMap A K) inv)]; rw [← map_mul]; rw [← h_inv]; rw [map_one]; rw [mul_one]

namespace UniqueFactorizationMonoid

/--
theorem `integer_of_integral` / 定理 `integer_of_integral`

English:
theorem integer_of_integral
  given: {x : K}
  statement: IsIntegral A x -> IsInteger A x
  proof: fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx

中文:
定理 integer_of_integral
  条件: {x : K}
  结论: 是整 A x -> Is整数eger A x
  证明: fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx
-/
theorem integer_of_integral {x : K} : IsIntegral A x -> IsInteger A x := fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx

-- See library note [lower instance priority]
instance (priority := 100) instIsIntegrallyClosed : IsIntegrallyClosed A :=
  (isIntegrallyClosed_iff (FractionRing A)).mpr fun {_} => integer_of_integral

end UniqueFactorizationMonoid

end RationalRootTheorem
