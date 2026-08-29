/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.ChainOfDivisors
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Dedekind domains and ideals

In this file, we prove some results on the unique factorization monoid structure of the ideals.
The unique factorization of ideals and invertibility of fractional ideals can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `IsDedekindDomain.HeightOneSpectrum` defines the type of nonzero prime ideals of `R`.

## Implementation notes

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## TODO

In #38133, many declarations were moved from the root namespace into `Ideal` or `IsDedekindDomain`.
The deprecations have the effect that downstream files now have to use the fully qualified name
even when the corresponding namespace is `open`ed.

After the deprecations have been removed, the shorter names can be restored:
* In Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind:
  + `Ideal.span_singleton_dvd_span_singleton_iff_dvd` → `span_singleton_dvd_span_singleton_iff_dvd`
     in line 75 (as of 2026-04-17)
  + `Ideal.normalizedFactorsEquivSpanNormalizedFactors` →
    `normalizedFactorsEquivSpanNormalizedFactors` in line 115
  + `Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity` →
    `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity` in line 129
  + `Ideal.normalizedFactorsEquivSpanNormalizedFactors` →
    `normalizedFactorsEquivSpanNormalizedFactors` in line 221
* In Mathlib.NumberTheory.NumberField.ClassNumber:
  + `Ideal.prod_normalizedFactors_eq_self` → `prod_normalizedFactors_eq_self` in line 122
* In Mathlib.NumberTheory.RamificationInertia.Basic, one could add `open IsDedekindDomain`
  around line 498 and then remove many `IsDedekindDomain.` prefixes below.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

@[expose] public section

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open Module
open scoped nonZeroDivisors Polynomial

section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

namespace FractionalIdeal

open Ideal

/--
theorem `exists_notMem_one_of_ne_bot` / 定理 `exists_notMem_one_of_ne_bot`

English:
theorem exists_notMem_one_of_ne_bot
  statement: [IsDedekindDomain A] {I : Ideal A} (hI0 : I != ⊥)
  proof: Set.not_subset.1 not_inv_le_one_of_ne_bot hI0 hI1

中文:
定理 存在_notMem_one_of_ne_bot
  结论: [是Dedekind整环 A] {I : 理想 A} (hI0 : I != ⊥)
  证明: Set.not_subset.1 not_inv_le_one_of_ne_bot hI0 hI1

Depends on / 依赖: Set.not_subset, not_inv_le_one_of_ne_bot, not_subset
-/
theorem exists_notMem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I != ⊥)
    (hI1 : I != ⊤) : exists x in (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
Set.not_subset.1 not_inv_le_one_of_ne_bot hI0 hI1

end FractionalIdeal

end Inverse

section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

namespace Ideal

@[simp]
/--
theorem `dvd_span_singleton` / 定理 `dvd_span_singleton`

English:
theorem dvd_span_singleton
  given: {I : Ideal A} {x : A}
  statement: I ∣ span {x} ↔ x in I
  proof: dvd_iff_le.trans (span_le.trans Set.singleton_subset_iff)

中文:
定理 dvd_span_singleton
  条件: {I : 理想 A} {x : A}
  结论: I ∣ span {x} ↔ x in I
  证明: dvd_iff_le.trans (span_le.trans Set.singleton_subset_iff)

Depends on / 依赖: Set.singleton_subset_iff, dvd_iff_le, dvd_iff_le.trans, singleton_subset_iff, span_le, span_le.trans
-/
theorem dvd_span_singleton {I : Ideal A} {x : A} : I ∣ span {x} ↔ x in I :=
  dvd_iff_le.trans (span_le.trans Set.singleton_subset_iff)

/--
theorem `isPrime_of_prime` / 定理 `isPrime_of_prime`

English:
theorem isPrime_of_prime
  given: {P : Ideal A} (h : Prime P)
  statement: IsPrime P
  proof: by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← one_eq_top] at h
    exact h.not_isUnit isUnit_one
  · simp only [← dvd_span_singleton, ← span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy

中文:
定理 isPrime_of_prime
  条件: {P : 理想 A} (h : 素 P)
  结论: 是素 P
  证明: by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← one_eq_top] at h
    exact h.not_isUnit isUnit_one
  · simp only [← dvd_span_singleton, ← span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy

Depends on / 依赖: dvd_or_dvd, dvd_span_singleton, h.dvd_or_dvd, h.not_isUnit, isUnit_one, not_isUnit, one_eq_top, span_singleton_mul_span_singleton
-/
theorem isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P := by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← one_eq_top] at h
    exact h.not_isUnit isUnit_one
  · simp only [← dvd_span_singleton, ← span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy

/--
theorem `prime_of_isPrime` / 定理 `prime_of_isPrime`

English:
theorem prime_of_isPrime
  given: {P : Ideal A} (hP : P != ⊥) (h : IsPrime P)
  statement: Prime P
  proof: by
  refine ⟨hP, mt isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [dvd_iff_le] using h.mul_le.mp (le_of_dvd hIJ)

中文:
定理 prime_of_isPrime
  条件: {P : 理想 A} (hP : P != ⊥) (h : 是素 P)
  结论: 素 P
  证明: by
  refine ⟨hP, mt isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [dvd_iff_le] using h.mul_le.mp (le_of_dvd hIJ)

Depends on / 依赖: dvd_iff_le, h.mul_le.mp, h.ne_top, isUnit_iff, isUnit_iff.mp, le_of_dvd, mul_le, ne_top
-/
theorem prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h : IsPrime P) : Prime P := by
  refine ⟨hP, mt isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [dvd_iff_le] using h.mul_le.mp (le_of_dvd hIJ)

/--
theorem `prime_of_mem_primesOver` / 定理 `prime_of_mem_primesOver`

English:
theorem prime_of_mem_primesOver
  statement: {R : Type*} [CommRing R] [Algebra R A] {p : Ideal R}
  proof: prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

中文:
定理 prime_of_mem_primesOver
  结论: {R : 类型} [交换环 R] [代数 R A] {p : 理想 R}
  证明: prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

Depends on / 依赖: ne_bot_of_mem_primesOver, prime_of_isPrime
-/
theorem prime_of_mem_primesOver {R : Type*} [CommRing R] [Algebra R A] {p : Ideal R}
    [IsDomain R] [IsTorsionFree R A] (hp : p != ⊥) {P : Ideal A} (hP : P in primesOver p A) :
    Prime P :=
  prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

/--
theorem `prime_iff_isPrime` / 定理 `prime_iff_isPrime`

English:
theorem prime_iff_isPrime
  given: {P : Ideal A} (hP : P != ⊥)
  statement: Prime P ↔ IsPrime P
  proof: ⟨isPrime_of_prime, prime_of_isPrime hP⟩

中文:
定理 prime_iff_isPrime
  条件: {P : 理想 A} (hP : P != ⊥)
  结论: 素 P ↔ 是素 P
  证明: ⟨isPrime_of_prime, prime_of_isPrime hP⟩

Depends on / 依赖: isPrime_of_prime, prime_of_isPrime
-/
theorem prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) : Prime P ↔ IsPrime P :=
  ⟨isPrime_of_prime, prime_of_isPrime hP⟩

/--
theorem `isPrime_iff_bot_or_prime` / 定理 `isPrime_iff_bot_or_prime`

English:
theorem isPrime_iff_bot_or_prime
  given: {P : Ideal A}
  statement: IsPrime P ↔ P = ⊥ ∨ Prime P
  proof: ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ isPrime_bot) isPrime_of_prime⟩

@[simp]

中文:
定理 isPrime_iff_bot_or_prime
  条件: {P : 理想 A}
  结论: 是素 P ↔ P = ⊥ ∨ 素 P
  证明: ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ isPrime_bot) isPrime_of_prime⟩

@[simp]

Depends on / 依赖: eq_or_ne, h.symm, hp.elim, imp_right, isPrime_bot, isPrime_of_prime, prime_of_isPrime
-/
theorem isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ isPrime_bot) isPrime_of_prime⟩

@[simp]
/--
theorem `prime_span_singleton_iff` / 定理 `prime_span_singleton_iff`

English:
theorem prime_span_singleton_iff
  given: {a : A}
  statement: Prime (span {a}) ↔ Prime a
  proof: by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} != ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [prime_iff_isPrime ha']; rw [span_singleton_prime

中文:
定理 prime_span_singleton_iff
  条件: {a : A}
  结论: 素 (span {a}) ↔ 素 a
  证明: by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} != ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [prime_iff_isPrime ha']; rw [span_singleton_prime

Depends on / 依赖: Set.singleton_zero, eq_or_ne, ne_eq, not_false_eq_true, not_iff_not, not_prime_zero, prime_iff_isPrime, singleton_zero, span_singleton_eq_bot, span_singleton_prime, span_zero, zero_eq_bot
-/
theorem prime_span_singleton_iff {a : A} : Prime (span {a}) ↔ Prime a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} != ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [prime_iff_isPrime ha']; rw [span_singleton_prime ha]

open Submodule.IsPrincipal in
/--
theorem `prime_generator_of_prime` / 定理 `prime_generator_of_prime`

English:
theorem prime_generator_of_prime
  given: {P : Ideal A} (h : Prime P) [P.IsPrincipal]
  proof: have : IsPrime P := isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

中文:
定理 prime_generator_of_prime
  条件: {P : 理想 A} (h : 素 P) [P.是Principal]
  证明: have : IsPrime P := isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

Depends on / 依赖: IsPrime, h.ne_zero, isPrime_of_prime, ne_zero, prime_generator_of_isPrime
-/
theorem prime_generator_of_prime {P : Ideal A} (h : Prime P) [P.IsPrincipal] :
    Prime (generator P) :=
  have : IsPrime P := isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

open UniqueFactorizationMonoid in
nonrec theorem mem_normalizedFactors_iff {p I : Ideal A} (hI : I != ⊥) :
    p in normalizedFactors I ↔ p.IsPrime ∧ I <= p := by
  rw [← dvd_iff_le]
  by_cases hp : p = 0
  · rw [← zero_eq_bot] at hI
    simp only [hp, zero_notMem_normalizedFactors, zero_dvd_iff, hI, false_iff, not_and,
      not_false_eq_true, implies_true]
  · rwa [mem_normalizedFactors_iff hI, prime_iff_isPrime]

variable (A) in
open UniqueFactorizationMonoid in
/--
theorem `mem_primesOver_iff_mem_normalizedFactors` / 定理 `mem_primesOver_iff_mem_normalizedFactors`

English:
theorem mem_primesOver_iff_mem_normalizedFactors
  statement: {p : Ideal R} [h : p.IsMaximal]
  proof: by
  rw [primesOver]; rw [Set.mem_ofPred_eq]; rw [mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hp)]; rw [liesOver_iff]; rw [under_def]; rw [and_congr_right_iff]; rw [map_le_iff_le_comap]
  intro hP
  refine ⟨fun h => le_of_eq h, fun h' => ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩

中文:
定理 mem_primesOver_iff_mem_normalizedFactors
  结论: {p : 理想 R} [h : p.是极大]
  证明: by
  rw [primesOver]; rw [Set.mem_ofPred_eq]; rw [mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hp)]; rw [liesOver_iff]; rw [under_def]; rw [and_congr_right_iff]; rw [map_le_iff_le_comap]
  intro hP
  refine ⟨fun h => le_of_eq h, fun h' => ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩

Depends on / 依赖: IsCoatom, IsCoatom.le_iff_eq, IsPrime, IsPrime.ne_top, Set.mem_ofPred_eq, algebraMap, and_congr_right_iff, comap_ne_top, isMaximal_def, isMaximal_def.mp, le_iff_eq, le_of_eq, liesOver_iff, map_le_iff_le_comap, map_ne_bot_of_ne_bot, mem_normalizedFactors_iff, mem_ofPred_eq, ne_top, primesOver, under_def
-/
theorem mem_primesOver_iff_mem_normalizedFactors {p : Ideal R} [h : p.IsMaximal]
    [Algebra R A] [IsDomain R] [IsTorsionFree R A] (hp : p != ⊥) {P : Ideal A} :
    P in p.primesOver A ↔ P in normalizedFactors (map (algebraMap R A) p) := by
  rw [primesOver]; rw [Set.mem_ofPred_eq]; rw [mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hp)]; rw [liesOver_iff]; rw [under_def]; rw [and_congr_right_iff]; rw [map_le_iff_le_comap]
  intro hP
  refine ⟨fun h => le_of_eq h, fun h' => ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩
  exact comap_ne_top (algebraMap R A) (IsPrime.ne_top hP)

/--
theorem `pow_right_strictAnti` / 定理 `pow_right_strictAnti`

English:
theorem pow_right_strictAnti
  given: (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤)
  proof: strictAnti_nat_of_succ_lt fun e =>
    dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩

中文:
定理 pow_right_strictAnti
  条件: (I : 理想 A) (hI0 : I != ⊥) (hI1 : I != ⊤)
  证明: strictAnti_nat_of_succ_lt fun e =>
    dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩

Depends on / 依赖: dvdNotUnit_iff_lt, dvdNotUnit_iff_lt.mp, isUnit_iff, isUnit_iff.mp, pow_ne_zero, pow_succ, strictAnti_nat_of_succ_lt
-/
theorem pow_right_strictAnti (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) :
    StrictAnti (I ^ · : Nat -> Ideal A) :=
  strictAnti_nat_of_succ_lt fun e =>
    dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩

/--
theorem `pow_lt_self` / 定理 `pow_lt_self`

English:
theorem pow_lt_self
  given: (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : Nat) (he : 2 <= e)
  proof: by
  convert! I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]

中文:
定理 pow_lt_self
  条件: (I : 理想 A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : 自然数) (he : 2 <= e)
  证明: by
  convert! I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]

Depends on / 依赖: I.pow_right_strictAnti, convert, pow_one, pow_right_strictAnti
-/
theorem pow_lt_self (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : Nat) (he : 2 <= e) :
    I ^ e < I := by
  convert! I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]

/--
theorem `exists_mem_pow_notMem_pow_succ` / 定理 `exists_mem_pow_notMem_pow_succ`

English:
theorem exists_mem_pow_notMem_pow_succ
  given: (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : Nat)
  proof: SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)

中文:
定理 存在_mem_pow_notMem_pow_succ
  条件: (I : 理想 A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : 自然数)
  证明: SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)

Depends on / 依赖: I.pow_right_strictAnti, SetLike, SetLike.exists_of_lt, e.lt_succ_self, exists_of_lt, lt_succ_self, pow_right_strictAnti
-/
theorem exists_mem_pow_notMem_pow_succ (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : Nat) :
    exists x in I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)

open UniqueFactorizationMonoid

/--
theorem `eq_prime_pow_of_succ_lt_of_le` / 定理 `eq_prime_pow_of_succ_lt_of_le`

English:
theorem eq_prime_pow_of_succ_lt_of_le
  statement: {P I : Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥)
  proof: by
  refine le_antisymm hle ?_
  have P_prime' := prime_of_isPrime hP P_prime
  have h1 : I != ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← dvdNotUnit_iff_lt]; rw [dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3]; rw [normali

中文:
定理 eq_prime_pow_of_succ_lt_of_le
  结论: {P I : 理想 A} [P_prime : P.是素] (hP : P != ⊥)
  证明: by
  refine le_antisymm hle ?_
  have P_prime' := prime_of_isPrime hP P_prime
  have h1 : I != ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← dvdNotUnit_iff_lt]; rw [dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3]; rw [normali

Depends on / 依赖: Multiset, Multiset.lt_replicate_succ, Multiset.nsmul_singleton, P_prime, bot_le, dvdNotUnit_iff_lt, dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors, dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactor, irreducible, le_antisymm, lt_of_le_of_lt, lt_replicate_succ, normalizedFactors_irreducible, normalizedFactors_pow, nsmul_singleton, pow_ne_zero, prime_of_isPrime
-/
theorem eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥)
    {i : Nat} (hlt : P ^ (i + 1) < I) (hle : I <= P ^ i) : I = P ^ i := by
  refine le_antisymm hle ?_
  have P_prime' := prime_of_isPrime hP P_prime
  have h1 : I != ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← dvdNotUnit_iff_lt]; rw [dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3]; rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible P_prime'.irreducible]; rw [Multiset.nsmul_singleton]; rw [Multiset.lt_replicate_succ] at hlt
  rw [← dvd_iff_le]; rw [dvd_iff_normalizedFactors_le_normalizedFactors]; rw [normalizedFactors_pow]; rw [normalizedFactors_irreducible P_prime'.irreducible]; rw [Multiset.nsmul_singleton]
  all_goals assumption

/--
theorem `pow_succ_lt_pow` / 定理 `pow_succ_lt_pow`

English:
theorem pow_succ_lt_pow
  given: {P : Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥) (i : Nat)
  proof: lt_of_le_of_ne (pow_le_pow_right (Nat.le_succ _))
    (mt (pow_inj_of_not_isUnit (mt isUnit_iff.mp P_prime.ne_top) hP).mp i.succ_ne_self)

中文:
定理 pow_succ_lt_pow
  条件: {P : 理想 A} [P_prime : P.是素] (hP : P != ⊥) (i : 自然数)
  证明: lt_of_le_of_ne (pow_le_pow_right (Nat.le_succ _))
    (mt (pow_inj_of_not_isUnit (mt isUnit_iff.mp P_prime.ne_top) hP).mp i.succ_ne_self)

Depends on / 依赖: Nat.le_succ, P_prime, P_prime.ne_top, i.succ_ne_self, isUnit_iff, isUnit_iff.mp, le_succ, lt_of_le_of_ne, ne_top, pow_inj_of_not_isUnit, pow_le_pow_right, succ_ne_self
-/
theorem pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥) (i : Nat) :
    P ^ (i + 1) < P ^ i :=
  lt_of_le_of_ne (pow_le_pow_right (Nat.le_succ _))
    (mt (pow_inj_of_not_isUnit (mt isUnit_iff.mp P_prime.ne_top) hP).mp i.succ_ne_self)

end Ideal

/--
theorem `Associates.le_singleton_iff` / 定理 `Associates.le_singleton_iff`

English:
theorem Associates.le_singleton_iff
  given: (x : A) (n : Nat) (I : Ideal A)
  proof: by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]

中文:
定理 Associates.le_singleton_iff
  条件: (x : A) (n : 自然数) (I : 理想 A)
  证明: by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]

Depends on / 依赖: Associates, Associates.dvd_eq_le, Associates.mk_dvd_mk, Associates.mk_pow, Ideal.dvd_span_singleton, dvd_eq_le, dvd_span_singleton, mk_dvd_mk, mk_pow, simp_rw
-/
theorem Associates.le_singleton_iff (x : A) (n : Nat) (I : Ideal A) :
    Associates.mk I ^ n <= Associates.mk (Ideal.span {x}) ↔ x in I ^ n := by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]

variable {K}

namespace FractionalIdeal

/--
lemma `le_inv_comm` / 引理 `le_inv_comm`

English:
lemma le_inv_comm
  given: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  proof: by
  rw [inv_eq]; rw [inv_eq]; rw [le_div_iff_mul_le hI]; rw [le_div_iff_mul_le hJ]; rw [mul_comm]

中文:
引理 le_inv_comm
  条件: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  证明: by
  rw [inv_eq]; rw [inv_eq]; rw [le_div_iff_mul_le hI]; rw [le_div_iff_mul_le hJ]; rw [mul_comm]

Depends on / 依赖: inv_eq, le_div_iff_mul_le, mul_comm
-/
lemma le_inv_comm {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) :
    I <= J⁻¹ ↔ J <= I⁻¹ := by
  rw [inv_eq]; rw [inv_eq]; rw [le_div_iff_mul_le hI]; rw [le_div_iff_mul_le hJ]; rw [mul_comm]

/--
lemma `inv_le_comm` / 引理 `inv_le_comm`

English:
lemma inv_le_comm
  given: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  proof: by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

@[simp]

中文:
引理 inv_le_comm
  条件: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  证明: by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

@[simp]

Depends on / 依赖: inv_ne_zero, le_inv_comm
-/
lemma inv_le_comm {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) :
    I⁻¹ <= J ↔ J⁻¹ <= I := by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

@[simp]
/--
theorem `inv_le_inv_iff` / 定理 `inv_le_inv_iff`

English:
theorem inv_le_inv_iff
  given: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  proof: by
  rw [le_inv_comm (inv_ne_zero hI) hJ]; rw [inv_inv]

中文:
定理 inv_le_inv_iff
  条件: {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0)
  证明: by
  rw [le_inv_comm (inv_ne_zero hI) hJ]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_ne_zero, le_inv_comm
-/
theorem inv_le_inv_iff {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) :
    I⁻¹ <= J⁻¹ ↔ J <= I := by
  rw [le_inv_comm (inv_ne_zero hI) hJ]; rw [inv_inv]

end FractionalIdeal

namespace Ideal

/--
theorem `exist_integer_multiples_notMem` / 定理 `exist_integer_multiples_notMem`

English:
theorem exist_integer_multiples_notMem
  statement: {J : Ideal A} (hJ : J != ⊤) {ι : Type*} (s : Finset ι)
  proof: by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I != 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI

中文:
定理 exist_integer_multiples_notMem
  结论: {J : 理想 A} (hJ : J != ⊤) {ι : 类型} (s : 有限集 ι)
  证明: by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I != 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI
-/
theorem exist_integer_multiples_notMem {J : Ideal A} (hJ : J != ⊤) {ι : Type*} (s : Finset ι)
    (f : ι -> K) {j} (hjs : j in s) (hjf : f j != 0) :
    exists a : K,
      (forall i in s, IsLocalization.IsInteger A (a * f i)) ∧
        exists i in s, a * f i ∉ (J : FractionalIdeal A⁰ K) := by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I != 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI⟩ := SetLike.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI
    refine ⟨a, fun i hi => ?_, ?_⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine (mem_div_iff_of_ne_zero hI0).mpr fun y hy => Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, rfl⟩; exact hpI i hi
      · rw [mul_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
      · intro b x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  rw [div_eq_mul_inv]
  refine mul_lt_of_lt_one_left (by simpa [pos_iff_ne_zero]) ?_
  rw [← coeIdeal_top]
  -- And multiplying by `I⁻¹` is indeed strictly monotone.
  exact
    strictMono_of_le_iff_le (fun _ _ => (coeIdeal_le_coeIdeal K).symm)
      (lt_top_iff_ne_top.mpr hJ)

/--
lemma `mul_iInf` / 引理 `mul_iInf`

English:
lemma mul_iInf
  given: (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A)
  proof: by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i => mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i <= I := (iInf_le _ (Nonempty.some ‹_›)).trans mul_le_left
  obtain ⟨K, hK⟩ := dvd_iff_le.mpr H
  grw [hK, le_iInf (a := K) fun i => ?_]
  rw [← mul_le_mul_iff_of_pos_le

中文:
引理 mul_iInf
  条件: (I : 理想 A) {ι : 类型} [非空 ι] (J : ι -> 理想 A)
  证明: by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i => mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i <= I := (iInf_le _ (Nonempty.some ‹_›)).trans mul_le_left
  obtain ⟨K, hK⟩ := dvd_iff_le.mpr H
  grw [hK, le_iInf (a := K) fun i => ?_]
  rw [← mul_le_mul_iff_of_pos_le

Depends on / 依赖: Nonempty, Nonempty.some, antisymm, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, dvd_iff_le, dvd_iff_le.mpr, iInf_le, le_iInf, mul_le_left, mul_le_mul_iff_of_pos_left, mul_mono_right
-/
lemma mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A) :
    I * ⨅ i, J i = ⨅ i, I * J i := by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i => mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i <= I := (iInf_le _ (Nonempty.some ‹_›)).trans mul_le_left
  obtain ⟨K, hK⟩ := dvd_iff_le.mpr H
  grw [hK, le_iInf (a := K) fun i => ?_]
  rw [← mul_le_mul_iff_of_pos_left (a := I)]; rw [← hK]
  · exact iInf_le _ _
  · exact bot_lt_iff_ne_bot.mpr hI

/--
lemma `iInf_mul` / 引理 `iInf_mul`

English:
lemma iInf_mul
  given: (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A)
  proof: by
  simp only [mul_iInf, mul_comm _ I]

中文:
引理 iInf_mul
  条件: (I : 理想 A) {ι : 类型} [非空 ι] (J : ι -> 理想 A)
  证明: by
  simp only [mul_iInf, mul_comm _ I]

Depends on / 依赖: mul_comm, mul_iInf
-/
lemma iInf_mul (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A) :
    (⨅ i, J i) * I = ⨅ i, J i * I := by
  simp only [mul_iInf, mul_comm _ I]

/--
lemma `mul_inf` / 引理 `mul_inf`

English:
lemma mul_inf
  given: (I J K : Ideal A)
  statement: I * (J ⊓ K) = I * J ⊓ I * K
  proof: by
  rw [inf_eq_iInf]; rw [mul_iInf]; rw [inf_eq_iInf]
  congr! 2 with ⟨⟩

中文:
引理 mul_inf
  条件: (I J K : 理想 A)
  结论: I * (J ⊓ K) = I * J ⊓ I * K
  证明: by
  rw [inf_eq_iInf]; rw [mul_iInf]; rw [inf_eq_iInf]
  congr! 2 with ⟨⟩

Depends on / 依赖: inf_eq_iInf, mul_iInf
-/
lemma mul_inf (I J K : Ideal A) : I * (J ⊓ K) = I * J ⊓ I * K := by
  rw [inf_eq_iInf]; rw [mul_iInf]; rw [inf_eq_iInf]
  congr! 2 with ⟨⟩

/--
lemma `inf_mul` / 引理 `inf_mul`

English:
lemma inf_mul
  given: (I J K : Ideal A)
  statement: (I ⊓ J) * K = I * K ⊓ J * K
  proof: by
  simp only [mul_inf, mul_comm _ K]

中文:
引理 inf_mul
  条件: (I J K : 理想 A)
  结论: (I ⊓ J) * K = I * K ⊓ J * K
  证明: by
  simp only [mul_inf, mul_comm _ K]

Depends on / 依赖: mul_comm, mul_inf
-/
lemma inf_mul (I J K : Ideal A) : (I ⊓ J) * K = I * K ⊓ J * K := by
  simp only [mul_inf, mul_comm _ K]

end Ideal

/--
lemma `FractionalIdeal.mul_inf` / 引理 `FractionalIdeal.mul_inf`

English:
lemma FractionalIdeal.mul_inf
  given: (I J K : FractionalIdeal A⁰ K)
  statement: I * (J ⊓ K) = I * J ⊓ I * K
  proof: mul_inf₀ (zero_le _) _ _

中文:
引理 FractionalIdeal.mul_inf
  条件: (I J K : FractionalIdeal A⁰ K)
  结论: I * (J ⊓ K) = I * J ⊓ I * K
  证明: mul_inf₀ (zero_le _) _ _

Depends on / 依赖: zero_le
-/
lemma FractionalIdeal.mul_inf (I J K : FractionalIdeal A⁰ K) : I * (J ⊓ K) = I * J ⊓ I * K :=
  mul_inf₀ (zero_le _) _ _

/--
lemma `FractionalIdeal.inf_mul` / 引理 `FractionalIdeal.inf_mul`

English:
lemma FractionalIdeal.inf_mul
  given: (I J K : FractionalIdeal A⁰ K)
  statement: (I ⊓ J) * K = I * K ⊓ J * K
  proof: inf_mul₀ (zero_le _) _ _

中文:
引理 FractionalIdeal.inf_mul
  条件: (I J K : FractionalIdeal A⁰ K)
  结论: (I ⊓ J) * K = I * K ⊓ J * K
  证明: inf_mul₀ (zero_le _) _ _

Depends on / 依赖: zero_le
-/
lemma FractionalIdeal.inf_mul (I J K : FractionalIdeal A⁰ K) : (I ⊓ J) * K = I * K ⊓ J * K :=
  inf_mul₀ (zero_le _) _ _

section Gcd

namespace Ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `NormalizedGCDMonoid (Ideal A)`.
-/


@[simp]
/--
theorem `sup_mul_inf` / 定理 `sup_mul_inf`

English:
theorem sup_mul_inf
  given: (I J : Ideal A)
  statement: (I ⊔ J) * (I ⊓ J) = I * J
  proof: by
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _]; rw [normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le

中文:
定理 sup_mul_inf
  条件: (I J : 理想 A)
  结论: (I ⊔ J) * (I ⊓ J) = I * J
  证明: by
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _]; rw [normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.toNormalizedGCDMonoid, dvd_gcd_iff, dvd_iff_le, dvd_lcm_lef, gcd_dvd_left, gcd_dvd_right, gcd_eq_normalize, lcm_dvd_iff, lcm_eq_normalize, le_inf_iff, normalize_eq, sup_le_iff, toNormalizedGCDMonoid
-/
theorem sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J := by
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _]; rw [normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le]
      simp
  have hlcm : lcm I J = I ⊓ J := by
    rw [lcm_eq_normalize _ _]; rw [normalize_eq]
    · rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le]
      simp
    · rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩
  rw [← hgcd]; rw [← hlcm]; rw [associated_iff_eq.mp (gcd_mul_lcm _ _)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongNormalizedGCDMonoid (Ideal A)
  body: { strongNormalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ 

中文:
实例 :
  签名: StrongNormalizedGCD幺半群 (理想 A)
  定义体: { strongNormalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ 

Depends on / 依赖: associated_iff_eq, bot_inf_eq, dvd_gcd, dvd_iff_le, gcd_dvd_left, gcd_dvd_right, gcd_mul_lcm, inf_bot_eq, lcm_zero_left, lcm_zero_right, le_sup_left, le_sup_right, normali, strongNormalizationMonoid, sup_le, sup_mul_inf, zero_eq_bot
-/
noncomputable instance : StrongNormalizedGCDMonoid (Ideal A) :=
  { strongNormalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ _ _ h1 h2
    lcm := (· ⊓ ·)
    lcm_zero_left := fun _ => by simp only [zero_eq_bot, bot_inf_eq]
    lcm_zero_right := fun _ => by simp only [zero_eq_bot, inf_bot_eq]
    gcd_mul_lcm := fun _ _ => by rw [associated_iff_eq, sup_mul_inf]
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp]
/--
theorem `gcd_eq_sup` / 定理 `gcd_eq_sup`

English:
theorem gcd_eq_sup
  given: (I J : Ideal A)
  statement: gcd I J = I ⊔ J
  proof: rfl

@[simp]

中文:
定理 gcd_eq_sup
  条件: (I J : 理想 A)
  结论: 最大公约数 I J = I ⊔ J
  证明: rfl

@[simp]
-/
theorem gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J := rfl

@[simp]
/--
theorem `lcm_eq_inf` / 定理 `lcm_eq_inf`

English:
theorem lcm_eq_inf
  given: (I J : Ideal A)
  statement: lcm I J = I ⊓ J
  proof: rfl

中文:
定理 lcm_eq_inf
  条件: (I J : 理想 A)
  结论: 最小公倍数 I J = I ⊓ J
  证明: rfl
-/
theorem lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J := rfl

/--
theorem `isCoprime_iff_gcd` / 定理 `isCoprime_iff_gcd`

English:
theorem isCoprime_iff_gcd
  given: {I J : Ideal A}
  statement: IsCoprime I J ↔ gcd I J = 1
  proof: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [one_eq_top]; rw [gcd_eq_sup]

中文:
定理 isCoprime_iff_gcd
  条件: {I J : 理想 A}
  结论: IsCoprime I J ↔ 最大公约数 I J = 1
  证明: by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [one_eq_top]; rw [gcd_eq_sup]

Depends on / 依赖: codisjoint_iff, gcd_eq_sup, isCoprime_iff_codisjoint, one_eq_top
-/
theorem isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I J ↔ gcd I J = 1 := by
  rw [isCoprime_iff_codisjoint]; rw [codisjoint_iff]; rw [one_eq_top]; rw [gcd_eq_sup]

open UniqueFactorizationMonoid

/--
theorem `factors_span_eq` / 定理 `factors_span_eq`

English:
theorem factors_span_eq
  given: {p : K[X]}
  statement: factors (span {p}) = (factors p).map (fun q => span {q})
  proof: by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using! normalizedFactors_zero
  have : forall q in (factors p).map (fun q => span {q}), Prime q := fun q hq => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
exact prime_span_singleton_iff.mpr prime_of_factor r hr
  rw [← spa

中文:
定理 factors_span_eq
  条件: {p : K[X]}
  结论: factors (span {p}) = (factors p).map (fun q => span {q})
  证明: by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using! normalizedFactors_zero
  have : forall q in (factors p).map (fun q => span {q}), Prime q := fun q hq => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
exact prime_span_singleton_iff.mpr prime_of_factor r hr
  rw [← spa

Depends on / 依赖: Multiset, Multiset.mem_map.mp, Set.singleton_zero, eq_or_ne, factors, factors_eq_normalizedFactors, factors_prod, mem_map, multiset_prod_span_singleton, normalizedFactors_prod_of_prime, normalizedFactors_zero, prime_of_factor, prime_span_singleton_iff, prime_span_singleton_iff.mpr, singleton_zero, span_singleton_eq_span_singleton, span_singleton_eq_span_singleton.mpr
-/
theorem factors_span_eq {p : K[X]} : factors (span {p}) = (factors p).map (fun q => span {q}) := by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using! normalizedFactors_zero
  have : forall q in (factors p).map (fun q => span {q}), Prime q := fun q hq => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
exact prime_span_singleton_iff.mpr prime_of_factor r hr
  rw [← span_singleton_eq_span_singleton.mpr (factors_prod hp)]; rw [← multiset_prod_span_singleton]; rw [factors_eq_normalizedFactors]; rw [normalizedFactors_prod_of_prime this]

end Ideal

/--
lemma `FractionalIdeal.sup_mul_inf` / 引理 `FractionalIdeal.sup_mul_inf`

English:
lemma FractionalIdeal.sup_mul_inf
  given: (I J : FractionalIdeal A⁰ K)
  proof: by
  apply mul_left_injective₀ (b := spanSingleton A⁰ (algebraMap A K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeI

中文:
引理 FractionalIdeal.sup_mul_inf
  条件: (I J : FractionalIdeal A⁰ K)
  证明: by
  apply mul_left_injective₀ (b := spanSingleton A⁰ (algebraMap A K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeI

Depends on / 依赖: FractionalIdeal, FractionalIdeal.zero_le, I.den, I.num, Ideal.span, Ideal.sup_mul_inf, J.den, J.num, algebraMap, coeIdeal_inf, coeIdeal_inj, coeIdeal_mul, coeIdeal_span_singleton, coeIdeal_sup, den_mul_self_eq_num, mul_add, mul_left_comm, spanSingleton, spanSingleton_eq_zero_iff, sup_mul_inf
-/
lemma FractionalIdeal.sup_mul_inf (I J : FractionalIdeal A⁰ K) :
    (I ⊓ J) * (I ⊔ J) = I * J := by
  apply mul_left_injective₀ (b := spanSingleton A⁰ (algebraMap A K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeIdeal_sup, coeIdeal_inf,
    ← den_mul_self_eq_num', coeIdeal_span_singleton] at this
  rw [mul_left_comm]; rw [← mul_add]; rw [← mul_add]; rw [← mul_inf₀ (FractionalIdeal.zero_le _)]; rw [← mul_inf₀ (FractionalIdeal.zero_le _)] at this
  simp only [FractionalIdeal.sup_eq_add, _root_.map_mul, ← spanSingleton_mul_spanSingleton]
  convert! this using 1 <;> ring

end Gcd

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type*} [CommRing T] [IsDedekindDomain T] {I J : Ideal T}

open Multiset UniqueFactorizationMonoid

namespace Ideal

/--
theorem `prod_normalizedFactors_eq_self` / 定理 `prod_normalizedFactors_eq_self`

English:
theorem prod_normalizedFactors_eq_self
  given: (hI : I != ⊥)
  statement: (normalizedFactors I).prod = I
  proof: associated_iff_eq.1 (prod_normalizedFactors hI)

@[deprecated (since := "2026-04-16")]
alias _root_.prod_normalizedFactors_eq_self := prod_normalizedFactors_eq_self

中文:
定理 prod_normalizedFactors_eq_self
  条件: (hI : I != ⊥)
  结论: (normalizedFactors I).乘积 = I
  证明: associated_iff_eq.1 (prod_normalizedFactors hI)

@[deprecated (since := "2026-04-16")]
alias _root_.prod_normalizedFactors_eq_self := prod_normalizedFactors_eq_self

Depends on / 依赖: associated_iff_eq, prod_normalizedFactors
-/
theorem prod_normalizedFactors_eq_self (hI : I != ⊥) : (normalizedFactors I).prod = I :=
  associated_iff_eq.1 (prod_normalizedFactors hI)

@[deprecated (since := "2026-04-16")]
alias _root_.prod_normalizedFactors_eq_self := prod_normalizedFactors_eq_self

/--
theorem `count_le_of_ideal_ge` / 定理 `count_le_of_ideal_ge`

English:
theorem count_le_of_ideal_ge
  proof: le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _

@[deprecated (since := "2026-04-16")] alias _root_.count_le_of_ideal_ge := count_le_of_ideal_ge

中文:
定理 count_le_of_ideal_ge
  证明: le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _

@[deprecated (since := "2026-04-16")] alias _root_.count_le_of_ideal_ge := count_le_of_ideal_ge

Depends on / 依赖: dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, le_iff_count, ne_bot_of_le_ne_bot
-/
theorem count_le_of_ideal_ge
    {I J : Ideal T} (h : I <= J) (hI : I != ⊥) (K : Ideal T) :
    count K (normalizedFactors J) <= count K (normalizedFactors I) :=
  le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _

@[deprecated (since := "2026-04-16")] alias _root_.count_le_of_ideal_ge := count_le_of_ideal_ge

/--
theorem `sup_eq_prod_inf_factors` / 定理 `sup_eq_prod_inf_factors`

English:
theorem sup_eq_prod_inf_factors
  given: (hI : I != ⊥) (hJ : J != ⊥)
  proof: by
  have := prod_inter_normalizedFactors_ne_zero I J
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor <;>
      rw [dvd_iff_normalizedFactors_le_normalizedFactors this (by assumption)]; rw [normalizedFactors_prod_inter_eq_inter]
    exacts [inf_le_left, inf_le_rig

中文:
定理 sup_eq_prod_inf_factors
  条件: (hI : I != ⊥) (hJ : J != ⊥)
  证明: by
  have := prod_inter_normalizedFactors_ne_zero I J
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor <;>
      rw [dvd_iff_normalizedFactors_le_normalizedFactors this (by assumption)]; rw [normalizedFactors_prod_inter_eq_inter]
    exacts [inf_le_left, inf_le_rig

Depends on / 依赖: Multiset, Multiset.count_inter, count_inter, dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, exacts, inf_le_left, inf_le_right, le_antisymm, le_iff_count, le_sup_left, ne_bot_of_le_ne_bot, normalizedFactors_prod_inter_eq_inter, prod_inter_normalizedFactors_ne_zero, sup_le_iff
-/
theorem sup_eq_prod_inf_factors (hI : I != ⊥) (hJ : J != ⊥) :
    I ⊔ J = (normalizedFactors I inter normalizedFactors J).prod := by
  have := prod_inter_normalizedFactors_ne_zero I J
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor <;>
      rw [dvd_iff_normalizedFactors_le_normalizedFactors this (by assumption)]; rw [normalizedFactors_prod_inter_eq_inter]
    exacts [inf_le_left, inf_le_right]
  · rw [← dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors ?H this,
      normalizedFactors_prod_inter_eq_inter, le_iff_count]
    case H => exact ne_bot_of_le_ne_bot hI le_sup_left
    intro a
    rw [Multiset.count_inter]
    exact le_min (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)

@[deprecated (since := "2026-04-16")]
alias _root_.sup_eq_prod_inf_factors := sup_eq_prod_inf_factors

/--
theorem `irreducible_pow_sup` / 定理 `irreducible_pow_sup`

English:
theorem irreducible_pow_sup
  given: (hI : I != ⊥) (hJ : Irreducible J) (n : Nat)
  proof: by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI]; rw [min_comm]; rw [normalizedFactors_of_irreducible_pow hJ]; rw [normalize_eq J]; rw [replicate_inter]; rw [prod_replicate]

@[deprecated (since := "2026-04-16")] alias _root_.irreducible_pow_sup := irreducible_pow_sup

中文:
定理 irreducible_pow_sup
  条件: (hI : I != ⊥) (hJ : 不可约 J) (n : 自然数)
  证明: by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI]; rw [min_comm]; rw [normalizedFactors_of_irreducible_pow hJ]; rw [normalize_eq J]; rw [replicate_inter]; rw [prod_replicate]

@[deprecated (since := "2026-04-16")] alias _root_.irreducible_pow_sup := irreducible_pow_sup

Depends on / 依赖: hJ.ne_zero, min_comm, ne_zero, normalize_eq, normalizedFactors_of_irreducible_pow, pow_ne_zero, prod_replicate, replicate_inter, sup_eq_prod_inf_factors
-/
theorem irreducible_pow_sup (hI : I != ⊥) (hJ : Irreducible J) (n : Nat) :
    J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n := by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI]; rw [min_comm]; rw [normalizedFactors_of_irreducible_pow hJ]; rw [normalize_eq J]; rw [replicate_inter]; rw [prod_replicate]

@[deprecated (since := "2026-04-16")] alias _root_.irreducible_pow_sup := irreducible_pow_sup

/--
theorem `irreducible_pow_sup_of_le` / 定理 `irreducible_pow_sup_of_le`

English:
theorem irreducible_pow_sup_of_le
  given: (hJ : Irreducible J) (n : Nat) (hn : n <= emultiplicity J I)
  proof: by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_right]
  rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J] at hn
  exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_le := irreducible_pow_sup_of_le

中文:
定理 irreducible_pow_sup_of_le
  条件: (hJ : 不可约 J) (n : 自然数) (hn : n <= emultiplicity J I)
  证明: by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_right]
  rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J] at hn
  exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_le := irreducible_pow_sup_of_le

Depends on / 依赖: emultiplicity_eq_count_normalizedFactors, irreducible_pow_sup, min_eq_right, normalize_eq
-/
theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : Nat) (hn : n <= emultiplicity J I) :
    J ^ n ⊔ I = J ^ n := by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_right]
  rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J] at hn
  exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_le := irreducible_pow_sup_of_le

/--
theorem `irreducible_pow_sup_of_ge` / 定理 `irreducible_pow_sup_of_ge`

English:
theorem irreducible_pow_sup_of_ge
  statement: (hI : I != ⊥) (hJ : Irreducible J) (n : Nat)
  proof: by
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_left]
  · congr
    rw [← Nat.cast_inj (R := Nat∞)]; rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity]; rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J]
    rw [← emultiplicity_lt_top]
    apply hn.trans_lt
    simp
  · rw

中文:
定理 irreducible_pow_sup_of_ge
  结论: (hI : I != ⊥) (hJ : 不可约 J) (n : 自然数)
  证明: by
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_left]
  · congr
    rw [← Nat.cast_inj (R := Nat∞)]; rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity]; rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J]
    rw [← emultiplicity_lt_top]
    apply hn.trans_lt
    simp
  · rw

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.emultiplicity_eq_multiplicity, Nat.cast_inj, cast_inj, emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_multiplicity, emultiplicity_lt_top, hn.trans_lt, irreducible_pow_sup, min_eq_left, normalize_eq, trans_lt
-/
theorem irreducible_pow_sup_of_ge (hI : I != ⊥) (hJ : Irreducible J) (n : Nat)
    (hn : emultiplicity J I <= n) : J ^ n ⊔ I = J ^ multiplicity J I := by
  rw [irreducible_pow_sup hI hJ]; rw [min_eq_left]
  · congr
    rw [← Nat.cast_inj (R := Nat∞)]; rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity]; rw [emultiplicity_eq_count_normalizedFactors hJ hI]; rw [normalize_eq J]
    rw [← emultiplicity_lt_top]
    apply hn.trans_lt
    simp
  · rw [emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J] at hn
    exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_ge := irreducible_pow_sup_of_ge

/--
theorem `eq_prime_pow_mul_coprime` / 定理 `eq_prime_pow_mul_coprime`

English:
theorem eq_prime_pow_mul_coprime
  statement: {I : Ideal T} (hI : I != ⊥)
  proof: by
  use (filter (¬ P = ·) (normalizedFactors I)).prod
  constructor
  · refine P.sup_multiset_prod_eq_top (fun p hpi => ?_)
    have hp : Prime p := prime_of_normalized_factor p (filter_subset _ (normalizedFactors I) hpi)
    exact hpm.coprime_of_ne ((isPrime_of_prime hp).isMaximal hp.ne_zero) (of_

中文:
定理 eq_prime_pow_mul_coprime
  结论: {I : 理想 T} (hI : I != ⊥)
  证明: by
  use (filter (¬ P = ·) (normalizedFactors I)).prod
  constructor
  · refine P.sup_multiset_prod_eq_top (fun p hpi => ?_)
    have hp : Prime p := prime_of_normalized_factor p (filter_subset _ (normalizedFactors I) hpi)
    exact hpm.coprime_of_ne ((isPrime_of_prime hp).isMaximal hp.ne_zero) (of_

Depends on / 依赖: P.sup_multiset_prod_eq_top, coprime_of_ne, filter, filter_add_not, filter_subset, hp.ne_zero, hpm.coprime_of_ne, isMaximal, isPrime_of_prime, ne_zero, normalizedFactors, nth_rw, of_mem_filter, pow_count, prime_of_normalized_factor, prod_add, prod_normalizedFactors_eq_self, sup_multiset_prod_eq_top
-/
theorem eq_prime_pow_mul_coprime {I : Ideal T} (hI : I != ⊥)
    (P : Ideal T) [hpm : P.IsMaximal] :
    exists Q : Ideal T, P ⊔ Q = ⊤ ∧ I = P ^ (Multiset.count P (normalizedFactors I)) * Q := by
  use (filter (¬ P = ·) (normalizedFactors I)).prod
  constructor
  · refine P.sup_multiset_prod_eq_top (fun p hpi => ?_)
    have hp : Prime p := prime_of_normalized_factor p (filter_subset _ (normalizedFactors I) hpi)
    exact hpm.coprime_of_ne ((isPrime_of_prime hp).isMaximal hp.ne_zero) (of_mem_filter hpi)
  · nth_rw 1 [← prod_normalizedFactors_eq_self hI, ← filter_add_not (P = ·) (normalizedFactors I)]
    rw [prod_add]; rw [pow_count]

/--
theorem `map_prime_of_equiv` / 定理 `map_prime_of_equiv`

English:
theorem map_prime_of_equiv
  statement: {R : Type*} [CommRing R] [IsDedekindDomain R]
  proof: by
  rw [prime_iff_isPrime h] at hI
  exact (prime_iff_isPrime <| (I.map_eq_bot_iff_of_injective f.injective).not.2 h).2
    (map_isPrime_of_equiv _)

@[deprecated (since := "2026-04-16")] alias _root_.map_prime_of_equiv := map_prime_of_equiv

中文:
定理 map_prime_of_equiv
  结论: {R : 类型} [交换环 R] [是Dedekind整环 R]
  证明: by
  rw [prime_iff_isPrime h] at hI
  exact (prime_iff_isPrime <| (I.map_eq_bot_iff_of_injective f.injective).not.2 h).2
    (map_isPrime_of_equiv _)

@[deprecated (since := "2026-04-16")] alias _root_.map_prime_of_equiv := map_prime_of_equiv

Depends on / 依赖: I.map_eq_bot_iff_of_injective, f.injective, injective, map_eq_bot_iff_of_injective, map_isPrime_of_equiv, prime_iff_isPrime
-/
theorem map_prime_of_equiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    (f : T ≃+* R) {I : Ideal T} (hI : Prime I) (h : I != ⊥) : Prime (I.map f) := by
  rw [prime_iff_isPrime h] at hI
  exact (prime_iff_isPrime <| (I.map_eq_bot_iff_of_injective f.injective).not.2 h).2
    (map_isPrime_of_equiv _)

@[deprecated (since := "2026-04-16")] alias _root_.map_prime_of_equiv := map_prime_of_equiv

end Ideal

end IsDedekindDomain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `HeightOneSpectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/


namespace IsDedekindDomain

variable [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint unusedArguments]
/--
Definition of `HeightOneSpectrum` / `HeightOneSpectrum` 的定义

English:
structure HeightOneSpectrum
  parameters: where
  axioms and operations (3):
    - asIdeal : Ideal R
    - isPrime : asIdeal.IsPrime
    - ne_bot : asIdeal != ⊥

中文:
结构 高一谱
  参数: where
  公理与运算 (3 个):
    - asIdeal : 理想 R
    - isPrime : asIdeal.是素
    - ne_bot : asIdeal != ⊥
-/
structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal != ⊥

attribute [instance] HeightOneSpectrum.isPrime

variable (v : HeightOneSpectrum R) {R}

namespace HeightOneSpectrum

/--
Instance `isMaximal` / 实例 `isMaximal`

English:
instance isMaximal
  signature: : v.asIdeal.IsMaximal
  body: v.isPrime.isMaximal v.ne_bot

中文:
实例 isMaximal
  签名: : v.asIdeal.是极大
  定义体: v.isPrime.isMaximal v.ne_bot

Depends on / 依赖: isMaximal, isPrime, ne_bot, v.isPrime.isMaximal, v.ne_bot
-/
instance isMaximal : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot

/--
theorem `prime` / 定理 `prime`

English:
theorem prime
  statement: Prime v.asIdeal
  proof: Ideal.prime_of_isPrime v.ne_bot v.isPrime

中文:
定理 prime
  结论: 素 v.asIdeal
  证明: Ideal.prime_of_isPrime v.ne_bot v.isPrime

Depends on / 依赖: Ideal.prime_of_isPrime, isPrime, ne_bot, prime_of_isPrime, v.isPrime, v.ne_bot
-/
theorem prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (HeightOneSpectrum R) (Ideal R)
  body: P.asIdeal

omit [IsDedekindDomain R] in

中文:
实例 :
  签名: Coe (高一谱 R) (理想 R)
  定义体: P.asIdeal

omit [IsDedekindDomain R] in

Depends on / 依赖: P.asIdeal, asIdeal
-/
instance : Coe (HeightOneSpectrum R) (Ideal R) where
  coe P := P.asIdeal

omit [IsDedekindDomain R] in
/--
lemma `asIdeal_injective` / 引理 `asIdeal_injective`

English:
lemma asIdeal_injective
  statement: (HeightOneSpectrum.asIdeal (R := R)).Injective
  proof: fun ⦃_ _⦄ h => HeightOneSpectrum.ext h

alias asIdeal_inj := HeightOneSpectrum.ext

中文:
引理 asIdeal_injective
  结论: (高一谱.asIdeal (R := R)).单射
  证明: fun ⦃_ _⦄ h => HeightOneSpectrum.ext h

alias asIdeal_inj := HeightOneSpectrum.ext

Depends on / 依赖: Injective
-/
lemma asIdeal_injective : (HeightOneSpectrum.asIdeal (R := R)).Injective :=
  fun ⦃_ _⦄ h => HeightOneSpectrum.ext h

alias asIdeal_inj := HeightOneSpectrum.ext

/--
The (nonzero) prime elements of the monoid with zero `Ideal R` correspond
to an element of type `HeightOneSpectrum R`.

See `IsDedekindDomain.HeightOneSpectrum.prime` for the inverse direction. -/
@[simps]
/--
Definition of `ofPrime` / `ofPrime` 的定义

English:
definition ofPrime
  signature: {p : Ideal R} (hp : Prime p)
  body: ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

@[simp]

中文:
定义 ofPrime
  签名: {p : 理想 R} (hp : 素 p)
  定义体: ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

@[simp]

Depends on / 依赖: Ideal.isPrime_of_prime, hp.ne_zero, isPrime_of_prime, ne_zero
-/
def ofPrime {p : Ideal R} (hp : Prime p) : HeightOneSpectrum R :=
  ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

@[simp]
/--
theorem `ofPrime_prime` / 定理 `ofPrime_prime`

English:
theorem ofPrime_prime
  statement: ofPrime v.prime = v
  proof: rfl

中文:
定理 ofPrime_prime
  结论: ofPrime v.prime = v
  证明: rfl
-/
theorem ofPrime_prime : ofPrime v.prime = v := rfl

/--
theorem `irreducible` / 定理 `irreducible`

English:
theorem irreducible
  statement: Irreducible v.asIdeal
  proof: UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime

中文:
定理 irreducible
  结论: 不可约 v.asIdeal
  证明: UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mpr, irreducible_iff_prime, v.prime
-/
theorem irreducible : Irreducible v.asIdeal :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime

/--
theorem `associates_irreducible` / 定理 `associates_irreducible`

English:
theorem associates_irreducible
  statement: Irreducible Associates.mk v.asIdeal
  proof: Associates.irreducible_mk.mpr v.irreducible

中文:
定理 associates_irreducible
  结论: 不可约 Associates.mk v.asIdeal
  证明: Associates.irreducible_mk.mpr v.irreducible

Depends on / 依赖: Associates, Associates.irreducible_mk.mpr, irreducible, irreducible_mk, v.irreducible
-/
theorem associates_irreducible : Irreducible Associates.mk v.asIdeal :=
  Associates.irreducible_mk.mpr v.irreducible

/--
Definition of `equivMaximalSpectrum` / `equivMaximalSpectrum` 的定义

English:
definition equivMaximalSpectrum
  signature: (hR : ¬IsField R)
  body: ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.isMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.isMaximal hR⟩

中文:
定义 equivMaximalSpectrum
  签名: (hR : ¬是域 R)
  定义体: ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.isMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.isMaximal hR⟩

Depends on / 依赖: asIdeal, isMaximal, isPrime, ne_bot, v.asIdeal, v.isPrime.isMaximal, v.ne_bot
-/
def equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.isMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.isMaximal hR⟩

/--
theorem `ideal_ne_top_iff_exists` / 定理 `ideal_ne_top_iff_exists`

English:
theorem ideal_ne_top_iff_exists
  given: (hR : ¬IsField R) (I : Ideal R)
  proof: by
  rw [Ideal.ne_top_iff_exists_maximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(equivMaximalSpectrum hR).symm ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((equivMaximalSpectrum hR) P).asIdeal, ((equivMaximalSpectrum hR) P).isMaximal, hP⟩

中文:
定理 ideal_ne_top_iff_存在
  条件: (hR : ¬是域 R) (I : 理想 R)
  证明: by
  rw [Ideal.ne_top_iff_exists_maximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(equivMaximalSpectrum hR).symm ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((equivMaximalSpectrum hR) P).asIdeal, ((equivMaximalSpectrum hR) P).isMaximal, hP⟩

Depends on / 依赖: Ideal.ne_top_iff_exists_maximal, asIdeal, equivMaximalSpectrum, isMaximal, ne_top_iff_exists_maximal
-/
theorem ideal_ne_top_iff_exists (hR : ¬IsField R) (I : Ideal R) :
    I != ⊤ ↔ exists P : HeightOneSpectrum R, I <= P.asIdeal := by
  rw [Ideal.ne_top_iff_exists_maximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(equivMaximalSpectrum hR).symm ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((equivMaximalSpectrum hR) P).asIdeal, ((equivMaximalSpectrum hR) P).isMaximal, hP⟩

/--
theorem `isCoprime_of_ne` / 定理 `isCoprime_of_ne`

English:
theorem isCoprime_of_ne
  given: (P Q : HeightOneSpectrum R) (hPQ : P != Q)
  statement: IsCoprime P.asIdeal Q.asIdeal
  proof: Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
    (by simpa [HeightOneSpectrum.ext_iff] using hPQ))

中文:
定理 isCoprime_of_ne
  条件: (P Q : 高一谱 R) (hPQ : P != Q)
  结论: IsCoprime P.asIdeal Q.asIdeal
  证明: Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
    (by simpa [HeightOneSpectrum.ext_iff] using hPQ))

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.ext_iff, Ideal.IsMaximal.coprime_of_ne, Ideal.isCoprime_iff_sup_eq.mpr, IsMaximal, P.isMaximal, Q.isMaximal, coprime_of_ne, ext_iff, isCoprime_iff_sup_eq, isMaximal
-/
theorem isCoprime_of_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) : IsCoprime P.asIdeal Q.asIdeal :=
  Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
    (by simpa [HeightOneSpectrum.ext_iff] using hPQ))

/--
theorem `isCoprime_pow_of_ne` / 定理 `isCoprime_pow_of_ne`

English:
theorem isCoprime_pow_of_ne
  given: (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat)
  proof: Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top (P.isCoprime_of_ne Q hPQ).sup_eq)

中文:
定理 isCoprime_pow_of_ne
  条件: (P Q : 高一谱 R) (hPQ : P != Q) (n m : 自然数)
  证明: Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top (P.isCoprime_of_ne Q hPQ).sup_eq)

Depends on / 依赖: Ideal.isCoprime_iff_sup_eq.mpr, Ideal.pow_sup_pow_eq_top, P.isCoprime_of_ne, isCoprime_iff_sup_eq, isCoprime_of_ne, pow_sup_pow_eq_top, sup_eq
-/
theorem isCoprime_pow_of_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat) :
    IsCoprime (P.asIdeal ^ n) (Q.asIdeal ^ m) :=
  Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top (P.isCoprime_of_ne Q hPQ).sup_eq)

variable (R)

/--
theorem `iInf_localization_eq_bot` / 定理 `iInf_localization_eq_bot`

English:
theorem iInf_localization_eq_bot
  given: [Algebra R K] [hK : IsFractionRing R K]
  proof: by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exac

中文:
定理 iInf_localization_eq_bot
  条件: [代数 R K] [hK : IsFractionRing R K]
  证明: by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exac

Depends on / 依赖: Algebra, Algebra.mem_bot.mpr, Algebra.mem_iInf, Function, Function.bijective_iff_has_inverse.mp, IsField, IsField.localization_map_bijective, MaximalSpectrum, MaximalSpectrum.iInf_localization_eq_bot, algebra_map_inv, algebra_map_right_inv, all_goals, bijective_iff_has_inverse, equivMaximalSpectrum, iInf_localization_eq_bot, localization_map_bijective, mem_bot, mem_iInf, ne_zero, nonZeroDivisors
-/
theorem iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] :
    (⨅ v : HeightOneSpectrum R,
        Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exact fun _ => Algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩
  all_goals rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
  · exact fun hx ⟨v, hv⟩ => hx ((equivMaximalSpectrum hR).symm ⟨v, hv⟩)
  · exact fun hx ⟨v, hv, hbot⟩ => hx ⟨v, hv.isMaximal hbot⟩

section RingEquiv

variable {R} {S : Type*} [CommRing S]

/-- A surjective ring homomorphism `f : R →+* S` induces a map from `HeightOneSpectrum S` to
  `HeightOneSpectrum R` sending `v` to `v.asIdeal.comap f`. -/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : R ->+* S) (hf : Function.Surjective f) (v : HeightOneSpectrum S)
  body: v.asIdeal.comap f
  isPrime := v.asIdeal.comap_isPrime f
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' hf).mt v.ne_bot

中文:
定义 comap
  签名: (f : R ->+* S) (hf : 函数.满射 f) (v : 高一谱 S)
  定义体: v.asIdeal.comap f
  isPrime := v.asIdeal.comap_isPrime f
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' hf).mt v.ne_bot

Depends on / 依赖: asIdeal, v.asIdeal.comap
-/
def comap (f : R ->+* S) (hf : Function.Surjective f) (v : HeightOneSpectrum S) :
    (HeightOneSpectrum R) where
  asIdeal := v.asIdeal.comap f
  isPrime := v.asIdeal.comap_isPrime f
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' hf).mt v.ne_bot

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `HeightOneSpectrum`s of isomorphic rings. -/
@[simps]
/--
Definition of `equivOfRingEquiv` / `equivOfRingEquiv` 的定义

English:
definition equivOfRingEquiv
  signature: (e : R ≃+* S)
  body: HeightOneSpectrum.comap e.symm e.symm.surjective
  invFun := HeightOneSpectrum.comap e e.surjective
  left_inv x := by ext; simp
  right_inv x := by
    ext
    rw [← Ideal.map_comap_eq_self_of_equiv e x.asIdeal]
    simp only [comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, Ideal.symm_apply_mem_of

中文:
定义 equivOfRingEquiv
  签名: (e : R ≃+* S)
  定义体: HeightOneSpectrum.comap e.symm e.symm.surjective
  invFun := HeightOneSpectrum.comap e e.surjective
  left_inv x := by ext; simp
  right_inv x := by
    ext
    rw [← Ideal.map_comap_eq_self_of_equiv e x.asIdeal]
    simp only [comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, Ideal.symm_apply_mem_of

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.comap, e.symm, e.symm.surjective, surjective
-/
def equivOfRingEquiv (e : R ≃+* S) : (HeightOneSpectrum R) ≃ (HeightOneSpectrum S) where
  toFun := HeightOneSpectrum.comap e.symm e.symm.surjective
  invFun := HeightOneSpectrum.comap e e.surjective
  left_inv x := by ext; simp
  right_inv x := by
    ext
    rw [← Ideal.map_comap_eq_self_of_equiv e x.asIdeal]
    simp only [comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, Ideal.symm_apply_mem_of_equiv_iff]
    exact Iff.rfl

/--
theorem `RingEquiv.nontrivial_heightOneSpectrum` / 定理 `RingEquiv.nontrivial_heightOneSpectrum`

English:
theorem RingEquiv.nontrivial_heightOneSpectrum
  statement: {R S : Type*} [CommRing R] [CommRing S]
  proof: (equivOfRingEquiv e).surjective.nontrivial

中文:
定理 环等价.nontrivial_heightOneSpectrum
  结论: {R S : 类型} [交换环 R] [交换环 S]
  证明: (equivOfRingEquiv e).surjective.nontrivial

Depends on / 依赖: equivOfRingEquiv, nontrivial, surjective, surjective.nontrivial
-/
theorem RingEquiv.nontrivial_heightOneSpectrum {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial (HeightOneSpectrum S)] (e : R ≃+* S) : Nontrivial (HeightOneSpectrum R) :=
  (equivOfRingEquiv e).surjective.nontrivial

end RingEquiv

end HeightOneSpectrum

end IsDedekindDomain

section

open Ideal

variable {R A}
variable [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

namespace IsDedekindDomain

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
/--
Definition of `idealFactorsFunOfQuotHom` / `idealFactorsFunOfQuotHom` 的定义

English:
definition idealFactorsFunOfQuotHom
  signature: {f : R ⧸ I ->+* A ⧸ J} (hf : Function.Surjective f)
  body: ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) <=
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monoto

中文:
定义 idealFactorsFunOfQuotHom
  签名: {f : R ⧸ I ->+* A ⧸ J} (hf : 函数.满射 f)
  定义体: ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) <=
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monoto

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.ker, Subtype, Subtype.coe_le_coe, Subtype.coe_mk, coe_le_coe, coe_mk, comap_le_comap_iff_of_surjective, dvd_iff_le, dvd_iff_le.mpr, ker_le_comap, mk_ker, mk_surjective, monotone
-/
def idealFactorsFunOfQuotHom {f : R ⧸ I ->+* A ⧸ J} (hf : Function.Surjective f) :
    {p : Ideal R // p ∣ I} ->o {p : Ideal A // p ∣ J} where
  toFun X := ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) <=
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe]; rw [Subtype.coe_mk]; rw [Subtype.coe_mk] at h ⊢
    rw [Subtype.coe_mk]; rw [comap_le_comap_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective]; rw [map_le_iff_le_comap]; rw [Subtype.coe_mk]; rw [comap_map_of_surjective _ hf (map (Ideal.Quotient.mk I) Y)]
    suffices map (Ideal.Quotient.mk I) X <= map (Ideal.Quotient.mk I) Y by
      exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
sup_eq_left.mpr le_of_dvd hY]

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom := idealFactorsFunOfQuotHom

@[simp]
/--
theorem `idealFactorsFunOfQuotHom_id` / 定理 `idealFactorsFunOfQuotHom_id`

English:
theorem idealFactorsFunOfQuotHom_id
  proof: OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.

中文:
定理 idealFactorsFunOfQuotHom_id
  证明: OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, OrderHom, OrderHom.coe_mk, OrderHom.ext, OrderHom.id_coe, Quotient, RingHom, RingHom.ker_eq_comap_bot, Subtype, Subtype.coe_eta, X.prop, coe_eta, coe_mk, comap_map_of_surjective, dvd_iff_le, dvd_iff_le.mp, id_coe, idealFactorsFunOfQuotHom, ker_eq_comap_bot
-/
theorem idealFactorsFunOfQuotHom_id :
    idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.mpr (dvd_iff_le.mp X.prop), Subtype.coe_eta])

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom_id := idealFactorsFunOfQuotHom_id

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Ideal B}

/--
theorem `idealFactorsFunOfQuotHom_comp` / 定理 `idealFactorsFunOfQuotHom_comp`

English:
theorem idealFactorsFunOfQuotHom_comp
  statement: {f : R ⧸ I ->+* A ⧸ J} {g : A ⧸ J ->+* B ⧸ L}
  proof: by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.comp_coe]; rw [OrderHom.coe_mk]; rw [OrderHom.coe_mk]; rw [Function.comp_apply]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.coe_mk]; rw [Subtype.mk_eq_mk]; rw [Subtype.coe_

中文:
定理 idealFactorsFunOfQuotHom_comp
  结论: {f : R ⧸ I ->+* A ⧸ J} {g : A ⧸ J ->+* B ⧸ L}
  证明: by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.comp_coe]; rw [OrderHom.coe_mk]; rw [OrderHom.coe_mk]; rw [Function.comp_apply]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.coe_mk]; rw [Subtype.mk_eq_mk]; rw [Subtype.coe_

Depends on / 依赖: Function, Function.comp_apply, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, OrderHom, OrderHom.coe_mk, OrderHom.comp_coe, OrderHom.ext, Quotient, Subtype, Subtype.coe_mk, Subtype.mk_eq_mk, coe_mk, comp_apply, comp_coe, idealFactorsFunOfQuotHom, map_comap_of_surjective, map_map, mk_eq_mk, mk_surjective
-/
theorem idealFactorsFunOfQuotHom_comp {f : R ⧸ I ->+* A ⧸ J} {g : A ⧸ J ->+* B ⧸ L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) := by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.comp_coe]; rw [OrderHom.coe_mk]; rw [OrderHom.coe_mk]; rw [Function.comp_apply]; rw [idealFactorsFunOfQuotHom]; rw [OrderHom.coe_mk]; rw [Subtype.mk_eq_mk]; rw [Subtype.coe_mk]; rw [map_comap_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective]; rw [map_map]

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom_comp := idealFactorsFunOfQuotHom_comp

variable [IsDedekindDomain R] (f : R ⧸ I ≃+* A ⧸ J)

/--
Definition of `idealFactorsEquivOfQuotEquiv` / `idealFactorsEquivOfQuotEquiv` 的定义

English:
definition idealFactorsEquivOfQuotEquiv
  signature: : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J }
  body: by
  have f_surj : Function.Surjective (f : R ⧸ I ->+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J ->+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · simpa using! idealFact

中文:
定义 idealFactorsEquivOfQuotEquiv
  签名: : { p : 理想 R | p ∣ I } ≃o { p : 理想 A | p ∣ J }
  定义体: by
  have f_surj : Function.Surjective (f : R ⧸ I ->+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J ->+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · simpa using! idealFact

Depends on / 依赖: Function, Function.Surjective, OrderIso, OrderIso.ofHomInv, Surjective, f.surjective, f.symm, f.symm.surjective, f_surj, fsym_surj, idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom_comp, ofHomInv, surjective
-/
def idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } := by
  have f_surj : Function.Surjective (f : R ⧸ I ->+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J ->+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · simpa using! idealFactorsFunOfQuotHom_comp fsym_surj f_surj
  · simpa using! idealFactorsFunOfQuotHom_comp f_surj fsym_surj

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv := idealFactorsEquivOfQuotEquiv

/--
theorem `idealFactorsEquivOfQuotEquiv_symm` / 定理 `idealFactorsEquivOfQuotEquiv_symm`

English:
theorem idealFactorsEquivOfQuotEquiv_symm
  proof: rfl

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_symm := idealFactorsEquivOfQuotEquiv_symm

中文:
定理 idealFactorsEquivOfQuotEquiv_symm
  证明: rfl

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_symm := idealFactorsEquivOfQuotEquiv_symm
-/
theorem idealFactorsEquivOfQuotEquiv_symm :
    (idealFactorsEquivOfQuotEquiv f).symm = idealFactorsEquivOfQuotEquiv f.symm := rfl

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_symm := idealFactorsEquivOfQuotEquiv_symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `idealFactorsEquivOfQuotEquiv_is_dvd_iso` / 定理 `idealFactorsEquivOfQuotEquiv_is_dvd_iso`

English:
theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso
  given: {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I)
  proof: by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ <= idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) <= ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le

@[deprecated (s

中文:
定理 idealFactorsEquivOfQuotEquiv_is_dvd_iso
  条件: {L M : 理想 R} (hL : L ∣ I) (hM : M ∣ I)
  证明: by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ <= idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) <= ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le

@[deprecated (s

Depends on / 依赖: Subtype, Subtype.coe_le_coe, Subtype.mk_le_mk, coe_le_coe, dvd_iff_le, idealFactorsEquivOfQuotEquiv, le_iff_le, mk_le_mk
-/
theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) :
    (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ↔
      L ∣ M := by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ <= idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) <= ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_is_dvd_iso := idealFactorsEquivOfQuotEquiv_is_dvd_iso

open UniqueFactorizationMonoid

/--
theorem `idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors` / 定理 `idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors`

English:
theorem idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors
  statement: (hJ : J != ⊥)
  proof: by
  have hI : I != ⊥ := by
    intro hI
    rw [hI]; rw [bot_eq_zero]; rw [normalizedFactors_zero]; rw [← Multiset.empty_eq_zero] at hL
    exact Finset.notMem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEqu

中文:
定理 idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors
  结论: (hJ : J != ⊥)
  证明: by
  have hI : I != ⊥ := by
    intro hI
    rw [hI]; rw [bot_eq_zero]; rw [normalizedFactors_zero]; rw [← Multiset.empty_eq_zero] at hL
    exact Finset.notMem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEqu

Depends on / 依赖: Finset, Finset.notMem_empty, Multiset, Multiset.empty_eq_zero, Subtype, Subtype.coe_mk, bot_eq_zero, coe_mk, empty_eq_zero, idealFactorsEquivOfQuotEquiv, idealFactorsEquivOfQuotEquiv_is_dvd_iso, mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors, normalizedFactors_zero, notMem_empty, toEquiv
-/
theorem idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors (hJ : J != ⊥)
    {L : Ideal R} (hL : L in normalizedFactors I) :
    ↑(idealFactorsEquivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩)
      in normalizedFactors J := by
  have hI : I != ⊥ := by
    intro hI
    rw [hI]; rw [bot_eq_zero]; rw [normalizedFactors_zero]; rw [← Multiset.empty_eq_zero] at hL
    exact Finset.notMem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  rintro ⟨l, hl⟩ ⟨l', hl'⟩
  rw [Subtype.coe_mk]; rw [Subtype.coe_mk]
  apply idealFactorsEquivOfQuotEquiv_is_dvd_iso f

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors :=
  idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `normalizedFactorsEquivOfQuotEquiv` / `normalizedFactorsEquivOfQuotEquiv` 的定义

English:
definition normalizedFactorsEquivOfQuotEquiv
  signature: (hI : I != ⊥) (hJ : J != ⊥)
  body: ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquiv

中文:
定义 normalizedFactorsEquivOfQuotEquiv
  签名: (hI : I != ⊥) (hJ : J != ⊥)
  定义体: ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquiv

Depends on / 依赖: dvd_of_mem_normalizedFactors, f.symm, idealFactorsEquivOfQuotEquiv, idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors, idealFactorsEquivOfQuotEquiv_symm, invFun, j.prop, left_inv, right_inv
-/
def normalizedFactorsEquivOfQuotEquiv (hI : I != ⊥) (hJ : J != ⊥) :
    { L : Ideal R | L in normalizedFactors I } ≃ { M : Ideal A | M in normalizedFactors J } where
  toFun j :=
    ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquivOfQuotEquiv_symm]
      exact
        idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f.symm hI
          j.prop⟩
  left_inv := fun ⟨j, hj⟩ => by simp
  right_inv := fun ⟨j, hj⟩ => by simp

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv := normalizedFactorsEquivOfQuotEquiv

@[simp]
/--
theorem `normalizedFactorsEquivOfQuotEquiv_symm` / 定理 `normalizedFactorsEquivOfQuotEquiv_symm`

English:
theorem normalizedFactorsEquivOfQuotEquiv_symm
  given: (hI : I != ⊥) (hJ : J != ⊥)
  proof: rfl

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_symm := normalizedFactorsEquivOfQuotEquiv_symm

中文:
定理 normalizedFactorsEquivOfQuotEquiv_symm
  条件: (hI : I != ⊥) (hJ : J != ⊥)
  证明: rfl

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_symm := normalizedFactorsEquivOfQuotEquiv_symm
-/
theorem normalizedFactorsEquivOfQuotEquiv_symm (hI : I != ⊥) (hJ : J != ⊥) :
    (normalizedFactorsEquivOfQuotEquiv f hI hJ).symm =
      normalizedFactorsEquivOfQuotEquiv f.symm hJ hI := rfl

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_symm := normalizedFactorsEquivOfQuotEquiv_symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity` / 定理 `normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity`

English:
theorem normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity
  statement: (hI : I != ⊥) (hJ : J != ⊥)
  proof: by
  rw [normalizedFactorsEquivOfQuotEquiv]; rw [Equiv.coe_fn_mk]; rw [Subtype.coe_mk]
  refine emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_

中文:
定理 normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity
  结论: (hI : I != ⊥) (hJ : J != ⊥)
  证明: by
  rw [normalizedFactorsEquivOfQuotEquiv]; rw [Equiv.coe_fn_mk]; rw [Subtype.coe_mk]
  refine emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_

Depends on / 依赖: Equiv.coe_fn_mk, Subtype, Subtype.coe_mk, coe_fn_mk, coe_mk, emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors, idealFactorsEquivOfQuotEquiv, idealFactorsEquivOfQuotEquiv_is_dvd_iso, normalizedFactorsEquivOfQuotEquiv, toEquiv
-/
theorem normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity (hI : I != ⊥) (hJ : J != ⊥)
    (L : Ideal R) (hL : L in normalizedFactors I) :
    emultiplicity (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = emultiplicity L I := by
  rw [normalizedFactorsEquivOfQuotEquiv]; rw [Equiv.coe_fn_mk]; rw [Subtype.coe_mk]
  refine emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_iso f hl hl'

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity :=
  normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity

end IsDedekindDomain

end

noncomputable section ChineseRemainder

open Ideal UniqueFactorizationMonoid

variable {R ι}

/--
theorem `Ring.DimensionLeOne.prime_le_prime_iff_eq` / 定理 `Ring.DimensionLeOne.prime_le_prime_iff_eq`

English:
theorem Ring.DimensionLeOne.prime_le_prime_iff_eq
  statement: [Ring.DimensionLEOne R] {P Q : Ideal R}
  proof: ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩

中文:
定理 环.DimensionLeOne.prime_le_prime_iff_eq
  结论: [环.维数不超过一 R] {P Q : 理想 R}
  证明: ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩

Depends on / 依赖: Eq.le, eq_of_le, hP.isMaximal, hQ.ne_top, isMaximal, ne_top
-/
theorem Ring.DimensionLeOne.prime_le_prime_iff_eq [Ring.DimensionLEOne R] {P Q : Ideal R}
    [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P != ⊥) : P <= Q ↔ P = Q :=
  ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩

section DedekindDomain

variable [IsDedekindDomain R]

namespace Ideal

/--
theorem `IsPrime.mul_mem_pow` / 定理 `IsPrime.mul_mem_pow`

English:
theorem IsPrime.mul_mem_pow
  statement: (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : Nat}
  proof: by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  have : I.IsMaximal := hI.isMaximal hI0
  exact IsMaximal.mul_mem_pow I h

中文:
定理 是素.mul_mem_pow
  结论: (I : 理想 R) [hI : I.是素] {a b : R} {n : 自然数}
  证明: by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  have : I.IsMaximal := hI.isMaximal hI0
  exact IsMaximal.mul_mem_pow I h

Depends on / 依赖: I.IsMaximal, IsMaximal, IsMaximal.mul_mem_pow, hI.isMaximal, isMaximal, mul_mem_pow, pow_succ
-/
theorem IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : Nat}
    (h : a * b in I ^ n) : a in I ∨ b in I ^ n := by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  have : I.IsMaximal := hI.isMaximal hI0
  exact IsMaximal.mul_mem_pow I h

/--
theorem `IsPrime.mem_pow_mul` / 定理 `IsPrime.mem_pow_mul`

English:
theorem IsPrime.mem_pow_mul
  statement: (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : Nat}
  proof: by
  rw [mul_comm] at h
  rw [or_comm]
  exact IsPrime.mul_mem_pow _ h

中文:
定理 是素.mem_pow_mul
  结论: (I : 理想 R) [hI : I.是素] {a b : R} {n : 自然数}
  证明: by
  rw [mul_comm] at h
  rw [or_comm]
  exact IsPrime.mul_mem_pow _ h

Depends on / 依赖: IsPrime, IsPrime.mul_mem_pow, mul_comm, mul_mem_pow, or_comm
-/
theorem IsPrime.mem_pow_mul (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : Nat}
    (h : a * b in I ^ n) : a in I ^ n ∨ b in I := by
  rw [mul_comm] at h
  rw [or_comm]
  exact IsPrime.mul_mem_pow _ h

section

/--
theorem `count_normalizedFactors_eq` / 定理 `count_normalizedFactors_eq`

English:
theorem count_normalizedFactors_eq
  statement: {p x : Ideal R} [hp : p.IsPrime] {n : Nat} (hle : x <= p ^ n)
  proof: count_normalizedFactors_eq' ((isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (dvd_iff_le.mpr hle) (mt le_of_dvd hlt)

中文:
定理 count_normalizedFactors_eq
  结论: {p x : 理想 R} [hp : p.是素] {n : 自然数} (hle : x <= p ^ n)
  证明: count_normalizedFactors_eq' ((isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (dvd_iff_le.mpr hle) (mt le_of_dvd hlt)

Depends on / 依赖: Prime.irreducible, count_normalizedFactors_eq, dvd_iff_le, dvd_iff_le.mpr, imp_right, irreducible, isPrime_iff_bot_or_prime, isPrime_iff_bot_or_prime.mp, le_of_dvd, normalize_eq
-/
theorem count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : Nat} (hle : x <= p ^ n)
    (hlt : ¬x <= p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalizedFactors_eq' ((isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (dvd_iff_le.mpr hle) (mt le_of_dvd hlt)

/--
theorem `count_associates_factors_eq` / 定理 `count_associates_factors_eq`

English:
theorem count_associates_factors_eq
  proof: by
  replace hI : Associates.mk I != 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (prime_of_isPrime hJ₀ hJ).irreducible
  apply (count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← dvd_iff

中文:
定理 count_associates_factors_eq
  证明: by
  replace hI : Associates.mk I != 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (prime_of_isPrime hJ₀ hJ).irreducible
  apply (count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← dvd_iff

Depends on / 依赖: Associates, Associates.dvd_eq_le, Associates.irreducible_mk, Associates.mk, Associates.mk_dvd_mk, Associates.mk_ne_zero.mpr, Associates.mk_pow, Associates.prime_pow_dvd_iff_le, Irreducible, all_goals, count_normalizedFactors_eq, dvd_eq_le, dvd_iff_le, irreducible, irreducible_mk, mk_dvd_mk, mk_ne_zero, mk_pow, prime_of_isPrime, prime_pow_dvd_iff_le
-/
theorem count_associates_factors_eq
    {I J : Ideal R} (hI : I != 0) (hJ : J.IsPrime) (hJ₀ : J != ⊥) :
    (Associates.mk J).count (Associates.mk I).factors = Multiset.count J (normalizedFactors I) := by
  replace hI : Associates.mk I != 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (prime_of_isPrime hJ₀ hJ).irreducible
  apply (count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← dvd_iff_le]; rw [← Associates.mk_dvd_mk]; rw [Associates.mk_pow]
    simp only [Associates.dvd_eq_le]
    rw [Associates.prime_pow_dvd_iff_le hI hJ']
  lia

@[deprecated (since := "2026-04-16")]
alias _root_.count_associates_factors_eq := count_associates_factors_eq

/--
theorem `count_associates_eq` / 定理 `count_associates_eq`

English:
theorem count_associates_eq
  proof: by
  have hx0 : x != 0 := Prime.ne_zero hx
  rw [count_associates_factors_eq]; rw [UniqueFactorizationMonoid.count_normalizedFactors_eq]
  · exact (prime_span_singleton_iff.mpr hx).irreducible
  · exact normalize_eq _
  · simp only [span_singleton_pow, heq, dvd_span_singleton]
    exact mul_mem_righ

中文:
定理 count_associates_eq
  证明: by
  have hx0 : x != 0 := Prime.ne_zero hx
  rw [count_associates_factors_eq]; rw [UniqueFactorizationMonoid.count_normalizedFactors_eq]
  · exact (prime_span_singleton_iff.mpr hx).irreducible
  · exact normalize_eq _
  · simp only [span_singleton_pow, heq, dvd_span_singleton]
    exact mul_mem_righ

Depends on / 依赖: Prime.ne_zero, UniqueFactorizationMonoid, UniqueFactorizationMonoid.count_normalizedFactors_eq, count_associates_factors_eq, count_normalizedFactors_eq, dvd_span_singleton, irreducible, mem_span_singleton, mem_span_singleton_self, mul_dvd_mul_iff_left, mul_mem_right, ne_zero, normalize_eq, pow_add, pow_ne_zero, pow_one, prime_span_singleton_iff, prime_span_singleton_iff.mpr, span_singleton_pow
-/
theorem count_associates_eq
    {a a₀ x : R} {n : Nat} (hx : Prime x) (ha : ¬x ∣ a) (heq : a₀ = x ^ n * a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a₀})).factors = n := by
  have hx0 : x != 0 := Prime.ne_zero hx
  rw [count_associates_factors_eq]; rw [UniqueFactorizationMonoid.count_normalizedFactors_eq]
  · exact (prime_span_singleton_iff.mpr hx).irreducible
  · exact normalize_eq _
  · simp only [span_singleton_pow, heq, dvd_span_singleton]
    exact mul_mem_right _ _ (mem_span_singleton_self (x ^ n))
  · simp only [span_singleton_pow, heq, dvd_span_singleton, mem_span_singleton]
    rw [pow_add]; rw [pow_one]; rw [mul_dvd_mul_iff_left (pow_ne_zero n hx0)]
    exact ha
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot]
    aesop
  · exact (span_singleton_prime hx0).mpr hx
  · simp only [ne_eq, span_singleton_eq_bot]; exact hx0

/--
theorem `count_associates_eq'` / 定理 `count_associates_eq'`

English:
theorem count_associates_eq'
  proof: by
  obtain ⟨q, hq⟩ := hle
  apply count_associates_eq hx _ hq
  contrapose hlt with hdvd
  obtain ⟨q', hq'⟩ := hdvd
  use q'
  rw [hq]; rw [hq']
  ring

中文:
定理 count_associates_eq'
  证明: by
  obtain ⟨q, hq⟩ := hle
  apply count_associates_eq hx _ hq
  contrapose hlt with hdvd
  obtain ⟨q', hq'⟩ := hdvd
  use q'
  rw [hq]; rw [hq']
  ring

Depends on / 依赖: contrapose, count_associates_eq
-/
theorem count_associates_eq'
    {a x : R} (hx : Prime x) {n : Nat} (hle : x ^ n ∣ a) (hlt : ¬x ^ (n + 1) ∣ a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a})).factors = n := by
  obtain ⟨q, hq⟩ := hle
  apply count_associates_eq hx _ hq
  contrapose hlt with hdvd
  obtain ⟨q', hq'⟩ := hdvd
  use q'
  rw [hq]; rw [hq']
  ring

end

/--
theorem `le_mul_of_no_prime_factors` / 定理 `le_mul_of_no_prime_factors`

English:
theorem le_mul_of_no_prime_factors
  statement: {I J K : Ideal R}
  proof: by
  simp only [← dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt i

中文:
定理 le_mul_of_no_prime_factors
  结论: {I J K : 理想 R}
  证明: by
  simp only [← dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt i

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors, coprime, dvd_iff_le, dvd_of_dvd_mul_right_of_no_prime_factors, isPrime_of_prime, mul_comm, mul_dvd_mul_left, zero_mul
-/
theorem le_mul_of_no_prime_factors {I J K : Ideal R}
    (coprime : forall P, J <= P -> K <= P -> ¬IsPrime P) (hJ : I <= J) (hK : I <= K) : I <= J * K := by
  simp only [← dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt isPrime_of_prime (coprime _ hPJ hPK)

end Ideal

namespace IsDedekindDomain

/--
theorem `HeightOneSpectrum.inf_pow_eq_prod` / 定理 `HeightOneSpectrum.inf_pow_eq_prod`

English:
theorem HeightOneSpectrum.inf_pow_eq_prod
  statement: (s : Finset ι) (e : ι -> Nat)
  proof: by
  rw [prod_eq_iInf_of_pairwise_isCoprime]
  · rw [Finset.inf_eq_iInf s fun i => (f i).asIdeal ^ e i]
  · intro i hi j hj hij
    exact HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime i hi j hj hij) _ _

中文:
定理 高一谱.inf_pow_eq_prod
  结论: (s : 有限集 ι) (e : ι -> 自然数)
  证明: by
  rw [prod_eq_iInf_of_pairwise_isCoprime]
  · rw [Finset.inf_eq_iInf s fun i => (f i).asIdeal ^ e i]
  · intro i hi j hj hij
    exact HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime i hi j hj hij) _ _

Depends on / 依赖: Finset, Finset.inf_eq_iInf, HeightOneSpectrum, HeightOneSpectrum.isCoprime_pow_of_ne, asIdeal, coprime, inf_eq_iInf, isCoprime_pow_of_ne, prod_eq_iInf_of_pairwise_isCoprime
-/
theorem HeightOneSpectrum.inf_pow_eq_prod (s : Finset ι) (e : ι -> Nat)
    (f : ι -> HeightOneSpectrum R) (coprime : forallᵉ (i in s) (j in s), i != j -> f i != f j) :
    (s.inf fun i => (f i).asIdeal ^ e i) = ∏ i in s, (f i).asIdeal ^ e i := by
  rw [prod_eq_iInf_of_pairwise_isCoprime]
  · rw [Finset.inf_eq_iInf s fun i => (f i).asIdeal ^ e i]
  · intro i hi j hj hij
    exact HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime i hi j hj hij) _ _

/--
theorem `inf_pow_eq_prod_of_prime` / 定理 `inf_pow_eq_prod_of_prime`

English:
theorem inf_pow_eq_prod_of_prime
  statement: (s : Finset ι) (f : ι -> Ideal R)
  proof: by
  rw [prod_eq_iInf_of_pairwise_isCoprime]; rw [Finset.inf_eq_iInf s fun i => (f i) ^ e i]
  intro i hi j hj hij
  exact Ideal.isCoprime_iff_sup_eq.mpr (pow_sup_pow_eq_top (IsMaximal.coprime_of_ne
    (IsPrime.isMaximal (isPrime_of_prime (prime i hi)) (prime i hi).ne_zero)
    (IsPrime.isMaximal (

中文:
定理 inf_pow_eq_prod_of_prime
  结论: (s : 有限集 ι) (f : ι -> 理想 R)
  证明: by
  rw [prod_eq_iInf_of_pairwise_isCoprime]; rw [Finset.inf_eq_iInf s fun i => (f i) ^ e i]
  intro i hi j hj hij
  exact Ideal.isCoprime_iff_sup_eq.mpr (pow_sup_pow_eq_top (IsMaximal.coprime_of_ne
    (IsPrime.isMaximal (isPrime_of_prime (prime i hi)) (prime i hi).ne_zero)
    (IsPrime.isMaximal (

Depends on / 依赖: Finset, Finset.inf_eq_iInf, Ideal.isCoprime_iff_sup_eq.mpr, IsMaximal, IsMaximal.coprime_of_ne, IsPrime, IsPrime.isMaximal, coprime, coprime_of_ne, inf_eq_iInf, isCoprime_iff_sup_eq, isMaximal, isPrime_of_prime, ne_zero, pow_sup_pow_eq_top, prod_eq_iInf_of_pairwise_isCoprime
-/
theorem inf_pow_eq_prod_of_prime (s : Finset ι) (f : ι -> Ideal R)
    (e : ι -> Nat) (prime : forall i in s, Prime (f i)) (coprime : forallᵉ (i in s) (j in s), i != j -> f i != f j) :
    (s.inf fun i => f i ^ e i) = ∏ i in s, f i ^ e i := by
  rw [prod_eq_iInf_of_pairwise_isCoprime]; rw [Finset.inf_eq_iInf s fun i => (f i) ^ e i]
  intro i hi j hj hij
  exact Ideal.isCoprime_iff_sup_eq.mpr (pow_sup_pow_eq_top (IsMaximal.coprime_of_ne
    (IsPrime.isMaximal (isPrime_of_prime (prime i hi)) (prime i hi).ne_zero)
    (IsPrime.isMaximal (isPrime_of_prime (prime j hj)) (prime j hj).ne_zero)
    (coprime i hi j hj hij)))

@[deprecated (since := "2026-03-10")] alias inf_prime_pow_eq_prod :=
  inf_pow_eq_prod_of_prime

/--
Definition of `HeightOneSpectrum.quotientEquivPiOfProdEq` / `HeightOneSpectrum.quotientEquivPiOfProdEq` 的定义

English:
definition HeightOneSpectrum.quotientEquivPiOfProdEq
  signature: [Fintype ι] (I : Ideal R)
  body: (Ideal.quotEquivOfEq
    (by simp [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ,
      ← HeightOneSpectrum.inf_pow_eq_prod _ _ _ (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime hij) _ _

中文:
定义 高一谱.quotientEquivPiOfProdEq
  签名: [有限类型 ι] (I : 理想 R)
  定义体: (Ideal.quotEquivOfEq
    (by simp [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ,
      ← HeightOneSpectrum.inf_pow_eq_prod _ _ _ (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime hij) _ _

Depends on / 依赖: Finset, Finset.inf_eq_iInf, Finset.mem_univ, HeightOneSpectrum, HeightOneSpectrum.inf_pow_eq_prod, HeightOneSpectrum.isCoprime_pow_of_ne, Ideal.quotEquivOfEq, Ideal.quotientInfRingEquivPiQuotient, coprime, coprime.set_pairwise, inf_eq_iInf, inf_pow_eq_prod, isCoprime_pow_of_ne, mem_univ, prod_eq, quotEquivOfEq, quotientInfRingEquivPiQuotient, set_pairwise
-/
def HeightOneSpectrum.quotientEquivPiOfProdEq [Fintype ι] (I : Ideal R)
    (P : ι -> HeightOneSpectrum R) (e : ι -> Nat) (coprime : Pairwise fun i j => P i != P j)
    (prod_eq : ∏ i, (P i).asIdeal ^ e i = I) : R ⧸ I ≃+* forall i, R ⧸ (P i).asIdeal ^ e i :=
  (Ideal.quotEquivOfEq
    (by simp [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ,
      ← HeightOneSpectrum.inf_pow_eq_prod _ _ _ (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime hij) _ _

/--
Definition of `quotientEquivPiOfProdEq` / `quotientEquivPiOfProdEq` 的定义

English:
definition quotientEquivPiOfProdEq
  signature: {ι : Type*} [Fintype ι] (I : Ideal R) (P : ι -> Ideal R)
  body: HeightOneSpectrum.quotientEquivPiOfProdEq I
    (fun i => ⟨P i, (isPrime_of_prime (prime i)), (prime i).ne_zero⟩) e (by grind) prod_eq

中文:
定义 quotientEquivPiOfProdEq
  签名: {ι : 类型} [有限类型 ι] (I : 理想 R) (P : ι -> 理想 R)
  定义体: HeightOneSpectrum.quotientEquivPiOfProdEq I
    (fun i => ⟨P i, (isPrime_of_prime (prime i)), (prime i).ne_zero⟩) e (by grind) prod_eq

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.quotientEquivPiOfProdEq, isPrime_of_prime, ne_zero, prod_eq, quotientEquivPiOfProdEq
-/
def quotientEquivPiOfProdEq {ι : Type*} [Fintype ι] (I : Ideal R) (P : ι -> Ideal R)
    (e : ι -> Nat) (prime : forall i, Prime (P i)) (coprime : Pairwise fun i j => P i != P j)
    (prod_eq : ∏ i, P i ^ e i = I) : R ⧸ I ≃+* forall i, R ⧸ P i ^ e i :=
  HeightOneSpectrum.quotientEquivPiOfProdEq I
    (fun i => ⟨P i, (isPrime_of_prime (prime i)), (prime i).ne_zero⟩) e (by grind) prod_eq

/--
Definition of `quotientEquivPiFactors` / `quotientEquivPiFactors` 的定义

English:
definition quotientEquivPiFactors
  signature: {I : Ideal R} (hI : I != ⊥)
  body: quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun _ _ hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P in (factors I).toFin

中文:
定义 quotientEquivPiFactors
  签名: {I : 理想 R} (hI : I != ⊥)
  定义体: quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun _ _ hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P in (factors I).toFin

Depends on / 依赖: Finset, Finset.prod_multiset_map_count, Multiset, Multiset.mem_toFinset.mp, P.prop, Subtype, Subtype.coe_injective.ne, coe_injective, factors, mem_toFinset, prime_of_factor, prod_coe_sort, prod_multiset_map_count, quotientEquivPiOfProdEq, toFinset, toFinset.prod_coe_sort
-/
def quotientEquivPiFactors {I : Ideal R} (hI : I != ⊥) :
    R ⧸ I ≃+* forall P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (Multiset.count ↑P (factors I)) :=
  quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun _ _ hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P in (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI))

@[simp]
/--
theorem `quotientEquivPiFactors_mk` / 定理 `quotientEquivPiFactors_mk`

English:
theorem quotientEquivPiFactors_mk
  given: {I : Ideal R} (hI : I != ⊥) (x : R)
  proof: rfl

中文:
定理 quotientEquivPiFactors_mk
  条件: {I : 理想 R} (hI : I != ⊥) (x : R)
  证明: rfl
-/
theorem quotientEquivPiFactors_mk {I : Ideal R} (hI : I != ⊥) (x : R) :
    quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun _P =>
      Ideal.Quotient.mk _ x := rfl

/--
Definition of `quotientEquivPiOfFinsetProdEq` / `quotientEquivPiOfFinsetProdEq` 的定义

English:
definition quotientEquivPiOfFinsetProdEq
  signature: {ι : Type*} {s : Finset ι}
  body: quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)

中文:
定义 quotientEquivPiOfFinsetProdEq
  签名: {ι : 类型} {s : 有限集 ι}
  定义体: quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)

Depends on / 依赖: Finset, Finset.prod_coe_sort, Subtype, Subtype.coe_injective.ne, _root_, _root_.trans, coe_injective, coprime, prod_coe_sort, prod_eq, quotientEquivPiOfProdEq
-/
def quotientEquivPiOfFinsetProdEq {ι : Type*} {s : Finset ι}
    (I : Ideal R) (P : ι -> Ideal R) (e : ι -> Nat) (prime : forall i in s, Prime (P i))
    (coprime : forallᵉ (i in s) (j in s), i != j -> P i != P j)
    (prod_eq : ∏ i in s, P i ^ e i = I) : R ⧸ I ≃+* forall i : s, R ⧸ P i ^ e i :=
  quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)

/--
theorem `exists_representative_mod_finset` / 定理 `exists_representative_mod_finset`

English:
theorem exists_representative_mod_finset
  statement: {ι : Type*} {s : Finset ι}
  proof: by
  let f := quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩

中文:
定理 存在_representative_mod_finset
  结论: {ι : 类型} {s : 有限集 ι}
  证明: by
  let f := quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, coprime, f.surjective, mk_surjective, quotientEquivPiOfFinsetProdEq, surjective
-/
theorem exists_representative_mod_finset {ι : Type*} {s : Finset ι}
    (P : ι -> Ideal R) (e : ι -> Nat) (prime : forall i in s, Prime (P i))
    (coprime : forallᵉ (i in s) (j in s), i != j -> P i != P j) (x : forall i : s, R ⧸ P i ^ e i) :
    exists y, forall (i) (hi : i in s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ := by
  let f := quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩

/--
theorem `exists_forall_sub_mem_ideal` / 定理 `exists_forall_sub_mem_ideal`

English:
theorem exists_forall_sub_mem_ideal
  statement: {ι : Type*} {s : Finset ι} (P : ι -> Ideal R)
  proof: by
  obtain ⟨y, hy⟩ :=
    exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩

中文:
定理 存在_对任意_sub_mem_ideal
  结论: {ι : 类型} {s : 有限集 ι} (P : ι -> 理想 R)
  证明: by
  obtain ⟨y, hy⟩ :=
    exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩

Depends on / 依赖: Ideal.Quotient.eq.mp, Ideal.Quotient.mk, Quotient, coprime, exists_representative_mod_finset
-/
theorem exists_forall_sub_mem_ideal {ι : Type*} {s : Finset ι} (P : ι -> Ideal R)
    (e : ι -> Nat) (prime : forall i in s, Prime (P i))
    (coprime : forallᵉ (i in s) (j in s), i != j -> P i != P j) (x : s -> R) :
    exists y, forall (i) (hi : i in s), y - x ⟨i, hi⟩ in P i ^ e i := by
  obtain ⟨y, hy⟩ :=
    exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩

end IsDedekindDomain

end DedekindDomain

end ChineseRemainder

section PID

open UniqueFactorizationMonoid Ideal

variable {R}
variable [IsDomain R] [IsPrincipalIdealRing R]

namespace Ideal

/--
theorem `span_singleton_dvd_span_singleton_iff_dvd` / 定理 `span_singleton_dvd_span_singleton_iff_dvd`

English:
theorem span_singleton_dvd_span_singleton_iff_dvd
  given: {a b : R}
  proof: ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩

@[deprecated (since := "2026-04-16")]
alias _root_.span_singleton_dvd_span_singleton_iff_dvd := span_sin

中文:
定理 span_singleton_dvd_span_singleton_iff_dvd
  条件: {a b : R}
  证明: ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩

@[deprecated (since := "2026-04-16")]
alias _root_.span_singleton_dvd_span_singleton_iff_dvd := span_sin

Depends on / 依赖: dvd_iff_le, dvd_iff_le.mp, dvd_iff_le.mpr, dvd_refl, dvd_trans, mem_span_singleton, mem_span_singleton.mp, mem_span_singleton.mpr
-/
theorem span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
    span {a} ∣ span ({b} : Set R) ↔ a ∣ b :=
  ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩

@[deprecated (since := "2026-04-16")]
alias _root_.span_singleton_dvd_span_singleton_iff_dvd := span_singleton_dvd_span_singleton_iff_dvd

@[simp]
/--
theorem `squarefree_span_singleton` / 定理 `squarefree_span_singleton`

English:
theorem squarefree_span_singleton
  given: {a : R}
  proof: by
  refine ⟨fun h x hx => ?_, fun h I hI => ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
exac

中文:
定理 squarefree_span_singleton
  条件: {a : R}
  证明: by
  refine ⟨fun h x hx => ?_, fun h I hI => ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
exac

Depends on / 依赖: IsPrincipal, Submodule, Submodule.IsPrincipal.generator_mem, eq_top_of_isUnit_mem, generator_mem, isUnit_iff, isUnit_iff.mpr, span_singleton_dvd_span_singleton_iff_dvd, span_singleton_generator, span_singleton_mul_span_singleton
-/
theorem squarefree_span_singleton {a : R} :
    Squarefree (span {a}) ↔ Squarefree a := by
  refine ⟨fun h x hx => ?_, fun h I hI => ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
exact isUnit_iff.mpr eq_top_of_isUnit_mem _ (Submodule.IsPrincipal.generator_mem I) (h _ hI)

/--
theorem `singleton_span_mem_normalizedFactors_of_mem_normalizedFactors` / 定理 `singleton_span_mem_normalizedFactors_of_mem_normalizedFactors`

English:
theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors
  statement: [NormalizationMonoid R]
  proof: by
  by_cases hb : b = 0
  · rw [span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb]; rw [normalizedFactors_zero] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · suffices Prime (span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd 

中文:
定理 singleton_span_mem_normalizedFactors_of_mem_normalizedFactors
  结论: [Normalization幺半群 R]
  证明: by
  by_cases hb : b = 0
  · rw [span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb]; rw [normalizedFactors_zero] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · suffices Prime (span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd 

Depends on / 依赖: Multiset, Multiset.notMem_zero, absurd, associated_iff_eq, associated_iff_eq.mp, bot_eq_zero, dvd_iff_le, dvd_iff_le.mpr, dvd_of_mem_normalizedFactors, exists_mem_normalizedFactors_of_dvd, irreducible, normalizedFactors_zero, notMem_zero, prime_iff_isPrime, span_singleton_eq_bot, span_singleton_eq_bot.mp, span_singleton_eq_bot.mpr, span_singleton_le_span_singleton, span_singleton_le_span_singleton.mpr, this.irreducible
-/
theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [NormalizationMonoid R]
    {a b : R} (ha : a in normalizedFactors b) :
    span ({a} : Set R) in normalizedFactors (span ({b} : Set R)) := by
  by_cases hb : b = 0
  · rw [span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb]; rw [normalizedFactors_zero] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · suffices Prime (span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd ?_ this.irreducible
          (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalizedFactors ha)))
      rwa [associated_iff_eq.mp hc']
    · by_contra h
      exact hb (span_singleton_eq_bot.mp h)
    rw [prime_iff_isPrime]
    · exact (span_singleton_prime (prime_of_normalized_factor a ha).ne_zero).mpr
        (prime_of_normalized_factor a ha)
    · by_contra h
      exact (prime_of_normalized_factor a ha).ne_zero (span_singleton_eq_bot.mp h)

@[deprecated (since := "2026-04-16")]
alias _root_.singleton_span_mem_normalizedFactors_of_mem_normalizedFactors :=
  singleton_span_mem_normalizedFactors_of_mem_normalizedFactors

/--
theorem `emultiplicity_eq_emultiplicity_span` / 定理 `emultiplicity_eq_emultiplicity_span`

English:
theorem emultiplicity_eq_emultiplicity_span
  given: {a b : R}
  proof: by
  by_cases h : FiniteMultiplicity a b
  · rw [h.emultiplicity_eq_multiplicity]
    apply emultiplicity_eq_of_dvd_of_not_dvd <;>
      rw [span_singleton_pow]; rw [span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd a b
    · apply h.not_pow_dvd_of_multiplicity_lt
      app

中文:
定理 emultiplicity_eq_emultiplicity_span
  条件: {a b : R}
  证明: by
  by_cases h : FiniteMultiplicity a b
  · rw [h.emultiplicity_eq_multiplicity]
    apply emultiplicity_eq_of_dvd_of_not_dvd <;>
      rw [span_singleton_pow]; rw [span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd a b
    · apply h.not_pow_dvd_of_multiplicity_lt
      app

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.not_iff_forall.mpr, emultiplicity_eq_multiplicity, emultiplicity_eq_of_dvd_of_not_dvd, emultiplicity_eq_top, h.emultiplicity_eq_multiplicity, h.not_pow_dvd_of_multiplicity_lt, lt_add_one, not_iff_forall, not_pow_dvd_of_multiplicity_lt, pow_multiplicity_dvd, span_singleton, span_singleton_dvd_span_singleton_iff_dvd, span_singleton_pow
-/
theorem emultiplicity_eq_emultiplicity_span {a b : R} :
    emultiplicity (span {a}) (span ({b} : Set R)) = emultiplicity a b := by
  by_cases h : FiniteMultiplicity a b
  · rw [h.emultiplicity_eq_multiplicity]
    apply emultiplicity_eq_of_dvd_of_not_dvd <;>
      rw [span_singleton_pow]; rw [span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd a b
    · apply h.not_pow_dvd_of_multiplicity_lt
      apply lt_add_one
  · suffices ¬FiniteMultiplicity (span ({a} : Set R)) (span ({b} : Set R)) by
      rw [emultiplicity_eq_top.2 h]; rw [emultiplicity_eq_top.2 this]
    exact FiniteMultiplicity.not_iff_forall.mpr fun n => by
      rw [span_singleton_pow]; rw [span_singleton_dvd_span_singleton_iff_dvd]
      exact FiniteMultiplicity.not_iff_forall.mp h n

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_eq_emultiplicity_span := emultiplicity_eq_emultiplicity_span

section NormalizationMonoid
variable [NormalizationMonoid R]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `normalizedFactorsEquivSpanNormalizedFactors` / `normalizedFactorsEquivSpanNormalizedFactors` 的定义

English:
definition normalizedFactorsEquivSpanNormalizedFactors
  signature: {r : R} (hr : r != 0)
  body: by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk]; rw [span_singleton_eq_span_singleton]; rw [Subtype.coe_mk]; rw [Subtype.coe_m

中文:
定义 normalizedFactorsEquivSpanNormalizedFactors
  签名: {r : R} (hr : r != 0)
  定义体: by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk]; rw [span_singleton_eq_span_singleton]; rw [Subtype.coe_mk]; rw [Subtype.coe_m

Depends on / 依赖: Equiv.ofBijective, IsPrime, Subtype, Subtype.coe_mk, Subtype.mk_eq_mk, Subtype.mk_eq_mk.mpr, coe_mk, d.prop, exists_mem_normalizedFactors_of_dvd, i.IsPrime, isPrime_of_prime, mem_normalizedFactors_eq_of_associated, mk_eq_mk, ofBijective, prime_of_normalized_factor, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors, span_singleton_eq_span_singleton
-/
noncomputable def normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r != 0) :
    { d : R | d in normalizedFactors r } ≃
      { I : Ideal R | I in normalizedFactors (span ({r} : Set R)) } := by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk]; rw [span_singleton_eq_span_singleton]; rw [Subtype.coe_mk]; rw [Subtype.coe_mk] at h
      exact Subtype.mk_eq_mk.mpr (mem_normalizedFactors_eq_of_associated ha hb h)
    · rintro ⟨i, hi⟩
      have : i.IsPrime := isPrime_of_prime (prime_of_normalized_factor i hi)
      have := exists_mem_normalizedFactors_of_dvd hr
        (Submodule.IsPrincipal.prime_generator_of_isPrime i
        (prime_of_normalized_factor i hi).ne_zero).irreducible ?_
      · obtain ⟨a, ha, ha'⟩ := this
        use ⟨a, ha⟩
        simp only [← span_singleton_eq_span_singleton.mpr ha',
            span_singleton_generator]
      · exact (Submodule.IsPrincipal.mem_iff_generator_dvd i).mp
          ((show span {r} <= i from dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi))
            (mem_span_singleton.mpr (dvd_refl r)))

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivSpanNormalizedFactors :=
  normalizedFactorsEquivSpanNormalizedFactors

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity` / 定理 `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity`

English:
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity
  statement: {r d : R}
  proof: by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, emultiplicity_eq_emultiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity :=
  emultiplicity_normalizedF

中文:
定理 emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity
  结论: {r d : R}
  证明: by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, emultiplicity_eq_emultiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity :=
  emultiplicity_normalizedF

Depends on / 依赖: Equiv.ofBijective_apply, Subtype, Subtype.coe_mk, coe_mk, emultiplicity_eq_emultiplicity_span, normalizedFactorsEquivSpanNormalizedFactors, ofBijective_apply
-/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity {r d : R}
    (hr : r != 0) (hd : d in normalizedFactors r) :
    emultiplicity d r =
      emultiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R)
        (span {r}) := by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, emultiplicity_eq_emultiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity :=
  emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity

/--
theorem `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity` / 定理 `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity`

English:
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity
  statement: {r : R}
  proof: by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm]; rw [Equiv.symm_apply_apply]; rw [Subtype.coe_mk]; rw [emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity hr ha]

@[deprecated (since := "2026-04-16")]
al

中文:
定理 emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity
  结论: {r : R}
  证明: by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm]; rw [Equiv.symm_apply_apply]; rw [Subtype.coe_mk]; rw [emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity hr ha]

@[deprecated (since := "2026-04-16")]
al

Depends on / 依赖: Equiv.symm_apply_apply, Subtype, Subtype.coe_mk, coe_mk, emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity, hx.symm, normalizedFactorsEquivSpanNormalizedFactors, surjective, symm_apply_apply
-/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity {r : R}
    (hr : r != 0) (I : { I : Ideal R | I in normalizedFactors (span ({r} : Set R)) }) :
    emultiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr).symm I : R) r =
      emultiplicity (I : Ideal R) (span {r}) := by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm]; rw [Equiv.symm_apply_apply]; rw [Subtype.coe_mk]; rw [emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity hr ha]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity :=
  emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity

variable [DecidableEq R]

/--
theorem `count_span_normalizedFactors_eq` / 定理 `count_span_normalizedFactors_eq`

English:
theorem count_span_normalizedFactors_eq
  given: {r X : R} (hr : r != 0) (hX : Prime X)
  proof: by
  have := emultiplicity_eq_emultiplicity_span (R := R) (a := X) (b := r)
  rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr]; rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible ?_)]; rw [normalize_apply]; rw [normUnit_eq_one]; rw [Units.val_one]; rw [one_eq_top]

中文:
定理 count_span_normalizedFactors_eq
  条件: {r X : R} (hr : r != 0) (hX : 素 X)
  证明: by
  have := emultiplicity_eq_emultiplicity_span (R := R) (a := X) (b := r)
  rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr]; rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible ?_)]; rw [normalize_apply]; rw [normUnit_eq_one]; rw [Units.val_one]; rw [one_eq_top]

Depends on / 依赖: Nat.cast_inj, Prime.irreducible, Submodule, Submodule.zero_eq_bot, Units.val_one, cast_inj, emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_emultiplicity_span, irreducible, mul_top, ne_eq, normUnit_eq_one, normalize_apply, not_false_eq_true, one_eq_top, prime_span_singleton_if, span_singleton_eq_bot, val_one, zero_eq_bot
-/
theorem count_span_normalizedFactors_eq {r X : R} (hr : r != 0) (hX : Prime X) :
    Multiset.count (span {X} : Ideal R) (normalizedFactors (span {r})) =
        Multiset.count (normalize X) (normalizedFactors r) := by
  have := emultiplicity_eq_emultiplicity_span (R := R) (a := X) (b := r)
  rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr]; rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible ?_)]; rw [normalize_apply]; rw [normUnit_eq_one]; rw [Units.val_one]; rw [one_eq_top]; rw [mul_top]; rw [Nat.cast_inj] at this
  · simp only [normalize_apply, this]
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, hr, not_false_eq_true]
  · simpa only [prime_span_singleton_iff]

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq := count_span_normalizedFactors_eq

/--
theorem `count_span_normalizedFactors_eq_of_normUnit` / 定理 `count_span_normalizedFactors_eq_of_normUnit`

English:
theorem count_span_normalizedFactors_eq_of_normUnit
  statement: {r X : R}
  proof: by
  simpa [hX₁, normalize_apply] using count_span_normalizedFactors_eq hr hX

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq_of_normUnit :=
  count_span_normalizedFactors_eq_of_normUnit

中文:
定理 count_span_normalizedFactors_eq_of_normUnit
  结论: {r X : R}
  证明: by
  simpa [hX₁, normalize_apply] using count_span_normalizedFactors_eq hr hX

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq_of_normUnit :=
  count_span_normalizedFactors_eq_of_normUnit

Depends on / 依赖: count_span_normalizedFactors_eq, normalize_apply
-/
theorem count_span_normalizedFactors_eq_of_normUnit {r X : R}
    (hr : r != 0) (hX₁ : normUnit X = 1) (hX : Prime X) :
      Multiset.count (span {X} : Ideal R) (normalizedFactors (span {r})) =
        Multiset.count X (normalizedFactors r) := by
  simpa [hX₁, normalize_apply] using count_span_normalizedFactors_eq hr hX

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq_of_normUnit :=
  count_span_normalizedFactors_eq_of_normUnit

end NormalizationMonoid

end Ideal

end PID

section primesOverFinset

open UniqueFactorizationMonoid Ideal

variable {A : Type*} [CommRing A] {p : Ideal A} (hpb : p != ⊥) [hpm : p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [IsDomain A] [IsTorsionFree A B]

namespace IsDedekindDomain

variable (p) in
/--
Definition of `primesOverFinset` / `primesOverFinset` 的定义

English:
abbreviation primesOverFinset
  signature: : Finset (Ideal B)
  body: (factors (p.map (algebraMap A B))).toFinset

@[deprecated (since := "2026-04-16")] alias _root_.primesOverFinset := primesOverFinset

include hpb in

中文:
缩写 primesOverFinset
  签名: : 有限集 (理想 B)
  定义体: (factors (p.map (algebraMap A B))).toFinset

@[deprecated (since := "2026-04-16")] alias _root_.primesOverFinset := primesOverFinset

include hpb in

Depends on / 依赖: algebraMap, factors, p.map, toFinset
-/
noncomputable abbrev primesOverFinset : Finset (Ideal B) :=
  (factors (p.map (algebraMap A B))).toFinset

@[deprecated (since := "2026-04-16")] alias _root_.primesOverFinset := primesOverFinset

include hpb in
/--
theorem `coe_primesOverFinset` / 定理 `coe_primesOverFinset`

English:
theorem coe_primesOverFinset
  statement: primesOverFinset p B = primesOver p B
  proof: by
  ext
  simpa using (mem_primesOver_iff_mem_normalizedFactors _ hpb).symm

@[deprecated (since := "2026-04-16")] alias _root_.coe_primesOverFinset := coe_primesOverFinset

include hpb in

中文:
定理 coe_primesOverFinset
  结论: primesOverFinset p B = primesOver p B
  证明: by
  ext
  simpa using (mem_primesOver_iff_mem_normalizedFactors _ hpb).symm

@[deprecated (since := "2026-04-16")] alias _root_.coe_primesOverFinset := coe_primesOverFinset

include hpb in

Depends on / 依赖: mem_primesOver_iff_mem_normalizedFactors
-/
theorem coe_primesOverFinset : primesOverFinset p B = primesOver p B := by
  ext
  simpa using (mem_primesOver_iff_mem_normalizedFactors _ hpb).symm

@[deprecated (since := "2026-04-16")] alias _root_.coe_primesOverFinset := coe_primesOverFinset

include hpb in
/--
theorem `mem_primesOverFinset_iff` / 定理 `mem_primesOverFinset_iff`

English:
theorem mem_primesOverFinset_iff
  given: {P : Ideal B}
  statement: P in primesOverFinset p B ↔ P in primesOver p B
  proof: by
  rw [← Finset.mem_coe]; rw [coe_primesOverFinset hpb]

@[deprecated (since := "2026-04-16")]
alias _root_.mem_primesOverFinset_iff := mem_primesOverFinset_iff

中文:
定理 mem_primesOverFinset_iff
  条件: {P : 理想 B}
  结论: P in primesOverFinset p B ↔ P in primesOver p B
  证明: by
  rw [← Finset.mem_coe]; rw [coe_primesOverFinset hpb]

@[deprecated (since := "2026-04-16")]
alias _root_.mem_primesOverFinset_iff := mem_primesOverFinset_iff

Depends on / 依赖: Finset, Finset.mem_coe, coe_primesOverFinset, mem_coe
-/
theorem mem_primesOverFinset_iff {P : Ideal B} : P in primesOverFinset p B ↔ P in primesOver p B := by
  rw [← Finset.mem_coe]; rw [coe_primesOverFinset hpb]

@[deprecated (since := "2026-04-16")]
alias _root_.mem_primesOverFinset_iff := mem_primesOverFinset_iff

end IsDedekindDomain

set_option linter.overlappingInstances false in
variable {R} (A) in
/--
theorem `IsLocalRing.primesOverFinset_eq` / 定理 `IsLocalRing.primesOverFinset_eq`

English:
theorem IsLocalRing.primesOverFinset_eq
  statement: [IsLocalRing A] [IsDedekindDomain A]
  proof: by
  have : IsDomain R := .of_faithfulSMul R A
  rw [← Finset.coe_eq_singleton]; rw [IsDedekindDomain.coe_primesOverFinset hp0]; rw [IsLocalRing.primesOver_eq A hp0]

中文:
定理 是局部环.primesOverFinset_eq
  结论: [是局部环 A] [是Dedekind整环 A]
  证明: by
  have : IsDomain R := .of_faithfulSMul R A
  rw [← Finset.coe_eq_singleton]; rw [IsDedekindDomain.coe_primesOverFinset hp0]; rw [IsLocalRing.primesOver_eq A hp0]

Depends on / 依赖: Finset, Finset.coe_eq_singleton, IsDedekindDomain, IsDedekindDomain.coe_primesOverFinset, IsDomain, IsLocalRing, IsLocalRing.primesOver_eq, coe_eq_singleton, coe_primesOverFinset, of_faithfulSMul, primesOver_eq
-/
theorem IsLocalRing.primesOverFinset_eq [IsLocalRing A] [IsDedekindDomain A]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p != ⊥) :
    IsDedekindDomain.primesOverFinset p A = {IsLocalRing.maximalIdeal A} := by
  have : IsDomain R := .of_faithfulSMul R A
  rw [← Finset.coe_eq_singleton]; rw [IsDedekindDomain.coe_primesOverFinset hp0]; rw [IsLocalRing.primesOver_eq A hp0]

namespace IsDedekindDomain.HeightOneSpectrum

/--
Definition of `equivPrimesOver` / `equivPrimesOver` 的定义

English:
definition equivPrimesOver
  signature: (hp : p != 0)
  body: Set.BijOn.equiv HeightOneSpectrum.asIdeal
    ⟨fun v hv => ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h => HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ => ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hp hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]

中文:
定义 equivPrimesOver
  签名: (hp : p != 0)
  定义体: Set.BijOn.equiv HeightOneSpectrum.asIdeal
    ⟨fun v hv => ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h => HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ => ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hp hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.asIdeal, HeightOneSpectrum.ext_iff.mpr, Set.BijOn.equiv, asIdeal, ext_iff, isPrime, liesOver_iff_dvd_map, ne_bot_of_mem_primesOver, ne_top, v.isPrime, v.isPrime.ne_top
-/
noncomputable def equivPrimesOver (hp : p != 0) :
    {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p} ≃ p.primesOver B :=
  Set.BijOn.equiv HeightOneSpectrum.asIdeal
    ⟨fun v hv => ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h => HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ => ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hp hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]
/--
theorem `equivPrimesOver_apply` / 定理 `equivPrimesOver_apply`

English:
theorem equivPrimesOver_apply
  statement: (hp : p != 0)
  proof: rfl

中文:
定理 equivPrimesOver_apply
  结论: (hp : p != 0)
  证明: rfl
-/
theorem equivPrimesOver_apply (hp : p != 0)
    (v : {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p}) :
    equivPrimesOver B hp v = v.1.asIdeal := rfl

variable (A) in
/-- The pullback of a height one prime in `B` to `A`. -/
@[simps]
/--
Definition of `under` / `under` 的定义

English:
definition under
  signature: {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
  body: w.asIdeal.under A
  isPrime := .under A w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

中文:
定义 under
  签名: {B : 类型} [交换环 B] [是整环 B] [代数 A B] [代数.是整 A B]
  定义体: w.asIdeal.under A
  isPrime := .under A w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

Depends on / 依赖: asIdeal, w.asIdeal.under
-/
def under {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.under A
  isPrime := .under A w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

end IsDedekindDomain.HeightOneSpectrum

variable (p) [Algebra.IsIntegral A B]

namespace IsDedekindDomain

/--
theorem `primesOver_finite` / 定理 `primesOver_finite`

English:
theorem primesOver_finite
  statement: (primesOver p B).Finite
  proof: by
  by_cases hpb : p = ⊥
  · rw [hpb] at hpm ⊢
    have : IsDomain A := IsDomain.of_bot_isPrime A
    rw [primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · rw [← coe_primesOverFinset hpb B]
    exact (primesOverFinset p B).finite_toSet

@[deprecated (since := "2026-04-16")] alias _root_.prim

中文:
定理 primesOver_finite
  结论: (primesOver p B).有限
  证明: by
  by_cases hpb : p = ⊥
  · rw [hpb] at hpm ⊢
    have : IsDomain A := IsDomain.of_bot_isPrime A
    rw [primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · rw [← coe_primesOverFinset hpb B]
    exact (primesOverFinset p B).finite_toSet

@[deprecated (since := "2026-04-16")] alias _root_.prim

Depends on / 依赖: IsDomain, IsDomain.of_bot_isPrime, Set.finite_singleton, coe_primesOverFinset, finite_singleton, finite_toSet, of_bot_isPrime, primesOverFinset, primesOver_bot
-/
theorem primesOver_finite : (primesOver p B).Finite := by
  by_cases hpb : p = ⊥
  · rw [hpb] at hpm ⊢
    have : IsDomain A := IsDomain.of_bot_isPrime A
    rw [primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · rw [← coe_primesOverFinset hpb B]
    exact (primesOverFinset p B).finite_toSet

@[deprecated (since := "2026-04-16")] alias _root_.primesOver_finite := primesOver_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (p.primesOver B)
  body: Set.Finite.fintype (primesOver_finite p B)

中文:
实例 :
  签名: 有限类型 (p.primesOver B)
  定义体: Set.Finite.fintype (primesOver_finite p B)

Depends on / 依赖: Finite, Set.Finite.fintype, fintype, primesOver_finite
-/
noncomputable instance : Fintype (p.primesOver B) := Set.Finite.fintype (primesOver_finite p B)

/--
theorem `primesOver_ncard_ne_zero` / 定理 `primesOver_ncard_ne_zero`

English:
theorem primesOver_ncard_ne_zero
  statement: (primesOver p B).ncard != 0
  proof: by
  rcases exists_maximal_ideal_liesOver_of_isIntegral (S := B) p with ⟨P, hPm, hp⟩
  exact Set.ncard_ne_zero_of_mem ⟨hPm.isPrime, hp⟩ (primesOver_finite p B)

@[deprecated (since := "2026-04-16")]
alias _root_.primesOver_ncard_ne_zero := primesOver_ncard_ne_zero

中文:
定理 primesOver_ncard_ne_zero
  结论: (primesOver p B).ncard != 0
  证明: by
  rcases exists_maximal_ideal_liesOver_of_isIntegral (S := B) p with ⟨P, hPm, hp⟩
  exact Set.ncard_ne_zero_of_mem ⟨hPm.isPrime, hp⟩ (primesOver_finite p B)

@[deprecated (since := "2026-04-16")]
alias _root_.primesOver_ncard_ne_zero := primesOver_ncard_ne_zero

Depends on / 依赖: Set.ncard_ne_zero_of_mem, exists_maximal_ideal_liesOver_of_isIntegral, hPm.isPrime, isPrime, ncard_ne_zero_of_mem, primesOver_finite
-/
theorem primesOver_ncard_ne_zero : (primesOver p B).ncard != 0 := by
  rcases exists_maximal_ideal_liesOver_of_isIntegral (S := B) p with ⟨P, hPm, hp⟩
  exact Set.ncard_ne_zero_of_mem ⟨hPm.isPrime, hp⟩ (primesOver_finite p B)

@[deprecated (since := "2026-04-16")]
alias _root_.primesOver_ncard_ne_zero := primesOver_ncard_ne_zero

/--
theorem `one_le_primesOver_ncard` / 定理 `one_le_primesOver_ncard`

English:
theorem one_le_primesOver_ncard
  statement: 1 <= (primesOver p B).ncard
  proof: Nat.one_le_iff_ne_zero.mpr (primesOver_ncard_ne_zero p B)

@[deprecated (since := "2026-04-16")]
alias _root_.one_le_primesOver_ncard := one_le_primesOver_ncard

中文:
定理 one_le_primesOver_ncard
  结论: 1 <= (primesOver p B).ncard
  证明: Nat.one_le_iff_ne_zero.mpr (primesOver_ncard_ne_zero p B)

@[deprecated (since := "2026-04-16")]
alias _root_.one_le_primesOver_ncard := one_le_primesOver_ncard

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, one_le_iff_ne_zero, primesOver_ncard_ne_zero
-/
theorem one_le_primesOver_ncard : 1 <= (primesOver p B).ncard :=
  Nat.one_le_iff_ne_zero.mpr (primesOver_ncard_ne_zero p B)

@[deprecated (since := "2026-04-16")]
alias _root_.one_le_primesOver_ncard := one_le_primesOver_ncard

end IsDedekindDomain

end primesOverFinset

open IsDedekindDomain in
/--
lemma `Algebra.IsIntegral.nontrivial_heightOneSpectrum` / 引理 `Algebra.IsIntegral.nontrivial_heightOneSpectrum`

English:
lemma Algebra.IsIntegral.nontrivial_heightOneSpectrum
  statement: [IsDomain A] [Algebra R A]
  proof: by
  have := (FaithfulSMul.algebraMap_injective R A).isDomain
  let f (p : HeightOneSpectrum A) : HeightOneSpectrum R := p.under R
  have : Function.Surjective f := fun ⟨p, _, hp⟩ => by
    obtain ⟨P, hP, rfl⟩ := p.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := A) (by simp)
    exact ⟨⟨P, h

中文:
引理 代数.是整.nontrivial_heightOneSpectrum
  结论: [是整环 A] [代数 R A]
  证明: by
  have := (FaithfulSMul.algebraMap_injective R A).isDomain
  let f (p : HeightOneSpectrum A) : HeightOneSpectrum R := p.under R
  have : Function.Surjective f := fun ⟨p, _, hp⟩ => by
    obtain ⟨P, hP, rfl⟩ := p.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := A) (by simp)
    exact ⟨⟨P, h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.Surjective, HeightOneSpectrum, Surjective, algebraMap_injective, exists_ideal_over_prime_of_isIntegral_of_isDomain, isDomain, nontrivial, p.exists_ideal_over_prime_of_isIntegral_of_isDomain, p.under, this.nontrivial
-/
lemma Algebra.IsIntegral.nontrivial_heightOneSpectrum [IsDomain A] [Algebra R A]
    [FaithfulSMul R A] [Algebra.IsIntegral R A] [Nontrivial (HeightOneSpectrum R)] :
    Nontrivial (HeightOneSpectrum A) := by
  have := (FaithfulSMul.algebraMap_injective R A).isDomain
  let f (p : HeightOneSpectrum A) : HeightOneSpectrum R := p.under R
  have : Function.Surjective f := fun ⟨p, _, hp⟩ => by
    obtain ⟨P, hP, rfl⟩ := p.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := A) (by simp)
    exact ⟨⟨P, hP, by aesop⟩, rfl⟩
  exact this.nontrivial
