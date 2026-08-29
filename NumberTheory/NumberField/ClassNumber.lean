/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
We denote by `M K` the Minkowski bound of a number field `K`, defined as
`(4 / π) ^ nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)`.
- `NumberField.classNumber`: the class number of a number field is the (finite)
  cardinality of the class group of its ring of integers
- `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field. To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
  `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
  `p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard technique to prove
  that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
- `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field such that `K/ℚ` is Galois. To show that `𝓞 K` is a PID it is enough to show
  that, for all (natural) primes `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such
  that either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is the standard
  technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977number], discussion
  after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
-/

@[expose] public section

open scoped nonZeroDivisors Real

open Module NumberField InfinitePlace Ideal Nat

variable (K : Type*) [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank Rat K)! / (finrank Rat K) ^ (finrank Rat K) * √|discr K|)

namespace NumberField

namespace RingOfIntegers

/--
Instance `instFintypeClassGroup` / 实例 `instFintypeClassGroup`

English:
instance instFintypeClassGroup
  signature: : Fintype (ClassGroup (𝓞 K))
  body: ClassGroup.fintypeOfAdmissibleOfFinite Rat K AbsoluteValue.absIsAdmissible

中文:
实例 instFintypeClassGroup
  签名: : Fintype (ClassGroup (𝓞 K))
  定义体: ClassGroup.fintypeOfAdmissibleOfFinite Rat K AbsoluteValue.absIsAdmissible

Depends on / 依赖: AbsoluteValue, AbsoluteValue.absIsAdmissible, ClassGroup, ClassGroup.fintypeOfAdmissibleOfFinite, absIsAdmissible, fintypeOfAdmissibleOfFinite
-/
noncomputable instance instFintypeClassGroup : Fintype (ClassGroup (𝓞 K)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite Rat K AbsoluteValue.absIsAdmissible

end RingOfIntegers

/--
Definition of `classNumber` / `classNumber` 的定义

English:
definition classNumber
  signature: : Nat
  body: Fintype.card (ClassGroup (𝓞 K))

中文:
定义 classNumber
  签名: : 自然数
  定义体: Fintype.card (ClassGroup (𝓞 K))

Depends on / 依赖: ClassGroup, Fintype, Fintype.card
-/
noncomputable def classNumber : Nat :=
  Fintype.card (ClassGroup (𝓞 K))

/--
theorem `classNumber_ne_zero` / 定理 `classNumber_ne_zero`

English:
theorem classNumber_ne_zero
  statement: classNumber K != 0
  proof: Fintype.card_ne_zero

中文:
定理 classNumber_ne_zero
  结论: classNumber K != 0
  证明: Fintype.card_ne_zero

Depends on / 依赖: Fintype, Fintype.card_ne_zero, card_ne_zero
-/
theorem classNumber_ne_zero : classNumber K != 0 := Fintype.card_ne_zero

/--
theorem `classNumber_pos` / 定理 `classNumber_pos`

English:
theorem classNumber_pos
  statement: 0 < classNumber K
  proof: Fintype.card_pos

中文:
定理 classNumber_pos
  结论: 0 < classNumber K
  证明: Fintype.card_pos

Depends on / 依赖: Fintype, Fintype.card_pos, card_pos
-/
theorem classNumber_pos : 0 < classNumber K := Fintype.card_pos

variable {K}

/--
theorem `classNumber_eq_one_iff` / 定理 `classNumber_eq_one_iff`

English:
theorem classNumber_eq_one_iff
  statement: classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
  proof: card_classGroup_eq_one_iff

中文:
定理 classNumber_eq_one_iff
  结论: classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
  证明: card_classGroup_eq_one_iff

Depends on / 依赖: card_classGroup_eq_one_iff
-/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff

/--
theorem `exists_ideal_in_class_of_norm_le` / 定理 `exists_ideal_in_class_of_norm_le`

English:
theorem exists_ideal_in_class_of_norm_le
  given: (C : ClassGroup (𝓞 K))
  proof: by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ != 0 := by
    contrapos

中文:
定理 exists_ideal_in_class_of_norm_le
  条件: (C : ClassGroup (𝓞 K))
  证明: by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ != 0 := by
    contrapos

Depends on / 依赖: Algebra, Algebra.linearMap_apply, ClassGroup, ClassGroup.mk0_surjective, FractionalIdeal, FractionalIdeal.mk0, contrapose, dvd_iff_le, dvd_iff_le.mpr, exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr, h_nm, h_nz, linearMap_apply, map_zero, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, mk0_surjective, mul_zero, span_singleton_eq_bot, span_singleton_le_iff_mem
-/
theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    exists I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) <= M K := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ != 0 := by
    contrapose h_nz
    rw [h_nz]; rw [mul_zero]; rw [zero_eq_bot]; rw [span_singleton_eq_bot] at hI
    rw [Algebra.linearMap_apply]; rw [hI]; rw [map_zero]
  let I := (⟨I₀, mem_nonZeroDivisors_iff_ne_zero.mpr this⟩ : (Ideal (𝓞 K))⁰)
  refine ⟨I, ?_, ?_⟩
  · suffices ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ by rw [this, hJ, inv_inv]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨a, Subtype.coe_ne_coe.1 h_nz, by rw [mul_comm, hI]⟩
  · rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), Algebra.linearMap_apply,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_absNorm, hI, map_mul,
      cast_mul, Rat.cast_mul, absNorm_apply, Rat.cast_natCast, Rat.cast_natCast,
      FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, mul_div_assoc,
      mul_assoc, mul_assoc] at h_nm
    refine le_of_mul_le_mul_of_pos_left h_nm ?_
exact cast_pos.mpr pos_of_ne_zero absNorm_ne_zero_of_nonZeroDivisors J

end NumberField

namespace RingOfIntegers

variable {K}

open scoped NumberField

/--
theorem `isPrincipalIdealRing_of_isPrincipal_of_norm_le` / 定理 `isPrincipalIdealRing_of_isPrincipal_of_norm_le`

English:
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le
  proof: by
  rw [← classNumber_eq_one_iff]; rw [classNumber]; rw [Fintype.card_eq_one_iff]
  refine ⟨1, fun C => ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI

中文:
定理 isPrincipalIdealRing_of_isPrincipal_of_norm_le
  证明: by
  rw [← classNumber_eq_one_iff]; rw [classNumber]; rw [Fintype.card_eq_one_iff]
  refine ⟨1, fun C => ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI

Depends on / 依赖: ClassGroup, ClassGroup.mk0_eq_one_iff, Fintype, Fintype.card_eq_one_iff, card_eq_one_iff, classNumber, classNumber_eq_one_iff, exists_ideal_in_class_of_norm_le, mk0_eq_one_iff
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le
    (h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm (I : Ideal (𝓞 K)) <= M K ->
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) : IsPrincipalIdealRing (𝓞 K) := by
  rw [← classNumber_eq_one_iff]; rw [classNumber]; rw [Fintype.card_eq_one_iff]
  refine ⟨1, fun C => ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI

/--
theorem `isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime` / 定理 `isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime`

English:
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
  proof: by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
  rw [← mem_isPrincipalSubmonoid_iff]; rw [← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ => mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J 

中文:
定理 isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
  证明: by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
  rw [← mem_isPrincipalSubmonoid_iff]; rw [← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ => mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J 

Depends on / 依赖: Ideal.prod_normalizedFactors_eq_self, Submonoid, Submonoid.multiset_prod_mem, Subtype, Subtype.coe_mk, bot_isPrincipal, cast_le, cast_le.mpr, coe_mk, coe_ne_zero, isPrincipalIdealRing_of_isPrincipal_of_norm_le, mem_isPrincipalSubmonoid_iff, mem_isPrincipalSubmonoid_iff.mp, mem_nonZeroDivisors_of_ne_zero, mem_normalizedFactors_iff, multiset_prod_mem, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, prod_normalizedFactors_eq_self
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    (h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime ->
      absNorm (I : Ideal (𝓞 K)) <= M K -> Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
  rw [← mem_isPrincipalSubmonoid_iff]; rw [← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ => mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J = 0
  · simpa [hJ0] using! bot_isPrincipal
  rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
  refine h (((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1) ?_
  exact (cast_le.mpr <| le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
absNorm_dvd_absNorm_of_le le_of_dvd
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ).trans hI

set_option linter.style.longLine false in
/--
theorem `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc` / 定理 `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`

English:
theorem isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  proof: by
refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun ⟨P, HP⟩ hP hPN => ?_
obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal under Int P
have hp0 : p != 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨P, HP⟩
eq_bot_of_comap_eq_bot (R := Int) by simpa only [hp, submodule_span_eq, span

中文:
定理 isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  证明: by
refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun ⟨P, HP⟩ hP hPN => ?_
obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal under Int P
have hp0 : p != 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨P, HP⟩
eq_bot_of_comap_eq_bot (R := Int) by simpa only [hp, submodule_span_eq, span

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.principal, LiesOver, P.LiesOver, abs_choice, coe_ne_zero, eq_bot_of_comap_eq_bot, hpprime, isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, principal, span_singleton_eq_bot, span_singleton_prime, submodule_span_eq
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> forall (P : Ideal (𝓞 K)),
      P in primesOver (span {(p : Int)}) (𝓞 K) -> p ^ P.inertiaDeg Int <= ⌊(M K)⌋₊ ->
      Submodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K) := by
refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun ⟨P, HP⟩ hP hPN => ?_
obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal under Int P
have hp0 : p != 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨P, HP⟩
eq_bot_of_comap_eq_bot (R := Int) by simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hlies : P.LiesOver (span {p}) := by
    rcases abs_choice p with h | h <;>
    simpa [h, span_singleton_neg p, ← submodule_span_eq, ← hp] using over_under P
  have hspan : span {↑p.natAbs} = span {p} := by
    rcases abs_choice p with h | h <;> simp [h]
  have hple : p.natAbs ^ P.inertiaDeg Int <= ⌊(M K)⌋₊ := by
    refine le_floor ?_
    have : P.IsMaximal := hP.isMaximal (by simpa using HP.2)
    have : (span {p}).IsMaximal := (hpprime (.under Int P)).isMaximal_span_singleton
    simpa only [hspan, ← cast_pow, ← natAbs_pow_inertiaDeg p P] using hPN
  have hpabsprime := Int.prime_iff_natAbs_prime.mp (hpprime (hP.under _))
  refine h _ ?_ hpabsprime _ ⟨hP, ?_⟩ hple
  · suffices 0 < P.inertiaDeg Int by
      exact Finset.mem_Icc.mpr ⟨hpabsprime.one_le, le_trans (le_pow this) hple⟩
    have := (isPrime_of_prime (prime_span_singleton_iff.mpr <|
      hpprime (hP.under _))).isMaximal <| by simp [((hpprime (hP.under _))).ne_zero]
    exact inertiaDeg_pos ..
  · exact hspan ▸ hlies

/--
theorem `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc` / 定理 `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`

English:
theorem isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  proof: by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P ⟨hP1, hP2⟩ hple => ?_)
  obtain ⟨Q, ⟨hQ1, hQ2⟩, H⟩ := h p hpmem hp
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])

中文:
定理 isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  证明: by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P ⟨hP1, hP2⟩ hple => ?_)
  obtain ⟨Q, ⟨hQ1, hQ2⟩, H⟩ := h p hpmem hp
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])

Depends on / 依赖: P.inertiaDeg, exists_smul_eq_of_isGaloisGroup, hp.ne_zero, inertiaDeg, inertiaDeg_eq_of_isGaloisGroup, isMaximal, isPrime_of_prime, isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc, ne_zero, prime_iff_prime_int, prime_iff_prime_int.mp, prime_span_singleton_iff, prime_span_singleton_iff.mpr
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    [IsGalois Rat K] (h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime ->
      exists P in primesOver (span {(p : Int)}) (𝓞 K),
        ⌊(M K)⌋₊ < p ^ P.inertiaDeg Int ∨
          Submodule.IsPrincipal P) :
      IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P ⟨hP1, hP2⟩ hple => ?_)
  obtain ⟨Q, ⟨hQ1, hQ2⟩, H⟩ := h p hpmem hp
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])
  by_cases h : ⌊(M K)⌋₊ < p ^ P.inertiaDeg Int
  · linarith
  rw [inertiaDeg_eq_of_isGaloisGroup (span {↑p}) Q P (K ≃ₐ[Rat] K)] at H
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span ({↑p} : Set Int)) Q P (K ≃ₐ[Rat] K)
  exact (H.resolve_left h).map_ringHom (MulSemiringAction.toRingHom (K ≃ₐ[Rat] K) (𝓞 K) σ)

/--
theorem `isPrincipalIdealRing_of_abs_discr_lt` / 定理 `isPrincipalIdealRing_of_abs_discr_lt`

English:
theorem isPrincipalIdealRing_of_abs_discr_lt
  proof: by
  have : 0 < finrank Rat K := finrank_pos -- Lean needs to know this for `positivity` to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀' (by positivity)]; rw [mul_inv]; rw [← inv_pow]; rw [inv_div]; rw [inv_div]; rw [mul_assoc]; rw [Int.cast_a

中文:
定理 isPrincipalIdealRing_of_abs_discr_lt
  证明: by
  have : 0 < finrank Rat K := finrank_pos -- Lean needs to know this for `positivity` to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀' (by positivity)]; rw [mul_inv]; rw [← inv_pow]; rw [inv_div]; rw [inv_div]; rw [mul_assoc]; rw [Int.cast_a

Depends on / 依赖: Int.cast_abs, Nat.lt_succ_iff.mp, Real.sqrt_lt, absNorm_eq_one_iff, absNorm_eq_one_iff.mp, cast_abs, cast_lt, cast_lt.mp, finrank, finrank_pos, inv_div, inv_pow, isPrincipalIdealRing_of_isPrincipal_of_norm_le, le_antisymm, lt_of_le_of_lt, lt_succ_iff, mul_assoc, mul_inv, one_le_iff_ne_zero, one_le_iff_ne_zero.mpr
-/
theorem isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank Rat K) ^ (finrank Rat K) / (finrank Rat K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  have : 0 < finrank Rat K := finrank_pos -- Lean needs to know this for `positivity` to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀' (by positivity)]; rw [mul_inv]; rw [← inv_pow]; rw [inv_div]; rw [inv_div]; rw [mul_assoc]; rw [Int.cast_abs] at h
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI => ?_)
  rw [absNorm_eq_one_iff.mp <| le_antisymm (Nat.lt_succ_iff.mp (cast_lt.mp
    (lt_of_le_of_lt hI h))) <| one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors I)]
  exact top_isPrincipal

end RingOfIntegers

namespace Rat

open NumberField

/--
theorem `classNumber_eq` / 定理 `classNumber_eq`

English:
theorem classNumber_eq
  statement: NumberField.classNumber Rat = 1
  proof: classNumber_eq_one_iff.mpr IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

中文:
定理 classNumber_eq
  结论: NumberField.classNumber Rat = 1
  证明: classNumber_eq_one_iff.mpr IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.of_surjective, Rat.ringOfIntegersEquiv.symm, Rat.ringOfIntegersEquiv.symm.surjective, classNumber_eq_one_iff, classNumber_eq_one_iff.mpr, of_surjective, ringOfIntegersEquiv, surjective
-/
theorem classNumber_eq : NumberField.classNumber Rat = 1 :=
classNumber_eq_one_iff.mpr IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

end Rat
