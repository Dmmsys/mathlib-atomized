/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

/-!

# Going down for integrally closed domains

In this file, we provide the instance that any integral extension of `R ⊆ S` satisfies going down
if `R` is integrally closed.

-/

public section

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
lemma `Polynomial.coeff_mem_radical_span_coeff_of_dvd` / 引理 `Polynomial.coeff_mem_radical_span_coeff_of_dvd`

English:
lemma Polynomial.coeff_mem_radical_span_coeff_of_dvd
  proof: by
  rw [Ideal.radical_eq_sInf]; rw [Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    

中文:
引理 Polynomial.coeff_mem_radical_span_coeff_of_dvd
  证明: by
  rw [Ideal.radical_eq_sInf]; rw [Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.mem_sInf, Ideal.radical_eq_sInf, Ideal.subset_span, Quotient, coeff_eq_zero_of_natDegree_lt, dvd_prime_pow, eq_zero_iff_mem, hi.ne, isUnit, isUnit_iff, isUnit_iff.mp, lt_trichotomy, map_dvd, mem_sInf, natDegree, p.map, p.natDegree, prime_X
-/
lemma Polynomial.coeff_mem_radical_span_coeff_of_dvd
    (p : R[X]) (q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p) (i : Nat) (hi : i != q.natDegree) :
    q.coeff i in (Ideal.span { p.coeff i | i < p.natDegree }).radical := by
  rw [Ideal.radical_eq_sInf]; rw [Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    · simp [hp]
    · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
  obtain ⟨j, hj, a, ha⟩ :=
    (dvd_prime_pow (prime_X (R := R ⧸ P)) _).mp (this ▸ map_dvd (Ideal.Quotient.mk P) H)
  obtain ⟨r, hr, e⟩ := isUnit_iff.mp a⁻¹.isUnit
  rw [← Units.eq_mul_inv_iff_mul_eq]; rw [← e] at ha
  obtain rfl : j = q.natDegree := by
    simpa [hq.natDegree_map, hr.ne_zero] using congr(($ha).natDegree).symm
  simpa [hi, Ideal.Quotient.eq_zero_iff_mem] using congr(($ha).coeff i)

@[stacks 00H8]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] :
  body: by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  constructor
  intro p _ Q _ hpQ
  let SQ := Localization.AtPrime Q
  suffices (p.map (algebraMap _ SQ)).comap (algebraMap _ SQ) <= p by
    obtain ⟨P, hP, e⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime _).mp (this.antisymm Ideal.le

中文:
实例 [IsDomain
  签名: S] [FaithfulSMul R S] [Algebra.Is整数egral R S] [Is整数egrallyClosed R] :
  定义体: by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  constructor
  intro p _ Q _ hpQ
  let SQ := Localization.AtPrime Q
  suffices (p.map (algebraMap _ SQ)).comap (algebraMap _ SQ) <= p by
    obtain ⟨P, hP, e⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime _).mp (this.antisymm Ideal.le

Depends on / 依赖: AtPrime, FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.comap_map_eq_self_iff_of_isPrime, Ideal.comap_mono, Ideal.le_comap_map, Ideal.under_under, IsLocalRing, IsLocalRing.le_maximalIdeal_of_isPrime, Localization, Localization.AtPrime, Localization.AtPrime.under_maximalIdeal, P.under, algebraMap, algebraMap_injective, antisymm, comap_map_eq_self_iff_of_isPrime, comap_mono, isDomain, le_comap_map
-/
instance [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] :
    Algebra.HasGoingDown R S := by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  constructor
  intro p _ Q _ hpQ
  let SQ := Localization.AtPrime Q
  suffices (p.map (algebraMap _ SQ)).comap (algebraMap _ SQ) <= p by
    obtain ⟨P, hP, e⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime _).mp (this.antisymm Ideal.le_comap_map)
    refine ⟨P.under S, ?_, inferInstance, ⟨by rw [Ideal.under_under, ← e]⟩⟩
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime P)).trans_eq
      Localization.AtPrime.under_maximalIdeal
  intro x hx
  obtain ⟨a, ha, haQ⟩ : exists a, x • a in Ideal.map (algebraMap R S) p ∧ a ∉ Q := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_eq R S SQ, ← Ideal.map_map,
      IsLocalization.mem_map_algebraMap_iff Q.primeCompl, ← map_mul] using hx
  obtain ⟨f, hfm, hfa, hf⟩ := exists_monic_aeval_eq_zero_forall_mem_of_mem_map ha
  obtain ⟨i, hi, hip⟩ : exists i != (minpoly R a).natDegree, (minpoly R a).coeff i ∉ p := by
    set g := minpoly R a
    by_contra! H
    have : g.map (Ideal.Quotient.mk p) = X ^ g.natDegree := by
      ext i
      obtain hi | rfl | hi := lt_trichotomy i g.natDegree
      · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using H _ hi.ne
      · simp [g, minpoly.monic (Algebra.IsIntegral.isIntegral _)]
      · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
    have : Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) (a ^ (minpoly R a).natDegree) = 0 := by
      simpa [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, g] using
        congr(aeval (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) a) $this).symm
    exact haQ (‹Q.IsPrime›.mem_of_pow_mem _
      (Ideal.map_le_iff_le_comap.mpr hpQ.le (Ideal.Quotient.eq_zero_iff_mem.mp this)))
  by_cases hx0 : x = 0; · simp [hx0]
  have := Polynomial.coeff_mem_radical_span_coeff_of_dvd _ _ hfm
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral _) hfa)
  simp only [IsIntegrallyClosed.minpoly_smul hx0 (Algebra.IsIntegral.isIntegral _),
    natDegree_scaleRoots, coeff_scaleRoots, Ideal.radical_eq_sInf, Submodule.mem_sInf,
    Set.mem_ofPred_eq, and_imp] at this
  refine ‹p.IsPrime›.mem_of_pow_mem _ ((‹p.IsPrime›.mem_or_mem
    (this i hi p ?_ inferInstance)).resolve_left hip)
  simp +contextual [Ideal.span_le, Set.subset_def, LT.lt.ne, hf]
