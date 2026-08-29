/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime

/-!
# Criteria under which a Dedekind domain is a PID

This file contains some results that we can use to test whether all ideals in a Dedekind domain are
principal.

## Main results

* `Ideal.IsPrincipal.of_finite_maximals_of_isUnit`: an invertible ideal in a commutative ring
  with finitely many maximal ideals, is a principal ideal.
* `IsPrincipalIdealRing.of_finite_primes`: if a Dedekind domain has finitely many prime ideals,
  it is a principal ideal domain.
* `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`: a Dedekind domain
  that is a unique factorisation domain, is also a principal ideal domain.
-/

public section


variable {R : Type*} [CommRing R]

open Ideal

open UniqueFactorizationMonoid

open scoped nonZeroDivisors

/--
theorem `Ideal.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne` / 定理 `Ideal.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne`

English:
theorem Ideal.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne
  statement: {P : Ideal R}
  proof: by
  by_cases hP0 : P = ⊥
  · subst hP0
    rwa [eq_comm, span_singleton_eq_bot, ← mem_bot]
  have hspan0 : span {x} != ⊥ := mt Ideal.span_singleton_eq_bot.mp (hxP2 <| · ▸ zero_mem _)
  rw [← associated_iff_eq]; rw [associated_iff_normalizedFactors_eq_normalizedFactors hP0 hspan0]
  refine Multiset.

中文:
定理 理想.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne
  结论: {P : 理想 R}
  证明: by
  by_cases hP0 : P = ⊥
  · subst hP0
    rwa [eq_comm, span_singleton_eq_bot, ← mem_bot]
  have hspan0 : span {x} != ⊥ := mt Ideal.span_singleton_eq_bot.mp (hxP2 <| · ▸ zero_mem _)
  rw [← associated_iff_eq]; rw [associated_iff_normalizedFactors_eq_normalizedFactors hP0 hspan0]
  refine Multiset.

Depends on / 依赖: Ideal.count_normalizedFactor, Ideal.prime_of_isPrime, Ideal.span_singleton_eq_bot.mp, Multiset, Multiset.count_singleton, Multiset.ext, associated_iff_eq, associated_iff_normalizedFactors_eq_normalizedFactors, count_normalizedFactor, count_singleton, eq_comm, hspan0, irreducible, mem_bot, normalize_eq, normalizedFactors_irreducible, prime_of_isPrime, span_singleton_eq_bot, split_ifs, zero_mem
-/
theorem Ideal.eq_span_singleton_of_mem_of_notMem_sq_of_notMem_prime_ne {P : Ideal R}
    (hP : P.IsPrime) [IsDedekindDomain R] {x : R} (x_mem : x in P) (hxP2 : x ∉ P ^ 2)
    (hxQ : forall Q : Ideal R, IsPrime Q -> Q != P -> x ∉ Q) : P = Ideal.span {x} := by
  by_cases hP0 : P = ⊥
  · subst hP0
    rwa [eq_comm, span_singleton_eq_bot, ← mem_bot]
  have hspan0 : span {x} != ⊥ := mt Ideal.span_singleton_eq_bot.mp (hxP2 <| · ▸ zero_mem _)
  rw [← associated_iff_eq]; rw [associated_iff_normalizedFactors_eq_normalizedFactors hP0 hspan0]
  refine Multiset.ext' fun Q => ?_
  rw [normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible]; rw [normalize_eq]; rw [Multiset.count_singleton]
  symm
  split_ifs with hQ
  · subst hQ
    apply Ideal.count_normalizedFactors_eq <;> simpa
  by_cases hQp : IsPrime Q
  · apply Ideal.count_normalizedFactors_eq <;> simp [hxQ _ hQp hQ]
  exact Multiset.count_eq_zero.mpr fun hQi =>
hQp isPrime_of_prime irreducible_iff_prime.mp irreducible_of_normalized_factor _ hQi

-- Porting note: replaced three implicit coercions of `I` with explicit `(I : Submodule R A)`
/--
theorem `FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top` / 定理 `FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top`

English:
theorem FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
  statement: {R A : Type*}
  proof: by
  have hinv := I.mul_inv
  set J := Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v})
  have hJ : IsLocalization.coeSubmodule A J = ↑I * Submodule.span R {v} := by
    rw [coe_ext_iff]; rw [coe_mul]; rw [coe_one] at hinv
    apply Submodule.map_comap_eq_self
   

中文:
定理 FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
  结论: {R A : 类型}
  证明: by
  have hinv := I.mul_inv
  set J := Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v})
  have hJ : IsLocalization.coeSubmodule A J = ↑I * Submodule.span R {v} := by
    rw [coe_ext_iff]; rw [coe_mul]; rw [coe_one] at hinv
    apply Submodule.map_comap_eq_self
   

Depends on / 依赖: Algebra, Algebra.linearMap, I.mul_inv, IsLocalization, IsLocalization.coeSubmodule, IsLocalization.coeSubmodule_top, Submodule, Submodule.comap, Submodule.map_comap_eq_self, Submodule.mem_one, Submodule.one_eq_range, Submodule.span, Submodule.span_singleton_le_iff_mem, coeSubmodule, coeSubmodule_top, coe_ext_iff, coe_mul, coe_one, linearMap, map_comap_eq_self
-/
theorem FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {S : Submonoid R} [IsLocalization S A]
    (I : (FractionalIdeal S A)ˣ) {v : A} (hv : v in (↑I⁻¹ : FractionalIdeal S A))
    (h : Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v}) = ⊤) :
    Submodule.IsPrincipal (I : Submodule R A) := by
  have hinv := I.mul_inv
  set J := Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v})
  have hJ : IsLocalization.coeSubmodule A J = ↑I * Submodule.span R {v} := by
    rw [coe_ext_iff]; rw [coe_mul]; rw [coe_one] at hinv
    apply Submodule.map_comap_eq_self
    grw [← Submodule.one_eq_range, ← hinv, (Submodule.span_singleton_le_iff_mem _ _).2 hv]
  have : (1 : A) in ↑I * Submodule.span R {v} := by
    rw [← hJ]; rw [h]; rw [IsLocalization.coeSubmodule_top]; rw [Submodule.mem_one]
    exact ⟨1, (algebraMap R _).map_one⟩
  obtain ⟨w, hw, hvw⟩ := Submodule.mem_mul_span_singleton.1 this
  refine ⟨⟨w, ?_⟩⟩
  rw [← FractionalIdeal.coe_spanSingleton S]; rw [← inv_inv I]; rw [eq_comm]
  refine congr_arg coeToSubmodule (Units.eq_inv_of_mul_eq_one_left (le_antisymm ?_ ?_))
  · conv_rhs => rw [← hinv, mul_comm]
    grw [FractionalIdeal.spanSingleton_le_iff_mem.mpr hw]
  · rw [FractionalIdeal.one_le, ← hvw, mul_comm]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hv

/--
theorem `FractionalIdeal.isPrincipal.of_finite_maximals_of_inv` / 定理 `FractionalIdeal.isPrincipal.of_finite_maximals_of_inv`

English:
theorem FractionalIdeal.isPrincipal.of_finite_maximals_of_inv
  statement: {A : Type*} [CommRing A]
  proof: by
  have hinv' := hinv
  rw [coe_ext_iff]; rw [coe_mul] at hinv
  let s := hf.toFinset
  have := Classical.decEq (Ideal R)
  have coprime : forall M in s, forall M' in s.erase M, M ⊔ M' = ⊤ := by
    simp_rw [s, Finset.mem_erase, hf.mem_toFinset]
    rintro M hM M' ⟨hne, hM'⟩
    exact Ideal.IsMaxi

中文:
定理 FractionalIdeal.isPrincipal.of_finite_maximals_of_inv
  结论: {A : 类型} [交换环 A]
  证明: by
  have hinv' := hinv
  rw [coe_ext_iff]; rw [coe_mul] at hinv
  let s := hf.toFinset
  have := Classical.decEq (Ideal R)
  have coprime : forall M in s, forall M' in s.erase M, M ⊔ M' = ⊤ := by
    simp_rw [s, Finset.mem_erase, hf.mem_toFinset]
    rintro M hM M' ⟨hne, hM'⟩
    exact Ideal.IsMaxi

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.mem_erase, Ideal.IsMaximal.coprime_of_ne, Ideal.sup_iInf_eq_top, IsMaximal, coe_ext_iff, coe_mul, coprime, coprime_of_ne, hf.mem_toFinset, hf.toFinset, hne.symm, left_lt_sup, lt_top, lt_top.trans_eq, mem_erase, mem_toFinset, s.erase
-/
theorem FractionalIdeal.isPrincipal.of_finite_maximals_of_inv {A : Type*} [CommRing A]
    [Algebra R A] {S : Submonoid R} [IsLocalization S A] (hS : S <= R⁰)
    (hf : {I : Ideal R | I.IsMaximal}.Finite) (I I' : FractionalIdeal S A) (hinv : I * I' = 1) :
    Submodule.IsPrincipal (I : Submodule R A) := by
  have hinv' := hinv
  rw [coe_ext_iff]; rw [coe_mul] at hinv
  let s := hf.toFinset
  have := Classical.decEq (Ideal R)
  have coprime : forall M in s, forall M' in s.erase M, M ⊔ M' = ⊤ := by
    simp_rw [s, Finset.mem_erase, hf.mem_toFinset]
    rintro M hM M' ⟨hne, hM'⟩
    exact Ideal.IsMaximal.coprime_of_ne hM hM' hne.symm
  have nle : forall M in s, ¬⨅ M' in s.erase M, M' <= M := fun M hM =>
    left_lt_sup.1
      ((hf.mem_toFinset.1 hM).lt_top.trans_eq (Ideal.sup_iInf_eq_top <| coprime M hM).symm)
  have : forall M in s, exists a in I, exists b in I', a * b ∉ IsLocalization.coeSubmodule A M := by
    intro M hM; by_contra! h
    obtain ⟨x, hx, hxM⟩ :=
      SetLike.exists_of_lt
        ((IsLocalization.coeSubmodule_strictMono hS (hf.mem_toFinset.1 hM).lt_top).trans_eq
          hinv.symm)
    exact hxM (Submodule.mul_le.2 h hx)
  choose! a ha b hb hm using this
  choose! u hu hum using fun M hM => SetLike.not_le_iff_exists.1 (nle M hM)
  let v := ∑ M in s, u M • b M
have hv : v in I' := Submodule.sum_mem _ fun M hM => Submodule.smul_mem _ _ hb M hM
  refine
    FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
      (Units.mkOfMulEqOne I I' hinv') hv (of_not_not fun h => ?_)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ h
  replace hM := hf.mem_toFinset.2 hM
  have : forall a in I, forall b in I', exists c, algebraMap R _ c = a * b := by
    intro a ha b hb; have hi := hinv.le
    obtain ⟨c, -, hc⟩ := hi (Submodule.mul_mem_mul ha hb)
    exact ⟨c, hc⟩
  have hmem : a M * v in IsLocalization.coeSubmodule A M := by
    obtain ⟨c, hc⟩ := this _ (ha M hM) v hv
    refine IsLocalization.coeSubmodule_mono _ hJM ⟨c, ?_, hc⟩
    have := Submodule.mul_mem_mul (ha M hM) (Submodule.mem_span_singleton_self v)
    rwa [← hc] at this
  simp_rw [v, Finset.mul_sum, mul_smul_comm] at hmem
  rw [← s.add_sum_erase _ hM]; rw [Submodule.add_mem_iff_left] at hmem
  · refine hm M hM ?_
    obtain ⟨c, hc : algebraMap R A c = a M * b M⟩ := this _ (ha M hM) _ (hb M hM)
    rw [← hc] at hmem ⊢
    rw [Algebra.smul_def]; rw [← map_mul] at hmem
    obtain ⟨d, hdM, he⟩ := hmem
    rw [IsLocalization.injective _ hS he] at hdM
exact Submodule.mem_map_of_mem
((hf.mem_toFinset.1 hM).isPrime.mem_or_mem hdM).resolve_left hum M hM
  · refine Submodule.sum_mem _ fun M' hM' => ?_
    rw [Finset.mem_erase] at hM'
    obtain ⟨c, hc⟩ := this _ (ha M hM) _ (hb M' hM'.2)
    rw [← hc]; rw [Algebra.smul_def]; rw [← map_mul]
    specialize hu M' hM'.2
    simp_rw [Ideal.mem_iInf, Finset.mem_erase] at hu
exact Submodule.mem_map_of_mem M.mul_mem_right _ hu M ⟨hM'.1.symm, hM⟩

/--
theorem `Ideal.IsPrincipal.of_finite_maximals_of_isUnit` / 定理 `Ideal.IsPrincipal.of_finite_maximals_of_isUnit`

English:
theorem Ideal.IsPrincipal.of_finite_maximals_of_isUnit
  statement: (hf : {I : Ideal R | I.IsMaximal}.Finite)
  proof: (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
    (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
      (↑hI.unit⁻¹ : FractionalIdeal R⁰ (FractionRing R)) hI.unit.mul_inv)

中文:
定理 理想.是Principal.of_finite_maximals_of_isUnit
  结论: (hf : {I : 理想 R | I.是极大}.有限)
  证明: (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
    (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
      (↑hI.unit⁻¹ : FractionalIdeal R⁰ (FractionRing R)) hI.unit.mul_inv)

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.isPrincipal.of_finite_maximals_of_inv, IsLocalization, IsLocalization.coeSubmodule_isPrincipal, coeSubmodule_isPrincipal, hI.unit, hI.unit.mul_inv, isPrincipal, le_rfl, mul_inv, of_finite_maximals_of_inv
-/
theorem Ideal.IsPrincipal.of_finite_maximals_of_isUnit (hf : {I : Ideal R | I.IsMaximal}.Finite)
    {I : Ideal R} (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) : I.IsPrincipal :=
  (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
    (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
      (↑hI.unit⁻¹ : FractionalIdeal R⁰ (FractionRing R)) hI.unit.mul_inv)

/--
theorem `IsPrincipalIdealRing.of_finite_maximals` / 定理 `IsPrincipalIdealRing.of_finite_maximals`

English:
theorem IsPrincipalIdealRing.of_finite_maximals
  statement: [IsDedekindDomain R]
  proof: ⟨fun I => by
    obtain rfl | hI := eq_or_ne I ⊥
    · exact bot_isPrincipal
    apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit h
    exact .of_mul_eq_one _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩

中文:
定理 是主理想环.of_finite_maximals
  结论: [是Dedekind整环 R]
  证明: ⟨fun I => by
    obtain rfl | hI := eq_or_ne I ⊥
    · exact bot_isPrincipal
    apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit h
    exact .of_mul_eq_one _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coe_ideal_mul_inv, Ideal.IsPrincipal.of_finite_maximals_of_isUnit, IsPrincipal, bot_isPrincipal, coe_ideal_mul_inv, eq_or_ne, of_finite_maximals_of_isUnit, of_mul_eq_one
-/
theorem IsPrincipalIdealRing.of_finite_maximals [IsDedekindDomain R]
    (h : {I : Ideal R | I.IsMaximal}.Finite) : IsPrincipalIdealRing R :=
  ⟨fun I => by
    obtain rfl | hI := eq_or_ne I ⊥
    · exact bot_isPrincipal
    apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit h
    exact .of_mul_eq_one _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩

/--
theorem `IsPrincipalIdealRing.of_finite_primes` / 定理 `IsPrincipalIdealRing.of_finite_primes`

English:
theorem IsPrincipalIdealRing.of_finite_primes
  statement: [IsDedekindDomain R]
  proof: IsPrincipalIdealRing.of_finite_maximals h.subset fun _ hi => hi.isPrime

中文:
定理 是主理想环.of_finite_primes
  结论: [是Dedekind整环 R]
  证明: IsPrincipalIdealRing.of_finite_maximals h.subset fun _ hi => hi.isPrime

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.of_finite_maximals, h.subset, hi.isPrime, isPrime, of_finite_maximals, subset
-/
theorem IsPrincipalIdealRing.of_finite_primes [IsDedekindDomain R]
    (h : {I : Ideal R | I.IsPrime}.Finite) : IsPrincipalIdealRing R :=
IsPrincipalIdealRing.of_finite_maximals h.subset fun _ hi => hi.isPrime

section
variable [IsDedekindDomain R]
variable (S : Type*) [CommRing S]
variable [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S]
variable (p : Ideal R) (hp0 : p != ⊥) [IsPrime p]
variable {Sₚ : Type*} [CommRing Sₚ] [Algebra S Sₚ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [Algebra R Sₚ] [IsScalarTower R S Sₚ]
include hp0

/- The first hypothesis below follows from properties of the localization but is needed for the
second, so we leave it to the user to provide (automatically). -/
variable [IsDedekindDomain Sₚ]

/--
theorem `IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime` / 定理 `IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime`

English:
theorem IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime
  statement: [IsDomain S]
  proof: by
  have non_zero_div : Algebra.algebraMapSubmonoid S p.primeCompl <= S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      p.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime p) Sₚ := localizationAlgebra p.primeCompl S
  have : IsScalarTowe

中文:
定理 是Localization.OverPrime.mem_normalizedFactors_of_isPrime
  结论: [是整环 S]
  证明: by
  have non_zero_div : Algebra.algebraMapSubmonoid S p.primeCompl <= S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      p.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime p) Sₚ := localizationAlgebra p.primeCompl S
  have : IsScalarTowe

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, AtPrime, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsLocalization, IsLocalization.map_eq, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_eq, Localization, Localization.AtPrime, Submonoid, Submonoid.le_com, algebraMapSubmonoid, algebraMap_apply, algebraMap_injective, le_com, localizationAlgebra, map_eq
-/
theorem IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime [IsDomain S]
    {P : Ideal Sₚ} (hP : IsPrime P) (hP0 : P != ⊥) :
    P in normalizedFactors (Ideal.map (algebraMap R Sₚ) p) := by
  have non_zero_div : Algebra.algebraMapSubmonoid S p.primeCompl <= S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      p.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime p) Sₚ := localizationAlgebra p.primeCompl S
  have : IsScalarTower R (Localization.AtPrime p) Sₚ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R S]
      exact (IsLocalization.map_eq (T := Algebra.algebraMapSubmonoid S (primeCompl p))
        (Submonoid.le_comap_map _) x).symm
  obtain ⟨pid, p', ⟨hp'0, hp'p⟩, hpu⟩ :=
    (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime p)).mp
      (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp0 _)
  have : IsLocalRing.maximalIdeal (Localization.AtPrime p) != ⊥ := by
    rw [Submodule.ne_bot_iff] at hp0 ⊢
    obtain ⟨x, x_mem, x_ne⟩ := hp0
    exact
      ⟨algebraMap _ _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr x_mem,
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero x_ne)⟩
  rw [← Multiset.singleton_le]; rw [← normalize_eq P]; rw [←
    normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible]; rw [←
    dvd_iff_normalizedFactors_le_normalizedFactors hP0]; rw [dvd_iff_le]; rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime p) Sₚ]; rw [← Ideal.map_map]; rw [Localization.AtPrime.map_eq_maximalIdeal]; rw [Ideal.map_le_iff_le_comap]; rw [hpu (IsLocalRing.maximalIdeal _) ⟨this]; rw [_⟩]; rw [hpu (comap _ _) ⟨_]; rw [_⟩]
  · have : Algebra.IsIntegral (Localization.AtPrime p) Sₚ := ⟨isIntegral_localization⟩
    exact mt (Ideal.eq_bot_of_comap_eq_bot) hP0
  · exact Ideal.comap_isPrime (algebraMap (Localization.AtPrime p) Sₚ) P
  · exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  · rw [Ne, zero_eq_bot, Ideal.map_eq_bot_iff_of_injective]
    · assumption
    rw [IsScalarTower.algebraMap_eq R S Sₚ]
    exact
      (IsLocalization.injective Sₚ non_zero_div).comp (FaithfulSMul.algebraMap_injective _ _)

/--
theorem `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime` / 定理 `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime`

English:
theorem IsDedekindDomain.isPrincipalIdealRing_localization_over_prime
  given: [IsDomain S]
  proof: by
  let := Classical.decEq (Ideal Sₚ)
  let := Classical.decPred fun P : Ideal Sₚ => P.IsPrime
  refine
    IsPrincipalIdealRing.of_finite_primes
      (Set.Finite.ofFinset
        {P in {⊥} union (normalizedFactors (Ideal.map (algebraMap R Sₚ) p)).toFinset | P.IsPrime}
        fun P => ?_)
  rw [F

中文:
定理 是Dedekind整环.isPrincipalIdealRing_localization_over_prime
  条件: [是整环 S]
  证明: by
  let := Classical.decEq (Ideal Sₚ)
  let := Classical.decPred fun P : Ideal Sₚ => P.IsPrime
  refine
    IsPrincipalIdealRing.of_finite_primes
      (Set.Finite.ofFinset
        {P in {⊥} union (normalizedFactors (Ideal.map (algebraMap R Sₚ) p)).toFinset | P.IsPrime}
        fun P => ?_)
  rw [F

Depends on / 依赖: Classical, Classical.decEq, Classical.decPred, Finite, Finset, Finset.mem_filter, Finset.mem_singleton, Finset.mem_union, Ideal.map, IsLocalization, IsLocalization.OverPrime.mem_normalizedFactors_of_isPri, IsPrime, IsPrincipalIdealRing, IsPrincipalIdealRing.of_finite_primes, Multiset, Multiset.mem_toFinset, OverPrime, P.IsPrime, Set.Finite.ofFinset, Set.mem_ofPred
-/
theorem IsDedekindDomain.isPrincipalIdealRing_localization_over_prime [IsDomain S] :
    IsPrincipalIdealRing Sₚ := by
  let := Classical.decEq (Ideal Sₚ)
  let := Classical.decPred fun P : Ideal Sₚ => P.IsPrime
  refine
    IsPrincipalIdealRing.of_finite_primes
      (Set.Finite.ofFinset
        {P in {⊥} union (normalizedFactors (Ideal.map (algebraMap R Sₚ) p)).toFinset | P.IsPrime}
        fun P => ?_)
  rw [Finset.mem_filter]; rw [Finset.mem_union]; rw [Finset.mem_singleton]; rw [Set.mem_ofPred]; rw [Multiset.mem_toFinset]
  exact
    and_iff_right_of_imp fun hP =>
      or_iff_not_imp_left.mpr (IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime S p hp0 hP)
end

-- not an instance because this might cause a timeout
/--
theorem `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid` / 定理 `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`

English:
theorem IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
  proof: by
  refine .of_prime_ne_bot fun P hp hp₀ => ?_
  obtain ⟨x, hx₁, hx₂⟩ := hp.exists_mem_prime_of_ne_bot hp₀
  suffices Ideal.span {x} = P from this ▸ inferInstance
  have := (Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp
    P.span_si

中文:
定理 是主理想环.of_isDedekindDomain_of_uniqueFactorizationMonoid
  证明: by
  refine .of_prime_ne_bot fun P hp hp₀ => ?_
  obtain ⟨x, hx₁, hx₂⟩ := hp.exists_mem_prime_of_ne_bot hp₀
  suffices Ideal.span {x} = P from this ▸ inferInstance
  have := (Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp
    P.span_si

Depends on / 依赖: DimensionLeOne, Ideal.span, Ideal.span_singleton_prime, P.span_singleton_le_iff_mem.mpr, Ring.DimensionLeOne.prime_le_prime_iff_eq, exists_mem_prime_of_ne_bot, hp.exists_mem_prime_of_ne_bot, ne_zero, of_prime_ne_bot, prime_le_prime_iff_eq, span_singleton_le_iff_mem, span_singleton_prime
-/
theorem IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
    (R : Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    IsPrincipalIdealRing R := by
  refine .of_prime_ne_bot fun P hp hp₀ => ?_
  obtain ⟨x, hx₁, hx₂⟩ := hp.exists_mem_prime_of_ne_bot hp₀
  suffices Ideal.span {x} = P from this ▸ inferInstance
  have := (Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp
    P.span_singleton_le_iff_mem.mpr hx₁
