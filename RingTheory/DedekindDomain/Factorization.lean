/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# Factorization of ideals and fractional ideals of Dedekind domains

Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.

Similarly, every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`FractionalIdeal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `FractionalIdeal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `Ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`, where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization` : If `I` is a nonzero fractional ideal,
  `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product
  `∏_v v^(val_v(J) - val_v(a))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization'` : If `I` is a nonzero fractional
  ideal, then `I` is equal to the product `∏_v v^(val_v(I))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal` : For a nonzero `k = r/s ∈ K`,
  the fractional ideal `(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `FractionalIdeal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.
- `IsDedekindDomain.exists_sup_span_eq`: For all ideals `0 < I ≤ J`,
  there exists `a` such that `J = I + ⟨a⟩`.
- `Ideal.map_algebraMap_eq_finsetProd_pow`: if `p` is a maximal ideal, then the lift of `p`
  in an extension is the product of the primes over `p` to the power the ramification index.

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we define
`val_v(0) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `WithTop ℤ`.

## Tags
dedekind domain, fractional ideal, ideal, factorization
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Factorization of ideals of Dedekind domains -/

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

/--
Definition of `IsDedekindDomain.HeightOneSpectrum.maxPowDividing` / `IsDedekindDomain.HeightOneSpectrum.maxPowDividing` 的定义

English:
definition IsDedekindDomain.HeightOneSpectrum.maxPowDividing
  signature: (I : Ideal R)
  body: v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

中文:
定义 是Dedekind整环.高一谱.maxPowDividing
  签名: (I : 理想 R)
  定义体: v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

Depends on / 依赖: Associates, Associates.mk, asIdeal, factors, v.asIdeal
-/
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

open Associates in
/--
theorem `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count` / 定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count`

English:
theorem IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
  proof: by
  rw [maxPowDividing]; rw [factors_mk _ hI]; rw [count_some (irreducible_mk.mpr v.irreducible)]; rw [← Multiset.count_map_eq_count' _ _ Subtype.val_injective]; rw [map_subtype_coe_factors']; rw [factors_eq_normalizedFactors]; rw [← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]

中文:
定理 是Dedekind整环.高一谱.maxPowDividing_eq_pow_multiset_count
  证明: by
  rw [maxPowDividing]; rw [factors_mk _ hI]; rw [count_some (irreducible_mk.mpr v.irreducible)]; rw [← Multiset.count_map_eq_count' _ _ Subtype.val_injective]; rw [map_subtype_coe_factors']; rw [factors_eq_normalizedFactors]; rw [← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]

Depends on / 依赖: Multiset, Multiset.count_map_eq_count, Subtype, Subtype.val_injective, count_map_eq_count, count_some, factors_eq_normalizedFactors, factors_mk, irreducible, irreducible_mk, irreducible_mk.mpr, map_subtype_coe_factors, maxPowDividing, mk_injective, v.irreducible, val_injective
-/
theorem IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
    {I : Ideal R} (hI : I != 0) :
    maxPowDividing v I =
      v.asIdeal ^ Multiset.count v.asIdeal (normalizedFactors I) := by
  rw [maxPowDividing]; rw [factors_mk _ hI]; rw [count_some (irreducible_mk.mpr v.irreducible)]; rw [← Multiset.count_map_eq_count' _ _ Subtype.val_injective]; rw [map_subtype_coe_factors']; rw [factors_eq_normalizedFactors]; rw [← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]

/--
theorem `Ideal.finite_factors` / 定理 `Ideal.finite_factors`

English:
theorem Ideal.finite_factors
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  rw [← Set.finite_coe_iff]; rw [Set.coe_ofPred]
  have h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))

中文:
定理 理想.finite_factors
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  rw [← Set.finite_coe_iff]; rw [Set.coe_ofPred]
  have h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))

Depends on / 依赖: Finite, Finite.of_injective, HeightOneSpectrum, HeightOneSpectrum.ext, Set.coe_ofPred, Set.finite_coe_iff, Subtype, Subtype.coe_injective, asIdeal, coe_injective, coe_ofPred, finite_coe_iff, fintypeSubtypeDvd, h_fin, of_injective
-/
theorem Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
    {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite := by
  rw [← Set.finite_coe_iff]; rw [Set.coe_ofPred]
  have h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))

/--
theorem `Associates.finite_factors` / 定理 `Associates.finite_factors`

English:
theorem Associates.finite_factors
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  have h_supp : {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : Int) = 0} = {v : HeightOneSpectrum R | v.asIdeal ∣ I} := by
    ext v
    simp_rw [Int.natCast_eq_zero]
    exact Associates.count_ne_zero_iff_dvd hI v.irreducible
  rw [Filter.eventuall

中文:
定理 Associates.finite_factors
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  have h_supp : {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : Int) = 0} = {v : HeightOneSpectrum R | v.asIdeal ∣ I} := by
    ext v
    simp_rw [Int.natCast_eq_zero]
    exact Associates.count_ne_zero_iff_dvd hI v.irreducible
  rw [Filter.eventuall

Depends on / 依赖: Associates, Associates.count_ne_zero_iff_dvd, Associates.mk, Filter, Filter.eventually_cofinite, HeightOneSpectrum, Ideal.finite_factors, Int.natCast_eq_zero, asIdeal, count_ne_zero_iff_dvd, eventually_cofinite, factors, finite_factors, h_supp, irreducible, natCast_eq_zero, simp_rw, v.asIdeal, v.irreducible
-/
theorem Associates.finite_factors {I : Ideal R} (hI : I != 0) :
    forallᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) = 0 := by
  have h_supp : {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : Int) = 0} = {v : HeightOneSpectrum R | v.asIdeal ∣ I} := by
    ext v
    simp_rw [Int.natCast_eq_zero]
    exact Associates.count_ne_zero_iff_dvd hI v.irreducible
  rw [Filter.eventually_cofinite]; rw [h_supp]
  exact Ideal.finite_factors hI

namespace Ideal

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
  `v^(val_v(I))` is not the unit ideal. -/
@[fun_prop]
/--
theorem `hasFiniteMulSupport` / 定理 `hasFiniteMulSupport`

English:
theorem hasFiniteMulSupport
  given: {I : Ideal R} (hI : I != 0)
  proof: haveI h_subset : {v : HeightOneSpectrum R | v.maxPowDividing I != 1} subseteq
      {v : HeightOneSpectrum R |
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) != 0} := by
    intro v hv h_zero
    have hv' : v.maxPowDividing I = 1 := by
      rw [IsDedekindDomain.HeightOneS

中文:
定理 hasFiniteMulSupport
  条件: {I : 理想 R} (hI : I != 0)
  证明: haveI h_subset : {v : HeightOneSpectrum R | v.maxPowDividing I != 1} subseteq
      {v : HeightOneSpectrum R |
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) != 0} := by
    intro v hv h_zero
    have hv' : v.maxPowDividing I = 1 := by
      rw [IsDedekindDomain.HeightOneS

Depends on / 依赖: Associates, Associates.finite_factors, Associates.mk, Filter, Filter.eventually_cofinite.mp, Finite, Finite.subset, HeightOneSpectrum, Int.natCast_eq_zero.mp, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, asIdeal, eventually_cofinite, factors, finite_factors, h_subset, h_zero, maxPowDividing, natCast_eq_zero, pow_zero
-/
theorem hasFiniteMulSupport {I : Ideal R} (hI : I != 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I :=
  haveI h_subset : {v : HeightOneSpectrum R | v.maxPowDividing I != 1} subseteq
      {v : HeightOneSpectrum R |
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) != 0} := by
    intro v hv h_zero
    have hv' : v.maxPowDividing I = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]; rw [Int.natCast_eq_zero.mp h_zero]; rw [pow_zero _]
    exact hv hv'
  Finite.subset (Filter.eventually_cofinite.mp (Associates.finite_factors hI)) h_subset

@[deprecated (since := "2026-03-03")] alias finite_mulSupport := hasFiniteMulSupport

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
@[fun_prop]
/--
theorem `hasFiniteMulSupport_coe` / 定理 `hasFiniteMulSupport_coe`

English:
theorem hasFiniteMulSupport_coe
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact hasFiniteMulSupport hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_coe := hasFiniteMulSupport_coe

中文:
定理 hasFiniteMulSupport_coe
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact hasFiniteMulSupport hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_coe := hasFiniteMulSupport_coe

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeIdeal_eq_one, FractionalIdeal.coeIdeal_pow, HasFiniteMulSupport, coeIdeal_eq_one, coeIdeal_pow, hasFiniteMulSupport, mulSupport, simp_rw, zpow_natCast
-/
theorem hasFiniteMulSupport_coe {I : Ideal R} (hI : I != 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) := by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact hasFiniteMulSupport hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_coe := hasFiniteMulSupport_coe

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
@[fun_prop]
/--
theorem `hasFiniteMulSupport_inv` / 定理 `hasFiniteMulSupport_inv`

English:
theorem hasFiniteMulSupport_inv
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact hasFiniteMulSupport_coe hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_inv := hasFiniteMulSupport_inv

中文:
定理 hasFiniteMulSupport_inv
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact hasFiniteMulSupport_coe hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_inv := hasFiniteMulSupport_inv

Depends on / 依赖: HasFiniteMulSupport, hasFiniteMulSupport_coe, inv_eq_one, mulSupport, simp_rw, zpow_neg
-/
theorem hasFiniteMulSupport_inv {I : Ideal R} (hI : I != 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int)) := by
  rw [HasFiniteMulSupport]; rw [mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact hasFiniteMulSupport_coe hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_inv := hasFiniteMulSupport_inv

/--
theorem `finprod_not_dvd` / 定理 `finprod_not_dvd`

English:
theorem finprod_not_dvd
  given: (I : Ideal R) (hI : I != 0)
  proof: by
  classical
  have hf := hasFiniteMulSupport hI
  have h_ne_zero : v.maxPowDividing I != 0 := pow_ne_zero _ v.ne_bot
  rw [← mul_finprod_cond_ne v hf]; rw [pow_add]; rw [pow_one]; rw [finprod_cond_ne _ _ hf]
  intro h_contr
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.is

中文:
定理 finprod_not_dvd
  条件: (I : 理想 R) (hI : I != 0)
  证明: by
  classical
  have hf := hasFiniteMulSupport hI
  have h_ne_zero : v.maxPowDividing I != 0 := pow_ne_zero _ v.ne_bot
  rw [← mul_finprod_cond_ne v hf]; rw [pow_add]; rw [pow_one]; rw [finprod_cond_ne _ _ hf]
  intro h_contr
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.is

Depends on / 依赖: Ideal.prime_of_isPrime, Prime.dvd_, Prime.exists_mem_finset_dvd, asIdeal, classical, dvd_, exists_mem_finset_dvd, finprod_cond_ne, h_contr, h_ne_zero, hasFiniteMulSupport, hv_prime, hw_prime, isPrime, maxPowDividing, mul_dvd_mul_iff_left, mul_finprod_cond_ne, ne_bot, pow_add, pow_ne_zero
-/
theorem finprod_not_dvd (I : Ideal R) (hI : I != 0) :
    ¬v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors + 1) ∣
        ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I := by
  classical
  have hf := hasFiniteMulSupport hI
  have h_ne_zero : v.maxPowDividing I != 0 := pow_ne_zero _ v.ne_bot
  rw [← mul_finprod_cond_ne v hf]; rw [pow_add]; rw [pow_one]; rw [finprod_cond_ne _ _ hf]
  intro h_contr
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  obtain ⟨w, hw, hvw'⟩ :=
    Prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr)
  have hw_prime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hvw := Prime.dvd_of_dvd_pow hv_prime hvw'
  rw [Prime.dvd_prime_iff_associated hv_prime hw_prime]; rw [associated_iff_eq] at hvw
  exact (Finset.mem_erase.mp hw).1 (HeightOneSpectrum.ext hvw.symm)

end Ideal

/--
theorem `Associates.finprod_ne_zero` / 定理 `Associates.finprod_ne_zero`

English:
theorem Associates.finprod_ne_zero
  given: (I : Ideal R)
  proof: by
  classical
  rw [Associates.mk_ne_zero]; rw [finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero

中文:
定理 Associates.finprod_ne_zero
  条件: (I : 理想 R)
  证明: by
  classical
  rw [Associates.mk_ne_zero]; rw [finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero

Depends on / 依赖: Associates, Associates.mk_ne_zero, Finset, Finset.prod_ne_zero_iff, classical, finprod_def, mk_ne_zero, ne_bot, one_ne_zero, pow_ne_zero, prod_ne_zero_iff, split_ifs, v.ne_bot
-/
theorem Associates.finprod_ne_zero (I : Ideal R) :
    Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) != 0 := by
  classical
  rw [Associates.mk_ne_zero]; rw [finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero

namespace Ideal

/--
theorem `finprod_count` / 定理 `finprod_count`

English:
theorem finprod_count
  given: (I : Ideal R) (hI : I != 0)
  statement: (Associates.mk v.asIdeal).count
  proof: by
  have h_ne_zero := Associates.finprod_ne_zero I
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have h_dvd := finprod_mem_dvd v (hasFiniteMulSupport hI)
  have h_not_dvd := Ideal.finprod_not_dvd v I hI
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing

中文:
定理 finprod_count
  条件: (I : 理想 R) (hI : I != 0)
  结论: (Associates.mk v.asIdeal).count
  证明: by
  have h_ne_zero := Associates.finprod_ne_zero I
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have h_dvd := finprod_mem_dvd v (hasFiniteMulSupport hI)
  have h_not_dvd := Ideal.finprod_not_dvd v I hI
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing

Depends on / 依赖: Associates, Associates.dvd_eq_le, Associates.finprod_ne_zero, Associates.mk, Associates.mk_dvd_mk, Associates.mk_pow, Associates.prime_pow_dvd_iff_le, HeightOneSpectrum, Ideal.finprod_not_dvd, Irreducible, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, asIdeal, associates_irreducible, dvd_eq_le, finprod_mem_dvd, finprod_ne_zero, finprod_not_dvd, h_dvd, h_ne_zero
-/
theorem finprod_count (I : Ideal R) (hI : I != 0) : (Associates.mk v.asIdeal).count
    (Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I)).factors =
    (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  have h_ne_zero := Associates.finprod_ne_zero I
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have h_dvd := finprod_mem_dvd v (hasFiniteMulSupport hI)
  have h_not_dvd := Ideal.finprod_not_dvd v I hI
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h_dvd h_ne_zero h_not_dvd
  rw [← Associates.mk_dvd_mk] at h_dvd h_not_dvd
  simp only [Associates.dvd_eq_le] at h_dvd h_not_dvd
  rw [Associates.mk_pow]; rw [Associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd
  rw [not_le] at h_not_dvd
  apply Nat.eq_of_le_of_lt_succ h_dvd h_not_dvd

/--
theorem `finprod_heightOneSpectrum_factorization` / 定理 `finprod_heightOneSpectrum_factorization`

English:
theorem finprod_heightOneSpectrum_factorization
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  rw [← associated_iff_eq]; rw [← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv]; rw [Associates.irreducible_mk] at hv
  rw 

中文:
定理 finprod_heightOneSpectrum_factorization
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  rw [← associated_iff_eq]; rw [← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv]; rw [Associates.irreducible_mk] at hv
  rw 

Depends on / 依赖: Associates, Associates.eq_of_eq_counts, Associates.exists_rep, Associates.finprod_ne_zero, Associates.irreducible_mk, Associates.mk_eq_mk_iff_associated, Associates.mk_ne_zero.mpr, Ideal.finprod_count, Ideal.isPrime_of_prime, Irreducible, Irreducible.ne_zero, associated_iff_eq, eq_of_eq_counts, exists_rep, finprod_count, finprod_ne_zero, irreducible_iff_prime, irreducible_iff_prime.mp, irreducible_mk, isPrime_of_prime
-/
theorem finprod_heightOneSpectrum_factorization {I : Ideal R} (hI : I != 0) :
    ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I = I := by
  rw [← associated_iff_eq]; rw [← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv]; rw [Associates.irreducible_mk] at hv
  rw [← hJv]
  apply Ideal.finprod_count
    ⟨J, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hv), Irreducible.ne_zero hv⟩ I hI

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `iInf_maxPowDividing_eq` / 定理 `iInf_maxPowDividing_eq`

English:
theorem iInf_maxPowDividing_eq
  given: {I : Ideal R} (h0 : I != 0)
  proof: by
  nth_rw 2 [← Ideal.finprod_heightOneSpectrum_factorization h0]
  classical
  rw [finprod_def]; rw [dif_pos (Ideal.hasFiniteMulSupport h0)]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · ext x
    constructor
    · aesop
    · simp only [Finite.mem_toFinset, mem_mulSupport, one_eq_top, ne_eq,

中文:
定理 iInf_maxPowDividing_eq
  条件: {I : 理想 R} (h0 : I != 0)
  证明: by
  nth_rw 2 [← Ideal.finprod_heightOneSpectrum_factorization h0]
  classical
  rw [finprod_def]; rw [dif_pos (Ideal.hasFiniteMulSupport h0)]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · ext x
    constructor
    · aesop
    · simp only [Finite.mem_toFinset, mem_mulSupport, one_eq_top, ne_eq,

Depends on / 依赖: Finite, Finite.mem_toFinset, HeightOneSpectrum, Ideal.finprod_heightOneSpectrum_factorization, Ideal.hasFiniteMulSupport, Ideal.prod_eq_iInf_of_pairwise_isCoprime, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne, Submodule, Submodule.mem_iInf, classical, dif_pos, finprod_def, finprod_heightOneSpectrum_factorization, hasFiniteMulSupport, i.maxPowDividing, isCoprime_pow_of_ne, maxPowDividing, mem_iInf, mem_mulSupport
-/
theorem iInf_maxPowDividing_eq {I : Ideal R} (h0 : I != 0) :
    ⨅ i : HeightOneSpectrum R, i.maxPowDividing I = I := by
  nth_rw 2 [← Ideal.finprod_heightOneSpectrum_factorization h0]
  classical
  rw [finprod_def]; rw [dif_pos (Ideal.hasFiniteMulSupport h0)]; rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · ext x
    constructor
    · aesop
    · simp only [Finite.mem_toFinset, mem_mulSupport, one_eq_top, ne_eq, Submodule.mem_iInf]
      intro h i
      by_cases i.maxPowDividing I = ⊤ <;> simp_all
  · intro x hx y hy hxy
    apply IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne _ _ hxy

variable (K)

/--
theorem `finprod_heightOneSpectrum_factorization_coe` / 定理 `finprod_heightOneSpectrum_factorization_coe`

English:
theorem finprod_heightOneSpectrum_factorization_coe
  given: {I : Ideal R} (hI : I != 0)
  proof: by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]

中文:
定理 finprod_heightOneSpectrum_factorization_coe
  条件: {I : 理想 R} (hI : I != 0)
  证明: by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeIdeal_finprod, FractionalIdeal.coeIdeal_pow, HeightOneSpectrum, Ideal.finprod_heightOneSpectrum_factorization, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.maxPowDividing, coeIdeal_finprod, coeIdeal_pow, conv_rhs, finprod_heightOneSpectrum_factorization, le_refl, maxPowDividing, simp_rw, zpow_natCast
-/
theorem finprod_heightOneSpectrum_factorization_coe {I : Ideal R} (hI : I != 0) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int)) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]

end Ideal

/-! ### Factorization of fractional ideals of Dedekind domains -/

namespace FractionalIdeal

open Int IsLocalization

open Ideal in
/--
theorem `finprod_heightOneSpectrum_factorization` / 定理 `finprod_heightOneSpectrum_factorization`

English:
theorem finprod_heightOneSpectrum_factorization
  statement: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  proof: by
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have hJ := Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have ha := Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
  rw [haJ]; r

中文:
定理 finprod_heightOneSpectrum_factorization
  结论: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  证明: by
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have hJ := Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have ha := Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
  rw [haJ]; r

Depends on / 依赖: Ideal.finprod_heightOneSpectrum_factorization_coe, Ideal.span, coeIdeal_span_singleton, constant_factor_ne_zero, div_eq_mul_inv, div_spanSingleton, finprod_heightOneSpectrum_factorization_coe, finprod_inv_distrib, finprod_mul_distrib, fun_prop, hJ_ne_zero, ha_ne_zero, ideal_factor_ne_zero, simp_rw, zpow_neg
-/
theorem finprod_heightOneSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : Int) = I := by
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have hJ := Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have ha := Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
  rw [haJ]; rw [← div_spanSingleton]; rw [div_eq_mul_inv]; rw [← coeIdeal_span_singleton]; rw [← hJ]; rw [← ha]; rw [← finprod_inv_distrib]
  simp_rw [← zpow_neg]
  rw [← finprod_mul_distrib (by fun_prop) (by fun_prop)]
  apply finprod_congr
  intro v
  rw [← zpow_add₀ ((@coeIdeal_ne_zero R _ K _ _ _ _).mpr v.ne_bot)]; rw [sub_eq_add_neg]

/--
theorem `finprod_heightOneSpectrum_factorization_principal_fraction` / 定理 `finprod_heightOneSpectrum_factorization_principal_fraction`

English:
theorem finprod_heightOneSpectrum_factorization_principal_fraction
  given: {n : R} (hn : n != 0) (d : ↥R⁰)
  proof: by
  have hd_ne_zero : (algebraMap R K) (d : R) != 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : spanSingleton R⁰ (mk' K n d) != 0 := by
    rw [spanSingleton_ne_zero_iff]; rw [IsFractionRing.mk'_eq_div]; rw [ne_eq]; rw [div_eq_zero_iff]; rw [not

中文:
定理 finprod_heightOneSpectrum_factorization_principal_fraction
  条件: {n : R} (hn : n != 0) (d : ↥R⁰)
  证明: by
  have hd_ne_zero : (algebraMap R K) (d : R) != 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : spanSingleton R⁰ (mk' K n d) != 0 := by
    rw [spanSingleton_ne_zero_iff]; rw [IsFractionRing.mk'_eq_div]; rw [ne_eq]; rw [div_eq_zero_iff]; rw [not

Depends on / 依赖: Ideal.span, IsFractionRing, IsFractionRing.injective, IsFractionRing.mk, _eq_div, algebraMap, d.property, div_eq_zero_iff, hd_ne_zero, injective, map_ne_zero_iff, map_ne_zero_of_mem_nonZeroDivisors, ne_eq, not_or, property, spanSingleton, spanSingleton_ne_zero_iff
-/
theorem finprod_heightOneSpectrum_factorization_principal_fraction {n : R} (hn : n != 0) (d : ↥R⁰) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑d : R)}) :
        Ideal R)).factors : Int) = spanSingleton R⁰ (mk' K n d) := by
  have hd_ne_zero : (algebraMap R K) (d : R) != 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : spanSingleton R⁰ (mk' K n d) != 0 := by
    rw [spanSingleton_ne_zero_iff]; rw [IsFractionRing.mk'_eq_div]; rw [ne_eq]; rw [div_eq_zero_iff]; rw [not_or]
    exact ⟨(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hn, hd_ne_zero⟩
  have hI : spanSingleton R⁰ (mk' K n d) =
      spanSingleton R⁰ ((algebraMap R K) d)⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [coeIdeal_span_singleton]; rw [spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div]; rw [div_eq_mul_inv]; rw [mul_comm]
  exact finprod_heightOneSpectrum_factorization h0 hI

open Classical in
/--
theorem `finprod_heightOneSpectrum_factorization_principal` / 定理 `finprod_heightOneSpectrum_factorization_principal`

English:
theorem finprod_heightOneSpectrum_factorization_principal
  statement: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  proof: by
  set n : R := choose (exists_mk'_eq R⁰ k)
  set d : ↥R⁰ := choose (choose_spec (exists_mk'_eq R⁰ k))
  have hnd : mk' K n d = k := choose_spec (choose_spec (exists_mk'_eq R⁰ k))
  have hn0 : n != 0 := by
    by_contra h
    rw [← hnd]; rw [h]; rw [IsFractionRing.mk'_eq_div]; rw [map_zero]; rw [z

中文:
定理 finprod_heightOneSpectrum_factorization_principal
  结论: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  证明: by
  set n : R := choose (exists_mk'_eq R⁰ k)
  set d : ↥R⁰ := choose (choose_spec (exists_mk'_eq R⁰ k))
  have hnd : mk' K n d = k := choose_spec (choose_spec (exists_mk'_eq R⁰ k))
  have hn0 : n != 0 := by
    by_contra h
    rw [← hnd]; rw [h]; rw [IsFractionRing.mk'_eq_div]; rw [map_zero]; rw [z

Depends on / 依赖: IsFractionRing, IsFractionRing.mk, _eq_div, choose_spec, exists_mk, finprod_heightOneSpectrum_factorization_principal_fraction, map_zero, spanSingleton_zero, zero_div
-/
theorem finprod_heightOneSpectrum_factorization_principal {I : FractionalIdeal R⁰ K} (hI : I != 0)
    (k : K) (hk : I = spanSingleton R⁰ k) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {choose
          (exists_mk'_eq R⁰ k)} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(choose
          (choose_spec (exists_mk'_eq R⁰ k)) : ↥R⁰) : R)}) : Ideal R)).factors : Int) = I := by
  set n : R := choose (exists_mk'_eq R⁰ k)
  set d : ↥R⁰ := choose (choose_spec (exists_mk'_eq R⁰ k))
  have hnd : mk' K n d = k := choose_spec (choose_spec (exists_mk'_eq R⁰ k))
  have hn0 : n != 0 := by
    by_contra h
    rw [← hnd]; rw [h]; rw [IsFractionRing.mk'_eq_div]; rw [map_zero]; rw [zero_div]; rw [spanSingleton_zero] at hk
    exact hI hk
  rw [finprod_heightOneSpectrum_factorization_principal_fraction hn0 d]; rw [hk]; rw [hnd]

variable (K)

open Classical in
/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: (I : FractionalIdeal R⁰ K)
  body: dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.spa

中文:
定义 count
  签名: (I : FractionalIdeal R⁰ K)
  定义体: dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.spa

Depends on / 依赖: Associates, Associates.mk, Ideal.span, asIdeal, choose_spec, exists_eq_spanSingleton_mul, factors, v.asIdeal
-/
def count (I : FractionalIdeal R⁰ K) : Int :=
  dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : Int)

/--
lemma `count_zero` / 引理 `count_zero`

English:
lemma count_zero
  statement: count K v (0 : FractionalIdeal R⁰ K) = 0
  proof: by simp only [count, dif_pos]

中文:
引理 count_zero
  结论: count K v (0 : FractionalIdeal R⁰ K) = 0
  证明: by simp only [count, dif_pos]

Depends on / 依赖: dif_pos
-/
lemma count_zero : count K v (0 : FractionalIdeal R⁰ K) = 0 := by simp only [count, dif_pos]

open Classical in
/--
lemma `count_ne_zero` / 引理 `count_ne_zero`

English:
lemma count_ne_zero
  given: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  proof: by
  simp only [count, dif_neg hI]

中文:
引理 count_ne_zero
  条件: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  证明: by
  simp only [count, dif_neg hI]

Depends on / 依赖: dif_neg
-/
lemma count_ne_zero {I : FractionalIdeal R⁰ K} (hI : I != 0) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk
      (choose (choose_spec (exists_eq_spanSingleton_mul I)))).factors -
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {choose (exists_eq_spanSingleton_mul I)})).factors : Int) := by
  simp only [count, dif_neg hI]

open Classical in
/--
theorem `count_well_defined` / 定理 `count_well_defined`

English:
theorem count_well_defined
  statement: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  proof: by
  set a₁ := choose (exists_eq_spanSingleton_mul I)
  set J₁ := choose (choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ != 0 := (choose_spec

中文:
定理 count_well_defined
  结论: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  证明: by
  set a₁ := choose (exists_eq_spanSingleton_mul I)
  set J₁ := choose (choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ != 0 := (choose_spec

Depends on / 依赖: Ideal.span, algebraMap, choose_spec, constant_factor_ne_zero, exists_eq_spanSingleton_mul, h_J_ne_zero, h_aJ, h_a_ne_zero, ideal_factor_ne_zero, spanSingleton
-/
theorem count_well_defined {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
    {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : Int) := by
  set a₁ := choose (exists_eq_spanSingleton_mul I)
  set J₁ := choose (choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ != 0 := (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).1
  have h_J₁_ne_zero : J₁ != 0 := ideal_factor_ne_zero hI h_a₁J₁
  have h_a_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI h_aJ
  have h_J_ne_zero : J != 0 := ideal_factor_ne_zero hI h_aJ
  have h_a₁' : spanSingleton R⁰ ((algebraMap R K) a₁) != 0 := by
    rw [ne_eq]; rw [spanSingleton_eq_zero_iff]; rw [← (algebraMap R K).map_zero]; rw [Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    exact h_a₁_ne_zero
  have h_a' : spanSingleton R⁰ ((algebraMap R K) a) != 0 := by
    rw [ne_eq]; rw [spanSingleton_eq_zero_iff]; rw [← (algebraMap R K).map_zero]; rw [Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    rw [ne_eq]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot] at h_a_ne_zero
    exact h_a_ne_zero
  have hv : Irreducible (Associates.mk v.asIdeal) := by
    exact Associates.irreducible_mk.mpr v.irreducible
  rw [h_a₁J₁]; rw [← div_spanSingleton]; rw [← div_spanSingleton]; rw [div_eq_div_iff h_a₁' h_a']; rw [← coeIdeal_span_singleton]; rw [← coeIdeal_span_singleton]; rw [← coeIdeal_mul]; rw [← coeIdeal_mul] at h_aJ
  rw [count]; rw [dif_neg hI]; rw [sub_eq_sub_iff_add_eq_add]; rw [← natCast_add]; rw [← natCast_add]; rw [natCast_inj]; rw [← Associates.count_mul _ _ hv]; rw [← Associates.count_mul _ _ hv]; rw [Associates.mk_mul_mk]; rw [Associates.mk_mul_mk]; rw [coeIdeal_injective h_aJ]
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h_a₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_a_ne_zero

/--
theorem `count_mul` / 定理 `count_mul`

English:
theorem count_mul
  given: {I I' : FractionalIdeal R⁰ K} (hI : I != 0) (hI' : I' != 0)
  proof: by
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) != 0 := by
    rw [ne_eq]; rw [Associates.mk_eq_zero]; rw [Ideal.zero_eq_bot]; rw [Ideal.sp

中文:
定理 count_mul
  条件: {I I' : FractionalIdeal R⁰ K} (hI : I != 0) (hI' : I' != 0)
  证明: by
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) != 0 := by
    rw [ne_eq]; rw [Associates.mk_eq_zero]; rw [Ideal.zero_eq_bot]; rw [Ideal.sp

Depends on / 依赖: Associates, Associates.mk, Associates.mk_eq_zero, Associates.mk_ne_zero.mpr, Ideal.span, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, Irreducible, _ne_zero, asIdeal, associates_irreducible, exists_eq_spanSingleton_mul, hJ_ne_zero, ha_ne_zero, ideal_factor_ne_zero, mk_eq_zero, mk_ne_zero, ne_eq, span_singleton_eq_bot, v.asIdeal
-/
theorem count_mul {I I' : FractionalIdeal R⁰ K} (hI : I != 0) (hI' : I' != 0) :
    count K v (I * I') = count K v I + count K v I' := by
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) != 0 := by
    rw [ne_eq]; rw [Associates.mk_eq_zero]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]; exact ha
  have hJ_ne_zero : Associates.mk J != 0 := Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI haJ)
  obtain ⟨a', J', ha', haJ'⟩ := exists_eq_spanSingleton_mul I'
  have ha'_ne_zero : Associates.mk (Ideal.span {a'} : Ideal R) != 0 := by
    rw [ne_eq]; rw [Associates.mk_eq_zero]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]; exact ha'
  have hJ'_ne_zero : Associates.mk J' != 0 :=
    Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI' haJ')
  have h_prod : I * I' = spanSingleton R⁰ ((algebraMap R K) (a * a'))⁻¹ * ↑(J * J') := by
    rw [haJ]; rw [haJ']; rw [mul_assoc]; rw [mul_comm (J : FractionalIdeal R⁰ K)]; rw [mul_assoc]; rw [← mul_assoc]; rw [spanSingleton_mul_spanSingleton]; rw [coeIdeal_mul]; rw [map_mul]; rw [mul_inv]; rw [mul_comm (J : FractionalIdeal R⁰ K)]
  rw [count_well_defined K v hI haJ]; rw [count_well_defined K v hI' haJ']; rw [count_well_defined K v (mul_ne_zero hI hI') h_prod]; rw [← Associates.mk_mul_mk]; rw [Associates.count_mul hJ_ne_zero hJ'_ne_zero hv]; rw [← Ideal.span_singleton_mul_span_singleton]; rw [← Associates.mk_mul_mk]; rw [Associates.count_mul ha_ne_zero ha'_ne_zero hv]
  push_cast
  ring

/--
theorem `count_mul'` / 定理 `count_mul'`

English:
theorem count_mul'
  given: (I I' : FractionalIdeal R⁰ K) [Decidable (I != 0 ∧ I' != 0)]
  proof: by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · rw [← mul_ne_zero_iff, not_ne_iff] at h
    rw [h]; rw [count_zero]

中文:
定理 count_mul'
  条件: (I I' : FractionalIdeal R⁰ K) [可判定 (I != 0 ∧ I' != 0)]
  证明: by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · rw [← mul_ne_zero_iff, not_ne_iff] at h
    rw [h]; rw [count_zero]

Depends on / 依赖: count_mul, count_zero, mul_ne_zero_iff, not_ne_iff, split_ifs
-/
theorem count_mul' (I I' : FractionalIdeal R⁰ K) [Decidable (I != 0 ∧ I' != 0)] :
    count K v (I * I') = if I != 0 ∧ I' != 0 then count K v I + count K v I' else 0 := by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · rw [← mul_ne_zero_iff, not_ne_iff] at h
    rw [h]; rw [count_zero]

/--
theorem `count_one` / 定理 `count_one`

English:
theorem count_one
  statement: count K v (1 : FractionalIdeal R⁰ K) = 0
  proof: by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one]; rw [Ideal.one_eq_top]; rw [coeIdeal_top]; rw [mul_one]; rw [inv_one]; rw [spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1]; rw [Ideal.spa

中文:
定理 count_one
  结论: count K v (1 : FractionalIdeal R⁰ K) = 0
  证明: by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one]; rw [Ideal.one_eq_top]; rw [coeIdeal_top]; rw [mul_one]; rw [inv_one]; rw [spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1]; rw [Ideal.spa

Depends on / 依赖: FractionalIdeal, Ideal.one_eq_top, Ideal.span_singleton_one, algebraMap, coeIdeal_top, count_well_defined, inv_one, map_one, mul_one, one_eq_top, one_ne_zero, spanSingleton, spanSingleton_one, span_singleton_one, sub_self
-/
theorem count_one : count K v (1 : FractionalIdeal R⁰ K) = 0 := by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one]; rw [Ideal.one_eq_top]; rw [coeIdeal_top]; rw [mul_one]; rw [inv_one]; rw [spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1]; rw [Ideal.span_singleton_one]; rw [Ideal.one_eq_top]; rw [sub_self]

/--
theorem `count_prod` / 定理 `count_prod`

English:
theorem count_prod
  given: {ι} (s : Finset ι) (I : ι -> FractionalIdeal R⁰ K) (hS : forall i in s, I i != 0)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, count_one]
  | insert i s hi hrec =>
    have hS' : forall i in s, I i != 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i in s, I i != 0 := Finset.prod_ne_zero_iff.mp

中文:
定理 count_prod
  条件: {ι} (s : 有限集 ι) (I : ι -> FractionalIdeal R⁰ K) (hS : 对任意 i in s, I i != 0)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, count_one]
  | insert i s hi hrec =>
    have hS' : forall i in s, I i != 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i in s, I i != 0 := Finset.prod_ne_zero_iff.mp

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_empty, Finset.prod_insert, Finset.prod_ne_zero_iff.mpr, Finset.sum_empty, Finset.sum_insert, classical, count_mul, count_one, insert, mem_insert_of_mem, mem_insert_self, prod_empty, prod_insert, prod_ne_zero_iff, sum_empty, sum_insert
-/
theorem count_prod {ι} (s : Finset ι) (I : ι -> FractionalIdeal R⁰ K) (hS : forall i in s, I i != 0) :
    count K v (∏ i in s, I i) = ∑ i in s, count K v (I i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, count_one]
  | insert i s hi hrec =>
    have hS' : forall i in s, I i != 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i in s, I i != 0 := Finset.prod_ne_zero_iff.mpr hS'
    have hi0 : I i != 0 := hS i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi]; rw [Finset.sum_insert hi]; rw [count_mul K v hi0 hS0]; rw [hrec hS']

/--
theorem `count_pow` / 定理 `count_pow`

English:
theorem count_pow
  given: (n : Nat) (I : FractionalIdeal R⁰ K)
  proof: by
  induction n with
  | zero => rw [pow_zero, ofNat_zero, zero_mul, count_one]
  | succ n h =>
    classical rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n != 0 ∧ I != 0) := by order
      rw [if_neg h_neg]; rw [hI]; rw [count_zero]; rw [mul_zero]
    · rw [if_pos (An

中文:
定理 count_pow
  条件: (n : 自然数) (I : FractionalIdeal R⁰ K)
  证明: by
  induction n with
  | zero => rw [pow_zero, ofNat_zero, zero_mul, count_one]
  | succ n h =>
    classical rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n != 0 ∧ I != 0) := by order
      rw [if_neg h_neg]; rw [hI]; rw [count_zero]; rw [mul_zero]
    · rw [if_pos (An

Depends on / 依赖: And.intro, Nat.cast_add, Nat.cast_one, cast_add, cast_one, classical, count_mul, count_one, count_zero, h_neg, if_neg, if_pos, mul_zero, ofNat_zero, pow_ne_zero, pow_succ, pow_zero, zero_mul
-/
theorem count_pow (n : Nat) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  induction n with
  | zero => rw [pow_zero, ofNat_zero, zero_mul, count_one]
  | succ n h =>
    classical rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n != 0 ∧ I != 0) := by order
      rw [if_neg h_neg]; rw [hI]; rw [count_zero]; rw [mul_zero]
    · rw [if_pos (And.intro (pow_ne_zero n hI) hI), h, Nat.cast_add,
        Nat.cast_one]
      ring

/--
theorem `count_self` / 定理 `count_self`

English:
theorem count_self
  statement: count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1
  proof: by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) != 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have h

中文:
定理 count_self
  结论: count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1
  证明: by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) != 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have h

Depends on / 依赖: Associates, Associates.count_self, Associates.mk, FractionalIdeal, Ideal.one_eq_top, Ideal.span_singleton_one, Irreducible, algebraMap, asIdeal, associates_irreducible, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, count_self, count_well_defined, h_self, hv_irred, inv_one, map_one, ne_bot, one_eq_top
-/
theorem count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) != 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have hv_irred : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  rw [count_well_defined K v hv h_self]; rw [Associates.count_self hv_irred]; rw [Ideal.span_singleton_one]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero hv_irred]; rw [ofNat_zero]; rw [sub_zero]; rw [ofNat_one]

/--
theorem `count_pow_self` / 定理 `count_pow_self`

English:
theorem count_pow_self
  given: (n : Nat)
  proof: by
  rw [count_pow]; rw [count_self]; rw [mul_one]

中文:
定理 count_pow_self
  条件: (n : 自然数)
  证明: by
  rw [count_pow]; rw [count_self]; rw [mul_one]

Depends on / 依赖: count_pow, count_self, mul_one
-/
theorem count_pow_self (n : Nat) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_pow]; rw [count_self]; rw [mul_one]

/--
theorem `count_neg_zpow` / 定理 `count_neg_zpow`

English:
theorem count_neg_zpow
  given: (n : Int) (I : FractionalIdeal R⁰ K)
  proof: by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀

中文:
定理 count_neg_zpow
  条件: (n : 整数) (I : FractionalIdeal R⁰ K)
  证明: by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀

Depends on / 依赖: count_mul, count_one, count_zero, eq_neg_iff_add_eq_zero, neg_add_cancel, neg_ne_zero, neg_ne_zero.mpr, neg_zero, zero_zpow, zpow_ne_zero, zpow_zero
-/
theorem count_neg_zpow (n : Int) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ (-n)) = -count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_cancel, zpow_zero]
    exact count_one K v

/--
theorem `count_inv` / 定理 `count_inv`

English:
theorem count_inv
  given: (I : FractionalIdeal R⁰ K)
  proof: by
  rw [← zpow_neg_one]; rw [count_neg_zpow K v (1 : Int) I]; rw [zpow_one]

中文:
定理 count_inv
  条件: (I : FractionalIdeal R⁰ K)
  证明: by
  rw [← zpow_neg_one]; rw [count_neg_zpow K v (1 : Int) I]; rw [zpow_one]

Depends on / 依赖: count_neg_zpow, zpow_neg_one, zpow_one
-/
theorem count_inv (I : FractionalIdeal R⁰ K) :
    count K v (I⁻¹) = -count K v I := by
  rw [← zpow_neg_one]; rw [count_neg_zpow K v (1 : Int) I]; rw [zpow_one]

/--
theorem `count_zpow` / 定理 `count_zpow`

English:
theorem count_zpow
  given: (n : Int) (I : FractionalIdeal R⁰ K)
  proof: by
  obtain n | n := n
  · rw [ofNat_eq_natCast, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_eq, count_neg_zpow, ← Int.natCast_succ, zpow_natCast, count_pow]
    ring

中文:
定理 count_zpow
  条件: (n : 整数) (I : FractionalIdeal R⁰ K)
  证明: by
  obtain n | n := n
  · rw [ofNat_eq_natCast, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_eq, count_neg_zpow, ← Int.natCast_succ, zpow_natCast, count_pow]
    ring

Depends on / 依赖: Int.natCast_succ, count_neg_zpow, count_pow, natCast_succ, negSucc_eq, ofNat_eq_natCast, zpow_natCast
-/
theorem count_zpow (n : Int) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  obtain n | n := n
  · rw [ofNat_eq_natCast, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_eq, count_neg_zpow, ← Int.natCast_succ, zpow_natCast, count_pow]
    ring

/--
theorem `count_zpow_self` / 定理 `count_zpow_self`

English:
theorem count_zpow_self
  given: (n : Int)
  proof: by
  rw [count_zpow]; rw [count_self]; rw [mul_one]

中文:
定理 count_zpow_self
  条件: (n : 整数)
  证明: by
  rw [count_zpow]; rw [count_self]; rw [mul_one]

Depends on / 依赖: count_self, count_zpow, mul_one
-/
theorem count_zpow_self (n : Int) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_zpow]; rw [count_self]; rw [mul_one]

/--
theorem `count_maximal_coprime` / 定理 `count_maximal_coprime`

English:
theorem count_maximal_coprime
  given: {w : HeightOneSpectrum R} (hw : w != v)
  proof: by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) != 0 :=
    coeIdeal_ne_zero.mpr w.ne

中文:
定理 count_maximal_coprime
  条件: {w : 高一谱 R} (hw : w != v)
  证明: by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) != 0 :=
    coeIdeal_ne_zero.mpr w.ne

Depends on / 依赖: Associates, Associates.mk, FractionalIdeal, Irreducible, algebraMap, asIdeal, associates_irreducible, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, count_well_defined, hw_f, hw_fact, hw_ne_zero, inv_one, map_one, ne_bot, one_mul, spanSingleton, spanSingleton_one, v.asIdeal
-/
theorem count_maximal_coprime {w : HeightOneSpectrum R} (hw : w != v) :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0 := by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one]; rw [inv_one]; rw [spanSingleton_one]; rw [one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) != 0 :=
    coeIdeal_ne_zero.mpr w.ne_bot
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  have hw' : Irreducible (Associates.mk w.asIdeal) := by apply w.associates_irreducible
  rw [count_well_defined K v hw_ne_zero hw_fact]; rw [Ideal.span_singleton_one]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero hv]; rw [ofNat_zero]; rw [sub_zero]; rw [natCast_eq_zero]; rw [← pow_one (Associates.mk w.asIdeal)]; rw [Associates.factors_prime_pow hw']; rw [Associates.count_some hv]; rw [Multiset.replicate_one]; rw [Multiset.count_eq_zero]; rw [Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated]; rw [associated_iff_eq]; rw [← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw

/--
theorem `count_maximal` / 定理 `count_maximal`

English:
theorem count_maximal
  given: (w : HeightOneSpectrum R) [Decidable (w = v)]
  proof: by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

中文:
定理 count_maximal
  条件: (w : 高一谱 R) [可判定 (w = v)]
  证明: by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

Depends on / 依赖: count_maximal_coprime, count_self, split_ifs
-/
theorem count_maximal (w : HeightOneSpectrum R) [Decidable (w = v)] :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = if w = v then 1 else 0 := by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

/--
theorem `count_finprod_coprime` / 定理 `count_finprod_coprime`

English:
theorem count_finprod_coprime
  given: (exps : HeightOneSpectrum R -> Int)
  proof: by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    classical
    by_cases h : I != 0 ∧ I' != 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow]; rw [count_maximal_cop

中文:
定理 count_finprod_coprime
  条件: (exps : 高一谱 R -> 整数)
  证明: by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    classical
    by_cases h : I != 0 ∧ I' != 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow]; rw [count_maximal_cop

Depends on / 依赖: add_zero, classical, count_maximal_coprime, count_mul, count_one, count_zpow, finprod_mem_induction, if_neg, if_pos, mul_zero
-/
theorem count_finprod_coprime (exps : HeightOneSpectrum R -> Int) :
    count K v (∏ᶠ (w : HeightOneSpectrum R) (_ : w != v),
      (w.asIdeal : (FractionalIdeal R⁰ K)) ^ exps w) = 0 := by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    classical
    by_cases h : I != 0 ∧ I' != 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow]; rw [count_maximal_coprime K v hw]; rw [mul_zero]

/--
theorem `count_finsuppProd` / 定理 `count_finsuppProd`

English:
theorem count_finsuppProd
  given: (exps : HeightOneSpectrum R ->₀ Int)
  proof: by
  rw [Finsupp.prod]; rw [count_prod]
  · classical simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm Int 0, imp_self]
  · exact fun v hv => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

中文:
定理 count_finsuppProd
  条件: (exps : 高一谱 R ->₀ 整数)
  证明: by
  rw [Finsupp.prod]; rw [count_prod]
  · classical simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm Int 0, imp_self]
  · exact fun v hv => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

Depends on / 依赖: Finset, Finset.sum_ite_eq, Finsupp, Finsupp.prod, classical, coeIdeal_ne_zero, coeIdeal_ne_zero.mpr, count_maximal, count_prod, count_zpow, eq_comm, exps.mem_support_iff, imp_self, ite_eq_right_iff, ite_not, mem_support_iff, mul_ite, mul_one, mul_zero, ne_bot
-/
theorem count_finsuppProd (exps : HeightOneSpectrum R ->₀ Int) :
    count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v := by
  rw [Finsupp.prod]; rw [count_prod]
  · classical simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm Int 0, imp_self]
  · exact fun v hv => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `count_finprod` / 定理 `count_finprod`

English:
theorem count_finprod
  statement: (exps : HeightOneSpectrum R -> Int)
  proof: by
  convert! count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _ => h_exps.mem_toFinset))
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := h_exps.toFinset)]; rw [Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport]; rw [h]; rw [zpow_zero] at hv

中文:
定理 count_finprod
  结论: (exps : 高一谱 R -> 整数)
  证明: by
  convert! count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _ => h_exps.mem_toFinset))
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := h_exps.toFinset)]; rw [Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport]; rw [h]; rw [zpow_zero] at hv

Depends on / 依赖: Eq.refl, Finite, Finite.coe_toFinset, Finsupp, Finsupp.mk, Finsupp.prod, coe_toFinset, convert, count_finsuppProd, finprod_eq_finsetProd_of_mulSupport_subset, h_exps, h_exps.mem_toFinset, h_exps.toFinset, mem_mulSupport, mem_toFinset, toFinset, zpow_zero
-/
theorem count_finprod (exps : HeightOneSpectrum R -> Int)
    (h_exps : forallᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v := by
  convert! count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _ => h_exps.mem_toFinset))
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := h_exps.toFinset)]; rw [Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport]; rw [h]; rw [zpow_zero] at hv
    exact hv (Eq.refl 1)

/--
theorem `count_coe` / 定理 `count_coe`

English:
theorem count_coe
  given: {J : Ideal R} (hJ : J != 0)
  proof: by
  rw [count_well_defined K (J := J) (a := 1)]; rw [Ideal.span_singleton_one]; rw [sub_eq_self]; rw [Nat.cast_eq_zero]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · sim

中文:
定理 count_coe
  条件: {J : 理想 R} (hJ : J != 0)
  证明: by
  rw [count_well_defined K (J := J) (a := 1)]; rw [Ideal.span_singleton_one]; rw [sub_eq_self]; rw [Nat.cast_eq_zero]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · sim

Depends on / 依赖: Associates, Associates.count_zero, Associates.factors_one, Associates.mk_one, Ideal.one_eq_top, Ideal.span_singleton_one, Nat.cast_eq_zero, associates_irreducible, cast_eq_zero, coeIdeal_eq_zero, count_well_defined, count_zero, factors_one, inv_one, map_one, mk_one, ne_eq, one_eq_top, one_mul, spanSingleton_one
-/
theorem count_coe {J : Ideal R} (hJ : J != 0) :
    count K v J = (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  rw [count_well_defined K (J := J) (a := 1)]; rw [Ideal.span_singleton_one]; rw [sub_eq_self]; rw [Nat.cast_eq_zero]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · simp only [map_one, inv_one, spanSingleton_one, one_mul]

/--
theorem `count_coe_nonneg` / 定理 `count_coe_nonneg`

English:
theorem count_coe_nonneg
  given: (J : Ideal R)
  statement: 0 <= count K v J
  proof: by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · classical simp only [count_coe K v hJ, Nat.cast_nonneg]

中文:
定理 count_coe_nonneg
  条件: (J : 理想 R)
  结论: 0 <= count K v J
  证明: by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · classical simp only [count_coe K v hJ, Nat.cast_nonneg]

Depends on / 依赖: Nat.cast_nonneg, Submodule, Submodule.zero_eq_bot, cast_nonneg, classical, coeIdeal_bot, count_coe, count_zero, le_refl, zero_eq_bot
-/
theorem count_coe_nonneg (J : Ideal R) : 0 <= count K v J := by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · classical simp only [count_coe K v hJ, Nat.cast_nonneg]

/--
theorem `count_mono` / 定理 `count_mono`

English:
theorem count_mono
  given: {I J} (hI : I != 0) (h : I <= J)
  statement: count K v J <= count K v I
  proof: by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := mul_le_mul_right h J⁻¹
  rw [inv_mul_cancel₀ hJ]; rw [FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I]; rw [← hJ']; rw [count_mul K

中文:
定理 count_mono
  条件: {I J} (hI : I != 0) (h : I <= J)
  结论: count K v J <= count K v I
  证明: by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := mul_le_mul_right h J⁻¹
  rw [inv_mul_cancel₀ hJ]; rw [FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I]; rw [← hJ']; rw [count_mul K

Depends on / 依赖: FractionalIdeal, FractionalIdeal.le_one_iff_exists_coeIdeal, FractionalIdeal.le_zero_iff.mp, count_coe_nonneg, count_mul, h.trans, hJ.le, inv_ne_zero, le_add_iff_nonneg_right, le_one_iff_exists_coeIdeal, le_zero_iff, mul_le_mul_right, mul_ne_zero
-/
theorem count_mono {I J} (hI : I != 0) (h : I <= J) : count K v J <= count K v I := by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := mul_le_mul_right h J⁻¹
  rw [inv_mul_cancel₀ hJ]; rw [FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I]; rw [← hJ']; rw [count_mul K v hJ]; rw [le_add_iff_nonneg_right]
  · exact count_coe_nonneg K v J'
  · exact hJ' ▸ mul_ne_zero (inv_ne_zero hJ) hI

/--
theorem `finprod_heightOneSpectrum_factorization'` / 定理 `finprod_heightOneSpectrum_factorization'`

English:
theorem finprod_heightOneSpectrum_factorization'
  given: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  proof: by
  have h := (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

中文:
定理 finprod_heightOneSpectrum_factorization'
  条件: {I : FractionalIdeal R⁰ K} (hI : I != 0)
  证明: by
  have h := (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, congr_arg, conv_rhs, count_ne_zero, exists_eq_spanSingleton_mul, finprod_congr, finprod_heightOneSpectrum_factorization
-/
theorem finprod_heightOneSpectrum_factorization' {I : FractionalIdeal R⁰ K} (hI : I != 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (count K v I) = I := by
  have h := (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

variable {K}

/--
theorem `finite_factors'` / 定理 `finite_factors'`

English:
theorem finite_factors'
  statement: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  proof: by
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : Int) -
      ↑((Associates.mk v.asIdeal).count (Associ

中文:
定理 finite_factors'
  结论: {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
  证明: by
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : Int) -
      ↑((Associates.mk v.asIdeal).count (Associ

Depends on / 依赖: Associates, Associates.mk, HeightOneSpectrum, Ideal.span, Irreducible, asIdeal, constant_factor_ne_zero, factors, hJ_ne_zero, h_subset, ha_ne_zero, hv_irred, ideal_factor_ne_zero, subseteq, v.asIdeal, v.irre
-/
theorem finite_factors' {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    forallᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors : Int) -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors = 0 := by
  have ha_ne_zero : Ideal.span {a} != 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J != 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : Int) -
      ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors) = 0} subseteq
    {v : HeightOneSpectrum R | v.asIdeal ∣ J} union
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {a}} := by
    intro v hv
    have hv_irred : Irreducible v.asIdeal := v.irreducible
    by_contra h_notMem
    rw [mem_union]; rw [mem_ofPred_eq]; rw [mem_ofPred_eq] at h_notMem
    push Not at h_notMem
    rw [← Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred]; rw [not_not]; rw [← Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred]; rw [not_not] at h_notMem
    rw [mem_ofPred_eq]; rw [h_notMem.1]; rw [h_notMem.2]; rw [sub_self] at hv
    exact hv (Eq.refl 0)
  exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
    (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset

open Classical in
/--
theorem `finite_factors` / 定理 `finite_factors`

English:
theorem finite_factors
  given: (I : FractionalIdeal R⁰ K)
  proof: by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, ofPred_false,
      finite_empty]
  · convert! finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

中文:
定理 finite_factors
  条件: (I : FractionalIdeal R⁰ K)
  证明: by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, ofPred_false,
      finite_empty]
  · convert! finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

Depends on / 依赖: Filter, Filter.eventually_cofinite, choose_spec, convert, count_ne_zero, count_zero, eventually_cofinite, exists_eq_spanSingleton_mul, finite_empty, finite_factors, not_true_eq_false, ofPred_false
-/
theorem finite_factors (I : FractionalIdeal R⁰ K) :
    forallᶠ v : HeightOneSpectrum R in Filter.cofinite, count K v I = 0 := by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, ofPred_false,
      finite_empty]
  · convert! finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

end FractionalIdeal

section div

/--
lemma `IsDedekindDomain.exists_sup_span_eq` / 引理 `IsDedekindDomain.exists_sup_span_eq`

English:
lemma IsDedekindDomain.exists_sup_span_eq
  given: {I J : Ideal R} (hIJ : I <= J) (hI : I != 0)
  proof: by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices exists a, exists K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal

中文:
引理 是Dedekind整环.存在_sup_span_eq
  条件: {I J : 理想 R} (hIJ : I <= J) (hI : I != 0)
  证明: by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices exists a, exists K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal

Depends on / 依赖: Finset, Finset.prod_eq_mul_prod_sdiff_si, I.finite_factors, Ideal.add_eq_sup, Ideal.dvd_iff_le.mpr, Ideal.mul_top, Ideal.span, add_eq_sup, asIdeal, classical, conv_rhs, dvd_iff_le, finite_factors, mul_add, mul_eq_zero, mul_one, mul_top, ne_eq, not_or, prod_eq_mul_prod_sdiff_si
-/
lemma IsDedekindDomain.exists_sup_span_eq {I J : Ideal R} (hIJ : I <= J) (hI : I != 0) :
    exists a, I ⊔ Ideal.span {a} = J := by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices exists a, exists K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal.mul_top]⟩
  let s := (I.finite_factors hI).toFinset
  have : forall p in s, J * ∏ q in s, q.asIdeal < J * ∏ q in s \ {p}, q.asIdeal := by
    intro p hps
    conv_rhs => rw [← mul_one (J * _)]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hps]; rw [← mul_assoc]; rw [mul_right_comm _ p.asIdeal]
    refine mul_lt_mul_of_pos_left ?_ ?_
    · rw [Ideal.one_eq_top, lt_top_iff_ne_top]
      exact p.2.ne_top
    · rw [Ideal.zero_eq_bot, bot_lt_iff_ne_bot, ← Ideal.zero_eq_bot,
        mul_ne_zero_iff, Finset.prod_ne_zero_iff]
      exact ⟨hJ, fun x _ => x.3⟩
  choose! a ha ha' using fun p hps => SetLike.exists_of_lt (this p hps)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {∑ p in s, a p} := by
    rw [Ideal.dvd_iff_le]; rw [Ideal.span_singleton_le_iff_mem]
    exact sum_mem fun p hp => Ideal.mul_le_left (ha p hp)
  refine ⟨_, _, hK.symm, ?_⟩
  by_contra H
  obtain ⟨p, hp, h⟩ := Ideal.exists_le_maximal _ H
  let p' : HeightOneSpectrum R := ⟨p, hp.isPrime, fun e => hI (by simp_all)⟩
  have hp's : p' in s := by simpa [p', s, Ideal.dvd_iff_le] using le_sup_left.trans h
  have H₁ : J * K <= J * p := Ideal.mul_mono_right (le_sup_right.trans h)
  replace H₁ := hK.trans_le H₁ (Ideal.mem_span_singleton_self _)
  have H₂ : ∑ q in s \ {p'}, a q in J * p := by
    refine sum_mem fun q hq => ?_
    rw [Finset.mem_sdiff]; rw [Finset.mem_singleton] at hq
    refine Ideal.mul_mono_right ?_ (ha q hq.1)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := p') (by simpa [hp's] using Ne.symm hq.2))
  apply ha' _ hp's
  have := IsDedekindDomain.inf_pow_eq_prod_of_prime s (fun i => i.asIdeal) (fun _ => 1)
    (fun i _ => i.prime) (fun i _ j _ e => mt HeightOneSpectrum.ext e)
  simp only [pow_one] at this
  have inst : Nonempty {x // x in s} := ⟨_, hp's⟩
  rw [← this]; rw [Finset.inf_eq_iInf]; rw [iInf_subtype']; rw [Ideal.mul_iInf]; rw [Ideal.mem_iInf]
  rintro ⟨q, hq⟩
  by_cases hqp : q = p'
  · subst hqp
    convert! sub_mem H₁ H₂
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hp's]; rw [add_sub_cancel_right]
  · refine Ideal.mul_mono_right ?_ (ha p' hp's)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := q) (by simpa [hq] using hqp))

/--
lemma `IsDedekindDomain.exists_eq_span_pair` / 引理 `IsDedekindDomain.exists_eq_span_pair`

English:
lemma IsDedekindDomain.exists_eq_span_pair
  given: {I : Ideal R} {x : R} (hxI : x in I) (hx : x != 0)
  proof: by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y

中文:
引理 是Dedekind整环.存在_eq_span_pair
  条件: {I : 理想 R} {x : R} (hxI : x in I) (hx : x != 0)
  证明: by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y

Depends on / 依赖: I.span_singleton_le_iff_mem.mpr, Ideal.span_union, Set.pair_comm, Set.union_singleton, exists_sup_span_eq, pair_comm, simp_rw, span_singleton_le_iff_mem, span_union, union_singleton
-/
lemma IsDedekindDomain.exists_eq_span_pair {I : Ideal R} {x : R} (hxI : x in I) (hx : x != 0) :
    exists y, I = .span {x, y} := by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y

/--
lemma `IsDedekindDomain.exists_add_spanSingleton_mul_eq` / 引理 `IsDedekindDomain.exists_add_spanSingleton_mul_eq`

English:
lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
  proof: by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c) (by gcongr) (by simp [ha, hb])
      one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have H : Ideal.span {c.den.1} * a.num <= c.num

中文:
引理 是Dedekind整环.存在_add_spanSingleton_mul_eq
  证明: by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c) (by gcongr) (by simp [ha, hb])
      one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have H : Ideal.span {c.den.1} * a.num <= c.num

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coeIdeal_le_coeIdeal, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.den_mul_self_eq_num, Ideal.span, a.den, a.num, c.den, c.num, coeIdeal_le_coeIdeal, coeIdeal_mul, coeIdeal_span_singleton, den_mul_self_eq_num, mul_add, mul_assoc, mul_comm, one_ne_zero, ring_nf, spanSingleton
-/
lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
    {a b c : FractionalIdeal R⁰ K} (hac : a <= c) (ha : a != 0) (hb : b != 0) :
    exists x : K, a + FractionalIdeal.spanSingleton R⁰ x * b = c := by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c) (by gcongr) (by simp [ha, hb])
      one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have H : Ideal.span {c.den.1} * a.num <= c.num * Ideal.span {a.den.1} := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K]
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, ←
      FractionalIdeal.den_mul_self_eq_num']
    ring_nf
    gcongr
  obtain ⟨x, hx⟩ := exists_sup_span_eq H
    (by simpa using FractionalIdeal.num_eq_zero_iff.not.mpr ha)
  refine ⟨algebraMap R K x / algebraMap R K (a.den.1 * c.den.1), ?_⟩
  refine mul_left_injective₀ (b := .spanSingleton _
    (algebraMap R K (a.den.1 * c.den.1))) ?_ ?_
  · simp [FractionalIdeal.spanSingleton_eq_zero_iff]
  · simp only [map_mul, mul_one, add_mul, FractionalIdeal.spanSingleton_mul_spanSingleton,
      isUnit_iff_ne_zero, ne_eq, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff,
      nonZeroDivisors.coe_ne_zero, or_self, not_false_eq_true, IsUnit.div_mul_cancel]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]; rw [← mul_assoc]; rw [mul_comm a]; rw [FractionalIdeal.den_mul_self_eq_num']; rw [← mul_assoc]; rw [mul_right_comm]; rw [mul_comm c]; rw [FractionalIdeal.den_mul_self_eq_num']; rw [mul_comm]
    simp_rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← hx, ← FractionalIdeal.coeIdeal_sup]

namespace FractionalIdeal

/-- `c.divMod b a` (i.e. `c / b mod a`) is an arbitrary `x` such that `c = bx + a`.
This is zero if the above is not possible, i.e. when `a = 0` or `b = 0` or `¬ a ≤ c`. -/
noncomputable
/--
Definition of `divMod` / `divMod` 的定义

English:
definition divMod
  signature: (c b a : FractionalIdeal R⁰ K)
  body: letI := Classical.propDecidable
  if h : a <= c ∧ a != 0 ∧ b != 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0

中文:
定义 divMod
  签名: (c b a : FractionalIdeal R⁰ K)
  定义体: letI := Classical.propDecidable
  if h : a <= c ∧ a != 0 ∧ b != 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0

Depends on / 依赖: Classical, Classical.propDecidable, IsDedekindDomain, IsDedekindDomain.exists_add_spanSingleton_mul_eq, exists_add_spanSingleton_mul_eq, propDecidable
-/
def divMod (c b a : FractionalIdeal R⁰ K) : K :=
  letI := Classical.propDecidable
  if h : a <= c ∧ a != 0 ∧ b != 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0


/--
lemma `divMod_spec` / 引理 `divMod_spec`

English:
lemma divMod_spec
  proof: by
  rw [divMod]; rw [dif_pos ⟨hac]; rw [ha]; rw [hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]

中文:
引理 divMod_spec
  证明: by
  rw [divMod]; rw [dif_pos ⟨hac]; rw [ha]; rw [hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]

Depends on / 依赖: IsDedekindDomain, IsDedekindDomain.exists_add_spanSingleton_mul_eq, choose_spec, dif_pos, divMod, exists_add_spanSingleton_mul_eq
-/
lemma divMod_spec
    {a b c : FractionalIdeal R⁰ K} (hac : a <= c) (ha : a != 0) (hb : b != 0) :
    a + spanSingleton R⁰ (c.divMod b a) * b = c := by
  rw [divMod]; rw [dif_pos ⟨hac]; rw [ha]; rw [hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]
/--
lemma `divMod_zero_left` / 引理 `divMod_zero_left`

English:
lemma divMod_zero_left
  given: {I J : FractionalIdeal R⁰ K}
  statement: I.divMod 0 J = 0
  proof: by
  simp [divMod]

@[simp]

中文:
引理 divMod_zero_left
  条件: {I J : FractionalIdeal R⁰ K}
  结论: I.divMod 0 J = 0
  证明: by
  simp [divMod]

@[simp]

Depends on / 依赖: divMod
-/
lemma divMod_zero_left {I J : FractionalIdeal R⁰ K} : I.divMod 0 J = 0 := by
  simp [divMod]

@[simp]
/--
lemma `divMod_zero_right` / 引理 `divMod_zero_right`

English:
lemma divMod_zero_right
  given: {I J : FractionalIdeal R⁰ K}
  statement: I.divMod J 0 = 0
  proof: by
  simp [divMod]

@[simp]

中文:
引理 divMod_zero_right
  条件: {I J : FractionalIdeal R⁰ K}
  结论: I.divMod J 0 = 0
  证明: by
  simp [divMod]

@[simp]

Depends on / 依赖: divMod
-/
lemma divMod_zero_right {I J : FractionalIdeal R⁰ K} : I.divMod J 0 = 0 := by
  simp [divMod]

@[simp]
/--
lemma `zero_divMod` / 引理 `zero_divMod`

English:
lemma zero_divMod
  given: {I J : FractionalIdeal R⁰ K}
  proof: by
  simp [divMod, ← and_assoc]

中文:
引理 zero_divMod
  条件: {I J : FractionalIdeal R⁰ K}
  证明: by
  simp [divMod, ← and_assoc]

Depends on / 依赖: and_assoc, divMod
-/
lemma zero_divMod {I J : FractionalIdeal R⁰ K} :
    (0 : FractionalIdeal R⁰ K).divMod I J = 0 := by
  simp [divMod, ← and_assoc]

/--
lemma `divMod_zero_of_not_le` / 引理 `divMod_zero_of_not_le`

English:
lemma divMod_zero_of_not_le
  given: {a b c : FractionalIdeal R⁰ K} (hac : ¬ a <= c)
  proof: by
  simp [divMod, hac]

中文:
引理 divMod_zero_of_not_le
  条件: {a b c : FractionalIdeal R⁰ K} (hac : ¬ a <= c)
  证明: by
  simp [divMod, hac]

Depends on / 依赖: divMod
-/
lemma divMod_zero_of_not_le {a b c : FractionalIdeal R⁰ K} (hac : ¬ a <= c) :
    c.divMod b a = 0 := by
  simp [divMod, hac]

/-- Let `I J I' J'` be nonzero fractional ideals in a Dedekind domain with `J ≤ I` and `J' ≤ I'`.
If `I/J = I'/J'` in the group of fractional ideals (i.e. `I * J' = I' * J`),
then `I/J ≃ I'/J'` as quotient `R`-modules. -/
noncomputable
/--
Definition of `quotientEquiv` / `quotientEquiv` 的定义

English:
definition quotientEquiv
  signature: (I J I' J' : FractionalIdeal R⁰ K)
  body: by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [FractionalIdeal.sup_eq_add, divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H,
      mul_comm I' J, ←

中文:
定义 quotientEquiv
  签名: (I J I' J' : FractionalIdeal R⁰ K)
  定义体: by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [FractionalIdeal.sup_eq_add, divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H,
      mul_comm I' J, ←

Depends on / 依赖: Algebra, Algebra.lsmul, FractionalIdeal, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_mul_inf, LinearMap, LinearMap.restrict, Submodule, Submodule.mapQ, divMod, divMod_spec, eq_iff, mul_assoc, mul_comm, mul_left_comm, ofBijective, restrict, spanSingleton, sup_eq_add, sup_mul_inf
-/
def quotientEquiv (I J I' J' : FractionalIdeal R⁰ K)
    (H : I * J' = I' * J) (h : J <= I) (h' : J' <= I') (hJ' : J' != 0) (hI : I != 0) :
    (I ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype) ≃ₗ[R]
      I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmodule.subtype := by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [FractionalIdeal.sup_eq_add, divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H,
      mul_comm I' J, ← mul_assoc, (mul_left_injective₀ _).eq_iff] at this
    rintro rfl
    exact hJ' (by simpa using h')
  refine .ofBijective (Submodule.mapQ _ _ (LinearMap.restrict
    (Algebra.lsmul R _ _ (I'.divMod I J')) ?_) ?_) ⟨?_, ?_⟩
  · intro x hx
    refine (divMod_spec h' hJ' hI).le ?_
    exact Submodule.mem_sup_right (mul_mem_mul (mem_spanSingleton_self _ _) hx)
  · rw [← Submodule.comap_comp, LinearMap.subtype_comp_restrict, LinearMap.domRestrict,
      Submodule.comap_comp]
    refine Submodule.comap_mono ?_
    intro x hx
    refine (Submodule.mem_inf.mp (this.ge ?_)).1
    simp only [Algebra.lsmul_coe, smul_eq_mul]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hx
  · rw [← LinearMap.ker_eq_bot, Submodule.mapQ, Submodule.ker_liftQ,
      LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.comap_comp,
      LinearMap.subtype_comp_restrict, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.domRestrict,
      Submodule.comap_comp, ← Submodule.map_le_iff_le_comap,
      Submodule.map_comap_eq, Submodule.range_subtype]
    by_cases H' : I'.divMod I J' = 0
    · obtain rfl : J' = I' := by simpa [H'] using divMod_spec h' hJ' hI
      obtain rfl : I = J := mul_left_injective₀ hJ' (H.trans (mul_comm _ _))
      exact inf_le_left
    rw [← inv_mul_eq_iff_eq_mul₀ (by simpa [spanSingleton_eq_zero_iff] using H'), mul_inf₀
      (zero_le _), inv_mul_cancel_left₀ (by simpa [spanSingleton_eq_zero_iff] using H')] at this
    rw [← this]; rw [inf_comm]; rw [coe_inf]
    refine inf_le_inf ?_ le_rfl
    intro x hx
    rw [spanSingleton_inv]
    convert! mul_mem_mul (mem_spanSingleton_self _ _) hx
    simp [H']
  · have H : Submodule.map (Algebra.lsmul R R K (I'.divMod I J')) ↑I =
        (spanSingleton R⁰ (I'.divMod I J') * I) := by
      ext x
      simp [Submodule.mem_span_singleton_mul]
    rw [← LinearMap.range_eq_top]; rw [Submodule.mapQ]; rw [Submodule.range_liftQ]; rw [LinearMap.range_comp]; rw [LinearMap.restrict]; rw [LinearMap.range_codRestrict]; rw [LinearMap.range_domRestrict]; rw [← top_le_iff]; rw [H]; rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]; rw [← Submodule.map_top]; rw [Submodule.map_le_iff_le_comap]; rw [Submodule.comap_map_eq]; rw [Submodule.ker_mkQ]; rw [← Submodule.map_le_map_iff_of_injective I'.coeToSubmodule.injective_subtype]; rw [Submodule.map_top]; rw [Submodule.map_sup]; rw [Submodule.map_comap_eq]; rw [Submodule.map_comap_eq]; rw [Submodule.range_subtype]; rw [sup_comm]; rw [inf_eq_right.mpr]; rw [inf_eq_right.mpr]
    · exact le_trans (divMod_spec h' hJ' hI).ge (by simp)
    · exact le_trans (by simp) (divMod_spec h' hJ' hI).le
    · exact h'

end FractionalIdeal

end div

section primesOver

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra.IsIntegral S R] [IsDomain S]
  [Module.IsTorsionFree S R]

open IsDedekindDomain Ideal.IsDedekindDomain HeightOneSpectrum

/--
theorem `Ideal.map_algebraMap_eq_finsetProd_pow` / 定理 `Ideal.map_algebraMap_eq_finsetProd_pow`

English:
theorem Ideal.map_algebraMap_eq_finsetProd_pow
  given: {p : Ideal S} [p.IsMaximal] (hp : p != 0)
  proof: by
  have h : map (algebraMap S R) p != 0 := map_ne_bot_of_ne_bot hp
  rw [← finprod_heightOneSpectrum_factorization (I := p.map (algebraMap S R)) h]
  let hF : Fintype {v : HeightOneSpectrum R | v.asIdeal ∣ map (algebraMap S R) p} :=
    (finite_factors h).fintype
  rw [finprod_eq_finsetProd_of_mul

中文:
定理 理想.map_algebraMap_eq_finsetProd_pow
  条件: {p : 理想 S} [p.是极大] (hp : p != 0)
  证明: by
  have h : map (algebraMap S R) p != 0 := map_ne_bot_of_ne_bot hp
  rw [← finprod_heightOneSpectrum_factorization (I := p.map (algebraMap S R)) h]
  let hF : Fintype {v : HeightOneSpectrum R | v.asIdeal ∣ map (algebraMap S R) p} :=
    (finite_factors h).fintype
  rw [finprod_eq_finsetProd_of_mul

Depends on / 依赖: Finset, Finset.prod_set_coe, Fintype, HeightOneSpectrum, algebraMap, asIdeal, finite_factors, finprod_eq_finsetProd_of_mulSupport_subset, finprod_heightOneSpectrum_factorization, fintype, map_ne_bot_of_ne_bot, p.map, prod_set_coe, toFinset, v.asIdeal
-/
theorem Ideal.map_algebraMap_eq_finsetProd_pow {p : Ideal S} [p.IsMaximal] (hp : p != 0) :
    map (algebraMap S R) p = ∏ P in p.primesOver R, P ^ P.ramificationIdx S := by
  have h : map (algebraMap S R) p != 0 := map_ne_bot_of_ne_bot hp
  rw [← finprod_heightOneSpectrum_factorization (I := p.map (algebraMap S R)) h]
  let hF : Fintype {v : HeightOneSpectrum R | v.asIdeal ∣ map (algebraMap S R) p} :=
    (finite_factors h).fintype
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := {v | v.asIdeal ∣ p.map (algebraMap S R)}.toFinset)]; rw [← Finset.prod_set_coe]; rw [← Finset.prod_set_coe]
  · let _ : Fintype {v : HeightOneSpectrum R // v.asIdeal ∣ map (algebraMap S R) p} := hF
    refine Fintype.prod_equiv (equivPrimesOver _ hp) _ _ fun ⟨v, _⟩ => ?_
    have : v.asIdeal.LiesOver p := by rwa [Ideal.liesOver_iff_dvd_map v.2.ne_top]
    simp [maxPowDividing_eq_pow_multiset_count _ h, ramificationIdx_eq_factors_count p v h]
  · intro v hv
    simpa [maxPowDividing, Function.mem_mulSupport, IsPrime.ne_top _,
      Associates.count_ne_zero_iff_dvd h (irreducible v)] using hv

@[deprecated (since := "2026-04-08")]
alias Ideal.map_algebraMap_eq_finset_prod_pow := Ideal.map_algebraMap_eq_finsetProd_pow

end primesOver

/-!
### Conversion between various multiplicities

We provide some lemmas that convert various ways of expressing the multiplicity of
a prime ideal `p` in the factorization of some ideal `I` into `multiplicity p.asIdeal I`.
-/

section conversion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

namespace IsDedekindDomain.HeightOneSpectrum

variable {I : Ideal R} (hI : I != ⊥) (p : HeightOneSpectrum R)
include hI

open UniqueFactorizationMonoid in
/-- Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
/--
lemma `count_normalizedFactors_eq_multiplicity` / 引理 `count_normalizedFactors_eq_multiplicity`

English:
lemma count_normalizedFactors_eq_multiplicity
  proof: by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  apply_fun ((↑) : Nat -> Nat∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

中文:
引理 count_normalizedFactors_eq_multiplicity
  证明: by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  apply_fun ((↑) : Nat -> Nat∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

Depends on / 依赖: CharZero, CharZero.cast_injective, apply_fun, asIdeal, cast_injective, emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_multiplicity, finiteMultiplicity_of_emultiplicity_eq_natCast, irreducible, normalize_eq, p.asIdeal
-/
lemma count_normalizedFactors_eq_multiplicity :
    Multiset.count p.asIdeal (normalizedFactors I) = multiplicity p.asIdeal I := by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  apply_fun ((↑) : Nat -> Nat∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

/--
lemma `maxPowDividing_eq_pow_multiplicity` / 引理 `maxPowDividing_eq_pow_multiplicity`

English:
lemma maxPowDividing_eq_pow_multiplicity
  proof: by
  rw [maxPowDividing_eq_pow_multiset_count _ hI]; rw [count_normalizedFactors_eq_multiplicity hI]

中文:
引理 maxPowDividing_eq_pow_multiplicity
  证明: by
  rw [maxPowDividing_eq_pow_multiset_count _ hI]; rw [count_normalizedFactors_eq_multiplicity hI]

Depends on / 依赖: count_normalizedFactors_eq_multiplicity, maxPowDividing_eq_pow_multiset_count
-/
lemma maxPowDividing_eq_pow_multiplicity :
    p.maxPowDividing I = p.asIdeal ^ multiplicity p.asIdeal I := by
  rw [maxPowDividing_eq_pow_multiset_count _ hI]; rw [count_normalizedFactors_eq_multiplicity hI]

/-- Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
/--
lemma `factorization_eq_multiplicity` / 引理 `factorization_eq_multiplicity`

English:
lemma factorization_eq_multiplicity
  proof: by
  rw [factorization_eq_count]; rw [count_normalizedFactors_eq_multiplicity hI]

中文:
引理 factorization_eq_multiplicity
  证明: by
  rw [factorization_eq_count]; rw [count_normalizedFactors_eq_multiplicity hI]

Depends on / 依赖: count_normalizedFactors_eq_multiplicity, factorization_eq_count
-/
lemma factorization_eq_multiplicity :
    factorization I p.asIdeal = multiplicity p.asIdeal I := by
  rw [factorization_eq_count]; rw [count_normalizedFactors_eq_multiplicity hI]

end IsDedekindDomain.HeightOneSpectrum

end conversion

/-!
### Lemmas about multiplicities

We collect here lemmas about the multiplicity of a prime ideal `p` in the factorization
of some ideal `I`.
These are phrased in terms of `multiplicity p.asIdeal I`.
-/

section multiplicity

@[simp]
/--
lemma `Ideal.emultiplicity_bot` / 引理 `Ideal.emultiplicity_bot`

English:
lemma Ideal.emultiplicity_bot
  given: {R : Type*} [CommSemiring R] (I : Ideal R)
  statement: emultiplicity I ⊥ = ⊤
  proof: Submodule.zero_eq_bot (R := R) (M := R) ▸ emultiplicity_zero I

中文:
引理 理想.emultiplicity_bot
  条件: {R : 类型} [交换半环 R] (I : 理想 R)
  结论: emultiplicity I ⊥ = ⊤
  证明: Submodule.zero_eq_bot (R := R) (M := R) ▸ emultiplicity_zero I

Depends on / 依赖: Submodule, Submodule.zero_eq_bot, emultiplicity_zero, zero_eq_bot
-/
lemma Ideal.emultiplicity_bot {R : Type*} [CommSemiring R] (I : Ideal R) : emultiplicity I ⊥ = ⊤ :=
  Submodule.zero_eq_bot (R := R) (M := R) ▸ emultiplicity_zero I

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/--
lemma `Ideal.finprod_heightOneSpectrum_pow_multiplicity` / 引理 `Ideal.finprod_heightOneSpectrum_pow_multiplicity`

English:
lemma Ideal.finprod_heightOneSpectrum_pow_multiplicity
  given: {I : Ideal R} (hI : I != ⊥)
  proof: by
  simpa only [maxPowDividing_eq_pow_multiplicity hI]
    using finprod_heightOneSpectrum_factorization hI

中文:
引理 理想.finprod_heightOneSpectrum_pow_multiplicity
  条件: {I : 理想 R} (hI : I != ⊥)
  证明: by
  simpa only [maxPowDividing_eq_pow_multiplicity hI]
    using finprod_heightOneSpectrum_factorization hI

Depends on / 依赖: finprod_heightOneSpectrum_factorization, maxPowDividing_eq_pow_multiplicity
-/
lemma Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I != ⊥) :
    ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I := by
  simpa only [maxPowDividing_eq_pow_multiplicity hI]
    using finprod_heightOneSpectrum_factorization hI

namespace IsDedekindDomain.HeightOneSpectrum

variable (p : HeightOneSpectrum R) {I J : Ideal R}

/--
lemma `multiplicity_le_of_ideal_ge` / 引理 `multiplicity_le_of_ideal_ge`

English:
lemma multiplicity_le_of_ideal_ge
  given: (h : J <= I) (hJ : J != ⊥)
  proof: by
  rw [← count_normalizedFactors_eq_multiplicity hJ]; rw [← count_normalizedFactors_eq_multiplicity ne_bot_of_le_ne_bot hJ h]
  exact Ideal.count_le_of_ideal_ge h hJ _

中文:
引理 multiplicity_le_of_ideal_ge
  条件: (h : J <= I) (hJ : J != ⊥)
  证明: by
  rw [← count_normalizedFactors_eq_multiplicity hJ]; rw [← count_normalizedFactors_eq_multiplicity ne_bot_of_le_ne_bot hJ h]
  exact Ideal.count_le_of_ideal_ge h hJ _

Depends on / 依赖: Ideal.count_le_of_ideal_ge, count_le_of_ideal_ge, count_normalizedFactors_eq_multiplicity, ne_bot_of_le_ne_bot
-/
lemma multiplicity_le_of_ideal_ge (h : J <= I) (hJ : J != ⊥) :
    multiplicity p.asIdeal I <= multiplicity p.asIdeal J := by
  rw [← count_normalizedFactors_eq_multiplicity hJ]; rw [← count_normalizedFactors_eq_multiplicity ne_bot_of_le_ne_bot hJ h]
  exact Ideal.count_le_of_ideal_ge h hJ _

open UniqueFactorizationMonoid Multiset in
/--
lemma `multiplicity_sup` / 引理 `multiplicity_sup`

English:
lemma multiplicity_sup
  given: (hI : I != ⊥) (hJ : J != ⊥)
  proof: by
  rw [Ideal.sup_eq_prod_inf_factors hI hJ]; rw [← count_normalizedFactors_eq_multiplicity ?h]; rw [← count_normalizedFactors_eq_multiplicity hI]; rw [← count_normalizedFactors_eq_multiplicity hJ]
  case h => exact prod_inter_normalizedFactors_ne_zero I J
  rw [normalizedFactors_prod_inter_eq_inte

中文:
引理 multiplicity_sup
  条件: (hI : I != ⊥) (hJ : J != ⊥)
  证明: by
  rw [Ideal.sup_eq_prod_inf_factors hI hJ]; rw [← count_normalizedFactors_eq_multiplicity ?h]; rw [← count_normalizedFactors_eq_multiplicity hI]; rw [← count_normalizedFactors_eq_multiplicity hJ]
  case h => exact prod_inter_normalizedFactors_ne_zero I J
  rw [normalizedFactors_prod_inter_eq_inte

Depends on / 依赖: Ideal.sup_eq_prod_inf_factors, count_inter, count_normalizedFactors_eq_multiplicity, normalizedFactors_prod_inter_eq_inter, prod_inter_normalizedFactors_ne_zero, sup_eq_prod_inf_factors
-/
lemma multiplicity_sup (hI : I != ⊥) (hJ : J != ⊥) :
    multiplicity p.asIdeal (I ⊔ J) = multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J := by
  rw [Ideal.sup_eq_prod_inf_factors hI hJ]; rw [← count_normalizedFactors_eq_multiplicity ?h]; rw [← count_normalizedFactors_eq_multiplicity hI]; rw [← count_normalizedFactors_eq_multiplicity hJ]
  case h => exact prod_inter_normalizedFactors_ne_zero I J
  rw [normalizedFactors_prod_inter_eq_inter]
  exact count_inter ..

variable (I J) in
/--
lemma `emultiplicity_sup` / 引理 `emultiplicity_sup`

English:
lemma emultiplicity_sup
  proof: by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  rcases eq_or_ne J ⊥ with rfl | hJ
  · simp
  have : I ⊔ J != ⊥ := by grind
  have H {I' : Ideal R} (h : I' != ⊥) : FiniteMultiplicity p.asIdeal I' :=
    FiniteMultiplicity.of_prime_left (prime p) h
  rw [(H this).emultiplicity_eq_multiplicity]; rw [

中文:
引理 emultiplicity_sup
  证明: by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  rcases eq_or_ne J ⊥ with rfl | hJ
  · simp
  have : I ⊔ J != ⊥ := by grind
  have H {I' : Ideal R} (h : I' != ⊥) : FiniteMultiplicity p.asIdeal I' :=
    FiniteMultiplicity.of_prime_left (prime p) h
  rw [(H this).emultiplicity_eq_multiplicity]; rw [

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.of_prime_left, asIdeal, emultiplicity_eq_multiplicity, eq_or_ne, multiplicity_sup, of_prime_left, p.asIdeal
-/
lemma emultiplicity_sup :
    emultiplicity p.asIdeal (I ⊔ J) = emultiplicity p.asIdeal I ⊓ emultiplicity p.asIdeal J := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  rcases eq_or_ne J ⊥ with rfl | hJ
  · simp
  have : I ⊔ J != ⊥ := by grind
  have H {I' : Ideal R} (h : I' != ⊥) : FiniteMultiplicity p.asIdeal I' :=
    FiniteMultiplicity.of_prime_left (prime p) h
  rw [(H this).emultiplicity_eq_multiplicity]; rw [(H hI).emultiplicity_eq_multiplicity]; rw [(H hJ).emultiplicity_eq_multiplicity]; rw [multiplicity_sup _ hI hJ]
  norm_cast

variable {ι : Type*} [Finite ι]

/--
lemma `emultiplicity_iSup` / 引理 `emultiplicity_iSup`

English:
lemma emultiplicity_iSup
  given: (I : ι -> Ideal R)
  proof: by
  induction ι using Finite.induction_empty_option with
  | h_empty =>
    rw [iSup_of_empty]; rw [iInf_of_empty]
    exact emultiplicity_zero _
  | of_equiv e ih =>
    specialize ih (I ∘ e)
    rw [← sSup_range]; rw [← sInf_range] at ih ⊢
    rw [EquivLike.range_comp I e] at ih
    rw [ih]
exact

中文:
引理 emultiplicity_iSup
  条件: (I : ι -> 理想 R)
  证明: by
  induction ι using Finite.induction_empty_option with
  | h_empty =>
    rw [iSup_of_empty]; rw [iInf_of_empty]
    exact emultiplicity_zero _
  | of_equiv e ih =>
    specialize ih (I ∘ e)
    rw [← sSup_range]; rw [← sInf_range] at ih ⊢
    rw [EquivLike.range_comp I e] at ih
    rw [ih]
exact

Depends on / 依赖: EquivLike, EquivLike.range_comp, Finite, Finite.induction_empty_option, asIdeal, emultiplicity, emultiplicity_sup, emultiplicity_zero, h_empty, h_option, iInf_of_empty, iInf_option, iSup_of_empty, iSup_option, induction_empty_option, of_equiv, p.asIdeal, range_comp, sInf_range, sSup_range
-/
lemma emultiplicity_iSup (I : ι -> Ideal R) :
    emultiplicity p.asIdeal (⨆ i, I i) = ⨅ i, emultiplicity p.asIdeal (I i) := by
  induction ι using Finite.induction_empty_option with
  | h_empty =>
    rw [iSup_of_empty]; rw [iInf_of_empty]
    exact emultiplicity_zero _
  | of_equiv e ih =>
    specialize ih (I ∘ e)
    rw [← sSup_range]; rw [← sInf_range] at ih ⊢
    rw [EquivLike.range_comp I e] at ih
    rw [ih]
exact congrArg _ EquivLike.range_comp (emultiplicity p.asIdeal <| I ·) e
  | h_option ih =>
    rw [iSup_option]; rw [emultiplicity_sup p ..]; rw [ih]; rw [iInf_option]

/--
lemma `multiplicity_iSup` / 引理 `multiplicity_iSup`

English:
lemma multiplicity_iSup
  given: [Nonempty ι] {I : ι -> Ideal R} (hI : forall i, I i != ⊥)
  proof: by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
FiniteMultiplicity.of_prime_left (prime p) hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero]; rw [iSup_eq_bot] at hI
    exact ⟨Classi

中文:
引理 multiplicity_iSup
  条件: [非空 ι] {I : ι -> 理想 R} (hI : 对任意 i, I i != ⊥)
  证明: by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
FiniteMultiplicity.of_prime_left (prime p) hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero]; rw [iSup_eq_bot] at hI
    exact ⟨Classi

Depends on / 依赖: Classical, Classical.ofNonempty, FiniteMultiplicity, FiniteMultiplicity.of_prime_left, asIdeal, bot_eq_zero, contrapose, emultiplicity_eq_multiplicity, emultiplicity_iSup, iSup_eq_bot, ofNonempty, of_prime_left, p.asIdeal
-/
lemma multiplicity_iSup [Nonempty ι] {I : ι -> Ideal R} (hI : forall i, I i != ⊥) :
    multiplicity p.asIdeal (⨆ i, I i) = ⨅ i, multiplicity p.asIdeal (I i) := by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
FiniteMultiplicity.of_prime_left (prime p) hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero]; rw [iSup_eq_bot] at hI
    exact ⟨Classical.ofNonempty, hI _⟩
  have := emultiplicity_iSup p I
  simp only [H'.emultiplicity_eq_multiplicity, (H _).emultiplicity_eq_multiplicity] at this
  exact_mod_cast this

end IsDedekindDomain.HeightOneSpectrum

end multiplicity
