/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Kummer-Dedekind theorem

This file proves the Kummer-Dedekind theorem on the splitting of prime ideals in an extension of
the ring of integers. This states the following: assume we are given
  - A prime ideal `I` of Dedekind domain `R`
  - An `R`-algebra `S` that is a Dedekind Domain
  - An `α : S` that is integral over `R` with minimal polynomial `f`

If the conductor `𝓒` of `x` is such that `𝓒 ∩ R` is coprime to `I` then the prime
factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the same number of
prime factors, and each prime factors of `I * S` can be paired with a prime factor of `f mod I` in
a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

* `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` : The bijection in the Kummer-Dedekind
  theorem. This is the pairing between the prime factors of `I * S` and the prime factors of
  `f mod I`.

## Main results

* `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` : The Kummer-Dedekind
  theorem.
* `Ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebraMap R S)` is irreducible if
  `(map (Ideal.Quotient.mk I) (minpoly R pb.gen))` is irreducible, where `pb` is a power basis
  of `S` over `R`.
  * `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span` : Let `Q` be a lift of
    factor of the minimal polynomial of `x`, a generator of `S` over `R`, taken
    `mod I`. Then (the reduction of) `Q` corresponds via
    `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
    `span (I.map (algebraMap R S) ∪ {Q.aeval x})`.

## TODO

* Prove the converse of `Ideal.irreducible_map_of_irreducible_minpoly`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

@[expose] public section


variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S} {I : Ideal R}

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom

namespace KummerDedekind

variable [IsDomain R] [IsIntegrallyClosed R]
variable [IsDedekindDomain S]
variable [Module.IsTorsionFree R S]

attribute [local instance] Ideal.Quotient.field

/--
Definition of `quotMapEquivQuotQuotMap` / `quotMapEquivQuotQuotMap` 的定义

English:
definition quotMapEquivQuotQuotMap
  signature: (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  body: (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])

中文:
定义 quotMapEquivQuotQuotMap
  签名: (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  定义体: (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin.powerBasis, FaithfulSMul, FaithfulSMul.algebraMap_injective, _minpoly_gen, adjoin, algebraMap_injective, powerBasis, quotAdjoinEquivQuotMap, quotEquivOfEq, quotientEquivQuotientMinpolyMap, symm.trans, toRingEquiv, toRingEquiv.trans
-/
noncomputable def quotMapEquivQuotQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(minpoly R x).map (Ideal.Quotient.mk I)} :=
  (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])

/--
lemma `quotMapEquivQuotQuotMap_symm_apply` / 引理 `quotMapEquivQuotQuotMap_symm_apply`

English:
lemma quotMapEquivQuotQuotMap_symm_apply
  statement: (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  proof: by
  apply (quotMapEquivQuotQuotMap hx hx').injective
  rw [quotMapEquivQuotQuotMap]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [RingEquiv.coe_trans]; rw [Function.comp_apply]; rw [RingEquiv.symm_apply_apply]; rw [RingEquiv.symm_trans_apply]; rw [quotEquivOfEq_symm]; rw [quotEqui

中文:
引理 quotMapEquivQuotQuotMap_symm_apply
  结论: (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  证明: by
  apply (quotMapEquivQuotQuotMap hx hx').injective
  rw [quotMapEquivQuotQuotMap]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [RingEquiv.coe_trans]; rw [Function.comp_apply]; rw [RingEquiv.symm_apply_apply]; rw [RingEquiv.symm_trans_apply]; rw [quotEquivOfEq_symm]; rw [quotEqui

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.comp_apply, RingEquiv, RingEquiv.coe_trans, RingEquiv.symm_apply_apply, RingEquiv.symm_symm, RingEquiv.symm_trans_apply, adjoin, adjoin.powerBasis, algebraMap_injective, coe_trans, comp_apply, convert, injective, powerBasis, quotAdjoinEquivQuotMap, quotEquivOfEq_mk, quotEquivOfEq_symm
-/
lemma quotMapEquivQuotQuotMap_symm_apply (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) (Q : R[X]) :
    (quotMapEquivQuotQuotMap hx hx').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x := by
  apply (quotMapEquivQuotQuotMap hx hx').injective
  rw [quotMapEquivQuotQuotMap]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [RingEquiv.coe_trans]; rw [Function.comp_apply]; rw [RingEquiv.symm_apply_apply]; rw [RingEquiv.symm_trans_apply]; rw [quotEquivOfEq_symm]; rw [quotEquivOfEq_mk]
  congr
  convert! (adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap_symm_apply_mk I Q
  apply (quotAdjoinEquivQuotMap hx
    (FaithfulSMul.algebraMap_injective ((adjoin R {x})) S)).injective
  simp only [RingEquiv.apply_symm_apply, adjoin.powerBasis'_gen, quotAdjoinEquivQuotMap_apply_mk,
    coe_aeval_mk_apply]

open scoped Classical in
/--
Definition of `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` / `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` 的定义

English:
definition normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
  signature: (hI : IsMaximal I)
  body: by
  refine (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv (quotMapEquivQuotQuotMap hx hx')
    ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) != 0 from
  

中文:
定义 normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
  签名: (hI : 是极大 I)
  定义体: by
  refine (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv (quotMapEquivQuotQuotMap hx hx')
    ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) != 0 from
  

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.Quotient.mk, Ideal.normalizedFactorsEquivSpanNormalizedFactors, IsDedekindDomain, IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv, Polynomial, Polynomial.map, Polynomial.map_monic_ne_zero, Quotient, algebraMap_injective, map_eq_bot_iff_of_injective, map_monic_ne_zero, minpoly, minpoly.monic, normalizedFactorsEquivOfQuotEquiv, normalizedFactorsEquivSpanNormalizedFactors, quotMapEquivQuotQuotMap, span_singleton_eq_bot, span_singleton_eq_bot.mp
-/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I != ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    {J : Ideal S | J in normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d in normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} := by
  refine (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv (quotMapEquivQuotQuotMap hx hx')
    ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) != 0 from
      Polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h)
  · refine (Ideal.normalizedFactorsEquivSpanNormalizedFactors ?_).symm
    exact Polynomial.map_monic_ne_zero (minpoly.monic hx')

/--
theorem `emultiplicity_factors_map_eq_emultiplicity` / 定理 `emultiplicity_factors_map_eq_emultiplicity`

English:
theorem emultiplicity_factors_map_eq_emultiplicity
  proof: by
  classical
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk]; rw [Equiv.coe_trans]; rw [Function.comp_apply]; rw [Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity

中文:
定理 emultiplicity_factors_map_eq_emultiplicity
  证明: by
  classical
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk]; rw [Equiv.coe_trans]; rw [Function.comp_apply]; rw [Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity

Depends on / 依赖: Equiv.coe_trans, Function, Function.comp_apply, Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity, IsDedekindDomain, IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity, classical, coe_trans, comp_apply, emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity, normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity, normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
-/
theorem emultiplicity_factors_map_eq_emultiplicity
    (hI : IsMaximal I) (hI' : I != ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {J : Ideal S}
    (hJ : J in normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
  classical
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk]; rw [Equiv.coe_trans]; rw [Function.comp_apply]; rw [Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` / 定理 `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map`

English:
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
  statement: (hI : IsMaximal I)
  proof: by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J in normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFact

中文:
定理 normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
  结论: (hI : 是极大 I)
  证明: by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J in normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFact
-/
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I != ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach := by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J in normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J').prop
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ
  rw [emultiplicity_eq_count_normalizedFactors]; rw [emultiplicity_eq_count_normalizedFactors]; rw [UniqueFactorizationMonoid.normalize_normalized_factor _ hJ]; rw [UniqueFactorizationMonoid.normalize_normalized_factor]; rw [Nat.cast_inj] at this
  · refine this.trans ?_
    -- Get rid of the `map` by applying the equiv to both sides.
    generalize hJ' :
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx') ⟨J, hJ⟩ = J'
    have : ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J' : Ideal S) =
        J := by
      rw [← hJ']; rw [Equiv.symm_apply_apply _ _]; rw [Subtype.coe_mk]
    subst this
    -- Get rid of the `attach` by applying the subtype `coe` to both sides.
    rw [Multiset.count_map_eq_count' fun f =>
        ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
          Ideal S)]; rw [Multiset.count_attach]
    · exact Subtype.coe_injective.comp (Equiv.injective _)
  · exact (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact irreducible_of_normalized_factor _
        (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
  · exact irreducible_of_normalized_factor _ hJ
  · rwa [← bot_eq_zero, Ne,
      map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Ideal.irreducible_map_of_irreducible_minpoly` / 定理 `Ideal.irreducible_map_of_irreducible_minpoly`

English:
theorem Ideal.irreducible_map_of_irreducible_minpoly
  statement: (hI : IsMaximal I) (hI' : I != ⊥)
  proof: by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) in
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices exists y, normalizedFactors (I.map (algebraMap R S)) = 

中文:
定理 理想.irreducible_map_of_irreducible_minpoly
  结论: (hI : 是极大 I) (hI' : I != ⊥)
  证明: by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) in
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices exists y, normalizedFactors (I.map (algebraMap R S)) = 

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, I.map, Ideal.Quotient.mk, Polynomial, Polynomial.map, Quotient, algebraMap, algebraMap_injective, associated_iff_eq, bot_eq_zero, classical, map_eq_bot_iff_of_injective, mem_norm_factors, minpoly, normalize, normalizedFactors, normalizedFactors_irreducible, prod_normalizedFactors
-/
theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I != ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    (hf : Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    Irreducible (I.map (algebraMap R S)) := by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) in
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices exists y, normalizedFactors (I.map (algebraMap R S)) = {y} by
    obtain ⟨y, hy⟩ := this
    have h := prod_normalizedFactors (show I.map (algebraMap R S) != 0 by
          rwa [← bot_eq_zero, Ne,
            map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)])
    rw [associated_iff_eq]; rw [hy]; rw [Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor y
        (show y in normalizedFactors (I.map (algebraMap R S)) by simp [hy])
  rw [normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx']
  use ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
        ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩
  refine ⟨?_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_val]; rw [Multiset.map_singleton]; rw [Subtype.coe_mk]
  exact normalizedFactors_irreducible hf

set_option backward.isDefEq.respectTransparency.types false in
open Set Classical in
/--
theorem `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span` / 定理 `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span`

English:
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
  proof: by
  unfold normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    Ideal.normalizedFactorsEquivSpanNormalizedFactors
  rw [Equiv.symm_trans_apply]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm]
  unfold IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv
  rw [Equiv.coe_fn_mk]; rw [Eq

中文:
定理 normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
  证明: by
  unfold normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    Ideal.normalizedFactorsEquivSpanNormalizedFactors
  rw [Equiv.symm_trans_apply]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm]
  unfold IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv
  rw [Equiv.coe_fn_mk]; rw [Eq

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.ofBijective_apply, Equiv.symm_symm, Equiv.symm_trans_apply, Ideal.normalizedFactorsEquivSpanNormalizedFactors, IsDedekindDomain, IsDedekindDomain.idealFactorsEquivOfQuotEquiv, IsDedekindDomain.idealFactorsFunOfQuotHom_coe_coe, IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv, IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm, OrderIso, OrderIso.ofHomInv_apply, coe_fn_mk, idealFactorsEquivOfQuotEquiv, idealFactorsFunOfQuotHom_coe_coe, normalizedFactorsEquivOfQuotEquiv, normalizedFactorsEquivOfQuotEquiv_symm, normalizedFactorsEquivSpanNormalizedFactors, normalizedFactorsMapEquivNormalizedFactorsMinPolyMk, ofBijective_apply
-/
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    (hI : I.IsMaximal) {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) in normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
    (hI' : I != ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm ⟨_, hQ⟩).val =
    span (I.map (algebraMap R S) union {Q.aeval x}) := by
  unfold normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    Ideal.normalizedFactorsEquivSpanNormalizedFactors
  rw [Equiv.symm_trans_apply]; rw [IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm]
  unfold IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv
  rw [Equiv.coe_fn_mk]; rw [Equiv.symm_symm]; rw [Equiv.ofBijective_apply]
  dsimp only
  unfold IsDedekindDomain.idealFactorsEquivOfQuotEquiv
  rw [OrderIso.ofHomInv_apply]
  erw [IsDedekindDomain.idealFactorsFunOfQuotHom_coe_coe]
  dsimp only
  rw [map_span]; rw [image_singleton]; rw [map_span]; rw [image_singleton]; rw [coe_coe]; rw [quotMapEquivQuotQuotMap_symm_apply]; rw [span_union]; rw [span_eq]; rw [sup_comm]; rw [← image_singleton]; rw [← map_span]; rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]; rw [Ideal.mk_ker]

end KummerDedekind
