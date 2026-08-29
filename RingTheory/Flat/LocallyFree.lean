/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# A finite flat module `M` is locally free if `rankAtStalk M` is constant
-/

public section

namespace Module

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Flat R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]

open LocalizedModule

attribute [local instance] Module.free_of_flat_of_isLocalRing

/--
lemma `bijective_of_surjective_of_rankAtStalk_eq` / 引理 `bijective_of_surjective_of_rankAtStalk_eq`

English:
lemma bijective_of_surjective_of_rankAtStalk_eq
  statement: {φ : M ->ₗ[R] N} (hs : Function.Surjective φ)
  proof: bijective_of_localized_maximal φ fun m _ =>
    OrzechProperty.bijective_of_surjective_of_finrank_le (map m.primeCompl φ)
      (map_surjective m.primeCompl φ hs) (h m).le

中文:
引理 bijective_of_surjective_of_rankAtStalk_eq
  结论: {φ : M ->ₗ[R] N} (hs : 函数.满射 φ)
  证明: bijective_of_localized_maximal φ fun m _ =>
    OrzechProperty.bijective_of_surjective_of_finrank_le (map m.primeCompl φ)
      (map_surjective m.primeCompl φ hs) (h m).le

Depends on / 依赖: OrzechProperty, OrzechProperty.bijective_of_surjective_of_finrank_le, bijective_of_localized_maximal, bijective_of_surjective_of_finrank_le, m.primeCompl, map_surjective, primeCompl
-/
lemma bijective_of_surjective_of_rankAtStalk_eq {φ : M ->ₗ[R] N} (hs : Function.Surjective φ)
    (h : forall (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective φ :=
  bijective_of_localized_maximal φ fun m _ =>
    OrzechProperty.bijective_of_surjective_of_finrank_le (map m.primeCompl φ)
      (map_surjective m.primeCompl φ hs) (h m).le

variable (M) in
/--
theorem `Free.away_of_finite_of_flat_of_rankAtStalk_constant` / 定理 `Free.away_of_finite_of_flat_of_rankAtStalk_constant`

English:
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant
  statement: (p : Ideal R) [p.IsPrime]
  proof: by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  · let Rₚ := Localization.AtPrime p
    let n := rankAtStalk M ⟨p, inferInstance⟩
    let f : (Fin n ->₀ R) ->ₗ[R] Fin n ->₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
    let g : M ->ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
    obtain ⟨φ, -, -, hφps⟩ := exists_localizedMap_surjective_of_surjective p.primeCompl f g
      ((finBasis Rₚ (LocalizedModule.AtPrime p M)).repr.restrictScalars R).symm.surjective
    obtain ⟨a, hap, hφas⟩ := by
      refine exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p φ ?_
      simpa [LocalizedModule.coe_map_eq f g]
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n ->₀ R)) :=
      free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n ->₀ R))
    let φₐ : LocalizedModule.Away a (Fin n ->₀ R) ->ₗ[Localization.Away a] LocalizedModule.Away a M :=
      LocalizedModule.map (Submonoid.powers a) φ
refine ⟨a, hap, Module.Free.of_equiv LinearEquiv.ofBijective φₐ
bijective_of_surjective_of_rankAtStalk_eq hφas fun m _ => ?_⟩
    obtain ⟨𝔪, _, hm𝔪⟩ : exists 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
        (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ <= 𝔪 :=
      (m.comap (algebraMap R (Localization.Away a))).exists_le_maximal Ideal.IsPrime.ne_top'
    simp [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) _),
      rankAtStalk_eq_of_le_of_finite_of_flat' M hm𝔪, h 𝔪, n]

中文:
定理 自由.away_of_finite_of_flat_of_rankAtStalk_constant
  结论: (p : 理想 R) [p.是素]
  证明: by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  · let Rₚ := Localization.AtPrime p
    let n := rankAtStalk M ⟨p, inferInstance⟩
    let f : (Fin n ->₀ R) ->ₗ[R] Fin n ->₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
    let g : M ->ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
    obtain ⟨φ, -, -, hφps⟩ := exists_localizedMap_surjective_of_surjective p.primeCompl f g
      ((finBasis Rₚ (LocalizedModule.AtPrime p M)).repr.restrictScalars R).symm.surjective
    obtain ⟨a, hap, hφas⟩ := by
      refine exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p φ ?_
      simpa [LocalizedModule.coe_map_eq f g]
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n ->₀ R)) :=
      free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n ->₀ R))
    let φₐ : LocalizedModule.Away a (Fin n ->₀ R) ->ₗ[Localization.Away a] LocalizedModule.Away a M :=
      LocalizedModule.map (Submonoid.powers a) φ
refine ⟨a, hap, Module.Free.of_equiv LinearEquiv.ofBijective φₐ
bijective_of_surjective_of_rankAtStalk_eq hφas fun m _ => ?_⟩
    obtain ⟨𝔪, _, hm𝔪⟩ : exists 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
        (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ <= 𝔪 :=
      (m.comap (algebraMap R (Localization.Away a))).exists_le_maximal Ideal.IsPrime.ne_top'
    simp [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) _),
      rankAtStalk_eq_of_le_of_finite_of_flat' M hm𝔪, h 𝔪, n]

Depends on / 依赖: Algebra, Algebra.linearMap, AtPrime, Finsupp, Finsupp.mapRange.linearMap, Ideal.IsPrime.one_notMem, IsPrime, Localization, Localization.AtPrime, Localization.Away, LocalizedModule, LocalizedModule.AtPrime, LocalizedModule.Away, LocalizedModule.mkLinearMap, Module, Module.Free.of_subsingleton, exists_localizedMap_surjective_of_sur, linearMap, mapRange, mkLinearMap
-/
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant (p : Ideal R) [p.IsPrime]
    (h : forall (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    exists a ∉ p, Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  · let Rₚ := Localization.AtPrime p
    let n := rankAtStalk M ⟨p, inferInstance⟩
    let f : (Fin n ->₀ R) ->ₗ[R] Fin n ->₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
    let g : M ->ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
    obtain ⟨φ, -, -, hφps⟩ := exists_localizedMap_surjective_of_surjective p.primeCompl f g
      ((finBasis Rₚ (LocalizedModule.AtPrime p M)).repr.restrictScalars R).symm.surjective
    obtain ⟨a, hap, hφas⟩ := by
      refine exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p φ ?_
      simpa [LocalizedModule.coe_map_eq f g]
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n ->₀ R)) :=
      free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n ->₀ R))
    let φₐ : LocalizedModule.Away a (Fin n ->₀ R) ->ₗ[Localization.Away a] LocalizedModule.Away a M :=
      LocalizedModule.map (Submonoid.powers a) φ
refine ⟨a, hap, Module.Free.of_equiv LinearEquiv.ofBijective φₐ
bijective_of_surjective_of_rankAtStalk_eq hφas fun m _ => ?_⟩
    obtain ⟨𝔪, _, hm𝔪⟩ : exists 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
        (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ <= 𝔪 :=
      (m.comap (algebraMap R (Localization.Away a))).exists_le_maximal Ideal.IsPrime.ne_top'
    simp [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) _),
      rankAtStalk_eq_of_le_of_finite_of_flat' M hm𝔪, h 𝔪, n]

end Module
