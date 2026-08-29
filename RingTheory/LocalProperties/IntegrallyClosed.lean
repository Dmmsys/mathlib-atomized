/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# `IsIntegrallyClosed` is a local property

In this file, we prove that `IsIntegrallyClosed` is a local property.

## Main results

* `IsIntegrallyClosed.of_localization_maximal` : An integral domain `R` is integral closed
  if `Rₘ` is integral closed for any maximal ideal `m` of `R`.
-/

public section

open scoped nonZeroDivisors

open Localization Ideal IsLocalization

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/--
theorem `IsIntegrallyClosed.iInf` / 定理 `IsIntegrallyClosed.iInf`

English:
theorem IsIntegrallyClosed.iInf
  statement: {ι : Type*} (S : ι -> Subalgebra R K)
  proof: by
  refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => CanLift.prf x (Algebra.mem_iInf.mpr ?_))
  intro i
  have le : (⨅ i : ι, S i : Subalgebra R K) <= S i := iInf_le S i
  algebraize [(Subalgebra.inclusion le).toRingHom]
  have : IsScalarTower ↥(⨅ i, S i) (S i) K := Subalgebra.inclusion.isScalarTower_right le K
  rcases (isIntegrallyClosed_iff K).mp (h i) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rwa [← hy]

中文:
定理 是整闭.iInf
  结论: {ι : 类型} (S : ι -> 子代数 R K)
  证明: by
  refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => CanLift.prf x (Algebra.mem_iInf.mpr ?_))
  intro i
  have le : (⨅ i : ι, S i : Subalgebra R K) <= S i := iInf_le S i
  algebraize [(Subalgebra.inclusion le).toRingHom]
  have : IsScalarTower ↥(⨅ i, S i) (S i) K := Subalgebra.inclusion.isScalarTower_right le K
  rcases (isIntegrallyClosed_iff K).mp (h i) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rwa [← hy]

Depends on / 依赖: Algebra, Algebra.mem_iInf.mpr, CanLift, CanLift.prf, IsScalarTower, Subalgebra, Subalgebra.inclusion, Subalgebra.inclusion.isScalarTower_right, algebraize, hx.tower_top, iInf_le, inclusion, isIntegrallyClosed_iff, isScalarTower_right, mem_iInf, toRingHom, tower_top
-/
theorem IsIntegrallyClosed.iInf {ι : Type*} (S : ι -> Subalgebra R K)
    (h : forall i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed (⨅ i, S i : Subalgebra R K) := by
  refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => CanLift.prf x (Algebra.mem_iInf.mpr ?_))
  intro i
  have le : (⨅ i : ι, S i : Subalgebra R K) <= S i := iInf_le S i
  algebraize [(Subalgebra.inclusion le).toRingHom]
  have : IsScalarTower ↥(⨅ i, S i) (S i) K := Subalgebra.inclusion.isScalarTower_right le K
  rcases (isIntegrallyClosed_iff K).mp (h i) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rwa [← hy]

/--
theorem `IsIntegrallyClosed.of_iInf_eq_bot` / 定理 `IsIntegrallyClosed.of_iInf_eq_bot`

English:
theorem IsIntegrallyClosed.of_iInf_eq_bot
  statement: {ι : Type*} (S : ι -> Subalgebra R K)
  proof: have f : (⊥ : Subalgebra R K) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K)
  (IsIntegrallyClosed.iInf S h).of_equiv (hs ▸ f).toRingEquiv

中文:
定理 是整闭.of_iInf_eq_bot
  结论: {ι : 类型} (S : ι -> 子代数 R K)
  证明: have f : (⊥ : Subalgebra R K) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K)
  (IsIntegrallyClosed.iInf S h).of_equiv (hs ▸ f).toRingEquiv

Depends on / 依赖: Algebra, Algebra.botEquivOfInjective, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsIntegrallyClosed, IsIntegrallyClosed.iInf, Subalgebra, algebraMap_injective, botEquivOfInjective, of_equiv, toRingEquiv
-/
theorem IsIntegrallyClosed.of_iInf_eq_bot {ι : Type*} (S : ι -> Subalgebra R K)
    (h : forall i : ι, IsIntegrallyClosed (S i)) (hs : ⨅ i : ι, S i = ⊥) : IsIntegrallyClosed R :=
  have f : (⊥ : Subalgebra R K) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K)
  (IsIntegrallyClosed.iInf S h).of_equiv (hs ▸ f).toRingEquiv

/--
theorem `IsIntegrallyClosed.of_localization_submonoid` / 定理 `IsIntegrallyClosed.of_localization_submonoid`

English:
theorem IsIntegrallyClosed.of_localization_submonoid
  statement: [IsDomain R] {ι : Type*} (S : ι -> Submonoid R)
  proof: IsIntegrallyClosed.of_iInf_eq_bot (fun i => Localization.subalgebra (FractionRing R) (S i) (h i))
    (fun i => (hi i).of_equiv (IsLocalization.algEquiv (S i) (Localization (S i)) _).toRingEquiv) hs

中文:
定理 是整闭.of_localization_submonoid
  结论: [是整环 R] {ι : 类型} (S : ι -> 子幺半群 R)
  证明: IsIntegrallyClosed.of_iInf_eq_bot (fun i => Localization.subalgebra (FractionRing R) (S i) (h i))
    (fun i => (hi i).of_equiv (IsLocalization.algEquiv (S i) (Localization (S i)) _).toRingEquiv) hs

Depends on / 依赖: FractionRing, IsIntegrallyClosed, IsIntegrallyClosed.of_iInf_eq_bot, IsLocalization, IsLocalization.algEquiv, Localization, Localization.subalgebra, algEquiv, of_equiv, of_iInf_eq_bot, subalgebra, toRingEquiv
-/
theorem IsIntegrallyClosed.of_localization_submonoid [IsDomain R] {ι : Type*} (S : ι -> Submonoid R)
    (h : forall i : ι, S i <= R⁰) (hi : forall i : ι, IsIntegrallyClosed (Localization (S i)))
    (hs : ⨅ i : ι, Localization.subalgebra (FractionRing R) (S i) (h i) = ⊥) :
    IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_iInf_eq_bot (fun i => Localization.subalgebra (FractionRing R) (S i) (h i))
    (fun i => (hi i).of_equiv (IsLocalization.algEquiv (S i) (Localization (S i)) _).toRingEquiv) hs

/--
theorem `IsIntegrallyClosed.of_localization` / 定理 `IsIntegrallyClosed.of_localization`

English:
theorem IsIntegrallyClosed.of_localization
  statement: [IsDomain R] (S : Set (PrimeSpectrum R))
  proof: by
  apply IsIntegrallyClosed.of_localization_submonoid (fun p : S => p.1.1.primeCompl)
    (fun p => p.1.1.primeCompl_le_nonZeroDivisors) (fun p => h p.1 p.2)
  ext x
  simp only [← hs, Algebra.mem_iInf, Subtype.forall]

中文:
定理 是整闭.of_localization
  结论: [是整环 R] (S : 集合 (素谱 R))
  证明: by
  apply IsIntegrallyClosed.of_localization_submonoid (fun p : S => p.1.1.primeCompl)
    (fun p => p.1.1.primeCompl_le_nonZeroDivisors) (fun p => h p.1 p.2)
  ext x
  simp only [← hs, Algebra.mem_iInf, Subtype.forall]

Depends on / 依赖: Algebra, Algebra.mem_iInf, IsIntegrallyClosed, IsIntegrallyClosed.of_localization_submonoid, Subtype, Subtype.forall, mem_iInf, of_localization_submonoid, primeCompl, primeCompl_le_nonZeroDivisors
-/
theorem IsIntegrallyClosed.of_localization [IsDomain R] (S : Set (PrimeSpectrum R))
    (h : forall p in S, IsIntegrallyClosed (Localization.AtPrime p.1))
    (hs : ⨅ p in S, (Localization.subalgebra (FractionRing R) p.1.primeCompl
      p.1.primeCompl_le_nonZeroDivisors) = ⊥) : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_submonoid (fun p : S => p.1.1.primeCompl)
    (fun p => p.1.1.primeCompl_le_nonZeroDivisors) (fun p => h p.1 p.2)
  ext x
  simp only [← hs, Algebra.mem_iInf, Subtype.forall]

/--
theorem `IsIntegrallyClosed.of_localization_maximal` / 定理 `IsIntegrallyClosed.of_localization_maximal`

English:
theorem IsIntegrallyClosed.of_localization_maximal
  statement: [IsDomain R]
  proof: by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  refine of_localization (.range MaximalSpectrum.toPrimeSpectrum) (fun _ => ?_) ?_
  · rintro ⟨p, rfl⟩
    exact h p.asIdeal (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf)
  · rw [iInf_range]
    convert! MaximalSpectrum.iInf_localization_eq_bot R (FractionRing R)
    rw [subalgebra.ofField_eq]; rw [MaximalSpectrum.toPrimeSpectrum]

中文:
定理 是整闭.of_localization_maximal
  结论: [是整环 R]
  证明: by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  refine of_localization (.range MaximalSpectrum.toPrimeSpectrum) (fun _ => ?_) ?_
  · rintro ⟨p, rfl⟩
    exact h p.asIdeal (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf)
  · rw [iInf_range]
    convert! MaximalSpectrum.iInf_localization_eq_bot R (FractionRing R)
    rw [subalgebra.ofField_eq]; rw [MaximalSpectrum.toPrimeSpectrum]

Depends on / 依赖: FractionRing, IsField, MaximalSpectrum, MaximalSpectrum.iInf_localization_eq_bot, MaximalSpectrum.toPrimeSpectrum, Ring.ne_bot_of_isMaximal_of_not_isField, asIdeal, convert, hf.toField.instIsIntegrallyClosed, iInf_localization_eq_bot, iInf_range, instIsIntegrallyClosed, isMaximal, ne_bot_of_isMaximal_of_not_isField, ofField_eq, of_localization, p.asIdeal, p.isMaximal, subalgebra, subalgebra.ofField_eq
-/
theorem IsIntegrallyClosed.of_localization_maximal [IsDomain R]
    (h : forall p : Ideal R, p != ⊥ -> [p.IsMaximal] -> IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  refine of_localization (.range MaximalSpectrum.toPrimeSpectrum) (fun _ => ?_) ?_
  · rintro ⟨p, rfl⟩
    exact h p.asIdeal (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf)
  · rw [iInf_range]
    convert! MaximalSpectrum.iInf_localization_eq_bot R (FractionRing R)
    rw [subalgebra.ofField_eq]; rw [MaximalSpectrum.toPrimeSpectrum]

/--
theorem `isIntegrallyClosed_ofLocalizationMaximal` / 定理 `isIntegrallyClosed_ofLocalizationMaximal`

English:
theorem isIntegrallyClosed_ofLocalizationMaximal
  proof: fun _ _ h _ => IsIntegrallyClosed.of_localization_maximal fun p _ hpm => h p hpm

中文:
定理 is整数egrallyClosed_ofLocalizationMaximal
  证明: fun _ _ h _ => IsIntegrallyClosed.of_localization_maximal fun p _ hpm => h p hpm

Depends on / 依赖: IsIntegrallyClosed, IsIntegrallyClosed.of_localization_maximal, of_localization_maximal
-/
theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ => ([IsDomain R] -> IsIntegrallyClosed R) :=
  fun _ _ h _ => IsIntegrallyClosed.of_localization_maximal fun p _ hpm => h p hpm

variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/--
theorem `IsIntegrallyClosed.of_isLocalization_maximal` / 定理 `IsIntegrallyClosed.of_isLocalization_maximal`

English:
theorem IsIntegrallyClosed.of_isLocalization_maximal
  statement: [IsDomain R]
  proof: .of_localization_maximal
  (fun P _ _ => .of_equiv <| ringEquivOfRingEquiv (Rₚ P) _ (RingEquiv.refl R) P.primeCompl.map_id)

中文:
定理 是整闭.of_isLocalization_maximal
  结论: [是整环 R]
  证明: .of_localization_maximal
  (fun P _ _ => .of_equiv <| ringEquivOfRingEquiv (Rₚ P) _ (RingEquiv.refl R) P.primeCompl.map_id)

Depends on / 依赖: of_localization_maximal
-/
theorem IsIntegrallyClosed.of_isLocalization_maximal [IsDomain R]
    (h : forall (P : Ideal R) [P.IsMaximal], IsIntegrallyClosed (Rₚ P)) :
    IsIntegrallyClosed R := .of_localization_maximal
  (fun P _ _ => .of_equiv <| ringEquivOfRingEquiv (Rₚ P) _ (RingEquiv.refl R) P.primeCompl.map_id)
