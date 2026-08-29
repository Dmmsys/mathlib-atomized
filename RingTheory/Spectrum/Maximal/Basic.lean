/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Maximal spectrum of a commutative (semi)ring

Basic properties the maximal spectrum of a ring.
-/

@[expose] public section

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
/--
Definition of `equivSubtype` / `equivSubtype` 的定义

English:
definition equivSubtype
  signature: : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  body: ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩

中文:
定义 equivSubtype
  签名: : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  定义体: ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩

Depends on / 依赖: I.asIdeal, asIdeal
-/
def equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩

/--
theorem `range_asIdeal` / 定理 `range_asIdeal`

English:
theorem range_asIdeal
  statement: Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal}
  proof: Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isMaximal,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

中文:
定理 range_asIdeal
  结论: Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal}
  证明: Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isMaximal,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

Depends on / 依赖: Set.ext, Set.mem_ofPred.mp, Set.mem_ofPred.mpr, Set.mem_range.mp, Set.mem_range.mpr, isMaximal, j.isMaximal, mem_ofPred, mem_range
-/
theorem range_asIdeal : Set.range MaximalSpectrum.asIdeal = {J : Ideal R | J.IsMaximal} :=
  Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isMaximal,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nonempty MaximalSpectrum R
  body: let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

中文:
实例 [Nontrivial
  签名: R] : Nonempty MaximalSpectrum R
  定义体: let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

Depends on / 依赖: Ideal.exists_maximal, exists_maximal
-/
instance [Nontrivial R] : Nonempty MaximalSpectrum R :=
  let ⟨I, hI⟩ := Ideal.exists_maximal R
  ⟨⟨I, hI⟩⟩

/--
Definition of `toPrimeSpectrum` / `toPrimeSpectrum` 的定义

English:
definition toPrimeSpectrum
  signature: (x : MaximalSpectrum R)
  body: ⟨x.asIdeal, x.isMaximal.isPrime⟩

中文:
定义 toPrimeSpectrum
  签名: (x : MaximalSpectrum R)
  定义体: ⟨x.asIdeal, x.isMaximal.isPrime⟩

Depends on / 依赖: asIdeal, isMaximal, isPrime, x.asIdeal, x.isMaximal.isPrime
-/
def toPrimeSpectrum (x : MaximalSpectrum R) : PrimeSpectrum R :=
  ⟨x.asIdeal, x.isMaximal.isPrime⟩

/--
theorem `toPrimeSpectrum_injective` / 定理 `toPrimeSpectrum_injective`

English:
theorem toPrimeSpectrum_injective
  statement: (@toPrimeSpectrum R _).Injective
  proof: fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using! PrimeSpectrum.ext_iff.mp h

中文:
定理 toPrimeSpectrum_injective
  结论: (@toPrimeSpectrum R _).Injective
  证明: fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using! PrimeSpectrum.ext_iff.mp h

Depends on / 依赖: MaximalSpectrum, MaximalSpectrum.mk.injEq, PrimeSpectrum, PrimeSpectrum.ext_iff.mp, ext_iff
-/
theorem toPrimeSpectrum_injective : (@toPrimeSpectrum R _).Injective := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simpa only [MaximalSpectrum.mk.injEq] using! PrimeSpectrum.ext_iff.mp h

/--
theorem `isCoprime_of_ne` / 定理 `isCoprime_of_ne`

English:
theorem isCoprime_of_ne
  given: {I J : MaximalSpectrum R} (h : I != J)
  statement: IsCoprime I.1 J.1
  proof: Ideal.isCoprime_iff_sup_eq.mpr I.2.coprime_of_ne J.2 mt MaximalSpectrum.ext h

中文:
定理 isCoprime_of_ne
  条件: {I J : MaximalSpectrum R} (h : I != J)
  结论: IsCoprime I.1 J.1
  证明: Ideal.isCoprime_iff_sup_eq.mpr I.2.coprime_of_ne J.2 mt MaximalSpectrum.ext h

Depends on / 依赖: Ideal.isCoprime_iff_sup_eq.mpr, MaximalSpectrum, MaximalSpectrum.ext, coprime_of_ne, isCoprime_iff_sup_eq
-/
theorem isCoprime_of_ne {I J : MaximalSpectrum R} (h : I != J) : IsCoprime I.1 J.1 :=
Ideal.isCoprime_iff_sup_eq.mpr I.2.coprime_of_ne J.2 mt MaximalSpectrum.ext h

end MaximalSpectrum
