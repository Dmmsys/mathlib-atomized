/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!

# Unramified and ramification index

We connect `Ideal.ramificationIdx` to the commutative algebra notion predicate of `IsUnramifiedAt`.

## Main result
- `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`:
  Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S ⊇ R` be a Dedekind domain
  that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`.

-/

public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation3 "e(" P "|" R ")" =>
  Ideal.ramificationIdx P R

open IsLocalRing Algebra

/--
lemma `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt` / 引理 `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`

English:
lemma Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  proof: p.ramificationIdx_eq_one R

中文:
引理 理想.ramificationIdx_eq_one_of_isUnramifiedAt
  证明: p.ramificationIdx_eq_one R

Depends on / 依赖: p.ramificationIdx_eq_one, ramificationIdx_eq_one
-/
lemma Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    {p : Ideal S} [p.IsPrime] [IsUnramifiedAt R p] [EssFiniteType R S] :
    e(p|R) = 1 :=
  p.ramificationIdx_eq_one R

variable (R) in
/--
lemma `IsUnramifiedAt.of_liesOver_of_ne_bot` / 引理 `IsUnramifiedAt.of_liesOver_of_ne_bot`

English:
lemma IsUnramifiedAt.of_liesOver_of_ne_bot
  proof: by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  let := Localization.AtPrime.algebraOfLiesOver p₀ p
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver p₀ P
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := Algebra.EssFiniteType.isNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq R p₀ P).mp ‹_›
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [this]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hp Ideal.map_comap_le]; rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le]
  intro H
  have := Ideal.ramificationIdx'_eq_one_of_map_localization
    (hp₀ ▸ Ideal.map_comap_le) (hP₂ hp) hP₁ h₂
  rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff (hp₀ ▸ Ideal.map_comap_le)] at this
  replace H := Ideal.map_mono (f := algebraMap S T) H
  rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_pow] at H
  refine this (H.trans (Ideal.pow_right_mono ?_ _))
  exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

中文:
引理 IsUnramifiedAt.of_liesOver_of_ne_bot
  证明: by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  let := Localization.AtPrime.algebraOfLiesOver p₀ p
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver p₀ P
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := Algebra.EssFiniteType.isNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq R p₀ P).mp ‹_›
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [this]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hp Ideal.map_comap_le]; rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le]
  intro H
  have := Ideal.ramificationIdx'_eq_one_of_map_localization
    (hp₀ ▸ Ideal.map_comap_le) (hP₂ hp) hP₁ h₂
  rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff (hp₀ ▸ Ideal.map_comap_le)] at this
  replace H := Ideal.map_mono (f := algebraMap S T) H
  rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_pow] at H
  refine this (H.trans (Ideal.pow_right_mono ?_ _))
  exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

Depends on / 依赖: Algebra, Algebra.EssFiniteType.isNoetherianRing, Algebra.isSeparable_tower_bot, AtPrime, EssFiniteType, Ideal.LiesOver.over, LiesOver, Localization, Localization.AtPrime.algebraOfLiesOver, P.LiesOver, P.under, algebraOfLiesOver, isNoetherianRing, isSeparable_tower_bot, isUnramifiedAt_iff_map_eq, of_comp, p.under
-/
lemma IsUnramifiedAt.of_liesOver_of_ne_bot
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] (hP₁ : P.primeCompl <= nonZeroDivisors T) (hP₂ : p != ⊥ -> P != ⊥) :
    IsUnramifiedAt R p := by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  let := Localization.AtPrime.algebraOfLiesOver p₀ p
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver p₀ P
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := Algebra.EssFiniteType.isNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq R p₀ P).mp ‹_›
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S]; rw [← Ideal.map_map]; rw [this]; rw [Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hp Ideal.map_comap_le]; rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le]
  intro H
  have := Ideal.ramificationIdx'_eq_one_of_map_localization
    (hp₀ ▸ Ideal.map_comap_le) (hP₂ hp) hP₁ h₂
  rw [← not_ne_iff]; rw [Ideal.ramificationIdx'_ne_one_iff (hp₀ ▸ Ideal.map_comap_le)] at this
  replace H := Ideal.map_mono (f := algebraMap S T) H
  rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_pow] at H
  refine this (H.trans (Ideal.pow_right_mono ?_ _))
  exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

section IsUnramifiedIn

namespace Algebra

variable (R) in
/--
lemma `IsUnramifiedAt.of_liesOver` / 引理 `IsUnramifiedAt.of_liesOver`

English:
lemma IsUnramifiedAt.of_liesOver
  proof: IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)

中文:
引理 IsUnramifiedAt.of_liesOver
  证明: IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)

Depends on / 依赖: Ideal.ne_bot_of_liesOver_of_ne_bot, IsUnramifiedAt, IsUnramifiedAt.of_liesOver_of_ne_bot, P.primeCompl_le_nonZeroDivisors, ne_bot_of_liesOver_of_ne_bot, of_liesOver_of_ne_bot, primeCompl_le_nonZeroDivisors
-/
lemma IsUnramifiedAt.of_liesOver
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [Module.IsTorsionFree S T] : IsUnramifiedAt R p :=
  IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)


/-- Let `R` be a domain of characteristic 0, finite rank over `ℤ`, `S` be a Dedekind domain
that is a finite `R`-algebra. Let `p` be a prime of `S`, then `p` is unramified iff `e(p) = 1`. -/
@[deprecated "Use `Ideal.ramificationIdx'_eq_one_iff` instead." (since := "2026-06-30")]
/--
lemma `isUnramifiedAt_iff_of_isDedekindDomain` / 引理 `isUnramifiedAt_iff_of_isDedekindDomain`

English:
lemma isUnramifiedAt_iff_of_isDedekindDomain
  proof: Ideal.ramificationIdx'_eq_one_iff.symm

中文:
引理 isUnramifiedAt_iff_of_isDedekindDomain
  证明: Ideal.ramificationIdx'_eq_one_iff.symm

Depends on / 依赖: Ideal.ramificationIdx, _eq_one_iff, _eq_one_iff.symm, ramificationIdx
-/
lemma isUnramifiedAt_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [EssFiniteType R S] [IsDomain R]
    [Module.Finite Int R] [CharZero R] [Algebra.IsIntegral R S] :
    Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1 :=
  Ideal.ramificationIdx'_eq_one_iff.symm

/--
theorem `isUnramifiedAt_bot` / 定理 `isUnramifiedAt_bot`

English:
theorem isUnramifiedAt_bot
  statement: [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S] [CharZero R]
  proof: by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal S)) := IsFractionRing.toField S
  have : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)
  let := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal S))
  have : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime ⊥) :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) (Localization.AtPrime (⊥ : Ideal S))
  have : FormallyUnramified (FractionRing R) (Localization.AtPrime (⊥ : Ideal S)) :=
    FormallyUnramified.of_isSeparable _ _
  exact FormallyUnramified.comp R (FractionRing R) (Localization.AtPrime ⊥)

中文:
定理 isUnramifiedAt_bot
  结论: [是整环 R] [是整环 S] [模.是无挠 R S] [特征零 R]
  证明: by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal S)) := IsFractionRing.toField S
  have : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)
  let := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal S))
  have : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime ⊥) :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) (Localization.AtPrime (⊥ : Ideal S))
  have : FormallyUnramified (FractionRing R) (Localization.AtPrime (⊥ : Ideal S)) :=
    FormallyUnramified.of_isSeparable _ _
  exact FormallyUnramified.comp R (FractionRing R) (Localization.AtPrime ⊥)

Depends on / 依赖: AtPrime, FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.primeCompl_bot, IsFractionRing, IsFractionRing.injective, IsFractionRing.toField, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, Localization.isLocalization, algebraMap_eq, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, injective, isLocalization, primeCompl, primeCompl_bot, toField
-/
theorem isUnramifiedAt_bot [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedAt R (⊥ : Ideal S) := by
  have : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal S).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal S)) := IsFractionRing.toField S
  have : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [faithfulSMul_iff_algebraMap_injective]; rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective R S)
  let := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal S))
  have : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime ⊥) :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) (Localization.AtPrime (⊥ : Ideal S))
  have : FormallyUnramified (FractionRing R) (Localization.AtPrime (⊥ : Ideal S)) :=
    FormallyUnramified.of_isSeparable _ _
  exact FormallyUnramified.comp R (FractionRing R) (Localization.AtPrime ⊥)

/--
theorem `isUnramifiedIn_bot` / 定理 `isUnramifiedIn_bot`

English:
theorem isUnramifiedIn_bot
  statement: [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
  proof: by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

中文:
定理 isUnramifiedIn_bot
  结论: [是整环 R] [是整环 S] [忠实标量乘法 R S] [特征零 R]
  证明: by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

Depends on / 依赖: Ideal.eq_bot_of_liesOver_bot, eq_bot_of_liesOver_bot, isUnramifiedAt_bot
-/
theorem isUnramifiedIn_bot [IsDomain R] [IsDomain S] [FaithfulSMul R S] [CharZero R]
    [Algebra.IsIntegral R S] : IsUnramifiedIn S (⊥ : Ideal R) := by
  intro P _ hP
  simpa [Ideal.eq_bot_of_liesOver_bot R P] using isUnramifiedAt_bot

/--
theorem `isUnramifiedIn_iff_forall_of_isDedekindDomain'` / 定理 `isUnramifiedIn_iff_forall_of_isDedekindDomain'`

English:
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain'
  statement: [IsDomain R] [IsDedekindDomain S]
  proof: ⟨fun h P hP hlo => h P hP.isPrime hlo,
    fun h P hP hlo => h P (hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)) hlo⟩

中文:
定理 isUnramifiedIn_iff_对任意_of_isDedekindDomain'
  结论: [是整环 R] [是Dedekind整环 S]
  证明: ⟨fun h P hP hlo => h P hP.isPrime hlo,
    fun h P hP hlo => h P (hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)) hlo⟩

Depends on / 依赖: Ideal.ne_bot_of_liesOver_of_ne_bot, hP.isMaximal, hP.isPrime, isMaximal, isPrime, ne_bot_of_liesOver_of_ne_bot
-/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain' [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] {p : Ideal R} (hp : p != ⊥) :
    IsUnramifiedIn S p ↔
      forall (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p -> IsUnramifiedAt R P :=
  ⟨fun h P hP hlo => h P hP.isPrime hlo,
    fun h P hP hlo => h P (hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)) hlo⟩

/--
theorem `isUnramifiedIn_iff_forall_of_isDedekindDomain` / 定理 `isUnramifiedIn_iff_forall_of_isDedekindDomain`

English:
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain
  statement: [IsDomain R] [IsDedekindDomain S]
  proof: by
  refine ⟨fun h P hP hlo => h P hP.isPrime hlo, fun h P hP hlo => ?_⟩
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact isUnramifiedAt_bot
  · exact h P (hP.isMaximal hPbot) hlo

中文:
定理 isUnramifiedIn_iff_对任意_of_isDedekindDomain
  结论: [是整环 R] [是Dedekind整环 S]
  证明: by
  refine ⟨fun h P hP hlo => h P hP.isPrime hlo, fun h P hP hlo => ?_⟩
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact isUnramifiedAt_bot
  · exact h P (hP.isMaximal hPbot) hlo

Depends on / 依赖: eq_or_ne, hP.isMaximal, hP.isPrime, isMaximal, isPrime, isUnramifiedAt_bot
-/
theorem isUnramifiedIn_iff_forall_of_isDedekindDomain [IsDomain R] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [CharZero R] [Algebra.IsIntegral R S] {p : Ideal R} :
    IsUnramifiedIn S p ↔
      forall (P : Ideal S) (_ : P.IsMaximal), P.LiesOver p -> IsUnramifiedAt R P := by
  refine ⟨fun h P hP hlo => h P hP.isPrime hlo, fun h P hP hlo => ?_⟩
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact isUnramifiedAt_bot
  · exact h P (hP.isMaximal hPbot) hlo

/--
theorem `IsUnramifiedIn.ramificationIdx_eq_one` / 定理 `IsUnramifiedIn.ramificationIdx_eq_one`

English:
theorem IsUnramifiedIn.ramificationIdx_eq_one
  statement: [IsDomain R]
  proof: Ideal.ramificationIdx_eq_one_iff.mpr
    (hunr 𝔓 inferInstance hP)

中文:
定理 IsUnramifiedIn.ramificationIdx_eq_one
  结论: [是整环 R]
  证明: Ideal.ramificationIdx_eq_one_iff.mpr
    (hunr 𝔓 inferInstance hP)

Depends on / 依赖: Ideal.ramificationIdx_eq_one_iff.mpr, ramificationIdx_eq_one_iff
-/
theorem IsUnramifiedIn.ramificationIdx_eq_one [IsDomain R]
    [Module.Finite Int R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} (hunr : IsUnramifiedIn S 𝔭) {𝔓 : Ideal S}
    [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx 𝔓 R = 1 :=
  Ideal.ramificationIdx_eq_one_iff.mpr
    (hunr 𝔓 inferInstance hP)

/--
theorem `isUnramifiedIn_iff_forall_ramificationIdx_eq_one` / 定理 `isUnramifiedIn_iff_forall_ramificationIdx_eq_one`

English:
theorem isUnramifiedIn_iff_forall_ramificationIdx_eq_one
  statement: [IsDomain R]
  proof: by
  refine ⟨fun hunr 𝔓 _ hP => hunr.ramificationIdx_eq_one hP, fun h 𝔓 _ hP => ?_⟩
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact h 𝔓 hP

中文:
定理 isUnramifiedIn_iff_对任意_ramificationIdx_eq_one
  结论: [是整环 R]
  证明: by
  refine ⟨fun hunr 𝔓 _ hP => hunr.ramificationIdx_eq_one hP, fun h 𝔓 _ hP => ?_⟩
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact h 𝔓 hP

Depends on / 依赖: Ideal.ramificationIdx_eq_one_iff, hunr.ramificationIdx_eq_one, ramificationIdx_eq_one, ramificationIdx_eq_one_iff
-/
theorem isUnramifiedIn_iff_forall_ramificationIdx_eq_one [IsDomain R]
    [Module.Finite Int R] [CharZero R] [EssFiniteType R S]
    [Algebra.IsIntegral R S] {𝔭 : Ideal R} :
    IsUnramifiedIn S 𝔭 ↔
      forall (𝔓 : Ideal S) [𝔓.IsPrime], 𝔓.LiesOver 𝔭 -> Ideal.ramificationIdx 𝔓 R = 1 := by
  refine ⟨fun hunr 𝔓 _ hP => hunr.ramificationIdx_eq_one hP, fun h 𝔓 _ hP => ?_⟩
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact h 𝔓 hP

end Algebra

end IsUnramifiedIn
