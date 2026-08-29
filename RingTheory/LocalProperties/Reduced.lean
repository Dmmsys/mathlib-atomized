/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# `IsReduced` is a local property

In this file, we prove that `IsReduced` is a local property.

## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `isReduced_localizationPreserves` : `M⁻¹R` is reduced if `R` is reduced.
* `isReduced_ofLocalizationMaximal` : `R` is reduced if `Rₘ` is reduced for all maximal ideal `m`.

-/

public section

/--
theorem `isReduced_localizationPreserves` / 定理 `isReduced_localizationPreserves`

English:
theorem isReduced_localizationPreserves
  statement: LocalizationPreserves fun R _ => IsReduced R
  proof: by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain

中文:
定理 isReduced_localizationPreserves
  结论: LocalizationPreserves fun R _ => IsReduced R
  证明: by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain

Depends on / 依赖: IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.surj, algebraMap, apply_fun, congr_arg, eq_iff_exists, introv, map_pow, map_zero, mul_assoc, mul_left_comm, mul_pow, mul_zero, n.succ, pow_succ, replace, zero_mul
-/
theorem isReduced_localizationPreserves : LocalizationPreserves fun R _ => IsReduced R := by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm]; rw [← pow_succ']; rw [← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj]; rw [hx]; rw [zero_mul]; rw [IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩

instance {R : Type*} [CommRing R] (M : Submonoid R) [IsReduced R] : IsReduced (Localization M) :=
  isReduced_localizationPreserves M _ inferInstance

/--
theorem `isReduced_ofLocalizationMaximal` / 定理 `isReduced_ofLocalizationMaximal`

English:
theorem isReduced_ofLocalizationMaximal
  statement: OfLocalizationMaximal fun R _ => IsReduced R
  proof: by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero

中文:
定理 isReduced_ofLocalizationMaximal
  结论: OfLocalizationMaximal fun R _ => IsReduced R
  证明: by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, algebraMap, eq_zero, eq_zero_of_localization, hx.map, introv, specialize
-/
theorem isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R _ => IsReduced R := by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero
