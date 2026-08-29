/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# The Krull dimension of a field

This file proves that the Krull dimension of a field is zero.
-/

public section

open Order

@[simp]
/--
theorem `ringKrullDim_eq_zero_of_field` / 定理 `ringKrullDim_eq_zero_of_field`

English:
theorem ringKrullDim_eq_zero_of_field
  given: (F : Type*) [Field F]
  statement: ringKrullDim F = 0
  proof: krullDim_eq_zero_of_unique

中文:
定理 ringKrullDim_eq_zero_of_field
  条件: (F : 类型) [Field F]
  结论: ringKrullDim F = 0
  证明: krullDim_eq_zero_of_unique

Depends on / 依赖: krullDim_eq_zero_of_unique
-/
theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique

/--
theorem `ringKrullDim_eq_zero_of_isField` / 定理 `ringKrullDim_eq_zero_of_isField`

English:
theorem ringKrullDim_eq_zero_of_isField
  given: {F : Type*} [CommRing F] (hF : IsField F)
  proof: @krullDim_eq_zero_of_unique _ _ @PrimeSpectrum.instUnique _ hF.toField

中文:
定理 ringKrullDim_eq_zero_of_isField
  条件: {F : 类型} [CommRing F] (hF : IsField F)
  证明: @krullDim_eq_zero_of_unique _ _ @PrimeSpectrum.instUnique _ hF.toField

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.instUnique, hF.toField, instUnique, krullDim_eq_zero_of_unique, toField
-/
theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
    ringKrullDim F = 0 :=
@krullDim_eq_zero_of_unique _ _ @PrimeSpectrum.instUnique _ hF.toField
