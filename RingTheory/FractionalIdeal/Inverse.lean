/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Inverse operator for fractional ideals

This file defines the notation `I⁻¹` where `I` is a not necessarily invertible fractional ideal.
Note that this is somewhat misleading notation in case `I` is not invertible.
The theorem that all nonzero fractional ideals are invertible in a Dedekind domain can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `FractionalIdeal.instInv` defines `I⁻¹ := 1 / I`.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

fractional ideal, invertible ideal
-/

public section

assert_not_exists IsDedekindDomain

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]
variable {I J : FractionalIdeal R₁⁰ K}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (FractionalIdeal R₁⁰ K)
  body: ⟨fun I => 1 / I⟩

中文:
实例 :
  签名: Inv (FractionalIdeal R₁⁰ K)
  定义体: ⟨fun I => 1 / I⟩
-/
noncomputable instance : Inv (FractionalIdeal R₁⁰ K) := ⟨fun I => 1 / I⟩

/--
theorem `inv_eq` / 定理 `inv_eq`

English:
theorem inv_eq
  statement: I⁻¹ = 1 / I
  proof: rfl

中文:
定理 inv_eq
  结论: I⁻¹ = 1 / I
  证明: rfl
-/
theorem inv_eq : I⁻¹ = 1 / I := rfl

/--
theorem `inv_zero'` / 定理 `inv_zero'`

English:
theorem inv_zero'
  statement: (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0
  proof: div_zero

中文:
定理 inv_zero'
  结论: (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0
  证明: div_zero

Depends on / 依赖: div_zero
-/
theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 := div_zero

/--
theorem `inv_of_ne_zero` / 定理 `inv_of_ne_zero`

English:
theorem inv_of_ne_zero
  given: {J : FractionalIdeal R₁⁰ K} (h : J != 0)
  proof: div_of_ne_zero h

中文:
定理 inv_of_ne_zero
  条件: {J : FractionalIdeal R₁⁰ K} (h : J != 0)
  证明: div_of_ne_zero h

Depends on / 依赖: div_of_ne_zero
-/
theorem inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J != 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, isFractional_div_of_ne_zero h⟩ := div_of_ne_zero h

/--
theorem `coe_inv_of_ne_zero` / 定理 `coe_inv_of_ne_zero`

English:
theorem coe_inv_of_ne_zero
  given: {J : FractionalIdeal R₁⁰ K} (h : J != 0)
  proof: by
  simp_rw [inv_of_ne_zero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]

中文:
定理 coe_inv_of_ne_zero
  条件: {J : FractionalIdeal R₁⁰ K} (h : J != 0)
  证明: by
  simp_rw [inv_of_ne_zero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]

Depends on / 依赖: IsLocalization, IsLocalization.coeSubmodule_top, coeSubmodule_top, coe_mk, coe_one, inv_of_ne_zero, simp_rw
-/
theorem coe_inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J != 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K) := by
  simp_rw [inv_of_ne_zero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]

variable {K}

/--
theorem `mem_inv_iff` / 定理 `mem_inv_iff`

English:
theorem mem_inv_iff
  given: (hI : I != 0) {x : K}
  statement: x in I⁻¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
  proof: mem_div_iff_of_ne_zero hI

中文:
定理 mem_inv_iff
  条件: (hI : I != 0) {x : K}
  结论: x in I⁻¹ ↔ 对任意 y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
  证明: mem_div_iff_of_ne_zero hI

Depends on / 依赖: mem_div_iff_of_ne_zero
-/
theorem mem_inv_iff (hI : I != 0) {x : K} : x in I⁻¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K) :=
  mem_div_iff_of_ne_zero hI

/--
theorem `inv_anti_mono` / 定理 `inv_anti_mono`

English:
theorem inv_anti_mono
  given: (hI : I != 0) (hJ : J != 0) (hIJ : I <= J)
  statement: J⁻¹ <= I⁻¹
  proof: by
  intro x
  simp only [mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)

中文:
定理 inv_anti_mono
  条件: (hI : I != 0) (hJ : J != 0) (hIJ : I <= J)
  结论: J⁻¹ <= I⁻¹
  证明: by
  intro x
  simp only [mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)

Depends on / 依赖: mem_inv_iff
-/
theorem inv_anti_mono (hI : I != 0) (hJ : J != 0) (hIJ : I <= J) : J⁻¹ <= I⁻¹ := by
  intro x
  simp only [mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)

/--
theorem `le_self_mul_inv` / 定理 `le_self_mul_inv`

English:
theorem le_self_mul_inv
  given: {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K))
  proof: le_self_mul_one_div hI

中文:
定理 le_self_mul_inv
  条件: {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K))
  证明: le_self_mul_one_div hI

Depends on / 依赖: le_self_mul_one_div
-/
theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K)) :
    I <= I * I⁻¹ :=
  le_self_mul_one_div hI

variable (K)

/--
theorem `coe_ideal_le_self_mul_inv` / 定理 `coe_ideal_le_self_mul_inv`

English:
theorem coe_ideal_le_self_mul_inv
  given: (I : Ideal R₁)
  proof: le_self_mul_inv coeIdeal_le_one

中文:
定理 coe_ideal_le_self_mul_inv
  条件: (I : Ideal R₁)
  证明: le_self_mul_inv coeIdeal_le_one

Depends on / 依赖: coeIdeal_le_one, le_self_mul_inv
-/
theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) :
    (I : FractionalIdeal R₁⁰ K) <= I * (I : FractionalIdeal R₁⁰ K)⁻¹ :=
  le_self_mul_inv coeIdeal_le_one

/--
theorem `right_inverse_eq` / 定理 `right_inverse_eq`

English:
theorem right_inverse_eq
  given: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  statement: J = I⁻¹
  proof: eq_one_div_of_mul_eq_one_right _ _ h

中文:
定理 right_inverse_eq
  条件: (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1)
  结论: J = I⁻¹
  证明: eq_one_div_of_mul_eq_one_right _ _ h

Depends on / 依赖: eq_one_div_of_mul_eq_one_right
-/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ :=
  eq_one_div_of_mul_eq_one_right _ _ h

/--
theorem `mul_inv_cancel_iff` / 定理 `mul_inv_cancel_iff`

English:
theorem mul_inv_cancel_iff
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I * I⁻¹ = 1 ↔ exists J, I * J = 1
  proof: ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩

中文:
定理 mul_inv_cancel_iff
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I * I⁻¹ = 1 ↔ 存在 J, I * J = 1
  证明: ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩

Depends on / 依赖: right_inverse_eq
-/
theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ exists J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩

/--
theorem `mul_inv_cancel_iff_isUnit` / 定理 `mul_inv_cancel_iff_isUnit`

English:
theorem mul_inv_cancel_iff_isUnit
  given: {I : FractionalIdeal R₁⁰ K}
  statement: I * I⁻¹ = 1 ↔ IsUnit I
  proof: (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

中文:
定理 mul_inv_cancel_iff_isUnit
  条件: {I : FractionalIdeal R₁⁰ K}
  结论: I * I⁻¹ = 1 ↔ IsUnit I
  证明: (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

Depends on / 依赖: isUnit_iff_exists_inv, isUnit_iff_exists_inv.symm, mul_inv_cancel_iff
-/
theorem mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  proof: by
  rw [inv_eq]; rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]; rw [inv_eq]

中文:
定理 map_inv
  条件: (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K')
  证明: by
  rw [inv_eq]; rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]; rw [inv_eq]
-/
protected theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K ->ₐ[R₁] K') = (I.map h)⁻¹ := by
  rw [inv_eq]; rw [FractionalIdeal.map_div]; rw [FractionalIdeal.map_one]; rw [inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
/--
theorem `spanSingleton_inv` / 定理 `spanSingleton_inv`

English:
theorem spanSingleton_inv
  given: (x : K)
  statement: (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹
  proof: one_div_spanSingleton x

中文:
定理 spanSingleton_inv
  条件: (x : K)
  结论: (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹
  证明: one_div_spanSingleton x

Depends on / 依赖: one_div_spanSingleton
-/
theorem spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹ :=
  one_div_spanSingleton x

/--
theorem `spanSingleton_div_spanSingleton` / 定理 `spanSingleton_div_spanSingleton`

English:
theorem spanSingleton_div_spanSingleton
  given: (x y : K)
  proof: by
  rw [div_spanSingleton]; rw [mul_comm]; rw [spanSingleton_mul_spanSingleton]; rw [div_eq_mul_inv]

中文:
定理 spanSingleton_div_spanSingleton
  条件: (x y : K)
  证明: by
  rw [div_spanSingleton]; rw [mul_comm]; rw [spanSingleton_mul_spanSingleton]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, div_spanSingleton, mul_comm, spanSingleton_mul_spanSingleton
-/
theorem spanSingleton_div_spanSingleton (x y : K) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_spanSingleton]; rw [mul_comm]; rw [spanSingleton_mul_spanSingleton]; rw [div_eq_mul_inv]

/--
theorem `spanSingleton_div_self` / 定理 `spanSingleton_div_self`

English:
theorem spanSingleton_div_self
  given: {x : K} (hx : x != 0)
  proof: by
  rw [spanSingleton_div_spanSingleton]; rw [div_self hx]; rw [spanSingleton_one]

中文:
定理 spanSingleton_div_self
  条件: {x : K} (hx : x != 0)
  证明: by
  rw [spanSingleton_div_spanSingleton]; rw [div_self hx]; rw [spanSingleton_one]

Depends on / 依赖: div_self, spanSingleton_div_spanSingleton, spanSingleton_one
-/
theorem spanSingleton_div_self {x : K} (hx : x != 0) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1 := by
  rw [spanSingleton_div_spanSingleton]; rw [div_self hx]; rw [spanSingleton_one]

/--
theorem `coe_ideal_span_singleton_div_self` / 定理 `coe_ideal_span_singleton_div_self`

English:
theorem coe_ideal_span_singleton_div_self
  given: {x : R₁} (hx : x != 0)
  proof: by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_div_self K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

中文:
定理 coe_ideal_span_singleton_div_self
  条件: {x : R₁} (hx : x != 0)
  证明: by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_div_self K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, coeIdeal_span_singleton, map_ne_zero_iff, spanSingleton_div_self
-/
theorem coe_ideal_span_singleton_div_self {x : R₁} (hx : x != 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1 := by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_div_self K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

/--
theorem `spanSingleton_mul_inv` / 定理 `spanSingleton_mul_inv`

English:
theorem spanSingleton_mul_inv
  given: {x : K} (hx : x != 0)
  proof: by
  rw [spanSingleton_inv]; rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀ hx]; rw [spanSingleton_one]

中文:
定理 spanSingleton_mul_inv
  条件: {x : K} (hx : x != 0)
  证明: by
  rw [spanSingleton_inv]; rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀ hx]; rw [spanSingleton_one]

Depends on / 依赖: spanSingleton_inv, spanSingleton_mul_spanSingleton, spanSingleton_one
-/
theorem spanSingleton_mul_inv {x : K} (hx : x != 0) :
    spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1 := by
  rw [spanSingleton_inv]; rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀ hx]; rw [spanSingleton_one]

/--
theorem `coe_ideal_span_singleton_mul_inv` / 定理 `coe_ideal_span_singleton_mul_inv`

English:
theorem coe_ideal_span_singleton_mul_inv
  given: {x : R₁} (hx : x != 0)
  proof: by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_mul_inv K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

中文:
定理 coe_ideal_span_singleton_mul_inv
  条件: {x : R₁} (hx : x != 0)
  证明: by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_mul_inv K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, coeIdeal_span_singleton, map_ne_zero_iff, spanSingleton_mul_inv
-/
theorem coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x != 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) *
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ = 1 := by
  rw [coeIdeal_span_singleton]; rw [spanSingleton_mul_inv K
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]

/--
theorem `spanSingleton_inv_mul` / 定理 `spanSingleton_inv_mul`

English:
theorem spanSingleton_inv_mul
  given: {x : K} (hx : x != 0)
  proof: by
  rw [mul_comm]; rw [spanSingleton_mul_inv K hx]

中文:
定理 spanSingleton_inv_mul
  条件: {x : K} (hx : x != 0)
  证明: by
  rw [mul_comm]; rw [spanSingleton_mul_inv K hx]

Depends on / 依赖: mul_comm, spanSingleton_mul_inv
-/
theorem spanSingleton_inv_mul {x : K} (hx : x != 0) :
    (spanSingleton R₁⁰ x)⁻¹ * spanSingleton R₁⁰ x = 1 := by
  rw [mul_comm]; rw [spanSingleton_mul_inv K hx]

/--
theorem `coe_ideal_span_singleton_inv_mul` / 定理 `coe_ideal_span_singleton_inv_mul`

English:
theorem coe_ideal_span_singleton_inv_mul
  given: {x : R₁} (hx : x != 0)
  proof: by
  rw [mul_comm]; rw [coe_ideal_span_singleton_mul_inv K hx]

中文:
定理 coe_ideal_span_singleton_inv_mul
  条件: {x : R₁} (hx : x != 0)
  证明: by
  rw [mul_comm]; rw [coe_ideal_span_singleton_mul_inv K hx]

Depends on / 依赖: coe_ideal_span_singleton_mul_inv, mul_comm
-/
theorem coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x != 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1 := by
  rw [mul_comm]; rw [coe_ideal_span_singleton_mul_inv K hx]

/--
theorem `mul_generator_self_inv` / 定理 `mul_generator_self_inv`

English:
theorem mul_generator_self_inv
  statement: {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
  proof: by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀]; rw [spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I]; rw [generator_I_eq_zero]; rw [

中文:
定理 mul_generator_self_inv
  结论: {R₁ : 类型} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
  证明: by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀]; rw [spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I]; rw [generator_I_eq_zero]; rw [
-/
theorem mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I != 0) :
    I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton]; rw [mul_inv_cancel₀]; rw [spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I]; rw [generator_I_eq_zero]; rw [spanSingleton_zero]

/--
theorem `invertible_of_principal` / 定理 `invertible_of_principal`

English:
theorem invertible_of_principal
  statement: (I : FractionalIdeal R₁⁰ K)
  proof: mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

中文:
定理 invertible_of_principal
  结论: (I : FractionalIdeal R₁⁰ K)
  证明: mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

Depends on / 依赖: Submodule, generator, mul_div_self_cancel_iff, mul_div_self_cancel_iff.mpr, mul_generator_self_inv, spanSingleton
-/
theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I != 0) : I * I⁻¹ = 1 :=
  mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩

/--
theorem `invertible_iff_generator_nonzero` / 定理 `invertible_iff_generator_nonzero`

English:
theorem invertible_iff_generator_nonzero
  statement: (I : FractionalIdeal R₁⁰ K)
  proof: by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I]; rw [hg]; rw [spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I

中文:
定理 invertible_iff_generator_nonzero
  结论: (I : FractionalIdeal R₁⁰ K)
  证明: by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I]; rw [hg]; rw [spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I

Depends on / 依赖: Submodule, eq_spanSingleton_of_principal, generator, invertible_of_principal, mem_spanSingleton_self, mem_zero_iff, ne_zero_of_mul_eq_one, spanSingleton_zero
-/
theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) != 0 := by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I]; rw [hg]; rw [spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I : Submodule R₁ K))
    rw [hI]; rw [mem_zero_iff] at this
    contradiction

/--
theorem `isPrincipal_inv` / 定理 `isPrincipal_inv`

English:
theorem isPrincipal_inv
  statement: (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
  proof: by
  rw [val_eq_coe]; rw [isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

中文:
定理 isPrincipal_inv
  结论: (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
  证明: by
  rw [val_eq_coe]; rw [isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

Depends on / 依赖: Submodule, generator, isPrincipal_iff, mul_generator_self_inv, right_inverse_eq, spanSingleton, val_eq_coe
-/
theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    (h : I != 0) : Submodule.IsPrincipal I⁻¹.1 := by
  rw [val_eq_coe]; rw [isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

variable {K}

/--
lemma `den_mem_inv` / 引理 `den_mem_inv`

English:
lemma den_mem_inv
  given: {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥)
  proof: by
  rw [mem_inv_iff hI]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i]; rw [← mem_coe]; rw [coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num <= 1 from
this (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
apply le_trans map_mono (show I.num <

中文:
引理 den_mem_inv
  条件: {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥)
  证明: by
  rw [mem_inv_iff hI]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i]; rw [← mem_coe]; rw [coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num <= 1 from
this (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
apply le_trans map_mono (show I.num <

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.smul_def, I.coeToSubmodule, I.den, I.num, Ideal.one_eq_top, Submodule, Submodule.map, Submodule.map_top, coeToSubmodule, coe_one, den_mul_self_eq_num, le_top, le_trans, linearMap, map_mono, map_top, mem_coe, mem_inv_iff
-/
lemma den_mem_inv {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥) :
    algebraMap R₁ K (I.den : R₁) in I⁻¹ := by
  rw [mem_inv_iff hI]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i]; rw [← mem_coe]; rw [coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num <= 1 from
this (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
apply le_trans map_mono (show I.num <= 1 by simp only [Ideal.one_eq_top, le_top])
  rw [Ideal.one_eq_top]; rw [Submodule.map_top]; rw [one_eq_range]

/--
lemma `num_le_mul_inv` / 引理 `num_le_mul_inv`

English:
lemma num_le_mul_inv
  given: (I : FractionalIdeal R₁⁰ K)
  statement: I.num <= I * I⁻¹
  proof: by
  by_cases hI : I = 0
  · rw [hI, num_zero_eq <| FaithfulSMul.algebraMap_injective R₁ K, zero_mul, zero_eq_bot,
      coeIdeal_bot]
  · rw [mul_comm, ← den_mul_self_eq_num']
    gcongr
    exact spanSingleton_le_iff_mem.2 (den_mem_inv hI)

中文:
引理 num_le_mul_inv
  条件: (I : FractionalIdeal R₁⁰ K)
  结论: I.num <= I * I⁻¹
  证明: by
  by_cases hI : I = 0
  · rw [hI, num_zero_eq <| FaithfulSMul.algebraMap_injective R₁ K, zero_mul, zero_eq_bot,
      coeIdeal_bot]
  · rw [mul_comm, ← den_mul_self_eq_num']
    gcongr
    exact spanSingleton_le_iff_mem.2 (den_mem_inv hI)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, coeIdeal_bot, den_mem_inv, den_mul_self_eq_num, mul_comm, num_zero_eq, spanSingleton_le_iff_mem, zero_eq_bot, zero_mul
-/
lemma num_le_mul_inv (I : FractionalIdeal R₁⁰ K) : I.num <= I * I⁻¹ := by
  by_cases hI : I = 0
  · rw [hI, num_zero_eq <| FaithfulSMul.algebraMap_injective R₁ K, zero_mul, zero_eq_bot,
      coeIdeal_bot]
  · rw [mul_comm, ← den_mul_self_eq_num']
    gcongr
    exact spanSingleton_le_iff_mem.2 (den_mem_inv hI)

/--
lemma `bot_lt_mul_inv` / 引理 `bot_lt_mul_inv`

English:
lemma bot_lt_mul_inv
  given: {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥)
  statement: ⊥ < I * I⁻¹
  proof: lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_inv

中文:
引理 bot_lt_mul_inv
  条件: {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥)
  结论: ⊥ < I * I⁻¹
  证明: lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_inv

Depends on / 依赖: I.num_le_mul_inv, bot_lt, coeIdeal_ne_zero, lt_of_lt_of_le, num_eq_zero_iff, num_le_mul_inv
-/
lemma bot_lt_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥) : ⊥ < I * I⁻¹ :=
  lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvOneClass (FractionalIdeal R₁⁰ K)
  body: { inv_one := div_one }

中文:
实例 :
  签名: InvOneClass (FractionalIdeal R₁⁰ K)
  定义体: { inv_one := div_one }

Depends on / 依赖: div_one, inv_one
-/
noncomputable instance : InvOneClass (FractionalIdeal R₁⁰ K) := { inv_one := div_one }

end FractionalIdeal
