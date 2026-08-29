/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Conjugating by the square root of a positive element in a C⋆-algebra

This file defines `conjSqrt c a` as `sqrt c * a * sqrt c`, and develops API for this operation.

## Main declarations

* `conjSqrt c`: the map `fun a => sqrt c * a * sqrt c`, bundled as a continuous linear map,
-/

namespace CFC

open Ring

public section ConjSqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra Real A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [NonnegSpectrumClass Real A] [SeparatelyContinuousMul A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`. -/
@[expose]
/--
Definition of `conjSqrt` / `conjSqrt` 的定义

English:
definition conjSqrt
  signature: (c : A)
  body: .mulLeftRight Real (sqrt c, sqrt c)

中文:
定义 conjSqrt
  签名: (c : A)
  定义体: .mulLeftRight Real (sqrt c, sqrt c)

Depends on / 依赖: mulLeftRight
-/
noncomputable def conjSqrt (c : A) : A ->L[Real] A where
  toLinearMap := .mulLeftRight Real (sqrt c, sqrt c)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toLinearMap_conjSqrt` / 引理 `toLinearMap_conjSqrt`

English:
lemma toLinearMap_conjSqrt
  given: (c : A)
  proof: rfl

中文:
引理 toLinearMap_conjSqrt
  条件: (c : A)
  证明: rfl
-/
@[simp] lemma toLinearMap_conjSqrt (c : A) :
    (conjSqrt c).toLinearMap = .mulLeftRight Real (sqrt c, sqrt c) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `conjSqrt_apply` / 引理 `conjSqrt_apply`

English:
lemma conjSqrt_apply
  given: {c a : A}
  statement: conjSqrt c a = sqrt c * a * sqrt c
  proof: rfl

中文:
引理 conjSqrt_apply
  条件: {c a : A}
  结论: conjSqrt c a = sqrt c * a * sqrt c
  证明: rfl

Depends on / 依赖: hasProjectiveDimensionLT_of_ge
-/
lemma conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `conjSqrt_of_not_nonneg` / 引理 `conjSqrt_of_not_nonneg`

English:
lemma conjSqrt_of_not_nonneg
  given: {c a : A} (hc : ¬0 <= c)
  statement: conjSqrt c a = 0
  proof: by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

中文:
引理 conjSqrt_of_not_nonneg
  条件: {c a : A} (hc : ¬0 <= c)
  结论: conjSqrt c a = 0
  证明: by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

Depends on / 依赖: conjSqrt_apply, hasProjectiveDimensionLT_of_ge, sqrt_of_not_nonneg
-/
lemma conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 <= c) : conjSqrt c a = 0 := by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `conjSqrt_monotone` / 引理 `conjSqrt_monotone`

English:
lemma conjSqrt_monotone
  given: {c : A}
  statement: Monotone (conjSqrt c)
  proof: by
  intro a b hab
  by_cases hc : 0 <= c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

中文:
引理 conjSqrt_monotone
  条件: {c : A}
  结论: 递增 (conjSqrt c)
  证明: by
  intro a b hab
  by_cases hc : 0 <= c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

Depends on / 依赖: HasProjectiveDimensionLT, IsSelfAdjoint, IsSelfAdjoint.conjugate_le_conjugate, cfc_tac, conjSqrt_of_not_nonneg, conjugate_le_conjugate
-/
lemma conjSqrt_monotone {c : A} : Monotone (conjSqrt c) := by
  intro a b hab
  by_cases hc : 0 <= c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

set_option backward.isDefEq.respectTransparency.types false in
@[gcongr]
/--
lemma `conjSqrt_le_conjSqrt` / 引理 `conjSqrt_le_conjSqrt`

English:
lemma conjSqrt_le_conjSqrt
  given: {c a b : A} (h : a <= b)
  statement: conjSqrt c a <= conjSqrt c b
  proof: conjSqrt_monotone h

中文:
引理 conjSqrt_le_conjSqrt
  条件: {c a b : A} (h : a <= b)
  结论: conjSqrt c a <= conjSqrt c b
  证明: conjSqrt_monotone h

Depends on / 依赖: HasExt, HasExt.standard, conjSqrt_monotone, e.eq_zero_of_projective, eq_zero_of_projective, hasProjectiveDimensionLT_iff, standard
-/
lemma conjSqrt_le_conjSqrt {c a b : A} (h : a <= b) : conjSqrt c a <= conjSqrt c b :=
  conjSqrt_monotone h

variable [IsSemitopologicalRing A] [T2Space A]

set_option linter.overlappingInstances false

@[grind =]
/--
lemma `isStrictlyPositive_conjSqrt_iff` / 引理 `isStrictlyPositive_conjSqrt_iff`

English:
lemma isStrictlyPositive_conjSqrt_iff
  given: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  proof: by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

中文:
引理 isStrictlyPositive_conjSqrt_iff
  条件: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  证明: by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

Depends on / 依赖: IsSelfAdjoint, IsStrictlyPositive, cfc_tac, conjSqrt, conjSqrt_apply
-/
lemma isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    IsStrictlyPositive (conjSqrt c a) ↔ IsStrictlyPositive a := by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

set_option backward.isDefEq.respectTransparency.types false in
@[grind _=_]
/--
lemma `ringInverse_conjSqrt` / 引理 `ringInverse_conjSqrt`

English:
lemma ringInverse_conjSqrt
  given: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  proof: by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply, IsUnit.mul_left_iff]
    simp [inverse_non_unit a ha, inverse_non_unit _ this]

中文:
引理 ringInverse_conjSqrt
  条件: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  证明: by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply, IsUnit.mul_left_iff]
    simp [inverse_non_unit a ha, inverse_non_unit _ this]

Depends on / 依赖: IsUnit, IsUnit.mul_left_iff, cfc_tac, conjSqrt, conjSqrt_apply, inverse_non_unit, mul_left_iff
-/
lemma ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    (conjSqrt c a)⁻¹ʳ = conjSqrt c⁻¹ʳ a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply, IsUnit.mul_left_iff]
    simp [inverse_non_unit a ha, inverse_non_unit _ this]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/--
lemma `conjSqrt_ringInverse_conjSqrt` / 引理 `conjSqrt_ringInverse_conjSqrt`

English:
lemma conjSqrt_ringInverse_conjSqrt
  given: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  proof: by
  grind [IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ (sqrt c) 1, Ring.inverse_mul_cancel,
         conjSqrt_apply] =>
    have : sqrt c⁻¹ʳ * sqrt c = 1
    have : Commute (sqrt c) (sqrt c⁻¹ʳ)
    finish

中文:
引理 conjSqrt_ringInverse_conjSqrt
  条件: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  证明: by
  grind [IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ (sqrt c) 1, Ring.inverse_mul_cancel,
         conjSqrt_apply] =>
    have : sqrt c⁻¹ʳ * sqrt c = 1
    have : Commute (sqrt c) (sqrt c⁻¹ʳ)
    finish

Depends on / 依赖: Commute, IsSelfAdjoint, IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint, Ring.inverse_mul_cancel, cfc_tac, commute_of_mul_eq_isSelfAdjoint, conjSqrt, conjSqrt_apply, finish, inverse_mul_cancel
-/
lemma conjSqrt_ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ (conjSqrt c a) = a := by
  grind [IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ (sqrt c) 1, Ring.inverse_mul_cancel,
         conjSqrt_apply] =>
    have : sqrt c⁻¹ʳ * sqrt c = 1
    have : Commute (sqrt c) (sqrt c⁻¹ʳ)
    finish

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/--
lemma `conjSqrt_conjSqrt_ringInverse` / 引理 `conjSqrt_conjSqrt_ringInverse`

English:
lemma conjSqrt_conjSqrt_ringInverse
  given: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  proof: by
  grind [conjSqrt_ringInverse_conjSqrt _ _ hc.ringInverse]

中文:
引理 conjSqrt_conjSqrt_ringInverse
  条件: (c a : A) (hc : IsStrictlyPositive c := by cfc_tac)
  证明: by
  grind [conjSqrt_ringInverse_conjSqrt _ _ hc.ringInverse]

Depends on / 依赖: HasProjectiveDimensionLT, Projective, cfc_tac, conjSqrt, conjSqrt_ringInverse_conjSqrt, hc.ringInverse, ringInverse
-/
lemma conjSqrt_conjSqrt_ringInverse (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c (conjSqrt c⁻¹ʳ a) = a := by
  grind [conjSqrt_ringInverse_conjSqrt _ _ hc.ringInverse]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/--
lemma `conjSqrt_one` / 引理 `conjSqrt_one`

English:
lemma conjSqrt_one
  given: (c : A) (hc : 0 <= c := by cfc_tac)
  statement: conjSqrt c 1 = c
  proof: by
  rw [conjSqrt_apply]; rw [mul_one]; rw [sqrt_mul_sqrt_self _]

中文:
引理 conjSqrt_one
  条件: (c : A) (hc : 0 <= c := by cfc_tac)
  结论: conjSqrt c 1 = c
  证明: by
  rw [conjSqrt_apply]; rw [mul_one]; rw [sqrt_mul_sqrt_self _]

Depends on / 依赖: cfc_tac, conjSqrt, conjSqrt_apply, mul_one, sqrt_mul_sqrt_self
-/
lemma conjSqrt_one (c : A) (hc : 0 <= c := by cfc_tac) : conjSqrt c 1 = c := by
  rw [conjSqrt_apply]; rw [mul_one]; rw [sqrt_mul_sqrt_self _]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/--
lemma `conjSqrt_ringInverse_self` / 引理 `conjSqrt_ringInverse_self`

English:
lemma conjSqrt_ringInverse_self
  given: (c : A) (hc : IsStrictlyPositive c := by cfc_tac)
  proof: by
  grind [conjSqrt_one c]

中文:
引理 conjSqrt_ringInverse_self
  条件: (c : A) (hc : IsStrictlyPositive c := by cfc_tac)
  证明: by
  grind [conjSqrt_one c]

Depends on / 依赖: cfc_tac, conjSqrt, conjSqrt_one
-/
lemma conjSqrt_ringInverse_self (c : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ c = 1 := by
  grind [conjSqrt_one c]

end ConjSqrt

end CFC
