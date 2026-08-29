/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Facts about `CFC.posPart` and `CFC.negPart` involving norms

This file collects various facts about the positive and negative parts of elements of a
C⋆-algebra that involve the norm.

## Main results

* `CFC.norm_eq_max_norm_posPart_negPart`: states that `‖a‖ = max ‖a⁺‖ ‖a⁻‖`
* `CFC.norm_posPart_le` and `CFC.norm_negPart_le`: state that `‖a⁺‖ ≤ ‖a‖` and `‖a⁻‖ ≤ ‖a‖`
  respectively.
-/

public section

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace Real A] [SMulCommClass Real A A]
  [IsScalarTower Real A A] [StarRing A]
  [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]

@[simp]
/--
lemma `CStarAlgebra.norm_posPart_le` / 引理 `CStarAlgebra.norm_posPart_le`

English:
lemma CStarAlgebra.norm_posPart_le
  given: (a : A)
  statement: ‖a⁺‖ <= ‖a‖
  proof: by
  by_cases ha : IsSelfAdjoint a
  case neg => simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx => ?_
  obtain (h | h) := le_or_gt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousF

中文:
引理 CStarAlgebra.norm_posPart_le
  条件: (a : A)
  结论: ‖a⁺‖ <= ‖a‖
  证明: by
  by_cases ha : IsSelfAdjoint a
  case neg => simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx => ?_
  obtain (h | h) := le_or_gt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousF

Depends on / 依赖: CFC.posPart_def, IsSelfAdjoint, NonUnitalIsometricContinuousFunctionalCalculus, NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le, h.le, le_or_gt, max_eq_left, max_eq_right, norm_quasispectrum_le, posPart_def
-/
lemma CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺‖ <= ‖a‖ := by
  by_cases ha : IsSelfAdjoint a
  case neg => simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx => ?_
  obtain (h | h) := le_or_gt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hx ha

@[simp]
/--
lemma `CStarAlgebra.norm_negPart_le` / 引理 `CStarAlgebra.norm_negPart_le`

English:
lemma CStarAlgebra.norm_negPart_le
  given: (a : A)
  statement: ‖a⁻‖ <= ‖a‖
  proof: by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

中文:
引理 CStarAlgebra.norm_negPart_le
  条件: (a : A)
  结论: ‖a⁻‖ <= ‖a‖
  证明: by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

Depends on / 依赖: CFC.negPart_neg, negPart_neg, norm_posPart_le
-/
lemma CStarAlgebra.norm_negPart_le (a : A) : ‖a⁻‖ <= ‖a‖ := by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

open CStarAlgebra in
/--
lemma `IsSelfAdjoint.norm_eq_max_norm_posPart_negPart` / 引理 `IsSelfAdjoint.norm_eq_max_norm_posPart_negPart`

English:
lemma IsSelfAdjoint.norm_eq_max_norm_posPart_negPart
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
refine le_antisymm ?_ max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' Real a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
refine le_of_eq_of_le ?_ norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx

中文:
引理 IsSelfAdjoint.norm_eq_max_norm_posPart_negPart
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
refine le_antisymm ?_ max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' Real a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
refine le_of_eq_of_le ?_ norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx

Depends on / 依赖: cfc_tac, conv_lhs, le_antisymm, le_max_of_le_left, le_max_of_le_right, le_of_eq_of_le, le_total, max_le, negPart_eq_neg, negPart_eq_neg.mpr, norm_neg, norm_negPart_le, norm_posPart_le, posPart_eq_self, posPart_eq_self.mpr
-/
lemma IsSelfAdjoint.norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ := by
refine le_antisymm ?_ max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' Real a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
refine le_of_eq_of_le ?_ norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx']
  · apply le_max_of_le_right
refine le_of_eq_of_le ?_ norm_apply_le_norm_cfcₙ _ a hx
    rw [negPart_eq_neg.mpr hx']; rw [norm_neg]
