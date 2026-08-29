/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Lebesgue Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about Lebesgue integration.
-/

public section

assert_not_exists NormedSpace

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

section MeasurableInv

variable [InvolutiveInv G] [MeasurableInv G]

/-- The Lebesgue integral of a function with respect to an inverse invariant measure is
invariant under the change of variables x ↦ x⁻¹. -/
@[to_additive
      /-- The Lebesgue integral of a function with respect to an inverse invariant measure is
invariant under the change of variables x ↦ -x. -/]
/--
theorem `lintegral_inv_eq_self` / 定理 `lintegral_inv_eq_self`

English:
theorem lintegral_inv_eq_self
  given: [IsInvInvariant μ] (f : G -> Real>=0∞)
  proof: by
  simpa using (lintegral_map_equiv f (μ := μ) <| MeasurableEquiv.inv G).symm

中文:
定理 lintegral_inv_eq_self
  条件: [是InvInvariant μ] (f : G -> 实数>=0∞)
  证明: by
  simpa using (lintegral_map_equiv f (μ := μ) <| MeasurableEquiv.inv G).symm

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.inv, lintegral_map_equiv
-/
theorem lintegral_inv_eq_self [IsInvInvariant μ] (f : G -> Real>=0∞) :
    ∫⁻ x, f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by
  simpa using (lintegral_map_equiv f (μ := μ) <| MeasurableEquiv.inv G).symm

end MeasurableInv

section MeasurableMul

variable [Group G] [MeasurableMul G]

/-- Translating a function by left-multiplication does not change its Lebesgue integral
with respect to a left-invariant measure. -/
@[to_additive
      /-- Translating a function by left-addition does not change its Lebesgue integral with
      respect to a left-invariant measure. -/]
/--
theorem `lintegral_mul_left_eq_self` / 定理 `lintegral_mul_left_eq_self`

English:
theorem lintegral_mul_left_eq_self
  given: [IsMulLeftInvariant μ] (f : G -> Real>=0∞) (g : G)
  proof: by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

中文:
定理 lintegral_mul_left_eq_self
  条件: [是MulLeftInvariant μ] (f : G -> 实数>=0∞) (g : G)
  证明: by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.mulLeft, convert, lintegral_map_equiv, map_mul_left_eq_self, mulLeft
-/
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G -> Real>=0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

/-- Translating a function by right-multiplication does not change its Lebesgue integral
with respect to a right-invariant measure. -/
@[to_additive
      /-- Translating a function by right-addition does not change its Lebesgue integral with
      respect to a right-invariant measure. -/]
/--
theorem `lintegral_mul_right_eq_self` / 定理 `lintegral_mul_right_eq_self`

English:
theorem lintegral_mul_right_eq_self
  given: [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g : G)
  proof: by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]

@[to_additive]

中文:
定理 lintegral_mul_right_eq_self
  条件: [是MulRightInvariant μ] (f : G -> 实数>=0∞) (g : G)
  证明: by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]

@[to_additive]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.mulRight, convert, lintegral_map_equiv, map_mul_right_eq_self, mulRight
-/
theorem lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g : G) :
    (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert! (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]

@[to_additive]
/--
theorem `lintegral_div_right_eq_self` / 定理 `lintegral_div_right_eq_self`

English:
theorem lintegral_div_right_eq_self
  given: [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g : G)
  proof: by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

@[to_additive]

中文:
定理 lintegral_div_right_eq_self
  条件: [是MulRightInvariant μ] (f : G -> 实数>=0∞) (g : G)
  证明: by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, lintegral_mul_right_eq_self, simp_rw
-/
theorem lintegral_div_right_eq_self [IsMulRightInvariant μ] (f : G -> Real>=0∞) (g : G) :
    (∫⁻ x, f (x / g) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

@[to_additive]
/--
theorem `lintegral_div_left_eq_self` / 定理 `lintegral_div_left_eq_self`

English:
theorem lintegral_div_left_eq_self
  statement: [IsMulLeftInvariant μ] [MeasurableInv G] [IsInvInvariant μ]
  proof: by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

中文:
定理 lintegral_div_left_eq_self
  结论: [是MulLeftInvariant μ] [MeasurableInv G] [是InvInvariant μ]
  证明: by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

Depends on / 依赖: div_eq_mul_inv, lintegral_inv_eq_self, lintegral_mul_left_eq_self, simp_rw
-/
theorem lintegral_div_left_eq_self [IsMulLeftInvariant μ] [MeasurableInv G] [IsInvInvariant μ]
    (f : G -> Real>=0∞) (g : G) : (∫⁻ x, f (g / x) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

end MeasurableMul


section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive
      /-- For nonzero regular left invariant measures, the integral of a continuous nonnegative
      function `f` is 0 iff `f` is 0. -/]
/--
theorem `lintegral_eq_zero_of_isMulLeftInvariant` / 定理 `lintegral_eq_zero_of_isMulLeftInvariant`

English:
theorem lintegral_eq_zero_of_isMulLeftInvariant
  statement: [Regular μ] [NeZero μ] {f : G -> Real>=0∞}
  proof: by
  rw [lintegral_eq_zero_iff hf.measurable]; rw [hf.ae_eq_iff_eq μ continuous_zero]

中文:
定理 lintegral_eq_zero_of_isMulLeftInvariant
  结论: [正则 μ] [NeZero μ] {f : G -> 实数>=0∞}
  证明: by
  rw [lintegral_eq_zero_iff hf.measurable]; rw [hf.ae_eq_iff_eq μ continuous_zero]

Depends on / 依赖: ae_eq_iff_eq, continuous_zero, hf.ae_eq_iff_eq, hf.measurable, lintegral_eq_zero_iff, measurable
-/
theorem lintegral_eq_zero_of_isMulLeftInvariant [Regular μ] [NeZero μ] {f : G -> Real>=0∞}
    (hf : Continuous f) : ∫⁻ x, f x ∂μ = 0 ↔ f = 0 := by
  rw [lintegral_eq_zero_iff hf.measurable]; rw [hf.ae_eq_iff_eq μ continuous_zero]

end IsTopologicalGroup

end MeasureTheory
