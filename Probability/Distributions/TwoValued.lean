/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.CondVar

import Mathlib.Probability.Notation

/-!
# Distributions on two values

This file proves a few lemmas about random variables that take at most two values.
-/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω -> Real} {μ : Measure Ω}

/--
lemma `integral_of_ae_eq_zero_or_one` / 引理 `integral_of_ae_eq_zero_or_one`

English:
lemma integral_of_ae_eq_zero_or_one
  given: (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
  proof: by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop]; rw [by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

中文:
引理 integral_of_ae_eq_zero_or_one
  条件: (hXmeas : 几乎处处可测 X μ) (hX : 对任意ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
  证明: by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop]; rw [by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

Depends on / 依赖: HasFiniteIntegral, Integrable, Measure, Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac, Measure.real, Set.preimage, ae_eq_or_eq_iff_map_eq_dirac_add_dirac, fun_prop, hXmeas, integrable_dirac, integral_add_measure, integral_map, integral_undef, preimage, smul_measure, symm.trans, zero_ne_one
-/
lemma integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    μ[X] = μ.real {ω | X ω = 1} := by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop]; rw [by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

/--
lemma `integral_one_sub_of_ae_eq_zero_or_one` / 引理 `integral_one_sub_of_ae_eq_zero_or_one`

English:
lemma integral_one_sub_of_ae_eq_zero_or_one
  statement: (hXmeas : AEMeasurable X μ)
  proof: by
  calc
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : Real))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

中文:
引理 integral_one_sub_of_ae_eq_zero_or_one
  结论: (hXmeas : 几乎处处可测 X μ)
  证明: by
  calc
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : Real))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

Depends on / 依赖: aemeasurable_const, eq_comm, hXmeas, integral_of_ae_eq_zero_or_one, or_comm, sub_eq_zero
-/
lemma integral_one_sub_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ)
    (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : ∫ ω, 1 - X ω ∂μ = μ.real {ω | X ω = 0} := by
  calc
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : Real))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

end MeasureTheory


namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω -> Real} {μ : Measure Real} {P : Measure Ω}

/--
lemma `condVar_of_ae_eq_zero_or_one` / 引理 `condVar_of_ae_eq_zero_or_one`

English:
lemma condVar_of_ae_eq_zero_or_one
  statement: {m₀ : MeasurableSpace Ω} (hm : m <= m₀) {μ : Measure[m₀] Ω}
  proof: by
  wlog hXmeas : Measurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
exact condExp_congr_ae by filter_upwards [hXY] with ω hω; simp [hω]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
condVar_ae_eq_condExp_sq_sub_sq_condExp hm .of_bound hXmeas.aestronglyMeasurable 1 by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
exact condExp_congr_ae by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq]; rw [← one_sub_mul]; rw [mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound (C := 1) hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

中文:
引理 condVar_of_ae_eq_zero_or_one
  结论: {m₀ : 可测空间 Ω} (hm : m <= m₀) {μ : 测度[m₀] Ω}
  证明: by
  wlog hXmeas : Measurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
exact condExp_congr_ae by filter_upwards [hXY] with ω hω; simp [hω]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
condVar_ae_eq_condExp_sq_sub_sq_condExp hm .of_bound hXmeas.aestronglyMeasurable 1 by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
exact condExp_congr_ae by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq]; rw [← one_sub_mul]; rw [mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound (C := 1) hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

Depends on / 依赖: AEMeasurable, Measurable, aemeasurable, condExp_congr_ae, condVar_ae_eq_condExp_sq_sub_sq_co, condVar_congr_ae, filter_upwards, hXmeas, hYmeas, hYmeas.aemeasurable
-/
lemma condVar_of_ae_eq_zero_or_one {m₀ : MeasurableSpace Ω} (hm : m <= m₀) {μ : Measure[m₀] Ω}
    [IsFiniteMeasure μ] (hXmeas : AEMeasurable[m₀] X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
  wlog hXmeas : Measurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
exact condExp_congr_ae by filter_upwards [hXY] with ω hω; simp [hω]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
condVar_ae_eq_condExp_sq_sub_sq_condExp hm .of_bound hXmeas.aestronglyMeasurable 1 by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
exact condExp_congr_ae by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq]; rw [← one_sub_mul]; rw [mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound (C := 1) hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

/--
lemma `variance_of_ae_eq_zero_or_one` / 引理 `variance_of_ae_eq_zero_or_one`

English:
lemma variance_of_ae_eq_zero_or_one
  statement: {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
  proof: by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  simpa [Pi.mul_def, integral_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one, mul_comm,
    *] using condVar_of_ae_eq_zero_or_one bot_le hXmeas hX

中文:
引理 variance_of_ae_eq_zero_or_one
  结论: {μ : 测度 Ω} [是ZeroOrProbabilityMeasure μ]
  证明: by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  simpa [Pi.mul_def, integral_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one, mul_comm,
    *] using condVar_of_ae_eq_zero_or_one bot_le hXmeas hX

Depends on / 依赖: Pi.mul_def, bot_le, condVar_of_ae_eq_zero_or_one, eq_zero_or_isProbabilityMeasure, hXmeas, integral_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one, mul_comm, mul_def
-/
lemma variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  simpa [Pi.mul_def, integral_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one, mul_comm,
    *] using condVar_of_ae_eq_zero_or_one bot_le hXmeas hX

end ProbabilityTheory
