/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Riesz–Markov–Kakutani representation theorem for `ℝ≥0`

This file proves the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `ℝ≥0`-linear functionals `Λ`.

## Implementation notes

The proof depends on the version of the theorem for `ℝ`-linear functional `Λ` because in a standard
proof one has to prove the inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.
Here we prove the result by writing `ℝ≥0`-linear `Λ` in terms of `ℝ`-linear `toRealLinear Λ` and by
reducing the statement to the `ℝ`-version of the theorem.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0)

namespace NNRealRMK

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (Bochner) integral of `f` (as a `ℝ`-valued function) with respect to the `rieszMeasure`
associated to `Λ` is equal to `Λ f`. -/
@[simp]
/--
theorem `integral_rieszMeasure` / 定理 `integral_rieszMeasure`

English:
theorem integral_rieszMeasure
  given: (f : C_c(X, Real>=0))
  statement: ∫ (x : X), (f x : Real) ∂(rieszMeasure Λ) = Λ f
  proof: by
  rw [← eq_toRealPositiveLinear_toReal Λ f]; rw [← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
  simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

中文:
定理 integral_rieszMeasure
  条件: (f : C_c(X, 实数>=0))
  结论: ∫ (x : X), (f x : 实数) ∂(rieszMeasure Λ) = Λ f
  证明: by
  rw [← eq_toRealPositiveLinear_toReal Λ f]; rw [← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
  simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

Depends on / 依赖: NNRealRMK, NNRealRMK.rieszMeasure, RealRMK, RealRMK.integral_rieszMeasure, RealRMK.rieszMeasure, eq_toRealPositiveLinear_toReal, f.toReal, integral_rieszMeasure, rieszMeasure, toReal, toRealPositiveLinear
-/
theorem integral_rieszMeasure (f : C_c(X, Real>=0)) : ∫ (x : X), (f x : Real) ∂(rieszMeasure Λ) = Λ f := by
  rw [← eq_toRealPositiveLinear_toReal Λ f]; rw [← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
  simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (lower) Lebesgue integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal
to `Λ f`. -/
@[simp]
/--
theorem `lintegral_rieszMeasure` / 定理 `lintegral_rieszMeasure`

English:
theorem lintegral_rieszMeasure
  given: (f : C_c(X, Real>=0))
  statement: ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f
  proof: by
  rw [lintegral_coe_eq_integral]; rw [← ENNReal.ofNNReal_toNNReal]
  · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integral_nonneg (by intro a; simp)),
       NNReal.eq_iff, NNReal.coe_mk]
    exact integral_rieszMeasure Λ f
  rw [rieszMeasure]
  exact Continuous.integrable_of_has

中文:
定理 lintegral_rieszMeasure
  条件: (f : C_c(X, 实数>=0))
  结论: ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f
  证明: by
  rw [lintegral_coe_eq_integral]; rw [← ENNReal.ofNNReal_toNNReal]
  · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integral_nonneg (by intro a; simp)),
       NNReal.eq_iff, NNReal.coe_mk]
    exact integral_rieszMeasure Λ f
  rw [rieszMeasure]
  exact Continuous.integrable_of_has

Depends on / 依赖: Continuous, Continuous.integrable_of_hasCompactSupport, ENNReal, ENNReal.coe_inj, ENNReal.ofNNReal_toNNReal, HasCompactSupport, HasCompactSupport.comp_left, MeasureTheory, MeasureTheory.integral_nonneg, NNReal, NNReal.coe_mk, NNReal.eq_iff, Real.toNNReal_of_nonneg, coe_inj, coe_mk, comp_left, eq_iff, f.hasCompactSupport, fun_prop, hasCompactSupport
-/
theorem lintegral_rieszMeasure (f : C_c(X, Real>=0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
  rw [lintegral_coe_eq_integral]; rw [← ENNReal.ofNNReal_toNNReal]
  · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integral_nonneg (by intro a; simp)),
       NNReal.eq_iff, NNReal.coe_mk]
    exact integral_rieszMeasure Λ f
  rw [rieszMeasure]
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.comp_left f.hasCompactSupport rfl)

/--
Instance `rieszMeasure_regular` / 实例 `rieszMeasure_regular`

English:
instance rieszMeasure_regular
  signature: (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0)
  body: (rieszContent Λ).regular

中文:
实例 rieszMeasure_regular
  签名: (Λ : C_c(X, 实数>=0) ->ₗ[实数>=0] 实数>=0)
  定义体: (rieszContent Λ).regular

Depends on / 依赖: regular, rieszContent
-/
instance rieszMeasure_regular (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0) : (rieszMeasure Λ).Regular :=
  (rieszContent Λ).regular

section integralLinearMap

/-! We show that `NNRealRMK.rieszMeasure` is a bijection between linear functionals on `C_c(X, ℝ≥0)`
and regular measures with inverse `NNRealRMK.integralLinearMap`. -/

/--
theorem `_root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal` / 定理 `_root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal`

English:
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  proof: by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  repeat rw [integral_eq_integral_pos_part_sub_integral_neg_part f.integrable]
  erw [hμν f.nnrealPart, hμν (-f).nnrealPart]
  rfl

中文:
定理 _root_.测度论.测度.ext_of_integral_eq_on_compactlySupported_nnreal
  证明: by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  repeat rw [integral_eq_integral_pos_part_sub_integral_neg_part f.integrable]
  erw [hμν f.nnrealPart, hμν (-f).nnrealPart]
  rfl

Depends on / 依赖: Measure, Measure.ext_of_integral_eq_on_compactlySupported, ext_of_integral_eq_on_compactlySupported, f.integrable, f.nnrealPart, integrable, integral_eq_integral_pos_part_sub_integral_neg_part, nnrealPart, repeat
-/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    (hμν : forall (f : C_c(X, Real>=0)), ∫ (x : X), (f x : Real) ∂μ = ∫ (x : X), (f x : Real) ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  repeat rw [integral_eq_integral_pos_part_sub_integral_neg_part f.integrable]
  erw [hμν f.nnrealPart, hμν (-f).nnrealPart]
  rfl

/-- If two regular measures induce the same linear functional on `C_c(X, ℝ≥0)`, then they are
equal. -/
@[simp]
/--
theorem `integralLinearMap_inj` / 定理 `integralLinearMap_inj`

English:
theorem integralLinearMap_inj
  given: {μ ν : Measure X} [μ.Regular] [ν.Regular]
  proof: ⟨fun hμν => Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f =>
      by simpa using congr(($hμν f).toReal), fun _ => by congr⟩

中文:
定理 integralLinearMap_inj
  条件: {μ ν : 测度 X} [μ.正则] [ν.正则]
  证明: ⟨fun hμν => Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f =>
      by simpa using congr(($hμν f).toReal), fun _ => by congr⟩

Depends on / 依赖: Measure, Measure.ext_of_integral_eq_on_compactlySupported_nnreal, ext_of_integral_eq_on_compactlySupported_nnreal, toReal
-/
theorem integralLinearMap_inj {μ ν : Measure X} [μ.Regular] [ν.Regular] :
    integralLinearMap μ = integralLinearMap ν ↔ μ = ν :=
  ⟨fun hμν => Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f =>
      by simpa using congr(($hμν f).toReal), fun _ => by congr⟩

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ≥0)`.
That is, `NNRealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
/--
theorem `rieszMeasure_integralLinearMap` / 定理 `rieszMeasure_integralLinearMap`

English:
theorem rieszMeasure_integralLinearMap
  given: {μ : Measure X} [μ.Regular]
  proof: Measure.ext_of_integral_eq_on_compactlySupported_nnreal (by simp)

@[simp]

中文:
定理 rieszMeasure_integralLinearMap
  条件: {μ : 测度 X} [μ.正则]
  证明: Measure.ext_of_integral_eq_on_compactlySupported_nnreal (by simp)

@[simp]

Depends on / 依赖: Measure, Measure.ext_of_integral_eq_on_compactlySupported_nnreal, ext_of_integral_eq_on_compactlySupported_nnreal
-/
theorem rieszMeasure_integralLinearMap {μ : Measure X} [μ.Regular] :
    rieszMeasure (integralLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported_nnreal (by simp)

@[simp]
/--
theorem `integralLinearMap_rieszMeasure` / 定理 `integralLinearMap_rieszMeasure`

English:
theorem integralLinearMap_rieszMeasure
  proof: by ext; simp

中文:
定理 integralLinearMap_rieszMeasure
  证明: by ext; simp
-/
theorem integralLinearMap_rieszMeasure :
    integralLinearMap (rieszMeasure Λ) = Λ := by ext; simp

end integralLinearMap

end NNRealRMK
