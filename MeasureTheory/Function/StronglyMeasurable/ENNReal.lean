/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Finitely strongly measurable functions with value in ENNReal

A measurable function with finite Lebesgue integral can be approximated by simple functions
whose support has finite measure.

-/

public section

open MeasureTheory
open scoped ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ≥0∞}

/-
**ENNReal.finStronglyMeasurable_of_measurable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ENNReal.finStronglyMeasurable_of_measurable (hf : ∫⁻ x, f x ∂μ != ∞) (hf_m
eas : Measurable f) : FinStronglyMeasurable f μ
参数：hf : ∫⁻ x, f x ∂μ != ∞；hf_meas : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_support_eapprox_lt_top`：measure_support_eapprox_lt
_top {f : α -> Real>=0∞} (hf_meas : Measurable f) (hf : ∫⁻ x, f x ∂μ != ∞) (n : 
Nat) : μ (Function.support (eappro…
· 使用引理 `MeasureTheory.SimpleFunc.tendsto_eapprox`：tendsto_eapprox {f : α -> Real
>=0∞} (hf_meas : Measurable f) (a : α) : Tendsto (fun n => eapprox f n a) atTop 
(𝓝 (f a))
-/
lemma ENNReal.finStronglyMeasurable_of_measurable (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hf_meas : Measurable f) :
    FinStronglyMeasurable f μ :=
  ⟨SimpleFunc.eapprox f, measure_support_eapprox_lt_top hf_meas hf,
    SimpleFunc.tendsto_eapprox hf_meas⟩
/-
**ENNReal.aefinStronglyMeasurable_of_aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ENNReal.aefinStronglyMeasurable_of_aemeasurable (hf : ∫⁻ x, f x ∂μ != ∞) (
hf_meas : AEMeasurable f μ) : AEFinStronglyMeasurable f μ
参数：hf : ∫⁻ x, f x ∂μ != ∞；hf_meas : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ENNReal.finStronglyMeasurable_of_measurable`：ENNReal.finStronglyMeasurab
le_of_measurable (hf : ∫⁻ x, f x ∂μ != ∞) (hf_meas : Measurable f) : FinStrongly
Measurable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
-/
lemma ENNReal.aefinStronglyMeasurable_of_aemeasurable (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hf_meas : AEMeasurable f μ) :
    AEFinStronglyMeasurable f μ := by
  refine ⟨hf_meas.mk f, ENNReal.finStronglyMeasurable_of_measurable ?_ hf_meas.measurable_mk,
    hf_meas.ae_eq_mk⟩
  rwa [lintegral_congr_ae hf_meas.ae_eq_mk.symm]
