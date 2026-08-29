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

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α -> Real>=0∞}

/--
lemma `ENNReal.finStronglyMeasurable_of_measurable` / 引理 `ENNReal.finStronglyMeasurable_of_measurable`

English:
lemma ENNReal.finStronglyMeasurable_of_measurable
  statement: (hf : ∫⁻ x, f x ∂μ != ∞)
  proof: ⟨SimpleFunc.eapprox f, measure_support_eapprox_lt_top hf_meas hf,
    SimpleFunc.tendsto_eapprox hf_meas⟩

中文:
引理 广义非负实数.finStronglyMeasurable_of_measurable
  结论: (hf : ∫⁻ x, f x ∂μ != ∞)
  证明: ⟨SimpleFunc.eapprox f, measure_support_eapprox_lt_top hf_meas hf,
    SimpleFunc.tendsto_eapprox hf_meas⟩

Depends on / 依赖: SimpleFunc, SimpleFunc.eapprox, SimpleFunc.tendsto_eapprox, eapprox, hf_meas, measure_support_eapprox_lt_top, tendsto_eapprox
-/
lemma ENNReal.finStronglyMeasurable_of_measurable (hf : ∫⁻ x, f x ∂μ != ∞)
    (hf_meas : Measurable f) :
    FinStronglyMeasurable f μ :=
  ⟨SimpleFunc.eapprox f, measure_support_eapprox_lt_top hf_meas hf,
    SimpleFunc.tendsto_eapprox hf_meas⟩

/--
lemma `ENNReal.aefinStronglyMeasurable_of_aemeasurable` / 引理 `ENNReal.aefinStronglyMeasurable_of_aemeasurable`

English:
lemma ENNReal.aefinStronglyMeasurable_of_aemeasurable
  statement: (hf : ∫⁻ x, f x ∂μ != ∞)
  proof: by
  refine ⟨hf_meas.mk f, ENNReal.finStronglyMeasurable_of_measurable ?_ hf_meas.measurable_mk,
    hf_meas.ae_eq_mk⟩
  rwa [lintegral_congr_ae hf_meas.ae_eq_mk.symm]

中文:
引理 广义非负实数.aefinStronglyMeasurable_of_aemeasurable
  结论: (hf : ∫⁻ x, f x ∂μ != ∞)
  证明: by
  refine ⟨hf_meas.mk f, ENNReal.finStronglyMeasurable_of_measurable ?_ hf_meas.measurable_mk,
    hf_meas.ae_eq_mk⟩
  rwa [lintegral_congr_ae hf_meas.ae_eq_mk.symm]

Depends on / 依赖: ENNReal, ENNReal.finStronglyMeasurable_of_measurable, ae_eq_mk, finStronglyMeasurable_of_measurable, hf_meas, hf_meas.ae_eq_mk, hf_meas.ae_eq_mk.symm, hf_meas.measurable_mk, hf_meas.mk, lintegral_congr_ae, measurable_mk
-/
lemma ENNReal.aefinStronglyMeasurable_of_aemeasurable (hf : ∫⁻ x, f x ∂μ != ∞)
    (hf_meas : AEMeasurable f μ) :
    AEFinStronglyMeasurable f μ := by
  refine ⟨hf_meas.mk f, ENNReal.finStronglyMeasurable_of_measurable ?_ hf_meas.measurable_mk,
    hf_meas.ae_eq_mk⟩
  rwa [lintegral_congr_ae hf_meas.ae_eq_mk.symm]
