/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.condExp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is an
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/

public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω -> E}

/--
theorem `condExp_indep_eq` / 定理 `condExp_indep_eq`

English:
theorem condExp_indep_eq
  statement: (hle₁ : m₁ <= m) (hle₂ : m₂ <= m) [SigmaFinite (μ.trim hle₂)]
  proof: by
  by_cases hfint : Integrable f μ
  swap; · rw [condExp_of_not_integrable hfint, integral_undef hfint]; rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle₂ hfint
    (fun s _ hs => integrableOn_const hs.ne) (fun s hms hs => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const]
  rw [← memLp_one_iff_integrable] at hfint
  refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint ?_
  · exact ⟨f, hf, EventuallyEq.rfl⟩
  · intro c t hmt _
    rw [Indep_iff] at hindp
    rw [integral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [smul_smul]; rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [mul_comm]; rw [← hindp _ _ hmt hms]; rw [setIntegral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [Set.inter_comm]; rw [measureReal_def]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    rw [memLp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint]; rw [smul_add]; rw [hu_eq]; rw [hv_eq]; rw [integral_add' huint.integrableOn hvint.integrableOn]
  · have h_integral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x, (f : Ω -> E) x ∂μ := by
      simpa using! continuous_integral.comp (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    have h_setIntegral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x in s, (f : Ω -> E) x ∂μ := by
      simpa using! (continuous_setIntegral s).comp
        (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
  · intro u v huv _ hueq
    rwa [← integral_congr_ae huv, ←
      (setIntegral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx

中文:
定理 condExp_indep_eq
  结论: (hle₁ : m₁ <= m) (hle₂ : m₂ <= m) [σ有限 (μ.trim hle₂)]
  证明: by
  by_cases hfint : Integrable f μ
  swap; · rw [condExp_of_not_integrable hfint, integral_undef hfint]; rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle₂ hfint
    (fun s _ hs => integrableOn_const hs.ne) (fun s hms hs => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const]
  rw [← memLp_one_iff_integrable] at hfint
  refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint ?_
  · exact ⟨f, hf, EventuallyEq.rfl⟩
  · intro c t hmt _
    rw [Indep_iff] at hindp
    rw [integral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [smul_smul]; rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [mul_comm]; rw [← hindp _ _ hmt hms]; rw [setIntegral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [Set.inter_comm]; rw [measureReal_def]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    rw [memLp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint]; rw [smul_add]; rw [hu_eq]; rw [hv_eq]; rw [integral_add' huint.integrableOn hvint.integrableOn]
  · have h_integral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x, (f : Ω -> E) x ∂μ := by
      simpa using! continuous_integral.comp (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    have h_setIntegral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x in s, (f : Ω -> E) x ∂μ := by
      simpa using! (continuous_setIntegral s).comp
        (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
  · intro u v huv _ hueq
    rwa [← integral_congr_ae huv, ←
      (setIntegral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, EventuallyEq, EventuallyEq.rfl, Indep_iff, Integrable, MemLp.induction_stronglyMeasurable, ae_eq_condExp_of_forall_setIntegral_eq, aestronglyMeasurable, condExp_of_not_integrable, hs.ne, induction_stronglyMeasurable, integrableOn_const, integral_undef, memLp_one_iff_integrable, one_ne_top, setIntegral_const, stronglyMeasurable_const, stronglyMeasurable_const.aestronglyMeasurable
-/
theorem condExp_indep_eq (hle₁ : m₁ <= m) (hle₂ : m₂ <= m) [SigmaFinite (μ.trim hle₂)]
    (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] fun _ => μ[f] := by
  by_cases hfint : Integrable f μ
  swap; · rw [condExp_of_not_integrable hfint, integral_undef hfint]; rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle₂ hfint
    (fun s _ hs => integrableOn_const hs.ne) (fun s hms hs => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const]
  rw [← memLp_one_iff_integrable] at hfint
  refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint ?_
  · exact ⟨f, hf, EventuallyEq.rfl⟩
  · intro c t hmt _
    rw [Indep_iff] at hindp
    rw [integral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [smul_smul]; rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_mul]; rw [mul_comm]; rw [← hindp _ _ hmt hms]; rw [setIntegral_indicator (hle₁ _ hmt)]; rw [setIntegral_const]; rw [Set.inter_comm]; rw [measureReal_def]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    rw [memLp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint]; rw [smul_add]; rw [hu_eq]; rw [hv_eq]; rw [integral_add' huint.integrableOn hvint.integrableOn]
  · have h_integral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x, (f : Ω -> E) x ∂μ := by
      simpa using! continuous_integral.comp (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    have h_setIntegral : Continuous fun f : lpMeas E Real m₁ 1 μ => ∫ x in s, (f : Ω -> E) x ∂μ := by
      simpa using! (continuous_setIntegral s).comp
        (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
  · intro u v huv _ hueq
    rwa [← integral_congr_ae huv, ←
      (setIntegral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx

end MeasureTheory
