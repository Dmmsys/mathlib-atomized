/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!

# Conditional expectation of real-valued functions

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `MeasureTheory.rnDeriv_ae_eq_condExp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `MeasureTheory.Integrable.uniformIntegrable_condExp`: the conditional expectation of a function
  form a uniformly integrable class.

-/

public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

/--
theorem `rnDeriv_ae_eq_condExp` / 定理 `rnDeriv_ae_eq_condExp`

English:
theorem rnDeriv_ae_eq_condExp
  statement: {hm : m <= m0} [hμm : SigmaFinite (μ.trim hm)] {f : α -> Real}
  proof: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
  

中文:
定理 rnDeriv_ae_eq_condExp
  结论: {hm : m <= m0} [hμm : SigmaFinite (μ.trim hm)] {f : α -> 实数}
  证明: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
  

Depends on / 依赖: SignedMeasure, SignedMeasure.integrable_rnDeriv, SignedMeasure.withDensity, ae_eq_condExp_of_forall_setIntegral_eq, conv_rhs, hf.withDensity, integrableOn, integrable_of_integrable_trim, integrable_rnDeriv
-/
theorem rnDeriv_ae_eq_condExp {hm : m <= m0} [hμm : SigmaFinite (μ.trim hm)] {f : α -> Real}
    (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm)) hs]; rw [← setIntegral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable

section HasSolidNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/--
lemma `condExp_le_nonneg_const` / 引理 `condExp_le_nonneg_const`

English:
lemma condExp_le_nonneg_const
  statement: [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
  proof: by
  by_cases! hm : ¬ m <= m0
  · filter_upwards with a using by simpa [condExp_of_not_le hm]
  by_cases! hfint : ¬ Integrable f μ
  · filter_upwards with a using by simpa [condExp_of_not_integrable hfint]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · filter_upwards with a using by simpa [condExp

中文:
引理 condExp_le_nonneg_const
  结论: [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
  证明: by
  by_cases! hm : ¬ m <= m0
  · filter_upwards with a using by simpa [condExp_of_not_le hm]
  by_cases! hfint : ¬ Integrable f μ
  · filter_upwards with a using by simpa [condExp_of_not_integrable hfint]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · filter_upwards with a using by simpa [condExp

Depends on / 依赖: Integrable, SigmaFinite, condExp_of_not_integrable, condExp_of_not_le, condExp_of_not_sigmaFinite, filter_upwards, isCountablySpanning_spanningSets, measurableSet_spanningSets, null_of_forall_restrict_null
-/
lemma condExp_le_nonneg_const [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [IsOrderedModule Real E] {f : α -> E} {c : E} (hc : 0 <= c) (hfc : forallᵐ x ∂μ, f x <= c) :
    forallᵐ x ∂μ, μ[f | m] x <= c := by
  by_cases! hm : ¬ m <= m0
  · filter_upwards with a using by simpa [condExp_of_not_le hm]
  by_cases! hfint : ¬ Integrable f μ
  · filter_upwards with a using by simpa [condExp_of_not_integrable hfint]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · filter_upwards with a using by simpa [condExp_of_not_sigmaFinite hm hsig]
  refine (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null ?_ ?_ <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  · have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hfint
    have h2 := condExp_mono (μ := μ.restrict (spanningSets (μ.trim hm) n)) (m := m)
      hfint.restrict (integrable_const c) (ae_restrict_of_ae hfc)
    filter_upwards [h1, h2] with a ha hb
    grw [← ha, hb, condExp_const hm]

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule Real E]

/--
theorem `abs_condExp_ae_le_condExp_abs` / 定理 `abs_condExp_ae_le_condExp_abs`

English:
theorem abs_condExp_ae_le_condExp_abs
  given: (f : α -> E)
  statement: |(μ[f | m])| <=ᵐ[μ] μ[|f| | m]
  proof: by
  by_cases! hfint : ¬Integrable f μ
  · simp only [condExp_of_not_integrable hfint, abs_zero]
    apply condExp_nonneg
    filter_upwards with a using abs_nonneg (f a)
  have h1 := condExp_mono (m := m) hfint hfint.abs (.of_forall (fun x => le_abs_self f x))
  have h2 := condExp_mono (m := m) hfi

中文:
定理 abs_condExp_ae_le_condExp_abs
  条件: (f : α -> E)
  结论: |(μ[f | m])| <=ᵐ[μ] μ[|f| | m]
  证明: by
  by_cases! hfint : ¬Integrable f μ
  · simp only [condExp_of_not_integrable hfint, abs_zero]
    apply condExp_nonneg
    filter_upwards with a using abs_nonneg (f a)
  have h1 := condExp_mono (m := m) hfint hfint.abs (.of_forall (fun x => le_abs_self f x))
  have h2 := condExp_mono (m := m) hfi

Depends on / 依赖: Integrable, abs_le, abs_nonneg, abs_zero, condExp_mono, condExp_neg, condExp_nonneg, condExp_of_not_integrable, filter_upwards, hc.symm.le.trans, hfint.abs, hfint.neg, le_abs_self, neg_le_abs, of_forall
-/
theorem abs_condExp_ae_le_condExp_abs (f : α -> E) : |(μ[f | m])| <=ᵐ[μ] μ[|f| | m] := by
  by_cases! hfint : ¬Integrable f μ
  · simp only [condExp_of_not_integrable hfint, abs_zero]
    apply condExp_nonneg
    filter_upwards with a using abs_nonneg (f a)
  have h1 := condExp_mono (m := m) hfint hfint.abs (.of_forall (fun x => le_abs_self f x))
  have h2 := condExp_mono (m := m) hfint.neg hfint.abs (.of_forall fun x => neg_le_abs (f x))
  filter_upwards [h1, h2, condExp_neg f m] with a ha hb hc
  exact abs_le'.2 ⟨ha, hc.symm.le.trans hb⟩

/--
theorem `integral_abs_condExp_le` / 定理 `integral_abs_condExp_le`

English:
theorem integral_abs_condExp_le
  given: (f : α -> E)
  statement: ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| ∂μ
  proof: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ <= ∫ x, μ[|f| | m] x ∂μ :=
    integra

中文:
定理 integral_abs_condExp_le
  条件: (f : α -> E)
  结论: ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| ∂μ
  证明: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ <= ∫ x, μ[|f| | m] x ∂μ :=
    integra

Depends on / 依赖: SigmaFinite, abs_condExp_ae_le_condExp_abs, abs_nonneg, condExp_of_not_le, condExp_of_not_sigmaFinite, integrable_condExp, integrable_condExp.abs, integral_condExp, integral_mono_ae, integral_nonneg
-/
theorem integral_abs_condExp_le (f : α -> E) : ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| ∂μ := by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ <= ∫ x, μ[|f| | m] x ∂μ :=
    integral_mono_ae integrable_condExp.abs integrable_condExp (abs_condExp_ae_le_condExp_abs f)
  _ = _ := integral_condExp hm

/--
lemma `integral_condExp_le_of_ae_nonneg` / 引理 `integral_condExp_le_of_ae_nonneg`

English:
lemma integral_condExp_le_of_ae_nonneg
  given: {f : α -> Real} (hf : 0 <=ᵐ[μ] f)
  proof: calc
  ∫ x, μ[f | m] x ∂μ = ∫ x, |μ[f | m] x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_nonneg hf] with ω hω using (abs_of_nonneg hω).symm
  _ <= ∫ x, |f x| ∂μ := integral_abs_condExp_le f
  _ = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with ω hω us

中文:
引理 integral_condExp_le_of_ae_nonneg
  条件: {f : α -> 实数} (hf : 0 <=ᵐ[μ] f)
  证明: calc
  ∫ x, μ[f | m] x ∂μ = ∫ x, |μ[f | m] x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_nonneg hf] with ω hω using (abs_of_nonneg hω).symm
  _ <= ∫ x, |f x| ∂μ := integral_abs_condExp_le f
  _ = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with ω hω us
-/
lemma integral_condExp_le_of_ae_nonneg {f : α -> Real} (hf : 0 <=ᵐ[μ] f) :
    ∫ x, μ[f | m] x ∂μ <= ∫ x, f x ∂μ := calc
  ∫ x, μ[f | m] x ∂μ = ∫ x, |μ[f | m] x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_nonneg hf] with ω hω using (abs_of_nonneg hω).symm
  _ <= ∫ x, |f x| ∂μ := integral_abs_condExp_le f
  _ = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with ω hω using abs_of_nonneg hω

/--
theorem `setIntegral_abs_condExp_le` / 定理 `setIntegral_abs_condExp_le`

English:
theorem setIntegral_abs_condExp_le
  given: {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E)
  proof: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [cond

中文:
定理 setIntegral_abs_condExp_le
  条件: {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E)
  证明: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [cond

Depends on / 依赖: Integrable, SigmaFinite, abs_nonneg, condExp_of_not_integrable, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_restrict_ae_eq_restrict, fun_comp, integral_congr_ae, integral_nonneg, restrict
-/
theorem setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E) :
    ∫ x in s, |μ[f | m] x| ∂μ <= ∫ x in s, |f x| ∂μ := by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ = ∫ x in s, |(μ.restrict s)[f | m] x| ∂μ :=
    (integral_congr_ae ((condExp_restrict_ae_eq_restrict hm hs hfint).fun_comp abs)).symm
  _ <= _ := integral_abs_condExp_le f

/--
lemma `setIntegral_condExp_le_of_ae_restrict_nonneg` / 引理 `setIntegral_condExp_le_of_ae_restrict_nonneg`

English:
lemma setIntegral_condExp_le_of_ae_restrict_nonneg
  statement: {s : Set α} (hs : MeasurableSet[m] s) {f : α -> Real}
  proof: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not

中文:
引理 setIntegral_condExp_le_of_ae_restrict_nonneg
  结论: {s : Set α} (hs : MeasurableSet[m] s) {f : α -> 实数}
  证明: by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not

Depends on / 依赖: Integrable, SigmaFinite, condExp_of_not_integrable, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_restrict_ae_eq_restrict, integral_congr_ae, restrict, setIntegral_nonneg_of_ae_restrict
-/
lemma setIntegral_condExp_le_of_ae_restrict_nonneg {s : Set α} (hs : MeasurableSet[m] s) {f : α -> Real}
    (hf : 0 <=ᵐ[μ.restrict s] f) :
    ∫ x in s, μ[f | m] x ∂μ <= ∫ x in s, f x ∂μ := by
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using setIntegral_nonneg_of_ae_restrict hf
  calc
  ∫ x in s, μ[f | m] x ∂μ = ∫ x in s, (μ.restrict s)[f | m] x ∂μ :=
    integral_congr_ae (condExp_restrict_ae_eq_restrict hm hs hfint).symm
  _ <= ∫ x in s, f x ∂μ := integral_condExp_le_of_ae_nonneg hf

/--
lemma `setIntegral_condExp_le_of_ae_nonneg` / 引理 `setIntegral_condExp_le_of_ae_nonneg`

English:
lemma setIntegral_condExp_le_of_ae_nonneg
  statement: {s : Set α} (hs : MeasurableSet[m] s) {f : α -> Real}
  proof: setIntegral_condExp_le_of_ae_restrict_nonneg hs (ae_restrict_le hf)

中文:
引理 setIntegral_condExp_le_of_ae_nonneg
  结论: {s : Set α} (hs : MeasurableSet[m] s) {f : α -> 实数}
  证明: setIntegral_condExp_le_of_ae_restrict_nonneg hs (ae_restrict_le hf)

Depends on / 依赖: ae_restrict_le, setIntegral_condExp_le_of_ae_restrict_nonneg
-/
lemma setIntegral_condExp_le_of_ae_nonneg {s : Set α} (hs : MeasurableSet[m] s) {f : α -> Real}
    (hf : 0 <=ᵐ[μ] f) :
    ∫ x in s, μ[f | m] x ∂μ <= ∫ x in s, f x ∂μ :=
  setIntegral_condExp_le_of_ae_restrict_nonneg hs (ae_restrict_le hf)

/--
theorem `ae_bdd_abs_condExp_of_ae_bdd_abs` / 定理 `ae_bdd_abs_condExp_of_ae_bdd_abs`

English:
theorem ae_bdd_abs_condExp_of_ae_bdd_abs
  given: {R : E} {f : α -> E} (hbdd : forallᵐ x ∂μ, |f x| <= R)
  proof: by
  by_cases! hn : {x | |f x| <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  have hR : 0 <= R := (abs_nonneg _).trans hn.some_mem
  exact (abs_condExp_ae_le_condExp_abs f).trans (condExp_le_nonneg_const (m := m) hR hbdd)

中文:
定理 ae_bdd_abs_condExp_of_ae_bdd_abs
  条件: {R : E} {f : α -> E} (hbdd : 对任意ᵐ x ∂μ, |f x| <= R)
  证明: by
  by_cases! hn : {x | |f x| <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  have hR : 0 <= R := (abs_nonneg _).trans hn.some_mem
  exact (abs_condExp_ae_le_condExp_abs f).trans (condExp_le_nonneg_const (m := m) hR hbdd)

Depends on / 依赖: abs_condExp_ae_le_condExp_abs, abs_nonneg, ae_eq_empty, ae_eq_univ, condExp_le_nonneg_const, hn.some_mem, measure_mono_null, some_mem
-/
theorem ae_bdd_abs_condExp_of_ae_bdd_abs {R : E} {f : α -> E} (hbdd : forallᵐ x ∂μ, |f x| <= R) :
    forallᵐ x ∂μ, |μ[f | m] x| <= R := by
  by_cases! hn : {x | |f x| <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  have hR : 0 <= R := (abs_nonneg _).trans hn.some_mem
  exact (abs_condExp_ae_le_condExp_abs f).trans (condExp_le_nonneg_const (m := m) hR hbdd)

/-- If the real-valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
@[deprecated ae_bdd_abs_condExp_of_ae_bdd_abs (since := "2026-05-05")]
/--
theorem `ae_bdd_condExp_of_ae_bdd` / 定理 `ae_bdd_condExp_of_ae_bdd`

English:
theorem ae_bdd_condExp_of_ae_bdd
  given: {R : Real>=0} {f : α -> Real} (hbdd : forallᵐ x ∂μ, |f x| <= R)
  proof: by
  by_cases hnm : m <= m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply]; rw [

中文:
定理 ae_bdd_condExp_of_ae_bdd
  条件: {R : 实数>=0} {f : α -> 实数} (hbdd : 对任意ᵐ x ∂μ, |f x| <= R)
  证明: by
  by_cases hnm : m <= m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply]; rw [

Depends on / 依赖: Eventually, Eventually.of_forall, Integrable, Pi.zero_apply, R.coe_nonneg, Set.compl_def, Set.mem_ofPred_eq, abs_nonneg, abs_zero, coe_nonneg, compl_def, condExp_of_not_integrable, condExp_of_not_le, filter_upwards, mem_ofPred_eq, not_le, of_forall, pos_iff_ne_zero, simp_rw, zero_apply
-/
theorem ae_bdd_condExp_of_ae_bdd {R : Real>=0} {f : α -> Real} (hbdd : forallᵐ x ∂μ, |f x| <= R) :
    forallᵐ x ∂μ, |(μ[f | m]) x| <= R := by
  by_cases hnm : m <= m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply]; rw [abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ != 0 at h
  simp only [← pos_iff_ne_zero, Set.compl_def, Set.mem_ofPred_eq, not_le] at h
  suffices μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R < μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R by
    exact this.ne rfl
  refine lt_of_lt_of_le (setIntegral_gt_gt R.coe_nonneg ?_ h.ne') ?_
  · exact integrable_condExp.abs.integrableOn
  refine (setIntegral_abs_condExp_le ?_ _).trans ?_
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condExp.norm.measurable
  simp only [← smul_eq_mul, ← setIntegral_const]
  refine setIntegral_mono_ae hfint.abs.integrableOn ?_ hbdd
  refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_
    (integrable_condExp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
  refine setLIntegral_mono
    (stronglyMeasurable_condExp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => ?_
  rw [enorm_eq_nnnorm]; rw [enorm_eq_nnnorm]; rw [ENNReal.coe_le_coe]; rw [Real.nnnorm_of_nonneg R.coe_nonneg]
  exact Subtype.mk_le_mk.2 (le_of_lt hx)

end HasSolidNorm

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/--
theorem `integral_norm_condExp_rpow_le` / 定理 `integral_norm_condExp_rpow_le`

English:
theorem integral_norm_condExp_rpow_le
  statement: {p : Real} (hp : 1 <= p) {f : α -> E}
  proof: calc
  _ <= ∫ x, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp (Integrable.norm_condExp_rpow_le hp hf)
    filter_upwards with a using by positivity
  _ <= _ := by
    apply integral_condExp_le_of_ae_nonneg
    filter_upwards with ω using by positivi

中文:
定理 integral_norm_condExp_rpow_le
  结论: {p : 实数} (hp : 1 <= p) {f : α -> E}
  证明: calc
  _ <= ∫ x, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp (Integrable.norm_condExp_rpow_le hp hf)
    filter_upwards with a using by positivity
  _ <= _ := by
    apply integral_condExp_le_of_ae_nonneg
    filter_upwards with ω using by positivi
-/
theorem integral_norm_condExp_rpow_le {p : Real} (hp : 1 <= p) {f : α -> E}
    (hf : Integrable (‖f ·‖ ^ p) μ) :
    ∫ x, ‖μ[f | m] x‖ ^ p ∂μ <= ∫ x, ‖f x‖ ^ p ∂μ := calc
  _ <= ∫ x, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp (Integrable.norm_condExp_rpow_le hp hf)
    filter_upwards with a using by positivity
  _ <= _ := by
    apply integral_condExp_le_of_ae_nonneg
    filter_upwards with ω using by positivity

/--
theorem `integral_norm_condExp_le` / 定理 `integral_norm_condExp_le`

English:
theorem integral_norm_condExp_le
  given: (f : α -> E)
  statement: ∫ x, ‖μ[f | m] x‖ ∂μ <= ∫ x, ‖f x‖ ∂μ
  proof: by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using integral_norm_condExp_rpow_le le_rfl (by simpa using hfint.norm)

中文:
定理 integral_norm_condExp_le
  条件: (f : α -> E)
  结论: ∫ x, ‖μ[f | m] x‖ ∂μ <= ∫ x, ‖f x‖ ∂μ
  证明: by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using integral_norm_condExp_rpow_le le_rfl (by simpa using hfint.norm)

Depends on / 依赖: Integrable, condExp_of_not_integrable, hfint.norm, integral_nonneg, integral_norm_condExp_rpow_le, le_rfl, norm_nonneg
-/
theorem integral_norm_condExp_le (f : α -> E) : ∫ x, ‖μ[f | m] x‖ ∂μ <= ∫ x, ‖f x‖ ∂μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using integral_norm_condExp_rpow_le le_rfl (by simpa using hfint.norm)

/--
theorem `setIntegral_norm_condExp_rpow_le` / 定理 `setIntegral_norm_condExp_rpow_le`

English:
theorem setIntegral_norm_condExp_rpow_le
  statement: {p : Real} (hp : 1 <= p) {f : α -> E} {s : Set α}
  proof: by
  have hp' : p != 0 := by linarith
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm, hp'] using integral_nonneg (fun x => by positivity)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig, hp'] using integral_nonneg (fun x => by positivity)
  calc

中文:
定理 setIntegral_norm_condExp_rpow_le
  结论: {p : 实数} (hp : 1 <= p) {f : α -> E} {s : Set α}
  证明: by
  have hp' : p != 0 := by linarith
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm, hp'] using integral_nonneg (fun x => by positivity)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig, hp'] using integral_nonneg (fun x => by positivity)
  calc

Depends on / 依赖: SigmaFinite, condExp_of_not_le, condExp_of_not_sigmaFinite, condExp_restrict_ae_eq_restrict, filter_upwards, integrable_condExp, integrable_condExp.congr, integral_mono_of_nonneg, integral_nonneg
-/
theorem setIntegral_norm_condExp_rpow_le {p : Real} (hp : 1 <= p) {f : α -> E} {s : Set α}
    (hs : MeasurableSet[m] s) (hf : Integrable (‖f ·‖ ^ p) μ) :
    ∫ x in s, ‖μ[f | m] x‖ ^ p ∂μ <= ∫ x in s, ‖f x‖ ^ p ∂μ := by
  have hp' : p != 0 := by linarith
  by_cases! hm : ¬ m <= m0
  · simpa [condExp_of_not_le hm, hp'] using integral_nonneg (fun x => by positivity)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig, hp'] using integral_nonneg (fun x => by positivity)
  calc
  _ <= ∫ x in s, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with a using by positivity
    · exact integrable_condExp.congr (condExp_restrict_ae_eq_restrict hm hs hf)
    · exact ae_restrict_le (Integrable.norm_condExp_rpow_le hp hf)
  _ <= _ := by
    apply setIntegral_condExp_le_of_ae_nonneg hs
    filter_upwards with ω using by positivity

/--
theorem `setIntegral_norm_condExp_le` / 定理 `setIntegral_norm_condExp_le`

English:
theorem setIntegral_norm_condExp_le
  given: {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E)
  proof: by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using setIntegral_norm_condExp_rpow_le le_rfl hs (by simpa using hfint.norm)

中文:
定理 setIntegral_norm_condExp_le
  条件: {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E)
  证明: by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using setIntegral_norm_condExp_rpow_le le_rfl hs (by simpa using hfint.norm)

Depends on / 依赖: Integrable, condExp_of_not_integrable, hfint.norm, integral_nonneg, le_rfl, norm_nonneg, setIntegral_norm_condExp_rpow_le
-/
theorem setIntegral_norm_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α -> E) :
    ∫ x in s, ‖(μ[f | m]) x‖ ∂μ <= ∫ x in s, ‖f x‖ ∂μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using setIntegral_norm_condExp_rpow_le le_rfl hs (by simpa using hfint.norm)

/--
theorem `ae_bdd_norm_condExp_of_ae_bdd_norm` / 定理 `ae_bdd_norm_condExp_of_ae_bdd_norm`

English:
theorem ae_bdd_norm_condExp_of_ae_bdd_norm
  given: {R : Real} {f : α -> E} (hbdd : forallᵐ x ∂μ, ‖f x‖ <= R)
  proof: by
  by_cases! hn : {x | ‖f x‖ <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  exact (norm_condExp_le f).trans (condExp_le_nonneg_const ((norm_nonneg _).trans hn.some_mem) hbdd)

中文:
定理 ae_bdd_norm_condExp_of_ae_bdd_norm
  条件: {R : 实数} {f : α -> E} (hbdd : 对任意ᵐ x ∂μ, ‖f x‖ <= R)
  证明: by
  by_cases! hn : {x | ‖f x‖ <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  exact (norm_condExp_le f).trans (condExp_le_nonneg_const ((norm_nonneg _).trans hn.some_mem) hbdd)

Depends on / 依赖: ae_eq_empty, ae_eq_univ, condExp_le_nonneg_const, hn.some_mem, measure_mono_null, norm_condExp_le, norm_nonneg, some_mem
-/
theorem ae_bdd_norm_condExp_of_ae_bdd_norm {R : Real} {f : α -> E} (hbdd : forallᵐ x ∂μ, ‖f x‖ <= R) :
    forallᵐ x ∂μ, ‖μ[f | m] x‖ <= R := by
  by_cases! hn : {x | ‖f x‖ <= R} = ∅
· exact measure_mono_null (by simp) ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  exact (norm_condExp_le f).trans (condExp_le_nonneg_const ((norm_nonneg _).trans hn.some_mem) hbdd)

/--
theorem `MemLp.ae_norm_condExp_le_essSup` / 定理 `MemLp.ae_norm_condExp_le_essSup`

English:
theorem MemLp.ae_norm_condExp_le_essSup
  given: {f : α -> E} (hf : MemLp f ∞ μ)
  proof: ae_bdd_norm_condExp_of_ae_bdd_norm (ae_le_essSup ⟨_, ae_le_lpNorm_exponent_top hf⟩)

中文:
定理 MemLp.ae_norm_condExp_le_essSup
  条件: {f : α -> E} (hf : MemLp f ∞ μ)
  证明: ae_bdd_norm_condExp_of_ae_bdd_norm (ae_le_essSup ⟨_, ae_le_lpNorm_exponent_top hf⟩)

Depends on / 依赖: ae_bdd_norm_condExp_of_ae_bdd_norm, ae_le_essSup, ae_le_lpNorm_exponent_top
-/
theorem MemLp.ae_norm_condExp_le_essSup {f : α -> E} (hf : MemLp f ∞ μ) :
    forallᵐ (x : α) ∂μ, ‖μ[f | m] x‖ <= essSup (‖f ·‖) μ :=
  ae_bdd_norm_condExp_of_ae_bdd_norm (ae_le_essSup ⟨_, ae_le_lpNorm_exponent_top hf⟩)

/--
theorem `MemLp.essSup_norm_condExp_le_essSup_norm` / 定理 `MemLp.essSup_norm_condExp_le_essSup_norm`

English:
theorem MemLp.essSup_norm_condExp_le_essSup_norm
  given: [NeZero μ] {f : α -> E} (hf : MemLp f ∞ μ)
  proof: essSup_le_of_ae_le _ hf.ae_norm_condExp_le_essSup
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))

中文:
定理 MemLp.essSup_norm_condExp_le_essSup_norm
  条件: [NeZero μ] {f : α -> E} (hf : MemLp f ∞ μ)
  证明: essSup_le_of_ae_le _ hf.ae_norm_condExp_le_essSup
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))

Depends on / 依赖: ae_norm_condExp_le_essSup, essSup_le_of_ae_le, hf.ae_norm_condExp_le_essSup, isCoboundedUnder_le_of_le, norm_nonneg
-/
theorem MemLp.essSup_norm_condExp_le_essSup_norm [NeZero μ] {f : α -> E} (hf : MemLp f ∞ μ) :
    essSup (fun x => ‖μ[f | m] x‖) μ <= essSup (fun x => ‖f x‖) μ :=
  essSup_le_of_ae_le _ hf.ae_norm_condExp_le_essSup
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))

/--
theorem `MemLp.lpNorm_condExp_le_lpNorm` / 定理 `MemLp.lpNorm_condExp_le_lpNorm`

English:
theorem MemLp.lpNorm_condExp_le_lpNorm
  given: {f : α -> E} {p : Real>=0∞} (hp : 1 <= p) (hf : MemLp f p μ)
  proof: by
  by_cases NeZero μ
  · have hp' : 0 < p := zero_lt_one.trans_le hp
    by_cases! hm : ¬ m <= m0
    · simp [condExp_of_not_le hm]
    by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
    · simp [condExp_of_not_sigmaFinite hm hsig]
    · by_cases! hpt : p != ⊤
      · rw [lpNorm_eq_integral_norm_rpow_t

中文:
定理 MemLp.lpNorm_condExp_le_lpNorm
  条件: {f : α -> E} {p : 实数>=0∞} (hp : 1 <= p) (hf : MemLp f p μ)
  证明: by
  by_cases NeZero μ
  · have hp' : 0 < p := zero_lt_one.trans_le hp
    by_cases! hm : ¬ m <= m0
    · simp [condExp_of_not_le hm]
    by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
    · simp [condExp_of_not_sigmaFinite hm hsig]
    · by_cases! hpt : p != ⊤
      · rw [lpNorm_eq_integral_norm_rpow_t

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, ENNReal.toReal_le_toReal, ENNReal.toReal_one, NeZero, SigmaFinite, condExp_of_not_le, condExp_of_not_sigmaFinite, integrable_condExp, lpNorm_eq_integral_norm_rpow_toReal, ne.symm, one_ne_top, p.toReal, toReal, toReal_le_toReal, toReal_one, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem MemLp.lpNorm_condExp_le_lpNorm {f : α -> E} {p : Real>=0∞} (hp : 1 <= p) (hf : MemLp f p μ) :
    lpNorm μ[f | m] p μ <= lpNorm f p μ := by
  by_cases NeZero μ
  · have hp' : 0 < p := zero_lt_one.trans_le hp
    by_cases! hm : ¬ m <= m0
    · simp [condExp_of_not_le hm]
    by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
    · simp [condExp_of_not_sigmaFinite hm hsig]
    · by_cases! hpt : p != ⊤
      · rw [lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt hf.1,
          lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt integrable_condExp.1]
        gcongr ?_ ^ ?_
        have : 1 <= p.toReal := by
          rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
exact integral_norm_condExp_rpow_le this
          (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
      · by_cases! h : MemLp μ[f | m] ⊤ μ
        · simp_all only [lpNorm_exponent_top_eq_essSup]
          exact hf.essSup_norm_condExp_le_essSup_norm
        · simp_all
  · simp_all [not_neZero]

/--
theorem `MemLp.condExp` / 定理 `MemLp.condExp`

English:
theorem MemLp.condExp
  given: {f : α -> E} {p : Real>=0∞} (hp : 1 <= p) (hf : MemLp f p μ)
  proof: by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p != ⊤
  · rw [← integrable_norm_rpow_iff integrable_condExp.1 hp'.ne.symm hpt]
    have hp : 1 <= p.toReal := by
      rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
have := Integrable.norm_condExp_rpow_

中文:
定理 MemLp.condExp
  条件: {f : α -> E} {p : 实数>=0∞} (hp : 1 <= p) (hf : MemLp f p μ)
  证明: by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p != ⊤
  · rw [← integrable_norm_rpow_iff integrable_condExp.1 hp'.ne.symm hpt]
    have hp : 1 <= p.toReal := by
      rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
have := Integrable.norm_condExp_rpow_

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, ENNReal.toReal_le_toReal, ENNReal.toReal_one, Integrable, Integrable.mono_nonneg, Integrable.norm_condExp_rpow_le, discharger, filter_upwards, fun_prop, integrable_condExp, integrable_norm_rpow_iff, mono_nonneg, ne.symm, norm_condExp_rpow_le, one_ne_top, p.toReal, toReal, toReal_le_toReal, toReal_one
-/
theorem MemLp.condExp {f : α -> E} {p : Real>=0∞} (hp : 1 <= p) (hf : MemLp f p μ) :
    MemLp (μ[f | m]) p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p != ⊤
  · rw [← integrable_norm_rpow_iff integrable_condExp.1 hp'.ne.symm hpt]
    have hp : 1 <= p.toReal := by
      rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
have := Integrable.norm_condExp_rpow_le (m := m) hp
      (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
    refine Integrable.mono_nonneg integrable_condExp ?_ ?_ this
    · fun_prop (discharger := simp)
    · filter_upwards with a; positivity
  · simp_all only
    exact memLp_top_of_bound integrable_condExp.1 (essSup (‖f ·‖) μ) hf.ae_norm_condExp_le_essSup

/--
theorem `eLpNorm_condExp_le_eLpNorm` / 定理 `eLpNorm_condExp_le_eLpNorm`

English:
theorem eLpNorm_condExp_le_eLpNorm
  given: (f : α -> E) {p : Real>=0∞} (hp : 1 <= p)
  proof: by
  by_cases! hf : MemLp f p μ
  · rw [← ofReal_lpNorm hf, ← ofReal_lpNorm (hf.condExp hp)]
    exact ENNReal.ofReal_le_ofReal (hf.lpNorm_condExp_le_lpNorm hp)
  · simp only [MemLp, not_and, not_lt, top_le_iff] at hf
    by_cases! ha : AEStronglyMeasurable f μ
    · simp [hf ha]
    · simp [condExp

中文:
定理 eLpNorm_condExp_le_eLpNorm
  条件: (f : α -> E) {p : 实数>=0∞} (hp : 1 <= p)
  证明: by
  by_cases! hf : MemLp f p μ
  · rw [← ofReal_lpNorm hf, ← ofReal_lpNorm (hf.condExp hp)]
    exact ENNReal.ofReal_le_ofReal (hf.lpNorm_condExp_le_lpNorm hp)
  · simp only [MemLp, not_and, not_lt, top_le_iff] at hf
    by_cases! ha : AEStronglyMeasurable f μ
    · simp [hf ha]
    · simp [condExp

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.ofReal_le_ofReal, aestronglyMeasurable, condExp, condExp_of_not_integrable, h.aestronglyMeasurable, hf.condExp, hf.lpNorm_condExp_le_lpNorm, lpNorm_condExp_le_lpNorm, not_and, not_lt, ofReal_le_ofReal, ofReal_lpNorm, top_le_iff
-/
theorem eLpNorm_condExp_le_eLpNorm (f : α -> E) {p : Real>=0∞} (hp : 1 <= p) :
    eLpNorm (μ[f | m]) p μ <= eLpNorm f p μ := by
  by_cases! hf : MemLp f p μ
  · rw [← ofReal_lpNorm hf, ← ofReal_lpNorm (hf.condExp hp)]
    exact ENNReal.ofReal_le_ofReal (hf.lpNorm_condExp_le_lpNorm hp)
  · simp only [MemLp, not_and, not_lt, top_le_iff] at hf
    by_cases! ha : AEStronglyMeasurable f μ
    · simp [hf ha]
    · simp [condExp_of_not_integrable (fun h => ha h.aestronglyMeasurable)]

@[deprecated eLpNorm_condExp_le_eLpNorm (since := "2026-07-01")]
/--
theorem `eLpNorm_one_condExp_le_eLpNorm` / 定理 `eLpNorm_one_condExp_le_eLpNorm`

English:
theorem eLpNorm_one_condExp_le_eLpNorm
  given: (f : α -> E)
  statement: eLpNorm (μ[f | m]) 1 μ <= eLpNorm f 1 μ
  proof: eLpNorm_condExp_le_eLpNorm f (refl 1)

中文:
定理 eLpNorm_one_condExp_le_eLpNorm
  条件: (f : α -> E)
  结论: eLpNorm (μ[f | m]) 1 μ <= eLpNorm f 1 μ
  证明: eLpNorm_condExp_le_eLpNorm f (refl 1)

Depends on / 依赖: eLpNorm_condExp_le_eLpNorm
-/
theorem eLpNorm_one_condExp_le_eLpNorm (f : α -> E) : eLpNorm (μ[f | m]) 1 μ <= eLpNorm f 1 μ :=
    eLpNorm_condExp_le_eLpNorm f (refl 1)

end NormedSpace

/--
theorem `Integrable.uniformIntegrable_condExp` / 定理 `Integrable.uniformIntegrable_condExp`

English:
theorem Integrable.uniformIntegrable_condExp
  statement: {ι : Type*} [IsFiniteMeasure μ] {g : α -> Real}
  proof: by
  let A : MeasurableSpace α := m0
  have hmeas : forall n, forall C, MeasurableSet {x | C <= ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformI

中文:
定理 Integrable.uniformIntegrable_condExp
  结论: {ι : 类型} [IsFiniteMeasure μ] {g : α -> 实数}
  证明: by
  let A : MeasurableSpace α := m0
  have hmeas : forall n, forall C, MeasurableSet {x | C <= ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformI

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, MeasurableSet, MeasurableSpace, aestronglyMeasurable, eLpNorm, eLpNorm_eq_zero_iff, le_rfl, measurable, measurable.nnnorm, measurableSet_le, measurable_const, memLp_one_iff_integrable, nnnorm, one_ne_top, one_ne_zero, stronglyMeasurable_condExp, stronglyMeasurable_condExp.mono, uniformIntegrable_of
-/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α -> Real}
    (hint : Integrable g μ) {ℱ : ι -> MeasurableSpace α} (hℱ : forall i, ℱ i <= m0) :
    UniformIntegrable (fun i => μ[g | ℱ i]) 1 μ := by
  let A : MeasurableSpace α := m0
  have hmeas : forall n, forall C, MeasurableSet {x | C <= ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans zero_le⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp [hx]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : Real>=0 := (.mk δ hδ.le)⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : forall n, μ {x : α | C <= ‖(μ[g|ℱ n]) x‖₊} <= ENNReal.ofReal δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C <= ‖μ[g|ℱ n] x‖₊} <=
        eLpNorm μ[g | ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one]; rw [ENNReal.rpow_one]
      convert!
        mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top
          (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable C
      · rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one]; rw [ENNReal.rpow_one]; rw [mul_comm]; rw [←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)]; rw [hC]; rw [NNReal.inv_mk]; rw [ENNReal.coe_mul]; rw [ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne]; rw [← mul_assoc]; rw [←
      ENNReal.ofReal_eq_coe_nnreal]; rw [← ENNReal.ofReal_mul hδ.le]; rw [mul_inv_cancel₀ hδ.ne']; rw [ENNReal.ofReal_one]; rw [one_mul]; rw [ENNReal.rpow_one]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C <= ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C <= ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condExp.measurable)
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_condExp_le_eLpNorm _ le_rfl

end MeasureTheory
