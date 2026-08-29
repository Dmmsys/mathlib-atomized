/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Conditional expectation of indicator functions

This file proves some results about the conditional expectation of an indicator function and
as a corollary, also proves several results about the behaviour of the conditional expectation on
a restricted measure.

## Main result

* `MeasureTheory.condExp_indicator`: If `s` is an `m`-measurable set, then the conditional
  expectation of the indicator function of `s` is almost everywhere equal to the indicator
  of `s` of the conditional expectation. Namely, `𝔼[s.indicator f | m] = s.indicator 𝔼[f | m]` a.e.

-/

public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E : Type*} {m m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E] {μ : Measure α} {f : α -> E} {s : Set α}

/--
theorem `condExp_ae_eq_restrict_zero` / 定理 `condExp_ae_eq_restrict_zero`

English:
theorem condExp_ae_eq_restrict_zero
  given: (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0)
  proof: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf_int]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm ?_ ?_ ?_ ?_ ?_
  · exact fun t _ _ => integrable_condExp.integrableOn.integrableOn
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
  · intro t ht _
    rw [Measure.restrict_restrict (hm _ ht)]; rw [setIntegral_condExp hm hf_int (ht.inter hs)]; rw [←
      Measure.restrict_restrict (hm _ ht)]
    refine setIntegral_congr_ae (hm _ ht) ?_
    filter_upwards [hf] with x hx _ using hx
  · exact stronglyMeasurable_condExp.aestronglyMeasurable
  · exact stronglyMeasurable_zero.aestronglyMeasurable

中文:
定理 condExp_ae_eq_restrict_zero
  条件: (hs : 可测集[m] s) (hf : f =ᵐ[μ.restrict s] 0)
  证明: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf_int]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm ?_ ?_ ?_ ?_ ?_
  · exact fun t _ _ => integrable_condExp.integrableOn.integrableOn
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
  · intro t ht _
    rw [Measure.restrict_restrict (hm _ ht)]; rw [setIntegral_condExp hm hf_int (ht.inter hs)]; rw [←
      Measure.restrict_restrict (hm _ ht)]
    refine setIntegral_congr_ae (hm _ ht) ?_
    filter_upwards [hf] with x hx _ using hx
  · exact stronglyMeasurable_condExp.aestronglyMeasurable
  · exact stronglyMeasurable_zero.aestronglyMeasurable

Depends on / 依赖: Integrable, Restrict, Restrict.sigmaFinite, SigmaFinite, ae_eq_of_forall_setIntegral_eq_of_sigmaFinite, condExp_of_not_integrable, condExp_of_not_le, condExp_of_not_sigmaFinite, hf_int, integrable_cond, restrict, restrict_trim, sigmaFinite, simp_rw
-/
theorem condExp_ae_eq_restrict_zero (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
    μ[f | m] =ᵐ[μ.restrict s] 0 := by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf_int]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm ?_ ?_ ?_ ?_ ?_
  · exact fun t _ _ => integrable_condExp.integrableOn.integrableOn
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
  · intro t ht _
    rw [Measure.restrict_restrict (hm _ ht)]; rw [setIntegral_condExp hm hf_int (ht.inter hs)]; rw [←
      Measure.restrict_restrict (hm _ ht)]
    refine setIntegral_congr_ae (hm _ ht) ?_
    filter_upwards [hf] with x hx _ using hx
  · exact stronglyMeasurable_condExp.aestronglyMeasurable
  · exact stronglyMeasurable_zero.aestronglyMeasurable

/--
theorem `condExp_indicator_aux` / 定理 `condExp_indicator_aux`

English:
theorem condExp_indicator_aux
  given: (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0)
  proof: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  have hsf_zero : forall g : α -> E, g =ᵐ[μ.restrict sᶜ] 0 -> s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine ((hsf_zero (μ[f | m]) (condExp_ae_eq_restrict_zero hs.compl hf)).trans ?_).symm
  exact condExp_congr_ae (hsf_zero f hf).symm

中文:
定理 condExp_indicator_aux
  条件: (hs : 可测集[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0)
  证明: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  have hsf_zero : forall g : α -> E, g =ᵐ[μ.restrict sᶜ] 0 -> s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine ((hsf_zero (μ[f | m]) (condExp_ae_eq_restrict_zero hs.compl hf)).trans ?_).symm
  exact condExp_congr_ae (hsf_zero f hf).symm

Depends on / 依赖: Set.indicator_zero, condExp_ae_eq_restrict_zero, condExp_congr_ae, condExp_of_not_le, hs.compl, hsf_zero, indicator, indicator_ae_eq_of_restrict_compl_ae_eq_zero, indicator_zero, restrict, s.indicator, simp_rw
-/
theorem condExp_indicator_aux (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) := by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  have hsf_zero : forall g : α -> E, g =ᵐ[μ.restrict sᶜ] 0 -> s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine ((hsf_zero (μ[f | m]) (condExp_ae_eq_restrict_zero hs.compl hf)).trans ?_).symm
  exact condExp_congr_ae (hsf_zero f hf).symm

/--
theorem `condExp_indicator` / 定理 `condExp_indicator`

English:
theorem condExp_indicator
  given: (hf_int : Integrable f μ) (hs : MeasurableSet[m] s)
  proof: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f | m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine (this.trans ?_).symm
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f | m] + μ[sᶜ.indicator f | m]) := by
      filter_upwards [condExp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)) m]
        with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f | m]) + s.indicator (μ[sᶜ.indicator f | m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f | m])) := by
      refine Filter.EventuallyEq.rfl.add ?_
      have : sᶜ.indicator (μ[sᶜ.indicator f | m]) =ᵐ[μ] μ[sᶜ.indicator f | m] := by
        refine (condExp_indicator_aux hs.compl ?_).symm.trans ?_
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x in s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_notMem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) := by
      rw [Set.indicator_indicator]; rw [Set.inter_compl_self]; rw [Set.indicator_empty']; rw [add_zero]
    _ =ᵐ[μ] μ[s.indicator f | m] := by
      refine (condExp_indicator_aux hs ?_).symm.trans ?_
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]

中文:
定理 condExp_indicator
  条件: (hf_int : 可积 f μ) (hs : 可测集[m] s)
  证明: by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f | m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine (this.trans ?_).symm
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f | m] + μ[sᶜ.indicator f | m]) := by
      filter_upwards [condExp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)) m]
        with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f | m]) + s.indicator (μ[sᶜ.indicator f | m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f | m])) := by
      refine Filter.EventuallyEq.rfl.add ?_
      have : sᶜ.indicator (μ[sᶜ.indicator f | m]) =ᵐ[μ] μ[sᶜ.indicator f | m] := by
        refine (condExp_indicator_aux hs.compl ?_).symm.trans ?_
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x in s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_notMem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) := by
      rw [Set.indicator_indicator]; rw [Set.inter_compl_self]; rw [Set.indicator_empty']; rw [add_zero]
    _ =ᵐ[μ] μ[s.indicator f | m] := by
      refine (condExp_indicator_aux hs ?_).symm.trans ?_
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]

Depends on / 依赖: Set.indicator_zero, SigmaFinite, condExp_of_not_le, condExp_of_not_sigmaFinite, indicator_zero, simp_rw
-/
theorem condExp_indicator (hf_int : Integrable f μ) (hs : MeasurableSet[m] s) :
    μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) := by
  by_cases hm : m <= m0
  swap; · simp_rw [condExp_of_not_le hm, Set.indicator_zero']; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  have : SigmaFinite (μ.trim hm) := hμm
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f | m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine (this.trans ?_).symm
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f | m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f | m] + μ[sᶜ.indicator f | m]) := by
      filter_upwards [condExp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)) m]
        with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f | m]) + s.indicator (μ[sᶜ.indicator f | m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f | m])) := by
      refine Filter.EventuallyEq.rfl.add ?_
      have : sᶜ.indicator (μ[sᶜ.indicator f | m]) =ᵐ[μ] μ[sᶜ.indicator f | m] := by
        refine (condExp_indicator_aux hs.compl ?_).symm.trans ?_
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x in s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_notMem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f | m]) := by
      rw [Set.indicator_indicator]; rw [Set.inter_compl_self]; rw [Set.indicator_empty']; rw [add_zero]
    _ =ᵐ[μ] μ[s.indicator f | m] := by
      refine (condExp_indicator_aux hs ?_).symm.trans ?_
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]

/--
theorem `condExp_restrict_ae_eq_restrict` / 定理 `condExp_restrict_ae_eq_restrict`

English:
theorem condExp_restrict_ae_eq_restrict
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  refine EventuallyEq.trans ?_ (condExp_indicator hf_int hs_m)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hf_int.indicator (hm _ hs_m)) ?_ ?_ ?_
  · intro t ht _
    rw [← integrable_indicator_iff (hm _ ht)]; rw [Set.indicator_indicator]; rw [Set.inter_comm]; rw [←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f | m])) (μ.restrict s) by
      rw [integrable_indicator_iff (hm _ hs_m)]; rw [IntegrableOn]
      exact h_int_restrict
    exact integrable_condExp.indicator (hm _ ht)
  · intro t ht _
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f | m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f | m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := setIntegral_condExp hm hf_int.integrableOn ht
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
  · exact (stronglyMeasurable_condExp.indicator hs_m).aestronglyMeasurable

中文:
定理 condExp_restrict_ae_eq_restrict
  结论: (hm : m <= m0) [σ有限 (μ.trim hm)]
  证明: by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  refine EventuallyEq.trans ?_ (condExp_indicator hf_int hs_m)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hf_int.indicator (hm _ hs_m)) ?_ ?_ ?_
  · intro t ht _
    rw [← integrable_indicator_iff (hm _ ht)]; rw [Set.indicator_indicator]; rw [Set.inter_comm]; rw [←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f | m])) (μ.restrict s) by
      rw [integrable_indicator_iff (hm _ hs_m)]; rw [IntegrableOn]
      exact h_int_restrict
    exact integrable_condExp.indicator (hm _ ht)
  · intro t ht _
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f | m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f | m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := setIntegral_condExp hm hf_int.integrableOn ht
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
  · exact (stronglyMeasurable_condExp.indicator hs_m).aestronglyMeasurable

Depends on / 依赖: EventuallyEq, EventuallyEq.trans, Integrable, Set.indicator_indicator, Set.inter_comm, SigmaFinite, ae_eq_condExp_of_forall_setIntegral_eq, ae_eq_restrict_iff_indicator_ae_eq, condExp_indicator, h_int_restrict, hf_int, hf_int.indicator, hs_m, indicator, indicator_indicator, infer_instance, integrable_indicator_iff, inter_comm, restrict, restrict_trim
-/
theorem condExp_restrict_ae_eq_restrict (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) :
    (μ.restrict s)[f | m] =ᵐ[μ.restrict s] μ[f | m] := by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  refine EventuallyEq.trans ?_ (condExp_indicator hf_int hs_m)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hf_int.indicator (hm _ hs_m)) ?_ ?_ ?_
  · intro t ht _
    rw [← integrable_indicator_iff (hm _ ht)]; rw [Set.indicator_indicator]; rw [Set.inter_comm]; rw [←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f | m])) (μ.restrict s) by
      rw [integrable_indicator_iff (hm _ hs_m)]; rw [IntegrableOn]
      exact h_int_restrict
    exact integrable_condExp.indicator (hm _ ht)
  · intro t ht _
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f | m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f | m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := setIntegral_condExp hm hf_int.integrableOn ht
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ hs_m)]; rw [Measure.restrict_restrict (hm _ ht)]; rw [Set.inter_comm]
  · exact (stronglyMeasurable_condExp.indicator hs_m).aestronglyMeasurable

/--
theorem `condExp_ae_eq_restrict_of_measurableSpace_eq_on` / 定理 `condExp_ae_eq_restrict_of_measurableSpace_eq_on`

English:
theorem condExp_ae_eq_restrict_of_measurableSpace_eq_on
  statement: {m m₂ m0 : MeasurableSpace α}
  proof: by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  by_cases hf_int : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf_int]; rfl
  refine ((condExp_indicator hf_int hs_m).symm.trans ?_).trans (condExp_indicator hf_int hs_m₂)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condExp.integrableOn)
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  swap
  · have : StronglyMeasurable[m] (μ[s.indicator f | m]) := stronglyMeasurable_condExp
    refine this.aestronglyMeasurable.of_measurableSpace_le_on hm hs_m (fun t => (hs t).mp) ?_
    exact condExp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
  intro t ht _
  have : ∫ x in t, (μ[s.indicator f | m]) x ∂μ = ∫ x in s inter t, (μ[s.indicator f | m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condExp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f | m]) x ∂μ.restrict t = 0 by
      rw [this]; rw [add_zero]; rw [Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f | m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm]; rw [← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f | m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine setIntegral_congr_ae (hm₂ _ ht) ?_
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine condExp_ae_eq_restrict_zero hs_m.compl ?_
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s inter t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, setIntegral_condExp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    setIntegral_condExp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]

中文:
定理 condExp_ae_eq_restrict_of_measurableSpace_eq_on
  结论: {m m₂ m0 : 可测空间 α}
  证明: by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  by_cases hf_int : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf_int]; rfl
  refine ((condExp_indicator hf_int hs_m).symm.trans ?_).trans (condExp_indicator hf_int hs_m₂)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condExp.integrableOn)
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  swap
  · have : StronglyMeasurable[m] (μ[s.indicator f | m]) := stronglyMeasurable_condExp
    refine this.aestronglyMeasurable.of_measurableSpace_le_on hm hs_m (fun t => (hs t).mp) ?_
    exact condExp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
  intro t ht _
  have : ∫ x in t, (μ[s.indicator f | m]) x ∂μ = ∫ x in s inter t, (μ[s.indicator f | m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condExp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f | m]) x ∂μ.restrict t = 0 by
      rw [this]; rw [add_zero]; rw [Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f | m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm]; rw [← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f | m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine setIntegral_congr_ae (hm₂ _ ht) ?_
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine condExp_ae_eq_restrict_zero hs_m.compl ?_
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s inter t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, setIntegral_condExp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    setIntegral_condExp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]

Depends on / 依赖: Integrable, MeasurableSet, Set.inter_univ, Set.univ, ae_eq_of_forall_setIntegral_eq_of_sigmaFinite, ae_eq_restrict_iff_indicator_ae_eq, condExp_indicator, condExp_of_not_integrable, hf_int, hs_m, integrableOn, integrable_condExp, integrable_condExp.integrableOn, inter_univ, simp_rw, stronglyM, symm.trans
-/
theorem condExp_ae_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m <= m0) (hm₂ : m₂ <= m0) [SigmaFinite (μ.trim hm)]
    [SigmaFinite (μ.trim hm₂)] (hs_m : MeasurableSet[m] s)
    (hs : forall t, MeasurableSet[m] (s inter t) ↔ MeasurableSet[m₂] (s inter t)) :
    μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂] := by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  by_cases hf_int : Integrable f μ
  swap; · simp_rw [condExp_of_not_integrable hf_int]; rfl
  refine ((condExp_indicator hf_int hs_m).symm.trans ?_).trans (condExp_indicator hf_int hs_m₂)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condExp.integrableOn)
    (fun s _ _ => integrable_condExp.integrableOn) ?_ ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  swap
  · have : StronglyMeasurable[m] (μ[s.indicator f | m]) := stronglyMeasurable_condExp
    refine this.aestronglyMeasurable.of_measurableSpace_le_on hm hs_m (fun t => (hs t).mp) ?_
    exact condExp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
  intro t ht _
  have : ∫ x in t, (μ[s.indicator f | m]) x ∂μ = ∫ x in s inter t, (μ[s.indicator f | m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condExp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f | m]) x ∂μ.restrict t = 0 by
      rw [this]; rw [add_zero]; rw [Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f | m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm]; rw [← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f | m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine setIntegral_congr_ae (hm₂ _ ht) ?_
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine condExp_ae_eq_restrict_zero hs_m.compl ?_
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s inter t) := (hs _).mpr (hs_m₂.inter ht)
  simp_rw [this, setIntegral_condExp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    setIntegral_condExp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]

end MeasureTheory
