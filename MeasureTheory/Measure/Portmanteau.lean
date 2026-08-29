/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Characterizations of weak convergence of finite measures and probability measures

This file will provide portmanteau characterizations of the weak convergence of finite measures
and of probability measures, i.e., the standard characterizations of convergence in distribution.

## Main definitions

The topologies of weak convergence on the types of finite measures and probability measures are
already defined in their corresponding files; no substantial new definitions are introduced here.

## Main results

The main result will be the portmanteau theorem providing various characterizations of the
weak convergence of measures (probability measures or finite measures). Given measures μs
and μ on a topological space Ω, the conditions that will be proven equivalent (under quite
general hypotheses) are:

  (T) The measures μs tend to the measure μ weakly.
  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).

The separate implications are:
* `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto` is the implication (T) → (C).
* `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge` is the equivalence (C) ↔ (O).
* `MeasureTheory.tendsto_measure_of_null_frontier` is the implication (O) → (B).
* `MeasureTheory.limsup_measure_closed_le_of_forall_tendsto_measure` is the implication (B) → (C).
* `MeasureTheory.tendsto_of_forall_isOpen_le_liminf` gives the implication (O) → (T) for
    any sequence of Borel probability measures.
* `MeasureTheory.tendsto_of_limsup_measure_closed_le` gives the implication (C) → (T).

We also deduce a practical convergence criterion for probability measures, in
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`.
Assume that, applied to all the elements of a π-system, a sequence of probability measures
converges to a limiting probability measure. Assume also that the π-system contains arbitrarily
small neighborhoods of any point. Then the sequence of probability measures converges for the
weak topology.

In case the set of measures is tight, (C) implies (T) even when 'closed' is replaced by 'compact'.
This is shown in `MeasureTheory.tendsto_of_forall_isCompact_of_isTightMeasureSet`.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
more general assumptions than in the usual statement of portmanteau theorem. The full portmanteau
theorem, however, is most convenient for probability measures on pseudo-emetrizable spaces with
their Borel sigma algebras.

Some specific considerations on the assumptions in the different implications:
* `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`, i.e., implication (T) → (C),
  assumes that in the underlying topological space, indicator functions of closed sets have
  decreasing bounded continuous pointwise approximating sequences. The assumption is in the form
  of the type class `HasOuterApproxClosed`. Type class inference knows that for example the more
  common assumptions of metrizability or pseudo-emetrizability suffice.
* Where formulations are currently only provided for probability measures, one can obtain the
  finite measure formulations using the characterization of convergence of finite measures by
  their total masses and their probability-normalized versions, i.e., by
  `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, convergence in distribution, convergence in law, finite measure,
probability measure

-/

public section


noncomputable section

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section LimsupClosedLEAndLELiminfOpen

/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/--
theorem `le_measure_compl_liminf_of_limsup_measure_le` / 定理 `le_measure_compl_liminf_of_limsup_measure_le`

English:
theorem le_measure_compl_liminf_of_limsup_measure_le
  statement: {ι : Type*} {L : Filter ι} {μ : Measure Ω}
  proof: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

中文:
定理 le_measure_compl_liminf_of_limsup_measure_le
  结论: {ι : 类型} {L : 滤子 ι} {μ : 测度 Ω}
  证明: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

Depends on / 依赖: E_mble, L.eq_or_neBot, L.liminf, antitone_const_tsub, antitone_const_tsub.map_, eq_or_neBot, le_top, liminf, liminf_bot, map_, meas_Ec, meas_i_Ec, measure_compl, measure_lt_top, measure_univ, simp_rw
-/
theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i E) <= μ E) :
    μ Eᶜ <= L.liminf fun i => μs i Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [liminf_bot, le_top]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

/--
theorem `le_measure_liminf_of_limsup_measure_compl_le` / 定理 `le_measure_liminf_of_limsup_measure_compl_le`

English:
theorem le_measure_liminf_of_limsup_measure_compl_le
  statement: {ι : Type*} {L : Filter ι} {μ : Measure Ω}
  proof: compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h

中文:
定理 le_measure_liminf_of_limsup_measure_compl_le
  结论: {ι : 类型} {L : 滤子 ι} {μ : 测度 Ω}
  证明: compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h

Depends on / 依赖: E_mble, MeasurableSet, MeasurableSet.compl, compl_compl, le_measure_compl_liminf_of_limsup_measure_le
-/
theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i Eᶜ) <= μ Eᶜ) :
    μ E <= L.liminf fun i => μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h

/--
theorem `limsup_measure_compl_le_of_le_liminf_measure` / 定理 `limsup_measure_compl_le_of_le_liminf_measure`

English:
theorem limsup_measure_compl_le_of_le_liminf_measure
  statement: {ι : Type*} {L : Filter ι} {μ : Measure Ω}
  proof: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

中文:
定理 limsup_measure_compl_le_of_le_liminf_measure
  结论: {ι : 类型} {L : 滤子 ι} {μ : 测度 Ω}
  证明: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

Depends on / 依赖: E_mble, L.eq_or_neBot, L.limsup, antitone_const_tsub, antitone_const_tsub.map_, bot_le, eq_or_neBot, limsup, limsup_bot, map_, meas_Ec, meas_i_Ec, measure_compl, measure_lt_top, measure_univ, simp_rw
-/
theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E <= L.liminf fun i => μs i E) :
    (L.limsup fun i => μs i Eᶜ) <= μ Eᶜ := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  have meas_Ec : μ Eᶜ = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne
  have meas_i_Ec : forall i, μs i Eᶜ = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne
  simp_rw [meas_Ec, meas_i_Ec]
  rw [show (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E)
      from rfl]
  have key := antitone_const_tsub.map_liminf_of_continuousAt (F := L)
    (fun i => μs i E) (ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt
  simpa [← key] using antitone_const_tsub h

/--
theorem `limsup_measure_le_of_le_liminf_measure_compl` / 定理 `limsup_measure_le_of_le_liminf_measure_compl`

English:
theorem limsup_measure_le_of_le_liminf_measure_compl
  statement: {ι : Type*} {L : Filter ι} {μ : Measure Ω}
  proof: compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h

中文:
定理 limsup_measure_le_of_le_liminf_measure_compl
  结论: {ι : 类型} {L : 滤子 ι} {μ : 测度 Ω}
  证明: compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h

Depends on / 依赖: E_mble, MeasurableSet, MeasurableSet.compl, compl_compl, limsup_measure_compl_le_of_le_liminf_measure
-/
theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ Eᶜ <= L.liminf fun i => μs i Eᶜ) :
    (L.limsup fun i => μs i E) <= μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `limsup_measure_closed_le_iff_liminf_measure_open_ge` / 定理 `limsup_measure_closed_le_iff_liminf_measure_open_ge`

English:
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))

中文:
定理 limsup_measure_closed_le_iff_liminf_measure_open_ge
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))

Depends on / 依赖: F_closed, F_closed.measurableSet, G_open, G_open.measurableSet, isClosed_compl_iff, isClosed_compl_iff.mpr, isOpen_compl_iff, isOpen_compl_iff.mpr, le_measure_liminf_of_limsup_measure_compl_le, limsup_measure_le_of_le_liminf_measure_compl, measurableSet
-/
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι -> Measure Ω} [IsProbabilityMeasure μ]
    [forall i, IsProbabilityMeasure (μs i)] :
    (forall F, IsClosed F -> (L.limsup fun i => μs i F) <= μ F) ↔
      forall G, IsOpen G -> μ G <= L.liminf fun i => μs i G := by
  constructor
  · intro h G G_open
    exact le_measure_liminf_of_limsup_measure_compl_le
      G_open.measurableSet (h Gᶜ (isClosed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact limsup_measure_le_of_le_liminf_measure_compl
      F_closed.measurableSet (h Fᶜ (isOpen_compl_iff.mpr F_closed))

end LimsupClosedLEAndLELiminfOpen -- section

section TendstoOfNullFrontier

/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F);
  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

implies that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
-/


variable {Ω : Type*} [MeasurableSpace Ω]

/--
theorem `tendsto_measure_of_le_liminf_measure_of_limsup_measure_le` / 定理 `tendsto_measure_of_le_liminf_measure_of_limsup_measure_le`

English:
theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ <= L.liminf fun i => μs i E₀ := h_E₀
      _ <= L.liminf fun i => μs i E :=
        liminf_le_liminf (.of_forall fun _ => measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i => μs i E) <= L.limsup fun i => μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ => measure_mono subset_E₁)
      _ <= μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param

中文:
定理 tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ <= L.liminf fun i => μs i E₀ := h_E₀
      _ <= L.liminf fun i => μs i E :=
        liminf_le_liminf (.of_forall fun _ => measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i => μs i E) <= L.limsup fun i => μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ => measure_mono subset_E₁)
      _ <= μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param

Depends on / 依赖: EventuallyLE, EventuallyLE.antisymm, L.liminf, _ae_eq_E.symm, _subset.eventuallyLE, ae_le_set, ae_le_set.mpr, antisymm, eventuallyLE, eventuallyLE.trans, liminf, liminf_le_liminf, measure_congr, measure_mono, nulldiff, of_forall, tendsto_of_le_liminf_of_limsup_le
-/
theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type*} {L : Filter ι}
    {μ : Measure Ω} {μs : ι -> Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : E₀ subseteq E) (subset_E₁ : E subseteq E₁)
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ <= L.liminf fun i => μs i E₀)
    (h_E₁ : (L.limsup fun i => μs i E₁) <= μ E₁) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      EventuallyLE.antisymm E₀_subset.eventuallyLE
        (subset_E₁.eventuallyLE.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ <= L.liminf fun i => μs i E₀ := h_E₀
      _ <= L.liminf fun i => μs i E :=
        liminf_le_liminf (.of_forall fun _ => measure_mono E₀_subset)
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      EventuallyLE.antisymm subset_E₁.eventuallyLE
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventuallyLE)
    calc
      (L.limsup fun i => μs i E) <= L.limsup fun i => μs i E₁ :=
        limsup_le_limsup (.of_forall fun _ => measure_mono subset_E₁)
      _ <= μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
  · infer_param
  · infer_param

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `tendsto_measure_of_null_frontier` / 定理 `tendsto_measure_of_null_frontier`

English:
theorem tendsto_measure_of_null_frontier
  statement: {ι : Type*} {L : Filter ι} {μ : Measure Ω}
  proof: haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => μs i F) <= μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)

中文:
定理 tendsto_measure_of_null_frontier
  结论: {ι : 类型} {L : 滤子 ι} {μ : 测度 Ω}
  证明: haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => μs i F) <= μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.toBoundedOrder, BoundedOrder, E_nullbdry, IsClosed, L.limsup, h_closeds, h_opens, interior_subset, isClosed_closure, isOpen_interior, limsup, limsup_measure_closed_le_iff_liminf_measure_open_ge, limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr, subset_closure, tendsto_measure_of_le_liminf_measure_of_limsup_measure_le, toBoundedOrder
-/
theorem tendsto_measure_of_null_frontier {ι : Type*} {L : Filter ι} {μ : Measure Ω}
    {μs : ι -> Measure Ω} [IsProbabilityMeasure μ] [forall i, IsProbabilityMeasure (μs i)]
    (h_opens : forall G, IsOpen G -> μ G <= L.liminf fun i => μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => μs i F) <= μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ isOpen_interior) (h_closeds _ isClosed_closure)

end TendstoOfNullFrontier --section

section ConvergenceImpliesLimsupClosedLE

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (T) The measures μs tend to the measure μ weakly

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with earlier proven implications, we get that (T) implies also both

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G);
  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B).
-/


/--
theorem `FiniteMeasure.limsup_measure_closed_le_of_tendsto` / 定理 `FiniteMeasure.limsup_measure_closed_le_of_tendsto`

English:
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto
  statement: {Ω ι : Type*} {L : Filter ι}
  proof: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n => ∫⁻ ω, (fs n ω : Real>=0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => fs M a) <
      (lintegral (μ : Measure Ω) fun a => fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n => le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : Real>=0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]

中文:
定理 有限测度.limsup_measure_closed_le_of_tendsto
  结论: {Ω ι : 类型} {L : 滤子 ι}
  证明: by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n => ∫⁻ ω, (fs n ω : Real>=0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => fs M a) <
      (lintegral (μ : Measure Ω) fun a => fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n => le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : Real>=0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero.mpr, ENNReal.half_pos, ENNReal.le_of_forall_pos_le_add, ENNReal.lt_add_right, F_closed, F_closed.apprSeq, HasOuterApproxClosed, HasOuterApproxClosed.tendsto_lintegral_apprSeq, L.eq_or_neBot, Measure, Tendsto, _pos.ne.symm, apprSeq, bot_le, coe_ne_zero, eq_or_neBot, half_pos, le_of_forall_pos_le_add, limsup_bot
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι -> FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure Ω) F) <= (μ : Measure Ω) F := by
  rcases L.eq_or_neBot with rfl | hne
  · simp only [limsup_bot, bot_le]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos _
  have ε_pos' := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr ε_pos.ne.symm)).ne.symm
  let fs := F_closed.apprSeq
  have key₁ : Tendsto (fun n => ∫⁻ ω, (fs n ω : Real>=0∞) ∂μ) atTop (𝓝 ((μ : Measure Ω) F)) :=
    HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed (μ : Measure Ω)
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 :=
    ENNReal.lt_add_right (measure_lt_top (μ : Measure Ω) F).ne ε_pos'
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (fs M)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => fs M a) <
      (lintegral (μ : Measure Ω) fun a => fs M a) + ε / 2 :=
    ENNReal.lt_add_right (ne_of_lt ((fs M).lintegral_lt_top_of_nnreal _)) ε_pos'
  have ev_near := key₂.eventually_le_const room₂
  have ev_near' := ev_near.mono
    (fun n => le_trans (HasOuterApproxClosed.measure_le_lintegral F_closed (μs n) M))
  apply (Filter.limsup_le_limsup ev_near').trans
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : Real>=0∞)))
  simp only [add_assoc, ENNReal.add_halves, le_refl]

/--
theorem `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` / 定理 `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`

English:
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
  statement: {Ω ι : Type*} {L : Filter ι}
  proof: by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

中文:
定理 概率测度.limsup_measure_closed_le_of_tendsto
  结论: {Ω ι : 类型} {L : 滤子 ι}
  证明: by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

Depends on / 依赖: F_closed, FiniteMeasure, FiniteMeasure.limsup_measure_closed_le_of_tendsto, limsup_measure_closed_le_of_tendsto, tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
-/
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure Ω) F) <= (μ : Measure Ω) F := by
  apply FiniteMeasure.limsup_measure_closed_le_of_tendsto
    ((tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds L).mp μs_lim) F_closed

/--
theorem `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` / 定理 `ProbabilityMeasure.le_liminf_measure_open_of_tendsto`

English:
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto
  statement: {Ω ι : Type*} {L : Filter ι}
  proof: haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => (μs i : Measure Ω) F) <= (μ : Measure Ω) F :=
    fun _ F_closed => limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))

中文:
定理 概率测度.le_liminf_measure_open_of_tendsto
  结论: {Ω ι : 类型} {L : 滤子 ι}
  证明: haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => (μs i : Measure Ω) F) <= (μ : Measure Ω) F :=
    fun _ F_closed => limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))

Depends on / 依赖: F_closed, G_open, G_open.measurableSet, IsClosed, L.limsup, Measure, h_closeds, isClosed_compl_iff, isClosed_compl_iff.mpr, le_measure_liminf_of_limsup_measure_compl_le, limsup, limsup_measure_closed_le_of_tendsto, measurableSet
-/
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G <= L.liminf fun i => (μs i : Measure Ω) G :=
  haveI h_closeds : forall F, IsClosed F -> (L.limsup fun i => (μs i : Measure Ω) F) <= (μ : Measure Ω) F :=
    fun _ F_closed => limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
    (h_closeds _ (isClosed_compl_iff.mpr G_open))

/--
theorem `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` / 定理 `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`

English:
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
  statement: {Ω ι : Type*}
  proof: haveI h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf fun i => (μs i : Measure Ω) G :=
    fun _ G_open => le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry

中文:
定理 概率测度.tendsto_measure_of_null_frontier_of_tendsto'
  结论: {Ω ι : 类型}
  证明: haveI h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf fun i => (μs i : Measure Ω) G :=
    fun _ G_open => le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry

Depends on / 依赖: E_nullbdry, G_open, IsOpen, L.liminf, Measure, h_opens, le_liminf_measure_open_of_tendsto, liminf, tendsto_measure_of_null_frontier
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf fun i => (μs i : Measure Ω) G :=
    fun _ G_open => le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry

/--
theorem `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` / 定理 `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`

English:
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
  statement: {Ω ι : Type*} {L : Filter ι}
  proof: by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key

中文:
定理 概率测度.tendsto_measure_of_null_frontier_of_tendsto
  结论: {Ω ι : 类型} {L : 滤子 ι}
  证明: by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key

Depends on / 依赖: ENNReal, ENNReal.tendsto_toNNReal, E_nullbdry, measure_ne_top, tendsto_measure_of_null_frontier_of_tendsto, tendsto_toNNReal
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i => μs i E) L (𝓝 (μ E)) := by
  have key := tendsto_measure_of_null_frontier_of_tendsto' μs_lim (by simpa using E_nullbdry)
  exact (ENNReal.tendsto_toNNReal (measure_ne_top (↑μ) E)).comp key

/--
theorem `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto` / 定理 `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`

English:
theorem ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
  statement: {Ω ι : Type*} {L : Filter ι}
  proof: ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto μs_lim (by simp [hE])

中文:
定理 概率测度.tendsto_measure_of_isClopen_of_tendsto
  结论: {Ω ι : 类型} {L : 滤子 ι}
  证明: ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto μs_lim (by simp [hE])

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto, tendsto_measure_of_null_frontier_of_tendsto
-/
theorem ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (hE : IsClopen E) : Tendsto (fun i => μs i E) L (𝓝 (μ E)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto μs_lim (by simp [hE])

end ConvergenceImpliesLimsupClosedLE --section

section LimitBorelImpliesLimsupClosedLE

/-! ### Portmanteau implication: limit condition for Borel sets implies limsup for closed sets


In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that

  (B) For any Borel set B whose boundary carries no mass under μ, i.e. μ(∂B) = 0,
      the measures of B under μs tend to the measure of B under μ, i.e., limᵢ μsᵢ(B) = μ(B)

implies

  (C) For any closed set F, the limsup of the measures of F under μs is at most
      the measure of F under μ, i.e., limsupᵢ μsᵢ(F) ≤ μ(F).

Combining with earlier proven implications, we get that (B) implies also

  (O) For any open set G, the liminf of the measures of G under μs is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfᵢ μsᵢ(G).

-/

open ENNReal

section PseudoMetricSpace

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `exists_null_frontier_thickening` / 定理 `exists_null_frontier_thickening`

English:
theorem exists_null_frontier_thickening
  statement: (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : Real}
  proof: by
  have mbles : forall r : Real, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_sdiff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo]; rw [← aux] at len_pos
  simpa [Set.Nonempty] using nonempty_of_measure_ne_zero len_pos.ne'

中文:
定理 存在_null_frontier_thickening
  结论: (μ : 测度 Ω) [SFinite μ] (s : 集合 Ω) {a b : 实数}
  证明: by
  have mbles : forall r : Real, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_sdiff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo]; rw [← aux] at len_pos
  simpa [Set.Nonempty] using nonempty_of_measure_ne_zero len_pos.ne'

Depends on / 依赖: Countable, ENNReal, ENNReal.ofReal, ENNReal.ofReal_pos, MeasurableSet, Measure, Measure.countable_meas_pos_of_disjoint_iUnion, Metric, Metric.frontier_thickening_disjoint, Metric.thickening, Nonempt, Real.volume_Ioo, Set.Countable.measure_zero, Set.Nonempt, countable_meas_pos_of_disjoint_iUnion, frontier, frontier_thickening_disjoint, isClosed_frontier, isClosed_frontier.measurableSet, len_pos
-/
theorem exists_null_frontier_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) {a b : Real}
    (hab : a < b) : exists r in Ioo a b, μ (frontier (Metric.thickening r s)) = 0 := by
  have mbles : forall r : Real, MeasurableSet (frontier (Metric.thickening r s)) :=
    fun r => isClosed_frontier.measurableSet
  have disjs := Metric.frontier_thickening_disjoint s
  have key := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) mbles disjs
  have aux := measure_sdiff_null (s := Ioo a b) (Set.Countable.measure_zero key volume)
  have len_pos : 0 < ENNReal.ofReal (b - a) := by simp only [hab, ENNReal.ofReal_pos, sub_pos]
  rw [← Real.volume_Ioo]; rw [← aux] at len_pos
  simpa [Set.Nonempty] using nonempty_of_measure_ne_zero len_pos.ne'

/--
theorem `exists_null_frontiers_thickening` / 定理 `exists_null_frontiers_thickening`

English:
theorem exists_null_frontiers_thickening
  given: (μ : Measure Ω) [SFinite μ] (s : Set Ω)
  proof: by
  rcases exists_seq_strictAnti_tendsto (0 : Real) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : Nat => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : Nat => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n => (obs n).choose_spec.1.1.le) fun n => (obs n).choose_spec.1.2.le
  · exact fun n => ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩

中文:
定理 存在_null_frontiers_thickening
  条件: (μ : 测度 Ω) [SFinite μ] (s : 集合 Ω)
  证明: by
  rcases exists_seq_strictAnti_tendsto (0 : Real) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : Nat => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : Nat => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n => (obs n).choose_spec.1.1.le) fun n => (obs n).choose_spec.1.2.le
  · exact fun n => ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩

Depends on / 依赖: Rs_lim, Rs_pos, choose_spec, exists_null_frontier_thickening, exists_seq_strictAnti_tendsto, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
theorem exists_null_frontiers_thickening (μ : Measure Ω) [SFinite μ] (s : Set Ω) :
    exists rs : Nat -> Real,
      Tendsto rs atTop (𝓝 0) ∧ forall n, 0 < rs n ∧ μ (frontier (Metric.thickening (rs n) s)) = 0 := by
  rcases exists_seq_strictAnti_tendsto (0 : Real) with ⟨Rs, ⟨_, ⟨Rs_pos, Rs_lim⟩⟩⟩
  have obs := fun n : Nat => exists_null_frontier_thickening μ s (Rs_pos n)
  refine ⟨fun n : Nat => (obs n).choose, ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds Rs_lim
      (fun n => (obs n).choose_spec.1.1.le) fun n => (obs n).choose_spec.1.2.le
  · exact fun n => ⟨(obs n).choose_spec.1.1, (obs n).choose_spec.2⟩

end PseudoMetricSpace

open TopologicalSpace

/--
lemma `limsup_measure_closed_le_of_forall_tendsto_measure` / 引理 `limsup_measure_closed_le_of_forall_tendsto_measure`

English:
lemma limsup_measure_closed_le_of_forall_tendsto_measure
  proof: by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : forall n, 0 < rs n := fun n => ((Classical.choose_spec ex).2 n).1
  have rs_null : forall n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n => ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : forall n, IsOpen (Metric.thickening (rs n) F) :=
    fun n => Metric.isOpen_thickening
  have key := fun (n : Nat) => h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhds : Iio (μ F + ε) in 𝓝 (μ F) :=
Iio_mem_nhds ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhds)
  simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i => (μs i F)) <=ᶠ[L] (fun i => μs i (Metric.thickening (rs m) F)) :=
.of_forall fun i => measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

中文:
引理 limsup_measure_closed_le_of_对任意_tendsto_measure
  证明: by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : forall n, 0 < rs n := fun n => ((Classical.choose_spec ex).2 n).1
  have rs_null : forall n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n => ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : forall n, IsOpen (Metric.thickening (rs n) F) :=
    fun n => Metric.isOpen_thickening
  have key := fun (n : Nat) => h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhds : Iio (μ F + ε) in 𝓝 (μ F) :=
Iio_mem_nhds ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhds)
  simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i => (μs i F)) <=ᶠ[L] (fun i => μs i (Metric.thickening (rs m) F)) :=
.of_forall fun i => measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, L.eq_or_neBot, Metric, Metric.thickening, PseudoMetricSpace, Tendsto, TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, bot_eq_zero, choose_spec, eq_or_neBot, exists_null_frontiers_thickening, frontier, limsup_bot, pseudoMetrizableSpacePseudoMetric, rs_lim, rs_null, rs_pos
-/
lemma limsup_measure_closed_le_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ι -> Measure Ω}
    (h : forall {E : Set Ω}, MeasurableSet E -> μ (frontier E) = 0 ->
            Tendsto (fun i => μs i E) L (𝓝 (μ E)))
    (F : Set Ω) (F_closed : IsClosed F) :
    L.limsup (fun i => μs i F) <= μ F := by
  let : PseudoMetricSpace Ω := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Ω
  rcases L.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le]
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : forall n, 0 < rs n := fun n => ((Classical.choose_spec ex).2 n).1
  have rs_null : forall n, μ (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n => ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : forall n, IsOpen (Metric.thickening (rs n) F) :=
    fun n => Metric.isOpen_thickening
  have key := fun (n : Nat) => h (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε ε_pos μF_finite
  have keyB := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := F)
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhds : Iio (μ F + ε) in 𝓝 (μ F) :=
Iio_mem_nhds ENNReal.lt_add_right μF_finite.ne (ENNReal.coe_pos.mpr ε_pos).ne'
  specialize rs_lim (keyB nhds)
  simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux : (fun i => (μs i F)) <=ᶠ[L] (fun i => μs i (Metric.thickening (rs m) F)) :=
.of_forall fun i => measure_mono (Metric.self_subset_thickening (rs_pos m) F)
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

/--
lemma `le_liminf_measure_open_of_forall_tendsto_measure` / 引理 `le_liminf_measure_open_of_forall_tendsto_measure`

English:
lemma le_liminf_measure_open_of_forall_tendsto_measure
  proof: by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)

中文:
引理 le_liminf_measure_open_of_对任意_tendsto_measure
  证明: by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)

Depends on / 依赖: G_open, G_open.measurableSet, isClosed_compl_iff, isClosed_compl_iff.mpr, le_measure_liminf_of_limsup_measure_compl_le, limsup_measure_closed_le_of_forall_tendsto_measure, measurableSet
-/
lemma le_liminf_measure_open_of_forall_tendsto_measure
    {Ω ι : Type*} {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι -> Measure Ω} [forall i, IsProbabilityMeasure (μs i)]
    (h : forall {E}, MeasurableSet E -> μ (frontier E) = 0 -> Tendsto (fun i => μs i E) L (𝓝 (μ E)))
    (G : Set Ω) (G_open : IsOpen G) :
    μ G <= L.liminf (fun i => μs i G) := by
  apply le_measure_liminf_of_limsup_measure_compl_le G_open.measurableSet
  exact limsup_measure_closed_le_of_forall_tendsto_measure h _ (isClosed_compl_iff.mpr G_open)

end LimitBorelImpliesLimsupClosedLE --section

section le_liminf_open_implies_convergence

/-! ### Portmanteau implication: liminf condition for open sets implies weak convergence


In this section we prove for a sequence (μsₙ)ₙ Borel probability measures that

  (O) For any open set G, the liminf of the measures of G under μsₙ is at least
      the measure of G under μ, i.e., μ(G) ≤ liminfₙ μsₙ(G).

implies

  (T) The measures μsₙ converge weakly to the measure μ.

-/

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/--
lemma `lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure` / 引理 `lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`

English:
lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
  proof: by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc ∫⁻ (t : Real) in Set.Ioi 0, μ {a | t < f a}
      <= ∫⁻ (t : Real) in Set.Ioi 0, atTop.liminf (fun i => (μs i) {a | t < f a}) := ?_ -- (i)
    _ <= atTop.liminf (fun i => ∫⁻ (t : Real) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t => h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
            measure_mono (fun ω hω => lt_of_le_of_lt hst hω)))

中文:
引理 lintegral_le_liminf_lintegral_of_对任意_isOpen_measure_le_liminf_measure
  证明: by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc ∫⁻ (t : Real) in Set.Ioi 0, μ {a | t < f a}
      <= ∫⁻ (t : Real) in Set.Ioi 0, atTop.liminf (fun i => (μs i) {a | t < f a}) := ?_ -- (i)
    _ <= atTop.liminf (fun i => ∫⁻ (t : Real) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t => h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
            measure_mono (fun ω hω => lt_of_le_of_lt hst hω)))

Depends on / 依赖: Antitone, Antitone.measurable, Eventually, Eventually.of_forall, Set.Ioi, aemeasurable, atTop.liminf, continuous_def, continuous_def.mp, f_cont, f_cont.aemeasurable, f_nn, h_opens, isOpen_Ioi, le_refl, liminf, lintegral_eq_lintegral_meas_lt, lintegral_liminf_le, lintegral_mono, measurable
-/
lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : Nat -> Measure Ω} {f : Ω -> Real} (f_cont : Continuous f) (f_nn : 0 <= f)
    (h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ <= atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_cont.aemeasurable]
  calc ∫⁻ (t : Real) in Set.Ioi 0, μ {a | t < f a}
      <= ∫⁻ (t : Real) in Set.Ioi 0, atTop.liminf (fun i => (μs i) {a | t < f a}) := ?_ -- (i)
    _ <= atTop.liminf (fun i => ∫⁻ (t : Real) in Set.Ioi 0, (μs i) {a | t < f a}) := ?_ -- (ii)
  · -- (i)
    exact (lintegral_mono (fun t => h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans
            (le_refl _)
  · -- (ii)
    exact lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
            measure_mono (fun ω hω => lt_of_le_of_lt hst hω)))

/--
lemma `integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure` / 引理 `integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure`

English:
lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
  proof: by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert! ENNReal.toReal_mono ?_ same
  · simp only [fun i => @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : forall i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) <= nndist 0 g := fun i => by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using!
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : Nat) => @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) Real _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : Real>=0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp)⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert! obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

中文:
引理 integral_le_liminf_integral_of_对任意_isOpen_measure_le_liminf_measure
  证明: by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert! ENNReal.toReal_mono ?_ same
  · simp only [fun i => @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : forall i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) <= nndist 0 g := fun i => by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using!
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : Nat) => @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) Real _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : Real>=0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp)⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert! obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.comp, ENNReal, ENNReal.toReal_mono, Eventually, Eventually.of_forall, Real.lipschitzWith_toNNReal, aestronglyMeasurable, continuous, convert, f.continuous, f.continuous.measurable.aestronglyMeasurable, f_nn, h_opens, integral_eq_lintegral_of_nonneg_ae, lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure, lipschitzWith_toNNReal, measurable, of_forall, toReal_mono
-/
lemma integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
    {μ : Measure Ω} {μs : Nat -> Measure Ω} [forall i, IsProbabilityMeasure (μs i)]
    {f : Ω ->ᵇ Real} (f_nn : 0 <= f)
    (h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i => μs i G)) :
    ∫ x, (f x) ∂μ <= atTop.liminf (fun i => ∫ x, (f x) ∂(μs i)) := by
  have same := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
                  f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (Eventually.of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert! ENNReal.toReal_mono ?_ same
  · simp only [fun i => @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (Eventually.of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    let g := BoundedContinuousFunction.comp _ Real.lipschitzWith_toNNReal f
    have bound : forall i, ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i) <= nndist 0 g := fun i => by
      simpa only [coe_nnreal_ennreal_nndist, measure_univ, mul_one, ge_iff_le] using!
            BoundedContinuousFunction.lintegral_le_edist_mul (μ := μs i) g
    apply ENNReal.liminf_toReal_eq ENNReal.coe_ne_top (Eventually.of_forall bound)
  · apply ne_of_lt
    have obs := fun (i : Nat) => @BoundedContinuousFunction.lintegral_nnnorm_le Ω _ _ (μs i) Real _ f
    simp only [measure_univ, mul_one] at obs
    apply lt_of_le_of_lt _ (show (‖f‖₊ : Real>=0∞) < ∞ from ENNReal.coe_lt_top)
    apply liminf_le_of_le
    · refine ⟨0, .of_forall (by simp)⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hx.exists
      apply le_trans hi
      convert! obs i with x
      have aux := ENNReal.ofReal_eq_coe_nnreal (f_nn x)
      simp only [ContinuousMap.toFun_eq_coe, BoundedContinuousFunction.coe_toContinuousMap] at aux
      rw [aux]
      congr
      exact (Real.norm_of_nonneg (f_nn x)).symm

/--
theorem `tendsto_of_forall_isOpen_le_liminf_nat'` / 定理 `tendsto_of_forall_isOpen_le_liminf_nat'`

English:
theorem tendsto_of_forall_isOpen_le_liminf_nat'
  statement: {μ : ProbabilityMeasure Ω}
  proof: by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  refine tendsto_integral_of_forall_integral_le_liminf_integral fun f f_nn => ?_
  exact integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure f_nn h_opens

中文:
定理 tendsto_of_对任意_isOpen_le_liminf_nat'
  结论: {μ : 概率测度 Ω}
  证明: by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  refine tendsto_integral_of_forall_integral_le_liminf_integral fun f f_nn => ?_
  exact integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure f_nn h_opens

Depends on / 依赖: ProbabilityMeasure, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr, f_nn, h_opens, integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure, tendsto_iff_forall_integral_tendsto, tendsto_integral_of_forall_integral_le_liminf_integral
-/
theorem tendsto_of_forall_isOpen_le_liminf_nat' {μ : ProbabilityMeasure Ω}
    {μs : Nat -> ProbabilityMeasure Ω}
    (h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= liminf (fun i => (μs i : Measure Ω) G) atTop) :
    atTop.Tendsto (fun i => μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  refine tendsto_integral_of_forall_integral_le_liminf_integral fun f f_nn => ?_
  exact integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure f_nn h_opens

/--
theorem `tendsto_of_forall_isOpen_le_liminf_nat` / 定理 `tendsto_of_forall_isOpen_le_liminf_nat`

English:
theorem tendsto_of_forall_isOpen_le_liminf_nat
  statement: {μ : ProbabilityMeasure Ω}
  proof: by
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G G_open => ?_
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i => μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i => μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp only [Function.comp_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

中文:
定理 tendsto_of_对任意_isOpen_le_liminf_nat
  结论: {μ : 概率测度 Ω}
  证明: by
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G G_open => ?_
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i => μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i => μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp only [Function.comp_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

Depends on / 依赖: ENNReal, ENNReal.coe_mono, ENNReal.continuous_coe.continuousAt, ENNReal.ofNNReal, G_open, IsBoundedUnder, IsBoundedUnder.isCoboundedUnder_ge, Monotone, Monotone.map_liminf_of_continuousAt, ProbabilityMeasure, ProbabilityMeasure.ennre, coe_mono, continuousAt, continuous_coe, h_opens, isCoboundedUnder_ge, liminf, map_liminf_of_continuousAt, ofNNReal, specialize
-/
theorem tendsto_of_forall_isOpen_le_liminf_nat {μ : ProbabilityMeasure Ω}
    {μs : Nat -> ProbabilityMeasure Ω}
    (h_opens : forall G, IsOpen G -> μ G <= atTop.liminf (fun i => μs i G)) :
    atTop.Tendsto (fun i => μs i) (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G G_open => ?_
  specialize h_opens G G_open
  have aux : ENNReal.ofNNReal (liminf (fun i => μs i G) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun i => μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · exact IsBoundedUnder.isCoboundedUnder_ge ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h_opens
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp only [Function.comp_apply, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

/--
theorem `tendsto_of_forall_isOpen_le_liminf'` / 定理 `tendsto_of_forall_isOpen_le_liminf'`

English:
theorem tendsto_of_forall_isOpen_le_liminf'
  statement: {ι : Type*} {μ : ProbabilityMeasure Ω}
  proof: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat' fun G hG => ?_
  exact (h_opens G hG).trans (liminf_le_liminf_of_le hu)

中文:
定理 tendsto_of_对任意_isOpen_le_liminf'
  结论: {ι : 类型} {μ : 概率测度 Ω}
  证明: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat' fun G hG => ?_
  exact (h_opens G hG).trans (liminf_le_liminf_of_le hu)

Depends on / 依赖: Filter, Filter.tendsto_of_seq_tendsto, h_opens, liminf_le_liminf_of_le, tendsto_of_forall_isOpen_le_liminf_nat, tendsto_of_seq_tendsto
-/
theorem tendsto_of_forall_isOpen_le_liminf' {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι -> ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : forall G, IsOpen G -> (μ : Measure Ω) G <= L.liminf (fun i => (μs i : Measure Ω) G)) :
    L.Tendsto (fun i => μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat' fun G hG => ?_
  exact (h_opens G hG).trans (liminf_le_liminf_of_le hu)

/--
theorem `tendsto_of_forall_isOpen_le_liminf` / 定理 `tendsto_of_forall_isOpen_le_liminf`

English:
theorem tendsto_of_forall_isOpen_le_liminf
  statement: {ι : Type*} {μ : ProbabilityMeasure Ω}
  proof: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat fun G hG => (h_opens G hG).trans ?_
  change _ <= atTop.liminf ((fun i => μs i G) ∘ u)
  rw [liminf_comp]
  refine liminf_le_liminf_of_le hu (by isBoundedDefault) ?_
.isCoboundedUnder_ge exact isBoundedUnder_of ⟨1, by simp⟩

中文:
定理 tendsto_of_对任意_isOpen_le_liminf
  结论: {ι : 类型} {μ : 概率测度 Ω}
  证明: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat fun G hG => (h_opens G hG).trans ?_
  change _ <= atTop.liminf ((fun i => μs i G) ∘ u)
  rw [liminf_comp]
  refine liminf_le_liminf_of_le hu (by isBoundedDefault) ?_
.isCoboundedUnder_ge exact isBoundedUnder_of ⟨1, by simp⟩

Depends on / 依赖: Filter, Filter.tendsto_of_seq_tendsto, atTop.liminf, h_opens, isBoundedDefault, isBoundedUnder_of, isCoboundedUnder_ge, liminf, liminf_comp, liminf_le_liminf_of_le, tendsto_of_forall_isOpen_le_liminf_nat, tendsto_of_seq_tendsto
-/
theorem tendsto_of_forall_isOpen_le_liminf {ι : Type*} {μ : ProbabilityMeasure Ω}
    {μs : ι -> ProbabilityMeasure Ω} {L : Filter ι} [L.IsCountablyGenerated]
    (h_opens : forall G, IsOpen G -> μ G <= L.liminf (fun i => μs i G)) :
    L.Tendsto (fun i => μs i) (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isOpen_le_liminf_nat fun G hG => (h_opens G hG).trans ?_
  change _ <= atTop.liminf ((fun i => μs i G) ∘ u)
  rw [liminf_comp]
  refine liminf_le_liminf_of_le hu (by isBoundedDefault) ?_
.isCoboundedUnder_ge exact isBoundedUnder_of ⟨1, by simp⟩

end le_liminf_open_implies_convergence

section Closed

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι -> ProbabilityMeasure Ω}
    {L : Filter ι} [L.IsCountablyGenerated]

/--
lemma `tendsto_of_forall_isClosed_limsup_le'` / 引理 `tendsto_of_forall_isClosed_limsup_le'`

English:
lemma tendsto_of_forall_isClosed_limsup_le'
  proof: by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]

中文:
引理 tendsto_of_对任意_isClosed_limsup_le'
  证明: by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]

Depends on / 依赖: limsup_measure_closed_le_iff_liminf_measure_open_ge, tendsto_of_forall_isOpen_le_liminf
-/
lemma tendsto_of_forall_isClosed_limsup_le'
    (h : forall F : Set Ω, IsClosed F -> limsup (fun i => (μs i : Measure Ω) F) L <= (μ : Measure Ω) F) :
    Tendsto μs L (𝓝 μ) := by
  refine tendsto_of_forall_isOpen_le_liminf' ?_
  rwa [← limsup_measure_closed_le_iff_liminf_measure_open_ge]

/--
lemma `tendsto_of_forall_isClosed_limsup_le_nat` / 引理 `tendsto_of_forall_isClosed_limsup_le_nat`

English:
lemma tendsto_of_forall_isClosed_limsup_le_nat
  statement: {μs : Nat -> ProbabilityMeasure Ω}
  proof: by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF_closed => ?_
  specialize h F hF_closed
  have aux : ENNReal.ofNNReal (limsup (fun i => μs i F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun i => μs i F) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · F) (by fun_prop)
      ⟨1, by simp⟩ ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp

中文:
引理 tendsto_of_对任意_isClosed_limsup_le_nat
  结论: {μs : 自然数 -> 概率测度 Ω}
  证明: by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF_closed => ?_
  specialize h F hF_closed
  have aux : ENNReal.ofNNReal (limsup (fun i => μs i F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun i => μs i F) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · F) (by fun_prop)
      ⟨1, by simp⟩ ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp

Depends on / 依赖: ENNReal, ENNReal.coe_mono, ENNReal.ofNNReal, Monotone, Monotone.map_limsup_of_continuousAt, ProbabilityMeasure, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, coe_mono, convert, ennreal_coeFn_eq_coeFn_toMeasure, fun_prop, hF_closed, limsup, map_limsup_of_continuousAt, ofNNReal, specialize, tendsto_of_forall_isClosed_limsup_le
-/
lemma tendsto_of_forall_isClosed_limsup_le_nat {μs : Nat -> ProbabilityMeasure Ω}
    (h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) atTop <= μ F) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_forall_isClosed_limsup_le' fun F hF_closed => ?_
  specialize h F hF_closed
  have aux : ENNReal.ofNNReal (limsup (fun i => μs i F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun i => μs i F) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · F) (by fun_prop)
      ⟨1, by simp⟩ ⟨0, by simp⟩
  have obs := ENNReal.coe_mono h
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, aux] at obs
  convert! obs
  simp

/--
theorem `tendsto_of_forall_isClosed_limsup_le` / 定理 `tendsto_of_forall_isClosed_limsup_le`

English:
theorem tendsto_of_forall_isClosed_limsup_le
  proof: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isClosed_limsup_le_nat fun F hF => le_trans ?_ (h F hF)
  exact (limsup_comp (fun i => μs i F) u _).trans_le
    (limsup_le_limsup_of_le hu (by isBoundedDefault) ⟨1, by simp⟩)

中文:
定理 tendsto_of_对任意_isClosed_limsup_le
  证明: by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isClosed_limsup_le_nat fun F hF => le_trans ?_ (h F hF)
  exact (limsup_comp (fun i => μs i F) u _).trans_le
    (limsup_le_limsup_of_le hu (by isBoundedDefault) ⟨1, by simp⟩)

Depends on / 依赖: Filter, Filter.tendsto_of_seq_tendsto, isBoundedDefault, le_trans, limsup_comp, limsup_le_limsup_of_le, tendsto_of_forall_isClosed_limsup_le_nat, tendsto_of_seq_tendsto, trans_le
-/
theorem tendsto_of_forall_isClosed_limsup_le
    (h : forall F : Set Ω, IsClosed F -> limsup (fun i => μs i F) L <= μ F) :
    Tendsto μs L (𝓝 μ) := by
  apply Filter.tendsto_of_seq_tendsto fun u hu => ?_
  apply tendsto_of_forall_isClosed_limsup_le_nat fun F hF => le_trans ?_ (h F hF)
  exact (limsup_comp (fun i => μs i F) u _).trans_le
    (limsup_le_limsup_of_le hu (by isBoundedDefault) ⟨1, by simp⟩)

/--
lemma `tendsto_of_forall_isClosed_limsup_real_le'` / 引理 `tendsto_of_forall_isClosed_limsup_real_le'`

English:
lemma tendsto_of_forall_isClosed_limsup_real_le'
  statement: {L : Filter ι} [L.IsCountablyGenerated]
  proof: tendsto_of_forall_isClosed_limsup_le (by simpa using h)

中文:
引理 tendsto_of_对任意_isClosed_limsup_real_le'
  结论: {L : 滤子 ι} [L.是余untablyGenerated]
  证明: tendsto_of_forall_isClosed_limsup_le (by simpa using h)

Depends on / 依赖: tendsto_of_forall_isClosed_limsup_le
-/
lemma tendsto_of_forall_isClosed_limsup_real_le' {L : Filter ι} [L.IsCountablyGenerated]
    (h : forall F : Set Ω, IsClosed F ->
      limsup (fun i => (μs i : Measure Ω).real F) L <= (μ : Measure Ω).real F) :
    Tendsto μs L (𝓝 μ) := tendsto_of_forall_isClosed_limsup_le (by simpa using h)

/--
theorem `tendsto_of_forall_isCompact_of_isTightMeasureSet` / 定理 `tendsto_of_forall_isCompact_of_isTightMeasureSet`

English:
theorem tendsto_of_forall_isCompact_of_isTightMeasureSet
  proof: by
  obtain rfl | _ := L.eq_or_neBot
  · simp
refine tendsto_of_forall_isClosed_limsup_le fun F hF_closed => ?_
  rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)]
refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨K, hKc, hK_le⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    h₁ ε (by positivity)
  grw [limsup_le_limsup (v := fun i => μs i (F inter K) + (ε : ENNReal))]
  · rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
    apply add_le_add _ (by simp)
specialize h₂ (F inter K) hKc.inter_left hF_closed
    rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)] at h₂
    grw [h₂]
    simp [measure_mono]
  · refine .of_forall (fun i => ?_)
    simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    grw [measure_mono (t := (F inter K) union F \ K) (by simp), measure_union_le]
    gcongr
exact le_trans (measure_mono (by simp)) hK_le (μs i) by simp

中文:
定理 tendsto_of_对任意_isCompact_of_isTightMeasureSet
  证明: by
  obtain rfl | _ := L.eq_or_neBot
  · simp
refine tendsto_of_forall_isClosed_limsup_le fun F hF_closed => ?_
  rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)]
refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨K, hKc, hK_le⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    h₁ ε (by positivity)
  grw [limsup_le_limsup (v := fun i => μs i (F inter K) + (ε : ENNReal))]
  · rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
    apply add_le_add _ (by simp)
specialize h₂ (F inter K) hKc.inter_left hF_closed
    rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)] at h₂
    grw [h₂]
    simp [measure_mono]
  · refine .of_forall (fun i => ?_)
    simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    grw [measure_mono (t := (F inter K) union F \ K) (by simp), measure_union_le]
    gcongr
exact le_trans (measure_mono (by simp)) hK_le (μs i) by simp

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.le_of_forall_pos_le_add, ENNReal.ofNNReal_limsup, L.eq_or_neBot, coe_le_coe, eq_or_neBot, hF_closed, hK_le, isBoundedDefaul, isBoundedUnder_of_eventually_le, isTightMeasureSet_iff_exists_isCompact_measure_compl_le, isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp, le_of_forall_pos_le_add, limsup_add_const, limsup_le_limsup, ofNNReal_limsup, tendsto_of_forall_isClosed_limsup_le
-/
theorem tendsto_of_forall_isCompact_of_isTightMeasureSet
    (h₁ : IsTightMeasureSet (range (ProbabilityMeasure.toMeasure ∘ μs)))
    (h₂ : forall F, IsCompact F -> limsup (μs · F) L <= μ F) :
    Tendsto μs L (𝓝 μ) := by
  obtain rfl | _ := L.eq_or_neBot
  · simp
refine tendsto_of_forall_isClosed_limsup_le fun F hF_closed => ?_
  rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)]
refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨K, hKc, hK_le⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    h₁ ε (by positivity)
  grw [limsup_le_limsup (v := fun i => μs i (F inter K) + (ε : ENNReal))]
  · rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
    apply add_le_add _ (by simp)
specialize h₂ (F inter K) hKc.inter_left hF_closed
    rw [← ENNReal.coe_le_coe]; rw [ENNReal.ofNNReal_limsup <|
      isBoundedUnder_of_eventually_le (a := 1) (by simp)] at h₂
    grw [h₂]
    simp [measure_mono]
  · refine .of_forall (fun i => ?_)
    simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    grw [measure_mono (t := (F inter K) union F \ K) (by simp), measure_union_le]
    gcongr
exact le_trans (measure_mono (by simp)) hK_le (μs i) by simp

end Closed

section Lipschitz

/--
theorem `tendsto_iff_forall_lipschitz_integral_tendsto` / 定理 `tendsto_iff_forall_lipschitz_integral_tendsto`

English:
theorem tendsto_iff_forall_lipschitz_integral_tendsto
  statement: {γ Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  constructor
  · -- A bounded Lipschitz function is in particular a bounded continuous function, and we already
    -- know that weak convergence implies convergence of their integrals
    intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω Real :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using! h f'
  -- To prove the other direction, we prove convergence of the measure of closed sets.
  -- We approximate the indicator function of a closed set by bounded Lipschitz functions.
  rcases F.eq_or_neBot with rfl | hne
  · simp
  refine fun h => tendsto_of_forall_isClosed_limsup_real_le' fun s hs => ?_
  refine le_of_forall_pos_le_add fun ε ε_pos => ?_
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δ := (1 : Real) / (n + 1)) (by positivity) s ω
  have key₁ : Tendsto (fun n => ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hs (δs := fun n => (1 : Real) / (n + 1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ : Tendsto (fun i => ∫ ω, fs M ω ∂(μs i)) F (𝓝 (∫ ω, fs M ω ∂μ)) :=
    h (fs M) ⟨1, fun x y => ?_⟩
      ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s⟩
  swap
  · simp only [Real.dist_eq, abs_le]
    have h1 x : fs M x <= 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 <= fs M x := by simp [fs]
    grind
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near : forallᶠ x in F, (μs x : Measure Ω).real s <= ∫ a, fs M a ∂μ + ε / 2 := by
    refine (key₂.eventually_le_const room₂).mono fun x hx => le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ (integrable_thickenedIndicator _ _) ?_
    · exact (integrable_indicator_iff hs.measurableSet).mpr (integrable_const _).integrableOn
    · have h : _ <= fs M :=
        indicator_le_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s
      simpa using! h
  apply (Filter.limsup_le_of_le ?_ ev_near).trans
  · apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
    ring
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)

中文:
定理 tendsto_iff_对任意_lipschitz_integral_tendsto
  结论: {γ Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  constructor
  · -- A bounded Lipschitz function is in particular a bounded continuous function, and we already
    -- know that weak convergence implies convergence of their integrals
    intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω Real :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using! h f'
  -- To prove the other direction, we prove convergence of the measure of closed sets.
  -- We approximate the indicator function of a closed set by bounded Lipschitz functions.
  rcases F.eq_or_neBot with rfl | hne
  · simp
  refine fun h => tendsto_of_forall_isClosed_limsup_real_le' fun s hs => ?_
  refine le_of_forall_pos_le_add fun ε ε_pos => ?_
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δ := (1 : Real) / (n + 1)) (by positivity) s ω
  have key₁ : Tendsto (fun n => ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hs (δs := fun n => (1 : Real) / (n + 1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ : Tendsto (fun i => ∫ ω, fs M ω ∂(μs i)) F (𝓝 (∫ ω, fs M ω ∂μ)) :=
    h (fs M) ⟨1, fun x y => ?_⟩
      ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s⟩
  swap
  · simp only [Real.dist_eq, abs_le]
    have h1 x : fs M x <= 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 <= fs M x := by simp [fs]
    grind
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near : forallᶠ x in F, (μs x : Measure Ω).real s <= ∫ a, fs M a ∂μ + ε / 2 := by
    refine (key₂.eventually_le_const room₂).mono fun x hx => le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ (integrable_thickenedIndicator _ _) ?_
    · exact (integrable_indicator_iff hs.measurableSet).mpr (integrable_const _).integrableOn
    · have h : _ <= fs M :=
        indicator_le_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s
      simpa using! h
  apply (Filter.limsup_le_of_le ?_ ev_near).trans
  · apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
    ring
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)

Depends on / 依赖: Lipschitz, already, bounded, continuous, function, particular
-/
theorem tendsto_iff_forall_lipschitz_integral_tendsto {γ Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {F : Filter γ} [F.IsCountablyGenerated]
    {μs : γ -> ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      forall f : Ω -> Real, (exists (C : Real), forall x y, dist (f x) (f y) <= C) -> (exists L, LipschitzWith L f) ->
        Tendsto (fun i => ∫ ω, f ω ∂(μs i)) F (𝓝 (∫ ω, f ω ∂μ)) := by
  constructor
  · -- A bounded Lipschitz function is in particular a bounded continuous function, and we already
    -- know that weak convergence implies convergence of their integrals
    intro h f hf_bounded hf_lip
    simp_rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    let f' : BoundedContinuousFunction Ω Real :=
    { toFun := f
      continuous_toFun := hf_lip.choose_spec.continuous
      map_bounded' := hf_bounded }
    simpa using! h f'
  -- To prove the other direction, we prove convergence of the measure of closed sets.
  -- We approximate the indicator function of a closed set by bounded Lipschitz functions.
  rcases F.eq_or_neBot with rfl | hne
  · simp
  refine fun h => tendsto_of_forall_isClosed_limsup_real_le' fun s hs => ?_
  refine le_of_forall_pos_le_add fun ε ε_pos => ?_
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δ := (1 : Real) / (n + 1)) (by positivity) s ω
  have key₁ : Tendsto (fun n => ∫ ω, fs n ω ∂μ) atTop (𝓝 ((μ : Measure Ω).real s)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hs (δs := fun n => (1 : Real) / (n + 1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have room₁ : (μ : Measure Ω).real s < (μ : Measure Ω).real s + ε / 2 := by simp [ε_pos]
obtain ⟨M, hM⟩ := eventually_atTop.mp key₁.eventually_lt_const room₁
  have key₂ : Tendsto (fun i => ∫ ω, fs M ω ∂(μs i)) F (𝓝 (∫ ω, fs M ω ∂μ)) :=
    h (fs M) ⟨1, fun x y => ?_⟩
      ⟨_, lipschitzWith_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s⟩
  swap
  · simp only [Real.dist_eq, abs_le]
    have h1 x : fs M x <= 1 := thickenedIndicator_le_one _ _ _
    have h2 x : 0 <= fs M x := by simp [fs]
    grind
  have room₂ : ∫ a, fs M a ∂μ < ∫ a, fs M a ∂μ + ε / 2 := by simp [ε_pos]
  have ev_near : forallᶠ x in F, (μs x : Measure Ω).real s <= ∫ a, fs M a ∂μ + ε / 2 := by
    refine (key₂.eventually_le_const room₂).mono fun x hx => le_trans ?_ hx
    rw [← integral_indicator_one hs.measurableSet]
    refine integral_mono ?_ (integrable_thickenedIndicator _ _) ?_
    · exact (integrable_indicator_iff hs.measurableSet).mpr (integrable_const _).integrableOn
    · have h : _ <= fs M :=
        indicator_le_thickenedIndicator (δ := (1 : Real) / (M + 1)) (by positivity) s
      simpa using! h
  apply (Filter.limsup_le_of_le ?_ ev_near).trans
  · apply (add_le_add (hM M rfl.le).le (le_refl (ε / 2))).trans_eq
    ring
  · exact isCoboundedUnder_le_of_le F (x := 0) (by simp)

end Lipschitz

section convergenceCriterion

open scoped Finset

variable {Ω ι : Type*} [MeasurableSpace Ω]

/--
lemma `_root_.IsPiSystem.tendsto_measureReal_biUnion` / 引理 `_root_.IsPiSystem.tendsto_measureReal_biUnion`

English:
lemma _root_.IsPiSystem.tendsto_measureReal_biUnion
  proof: by
  /- This statement is not completely obvious, as `⋃ s ∈ t, s` does not belong to the π-system `S`.
  However, thanks to the inclusion-exclusion formula one may express its measure in terms of
  measures of elements of `S`, from which the result follows. -/
  have A (i) : (μ i).real (⋃ s in t, s) = ∑ u in t.powerset with u.Nonempty,
      (-1 : Real) ^ (#u + 1) * (μ i).real (⋂ s in u, s) :=
    measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
      (fun s hs => hμ _ (ht _ hs) i)
  simp_rw [A, measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
    (fun s hs => hν _ (ht _ hs))]
  refine tendsto_finsetSum _ (fun u hu => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hu
  apply Filter.Tendsto.const_mul
  rcases eq_empty_or_nonempty (⋂ s in u, s) with h'u | h'u
  · simpa [h'u] using tendsto_const_nhds
  apply h
  exact hS.biInter_mem hu.2 (fun s hs => ht _ (hu.1 hs)) h'u

中文:
引理 _root_.IsPiSystem.tendsto_measure实数_biUnion
  证明: by
  /- This statement is not completely obvious, as `⋃ s ∈ t, s` does not belong to the π-system `S`.
  However, thanks to the inclusion-exclusion formula one may express its measure in terms of
  measures of elements of `S`, from which the result follows. -/
  have A (i) : (μ i).real (⋃ s in t, s) = ∑ u in t.powerset with u.Nonempty,
      (-1 : Real) ^ (#u + 1) * (μ i).real (⋂ s in u, s) :=
    measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
      (fun s hs => hμ _ (ht _ hs) i)
  simp_rw [A, measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
    (fun s hs => hν _ (ht _ hs))]
  refine tendsto_finsetSum _ (fun u hu => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hu
  apply Filter.Tendsto.const_mul
  rcases eq_empty_or_nonempty (⋂ s in u, s) with h'u | h'u
  · simpa [h'u] using tendsto_const_nhds
  apply h
  exact hS.biInter_mem hu.2 (fun s hs => ht _ (hu.1 hs)) h'u

Depends on / 依赖: Tendsto, finiteness
-/
lemma _root_.IsPiSystem.tendsto_measureReal_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι -> Measure Ω} {ν : Measure Ω} {l : Filter ι}
    {t : Finset (Set Ω)} (ht : forall s in t, s in S)
    (hmeas : forall s in S, MeasurableSet s)
    (h : forall s in S, Tendsto (fun i => (μ i).real s) l (𝓝 (ν.real s)))
    (hν : forall s in S, ν s != ∞ := by finiteness)
    (hμ : forall s in S, forall i, μ i s != ∞ := by finiteness) :
    Tendsto (fun i => (μ i).real (⋃ s in t, s)) l (𝓝 (ν.real (⋃ s in t, s))) := by
  /- This statement is not completely obvious, as `⋃ s ∈ t, s` does not belong to the π-system `S`.
  However, thanks to the inclusion-exclusion formula one may express its measure in terms of
  measures of elements of `S`, from which the result follows. -/
  have A (i) : (μ i).real (⋃ s in t, s) = ∑ u in t.powerset with u.Nonempty,
      (-1 : Real) ^ (#u + 1) * (μ i).real (⋂ s in u, s) :=
    measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
      (fun s hs => hμ _ (ht _ hs) i)
  simp_rw [A, measureReal_biUnion_eq_sum_powerset (fun s hs => hmeas _ (ht _ hs))
    (fun s hs => hν _ (ht _ hs))]
  refine tendsto_finsetSum _ (fun u hu => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hu
  apply Filter.Tendsto.const_mul
  rcases eq_empty_or_nonempty (⋂ s in u, s) with h'u | h'u
  · simpa [h'u] using tendsto_const_nhds
  apply h
  exact hS.biInter_mem hu.2 (fun s hs => ht _ (hu.1 hs)) h'u

/--
lemma `_root_.IsPiSystem.tendsto_probabilityMeasure_biUnion` / 引理 `_root_.IsPiSystem.tendsto_probabilityMeasure_biUnion`

English:
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_biUnion
  proof: by
  have : Tendsto (fun i => (μ i : Measure Ω).real (⋃ s in t, s)) l
      (𝓝 ((ν : Measure Ω).real (⋃ s in t, s))) := by
    apply hS.tendsto_measureReal_biUnion ht hmeas
    simpa using h
  simpa using this

中文:
引理 _root_.IsPiSystem.tendsto_probabilityMeasure_biUnion
  证明: by
  have : Tendsto (fun i => (μ i : Measure Ω).real (⋃ s in t, s)) l
      (𝓝 ((ν : Measure Ω).real (⋃ s in t, s))) := by
    apply hS.tendsto_measureReal_biUnion ht hmeas
    simpa using h
  simpa using this

Depends on / 依赖: Measure, Tendsto, hS.tendsto_measureReal_biUnion, tendsto_measureReal_biUnion
-/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_biUnion
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι -> ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} {t : Finset (Set Ω)} (ht : forall s in t, s in S) (hmeas : forall s in S, MeasurableSet s)
    (h : forall s in S, Tendsto (fun i => μ i s) l (𝓝 (ν s))) :
    Tendsto (fun i => μ i (⋃ s in t, s)) l (𝓝 (ν (⋃ s in t, s))) := by
  have : Tendsto (fun i => (μ i : Measure Ω).real (⋃ s in t, s)) l
      (𝓝 ((ν : Measure Ω).real (⋃ s in t, s))) := by
    apply hS.tendsto_measureReal_biUnion ht hmeas
    simpa using h
  simpa using this

/--
lemma `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen` / 引理 `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`

English:
lemma ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen
  proof: by
  obtain ⟨T, TS, T_count, hT⟩ : exists T : Set (Set Ω), T subseteq S ∧ T.Countable ∧ ⋃ t in T, t = G := by
    have : forall (x : G), exists s in S, s in 𝓝 (x : Ω) ∧ s subseteq G := fun x => h G hG x x.2
    choose! s hsS hs_nhds hsG using this
    rcases TopologicalSpace.isOpen_iUnion_countable (fun i => interior (s i))
      (fun i => isOpen_interior) with ⟨T₀, T₀_count, hT₀⟩
    refine ⟨s '' T₀, by grind, T₀_count.image s, ?_⟩
    refine Subset.antisymm (by simp; grind) ?_
    have : G subseteq ⋃ i, interior (s i) := by
      intro y hy
      simpa using ⟨y, hy, mem_interior_iff_mem_nhds.2 (hs_nhds ⟨y, hy⟩)⟩
    apply this.trans
    rw [← hT₀]; rw [biUnion_image]
    exact iUnion₂_mono fun i j => interior_subset
  have : T.Nonempty := by
    contrapose! hr
    simp [← hT, hr]
  rcases T_count.exists_eq_range this with ⟨f, hf⟩
  have G_eq : G = ⋃ n, f n := by simp [← hT, hf]
  have : Tendsto (fun i => ν (accumulate f i)) atTop (𝓝 (ν (⋃ i, f i))) :=
    (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
  rw [← G_eq] at this
  rcases ((tendsto_order.1 this).1 r hr).exists with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).image f, by grind, ?_, ?_⟩
  · convert! hn
    simp [accumulate_def]
  · simpa [G_eq] using fun i _ => subset_iUnion f i

中文:
引理 概率测度.存在_lt_measure_biUnion_of_isOpen
  证明: by
  obtain ⟨T, TS, T_count, hT⟩ : exists T : Set (Set Ω), T subseteq S ∧ T.Countable ∧ ⋃ t in T, t = G := by
    have : forall (x : G), exists s in S, s in 𝓝 (x : Ω) ∧ s subseteq G := fun x => h G hG x x.2
    choose! s hsS hs_nhds hsG using this
    rcases TopologicalSpace.isOpen_iUnion_countable (fun i => interior (s i))
      (fun i => isOpen_interior) with ⟨T₀, T₀_count, hT₀⟩
    refine ⟨s '' T₀, by grind, T₀_count.image s, ?_⟩
    refine Subset.antisymm (by simp; grind) ?_
    have : G subseteq ⋃ i, interior (s i) := by
      intro y hy
      simpa using ⟨y, hy, mem_interior_iff_mem_nhds.2 (hs_nhds ⟨y, hy⟩)⟩
    apply this.trans
    rw [← hT₀]; rw [biUnion_image]
    exact iUnion₂_mono fun i j => interior_subset
  have : T.Nonempty := by
    contrapose! hr
    simp [← hT, hr]
  rcases T_count.exists_eq_range this with ⟨f, hf⟩
  have G_eq : G = ⋃ n, f n := by simp [← hT, hf]
  have : Tendsto (fun i => ν (accumulate f i)) atTop (𝓝 (ν (⋃ i, f i))) :=
    (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
  rw [← G_eq] at this
  rcases ((tendsto_order.1 this).1 r hr).exists with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).image f, by grind, ?_, ?_⟩
  · convert! hn
    simp [accumulate_def]
  · simpa [G_eq] using fun i _ => subset_iUnion f i

Depends on / 依赖: Countable, Subset, Subset.antisymm, T.Countable, T_count, TopologicalSpace, TopologicalSpace.isOpen_iUnion_countable, _count.image, antisymm, hs_nhds, interior, isOpen_iUnion_countable, isOpen_interior, subseteq
-/
lemma ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen
    [TopologicalSpace Ω] [SecondCountableTopology Ω]
    {S : Set (Set Ω)} (ν : ProbabilityMeasure Ω)
    (h : forall (u : Set Ω), IsOpen u -> forall x in u, exists s in S, s in 𝓝 x ∧ s subseteq u)
    {G : Set Ω} (hG : IsOpen G) {r : Real>=0} (hr : r < ν G) :
    exists T : Finset (Set Ω), (forall t in T, t in S) ∧ (r < ν (⋃ t in T, t)) ∧ (⋃ t in T, t) subseteq G := by
  obtain ⟨T, TS, T_count, hT⟩ : exists T : Set (Set Ω), T subseteq S ∧ T.Countable ∧ ⋃ t in T, t = G := by
    have : forall (x : G), exists s in S, s in 𝓝 (x : Ω) ∧ s subseteq G := fun x => h G hG x x.2
    choose! s hsS hs_nhds hsG using this
    rcases TopologicalSpace.isOpen_iUnion_countable (fun i => interior (s i))
      (fun i => isOpen_interior) with ⟨T₀, T₀_count, hT₀⟩
    refine ⟨s '' T₀, by grind, T₀_count.image s, ?_⟩
    refine Subset.antisymm (by simp; grind) ?_
    have : G subseteq ⋃ i, interior (s i) := by
      intro y hy
      simpa using ⟨y, hy, mem_interior_iff_mem_nhds.2 (hs_nhds ⟨y, hy⟩)⟩
    apply this.trans
    rw [← hT₀]; rw [biUnion_image]
    exact iUnion₂_mono fun i j => interior_subset
  have : T.Nonempty := by
    contrapose! hr
    simp [← hT, hr]
  rcases T_count.exists_eq_range this with ⟨f, hf⟩
  have G_eq : G = ⋃ n, f n := by simp [← hT, hf]
  have : Tendsto (fun i => ν (accumulate f i)) atTop (𝓝 (ν (⋃ i, f i))) :=
    (ENNReal.tendsto_toNNReal_iff (by simp) (by simp)).2 tendsto_measure_iUnion_accumulate
  rw [← G_eq] at this
  rcases ((tendsto_order.1 this).1 r hr).exists with ⟨n, hn⟩
  refine ⟨(Finset.range (n + 1)).image f, by grind, ?_, ?_⟩
  · convert! hn
    simp [accumulate_def]
  · simpa [G_eq] using fun i _ => subset_iUnion f i

/--
lemma `_root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` / 引理 `_root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`

English:
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
  proof: by
  /- We apply the portmanteau theorem: it suffices to show that, given an open set `G`
  and `r < ν G`, then for large `i` one has `r < μᵢ G`. For this, we approximate `G` from inside by
  a finite union `G'` of elements of `S`, still with measure `> r`, by Lemma
  `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`. If we have `μᵢ G' → ν G'`,
  then we deduce `r < μᵢ G'` for large `i`, and therefore `r < μᵢ G`.

  Our assumption does not give directly `μᵢ G' → ν G'`, as `G'` does not belong to the π-system `S`.
  However, the inclusion-exclusion formula makes it possible to express `μᵢ G'` and `ν G'` in terms
  of the measures of intersections of elements of `S`, for which we have the convergence. It follows
  that `μᵢ G' → ν G'` holds, concluding the proof. This second step is already formalized in the
  lemma `IsPiSystem.tendsto_probabilityMeasure_biUnion`. -/
  rcases l.eq_or_neBot with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) l (by simp)) (by isBoundedDefault)).2
    (fun r hr => ?_)
  obtain ⟨T, TS, T_meas, TG⟩ :
      exists T : Finset (Set Ω), (forall t in T, t in S) ∧ (r < ν (⋃ t in T, t)) ∧ (⋃ t in T, t) subseteq G :=
    ν.exists_lt_measure_biUnion_of_isOpen h hG hr
  have : Tendsto (fun i => μ i (⋃ t in T, t)) l (𝓝 (ν (⋃ t in T, t))) :=
    hS.tendsto_probabilityMeasure_biUnion TS hmeas h'
  filter_upwards [(tendsto_order.1 this).1 r T_meas] with i hi
exact hi.trans_le ProbabilityMeasure.apply_mono _ TG

中文:
引理 _root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
  证明: by
  /- We apply the portmanteau theorem: it suffices to show that, given an open set `G`
  and `r < ν G`, then for large `i` one has `r < μᵢ G`. For this, we approximate `G` from inside by
  a finite union `G'` of elements of `S`, still with measure `> r`, by Lemma
  `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`. If we have `μᵢ G' → ν G'`,
  then we deduce `r < μᵢ G'` for large `i`, and therefore `r < μᵢ G`.

  Our assumption does not give directly `μᵢ G' → ν G'`, as `G'` does not belong to the π-system `S`.
  However, the inclusion-exclusion formula makes it possible to express `μᵢ G'` and `ν G'` in terms
  of the measures of intersections of elements of `S`, for which we have the convergence. It follows
  that `μᵢ G' → ν G'` holds, concluding the proof. This second step is already formalized in the
  lemma `IsPiSystem.tendsto_probabilityMeasure_biUnion`. -/
  rcases l.eq_or_neBot with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) l (by simp)) (by isBoundedDefault)).2
    (fun r hr => ?_)
  obtain ⟨T, TS, T_meas, TG⟩ :
      exists T : Finset (Set Ω), (forall t in T, t in S) ∧ (r < ν (⋃ t in T, t)) ∧ (⋃ t in T, t) subseteq G :=
    ν.exists_lt_measure_biUnion_of_isOpen h hG hr
  have : Tendsto (fun i => μ i (⋃ t in T, t)) l (𝓝 (ν (⋃ t in T, t))) :=
    hS.tendsto_probabilityMeasure_biUnion TS hmeas h'
  filter_upwards [(tendsto_order.1 this).1 r T_meas] with i hi
exact hi.trans_le ProbabilityMeasure.apply_mono _ TG
-/
lemma _root_.IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    [TopologicalSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
    {S : Set (Set Ω)} (hS : IsPiSystem S) {μ : ι -> ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hmeas : forall s in S, MeasurableSet s)
    (h : forall (u : Set Ω), IsOpen u -> forall x in u, exists s in S, s in 𝓝 x ∧ s subseteq u)
    (h' : forall s in S, Tendsto (fun i => μ i s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  /- We apply the portmanteau theorem: it suffices to show that, given an open set `G`
  and `r < ν G`, then for large `i` one has `r < μᵢ G`. For this, we approximate `G` from inside by
  a finite union `G'` of elements of `S`, still with measure `> r`, by Lemma
  `ProbabilityMeasure.exists_lt_measure_biUnion_of_isOpen`. If we have `μᵢ G' → ν G'`,
  then we deduce `r < μᵢ G'` for large `i`, and therefore `r < μᵢ G`.

  Our assumption does not give directly `μᵢ G' → ν G'`, as `G'` does not belong to the π-system `S`.
  However, the inclusion-exclusion formula makes it possible to express `μᵢ G'` and `ν G'` in terms
  of the measures of intersections of elements of `S`, for which we have the convergence. It follows
  that `μᵢ G' → ν G'` holds, concluding the proof. This second step is already formalized in the
  lemma `IsPiSystem.tendsto_probabilityMeasure_biUnion`. -/
  rcases l.eq_or_neBot with rfl | hl
  · simp
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  refine (le_liminf_iff (isCoboundedUnder_ge_of_le (x := 1) l (by simp)) (by isBoundedDefault)).2
    (fun r hr => ?_)
  obtain ⟨T, TS, T_meas, TG⟩ :
      exists T : Finset (Set Ω), (forall t in T, t in S) ∧ (r < ν (⋃ t in T, t)) ∧ (⋃ t in T, t) subseteq G :=
    ν.exists_lt_measure_biUnion_of_isOpen h hG hr
  have : Tendsto (fun i => μ i (⋃ t in T, t)) l (𝓝 (ν (⋃ t in T, t))) :=
    hS.tendsto_probabilityMeasure_biUnion TS hmeas h'
  filter_upwards [(tendsto_order.1 this).1 r T_meas] with i hi
exact hi.trans_le ProbabilityMeasure.apply_mono _ TG

end convergenceCriterion

end MeasureTheory --namespace
