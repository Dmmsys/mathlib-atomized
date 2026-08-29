/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Results about indicator functions, their integrals, and measures

This file has a few measure-theoretic or integration-related results on indicator functions.

## Implementation notes

This file exists to avoid importing `Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
in `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`.

## TODO

The result `MeasureTheory.tendsto_measure_of_tendsto_indicator` here could be proved without
integration, if we had convergence of measures results for countably generated filters. Ideally,
the present file would then become unnecessary: lemmas such as
`MeasureTheory.tendsto_measure_of_ae_tendsto_indicator` would not need integration so could be
moved out of `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`, and the lemmas in this file could
be moved to, e.g., `Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`.
-/

public section

namespace MeasureTheory

section TendstoIndicator

open Set Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι -> Set α}

/--
lemma `tendsto_measure_of_ae_tendsto_indicator` / 引理 `tendsto_measure_of_ae_tendsto_indicator`

English:
lemma tendsto_measure_of_ae_tendsto_indicator
  statement: {μ : Measure α} (A_mble : MeasurableSet A)
  proof: by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α -> Real>=0∞))
          (Eventually.of_forall ?_) ?_ ?_ ?_
  · exact fun i => Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact Eventually.of_forall fun x => by grw [hi]
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
  · simpa only [Pi.one_def, tendsto_indicator_const_apply_iff_eventually] using h_lim

中文:
引理 tendsto_measure_of_ae_tendsto_indicator
  结论: {μ : 测度 α} (A_mble : 可测集 A)
  证明: by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α -> Real>=0∞))
          (Eventually.of_forall ?_) ?_ ?_ ?_
  · exact fun i => Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact Eventually.of_forall fun x => by grw [hi]
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
  · simpa only [Pi.one_def, tendsto_indicator_const_apply_iff_eventually] using h_lim

Depends on / 依赖: A_mble, As_le_B, As_mble, B.indicator, B_finmeas, B_mble, Eventually, Eventually.of_forall, Measurable, Measurable.indicator, MeasureTheory, MeasureTheory.lintegral_indicator_one, Pi.one_def, filter_upwards, indicator, lintegral_indicator_one, measurable_const, of_forall, one_def, simp_rw
-/
lemma tendsto_measure_of_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A)
    (As_mble : forall i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B != ∞) (As_le_B : forallᶠ i in L, As i subseteq B)
    (h_lim : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A) :
    Tendsto (fun i => μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α -> Real>=0∞))
          (Eventually.of_forall ?_) ?_ ?_ ?_
  · exact fun i => Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact Eventually.of_forall fun x => by grw [hi]
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
  · simpa only [Pi.one_def, tendsto_indicator_const_apply_iff_eventually] using h_lim

/--
lemma `tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure` / 引理 `tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure`

English:
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
  proof: tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (by finiteness) (Eventually.of_forall (fun i => subset_univ (As i))) h_lim

中文:
引理 tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
  证明: tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (by finiteness) (Eventually.of_forall (fun i => subset_univ (As i))) h_lim

Depends on / 依赖: A_mble, As_mble, Eventually, Eventually.of_forall, MeasurableSet, MeasurableSet.univ, finiteness, h_lim, of_forall, subset_univ, tendsto_measure_of_ae_tendsto_indicator
-/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    {μ : Measure α} [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : forall i, MeasurableSet (As i)) (h_lim : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A) :
    Tendsto (fun i => μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (by finiteness) (Eventually.of_forall (fun i => subset_univ (As i))) h_lim

/--
lemma `tendsto_measure_of_tendsto_indicator` / 引理 `tendsto_measure_of_tendsto_indicator`

English:
lemma tendsto_measure_of_tendsto_indicator
  statement: {μ : Measure α}
  proof: by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
        (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

中文:
引理 tendsto_measure_of_tendsto_indicator
  结论: {μ : 测度 α}
  证明: by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
        (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

Depends on / 依赖: As_le_B, As_mble, B_finmeas, B_mble, L.eq_or_neBot, ae_of_all, eq_or_neBot, h_lim, measurableSet_of_tendsto_indicator, tendsto_bot, tendsto_measure_of_ae_tendsto_indicator
-/
lemma tendsto_measure_of_tendsto_indicator {μ : Measure α}
    (As_mble : forall i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B != ∞) (As_le_B : forallᶠ i in L, As i subseteq B)
    (h_lim : forall x, forallᶠ i in L, x in As i ↔ x in A) :
    Tendsto (fun i => μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
        (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

/--
lemma `tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure` / 引理 `tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure`

English:
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
  proof: by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

中文:
引理 tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
  证明: by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

Depends on / 依赖: As_mble, L.eq_or_neBot, ae_of_all, eq_or_neBot, h_lim, measurableSet_of_tendsto_indicator, tendsto_bot, tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
-/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : forall i, MeasurableSet (As i))
    (h_lim : forall x, forallᶠ i in L, x in As i ↔ x in A) :
    Tendsto (fun i => μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoIndicator -- section

end MeasureTheory
