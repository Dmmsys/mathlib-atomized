/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Metrizable.Real
public import Mathlib.Topology.IndicatorConstPointwise

/-!
# Measurable functions in (pseudo-)metrizable Borel spaces
-/

public section

open Filter MeasureTheory TopologicalSpace Topology NNReal ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

section Limits

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]

open Metric

/--
theorem `measurable_of_tendsto_metrizable'` / 定理 `measurable_of_tendsto_metrizable'`

English:
theorem measurable_of_tendsto_metrizable'
  statement: {ι} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u]
  proof: by
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  apply measurable_of_isClosed'
  intro s h1s h2s h3s
  have : Measurable fun x => infNndist (g x) s := by
    suffices Tendsto (fun i x => infNndist (f i x) s) u (𝓝 fun x => infNndist (g x) s) from
      NNReal.measurable_of_tendsto' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim ⊢
    intro x
    exact ((continuous_infNndist_pt s).tendsto (g x)).comp (lim x)
  have h4s : g ⁻¹' s = (fun x => infNndist (g x) s) ⁻¹' {0} := by
    ext x
    simp [← h1s.mem_iff_infDist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  exact this (measurableSet_singleton 0)

中文:
定理 measurable_of_tendsto_metrizable'
  结论: {ι} {f : ι -> α -> β} {g : α -> β} (u : 滤子 ι) [NeBot u]
  证明: by
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  apply measurable_of_isClosed'
  intro s h1s h2s h3s
  have : Measurable fun x => infNndist (g x) s := by
    suffices Tendsto (fun i x => infNndist (f i x) s) u (𝓝 fun x => infNndist (g x) s) from
      NNReal.measurable_of_tendsto' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim ⊢
    intro x
    exact ((continuous_infNndist_pt s).tendsto (g x)).comp (lim x)
  have h4s : g ⁻¹' s = (fun x => infNndist (g x) s) ⁻¹' {0} := by
    ext x
    simp [← h1s.mem_iff_infDist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  exact this (measurableSet_singleton 0)

Depends on / 依赖: Measurable, NNReal, NNReal.measurable_of_tendsto, PseudoMetricSpace, Tendsto, continuous_infNndist_pt, infNndist, measurable_of_isClosed, measurable_of_tendsto, pseudoMetrizableSpacePseudoMetric, tendsto, tendsto_pi_nhds
-/
theorem measurable_of_tendsto_metrizable' {ι} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : forall i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  apply measurable_of_isClosed'
  intro s h1s h2s h3s
  have : Measurable fun x => infNndist (g x) s := by
    suffices Tendsto (fun i x => infNndist (f i x) s) u (𝓝 fun x => infNndist (g x) s) from
      NNReal.measurable_of_tendsto' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim ⊢
    intro x
    exact ((continuous_infNndist_pt s).tendsto (g x)).comp (lim x)
  have h4s : g ⁻¹' s = (fun x => infNndist (g x) s) ⁻¹' {0} := by
    ext x
    simp [← h1s.mem_iff_infDist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  exact this (measurableSet_singleton 0)

/--
theorem `measurable_of_tendsto_metrizable` / 定理 `measurable_of_tendsto_metrizable`

English:
theorem measurable_of_tendsto_metrizable
  statement: {f : Nat -> α -> β} {g : α -> β} (hf : forall i, Measurable (f i))
  proof: measurable_of_tendsto_metrizable' atTop hf lim

中文:
定理 measurable_of_tendsto_metrizable
  结论: {f : 自然数 -> α -> β} {g : α -> β} (hf : 对任意 i, 可测 (f i))
  证明: measurable_of_tendsto_metrizable' atTop hf lim

Depends on / 依赖: measurable_of_tendsto_metrizable
-/
theorem measurable_of_tendsto_metrizable {f : Nat -> α -> β} {g : α -> β} (hf : forall i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable' atTop hf lim

/--
theorem `aemeasurable_of_tendsto_metrizable_ae` / 定理 `aemeasurable_of_tendsto_metrizable_ae`

English:
theorem aemeasurable_of_tendsto_metrizable_ae
  statement: {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β}
  proof: by
  classical
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : forall n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  set p : α -> (Nat -> β) -> Prop := fun x f' => Tendsto (fun n => f' n) atTop (𝓝 (g x))
  have hp : forallᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto] with x hx using hx.comp hv
  set aeSeqLim := fun x => ite (x in aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some
  refine
    ⟨aeSeqLim,
      measurable_of_tendsto_metrizable' atTop (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => ?_),
      ?_⟩
  · simp_rw [aeSeqLim, aeSeq]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
    · exact tendsto_const_nhds
  · exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm

中文:
定理 aemeasurable_of_tendsto_metrizable_ae
  结论: {ι} {μ : 测度 α} {f : ι -> α -> β} {g : α -> β}
  证明: by
  classical
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : forall n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  set p : α -> (Nat -> β) -> Prop := fun x f' => Tendsto (fun n => f' n) atTop (𝓝 (g x))
  have hp : forallᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto] with x hx using hx.comp hv
  set aeSeqLim := fun x => ite (x in aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some
  refine
    ⟨aeSeqLim,
      measurable_of_tendsto_metrizable' atTop (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => ?_),
      ?_⟩
  · simp_rw [aeSeqLim, aeSeq]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
    · exact tendsto_const_nhds
  · exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm

Depends on / 依赖: AEMeasurable, Nonempty, Tendsto, aeSeq.measurable, aeSeqLim, aeSeqSet, classical, exists_seq_tendsto, filter_upwards, h_tendsto, hx.comp, measurable, measurable_of_tendsto_metrizable, tendsto_pi_n, u.exists_seq_tendsto
-/
theorem aemeasurable_of_tendsto_metrizable_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β}
    (u : Filter ι) [hu : NeBot u] [IsCountablyGenerated u] (hf : forall n, AEMeasurable (f n) μ)
    (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : AEMeasurable g μ := by
  classical
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : forall n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  set p : α -> (Nat -> β) -> Prop := fun x f' => Tendsto (fun n => f' n) atTop (𝓝 (g x))
  have hp : forallᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto] with x hx using hx.comp hv
  set aeSeqLim := fun x => ite (x in aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some
  refine
    ⟨aeSeqLim,
      measurable_of_tendsto_metrizable' atTop (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => ?_),
      ?_⟩
  · simp_rw [aeSeqLim, aeSeq]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
    · exact tendsto_const_nhds
  · exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm

/--
theorem `aemeasurable_of_tendsto_metrizable_ae'` / 定理 `aemeasurable_of_tendsto_metrizable_ae'`

English:
theorem aemeasurable_of_tendsto_metrizable_ae'
  statement: {μ : Measure α} {f : Nat -> α -> β} {g : α -> β}
  proof: aemeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto

中文:
定理 aemeasurable_of_tendsto_metrizable_ae'
  结论: {μ : 测度 α} {f : 自然数 -> α -> β} {g : α -> β}
  证明: aemeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto

Depends on / 依赖: aemeasurable_of_tendsto_metrizable_ae, h_ae_tendsto
-/
theorem aemeasurable_of_tendsto_metrizable_ae' {μ : Measure α} {f : Nat -> α -> β} {g : α -> β}
    (hf : forall n, AEMeasurable (f n) μ)
    (h_ae_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : AEMeasurable g μ :=
  aemeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto

/--
theorem `aemeasurable_of_unif_approx` / 定理 `aemeasurable_of_unif_approx`

English:
theorem aemeasurable_of_unif_approx
  statement: {β} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]
  proof: by
  obtain ⟨u, -, u_pos, u_lim⟩ :
    exists u : Nat -> Real, StrictAnti u ∧ (forall n : Nat, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  choose f Hf using fun n : Nat => hf (u n) (u_pos n)
  have : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have : forallᵐ x ∂μ, forall n, dist (f n x) (g x) <= u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this

中文:
定理 aemeasurable_of_unif_approx
  结论: {β} [可测空间 β] [伪度量空间 β] [Borel空间 β]
  证明: by
  obtain ⟨u, -, u_pos, u_lim⟩ :
    exists u : Nat -> Real, StrictAnti u ∧ (forall n : Nat, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  choose f Hf using fun n : Nat => hf (u n) (u_pos n)
  have : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have : forallᵐ x ∂μ, forall n, dist (f n x) (g x) <= u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this

Depends on / 依赖: StrictAnti, Tendsto, ae_all_iff, dist_nonneg, exists_seq_strictAnti_tendsto, filter_upwards, squeeze_zero, tendsto_iff_dist_tendsto_zero, u_lim, u_pos
-/
theorem aemeasurable_of_unif_approx {β} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]
    {μ : Measure α} {g : α -> β}
    (hf : forall ε > (0 : Real), exists f : α -> β, AEMeasurable f μ ∧ forallᵐ x ∂μ, dist (f x) (g x) <= ε) :
    AEMeasurable g μ := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
    exists u : Nat -> Real, StrictAnti u ∧ (forall n : Nat, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  choose f Hf using fun n : Nat => hf (u n) (u_pos n)
  have : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have : forallᵐ x ∂μ, forall n, dist (f n x) (g x) <= u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this

/--
theorem `measurable_of_tendsto_metrizable_ae` / 定理 `measurable_of_tendsto_metrizable_ae`

English:
theorem measurable_of_tendsto_metrizable_ae
  statement: {μ : Measure α} [μ.IsComplete] {f : Nat -> α -> β}
  proof: aemeasurable_iff_measurable.mp
    (aemeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).aemeasurable) h_ae_tendsto)

中文:
定理 measurable_of_tendsto_metrizable_ae
  结论: {μ : 测度 α} [μ.是完备] {f : 自然数 -> α -> β}
  证明: aemeasurable_iff_measurable.mp
    (aemeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).aemeasurable) h_ae_tendsto)

Depends on / 依赖: aemeasurable, aemeasurable_iff_measurable, aemeasurable_iff_measurable.mp, aemeasurable_of_tendsto_metrizable_ae, h_ae_tendsto
-/
theorem measurable_of_tendsto_metrizable_ae {μ : Measure α} [μ.IsComplete] {f : Nat -> α -> β}
    {g : α -> β} (hf : forall n, Measurable (f n))
    (h_ae_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g :=
  aemeasurable_iff_measurable.mp
    (aemeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).aemeasurable) h_ae_tendsto)

/--
theorem `measurable_limit_of_tendsto_metrizable_ae` / 定理 `measurable_limit_of_tendsto_metrizable_ae`

English:
theorem measurable_limit_of_tendsto_metrizable_ae
  statement: {ι} [Nonempty ι] {μ : Measure α}
  proof: by
  classical
  inhabit ι
  rcases eq_or_neBot L with (rfl | hL)
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, Eventually.of_forall fun x => tendsto_bot⟩
  set f_lim : α -> β := fun x =>
    if h : exists l : β, Tendsto (fun n => f n x) L (𝓝 l) then h.choose
      else (⟨f default x⟩ : Nonempty β).some
  have h_ae_tendsto_f_lim : forallᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
    filter_upwards [h_ae_tendsto] with x hx
    simpa [f_lim, hx] using hx.choose_spec
  have hf_lim : AEMeasurable f_lim μ :=
    aemeasurable_of_tendsto_metrizable_ae L hf h_ae_tendsto_f_lim
  refine ⟨hf_lim.mk f_lim, hf_lim.measurable_mk, ?_⟩
  filter_upwards [h_ae_tendsto_f_lim, hf_lim.ae_eq_mk] with x hx h_eq
  simpa [h_eq] using hx

中文:
定理 measurable_limit_of_tendsto_metrizable_ae
  结论: {ι} [非空 ι] {μ : 测度 α}
  证明: by
  classical
  inhabit ι
  rcases eq_or_neBot L with (rfl | hL)
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, Eventually.of_forall fun x => tendsto_bot⟩
  set f_lim : α -> β := fun x =>
    if h : exists l : β, Tendsto (fun n => f n x) L (𝓝 l) then h.choose
      else (⟨f default x⟩ : Nonempty β).some
  have h_ae_tendsto_f_lim : forallᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
    filter_upwards [h_ae_tendsto] with x hx
    simpa [f_lim, hx] using hx.choose_spec
  have hf_lim : AEMeasurable f_lim μ :=
    aemeasurable_of_tendsto_metrizable_ae L hf h_ae_tendsto_f_lim
  refine ⟨hf_lim.mk f_lim, hf_lim.measurable_mk, ?_⟩
  filter_upwards [h_ae_tendsto_f_lim, hf_lim.ae_eq_mk] with x hx h_eq
  simpa [h_eq] using hx

Depends on / 依赖: AEMeasurable, Eventually, Eventually.of_forall, Nonempty, Tendsto, choose_spec, classical, eq_or_neBot, f_lim, filter_upwards, h.choose, h_ae_tendsto, h_ae_tendsto_f_lim, hf_lim, hx.choose_spec, inhabit, measurable_mk, of_forall, tendsto_bot
-/
theorem measurable_limit_of_tendsto_metrizable_ae {ι} [Nonempty ι] {μ : Measure α}
    {f : ι -> α -> β} {L : Filter ι} [L.IsCountablyGenerated] (hf : forall n, AEMeasurable (f n) μ)
    (h_ae_tendsto : forallᵐ x ∂μ, exists l : β, Tendsto (fun n => f n x) L (𝓝 l)) :
    exists f_lim : α -> β, Measurable f_lim ∧ forallᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
  classical
  inhabit ι
  rcases eq_or_neBot L with (rfl | hL)
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, Eventually.of_forall fun x => tendsto_bot⟩
  set f_lim : α -> β := fun x =>
    if h : exists l : β, Tendsto (fun n => f n x) L (𝓝 l) then h.choose
      else (⟨f default x⟩ : Nonempty β).some
  have h_ae_tendsto_f_lim : forallᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
    filter_upwards [h_ae_tendsto] with x hx
    simpa [f_lim, hx] using hx.choose_spec
  have hf_lim : AEMeasurable f_lim μ :=
    aemeasurable_of_tendsto_metrizable_ae L hf h_ae_tendsto_f_lim
  refine ⟨hf_lim.mk f_lim, hf_lim.measurable_mk, ?_⟩
  filter_upwards [h_ae_tendsto_f_lim, hf_lim.ae_eq_mk] with x hx h_eq
  simpa [h_eq] using hx

end Limits

section TendstoIndicator

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι -> Set α}

/--
lemma `measurableSet_of_tendsto_indicator` / 引理 `measurableSet_of_tendsto_indicator`

English:
lemma measurableSet_of_tendsto_indicator
  statement: [NeBot L] (As_mble : forall i, MeasurableSet (As i))
  proof: by
  simp_rw [← measurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  exact ENNReal.measurable_of_tendsto' L As_mble
    ((tendsto_indicator_const_iff_forall_eventually L (1 : Real>=0∞)).mpr h_lim)

中文:
引理 measurableSet_of_tendsto_indicator
  结论: [NeBot L] (As_mble : 对任意 i, 可测集 (As i))
  证明: by
  simp_rw [← measurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  exact ENNReal.measurable_of_tendsto' L As_mble
    ((tendsto_indicator_const_iff_forall_eventually L (1 : Real>=0∞)).mpr h_lim)

Depends on / 依赖: As_mble, ENNReal, ENNReal.measurable_of_tendsto, h_lim, measurable_indicator_const_iff, measurable_of_tendsto, simp_rw, tendsto_indicator_const_iff_forall_eventually
-/
lemma measurableSet_of_tendsto_indicator [NeBot L] (As_mble : forall i, MeasurableSet (As i))
    (h_lim : forall x, forallᶠ i in L, x in As i ↔ x in A) :
    MeasurableSet A := by
  simp_rw [← measurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  exact ENNReal.measurable_of_tendsto' L As_mble
    ((tendsto_indicator_const_iff_forall_eventually L (1 : Real>=0∞)).mpr h_lim)

/--
lemma `nullMeasurableSet_of_tendsto_indicator` / 引理 `nullMeasurableSet_of_tendsto_indicator`

English:
lemma nullMeasurableSet_of_tendsto_indicator
  statement: [NeBot L] {μ : Measure α}
  proof: by
  simp_rw [← aemeasurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  apply aemeasurable_of_tendsto_metrizable_ae L As_mble
  simpa [tendsto_indicator_const_apply_iff_eventually] using h_lim

中文:
引理 nullMeasurableSet_of_tendsto_indicator
  结论: [NeBot L] {μ : 测度 α}
  证明: by
  simp_rw [← aemeasurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  apply aemeasurable_of_tendsto_metrizable_ae L As_mble
  simpa [tendsto_indicator_const_apply_iff_eventually] using h_lim

Depends on / 依赖: As_mble, aemeasurable_indicator_const_iff, aemeasurable_of_tendsto_metrizable_ae, h_lim, simp_rw, tendsto_indicator_const_apply_iff_eventually
-/
lemma nullMeasurableSet_of_tendsto_indicator [NeBot L] {μ : Measure α}
    (As_mble : forall i, NullMeasurableSet (As i) μ)
    (h_lim : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A) :
    NullMeasurableSet A μ := by
  simp_rw [← aemeasurable_indicator_const_iff (1 : Real>=0∞)] at As_mble ⊢
  apply aemeasurable_of_tendsto_metrizable_ae L As_mble
  simpa [tendsto_indicator_const_apply_iff_eventually] using h_lim

end TendstoIndicator
