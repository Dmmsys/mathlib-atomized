/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of functions implies that the measure is a probability measure

If a nonzero function belongs to `ℒ^p` (in particular if it is integrable) and is independent
of another function, then the space is a probability space.

-/

public section

open Filter ProbabilityTheory

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [MeasurableSpace F]

/--
lemma `MemLp.isProbabilityMeasure_of_indepFun` / 引理 `MemLp.isProbabilityMeasure_of_indepFun`

English:
lemma MemLp.isProbabilityMeasure_of_indepFun
  proof: by
  obtain ⟨c, c_pos, hc⟩ : exists (c : Real>=0), 0 < c ∧ 0 < μ {ω | c <= ‖f ω‖₊} := by
    contrapose! h'f
    have A (c : Real>=0) (hc : 0 < c) : forallᵐ ω ∂μ, ‖f ω‖₊ < c := by simpa [ae_iff] using h'f c hc
    obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n)
   

中文:
引理 MemLp.isProbabilityMeasure_of_indepFun
  证明: by
  obtain ⟨c, c_pos, hc⟩ : exists (c : Real>=0), 0 < c ∧ 0 < μ {ω | c <= ‖f ω‖₊} := by
    contrapose! h'f
    have A (c : Real>=0) (hc : 0 < c) : forallᵐ ω ∂μ, ‖f ω‖₊ < c := by simpa [ae_iff] using h'f c hc
    obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n)
   

Depends on / 依赖: StrictAnti, Tendsto, ae_all_iff, ae_iff, c_pos, contrapose, exists_seq_strictAnti_tendsto, filter_upwards, ge_of_tendsto, u_lim, u_pos
-/
lemma MemLp.isProbabilityMeasure_of_indepFun
    (f : Ω -> E) (g : Ω -> F) {p : Real>=0∞} (hp : p != 0) (hp' : p != ∞)
    (hℒp : MemLp f p μ) (h'f : ¬ (forallᵐ ω ∂μ, f ω = 0)) (hindep : f ⟂ᵢ[μ] g) :
    IsProbabilityMeasure μ := by
  obtain ⟨c, c_pos, hc⟩ : exists (c : Real>=0), 0 < c ∧ 0 < μ {ω | c <= ‖f ω‖₊} := by
    contrapose! h'f
    have A (c : Real>=0) (hc : 0 < c) : forallᵐ ω ∂μ, ‖f ω‖₊ < c := by simpa [ae_iff] using h'f c hc
    obtain ⟨u, -, u_pos, u_lim⟩ : exists u, StrictAnti u ∧ (forall (n : Nat), 0 < u n)
      ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : Real>=0)
    filter_upwards [ae_all_iff.2 (fun n => A (u n) (u_pos n))] with ω hω
    simpa using ge_of_tendsto' u_lim (fun i => (hω i).le)
  have h'c : μ {ω | c <= ‖f ω‖₊} < ∞ := hℒp.meas_ge_lt_top hp hp' c_pos.ne'
  have := hindep.measure_inter_preimage_eq_mul {x | c <= ‖x‖₊} Set.univ
    (isClosed_le continuous_const continuous_nnnorm).measurableSet MeasurableSet.univ
  simp only [Set.preimage_ofPred_eq, Set.preimage_univ, Set.inter_univ] at this
  exact ⟨(ENNReal.mul_eq_left hc.ne' h'c.ne).1 this.symm⟩


/--
lemma `Integrable.isProbabilityMeasure_of_indepFun` / 引理 `Integrable.isProbabilityMeasure_of_indepFun`

English:
lemma Integrable.isProbabilityMeasure_of_indepFun
  statement: (f : Ω -> E) (g : Ω -> F)
  proof: MemLp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hf) h'f hindep

中文:
引理 可积.isProbabilityMeasure_of_indepFun
  结论: (f : Ω -> E) (g : Ω -> F)
  证明: MemLp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hf) h'f hindep

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, MemLp.isProbabilityMeasure_of_indepFun, hindep, isProbabilityMeasure_of_indepFun, memLp_one_iff_integrable, memLp_one_iff_integrable.mpr, one_ne_top, one_ne_zero
-/
lemma Integrable.isProbabilityMeasure_of_indepFun (f : Ω -> E) (g : Ω -> F)
    (hf : Integrable f μ) (h'f : ¬ (forallᵐ ω ∂μ, f ω = 0)) (hindep : f ⟂ᵢ[μ] g) :
    IsProbabilityMeasure μ :=
  MemLp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hf) h'f hindep

end MeasureTheory
