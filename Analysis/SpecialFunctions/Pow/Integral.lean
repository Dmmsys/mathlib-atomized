/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Tactic.MoveAdd

/-!
# The integral of the real power of a nonnegative function

In this file, we give a common application of the layer cake formula ---
a representation of the integral of the p:th power of a nonnegative function `f`:
`∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt`.

A variant of the formula with measures of sets of the form `{ω | f(ω) > t}` instead of
`{ω | f(ω) ≥ t}` is also included.

Moreover, we prove that `‖x‖ ^ (-d + ε)` is locally integrable.

## Main results

* `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` and
  `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`:
  other common special cases of the layer cake formulas, stating that for a nonnegative function `f`
  and `p > 0`, we have `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) ≥ t} * tᵖ⁻¹ dt` and
  `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) > t} * tᵖ⁻¹ dt`, respectively.
* `MeasureTheory.locallyIntegrable_of_norm_le_rpow`:
  a function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

section Layercake

/--
theorem `lintegral_rpow_eq_lintegral_meas_le_mul` / 定理 `lintegral_rpow_eq_lintegral_meas_le_mul`

English:
theorem lintegral_rpow_eq_lintegral_meas_le_mul
  proof: by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : forall x : Real, ∫ t : Real in 0..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : Real => t ^ (p - 1)
  have g_nn : forallᵐ t ∂volume.restrict (Ioi (0 : Real)), 0 <= g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : Real)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble (t) (ht : 0 < t) : IntervalIntegrable g volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key]; rw [← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le]; rw [mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (measurable_const (a := p)).aemeasurable (μ := μ)
exact measurable_id.ennreal_ofReal.comp_aemeasurable (f_mble.pow aux).div_const p

中文:
定理 lintegral_rpow_eq_lintegral_meas_le_mul
  证明: by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : forall x : Real, ∫ t : Real in 0..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : Real => t ^ (p - 1)
  have g_nn : forallᵐ t ∂volume.restrict (Ioi (0 : Real)), 0 <= g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : Real)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble (t) (ht : 0 < t) : IntervalIntegrable g volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key]; rw [← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le]; rw [mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (measurable_const (a := p)).aemeasurable (μ := μ)
exact measurable_id.ennreal_ofReal.comp_aemeasurable (f_mble.pow aux).div_const p

Depends on / 依赖: MeasurableSet, Or.inl, Real.rpow_nonneg, Real.zero_rpow, filter_upwards, g_intble, g_nn, integral_rpow, measurableSet_Ioi, mem_Ioi, mem_Ioi.mp, one_lt_p, p_pos, p_pos.ne.symm, restrict, rpow_nonneg, self_mem_ae_restrict, t_pos, volume, volume.restrict
-/
theorem lintegral_rpow_eq_lintegral_meas_le_mul
    {f : α -> Real} (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : Real} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t <= f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : forall x : Real, ∫ t : Real in 0..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : Real => t ^ (p - 1)
  have g_nn : forallᵐ t ∂volume.restrict (Ioi (0 : Real)), 0 <= g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : Real)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble (t) (ht : 0 < t) : IntervalIntegrable g volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key]; rw [← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le]; rw [mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (measurable_const (a := p)).aemeasurable (μ := μ)
exact measurable_id.ennreal_ofReal.comp_aemeasurable (f_mble.pow aux).div_const p

end Layercake

section LayercakeLT

/--
theorem `lintegral_rpow_eq_lintegral_meas_lt_mul` / 定理 `lintegral_rpow_eq_lintegral_meas_lt_mul`

English:
theorem lintegral_rpow_eq_lintegral_meas_lt_mul
  proof: by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  rw [ht]

中文:
定理 lintegral_rpow_eq_lintegral_meas_lt_mul
  证明: by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  rw [ht]

Depends on / 依赖: ENNReal, ENNReal.ofReal, congr_arg, f_mble, f_nn, filter_upwards, lintegral_congr_ae, lintegral_rpow_eq_lintegral_meas_le_mul, meas_le_ae_eq_meas_lt, ofReal, p_pos, restrict, volume, volume.restrict
-/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul
    {f : α -> Real} (f_nn : 0 <=ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : Real} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  rw [ht]

end LayercakeLT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open Set Metric in
/--
lemma `integrableOn_ball_of_norm_le_rpow` / 引理 `integrableOn_ball_of_norm_le_rpow`

English:
lemma integrableOn_ball_of_norm_le_rpow
  statement: (hd : 1 <= Module.finrank Real E) {f : E -> F} {C α r : Real}
  proof: by
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := Real)
    positivity
  have hint : IntegrableOn (fun y => y ^ (Module.finrank Real E - 1) • (C * y ^ (-α))) (Ioo 0 r) := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y => y ^ ((Module.finrank Real E : Real) - 1 - α)) (Ioo 0 r) := by
      by_cases! hr : 0 < r
      · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
        linarith
      · simp [hr]
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy, _⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank Real E - 1)]; rw [← Real.rpow_add hy]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar μ] at hint
  exact Integrable.mono' hint h_meas.restrict h_decay

中文:
引理 integrableOn_ball_of_norm_le_rpow
  结论: (hd : 1 <= 模.finrank 实数 E) {f : E -> F} {C α r : 实数}
  证明: by
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := Real)
    positivity
  have hint : IntegrableOn (fun y => y ^ (Module.finrank Real E - 1) • (C * y ^ (-α))) (Ioo 0 r) := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y => y ^ ((Module.finrank Real E : Real) - 1 - α)) (Ioo 0 r) := by
      by_cases! hr : 0 < r
      · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
        linarith
      · simp [hr]
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy, _⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank Real E - 1)]; rw [← Real.rpow_add hy]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar μ] at hint
  exact Integrable.mono' hint h_meas.restrict h_decay

Depends on / 依赖: IntegrableOn, IntegrableOn.congr_fun, Module, Module.finrank, Module.nontrivial_of_finrank_pos, Nontrivial, congr_fun, const_mul, finrank, h_rpow, h_rpow.const_mul, integrableOn_Ioo_rpow_iff, intervalIntegral, intervalIntegral.integrableOn_Ioo_rpow_iff, measurableSet_Ioo, nontrivial_of_finrank_pos, smul_eq_mul
-/
lemma integrableOn_ball_of_norm_le_rpow (hd : 1 <= Module.finrank Real E) {f : E -> F} {C α r : Real}
    (hα : α < Module.finrank Real E) (h_decay : forallᵐ x ∂μ.restrict (ball 0 r), ‖f x‖ <= C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f μ) :
    IntegrableOn f (ball 0 r) μ := by
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := Real)
    positivity
  have hint : IntegrableOn (fun y => y ^ (Module.finrank Real E - 1) • (C * y ^ (-α))) (Ioo 0 r) := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y => y ^ ((Module.finrank Real E : Real) - 1 - α)) (Ioo 0 r) := by
      by_cases! hr : 0 < r
      · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
        linarith
      · simp [hr]
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy, _⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank Real E - 1)]; rw [← Real.rpow_add hy]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar μ] at hint
  exact Integrable.mono' hint h_meas.restrict h_decay

/--
theorem `locallyIntegrable_of_norm_le_rpow` / 定理 `locallyIntegrable_of_norm_le_rpow`

English:
theorem locallyIntegrable_of_norm_le_rpow
  statement: (hdim : 1 <= Module.finrank Real E) {f : E -> F} {C α : Real}
  proof: by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_ball_of_norm_le_rpow hdim hα (ae_restrict_of_ae h_decay) h_meas).mono_set
    (mem_ball_zero_iff.mpr <| hR · ·)

中文:
定理 locally整数egrable_of_norm_le_rpow
  结论: (hdim : 1 <= 模.finrank 实数 E) {f : E -> F} {C α : 实数}
  证明: by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_ball_of_norm_le_rpow hdim hα (ae_restrict_of_ae h_decay) h_meas).mono_set
    (mem_ball_zero_iff.mpr <| hR · ·)

Depends on / 依赖: ae_restrict_of_ae, exists_pos_norm_lt, hK.isBounded.exists_pos_norm_lt, hR_pos, h_decay, h_meas, integrableOn_ball_of_norm_le_rpow, isBounded, locallyIntegrable_iff, mem_ball_zero_iff, mem_ball_zero_iff.mpr, mono_set
-/
theorem locallyIntegrable_of_norm_le_rpow (hdim : 1 <= Module.finrank Real E) {f : E -> F} {C α : Real}
    (hα : α < Module.finrank Real E)
    (h_decay : forallᵐ x ∂μ, ‖f x‖ <= C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrable f μ := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_ball_of_norm_le_rpow hdim hα (ae_restrict_of_ae h_decay) h_meas).mono_set
    (mem_ball_zero_iff.mpr <| hR · ·)

end MeasureTheory
