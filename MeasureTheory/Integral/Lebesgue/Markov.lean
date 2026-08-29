/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Markov's inequality

The classical form of Markov's inequality states that for a nonnegative random variable `X` and
real number `ε > 0`, `P(X ≥ ε) ≤ E(X) / ε`. Multiplying both sides by the measure of the space gives
the measure-theoretic form:
```
μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε
```
This file proves a few variants of the inequality and other lemmas that depend on it.
-/

public section

namespace MeasureTheory

open Set Filter ENNReal Topology

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/--
theorem `lintegral_add_mul_meas_add_le_le_lintegral` / 定理 `lintegral_add_mul_meas_add_le_le_lintegral`

English:
theorem lintegral_add_mul_meas_add_le_le_lintegral
  statement: {f g : α -> Real>=0∞} (hle : f <=ᵐ[μ] g)
  proof: by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε <= g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε <= g x } := by
      rw [hφ_eq]
    _ <= ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε <= g x } := by
      gcongr
      exact hφ_le _
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε <= g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm]; rw [lintegral_indicator₀]; rw [setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ <= ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

中文:
定理 lintegral_add_mul_meas_add_le_le_lintegral
  结论: {f g : α -> 实数>=0∞} (hle : f <=ᵐ[μ] g)
  证明: by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε <= g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε <= g x } := by
      rw [hφ_eq]
    _ <= ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε <= g x } := by
      gcongr
      exact hφ_le _
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε <= g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm]; rw [lintegral_indicator₀]; rw [setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ <= ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

Depends on / 依赖: add_const, exists_measurable_le_lintegral_eq, hg.nullMeasurab, indicator, lintegral_add_left, m.nullMeasurable.measurable, measurable, measurableSet_le, nullMeasurab, nullMeasurable, setLIntegral_const
-/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α -> Real>=0∞} (hle : f <=ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : Real>=0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε <= g x } <= ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε <= g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε <= g x } := by
      rw [hφ_eq]
    _ <= ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε <= g x } := by
      gcongr
      exact hφ_le _
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε <= g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm]; rw [lintegral_indicator₀]; rw [setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ <= ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

/--
theorem `mul_meas_ge_le_lintegral₀` / 定理 `mul_meas_ge_le_lintegral₀`

English:
theorem mul_meas_ge_le_lintegral₀
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞)
  proof: by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le) hf ε

中文:
定理 mul_meas_ge_le_lintegral₀
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ) (ε : 实数>=0∞)
  证明: by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le) hf ε

Depends on / 依赖: ae_of_all, lintegral_add_mul_meas_add_le_le_lintegral, lintegral_zero, zero_add, zero_le
-/
theorem mul_meas_ge_le_lintegral₀ {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) :
    ε * μ { x | ε <= f x } <= ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le) hf ε

/--
theorem `mul_meas_ge_le_lintegral` / 定理 `mul_meas_ge_le_lintegral`

English:
theorem mul_meas_ge_le_lintegral
  given: {f : α -> Real>=0∞} (hf : Measurable f) (ε : Real>=0∞)
  proof: mul_meas_ge_le_lintegral₀ hf.aemeasurable ε

中文:
定理 mul_meas_ge_le_lintegral
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (ε : 实数>=0∞)
  证明: mul_meas_ge_le_lintegral₀ hf.aemeasurable ε

Depends on / 依赖: aemeasurable, hf.aemeasurable
-/
theorem mul_meas_ge_le_lintegral {f : α -> Real>=0∞} (hf : Measurable f) (ε : Real>=0∞) :
    ε * μ { x | ε <= f x } <= ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.aemeasurable ε

/--
lemma `meas_le_lintegral₀` / 引理 `meas_le_lintegral₀`

English:
lemma meas_le_lintegral₀
  statement: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

中文:
引理 meas_le_lintegral₀
  结论: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

Depends on / 依赖: le_trans, measure_mono, one_mul
-/
lemma meas_le_lintegral₀ {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : forall x in s, 1 <= f x) : μ s <= ∫⁻ a, f a ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

/--
lemma `lintegral_le_meas` / 引理 `lintegral_le_meas`

English:
lemma lintegral_le_meas
  given: {s : Set α} {f : α -> Real>=0∞} (hf : forall a, f a <= 1) (h'f : forall a in sᶜ, f a = 0)
  proof: by
  apply (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x in s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

中文:
引理 lintegral_le_meas
  条件: {s : 集合 α} {f : α -> 实数>=0∞} (hf : 对任意 a, f a <= 1) (h'f : 对任意 a in sᶜ, f a = 0)
  证明: by
  apply (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x in s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

Depends on / 依赖: lintegral_indicator_one_le, lintegral_mono
-/
lemma lintegral_le_meas {s : Set α} {f : α -> Real>=0∞} (hf : forall a, f a <= 1) (h'f : forall a in sᶜ, f a = 0) :
    ∫⁻ a, f a ∂μ <= μ s := by
  apply (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x in s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

/--
lemma `setLIntegral_le_meas` / 引理 `setLIntegral_le_meas`

English:
lemma setLIntegral_le_meas
  statement: {s t : Set α} (hs : MeasurableSet s)
  proof: by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a => ?_) (by simp_all)
  by_cases has : a in s <;> [by_cases hat : a in t; skip] <;> simp [*]

中文:
引理 setL整数egral_le_meas
  结论: {s t : 集合 α} (hs : 可测集 s)
  证明: by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a => ?_) (by simp_all)
  by_cases has : a in s <;> [by_cases hat : a in t; skip] <;> simp [*]

Depends on / 依赖: lintegral_indicator, lintegral_le_meas
-/
lemma setLIntegral_le_meas {s t : Set α} (hs : MeasurableSet s)
    {f : α -> Real>=0∞} (hf : forall a in s, a in t -> f a <= 1)
    (hf' : forall a in s, a ∉ t -> f a = 0) : ∫⁻ a in s, f a ∂μ <= μ t := by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a => ?_) (by simp_all)
  by_cases has : a in s <;> [by_cases hat : a in t; skip] <;> simp [*]

/--
theorem `lintegral_eq_top_of_measure_eq_top_ne_zero` / 定理 `lintegral_eq_top_of_measure_eq_top_ne_zero`

English:
theorem lintegral_eq_top_of_measure_eq_top_ne_zero
  statement: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: eq_top_iff.mpr
    calc
      ∞ = ∞ * μ { x | ∞ <= f x } := by simp [hμf]
      _ <= ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞

中文:
定理 lintegral_eq_top_of_measure_eq_top_ne_zero
  结论: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: eq_top_iff.mpr
    calc
      ∞ = ∞ * μ { x | ∞ <= f x } := by simp [hμf]
      _ <= ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr
-/
theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} != 0) : ∫⁻ x, f x ∂μ = ∞ :=
eq_top_iff.mpr
    calc
      ∞ = ∞ * μ { x | ∞ <= f x } := by simp [hμf]
      _ <= ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞

/--
theorem `setLIntegral_eq_top_of_measure_eq_top_ne_zero` / 定理 `setLIntegral_eq_top_of_measure_eq_top_ne_zero`

English:
theorem setLIntegral_eq_top_of_measure_eq_top_ne_zero
  statement: {f : α -> Real>=0∞} {s : Set α}
  proof: lintegral_eq_top_of_measure_eq_top_ne_zero hf
    mt (eq_bot_mono <| by rw [← ofPred_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf

中文:
定理 setL整数egral_eq_top_of_measure_eq_top_ne_zero
  结论: {f : α -> 实数>=0∞} {s : 集合 α}
  证明: lintegral_eq_top_of_measure_eq_top_ne_zero hf
    mt (eq_bot_mono <| by rw [← ofPred_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf

Depends on / 依赖: Measure, Measure.le_restrict_apply, eq_bot_mono, le_restrict_apply, lintegral_eq_top_of_measure_eq_top_ne_zero, ofPred_inter_eq_sep
-/
theorem setLIntegral_eq_top_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : μ ({x in s | f x = ∞}) != 0) :
    ∫⁻ x in s, f x ∂μ = ∞ :=
lintegral_eq_top_of_measure_eq_top_ne_zero hf
    mt (eq_bot_mono <| by rw [← ofPred_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf

/--
theorem `measure_eq_top_of_lintegral_ne_top` / 定理 `measure_eq_top_of_lintegral_ne_top`

English:
theorem measure_eq_top_of_lintegral_ne_top
  statement: {f : α -> Real>=0∞}
  proof: of_not_not fun h => hμf lintegral_eq_top_of_measure_eq_top_ne_zero hf h

中文:
定理 measure_eq_top_of_lintegral_ne_top
  结论: {f : α -> 实数>=0∞}
  证明: of_not_not fun h => hμf lintegral_eq_top_of_measure_eq_top_ne_zero hf h

Depends on / 依赖: lintegral_eq_top_of_measure_eq_top_ne_zero, of_not_not
-/
theorem measure_eq_top_of_lintegral_ne_top {f : α -> Real>=0∞}
    (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ != ∞) : μ {x | f x = ∞} = 0 :=
of_not_not fun h => hμf lintegral_eq_top_of_measure_eq_top_ne_zero hf h

/--
theorem `measure_eq_top_of_setLIntegral_ne_top` / 定理 `measure_eq_top_of_setLIntegral_ne_top`

English:
theorem measure_eq_top_of_setLIntegral_ne_top
  statement: {f : α -> Real>=0∞} {s : Set α}
  proof: of_not_not fun h => hμf setLIntegral_eq_top_of_measure_eq_top_ne_zero hf h

中文:
定理 measure_eq_top_of_setL整数egral_ne_top
  结论: {f : α -> 实数>=0∞} {s : 集合 α}
  证明: of_not_not fun h => hμf setLIntegral_eq_top_of_measure_eq_top_ne_zero hf h

Depends on / 依赖: of_not_not, setLIntegral_eq_top_of_measure_eq_top_ne_zero
-/
theorem measure_eq_top_of_setLIntegral_ne_top {f : α -> Real>=0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : ∫⁻ x in s, f x ∂μ != ∞) :
    μ ({x in s | f x = ∞}) = 0 :=
of_not_not fun h => hμf setLIntegral_eq_top_of_measure_eq_top_ne_zero hf h

/--
theorem `meas_ge_le_lintegral_div` / 定理 `meas_ge_le_lintegral_div`

English:
theorem meas_ge_le_lintegral_div
  statement: {f : α -> Real>=0∞} (hf : AEMeasurable f μ) {ε : Real>=0∞} (hε : ε != 0)
  proof: (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε

中文:
定理 meas_ge_le_lintegral_div
  结论: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ) {ε : 实数>=0∞} (hε : ε != 0)
  证明: (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, Or.inl, le_div_iff_mul_le, mul_comm
-/
theorem meas_ge_le_lintegral_div {f : α -> Real>=0∞} (hf : AEMeasurable f μ) {ε : Real>=0∞} (hε : ε != 0)
    (hε' : ε != ∞) : μ { x | ε <= f x } <= (∫⁻ a, f a ∂μ) / ε :=
(ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε

/--
theorem `ae_eq_of_ae_le_of_lintegral_le` / 定理 `ae_eq_of_ae_le_of_lintegral_le`

English:
theorem ae_eq_of_ae_le_of_lintegral_le
  statement: {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞)
  proof: by
  have : forall n : Nat, forallᵐ x ∂μ, g x < f x + (n : Real>=0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : Real>=0∞)⁻¹ <= g x } <= ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right]; rw [nonpos_iff_eq_zero]; rw [mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : Nat => f x + (n : Real>=0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)

中文:
定理 ae_eq_of_ae_le_of_lintegral_le
  结论: {f g : α -> 实数>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞)
  证明: by
  have : forall n : Nat, forallᵐ x ∂μ, g x < f x + (n : Real>=0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : Real>=0∞)⁻¹ <= g x } <= ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right]; rw [nonpos_iff_eq_zero]; rw [mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : Nat => f x + (n : Real>=0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)

Depends on / 依赖: ENNReal, ENNReal.cancel_of_ne, ENNReal.inv_ne_zero, ENNReal.natCast_ne_top, add_le_iff_nonpos_right, ae_all_iff, ae_iff, cancel_of_ne, hfg.mp, inv_ne_zero, lintegral_add_mul_meas_add_le_le_lintegral, mul_eq_zero, natCast_ne_top, nonpos_iff_eq_zero, not_lt, resolve_left, this.resolve_left
-/
theorem ae_eq_of_ae_le_of_lintegral_le {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞)
    (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ <= ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g := by
  have : forall n : Nat, forallᵐ x ∂μ, g x < f x + (n : Real>=0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : Real>=0∞)⁻¹ <= g x } <= ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right]; rw [nonpos_iff_eq_zero]; rw [mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : Nat => f x + (n : Real>=0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)

/--
theorem `lintegral_strict_mono_of_ae_le_of_frequently_ae_lt` / 定理 `lintegral_strict_mono_of_ae_le_of_frequently_ae_lt`

English:
theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
  statement: {f g : α -> Real>=0∞} (hg : AEMeasurable g μ)
  proof: by
  contrapose! h
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h

中文:
定理 lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
  结论: {f g : α -> 实数>=0∞} (hg : 几乎处处可测 g μ)
  证明: by
  contrapose! h
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h

Depends on / 依赖: ae_eq_of_ae_le_of_lintegral_le, contrapose, h_le
-/
theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α -> Real>=0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] g) (h : existsᵐ x ∂μ, f x != g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h

/--
theorem `lintegral_strict_mono_of_ae_le_of_ae_lt_on` / 定理 `lintegral_strict_mono_of_ae_le_of_ae_lt_on`

English:
theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on
  statement: {f g : α -> Real>=0∞} (hg : AEMeasurable g μ)
  proof: lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne

中文:
定理 lintegral_strict_mono_of_ae_le_of_ae_lt_on
  结论: {f g : α -> 实数>=0∞} (hg : 几乎处处可测 g μ)
  证明: lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne

Depends on / 依赖: and_eventually, frequently_ae_mem_iff, h_le, lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
-/
theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α -> Real>=0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] g) {s : Set α} (hμs : μ s != 0)
    (h : forallᵐ x ∂μ, x in s -> f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne

/--
theorem `lintegral_strict_mono` / 定理 `lintegral_strict_mono`

English:
theorem lintegral_strict_mono
  statement: {f g : α -> Real>=0∞} (hμ : μ != 0) (hg : AEMeasurable g μ)
  proof: by
  rw [Ne]; rw [← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h

中文:
定理 lintegral_strict_mono
  结论: {f g : α -> 实数>=0∞} (hμ : μ != 0) (hg : 几乎处处可测 g μ)
  证明: by
  rw [Ne]; rw [← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h

Depends on / 依赖: Measure, Measure.measure_univ_eq_zero, ae_le_of_ae_lt, lintegral_strict_mono_of_ae_le_of_ae_lt_on, measure_univ_eq_zero
-/
theorem lintegral_strict_mono {f g : α -> Real>=0∞} (hμ : μ != 0) (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ != ∞) (h : forallᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  rw [Ne]; rw [← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h

/--
theorem `setLIntegral_strict_mono` / 定理 `setLIntegral_strict_mono`

English:
theorem setLIntegral_strict_mono
  statement: {f g : α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s)
  proof: lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)

中文:
定理 setL整数egral_strict_mono
  结论: {f g : α -> 实数>=0∞} {s : 集合 α} (hsm : 可测集 s)
  证明: lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)

Depends on / 依赖: ae_restrict_iff, aemeasurable, hg.aemeasurable, lintegral_strict_mono
-/
theorem setLIntegral_strict_mono {f g : α -> Real>=0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s != 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ != ∞)
    (h : forallᵐ x ∂μ, x in s -> f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)

/--
theorem `ae_lt_top'` / 定理 `ae_lt_top'`

English:
theorem ae_lt_top'
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ != ∞)
  proof: by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f

中文:
定理 ae_lt_top'
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ) (h2f : ∫⁻ x, f x ∂μ != ∞)
  证明: by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f

Depends on / 依赖: ENNReal, ENNReal.not_lt_top, ae_iff, measure_eq_top_of_lintegral_ne_top, not_lt_top, simp_rw
-/
theorem ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) :
    forallᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f

/--
theorem `ae_lt_top` / 定理 `ae_lt_top`

English:
theorem ae_lt_top
  given: {f : α -> Real>=0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ != ∞)
  proof: ae_lt_top' hf.aemeasurable h2f

中文:
定理 ae_lt_top
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (h2f : ∫⁻ x, f x ∂μ != ∞)
  证明: ae_lt_top' hf.aemeasurable h2f

Depends on / 依赖: ae_lt_top, aemeasurable, hf.aemeasurable
-/
theorem ae_lt_top {f : α -> Real>=0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ != ∞) :
    forallᵐ x ∂μ, f x < ∞ :=
  ae_lt_top' hf.aemeasurable h2f

end MeasureTheory
