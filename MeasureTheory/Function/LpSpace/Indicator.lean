/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Filter.IndicatorFunction

/-!
# Indicator of a set as an element of `Lp`

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ => c)`.

## Main definitions

* `MeasureTheory.indicatorConstLp`: Indicator of a set as an element of `Lp`.
* `MeasureTheory.Lp.const`: Constant function as an element of `Lp` for a finite measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology symmDiff

variable {α E : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {μ : Measure α} [NormedAddCommGroup E]

namespace MeasureTheory

/--
theorem `exists_eLpNorm_indicator_le` / 定理 `exists_eLpNorm_indicator_le`

English:
theorem exists_eLpNorm_indicator_le
  given: (hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0)
  proof: by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 <= 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_

中文:
定理 存在_eLpNorm_indicator_le
  条件: (hp : p != ∞) (c : E) {ε : 实数>=0∞} (hε : ε != 0)
  证明: by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 <= 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, ENNReal.toReal_pos, Filter, Filter.Tendsto, Tendsto, bot_lt_iff_ne_bot, div_nonneg, eq_or_ne, p.toReal, toReal, toReal_nonneg, toReal_pos, zero_le_one, zero_lt_one
-/
theorem exists_eLpNorm_indicator_le (hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0) :
    exists η : Real>=0, 0 < η ∧ forall s : Set α, μ s <= η -> eLpNorm (s.indicator fun _ => c) p μ <= ε := by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 <= 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_le⟩ : exists η : Real>=0, 0 < η ∧ ‖c‖ₑ * (η : Real>=0∞) ^ (1 / p.toReal) <= ε := by
    have :
      Filter.Tendsto (fun x : Real>=0 => ((‖c‖₊ * x ^ (1 / p.toReal) : Real>=0) : Real>=0∞)) (𝓝 0)
        (𝓝 (0 : Real>=0)) := by
      rw [ENNReal.tendsto_coe]
      convert! (NNReal.continuousAt_rpow_const (Or.inr hp₀')).tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ := NNReal.nhds_zero_basis.eventually_iff.mp (this.eventually_le_const hε')
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine ⟨η, hη, ?_⟩
    simpa only [← ENNReal.coe_rpow_of_nonneg _ hp₀', enorm, ← ENNReal.coe_mul] using hδε' hηδ
  refine ⟨η, hη_pos, fun s hs => ?_⟩
  grw [eLpNorm_indicator_const_le, ← hη_le, hs]

section Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/--
theorem `_root_.HasCompactSupport.memLp_of_bound` / 定理 `_root_.HasCompactSupport.memLp_of_bound`

English:
theorem _root_.HasCompactSupport.memLp_of_bound
  statement: {f : X -> E} (hf : HasCompactSupport f)
  proof: by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

中文:
定理 _root_.HasCompactSupport.memLp_of_bound
  结论: {f : X -> E} (hf : HasCompactSupport f)
  证明: by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

Depends on / 依赖: hf.measure_lt_top.ne, image_eq_zero_of_notMem_tsupport, le_top, measure_lt_top, memLp_top_of_bound, mono_exponent_of_measure_support_ne_top, this.mono_exponent_of_measure_support_ne_top
-/
theorem _root_.HasCompactSupport.memLp_of_bound {f : X -> E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f p μ := by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (hf.measure_lt_top.ne) le_top

/--
theorem `_root_.HasCompactSupport.memLp_of_enorm_bound` / 定理 `_root_.HasCompactSupport.memLp_of_enorm_bound`

English:
theorem _root_.HasCompactSupport.memLp_of_enorm_bound
  statement: {f : X -> E} (hf : HasCompactSupport f)
  proof: by
  have : MemLp f ∞ μ :=
.trans_lt hC.lt_top⟩ ⟨h2f, eLpNormEssSup_le_of_ae_enorm_bound hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) hf.measure_ne_top le_top

中文:
定理 _root_.HasCompactSupport.memLp_of_enorm_bound
  结论: {f : X -> E} (hf : HasCompactSupport f)
  证明: by
  have : MemLp f ∞ μ :=
.trans_lt hC.lt_top⟩ ⟨h2f, eLpNormEssSup_le_of_ae_enorm_bound hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) hf.measure_ne_top le_top

Depends on / 依赖: eLpNormEssSup_le_of_ae_enorm_bound, hC.lt_top, hf.measure_ne_top, image_eq_zero_of_notMem_tsupport, le_top, lt_top, measure_ne_top, mono_exponent_of_measure_support_ne_top, this.mono_exponent_of_measure_support_ne_top, trans_lt
-/
theorem _root_.HasCompactSupport.memLp_of_enorm_bound {f : X -> E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) (hC : C != ⊤) :
      MemLp f p μ := by
  have : MemLp f ∞ μ :=
.trans_lt hC.lt_top⟩ ⟨h2f, eLpNormEssSup_le_of_ae_enorm_bound hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) hf.measure_ne_top le_top

/--
theorem `_root_.Continuous.memLp_of_hasCompactSupport` / 定理 `_root_.Continuous.memLp_of_hasCompactSupport`

English:
theorem _root_.Continuous.memLp_of_hasCompactSupport
  statement: [OpensMeasurableSpace X]
  proof: by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

中文:
定理 _root_.连续.memLp_of_hasCompactSupport
  结论: [OpensMeasurable空间 X]
  证明: by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

Depends on / 依赖: f.measure_lt_top.ne, hf.memLp_top_of_hasCompactSupport, image_eq_zero_of_notMem_tsupport, le_top, measure_lt_top, memLp_top_of_hasCompactSupport, mono_exponent_of_measure_support_ne_top, this.mono_exponent_of_measure_support_ne_top
-/
theorem _root_.Continuous.memLp_of_hasCompactSupport [OpensMeasurableSpace X]
    {f : X -> E} (hf : Continuous f) (h'f : HasCompactSupport f) : MemLp f p μ := by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x => image_eq_zero_of_notMem_tsupport) (h'f.measure_lt_top.ne) le_top

end Topology

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s != ∞} {c : E}

/--
Definition of `indicatorConstLp` / `indicatorConstLp` 的定义

English:
definition indicatorConstLp
  signature: (p : Real>=0∞) (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  body: MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

中文:
定义 indicatorConstLp
  签名: (p : 实数>=0∞) (hs : 可测集 s) (hμs : μ s != ∞) (c : E)
  定义体: MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

Depends on / 依赖: MemLp.toLp, Or.inr, indicator, memLp_indicator_const, s.indicator
-/
def indicatorConstLp (p : Real>=0∞) (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : Lp E p μ :=
  MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

/--
theorem `indicatorConstLp_add` / 定理 `indicatorConstLp_add`

English:
theorem indicatorConstLp_add
  given: {c' : E}
  proof: by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

中文:
定理 indicatorConstLp_add
  条件: {c' : E}
  证明: by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

Depends on / 依赖: MemLp.toLp_add, indicatorConstLp, indicator_add, simp_rw, toLp_add
-/
theorem indicatorConstLp_add {c' : E} :
    indicatorConstLp p hs hμs c + indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c + c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

/--
theorem `indicatorConstLp_sub` / 定理 `indicatorConstLp_sub`

English:
theorem indicatorConstLp_sub
  given: {c' : E}
  proof: by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

中文:
定理 indicatorConstLp_sub
  条件: {c' : E}
  证明: by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

Depends on / 依赖: MemLp.toLp_sub, indicatorConstLp, indicator_sub, simp_rw, toLp_sub
-/
theorem indicatorConstLp_sub {c' : E} :
    indicatorConstLp p hs hμs c - indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c - c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

/--
theorem `indicatorConstLp_coeFn` / 定理 `indicatorConstLp_coeFn`

English:
theorem indicatorConstLp_coeFn
  statement: ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
  proof: MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

中文:
定理 indicatorConstLp_coeFn
  结论: ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
  证明: MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

Depends on / 依赖: MemLp.coeFn_toLp, Or.inr, coeFn_toLp, memLp_indicator_const
-/
theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

/--
theorem `indicatorConstLp_coeFn_mem` / 定理 `indicatorConstLp_coeFn_mem`

English:
theorem indicatorConstLp_coeFn_mem
  statement: forallᵐ x : α ∂μ, x in s -> indicatorConstLp p hs hμs c x = c
  proof: indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

中文:
定理 indicatorConstLp_coeFn_mem
  结论: 对任意ᵐ x : α ∂μ, x in s -> indicatorConstLp p hs hμs c x = c
  证明: indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

Depends on / 依赖: Set.indicator_of_mem, hx.trans, indicatorConstLp_coeFn, indicatorConstLp_coeFn.mono, indicator_of_mem
-/
theorem indicatorConstLp_coeFn_mem : forallᵐ x : α ∂μ, x in s -> indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

/--
theorem `indicatorConstLp_coeFn_notMem` / 定理 `indicatorConstLp_coeFn_notMem`

English:
theorem indicatorConstLp_coeFn_notMem
  statement: forallᵐ x : α ∂μ, x ∉ s -> indicatorConstLp p hs hμs c x = 0
  proof: indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_notMem hxs _)

中文:
定理 indicatorConstLp_coeFn_notMem
  结论: 对任意ᵐ x : α ∂μ, x ∉ s -> indicatorConstLp p hs hμs c x = 0
  证明: indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_notMem hxs _)

Depends on / 依赖: Set.indicator_of_notMem, hx.trans, indicatorConstLp_coeFn, indicatorConstLp_coeFn.mono, indicator_of_notMem
-/
theorem indicatorConstLp_coeFn_notMem : forallᵐ x : α ∂μ, x ∉ s -> indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_notMem hxs _)

/--
theorem `norm_indicatorConstLp` / 定理 `norm_indicatorConstLp`

English:
theorem norm_indicatorConstLp
  given: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const hs hp_ne_zero hp_ne_top]; rw [ENNReal.toReal_mul]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [toReal_enorm]

中文:
定理 norm_indicatorConstLp
  条件: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const hs hp_ne_zero hp_ne_top]; rw [ENNReal.toReal_mul]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [toReal_enorm]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def, eLpNorm_congr_ae, eLpNorm_indicator_const, hp_ne_top, hp_ne_zero, indicatorConstLp_coeFn, measureReal_def, norm_def, toReal_enorm, toReal_mul, toReal_rpow
-/
theorem norm_indicatorConstLp (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const hs hp_ne_zero hp_ne_top]; rw [ENNReal.toReal_mul]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [toReal_enorm]

/--
theorem `norm_indicatorConstLp_top` / 定理 `norm_indicatorConstLp_top`

English:
theorem norm_indicatorConstLp_top
  given: (hμs_ne_zero : μ s != 0)
  proof: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero]; rw [ENNReal.toReal_top]; rw [_root_.div_zero]; rw [ENNReal.rpow_zero]; rw [mul_one]; rw [toReal_enorm]

中文:
定理 norm_indicatorConstLp_top
  条件: (hμs_ne_zero : μ s != 0)
  证明: by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero]; rw [ENNReal.toReal_top]; rw [_root_.div_zero]; rw [ENNReal.rpow_zero]; rw [mul_one]; rw [toReal_enorm]

Depends on / 依赖: ENNReal, ENNReal.rpow_zero, ENNReal.toReal_top, ENNReal.top_ne_zero, Lp.norm_def, _root_, _root_.div_zero, div_zero, eLpNorm_congr_ae, eLpNorm_indicator_const, indicatorConstLp_coeFn, mul_one, norm_def, rpow_zero, toReal_enorm, toReal_top, top_ne_zero
-/
theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s != 0) :
    ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ := by
  rw [Lp.norm_def]; rw [eLpNorm_congr_ae indicatorConstLp_coeFn]; rw [eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero]; rw [ENNReal.toReal_top]; rw [_root_.div_zero]; rw [ENNReal.rpow_zero]; rw [mul_one]; rw [toReal_enorm]

/--
theorem `norm_indicatorConstLp'` / 定理 `norm_indicatorConstLp'`

English:
theorem norm_indicatorConstLp'
  given: (hp_pos : p != 0) (hμs_pos : μ s != 0)
  proof: by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top

中文:
定理 norm_indicatorConstLp'
  条件: (hp_pos : p != 0) (hμs_pos : μ s != 0)
  证明: by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top

Depends on / 依赖: ENNReal, ENNReal.toReal_top, Real.rpow_zero, _root_, _root_.div_zero, div_zero, hp_pos, hp_top, mul_one, norm_indicatorConstLp, norm_indicatorConstLp_top, rpow_zero, toReal_top
-/
theorem norm_indicatorConstLp' (hp_pos : p != 0) (hμs_pos : μ s != 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top

/--
theorem `norm_indicatorConstLp_le` / 定理 `norm_indicatorConstLp_le`

English:
theorem norm_indicatorConstLp_le
  proof: by
  rw [indicatorConstLp]; rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _)]; rw [ofReal_norm]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [ENNReal.ofReal_toReal]
  fin

中文:
定理 norm_indicatorConstLp_le
  证明: by
  rw [indicatorConstLp]; rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _)]; rw [ofReal_norm]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [ENNReal.ofReal_toReal]
  fin

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, ENNReal.ofReal_toReal, ENNReal.toReal_le_of_le_ofReal, ENNReal.toReal_rpow, Lp.norm_toLp, eLpNorm_indicator_const_le, finiteness, indicatorConstLp, measureReal_def, norm_nonneg, norm_toLp, ofReal_mul, ofReal_norm, ofReal_toReal, toReal_le_of_le_ofReal, toReal_rpow, trans_eq
-/
theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ <= ‖c‖ * μ.real s ^ (1 / p.toReal) := by
  rw [indicatorConstLp]; rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _)]; rw [ofReal_norm]; rw [measureReal_def]; rw [ENNReal.toReal_rpow]; rw [ENNReal.ofReal_toReal]
  finiteness

/--
theorem `nnnorm_indicatorConstLp_le` / 定理 `nnnorm_indicatorConstLp_le`

English:
theorem nnnorm_indicatorConstLp_le
  proof: norm_indicatorConstLp_le

中文:
定理 nnnorm_indicatorConstLp_le
  证明: norm_indicatorConstLp_le

Depends on / 依赖: norm_indicatorConstLp_le
-/
theorem nnnorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖₊ <= ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal) :=
  norm_indicatorConstLp_le

/--
theorem `enorm_indicatorConstLp_le` / 定理 `enorm_indicatorConstLp_le`

English:
theorem enorm_indicatorConstLp_le
  proof: by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
using ENNReal.coe_le_coe.2 nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

中文:
定理 enorm_indicatorConstLp_le
  证明: by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
using ENNReal.coe_le_coe.2 nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal, Lp.enorm_def, coe_le_coe, coe_rpow_of_nonneg, coe_toNNReal, enorm_def, enorm_eq_nnnorm, nnnorm_indicatorConstLp_le
-/
theorem enorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ₑ <= ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
using ENNReal.coe_le_coe.2 nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

/--
theorem `edist_indicatorConstLp_eq_enorm` / 定理 `edist_indicatorConstLp_eq_enorm`

English:
theorem edist_indicatorConstLp_eq_enorm
  given: {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞}
  proof: by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp]; rw [eLpNorm_indicator_sub_indicator]; rw [Lp.enorm_toLp]

中文:
定理 edist_indicatorConstLp_eq_enorm
  条件: {t : 集合 α} {ht : 可测集 t} {hμt : μ t != ∞}
  证明: by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp]; rw [eLpNorm_indicator_sub_indicator]; rw [Lp.enorm_toLp]

Depends on / 依赖: Lp.edist_toLp_toLp, Lp.enorm_toLp, eLpNorm_indicator_sub_indicator, edist_toLp_toLp, enorm_toLp, finiteness, hs.symmDiff, indicatorConstLp, symmDiff
-/
theorem edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞} :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp (μ := μ) p (hs.symmDiff ht) (by finiteness) c‖ₑ := by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp]; rw [eLpNorm_indicator_sub_indicator]; rw [Lp.enorm_toLp]

/--
theorem `dist_indicatorConstLp_eq_norm` / 定理 `dist_indicatorConstLp_eq_norm`

English:
theorem dist_indicatorConstLp_eq_norm
  given: {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞}
  proof: by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

中文:
定理 dist_indicatorConstLp_eq_norm
  条件: {t : 集合 α} {ht : 可测集 t} {hμt : μ t != ∞}
  证明: by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

Depends on / 依赖: finiteness, hs.symmDiff, symmDiff
-/
theorem dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ t != ∞} :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp (μ := μ) p (hs.symmDiff ht) (by finiteness) c‖ := by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

/--
theorem `tendsto_indicatorConstLp_set` / 定理 `tendsto_indicatorConstLp_set`

English:
theorem tendsto_indicatorConstLp_set
  statement: [hp₁ : Fact (1 <= p)] {β : Type*} {l : Filter β} {t : β -> Set α}
  proof: by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p != 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert!
    tendsto_const_nhds.mul (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_

中文:
定理 tendsto_indicatorConstLp_set
  结论: [hp₁ : Fact (1 <= p)] {β : 类型} {l : 滤子 β} {t : β -> 集合 α}
  证明: by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p != 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert!
    tendsto_const_nhds.mul (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_

Depends on / 依赖: ENNReal, ENNReal.tendsto_toReal, ENNReal.toReal_eq_zero_iff, ENNReal.zero_ne_top, convert, dist_indicatorConstLp_eq_norm, norm_indicatorConstLp, one_pos, one_pos.trans_le, rpow_const, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_iff_dist_tendsto_zero, tendsto_toReal, toReal_eq_zero_iff, trans_le, zero_ne_top
-/
theorem tendsto_indicatorConstLp_set [hp₁ : Fact (1 <= p)] {β : Type*} {l : Filter β} {t : β -> Set α}
    {ht : forall b, MeasurableSet (t b)} {hμt : forall b, μ (t b) != ∞} (hp : p != ∞)
    (h : Tendsto (fun b => μ (t b ∆ s)) l (𝓝 0)) :
    Tendsto (fun b => indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p != 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert!
    tendsto_const_nhds.mul (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [ENNReal.toReal_eq_zero_iff, hp, hp₀]
  · simp

/--
theorem `continuous_indicatorConstLp_set` / 定理 `continuous_indicatorConstLp_set`

English:
theorem continuous_indicatorConstLp_set
  statement: [Fact (1 <= p)] {X : Type*} [TopologicalSpace X]
  proof: continuous_iff_continuousAt.2 fun x => tendsto_indicatorConstLp_set hp (h x)

@[simp]

中文:
定理 continuous_indicatorConstLp_set
  结论: [Fact (1 <= p)] {X : 类型} [拓扑空间 X]
  证明: continuous_iff_continuousAt.2 fun x => tendsto_indicatorConstLp_set hp (h x)

@[simp]

Depends on / 依赖: continuous_iff_continuousAt, tendsto_indicatorConstLp_set
-/
theorem continuous_indicatorConstLp_set [Fact (1 <= p)] {X : Type*} [TopologicalSpace X]
    {s : X -> Set α} {hs : forall x, MeasurableSet (s x)} {hμs : forall x, μ (s x) != ∞} (hp : p != ∞)
    (h : forall x, Tendsto (fun y => μ (s y ∆ s x)) (𝓝 x) (𝓝 0)) :
    Continuous fun x => indicatorConstLp p (hs x) (hμs x) c :=
  continuous_iff_continuousAt.2 fun x => tendsto_indicatorConstLp_set hp (h x)

@[simp]
/--
theorem `indicatorConstLp_empty` / 定理 `indicatorConstLp_empty`

English:
theorem indicatorConstLp_empty
  proof: by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]

中文:
定理 indicatorConstLp_empty
  证明: by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]

Depends on / 依赖: MemLp.toLp_zero, Set.indicator_empty, indicatorConstLp, indicator_empty, toLp_zero
-/
theorem indicatorConstLp_empty :
    indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ != ∞) c = 0 := by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]

/--
theorem `indicatorConstLp_inj` / 定理 `indicatorConstLp_inj`

English:
theorem indicatorConstLp_inj
  statement: {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s != ∞)
  proof: by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]

中文:
定理 indicatorConstLp_inj
  结论: {s t : 集合 α} (hs : 可测集 s) (hsμ : μ s != ∞)
  证明: by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]

Depends on / 依赖: MemLp.toLp_eq_toLp_iff, indicatorConstLp, indicator_const_eventuallyEq, simp_rw, toLp_eq_toLp_iff
-/
theorem indicatorConstLp_inj {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s != ∞)
    (ht : MeasurableSet t) (htμ : μ t != ∞) {c : E} (hc : c != 0) :
    indicatorConstLp p hs hsμ c = indicatorConstLp p ht htμ c ↔ s =ᵐ[μ] t := by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]

/--
theorem `memLp_add_of_disjoint` / 定理 `memLp_add_of_disjoint`

English:
theorem memLp_add_of_disjoint
  statement: {f g : α -> E} (h : Disjoint (support f) (support g))
  proof: by
  borelize E
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

中文:
定理 memLp_add_of_disjoint
  结论: {f g : α -> E} (h : Disjoint (support f) (support g))
  证明: by
  borelize E
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

Depends on / 依赖: Set.indicator_add_eq_left, Set.indicator_add_eq_right, borelize, hf.measurable, hfg.indicator, hg.measurable, indicator, indicator_add_eq_left, indicator_add_eq_right, measurable, measurableSet_support
-/
theorem memLp_add_of_disjoint {f g : α -> E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MemLp (f + g) p μ ↔ MemLp f p μ ∧ MemLp g p μ := by
  borelize E
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

/--
theorem `indicatorConstLp_disjoint_union` / 定理 `indicatorConstLp_disjoint_union`

English:
theorem indicatorConstLp_disjoint_union
  statement: {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  ext1
  grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  rw [Set.indicator_union_of_disjoint hst]; rw [Pi.add_def]

中文:
定理 indicatorConstLp_disjoint_union
  结论: {s t : 集合 α} (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  ext1
  grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  rw [Set.indicator_union_of_disjoint hst]; rw [Pi.add_def]

Depends on / 依赖: Lp.coeFn_add, Pi.add_def, Set.indicator_union_of_disjoint, add_def, coeFn_add, indicatorConstLp_coeFn, indicator_union_of_disjoint
-/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s != ∞) (hμt : μ t != ∞) (hst : Disjoint s t) (c : E) :
    indicatorConstLp p (hs.union ht) (by finiteness) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  ext1
  grw [Lp.coeFn_add, indicatorConstLp_coeFn, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
  rw [Set.indicator_union_of_disjoint hst]; rw [Pi.add_def]
end IndicatorConstLp

section const

variable (μ p)
variable [IsFiniteMeasure μ] (c : E)

/--
Definition of `Lp.const` / `Lp.const` 的定义

English:
definition Lp.const
  signature: : E ->+ Lp E p μ where
  body: ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 Lp.const
  签名: : E ->+ Lp E p μ where
  定义体: ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl
-/
protected def Lp.const : E ->+ Lp E p μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/--
lemma `Lp.coeFn_const` / 引理 `Lp.coeFn_const`

English:
lemma Lp.coeFn_const
  statement: Lp.const p μ c =ᵐ[μ] Function.const α c
  proof: AEEqFun.coeFn_const α c

中文:
引理 Lp.coeFn_const
  结论: Lp.const p μ c =ᵐ[μ] 函数.const α c
  证明: AEEqFun.coeFn_const α c

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_const, coeFn_const
-/
lemma Lp.coeFn_const : Lp.const p μ c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

/--
lemma `Lp.const_val` / 引理 `Lp.const_val`

English:
lemma Lp.const_val
  statement: (Lp.const p μ c).1 = AEEqFun.const α c
  proof: rfl

@[simp]

中文:
引理 Lp.const_val
  结论: (Lp.const p μ c).1 = AEEqFun.const α c
  证明: rfl

@[simp]
-/
@[simp] lemma Lp.const_val : (Lp.const p μ c).1 = AEEqFun.const α c := rfl

@[simp]
/--
lemma `MemLp.toLp_const` / 引理 `MemLp.toLp_const`

English:
lemma MemLp.toLp_const
  statement: MemLp.toLp _ (memLp_const c) = Lp.const p μ c
  proof: rfl

@[simp]

中文:
引理 MemLp.toLp_const
  结论: MemLp.toLp _ (memLp_const c) = Lp.const p μ c
  证明: rfl

@[simp]
-/
lemma MemLp.toLp_const : MemLp.toLp _ (memLp_const c) = Lp.const p μ c := rfl

@[simp]
/--
lemma `indicatorConstLp_univ` / 引理 `indicatorConstLp_univ`

English:
lemma indicatorConstLp_univ
  proof: by
  rw [← MemLp.toLp_const]; rw [indicatorConstLp]
  simp only [Set.indicator_univ]

中文:
引理 indicatorConstLp_univ
  证明: by
  rw [← MemLp.toLp_const]; rw [indicatorConstLp]
  simp only [Set.indicator_univ]

Depends on / 依赖: MemLp.toLp_const, Set.indicator_univ, indicatorConstLp, indicator_univ, toLp_const
-/
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← MemLp.toLp_const]; rw [indicatorConstLp]
  simp only [Set.indicator_univ]

/--
theorem `Lp.norm_const` / 定理 `Lp.norm_const`

English:
theorem Lp.norm_const
  given: [NeZero μ] (hp_zero : p != 0)
  proof: by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

中文:
定理 Lp.norm_const
  条件: [NeZero μ] (hp_zero : p != 0)
  证明: by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_toLp, MemLp.toLp_const, NeZero, NeZero.ne, eLpNorm_const, measureReal_def, norm_toLp, toLp_const, toReal_enorm, toReal_mul, toReal_rpow
-/
theorem Lp.norm_const [NeZero μ] (hp_zero : p != 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

/--
theorem `Lp.norm_const'` / 定理 `Lp.norm_const'`

English:
theorem Lp.norm_const'
  given: (hp_zero : p != 0) (hp_top : p != ∞)
  proof: by
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const'] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

中文:
定理 Lp.norm_const'
  条件: (hp_zero : p != 0) (hp_top : p != ∞)
  证明: by
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const'] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_toLp, MemLp.toLp_const, eLpNorm_const, measureReal_def, norm_toLp, toLp_const, toReal_enorm, toReal_mul, toReal_rpow
-/
theorem Lp.norm_const' (hp_zero : p != 0) (hp_top : p != ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← MemLp.toLp_const]; rw [Lp.norm_toLp]; rw [eLpNorm_const'] <;> try assumption
  rw [measureReal_def]; rw [ENNReal.toReal_mul]; rw [toReal_enorm]; rw [← ENNReal.toReal_rpow]

/--
theorem `Lp.norm_const_le` / 定理 `Lp.norm_const_le`

English:
theorem Lp.norm_const_le
  statement: ‖Lp.const p μ c‖ <= ‖c‖ * μ.real Set.univ ^ (1 / p.toReal)
  proof: by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

中文:
定理 Lp.norm_const_le
  结论: ‖Lp.const p μ c‖ <= ‖c‖ * μ.real 集合.univ ^ (1 / p.to实数)
  证明: by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

Depends on / 依赖: indicatorConstLp_univ, norm_indicatorConstLp_le
-/
theorem Lp.norm_const_le : ‖Lp.const p μ c‖ <= ‖c‖ * μ.real Set.univ ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

/--
Definition of `Lp.constₗ` / `Lp.constₗ` 的定义

English:
definition Lp.constₗ
  signature: (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  body: Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

中文:
定义 Lp.constₗ
  签名: (𝕜 : 类型) [赋范环 𝕜] [模 𝕜 E] [是BoundedSMul 𝕜 E]
  定义体: Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl
-/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    E ->ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

/-- `MeasureTheory.Lp.const` as a `ContinuousLinearMap`. -/
@[simps! apply]
/--
Definition of `Lp.constL` / `Lp.constL` 的定义

English:
definition Lp.constL
  signature: (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 <= p)]
  body: (Lp.constₗ p μ 𝕜).mkContinuous (μ.real Set.univ ^ (1 / p.toReal)) fun _ =>
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

中文:
定义 Lp.constL
  签名: (𝕜 : 类型) [赋范环 𝕜] [模 𝕜 E] [是BoundedSMul 𝕜 E] [Fact (1 <= p)]
  定义体: (Lp.constₗ p μ 𝕜).mkContinuous (μ.real Set.univ ^ (1 / p.toReal)) fun _ =>
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)
-/
protected def Lp.constL (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 <= p)] :
    E ->L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous (μ.real Set.univ ^ (1 / p.toReal)) fun _ =>
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

/--
theorem `Lp.norm_constL_le` / 定理 `Lp.norm_constL_le`

English:
theorem Lp.norm_constL_le
  statement: (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  proof: LinearMap.mkContinuous_norm_le _ (by positivity) _

中文:
定理 Lp.norm_constL_le
  结论: (𝕜 : 类型) [NontriviallyNormedField 𝕜] [赋范空间 𝕜 E]
  证明: LinearMap.mkContinuous_norm_le _ (by positivity) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, mkContinuous_norm_le
-/
theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 <= p)] :
    ‖(Lp.constL p μ 𝕜 : E ->L[𝕜] Lp E p μ)‖ <= μ.real Set.univ ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end const

namespace Lp

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α -> β}

/--
theorem `indicatorConstLp_compMeasurePreserving` / 定理 `indicatorConstLp_compMeasurePreserving`

English:
theorem indicatorConstLp_compMeasurePreserving
  statement: {s : Set β} (hs : MeasurableSet s)
  proof: rfl

中文:
定理 indicatorConstLp_compMeasurePreserving
  结论: {s : 集合 β} (hs : 可测集 s)
  证明: rfl
-/
theorem indicatorConstLp_compMeasurePreserving {s : Set β} (hs : MeasurableSet s)
    (hμs : μb s != ∞) (c : E) (hf : MeasurePreserving f μ μb) :
    Lp.compMeasurePreserving f hf (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (hs.preimage hf.measurable)
        (by rwa [hf.measure_preimage hs.nullMeasurableSet]) c :=
  rfl

end Lp

/--
theorem `indicatorConstLp_eq_toSpanSingleton_compLp` / 定理 `indicatorConstLp_eq_toSpanSingleton_compLp`

English:
theorem indicatorConstLp_eq_toSpanSingleton_compLp
  statement: {s : Set α} [NormedSpace Real E]
  proof: by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton Real x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : Real))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs

中文:
定理 indicatorConstLp_eq_toSpanSingleton_compLp
  结论: {s : 集合 α} [赋范空间 实数 E]
  证明: by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton Real x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : Real))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toSpanSingleton, ContinuousLinearMap.toSpanSingleton_apply, EventuallyEq, EventuallyEq.trans, coeFn_compLp, h_compLp, h_compLp.symm, hy_mem, indicatorConstLp, indicatorConstLp_coeFn, indicatorConstLp_coeFn.trans, simp_rw, toSpanSingleton, toSpanSingleton_apply
-/
theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace Real E]
    (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton Real x).compLp (indicatorConstLp 2 hs hμs (1 : Real)) := by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton Real x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : Real))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs (1 : Real)).mono fun y hy => ?_
  dsimp only
  rw [hy]
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hy_mem : y in s <;> simp [hy_mem]

end MeasureTheory
