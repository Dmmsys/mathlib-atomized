/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.Lp.simpleFunc`, the type of `Lp` simple functions
* `coeToLp`, the embedding of `Lp.simpleFunc E p μ` into `Lp E p μ`

## Main results

* `tendsto_approxOn_Lp_eLpNorm` (Lᵖ convergence): If `E` is a `NormedAddCommGroup` and `f` is
  measurable and `MemLp` (for `p < ∞`), then the simple functions
  `SimpleFunc.approxOn f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simpleFunc.isDenseEmbedding`: the embedding `coeToLp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simpleFunc.induction`, `Lp.induction`, `MemLp.induction`, `Integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

@[expose] public section


noncomputable section


open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Topology ENNReal MeasureTheory

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Lp approximation by simple functions -/

section Lp

variable [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {q : Real} {p : Real>=0∞}

/--
theorem `nnnorm_approxOn_le` / 定理 `nnnorm_approxOn_le`

English:
theorem nnnorm_approxOn_le
  statement: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  proof: by
  have := edist_approxOn_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this

中文:
定理 nnnorm_approxOn_le
  结论: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  证明: by
  have := edist_approxOn_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this

Depends on / 依赖: edist_approxOn_le, edist_comm, edist_nndist, mod_cast, nndist_eq_nnnorm
-/
theorem nnnorm_approxOn_le [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] (x : β) (n : Nat) :
    ‖approxOn f hf s y₀ h₀ n x - f x‖₊ <= ‖f x - y₀‖₊ := by
  have := edist_approxOn_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this

/--
theorem `norm_approxOn_y₀_le` / 定理 `norm_approxOn_y₀_le`

English:
theorem norm_approxOn_y₀_le
  statement: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  proof: by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

中文:
定理 norm_approxOn_y₀_le
  结论: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  证明: by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

Depends on / 依赖: ENNReal, ENNReal.coe_add, coe_add, edist_approxOn_y0_le, edist_eq_enorm_sub, norm_sub_rev
-/
theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] (x : β) (n : Nat) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ <= ‖f x - y₀‖ + ‖f x - y₀‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

/--
theorem `norm_approxOn_zero_le` / 定理 `norm_approxOn_zero_le`

English:
theorem norm_approxOn_zero_le
  statement: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  proof: by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

中文:
定理 norm_approxOn_zero_le
  结论: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
  证明: by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

Depends on / 依赖: ENNReal, ENNReal.coe_add, coe_add, edist_approxOn_y0_le, edist_eq_enorm_sub, norm_sub_rev
-/
theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) in s) [SeparableSpace s] (x : β) (n : Nat) :
    ‖approxOn f hf s 0 h₀ n x‖ <= ‖f x‖ + ‖f x‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n

/--
theorem `tendsto_approxOn_Lp_eLpNorm` / 定理 `tendsto_approxOn_Lp_eLpNorm`

English:
theorem tendsto_approxOn_Lp_eLpNorm
  statement: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
  proof: by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow

中文:
定理 tendsto_approxOn_Lp_eLpNorm
  结论: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
  证明: by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow

Depends on / 依赖: Tendsto, _root_, _root_.inv_pos.mpr, approxOn, continuousAt, continuous_rpow_const, continuous_rpow_const.continuousAt.tendsto.comp, convert, eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_exponent_zero, hp_ne_top, hp_zero, inv_pos, p.toReal, tendsto, tendsto_const_nhds, toReal, toReal_pos, zero_rpow_of_pos
-/
theorem tendsto_approxOn_Lp_eLpNorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] (hp_ne_top : p != ∞) {μ : Measure β}
    (hμ : forallᵐ x ∂μ, f x in closure s) (hi : eLpNorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0) := by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_ne_top]
    convert! continuous_rpow_const.continuousAt.tendsto.comp this
    simp [zero_rpow_of_pos (_root_.inv_pos.mpr hp)]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas n : Measurable fun x => ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal := by
    simpa only [← edist_eq_enorm_sub] using
      (approxOn f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.toReal) fun y =>
        (measurable_edist_right.comp hf).pow_const p.toReal
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `fun x => ‖f x - y₀‖ ^ p.toReal`
  have h_bound n :
    (fun x => ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal) <=ᵐ[μ] (‖f · - y₀‖ₑ ^ p.toReal) :=
    .of_forall fun x => rpow_le_rpow (coe_mono (nnnorm_approxOn_le hf h₀ x n)) toReal_nonneg
  -- (3) The bounding function `fun x => ‖f x - y₀‖ ^ p.toReal` has finite integral
  have h_fin : (∫⁻ a : β, ‖f a - y₀‖ₑ ^ p.toReal ∂μ) != ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_ne_top hi).ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    forallᵐ a : β ∂μ, Tendsto (‖approxOn f hf s y₀ h₀ · a - f a‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hμ] with a ha
    have : Tendsto (fun n => (approxOn f hf s y₀ h₀ n) a - f a) atTop (𝓝 (f a - f a)) :=
      (tendsto_approxOn hf h₀ ha).sub tendsto_const_nhds
    convert! continuous_rpow_const.continuousAt.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim

/--
theorem `memLp_approxOn` / 定理 `memLp_approxOn`

English:
theorem memLp_approxOn
  statement: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  proof: by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert

中文:
定理 memLp_approxOn
  结论: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  证明: by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert

Depends on / 依赖: Measurable, aemeasurable, aestronglyMea, aestronglyMeasurable, approxOn, convert, dist_eq_norm, eLpNorm, eLpNorm_add_lt_top, fun_prop, h_meas, h_meas.aemeasurable.aestronglyMea
-/
theorem memLp_approxOn [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
    (hf : MemLp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s]
    (hi₀ : MemLp (fun _ => y₀) p μ) (n : Nat) : MemLp (approxOn f fmeas s y₀ h₀ n) p μ := by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert! eLpNorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : MemLp (fun x => ‖f x - y₀‖) p μ := by
    have h_meas : Measurable fun x => ‖f x - y₀‖ := by
      simp only [← dist_eq_norm]
      fun_prop
    refine ⟨h_meas.aemeasurable.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    convert! eLpNorm_add_lt_top hf hi₀.neg with x
    simp [sub_eq_add_neg]
  have : forallᵐ x ∂μ, ‖approxOn f fmeas s y₀ h₀ n x - y₀‖ <= ‖‖f x - y₀‖ + ‖f x - y₀‖‖ := by
    filter_upwards with x
    convert! norm_approxOn_y₀_le fmeas h₀ x n using 1
    rw [Real.norm_eq_abs]; rw [abs_of_nonneg]
    positivity
  calc
    eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ <=
        eLpNorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      eLpNorm_mono_ae this
    _ < ⊤ := eLpNorm_add_lt_top hf' hf'

/--
theorem `tendsto_approxOn_range_Lp_eLpNorm` / 定理 `tendsto_approxOn_range_Lp_eLpNorm`

English:
theorem tendsto_approxOn_range_Lp_eLpNorm
  statement: [BorelSpace E] {f : β -> E} (hp_ne_top : p != ∞)
  proof: by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf

中文:
定理 tendsto_approxOn_range_Lp_eLpNorm
  结论: [BorelSpace E] {f : β -> E} (hp_ne_top : p != ∞)
  证明: by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf

Depends on / 依赖: filter_upwards, hp_ne_top, subset_closure, tendsto_approxOn_Lp_eLpNorm
-/
theorem tendsto_approxOn_range_Lp_eLpNorm [BorelSpace E] {f : β -> E} (hp_ne_top : p != ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f union {0} : Set E)]
    (hf : eLpNorm f p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f fmeas (range f union {0}) 0 (by simp) n) - f) p μ)
      atTop (𝓝 0) := by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf

/--
theorem `memLp_approxOn_range` / 定理 `memLp_approxOn_range`

English:
theorem memLp_approxOn_range
  statement: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  proof: memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n

中文:
定理 memLp_approxOn_range
  结论: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  证明: memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n

Depends on / 依赖: MemLp.zero, memLp_approxOn
-/
theorem memLp_approxOn_range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f union {0} : Set E)] (hf : MemLp f p μ) (n : Nat) :
    MemLp (approxOn f fmeas (range f union {0}) 0 (by simp) n) p μ :=
  memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n

/--
theorem `tendsto_approxOn_range_Lp` / 定理 `tendsto_approxOn_range_Lp`

English:
theorem tendsto_approxOn_range_Lp
  statement: [BorelSpace E] {f : β -> E} [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
  proof: by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

中文:
定理 tendsto_approxOn_range_Lp
  结论: [BorelSpace E] {f : β -> E} [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
  证明: by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

Depends on / 依赖: Lp.tendsto_Lp_iff_tendsto_eLpNorm, hp_ne_top, tendsto_Lp_iff_tendsto_eLpNorm, tendsto_approxOn_range_Lp_eLpNorm
-/
theorem tendsto_approxOn_range_Lp [BorelSpace E] {f : β -> E} [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f union {0} : Set E)]
    (hf : MemLp f p μ) :
    Tendsto
      (fun n =>
        (memLp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f union {0}) 0 (by simp) n))
      atTop (𝓝 (hf.toLp f)) := by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

/--
theorem `_root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt` / 定理 `_root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt`

English:
theorem _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
  statement: {E : Type*}
  proof: by
  borelize E
  let f' := hf.1.mk f
  rsuffices ⟨g, hg, g_mem⟩ : exists g : β ->ₛ E, eLpNorm (f' - ⇑g) p μ < ε ∧ MemLp g p μ
  · refine ⟨g, ?_, g_mem⟩
    suffices eLpNorm (f - ⇑g) p μ = eLpNorm (f' - ⇑g) p μ by rwa [this]
    apply eLpNorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk] with x hx
   

中文:
定理 _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
  结论: {E : 类型}
  证明: by
  borelize E
  let f' := hf.1.mk f
  rsuffices ⟨g, hg, g_mem⟩ : exists g : β ->ₛ E, eLpNorm (f' - ⇑g) p μ < ε ∧ MemLp g p μ
  · refine ⟨g, ?_, g_mem⟩
    suffices eLpNorm (f - ⇑g) p μ = eLpNorm (f' - ⇑g) p μ by rwa [this]
    apply eLpNorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk] with x hx
   

Depends on / 依赖: Measurable, Pi.sub_apply, SeparableSpace, StronglyMeasurable, StronglyMeasurable.s, ae_eq, ae_eq_mk, borelize, eLpNorm, eLpNorm_congr_ae, filter_upwards, g_mem, hf.ae_eq, measurable_mk, rsuffices, sub_apply, sub_left_inj
-/
theorem _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt {E : Type*}
    [NormedAddCommGroup E] {f : β -> E} {μ : Measure β} (hf : MemLp f p μ) (hp_ne_top : p != ∞)
    {ε : Real>=0∞} (hε : ε != 0) : exists g : β ->ₛ E, eLpNorm (f - ⇑g) p μ < ε ∧ MemLp g p μ := by
  borelize E
  let f' := hf.1.mk f
  rsuffices ⟨g, hg, g_mem⟩ : exists g : β ->ₛ E, eLpNorm (f' - ⇑g) p μ < ε ∧ MemLp g p μ
  · refine ⟨g, ?_, g_mem⟩
    suffices eLpNorm (f - ⇑g) p μ = eLpNorm (f' - ⇑g) p μ by rwa [this]
    apply eLpNorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk] with x hx
    simpa only [Pi.sub_apply, sub_left_inj] using hx
  have hf' : MemLp f' p μ := hf.ae_eq hf.1.ae_eq_mk
  have f'meas : Measurable f' := hf.1.measurable_mk
  have : SeparableSpace (range f' union {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hf.1.stronglyMeasurable_mk
  rcases ((tendsto_approxOn_range_Lp_eLpNorm hp_ne_top f'meas hf'.2).eventually <|
    gt_mem_nhds hε.bot_lt).exists with ⟨n, hn⟩
  rw [← eLpNorm_neg]; rw [neg_sub] at hn
  exact ⟨_, hn, memLp_approxOn_range f'meas hf' _⟩

end Lp

/-! ### L1 approximation by simple functions -/


section Integrable

variable [MeasurableSpace β]
variable [MeasurableSpace E] [NormedAddCommGroup E]

/--
theorem `tendsto_approxOn_L1_enorm` / 定理 `tendsto_approxOn_L1_enorm`

English:
theorem tendsto_approxOn_L1_enorm
  statement: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
  proof: by
  simpa [eLpNorm_one_eq_lintegral_enorm] using!
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using! hi)

中文:
定理 tendsto_approxOn_L1_enorm
  结论: [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
  证明: by
  simpa [eLpNorm_one_eq_lintegral_enorm] using!
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using! hi)

Depends on / 依赖: eLpNorm_one_eq_lintegral_enorm, one_ne_top, tendsto_approxOn_Lp_eLpNorm
-/
theorem tendsto_approxOn_L1_enorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] {μ : Measure β}
    (hμ : forallᵐ x ∂μ, f x in closure s) (hi : HasFiniteIntegral (fun x => f x - y₀) μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
  simpa [eLpNorm_one_eq_lintegral_enorm] using!
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using! hi)

/--
theorem `integrable_approxOn` / 定理 `integrable_approxOn`

English:
theorem integrable_approxOn
  statement: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  proof: by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n

中文:
定理 integrable_approxOn
  结论: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  证明: by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n

Depends on / 依赖: memLp_approxOn, memLp_one_iff_integrable
-/
theorem integrable_approxOn [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s]
    (hi₀ : Integrable (fun _ => y₀) μ) (n : Nat) : Integrable (approxOn f fmeas s y₀ h₀ n) μ := by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n

/--
theorem `tendsto_approxOn_range_L1_enorm` / 定理 `tendsto_approxOn_range_L1_enorm`

English:
theorem tendsto_approxOn_range_L1_enorm
  statement: [OpensMeasurableSpace E] {f : β -> E} {μ : Measure β}
  proof: by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2

中文:
定理 tendsto_approxOn_range_L1_enorm
  结论: [OpensMeasurableSpace E] {f : β -> E} {μ : Measure β}
  证明: by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2

Depends on / 依赖: filter_upwards, subset_closure, tendsto_approxOn_L1_enorm
-/
theorem tendsto_approxOn_range_L1_enorm [OpensMeasurableSpace E] {f : β -> E} {μ : Measure β}
    [SeparableSpace (range f union {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f union {0}) 0 (by simp) n x - f x‖ₑ ∂μ) atTop
      (𝓝 0) := by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2

/--
theorem `integrable_approxOn_range` / 定理 `integrable_approxOn_range`

English:
theorem integrable_approxOn_range
  statement: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  proof: integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

中文:
定理 integrable_approxOn_range
  结论: [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
  证明: integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

Depends on / 依赖: integrable_approxOn, integrable_zero
-/
theorem integrable_approxOn_range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f union {0} : Set E)] (hf : Integrable f μ) (n : Nat) :
    Integrable (approxOn f fmeas (range f union {0}) 0 (by simp) n) μ :=
  integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

end Integrable

section SimpleFuncProperties

variable [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure α} {p : Real>=0∞}



/--
theorem `exists_forall_norm_le` / 定理 `exists_forall_norm_le`

English:
theorem exists_forall_norm_le
  given: (f : α ->ₛ F)
  statement: exists C, forall x, ‖f x‖ <= C
  proof: exists_forall_le (f.map fun x => ‖x‖)

中文:
定理 exists_forall_norm_le
  条件: (f : α ->ₛ F)
  结论: 存在 C, 对任意 x, ‖f x‖ <= C
  证明: exists_forall_le (f.map fun x => ‖x‖)

Depends on / 依赖: exists_forall_le, f.map
-/
theorem exists_forall_norm_le (f : α ->ₛ F) : exists C, forall x, ‖f x‖ <= C :=
  exists_forall_le (f.map fun x => ‖x‖)

/--
theorem `memLp_zero` / 定理 `memLp_zero`

English:
theorem memLp_zero
  given: (f : α ->ₛ E) (μ : Measure α)
  statement: MemLp f 0 μ
  proof: memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable

中文:
定理 memLp_zero
  条件: (f : α ->ₛ E) (μ : Measure α)
  结论: MemLp f 0 μ
  证明: memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, f.aestronglyMeasurable, memLp_zero_iff_aestronglyMeasurable, memLp_zero_iff_aestronglyMeasurable.mpr
-/
theorem memLp_zero (f : α ->ₛ E) (μ : Measure α) : MemLp f 0 μ :=
  memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable

/--
theorem `memLp_top` / 定理 `memLp_top`

English:
theorem memLp_top
  given: (f : α ->ₛ E) (μ : Measure α)
  statement: MemLp f ∞ μ
  proof: let ⟨C, hfC⟩ := f.exists_forall_norm_le
memLp_top_of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

中文:
定理 memLp_top
  条件: (f : α ->ₛ E) (μ : Measure α)
  结论: MemLp f ∞ μ
  证明: let ⟨C, hfC⟩ := f.exists_forall_norm_le
memLp_top_of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, exists_forall_norm_le, f.aestronglyMeasurable, f.exists_forall_norm_le, memLp_top_of_bound, of_forall
-/
theorem memLp_top (f : α ->ₛ E) (μ : Measure α) : MemLp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
memLp_top_of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

/--
theorem `eLpNorm'_eq` / 定理 `eLpNorm'_eq`

English:
theorem eLpNorm'_eq
  given: {p : Real} (f : α ->ₛ F) (μ : Measure α)
  proof: by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm]; rw [h_map]; rw [lintegral_eq_lintegral]; rw [map_lintegral]

中文:
定理 eLpNorm'_eq
  条件: {p : 实数} (f : α ->ₛ F) (μ : Measure α)
  证明: by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm]; rw [h_map]; rw [lintegral_eq_lintegral]; rw [map_lintegral]
-/
protected theorem eLpNorm'_eq {p : Real} (f : α ->ₛ F) (μ : Measure α) :
    eLpNorm' f p μ = (∑ y in f.range, ‖y‖ₑ ^ p * μ (f ⁻¹' {y})) ^ (1 / p) := by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm]; rw [h_map]; rw [lintegral_eq_lintegral]; rw [map_lintegral]

/--
theorem `measure_preimage_lt_top_of_memLp` / 定理 `measure_preimage_lt_top_of_memLp`

English:
theorem measure_preimage_lt_top_of_memLp
  statement: (hp_pos : p != 0) (hp_ne_top : p != ∞) (f : α ->ₛ E)
  proof: by
  have h_fin : (f.map fun x => ‖x‖ₑ ^ p.toReal).FinMeasSupp μ := by
    refine FinMeasSupp.of_lintegral_ne_top ?_
    rw [← (f.map fun x => ‖x‖ₑ ^ p.toReal).lintegral_eq_lintegral μ]
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_pos hp_ne_top hf.eLpNorm_lt_top).ne
  have hf_fin : f.

中文:
定理 measure_preimage_lt_top_of_memLp
  结论: (hp_pos : p != 0) (hp_ne_top : p != ∞) (f : α ->ₛ E)
  证明: by
  have h_fin : (f.map fun x => ‖x‖ₑ ^ p.toReal).FinMeasSupp μ := by
    refine FinMeasSupp.of_lintegral_ne_top ?_
    rw [← (f.map fun x => ‖x‖ₑ ^ p.toReal).lintegral_eq_lintegral μ]
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_pos hp_ne_top hf.eLpNorm_lt_top).ne
  have hf_fin : f.

Depends on / 依赖: FinMeasSupp, FinMeasSupp.map_iff, FinMeasSupp.of_lintegral_ne_top, eLpNorm_lt_top, f.FinMeasSupp, f.map, h_fin, hf.eLpNorm_lt_top, hf_fin, hf_fin.meas_preimage_single, hp_ne_top, hp_pos, lintegral_eq_lintegral, lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top, map_iff, meas_preimage_single, of_lintegral_ne_top, p.toReal, rpow_eq_zero_iff_of_pos, toReal
-/
theorem measure_preimage_lt_top_of_memLp (hp_pos : p != 0) (hp_ne_top : p != ∞) (f : α ->ₛ E)
    (hf : MemLp f p μ) (y : E) (hy_ne : y != 0) : μ (f ⁻¹' {y}) < ∞ := by
  have h_fin : (f.map fun x => ‖x‖ₑ ^ p.toReal).FinMeasSupp μ := by
    refine FinMeasSupp.of_lintegral_ne_top ?_
    rw [← (f.map fun x => ‖x‖ₑ ^ p.toReal).lintegral_eq_lintegral μ]
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_pos hp_ne_top hf.eLpNorm_lt_top).ne
  have hf_fin : f.FinMeasSupp μ := by
    have {b : E} : (fun x => ‖x‖ₑ ^ p.toReal) b = 0 ↔ b = 0 := by
      simp [rpow_eq_zero_iff_of_pos (toReal_pos hp_pos hp_ne_top)]
    rwa [FinMeasSupp.map_iff this] at h_fin
  exact hf_fin.meas_preimage_singleton_ne_zero hy_ne

/--
theorem `memLp_of_finite_measure_preimage` / 定理 `memLp_of_finite_measure_preimage`

English:
theorem memLp_of_finite_measure_preimage
  statement: (p : Real>=0∞) {f : α ->ₛ E}
  proof: by
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact memLp_top f μ
  refine ⟨f.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]; rw [f.eLpNorm'_eq]
  refine ENNReal.rpow_lt_top_of_non

中文:
定理 memLp_of_finite_measure_preimage
  结论: (p : 实数>=0∞) {f : α ->ₛ E}
  证明: by
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact memLp_top f μ
  refine ⟨f.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]; rw [f.eLpNorm'_eq]
  refine ENNReal.rpow_lt_top_of_non

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, ENNReal.rpow_lt_top_of_nonneg, ENNReal.sum_lt_top.mpr, ENNReal.toReal_, ENNReal.toReal_pos, aestronglyMeasurable, eLpNorm, eLpNorm_eq_eLpNorm, f.aestronglyMeasurable, f.eLpNorm, hp_top, memLp_top, memLp_zero_iff_aestronglyMeasurable, mul_lt_top, rpow_lt_top_of_nonneg, sum_lt_top, toReal_, toReal_pos
-/
theorem memLp_of_finite_measure_preimage (p : Real>=0∞) {f : α ->ₛ E}
    (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞) : MemLp f p μ := by
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact memLp_top f μ
  refine ⟨f.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]; rw [f.eLpNorm'_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by simp) (ENNReal.sum_lt_top.mpr fun y _ => ?_).ne
  by_cases hy0 : y = 0
  · simp [hy0, ENNReal.toReal_pos hp0 hp_top]
  · refine ENNReal.mul_lt_top ?_ (hf y hy0)
    exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top

/--
theorem `memLp_iff` / 定理 `memLp_iff`

English:
theorem memLp_iff
  given: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  proof: ⟨fun h => measure_preimage_lt_top_of_memLp hp_pos hp_ne_top f h, fun h =>
    memLp_of_finite_measure_preimage p h⟩

中文:
定理 memLp_iff
  条件: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  证明: ⟨fun h => measure_preimage_lt_top_of_memLp hp_pos hp_ne_top f h, fun h =>
    memLp_of_finite_measure_preimage p h⟩

Depends on / 依赖: hp_ne_top, hp_pos, measure_preimage_lt_top_of_memLp, memLp_of_finite_measure_preimage
-/
theorem memLp_iff {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) :
    MemLp f p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_memLp hp_pos hp_ne_top f h, fun h =>
    memLp_of_finite_measure_preimage p h⟩

/--
theorem `integrable_iff` / 定理 `integrable_iff`

English:
theorem integrable_iff
  given: {f : α ->ₛ E}
  statement: Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
  proof: memLp_one_iff_integrable.symm.trans memLp_iff one_ne_zero ENNReal.coe_ne_top

中文:
定理 integrable_iff
  条件: {f : α ->ₛ E}
  结论: 整数egrable f μ ↔ 对任意 y, y != 0 -> μ (f ⁻¹' {y}) < ∞
  证明: memLp_one_iff_integrable.symm.trans memLp_iff one_ne_zero ENNReal.coe_ne_top

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, coe_ne_top, memLp_iff, memLp_one_iff_integrable, memLp_one_iff_integrable.symm.trans, one_ne_zero
-/
theorem integrable_iff {f : α ->ₛ E} : Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞ :=
memLp_one_iff_integrable.symm.trans memLp_iff one_ne_zero ENNReal.coe_ne_top

/--
theorem `memLp_iff_integrable` / 定理 `memLp_iff_integrable`

English:
theorem memLp_iff_integrable
  given: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  proof: (memLp_iff hp_pos hp_ne_top).trans integrable_iff.symm

中文:
定理 memLp_iff_integrable
  条件: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  证明: (memLp_iff hp_pos hp_ne_top).trans integrable_iff.symm

Depends on / 依赖: hp_ne_top, hp_pos, integrable_iff, integrable_iff.symm, memLp_iff
-/
theorem memLp_iff_integrable {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) :
    MemLp f p μ ↔ Integrable f μ :=
  (memLp_iff hp_pos hp_ne_top).trans integrable_iff.symm

/--
theorem `memLp_iff_finMeasSupp` / 定理 `memLp_iff_finMeasSupp`

English:
theorem memLp_iff_finMeasSupp
  given: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  proof: (memLp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm

中文:
定理 memLp_iff_finMeasSupp
  条件: {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
  证明: (memLp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm

Depends on / 依赖: finMeasSupp_iff, finMeasSupp_iff.symm, hp_ne_top, hp_pos, memLp_iff
-/
theorem memLp_iff_finMeasSupp {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) :
    MemLp f p μ ↔ f.FinMeasSupp μ :=
  (memLp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm

/--
theorem `integrable_iff_finMeasSupp` / 定理 `integrable_iff_finMeasSupp`

English:
theorem integrable_iff_finMeasSupp
  given: {f : α ->ₛ E}
  statement: Integrable f μ ↔ f.FinMeasSupp μ
  proof: integrable_iff.trans finMeasSupp_iff.symm

中文:
定理 integrable_iff_finMeasSupp
  条件: {f : α ->ₛ E}
  结论: 整数egrable f μ ↔ f.FinMeasSupp μ
  证明: integrable_iff.trans finMeasSupp_iff.symm

Depends on / 依赖: finMeasSupp_iff, finMeasSupp_iff.symm, integrable_iff, integrable_iff.trans
-/
theorem integrable_iff_finMeasSupp {f : α ->ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ :=
  integrable_iff.trans finMeasSupp_iff.symm

/--
theorem `FinMeasSupp.integrable` / 定理 `FinMeasSupp.integrable`

English:
theorem FinMeasSupp.integrable
  given: {f : α ->ₛ E} (h : f.FinMeasSupp μ)
  statement: Integrable f μ
  proof: integrable_iff_finMeasSupp.2 h

中文:
定理 FinMeasSupp.integrable
  条件: {f : α ->ₛ E} (h : f.FinMeasSupp μ)
  结论: 整数egrable f μ
  证明: integrable_iff_finMeasSupp.2 h

Depends on / 依赖: integrable_iff_finMeasSupp
-/
theorem FinMeasSupp.integrable {f : α ->ₛ E} (h : f.FinMeasSupp μ) : Integrable f μ :=
  integrable_iff_finMeasSupp.2 h

/--
theorem `integrable_pair` / 定理 `integrable_pair`

English:
theorem integrable_pair
  given: {f : α ->ₛ E} {g : α ->ₛ F}
  proof: by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair

中文:
定理 integrable_pair
  条件: {f : α ->ₛ E} {g : α ->ₛ F}
  证明: by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair

Depends on / 依赖: FinMeasSupp, FinMeasSupp.pair, integrable_iff_finMeasSupp
-/
theorem integrable_pair {f : α ->ₛ E} {g : α ->ₛ F} :
    Integrable f μ -> Integrable g μ -> Integrable (pair f g) μ := by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair

/--
theorem `memLp_of_isFiniteMeasure` / 定理 `memLp_of_isFiniteMeasure`

English:
theorem memLp_of_isFiniteMeasure
  given: (f : α ->ₛ E) (p : Real>=0∞) (μ : Measure α) [IsFiniteMeasure μ]
  proof: let ⟨C, hfC⟩ := f.exists_forall_norm_le
MemLp.of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

@[fun_prop]

中文:
定理 memLp_of_isFiniteMeasure
  条件: (f : α ->ₛ E) (p : 实数>=0∞) (μ : Measure α) [IsFiniteMeasure μ]
  证明: let ⟨C, hfC⟩ := f.exists_forall_norm_le
MemLp.of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

@[fun_prop]

Depends on / 依赖: Eventually, Eventually.of_forall, MemLp.of_bound, aestronglyMeasurable, exists_forall_norm_le, f.aestronglyMeasurable, f.exists_forall_norm_le, of_bound, of_forall
-/
theorem memLp_of_isFiniteMeasure (f : α ->ₛ E) (p : Real>=0∞) (μ : Measure α) [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
MemLp.of_bound f.aestronglyMeasurable C Eventually.of_forall hfC

@[fun_prop]
/--
theorem `integrable_of_isFiniteMeasure` / 定理 `integrable_of_isFiniteMeasure`

English:
theorem integrable_of_isFiniteMeasure
  given: [IsFiniteMeasure μ] (f : α ->ₛ E)
  statement: Integrable f μ
  proof: memLp_one_iff_integrable.mp (f.memLp_of_isFiniteMeasure 1 μ)

中文:
定理 integrable_of_isFiniteMeasure
  条件: [IsFiniteMeasure μ] (f : α ->ₛ E)
  结论: 整数egrable f μ
  证明: memLp_one_iff_integrable.mp (f.memLp_of_isFiniteMeasure 1 μ)

Depends on / 依赖: f.memLp_of_isFiniteMeasure, memLp_of_isFiniteMeasure, memLp_one_iff_integrable, memLp_one_iff_integrable.mp
-/
theorem integrable_of_isFiniteMeasure [IsFiniteMeasure μ] (f : α ->ₛ E) : Integrable f μ :=
  memLp_one_iff_integrable.mp (f.memLp_of_isFiniteMeasure 1 μ)

/--
theorem `measure_preimage_lt_top_of_integrable` / 定理 `measure_preimage_lt_top_of_integrable`

English:
theorem measure_preimage_lt_top_of_integrable
  statement: (f : α ->ₛ E) (hf : Integrable f μ) {x : E}
  proof: integrable_iff.mp hf x hx

中文:
定理 measure_preimage_lt_top_of_integrable
  结论: (f : α ->ₛ E) (hf : 整数egrable f μ) {x : E}
  证明: integrable_iff.mp hf x hx

Depends on / 依赖: integrable_iff, integrable_iff.mp
-/
theorem measure_preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E}
    (hx : x != 0) : μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx

/--
theorem `measure_support_lt_top_of_memLp` / 定理 `measure_support_lt_top_of_memLp`

English:
theorem measure_support_lt_top_of_memLp
  statement: (f : α ->ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  proof: f.measure_support_lt_top ((memLp_iff hp_ne_zero hp_ne_top).mp hf)

中文:
定理 measure_support_lt_top_of_memLp
  结论: (f : α ->ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  证明: f.measure_support_lt_top ((memLp_iff hp_ne_zero hp_ne_top).mp hf)

Depends on / 依赖: f.measure_support_lt_top, hp_ne_top, hp_ne_zero, measure_support_lt_top, memLp_iff
-/
theorem measure_support_lt_top_of_memLp (f : α ->ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) : μ (support f) < ∞ :=
  f.measure_support_lt_top ((memLp_iff hp_ne_zero hp_ne_top).mp hf)

/--
theorem `measure_support_lt_top_of_integrable` / 定理 `measure_support_lt_top_of_integrable`

English:
theorem measure_support_lt_top_of_integrable
  given: (f : α ->ₛ E) (hf : Integrable f μ)
  proof: f.measure_support_lt_top (integrable_iff.mp hf)

中文:
定理 measure_support_lt_top_of_integrable
  条件: (f : α ->ₛ E) (hf : 整数egrable f μ)
  证明: f.measure_support_lt_top (integrable_iff.mp hf)

Depends on / 依赖: f.measure_support_lt_top, integrable_iff, integrable_iff.mp, measure_support_lt_top
-/
theorem measure_support_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) :
    μ (support f) < ∞ :=
  f.measure_support_lt_top (integrable_iff.mp hf)

/--
theorem `measure_lt_top_of_memLp_indicator` / 定理 `measure_lt_top_of_memLp_indicator`

English:
theorem measure_lt_top_of_memLp_indicator
  statement: (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 0)
  proof: by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [memLp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs

中文:
定理 measure_lt_top_of_memLp_indicator
  结论: (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 0)
  证明: by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [memLp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs

Depends on / 依赖: Function, Function.support, Function.support_const, Set.inter_univ, Set.univ, finMeasSupp_iff_support, hp_ne_top, hp_pos, inter_univ, memLp_iff_finMeasSupp, support, support_const, support_indicator
-/
theorem measure_lt_top_of_memLp_indicator (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 0)
    {s : Set α} (hs : MeasurableSet s) (hcs : MemLp ((const α c).piecewise s hs (const α 0)) p μ) :
    μ s < ⊤ := by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [memLp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs

end SimpleFuncProperties

end SimpleFunc

open SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AEEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : Real>=0∞)
  (μ : Measure α)

variable (E)

/--
Definition of `simpleFunc` / `simpleFunc` 的定义

English:
definition simpleFunc
  signature: : AddSubgroup (Lp E p μ) where
  body: { f : Lp E p μ | exists s : α ->ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α ->ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro

中文:
定义 simpleFunc
  签名: : AddSubgroup (Lp E p μ) where
  定义体: { f : Lp E p μ | exists s : α ->ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α ->ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro

Depends on / 依赖: AEEqFun, AEEqFun.mk, aestronglyMeasurable, s.aestronglyMeasurable
-/
def simpleFunc : AddSubgroup (Lp E p μ) where
  carrier := { f : Lp E p μ | exists s : α ->ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α ->ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro f ⟨s, hs⟩
    use -s
    simp only [← hs, AEEqFun.neg_mk, SimpleFunc.coe_neg, AddSubgroup.coe_neg]

variable {E p μ}

namespace simpleFunc

section Instances




/--
theorem `eq'` / 定理 `eq'`

English:
theorem eq'
  given: {f g : Lp.simpleFunc E p μ}
  statement: (f : α ->ₘ[μ] E) = (g : α ->ₘ[μ] E) -> f = g
  proof: Subtype.ext ∘ Subtype.ext

中文:
定理 eq'
  条件: {f g : Lp.simpleFunc E p μ}
  结论: (f : α ->ₘ[μ] E) = (g : α ->ₘ[μ] E) -> f = g
  证明: Subtype.ext ∘ Subtype.ext
-/
protected theorem eq' {f g : Lp.simpleFunc E p μ} : (f : α ->ₘ[μ] E) = (g : α ->ₘ[μ] E) -> f = g :=
  Subtype.ext ∘ Subtype.ext

/-! Implementation note: If `Lp.simpleFunc E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simpleFunc E p μ`, would be
unnecessary. But instead, `Lp.simpleFunc E p μ` is defined as an `AddSubgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : SMul 𝕜 (Lp.simpleFunc E p μ)
  body: ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩

中文:
定义 smul
  签名: : SMul 𝕜 (Lp.simpleFunc E p μ)
  定义体: ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩
-/
protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩

attribute [local instance] simpleFunc.smul

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : 𝕜) (f : Lp.simpleFunc E p μ)
  proof: rfl

中文:
定理 coe_smul
  条件: (c : 𝕜) (f : Lp.simpleFunc E p μ)
  证明: rfl
-/
theorem coe_smul (c : 𝕜) (f : Lp.simpleFunc E p μ) :
    ((c • f : Lp.simpleFunc E p μ) : Lp E p μ) = c • (f : Lp E p μ) :=
  rfl

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/--
Definition of `module` / `module` 的定义

English:
definition module
  signature: : Module 𝕜 (Lp.simpleFunc E p μ) where
  body: by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _

中文:
定义 module
  签名: : Module 𝕜 (Lp.simpleFunc E p μ) where
  定义体: by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _
-/
protected def module : Module 𝕜 (Lp.simpleFunc E p μ) where
  one_smul f := by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _

attribute [local instance] simpleFunc.module

/--
theorem `isBoundedSMul` / 定理 `isBoundedSMul`

English:
theorem isBoundedSMul
  given: [Fact (1 <= p)]
  statement: IsBoundedSMul 𝕜 (Lp.simpleFunc E p μ)
  proof: IsBoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) :)

中文:
定理 isBoundedSMul
  条件: [Fact (1 <= p)]
  结论: IsBoundedSMul 𝕜 (Lp.simpleFunc E p μ)
  证明: IsBoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) :)
-/
protected theorem isBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp.simpleFunc E p μ) :=
  IsBoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) :)

attribute [local instance] simpleFunc.isBoundedSMul

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/--
Definition of `normedSpace` / `normedSpace` 的定义

English:
definition normedSpace
  signature: {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 <= p)]
  body: ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩

中文:
定义 normedSpace
  签名: {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 <= p)]
  定义体: ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩
-/
protected def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 <= p)] :
    NormedSpace 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩

end Instances

attribute [local instance] simpleFunc.module simpleFunc.normedSpace simpleFunc.isBoundedSMul

section ToLp

/--
Definition of `_root_.MeasureTheory.SimpleFunc.toLp` / `_root_.MeasureTheory.SimpleFunc.toLp` 的定义

English:
abbreviation _root_.MeasureTheory.SimpleFunc.toLp
  signature: (f : α ->ₛ E) (hf : MemLp f p μ)
  body: ⟨hf.toLp f, ⟨f, rfl⟩⟩

中文:
缩写 _root_.MeasureTheory.SimpleFunc.toLp
  签名: (f : α ->ₛ E) (hf : MemLp f p μ)
  定义体: ⟨hf.toLp f, ⟨f, rfl⟩⟩

Depends on / 依赖: hf.toLp
-/
abbrev _root_.MeasureTheory.SimpleFunc.toLp (f : α ->ₛ E) (hf : MemLp f p μ) : Lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩

/--
theorem `toLp_eq_toLp` / 定理 `toLp_eq_toLp`

English:
theorem toLp_eq_toLp
  given: (f : α ->ₛ E) (hf : MemLp f p μ)
  statement: (toLp f hf : Lp E p μ) = hf.toLp f
  proof: rfl

中文:
定理 toLp_eq_toLp
  条件: (f : α ->ₛ E) (hf : MemLp f p μ)
  结论: (toLp f hf : Lp E p μ) = hf.toLp f
  证明: rfl
-/
theorem toLp_eq_toLp (f : α ->ₛ E) (hf : MemLp f p μ) : (toLp f hf : Lp E p μ) = hf.toLp f :=
  rfl

/--
theorem `toLp_eq_mk` / 定理 `toLp_eq_mk`

English:
theorem toLp_eq_mk
  given: (f : α ->ₛ E) (hf : MemLp f p μ)
  proof: rfl

中文:
定理 toLp_eq_mk
  条件: (f : α ->ₛ E) (hf : MemLp f p μ)
  证明: rfl
-/
theorem toLp_eq_mk (f : α ->ₛ E) (hf : MemLp f p μ) :
    (toLp f hf : α ->ₘ[μ] E) = AEEqFun.mk f f.aestronglyMeasurable :=
  rfl

/--
theorem `toLp_zero` / 定理 `toLp_zero`

English:
theorem toLp_zero
  statement: toLp (0 : α ->ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ)
  proof: rfl

中文:
定理 toLp_zero
  结论: toLp (0 : α ->ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ)
  证明: rfl
-/
theorem toLp_zero : toLp (0 : α ->ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ) :=
  rfl

/--
theorem `toLp_add` / 定理 `toLp_add`

English:
theorem toLp_add
  given: (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: rfl

中文:
定理 toLp_add
  条件: (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: rfl
-/
theorem toLp_add (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f + g) (hf.add hg) = toLp f hf + toLp g hg :=
  rfl

/--
theorem `toLp_neg` / 定理 `toLp_neg`

English:
theorem toLp_neg
  given: (f : α ->ₛ E) (hf : MemLp f p μ)
  statement: toLp (-f) hf.neg = -toLp f hf
  proof: rfl

中文:
定理 toLp_neg
  条件: (f : α ->ₛ E) (hf : MemLp f p μ)
  结论: toLp (-f) hf.neg = -toLp f hf
  证明: rfl
-/
theorem toLp_neg (f : α ->ₛ E) (hf : MemLp f p μ) : toLp (-f) hf.neg = -toLp f hf :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toLp_sub` / 定理 `toLp_sub`

English:
theorem toLp_sub
  given: (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]

中文:
定理 toLp_sub
  条件: (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]

Depends on / 依赖: sub_eq_add_neg, toLp_add, toLp_neg
-/
theorem toLp_sub (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f - g) (hf.sub hg) = toLp f hf - toLp g hg := by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `toLp_smul` / 定理 `toLp_smul`

English:
theorem toLp_smul
  given: (f : α ->ₛ E) (hf : MemLp f p μ) (c : 𝕜)
  proof: rfl

nonrec theorem norm_toLp [Fact (1 <= p)] (f : α ->ₛ E) (hf : MemLp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ) :=
  norm_toLp f hf

中文:
定理 toLp_smul
  条件: (f : α ->ₛ E) (hf : MemLp f p μ) (c : 𝕜)
  证明: rfl

nonrec theorem norm_toLp [Fact (1 <= p)] (f : α ->ₛ E) (hf : MemLp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ) :=
  norm_toLp f hf
-/
theorem toLp_smul (f : α ->ₛ E) (hf : MemLp f p μ) (c : 𝕜) :
    toLp (c • f) (hf.const_smul c) = c • toLp f hf :=
  rfl

nonrec theorem norm_toLp [Fact (1 <= p)] (f : α ->ₛ E) (hf : MemLp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ) :=
  norm_toLp f hf

end ToLp

section ToSimpleFunc

/--
Definition of `toSimpleFunc` / `toSimpleFunc` 的定义

English:
definition toSimpleFunc
  signature: (f : Lp.simpleFunc E p μ)
  body: Classical.choose f.2

中文:
定义 toSimpleFunc
  签名: (f : Lp.simpleFunc E p μ)
  定义体: Classical.choose f.2

Depends on / 依赖: Classical, Classical.choose
-/
def toSimpleFunc (f : Lp.simpleFunc E p μ) : α ->ₛ E :=
  Classical.choose f.2

/-- `(toSimpleFunc f)` is measurable. -/
@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: [MeasurableSpace E] (f : Lp.simpleFunc E p μ)
  proof: (toSimpleFunc f).measurable

中文:
定理 measurable
  条件: [MeasurableSpace E] (f : Lp.simpleFunc E p μ)
  证明: (toSimpleFunc f).measurable
-/
protected theorem measurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    Measurable (toSimpleFunc f) :=
  (toSimpleFunc f).measurable

/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (f : Lp.simpleFunc E p μ)
  proof: (toSimpleFunc f).stronglyMeasurable

@[fun_prop]

中文:
定理 stronglyMeasurable
  条件: (f : Lp.simpleFunc E p μ)
  证明: (toSimpleFunc f).stronglyMeasurable

@[fun_prop]
-/
protected theorem stronglyMeasurable (f : Lp.simpleFunc E p μ) :
    StronglyMeasurable (toSimpleFunc f) :=
  (toSimpleFunc f).stronglyMeasurable

@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  given: [MeasurableSpace E] (f : Lp.simpleFunc E p μ)
  proof: (simpleFunc.measurable f).aemeasurable

中文:
定理 aemeasurable
  条件: [MeasurableSpace E] (f : Lp.simpleFunc E p μ)
  证明: (simpleFunc.measurable f).aemeasurable
-/
protected theorem aemeasurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    AEMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.measurable f).aemeasurable

/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: (f : Lp.simpleFunc E p μ)
  proof: (simpleFunc.stronglyMeasurable f).aestronglyMeasurable

中文:
定理 aestronglyMeasurable
  条件: (f : Lp.simpleFunc E p μ)
  证明: (simpleFunc.stronglyMeasurable f).aestronglyMeasurable
-/
protected theorem aestronglyMeasurable (f : Lp.simpleFunc E p μ) :
    AEStronglyMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.stronglyMeasurable f).aestronglyMeasurable

/--
theorem `toSimpleFunc_eq_toFun` / 定理 `toSimpleFunc_eq_toFun`

English:
theorem toSimpleFunc_eq_toFun
  given: (f : Lp.simpleFunc E p μ)
  statement: toSimpleFunc f =ᵐ[μ] f
  proof: show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α ->ₘ[μ] E) by
    convert! (AEEqFun.coeFn_mk (toSimpleFunc f) (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm

中文:
定理 toSimpleFunc_eq_toFun
  条件: (f : Lp.simpleFunc E p μ)
  结论: toSimpleFunc f =ᵐ[μ] f
  证明: show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α ->ₘ[μ] E) by
    convert! (AEEqFun.coeFn_mk (toSimpleFunc f) (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, Classical, Classical.choose_spec, aestronglyMeasurable, choose_spec, coeFn_mk, convert, toSimpleFunc
-/
theorem toSimpleFunc_eq_toFun (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f :=
  show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α ->ₘ[μ] E) by
    convert! (AEEqFun.coeFn_mk (toSimpleFunc f) (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm

/--
theorem `memLp` / 定理 `memLp`

English:
theorem memLp
  given: (f : Lp.simpleFunc E p μ)
  statement: MemLp (toSimpleFunc f) p μ
  proof: MemLp.ae_eq (toSimpleFunc_eq_toFun f).symm mem_Lp_iff_memLp.mp (f : Lp E p μ).2

中文:
定理 memLp
  条件: (f : Lp.simpleFunc E p μ)
  结论: MemLp (toSimpleFunc f) p μ
  证明: MemLp.ae_eq (toSimpleFunc_eq_toFun f).symm mem_Lp_iff_memLp.mp (f : Lp E p μ).2
-/
protected theorem memLp (f : Lp.simpleFunc E p μ) : MemLp (toSimpleFunc f) p μ :=
MemLp.ae_eq (toSimpleFunc_eq_toFun f).symm mem_Lp_iff_memLp.mp (f : Lp E p μ).2

/--
theorem `toLp_toSimpleFunc` / 定理 `toLp_toSimpleFunc`

English:
theorem toLp_toSimpleFunc
  given: (f : Lp.simpleFunc E p μ)
  proof: simpleFunc.eq' (Classical.choose_spec f.2)

中文:
定理 toLp_toSimpleFunc
  条件: (f : Lp.simpleFunc E p μ)
  证明: simpleFunc.eq' (Classical.choose_spec f.2)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, simpleFunc, simpleFunc.eq
-/
theorem toLp_toSimpleFunc (f : Lp.simpleFunc E p μ) :
    toLp (toSimpleFunc f) (simpleFunc.memLp f) = f :=
  simpleFunc.eq' (Classical.choose_spec f.2)

/--
theorem `toSimpleFunc_toLp` / 定理 `toSimpleFunc_toLp`

English:
theorem toSimpleFunc_toLp
  given: (f : α ->ₛ E) (hfi : MemLp f p μ)
  statement: toSimpleFunc (toLp f hfi) =ᵐ[μ] f
  proof: by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2

中文:
定理 toSimpleFunc_toLp
  条件: (f : α ->ₛ E) (hfi : MemLp f p μ)
  结论: toSimpleFunc (toLp f hfi) =ᵐ[μ] f
  证明: by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2

Depends on / 依赖: AEEqFun, AEEqFun.mk_eq_mk, Classical, Classical.choose_spec, choose_spec, mk_eq_mk
-/
theorem toSimpleFunc_toLp (f : α ->ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f := by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2

variable (E μ)

/--
theorem `zero_toSimpleFunc` / 定理 `zero_toSimpleFunc`

English:
theorem zero_toSimpleFunc
  statement: toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0
  proof: by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]

中文:
定理 zero_toSimpleFunc
  结论: toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0
  证明: by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]

Depends on / 依赖: Lp.coeFn_zero, Lp.simpleFunc, coeFn_zero, filter_upwards, simpleFunc, toSimpleFunc_eq_toFun
-/
theorem zero_toSimpleFunc : toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0 := by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]

variable {E μ}

/--
theorem `add_toSimpleFunc` / 定理 `add_toSimpleFunc`

English:
theorem add_toSimpleFunc
  given: (f g : Lp.simpleFunc E p μ)
  proof: by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]

中文:
定理 add_toSimpleFunc
  条件: (f g : Lp.simpleFunc E p μ)
  证明: by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_add, Lp.coeFn_add, Pi.add_apply, add_apply, coeFn_add, coe_add, filter_upwards, iterate, toSimpleFunc_eq_toFun
-/
theorem add_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]

/--
theorem `neg_toSimpleFunc` / 定理 `neg_toSimpleFunc`

English:
theorem neg_toSimpleFunc
  given: (f : Lp.simpleFunc E p μ)
  statement: toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f
  proof: by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  repeat intro h; rw [h]

中文:
定理 neg_toSimpleFunc
  条件: (f : Lp.simpleFunc E p μ)
  结论: toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f
  证明: by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  repeat intro h; rw [h]

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_neg, Lp.coeFn_neg, Pi.neg_apply, coeFn_neg, coe_neg, filter_upwards, neg_apply, repeat, toSimpleFunc_eq_toFun
-/
theorem neg_toSimpleFunc (f : Lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f := by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  repeat intro h; rw [h]

/--
theorem `sub_toSimpleFunc` / 定理 `sub_toSimpleFunc`

English:
theorem sub_toSimpleFunc
  given: (f g : Lp.simpleFunc E p μ)
  proof: by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  repeat' intro h; rw [h]

中文:
定理 sub_toSimpleFunc
  条件: (f g : Lp.simpleFunc E p μ)
  证明: by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  repeat' intro h; rw [h]

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_sub, Lp.coeFn_sub, Pi.sub_apply, coeFn_sub, coe_sub, filter_upwards, repeat, sub_apply, toSimpleFunc_eq_toFun
-/
theorem sub_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f - g) =ᵐ[μ] toSimpleFunc f - toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  repeat' intro h; rw [h]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `smul_toSimpleFunc` / 定理 `smul_toSimpleFunc`

English:
theorem smul_toSimpleFunc
  given: (k : 𝕜) (f : Lp.simpleFunc E p μ)
  proof: by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  repeat intro h; rw [h]

中文:
定理 smul_toSimpleFunc
  条件: (k : 𝕜) (f : Lp.simpleFunc E p μ)
  证明: by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  repeat intro h; rw [h]

Depends on / 依赖: Lp.coeFn_smul, Pi.smul_apply, coeFn_smul, coe_smul, filter_upwards, repeat, smul_apply, toSimpleFunc_eq_toFun
-/
theorem smul_toSimpleFunc (k : 𝕜) (f : Lp.simpleFunc E p μ) :
    toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f) := by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  repeat intro h; rw [h]

/--
theorem `norm_toSimpleFunc` / 定理 `norm_toSimpleFunc`

English:
theorem norm_toSimpleFunc
  given: [Fact (1 <= p)] (f : Lp.simpleFunc E p μ)
  proof: by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memLp f)

中文:
定理 norm_toSimpleFunc
  条件: [Fact (1 <= p)] (f : Lp.simpleFunc E p μ)
  证明: by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memLp f)

Depends on / 依赖: norm_toLp, simpleFunc, simpleFunc.memLp, toLp_toSimpleFunc, toSimpleFunc
-/
theorem norm_toSimpleFunc [Fact (1 <= p)] (f : Lp.simpleFunc E p μ) :
    ‖f‖ = ENNReal.toReal (eLpNorm (toSimpleFunc f) p μ) := by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memLp f)

end ToSimpleFunc

section Induction

variable (p) in
/--
Definition of `indicatorConst` / `indicatorConst` 的定义

English:
definition indicatorConst
  signature: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  body: toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memLp_indicator_const p hs c (Or.inr hμs))

@[simp]

中文:
定义 indicatorConst
  签名: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  定义体: toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memLp_indicator_const p hs c (Or.inr hμs))

@[simp]

Depends on / 依赖: Or.inr, SimpleFunc, SimpleFunc.const, memLp_indicator_const, piecewise
-/
def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) :
    Lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memLp_indicator_const p hs c (Or.inr hμs))

@[simp]
/--
theorem `coe_indicatorConst` / 定理 `coe_indicatorConst`

English:
theorem coe_indicatorConst
  given: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  proof: rfl

中文:
定理 coe_indicatorConst
  条件: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  证明: rfl
-/
theorem coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) :
    (↑(indicatorConst p hs hμs c) : Lp E p μ) = indicatorConstLp p hs hμs c :=
  rfl

/--
theorem `toSimpleFunc_indicatorConst` / 定理 `toSimpleFunc_indicatorConst`

English:
theorem toSimpleFunc_indicatorConst
  given: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  proof: Lp.simpleFunc.toSimpleFunc_toLp _ _

中文:
定理 toSimpleFunc_indicatorConst
  条件: {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
  证明: Lp.simpleFunc.toSimpleFunc_toLp _ _

Depends on / 依赖: Lp.simpleFunc.toSimpleFunc_toLp, simpleFunc, toSimpleFunc_toLp
-/
theorem toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) :
    toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ]
      (SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0) :=
  Lp.simpleFunc.toSimpleFunc_toLp _ _

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: (hp_pos : p != 0) (hp_ne_top : p != ∞) {P : Lp.simpleFunc E p μ -> Prop}
  proof: by
  suffices forall f : α ->ₛ E, forall hf : MemLp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  apply SimpleFunc.induction
  · intro c s hs hf
    by_cases hc : c = 0
    · convert! indicatorConst 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc

中文:
定理 induction
  结论: (hp_pos : p != 0) (hp_ne_top : p != ∞) {P : Lp.simpleFunc E p μ -> 命题}
  证明: by
  suffices forall f : α ->ₛ E, forall hf : MemLp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  apply SimpleFunc.induction
  · intro c s hs hf
    by_cases hc : c = 0
    · convert! indicatorConst 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc
-/
protected theorem induction (hp_pos : p != 0) (hp_ne_top : p != ∞) {P : Lp.simpleFunc E p μ -> Prop}
    (indicatorConst :
      forall (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add :
      forall ⦃f g : α ->ₛ E⦄,
        forall hf : MemLp f p μ,
          forall hg : MemLp g p μ,
            Disjoint (support f) (support g) ->
              P (toLp f hf) ->
                P (toLp g hg) -> P (toLp f hf + toLp g hg))
    (f : Lp.simpleFunc E p μ) : P f := by
  suffices forall f : α ->ₛ E, forall hf : MemLp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  apply SimpleFunc.induction
  · intro c s hs hf
    by_cases hc : c = 0
    · convert! indicatorConst 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc]
    exact indicatorConst c hs
      (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs hf)
  · intro f g hfg hf hg hfg'
    obtain ⟨hf', hg'⟩ : MemLp f p μ ∧ MemLp g p μ :=
      (memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable).mp hfg'
    exact add hf' hg' hfg (hf hf') (hg hg')

end Induction

section CoeToLp

variable [Fact (1 <= p)]

@[fun_prop]
/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  statement: UniformContinuous ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  proof: uniformContinuous_comap

中文:
定理 uniformContinuous
  结论: UniformContinuous ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  证明: uniformContinuous_comap
-/
protected theorem uniformContinuous : UniformContinuous ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) :=
  uniformContinuous_comap

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  statement: IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  proof: isUniformEmbedding_comap Subtype.val_injective

中文:
引理 isUniformEmbedding
  结论: IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  证明: isUniformEmbedding_comap Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, isUniformEmbedding_comap, val_injective
-/
lemma isUniformEmbedding : IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) :=
  isUniformEmbedding_comap Subtype.val_injective

/--
theorem `isUniformInducing` / 定理 `isUniformInducing`

English:
theorem isUniformInducing
  statement: IsUniformInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  proof: simpleFunc.isUniformEmbedding.isUniformInducing

中文:
定理 isUniformInducing
  结论: IsUniformInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
  证明: simpleFunc.isUniformEmbedding.isUniformInducing

Depends on / 依赖: isUniformEmbedding, isUniformInducing, simpleFunc, simpleFunc.isUniformEmbedding.isUniformInducing
-/
theorem isUniformInducing : IsUniformInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) :=
  simpleFunc.isUniformEmbedding.isUniformInducing

/--
lemma `isDenseEmbedding` / 引理 `isDenseEmbedding`

English:
lemma isDenseEmbedding
  given: (hp_ne_top : p != ∞)
  proof: by
  borelize E
  apply simpleFunc.isUniformEmbedding.isDenseEmbedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : MemLp f p μ := Lp.memLp f
  have : SeparableSpace (range f union {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine
    ⟨fun n =>
 

中文:
引理 isDenseEmbedding
  条件: (hp_ne_top : p != ∞)
  证明: by
  borelize E
  apply simpleFunc.isUniformEmbedding.isDenseEmbedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : MemLp f p μ := Lp.memLp f
  have : SeparableSpace (range f union {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine
    ⟨fun n =>
 

Depends on / 依赖: Lp.memLp, Lp.stronglyMeasurable, SeparableSpace, SimpleFunc, SimpleFunc.approxOn, SimpleFunc.memLp_approxOn_range, SimpleFunc.t, approxOn, borelize, convert, isDenseEmbedding, isUniformEmbedding, measurable, memLp_approxOn_range, mem_closure_iff_seq_limit, mem_range_self, separableSpace_range_union_singleton, simpleFunc, simpleFunc.isUniformEmbedding.isDenseEmbedding, stronglyMeasurable
-/
lemma isDenseEmbedding (hp_ne_top : p != ∞) :
    IsDenseEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) := by
  borelize E
  apply simpleFunc.isUniformEmbedding.isDenseEmbedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : MemLp f p μ := Lp.memLp f
  have : SeparableSpace (range f union {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine
    ⟨fun n =>
      toLp
        (SimpleFunc.approxOn f (Lp.stronglyMeasurable f).measurable (range f union {0}) 0 _ n)
        (SimpleFunc.memLp_approxOn_range (Lp.stronglyMeasurable f).measurable hfi' n),
      fun n => mem_range_self _, ?_⟩
  convert! SimpleFunc.tendsto_approxOn_range_Lp hp_ne_top (Lp.stronglyMeasurable f).measurable hfi'
  rw [toLp_coeFn f (Lp.memLp f)]

/--
theorem `isDenseInducing` / 定理 `isDenseInducing`

English:
theorem isDenseInducing
  given: (hp_ne_top : p != ∞)
  proof: (simpleFunc.isDenseEmbedding hp_ne_top).isDenseInducing

中文:
定理 isDenseInducing
  条件: (hp_ne_top : p != ∞)
  证明: (simpleFunc.isDenseEmbedding hp_ne_top).isDenseInducing
-/
protected theorem isDenseInducing (hp_ne_top : p != ∞) :
    IsDenseInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) :=
  (simpleFunc.isDenseEmbedding hp_ne_top).isDenseInducing

/--
theorem `denseRange` / 定理 `denseRange`

English:
theorem denseRange
  given: (hp_ne_top : p != ∞)
  proof: (simpleFunc.isDenseInducing hp_ne_top).dense

中文:
定理 denseRange
  条件: (hp_ne_top : p != ∞)
  证明: (simpleFunc.isDenseInducing hp_ne_top).dense
-/
protected theorem denseRange (hp_ne_top : p != ∞) :
    DenseRange ((↑) : Lp.simpleFunc E p μ -> Lp E p μ) :=
  (simpleFunc.isDenseInducing hp_ne_top).dense

/--
theorem `dense` / 定理 `dense`

English:
theorem dense
  given: (hp_ne_top : p != ∞)
  statement: Dense (Lp.simpleFunc E p μ : Set (Lp E p μ))
  proof: by
  simpa only [denseRange_subtype_val] using! simpleFunc.denseRange (E := E) (μ := μ) hp_ne_top

中文:
定理 dense
  条件: (hp_ne_top : p != ∞)
  结论: Dense (Lp.simpleFunc E p μ : Set (Lp E p μ))
  证明: by
  simpa only [denseRange_subtype_val] using! simpleFunc.denseRange (E := E) (μ := μ) hp_ne_top
-/
protected theorem dense (hp_ne_top : p != ∞) : Dense (Lp.simpleFunc E p μ : Set (Lp E p μ)) := by
  simpa only [denseRange_subtype_val] using! simpleFunc.denseRange (E := E) (μ := μ) hp_ne_top

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable (α E 𝕜)

/--
Definition of `coeToLp` / `coeToLp` 的定义

English:
definition coeToLp
  signature: : Lp.simpleFunc E p μ ->L[𝕜] Lp E p μ
  body: { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl }

中文:
定义 coeToLp
  签名: : Lp.simpleFunc E p μ ->L[𝕜] Lp E p μ
  定义体: { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: AddSubgroup, AddSubgroup.subtype, Lp.simpleFunc, map_smul, simpleFunc, subtype
-/
def coeToLp : Lp.simpleFunc E p μ ->L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl }

end CoeToLp

section Order

variable {G : Type*} [NormedAddCommGroup G]

/--
theorem `coeFn_le` / 定理 `coeFn_le`

English:
theorem coeFn_le
  given: [PartialOrder G] (f g : Lp.simpleFunc G p μ)
  statement: (f : α -> G) <=ᵐ[μ] g ↔ f <= g
  proof: by
  rw [← Subtype.coe_le_coe]; rw [← Lp.coeFn_le]

中文:
定理 coeFn_le
  条件: [PartialOrder G] (f g : Lp.simpleFunc G p μ)
  结论: (f : α -> G) <=ᵐ[μ] g ↔ f <= g
  证明: by
  rw [← Subtype.coe_le_coe]; rw [← Lp.coeFn_le]

Depends on / 依赖: Lp.coeFn_le, Subtype, Subtype.coe_le_coe, coeFn_le, coe_le_coe
-/
theorem coeFn_le [PartialOrder G] (f g : Lp.simpleFunc G p μ) : (f : α -> G) <=ᵐ[μ] g ↔ f <= g := by
  rw [← Subtype.coe_le_coe]; rw [← Lp.coeFn_le]

variable (p μ G)

/--
theorem `coeFn_zero` / 定理 `coeFn_zero`

English:
theorem coeFn_zero
  statement: (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α -> G)
  proof: Lp.coeFn_zero _ _ _

中文:
定理 coeFn_zero
  结论: (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α -> G)
  证明: Lp.coeFn_zero _ _ _

Depends on / 依赖: Lp.coeFn_zero, coeFn_zero
-/
theorem coeFn_zero : (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α -> G) :=
  Lp.coeFn_zero _ _ _

variable {p μ G}

variable [PartialOrder G]

/--
theorem `coeFn_nonneg` / 定理 `coeFn_nonneg`

English:
theorem coeFn_nonneg
  given: (f : Lp.simpleFunc G p μ)
  statement: (0 : α -> G) <=ᵐ[μ] f ↔ 0 <= f
  proof: by
  rw [← Subtype.coe_le_coe]; rw [Lp.coeFn_nonneg]; rw [AddSubmonoid.coe_zero]

中文:
定理 coeFn_nonneg
  条件: (f : Lp.simpleFunc G p μ)
  结论: (0 : α -> G) <=ᵐ[μ] f ↔ 0 <= f
  证明: by
  rw [← Subtype.coe_le_coe]; rw [Lp.coeFn_nonneg]; rw [AddSubmonoid.coe_zero]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_zero, Lp.coeFn_nonneg, Subtype, Subtype.coe_le_coe, coeFn_nonneg, coe_le_coe, coe_zero
-/
theorem coeFn_nonneg (f : Lp.simpleFunc G p μ) : (0 : α -> G) <=ᵐ[μ] f ↔ 0 <= f := by
  rw [← Subtype.coe_le_coe]; rw [Lp.coeFn_nonneg]; rw [AddSubmonoid.coe_zero]

/--
theorem `exists_simpleFunc_nonneg_ae_eq` / 定理 `exists_simpleFunc_nonneg_ae_eq`

English:
theorem exists_simpleFunc_nonneg_ae_eq
  given: {f : Lp.simpleFunc G p μ} (hf : 0 <= f)
  proof: by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  change 0 <=ᵐ[μ] g at hf
  classical
  refine ⟨g.map ({x : G | 0 <= x}.piecewise id 0), fun x => ?_, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  · simpa using! Set.indicator_apply_nonneg id
  · filter_upwards [hf] with x (hx : 0 <= g x)
.symm simpa using! Set.i

中文:
定理 exists_simpleFunc_nonneg_ae_eq
  条件: {f : Lp.simpleFunc G p μ} (hf : 0 <= f)
  证明: by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  change 0 <=ᵐ[μ] g at hf
  classical
  refine ⟨g.map ({x : G | 0 <= x}.piecewise id 0), fun x => ?_, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  · simpa using! Set.indicator_apply_nonneg id
  · filter_upwards [hf] with x (hx : 0 <= g x)
.symm simpa using! Set.i

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_mk, Set.indicator_apply_nonneg, Set.indicator_of_mem, classical, coeFn_mk, filter_upwards, g.map, indicator_apply_nonneg, indicator_of_mem, piecewise
-/
theorem exists_simpleFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 <= f) :
    exists f' : α ->ₛ G, 0 <= f' ∧ f =ᵐ[μ] f' := by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  change 0 <=ᵐ[μ] g at hf
  classical
  refine ⟨g.map ({x : G | 0 <= x}.piecewise id 0), fun x => ?_, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  · simpa using! Set.indicator_apply_nonneg id
  · filter_upwards [hf] with x (hx : 0 <= g x)
.symm simpa using! Set.indicator_of_mem hx id

variable (p μ G)

/--
Definition of `coeSimpleFuncNonnegToLpNonneg` / `coeSimpleFuncNonnegToLpNonneg` 的定义

English:
definition coeSimpleFuncNonnegToLpNonneg
  signature: :
  body: fun g => ⟨g, g.2⟩

中文:
定义 coeSimpleFuncNonnegToLpNonneg
  签名: :
  定义体: fun g => ⟨g, g.2⟩
-/
def coeSimpleFuncNonnegToLpNonneg :
    { g : Lp.simpleFunc G p μ // 0 <= g } -> { g : Lp G p μ // 0 <= g } := fun g => ⟨g, g.2⟩

/--
theorem `denseRange_coeSimpleFuncNonnegToLpNonneg` / 定理 `denseRange_coeSimpleFuncNonnegToLpNonneg`

English:
theorem denseRange_coeSimpleFuncNonnegToLpNonneg
  given: [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
  proof: fun g => by
  borelize G
  rw [mem_closure_iff_seq_limit]
  have hg_memLp : MemLp (g : α -> G) p μ := Lp.memLp (g : Lp G p μ)
  have zero_mem : (0 : G) in (range (g : α -> G) union {0} : Set G) inter { y | 0 <= y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, true_or,
      m

中文:
定理 denseRange_coeSimpleFuncNonnegToLpNonneg
  条件: [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
  证明: fun g => by
  borelize G
  rw [mem_closure_iff_seq_limit]
  have hg_memLp : MemLp (g : α -> G) p μ := Lp.memLp (g : Lp G p μ)
  have zero_mem : (0 : G) in (range (g : α -> G) union {0} : Set G) inter { y | 0 <= y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, true_or,
      m

Depends on / 依赖: IsSeparable, IsSeparable.mono, IsSeparable.separableSpace, Lp.memLp, Lp.s, SeparableSpace, Set.inter_subset_left, and_self_iff, borelize, hg_memLp, inter_subset_left, le_refl, mem_closure_iff_seq_limit, mem_insert_iff, mem_inter_iff, mem_ofPred_eq, separableSpace, true_or, union_singleton, zero_mem
-/
theorem denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 <= p)] (hp_ne_top : p != ∞) :
    DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G) := fun g => by
  borelize G
  rw [mem_closure_iff_seq_limit]
  have hg_memLp : MemLp (g : α -> G) p μ := Lp.memLp (g : Lp G p μ)
  have zero_mem : (0 : G) in (range (g : α -> G) union {0} : Set G) inter { y | 0 <= y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, true_or,
      mem_ofPred_eq, le_refl, and_self_iff]
  have : SeparableSpace ((range (g : α -> G) union {0}) inter { y | 0 <= y } : Set G) := by
    apply IsSeparable.separableSpace
    apply IsSeparable.mono _ Set.inter_subset_left
    exact
      (Lp.stronglyMeasurable (g : Lp G p μ)).isSeparable_range.union
        (finite_singleton _).isSeparable
  have g_meas : Measurable (g : α -> G) := (Lp.stronglyMeasurable (g : Lp G p μ)).measurable
  let x n := SimpleFunc.approxOn (g : α -> G) g_meas
    ((range (g : α -> G) union {0}) inter { y | 0 <= y }) 0 zero_mem n
  have hx_nonneg : forall n, 0 <= x n := by
    intro n a
    change x n a in { y : G | 0 <= y }
    have A : (range (g : α -> G) union {0} : Set G) inter { y | 0 <= y } subseteq { y | 0 <= y } :=
      inter_subset_right
    apply A
    exact SimpleFunc.approxOn_mem g_meas _ n a
  have hx_memLp : forall n, MemLp (x n) p μ :=
    SimpleFunc.memLp_approxOn _ hg_memLp _ ⟨aestronglyMeasurable_const, by simp⟩
  have h_toLp := fun n => MemLp.coeFn_toLp (hx_memLp n)
  have hx_nonneg_Lp : forall n, 0 <= toLp (x n) (hx_memLp n) := by
    intro n
    rw [← Lp.simpleFunc.coeFn_le]; rw [Lp.simpleFunc.toLp_eq_toLp]
    filter_upwards [Lp.simpleFunc.coeFn_zero p μ G, h_toLp n] with a ha0 ha_toLp
    rw [ha0]; rw [ha_toLp]
    exact hx_nonneg n a
  have hx_tendsto :
      Tendsto (fun n : Nat => eLpNorm ((x n : α -> G) - (g : α -> G)) p μ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm g_meas zero_mem hp_ne_top
    · have hg_nonneg : (0 : α -> G) <=ᵐ[μ] g := (Lp.coeFn_nonneg _).mpr g.2
      refine hg_nonneg.mono fun a ha => subset_closure ?_
      simpa using ha
    · simp_rw [sub_zero]; finiteness
  refine
    ⟨fun n =>
      (coeSimpleFuncNonnegToLpNonneg p μ G) ⟨toLp (x n) (hx_memLp n), hx_nonneg_Lp n⟩,
      fun n => mem_range_self _, ?_⟩
  suffices Tendsto (fun n : Nat => (toLp (x n) (hx_memLp n) : Lp G p μ)) atTop (𝓝 (g : Lp G p μ)) by
    rw [tendsto_iff_dist_tendsto_zero] at this ⊢
    simp_rw [Subtype.dist_eq]
    exact this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine Filter.Tendsto.congr (fun n => eLpNorm_congr_ae (EventuallyEq.sub ?_ ?_)) hx_tendsto
  · symm
    rw [Lp.simpleFunc.toLp_eq_toLp]
    exact h_toLp n
  · rfl

end Order

end simpleFunc

end Lp

variable [MeasurableSpace α] [NormedAddCommGroup E] {f : α -> E} {p : Real>=0∞} {μ : Measure α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_elim]
/--
theorem `Lp.induction` / 定理 `Lp.induction`

English:
theorem Lp.induction
  statement: [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : Lp E p μ -> Prop)
  proof: by
  refine fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f isClosed ?_
  refine Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top ?_ ?_
  · exact fun c s => indicatorConst c
  · exact fun f g hf hg => add hf hg

中文:
定理 Lp.induction
  结论: [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : Lp E p μ -> 命题)
  证明: by
  refine fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f isClosed ?_
  refine Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top ?_ ?_
  · exact fun c s => indicatorConst c
  · exact fun f g hf hg => add hf hg

Depends on / 依赖: Lp.simpleFunc.denseRange, Lp.simpleFunc.induction, _i.elim, denseRange, hp_ne_top, indicatorConst, induction_on, isClosed, lt_of_lt_of_le, simpleFunc, zero_lt_one
-/
theorem Lp.induction [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : Lp E p μ -> Prop)
    (indicatorConst : forall (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
      motive (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add : forall ⦃f g⦄, forall hf : MemLp f p μ, forall hg : MemLp g p μ, Disjoint (support f) (support g) ->
      motive (hf.toLp f) -> motive (hg.toLp g) -> motive (hf.toLp f + hg.toLp g))
    (isClosed : IsClosed { f : Lp E p μ | motive f }) : forall f : Lp E p μ, motive f := by
  refine fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f isClosed ?_
  refine Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top ?_ ?_
  · exact fun c s => indicatorConst c
  · exact fun f g hf hg => add hf hg

/-- To prove something for an arbitrary `MemLp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
/--
theorem `MemLp.induction` / 定理 `MemLp.induction`

English:
theorem MemLp.induction
  statement: [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : (α -> E) -> Prop)
  proof: by
  have : forall f : SimpleFunc α E, MemLp f p μ -> motive f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert! indicator 0 MeasurableSet.empty (by simp) using 1; ext; simp
      have hp_pos : p != 0 := (lt_of_lt_of_le zero_lt_one _i.elim

中文:
定理 MemLp.induction
  结论: [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : (α -> E) -> 命题)
  证明: by
  have : forall f : SimpleFunc α E, MemLp f p μ -> motive f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert! indicator 0 MeasurableSet.empty (by simp) using 1; ext; simp
      have hp_pos : p != 0 := (lt_of_lt_of_le zero_lt_one _i.elim

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, SimpleFunc, SimpleFunc.coe_add, SimpleFunc.induction, SimpleFunc.measure_lt_top_of_memLp_indicator, _i.elim, coe_add, convert, f.stronglyMeasurable, g.stronglyMeasurable, hp_ne_top, hp_pos, indicator, int_fg, lt_of_lt_of_le, measure_lt_top_of_memLp_indicator, memLp_add_of_disjoint, motive, stronglyMeasurable
-/
theorem MemLp.induction [_i : Fact (1 <= p)] (hp_ne_top : p != ∞) (motive : (α -> E) -> Prop)
    (indicator : forall (c : E) ⦃s⦄, MeasurableSet s -> μ s < ∞ -> motive (s.indicator fun _ => c))
    (add : forall ⦃f g : α -> E⦄, Disjoint (support f) (support g) -> MemLp f p μ -> MemLp g p μ ->
      motive f -> motive g -> motive (f + g))
    (closed : IsClosed { f : Lp E p μ | motive f })
    (ae : forall ⦃f g⦄, f =ᵐ[μ] g -> MemLp f p μ -> motive f -> motive g) :
    forall ⦃f : α -> E⦄, MemLp f p μ -> motive f := by
  have : forall f : SimpleFunc α E, MemLp f p μ -> motive f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert! indicator 0 MeasurableSet.empty (by simp) using 1; ext; simp
      have hp_pos : p != 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne'
      exact indicator c hs (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs h)
    · intro f g hfg hf hg int_fg
      rw [SimpleFunc.coe_add]; rw [memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable] at int_fg
      exact add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)
  have : forall f : Lp.simpleFunc E p μ, motive f := by
    intro f
    exact
      ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f) (Lp.simpleFunc.memLp f)
        (this (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.memLp f))
  have : forall f : Lp E p μ, motive f := fun f =>
    (Lp.simpleFunc.denseRange hp_ne_top).induction_on f closed this
  exact fun f hf => ae hf.coeFn_toLp (Lp.memLp _) (this (hf.toLp f))

/--
theorem `MemLp.induction_dense` / 定理 `MemLp.induction_dense`

English:
theorem MemLp.induction_dense
  statement: (hp_ne_top : p != ∞) (P : (α -> E) -> Prop)
  proof: by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp, Pg⟩
  suffices H : forall (f' : α ->ₛ E) (δ : Real>=0∞) (hδ : δ != 0), MemLp f' p μ ->
      exists g, eLpNorm (⇑f' - 

中文:
定理 MemLp.induction_dense
  结论: (hp_ne_top : p != ∞) (P : (α -> E) -> 命题)
  证明: by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp, Pg⟩
  suffices H : forall (f' : α ->ₛ E) (δ : Real>=0∞) (hδ : δ != 0), MemLp f' p μ ->
      exists g, eLpNorm (⇑f' - 

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, _mem, eLpNorm, eq_or_ne, exists_Lp_half, exists_simpleFunc_eLpNorm_sub_lt, hf.exists_simpleFunc_eLpNorm_sub_lt, hp_ne_top, hp_pos, measure_empty, pos.ne, zero_lt_top
-/
theorem MemLp.induction_dense (hp_ne_top : p != ∞) (P : (α -> E) -> Prop)
    (h0P :
      forall (c : E) ⦃s : Set α⦄,
        MeasurableSet s ->
          μ s < ∞ ->
            forall {ε : Real>=0∞}, ε != 0 -> exists g : α -> E, eLpNorm (g - s.indicator fun _ => c) p μ <= ε ∧ P g)
    (h1P : forall f g, P f -> P g -> P (f + g)) (h2P : forall f, P f -> AEStronglyMeasurable f μ) {f : α -> E}
    (hf : MemLp f p μ) {ε : Real>=0∞} (hε : ε != 0) : exists g : α -> E, eLpNorm (f - g) p μ <= ε ∧ P g := by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp, Pg⟩
  suffices H : forall (f' : α ->ₛ E) (δ : Real>=0∞) (hδ : δ != 0), MemLp f' p μ ->
      exists g, eLpNorm (⇑f' - g) p μ <= δ ∧ P g by
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p hε
    rcases hf.exists_simpleFunc_eLpNorm_sub_lt hp_ne_top ηpos.ne' with ⟨f', hf', f'_mem⟩
    rcases H f' η ηpos.ne' f'_mem with ⟨g, hg, Pg⟩
    refine ⟨g, ?_, Pg⟩
    convert!
      (hη _ _ (hf.aestronglyMeasurable.sub f'.aestronglyMeasurable)
          (f'.aestronglyMeasurable.sub (h2P g Pg)) hf'.le hg).le using 2
    simp only [sub_add_sub_cancel]
  apply SimpleFunc.induction
  · intro c s hs ε εpos Hs
    rcases eq_or_ne c 0 with (rfl | hc)
    · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
          εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg]; rw [neg_sub] at hg
      refine ⟨g, ?_, Pg⟩
      convert! hg
      ext x
      simp
    · have : μ s < ∞ := SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs Hs
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg]; rw [neg_sub] at hg
      exact ⟨g, hg, Pg⟩
  · intro f f' hff' hf hf' δ δpos int_ff'
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p δpos
    rw [SimpleFunc.coe_add]; rw [memLp_add_of_disjoint hff' f.stronglyMeasurable f'.stronglyMeasurable] at int_ff'
    rcases hf η ηpos.ne' int_ff'.1 with ⟨g, hg, Pg⟩
    rcases hf' η ηpos.ne' int_ff'.2 with ⟨g', hg', Pg'⟩
    refine ⟨g + g', ?_, h1P g g' Pg Pg'⟩
    convert!
      (hη _ _ (f.aestronglyMeasurable.sub (h2P g Pg)) (f'.aestronglyMeasurable.sub (h2P g' Pg')) hg
          hg').le using 2
    rw [SimpleFunc.coe_add]
    abel

section Integrable

@[inherit_doc MeasureTheory.Lp.simpleFunc]
notation3:25 α " ->₁ₛ[" μ "] " E => @MeasureTheory.Lp.simpleFunc α E _ _ 1 μ

/--
theorem `L1.SimpleFunc.toLp_one_eq_toL1` / 定理 `L1.SimpleFunc.toLp_one_eq_toL1`

English:
theorem L1.SimpleFunc.toLp_one_eq_toL1
  given: (f : α ->ₛ E) (hf : Integrable f μ)
  proof: rfl

@[fun_prop]

中文:
定理 L1.SimpleFunc.toLp_one_eq_toL1
  条件: (f : α ->ₛ E) (hf : 整数egrable f μ)
  证明: rfl

@[fun_prop]
-/
theorem L1.SimpleFunc.toLp_one_eq_toL1 (f : α ->ₛ E) (hf : Integrable f μ) :
    (toLp f (memLp_one_iff_integrable.2 hf) : α ->₁[μ] E) = hf.toL1 f :=
  rfl

@[fun_prop]
/--
theorem `L1.SimpleFunc.integrable` / 定理 `L1.SimpleFunc.integrable`

English:
theorem L1.SimpleFunc.integrable
  given: (f : α ->₁ₛ[μ] E)
  proof: by
  rw [← memLp_one_iff_integrable]; exact Lp.simpleFunc.memLp f

中文:
定理 L1.SimpleFunc.integrable
  条件: (f : α ->₁ₛ[μ] E)
  证明: by
  rw [← memLp_one_iff_integrable]; exact Lp.simpleFunc.memLp f
-/
protected theorem L1.SimpleFunc.integrable (f : α ->₁ₛ[μ] E) :
    Integrable (Lp.simpleFunc.toSimpleFunc f) μ := by
  rw [← memLp_one_iff_integrable]; exact Lp.simpleFunc.memLp f

/-- To prove something for an arbitrary integrable function in a normed group,
it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
/--
theorem `Integrable.induction` / 定理 `Integrable.induction`

English:
theorem Integrable.induction
  statement: (P : (α -> E) -> Prop)
  proof: by
  simp only [← memLp_one_iff_integrable] at *
  exact MemLp.induction one_ne_top (motive := P) h_ind h_add h_closed h_ae

中文:
定理 Integrable.induction
  结论: (P : (α -> E) -> 命题)
  证明: by
  simp only [← memLp_one_iff_integrable] at *
  exact MemLp.induction one_ne_top (motive := P) h_ind h_add h_closed h_ae

Depends on / 依赖: MemLp.induction, h_add, h_ae, h_closed, h_ind, memLp_one_iff_integrable, motive, one_ne_top
-/
theorem Integrable.induction (P : (α -> E) -> Prop)
    (h_ind : forall (c : E) ⦃s⦄, MeasurableSet s -> μ s < ∞ -> P (s.indicator fun _ => c))
    (h_add :
      forall ⦃f g : α -> E⦄,
        Disjoint (support f) (support g) -> Integrable f μ -> Integrable g μ -> P f -> P g -> P (f + g))
    (h_closed : IsClosed { f : α ->₁[μ] E | P f })
    (h_ae : forall ⦃f g⦄, f =ᵐ[μ] g -> Integrable f μ -> P f -> P g) :
    forall ⦃f : α -> E⦄, Integrable f μ -> P f := by
  simp only [← memLp_one_iff_integrable] at *
  exact MemLp.induction one_ne_top (motive := P) h_ind h_add h_closed h_ae

end Integrable

end MeasureTheory
