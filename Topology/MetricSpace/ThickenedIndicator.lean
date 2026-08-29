/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Data.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Thickened indicators

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

* `thickenedIndicatorAux δ E`: The `δ`-thickened indicator of a set `E` as an
  unbundled `ℝ≥0∞`-valued function.
* `thickenedIndicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
  bounded continuous `ℝ≥0`-valued function.

## Main results

* For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
  pointwise to the indicator of `closure E`.
  - `thickenedIndicatorAux_tendsto_indicator_closure`: The version is for the
    unbundled `ℝ≥0∞`-valued functions.
  - `thickenedIndicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
    bounded continuous functions.

-/

@[expose] public section

open NNReal ENNReal Topology BoundedContinuousFunction Set Metric Filter

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

/--
Definition of `thickenedIndicatorAux` / `thickenedIndicatorAux` 的定义

English:
definition thickenedIndicatorAux
  signature: (δ : Real) (E : Set α)
  body: fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ

中文:
定义 thickenedIndicatorAux
  签名: (δ : 实数) (E : 集合 α)
  定义体: fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ

Depends on / 依赖: ENNReal, ENNReal.ofReal, infEDist, ofReal
-/
def thickenedIndicatorAux (δ : Real) (E : Set α) : α -> Real>=0∞ :=
  fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ

/--
theorem `continuous_thickenedIndicatorAux` / 定理 `continuous_thickenedIndicatorAux`

English:
theorem continuous_thickenedIndicatorAux
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  proof: by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : Real>=0 × Real>=0∞)
  let sub := fun p : Real>=0 × Real>=0∞ => (p.1 : Real>=0∞) - p.2
  rw [show (fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.conti

中文:
定理 continuous_thickenedIndicatorAux
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α)
  证明: by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : Real>=0 × Real>=0∞)
  let sub := fun p : Real>=0 × Real>=0∞ => (p.1 : Real>=0∞) - p.2
  rw [show (fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.conti

Depends on / 依赖: ENNReal, ENNReal.continuous_div_const, ENNReal.continuous_nnreal_sub, ENNReal.ofReal, continuous_div_const, continuous_infEDist, continuous_nnreal_sub, infEDist, ofReal, thickenedIndicatorAux
-/
theorem continuous_thickenedIndicatorAux {δ : Real} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : Real>=0 × Real>=0∞)
  let sub := fun p : Real>=0 × Real>=0∞ => (p.1 : Real>=0∞) - p.2
  rw [show (fun x : α => (1 : Real>=0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_infEDist
  norm_num [δ_pos]

/--
theorem `thickenedIndicatorAux_le_one` / 定理 `thickenedIndicatorAux_le_one`

English:
theorem thickenedIndicatorAux_le_one
  given: (δ : Real) (E : Set α) (x : α)
  proof: by
  apply tsub_le_self (α := Real>=0∞)

@[aesop safe (rule_sets := [finiteness])]

中文:
定理 thickenedIndicatorAux_le_one
  条件: (δ : 实数) (E : 集合 α) (x : α)
  证明: by
  apply tsub_le_self (α := Real>=0∞)

@[aesop safe (rule_sets := [finiteness])]

Depends on / 依赖: tsub_le_self
-/
theorem thickenedIndicatorAux_le_one (δ : Real) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x <= 1 := by
  apply tsub_le_self (α := Real>=0∞)

@[aesop safe (rule_sets := [finiteness])]
/--
theorem `thickenedIndicatorAux_lt_top` / 定理 `thickenedIndicatorAux_lt_top`

English:
theorem thickenedIndicatorAux_lt_top
  given: {δ : Real} {E : Set α} {x : α}
  proof: lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top

中文:
定理 thickenedIndicatorAux_lt_top
  条件: {δ : 实数} {E : 集合 α} {x : α}
  证明: lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top

Depends on / 依赖: lt_of_le_of_lt, one_lt_top, thickenedIndicatorAux_le_one
-/
theorem thickenedIndicatorAux_lt_top {δ : Real} {E : Set α} {x : α} :
    thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top

/--
theorem `thickenedIndicatorAux_closure_eq` / 定理 `thickenedIndicatorAux_closure_eq`

English:
theorem thickenedIndicatorAux_closure_eq
  given: (δ : Real) (E : Set α)
  proof: by
  simp +unfoldPartialApp only [thickenedIndicatorAux, infEDist_closure]

中文:
定理 thickenedIndicatorAux_closure_eq
  条件: (δ : 实数) (E : 集合 α)
  证明: by
  simp +unfoldPartialApp only [thickenedIndicatorAux, infEDist_closure]

Depends on / 依赖: infEDist_closure, thickenedIndicatorAux, unfoldPartialApp
-/
theorem thickenedIndicatorAux_closure_eq (δ : Real) (E : Set α) :
    thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux δ E := by
  simp +unfoldPartialApp only [thickenedIndicatorAux, infEDist_closure]

/--
theorem `thickenedIndicatorAux_one` / 定理 `thickenedIndicatorAux_one`

English:
theorem thickenedIndicatorAux_one
  given: (δ : Real) (E : Set α) {x : α} (x_in_E : x in E)
  proof: by
  simp [thickenedIndicatorAux, infEDist_zero_of_mem x_in_E, tsub_zero]

中文:
定理 thickenedIndicatorAux_one
  条件: (δ : 实数) (E : 集合 α) {x : α} (x_in_E : x in E)
  证明: by
  simp [thickenedIndicatorAux, infEDist_zero_of_mem x_in_E, tsub_zero]

Depends on / 依赖: infEDist_zero_of_mem, thickenedIndicatorAux, tsub_zero, x_in_E
-/
theorem thickenedIndicatorAux_one (δ : Real) (E : Set α) {x : α} (x_in_E : x in E) :
    thickenedIndicatorAux δ E x = 1 := by
  simp [thickenedIndicatorAux, infEDist_zero_of_mem x_in_E, tsub_zero]

/--
theorem `thickenedIndicatorAux_one_of_mem_closure` / 定理 `thickenedIndicatorAux_one_of_mem_closure`

English:
theorem thickenedIndicatorAux_one_of_mem_closure
  statement: (δ : Real) (E : Set α) {x : α}
  proof: by
  rw [← thickenedIndicatorAux_closure_eq]; rw [thickenedIndicatorAux_one δ (closure E) x_mem]

中文:
定理 thickenedIndicatorAux_one_of_mem_closure
  结论: (δ : 实数) (E : 集合 α) {x : α}
  证明: by
  rw [← thickenedIndicatorAux_closure_eq]; rw [thickenedIndicatorAux_one δ (closure E) x_mem]

Depends on / 依赖: closure, thickenedIndicatorAux_closure_eq, thickenedIndicatorAux_one, x_mem
-/
theorem thickenedIndicatorAux_one_of_mem_closure (δ : Real) (E : Set α) {x : α}
    (x_mem : x in closure E) : thickenedIndicatorAux δ E x = 1 := by
  rw [← thickenedIndicatorAux_closure_eq]; rw [thickenedIndicatorAux_one δ (closure E) x_mem]

/--
theorem `thickenedIndicatorAux_zero` / 定理 `thickenedIndicatorAux_zero`

English:
theorem thickenedIndicatorAux_zero
  statement: {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
  proof: by
  rw [thickening]; rw [mem_ofPred_eq]; rw [not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub
    (@rfl _ (1 : Real>=0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : Real>=0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_p

中文:
定理 thickenedIndicatorAux_zero
  结论: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α) {x : α}
  证明: by
  rw [thickening]; rw [mem_ofPred_eq]; rw [not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub
    (@rfl _ (1 : Real>=0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : Real>=0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_p

Depends on / 依赖: ENNReal, ENNReal.div_le_div, ENNReal.div_self, ENNReal.ofReal, ENNReal.ofReal_pos.mpr, bot_le, div_le_div, div_self, le_antisymm, mem_ofPred_eq, ne_of_gt, not_lt, ofReal, ofReal_ne_top, ofReal_pos, thickenedIndicatorAux, thickening, tsub_le_tsub, tsub_self, x_out
-/
theorem thickenedIndicatorAux_zero {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0 := by
  rw [thickening]; rw [mem_ofPred_eq]; rw [not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub
    (@rfl _ (1 : Real>=0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : Real>=0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr δ_pos)) ofReal_ne_top] at key
  simpa [tsub_self] using key

/--
theorem `thickenedIndicatorAux_mono` / 定理 `thickenedIndicatorAux_mono`

English:
theorem thickenedIndicatorAux_mono
  given: {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α)
  proof: fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))

中文:
定理 thickenedIndicatorAux_mono
  条件: {δ₁ δ₂ : 实数} (hle : δ₁ <= δ₂) (E : 集合 α)
  证明: fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))

Depends on / 依赖: ENNReal, ENNReal.div_le_div, div_le_div, ofReal_le_ofReal, rfl.le, tsub_le_tsub
-/
theorem thickenedIndicatorAux_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E <= thickenedIndicatorAux δ₂ E :=
  fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))

/--
theorem `indicator_le_thickenedIndicatorAux` / 定理 `indicator_le_thickenedIndicatorAux`

English:
theorem indicator_le_thickenedIndicatorAux
  given: (δ : Real) (E : Set α)
  proof: by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

中文:
定理 indicator_le_thickenedIndicatorAux
  条件: (δ : 实数) (E : 集合 α)
  证明: by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

Depends on / 依赖: indicator_of_mem, indicator_of_notMem, le_refl, not_false_iff, thickenedIndicatorAux_one, zero_le
-/
theorem indicator_le_thickenedIndicatorAux (δ : Real) (E : Set α) :
    (E.indicator fun _ => (1 : Real>=0∞)) <= thickenedIndicatorAux δ E := by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

/--
theorem `thickenedIndicatorAux_subset` / 定理 `thickenedIndicatorAux_subset`

English:
theorem thickenedIndicatorAux_subset
  given: (δ : Real) {E₁ E₂ : Set α} (subset : E₁ subseteq E₂)
  proof: fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div (infEDist_anti subset) rfl.le)

中文:
定理 thickenedIndicatorAux_subset
  条件: (δ : 实数) {E₁ E₂ : 集合 α} (subset : E₁ subseteq E₂)
  证明: fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div (infEDist_anti subset) rfl.le)

Depends on / 依赖: ENNReal, ENNReal.div_le_div, div_le_div, infEDist_anti, rfl.le, subset, tsub_le_tsub
-/
theorem thickenedIndicatorAux_subset (δ : Real) {E₁ E₂ : Set α} (subset : E₁ subseteq E₂) :
    thickenedIndicatorAux δ E₁ <= thickenedIndicatorAux δ E₂ :=
  fun _ => tsub_le_tsub (@rfl Real>=0∞ 1).le (ENNReal.div_le_div (infEDist_anti subset) rfl.le)

/--
lemma `thickenedIndicatorAux_mono_infEDist` / 引理 `thickenedIndicatorAux_mono_infEDist`

English:
lemma thickenedIndicatorAux_mono_infEDist
  statement: (δ : Real) {E : Set α} {x y : α}
  proof: by
  simp only [thickenedIndicatorAux]
  rcases le_total (infEDist x E / ENNReal.ofReal δ) 1 with hle | hle
  · rw [ENNReal.sub_le_sub_iff_left hle (by simp)]
    gcongr
  · rw [tsub_eq_zero_of_le hle, tsub_eq_zero_of_le]
    exact hle.trans (by gcongr)

@[deprecated (since := "2026-01-08")]
alias t

中文:
引理 thickenedIndicatorAux_mono_infEDist
  结论: (δ : 实数) {E : 集合 α} {x y : α}
  证明: by
  simp only [thickenedIndicatorAux]
  rcases le_total (infEDist x E / ENNReal.ofReal δ) 1 with hle | hle
  · rw [ENNReal.sub_le_sub_iff_left hle (by simp)]
    gcongr
  · rw [tsub_eq_zero_of_le hle, tsub_eq_zero_of_le]
    exact hle.trans (by gcongr)

@[deprecated (since := "2026-01-08")]
alias t

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.sub_le_sub_iff_left, hle.trans, infEDist, le_total, ofReal, sub_le_sub_iff_left, thickenedIndicatorAux, tsub_eq_zero_of_le
-/
lemma thickenedIndicatorAux_mono_infEDist (δ : Real) {E : Set α} {x y : α}
    (h : infEDist x E <= infEDist y E) :
    thickenedIndicatorAux δ E y <= thickenedIndicatorAux δ E x := by
  simp only [thickenedIndicatorAux]
  rcases le_total (infEDist x E / ENNReal.ofReal δ) 1 with hle | hle
  · rw [ENNReal.sub_le_sub_iff_left hle (by simp)]
    gcongr
  · rw [tsub_eq_zero_of_le hle, tsub_eq_zero_of_le]
    exact hle.trans (by gcongr)

@[deprecated (since := "2026-01-08")]
alias thickenedIndicatorAux_mono_infEdist := thickenedIndicatorAux_mono_infEDist

/--
theorem `thickenedIndicatorAux_tendsto_indicator_closure` / 定理 `thickenedIndicatorAux_tendsto_indicator_closure`

English:
theorem thickenedIndicatorAux_tendsto_indicator_closure
  statement: {δseq : Nat -> Real}
  proof: by
  rw [tendsto_pi_nhds]
  intro x
  by_cases x_mem_closure : x in closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : Real>=0∞)) x = 1 by
        simp only [x_mem_closure]; rw [indicator_of_mem]]
    exact tendsto_con

中文:
定理 thickenedIndicatorAux_tendsto_indicator_closure
  结论: {δseq : 自然数 -> 实数}
  证明: by
  rw [tendsto_pi_nhds]
  intro x
  by_cases x_mem_closure : x in closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : Real>=0∞)) x = 1 by
        simp only [x_mem_closure]; rw [indicator_of_mem]]
    exact tendsto_con

Depends on / 依赖: closure, exists_real_pos_lt_infEDist_of_notMem_closure, indicator, indicator_of_mem, indicator_of_notMem, not_false_iff, simp_rw, tendsto_const_nhds, tendsto_pi_nhds, thickenedIndicatorAux_one_of_mem_closure, x_mem_closure
-/
theorem thickenedIndicatorAux_tendsto_indicator_closure {δseq : Nat -> Real}
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n => thickenedIndicatorAux (δseq n) E) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : Real>=0∞))) := by
  rw [tendsto_pi_nhds]
  intro x
  by_cases x_mem_closure : x in closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : Real>=0∞)) x = 1 by
        simp only [x_mem_closure]; rw [indicator_of_mem]]
    exact tendsto_const_nhds
  · rw [show (closure E).indicator (fun _ => (1 : Real>=0∞)) x = 0 by
        simp only [x_mem_closure, indicator_of_notMem, not_false_iff]]
    rcases exists_real_pos_lt_infEDist_of_notMem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩
    rw [Metric.tendsto_nhds] at δseq_lim
    specialize δseq_lim ε ε_pos
    simp only [dist_zero_right, Real.norm_eq_abs, eventually_atTop] at δseq_lim
    rcases δseq_lim with ⟨N, hN⟩
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n n_large
    have key : x ∉ thickening ε E := by simpa only [thickening, mem_ofPred_eq, not_lt] using ε_lt.le
    refine le_antisymm ?_ bot_le
    apply (thickenedIndicatorAux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    exact (thickenedIndicatorAux_zero ε_pos E key).le

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickenedIndicatorAux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
/--
Definition of `thickenedIndicator` / `thickenedIndicator` 的定义

English:
definition thickenedIndicator
  signature: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  body: fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
  map_bounded' := 

中文:
定义 thickenedIndicator
  签名: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α)
  定义体: fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
  map_bounded' := 

Depends on / 依赖: thickenedIndicatorAux, toNNReal
-/
def thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) : α ->ᵇ Real>=0 where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
  map_bounded' := by
    use 2
    intro x y
    rw [NNReal.dist_eq]
    apply (abs_sub _ _).trans
    rw [NNReal.abs_eq]; rw [NNReal.abs_eq]; rw [← one_add_one_eq_two]
    have key := @thickenedIndicatorAux_le_one _ _ δ E
    apply add_le_add <;>
      · norm_cast
        exact (toNNReal_le_toNNReal (lt_of_le_of_lt (key _) one_lt_top).ne one_ne_top).mpr (key _)

/--
theorem `thickenedIndicator.coeFn_eq_comp` / 定理 `thickenedIndicator.coeFn_eq_comp`

English:
theorem thickenedIndicator.coeFn_eq_comp
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  proof: rfl

中文:
定理 thickenedIndicator.coeFn_eq_comp
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α)
  证明: rfl
-/
theorem thickenedIndicator.coeFn_eq_comp {δ : Real} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E :=
  rfl

/--
theorem `thickenedIndicator_le_one` / 定理 `thickenedIndicator_le_one`

English:
theorem thickenedIndicator_le_one
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α) (x : α)
  proof: by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using (toNNReal_le_toNNReal (by finiteness) one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)

中文:
定理 thickenedIndicator_le_one
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α) (x : α)
  证明: by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using (toNNReal_le_toNNReal (by finiteness) one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)

Depends on / 依赖: coeFn_eq_comp, finiteness, one_ne_top, thickenedIndicator, thickenedIndicator.coeFn_eq_comp, thickenedIndicatorAux_le_one, toNNReal_le_toNNReal
-/
theorem thickenedIndicator_le_one {δ : Real} (δ_pos : 0 < δ) (E : Set α) (x : α) :
    thickenedIndicator δ_pos E x <= 1 := by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using (toNNReal_le_toNNReal (by finiteness) one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)

/--
theorem `thickenedIndicator_one_of_mem_closure` / 定理 `thickenedIndicator_one_of_mem_closure`

English:
theorem thickenedIndicator_one_of_mem_closure
  statement: {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
  proof: by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_one_of_mem_closure δ E x_mem]; rw [toNNReal_one]

中文:
定理 thickenedIndicator_one_of_mem_closure
  结论: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α) {x : α}
  证明: by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_one_of_mem_closure δ E x_mem]; rw [toNNReal_one]

Depends on / 依赖: thickenedIndicatorAux_one_of_mem_closure, thickenedIndicator_apply, toNNReal_one, x_mem
-/
theorem thickenedIndicator_one_of_mem_closure {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_mem : x in closure E) : thickenedIndicator δ_pos E x = 1 := by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_one_of_mem_closure δ E x_mem]; rw [toNNReal_one]

/--
lemma `one_le_thickenedIndicator_apply'` / 引理 `one_le_thickenedIndicator_apply'`

English:
lemma one_le_thickenedIndicator_apply'
  statement: {X : Type _} [PseudoEMetricSpace X]
  proof: by
  rw [thickenedIndicator_one_of_mem_closure δ_pos F hxF]

中文:
引理 one_le_thickenedIndicator_apply'
  结论: {X : 类型 _} [PseudoEMetric空间 X]
  证明: by
  rw [thickenedIndicator_one_of_mem_closure δ_pos F hxF]

Depends on / 依赖: thickenedIndicator_one_of_mem_closure
-/
lemma one_le_thickenedIndicator_apply' {X : Type _} [PseudoEMetricSpace X]
    {δ : Real} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x in closure F) :
    1 <= thickenedIndicator δ_pos F x := by
  rw [thickenedIndicator_one_of_mem_closure δ_pos F hxF]

/--
lemma `one_le_thickenedIndicator_apply` / 引理 `one_le_thickenedIndicator_apply`

English:
lemma one_le_thickenedIndicator_apply
  statement: (X : Type _) [PseudoEMetricSpace X]
  proof: one_le_thickenedIndicator_apply' δ_pos (subset_closure hxF)

中文:
引理 one_le_thickenedIndicator_apply
  结论: (X : 类型 _) [PseudoEMetric空间 X]
  证明: one_le_thickenedIndicator_apply' δ_pos (subset_closure hxF)

Depends on / 依赖: one_le_thickenedIndicator_apply, subset_closure
-/
lemma one_le_thickenedIndicator_apply (X : Type _) [PseudoEMetricSpace X]
    {δ : Real} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x in F) :
    1 <= thickenedIndicator δ_pos F x :=
  one_le_thickenedIndicator_apply' δ_pos (subset_closure hxF)

/--
theorem `thickenedIndicator_one` / 定理 `thickenedIndicator_one`

English:
theorem thickenedIndicator_one
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x in E)
  proof: thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)

中文:
定理 thickenedIndicator_one
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α) {x : α} (x_in_E : x in E)
  证明: thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)

Depends on / 依赖: subset_closure, thickenedIndicator_one_of_mem_closure, x_in_E
-/
theorem thickenedIndicator_one {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x in E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)

/--
theorem `thickenedIndicator_zero` / 定理 `thickenedIndicator_zero`

English:
theorem thickenedIndicator_zero
  statement: {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
  proof: by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_zero δ_pos E x_out]; rw [toNNReal_zero]

中文:
定理 thickenedIndicator_zero
  结论: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α) {x : α}
  证明: by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_zero δ_pos E x_out]; rw [toNNReal_zero]

Depends on / 依赖: thickenedIndicatorAux_zero, thickenedIndicator_apply, toNNReal_zero, x_out
-/
theorem thickenedIndicator_zero {δ : Real} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0 := by
  rw [thickenedIndicator_apply]; rw [thickenedIndicatorAux_zero δ_pos E x_out]; rw [toNNReal_zero]

/--
theorem `indicator_le_thickenedIndicator` / 定理 `indicator_le_thickenedIndicator`

English:
theorem indicator_le_thickenedIndicator
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  proof: by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

中文:
定理 indicator_le_thickenedIndicator
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α)
  证明: by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

Depends on / 依赖: indicator_of_mem, indicator_of_notMem, le_refl, not_false_iff, thickenedIndicator_one, zero_le
-/
theorem indicator_le_thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : Real>=0)) <= thickenedIndicator δ_pos E := by
  intro a
  by_cases h : a in E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

/--
theorem `thickenedIndicator_mono` / 定理 `thickenedIndicator_mono`

English:
theorem thickenedIndicator_mono
  statement: {δ₁ δ₂ : Real} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ <= δ₂)
  proof: by
  intro x
  apply (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
  apply thickenedIndicatorAux_mono hle

中文:
定理 thickenedIndicator_mono
  结论: {δ₁ δ₂ : 实数} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ <= δ₂)
  证明: by
  intro x
  apply (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
  apply thickenedIndicatorAux_mono hle

Depends on / 依赖: finiteness, thickenedIndicatorAux_mono, toNNReal_le_toNNReal
-/
theorem thickenedIndicator_mono {δ₁ δ₂ : Real} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ <= δ₂)
    (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) <= thickenedIndicator δ₂_pos E := by
  intro x
  apply (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
  apply thickenedIndicatorAux_mono hle

/--
theorem `thickenedIndicator_subset` / 定理 `thickenedIndicator_subset`

English:
theorem thickenedIndicator_subset
  given: {δ : Real} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ subseteq E₂)
  proof: fun x =>
  (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
    (thickenedIndicatorAux_subset δ subset x)

@[gcongr only]

中文:
定理 thickenedIndicator_subset
  条件: {δ : 实数} (δ_pos : 0 < δ) {E₁ E₂ : 集合 α} (subset : E₁ subseteq E₂)
  证明: fun x =>
  (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
    (thickenedIndicatorAux_subset δ subset x)

@[gcongr only]
-/
theorem thickenedIndicator_subset {δ : Real} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ subseteq E₂) :
    ⇑(thickenedIndicator δ_pos E₁) <= thickenedIndicator δ_pos E₂ := fun x =>
  (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
    (thickenedIndicatorAux_subset δ subset x)

@[gcongr only]
/--
lemma `thickenedIndicator_mono_infEDist` / 引理 `thickenedIndicator_mono_infEDist`

English:
lemma thickenedIndicator_mono_infEDist
  statement: {δ : Real} (δ_pos : 0 < δ) {E : Set α} {x y : α}
  proof: by
  simp only [thickenedIndicator_apply]
  gcongr
  · finiteness
  · exact thickenedIndicatorAux_mono_infEDist δ h

@[deprecated (since := "2026-01-08")]
alias thickenedIndicator_mono_infEdist := thickenedIndicator_mono_infEDist

中文:
引理 thickenedIndicator_mono_infEDist
  结论: {δ : 实数} (δ_pos : 0 < δ) {E : 集合 α} {x y : α}
  证明: by
  simp only [thickenedIndicator_apply]
  gcongr
  · finiteness
  · exact thickenedIndicatorAux_mono_infEDist δ h

@[deprecated (since := "2026-01-08")]
alias thickenedIndicator_mono_infEdist := thickenedIndicator_mono_infEDist

Depends on / 依赖: finiteness, thickenedIndicatorAux_mono_infEDist, thickenedIndicator_apply
-/
lemma thickenedIndicator_mono_infEDist {δ : Real} (δ_pos : 0 < δ) {E : Set α} {x y : α}
    (h : infEDist x E <= infEDist y E) :
    thickenedIndicator δ_pos E y <= thickenedIndicator δ_pos E x := by
  simp only [thickenedIndicator_apply]
  gcongr
  · finiteness
  · exact thickenedIndicatorAux_mono_infEDist δ h

@[deprecated (since := "2026-01-08")]
alias thickenedIndicator_mono_infEdist := thickenedIndicator_mono_infEDist

/--
theorem `thickenedIndicator_tendsto_indicator_closure` / 定理 `thickenedIndicator_tendsto_indicator_closure`

English:
theorem thickenedIndicator_tendsto_indicator_closure
  statement: {δseq : Nat -> Real} (δseq_pos : forall n, 0 < δseq n)
  proof: by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show indicator (closure E) (fun _ => (1 : Real>=0)) x =
        (indicator (closure E) (fun _ => (1 : Real>=0∞)) x).toNNReal
      by refine (congr_fun (comp_indicator_const 1 ENNR

中文:
定理 thickenedIndicator_tendsto_indicator_closure
  结论: {δseq : 自然数 -> 实数} (δseq_pos : 对任意 n, 0 < δseq n)
  证明: by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show indicator (closure E) (fun _ => (1 : Real>=0)) x =
        (indicator (closure E) (fun _ => (1 : Real>=0∞)) x).toNNReal
      by refine (congr_fun (comp_indicator_const 1 ENNR

Depends on / 依赖: ENNReal, ENNReal.toNNReal, Tendsto, Tendsto.comp, closure, comp_indicator_const, congr_fun, indicator, tendsto_pi_nhds, tendsto_toNNReal, thickenedIndicatorAux_tendsto_indicator_closure, toNNReal, toNNReal_zero, x_mem
-/
theorem thickenedIndicator_tendsto_indicator_closure {δseq : Nat -> Real} (δseq_pos : forall n, 0 < δseq n)
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n : Nat => ((↑) : (α ->ᵇ Real>=0) -> α -> Real>=0) (thickenedIndicator (δseq_pos n) E)) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : Real>=0))) := by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show indicator (closure E) (fun _ => (1 : Real>=0)) x =
        (indicator (closure E) (fun _ => (1 : Real>=0∞)) x).toNNReal
      by refine (congr_fun (comp_indicator_const 1 ENNReal.toNNReal toNNReal_zero) x).symm]
  refine Tendsto.comp (tendsto_toNNReal ?_) (key x)
  by_cases x_mem : x in closure E <;> simp [x_mem]

/--
lemma `lipschitzWith_thickenedIndicator` / 引理 `lipschitzWith_thickenedIndicator`

English:
lemma lipschitzWith_thickenedIndicator
  given: {δ : Real} (δ_pos : 0 < δ) (E : Set α)
  proof: by
  intro x y
  wlog h : infEDist x E <= infEDist y E generalizing x y
  · specialize this y x (le_of_not_ge h)
    rwa [edist_comm, edist_comm x]
  simp_rw [edist_dist, NNReal.dist_eq, thickenedIndicator_apply, coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sub_of_le (thickenedIndicatorAux_mono_in

中文:
引理 lipschitzWith_thickenedIndicator
  条件: {δ : 实数} (δ_pos : 0 < δ) (E : 集合 α)
  证明: by
  intro x y
  wlog h : infEDist x E <= infEDist y E generalizing x y
  · specialize this y x (le_of_not_ge h)
    rwa [edist_comm, edist_comm x]
  simp_rw [edist_dist, NNReal.dist_eq, thickenedIndicator_apply, coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sub_of_le (thickenedIndicatorAux_mono_in

Depends on / 依赖: ENNReal, ENNReal.coe_inv, ENNReal.of, ENNReal.toReal_sub_of_le, NNReal, NNReal.dist_eq, abs_toReal, and_true, coe_inv, coe_toNNReal_eq_toReal, dist_eq, edist_comm, edist_dist, false_and, finiteness, generalizing, infEDist, le_of_not_ge, ne_eq, not_false_eq_true
-/
lemma lipschitzWith_thickenedIndicator {δ : Real} (δ_pos : 0 < δ) (E : Set α) :
    LipschitzWith δ.toNNReal⁻¹ (thickenedIndicator δ_pos E) := by
  intro x y
  wlog h : infEDist x E <= infEDist y E generalizing x y
  · specialize this y x (le_of_not_ge h)
    rwa [edist_comm, edist_comm x]
  simp_rw [edist_dist, NNReal.dist_eq, thickenedIndicator_apply, coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sub_of_le (thickenedIndicatorAux_mono_infEDist _ h) (by finiteness)]
  simp only [thickenedIndicatorAux, abs_toReal, ne_eq, sub_eq_top_iff, one_ne_top, false_and,
    not_false_eq_true, and_true, ofReal_toReal]
  rw [ENNReal.coe_inv (by simp [δ_pos]), ENNReal.ofReal, div_eq_mul_inv, div_eq_mul_inv]
  by_cases h_le : infEDist y E * (↑δ.toNNReal)⁻¹ <= 1
  · calc 1 - infEDist x E * (↑δ.toNNReal)⁻¹ - (1 - infEDist y E * (↑δ.toNNReal)⁻¹)
    _ <= infEDist y E * (↑δ.toNNReal)⁻¹ - infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [ENNReal.sub_sub_sub_cancel_left (by finiteness) h_le]
    _ <= (↑δ.toNNReal)⁻¹ * edist x y := by
      rw [← ENNReal.sub_mul (by simp [δ_pos]), mul_comm, edist_comm]
      gcongr
      simp only [tsub_le_iff_right]
      exact infEDist_le_edist_add_infEDist
  · simp only [tsub_le_iff_right]
    rw [tsub_eq_zero_of_le (not_le.mp h_le).le]; rw [add_zero]; rw [mul_comm]
    calc 1
    _ <= infEDist y E * (↑δ.toNNReal)⁻¹ := (not_le.mp h_le).le
    _ <= edist x y * (↑δ.toNNReal)⁻¹ + infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [← add_mul]; rw [edist_comm]
      gcongr
      exact infEDist_le_edist_add_infEDist

end thickenedIndicator

section indicator

variable {α : Type*} [PseudoEMetricSpace α] {β : Type*} [One β]

/-- Pointwise, the multiplicative indicators of δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ>0 tends to zero. -/
@[to_additive /-- Pointwise, the indicators of δ-thickenings of a set eventually coincide
with the indicator of the set as δ>0 tends to zero. -/]
/--
lemma `mulIndicator_thickening_eventually_eq_mulIndicator_closure` / 引理 `mulIndicator_thickening_eventually_eq_mulIndicator_closure`

English:
lemma mulIndicator_thickening_eventually_eq_mulIndicator_closure
  given: (f : α -> β) (E : Set α) (x : α)
  proof: by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
  · have obs := eventually_notMem_thickening_of_infEDist_pos x_mem_closure
    filter_upwards [mem_nh

中文:
引理 mulIndicator_thickening_eventually_eq_mulIndicator_closure
  条件: (f : α -> β) (E : 集合 α) (x : α)
  证明: by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
  · have obs := eventually_notMem_thickening_of_infEDist_pos x_mem_closure
    filter_upwards [mem_nh

Depends on / 依赖: closure, closure_subset_thickening, eventually_notMem_thickening_of_infEDist_pos, filter_upwards, mem_nhdsWithin_of_mem_nhds, mulIndicator_of_mem, mulIndicator_of_notMem, not_false_eq_true, self_mem_nhdsWithin, x_mem_closure, x_notin_thE
-/
lemma mulIndicator_thickening_eventually_eq_mulIndicator_closure (f : α -> β) (E : Set α) (x : α) :
    forallᶠ δ in 𝓝[>] (0 : Real),
      (Metric.thickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
  · have obs := eventually_notMem_thickening_of_infEDist_pos x_mem_closure
    filter_upwards [mem_nhdsWithin_of_mem_nhds obs, self_mem_nhdsWithin]
      with δ x_notin_thE _
    simp only [x_notin_thE, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

/-- Pointwise, the multiplicative indicators of closed δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ tends to zero. -/
@[to_additive /-- Pointwise, the indicators of closed δ-thickenings of a set eventually coincide
with the indicator of the set as δ tends to zero. -/]
/--
lemma `mulIndicator_cthickening_eventually_eq_mulIndicator_closure` / 引理 `mulIndicator_cthickening_eventually_eq_mulIndicator_closure`

English:
lemma mulIndicator_cthickening_eventually_eq_mulIndicator_closure
  given: (f : α -> β) (E : Set α) (x : α)
  proof: by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [univ_mem] with δ _
    have obs : x in cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    rw [mulIndicator_of_mem obs f]; rw [mulIndicator_of_mem x_mem_closure f]
  · filter_upwards [eventually_notMem_cthickening_of_in

中文:
引理 mulIndicator_cthickening_eventually_eq_mulIndicator_closure
  条件: (f : α -> β) (E : 集合 α) (x : α)
  证明: by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [univ_mem] with δ _
    have obs : x in cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    rw [mulIndicator_of_mem obs f]; rw [mulIndicator_of_mem x_mem_closure f]
  · filter_upwards [eventually_notMem_cthickening_of_in

Depends on / 依赖: closure, closure_subset_cthickening, cthickening, eventually_notMem_cthickening_of_infEDist_pos, filter_upwards, mulIndicator_of_mem, mulIndicator_of_notMem, not_false_eq_true, univ_mem, x_mem_closure
-/
lemma mulIndicator_cthickening_eventually_eq_mulIndicator_closure (f : α -> β) (E : Set α) (x : α) :
    forallᶠ δ in 𝓝 (0 : Real),
      (Metric.cthickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x in closure E
  · filter_upwards [univ_mem] with δ _
    have obs : x in cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    rw [mulIndicator_of_mem obs f]; rw [mulIndicator_of_mem x_mem_closure f]
  · filter_upwards [eventually_notMem_cthickening_of_infEDist_pos x_mem_closure] with δ hδ
    simp only [hδ, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

variable [TopologicalSpace β]

/-- The multiplicative indicators of δ-thickenings of a set tend pointwise to the multiplicative
indicator of the set, as δ>0 tends to zero. -/
@[to_additive /-- The indicators of δ-thickenings of a set tend pointwise to the indicator of the
set, as δ>0 tends to zero. -/]
/--
lemma `tendsto_mulIndicator_thickening_mulIndicator_closure` / 引理 `tendsto_mulIndicator_thickening_mulIndicator_closure`

English:
lemma tendsto_mulIndicator_thickening_mulIndicator_closure
  given: (f : α -> β) (E : Set α)
  proof: by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

中文:
引理 tendsto_mulIndicator_thickening_mulIndicator_closure
  条件: (f : α -> β) (E : 集合 α)
  证明: by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

Depends on / 依赖: mulIndicator_thickening_eventually_eq_mulIndicator_closure, tendsto_congr, tendsto_const_nhds, tendsto_pi_nhds
-/
lemma tendsto_mulIndicator_thickening_mulIndicator_closure (f : α -> β) (E : Set α) :
    Tendsto (fun δ => (Metric.thickening δ E).mulIndicator f) (𝓝[>] 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

/-- The multiplicative indicators of closed δ-thickenings of a set tend pointwise to the
multiplicative indicator of the set, as δ tends to zero. -/
@[to_additive /-- The indicators of closed δ-thickenings of a set tend pointwise to the indicator
of the set, as δ tends to zero. -/]
/--
lemma `tendsto_mulIndicator_cthickening_mulIndicator_closure` / 引理 `tendsto_mulIndicator_cthickening_mulIndicator_closure`

English:
lemma tendsto_mulIndicator_cthickening_mulIndicator_closure
  given: (f : α -> β) (E : Set α)
  proof: by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

中文:
引理 tendsto_mulIndicator_cthickening_mulIndicator_closure
  条件: (f : α -> β) (E : 集合 α)
  证明: by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

Depends on / 依赖: mulIndicator_cthickening_eventually_eq_mulIndicator_closure, tendsto_congr, tendsto_const_nhds, tendsto_pi_nhds
-/
lemma tendsto_mulIndicator_cthickening_mulIndicator_closure (f : α -> β) (E : Set α) :
    Tendsto (fun δ => (Metric.cthickening δ E).mulIndicator f) (𝓝 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

end indicator
