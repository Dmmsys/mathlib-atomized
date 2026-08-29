/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Fernique's theorem for rotation-invariant measures

Let `μ` be a finite measure on a second-countable normed space `E` such that the product measure
`μ.prod μ` on `E × E` is invariant by rotation of angle `-π/4`.
Then there exists a constant `C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable
with respect to `μ`.

## Sketch of the proof

The main case of the proof is for `μ` a probability measure such that there exists a positive
`a : ℝ` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`. If `μ` is a probability measure and `a` does not
exist then we can show that there is a ball with finite radius of measure 1, and the result is true
for `C = 1` (for example), since `x ↦ exp (‖x‖ ^ 2)` is almost surely bounded.
We then choose such an `a`.

In order to show the existence of `C` such that `x ↦ exp (C * ‖x‖ ^ 2)` is integrable, we prove as
intermediate result that for `a, c` with `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`,
the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2) ∂μ` is bounded by a finite quantity
(`logRatio c` is a multiple of `log (c / (1 - c))`). We can then take `C = logRatio c * a⁻¹ ^ 2`.

We now turn to the proof of the intermediate result.

First in `measure_le_mul_measure_gt_le_of_map_rotation_eq_self` we prove that if a measure `μ` is
such that `μ.prod μ` is invariant by rotation of angle `-π/4` then
`μ {x | ‖x‖ ≤ a} * μ {x | b < ‖x‖} ≤ μ {x | (b - a) / √2 < ‖x‖} ^ 2`.
The rotation invariance is used only through that inequality.

We define a sequence of thresholds `t n` inductively by `t 0 = a` and `t (n + 1) = √2 * t n + a`.
They are chosen such that the invariance by rotation gives
`μ {x | ‖x‖ ≤ a} * μ {x | t (n + 1) < ‖x‖} ≤ μ {x | t n < ‖x‖} ^ 2`.
Thanks to that inequality we can show that `μ {x | t n < ‖x‖}` decreases fast with `n`:
for `mₐ = μ {x | ‖x‖ ≤ a}`, `μ {x | t n < ‖x‖} ≤ mₐ * exp (- log (mₐ / (1 - mₐ)) * 2 ^ n)`.

We cut the space into annuli `{x | t n < ‖x‖ ≤ t n + 1}` and bound the integral separately on
each annulus. On that set the function `exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)` is bounded by
`exp (logRatio c * a⁻¹ ^ 2 * t (n + 1) ^ 2)`, which is in turn less than
`exp (2⁻¹ * log (c / (1 - c)) * 2 ^ n)` (from the definition of the threshold `t` and `logRatio c`).
The measure of the annulus is bounded by `μ {x | t n < ‖x‖}`, for which we derived an upper bound
above. The function gets exponentially large, but `μ {x | t n < ‖x‖}` decreases even faster, so the
integral is bounded by a quantity of the form `exp (- u * 2 ^ n)` for `u>0`.
Summing over all annuli (over `n`) gives a finite value for the integral.

## Main statements

* `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self`: for `μ` a probability measure
  whose product with itself is invariant by rotation and for `a, c` with
  `2⁻¹ < c ≤ μ {x | ‖x‖ ≤ a}`, the integral `∫⁻ x, exp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2) ∂μ`
  is bounded by a quantity that does not depend on `a`.
* `exists_integrable_exp_sq_of_map_rotation_eq_self`: Fernique's theorem for finite measures
  whose product is invariant by rotation.

## References

* [Xavier Fernique, *Intégrabilité des vecteurs gaussiens*][fernique1970integrabilite]
* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

## TODO

From the intermediate result `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self`,
we can deduce bounds on all the moments of the measure `μ` as function of powers of
the first moment.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex NormedSpace Filter
open scoped ENNReal NNReal Real Topology

section Aux

/--
lemma `StrictMono.exists_between_of_tendsto_atTop` / 引理 `StrictMono.exists_between_of_tendsto_atTop`

English:
lemma StrictMono.exists_between_of_tendsto_atTop
  statement: {β : Type*} [LinearOrder β] {t : Nat -> β}
  proof: by
  have h : exists n, x <= t n := by
    simp only [tendsto_atTop_atTop_iff_of_monotone ht_mono.monotone] at ht_tendsto
    exact ht_tendsto x
  have h' m := Nat.find_min h (m := m)
  simp only [not_le] at h'
  exact ⟨Nat.find h - 1, h' _ (by simp [hx]), by simp [Nat.find_spec h, hx]⟩

中文:
引理 严格递增.存在_between_of_tendsto_atTop
  结论: {β : 类型} [线性序 β] {t : 自然数 -> β}
  证明: by
  have h : exists n, x <= t n := by
    simp only [tendsto_atTop_atTop_iff_of_monotone ht_mono.monotone] at ht_tendsto
    exact ht_tendsto x
  have h' m := Nat.find_min h (m := m)
  simp only [not_le] at h'
  exact ⟨Nat.find h - 1, h' _ (by simp [hx]), by simp [Nat.find_spec h, hx]⟩

Depends on / 依赖: Nat.find, Nat.find_min, Nat.find_spec, find_min, find_spec, ht_mono, ht_mono.monotone, ht_tendsto, monotone, not_le, tendsto_atTop_atTop_iff_of_monotone
-/
lemma StrictMono.exists_between_of_tendsto_atTop {β : Type*} [LinearOrder β] {t : Nat -> β}
    (ht_mono : StrictMono t) (ht_tendsto : Tendsto t atTop atTop) {x : β} (hx : t 0 < x) :
    exists n, t n < x ∧ x <= t (n + 1) := by
  have h : exists n, x <= t n := by
    simp only [tendsto_atTop_atTop_iff_of_monotone ht_mono.monotone] at ht_tendsto
    exact ht_tendsto x
  have h' m := Nat.find_min h (m := m)
  simp only [not_le] at h'
  exact ⟨Nat.find h - 1, h' _ (by simp [hx]), by simp [Nat.find_spec h, hx]⟩

end Aux

namespace ProbabilityTheory

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Real E]

/-- The rotation in `E × E` with angle `θ`, as a continuous linear map. -/
noncomputable
/--
Definition of `_root_.ContinuousLinearMap.rotation` / `_root_.ContinuousLinearMap.rotation` 的定义

English:
definition _root_.ContinuousLinearMap.rotation
  signature: (θ : Real)
  body: fun x => (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by simp [smul_comm c]

中文:
定义 _root_.连续线性映射.rotation
  签名: (θ : 实数)
  定义体: fun x => (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by simp [smul_comm c]

Depends on / 依赖: Real.cos, Real.sin
-/
def _root_.ContinuousLinearMap.rotation (θ : Real) : E × E ->L[Real] E × E where
  toFun := fun x => (Real.cos θ • x.1 + Real.sin θ • x.2, - Real.sin θ • x.1 + Real.cos θ • x.2)
  map_add' x y := by
    simp only [Prod.fst_add, smul_add, Prod.snd_add, neg_smul, Prod.mk_add_mk]
    abel_nf
  map_smul' c x := by simp [smul_comm c]

/--
lemma `_root_.ContinuousLinearMap.rotation_apply` / 引理 `_root_.ContinuousLinearMap.rotation_apply`

English:
lemma _root_.ContinuousLinearMap.rotation_apply
  given: (θ : Real) (x : E × E)
  proof: rfl

中文:
引理 _root_.连续线性映射.rotation_apply
  条件: (θ : 实数) (x : E × E)
  证明: rfl
-/
lemma _root_.ContinuousLinearMap.rotation_apply (θ : Real) (x : E × E) :
    ContinuousLinearMap.rotation θ x
     = (Real.cos θ • x.1 + Real.sin θ • x.2, -Real.sin θ • x.1 + Real.cos θ • x.2) := rfl

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {a : Real}

/--
lemma `measure_le_mul_measure_gt_le_of_map_rotation_eq_self` / 引理 `measure_le_mul_measure_gt_le_of_map_rotation_eq_self`

English:
lemma measure_le_mul_measure_gt_le_of_map_rotation_eq_self
  statement: [SFinite μ]
  proof: by
  calc μ {x | ‖x‖ <= a} * μ {x | b < ‖x‖}
  _ = (μ.prod μ) ({x | ‖x‖ <= a} ×ˢ {y | b < ‖y‖}) := by rw [Measure.prod_prod]
    -- This is the measure of two bands in the plane (draw a picture!)
  _ = (μ.prod μ) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := rfl
  _ = ((μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4)))) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := by
    -- We can rotate the bands since `μ.prod μ` is invariant under rotation
    rw [h]
  _ = (μ.prod μ) {p | ‖p.1 - p.2‖ / √2 <= a ∧ b < ‖p.1 + p.2‖ / √2} := by
    rw [Measure.map_apply (by fun_prop)]
    swap
    · refine MeasurableSet.inter ?_ ?_
      · change MeasurableSet {p : E × E | ‖p.1‖ <= a}
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · change MeasurableSet {p : E × E | b < ‖p.2‖}
        exact measurableSet_lt (by fun_prop) (by fun_prop)
    congr 1
    simp only [Set.preimage_ofPred_eq, ContinuousLinearMap.rotation_apply, Real.cos_neg,
      Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg]
    have h_twos : ‖2⁻¹ * √2‖ = (√2)⁻¹ := by
      simp only [norm_mul, norm_inv, Real.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nth_rw 1 [← Real.sq_sqrt (by simp : (0 : Real) <= 2)]
      rw [pow_two]; rw [mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [mul_one]
    congr! with p
    · rw [← sub_eq_add_neg, ← smul_sub, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
    · rw [← smul_add, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
  _ <= (μ.prod μ) {p | (b - a) / √2 < ‖p.1‖ ∧ (b - a) / √2 < ‖p.2‖} := by
    -- The rotated bands are contained in quadrants.
    refine measure_mono fun p => ?_
    simp only [Set.mem_ofPred_eq, and_imp]
    intro hp1 hp2
    suffices (b - a) / √2 < min ‖p.1‖ ‖p.2‖ from lt_min_iff.mp this
    calc (b - a) / √2
    _ < (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
      suffices b - a < ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 by
        calc (b - a) / √2 < (‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2) / √2 := by gcongr
        _ = (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
          field_simp; rw [Real.sq_sqrt (by positivity)]; ring
      calc b - a < ‖p.1 + p.2‖ / √2 - a := by gcongr
      _ <= ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 := by gcongr
    _ <= min ‖p.1‖ ‖p.2‖ := by
      have := norm_add_sub_norm_sub_le_two_mul_min p.1 p.2
      linarith
  _ = (μ.prod μ) ({x | (b - a) / √2 < ‖x‖} ×ˢ {y | (b - a) / √2 < ‖y‖}) := rfl
  _ <= μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by rw [Measure.prod_prod, pow_two]

中文:
引理 measure_le_mul_measure_gt_le_of_map_rotation_eq_self
  结论: [SFinite μ]
  证明: by
  calc μ {x | ‖x‖ <= a} * μ {x | b < ‖x‖}
  _ = (μ.prod μ) ({x | ‖x‖ <= a} ×ˢ {y | b < ‖y‖}) := by rw [Measure.prod_prod]
    -- This is the measure of two bands in the plane (draw a picture!)
  _ = (μ.prod μ) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := rfl
  _ = ((μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4)))) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := by
    -- We can rotate the bands since `μ.prod μ` is invariant under rotation
    rw [h]
  _ = (μ.prod μ) {p | ‖p.1 - p.2‖ / √2 <= a ∧ b < ‖p.1 + p.2‖ / √2} := by
    rw [Measure.map_apply (by fun_prop)]
    swap
    · refine MeasurableSet.inter ?_ ?_
      · change MeasurableSet {p : E × E | ‖p.1‖ <= a}
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · change MeasurableSet {p : E × E | b < ‖p.2‖}
        exact measurableSet_lt (by fun_prop) (by fun_prop)
    congr 1
    simp only [Set.preimage_ofPred_eq, ContinuousLinearMap.rotation_apply, Real.cos_neg,
      Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg]
    have h_twos : ‖2⁻¹ * √2‖ = (√2)⁻¹ := by
      simp only [norm_mul, norm_inv, Real.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nth_rw 1 [← Real.sq_sqrt (by simp : (0 : Real) <= 2)]
      rw [pow_two]; rw [mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [mul_one]
    congr! with p
    · rw [← sub_eq_add_neg, ← smul_sub, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
    · rw [← smul_add, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
  _ <= (μ.prod μ) {p | (b - a) / √2 < ‖p.1‖ ∧ (b - a) / √2 < ‖p.2‖} := by
    -- The rotated bands are contained in quadrants.
    refine measure_mono fun p => ?_
    simp only [Set.mem_ofPred_eq, and_imp]
    intro hp1 hp2
    suffices (b - a) / √2 < min ‖p.1‖ ‖p.2‖ from lt_min_iff.mp this
    calc (b - a) / √2
    _ < (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
      suffices b - a < ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 by
        calc (b - a) / √2 < (‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2) / √2 := by gcongr
        _ = (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
          field_simp; rw [Real.sq_sqrt (by positivity)]; ring
      calc b - a < ‖p.1 + p.2‖ / √2 - a := by gcongr
      _ <= ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 := by gcongr
    _ <= min ‖p.1‖ ‖p.2‖ := by
      have := norm_add_sub_norm_sub_le_two_mul_min p.1 p.2
      linarith
  _ = (μ.prod μ) ({x | (b - a) / √2 < ‖x‖} ×ˢ {y | (b - a) / √2 < ‖y‖}) := rfl
  _ <= μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by rw [Measure.prod_prod, pow_two]

Depends on / 依赖: Measure, Measure.prod_prod, prod_prod
-/
lemma measure_le_mul_measure_gt_le_of_map_rotation_eq_self [SFinite μ]
    (h : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (a b : Real) :
    μ {x | ‖x‖ <= a} * μ {x | b < ‖x‖} <= μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by
  calc μ {x | ‖x‖ <= a} * μ {x | b < ‖x‖}
  _ = (μ.prod μ) ({x | ‖x‖ <= a} ×ˢ {y | b < ‖y‖}) := by rw [Measure.prod_prod]
    -- This is the measure of two bands in the plane (draw a picture!)
  _ = (μ.prod μ) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := rfl
  _ = ((μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4)))) {p | ‖p.1‖ <= a ∧ b < ‖p.2‖} := by
    -- We can rotate the bands since `μ.prod μ` is invariant under rotation
    rw [h]
  _ = (μ.prod μ) {p | ‖p.1 - p.2‖ / √2 <= a ∧ b < ‖p.1 + p.2‖ / √2} := by
    rw [Measure.map_apply (by fun_prop)]
    swap
    · refine MeasurableSet.inter ?_ ?_
      · change MeasurableSet {p : E × E | ‖p.1‖ <= a}
        exact measurableSet_le (by fun_prop) (by fun_prop)
      · change MeasurableSet {p : E × E | b < ‖p.2‖}
        exact measurableSet_lt (by fun_prop) (by fun_prop)
    congr 1
    simp only [Set.preimage_ofPred_eq, ContinuousLinearMap.rotation_apply, Real.cos_neg,
      Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four, neg_smul, neg_neg]
    have h_twos : ‖2⁻¹ * √2‖ = (√2)⁻¹ := by
      simp only [norm_mul, norm_inv, Real.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nth_rw 1 [← Real.sq_sqrt (by simp : (0 : Real) <= 2)]
      rw [pow_two]; rw [mul_inv]; rw [mul_assoc]; rw [inv_mul_cancel₀ (by positivity)]; rw [mul_one]
    congr! with p
    · rw [← sub_eq_add_neg, ← smul_sub, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
    · rw [← smul_add, norm_smul, div_eq_inv_mul, div_eq_inv_mul, h_twos]
  _ <= (μ.prod μ) {p | (b - a) / √2 < ‖p.1‖ ∧ (b - a) / √2 < ‖p.2‖} := by
    -- The rotated bands are contained in quadrants.
    refine measure_mono fun p => ?_
    simp only [Set.mem_ofPred_eq, and_imp]
    intro hp1 hp2
    suffices (b - a) / √2 < min ‖p.1‖ ‖p.2‖ from lt_min_iff.mp this
    calc (b - a) / √2
    _ < (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
      suffices b - a < ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 by
        calc (b - a) / √2 < (‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2) / √2 := by gcongr
        _ = (‖p.1 + p.2‖ - ‖p.1 - p.2‖) / 2 := by
          field_simp; rw [Real.sq_sqrt (by positivity)]; ring
      calc b - a < ‖p.1 + p.2‖ / √2 - a := by gcongr
      _ <= ‖p.1 + p.2‖ / √2 - ‖p.1 - p.2‖ / √2 := by gcongr
    _ <= min ‖p.1‖ ‖p.2‖ := by
      have := norm_add_sub_norm_sub_le_two_mul_min p.1 p.2
      linarith
  _ = (μ.prod μ) ({x | (b - a) / √2 < ‖x‖} ×ˢ {y | (b - a) / √2 < ‖y‖}) := rfl
  _ <= μ {x | (b - a) / √2 < ‖x‖} ^ 2 := by rw [Measure.prod_prod, pow_two]

namespace Fernique

/--
Definition of `normThreshold` / `normThreshold` 的定义

English:
definition normThreshold
  signature: (a : Real)
  body: arithGeom √2 a a

中文:
定义 normThreshold
  签名: (a : 实数)
  定义体: arithGeom √2 a a

Depends on / 依赖: arithGeom
-/
noncomputable def normThreshold (a : Real) : Nat -> Real := arithGeom √2 a a

/--
lemma `normThreshold_zero` / 引理 `normThreshold_zero`

English:
lemma normThreshold_zero
  statement: normThreshold a 0 = a
  proof: rfl

中文:
引理 normThreshold_zero
  结论: normThreshold a 0 = a
  证明: rfl
-/
lemma normThreshold_zero : normThreshold a 0 = a := rfl

/--
lemma `normThreshold_add_one` / 引理 `normThreshold_add_one`

English:
lemma normThreshold_add_one
  given: (n : Nat)
  statement: normThreshold a (n + 1) = √2 * normThreshold a n + a
  proof: rfl

中文:
引理 normThreshold_add_one
  条件: (n : 自然数)
  结论: normThreshold a (n + 1) = √2 * normThreshold a n + a
  证明: rfl
-/
lemma normThreshold_add_one (n : Nat) : normThreshold a (n + 1) = √2 * normThreshold a n + a := rfl

/--
lemma `measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self` / 引理 `measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self`

English:
lemma measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self
  statement: [SFinite μ]
  proof: by
  convert! measure_le_mul_measure_gt_le_of_map_rotation_eq_self h_rot _ _
  simp [normThreshold_add_one]

中文:
引理 measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self
  结论: [SFinite μ]
  证明: by
  convert! measure_le_mul_measure_gt_le_of_map_rotation_eq_self h_rot _ _
  simp [normThreshold_add_one]

Depends on / 依赖: convert, h_rot, measure_le_mul_measure_gt_le_of_map_rotation_eq_self, normThreshold_add_one
-/
lemma measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self [SFinite μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) (a : Real) (n : Nat) :
    μ {x | ‖x‖ <= a} * μ {x | normThreshold a (n + 1) < ‖x‖}
      <= μ {x | normThreshold a n < ‖x‖} ^ 2 := by
  convert! measure_le_mul_measure_gt_le_of_map_rotation_eq_self h_rot _ _
  simp [normThreshold_add_one]

/--
lemma `lt_normThreshold_zero` / 引理 `lt_normThreshold_zero`

English:
lemma lt_normThreshold_zero
  given: (ha_pos : 0 < a)
  statement: a / (1 - √2) < normThreshold a 0
  proof: by
  simp only [normThreshold_zero]
  calc a / (1 - √2)
  _ <= 0 := div_nonpos_of_nonneg_of_nonpos ha_pos.le (by simp)
  _ < a := ha_pos

中文:
引理 lt_normThreshold_zero
  条件: (ha_pos : 0 < a)
  结论: a / (1 - √2) < normThreshold a 0
  证明: by
  simp only [normThreshold_zero]
  calc a / (1 - √2)
  _ <= 0 := div_nonpos_of_nonneg_of_nonpos ha_pos.le (by simp)
  _ < a := ha_pos

Depends on / 依赖: div_nonpos_of_nonneg_of_nonpos, ha_pos, ha_pos.le, normThreshold_zero
-/
lemma lt_normThreshold_zero (ha_pos : 0 < a) : a / (1 - √2) < normThreshold a 0 := by
  simp only [normThreshold_zero]
  calc a / (1 - √2)
  _ <= 0 := div_nonpos_of_nonneg_of_nonpos ha_pos.le (by simp)
  _ < a := ha_pos

/--
lemma `normThreshold_strictMono` / 引理 `normThreshold_strictMono`

English:
lemma normThreshold_strictMono
  given: (ha_pos : 0 < a)
  statement: StrictMono (normThreshold a)
  proof: arithGeom_strictMono Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

中文:
引理 normThreshold_strictMono
  条件: (ha_pos : 0 < a)
  结论: 严格递增 (normThreshold a)
  证明: arithGeom_strictMono Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

Depends on / 依赖: Real.one_lt_sqrt_two, arithGeom_strictMono, ha_pos, lt_normThreshold_zero, one_lt_sqrt_two
-/
lemma normThreshold_strictMono (ha_pos : 0 < a) : StrictMono (normThreshold a) :=
  arithGeom_strictMono Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

/--
lemma `tendsto_normThreshold_atTop` / 引理 `tendsto_normThreshold_atTop`

English:
lemma tendsto_normThreshold_atTop
  given: (ha_pos : 0 < a)
  statement: Tendsto (normThreshold a) atTop atTop
  proof: tendsto_arithGeom_atTop_of_one_lt Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

中文:
引理 tendsto_normThreshold_atTop
  条件: (ha_pos : 0 < a)
  结论: 收敛 (normThreshold a) atTop atTop
  证明: tendsto_arithGeom_atTop_of_one_lt Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

Depends on / 依赖: Real.one_lt_sqrt_two, ha_pos, lt_normThreshold_zero, one_lt_sqrt_two, tendsto_arithGeom_atTop_of_one_lt
-/
lemma tendsto_normThreshold_atTop (ha_pos : 0 < a) : Tendsto (normThreshold a) atTop atTop :=
  tendsto_arithGeom_atTop_of_one_lt Real.one_lt_sqrt_two (lt_normThreshold_zero ha_pos)

/--
lemma `normThreshold_eq` / 引理 `normThreshold_eq`

English:
lemma normThreshold_eq
  given: (n : Nat)
  statement: normThreshold a n = a * (1 + √2) * (√2 ^ (n + 1) - 1)
  proof: by
  rw [normThreshold]; rw [arithGeom_same_eq_mul_div (by simp)]; rw [div_eq_mul_inv]; rw [Real.inv_sqrt_two_sub_one]
  ring

中文:
引理 normThreshold_eq
  条件: (n : 自然数)
  结论: normThreshold a n = a * (1 + √2) * (√2 ^ (n + 1) - 1)
  证明: by
  rw [normThreshold]; rw [arithGeom_same_eq_mul_div (by simp)]; rw [div_eq_mul_inv]; rw [Real.inv_sqrt_two_sub_one]
  ring

Depends on / 依赖: Real.inv_sqrt_two_sub_one, arithGeom_same_eq_mul_div, div_eq_mul_inv, inv_sqrt_two_sub_one, normThreshold
-/
lemma normThreshold_eq (n : Nat) : normThreshold a n = a * (1 + √2) * (√2 ^ (n + 1) - 1) := by
  rw [normThreshold]; rw [arithGeom_same_eq_mul_div (by simp)]; rw [div_eq_mul_inv]; rw [Real.inv_sqrt_two_sub_one]
  ring

/--
lemma `sq_normThreshold_add_one_le` / 引理 `sq_normThreshold_add_one_le`

English:
lemma sq_normThreshold_add_one_le
  given: (n : Nat)
  proof: by
  simp_rw [normThreshold_eq, mul_pow, mul_assoc]
  gcongr
  calc (√2 ^ (n + 2) - 1) ^ 2
  _ <= (√2 ^ (n + 2)) ^ 2 := by
    gcongr
    · calc 0 <= √2 ^ (0 + 2) - 1 := by simp
      _ <= √2 ^ (n + 2) - 1 := by gcongr <;> simp
    · exact sub_le_self _ (by simp)
  _ = 2 ^ (n + 2) := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]

中文:
引理 sq_normThreshold_add_one_le
  条件: (n : 自然数)
  证明: by
  simp_rw [normThreshold_eq, mul_pow, mul_assoc]
  gcongr
  calc (√2 ^ (n + 2) - 1) ^ 2
  _ <= (√2 ^ (n + 2)) ^ 2 := by
    gcongr
    · calc 0 <= √2 ^ (0 + 2) - 1 := by simp
      _ <= √2 ^ (n + 2) - 1 := by gcongr <;> simp
    · exact sub_le_self _ (by simp)
  _ = 2 ^ (n + 2) := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]

Depends on / 依赖: Real.sq_sqrt, mul_assoc, mul_comm, mul_pow, normThreshold_eq, pow_mul, simp_rw, sq_sqrt, sub_le_self
-/
lemma sq_normThreshold_add_one_le (n : Nat) :
    normThreshold a (n + 1) ^ 2 <= a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2) := by
  simp_rw [normThreshold_eq, mul_pow, mul_assoc]
  gcongr
  calc (√2 ^ (n + 2) - 1) ^ 2
  _ <= (√2 ^ (n + 2)) ^ 2 := by
    gcongr
    · calc 0 <= √2 ^ (0 + 2) - 1 := by simp
      _ <= √2 ^ (n + 2) - 1 := by gcongr <;> simp
    · exact sub_le_self _ (by simp)
  _ = 2 ^ (n + 2) := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]

/--
lemma `measure_gt_normThreshold_le_rpow` / 引理 `measure_gt_normThreshold_le_rpow`

English:
lemma measure_gt_normThreshold_le_rpow
  statement: [IsProbabilityMeasure μ]
  proof: by
  let c := μ {x | ‖x‖ <= a}
  replace hc_gt : 2⁻¹ < c := ha_gt
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) hc_gt.le
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, normThreshold_zero]
    rw [ENNReal.mul_div_cancel hc_pos.ne' hc_lt_top.ne]
    refine le_of_eq ?_
    rw [← prob_compl_eq_one_sub (measurableSet_le (by fun_prop) (by fun_prop))]
    congr with x
    simp
  | succ n hn =>
    have h_mul_le : c * μ {x | normThreshold a (n + 1) < ‖x‖}
        <= μ {x | normThreshold a n < ‖x‖} ^ 2 :=
      measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self h_rot _ _
    calc μ {x | normThreshold a (n + 1) < ‖x‖}
    _ = c⁻¹ * (c * μ {x | normThreshold a (n + 1) < ‖x‖}) := by
      rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]
    _ <= c⁻¹ * μ {x | normThreshold a n < ‖x‖} ^ 2 := by gcongr
    _ <= c⁻¹ * (c * ((1 - c) / c) ^ 2 ^ n) ^ 2 := by gcongr
    _ = c * ((1 - c) / c) ^ 2 ^ (n + 1) := by
      rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]; rw [pow_add]; rw [pow_one]

中文:
引理 measure_gt_normThreshold_le_rpow
  结论: [是概率测度 μ]
  证明: by
  let c := μ {x | ‖x‖ <= a}
  replace hc_gt : 2⁻¹ < c := ha_gt
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) hc_gt.le
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, normThreshold_zero]
    rw [ENNReal.mul_div_cancel hc_pos.ne' hc_lt_top.ne]
    refine le_of_eq ?_
    rw [← prob_compl_eq_one_sub (measurableSet_le (by fun_prop) (by fun_prop))]
    congr with x
    simp
  | succ n hn =>
    have h_mul_le : c * μ {x | normThreshold a (n + 1) < ‖x‖}
        <= μ {x | normThreshold a n < ‖x‖} ^ 2 :=
      measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self h_rot _ _
    calc μ {x | normThreshold a (n + 1) < ‖x‖}
    _ = c⁻¹ * (c * μ {x | normThreshold a (n + 1) < ‖x‖}) := by
      rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]
    _ <= c⁻¹ * μ {x | normThreshold a n < ‖x‖} ^ 2 := by gcongr
    _ <= c⁻¹ * (c * ((1 - c) / c) ^ 2 ^ n) ^ 2 := by gcongr
    _ = c * ((1 - c) / c) ^ 2 ^ (n + 1) := by
      rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]; rw [pow_add]; rw [pow_one]

Depends on / 依赖: ENNReal, ENNReal.mul_div_cancel, fun_prop, h_mul_le, ha_gt, hc_gt, hc_gt.le, hc_lt_top, hc_lt_top.ne, hc_pos, hc_pos.ne, le_of_eq, lt_of_lt_of_le, measurableSet_le, measure_lt_top, mul_div_cancel, normThresho, normThreshold, normThreshold_zero, pow_one
-/
lemma measure_gt_normThreshold_le_rpow [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (n : Nat) :
    μ {x | normThreshold a n < ‖x‖}
      <= μ {x | ‖x‖ <= a} * ((1 - μ {x | ‖x‖ <= a}) / μ {x | ‖x‖ <= a}) ^ (2 ^ n) := by
  let c := μ {x | ‖x‖ <= a}
  replace hc_gt : 2⁻¹ < c := ha_gt
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) hc_gt.le
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, normThreshold_zero]
    rw [ENNReal.mul_div_cancel hc_pos.ne' hc_lt_top.ne]
    refine le_of_eq ?_
    rw [← prob_compl_eq_one_sub (measurableSet_le (by fun_prop) (by fun_prop))]
    congr with x
    simp
  | succ n hn =>
    have h_mul_le : c * μ {x | normThreshold a (n + 1) < ‖x‖}
        <= μ {x | normThreshold a n < ‖x‖} ^ 2 :=
      measure_le_mul_measure_gt_normThreshold_le_of_map_rotation_eq_self h_rot _ _
    calc μ {x | normThreshold a (n + 1) < ‖x‖}
    _ = c⁻¹ * (c * μ {x | normThreshold a (n + 1) < ‖x‖}) := by
      rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]
    _ <= c⁻¹ * μ {x | normThreshold a n < ‖x‖} ^ 2 := by gcongr
    _ <= c⁻¹ * (c * ((1 - c) / c) ^ 2 ^ n) ^ 2 := by gcongr
    _ = c * ((1 - c) / c) ^ 2 ^ (n + 1) := by
      rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [pow_two]; rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel hc_pos.ne' hc_lt_top.ne]; rw [one_mul]; rw [pow_add]; rw [pow_one]

/--
lemma `measure_gt_normThreshold_le_exp` / 引理 `measure_gt_normThreshold_le_exp`

English:
lemma measure_gt_normThreshold_le_exp
  statement: [IsProbabilityMeasure μ]
  proof: by
  let c := μ {x | ‖x‖ <= a}
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) ha_gt.le
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have hc_ratio_pos : 0 < (c / (1 - c)).toReal := by
    rw [ENNReal.toReal_div]; rw [div_pos_iff_of_pos_right]
    · simp [ENNReal.toReal_pos_iff, hc_pos, hc_lt_top]
    · simp [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, hc_one_sub_lt_top]
  refine (measure_gt_normThreshold_le_rpow h_rot ha_gt n).trans_eq ?_
  congr
  rw [← Real.log_inv]; rw [mul_comm (Real.log _)]; rw [← Real.log_rpow (by positivity)]; rw [Real.exp_log (by positivity)]; rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]; rw [ENNReal.toReal_div]; rw [inv_div]; rw [← ENNReal.toReal_div]; rw [ENNReal.ofReal_toReal]
  · norm_cast
  · exact ENNReal.div_ne_top (by finiteness) (lt_trans (by simp) ha_gt).ne'

中文:
引理 measure_gt_normThreshold_le_exp
  结论: [是概率测度 μ]
  证明: by
  let c := μ {x | ‖x‖ <= a}
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) ha_gt.le
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have hc_ratio_pos : 0 < (c / (1 - c)).toReal := by
    rw [ENNReal.toReal_div]; rw [div_pos_iff_of_pos_right]
    · simp [ENNReal.toReal_pos_iff, hc_pos, hc_lt_top]
    · simp [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, hc_one_sub_lt_top]
  refine (measure_gt_normThreshold_le_rpow h_rot ha_gt n).trans_eq ?_
  congr
  rw [← Real.log_inv]; rw [mul_comm (Real.log _)]; rw [← Real.log_rpow (by positivity)]; rw [Real.exp_log (by positivity)]; rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]; rw [ENNReal.toReal_div]; rw [inv_div]; rw [← ENNReal.toReal_div]; rw [ENNReal.ofReal_toReal]
  · norm_cast
  · exact ENNReal.div_ne_top (by finiteness) (lt_trans (by simp) ha_gt).ne'

Depends on / 依赖: ENNReal, ENNReal.toReal_div, ENNReal.toReal_pos_iff, div_pos_iff_of_pos_right, ha_gt, ha_gt.le, ha_lt, hc_lt, hc_lt_top, hc_one_sub_lt_top, hc_pos, hc_ratio_pos, lt_of_lt_of_le, lt_top_of_lt, measure_lt_top, replace, toReal, toReal_div, toReal_pos_iff, trans_lt
-/
lemma measure_gt_normThreshold_le_exp [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ <= a} < 1) (n : Nat) :
    μ {x | normThreshold a n < ‖x‖}
      <= μ {x | ‖x‖ <= a} * .ofReal (rexp
        (-Real.log (μ {x | ‖x‖ <= a} / (1 - μ {x | ‖x‖ <= a})).toReal * 2 ^ n)) := by
  let c := μ {x | ‖x‖ <= a}
  have hc_pos : 0 < c := lt_of_lt_of_le (by simp) ha_gt.le
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have hc_ratio_pos : 0 < (c / (1 - c)).toReal := by
    rw [ENNReal.toReal_div]; rw [div_pos_iff_of_pos_right]
    · simp [ENNReal.toReal_pos_iff, hc_pos, hc_lt_top]
    · simp [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, hc_one_sub_lt_top]
  refine (measure_gt_normThreshold_le_rpow h_rot ha_gt n).trans_eq ?_
  congr
  rw [← Real.log_inv]; rw [mul_comm (Real.log _)]; rw [← Real.log_rpow (by positivity)]; rw [Real.exp_log (by positivity)]; rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]; rw [ENNReal.toReal_div]; rw [inv_div]; rw [← ENNReal.toReal_div]; rw [ENNReal.ofReal_toReal]
  · norm_cast
  · exact ENNReal.div_ne_top (by finiteness) (lt_trans (by simp) ha_gt).ne'

/--
Definition of `logRatio` / `logRatio` 的定义

English:
definition logRatio
  signature: (c : Real>=0∞)
  body: Real.log (c.toReal / (1 - c).toReal) / (8 * (1 + √2) ^ 2)

中文:
定义 logRatio
  签名: (c : 实数>=0∞)
  定义体: Real.log (c.toReal / (1 - c).toReal) / (8 * (1 + √2) ^ 2)

Depends on / 依赖: Real.log, c.toReal, toReal
-/
noncomputable def logRatio (c : Real>=0∞) : Real :=
  Real.log (c.toReal / (1 - c).toReal) / (8 * (1 + √2) ^ 2)

/--
lemma `logRatio_pos` / 引理 `logRatio_pos`

English:
lemma logRatio_pos
  given: {c : Real>=0∞} (hc_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1)
  statement: 0 < logRatio c
  proof: by
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [one_lt_div_iff]
  refine Or.inl ⟨?_, ?_⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
    finiteness
  · refine (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr ?_
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hc_gt

中文:
引理 logRatio_pos
  条件: {c : 实数>=0∞} (hc_gt : (2 : 实数>=0∞)⁻¹ < c) (hc_lt : c < 1)
  结论: 0 < logRatio c
  证明: by
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [one_lt_div_iff]
  refine Or.inl ⟨?_, ?_⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
    finiteness
  · refine (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr ?_
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hc_gt

Depends on / 依赖: ENNReal, ENNReal.div_lt_iff, ENNReal.sub_lt_of_lt_add, ENNReal.toReal_lt_toReal, ENNReal.toReal_pos_iff, Or.inl, Real.log_pos, div_lt_iff, div_pos, finiteness, hc_gt, hc_lt, hc_lt.le, inv_eq_one_div, log_pos, mul_comm, one_lt_div_iff, sub_lt_of_lt_add, toReal_lt_toReal, toReal_pos_iff
-/
lemma logRatio_pos {c : Real>=0∞} (hc_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1) : 0 < logRatio c := by
  refine div_pos (Real.log_pos ?_) (by positivity)
  rw [one_lt_div_iff]
  refine Or.inl ⟨?_, ?_⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
    finiteness
  · refine (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr ?_
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hc_gt

/--
lemma `logRatio_nonneg` / 引理 `logRatio_nonneg`

English:
lemma logRatio_nonneg
  given: {c : Real>=0∞} (hc_ge : (2 : Real>=0∞)⁻¹ <= c) (hc_le : c <= 1)
  statement: 0 <= logRatio c
  proof: by
  cases hc_ge.eq_or_lt'
  · simp [logRatio, *]
  cases hc_le.eq_or_lt'
  · simp [logRatio, *]
  exact (logRatio_pos ‹_› ‹_›).le

中文:
引理 logRatio_nonneg
  条件: {c : 实数>=0∞} (hc_ge : (2 : 实数>=0∞)⁻¹ <= c) (hc_le : c <= 1)
  结论: 0 <= logRatio c
  证明: by
  cases hc_ge.eq_or_lt'
  · simp [logRatio, *]
  cases hc_le.eq_or_lt'
  · simp [logRatio, *]
  exact (logRatio_pos ‹_› ‹_›).le

Depends on / 依赖: eq_or_lt, hc_ge, hc_ge.eq_or_lt, hc_le, hc_le.eq_or_lt, logRatio, logRatio_pos
-/
lemma logRatio_nonneg {c : Real>=0∞} (hc_ge : (2 : Real>=0∞)⁻¹ <= c) (hc_le : c <= 1) : 0 <= logRatio c := by
  cases hc_ge.eq_or_lt'
  · simp [logRatio, *]
  cases hc_le.eq_or_lt'
  · simp [logRatio, *]
  exact (logRatio_pos ‹_› ‹_›).le

/--
lemma `logRatio_mono` / 引理 `logRatio_mono`

English:
lemma logRatio_mono
  given: {c d : Real>=0∞} (hc : (2 : Real>=0∞)⁻¹ < c) (hd : d < 1) (h : c <= d)
  proof: by
  unfold logRatio
  gcongr
  · refine div_pos ?_ ?_
    · rw [ENNReal.toReal_pos_iff]
      exact ⟨lt_trans (by norm_num) hc, h.trans_lt (by finiteness)⟩
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
      exact ⟨h.trans_lt hd, by finiteness⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hd, true_and]
    finiteness
  · finiteness
  · finiteness

中文:
引理 logRatio_mono
  条件: {c d : 实数>=0∞} (hc : (2 : 实数>=0∞)⁻¹ < c) (hd : d < 1) (h : c <= d)
  证明: by
  unfold logRatio
  gcongr
  · refine div_pos ?_ ?_
    · rw [ENNReal.toReal_pos_iff]
      exact ⟨lt_trans (by norm_num) hc, h.trans_lt (by finiteness)⟩
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
      exact ⟨h.trans_lt hd, by finiteness⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hd, true_and]
    finiteness
  · finiteness
  · finiteness

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff, div_pos, finiteness, h.trans_lt, logRatio, lt_trans, toReal_pos_iff, trans_lt, true_and, tsub_pos_iff_lt
-/
lemma logRatio_mono {c d : Real>=0∞} (hc : (2 : Real>=0∞)⁻¹ < c) (hd : d < 1) (h : c <= d) :
    logRatio c <= logRatio d := by
  unfold logRatio
  gcongr
  · refine div_pos ?_ ?_
    · rw [ENNReal.toReal_pos_iff]
      exact ⟨lt_trans (by norm_num) hc, h.trans_lt (by finiteness)⟩
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
      exact ⟨h.trans_lt hd, by finiteness⟩
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hd, true_and]
    finiteness
  · finiteness
  · finiteness

/--
lemma `logRatio_mul_normThreshold_add_one_le` / 引理 `logRatio_mul_normThreshold_add_one_le`

English:
lemma logRatio_mul_normThreshold_add_one_le
  statement: {c : Real>=0∞}
  proof: by
  by_cases ha : a = 0
  · simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right, inv_pos, mul_nonneg_iff_of_pos_left]
    refine Real.log_nonneg ?_
    rw [one_le_div]
    · refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr ?_
      refine tsub_le_iff_left.mpr ?_
      rw [← two_mul]
      rw [inv_eq_one_div]; rw [ENNReal.div_lt_iff (by simp) (by simp)]; rw [mul_comm] at hc_gt
      exact hc_gt.le
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
      finiteness
  calc logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
  _ <= logRatio c * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2)) * a⁻¹ ^ 2 := by
    gcongr
    · exact (logRatio_pos hc_gt hc_lt).le
    · exact sq_normThreshold_add_one_le n
  _ = 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
    unfold logRatio
    field

中文:
引理 logRatio_mul_normThreshold_add_one_le
  结论: {c : 实数>=0∞}
  证明: by
  by_cases ha : a = 0
  · simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right, inv_pos, mul_nonneg_iff_of_pos_left]
    refine Real.log_nonneg ?_
    rw [one_le_div]
    · refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr ?_
      refine tsub_le_iff_left.mpr ?_
      rw [← two_mul]
      rw [inv_eq_one_div]; rw [ENNReal.div_lt_iff (by simp) (by simp)]; rw [mul_comm] at hc_gt
      exact hc_gt.le
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
      finiteness
  calc logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
  _ <= logRatio c * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2)) * a⁻¹ ^ 2 := by
    gcongr
    · exact (logRatio_pos hc_gt hc_lt).le
    · exact sq_normThreshold_add_one_le n
  _ = 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
    unfold logRatio
    field

Depends on / 依赖: ENNReal, ENNReal.div_lt_iff, ENNReal.toRea, ENNReal.toReal_le_toReal, Nat.ofNat_pos, OfNat.ofNat_ne_zero, Real.log_nonneg, div_lt_iff, finiteness, hc_gt, hc_gt.le, inv_eq_one_div, inv_pos, inv_zero, log_nonneg, mul_comm, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_right, mul_zero, ne_eq
-/
lemma logRatio_mul_normThreshold_add_one_le {c : Real>=0∞}
    (hc_gt : (2 : Real>=0∞)⁻¹ < c) (hc_lt : c < 1) (n : Nat) :
    logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
      <= 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
  by_cases ha : a = 0
  · simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right, inv_pos, mul_nonneg_iff_of_pos_left]
    refine Real.log_nonneg ?_
    rw [one_le_div]
    · refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr ?_
      refine tsub_le_iff_left.mpr ?_
      rw [← two_mul]
      rw [inv_eq_one_div]; rw [ENNReal.div_lt_iff (by simp) (by simp)]; rw [mul_comm] at hc_gt
      exact hc_gt.le
    · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt, true_and]
      finiteness
  calc logRatio c * normThreshold a (n + 1) ^ 2 * a⁻¹ ^ 2
  _ <= logRatio c * (a ^ 2 * (1 + √2) ^ 2 * 2 ^ (n + 2)) * a⁻¹ ^ 2 := by
    gcongr
    · exact (logRatio_pos hc_gt hc_lt).le
    · exact sq_normThreshold_add_one_le n
  _ = 2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n := by
    unfold logRatio
    field

open Metric in
/--
lemma `lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le` / 引理 `lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le`

English:
lemma lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le
  statement: [IsProbabilityMeasure μ]
  proof: let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c * a⁻¹ ^ 2
  calc ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
  -- We bound the function on the set by its maximal value, at the outer boundary of the annulus
  _ <= ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
      .ofReal (rexp (C * t (n + 1) ^ 2)) ∂μ := by
    refine setLIntegral_mono (by fun_prop) fun x hx => ?_
    gcongr
    · exact mul_nonneg (logRatio_pos ha_gt ha_lt).le (by positivity)
    · simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.1
  -- The integral of a constant is the constant times the measure of the set
  _ = .ofReal (rexp (C * t (n + 1) ^ 2)) * μ (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)) := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, C, t]
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
    gcongr
    intro x
    simp
  -- We obtained an upper bound on the measure of that annulus in a previous lemma
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    conv_rhs => rw [mul_assoc]
    gcongr
    exact measure_gt_normThreshold_le_exp h_rot ha_gt ha_lt n
  _ <= .ofReal (rexp (2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    gcongr ENNReal.ofReal (rexp ?_) * _ * _
    convert! logRatio_mul_normThreshold_add_one_le ha_gt ha_lt n (a := a) using 1
    ring
  _ = c * .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    rw [mul_comm _ c]; rw [mul_assoc]; rw [← ENNReal.ofReal_mul (by positivity)]; rw [← Real.exp_add]
    congr
    norm_cast
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_div]
    ring

@[deprecated (since := "2026-06-03")]
alias lintegral_closedBall_diff_exp_logRatio_mul_sq_le :=
  lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le

中文:
引理 lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le
  结论: [是概率测度 μ]
  证明: let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c * a⁻¹ ^ 2
  calc ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
  -- We bound the function on the set by its maximal value, at the outer boundary of the annulus
  _ <= ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
      .ofReal (rexp (C * t (n + 1) ^ 2)) ∂μ := by
    refine setLIntegral_mono (by fun_prop) fun x hx => ?_
    gcongr
    · exact mul_nonneg (logRatio_pos ha_gt ha_lt).le (by positivity)
    · simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.1
  -- The integral of a constant is the constant times the measure of the set
  _ = .ofReal (rexp (C * t (n + 1) ^ 2)) * μ (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)) := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, C, t]
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
    gcongr
    intro x
    simp
  -- We obtained an upper bound on the measure of that annulus in a previous lemma
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    conv_rhs => rw [mul_assoc]
    gcongr
    exact measure_gt_normThreshold_le_exp h_rot ha_gt ha_lt n
  _ <= .ofReal (rexp (2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    gcongr ENNReal.ofReal (rexp ?_) * _ * _
    convert! logRatio_mul_normThreshold_add_one_le ha_gt ha_lt n (a := a) using 1
    ring
  _ = c * .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    rw [mul_comm _ c]; rw [mul_assoc]; rw [← ENNReal.ofReal_mul (by positivity)]; rw [← Real.exp_add]
    congr
    norm_cast
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_div]
    ring

@[deprecated (since := "2026-06-03")]
alias lintegral_closedBall_diff_exp_logRatio_mul_sq_le :=
  lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le

Depends on / 依赖: closedBall, logRatio, normThreshold, ofReal
-/
lemma lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ <= a} < 1) (n : Nat) :
    ∫⁻ x in (closedBall 0 (normThreshold a (n + 1)) \ closedBall 0 (normThreshold a n)),
        .ofReal (rexp (logRatio (μ {x | ‖x‖ <= a}) * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      <= μ {x | ‖x‖ <= a} * .ofReal (rexp
          (-2⁻¹ * Real.log (μ {x | ‖x‖ <= a} / (1 - μ {x | ‖x‖ <= a})).toReal * 2 ^ n)) :=
  let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c * a⁻¹ ^ 2
  calc ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
  -- We bound the function on the set by its maximal value, at the outer boundary of the annulus
  _ <= ∫⁻ x in (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)),
      .ofReal (rexp (C * t (n + 1) ^ 2)) ∂μ := by
    refine setLIntegral_mono (by fun_prop) fun x hx => ?_
    gcongr
    · exact mul_nonneg (logRatio_pos ha_gt ha_lt).le (by positivity)
    · simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.1
  -- The integral of a constant is the constant times the measure of the set
  _ = .ofReal (rexp (C * t (n + 1) ^ 2)) * μ (closedBall 0 (t (n + 1)) \ closedBall 0 (t n)) := by
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, C, t]
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2)) * μ {x | t n < ‖x‖} := by
    gcongr
    intro x
    simp
  -- We obtained an upper bound on the measure of that annulus in a previous lemma
  _ <= .ofReal (rexp (C * t (n + 1) ^ 2))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    conv_rhs => rw [mul_assoc]
    gcongr
    exact measure_gt_normThreshold_le_exp h_rot ha_gt ha_lt n
  _ <= .ofReal (rexp (2⁻¹ * Real.log (c.toReal / (1 - c).toReal) * 2 ^ n))
      * c * .ofReal (rexp (-Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    gcongr ENNReal.ofReal (rexp ?_) * _ * _
    convert! logRatio_mul_normThreshold_add_one_le ha_gt ha_lt n (a := a) using 1
    ring
  _ = c * .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
    rw [mul_comm _ c]; rw [mul_assoc]; rw [← ENNReal.ofReal_mul (by positivity)]; rw [← Real.exp_add]
    congr
    norm_cast
    simp only [Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_div]
    ring

@[deprecated (since := "2026-06-03")]
alias lintegral_closedBall_diff_exp_logRatio_mul_sq_le :=
  lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le

set_option backward.isDefEq.respectTransparency.types false in
open Metric in
/--
lemma `lintegral_exp_mul_sq_norm_le_mul` / 引理 `lintegral_exp_mul_sq_norm_le_mul`

English:
lemma lintegral_exp_mul_sq_norm_le_mul
  statement: [IsProbabilityMeasure μ]
  proof: by
  let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c' * a⁻¹ ^ 2
  have hc'_le : c' <= 1 := hc'.trans prob_le_one
  -- We want to bound an integral
  change ∫⁻ x, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= c * (.ofReal (rexp (logRatio c'))
            + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n)))
  -- We will cut the space into a ball of radius `a` and annuli defined from the thresholds `t n`
  -- and bound the integral on each piece.
  -- First, we bound the integral on the ball of radius `a`
  have ht_int_zero : ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
    calc ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ <= ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * a ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx => ?_
      gcongr
      · exact mul_nonneg (logRatio_nonneg hc'_gt.le hc'_le) (by positivity)
      · simpa using hx
    _ = μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
      rw [mul_comm]
      simp only [inv_pow, C]
      field_simp
      congr with x
      simp
  -- We dispense with an edge case. If `μ {x | ‖x‖ ≤ a} = 1`, then the integral over
  -- the complement of the ball is zero and we are done.
  by_cases ha : μ {x | ‖x‖ <= a} = 1
  · simp only [ha, one_mul, ENNReal.toReal_div, neg_mul, ge_iff_le, c] at ht_int_zero ⊢
    refine le_add_right ((le_of_eq ?_).trans ht_int_zero)
    rw [← setLIntegral_univ]
    refine setLIntegral_congr ?_
    rw [← ae_iff_prob_eq_one ?_] at ha
    · rw [eventuallyEq_comm, ae_eq_univ]
      change μ {x | ¬ x in closedBall 0 a} = 0
      rw [← ae_iff]
      filter_upwards [ha] with x hx using by simp [hx]
    · fun_prop
  -- So we can assume `μ {x | ‖x‖ ≤ a} < 1`, which implies `c' < 1`
  have ha_lt : μ {x | ‖x‖ <= a} < 1 := lt_of_le_of_ne prob_le_one ha
  have hc'_lt : c' < 1 := lt_of_le_of_lt hc' ha_lt
  -- We cut the space into a ball and a sequence of annuli between the thresholds `t n`
  have h_iUnion : (Set.univ : Set E)
      = closedBall 0 a union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion,
      Set.mem_sdiff, not_le, true_iff]
    simp_rw [and_comm (b := t _ < ‖x‖)]
    rcases le_or_gt (‖x‖) a with ha' | ha'
    · exact Or.inl ha'
· exact Or.inr (normThreshold_strictMono ha_pos).exists_between_of_tendsto_atTop
        (tendsto_normThreshold_atTop ha_pos) ha'
  -- The integral over the union is at most the sum of the integrals
  rw [← setLIntegral_univ]; rw [h_iUnion]
  have : ∫⁻ x in closedBall 0 (t 0) union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= ∫⁻ x in closedBall 0 (t 0), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ +
        ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
          .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ := by
    refine (lintegral_union_le _ _ _).trans ?_
    gcongr
    exact lintegral_iUnion_le _ _
  -- Each of the integrals in the sum correspond to the terms in the goal
  refine this.trans ?_
  rw [mul_add]
  gcongr
  -- We already proved the upper bound for the ball
  · exact ht_int_zero
  rw [← ENNReal.tsum_mul_left]
  gcongr with n
  -- Now we prove the bound for each annulus, by calling a previous lemma
  refine (le_trans ?_ (lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le h_rot
    (hc'_gt.trans_le hc') ha_lt n)).trans ?_
  · gcongr
    simp only [inv_pow, C]
    field_simp
    exact logRatio_mono hc'_gt ha_lt hc'
  gcongr _ * ENNReal.ofReal (rexp ?_)
  simp only [ENNReal.toReal_div, neg_mul, neg_le_neg_iff]
  gcongr
  · refine div_pos ?_ ?_
    all_goals rw [ENNReal.toReal_pos_iff]
    · exact ⟨lt_trans (by norm_num) hc'_gt, by finiteness⟩
    · simp only [tsub_pos_iff_lt, hc'_lt, true_and]
      finiteness
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
    exact ⟨ha_lt, by finiteness⟩
  · finiteness
  · finiteness

中文:
引理 lintegral_exp_mul_sq_norm_le_mul
  结论: [是概率测度 μ]
  证明: by
  let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c' * a⁻¹ ^ 2
  have hc'_le : c' <= 1 := hc'.trans prob_le_one
  -- We want to bound an integral
  change ∫⁻ x, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= c * (.ofReal (rexp (logRatio c'))
            + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n)))
  -- We will cut the space into a ball of radius `a` and annuli defined from the thresholds `t n`
  -- and bound the integral on each piece.
  -- First, we bound the integral on the ball of radius `a`
  have ht_int_zero : ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
    calc ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ <= ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * a ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx => ?_
      gcongr
      · exact mul_nonneg (logRatio_nonneg hc'_gt.le hc'_le) (by positivity)
      · simpa using hx
    _ = μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
      rw [mul_comm]
      simp only [inv_pow, C]
      field_simp
      congr with x
      simp
  -- We dispense with an edge case. If `μ {x | ‖x‖ ≤ a} = 1`, then the integral over
  -- the complement of the ball is zero and we are done.
  by_cases ha : μ {x | ‖x‖ <= a} = 1
  · simp only [ha, one_mul, ENNReal.toReal_div, neg_mul, ge_iff_le, c] at ht_int_zero ⊢
    refine le_add_right ((le_of_eq ?_).trans ht_int_zero)
    rw [← setLIntegral_univ]
    refine setLIntegral_congr ?_
    rw [← ae_iff_prob_eq_one ?_] at ha
    · rw [eventuallyEq_comm, ae_eq_univ]
      change μ {x | ¬ x in closedBall 0 a} = 0
      rw [← ae_iff]
      filter_upwards [ha] with x hx using by simp [hx]
    · fun_prop
  -- So we can assume `μ {x | ‖x‖ ≤ a} < 1`, which implies `c' < 1`
  have ha_lt : μ {x | ‖x‖ <= a} < 1 := lt_of_le_of_ne prob_le_one ha
  have hc'_lt : c' < 1 := lt_of_le_of_lt hc' ha_lt
  -- We cut the space into a ball and a sequence of annuli between the thresholds `t n`
  have h_iUnion : (Set.univ : Set E)
      = closedBall 0 a union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion,
      Set.mem_sdiff, not_le, true_iff]
    simp_rw [and_comm (b := t _ < ‖x‖)]
    rcases le_or_gt (‖x‖) a with ha' | ha'
    · exact Or.inl ha'
· exact Or.inr (normThreshold_strictMono ha_pos).exists_between_of_tendsto_atTop
        (tendsto_normThreshold_atTop ha_pos) ha'
  -- The integral over the union is at most the sum of the integrals
  rw [← setLIntegral_univ]; rw [h_iUnion]
  have : ∫⁻ x in closedBall 0 (t 0) union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= ∫⁻ x in closedBall 0 (t 0), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ +
        ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
          .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ := by
    refine (lintegral_union_le _ _ _).trans ?_
    gcongr
    exact lintegral_iUnion_le _ _
  -- Each of the integrals in the sum correspond to the terms in the goal
  refine this.trans ?_
  rw [mul_add]
  gcongr
  -- We already proved the upper bound for the ball
  · exact ht_int_zero
  rw [← ENNReal.tsum_mul_left]
  gcongr with n
  -- Now we prove the bound for each annulus, by calling a previous lemma
  refine (le_trans ?_ (lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le h_rot
    (hc'_gt.trans_le hc') ha_lt n)).trans ?_
  · gcongr
    simp only [inv_pow, C]
    field_simp
    exact logRatio_mono hc'_gt ha_lt hc'
  gcongr _ * ENNReal.ofReal (rexp ?_)
  simp only [ENNReal.toReal_div, neg_mul, neg_le_neg_iff]
  gcongr
  · refine div_pos ?_ ?_
    all_goals rw [ENNReal.toReal_pos_iff]
    · exact ⟨lt_trans (by norm_num) hc'_gt, by finiteness⟩
    · simp only [tsub_pos_iff_lt, hc'_lt, true_and]
      finiteness
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
    exact ⟨ha_lt, by finiteness⟩
  · finiteness
  · finiteness

Depends on / 依赖: logRatio, normThreshold, prob_le_one
-/
lemma lintegral_exp_mul_sq_norm_le_mul [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    (ha_pos : 0 < a)
    {c' : Real>=0∞} (hc' : c' <= μ {x | ‖x‖ <= a}) (hc'_gt : 2⁻¹ < c') :
    ∫⁻ x, .ofReal (rexp (logRatio c' * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      <= μ {x | ‖x‖ <= a} *
       (.ofReal (rexp (logRatio c'))
        + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n))) := by
  let t := normThreshold a
  let c := μ {x | ‖x‖ <= a}
  let C := logRatio c' * a⁻¹ ^ 2
  have hc'_le : c' <= 1 := hc'.trans prob_le_one
  -- We want to bound an integral
  change ∫⁻ x, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= c * (.ofReal (rexp (logRatio c'))
            + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c' / (1 - c')).toReal * 2 ^ n)))
  -- We will cut the space into a ball of radius `a` and annuli defined from the thresholds `t n`
  -- and bound the integral on each piece.
  -- First, we bound the integral on the ball of radius `a`
  have ht_int_zero : ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
    calc ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
    _ <= ∫⁻ x in closedBall 0 a, .ofReal (rexp (C * a ^ 2)) ∂μ := by
      refine setLIntegral_mono (by fun_prop) fun x hx => ?_
      gcongr
      · exact mul_nonneg (logRatio_nonneg hc'_gt.le hc'_le) (by positivity)
      · simpa using hx
    _ = μ {x | ‖x‖ <= a} * .ofReal (rexp (logRatio c')) := by
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter]
      rw [mul_comm]
      simp only [inv_pow, C]
      field_simp
      congr with x
      simp
  -- We dispense with an edge case. If `μ {x | ‖x‖ ≤ a} = 1`, then the integral over
  -- the complement of the ball is zero and we are done.
  by_cases ha : μ {x | ‖x‖ <= a} = 1
  · simp only [ha, one_mul, ENNReal.toReal_div, neg_mul, ge_iff_le, c] at ht_int_zero ⊢
    refine le_add_right ((le_of_eq ?_).trans ht_int_zero)
    rw [← setLIntegral_univ]
    refine setLIntegral_congr ?_
    rw [← ae_iff_prob_eq_one ?_] at ha
    · rw [eventuallyEq_comm, ae_eq_univ]
      change μ {x | ¬ x in closedBall 0 a} = 0
      rw [← ae_iff]
      filter_upwards [ha] with x hx using by simp [hx]
    · fun_prop
  -- So we can assume `μ {x | ‖x‖ ≤ a} < 1`, which implies `c' < 1`
  have ha_lt : μ {x | ‖x‖ <= a} < 1 := lt_of_le_of_ne prob_le_one ha
  have hc'_lt : c' < 1 := lt_of_le_of_lt hc' ha_lt
  -- We cut the space into a ball and a sequence of annuli between the thresholds `t n`
  have h_iUnion : (Set.univ : Set E)
      = closedBall 0 a union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion,
      Set.mem_sdiff, not_le, true_iff]
    simp_rw [and_comm (b := t _ < ‖x‖)]
    rcases le_or_gt (‖x‖) a with ha' | ha'
    · exact Or.inl ha'
· exact Or.inr (normThreshold_strictMono ha_pos).exists_between_of_tendsto_atTop
        (tendsto_normThreshold_atTop ha_pos) ha'
  -- The integral over the union is at most the sum of the integrals
  rw [← setLIntegral_univ]; rw [h_iUnion]
  have : ∫⁻ x in closedBall 0 (t 0) union ⋃ n, closedBall 0 (t (n + 1)) \ closedBall 0 (t n),
        .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ
      <= ∫⁻ x in closedBall 0 (t 0), .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ +
        ∑' i, ∫⁻ x in closedBall 0 (t (i + 1)) \ closedBall 0 (t i),
          .ofReal (rexp (C * ‖x‖ ^ 2)) ∂μ := by
    refine (lintegral_union_le _ _ _).trans ?_
    gcongr
    exact lintegral_iUnion_le _ _
  -- Each of the integrals in the sum correspond to the terms in the goal
  refine this.trans ?_
  rw [mul_add]
  gcongr
  -- We already proved the upper bound for the ball
  · exact ht_int_zero
  rw [← ENNReal.tsum_mul_left]
  gcongr with n
  -- Now we prove the bound for each annulus, by calling a previous lemma
  refine (le_trans ?_ (lintegral_closedBall_sdiff_exp_logRatio_mul_sq_le h_rot
    (hc'_gt.trans_le hc') ha_lt n)).trans ?_
  · gcongr
    simp only [inv_pow, C]
    field_simp
    exact logRatio_mono hc'_gt ha_lt hc'
  gcongr _ * ENNReal.ofReal (rexp ?_)
  simp only [ENNReal.toReal_div, neg_mul, neg_le_neg_iff]
  gcongr
  · refine div_pos ?_ ?_
    all_goals rw [ENNReal.toReal_pos_iff]
    · exact ⟨lt_trans (by norm_num) hc'_gt, by finiteness⟩
    · simp only [tsub_pos_iff_lt, hc'_lt, true_and]
      finiteness
  · simp only [ENNReal.toReal_pos_iff, tsub_pos_iff_lt]
    exact ⟨ha_lt, by finiteness⟩
  · finiteness
  · finiteness

end Fernique

open Fernique

/--
theorem `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self` / 定理 `lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self`

English:
theorem lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self
  statement: [IsProbabilityMeasure μ]
  proof: by
  have ha : 0 <= a := by
    by_contra! h_neg
    have : {x : E | ‖x‖ <= a} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact h_neg.trans_le (norm_nonneg _)
    simp only [this, measure_empty, nonpos_iff_eq_zero] at hc
    simp [hc] at hc_gt
  cases ha.eq_or_lt' with
  | inl ha =>
    simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_div, neg_mul]
    refine le_add_right ?_
    rw [← ENNReal.ofReal_one]
    gcongr
    simp only [Real.one_le_exp_iff]
    exact logRatio_nonneg hc_gt.le (hc.trans prob_le_one)
  | inr ha_pos =>
  refine (lintegral_exp_mul_sq_norm_le_mul h_rot ha_pos hc hc_gt).trans ?_
  conv_rhs => rw [← one_mul (ENNReal.ofReal _ + _)]
  gcongr
  exact prob_le_one

中文:
定理 lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self
  结论: [是概率测度 μ]
  证明: by
  have ha : 0 <= a := by
    by_contra! h_neg
    have : {x : E | ‖x‖ <= a} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact h_neg.trans_le (norm_nonneg _)
    simp only [this, measure_empty, nonpos_iff_eq_zero] at hc
    simp [hc] at hc_gt
  cases ha.eq_or_lt' with
  | inl ha =>
    simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_div, neg_mul]
    refine le_add_right ?_
    rw [← ENNReal.ofReal_one]
    gcongr
    simp only [Real.one_le_exp_iff]
    exact logRatio_nonneg hc_gt.le (hc.trans prob_le_one)
  | inr ha_pos =>
  refine (lintegral_exp_mul_sq_norm_le_mul h_rot ha_pos hc hc_gt).trans ?_
  conv_rhs => rw [← one_mul (ENNReal.ofReal _ + _)]
  gcongr
  exact prob_le_one

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, ENNReal.toReal, OfNat.ofNat_ne_zero, Real.exp_zero, Set.mem_empty_iff_false, Set.mem_ofPred_eq, eq_or_lt, exp_zero, h_neg, h_neg.trans_le, ha.eq_or_lt, hc_gt, iff_false, inv_zero, lintegral_const, measure_empty, measure_univ, mem_empty_iff_false, mem_ofPred_eq
-/
theorem lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    {c : Real>=0∞} (hc : c <= μ {x | ‖x‖ <= a}) (hc_gt : 2⁻¹ < c) :
    ∫⁻ x, .ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ
      <= .ofReal (rexp (logRatio c))
        + ∑' n, .ofReal (rexp (-2⁻¹ * Real.log (c / (1 - c)).toReal * 2 ^ n)) := by
  have ha : 0 <= a := by
    by_contra! h_neg
    have : {x : E | ‖x‖ <= a} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact h_neg.trans_le (norm_nonneg _)
    simp only [this, measure_empty, nonpos_iff_eq_zero] at hc
    simp [hc] at hc_gt
  cases ha.eq_or_lt' with
  | inl ha =>
    simp only [ha, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_div, neg_mul]
    refine le_add_right ?_
    rw [← ENNReal.ofReal_one]
    gcongr
    simp only [Real.one_le_exp_iff]
    exact logRatio_nonneg hc_gt.le (hc.trans prob_le_one)
  | inr ha_pos =>
  refine (lintegral_exp_mul_sq_norm_le_mul h_rot ha_pos hc hc_gt).trans ?_
  conv_rhs => rw [← one_mul (ENNReal.ofReal _ + _)]
  gcongr
  exact prob_le_one

/--
lemma `exists_integrable_exp_sq_of_map_rotation_eq_self'` / 引理 `exists_integrable_exp_sq_of_map_rotation_eq_self'`

English:
lemma exists_integrable_exp_sq_of_map_rotation_eq_self'
  statement: [IsProbabilityMeasure μ]
  proof: by
  let c := μ {x | ‖x‖ <= a}
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have h_one_sub_lt_self : 1 - c < c := by
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at ha_gt
  have h_pos : 0 < logRatio c * a⁻¹ ^ 2 := mul_pos (logRatio_pos ha_gt hc_lt) (by positivity)
  refine ⟨logRatio c * a⁻¹ ^ 2, h_pos, ⟨by fun_prop, ?_⟩⟩
  simp only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs, Real.abs_exp]
  -- `⊢ ∫⁻ x, ENNReal.ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ < ∞`
  refine (lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self h_rot le_rfl ha_gt).trans_lt ?_
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
refine Summable.tsum_ofReal_lt_top
    Real.summable_exp_nat_mul_of_ge ?_ (fun i => mod_cast (Nat.lt_pow_self (by simp)).le)
  refine mul_neg_of_neg_of_pos (by simp) (Real.log_pos ?_)
  change 1 < (c / (1 - c)).toReal
  simp only [ENNReal.toReal_div, one_lt_div_iff, ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt,
    hc_one_sub_lt_top, and_self, true_and]
  rw [ENNReal.toReal_lt_toReal hc_one_sub_lt_top.ne hc_lt_top.ne]
  exact .inl h_one_sub_lt_self

中文:
引理 存在_integrable_exp_sq_of_map_rotation_eq_self'
  结论: [是概率测度 μ]
  证明: by
  let c := μ {x | ‖x‖ <= a}
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have h_one_sub_lt_self : 1 - c < c := by
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at ha_gt
  have h_pos : 0 < logRatio c * a⁻¹ ^ 2 := mul_pos (logRatio_pos ha_gt hc_lt) (by positivity)
  refine ⟨logRatio c * a⁻¹ ^ 2, h_pos, ⟨by fun_prop, ?_⟩⟩
  simp only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs, Real.abs_exp]
  -- `⊢ ∫⁻ x, ENNReal.ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ < ∞`
  refine (lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self h_rot le_rfl ha_gt).trans_lt ?_
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
refine Summable.tsum_ofReal_lt_top
    Real.summable_exp_nat_mul_of_ge ?_ (fun i => mod_cast (Nat.lt_pow_self (by simp)).le)
  refine mul_neg_of_neg_of_pos (by simp) (Real.log_pos ?_)
  change 1 < (c / (1 - c)).toReal
  simp only [ENNReal.toReal_div, one_lt_div_iff, ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt,
    hc_one_sub_lt_top, and_self, true_and]
  rw [ENNReal.toReal_lt_toReal hc_one_sub_lt_top.ne hc_lt_top.ne]
  exact .inl h_one_sub_lt_self

Depends on / 依赖: ENNReal, ENNReal.div_lt_iff, ENNReal.sub_lt_of_lt_add, div_lt_iff, h_one_sub_lt_self, h_pos, ha_gt, ha_lt, hc_lt, hc_lt.le, hc_lt_top, hc_one_sub_lt_top, inv_eq_one_div, logRatio, logRatio_pos, lt_top_of_lt, measure_lt_top, mul_comm, mul_pos, replace
-/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self' [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ)
    {a : Real} (ha_pos : 0 < a) (ha_gt : 2⁻¹ < μ {x | ‖x‖ <= a}) (ha_lt : μ {x | ‖x‖ <= a} < 1) :
    exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ := by
  let c := μ {x | ‖x‖ <= a}
  replace hc_lt : c < 1 := ha_lt
  have hc_lt_top : c < ∞ := measure_lt_top _ _
  have hc_one_sub_lt_top : 1 - c < ∞ := lt_top_of_lt (b := 2) (tsub_le_self.trans_lt (by simp))
  have h_one_sub_lt_self : 1 - c < c := by
    refine ENNReal.sub_lt_of_lt_add hc_lt.le ?_
    rw [← two_mul]
    rwa [inv_eq_one_div, ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at ha_gt
  have h_pos : 0 < logRatio c * a⁻¹ ^ 2 := mul_pos (logRatio_pos ha_gt hc_lt) (by positivity)
  refine ⟨logRatio c * a⁻¹ ^ 2, h_pos, ⟨by fun_prop, ?_⟩⟩
  simp only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs, Real.abs_exp]
  -- `⊢ ∫⁻ x, ENNReal.ofReal (rexp (logRatio c * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ < ∞`
  refine (lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self h_rot le_rfl ha_gt).trans_lt ?_
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
refine Summable.tsum_ofReal_lt_top
    Real.summable_exp_nat_mul_of_ge ?_ (fun i => mod_cast (Nat.lt_pow_self (by simp)).le)
  refine mul_neg_of_neg_of_pos (by simp) (Real.log_pos ?_)
  change 1 < (c / (1 - c)).toReal
  simp only [ENNReal.toReal_div, one_lt_div_iff, ENNReal.toReal_pos_iff, tsub_pos_iff_lt, hc_lt,
    hc_one_sub_lt_top, and_self, true_and]
  rw [ENNReal.toReal_lt_toReal hc_one_sub_lt_top.ne hc_lt_top.ne]
  exact .inl h_one_sub_lt_self

/--
lemma `exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure` / 引理 `exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure`

English:
lemma exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure
  proof: by
  -- If there exists `a > 0` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`, we can call the previous lemma.
  by_cases h_meas_Ioo : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1
  · obtain ⟨a, ha_pos, ha_gt, ha_lt⟩ : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1 :=
      h_meas_Ioo
    exact exists_integrable_exp_sq_of_map_rotation_eq_self' h_rot ha_pos ha_gt ha_lt
  -- Otherwise, we can find `b > 0` such that the ball of radius `b` has full measure
  obtain ⟨b, hb⟩ : exists b, μ {x | ‖x‖ <= b} = 1 := by
    by_contra h_ne
    push Not at h_meas_Ioo h_ne
    suffices μ .univ <= 2⁻¹ by simp at this
    have h_le a : μ {x | ‖x‖ <= a} <= 2⁻¹ := by
      have h_of_pos a' (ha : 0 < a') : μ {x | ‖x‖ <= a'} <= 2⁻¹ := by
        by_contra h_lt
        refine h_ne a' ?_
        exact le_antisymm prob_le_one (h_meas_Ioo a' ha (not_le.mp h_lt))
      rcases le_or_gt a 0 with ha | ha
      · calc μ {x | ‖x‖ <= a}
        _ <= μ {x | ‖x‖ <= 1} := measure_mono fun x hx => hx.trans (ha.trans (by positivity))
        _ <= 2⁻¹ := h_of_pos _ (by positivity)
      · exact h_of_pos a ha
    have h_univ : (Set.univ : Set E) = ⋃ a : Nat, {x | ‖x‖ <= a} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact exists_nat_ge _
    rw [h_univ]; rw [Monotone.measure_iUnion]
    · simp [h_le]
    · intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans (mod_cast hab)
  -- So we can take `C = 1` and show that `x ↦ exp (‖x‖ ^ 2)` is integrable, since it is bounded.
  have hb' : forallᵐ x ∂μ, ‖x‖ <= b := by
    rwa [ae_iff_prob_eq_one]
    refine measurable_to_prop ?_
    rw [show (fun x : E => ‖x‖ <= b) ⁻¹' {True} = {x : E | ‖x‖ <= b} by ext; simp]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  refine ⟨1, by positivity, ?_⟩
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ => rexp (b ^ 2)) (by fun_prop)
    ?_ ?_ (integrable_const _) (integrable_const _)
  · exact ae_of_all _ fun _ => by positivity
  · filter_upwards [hb'] with x hx
    simp only [one_mul]
    gcongr

中文:
引理 存在_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure
  证明: by
  -- If there exists `a > 0` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`, we can call the previous lemma.
  by_cases h_meas_Ioo : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1
  · obtain ⟨a, ha_pos, ha_gt, ha_lt⟩ : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1 :=
      h_meas_Ioo
    exact exists_integrable_exp_sq_of_map_rotation_eq_self' h_rot ha_pos ha_gt ha_lt
  -- Otherwise, we can find `b > 0` such that the ball of radius `b` has full measure
  obtain ⟨b, hb⟩ : exists b, μ {x | ‖x‖ <= b} = 1 := by
    by_contra h_ne
    push Not at h_meas_Ioo h_ne
    suffices μ .univ <= 2⁻¹ by simp at this
    have h_le a : μ {x | ‖x‖ <= a} <= 2⁻¹ := by
      have h_of_pos a' (ha : 0 < a') : μ {x | ‖x‖ <= a'} <= 2⁻¹ := by
        by_contra h_lt
        refine h_ne a' ?_
        exact le_antisymm prob_le_one (h_meas_Ioo a' ha (not_le.mp h_lt))
      rcases le_or_gt a 0 with ha | ha
      · calc μ {x | ‖x‖ <= a}
        _ <= μ {x | ‖x‖ <= 1} := measure_mono fun x hx => hx.trans (ha.trans (by positivity))
        _ <= 2⁻¹ := h_of_pos _ (by positivity)
      · exact h_of_pos a ha
    have h_univ : (Set.univ : Set E) = ⋃ a : Nat, {x | ‖x‖ <= a} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact exists_nat_ge _
    rw [h_univ]; rw [Monotone.measure_iUnion]
    · simp [h_le]
    · intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans (mod_cast hab)
  -- So we can take `C = 1` and show that `x ↦ exp (‖x‖ ^ 2)` is integrable, since it is bounded.
  have hb' : forallᵐ x ∂μ, ‖x‖ <= b := by
    rwa [ae_iff_prob_eq_one]
    refine measurable_to_prop ?_
    rw [show (fun x : E => ‖x‖ <= b) ⁻¹' {True} = {x : E | ‖x‖ <= b} by ext; simp]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  refine ⟨1, by positivity, ?_⟩
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ => rexp (b ^ 2)) (by fun_prop)
    ?_ ?_ (integrable_const _) (integrable_const _)
  · exact ae_of_all _ fun _ => by positivity
  · filter_upwards [hb'] with x hx
    simp only [one_mul]
    gcongr
-/
lemma exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure
    [IsProbabilityMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ := by
  -- If there exists `a > 0` such that `2⁻¹ < μ {x | ‖x‖ ≤ a} < 1`, we can call the previous lemma.
  by_cases h_meas_Ioo : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1
  · obtain ⟨a, ha_pos, ha_gt, ha_lt⟩ : exists a, 0 < a ∧ 2⁻¹ < μ {x | ‖x‖ <= a} ∧ μ {x | ‖x‖ <= a} < 1 :=
      h_meas_Ioo
    exact exists_integrable_exp_sq_of_map_rotation_eq_self' h_rot ha_pos ha_gt ha_lt
  -- Otherwise, we can find `b > 0` such that the ball of radius `b` has full measure
  obtain ⟨b, hb⟩ : exists b, μ {x | ‖x‖ <= b} = 1 := by
    by_contra h_ne
    push Not at h_meas_Ioo h_ne
    suffices μ .univ <= 2⁻¹ by simp at this
    have h_le a : μ {x | ‖x‖ <= a} <= 2⁻¹ := by
      have h_of_pos a' (ha : 0 < a') : μ {x | ‖x‖ <= a'} <= 2⁻¹ := by
        by_contra h_lt
        refine h_ne a' ?_
        exact le_antisymm prob_le_one (h_meas_Ioo a' ha (not_le.mp h_lt))
      rcases le_or_gt a 0 with ha | ha
      · calc μ {x | ‖x‖ <= a}
        _ <= μ {x | ‖x‖ <= 1} := measure_mono fun x hx => hx.trans (ha.trans (by positivity))
        _ <= 2⁻¹ := h_of_pos _ (by positivity)
      · exact h_of_pos a ha
    have h_univ : (Set.univ : Set E) = ⋃ a : Nat, {x | ‖x‖ <= a} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact exists_nat_ge _
    rw [h_univ]; rw [Monotone.measure_iUnion]
    · simp [h_le]
    · intro a b hab x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans (mod_cast hab)
  -- So we can take `C = 1` and show that `x ↦ exp (‖x‖ ^ 2)` is integrable, since it is bounded.
  have hb' : forallᵐ x ∂μ, ‖x‖ <= b := by
    rwa [ae_iff_prob_eq_one]
    refine measurable_to_prop ?_
    rw [show (fun x : E => ‖x‖ <= b) ⁻¹' {True} = {x : E | ‖x‖ <= b} by ext; simp]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  refine ⟨1, by positivity, ?_⟩
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ => rexp (b ^ 2)) (by fun_prop)
    ?_ ?_ (integrable_const _) (integrable_const _)
  · exact ae_of_all _ fun _ => by positivity
  · filter_upwards [hb'] with x hx
    simp only [one_mul]
    gcongr

/--
theorem `exists_integrable_exp_sq_of_map_rotation_eq_self` / 定理 `exists_integrable_exp_sq_of_map_rotation_eq_self`

English:
theorem exists_integrable_exp_sq_of_map_rotation_eq_self
  statement: [IsFiniteMeasure μ]
  proof: by
  by_cases hμ_zero : μ = 0
  · exact ⟨1, by positivity, by simp [hμ_zero]⟩
  let μ' := cond μ .univ
  have hμ'_eq : μ' = (μ .univ)⁻¹ • μ := by simp [μ', cond]
have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure by simp [hμ_zero]
  have h_rot : (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4))) = μ'.prod μ' := by
    calc (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4)))
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹)
        • (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹) • (μ.prod μ) := by rw [h_rot]
    _ = μ'.prod μ' := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  obtain ⟨C, hC_pos, hC⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure (μ := μ') h_rot
  refine ⟨C, hC_pos, ?_⟩
  rwa [hμ'_eq, integrable_smul_measure] at hC
  · simp
  · simp [hμ_zero]

中文:
定理 存在_integrable_exp_sq_of_map_rotation_eq_self
  结论: [是有限测度 μ]
  证明: by
  by_cases hμ_zero : μ = 0
  · exact ⟨1, by positivity, by simp [hμ_zero]⟩
  let μ' := cond μ .univ
  have hμ'_eq : μ' = (μ .univ)⁻¹ • μ := by simp [μ', cond]
have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure by simp [hμ_zero]
  have h_rot : (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4))) = μ'.prod μ' := by
    calc (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4)))
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹)
        • (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹) • (μ.prod μ) := by rw [h_rot]
    _ = μ'.prod μ' := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  obtain ⟨C, hC_pos, hC⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure (μ := μ') h_rot
  refine ⟨C, hC_pos, ?_⟩
  rwa [hμ'_eq, integrable_smul_measure] at hC
  · simp
  · simp [hμ_zero]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.rotation, IsProbabilityMeasure, Set.univ, cond_isProbabilityMeasure, h_rot, rotation
-/
theorem exists_integrable_exp_sq_of_map_rotation_eq_self [IsFiniteMeasure μ]
    (h_rot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.prod μ) :
    exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ := by
  by_cases hμ_zero : μ = 0
  · exact ⟨1, by positivity, by simp [hμ_zero]⟩
  let μ' := cond μ .univ
  have hμ'_eq : μ' = (μ .univ)⁻¹ • μ := by simp [μ', cond]
have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure by simp [hμ_zero]
  have h_rot : (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4))) = μ'.prod μ' := by
    calc (μ'.prod μ').map (ContinuousLinearMap.rotation (-(π / 4)))
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹)
        • (μ.prod μ).map (ContinuousLinearMap.rotation (-(π / 4))) := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = ((μ Set.univ)⁻¹ * (μ Set.univ)⁻¹) • (μ.prod μ) := by rw [h_rot]
    _ = μ'.prod μ' := by
      simp [hμ'_eq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  obtain ⟨C, hC_pos, hC⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self_of_isProbabilityMeasure (μ := μ') h_rot
  refine ⟨C, hC_pos, ?_⟩
  rwa [hμ'_eq, integrable_smul_measure] at hC
  · simp
  · simp [hμ_zero]

end ProbabilityTheory
