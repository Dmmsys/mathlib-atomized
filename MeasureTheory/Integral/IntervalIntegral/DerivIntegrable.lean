/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* `MonotoneOn.intervalIntegrable_deriv`: If `f` is monotone on `a..b`, then `f'` is interval
  integrable on `a..b`.
* `MonotoneOn.intervalIntegral_deriv_mem_uIcc`: If `f` is monotone on `a..b`, then the integral of
  `f'` on `a..b` is in `uIcc 0 (f b - f a)`.
* `BoundedVariationOn.intervalIntegrable_deriv`: If `f` has bounded variation on `a..b`,
  then `f'` is interval integrable on `a..b`.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`: If `f` is absolutely continuous on
  `a..b`, then `f'` is interval integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

public section

open MeasureTheory Set Filter

open scoped Topology

/--
lemma `MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le` / 引理 `MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le`

English:
lemma MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le
  proof: by
  /- Proof Sketch: Extend `f` on `[a, b]` to a function `g` on `ℝ` by defining `g x = f a` for
  `x < a` and `g x = f b` for `x > b`. `g` is globally monotone and `g'` agrees with `f'` on
  `(a, b)`. We let `G c x = slope g x (x + c)` for `c > 0`. Then `G c x` is nonnegative,
  `∫⁻ (x : ℝ) in Icc

中文:
引理 MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le
  证明: by
  /- Proof Sketch: Extend `f` on `[a, b]` to a function `g` on `ℝ` by defining `g x = f a` for
  `x < a` and `g x = f b` for `x > b`. `g` is globally monotone and `g'` agrees with `f'` on
  `(a, b)`. We let `G c x = slope g x (x + c)` for `c > 0`. Then `G c x` is nonnegative,
  `∫⁻ (x : ℝ) in Icc
-/
lemma MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le
    {f : Real -> Real} {a b : Real} (hab : a <= b) (hf : MonotoneOn f (Icc a b)) :
    exists G : (Nat -> Real -> Real), (forallᵐ x ∂volume.restrict (Icc a b),
      Filter.Tendsto (fun (n : Nat) => G n x) Filter.atTop (𝓝 (deriv f x))) ∧
      (forall (n : Nat), AEStronglyMeasurable (G n) (volume.restrict (Icc a b))) ∧
      liminf (fun (n : Nat) => ∫⁻ (x : Real) in Icc a b, ‖G n x‖ₑ) atTop <=
        ENNReal.ofReal (f b - f a) := by
  /- Proof Sketch: Extend `f` on `[a, b]` to a function `g` on `ℝ` by defining `g x = f a` for
  `x < a` and `g x = f b` for `x > b`. `g` is globally monotone and `g'` agrees with `f'` on
  `(a, b)`. We let `G c x = slope g x (x + c)` for `c > 0`. Then `G c x` is nonnegative,
  `∫⁻ (x : ℝ) in Icc a b, ‖G c x‖ₑ ≤ f b - f a`, and `G c x` tends to `f' x` as `c` tends to `0`
  from the right. The function `fun n x ↦ G (n : ℝ)⁻¹ x` is a witness to the conclusion of the
  lemma. -/
  let g (x : Real) : Real := f (max a (min x b))
have hg : Monotone g := monotoneOn_univ.mp hf.comp
    (monotoneOn_const.max <| monotoneOn_id.min monotoneOn_const) (by simpa)
have hfg : EqOn f g (Ioo a b) := fun x ⟨hxa, hxb⟩ => congrArg f
.symm ▸ (max_eq_right hxa.le).symm min_eq_left hxb.le
  replace hfg := hfg.deriv isOpen_Ioo
  let G (c x : Real) := slope g x (x + c)
  have G_integrable (n : Nat) : Integrable (G (↑n)⁻¹) (volume.restrict (Icc a b)) := by
.intervalIntegrable_slope hab (by simp) have := hg.monotoneOn (Icc a (b + (n : Real)⁻¹))
.mp this exact intervalIntegrable_iff_integrableOn_Icc_of_le hab
.aestronglyMeasurable, ?_⟩ refine ⟨fun n x => G (n : Real)⁻¹ x, ?_, fun n => G_integrable n
  · rw [← restrict_Ioo_eq_restrict_Icc, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hg.ae_differentiableAt] with x hx₁ hx₂
    rw [hfg hx₂]
exact hx₁.hasDerivAt.tendsto_slope.comp
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by convert! tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := Real)); simp)
      (by simp [eventually_ne_atTop 0])
  · calc
      _ = liminf (fun (n : Nat) => ENNReal.ofReal (∫ (x : Real) in Icc a b, (G (n : Real)⁻¹) x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (G_integrable n)]
        congr with y
        exact abs_eq_self.mpr (hg.monotoneOn univ |>.slope_nonneg trivial trivial)
      _ <= ENNReal.ofReal (g b - g a) := by
        refine Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall fun n => ENNReal.ofReal_le_ofReal ?_)
        rw [integral_Icc_eq_integral_Ioc]; rw [← intervalIntegral.integral_of_le hab]
        convert!
.intervalIntegral_slope_le hab (by simp) using 2 hg.monotoneOn (Icc a (b + (n : Real)⁻¹))
        simp [g]
      _ = ENNReal.ofReal (f b - f a) := by grind

/--
theorem `MonotoneOn.intervalIntegrable_deriv` / 定理 `MonotoneOn.intervalIntegrable_deriv`

English:
theorem MonotoneOn.intervalIntegrable_deriv
  statement: {f : Real -> Real} {a b : Real}
  proof: by
  wlog hab : a <= b generalizing a b with h
.symm · exact h (uIcc_comm a b ▸ hf) (by linarith)
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : Nat) => ∫⁻ (x : Real) in Icc a b, ‖G n x‖ₑ) atTop != ⊤ :=
.

中文:
定理 MonotoneOn.intervalIntegrable_deriv
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: by
  wlog hab : a <= b generalizing a b with h
.symm · exact h (uIcc_comm a b ▸ hf) (by linarith)
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : Nat) => ∫⁻ (x : Real) in Icc a b, ‖G n x‖ₑ) atTop != ⊤ :=
.

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, exists_tendsto_deriv_liminf_lintegral_enorm_le, generalizing, hf.exists_tendsto_deriv_liminf_lintegral_enorm_le, integrable_f_deriv, integrable_of_tendsto, intervalIntegrable_iff_integrableOn_Icc_of_le, liminf, lt_of_le_of_lt, ne_top, ofReal_lt_top, uIcc_comm, uIcc_of_le
-/
theorem MonotoneOn.intervalIntegrable_deriv {f : Real -> Real} {a b : Real}
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a <= b generalizing a b with h
.symm · exact h (uIcc_comm a b ▸ hf) (by linarith)
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : Nat) => ∫⁻ (x : Real) in Icc a b, ‖G n x‖ₑ) atTop != ⊤ :=
.ne_top lt_of_le_of_lt hG' ENNReal.ofReal_lt_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr integrable_f_deriv

/--
theorem `MonotoneOn.intervalIntegral_deriv_mem_uIcc` / 定理 `MonotoneOn.intervalIntegral_deriv_mem_uIcc`

English:
theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc
  statement: {f : Real -> Real} {a b : Real}
  proof: by
  wlog hab : a <= b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    have : f b <= f a := hf (by simp) (by simp) (by linarith)
    rw [intervalIntegral.integral_symm]; rw [uIcc_of_ge (by linarith)]
    refine neg_mem_Icc_iff.mpr ?_
    simp only [neg_zero, neg_sub]


中文:
定理 MonotoneOn.intervalIntegral_deriv_mem_uIcc
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: by
  wlog hab : a <= b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    have : f b <= f a := hf (by simp) (by simp) (by linarith)
    rw [intervalIntegral.integral_symm]; rw [uIcc_of_ge (by linarith)]
    refine neg_mem_Icc_iff.mpr ?_
    simp only [neg_zero, neg_sub]


Depends on / 依赖: exists_tendsto_deriv_liminf_lintegral_enorm_le, generalizing, hf.exists_tendsto_deriv_liminf_lintegral_enorm_le, integral_symm, intervalIntegral, intervalIntegral.integral_symm, liminf, neg_mem_Icc_iff, neg_mem_Icc_iff.mpr, neg_sub, neg_zero, specialize, uIcc_comm, uIcc_of_ge, uIcc_of_le
-/
theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc {f : Real -> Real} {a b : Real}
    (hf : MonotoneOn f (uIcc a b)) :
    ∫ x in a..b, deriv f x in uIcc 0 (f b - f a) := by
  wlog hab : a <= b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    have : f b <= f a := hf (by simp) (by simp) (by linarith)
    rw [intervalIntegral.integral_symm]; rw [uIcc_of_ge (by linarith)]
    refine neg_mem_Icc_iff.mpr ?_
    simp only [neg_zero, neg_sub]
    rwa [uIcc_of_le (by linarith)] at h
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : Nat) => ∫⁻ (x : Real) in Icc a b, ‖G n x‖ₑ) atTop != ⊤ :=
.ne_top lt_of_le_of_lt hG' ENNReal.ofReal_lt_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  rw [MeasureTheory.ae_restrict_iff' (by simp)] at hGf
  rw [← uIcc_of_le hab] at hGf hG hG'
  have : f a <= f b := hf (by simp [hab]) (by simp [hab]) hab
  rw [uIcc_of_le (by linarith)]; rw [mem_Icc]
  have f_deriv_nonneg {x : Real} (hx : x in Ioo a b) : 0 <= deriv f x := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.left hx.right)]
    exact hf.derivWithin_nonneg
  constructor
  · apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE]; rw [← restrict_Ioo_eq_restrict_Icc]; rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall @f_deriv_nonneg
  · have ebound := lintegral_enorm_le_liminf_of_tendsto
      ((MeasureTheory.ae_restrict_iff' (by measurability) |>.mpr hGf))
      (fun n => (hG n).aemeasurable.enorm)
    grw [hG'] at ebound
    rw [uIcc_of_le hab]; rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm integrable_f_deriv]; rw [ENNReal.ofReal_le_ofReal_iff (by linarith)]; rw [integral_Icc_eq_integral_Ioc]; rw [← intervalIntegral.integral_of_le hab] at ebound
    convert! ebound using 1
    refine intervalIntegral.integral_congr_uIoo ?_
    rw [uIoo_of_le hab]
    intro x hx
exact Eq.symm abs_eq_self.mpr f_deriv_nonneg hx

/--
theorem `BoundedVariationOn.intervalIntegrable_deriv` / 定理 `BoundedVariationOn.intervalIntegrable_deriv`

English:
theorem BoundedVariationOn.intervalIntegrable_deriv
  statement: {f : Real -> Real} {a b : Real}
  proof: by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr_ae
  rw [Filter.EventuallyEq]; rw [MeasureTheory.ae_

中文:
定理 BoundedVariationOn.intervalIntegrable_deriv
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr_ae
  rw [Filter.EventuallyEq]; rw [MeasureTheory.ae_

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Ioc_subset_Icc_self, MeasureTheory, MeasureTheory.ae_restrict_iff, ae_differentiableWithinAt_of_mem, ae_iff, ae_restrict_iff, congr_ae, exists_monotoneOn_sub_monotoneOn, filter_upwards, hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn, hp.ae_differentiableWithinAt_of_mem, hp.intervalIntegrable_deriv.sub, hq.ae_differentiableWithinAt_of_mem, hq.intervalIntegrable_deriv, intervalIntegrable_deriv, locallyBoundedVariationOn, measure_singleton
-/
theorem BoundedVariationOn.intervalIntegrable_deriv {f : Real -> Real} {a b : Real}
    (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : forallᵐ x, x != max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr_ae
  rw [Filter.EventuallyEq]; rw [MeasureTheory.ae_restrict_iff' (by simp [uIoc])]
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  have hx₅ : x in uIcc a b := Ioc_subset_Icc_self hx₄
  rw [uIoc]; rw [mem_Ioc] at hx₄
  have hx₆ : uIcc a b in 𝓝 x := Icc_mem_nhds hx₄.left (lt_of_le_of_ne hx₄.right hx₃)
.hasDerivAt replace hx₁ := (hx₁ hx₅).differentiableAt hx₆
.hasDerivAt replace hx₂ := (hx₂ hx₅).differentiableAt hx₆
  exact (hx₁.sub hx₂).deriv.symm

/--
theorem `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` / 定理 `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`

English:
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv
  statement: {f : Real -> Real} {a b : Real}
  proof: hf.boundedVariationOn.intervalIntegrable_deriv

中文:
定理 AbsolutelyContinuousOnInterval.intervalIntegrable_deriv
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: hf.boundedVariationOn.intervalIntegrable_deriv

Depends on / 依赖: boundedVariationOn, hf.boundedVariationOn.intervalIntegrable_deriv, intervalIntegrable_deriv
-/
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : Real -> Real} {a b : Real}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.intervalIntegrable_deriv
