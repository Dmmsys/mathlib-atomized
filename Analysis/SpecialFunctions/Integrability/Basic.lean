/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Integrability of Special Functions

This file establishes basic facts about the interval integrability of special functions, including
powers and the logarithm.
-/

public section

open Interval MeasureTheory Real Set

variable {a b c d : Real} (n : Nat) {f : Real -> Real} {μ : Measure Real} [IsLocallyFiniteMeasure μ]

namespace intervalIntegral

@[simp]
/--
theorem `intervalIntegrable_pow` / 定理 `intervalIntegrable_pow`

English:
theorem intervalIntegrable_pow
  statement: IntervalIntegrable (fun x => x ^ n) μ a b
  proof: (continuous_pow n).intervalIntegrable a b

中文:
定理 intervalIntegrable_pow
  结论: 整数erval整数egrable (fun x => x ^ n) μ a b
  证明: (continuous_pow n).intervalIntegrable a b

Depends on / 依赖: continuous_pow, intervalIntegrable
-/
theorem intervalIntegrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuous_pow n).intervalIntegrable a b

/--
theorem `intervalIntegrable_zpow` / 定理 `intervalIntegrable_zpow`

English:
theorem intervalIntegrable_zpow
  given: {n : Int} (h : 0 <= n ∨ (0 : Real) ∉ [[a, b]])
  proof: (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

中文:
定理 intervalIntegrable_zpow
  条件: {n : 整数} (h : 0 <= n ∨ (0 : 实数) ∉ [[a, b]])
  证明: (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

Depends on / 依赖: continuousOn_id, continuousOn_id.zpow, h.symm.imp, intervalIntegrable, ne_of_mem_of_not_mem
-/
theorem intervalIntegrable_zpow {n : Int} (h : 0 <= n ∨ (0 : Real) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/--
theorem `intervalIntegrable_rpow` / 定理 `intervalIntegrable_rpow`

English:
theorem intervalIntegrable_rpow
  given: {r : Real} (h : 0 <= r ∨ (0 : Real) ∉ [[a, b]])
  proof: (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

中文:
定理 intervalIntegrable_rpow
  条件: {r : 实数} (h : 0 <= r ∨ (0 : 实数) ∉ [[a, b]])
  证明: (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

Depends on / 依赖: continuousOn_id, continuousOn_id.rpow_const, h.symm.imp, intervalIntegrable, ne_of_mem_of_not_mem, rpow_const
-/
theorem intervalIntegrable_rpow {r : Real} (h : 0 <= r ∨ (0 : Real) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/--
theorem `intervalIntegrable_rpow'` / 定理 `intervalIntegrable_rpow'`

English:
theorem intervalIntegrable_rpow'
  given: {r : Real} (h : -1 < r)
  proof: by
  suffices forall c : Real, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff]; rw [uIoc_of_le hc]
    h

中文:
定理 intervalIntegrable_rpow'
  条件: {r : 实数} (h : -1 < r)
  证明: by
  suffices forall c : Real, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff]; rw [uIoc_of_le hc]
    h

Depends on / 依赖: HasDerivAt, IntervalIntegrable, IntervalIntegrable.trans, Or.inl, Real.hasDerivAt_rpow_const, convert, div_const, hasDerivAt_rpow_const, hderiv, intervalIntegrable_iff, uIoc_of_le, volume
-/
theorem intervalIntegrable_rpow' {r : Real} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices forall c : Real, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff]; rw [uIoc_of_le hc]
    have hderiv : forall x in Ioo 0 c, HasDerivAt (fun x : Real => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert! (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.1.ne')).div_const (r + 1) using 1
      simp [(by linarith : r + 1 != 0)]
    apply integrableOn_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg hx.1.le
    · refine (continuousOn_id.rpow_const ?_).div_const _; intro x _; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    rw [intervalIntegrable_iff] at m ⊢
    refine m.congr_fun ?_ measurableSet_Ioc; intro x hx
    rw [uIoc_of_le (by linarith : 0 <= -c)] at hx
    simp only [Pi.smul_apply, smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]

/--
lemma `integrableOn_Ioo_rpow_iff` / 引理 `integrableOn_Ioo_rpow_iff`

English:
lemma integrableOn_Ioo_rpow_iff
  given: {s t : Real} (ht : 0 < t)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x => x ^ s) (Ioo 0 (min 1 t)) :=

中文:
引理 integrableOn_Ioo_rpow_iff
  条件: {s t : 实数} (ht : 0 < t)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x => x ^ s) (Ioo 0 (min 1 t)) :=

Depends on / 依赖: H.mono, IntegrableOn, Ioo_subset_Ioo, Set.Ioo_subset_Ioo, ae_restrict_mem, aestronglyMeasurable, contrapose, filter_upwards, ht.le, intervalIntegrable_iff_integrableOn_Ioo_of_le, intervalIntegrable_rpow, le_rfl, lt_min, measurableSet_, measurable_inv, measurable_inv.aestronglyMeasurable, min_le_right, zero_lt_one
-/
lemma integrableOn_Ioo_rpow_iff {s t : Real} (ht : 0 < t) :
    IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) t) ↔ -1 < s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x => x ^ s) (Ioo 0 (min 1 t)) :=
    H.mono (Set.Ioo_subset_Ioo le_rfl (min_le_right _ _)) le_rfl
  have : IntegrableOn (fun x => x⁻¹) (Ioo 0 (min 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hx.1)]
    rwa [← Real.rpow_neg_one x, Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1]
    exact lt_of_lt_of_le hx.2 (min_le_left _ _)
  have : IntervalIntegrable (fun x => x⁻¹) volume 0 (min 1 t) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le I.le]
  simp [intervalIntegrable_inv_iff, I.ne] at this

/--
theorem `intervalIntegrable_cpow` / 定理 `intervalIntegrable_cpow`

English:
theorem intervalIntegrable_cpow
  given: {r : Complex} (h : 0 <= r.re ∨ (0 : Real) ∉ [[a, b]])
  proof: by
  by_cases h2 : (0 : Real) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2]; rw [or_false]

中文:
定理 intervalIntegrable_cpow
  条件: {r : Complex} (h : 0 <= r.re ∨ (0 : 实数) ∉ [[a, b]])
  证明: by
  by_cases h2 : (0 : Real) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2]; rw [or_false]

Depends on / 依赖: Complex.continuousAt_ofReal_cpow_const, Complex.continuous_ofReal_cpow_const, Or.inr, continuity, continuousAt_ofReal_cpow_const, continuousOn_of_forall_continuousAt, continuous_ofReal_cpow_const, eq_false, intervalIntegrable, lt_or_eq_of_le, ne_of_mem_of_not_mem, or_false
-/
theorem intervalIntegrable_cpow {r : Complex} (h : 0 <= r.re ∨ (0 : Real) ∉ [[a, b]]) :
    IntervalIntegrable (fun x : Real => (x : Complex) ^ r) μ a b := by
  by_cases h2 : (0 : Real) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2]; rw [or_false] at h
  rcases lt_or_eq_of_le h with (h' | h')
  · -- Easy case #2: 0 < re r -- again use continuity
    exact (Complex.continuous_ofReal_cpow_const h').intervalIntegrable _ _
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine (IntervalIntegrable.intervalIntegrable_norm_iff ?_).mp ?_
  · refine (measurable_of_continuousOn_compl_singleton (0 : Real) ?_).aestronglyMeasurable
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x r (Or.inr hx)
  -- reduce to case of integral over `[0, c]`
  suffices forall c : Real, IntervalIntegrable (fun x : Real => ‖(x : Complex) ^ r‖) μ 0 c from
    (this a).symm.trans (this b)
  intro c
  rcases le_or_gt 0 c with (hc | hc)
  · -- case `0 ≤ c`: integrand is identically 1
    have : IntervalIntegrable (fun _ => 1 : Real -> Real) μ 0 c := intervalIntegrable_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc] at this ⊢
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioc
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]; rw [← h']; rw [rpow_zero]
  · -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply IntervalIntegrable.symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
    rw [← Ioo_union_right hc]; rw [integrableOn_union]; rw [and_comm]; constructor
· exact integrableOn_singleton (by simp)
        isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_singleton
    · have : forall x : Real, x in Ioo c 0 -> ‖Complex.exp (↑π * Complex.I * r)‖ = ‖(x : Complex) ^ r‖ := by
        intro x hx
        rw [Complex.ofReal_cpow_of_nonpos hx.2.le]; rw [norm_mul]; rw [← Complex.ofReal_neg]; rw [Complex.norm_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2)]; rw [← h']; rw [rpow_zero]; rw [one_mul]
      refine IntegrableOn.congr_fun ?_ this measurableSet_Ioo
      rw [integrableOn_const_iff]
      right
      refine (measure_mono Set.Ioo_subset_Icc_self).trans_lt ?_
      exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_Icc

/--
theorem `intervalIntegrable_cpow'` / 定理 `intervalIntegrable_cpow'`

English:
theorem intervalIntegrable_cpow'
  given: {r : Complex} (h : -1 < r.re)
  proof: by
  suffices forall c : Real, IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.inte

中文:
定理 intervalIntegrable_cpow'
  条件: {r : Complex} (h : -1 < r.re)
  证明: by
  suffices forall c : Real, IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.inte

Depends on / 依赖: IntegrableOn, IntegrableOn.congr_fun, IntervalIntegrable, IntervalIntegrable.intervalIntegrable_norm_iff, IntervalIntegrable.trans, congr_fun, intervalIntegrable_iff, intervalIntegrable_norm_iff, intervalIntegrable_rpow, intervalIntegral, intervalIntegral.intervalIntegrable_rpow, uIoc_of_le, volume
-/
theorem intervalIntegrable_cpow' {r : Complex} (h : -1 < r.re) :
    IntervalIntegrable (fun x : Real => (x : Complex) ^ r) volume a b := by
  suffices forall c : Real, IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : forall c : Real, 0 <= c -> IntervalIntegrable (fun x => (x : Complex) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.intervalIntegrable_norm_iff]
    · rw [intervalIntegrable_iff]
      apply IntegrableOn.congr_fun
      · rw [← intervalIntegrable_iff]; exact intervalIntegral.intervalIntegrable_rpow' h
      · intro x hx
        rw [uIoc_of_le hc] at hx
        dsimp only
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      · exact measurableSet_uIoc
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      rw [uIoc_of_le hc] at hx
      refine (continuousAt_cpow_const (Or.inl ?_)).comp Complex.continuous_ofReal.continuousAt
      rw [Complex.ofReal_re]
      exact hx.1
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).const_mul (Complex.exp (π * Complex.I * r))
    rw [intervalIntegrable_iff]; rw [uIoc_of_le (by linarith : 0 <= -c)] at m ⊢
    refine m.congr_fun (fun x hx => ?_) measurableSet_Ioc
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    have : -x <= 0 := by linarith [hx.1]
    rw [Complex.ofReal_cpow_of_nonpos this]; rw [mul_comm]
    simp

/--
theorem `integrableOn_Ioo_cpow_iff` / 定理 `integrableOn_Ioo_cpow_iff`

English:
theorem integrableOn_Ioo_cpow_iff
  given: {s : Complex} {t : Real} (ht : 0 < t)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact intervalIntegrable_cpow' h (a := 0) (b := t)
  have B : IntegrableOn (fun a => a ^ s.re) (Ioo 0 t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioo).1 h.norm
    intro a 

中文:
定理 integrableOn_Ioo_cpow_iff
  条件: {s : Complex} {t : 实数} (ht : 0 < t)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact intervalIntegrable_cpow' h (a := 0) (b := t)
  have B : IntegrableOn (fun a => a ^ s.re) (Ioo 0 t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioo).1 h.norm
    intro a 

Depends on / 依赖: Complex.norm_cpow_eq_rpow_re_of_pos, IntegrableOn, h.norm, ht.le, integrableOn_Ioo_rpow_iff, integrableOn_congr_fun, intervalIntegrable_cpow, intervalIntegrable_iff_integrableOn_Ioo_of_le, measurableSet_Ioo, norm_cpow_eq_rpow_re_of_pos, s.re
-/
theorem integrableOn_Ioo_cpow_iff {s : Complex} {t : Real} (ht : 0 < t) :
    IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioo (0 : Real) t) ↔ -1 < s.re := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact intervalIntegrable_cpow' h (a := 0) (b := t)
  have B : IntegrableOn (fun a => a ^ s.re) (Ioo 0 t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioo).1 h.norm
    intro a ha
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ha.1]
  rwa [integrableOn_Ioo_rpow_iff ht] at B

@[simp]
/--
theorem `intervalIntegrable_id` / 定理 `intervalIntegrable_id`

English:
theorem intervalIntegrable_id
  statement: IntervalIntegrable (fun x => x) μ a b
  proof: continuous_id.intervalIntegrable a b

中文:
定理 intervalIntegrable_id
  结论: 整数erval整数egrable (fun x => x) μ a b
  证明: continuous_id.intervalIntegrable a b

Depends on / 依赖: continuous_id, continuous_id.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.intervalIntegrable a b

/--
theorem `intervalIntegrable_one_div` / 定理 `intervalIntegrable_one_div`

English:
theorem intervalIntegrable_one_div
  statement: (h : forall x : Real, x in [[a, b]] -> f x != 0)
  proof: (continuousOn_const.div hf h).intervalIntegrable

@[simp]

中文:
定理 intervalIntegrable_one_div
  结论: (h : 对任意 x : 实数, x in [[a, b]] -> f x != 0)
  证明: (continuousOn_const.div hf h).intervalIntegrable

@[simp]

Depends on / 依赖: continuousOn_const, continuousOn_const.div, intervalIntegrable
-/
theorem intervalIntegrable_one_div (h : forall x : Real, x in [[a, b]] -> f x != 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuousOn_const.div hf h).intervalIntegrable

@[simp]
/--
theorem `intervalIntegrable_inv` / 定理 `intervalIntegrable_inv`

English:
theorem intervalIntegrable_inv
  statement: (h : forall x : Real, x in [[a, b]] -> f x != 0)
  proof: by
  simpa only [one_div] using intervalIntegrable_one_div h hf

@[simp]

中文:
定理 intervalIntegrable_inv
  结论: (h : 对任意 x : 实数, x in [[a, b]] -> f x != 0)
  证明: by
  simpa only [one_div] using intervalIntegrable_one_div h hf

@[simp]

Depends on / 依赖: intervalIntegrable_one_div, one_div
-/
theorem intervalIntegrable_inv (h : forall x : Real, x in [[a, b]] -> f x != 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [one_div] using intervalIntegrable_one_div h hf

@[simp]
/--
theorem `intervalIntegrable_sin` / 定理 `intervalIntegrable_sin`

English:
theorem intervalIntegrable_sin
  statement: IntervalIntegrable sin μ a b
  proof: continuous_sin.intervalIntegrable a b

@[simp]

中文:
定理 intervalIntegrable_sin
  结论: 整数erval整数egrable sin μ a b
  证明: continuous_sin.intervalIntegrable a b

@[simp]

Depends on / 依赖: continuous_sin, continuous_sin.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.intervalIntegrable a b

@[simp]
/--
theorem `intervalIntegrable_cos` / 定理 `intervalIntegrable_cos`

English:
theorem intervalIntegrable_cos
  statement: IntervalIntegrable cos μ a b
  proof: continuous_cos.intervalIntegrable a b

@[simp]

中文:
定理 intervalIntegrable_cos
  结论: 整数erval整数egrable cos μ a b
  证明: continuous_cos.intervalIntegrable a b

@[simp]

Depends on / 依赖: continuous_cos, continuous_cos.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.intervalIntegrable a b

@[simp]
/--
theorem `intervalIntegrable_exp` / 定理 `intervalIntegrable_exp`

English:
theorem intervalIntegrable_exp
  statement: IntervalIntegrable exp μ a b
  proof: continuous_exp.intervalIntegrable a b

@[simp]

中文:
定理 intervalIntegrable_exp
  结论: 整数erval整数egrable exp μ a b
  证明: continuous_exp.intervalIntegrable a b

@[simp]

Depends on / 依赖: continuous_exp, continuous_exp.intervalIntegrable, intervalIntegrable
-/
theorem intervalIntegrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.intervalIntegrable a b

@[simp]
/--
theorem `_root_.IntervalIntegrable.log` / 定理 `_root_.IntervalIntegrable.log`

English:
theorem _root_.IntervalIntegrable.log
  statement: (hf : ContinuousOn f [[a, b]])
  proof: (ContinuousOn.log hf h).intervalIntegrable

中文:
定理 _root_.IntervalIntegrable.log
  结论: (hf : ContinuousOn f [[a, b]])
  证明: (ContinuousOn.log hf h).intervalIntegrable

Depends on / 依赖: ContinuousOn, ContinuousOn.log, intervalIntegrable
-/
theorem _root_.IntervalIntegrable.log (hf : ContinuousOn f [[a, b]])
    (h : forall x : Real, x in [[a, b]] -> f x != 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable

/--
The real logarithm is interval integrable (with respect to every locally finite measure) over every
interval that does not contain zero. See `intervalIntegrable_log'` for a version without any
hypothesis on the interval, but assuming the measure is the volume.
-/
@[simp]
/--
theorem `intervalIntegrable_log` / 定理 `intervalIntegrable_log`

English:
theorem intervalIntegrable_log
  given: (h : (0 : Real) ∉ [[a, b]])
  statement: IntervalIntegrable log μ a b
  proof: IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

中文:
定理 intervalIntegrable_log
  条件: (h : (0 : 实数) ∉ [[a, b]])
  结论: 整数erval整数egrable log μ a b
  证明: IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.log, continuousOn_id, ne_of_mem_of_not_mem
-/
theorem intervalIntegrable_log (h : (0 : Real) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

/--
The real logarithm is interval integrable (with respect to the volume measure) on every interval.
See `intervalIntegrable_log` for a version applying to any locally finite measure, but with an
additional hypothesis on the interval.
-/
@[simp]
/--
theorem `intervalIntegrable_log'` / 定理 `intervalIntegrable_log'`

English:
theorem intervalIntegrable_log'
  statement: IntervalIntegrable log volume a b
  proof: by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_ne

中文:
定理 intervalIntegrable_log'
  结论: 整数erval整数egrable log volume a b
  证明: by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_ne
-/
theorem intervalIntegrable_log' : IntervalIntegrable log volume a b := by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg (g := fun x => -(x * log x - x))
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro s ⟨hs, _⟩
      norm_num at *
      simpa using! (hasDerivAt_id s).sub (hasDerivAt_mul_log hs.ne.symm)
    · intro s ⟨hs₁, hs₂⟩
      grind [Pi.neg_apply, log_nonpos_iff]
  · -- Show integrability on [1…t] by continuity
    apply ContinuousOn.intervalIntegrable
    apply Real.continuousOn_log.mono
    apply Set.notMem_uIcc_of_lt zero_lt_one at hx
    simpa

/--
theorem `intervalIntegrable_one_div_one_add_sq` / 定理 `intervalIntegrable_one_div_one_add_sq`

English:
theorem intervalIntegrable_one_div_one_add_sq
  proof: by
  apply Continuous.intervalIntegrable
  fun_prop (discharger := intro; nlinarith)

@[simp]

中文:
定理 intervalIntegrable_one_div_one_add_sq
  证明: by
  apply Continuous.intervalIntegrable
  fun_prop (discharger := intro; nlinarith)

@[simp]

Depends on / 依赖: Continuous, Continuous.intervalIntegrable, discharger, fun_prop, intervalIntegrable
-/
theorem intervalIntegrable_one_div_one_add_sq :
    IntervalIntegrable (fun x : Real => 1 / (↑1 + x ^ 2)) μ a b := by
  apply Continuous.intervalIntegrable
  fun_prop (discharger := intro; nlinarith)

@[simp]
/--
theorem `intervalIntegrable_inv_one_add_sq` / 定理 `intervalIntegrable_inv_one_add_sq`

English:
theorem intervalIntegrable_inv_one_add_sq
  proof: by
  simp [← one_div, intervalIntegrable_one_div_one_add_sq]

中文:
定理 intervalIntegrable_inv_one_add_sq
  证明: by
  simp [← one_div, intervalIntegrable_one_div_one_add_sq]

Depends on / 依赖: intervalIntegrable_one_div_one_add_sq, one_div
-/
theorem intervalIntegrable_inv_one_add_sq :
    IntervalIntegrable (fun x : Real => (↑1 + x ^ 2)⁻¹) μ a b := by
  simp [← one_div, intervalIntegrable_one_div_one_add_sq]

end intervalIntegral
