/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.CircleIntegral

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Integrability for Logarithms of Meromorphic Functions

We establish integrability for functions of the form `log ‖meromorphic‖`. In the real setting, these
functions are interval integrable over every interval of the real line. This implies in particular
that logarithms of trigonometric functions are interval integrable. In the complex setting, the
functions are circle integrable over every circle in the complex plane.
-/

public section

open Filter Interval MeasureTheory MeromorphicOn Metric Real

/-!
## Interval Integrability for Logarithms of Real Meromorphic Functions
-/

section IntervalIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {f : Real -> E} {a b : Real}

/--
theorem `MeromorphicOn.intervalIntegrable_log_norm` / 定理 `MeromorphicOn.intervalIntegrable_log_norm`

English:
theorem MeromorphicOn.intervalIntegrable_log_norm
  given: (hf : MeromorphicOn f [[a, b]])
  proof: by
  by_cases t₀ : forall u : [[a, b]], meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i))]; rw [(by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto

@[deprecated (since := "2026-03-28")]
alias intervalIntegrable_log_norm_meromorphicOn := MeromorphicOn.intervalIntegrable_log_norm

中文:
定理 MeromorphicOn.interval整数egrable_log_norm
  条件: (hf : MeromorphicOn f [[a, b]])
  证明: by
  by_cases t₀ : forall u : [[a, b]], meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i))]; rw [(by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto

@[deprecated (since := "2026-03-28")]
alias intervalIntegrable_log_norm_meromorphicOn := MeromorphicOn.intervalIntegrable_log_norm

Depends on / 依赖: Filter, Filter.codiscreteWithin_mono, IntervalIntegrable, IntervalIntegrable.add, IntervalIntegrable.const_mul, IntervalIntegrable.finsum, MeromorphicOn, MeromorphicOn.divisor, MeromorphicOn.extract_zeros_poles_log, Set.uIoc_subset_uIcc, codiscreteWithin_mono, const_mul, divisor, extract_zeros_poles, extract_zeros_poles_log, filter_mono, finiteSupport, finsum, g.filter_mono, hf.extract_zeros_poles
-/
theorem MeromorphicOn.intervalIntegrable_log_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : forall u : [[a, b]], meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i))]; rw [(by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto

@[deprecated (since := "2026-03-28")]
alias intervalIntegrable_log_norm_meromorphicOn := MeromorphicOn.intervalIntegrable_log_norm

/--
theorem `MeromorphicOn.intervalIntegrable_posLog_norm` / 定理 `MeromorphicOn.intervalIntegrable_posLog_norm`

English:
theorem MeromorphicOn.intervalIntegrable_posLog_norm
  given: (hf : MeromorphicOn f [[a, b]])
  proof: by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias MeromorphicOn.intervalIntegrable_posLog_norm_meromorphicOn := intervalIntegrable_posLog_norm

中文:
定理 MeromorphicOn.interval整数egrable_posLog_norm
  条件: (hf : MeromorphicOn f [[a, b]])
  证明: by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias MeromorphicOn.intervalIntegrable_posLog_norm_meromorphicOn := intervalIntegrable_posLog_norm

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.add, const_mul, half_mul_log_add_log_abs, hf.intervalIntegrable_log_norm.abs.const_mul, hf.intervalIntegrable_log_norm.const_mul, intervalIntegrable_log_norm, mul_add, simp_rw
-/
theorem MeromorphicOn.intervalIntegrable_posLog_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias MeromorphicOn.intervalIntegrable_posLog_norm_meromorphicOn := intervalIntegrable_posLog_norm

/--
theorem `_root_.MeromorphicOn.intervalIntegrable_log` / 定理 `_root_.MeromorphicOn.intervalIntegrable_log`

English:
theorem _root_.MeromorphicOn.intervalIntegrable_log
  given: {f : Real -> Real} (hf : MeromorphicOn f [[a, b]])
  proof: by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact hf.intervalIntegrable_log_norm

中文:
定理 _root_.MeromorphicOn.interval整数egrable_log
  条件: {f : 实数 -> 实数} (hf : MeromorphicOn f [[a, b]])
  证明: by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact hf.intervalIntegrable_log_norm

Depends on / 依赖: hf.intervalIntegrable_log_norm, intervalIntegrable_log_norm
-/
theorem _root_.MeromorphicOn.intervalIntegrable_log {f : Real -> Real} (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ∘ f) volume a b := by
  rw [(by aesop : log ∘ f = (log ‖f ·‖))]
  exact hf.intervalIntegrable_log_norm

/--
theorem `intervalIntegrable_log_sin` / 定理 `intervalIntegrable_log_sin`

English:
theorem intervalIntegrable_log_sin
  statement: IntervalIntegrable (log ∘ sin) volume a b
  proof: analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log

中文:
定理 interval整数egrable_log_sin
  结论: 整数erval整数egrable (log ∘ sin) volume a b
  证明: analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log

Depends on / 依赖: analyticOnNhd_sin, analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log, intervalIntegrable_log, meromorphicOn
-/
theorem intervalIntegrable_log_sin : IntervalIntegrable (log ∘ sin) volume a b :=
  analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log

/--
theorem `intervalIntegrable_log_cos` / 定理 `intervalIntegrable_log_cos`

English:
theorem intervalIntegrable_log_cos
  statement: IntervalIntegrable (log ∘ cos) volume a b
  proof: analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log

中文:
定理 interval整数egrable_log_cos
  结论: 整数erval整数egrable (log ∘ cos) volume a b
  证明: analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log

Depends on / 依赖: analyticOnNhd_cos, analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log, intervalIntegrable_log, meromorphicOn
-/
theorem intervalIntegrable_log_cos : IntervalIntegrable (log ∘ cos) volume a b :=
  analyticOnNhd_cos.meromorphicOn.intervalIntegrable_log

end IntervalIntegrable

/-!
## Circle Integrability for Logarithms of Complex Meromorphic Functions
-/

section CircleIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {c : Complex} {R : Real} {f : Complex -> E}

/--
theorem `MeromorphicOn.circleIntegrable_log_norm` / 定理 `MeromorphicOn.circleIntegrable_log_norm`

English:
theorem MeromorphicOn.circleIntegrable_log_norm
  given: (hf : MeromorphicOn f (sphere c |R|))
  proof: by
  by_cases t₀ : forall u : (sphere c |R|), meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      apply MeromorphicOn.intervalIntegrable_log_norm
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq]; rw [norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_sphere (by simp) c
      (abs_nonneg R))] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn := MeromorphicOn.circleIntegrable_log_norm

中文:
定理 MeromorphicOn.circle整数egrable_log_norm
  条件: (hf : MeromorphicOn f (sphere c |R|))
  证明: by
  by_cases t₀ : forall u : (sphere c |R|), meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      apply MeromorphicOn.intervalIntegrable_log_norm
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq]; rw [norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_sphere (by simp) c
      (abs_nonneg R))] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn := MeromorphicOn.circleIntegrable_log_norm

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.meromorphicOn, CircleIntegrable, CircleIntegrable.add, CircleIntegrable.congr_codiscreteWithin, CircleIntegrable.finsum, IntervalIntegrable, IntervalIntegrable.const_mul, MeromorphicOn, MeromorphicOn.extract_zeros_poles_log, MeromorphicOn.intervalIntegrable_log_norm, congr_codiscreteWithin, const_mul, divisor, extract_zeros_poles, extract_zeros_poles_log, finiteSupport, finsum, g.symm, hf.extract_zeros_poles
-/
theorem MeromorphicOn.circleIntegrable_log_norm (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log ‖f ·‖) c R := by
  by_cases t₀ : forall u : (sphere c |R|), meromorphicOrderAt f u != ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((divisor f (sphere c |R|)).finiteSupport (isCompact_sphere c |R|))
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    apply CircleIntegrable.congr_codiscreteWithin h₄g.symm
    apply CircleIntegrable.add
    · apply CircleIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      apply MeromorphicOn.intervalIntegrable_log_norm
      apply AnalyticOnNhd.meromorphicOn
      apply AnalyticOnNhd.sub _ analyticOnNhd_const
      apply (analyticOnNhd_circleMap c R).mono (by tauto)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        apply h₁g.continuousOn.comp (t := sphere c |R|) (continuous_circleMap c R).continuousOn
        intro x hx
        simp
      · intro x hx
        rw [ne_eq]; rw [norm_eq_zero]
        apply h₂g ⟨circleMap c R x, circleMap_mem_sphere' c R x⟩
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_sphere (by simp) c
      (abs_nonneg R))] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[codiscreteWithin (sphere c |R|)] 0 := by
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        self_mem_codiscreteWithin (sphere c |R|)] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    apply CircleIntegrable.congr_codiscreteWithin this.symm (circleIntegrable_const 0 c R)

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn := MeromorphicOn.circleIntegrable_log_norm

/--
theorem `MeromorphicOn.circleIntegrable_log_norm_of_nonneg` / 定理 `MeromorphicOn.circleIntegrable_log_norm_of_nonneg`

English:
theorem MeromorphicOn.circleIntegrable_log_norm_of_nonneg
  statement: (hf : MeromorphicOn f (sphere c R))
  proof: by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_log_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_log_norm_of_nonneg

中文:
定理 MeromorphicOn.circle整数egrable_log_norm_of_nonneg
  结论: (hf : MeromorphicOn f (sphere c R))
  证明: by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_log_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_log_norm_of_nonneg

Depends on / 依赖: abs_of_nonneg, circleIntegrable_log_norm, hf.circleIntegrable_log_norm
-/
theorem MeromorphicOn.circleIntegrable_log_norm_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 <= R) :
    CircleIntegrable (log ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_log_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_log_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_log_norm_of_nonneg

/--
Variant of `MeromorphicOn.circleIntegrable_log_norm` for factorized rational functions.
-/
@[fun_prop]
/--
theorem `circleIntegrable_log_norm_factorizedRational` / 定理 `circleIntegrable_log_norm_factorizedRational`

English:
theorem circleIntegrable_log_norm_factorizedRational
  given: {R : Real} {c : Complex} (D : Complex -> Int)
  proof: CircleIntegrable.finsum (fun _ =>
    ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm).const_smul)

中文:
定理 circle整数egrable_log_norm_factorizedRational
  条件: {R : 实数} {c : 复形} (D : 复形 -> 整数)
  证明: CircleIntegrable.finsum (fun _ =>
    ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm).const_smul)

Depends on / 依赖: CircleIntegrable, CircleIntegrable.finsum, analyticOnNhd_const, analyticOnNhd_id, analyticOnNhd_id.sub, circleIntegrable_log_norm, const_smul, finsum, meromorphicOn, meromorphicOn.circleIntegrable_log_norm
-/
theorem circleIntegrable_log_norm_factorizedRational {R : Real} {c : Complex} (D : Complex -> Int) :
    CircleIntegrable (∑ᶠ u, ((D u) * log ‖· - u‖)) c R :=
  CircleIntegrable.finsum (fun _ =>
    ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm).const_smul)

/--
theorem `MeromorphicOn.circleIntegrable_posLog_norm` / 定理 `MeromorphicOn.circleIntegrable_posLog_norm`

English:
theorem MeromorphicOn.circleIntegrable_posLog_norm
  given: (hf : MeromorphicOn f (sphere c |R|))
  proof: by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply hf.circleIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn := MeromorphicOn.circleIntegrable_posLog_norm

中文:
定理 MeromorphicOn.circle整数egrable_posLog_norm
  条件: (hf : MeromorphicOn f (sphere c |R|))
  证明: by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply hf.circleIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn := MeromorphicOn.circleIntegrable_posLog_norm

Depends on / 依赖: CircleIntegrable, CircleIntegrable.add, X.property, circleIntegrable_log_norm, const_mul, half_mul_log_add_log_abs, hf.circleIntegrable_log_norm.abs.const_mul, hf.circleIntegrable_log_norm.const_mul, mul_add, property, simp_rw
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply hf.circleIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn := MeromorphicOn.circleIntegrable_posLog_norm

/--
theorem `MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg` / 定理 `MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg`

English:
theorem MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg
  statement: (hf : MeromorphicOn f (sphere c R))
  proof: by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_posLog_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg

中文:
定理 MeromorphicOn.circle整数egrable_posLog_norm_of_nonneg
  结论: (hf : MeromorphicOn f (sphere c R))
  证明: by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_posLog_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg

Depends on / 依赖: abs_of_nonneg, circleIntegrable_posLog_norm, hf.circleIntegrable_posLog_norm
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 <= R) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_posLog_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg

end CircleIntegrable
