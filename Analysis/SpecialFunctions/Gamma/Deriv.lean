/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Derivative of the Gamma function

This file shows that the (complex) `Γ` function is complex-differentiable at all `s : ℂ` with
`s ∉ {-n : n ∈ ℕ}`, as well as the real counterpart.

## Main results

* `Complex.differentiableAt_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `Real.differentiableAt_Gamma`: `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/

public section


noncomputable section

open Filter Set Real Asymptotics
open scoped Topology

namespace Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/--
theorem `GammaIntegral_eq_mellin` / 定理 `GammaIntegral_eq_mellin`

English:
theorem GammaIntegral_eq_mellin
  statement: GammaIntegral = mellin fun x => ↑(Real.exp (-x))
  proof: funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

中文:
定理 Gamma整数egral_eq_mellin
  结论: Gamma整数egral = mellin fun x => ↑(实数.exp (-x))
  证明: funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

Depends on / 依赖: GammaIntegral, mellin, mul_comm, smul_eq_mul
-/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x)) :=
  funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

/--
theorem `hasDerivAt_GammaIntegral` / 定理 `hasDerivAt_GammaIntegral`

English:
theorem hasDerivAt_GammaIntegral
  given: {s : Complex} (hs : 0 < s.re)
  proof: by
  rw [GammaIntegral_eq_mellin]
  convert! (mellin_hasDerivAt_of_isBigO_rpow (E := Complex) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : Complex))) one_ne_zero
    rw [(by simp : (1 : Complex) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

@[fun_prop]

中文:
定理 hasDerivAt_Gamma整数egral
  条件: {s : 复形} (hs : 0 < s.re)
  证明: by
  rw [GammaIntegral_eq_mellin]
  convert! (mellin_hasDerivAt_of_isBigO_rpow (E := Complex) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : Complex))) one_ne_zero
    rw [(by simp : (1 : Complex) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

@[fun_prop]

Depends on / 依赖: Continuous, Continuous.continuousOn, GammaIntegral_eq_mellin, Real.continuous_exp.comp, Tendsto, continuousOn, continuous_exp, continuous_neg, continuous_ofReal, continuous_ofReal.comp, convert, isBigO, isBigO_const_of_tendsto, isBigO_norm_left, isLittleO_exp_neg_mul_rpow_atTop, locallyIntegrableOn, lt_add_one, measurableSet_Ioi, mellin_hasDerivAt_of_isBigO_rpow, neg_one_mul
-/
theorem hasDerivAt_GammaIntegral {s : Complex} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : Real in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  convert! (mellin_hasDerivAt_of_isBigO_rpow (E := Complex) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : Complex))) one_ne_zero
    rw [(by simp : (1 : Complex) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

@[fun_prop]
/--
theorem `differentiableAt_Gamma` / 定理 `differentiableAt_Gamma`

English:
theorem differentiableAt_Gamma
  given: (s : Complex) (hs : forall m : Nat, s != -m)
  statement: DifferentiableAt Complex Gamma s
  proof: by
  -- We will show, by induction on `n`, that `Gamma` is differentiable on `-n < Re s`.
  suffices forall (n : Nat) (s : Complex) (hsre : -n < s.re) (hs : forall m : Nat, s != -m), DifferentiableAt Complex _ s from
    this (⌊-s.re⌋₊ + 1) s (by grind [Nat.lt_floor_add_one (-s.re)]) hs
  intro n s hsre hs
  induction n generalizing s with
  | zero =>
    -- Case `n = 0`: use relation to `gammaIntegral`
    replace hsre : 0 < s.re := by simpa using hsre
    have : IsOpen {s : Complex | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    apply (hasDerivAt_GammaIntegral (by simpa using hsre)).differentiableAt.congr_of_eventuallyEq
    filter_upwards [this.mem_nhds hsre] with a using Gamma_eq_integral
  | succ n IH =>
    -- Induction step: use recurrence relation
    have hsne : s != 0 := by grind [hs 0]
    specialize IH (s + 1) (by grind [add_re, one_re]) (fun m => by grind [hs (m + 1)])
    have := IH.comp s (show DifferentiableAt Complex (fun s => s + 1) s by fun_prop)
    apply (this.fun_div differentiableAt_id hsne).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hsne] using by grind

中文:
定理 differentiableAt_Gamma
  条件: (s : 复形) (hs : 对任意 m : 自然数, s != -m)
  结论: DifferentiableAt 复形 Gamma s
  证明: by
  -- We will show, by induction on `n`, that `Gamma` is differentiable on `-n < Re s`.
  suffices forall (n : Nat) (s : Complex) (hsre : -n < s.re) (hs : forall m : Nat, s != -m), DifferentiableAt Complex _ s from
    this (⌊-s.re⌋₊ + 1) s (by grind [Nat.lt_floor_add_one (-s.re)]) hs
  intro n s hsre hs
  induction n generalizing s with
  | zero =>
    -- Case `n = 0`: use relation to `gammaIntegral`
    replace hsre : 0 < s.re := by simpa using hsre
    have : IsOpen {s : Complex | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    apply (hasDerivAt_GammaIntegral (by simpa using hsre)).differentiableAt.congr_of_eventuallyEq
    filter_upwards [this.mem_nhds hsre] with a using Gamma_eq_integral
  | succ n IH =>
    -- Induction step: use recurrence relation
    have hsne : s != 0 := by grind [hs 0]
    specialize IH (s + 1) (by grind [add_re, one_re]) (fun m => by grind [hs (m + 1)])
    have := IH.comp s (show DifferentiableAt Complex (fun s => s + 1) s by fun_prop)
    apply (this.fun_div differentiableAt_id hsne).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hsne] using by grind
-/
theorem differentiableAt_Gamma (s : Complex) (hs : forall m : Nat, s != -m) : DifferentiableAt Complex Gamma s := by
  -- We will show, by induction on `n`, that `Gamma` is differentiable on `-n < Re s`.
  suffices forall (n : Nat) (s : Complex) (hsre : -n < s.re) (hs : forall m : Nat, s != -m), DifferentiableAt Complex _ s from
    this (⌊-s.re⌋₊ + 1) s (by grind [Nat.lt_floor_add_one (-s.re)]) hs
  intro n s hsre hs
  induction n generalizing s with
  | zero =>
    -- Case `n = 0`: use relation to `gammaIntegral`
    replace hsre : 0 < s.re := by simpa using hsre
    have : IsOpen {s : Complex | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    apply (hasDerivAt_GammaIntegral (by simpa using hsre)).differentiableAt.congr_of_eventuallyEq
    filter_upwards [this.mem_nhds hsre] with a using Gamma_eq_integral
  | succ n IH =>
    -- Induction step: use recurrence relation
    have hsne : s != 0 := by grind [hs 0]
    specialize IH (s + 1) (by grind [add_re, one_re]) (fun m => by grind [hs (m + 1)])
    have := IH.comp s (show DifferentiableAt Complex (fun s => s + 1) s by fun_prop)
    apply (this.fun_div differentiableAt_id hsne).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hsne] using by grind

/--
theorem `differentiableAt_Gamma_one` / 定理 `differentiableAt_Gamma_one`

English:
theorem differentiableAt_Gamma_one
  statement: DifferentiableAt Complex Gamma 1
  proof: differentiableAt_Gamma 1 (by norm_cast; simp)

中文:
定理 differentiableAt_Gamma_one
  结论: DifferentiableAt 复形 Gamma 1
  证明: differentiableAt_Gamma 1 (by norm_cast; simp)

Depends on / 依赖: differentiableAt_Gamma
-/
theorem differentiableAt_Gamma_one : DifferentiableAt Complex Gamma 1 :=
  differentiableAt_Gamma 1 (by norm_cast; simp)

/--
theorem `continuousAt_Gamma` / 定理 `continuousAt_Gamma`

English:
theorem continuousAt_Gamma
  given: (s : Complex) (hs : forall m : Nat, s != -m)
  statement: ContinuousAt Gamma s
  proof: (differentiableAt_Gamma s hs).continuousAt

中文:
定理 continuousAt_Gamma
  条件: (s : 复形) (hs : 对任意 m : 自然数, s != -m)
  结论: ContinuousAt Gamma s
  证明: (differentiableAt_Gamma s hs).continuousAt

Depends on / 依赖: continuousAt, differentiableAt_Gamma
-/
theorem continuousAt_Gamma (s : Complex) (hs : forall m : Nat, s != -m) : ContinuousAt Gamma s :=
  (differentiableAt_Gamma s hs).continuousAt

/--
theorem `continuousAt_Gamma_one` / 定理 `continuousAt_Gamma_one`

English:
theorem continuousAt_Gamma_one
  statement: ContinuousAt Gamma 1
  proof: differentiableAt_Gamma_one.continuousAt

中文:
定理 continuousAt_Gamma_one
  结论: ContinuousAt Gamma 1
  证明: differentiableAt_Gamma_one.continuousAt

Depends on / 依赖: continuousAt, differentiableAt_Gamma_one, differentiableAt_Gamma_one.continuousAt
-/
theorem continuousAt_Gamma_one : ContinuousAt Gamma 1 :=
  differentiableAt_Gamma_one.continuousAt

/--
theorem `tendsto_self_mul_Gamma_nhds_zero` / 定理 `tendsto_self_mul_Gamma_nhds_zero`

English:
theorem tendsto_self_mul_Gamma_nhds_zero
  statement: Tendsto (fun z : Complex => z * Gamma z) (𝓝[!=] 0) (𝓝 1)
  proof: by
  rw [show 𝓝 (1 : Complex) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add]; rw [Complex.Gamma_one]]
  refine tendsto_nhdsWithin_congr Gamma_add_one (continuousAt_iff_punctured_nhds.mp ?_)
  exact ContinuousAt.comp' (by simp [continuousAt_Gamma_one]) (continuous_add_const 1).continuousAt

中文:
定理 tendsto_self_mul_Gamma_nhds_zero
  结论: 收敛 (fun z : 复形 => z * Gamma z) (𝓝[!=] 0) (𝓝 1)
  证明: by
  rw [show 𝓝 (1 : Complex) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add]; rw [Complex.Gamma_one]]
  refine tendsto_nhdsWithin_congr Gamma_add_one (continuousAt_iff_punctured_nhds.mp ?_)
  exact ContinuousAt.comp' (by simp [continuousAt_Gamma_one]) (continuous_add_const 1).continuousAt

Depends on / 依赖: Complex.Gamma_one, ContinuousAt, ContinuousAt.comp, Gamma_add_one, Gamma_one, continuousAt, continuousAt_Gamma_one, continuousAt_iff_punctured_nhds, continuousAt_iff_punctured_nhds.mp, continuous_add_const, tendsto_nhdsWithin_congr, zero_add
-/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : Complex => z * Gamma z) (𝓝[!=] 0) (𝓝 1) := by
  rw [show 𝓝 (1 : Complex) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add]; rw [Complex.Gamma_one]]
  refine tendsto_nhdsWithin_congr Gamma_add_one (continuousAt_iff_punctured_nhds.mp ?_)
  exact ContinuousAt.comp' (by simp [continuousAt_Gamma_one]) (continuous_add_const 1).continuousAt

/--
theorem `not_continuousAt_Gamma_zero` / 定理 `not_continuousAt_Gamma_zero`

English:
theorem not_continuousAt_Gamma_zero
  statement: ¬ ContinuousAt Gamma 0
  proof: tendsto_self_mul_Gamma_nhds_zero.not_tendsto (by simp) ∘
    continuousAt_iff_punctured_nhds.mp ∘ continuousAt_id.mul

中文:
定理 not_continuousAt_Gamma_zero
  结论: ¬ ContinuousAt Gamma 0
  证明: tendsto_self_mul_Gamma_nhds_zero.not_tendsto (by simp) ∘
    continuousAt_iff_punctured_nhds.mp ∘ continuousAt_id.mul

Depends on / 依赖: continuousAt_id, continuousAt_id.mul, continuousAt_iff_punctured_nhds, continuousAt_iff_punctured_nhds.mp, not_tendsto, tendsto_self_mul_Gamma_nhds_zero, tendsto_self_mul_Gamma_nhds_zero.not_tendsto
-/
theorem not_continuousAt_Gamma_zero : ¬ ContinuousAt Gamma 0 :=
  tendsto_self_mul_Gamma_nhds_zero.not_tendsto (by simp) ∘
    continuousAt_iff_punctured_nhds.mp ∘ continuousAt_id.mul

/--
theorem `not_differentiableAt_Gamma_zero` / 定理 `not_differentiableAt_Gamma_zero`

English:
theorem not_differentiableAt_Gamma_zero
  statement: ¬ DifferentiableAt Complex Gamma 0
  proof: mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

中文:
定理 not_differentiableAt_Gamma_zero
  结论: ¬ DifferentiableAt 复形 Gamma 0
  证明: mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

Depends on / 依赖: DifferentiableAt, DifferentiableAt.continuousAt, continuousAt, not_continuousAt_Gamma_zero
-/
theorem not_differentiableAt_Gamma_zero : ¬ DifferentiableAt Complex Gamma 0 :=
  mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

/--
theorem `not_continuousAt_Gamma_neg_nat` / 定理 `not_continuousAt_Gamma_neg_nat`

English:
theorem not_continuousAt_Gamma_neg_nat
  given: (n : Nat)
  statement: ¬ ContinuousAt Gamma (-n)
  proof: by
  induction n
  case zero =>
    rw [Nat.cast_zero]; rw [neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose ih
    rw [Nat.cast_add]; rw [Nat.cast_one] at ih
    suffices ContinuousAt (fun s => Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s => Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s => s - 1) (continuous_sub_right 1).continuousAt
    rw [← neg_add']
    have h0 : -(n + 1) != (0 : Complex) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

中文:
定理 not_continuousAt_Gamma_neg_nat
  条件: (n : 自然数)
  结论: ¬ ContinuousAt Gamma (-n)
  证明: by
  induction n
  case zero =>
    rw [Nat.cast_zero]; rw [neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose ih
    rw [Nat.cast_add]; rw [Nat.cast_one] at ih
    suffices ContinuousAt (fun s => Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s => Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s => s - 1) (continuous_sub_right 1).continuousAt
    rw [← neg_add']
    have h0 : -(n + 1) != (0 : Complex) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

Depends on / 依赖: ContinuousAt, Nat.cast_add, Nat.cast_one, Nat.cast_zero, cast_add, cast_add_one_ne_zero, cast_one, cast_zero, continuousAt, continuousAt_id, continuousAt_id.mul, continuous_sub_right, contrapose, n.cast_add_one_ne_zero, neg_add, neg_ne_zero, neg_ne_zero.mpr, neg_zero, not_continuousAt_Gamma_zero, this.comp
-/
theorem not_continuousAt_Gamma_neg_nat (n : Nat) : ¬ ContinuousAt Gamma (-n) := by
  induction n
  case zero =>
    rw [Nat.cast_zero]; rw [neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose ih
    rw [Nat.cast_add]; rw [Nat.cast_one] at ih
    suffices ContinuousAt (fun s => Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s => Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s => s - 1) (continuous_sub_right 1).continuousAt
    rw [← neg_add']
    have h0 : -(n + 1) != (0 : Complex) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

/--
theorem `not_differentiableAt_Gamma_neg_nat` / 定理 `not_differentiableAt_Gamma_neg_nat`

English:
theorem not_differentiableAt_Gamma_neg_nat
  given: (n : Nat)
  statement: ¬ DifferentiableAt Complex Gamma (-n)
  proof: mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

中文:
定理 not_differentiableAt_Gamma_neg_nat
  条件: (n : 自然数)
  结论: ¬ DifferentiableAt 复形 Gamma (-n)
  证明: mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.continuousAt, continuousAt, not_continuousAt_Gamma_neg_nat
-/
theorem not_differentiableAt_Gamma_neg_nat (n : Nat) : ¬ DifferentiableAt Complex Gamma (-n) :=
  mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

/--
theorem `deriv_Gamma_add_one` / 定理 `deriv_Gamma_add_one`

English:
theorem deriv_Gamma_add_one
  given: (s : Complex) (hs : s != 0)
  proof: by
  by_cases! h : exists m : Nat, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [← Nat.cast_one]; rw [← Nat.cast_sub]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m)]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1))]; rw [Gamma_neg_nat_eq_zero]; rw [zero_add]; rw [mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s => Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using! HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

中文:
定理 deriv_Gamma_add_one
  条件: (s : 复形) (hs : s != 0)
  证明: by
  by_cases! h : exists m : Nat, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [← Nat.cast_one]; rw [← Nat.cast_sub]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m)]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1))]; rw [Gamma_neg_nat_eq_zero]; rw [zero_add]; rw [mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s => Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using! HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

Depends on / 依赖: Gamma_neg_nat_eq_zero, HasDerivWithinAt, Nat.cast_ne_zero, Nat.cast_one, Nat.cast_sub, Nat.one_le_iff_ne_zero, cast_ne_zero, cast_one, cast_sub, deriv_zero_of_not_differentiableAt, mul_zero, neg_ne_zero, neg_sub, not_differentiableAt_Gamma_neg_nat, one_le_iff_ne_zero, sub_neg_eq_add, zero_add
-/
theorem deriv_Gamma_add_one (s : Complex) (hs : s != 0) :
    deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s := by
  by_cases! h : exists m : Nat, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [← Nat.cast_one]; rw [← Nat.cast_sub]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m)]; rw [deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1))]; rw [Gamma_neg_nat_eq_zero]; rw [zero_add]; rw [mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s => Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using! HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

end GammaHasDeriv

end Complex

namespace Real

@[fun_prop]
/--
theorem `differentiableAt_Gamma` / 定理 `differentiableAt_Gamma`

English:
theorem differentiableAt_Gamma
  given: {s : Real} (hs : forall m : Nat, s != -m)
  statement: DifferentiableAt Real Gamma s
  proof: by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  exact hs

中文:
定理 differentiableAt_Gamma
  条件: {s : 实数} (hs : 对任意 m : 自然数, s != -m)
  结论: DifferentiableAt 实数 Gamma s
  证明: by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  exact hs

Depends on / 依赖: Complex.differentiableAt_Gamma, Complex.ofReal_inj, Complex.ofReal_natCast, Complex.ofReal_neg, differentiableAt, differentiableAt_Gamma, hasDerivAt, hasDerivAt.real_of_complex.differentiableAt, ofReal_inj, ofReal_natCast, ofReal_neg, real_of_complex, simp_rw
-/
theorem differentiableAt_Gamma {s : Real} (hs : forall m : Nat, s != -m) : DifferentiableAt Real Gamma s := by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  exact hs

/--
theorem `differentiableOn_Gamma_Ioi` / 定理 `differentiableOn_Gamma_Ioi`

English:
theorem differentiableOn_Gamma_Ioi
  statement: DifferentiableOn Real Gamma (Ioi 0)
  proof: fun _ h => (differentiableAt_Gamma <| by bound [mem_Ioi.mp h]).differentiableWithinAt

中文:
定理 differentiableOn_Gamma_Ioi
  结论: DifferentiableOn 实数 Gamma (左开右无界区间 0)
  证明: fun _ h => (differentiableAt_Gamma <| by bound [mem_Ioi.mp h]).differentiableWithinAt

Depends on / 依赖: differentiableAt_Gamma, differentiableWithinAt, mem_Ioi, mem_Ioi.mp
-/
theorem differentiableOn_Gamma_Ioi : DifferentiableOn Real Gamma (Ioi 0) :=
  fun _ h => (differentiableAt_Gamma <| by bound [mem_Ioi.mp h]).differentiableWithinAt

end Real
