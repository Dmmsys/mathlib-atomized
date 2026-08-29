/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation

/-!
# Cartan's Formula

This file establishes Cartan's classic formula,
`ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`, describing the
characteristic function `characteristic f ⊤ r` as a sum of two circle averages,

- `circleAverage (logCounting f · r) 0 1` and
- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1`.

As a corollary, Cartan's formula implies the (surprisingly non-trivial) fact that the
characteristic function is monotone; this is stated in
`ValueDistribution.characteristic_monotoneOn`.

This file also establishes circle integrability of the function
`a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0‖` and computes values of the circle average.

## References

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter Metric Real Set Topology

variable {f : Complex -> Complex} {R : Real}

namespace ValueDistribution


/--
lemma `log_trailingCoeff_eq_zero_on_unitSphere` / 引理 `log_trailingCoeff_eq_zero_on_unitSphere`

English:
lemma log_trailingCoeff_eq_zero_on_unitSphere
  statement: {a : Complex} (h : 0 < meromorphicOrderAt f 0)
  proof: by
  simp_rw [sub_eq_neg_add]
  rw [(meromorphicAt_of_meromorphicOrderAt_ne_zero
    h.ne').meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt]
  · aesop
  · rw [meromorphicOrderAt_const]
    aesop

中文:
引理 log_trailingCoeff_eq_zero_on_unitSphere
  结论: {a : 复形} (h : 0 < meromorphicOrderAt f 0)
  证明: by
  simp_rw [sub_eq_neg_add]
  rw [(meromorphicAt_of_meromorphicOrderAt_ne_zero
    h.ne').meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt]
  · aesop
  · rw [meromorphicOrderAt_const]
    aesop

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.IsStarProjection.ext_iff, FiniteDimensional, FiniteDimensional.complete, IsStarProjection, S.isStarProjection_toContinuousLinearMap_iff.mpr, T.isStarProjection_toContinuousLinearMap_iff.mpr, complete, ext_iff, isStarProjection_toContinuousLinearMap_iff
-/
private lemma log_trailingCoeff_eq_zero_on_unitSphere {a : Complex} (h : 0 < meromorphicOrderAt f 0)
    (ha : a in sphere 0 |1|) :
    log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ = 0 := by
  simp_rw [sub_eq_neg_add]
  rw [(meromorphicAt_of_meromorphicOrderAt_ne_zero
    h.ne').meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt]
  · aesop
  · rw [meromorphicOrderAt_const]
    aesop

/--
lemma `eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero` / 引理 `eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero`

English:
lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero
  statement: (h₁ : MeromorphicAt f 0)
  proof: by
  filter_upwards [self_mem_codiscreteWithin (sphere 0 |1|), compl_singleton_mem_codiscreteWithin
    (meromorphicTrailingCoeffAt f 0)] with a ha_sphere ha_ne
  congr
  rw [h₁.meromorphicTrailingCoeffAt_fun_sub_eq_sub
    (by fun_prop)]; rw [meromorphicTrailingCoeffAt_const]; rw [sub_eq_add_neg]
 

中文:
引理 eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero
  结论: (h₁ : MeromorphicAt f 0)
  证明: by
  filter_upwards [self_mem_codiscreteWithin (sphere 0 |1|), compl_singleton_mem_codiscreteWithin
    (meromorphicTrailingCoeffAt f 0)] with a ha_sphere ha_ne
  congr
  rw [h₁.meromorphicTrailingCoeffAt_fun_sub_eq_sub
    (by fun_prop)]; rw [meromorphicTrailingCoeffAt_const]; rw [sub_eq_add_neg]
 
-/
private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (h₁ : MeromorphicAt f 0)
    (h₂ : meromorphicOrderAt f 0 = 0) :
    (log ‖meromorphicTrailingCoeffAt f 0 - ·‖) =ᶠ[codiscreteWithin (sphere 0 |1|)]
      fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
  filter_upwards [self_mem_codiscreteWithin (sphere 0 |1|), compl_singleton_mem_codiscreteWithin
    (meromorphicTrailingCoeffAt f 0)] with a ha_sphere ha_ne
  congr
  rw [h₁.meromorphicTrailingCoeffAt_fun_sub_eq_sub
    (by fun_prop)]; rw [meromorphicTrailingCoeffAt_const]; rw [sub_eq_add_neg]
  · simp only [meromorphicOrderAt_const]
    aesop
  · simp only [meromorphicTrailingCoeffAt_const, ne_eq]
    grind

/--
theorem `circleIntegrable_log_meromorphicTrailingCoeffAt` / 定理 `circleIntegrable_log_meromorphicTrailingCoeffAt`

English:
theorem circleIntegrable_log_meromorphicTrailingCoeffAt
  proof: by
  by_cases h: ¬MeromorphicAt f 0
  · have {a : Complex} : ¬MeromorphicAt (fun x => f x - a) 0 := by
      rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
    simp_all
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · refine (circleIntegrable

中文:
定理 circle整数egrable_log_meromorphicTrailingCoeffAt
  证明: by
  by_cases h: ¬MeromorphicAt f 0
  · have {a : Complex} : ¬MeromorphicAt (fun x => f x - a) 0 := by
      rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
    simp_all
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · refine (circleIntegrable

Depends on / 依赖: MeromorphicAt, MeromorphicAt.const, MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt, circleIntegrable_congr, circleIntegrable_const, fun_prop, lt_trichotomy, meromorphicOrderAt, meromorphicOrderAt_const, meromorphicTrailingCoeffAt, meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
-/
theorem circleIntegrable_log_meromorphicTrailingCoeffAt :
    CircleIntegrable (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
  by_cases h: ¬MeromorphicAt f 0
  · have {a : Complex} : ¬MeromorphicAt (fun x => f x - a) 0 := by
      rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
    simp_all
  rcases lt_trichotomy (meromorphicOrderAt f 0) 0 with hneg | hzero | hpos
  · refine (circleIntegrable_congr fun a ha => ?_).2 (circleIntegrable_const
      (log ‖meromorphicTrailingCoeffAt f 0‖) 0 1)
    rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
    rw [meromorphicOrderAt_const]
    aesop
  · apply CircleIntegrable.congr_codiscreteWithin
     (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (not_not.1 h) hzero)
    simpa [norm_sub_rev] using circleIntegrable_log_norm_sub_const 1
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact fun _ => log_trailingCoeff_eq_zero_on_unitSphere hpos

/--
theorem `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos` / 定理 `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos`

English:
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
  proof: circleAverage_const_on_circle (fun _ hx => log_trailingCoeff_eq_zero_on_unitSphere h hx)

中文:
定理 circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
  证明: circleAverage_const_on_circle (fun _ hx => log_trailingCoeff_eq_zero_on_unitSphere h hx)

Depends on / 依赖: circleAverage_const_on_circle, log_trailingCoeff_eq_zero_on_unitSphere
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
    (h : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 = 0 :=
  circleAverage_const_on_circle (fun _ hx => log_trailingCoeff_eq_zero_on_unitSphere h hx)

/--
theorem `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero` / 定理 `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero`

English:
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
  proof: by
  by_cases hf : MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  have {a : Complex} : ¬ MeromorphicAt (fun x

中文:
定理 circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
  证明: by
  by_cases hf : MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  have {a : Complex} : ¬ MeromorphicAt (fun x

Depends on / 依赖: MeromorphicAt, MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt, circleAverage_congr_codiscreteWithin, circleAverage_const, circleAverage_log_norm_sub_const_eq_posLog, eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero, fun_prop, norm_sub_rev, simp_rw, zero_ne_one, zero_ne_one.symm
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (h : meromorphicOrderAt f 0 = 0) :
    circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log⁺ ‖meromorphicTrailingCoeffAt f 0‖ := by
  by_cases hf : MeromorphicAt f 0
  · rw [← circleAverage_congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h) zero_ne_one.symm]
    simp_rw [norm_sub_rev]
    rw [circleAverage_log_norm_sub_const_eq_posLog]
  have {a : Complex} : ¬ MeromorphicAt (fun x => f x - a) 0 := by
    rwa [MeromorphicAt.meromorphicAt_fun_sub_iff_meromorphicAt₂ (by fun_prop)]
  simp_all [circleAverage_const]

/--
theorem `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero` / 定理 `circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero`

English:
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
  proof: by
  rw [circleAverage_congr_sphere (f₂ := fun _ => log ‖meromorphicTrailingCoeffAt f 0‖)]; rw [circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  aesop

中文:
定理 circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
  证明: by
  rw [circleAverage_congr_sphere (f₂ := fun _ => log ‖meromorphicTrailingCoeffAt f 0‖)]; rw [circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  aesop

Depends on / 依赖: MeromorphicAt, MeromorphicAt.const, circleAverage_congr_sphere, circleAverage_const, meromorphicOrderAt_const, meromorphicTrailingCoeffAt, meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
    (h : meromorphicOrderAt f 0 < 0) :
    circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1
      = log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [circleAverage_congr_sphere (f₂ := fun _ => log ‖meromorphicTrailingCoeffAt f 0‖)]; rw [circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [(MeromorphicAt.const a 0).meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt]
  rw [meromorphicOrderAt_const]
  aesop

/--
lemma `logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top` / 引理 `logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top`

English:
lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
  proof: by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero]; rw [← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_su

中文:
引理 logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
  证明: by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero]; rw [← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_su
-/
private lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    (h : Meromorphic f) (hR : R != 0) (a : Complex) :
    logCounting f a R + log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ =
      circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R := by
  have : logCounting f a R - logCounting f ⊤ R = circleAverage (log ‖f · - a‖) 0 R
        - log ‖meromorphicTrailingCoeffAt (f · - a) 0‖ := by
    rw [logCounting_coe_eq_logCounting_sub_const_zero]; rw [← logCounting_sub_const h]
    exact logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (by fun_prop) hR
  linarith

/--
theorem `circleIntegrable_logCounting` / 定理 `circleIntegrable_logCounting`

English:
theorem circleIntegrable_logCounting
  given: (h : Meromorphic f)
  proof: by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
.add convert circleIntegrable_circleAverage_log_norm_sub h
.sub (circleIntegrable_const (logCounting f ⊤ R) 0 1)
    circleIntegrable_log_meromorphicTrailingCoeffAt
  simpa using eq_sub_of_add_eq
    (logCounting_add_log

中文:
定理 circle整数egrable_logCounting
  条件: (h : 亚纯 f)
  证明: by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
.add convert circleIntegrable_circleAverage_log_norm_sub h
.sub (circleIntegrable_const (logCounting f ⊤ R) 0 1)
    circleIntegrable_log_meromorphicTrailingCoeffAt
  simpa using eq_sub_of_add_eq
    (logCounting_add_log

Depends on / 依赖: ValueDistribution, ValueDistribution.logCounting_eval_zero, circleIntegrable_circleAverage_log_norm_sub, circleIntegrable_const, circleIntegrable_log_meromorphicTrailingCoeffAt, convert, eq_sub_of_add_eq, logCounting, logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top, logCounting_eval_zero
-/
theorem circleIntegrable_logCounting (h : Meromorphic f) :
    CircleIntegrable (logCounting f · R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
.add convert circleIntegrable_circleAverage_log_norm_sub h
.sub (circleIntegrable_const (logCounting f ⊤ R) 0 1)
    circleIntegrable_log_meromorphicTrailingCoeffAt
  simpa using eq_sub_of_add_eq
    (logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR _)

/-!
## Cartan's formula
-/

/--
theorem `characteristic_top_eq_circleAverage_add_circleAverage` / 定理 `characteristic_top_eq_circleAverage_add_circleAverage`

English:
theorem characteristic_top_eq_circleAverage_add_circleAverage
  given: (h : Meromorphic f) (hR : R != 0)
  proof: calc
  characteristic f ⊤ R
      = circleAverage (fun a => circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top]; rw [← circleAverage_circleAverage_eq_proximity_top h]; rw [circleAverage_fun

中文:
定理 characteristic_top_eq_circleAverage_add_circleAverage
  条件: (h : 亚纯 f) (hR : R != 0)
  证明: calc
  characteristic f ⊤ R
      = circleAverage (fun a => circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top]; rw [← circleAverage_circleAverage_eq_proximity_top h]; rw [circleAverage_fun
-/
theorem characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f) (hR : R != 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1
      + circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := calc
  characteristic f ⊤ R
      = circleAverage (fun a => circleAverage (log ‖f · - a‖) 0 R + logCounting f ⊤ R) 0 1 := by
      simp only [characteristic, proximity, ↓reduceDIte, Pi.add_apply]
      rw [← proximity_top]; rw [← circleAverage_circleAverage_eq_proximity_top h]; rw [circleAverage_fun_add (circleIntegrable_circleAverage_log_norm_sub h)
          (circleIntegrable_const (logCounting f ⊤ R) 0 1)]; rw [circleAverage_const]
    _ = circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1 := by
      rw [← circleAverage_add (circleIntegrable_logCounting h)
        circleIntegrable_log_meromorphicTrailingCoeffAt]; rw [circleAverage_congr_sphere]
      intro a ha
      simp [logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a]

/--
theorem `characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos` / 定理 `characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos`

English:
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
  proof: by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos h₂f]

中文:
定理 characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
  证明: by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos h₂f]

Depends on / 依赖: characteristic_top_eq_circleAverage_add_circleAverage, circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
-/
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
    (h₁f : Meromorphic f) (h₂f : 0 < meromorphicOrderAt f 0) (hR : R != 0) :
    characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 := by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos h₂f]

/--
theorem `characteristic_top_eq_circleAverage_add_const` / 定理 `characteristic_top_eq_circleAverage_add_const`

English:
theorem characteristic_top_eq_circleAverage_add_const
  given: (h : Meromorphic f)
  proof: ⟨circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr => characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

中文:
定理 characteristic_top_eq_circleAverage_add_const
  条件: (h : 亚纯 f)
  证明: ⟨circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr => characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

Depends on / 依赖: characteristic_top_eq_circleAverage_add_circleAverage, circleAverage, meromorphicTrailingCoeffAt
-/
theorem characteristic_top_eq_circleAverage_add_const (h : Meromorphic f) :
    exists const, forall R != 0, characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1 + const :=
  ⟨circleAverage (fun a => log ‖meromorphicTrailingCoeffAt (f · - a) 0‖) 0 1,
    fun _ hr => characteristic_top_eq_circleAverage_add_circleAverage h hr⟩

/-!
## Application: Monotonicity of the Characteristic Function
-/

/--
theorem `characteristic_monotoneOn` / 定理 `characteristic_monotoneOn`

English:
theorem characteristic_monotoneOn
  given: (h : Meromorphic f)
  proof: by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne']; rw [characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

中文:
定理 characteristic_monotoneOn
  条件: (h : 亚纯 f)
  证明: by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne']; rw [characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

Depends on / 依赖: characteristic_top_eq_circleAverage_add_circleAverage, circleIntegrable_logCounting, ha.ne, hb.ne, logCounting_monotoneOn
-/
theorem characteristic_monotoneOn (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [characteristic_top_eq_circleAverage_add_circleAverage h ha.ne']; rw [characteristic_top_eq_circleAverage_add_circleAverage h hb.ne']
  gcongr <;> try exact circleIntegrable_logCounting h
  exact logCounting_monotoneOn ha hb hab

end ValueDistribution
