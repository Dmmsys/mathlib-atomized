/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# Translation and scaling of integral curves

New integral curves may be constructed by translating or scaling the domain of an existing integral
curve.

This file mirrors `Mathlib/Analysis/ODE/Transform`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

public section

open Function Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ γ' : Real -> M} {v : (x : M) -> TangentSpace I x} {s s' : Set Real} {t₀ : Real}

/-! ### Translation lemmas -/

section Translation

/--
lemma `IsMIntegralCurveOn.comp_add` / 引理 `IsMIntegralCurveOn.comp_add`

English:
lemma IsMIntegralCurveOn.comp_add
  given: (hγ : IsMIntegralCurveOn γ v s) (dt : Real)
  proof: by
  intro t ht
  rw [comp_apply]; rw [← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ subset_rfl
  refine ⟨(continuous_add_const _).continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  exact (hasFDerivWithinAt_id _

中文:
引理 IsM整数egralCurveOn.comp_add
  条件: (hγ : IsM整数egralCurveOn γ v s) (dt : 实数)
  证明: by
  intro t ht
  rw [comp_apply]; rw [← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ subset_rfl
  refine ⟨(continuous_add_const _).continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  exact (hasFDerivWithinAt_id _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_id, ContinuousLinearMap.smulRight, HasMFDerivWithinAt, HasMFDerivWithinAt.comp, add_const, comp_apply, comp_id, continuousWithinAt, continuous_add_const, hasFDerivWithinAt_id, mfld_simps, smulRight, subset_rfl
-/
lemma IsMIntegralCurveOn.comp_add (hγ : IsMIntegralCurveOn γ v s) (dt : Real) :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt in s } := by
  intro t ht
  rw [comp_apply]; rw [← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivWithinAt.comp t (hγ (t + dt) ht) _ subset_rfl
  refine ⟨(continuous_add_const _).continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  exact (hasFDerivWithinAt_id _ _).add_const _

/--
lemma `isMIntegralCurveOn_comp_add` / 引理 `isMIntegralCurveOn_comp_add`

English:
lemma isMIntegralCurveOn_comp_add
  given: {dt : Real}
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp
  · simp

中文:
引理 isM整数egralCurveOn_comp_add
  条件: {dt : 实数}
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp
  · simp

Depends on / 依赖: comp_add, convert
-/
lemma isMIntegralCurveOn_comp_add {dt : Real} :
    IsMIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt in s } ↔ IsMIntegralCurveOn γ v s := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp
  · simp

/--
lemma `isMIntegralCurveOn_comp_sub` / 引理 `isMIntegralCurveOn_comp_sub`

English:
lemma isMIntegralCurveOn_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isMIntegralCurveOn_comp_add (dt := -dt)

中文:
引理 isM整数egralCurveOn_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isMIntegralCurveOn_comp_add (dt := -dt)

Depends on / 依赖: isMIntegralCurveOn_comp_add
-/
lemma isMIntegralCurveOn_comp_sub {dt : Real} :
    IsMIntegralCurveOn (γ ∘ (· - dt)) v { t | t - dt in s } ↔ IsMIntegralCurveOn γ v s := by
  simpa using! isMIntegralCurveOn_comp_add (dt := -dt)

/--
lemma `IsMIntegralCurveAt.comp_add` / 引理 `IsMIntegralCurveAt.comp_add`

English:
lemma IsMIntegralCurveAt.comp_add
  given: (hγ : IsMIntegralCurveAt γ v t₀) (dt : Real)
  proof: by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert! h.comp_add dt
  rw [Metric.ball]
  simp_rw [Metric.mem_ball, Real.dist_eq, ← sub_add, add_sub_right_comm]

中文:
引理 IsM整数egralCurveAt.comp_add
  条件: (hγ : IsM整数egralCurveAt γ v t₀) (dt : 实数)
  证明: by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert! h.comp_add dt
  rw [Metric.ball]
  simp_rw [Metric.mem_ball, Real.dist_eq, ← sub_add, add_sub_right_comm]

Depends on / 依赖: Metric, Metric.ball, Metric.mem_ball, Real.dist_eq, add_sub_right_comm, comp_add, convert, dist_eq, h.comp_add, isMIntegralCurveAt_iff, mem_ball, simp_rw, sub_add
-/
lemma IsMIntegralCurveAt.comp_add (hγ : IsMIntegralCurveAt γ v t₀) (dt : Real) :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert! h.comp_add dt
  rw [Metric.ball]
  simp_rw [Metric.mem_ball, Real.dist_eq, ← sub_add, add_sub_right_comm]

/--
lemma `isMIntegralCurveAt_comp_add` / 引理 `isMIntegralCurveAt_comp_add`

English:
lemma isMIntegralCurveAt_comp_add
  given: {dt : Real}
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

中文:
引理 isM整数egralCurveAt_comp_add
  条件: {dt : 实数}
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

Depends on / 依赖: Function, Function.comp_apply, comp_add, comp_apply, convert, neg_add_cancel_right, sub_add_cancel, sub_neg_eq_add
-/
lemma isMIntegralCurveAt_comp_add {dt : Real} :
    IsMIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) ↔ IsMIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  · ext t
    simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

/--
lemma `isMIntegralCurveAt_comp_sub` / 引理 `isMIntegralCurveAt_comp_sub`

English:
lemma isMIntegralCurveAt_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isMIntegralCurveAt_comp_add (dt := -dt)

中文:
引理 isM整数egralCurveAt_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isMIntegralCurveAt_comp_add (dt := -dt)

Depends on / 依赖: isMIntegralCurveAt_comp_add
-/
lemma isMIntegralCurveAt_comp_sub {dt : Real} :
    IsMIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) ↔ IsMIntegralCurveAt γ v t₀ := by
  simpa using! isMIntegralCurveAt_comp_add (dt := -dt)

/--
lemma `IsMIntegralCurve.comp_add` / 引理 `IsMIntegralCurve.comp_add`

English:
lemma IsMIntegralCurve.comp_add
  given: (hγ : IsMIntegralCurve γ v) (dt : Real)
  proof: by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt

中文:
引理 IsM整数egralCurve.comp_add
  条件: (hγ : IsM整数egralCurve γ v) (dt : 实数)
  证明: by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt

Depends on / 依赖: comp_add, isMIntegralCurve_iff_isMIntegralCurveOn
-/
lemma IsMIntegralCurve.comp_add (hγ : IsMIntegralCurve γ v) (dt : Real) :
    IsMIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  simpa using hγ.comp_add dt

/--
lemma `isMIntegralCurve_comp_add` / 引理 `isMIntegralCurve_comp_add`

English:
lemma isMIntegralCurve_comp_add
  given: {dt : Real}
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

中文:
引理 isM整数egralCurve_comp_add
  条件: {dt : 实数}
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

Depends on / 依赖: Function, Function.comp_apply, comp_add, comp_apply, convert, neg_add_cancel_right
-/
lemma isMIntegralCurve_comp_add {dt : Real} :
    IsMIntegralCurve (γ ∘ (· + dt)) v ↔ IsMIntegralCurve γ v := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_add _⟩
  convert! hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

/--
lemma `isMIntegralCurve_comp_sub` / 引理 `isMIntegralCurve_comp_sub`

English:
lemma isMIntegralCurve_comp_sub
  given: {dt : Real}
  proof: by
  simpa using! isMIntegralCurve_comp_add (dt := -dt)

中文:
引理 isM整数egralCurve_comp_sub
  条件: {dt : 实数}
  证明: by
  simpa using! isMIntegralCurve_comp_add (dt := -dt)

Depends on / 依赖: isMIntegralCurve_comp_add
-/
lemma isMIntegralCurve_comp_sub {dt : Real} :
    IsMIntegralCurve (γ ∘ (· - dt)) v ↔ IsMIntegralCurve γ v := by
  simpa using! isMIntegralCurve_comp_add (dt := -dt)

end Translation

/-! ### Scaling lemmas -/

section Scaling

open Manifold

/--
lemma `IsMIntegralCurveOn.comp_mul` / 引理 `IsMIntegralCurveOn.comp_mul`

English:
lemma IsMIntegralCurveOn.comp_mul
  given: (hγ : IsMIntegralCurveOn γ v s) (a : Real)
  proof: by
  intro t ht
  have : (1 : Real ->L[Real] Real).smulRight (a • v (γ (t * a))) =
      (1 : Real ->L[Real] Real).smulRight (v (γ (t * a))) ∘SL (1 : Real ->L[Real] Real).smulRight a := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight]
  rw [comp_apply]; rw [Pi.smul_apply]; rw [this]
  refi

中文:
引理 IsM整数egralCurveOn.comp_mul
  条件: (hγ : IsM整数egralCurveOn γ v s) (a : 实数)
  证明: by
  intro t ht
  have : (1 : Real ->L[Real] Real).smulRight (a • v (γ (t * a))) =
      (1 : Real ->L[Real] Real).smulRight (v (γ (t * a))) ∘SL (1 : Real ->L[Real] Real).smulRight a := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight]
  rw [comp_apply]; rw [Pi.smul_apply]; rw [this]
  refi

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight_comp_smulRight, HasFDerivWithinAt, HasFDerivWithinAt.mul_const, HasMFDerivWithinAt, HasMFDerivWithinAt.comp, Pi.smul_apply, comp_apply, continuousWithinAt, continuous_mul_const, hasFDerivWithinAt_id, mfld_simps, mul_const, smulRight, smulRight_comp_smulRight, smul_apply, subset_rfl
-/
lemma IsMIntegralCurveOn.comp_mul (hγ : IsMIntegralCurveOn γ v s) (a : Real) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a in s } := by
  intro t ht
  have : (1 : Real ->L[Real] Real).smulRight (a • v (γ (t * a))) =
      (1 : Real ->L[Real] Real).smulRight (v (γ (t * a))) ∘SL (1 : Real ->L[Real] Real).smulRight a := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight]
  rw [comp_apply]; rw [Pi.smul_apply]; rw [this]
  refine HasMFDerivWithinAt.comp t (hγ (t * a) ht)
    ⟨(continuous_mul_const _).continuousWithinAt, ?_⟩ subset_rfl
  simp only [mfld_simps]
  exact HasFDerivWithinAt.mul_const' (hasFDerivWithinAt_id _ _) _

/--
lemma `isMIntegralCurveOn_comp_mul_ne_zero` / 引理 `isMIntegralCurveOn_comp_mul_ne_zero`

English:
lemma isMIntegralCurveOn_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_ofPred_eq, mul_assoc, inv_mul_eq_div, div_

中文:
引理 isM整数egralCurveOn_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_ofPred_eq, mul_assoc, inv_mul_eq_div, div_

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_mul, convert, div_self, inv_mul_eq_div, mem_ofPred_eq, mul_assoc, mul_one, ofPred_mem_eq, one_smul, smul_smul
-/
lemma isMIntegralCurveOn_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsMIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a in s } ↔ IsMIntegralCurveOn γ v s := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul a⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_ofPred_eq, mul_assoc, inv_mul_eq_div, div_self ha, mul_one, ofPred_mem_eq]

/--
lemma `IsMIntegralCurveAt.comp_mul_ne_zero` / 引理 `IsMIntegralCurveAt.comp_mul_ne_zero`

English:
lemma IsMIntegralCurveAt.comp_mul_ne_zero
  given: (hγ : IsMIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0)
  proof: by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; rw [sub_mu

中文:
引理 IsM整数egralCurveAt.comp_mul_ne_zero
  条件: (hγ : IsM整数egralCurveAt γ v t₀) {a : 实数} (ha : a != 0)
  证明: by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; rw [sub_mu

Depends on / 依赖: Metric, Metric.mem_ball, Real.dist_eq, abs_mul, abs_pos, abs_pos.mpr, comp_mul, convert, dist_eq, h.comp_mul, isMIntegralCurveAt_iff, mem_ball, mem_ofPred_eq, sub_mul
-/
lemma IsMIntegralCurveAt.comp_mul_ne_zero (hγ : IsMIntegralCurveAt γ v t₀) {a : Real} (ha : a != 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  rw [isMIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
  convert! h.comp_mul a
  ext t
  rw [mem_ofPred_eq]; rw [Metric.mem_ball]; rw [Metric.mem_ball]; rw [Real.dist_eq]; rw [Real.dist_eq]; rw [lt_div_iff₀ (abs_pos.mpr ha)]; rw [← abs_mul]; rw [sub_mul]; rw [div_mul_cancel₀ _ ha]

/--
lemma `isMIntegralCurveAt_comp_mul_ne_zero` / 引理 `isMIntegralCurveAt_comp_mul_ne_zero`

English:
lemma isMIntegralCurveAt_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, 

中文:
引理 isM整数egralCurveAt_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, 

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_mul_ne_zero, convert, div_inv_eq_mul, div_self, inv_mul_eq_div, inv_ne_zero, mul_assoc, mul_one, one_smul, smul_smul
-/
lemma isMIntegralCurveAt_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsMIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) ↔ IsMIntegralCurveAt γ v t₀ := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul_ne_zero ha⟩
  convert! hγ.comp_mul_ne_zero (inv_ne_zero ha)
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel₀ _ ha]

/--
lemma `IsMIntegralCurve.comp_mul` / 引理 `IsMIntegralCurve.comp_mul`

English:
lemma IsMIntegralCurve.comp_mul
  given: (hγ : IsMIntegralCurve γ v) (a : Real)
  proof: by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

中文:
引理 IsM整数egralCurve.comp_mul
  条件: (hγ : IsM整数egralCurve γ v) (a : 实数)
  证明: by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

Depends on / 依赖: comp_mul, isMIntegralCurve_iff_isMIntegralCurveOn
-/
lemma IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : Real) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

/--
lemma `isMIntegralCurve_comp_mul_ne_zero` / 引理 `isMIntegralCurve_comp_mul_ne_zero`

English:
lemma isMIntegralCurve_comp_mul_ne_zero
  given: {a : Real} (ha : a != 0)
  proof: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

中文:
引理 isM整数egralCurve_comp_mul_ne_zero
  条件: {a : 实数} (ha : a != 0)
  证明: by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_mul, convert, div_self, inv_mul_eq_div, mul_assoc, mul_one, one_smul, smul_smul
-/
lemma isMIntegralCurve_comp_mul_ne_zero {a : Real} (ha : a != 0) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) ↔ IsMIntegralCurve γ v := by
  refine ⟨fun hγ => ?_, fun hγ => hγ.comp_mul _⟩
  convert! hγ.comp_mul a⁻¹
  · ext t
    simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

open ContinuousLinearMap in
/--
lemma `isMIntegralCurve_const` / 引理 `isMIntegralCurve_const`

English:
lemma isMIntegralCurve_const
  given: {x : M} (h : v x = 0)
  statement: IsMIntegralCurve (fun _ => x) v
  proof: by
  intro t
  rw [h]; rw [smulRight_one_eq_toSpanSingleton]; rw [toSpanSingleton_zero]
  exact hasMFDerivAt_const ..

中文:
引理 isM整数egralCurve_const
  条件: {x : M} (h : v x = 0)
  结论: IsM整数egralCurve (fun _ => x) v
  证明: by
  intro t
  rw [h]; rw [smulRight_one_eq_toSpanSingleton]; rw [toSpanSingleton_zero]
  exact hasMFDerivAt_const ..

Depends on / 依赖: hasMFDerivAt_const, smulRight_one_eq_toSpanSingleton, toSpanSingleton_zero
-/
lemma isMIntegralCurve_const {x : M} (h : v x = 0) : IsMIntegralCurve (fun _ => x) v := by
  intro t
  rw [h]; rw [smulRight_one_eq_toSpanSingleton]; rw [toSpanSingleton_zero]
  exact hasMFDerivAt_const ..

end Scaling
