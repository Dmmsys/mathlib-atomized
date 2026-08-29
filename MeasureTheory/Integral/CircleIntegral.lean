/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `CircleIntegrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circleMap c R` is integrable on `[0, 2π]`;

* `circleIntegral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchyPowerSeries f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `hasFPowerSeriesOn_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchyPowerSeries f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `Metric.ball c R`;

* `circleIntegral.integral_sub_zpow_of_undef`, `circleIntegral.integral_sub_zpow_of_ne`, and
  `circleIntegral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circleIntegral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circleIntegral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circleIntegral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see https://github.com/leanprover-community/mathlib4/pull/10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open scoped Real NNReal Interval Pointwise Topology

open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics

/-!
### Facts about `circleMap`
-/

/-- The range of `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
/--
theorem `range_circleMap` / 定理 `range_circleMap`

English:
theorem range_circleMap
  given: (c : Complex) (R : Real)
  statement: range (circleMap c R) = sphere c |R|
  proof: calc
    range (circleMap c R) = c +ᵥ R • range fun θ : Real => exp (θ * I) := by
      simp +unfoldPartialApp only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I]; rw [smul_sphere R 0 zero_le_one]
      simp

中文:
定理 range_circleMap
  条件: (c : 复形) (R : 实数)
  结论: range (circleMap c R) = sphere c |R|
  证明: calc
    range (circleMap c R) = c +ᵥ R • range fun θ : Real => exp (θ * I) := by
      simp +unfoldPartialApp only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I]; rw [smul_sphere R 0 zero_le_one]
      simp

Depends on / 依赖: circleMap, comp_def, image_smul, image_vadd, range_comp, range_exp_mul_I, real_smul, smul_sphere, sphere, unfoldPartialApp, vadd_eq_add, zero_le_one
-/
theorem range_circleMap (c : Complex) (R : Real) : range (circleMap c R) = sphere c |R| :=
  calc
    range (circleMap c R) = c +ᵥ R • range fun θ : Real => exp (θ * I) := by
      simp +unfoldPartialApp only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I]; rw [smul_sphere R 0 zero_le_one]
      simp

/-- The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
/--
theorem `image_circleMap_Ioc` / 定理 `image_circleMap_Ioc`

English:
theorem image_circleMap_Ioc
  given: (c : Complex) (R : Real)
  statement: circleMap c R '' Ioc 0 (2 * π) = sphere c |R|
  proof: by
  rw [← range_circleMap]; rw [← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0]; rw [zero_add]

中文:
定理 image_circleMap_Ioc
  条件: (c : 复形) (R : 实数)
  结论: circleMap c R '' 左开右闭区间 0 (2 * π) = sphere c |R|
  证明: by
  rw [← range_circleMap]; rw [← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0]; rw [zero_add]

Depends on / 依赖: Real.two_pi_pos, image_Ioc, periodic_circleMap, range_circleMap, two_pi_pos, zero_add
-/
theorem image_circleMap_Ioc (c : Complex) (R : Real) : circleMap c R '' Ioc 0 (2 * π) = sphere c |R| := by
  rw [← range_circleMap]; rw [← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0]; rw [zero_add]

/--
theorem `hasDerivAt_circleMap` / 定理 `hasDerivAt_circleMap`

English:
theorem hasDerivAt_circleMap
  given: (c : Complex) (R : Real) (θ : Real)
  proof: by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : Complex)).const_add c

中文:
定理 hasDerivAt_circleMap
  条件: (c : 复形) (R : 实数) (θ : 实数)
  证明: by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : Complex)).const_add c

Depends on / 依赖: cexp.const_mul, circleMap, const_add, const_mul, hasDerivAt, mul_assoc, mul_const, ofRealCLM, ofRealCLM.hasDerivAt, ofRealCLM_apply, ofReal_one, one_mul, zero_add
-/
theorem hasDerivAt_circleMap (c : Complex) (R : Real) (θ : Real) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : Complex)).const_add c

/--
theorem `differentiable_circleMap` / 定理 `differentiable_circleMap`

English:
theorem differentiable_circleMap
  given: (c : Complex) (R : Real)
  statement: Differentiable Real (circleMap c R)
  proof: fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt

中文:
定理 differentiable_circleMap
  条件: (c : 复形) (R : 实数)
  结论: 可微 实数 (circleMap c R)
  证明: fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt
-/
theorem differentiable_circleMap (c : Complex) (R : Real) : Differentiable Real (circleMap c R) := fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt

/--
theorem `analyticOnNhd_circleMap` / 定理 `analyticOnNhd_circleMap`

English:
theorem analyticOnNhd_circleMap
  given: (c : Complex) (R : Real)
  proof: by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

中文:
定理 analyticOnNhd_circleMap
  条件: (c : 复形) (R : 实数)
  证明: by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

Depends on / 依赖: Function, Function.comp_def, analyticAt, analyticAt_cexp, analyticAt_cexp.restrictScalars.comp, analyticAt_const, analyticAt_const.add, analyticAt_const.mul, comp_def, fun_prop, ofRealCLM, ofRealCLM.analyticAt, restrictScalars
-/
theorem analyticOnNhd_circleMap (c : Complex) (R : Real) :
    AnalyticOnNhd Real (circleMap c R) Set.univ := by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

/--
theorem `contDiff_circleMap` / 定理 `contDiff_circleMap`

English:
theorem contDiff_circleMap
  given: (c : Complex) (R : Real) {n : WithTop Nat∞}
  proof: (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]

中文:
定理 contDiff_circleMap
  条件: (c : 复形) (R : 实数) {n : WithTop 自然数∞}
  证明: (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]

Depends on / 依赖: analyticOnNhd_circleMap, contDiff
-/
theorem contDiff_circleMap (c : Complex) (R : Real) {n : WithTop Nat∞} :
    ContDiff Real n (circleMap c R) :=
  (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]
/--
theorem `continuous_circleMap` / 定理 `continuous_circleMap`

English:
theorem continuous_circleMap
  given: (c : Complex) (R : Real)
  statement: Continuous (circleMap c R)
  proof: (differentiable_circleMap c R).continuous

@[fun_prop]

中文:
定理 continuous_circleMap
  条件: (c : 复形) (R : 实数)
  结论: 连续 (circleMap c R)
  证明: (differentiable_circleMap c R).continuous

@[fun_prop]

Depends on / 依赖: continuous, differentiable_circleMap
-/
theorem continuous_circleMap (c : Complex) (R : Real) : Continuous (circleMap c R) :=
  (differentiable_circleMap c R).continuous

@[fun_prop]
/--
theorem `measurable_circleMap` / 定理 `measurable_circleMap`

English:
theorem measurable_circleMap
  given: (c : Complex) (R : Real)
  statement: Measurable (circleMap c R)
  proof: (continuous_circleMap c R).measurable

@[simp]

中文:
定理 measurable_circleMap
  条件: (c : 复形) (R : 实数)
  结论: 可测 (circleMap c R)
  证明: (continuous_circleMap c R).measurable

@[simp]

Depends on / 依赖: continuous_circleMap, measurable
-/
theorem measurable_circleMap (c : Complex) (R : Real) : Measurable (circleMap c R) :=
  (continuous_circleMap c R).measurable

@[simp]
/--
theorem `deriv_circleMap` / 定理 `deriv_circleMap`

English:
theorem deriv_circleMap
  given: (c : Complex) (R : Real) (θ : Real)
  statement: deriv (circleMap c R) θ = circleMap 0 R θ * I
  proof: (hasDerivAt_circleMap _ _ _).deriv

中文:
定理 deriv_circleMap
  条件: (c : 复形) (R : 实数) (θ : 实数)
  结论: deriv (circleMap c R) θ = circleMap 0 R θ * I
  证明: (hasDerivAt_circleMap _ _ _).deriv

Depends on / 依赖: hasDerivAt_circleMap
-/
theorem deriv_circleMap (c : Complex) (R : Real) (θ : Real) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (hasDerivAt_circleMap _ _ _).deriv

/--
theorem `deriv_circleMap_eq_zero_iff` / 定理 `deriv_circleMap_eq_zero_iff`

English:
theorem deriv_circleMap_eq_zero_iff
  given: {c : Complex} {R : Real} {θ : Real}
  proof: by simp [I_ne_zero]

中文:
定理 deriv_circleMap_eq_zero_iff
  条件: {c : 复形} {R : 实数} {θ : 实数}
  证明: by simp [I_ne_zero]

Depends on / 依赖: I_ne_zero, IsAtomic
-/
theorem deriv_circleMap_eq_zero_iff {c : Complex} {R : Real} {θ : Real} :
    deriv (circleMap c R) θ = 0 ↔ R = 0 := by simp [I_ne_zero]

/--
theorem `deriv_circleMap_ne_zero` / 定理 `deriv_circleMap_ne_zero`

English:
theorem deriv_circleMap_ne_zero
  given: {c : Complex} {R : Real} {θ : Real} (hR : R != 0)
  proof: mt deriv_circleMap_eq_zero_iff.1 hR

中文:
定理 deriv_circleMap_ne_zero
  条件: {c : 复形} {R : 实数} {θ : 实数} (hR : R != 0)
  证明: mt deriv_circleMap_eq_zero_iff.1 hR

Depends on / 依赖: IsCoatomic, deriv_circleMap_eq_zero_iff
-/
theorem deriv_circleMap_ne_zero {c : Complex} {R : Real} {θ : Real} (hR : R != 0) :
    deriv (circleMap c R) θ != 0 :=
  mt deriv_circleMap_eq_zero_iff.1 hR

/--
theorem `lipschitzWith_circleMap` / 定理 `lipschitzWith_circleMap`

English:
theorem lipschitzWith_circleMap
  given: (c : Complex) (R : Real)
  statement: LipschitzWith (Real.nnabs R) (circleMap c R)
  proof: lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
NNReal.coe_le_coe.1 by simp

中文:
定理 lipschitzWith_circleMap
  条件: (c : 复形) (R : 实数)
  结论: LipschitzWith (实数.nnabs R) (circleMap c R)
  证明: lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
NNReal.coe_le_coe.1 by simp

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, differentiable_circleMap, lipschitzWith_of_nnnorm_deriv_le
-/
theorem lipschitzWith_circleMap (c : Complex) (R : Real) : LipschitzWith (Real.nnabs R) (circleMap c R) :=
  lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
NNReal.coe_le_coe.1 by simp

/--
theorem `continuous_circleMap_inv` / 定理 `continuous_circleMap_inv`

English:
theorem continuous_circleMap_inv
  given: {R : Real} {z w : Complex} (hw : w in ball z R)
  proof: by
  have : forall θ, circleMap z R θ - w != 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by fun_prop) this

中文:
定理 continuous_circleMap_inv
  条件: {R : 实数} {z w : 复形} (hw : w in ball z R)
  证明: by
  have : forall θ, circleMap z R θ - w != 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by fun_prop) this

Depends on / 依赖: circleMap, circleMap_ne_mem_ball, simp_rw, sub_ne_zero
-/
theorem continuous_circleMap_inv {R : Real} {z w : Complex} (hw : w in ball z R) :
    Continuous fun θ => (circleMap z R θ - w)⁻¹ := by
  have : forall θ, circleMap z R θ - w != 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by fun_prop) this

/--
theorem `circleMap_preimage_codiscrete` / 定理 `circleMap_preimage_codiscrete`

English:
theorem circleMap_preimage_codiscrete
  given: {c : Complex} {R : Real} (hR : R != 0)
  proof: by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]

中文:
定理 circleMap_preimage_codiscrete
  条件: {c : 复形} {R : 实数} (hR : R != 0)
  证明: by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]

Depends on / 依赖: Set.image_univ, analyticOnNhd_circleMap, eq_of_nhds, eventuallyConst_iff_exists_eventuallyEq, ha.deriv.eq_of_nhds, image_univ, preimage_mem_codiscreteWithin, range_circleMap
-/
theorem circleMap_preimage_codiscrete {c : Complex} {R : Real} (hR : R != 0) :
    map (circleMap c R) (codiscrete Real) <= codiscreteWithin (sphere c |R|) := by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    have := ha.deriv.eq_of_nhds
    simp [hR] at this
  · rwa [Set.image_univ, range_circleMap]

/--
theorem `circleMap_neg_radius` / 定理 `circleMap_neg_radius`

English:
theorem circleMap_neg_radius
  given: {r x : Real} {c : Complex}
  proof: by
  simp [circleMap, add_mul, Complex.exp_add]

中文:
定理 circleMap_neg_radius
  条件: {r x : 实数} {c : 复形}
  证明: by
  simp [circleMap, add_mul, Complex.exp_add]

Depends on / 依赖: Complex.exp_add, IsAtomistic, add_mul, circleMap, exp_add
-/
theorem circleMap_neg_radius {r x : Real} {c : Complex} :
    circleMap c (-r) x = circleMap c r (x + π) := by
  simp [circleMap, add_mul, Complex.exp_add]

/-!
### Integrability of a function on a circle
-/

/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circleMap c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circleIntegral` is
`(deriv (circleMap c R) θ) • f (circleMap c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circleMap c R` whenever `R ≠ 0`. -/
@[fun_prop]
/--
Definition of `CircleIntegrable` / `CircleIntegrable` 的定义

English:
definition CircleIntegrable
  signature: (f : Complex -> E) (c : Complex) (R : Real)
  body: IntervalIntegrable (fun θ : Real => f (circleMap c R θ)) volume 0 (2 * π)

中文:
定义 Circle整数egrable
  签名: (f : 复形 -> E) (c : 复形) (R : 实数)
  定义体: IntervalIntegrable (fun θ : Real => f (circleMap c R θ)) volume 0 (2 * π)

Depends on / 依赖: IntervalIntegrable, IsCoatomistic, circleMap, volume
-/
def CircleIntegrable (f : Complex -> E) (c : Complex) (R : Real) : Prop :=
  IntervalIntegrable (fun θ : Real => f (circleMap c R θ)) volume 0 (2 * π)

/--
theorem `circleIntegrable_def` / 定理 `circleIntegrable_def`

English:
theorem circleIntegrable_def
  given: (f : Complex -> E) (c : Complex) (R : Real)
  statement: CircleIntegrable f c R ↔
  proof: Iff.rfl

@[simp, fun_prop]

中文:
定理 circle整数egrable_def
  条件: (f : 复形 -> E) (c : 复形) (R : 实数)
  结论: Circle整数egrable f c R ↔
  证明: Iff.rfl

@[simp, fun_prop]

Depends on / 依赖: Iff.rfl
-/
theorem circleIntegrable_def (f : Complex -> E) (c : Complex) (R : Real) : CircleIntegrable f c R ↔
    IntervalIntegrable (fun θ : Real => f (circleMap c R θ)) volume 0 (2 * π) := Iff.rfl

@[simp, fun_prop]
/--
theorem `circleIntegrable_const` / 定理 `circleIntegrable_const`

English:
theorem circleIntegrable_const
  given: (a : E) (c : Complex) (R : Real)
  statement: CircleIntegrable (fun _ => a) c R
  proof: intervalIntegrable_const

@[fun_prop]

中文:
定理 circle整数egrable_const
  条件: (a : E) (c : 复形) (R : 实数)
  结论: Circle整数egrable (fun _ => a) c R
  证明: intervalIntegrable_const

@[fun_prop]

Depends on / 依赖: intervalIntegrable_const
-/
theorem circleIntegrable_const (a : E) (c : Complex) (R : Real) : CircleIntegrable (fun _ => a) c R :=
  intervalIntegrable_const

@[fun_prop]
/--
theorem `circleIntegrable_id` / 定理 `circleIntegrable_id`

English:
theorem circleIntegrable_id
  given: (c : Complex) (R : Real)
  statement: CircleIntegrable (fun z => z) c R
  proof: (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

中文:
定理 circle整数egrable_id
  条件: (c : 复形) (R : 实数)
  结论: Circle整数egrable (fun z => z) c R
  证明: (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

Depends on / 依赖: continuous_circleMap, intervalIntegrable
-/
theorem circleIntegrable_id (c : Complex) (R : Real) : CircleIntegrable (fun z => z) c R :=
  (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

namespace CircleIntegrable

variable {f g : Complex -> E} {c : Complex} {R : Real} {A : Type*} [NormedRing A] {a : A}

/--
Analogue of `IntervalIntegrable.abs`: If a real-valued function `f` is circle integrable, then so is
`|f|`.
-/
@[to_fun (attr := fun_prop)]
/--
theorem `abs` / 定理 `abs`

English:
theorem abs
  given: {f : Complex -> Real} (hf : CircleIntegrable f c R)
  proof: IntervalIntegrable.abs hf

@[to_fun (attr := fun_prop)]

中文:
定理 abs
  条件: {f : 复形 -> 实数} (hf : Circle整数egrable f c R)
  证明: IntervalIntegrable.abs hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.abs
-/
theorem abs {f : Complex -> Real} (hf : CircleIntegrable f c R) :
    CircleIntegrable |f| c R := IntervalIntegrable.abs hf

@[to_fun (attr := fun_prop)]
/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
  proof: IntervalIntegrable.add hf hg

@[to_fun (attr := fun_prop)]

中文:
定理 add
  条件: (hf : Circle整数egrable f c R) (hg : Circle整数egrable g c R)
  证明: IntervalIntegrable.add hf hg

@[to_fun (attr := fun_prop)]

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.add
-/
theorem add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f + g) c R :=
  IntervalIntegrable.add hf hg

@[to_fun (attr := fun_prop)]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
  proof: IntervalIntegrable.sub hf hg

中文:
定理 sub
  条件: (hf : Circle整数egrable f c R) (hg : Circle整数egrable g c R)
  证明: IntervalIntegrable.sub hf hg

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.sub
-/
theorem sub (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f - g) c R :=
  IntervalIntegrable.sub hf hg

/-- Sums of circle integrable functions are circle integrable. -/
@[to_fun (attr := fun_prop)]
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: {ι : Type*} (s : Finset ι) {f : ι -> Complex -> E}
  proof: by
  rw [CircleIntegrable]; rw [(by aesop : (fun θ => (∑ i in s]; rw [f i) (circleMap c R θ))
    = ∑ i in s]; rw [fun θ => f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h

中文:
定理 求和
  结论: {ι : 类型} (s : 有限集 ι) {f : ι -> 复形 -> E}
  证明: by
  rw [CircleIntegrable]; rw [(by aesop : (fun θ => (∑ i in s]; rw [f i) (circleMap c R θ))
    = ∑ i in s]; rw [fun θ => f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h
-/
protected theorem sum {ι : Type*} (s : Finset ι) {f : ι -> Complex -> E}
    (h : forall i in s, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ i in s, f i) c R := by
  rw [CircleIntegrable]; rw [(by aesop : (fun θ => (∑ i in s]; rw [f i) (circleMap c R θ))
    = ∑ i in s]; rw [fun θ => f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h

/-- `finsum`s of circle integrable functions are circle integrable. -/
@[fun_prop]
/--
theorem `finsum` / 定理 `finsum`

English:
theorem finsum
  given: {ι : Type*} {f : ι -> Complex -> E} (h : forall i, CircleIntegrable (f i) c R)
  proof: by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ => h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

@[to_fun (attr := fun_prop)]
nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg

中文:
定理 finsum
  条件: {ι : 类型} {f : ι -> 复形 -> E} (h : 对任意 i, Circle整数egrable (f i) c R)
  证明: by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ => h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

@[to_fun (attr := fun_prop)]
nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg
-/
protected theorem finsum {ι : Type*} {f : ι -> Complex -> E} (h : forall i, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ᶠ i, f i) c R := by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ => h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

@[to_fun (attr := fun_prop)]
nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg

/-- If `f` is circle integrable, then so are its scalar multiples. -/
@[to_fun (attr := fun_prop) const_fun_smul]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: {f : Complex -> A} (h : CircleIntegrable f c R)
  statement: CircleIntegrable (a • f) c R
  proof: IntervalIntegrable.const_mul h _

中文:
定理 const_smul
  条件: {f : 复形 -> A} (h : Circle整数egrable f c R)
  结论: Circle整数egrable (a • f) c R
  证明: IntervalIntegrable.const_mul h _

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.const_mul, const_mul
-/
theorem const_smul {f : Complex -> A} (h : CircleIntegrable f c R) : CircleIntegrable (a • f) c R :=
  IntervalIntegrable.const_mul h _

variable
  {𝕜 F : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g • f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/--
theorem `continuousOn_smul` / 定理 `continuousOn_smul`

English:
theorem continuousOn_smul
  statement: {f : Complex -> F} {g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
  proof: IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

中文:
定理 continuousOn_smul
  结论: {f : 复形 -> F} {g : 复形 -> 𝕜} (hf : Circle整数egrable f c R)
  证明: IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.continuousOn_smul, circleMap_mem_sphere, continuousOn_smul, fun_prop, hg.comp
-/
theorem continuousOn_smul {f : Complex -> F} {g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g • f) c R :=
  IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f • g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/--
theorem `smul_continuousOn` / 定理 `smul_continuousOn`

English:
theorem smul_continuousOn
  statement: {f : Complex -> 𝕜} {g : Complex -> F} (hf : CircleIntegrable f c R)
  proof: IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

中文:
定理 smul_continuousOn
  结论: {f : 复形 -> 𝕜} {g : 复形 -> F} (hf : Circle整数egrable f c R)
  证明: IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.smul_continuousOn, circleMap_mem_sphere, fun_prop, hg.comp, smul_continuousOn
-/
theorem smul_continuousOn {f : Complex -> 𝕜} {g : Complex -> F} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f • g) c R :=
  IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g * f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/--
theorem `continuousOn_mul` / 定理 `continuousOn_mul`

English:
theorem continuousOn_mul
  statement: {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
  proof: IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

中文:
定理 continuousOn_mul
  结论: {f g : 复形 -> 𝕜} (hf : Circle整数egrable f c R)
  证明: IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.continuousOn_mul, circleMap_mem_sphere, continuousOn_mul, fun_prop, hg.comp
-/
theorem continuousOn_mul {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g * f) c R :=
  IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f * g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
/--
theorem `mul_continuousOn` / 定理 `mul_continuousOn`

English:
theorem mul_continuousOn
  statement: {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
  proof: IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

@[deprecated (since := "2026-07-01")] alias smul_of_continuousOn := continuousOn_smul
@[deprecated (since := "2026-07-01")] alias mul_of_continuousOn := continuousOn_mul
@[deprecated (since := "2026-07-01")] alias fun_smul_of_continuousOn := fun_continuousOn_smul
@[deprecated (since := "2026-07-01")] alias fun_mul_of_continuousOn := fun_continuousOn_mul

中文:
定理 mul_continuousOn
  结论: {f g : 复形 -> 𝕜} (hf : Circle整数egrable f c R)
  证明: IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

@[deprecated (since := "2026-07-01")] alias smul_of_continuousOn := continuousOn_smul
@[deprecated (since := "2026-07-01")] alias mul_of_continuousOn := continuousOn_mul
@[deprecated (since := "2026-07-01")] alias fun_smul_of_continuousOn := fun_continuousOn_smul
@[deprecated (since := "2026-07-01")] alias fun_mul_of_continuousOn := fun_continuousOn_mul

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.mul_continuousOn, circleMap_mem_sphere, fun_prop, hg.comp, mul_continuousOn
-/
theorem mul_continuousOn {f g : Complex -> 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f * g) c R :=
  IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx => circleMap_mem_sphere' c R x))

@[deprecated (since := "2026-07-01")] alias smul_of_continuousOn := continuousOn_smul
@[deprecated (since := "2026-07-01")] alias mul_of_continuousOn := continuousOn_mul
@[deprecated (since := "2026-07-01")] alias fun_smul_of_continuousOn := fun_continuousOn_smul
@[deprecated (since := "2026-07-01")] alias fun_mul_of_continuousOn := fun_continuousOn_mul

/--
theorem `out` / 定理 `out`

English:
theorem out
  given: [NormedSpace Complex E] (hf : CircleIntegrable f c R)
  proof: by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]

中文:
定理 out
  条件: [赋范空间 复形 E] (hf : Circle整数egrable f c R)
  证明: by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]

Depends on / 依赖: CircleIntegrable, aestronglyMeasurable, aestronglyMeasurable.mul_const, const_mul, continuous_circleMap, deriv_circleMap, hf.aestronglyMeasurable, hf.norm.const_mul, intervalIntegrable_iff, mul_const, norm_smul
-/
theorem out [NormedSpace Complex E] (hf : CircleIntegrable f c R) :
    IntervalIntegrable (fun θ : Real => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0
      (2 * π) := by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]

end CircleIntegrable

@[simp]
/--
theorem `circleIntegrable_zero_radius` / 定理 `circleIntegrable_zero_radius`

English:
theorem circleIntegrable_zero_radius
  given: {f : Complex -> E} {c : Complex}
  statement: CircleIntegrable f c 0
  proof: by
  simp [CircleIntegrable]

中文:
定理 circle整数egrable_zero_radius
  条件: {f : 复形 -> E} {c : 复形}
  结论: Circle整数egrable f c 0
  证明: by
  simp [CircleIntegrable]

Depends on / 依赖: CircleIntegrable
-/
theorem circleIntegrable_zero_radius {f : Complex -> E} {c : Complex} : CircleIntegrable f c 0 := by
  simp [CircleIntegrable]

/--
theorem `circleIntegrable_congr` / 定理 `circleIntegrable_congr`

English:
theorem circleIntegrable_congr
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
  proof: intervalIntegrable_congr fun x _ => hf (circleMap_mem_sphere' c R x)

@[deprecated (since := "2026-04-26")] alias crcleIntegrable_congr := circleIntegrable_congr

中文:
定理 circle整数egrable_congr
  结论: {c : 复形} {R : 实数} {f₁ f₂ : 复形 -> E}
  证明: intervalIntegrable_congr fun x _ => hf (circleMap_mem_sphere' c R x)

@[deprecated (since := "2026-04-26")] alias crcleIntegrable_congr := circleIntegrable_congr

Depends on / 依赖: circleMap_mem_sphere, intervalIntegrable_congr
-/
theorem circleIntegrable_congr {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
    (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  intervalIntegrable_congr fun x _ => hf (circleMap_mem_sphere' c R x)

@[deprecated (since := "2026-04-26")] alias crcleIntegrable_congr := circleIntegrable_congr

/--
theorem `circleIntegrable_neg_radius` / 定理 `circleIntegrable_neg_radius`

English:
theorem circleIntegrable_neg_radius
  given: {c : Complex} {R : Real} {f : Complex -> E}
  proof: by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ => f (circleMap c (-R) θ))
    (g := fun θ => (f ∘ (circleMap c R)) (θ + π)) (fun _ _ => by simp [circleMap_neg_radius]),
    IntervalIntegrable.comp_add_right_iff (c := π), add_comm (2 * π) π]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₂ := 0)

中文:
定理 circle整数egrable_neg_radius
  条件: {c : 复形} {R : 实数} {f : 复形 -> E}
  证明: by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ => f (circleMap c (-R) θ))
    (g := fun θ => (f ∘ (circleMap c R)) (θ + π)) (fun _ _ => by simp [circleMap_neg_radius]),
    IntervalIntegrable.comp_add_right_iff (c := π), add_comm (2 * π) π]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₂ := 0)
-/
@[simp] theorem circleIntegrable_neg_radius {c : Complex} {R : Real} {f : Complex -> E} :
    CircleIntegrable f c (-R) ↔ CircleIntegrable f c R := by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ => f (circleMap c (-R) θ))
    (g := fun θ => (f ∘ (circleMap c R)) (θ + π)) (fun _ _ => by simp [circleMap_neg_radius]),
    IntervalIntegrable.comp_add_right_iff (c := π), add_comm (2 * π) π]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₂ := 0)

/--
theorem `CircleIntegrable.congr_codiscreteWithin` / 定理 `CircleIntegrable.congr_codiscreteWithin`

English:
theorem CircleIntegrable.congr_codiscreteWithin
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
  proof: by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

中文:
定理 Circle整数egrable.congr_codiscreteWithin
  结论: {c : 复形} {R : 实数} {f₁ f₂ : 复形 -> E}
  证明: by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

Depends on / 依赖: Set.subset_univ, circleMap, circleMap_preimage_codiscrete, codiscreteWithin_mono, eventuallyEq_iff_exists_mem, intervalIntegrable_congr_codiscreteWithin, subset_univ
-/
theorem CircleIntegrable.congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hf₁ : CircleIntegrable f₁ c R) :
    CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

/--
theorem `circleIntegrable_congr_codiscreteWithin` / 定理 `circleIntegrable_congr_codiscreteWithin`

English:
theorem circleIntegrable_congr_codiscreteWithin
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
  proof: ⟨(CircleIntegrable.congr_codiscreteWithin hf ·),
    (CircleIntegrable.congr_codiscreteWithin hf.symm ·)⟩

中文:
定理 circle整数egrable_congr_codiscreteWithin
  结论: {c : 复形} {R : 实数} {f₁ f₂ : 复形 -> E}
  证明: ⟨(CircleIntegrable.congr_codiscreteWithin hf ·),
    (CircleIntegrable.congr_codiscreteWithin hf.symm ·)⟩

Depends on / 依赖: CircleIntegrable, CircleIntegrable.congr_codiscreteWithin, congr_codiscreteWithin, hf.symm
-/
theorem circleIntegrable_congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  ⟨(CircleIntegrable.congr_codiscreteWithin hf ·),
    (CircleIntegrable.congr_codiscreteWithin hf.symm ·)⟩

/--
theorem `circleIntegrable_iff` / 定理 `circleIntegrable_iff`

English:
theorem circleIntegrable_iff
  given: [NormedSpace Complex E] {f : Complex -> E} {c : Complex} (R : Real)
  proof: by
  by_cases h₀ : R = 0
  · simp +unfoldPartialApp [h₀, const]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H : forall {θ}, circleMap 0 R θ * I != 0 := fun {θ} => by simp [h₀, I_ne_zero]
    simpa only [inv_smul_smul₀ H]
      using ((continuous_circleMap 0 R).aestronglyMeasurable.mul_const
        I).aemeasurable.fun_inv.aestronglyMeasurable.fun_smul h.aestronglyMeasurable
  · simp [norm_smul, h₀]

@[fun_prop]

中文:
定理 circle整数egrable_iff
  条件: [赋范空间 复形 E] {f : 复形 -> E} {c : 复形} (R : 实数)
  证明: by
  by_cases h₀ : R = 0
  · simp +unfoldPartialApp [h₀, const]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H : forall {θ}, circleMap 0 R θ * I != 0 := fun {θ} => by simp [h₀, I_ne_zero]
    simpa only [inv_smul_smul₀ H]
      using ((continuous_circleMap 0 R).aestronglyMeasurable.mul_const
        I).aemeasurable.fun_inv.aestronglyMeasurable.fun_smul h.aestronglyMeasurable
  · simp [norm_smul, h₀]

@[fun_prop]

Depends on / 依赖: CircleIntegrable, I_ne_zero, aemeasurable, aemeasurable.fun_inv.aestronglyMeasurable.fun_smul, aestronglyMeasurable, aestronglyMeasurable.mul_const, circleMap, const_mul, continuous_circleMap, deriv_circleMap, fun_inv, fun_smul, h.aestronglyMeasurable, h.norm.const_mul, h.out, intervalIntegrable_iff, mul_const, norm_smul, unfoldPartialApp
-/
theorem circleIntegrable_iff [NormedSpace Complex E] {f : Complex -> E} {c : Complex} (R : Real) :
    CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : Real =>
      deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) := by
  by_cases h₀ : R = 0
  · simp +unfoldPartialApp [h₀, const]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H : forall {θ}, circleMap 0 R θ * I != 0 := fun {θ} => by simp [h₀, I_ne_zero]
    simpa only [inv_smul_smul₀ H]
      using ((continuous_circleMap 0 R).aestronglyMeasurable.mul_const
        I).aemeasurable.fun_inv.aestronglyMeasurable.fun_smul h.aestronglyMeasurable
  · simp [norm_smul, h₀]

@[fun_prop]
/--
theorem `ContinuousOn.circleIntegrable'` / 定理 `ContinuousOn.circleIntegrable'`

English:
theorem ContinuousOn.circleIntegrable'
  statement: {f : Complex -> E} {c : Complex} {R : Real}
  proof: (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _

中文:
定理 ContinuousOn.circle整数egrable'
  结论: {f : 复形 -> E} {c : 复形} {R : 实数}
  证明: (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _

Depends on / 依赖: circleMap_mem_sphere, comp_continuous, continuous_circleMap, hf.comp_continuous, intervalIntegrable
-/
theorem ContinuousOn.circleIntegrable' {f : Complex -> E} {c : Complex} {R : Real}
    (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R :=
  (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _

/--
theorem `ContinuousOn.circleIntegrable` / 定理 `ContinuousOn.circleIntegrable`

English:
theorem ContinuousOn.circleIntegrable
  statement: {f : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R)
  proof: ContinuousOn.circleIntegrable' (abs_of_nonneg hR).symm ▸ hf

中文:
定理 ContinuousOn.circle整数egrable
  结论: {f : 复形 -> E} {c : 复形} {R : 实数} (hR : 0 <= R)
  证明: ContinuousOn.circleIntegrable' (abs_of_nonneg hR).symm ▸ hf

Depends on / 依赖: ContinuousOn, ContinuousOn.circleIntegrable, abs_of_nonneg, circleIntegrable
-/
theorem ContinuousOn.circleIntegrable {f : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R)
    (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R :=
ContinuousOn.circleIntegrable' (abs_of_nonneg hR).symm ▸ hf

/-- The function `fun z ↦ (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c`
and radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp]
/--
theorem `circleIntegrable_sub_zpow_iff` / 定理 `circleIntegrable_sub_zpow_iff`

English:
theorem circleIntegrable_sub_zpow_iff
  given: {c w : Complex} {R : Real} {n : Int}
  proof: by
  constructor
  · intro h; contrapose! h; rcases h with ⟨hR, hn, hw⟩
    simp only [circleIntegrable_iff R, deriv_circleMap]
    rw [← image_circleMap_Ioc] at hw; rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ in [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ
    set f : Real -> Complex := fun θ' => circleMap c R θ' - circleMap c R θ
    have : forallᶠ θ' in 𝓝[!=] θ, f θ' in ball (0 : Complex) 1 \ {0} := by
      suffices forallᶠ z in 𝓝[!=] circleMap c R θ, z - circleMap c R θ in ball (0 : Complex) 1 \ {0} from
        ((differentiable_circleMap c R θ).hasDerivAt.tendsto_nhdsNE
          (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    refine (((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).inv_rev
      (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans ?_
    refine IsBigO.of_bound |R|⁻¹ (this.mono fun θ' hθ' => ?_)
    set x := ‖f θ'‖
    suffices x⁻¹ <= x ^ n by
      simp only [smul_eq_mul, norm_mul,
        norm_inv, norm_I, mul_one]
      simpa only [norm_circleMap_zero, norm_zpow, Ne, abs_eq_zero.not.2 hR, not_false_iff,
        inv_mul_cancel_left₀] using this
    have : x in Ioo (0 : Real) 1 := by simpa [x, and_comm] using hθ'
    rw [← zpow_neg_one]
    refine (zpow_right_strictAnti₀ this.1 this.2).le_iff_ge.2 (Int.lt_add_one_iff.1 ?_); exact hn
  · rintro (rfl | H)
    exacts [circleIntegrable_zero_radius,
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
        H.symm.imp_left fun (hw : w ∉ sphere c |R|) =>
sub_ne_zero.2 ne_of_mem_of_not_mem hz hw).circleIntegrable']

@[simp]

中文:
定理 circle整数egrable_sub_zpow_iff
  条件: {c w : 复形} {R : 实数} {n : 整数}
  证明: by
  constructor
  · intro h; contrapose! h; rcases h with ⟨hR, hn, hw⟩
    simp only [circleIntegrable_iff R, deriv_circleMap]
    rw [← image_circleMap_Ioc] at hw; rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ in [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ
    set f : Real -> Complex := fun θ' => circleMap c R θ' - circleMap c R θ
    have : forallᶠ θ' in 𝓝[!=] θ, f θ' in ball (0 : Complex) 1 \ {0} := by
      suffices forallᶠ z in 𝓝[!=] circleMap c R θ, z - circleMap c R θ in ball (0 : Complex) 1 \ {0} from
        ((differentiable_circleMap c R θ).hasDerivAt.tendsto_nhdsNE
          (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    refine (((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).inv_rev
      (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans ?_
    refine IsBigO.of_bound |R|⁻¹ (this.mono fun θ' hθ' => ?_)
    set x := ‖f θ'‖
    suffices x⁻¹ <= x ^ n by
      simp only [smul_eq_mul, norm_mul,
        norm_inv, norm_I, mul_one]
      simpa only [norm_circleMap_zero, norm_zpow, Ne, abs_eq_zero.not.2 hR, not_false_iff,
        inv_mul_cancel_left₀] using this
    have : x in Ioo (0 : Real) 1 := by simpa [x, and_comm] using hθ'
    rw [← zpow_neg_one]
    refine (zpow_right_strictAnti₀ this.1 this.2).le_iff_ge.2 (Int.lt_add_one_iff.1 ?_); exact hn
  · rintro (rfl | H)
    exacts [circleIntegrable_zero_radius,
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
        H.symm.imp_left fun (hw : w ∉ sphere c |R|) =>
sub_ne_zero.2 ne_of_mem_of_not_mem hz hw).circleIntegrable']

@[simp]

Depends on / 依赖: Icc_subset_uIcc, Ioc_subset_Icc_self, Real.two_pi_pos.ne, circleIntegrable_iff, circleMap, contrapose, deriv_circleMap, image_circleMap_Ioc, not_intervalIntegrable_of_sub_inv_isBigO_punctured, replace, two_pi_pos
-/
theorem circleIntegrable_sub_zpow_iff {c w : Complex} {R : Real} {n : Int} :
    CircleIntegrable (fun z => (z - w) ^ n) c R ↔ R = 0 ∨ 0 <= n ∨ w ∉ sphere c |R| := by
  constructor
  · intro h; contrapose! h; rcases h with ⟨hR, hn, hw⟩
    simp only [circleIntegrable_iff R, deriv_circleMap]
    rw [← image_circleMap_Ioc] at hw; rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ in [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ
    set f : Real -> Complex := fun θ' => circleMap c R θ' - circleMap c R θ
    have : forallᶠ θ' in 𝓝[!=] θ, f θ' in ball (0 : Complex) 1 \ {0} := by
      suffices forallᶠ z in 𝓝[!=] circleMap c R θ, z - circleMap c R θ in ball (0 : Complex) 1 \ {0} from
        ((differentiable_circleMap c R θ).hasDerivAt.tendsto_nhdsNE
          (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    refine (((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).inv_rev
      (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans ?_
    refine IsBigO.of_bound |R|⁻¹ (this.mono fun θ' hθ' => ?_)
    set x := ‖f θ'‖
    suffices x⁻¹ <= x ^ n by
      simp only [smul_eq_mul, norm_mul,
        norm_inv, norm_I, mul_one]
      simpa only [norm_circleMap_zero, norm_zpow, Ne, abs_eq_zero.not.2 hR, not_false_iff,
        inv_mul_cancel_left₀] using this
    have : x in Ioo (0 : Real) 1 := by simpa [x, and_comm] using hθ'
    rw [← zpow_neg_one]
    refine (zpow_right_strictAnti₀ this.1 this.2).le_iff_ge.2 (Int.lt_add_one_iff.1 ?_); exact hn
  · rintro (rfl | H)
    exacts [circleIntegrable_zero_radius,
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
        H.symm.imp_left fun (hw : w ∉ sphere c |R|) =>
sub_ne_zero.2 ne_of_mem_of_not_mem hz hw).circleIntegrable']

@[simp]
/--
theorem `circleIntegrable_sub_inv_iff` / 定理 `circleIntegrable_sub_inv_iff`

English:
theorem circleIntegrable_sub_inv_iff
  given: {c w : Complex} {R : Real}
  proof: by
  simp only [← zpow_neg_one, circleIntegrable_sub_zpow_iff]; simp

中文:
定理 circle整数egrable_sub_inv_iff
  条件: {c w : 复形} {R : 实数}
  证明: by
  simp only [← zpow_neg_one, circleIntegrable_sub_zpow_iff]; simp

Depends on / 依赖: circleIntegrable_sub_zpow_iff, zpow_neg_one
-/
theorem circleIntegrable_sub_inv_iff {c w : Complex} {R : Real} :
    CircleIntegrable (fun z => (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ sphere c |R| := by
  simp only [← zpow_neg_one, circleIntegrable_sub_zpow_iff]; simp

variable [NormedSpace Complex E]

/--
Definition of `circleIntegral` / `circleIntegral` 的定义

English:
definition circleIntegral
  signature: (f : Complex -> E) (c : Complex) (R : Real)
  body: ∫ θ : Real in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

中文:
定义 circle整数egral
  签名: (f : 复形 -> E) (c : 复形) (R : 实数)
  定义体: ∫ θ : Real in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

Depends on / 依赖: circleMap
-/
def circleIntegral (f : Complex -> E) (c : Complex) (R : Real) : E :=
  ∫ θ : Real in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

/-- `∮ z in C(c, R), f z` is the circle integral $\oint_{|z-c|=R} f(z)\,dz$. -/
notation3 "∮ "(...)" in ""C("c", "R")"", "r:60:(scoped f => circleIntegral f c R) => r

/--
theorem `circleIntegral_def_Icc` / 定理 `circleIntegral_def_Icc`

English:
theorem circleIntegral_def_Icc
  given: (f : Complex -> E) (c : Complex) (R : Real)
  proof: by
  rw [circleIntegral]; rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]; rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]

中文:
定理 circle整数egral_def_Icc
  条件: (f : 复形 -> E) (c : 复形) (R : 实数)
  证明: by
  rw [circleIntegral]; rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]; rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]

Depends on / 依赖: Ioc_ae_eq_Icc, Measure, Measure.restrict_congr_set, Real.two_pi_pos.le, circleIntegral, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, restrict_congr_set, two_pi_pos
-/
theorem circleIntegral_def_Icc (f : Complex -> E) (c : Complex) (R : Real) :
    (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π),
    deriv (circleMap c R) θ • f (circleMap c R θ) := by
  rw [circleIntegral]; rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]; rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]

/--
theorem `_root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn` / 定理 `_root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn`

English:
theorem _root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
  proof: by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · refine hf.mono fun i hi => .smul ?_ (hi.comp ?_ ?_)
    · rw [funext (deriv_circleMap _ _)]
      fun_prop
    · fun_prop
    · simp [hR, MapsTo]
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    simp only [dist_smul₀, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_nonneg hR, mul_one]
    intro ε hε
    rcases exists_pos_mul_lt hε R with ⟨δ, hδ₀, hRδ⟩
    refine (h δ hδ₀).mono fun i hi x hx => ?_
    grw [← hRδ, hi (circleMap c R x) (by simp [hR])]

中文:
定理 _root_.TendstoUniformlyOn.tendsto_circle整数egral_of_continuousOn
  证明: by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · refine hf.mono fun i hi => .smul ?_ (hi.comp ?_ ?_)
    · rw [funext (deriv_circleMap _ _)]
      fun_prop
    · fun_prop
    · simp [hR, MapsTo]
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    simp only [dist_smul₀, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_nonneg hR, mul_one]
    intro ε hε
    rcases exists_pos_mul_lt hε R with ⟨δ, hδ₀, hRδ⟩
    refine (h δ hδ₀).mono fun i hi x hx => ?_
    grw [← hRδ, hi (circleMap c R x) (by simp [hR])]

Depends on / 依赖: MapsTo, Metric, Metric.tendstoUniformlyOn_iff, TendstoUniformlyOn, TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn, abs_of_nonneg, circleMap, deriv_circleMap, exists_pos_mul_lt, fun_prop, hf.mono, hi.comp, mul_one, norm_I, norm_circleMap_zero, norm_mul, tendstoUniformlyOn_iff, tendsto_intervalIntegral_of_continuousOn
-/
theorem _root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
    {ι : Type*} {f : ι -> Complex -> E} {g : Complex -> E} {c : Complex} {R : Real}
    {l : Filter ι} [l.IsCountablyGenerated] (hR : 0 <= R)
    (hf : forallᶠ i in l, ContinuousOn (f i) (sphere c R)) (h : TendstoUniformlyOn f g l (sphere c R)) :
    Tendsto (fun n => ∮ z in C(c, R), f n z) l (𝓝 (∮ z in C(c, R), g z)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · refine hf.mono fun i hi => .smul ?_ (hi.comp ?_ ?_)
    · rw [funext (deriv_circleMap _ _)]
      fun_prop
    · fun_prop
    · simp [hR, MapsTo]
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    simp only [dist_smul₀, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_nonneg hR, mul_one]
    intro ε hε
    rcases exists_pos_mul_lt hε R with ⟨δ, hδ₀, hRδ⟩
    refine (h δ hδ₀).mono fun i hi x hx => ?_
    grw [← hRδ, hi (circleMap c R x) (by simp [hR])]

namespace circleIntegral

@[simp]
/--
theorem `integral_radius_zero` / 定理 `integral_radius_zero`

English:
theorem integral_radius_zero
  given: (f : Complex -> E) (c : Complex)
  statement: (∮ z in C(c, 0), f z) = 0
  proof: by
  simp +unfoldPartialApp [circleIntegral, const]

中文:
定理 integral_radius_zero
  条件: (f : 复形 -> E) (c : 复形)
  结论: (∮ z in C(c, 0), f z) = 0
  证明: by
  simp +unfoldPartialApp [circleIntegral, const]

Depends on / 依赖: circleIntegral, unfoldPartialApp
-/
theorem integral_radius_zero (f : Complex -> E) (c : Complex) : (∮ z in C(c, 0), f z) = 0 := by
  simp +unfoldPartialApp [circleIntegral, const]

/--
theorem `integral_congr` / 定理 `integral_congr`

English:
theorem integral_congr
  given: {f g : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R) (h : EqOn f g (sphere c R))
  proof: intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]

中文:
定理 integral_congr
  条件: {f g : 复形 -> E} {c : 复形} {R : 实数} (hR : 0 <= R) (h : EqOn f g (sphere c R))
  证明: intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]

Depends on / 依赖: circleMap_mem_sphere, integral_congr, intervalIntegral, intervalIntegral.integral_congr
-/
theorem integral_congr {f g : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R) (h : EqOn f g (sphere c R)) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z :=
  intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]

/--
theorem `circleIntegral_congr_codiscreteWithin` / 定理 `circleIntegral_congr_codiscreteWithin`

English:
theorem circleIntegral_congr_codiscreteWithin
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> Complex}
  proof: by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

中文:
定理 circle整数egral_congr_codiscreteWithin
  结论: {c : 复形} {R : 实数} {f₁ f₂ : 复形 -> 复形}
  证明: by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

Depends on / 依赖: Complex.I_ne_zero, I_ne_zero, ae_restrict_le_codiscreteWithin, circleMap_eq_center_iff, circleMap_preimage_codiscrete, codiscreteWithin_mono, deriv_circleMap, integral_congr_ae_restrict, intervalIntegral, intervalIntegral.integral_congr_ae_restrict, measurableSet_uIoc, mul_eq_mul_left_iff, mul_eq_zero, or_false, or_self, smul_eq_mul
-/
theorem circleIntegral_congr_codiscreteWithin {c : Complex} {R : Real} {f₁ f₂ : Complex -> Complex}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0) :
    (∮ z in C(c, R), f₁ z) = (∮ z in C(c, R), f₂ z) := by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

/--
theorem `integral_sub_inv_smul_sub_smul` / 定理 `integral_sub_inv_smul_sub_smul`

English:
theorem integral_sub_inv_smul_sub_smul
  given: (f : Complex -> E) (c w : Complex) (R : Real)
  proof: by
  rcases eq_or_ne R 0 with (rfl | hR); · simp only [integral_radius_zero]
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circleMap c hR
  refine intervalIntegral.integral_congr_ae ((this.ae_notMem _).mono fun θ hθ _' => ?_)
  change circleMap c R θ != w at hθ
  simp only [inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]

中文:
定理 integral_sub_inv_smul_sub_smul
  条件: (f : 复形 -> E) (c w : 复形) (R : 实数)
  证明: by
  rcases eq_or_ne R 0 with (rfl | hR); · simp only [integral_radius_zero]
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circleMap c hR
  refine intervalIntegral.integral_congr_ae ((this.ae_notMem _).mono fun θ hθ _' => ?_)
  change circleMap c R θ != w at hθ
  simp only [inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]

Depends on / 依赖: Countable, ae_notMem, circleMap, countable_singleton, eq_or_ne, integral_congr_ae, integral_radius_zero, intervalIntegral, intervalIntegral.integral_congr_ae, preimage_circleMap, sub_ne_zero, this.ae_notMem
-/
theorem integral_sub_inv_smul_sub_smul (f : Complex -> E) (c w : Complex) (R : Real) :
    (∮ z in C(c, R), (z - w)⁻¹ • (z - w) • f z) = ∮ z in C(c, R), f z := by
  rcases eq_or_ne R 0 with (rfl | hR); · simp only [integral_radius_zero]
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circleMap c hR
  refine intervalIntegral.integral_congr_ae ((this.ae_notMem _).mono fun θ hθ _' => ?_)
  change circleMap c R θ != w at hθ
  simp only [inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]

/--
theorem `integral_undef` / 定理 `integral_undef`

English:
theorem integral_undef
  given: {f : Complex -> E} {c : Complex} {R : Real} (hf : ¬CircleIntegrable f c R)
  proof: intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)

中文:
定理 integral_undef
  条件: {f : 复形 -> E} {c : 复形} {R : 实数} (hf : ¬Circle整数egrable f c R)
  证明: intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)

Depends on / 依赖: circleIntegrable_iff, integral_undef, intervalIntegral, intervalIntegral.integral_undef
-/
theorem integral_undef {f : Complex -> E} {c : Complex} {R : Real} (hf : ¬CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)

/--
theorem `integral_add` / 定理 `integral_add`

English:
theorem integral_add
  statement: {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleIntegrable f c R)
  proof: by
  simp only [circleIntegral, smul_add, intervalIntegral.integral_add hf.out hg.out]

中文:
定理 integral_add
  结论: {f g : 复形 -> E} {c : 复形} {R : 实数} (hf : Circle整数egrable f c R)
  证明: by
  simp only [circleIntegral, smul_add, intervalIntegral.integral_add hf.out hg.out]

Depends on / 依赖: circleIntegral, hf.out, hg.out, integral_add, intervalIntegral, intervalIntegral.integral_add, smul_add
-/
theorem integral_add {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z + g z) = (∮ z in C(c, R), f z) + (∮ z in C(c, R), g z) := by
  simp only [circleIntegral, smul_add, intervalIntegral.integral_add hf.out hg.out]

/--
theorem `integral_sub` / 定理 `integral_sub`

English:
theorem integral_sub
  statement: {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleIntegrable f c R)
  proof: by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]

中文:
定理 integral_sub
  结论: {f g : 复形 -> E} {c : 复形} {R : 实数} (hf : Circle整数egrable f c R)
  证明: by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]

Depends on / 依赖: circleIntegral, hf.out, hg.out, integral_sub, intervalIntegral, intervalIntegral.integral_sub, smul_sub
-/
theorem integral_sub {f g : Complex -> E} {c : Complex} {R : Real} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z - g z) = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z := by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]

/--
theorem `integral_fun_sum` / 定理 `integral_fun_sum`

English:
theorem integral_fun_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E} {c : Complex} {R : Real}
  proof: by
  simp only [circleIntegral, Finset.smul_sum,
    intervalIntegral.integral_finsetSum fun i hi => (h i hi).out]

中文:
定理 integral_fun_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 复形 -> E} {c : 复形} {R : 实数}
  证明: by
  simp only [circleIntegral, Finset.smul_sum,
    intervalIntegral.integral_finsetSum fun i hi => (h i hi).out]

Depends on / 依赖: Finset, Finset.smul_sum, circleIntegral, integral_finsetSum, intervalIntegral, intervalIntegral.integral_finsetSum, smul_sum
-/
theorem integral_fun_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E} {c : Complex} {R : Real}
    (h : forall i in s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i in s, f i z) = ∑ i in s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum,
    intervalIntegral.integral_finsetSum fun i hi => (h i hi).out]

/--
theorem `norm_integral_le_of_norm_le_const'` / 定理 `norm_integral_le_of_norm_le_const'`

English:
theorem norm_integral_le_of_norm_le_const'
  statement: {f : Complex -> E} {c : Complex} {R C : Real}
  proof: calc
    ‖∮ z in C(c, R), f z‖ <= |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ <= |R| * C := by
gcongr; exact hf _ circleMap_mem_sphere' _ _ _
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl

中文:
定理 norm_integral_le_of_norm_le_const'
  结论: {f : 复形 -> E} {c : 复形} {R C : 实数}
  证明: calc
    ‖∮ z in C(c, R), f z‖ <= |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ <= |R| * C := by
gcongr; exact hf _ circleMap_mem_sphere' _ _ _
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl

Depends on / 依赖: Real.two_pi_pos, _root_, _root_.abs_of_pos, abs_of_pos, circleMap, circleMap_mem_sphere, intervalIntegral, intervalIntegral.norm_integral_le_of_norm_le_const, norm_integral_le_of_norm_le_const, norm_smul, sub_zero, two_pi_pos
-/
theorem norm_integral_le_of_norm_le_const' {f : Complex -> E} {c : Complex} {R C : Real}
    (hf : forall z in sphere c |R|, ‖f z‖ <= C) : ‖∮ z in C(c, R), f z‖ <= 2 * π * |R| * C :=
  calc
    ‖∮ z in C(c, R), f z‖ <= |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ <= |R| * C := by
gcongr; exact hf _ circleMap_mem_sphere' _ _ _
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl

/--
theorem `norm_integral_le_of_norm_le_const` / 定理 `norm_integral_le_of_norm_le_const`

English:
theorem norm_integral_le_of_norm_le_const
  statement: {f : Complex -> E} {c : Complex} {R C : Real} (hR : 0 <= R)
  proof: have : |R| = R := abs_of_nonneg hR
  calc
‖∮ z in C(c, R), f z‖ <= 2 * π * |R| * C := norm_integral_le_of_norm_le_const' by rwa [this]
    _ = 2 * π * R * C := by rw [this]

中文:
定理 norm_integral_le_of_norm_le_const
  结论: {f : 复形 -> E} {c : 复形} {R C : 实数} (hR : 0 <= R)
  证明: have : |R| = R := abs_of_nonneg hR
  calc
‖∮ z in C(c, R), f z‖ <= 2 * π * |R| * C := norm_integral_le_of_norm_le_const' by rwa [this]
    _ = 2 * π * R * C := by rw [this]

Depends on / 依赖: abs_of_nonneg, norm_integral_le_of_norm_le_const
-/
theorem norm_integral_le_of_norm_le_const {f : Complex -> E} {c : Complex} {R C : Real} (hR : 0 <= R)
    (hf : forall z in sphere c R, ‖f z‖ <= C) : ‖∮ z in C(c, R), f z‖ <= 2 * π * R * C :=
  have : |R| = R := abs_of_nonneg hR
  calc
‖∮ z in C(c, R), f z‖ <= 2 * π * |R| * C := norm_integral_le_of_norm_le_const' by rwa [this]
    _ = 2 * π * R * C := by rw [this]

/--
theorem `norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` / 定理 `norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`

English:
theorem norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
  statement: {f : Complex -> E} {c : Complex} {R C : Real}
  proof: by
  have : ‖(2 * π * I : Complex)⁻¹‖ = (2 * π)⁻¹ := by simp [Real.pi_pos.le]
  rw [norm_smul]; rw [this]; rw [← div_eq_inv_mul]; rw [div_le_iff₀ Real.two_pi_pos]; rw [mul_comm (R * C)]; rw [← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

中文:
定理 norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
  结论: {f : 复形 -> E} {c : 复形} {R C : 实数}
  证明: by
  have : ‖(2 * π * I : Complex)⁻¹‖ = (2 * π)⁻¹ := by simp [Real.pi_pos.le]
  rw [norm_smul]; rw [this]; rw [← div_eq_inv_mul]; rw [div_le_iff₀ Real.two_pi_pos]; rw [mul_comm (R * C)]; rw [← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

Depends on / 依赖: Real.pi_pos.le, Real.two_pi_pos, div_eq_inv_mul, mul_assoc, mul_comm, norm_integral_le_of_norm_le_const, norm_smul, pi_pos, two_pi_pos
-/
theorem norm_two_pi_i_inv_smul_integral_le_of_norm_le_const {f : Complex -> E} {c : Complex} {R C : Real}
    (hR : 0 <= R) (hf : forall z in sphere c R, ‖f z‖ <= C) :
    ‖(2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), f z‖ <= R * C := by
  have : ‖(2 * π * I : Complex)⁻¹‖ = (2 * π)⁻¹ := by simp [Real.pi_pos.le]
  rw [norm_smul]; rw [this]; rw [← div_eq_inv_mul]; rw [div_le_iff₀ Real.two_pi_pos]; rw [mul_comm (R * C)]; rw [← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

/--
theorem `norm_integral_lt_of_norm_le_const_of_lt` / 定理 `norm_integral_lt_of_norm_le_const_of_lt`

English:
theorem norm_integral_lt_of_norm_le_const_of_lt
  statement: {f : Complex -> E} {c : Complex} {R C : Real} (hR : 0 < R)
  proof: by
  rw [← _root_.abs_of_pos hR]; rw [← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ <= ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in 0..2 * π, R * C := by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_I,
        mul_one]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · gcongr
exact hf _ circleMap_mem_sphere _ hR.le _
      · gcongr
    _ = 2 * π * R * C := by simp [mul_assoc]; ring

@[simp]

中文:
定理 norm_integral_lt_of_norm_le_const_of_lt
  结论: {f : 复形 -> E} {c : 复形} {R C : 实数} (hR : 0 < R)
  证明: by
  rw [← _root_.abs_of_pos hR]; rw [← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ <= ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in 0..2 * π, R * C := by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_I,
        mul_one]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · gcongr
exact hf _ circleMap_mem_sphere _ hR.le _
      · gcongr
    _ = 2 * π * R * C := by simp [mul_assoc]; ring

@[simp]

Depends on / 依赖: Real.two_pi_, Real.two_pi_pos.le, _root_, _root_.abs_of_pos, abs_of_pos, circleMap, deriv_circleMap, image_circleMap_Ioc, integral_lt_integral_of_continuousOn_of_le_of_exists_lt, intervalIntegral, intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt, intervalIntegral.norm_integral_le_integral_norm, mul_one, norm_I, norm_circleMap_zero, norm_integral_le_integral_norm, norm_mul, norm_smul, two_pi_, two_pi_pos
-/
theorem norm_integral_lt_of_norm_le_const_of_lt {f : Complex -> E} {c : Complex} {R C : Real} (hR : 0 < R)
    (hc : ContinuousOn f (sphere c R)) (hf : forall z in sphere c R, ‖f z‖ <= C)
    (hlt : exists z in sphere c R, ‖f z‖ < C) : ‖∮ z in C(c, R), f z‖ < 2 * π * R * C := by
  rw [← _root_.abs_of_pos hR]; rw [← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ <= ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in 0..2 * π, R * C := by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_I,
        mul_one]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · gcongr
exact hf _ circleMap_mem_sphere _ hR.le _
      · gcongr
    _ = 2 * π * R * C := by simp [mul_assoc]; ring

@[simp]
/--
theorem `integral_smul` / 定理 `integral_smul`

English:
theorem integral_smul
  statement: {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜)
  proof: by
  simp only [circleIntegral, ← smul_comm a (_ : Complex) (_ : E), intervalIntegral.integral_smul]

@[simp]

中文:
定理 integral_smul
  结论: {𝕜 : 类型} [RCLike 𝕜] [赋范空间 𝕜 E] [标量交换类 𝕜 复形 E] (a : 𝕜)
  证明: by
  simp only [circleIntegral, ← smul_comm a (_ : Complex) (_ : E), intervalIntegral.integral_smul]

@[simp]

Depends on / 依赖: circleIntegral, integral_smul, intervalIntegral, intervalIntegral.integral_smul, smul_comm
-/
theorem integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 Complex E] (a : 𝕜)
    (f : Complex -> E) (c : Complex) (R : Real) : (∮ z in C(c, R), a • f z) = a • ∮ z in C(c, R), f z := by
  simp only [circleIntegral, ← smul_comm a (_ : Complex) (_ : E), intervalIntegral.integral_smul]

@[simp]
/--
theorem `integral_smul_const` / 定理 `integral_smul_const`

English:
theorem integral_smul_const
  given: [CompleteSpace E] (f : Complex -> Complex) (a : E) (c : Complex) (R : Real)
  proof: by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]

@[simp]

中文:
定理 integral_smul_const
  条件: [完备空间 E] (f : 复形 -> 复形) (a : E) (c : 复形) (R : 实数)
  证明: by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]

@[simp]

Depends on / 依赖: circleIntegral, integral_smul_const, intervalIntegral, intervalIntegral.integral_smul_const, smul_assoc
-/
theorem integral_smul_const [CompleteSpace E] (f : Complex -> Complex) (a : E) (c : Complex) (R : Real) :
    (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a := by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]

@[simp]
/--
theorem `integral_const_mul` / 定理 `integral_const_mul`

English:
theorem integral_const_mul
  given: (a : Complex) (f : Complex -> Complex) (c : Complex) (R : Real)
  proof: integral_smul a f c R

@[simp]

中文:
定理 integral_const_mul
  条件: (a : 复形) (f : 复形 -> 复形) (c : 复形) (R : 实数)
  证明: integral_smul a f c R

@[simp]

Depends on / 依赖: integral_smul
-/
theorem integral_const_mul (a : Complex) (f : Complex -> Complex) (c : Complex) (R : Real) :
    (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z :=
  integral_smul a f c R

@[simp]
/--
theorem `integral_sub_center_inv` / 定理 `integral_sub_center_inv`

English:
theorem integral_sub_center_inv
  given: (c : Complex) {R : Real} (hR : R != 0)
  proof: by
  simp [circleIntegral, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center hR)]

中文:
定理 integral_sub_center_inv
  条件: (c : 复形) {R : 实数} (hR : R != 0)
  证明: by
  simp [circleIntegral, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center hR)]

Depends on / 依赖: circleIntegral, circleMap_ne_center, div_eq_mul_inv
-/
theorem integral_sub_center_inv (c : Complex) {R : Real} (hR : R != 0) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I := by
  simp [circleIntegral, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center hR)]

/--
theorem `integral_eq_zero_of_hasDerivWithinAt'` / 定理 `integral_eq_zero_of_hasDerivWithinAt'`

English:
theorem integral_eq_zero_of_hasDerivWithinAt'
  statement: [CompleteSpace E] {f f' : Complex -> E} {c : Complex} {R : Real}
  proof: by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi

中文:
定理 integral_eq_zero_of_hasDerivWithinAt'
  结论: [完备空间 E] {f f' : 复形 -> E} {c : 复形} {R : 实数}
  证明: by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi

Depends on / 依赖: CircleIntegrable, circleMap_mem_sphere, differentiable_circleMap, hasDerivAt, hi.out, integral_eq_sub_of_hasDerivAt, integral_undef, intervalIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt, periodic_circleMap, scomp_hasDerivAt, sub_eq_zero
-/
theorem integral_eq_zero_of_hasDerivWithinAt' [CompleteSpace E] {f f' : Complex -> E} {c : Complex} {R : Real}
    (h : forall z in sphere c |R|, HasDerivWithinAt f (f' z) (sphere c |R|) z) :
    (∮ z in C(c, R), f' z) = 0 := by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi

/--
theorem `integral_eq_zero_of_hasDerivWithinAt` / 定理 `integral_eq_zero_of_hasDerivWithinAt`

English:
theorem integral_eq_zero_of_hasDerivWithinAt
  statement: [CompleteSpace E]
  proof: integral_eq_zero_of_hasDerivWithinAt' (abs_of_nonneg hR).symm ▸ h

中文:
定理 integral_eq_zero_of_hasDerivWithinAt
  结论: [完备空间 E]
  证明: integral_eq_zero_of_hasDerivWithinAt' (abs_of_nonneg hR).symm ▸ h

Depends on / 依赖: abs_of_nonneg, integral_eq_zero_of_hasDerivWithinAt
-/
theorem integral_eq_zero_of_hasDerivWithinAt [CompleteSpace E]
    {f f' : Complex -> E} {c : Complex} {R : Real} (hR : 0 <= R)
    (h : forall z in sphere c R, HasDerivWithinAt f (f' z) (sphere c R) z) : (∮ z in C(c, R), f' z) = 0 :=
integral_eq_zero_of_hasDerivWithinAt' (abs_of_nonneg hR).symm ▸ h

/--
theorem `integral_sub_zpow_of_undef` / 定理 `integral_sub_zpow_of_undef`

English:
theorem integral_sub_zpow_of_undef
  statement: {n : Int} {c w : Complex} {R : Real} (hn : n < 0)
  proof: by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or] using mem_sphere_iff_norm.1 hw

中文:
定理 integral_sub_zpow_of_undef
  结论: {n : 整数} {c w : 复形} {R : 实数} (hn : n < 0)
  证明: by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or] using mem_sphere_iff_norm.1 hw

Depends on / 依赖: circleIntegrable_sub_zpow_iff, eq_or_ne, integral_radius_zero, integral_undef, mem_sphere_iff_norm, not_or
-/
theorem integral_sub_zpow_of_undef {n : Int} {c w : Complex} {R : Real} (hn : n < 0)
    (hw : w in sphere c |R|) : (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or] using mem_sphere_iff_norm.1 hw

/--
theorem `integral_sub_zpow_of_ne` / 定理 `integral_sub_zpow_of_ne`

English:
theorem integral_sub_zpow_of_ne
  given: {n : Int} (hn : n != -1) (c w : Complex) (R : Real)
  proof: by
  by_cases! H : w in sphere c |R| ∧ n < -1
  · rcases H with ⟨hw, hn⟩
    exact integral_sub_zpow_of_undef (hn.trans (by decide)) hw
  have hd : forall z, z != w ∨ -1 <= n ->
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert!
      ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z ((hasDerivAt_id z).sub_const w)).div_const
        _ using 1
    · have hn' : (n + 1 : Complex) != 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z ?_).hasDerivWithinAt
exact (ne_or_eq z w).imp_right fun (h : z = w) => H h ▸ hz

中文:
定理 integral_sub_zpow_of_ne
  条件: {n : 整数} (hn : n != -1) (c w : 复形) (R : 实数)
  证明: by
  by_cases! H : w in sphere c |R| ∧ n < -1
  · rcases H with ⟨hw, hn⟩
    exact integral_sub_zpow_of_undef (hn.trans (by decide)) hw
  have hd : forall z, z != w ∨ -1 <= n ->
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert!
      ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z ((hasDerivAt_id z).sub_const w)).div_const
        _ using 1
    · have hn' : (n + 1 : Complex) != 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z ?_).hasDerivWithinAt
exact (ne_or_eq z w).imp_right fun (h : z = w) => H h ▸ hz

Depends on / 依赖: HasDerivAt, Int.cast_inj, Int.cast_neg, Int.cast_one, cast_inj, cast_neg, cast_one, convert, div_const, eq_neg_iff_add_eq_zero, hasDerivAt_id, hasDerivAt_zpow, hn.trans, hne.imp, integral_sub_zpow_of_undef, mul_div, sphere, sub_const
-/
theorem integral_sub_zpow_of_ne {n : Int} (hn : n != -1) (c w : Complex) (R : Real) :
    (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  by_cases! H : w in sphere c |R| ∧ n < -1
  · rcases H with ⟨hw, hn⟩
    exact integral_sub_zpow_of_undef (hn.trans (by decide)) hw
  have hd : forall z, z != w ∨ -1 <= n ->
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert!
      ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z ((hasDerivAt_id z).sub_const w)).div_const
        _ using 1
    · have hn' : (n + 1 : Complex) != 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z ?_).hasDerivWithinAt
exact (ne_or_eq z w).imp_right fun (h : z = w) => H h ▸ hz

end circleIntegral

/--
Definition of `cauchyPowerSeries` / `cauchyPowerSeries` 的定义

English:
definition cauchyPowerSeries
  signature: (f : Complex -> E) (c : Complex) (R : Real)
  body: fun n =>
ContinuousMultilinearMap.mkPiRing Complex _
    (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z

中文:
定义 cauchyPowerSeries
  签名: (f : 复形 -> E) (c : 复形) (R : 实数)
  定义体: fun n =>
ContinuousMultilinearMap.mkPiRing Complex _
    (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z
-/
def cauchyPowerSeries (f : Complex -> E) (c : Complex) (R : Real) : FormalMultilinearSeries Complex Complex E := fun n =>
ContinuousMultilinearMap.mkPiRing Complex _
    (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z

/--
theorem `cauchyPowerSeries_apply` / 定理 `cauchyPowerSeries_apply`

English:
theorem cauchyPowerSeries_apply
  given: (f : Complex -> E) (c : Complex) (R : Real) (n : Nat) (w : Complex)
  proof: by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    div_eq_mul_inv, mul_pow, mul_smul, circleIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]

中文:
定理 cauchyPowerSeries_apply
  条件: (f : 复形 -> E) (c : 复形) (R : 实数) (n : 自然数) (w : 复形)
  证明: by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    div_eq_mul_inv, mul_pow, mul_smul, circleIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, cauchyPowerSeries, circleIntegral, circleIntegral.integral_smul, div_eq_mul_inv, integral_smul, mkPiRing_apply, mul_pow, mul_smul, prod_const, smul_comm
-/
theorem cauchyPowerSeries_apply (f : Complex -> E) (c : Complex) (R : Real) (n : Nat) (w : Complex) :
    (cauchyPowerSeries f c R n fun _ => w) =
      (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    div_eq_mul_inv, mul_pow, mul_smul, circleIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]

/--
theorem `norm_cauchyPowerSeries_le` / 定理 `norm_cauchyPowerSeries_le`

English:
theorem norm_cauchyPowerSeries_le
  given: (f : Complex -> E) (c : Complex) (R : Real) (n : Nat)
  proof: calc ‖cauchyPowerSeries f c R n‖
    _ = (2 * π)⁻¹ * ‖∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp [cauchyPowerSeries, norm_smul, Real.pi_pos.le]
    _ <= (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ •
        (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = (2 * π)⁻¹ *
        (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ x : Real in 0..2 * π, ‖f (circleMap c R x)‖))) := by
      simp [norm_smul, mul_left_comm |R|]
    _ <= ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev]
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)]
        rwa [Ne, _root_.abs_eq_zero]

中文:
定理 norm_cauchyPowerSeries_le
  条件: (f : 复形 -> E) (c : 复形) (R : 实数) (n : 自然数)
  证明: calc ‖cauchyPowerSeries f c R n‖
    _ = (2 * π)⁻¹ * ‖∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp [cauchyPowerSeries, norm_smul, Real.pi_pos.le]
    _ <= (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ •
        (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = (2 * π)⁻¹ *
        (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ x : Real in 0..2 * π, ‖f (circleMap c R x)‖))) := by
      simp [norm_smul, mul_left_comm |R|]
    _ <= ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev]
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)]
        rwa [Ne, _root_.abs_eq_zero]

Depends on / 依赖: Real.pi_pos.le, cauchyPowerSeries, circleMap, intervalIntegral, intervalIntegral.norm_integral_le_integral_norm, mul_l, norm_integral_le_integral_norm, norm_smul, pi_pos
-/
theorem norm_cauchyPowerSeries_le (f : Complex -> E) (c : Complex) (R : Real) (n : Nat) :
    ‖cauchyPowerSeries f c R n‖ <=
      ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n :=
  calc ‖cauchyPowerSeries f c R n‖
    _ = (2 * π)⁻¹ * ‖∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp [cauchyPowerSeries, norm_smul, Real.pi_pos.le]
    _ <= (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ •
        (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = (2 * π)⁻¹ *
        (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ x : Real in 0..2 * π, ‖f (circleMap c R x)‖))) := by
      simp [norm_smul, mul_left_comm |R|]
    _ <= ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev]
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)]
        rwa [Ne, _root_.abs_eq_zero]

/--
theorem `le_radius_cauchyPowerSeries` / 定理 `le_radius_cauchyPowerSeries`

English:
theorem le_radius_cauchyPowerSeries
  given: (f : Complex -> E) (c : Complex) (R : Real>=0)
  proof: by
  refine
    (cauchyPowerSeries f c R).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans ?_
  rw [abs_of_nonneg R.coe_nonneg]
  rcases eq_or_ne (R ^ n : Real) 0 with hR | hR
  · rw_mod_cast [hR, mul_zero]
    exact mul_nonneg (inv_nonneg.2 Real.two_pi_pos.le)
      (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  · rw [inv_pow]
    have : (R : Real) ^ n != 0 := by norm_cast at hR ⊢
    rw [inv_mul_cancel_right₀ this]

中文:
定理 le_radius_cauchyPowerSeries
  条件: (f : 复形 -> E) (c : 复形) (R : 实数>=0)
  证明: by
  refine
    (cauchyPowerSeries f c R).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans ?_
  rw [abs_of_nonneg R.coe_nonneg]
  rcases eq_or_ne (R ^ n : Real) 0 with hR | hR
  · rw_mod_cast [hR, mul_zero]
    exact mul_nonneg (inv_nonneg.2 Real.two_pi_pos.le)
      (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  · rw [inv_pow]
    have : (R : Real) ^ n != 0 := by norm_cast at hR ⊢
    rw [inv_mul_cancel_right₀ this]

Depends on / 依赖: R.coe_nonneg, Real.two_pi_pos.le, abs_of_nonneg, cauchyPowerSeries, circleMap, coe_nonneg, eq_or_ne, integral_nonneg, intervalIntegral, intervalIntegral.integral_nonneg, inv_nonneg, inv_pow, le_radius_of_bound, mul_le_mul_of_nonneg_right, mul_nonneg, mul_zero, norm_cauchyPowerSeries_le, norm_nonneg, pow_nonneg, rw_mod_cast
-/
theorem le_radius_cauchyPowerSeries (f : Complex -> E) (c : Complex) (R : Real>=0) :
    ↑R <= (cauchyPowerSeries f c R).radius := by
  refine
    (cauchyPowerSeries f c R).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : Real in 0..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans ?_
  rw [abs_of_nonneg R.coe_nonneg]
  rcases eq_or_ne (R ^ n : Real) 0 with hR | hR
  · rw_mod_cast [hR, mul_zero]
    exact mul_nonneg (inv_nonneg.2 Real.two_pi_pos.le)
      (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  · rw [inv_pow]
    have : (R : Real) ^ n != 0 := by norm_cast at hR ⊢
    rw [inv_mul_cancel_right₀ this]

/--
theorem `hasSum_two_pi_I_cauchyPowerSeries_integral` / 定理 `hasSum_two_pi_I_cauchyPowerSeries_integral`

English:
theorem hasSum_two_pi_I_cauchyPowerSeries_integral
  statement: {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
  proof: by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hwR : ‖w‖ / R in Ico (0 : Real) 1 :=
    ⟨div_nonneg (norm_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (‖w‖ / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    · fun_prop
    · fun_prop
    · fun_prop
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, inv_mul_cancel_left₀ hR.ne', mul_comm ‖_‖]
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖w / (circleMap c R θ - c)‖ < 1 := by simpa [abs_of_pos hR] using hwR.2
    convert! (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    simp [← sub_sub, ← mul_inv, sub_mul, div_mul_cancel₀ _ (circleMap_ne_center hR.ne')]

中文:
定理 hasSum_two_pi_I_cauchyPowerSeries_integral
  结论: {f : 复形 -> E} {c : 复形} {R : 实数} {w : 复形}
  证明: by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hwR : ‖w‖ / R in Ico (0 : Real) 1 :=
    ⟨div_nonneg (norm_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (‖w‖ / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    · fun_prop
    · fun_prop
    · fun_prop
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, inv_mul_cancel_left₀ hR.ne', mul_comm ‖_‖]
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖w / (circleMap c R θ - c)‖ < 1 := by simpa [abs_of_pos hR] using hwR.2
    convert! (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    simp [← sub_sub, ← mul_inv, sub_mul, div_mul_cancel₀ _ (circleMap_ne_center hR.ne')]

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.smul, Measurable, Measurable.aestronglyMeasurable, abs_of_pos, aestronglyMeasurable, apply_rules, circleMap, deriv_circleMap, div_lt_one, div_nonneg, fun_prop, hR.le, hasSum_integral_of_dominated_convergence, hf.def, intervalIntegral, intervalIntegral.hasSum_integral_of_dominated_convergence, mul_left, norm_nonneg, norm_smul
-/
theorem hasSum_two_pi_I_cauchyPowerSeries_integral {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n : Nat => ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z)
      (∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hwR : ‖w‖ / R in Ico (0 : Real) 1 :=
    ⟨div_nonneg (norm_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (‖w‖ / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    · fun_prop
    · fun_prop
    · fun_prop
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, inv_mul_cancel_left₀ hR.ne', mul_comm ‖_‖]
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖w / (circleMap c R θ - c)‖ < 1 := by simpa [abs_of_pos hR] using hwR.2
    convert! (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    simp [← sub_sub, ← mul_inv, sub_mul, div_mul_cancel₀ _ (circleMap_ne_center hR.ne')]

/--
theorem `hasSum_cauchyPowerSeries_integral` / 定理 `hasSum_cauchyPowerSeries_integral`

English:
theorem hasSum_cauchyPowerSeries_integral
  statement: {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
  proof: by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _

中文:
定理 hasSum_cauchyPowerSeries_integral
  结论: {f : 复形 -> E} {c : 复形} {R : 实数} {w : 复形}
  证明: by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _

Depends on / 依赖: cauchyPowerSeries_apply, const_smul, hasSum_two_pi_I_cauchyPowerSeries_integral
-/
theorem hasSum_cauchyPowerSeries_integral {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n => cauchyPowerSeries f c R n fun _ => w)
      ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _

/--
theorem `sum_cauchyPowerSeries_eq_integral` / 定理 `sum_cauchyPowerSeries_eq_integral`

English:
theorem sum_cauchyPowerSeries_eq_integral
  statement: {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
  proof: (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq

中文:
定理 sum_cauchyPowerSeries_eq_integral
  结论: {f : 复形 -> E} {c : 复形} {R : 实数} {w : 复形}
  证明: (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq

Depends on / 依赖: hasSum_cauchyPowerSeries_integral, tsum_eq
-/
theorem sum_cauchyPowerSeries_eq_integral {f : Complex -> E} {c : Complex} {R : Real} {w : Complex}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    (cauchyPowerSeries f c R).sum w = (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z :=
  (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq

/--
theorem `hasFPowerSeriesOn_cauchy_integral` / 定理 `hasFPowerSeriesOn_cauchy_integral`

English:
theorem hasFPowerSeriesOn_cauchy_integral
  statement: {f : Complex -> E} {c : Complex} {R : Real>=0}
  proof: { r_le := le_radius_cauchyPowerSeries _ _ _
    r_pos := ENNReal.coe_pos.2 hR
hasSum := fun hy => hasSum_cauchyPowerSeries_integral hf by simpa using hy }

中文:
定理 hasFPowerSeriesOn_cauchy_integral
  结论: {f : 复形 -> E} {c : 复形} {R : 实数>=0}
  证明: { r_le := le_radius_cauchyPowerSeries _ _ _
    r_pos := ENNReal.coe_pos.2 hR
hasSum := fun hy => hasSum_cauchyPowerSeries_integral hf by simpa using hy }

Depends on / 依赖: ENNReal, ENNReal.coe_pos, coe_pos, hasSum, hasSum_cauchyPowerSeries_integral, le_radius_cauchyPowerSeries, r_le, r_pos
-/
theorem hasFPowerSeriesOn_cauchy_integral {f : Complex -> E} {c : Complex} {R : Real>=0}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    HasFPowerSeriesOnBall (fun w => (2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z)
      (cauchyPowerSeries f c R) c R :=
  { r_le := le_radius_cauchyPowerSeries _ _ _
    r_pos := ENNReal.coe_pos.2 hR
hasSum := fun hy => hasSum_cauchyPowerSeries_integral hf by simpa using hy }

namespace circleIntegral

/--
theorem `integral_sub_inv_of_mem_ball` / 定理 `integral_sub_inv_of_mem_ball`

English:
theorem integral_sub_inv_of_mem_ball
  given: {c w : Complex} {R : Real} (hw : w in ball c R)
  proof: by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : Nat => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : Complex)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A (mem_ball_iff_norm.1 hw)
  have H : forall n : Nat, n != 0 -> (∮ z in C(c, R), (z - c) ^ (-n - 1 : Int)) = 0 := by
    refine fun n hn => integral_sub_zpow_of_ne ?_ _ _ _; simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by simp [hR.ne']
  refine this ▸ hasSum_single _ fun n hn => ?_
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn)]; rw [mul_zero]
  intro z _
  rw [← pow_succ]; rw [← zpow_natCast]; rw [inv_zpow]; rw [← zpow_neg]; rw [Int.natCast_succ]; rw [neg_add]; rw [sub_eq_add_neg _ (1 : Int)]

中文:
定理 integral_sub_inv_of_mem_ball
  条件: {c w : 复形} {R : 实数} (hw : w in ball c R)
  证明: by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : Nat => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : Complex)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A (mem_ball_iff_norm.1 hw)
  have H : forall n : Nat, n != 0 -> (∮ z in C(c, R), (z - c) ^ (-n - 1 : Int)) = 0 := by
    refine fun n hn => integral_sub_zpow_of_ne ?_ _ _ _; simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by simp [hR.ne']
  refine this ▸ hasSum_single _ fun n hn => ?_
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn)]; rw [mul_zero]
  intro z _
  rw [← pow_succ]; rw [← zpow_natCast]; rw [inv_zpow]; rw [← zpow_neg]; rw [Int.natCast_succ]; rw [neg_add]; rw [sub_eq_add_neg _ (1 : Int)]

Depends on / 依赖: CircleIntegrable, H.unique, HasSum, add_sub_cancel, circleIntegrable, continuousOn_const, continuousOn_const.circleIntegrable, dist_nonneg, dist_nonneg.trans_lt, hasSum_two_pi_I_cauchyPowerSeries_integral, mem_ball_iff_norm, mul_one, smul_eq_mul, trans_lt, unique
-/
theorem integral_sub_inv_of_mem_ball {c w : Complex} {R : Real} (hw : w in ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : Nat => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : Complex)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A (mem_ball_iff_norm.1 hw)
  have H : forall n : Nat, n != 0 -> (∮ z in C(c, R), (z - c) ^ (-n - 1 : Int)) = 0 := by
    refine fun n hn => integral_sub_zpow_of_ne ?_ _ _ _; simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by simp [hR.ne']
  refine this ▸ hasSum_single _ fun n hn => ?_
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn)]; rw [mul_zero]
  intro z _
  rw [← pow_succ]; rw [← zpow_natCast]; rw [inv_zpow]; rw [← zpow_neg]; rw [Int.natCast_succ]; rw [neg_add]; rw [sub_eq_add_neg _ (1 : Int)]

end circleIntegral
