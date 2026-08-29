/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`. That is, the Kullback-Leibler divergence is an integral
of `klFun` composed with a Radon-Nikodym derivative.

For probability measures, any function `f` that differs from `klFun` by an affine function of the
form `x ↦ a * (x - 1)` would give the same value for the integral
`∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
However, `klFun` is the particular choice among those that satisfies `klFun 1 = 0` and
`deriv klFun 1 = 0`, which ensures that desirable properties of the Kullback-Leibler divergence
extend to other finite measures: it is nonnegative and zero iff the two measures are equal.

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a continuous nonnegative, strictly convex function on $[0,∞)$, with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff the log-likelihood ratio
  `llr μ ν` is integrable with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`.

-/

@[expose] public section

open Real MeasureTheory Filter Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : Real}

/--
Definition of `klFun` / `klFun` 的定义

English:
definition klFun
  signature: (x : Real)
  body: x * log x + 1 - x

中文:
定义 klFun
  签名: (x : 实数)
  定义体: x * log x + 1 - x
-/
noncomputable def klFun (x : Real) : Real := x * log x + 1 - x

/--
lemma `klFun_apply` / 引理 `klFun_apply`

English:
lemma klFun_apply
  given: (x : Real)
  statement: klFun x = x * log x + 1 - x
  proof: rfl

中文:
引理 klFun_apply
  条件: (x : 实数)
  结论: klFun x = x * log x + 1 - x
  证明: rfl
-/
lemma klFun_apply (x : Real) : klFun x = x * log x + 1 - x := rfl

/--
lemma `klFun_zero` / 引理 `klFun_zero`

English:
lemma klFun_zero
  statement: klFun 0 = 1
  proof: by simp [klFun]

中文:
引理 klFun_zero
  结论: klFun 0 = 1
  证明: by simp [klFun]
-/
lemma klFun_zero : klFun 0 = 1 := by simp [klFun]

/--
lemma `klFun_one` / 引理 `klFun_one`

English:
lemma klFun_one
  statement: klFun 1 = 0
  proof: by simp [klFun]

中文:
引理 klFun_one
  结论: klFun 1 = 0
  证明: by simp [klFun]
-/
lemma klFun_one : klFun 1 = 0 := by simp [klFun]

/--
lemma `strictConvexOn_klFun` / 引理 `strictConvexOn_klFun`

English:
lemma strictConvexOn_klFun
  statement: StrictConvexOn Real (Ici 0) klFun
  proof: (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

中文:
引理 strictConvexOn_klFun
  结论: StrictConvexOn 实数 (Ici 0) klFun
  证明: (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

Depends on / 依赖: add_convexOn, concaveOn_id, convexOn_const, convex_Ici, strictConvexOn_mul_log, strictConvexOn_mul_log.add_convexOn, sub_concaveOn
-/
lemma strictConvexOn_klFun : StrictConvexOn Real (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

/--
lemma `convexOn_klFun` / 引理 `convexOn_klFun`

English:
lemma convexOn_klFun
  statement: ConvexOn Real (Ici 0) klFun
  proof: strictConvexOn_klFun.convexOn

中文:
引理 convexOn_klFun
  结论: ConvexOn 实数 (Ici 0) klFun
  证明: strictConvexOn_klFun.convexOn

Depends on / 依赖: convexOn, strictConvexOn_klFun, strictConvexOn_klFun.convexOn
-/
lemma convexOn_klFun : ConvexOn Real (Ici 0) klFun := strictConvexOn_klFun.convexOn

/--
lemma `convexOn_Ioi_klFun` / 引理 `convexOn_Ioi_klFun`

English:
lemma convexOn_Ioi_klFun
  statement: ConvexOn Real (Ioi 0) klFun
  proof: convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

中文:
引理 convexOn_Ioi_klFun
  结论: ConvexOn 实数 (Ioi 0) klFun
  证明: convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

Depends on / 依赖: Ioi_subset_Ici, convexOn_klFun, convexOn_klFun.subset, convex_Ioi, le_rfl, subset
-/
lemma convexOn_Ioi_klFun : ConvexOn Real (Ioi 0) klFun :=
  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

/-- `klFun` is continuous. -/
@[continuity, fun_prop]
/--
lemma `continuous_klFun` / 引理 `continuous_klFun`

English:
lemma continuous_klFun
  statement: Continuous klFun
  proof: by unfold klFun; fun_prop

中文:
引理 continuous_klFun
  结论: Continuous klFun
  证明: by unfold klFun; fun_prop

Depends on / 依赖: fun_prop
-/
lemma continuous_klFun : Continuous klFun := by unfold klFun; fun_prop

/-- `klFun` is measurable. -/
@[fun_prop]
/--
lemma `measurable_klFun` / 引理 `measurable_klFun`

English:
lemma measurable_klFun
  statement: Measurable klFun
  proof: continuous_klFun.measurable

中文:
引理 measurable_klFun
  结论: Measurable klFun
  证明: continuous_klFun.measurable

Depends on / 依赖: continuous_klFun, continuous_klFun.measurable, measurable
-/
lemma measurable_klFun : Measurable klFun := continuous_klFun.measurable

/-- `klFun` is strongly measurable. -/
@[fun_prop]
/--
lemma `stronglyMeasurable_klFun` / 引理 `stronglyMeasurable_klFun`

English:
lemma stronglyMeasurable_klFun
  statement: StronglyMeasurable klFun
  proof: measurable_klFun.stronglyMeasurable

中文:
引理 stronglyMeasurable_klFun
  结论: StronglyMeasurable klFun
  证明: measurable_klFun.stronglyMeasurable

Depends on / 依赖: measurable_klFun, measurable_klFun.stronglyMeasurable, stronglyMeasurable
-/
lemma stronglyMeasurable_klFun : StronglyMeasurable klFun := measurable_klFun.stronglyMeasurable

section Derivatives

/--
lemma `hasDerivAt_klFun` / 引理 `hasDerivAt_klFun`

English:
lemma hasDerivAt_klFun
  given: (hx : x != 0)
  statement: HasDerivAt klFun (log x) x
  proof: by
  convert! ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

中文:
引理 hasDerivAt_klFun
  条件: (hx : x != 0)
  结论: HasDerivAt klFun (log x) x
  证明: by
  convert! ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

Depends on / 依赖: convert, hasDerivAt_const, hasDerivAt_id, hasDerivAt_mul_log
-/
lemma hasDerivAt_klFun (hx : x != 0) : HasDerivAt klFun (log x) x := by
  convert! ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

/--
lemma `not_differentiableAt_klFun_zero` / 引理 `not_differentiableAt_klFun_zero`

English:
lemma not_differentiableAt_klFun_zero
  statement: ¬ DifferentiableAt Real klFun 0
  proof: by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

中文:
引理 not_differentiableAt_klFun_zero
  结论: ¬ DifferentiableAt 实数 klFun 0
  证明: by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

Depends on / 依赖: not_DifferentiableAt_log_mul_zero
-/
lemma not_differentiableAt_klFun_zero : ¬ DifferentiableAt Real klFun 0 := by
  unfold klFun; simpa using not_DifferentiableAt_log_mul_zero

/-- The derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `deriv` in that case is 0. -/
@[simp]
/--
lemma `deriv_klFun` / 引理 `deriv_klFun`

English:
lemma deriv_klFun
  statement: deriv klFun = log
  proof: by
  ext x
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact deriv_zero_of_not_differentiableAt not_differentiableAt_klFun_zero
  · exact (hasDerivAt_klFun h0).deriv

中文:
引理 deriv_klFun
  结论: deriv klFun = log
  证明: by
  ext x
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact deriv_zero_of_not_differentiableAt not_differentiableAt_klFun_zero
  · exact (hasDerivAt_klFun h0).deriv

Depends on / 依赖: deriv_zero_of_not_differentiableAt, hasDerivAt_klFun, log_zero, not_differentiableAt_klFun_zero
-/
lemma deriv_klFun : deriv klFun = log := by
  ext x
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact deriv_zero_of_not_differentiableAt not_differentiableAt_klFun_zero
  · exact (hasDerivAt_klFun h0).deriv

/--
lemma `not_differentiableWithinAt_klFun_Ioi_zero` / 引理 `not_differentiableWithinAt_klFun_Ioi_zero`

English:
lemma not_differentiableWithinAt_klFun_Ioi_zero
  statement: ¬ DifferentiableWithinAt Real klFun (Ioi 0) 0
  proof: by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsGT_zero

中文:
引理 not_differentiableWithinAt_klFun_Ioi_zero
  结论: ¬ DifferentiableWithinAt 实数 klFun (Ioi 0) 0
  证明: by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsGT_zero

Depends on / 依赖: deriv_klFun, not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi, tendsto_log_nhdsGT_zero
-/
lemma not_differentiableWithinAt_klFun_Ioi_zero : ¬ DifferentiableWithinAt Real klFun (Ioi 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsGT_zero

/--
lemma `not_differentiableWithinAt_klFun_Iio_zero` / 引理 `not_differentiableWithinAt_klFun_Iio_zero`

English:
lemma not_differentiableWithinAt_klFun_Iio_zero
  statement: ¬ DifferentiableWithinAt Real klFun (Iio 0) 0
  proof: by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsLT_zero

中文:
引理 not_differentiableWithinAt_klFun_Iio_zero
  结论: ¬ DifferentiableWithinAt 实数 klFun (Iio 0) 0
  证明: by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsLT_zero

Depends on / 依赖: deriv_klFun, not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio, tendsto_log_nhdsLT_zero
-/
lemma not_differentiableWithinAt_klFun_Iio_zero : ¬ DifferentiableWithinAt Real klFun (Iio 0) 0 := by
  refine not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio _ ?_
  rw [deriv_klFun]
  exact tendsto_log_nhdsLT_zero

/-- The right derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
/--
lemma `rightDeriv_klFun` / 引理 `rightDeriv_klFun`

English:
lemma rightDeriv_klFun
  statement: derivWithin klFun (Ioi x) x = log x
  proof: by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Ioi_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

中文:
引理 rightDeriv_klFun
  结论: derivWithin klFun (Ioi x) x = log x
  证明: by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Ioi_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

Depends on / 依赖: derivWithin, derivWithin_zero_of_not_differentiableWithinAt, hasDerivAt_klFun, hasDerivWithinAt, hasDerivWithinAt.derivWithin, log_zero, not_differentiableWithinAt_klFun_Ioi_zero, uniqueDiffWithinAt_Ioi
-/
lemma rightDeriv_klFun : derivWithin klFun (Ioi x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Ioi_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

/-- The left derivative of `klFun` is `log x`. This also holds at `x = 0` although `klFun` is not
differentiable there since the default value of `derivWithin` in that case is 0. -/
@[simp]
/--
lemma `leftDeriv_klFun` / 引理 `leftDeriv_klFun`

English:
lemma leftDeriv_klFun
  statement: derivWithin klFun (Iio x) x = log x
  proof: by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Iio_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

中文:
引理 leftDeriv_klFun
  结论: derivWithin klFun (Iio x) x = log x
  证明: by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Iio_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

Depends on / 依赖: derivWithin, derivWithin_zero_of_not_differentiableWithinAt, hasDerivAt_klFun, hasDerivWithinAt, hasDerivWithinAt.derivWithin, log_zero, not_differentiableWithinAt_klFun_Iio_zero, uniqueDiffWithinAt_Iio
-/
lemma leftDeriv_klFun : derivWithin klFun (Iio x) x = log x := by
  by_cases h0 : x = 0
  · simp only [h0, log_zero]
    exact derivWithin_zero_of_not_differentiableWithinAt not_differentiableWithinAt_klFun_Iio_zero
  · exact (hasDerivAt_klFun h0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

/--
lemma `rightDeriv_klFun_one` / 引理 `rightDeriv_klFun_one`

English:
lemma rightDeriv_klFun_one
  statement: derivWithin klFun (Ioi 1) 1 = 0
  proof: by simp

中文:
引理 rightDeriv_klFun_one
  结论: derivWithin klFun (Ioi 1) 1 = 0
  证明: by simp
-/
lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp

/--
lemma `leftDeriv_klFun_one` / 引理 `leftDeriv_klFun_one`

English:
lemma leftDeriv_klFun_one
  statement: derivWithin klFun (Iio 1) 1 = 0
  proof: by simp

中文:
引理 leftDeriv_klFun_one
  结论: derivWithin klFun (Iio 1) 1 = 0
  证明: by simp
-/
lemma leftDeriv_klFun_one : derivWithin klFun (Iio 1) 1 = 0 := by simp

/--
lemma `tendsto_rightDeriv_klFun_atTop` / 引理 `tendsto_rightDeriv_klFun_atTop`

English:
lemma tendsto_rightDeriv_klFun_atTop
  proof: by
  simp only [rightDeriv_klFun]
  exact tendsto_log_atTop

中文:
引理 tendsto_rightDeriv_klFun_atTop
  证明: by
  simp only [rightDeriv_klFun]
  exact tendsto_log_atTop

Depends on / 依赖: rightDeriv_klFun, tendsto_log_atTop
-/
lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x => derivWithin klFun (Ioi x) x) atTop atTop := by
  simp only [rightDeriv_klFun]
  exact tendsto_log_atTop

end Derivatives

/--
lemma `isMinOn_klFun` / 引理 `isMinOn_klFun`

English:
lemma isMinOn_klFun
  statement: IsMinOn klFun (Ici 0) 1
  proof: convexOn_klFun.isMinOn_of_rightDeriv_eq_zero (by simp) (by simp)

中文:
引理 isMinOn_klFun
  结论: IsMinOn klFun (Ici 0) 1
  证明: convexOn_klFun.isMinOn_of_rightDeriv_eq_zero (by simp) (by simp)

Depends on / 依赖: convexOn_klFun, convexOn_klFun.isMinOn_of_rightDeriv_eq_zero, isMinOn_of_rightDeriv_eq_zero
-/
lemma isMinOn_klFun : IsMinOn klFun (Ici 0) 1 :=
  convexOn_klFun.isMinOn_of_rightDeriv_eq_zero (by simp) (by simp)

/--
lemma `klFun_nonneg` / 引理 `klFun_nonneg`

English:
lemma klFun_nonneg
  given: (hx : 0 <= x)
  statement: 0 <= klFun x
  proof: klFun_one ▸ isMinOn_klFun hx

中文:
引理 klFun_nonneg
  条件: (hx : 0 <= x)
  结论: 0 <= klFun x
  证明: klFun_one ▸ isMinOn_klFun hx

Depends on / 依赖: isMinOn_klFun, klFun_one
-/
lemma klFun_nonneg (hx : 0 <= x) : 0 <= klFun x := klFun_one ▸ isMinOn_klFun hx

/--
lemma `klFun_eq_zero_iff` / 引理 `klFun_eq_zero_iff`

English:
lemma klFun_eq_zero_iff
  given: (hx : 0 <= x)
  statement: klFun x = 0 ↔ x = 1
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy => h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' Real)

中文:
引理 klFun_eq_zero_iff
  条件: (hx : 0 <= x)
  结论: klFun x = 0 ↔ x = 1
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy => h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' Real)

Depends on / 依赖: eq_of_isMinOn, isMinOn_iff, isMinOn_iff.mpr, isMinOn_klFun, klFun_apply, klFun_nonneg, strictConvexOn_klFun, strictConvexOn_klFun.eq_of_isMinOn, zero_le_one
-/
lemma klFun_eq_zero_iff (hx : 0 <= x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [klFun_apply, h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy => h ▸ klFun_nonneg hy)
    isMinOn_klFun hx (zero_le_one' Real)

/--
lemma `tendsto_klFun_atTop` / 引理 `tendsto_klFun_atTop`

English:
lemma tendsto_klFun_atTop
  statement: Tendsto klFun atTop atTop
  proof: by
  have : klFun = (fun x => x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

中文:
引理 tendsto_klFun_atTop
  结论: Tendsto klFun atTop atTop
  证明: by
  have : klFun = (fun x => x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

Depends on / 依赖: Tendsto, Tendsto.atTop_add, atTop_add, tendsto_const_nhds, tendsto_id, tendsto_id.atTop_mul_atTop, tendsto_log_atTop, tendsto_log_atTop.atTop_add
-/
lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x => x * (log x - 1) + 1) := by unfold klFun; ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine tendsto_id.atTop_mul_atTop₀ ?_
  exact tendsto_log_atTop.atTop_add tendsto_const_nhds

section Integral

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/--
lemma `integrable_klFun_rnDeriv_iff` / 引理 `integrable_klFun_rnDeriv_iff`

English:
lemma integrable_klFun_rnDeriv_iff
  given: (hμν : μ ≪ ν)
  proof: by
  suffices Integrable (fun x => (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert! this using 3 with x
    rw [klFun]; rw [add_sub_assoc]
  rw [integrable_add_iff_integrable_left']; rw [integrable_rnDeriv_mul_log_if

中文:
引理 integrable_klFun_rnDeriv_iff
  条件: (hμν : μ ≪ ν)
  证明: by
  suffices Integrable (fun x => (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert! this using 3 with x
    rw [klFun]; rw [add_sub_assoc]
  rw [integrable_add_iff_integrable_left']; rw [integrable_rnDeriv_mul_log_if

Depends on / 依赖: Integrable, add_sub_assoc, convert, fun_prop, integrable_add_iff_integrable_left, integrable_rnDeriv_mul_log_iff, rnDeriv, toReal
-/
lemma integrable_klFun_rnDeriv_iff (hμν : μ ≪ ν) :
    Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by
  suffices Integrable (fun x => (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert! this using 3 with x
    rw [klFun]; rw [add_sub_assoc]
  rw [integrable_add_iff_integrable_left']; rw [integrable_rnDeriv_mul_log_iff hμν]
  fun_prop

/--
lemma `integral_klFun_rnDeriv` / 引理 `integral_klFun_rnDeriv`

English:
lemma integral_klFun_rnDeriv
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  unfold klFun
  rw [integral_sub]; rw [integral_add]; rw [integral_const]; rw [Measure.integral_toReal_rnDeriv hμν]; rw [smul_eq_mul]; rw [mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop
  · refine Integrable.add ?_ (integrable_c

中文:
引理 integral_klFun_rnDeriv
  条件: (hμν : μ ≪ ν) (h_int : 整数egrable (llr μ ν) μ)
  证明: by
  unfold klFun
  rw [integral_sub]; rw [integral_add]; rw [integral_const]; rw [Measure.integral_toReal_rnDeriv hμν]; rw [smul_eq_mul]; rw [mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop
  · refine Integrable.add ?_ (integrable_c

Depends on / 依赖: Integrable, Integrable.add, Measure, Measure.integral_toReal_rnDeriv, fun_prop, integrable_const, integrable_rnDeriv_mul_log_iff, integral_add, integral_const, integral_rnDeriv_smul, integral_sub, integral_toReal_rnDeriv, mul_one, smul_eq_mul
-/
lemma integral_klFun_rnDeriv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  unfold klFun
  rw [integral_sub]; rw [integral_add]; rw [integral_const]; rw [Measure.integral_toReal_rnDeriv hμν]; rw [smul_eq_mul]; rw [mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · fun_prop

end Integral

end InformationTheory
