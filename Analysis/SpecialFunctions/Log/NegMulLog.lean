/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.Deriv

/-!
# The functions `x ↦ x * log x` and `x ↦ - x * log x`

The purpose of this file is to record basic analytic properties of
- `x ↦ x * log x`, called `mul_log` in theorem statements
- `x ↦ - x * log x`, named `negMulLog`, which is notably used in the theory of Shannon entropy.

## Main definitions

* `negMulLog`: the function `x ↦ - x * log x` from `ℝ` to `ℝ`.

-/

@[expose] public section

open scoped Topology

namespace Real

section mulLog

/--
lemma `self_sub_one_lt_mul_log` / 引理 `self_sub_one_lt_mul_log`

English:
lemma self_sub_one_lt_mul_log
  given: {x : Real} (h0 : 0 <= x) (h1 : x != 1)
  statement: x - 1 < x * x.log
  proof: by
  by_cases hx_pos : 0 < x
  · nlinarith [Real.log_inv x, Real.log_lt_sub_one_of_pos (inv_pos.mpr hx_pos) (by aesop),
      mul_inv_cancel₀ hx_pos.ne']
  · cases lt_or_eq_of_le h0 <;> aesop

中文:
引理 self_sub_one_lt_mul_log
  条件: {x : 实数} (h0 : 0 <= x) (h1 : x != 1)
  结论: x - 1 < x * x.log
  证明: by
  by_cases hx_pos : 0 < x
  · nlinarith [Real.log_inv x, Real.log_lt_sub_one_of_pos (inv_pos.mpr hx_pos) (by aesop),
      mul_inv_cancel₀ hx_pos.ne']
  · cases lt_or_eq_of_le h0 <;> aesop

Depends on / 依赖: Real.log_inv, Real.log_lt_sub_one_of_pos, hx_pos, hx_pos.ne, inv_pos, inv_pos.mpr, log_inv, log_lt_sub_one_of_pos, lt_or_eq_of_le
-/
lemma self_sub_one_lt_mul_log {x : Real} (h0 : 0 <= x) (h1 : x != 1) : x - 1 < x * x.log := by
  by_cases hx_pos : 0 < x
  · nlinarith [Real.log_inv x, Real.log_lt_sub_one_of_pos (inv_pos.mpr hx_pos) (by aesop),
      mul_inv_cancel₀ hx_pos.ne']
  · cases lt_or_eq_of_le h0 <;> aesop

/--
lemma `self_sub_one_le_mul_log` / 引理 `self_sub_one_le_mul_log`

English:
lemma self_sub_one_le_mul_log
  given: {x : Real} (h0 : 0 <= x)
  statement: x - 1 <= x * x.log
  proof: by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (self_sub_one_lt_mul_log h0 h1)

@[fun_prop]

中文:
引理 self_sub_one_le_mul_log
  条件: {x : 实数} (h0 : 0 <= x)
  结论: x - 1 <= x * x.log
  证明: by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (self_sub_one_lt_mul_log h0 h1)

@[fun_prop]

Depends on / 依赖: eq_or_ne, le_of_lt, self_sub_one_lt_mul_log
-/
lemma self_sub_one_le_mul_log {x : Real} (h0 : 0 <= x) : x - 1 <= x * x.log := by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (self_sub_one_lt_mul_log h0 h1)

@[fun_prop]
/--
lemma `continuous_mul_log` / 引理 `continuous_mul_log`

English:
lemma continuous_mul_log
  statement: Continuous fun x => x * log x
  proof: by
  rw [continuous_iff_continuousAt]
  intro x
  obtain hx | rfl := ne_or_eq x 0
  · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [ContinuousAt]; rw [zero_mul]
  simp_rw [mul_comm _ (log _)]
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set Real) = Set.Iio 0 union S

中文:
引理 continuous_mul_log
  结论: 连续 fun x => x * log x
  证明: by
  rw [continuous_iff_continuousAt]
  intro x
  obtain hx | rfl := ne_or_eq x 0
  · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [ContinuousAt]; rw [zero_mul]
  simp_rw [mul_comm _ (log _)]
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set Real) = Set.Iio 0 union S

Depends on / 依赖: ContinuousAt, Filter, Filter.tendsto_sup, Set.Iio, Set.Ioi, Set.univ, continuousAt, continuousAt_log, continuous_id, continuous_iff_continuousAt, mul_comm, ne_or_eq, nhdsWithin_singleton, nhdsWithin_union, nhdsWithin_univ, nth_rewrite, simp_rw, tendsto_log_mul_self_nhdsLT_zero, tendsto_sup, zero_mul
-/
lemma continuous_mul_log : Continuous fun x => x * log x := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain hx | rfl := ne_or_eq x 0
  · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [ContinuousAt]; rw [zero_mul]
  simp_rw [mul_comm _ (log _)]
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set Real) = Set.Iio 0 union Set.Ioi 0 union {0} := by ext; simp [em]
  rw [this]; rw [nhdsWithin_union]; rw [nhdsWithin_union]
  simp only [nhdsWithin_singleton, Filter.tendsto_sup]
  refine ⟨⟨tendsto_log_mul_self_nhdsLT_zero, ?_⟩, ?_⟩
  · simpa only [rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  · convert! tendsto_pure_nhds (fun x => log x * x) 0
    simp

@[fun_prop]
/--
lemma `Continuous.mul_log` / 引理 `Continuous.mul_log`

English:
lemma Continuous.mul_log
  given: {α : Type*} [TopologicalSpace α] {f : α -> Real} (hf : Continuous f)
  proof: continuous_mul_log.comp hf

中文:
引理 连续.mul_log
  条件: {α : 类型} [拓扑空间 α] {f : α -> 实数} (hf : 连续 f)
  证明: continuous_mul_log.comp hf

Depends on / 依赖: continuous_mul_log, continuous_mul_log.comp
-/
lemma Continuous.mul_log {α : Type*} [TopologicalSpace α] {f : α -> Real} (hf : Continuous f) :
    Continuous fun a => f a * log (f a) := continuous_mul_log.comp hf

/--
lemma `differentiableOn_mul_log` / 引理 `differentiableOn_mul_log`

English:
lemma differentiableOn_mul_log
  statement: DifferentiableOn Real (fun x => x * log x) {0}ᶜ
  proof: differentiable_id.differentiableOn.mul differentiableOn_log

中文:
引理 differentiableOn_mul_log
  结论: DifferentiableOn 实数 (fun x => x * log x) {0}ᶜ
  证明: differentiable_id.differentiableOn.mul differentiableOn_log

Depends on / 依赖: differentiableOn, differentiableOn_log, differentiable_id, differentiable_id.differentiableOn.mul
-/
lemma differentiableOn_mul_log : DifferentiableOn Real (fun x => x * log x) {0}ᶜ :=
  differentiable_id.differentiableOn.mul differentiableOn_log

/--
lemma `deriv_mul_log` / 引理 `deriv_mul_log`

English:
lemma deriv_mul_log
  given: {x : Real} (hx : x != 0)
  statement: deriv (fun x => x * log x) x = log x + 1
  proof: by
  simp [hx]

中文:
引理 deriv_mul_log
  条件: {x : 实数} (hx : x != 0)
  结论: deriv (fun x => x * log x) x = log x + 1
  证明: by
  simp [hx]
-/
lemma deriv_mul_log {x : Real} (hx : x != 0) : deriv (fun x => x * log x) x = log x + 1 := by
  simp [hx]

/--
lemma `hasDerivAt_mul_log` / 引理 `hasDerivAt_mul_log`

English:
lemma hasDerivAt_mul_log
  given: {x : Real} (hx : x != 0)
  statement: HasDerivAt (fun x => x * log x) (log x + 1) x
  proof: by
  rw [← deriv_mul_log hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_mul_log ?_
  simp [hx]

@[simp]

中文:
引理 hasDerivAt_mul_log
  条件: {x : 实数} (hx : x != 0)
  结论: 在点处可导 (fun x => x * log x) (log x + 1) x
  证明: by
  rw [← deriv_mul_log hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_mul_log ?_
  simp [hx]

@[simp]

Depends on / 依赖: DifferentiableOn, DifferentiableOn.differentiableAt, deriv_mul_log, differentiableAt, differentiableOn_mul_log, hasDerivAt_deriv_iff
-/
lemma hasDerivAt_mul_log {x : Real} (hx : x != 0) : HasDerivAt (fun x => x * log x) (log x + 1) x := by
  rw [← deriv_mul_log hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_mul_log ?_
  simp [hx]

@[simp]
/--
lemma `rightDeriv_mul_log` / 引理 `rightDeriv_mul_log`

English:
lemma rightDeriv_mul_log
  given: {x : Real} (hx : x != 0)
  proof: (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]

中文:
引理 rightDeriv_mul_log
  条件: {x : 实数} (hx : x != 0)
  证明: (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]

Depends on / 依赖: derivWithin, hasDerivAt_mul_log, hasDerivWithinAt, hasDerivWithinAt.derivWithin, uniqueDiffWithinAt_Ioi
-/
lemma rightDeriv_mul_log {x : Real} (hx : x != 0) :
    derivWithin (fun x => x * log x) (Set.Ioi x) x = log x + 1 :=
  (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]
/--
lemma `leftDeriv_mul_log` / 引理 `leftDeriv_mul_log`

English:
lemma leftDeriv_mul_log
  given: {x : Real} (hx : x != 0)
  proof: (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

中文:
引理 leftDeriv_mul_log
  条件: {x : 实数} (hx : x != 0)
  证明: (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

Depends on / 依赖: derivWithin, hasDerivAt_mul_log, hasDerivWithinAt, hasDerivWithinAt.derivWithin, uniqueDiffWithinAt_Iio
-/
lemma leftDeriv_mul_log {x : Real} (hx : x != 0) :
    derivWithin (fun x => x * log x) (Set.Iio x) x = log x + 1 :=
  (hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

open Filter in
/--
lemma `tendsto_deriv_mul_log_nhdsWithin_zero` / 引理 `tendsto_deriv_mul_log_nhdsWithin_zero`

English:
lemma tendsto_deriv_mul_log_nhdsWithin_zero
  proof: by
  have : (deriv (fun x => x * log x)) =ᶠ[𝓝[>] 0] (fun x => log x + 1) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    rw [Set.mem_Ioi] at hx
    exact deriv_mul_log hx.ne'
  simp only [tendsto_congr' this, tendsto_atBot_add_const_right, tendsto_log_nhdsGT_zero]

中文:
引理 tendsto_deriv_mul_log_nhdsWithin_zero
  证明: by
  have : (deriv (fun x => x * log x)) =ᶠ[𝓝[>] 0] (fun x => log x + 1) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    rw [Set.mem_Ioi] at hx
    exact deriv_mul_log hx.ne'
  simp only [tendsto_congr' this, tendsto_atBot_add_const_right, tendsto_log_nhdsGT_zero]
-/
private lemma tendsto_deriv_mul_log_nhdsWithin_zero :
    Tendsto (deriv (fun x => x * log x)) (𝓝[>] 0) atBot := by
  have : (deriv (fun x => x * log x)) =ᶠ[𝓝[>] 0] (fun x => log x + 1) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    rw [Set.mem_Ioi] at hx
    exact deriv_mul_log hx.ne'
  simp only [tendsto_congr' this, tendsto_atBot_add_const_right, tendsto_log_nhdsGT_zero]

open Filter in
/--
lemma `tendsto_deriv_mul_log_atTop` / 引理 `tendsto_deriv_mul_log_atTop`

English:
lemma tendsto_deriv_mul_log_atTop
  proof: by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => deriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

中文:
引理 tendsto_deriv_mul_log_atTop
  证明: by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => deriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

Depends on / 依赖: EventuallyEq, atTop_add, deriv_mul_log, eventually_atTop, tendsto_congr, tendsto_const_nhds, tendsto_log_atTop, tendsto_log_atTop.atTop_add, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma tendsto_deriv_mul_log_atTop :
    Tendsto (fun x => deriv (fun x => x * log x) x) atTop atTop := by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => deriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

open Filter in
/--
lemma `tendsto_rightDeriv_mul_log_atTop` / 引理 `tendsto_rightDeriv_mul_log_atTop`

English:
lemma tendsto_rightDeriv_mul_log_atTop
  proof: by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

中文:
引理 tendsto_rightDeriv_mul_log_atTop
  证明: by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

Depends on / 依赖: EventuallyEq, atTop_add, eventually_atTop, rightDeriv_mul_log, tendsto_congr, tendsto_const_nhds, tendsto_log_atTop, tendsto_log_atTop.atTop_add, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma tendsto_rightDeriv_mul_log_atTop :
    Tendsto (fun x => derivWithin (fun x => x * log x) (Set.Ioi x) x) atTop atTop := by
  refine (tendsto_congr' ?_).mpr (tendsto_log_atTop.atTop_add (tendsto_const_nhds (x := 1)))
  rw [EventuallyEq]; rw [eventually_atTop]
  exact ⟨1, fun _ hx => rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

/--
lemma `not_DifferentiableAt_log_mul_zero` / 引理 `not_DifferentiableAt_log_mul_zero`

English:
lemma not_DifferentiableAt_log_mul_zero
  proof: fun h =>
  (not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (fun x : Real => x * log x) (a := 0))
    tendsto_deriv_mul_log_nhdsWithin_zero
    (h.differentiableWithinAt (s := Set.Ioi 0))

中文:
引理 not_DifferentiableAt_log_mul_zero
  证明: fun h =>
  (not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (fun x : Real => x * log x) (a := 0))
    tendsto_deriv_mul_log_nhdsWithin_zero
    (h.differentiableWithinAt (s := Set.Ioi 0))
-/
lemma not_DifferentiableAt_log_mul_zero :
    ¬ DifferentiableAt Real (fun x => x * log x) 0 := fun h =>
  (not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (fun x : Real => x * log x) (a := 0))
    tendsto_deriv_mul_log_nhdsWithin_zero
    (h.differentiableWithinAt (s := Set.Ioi 0))

/--
lemma `deriv_mul_log_zero` / 引理 `deriv_mul_log_zero`

English:
lemma deriv_mul_log_zero
  statement: deriv (fun x => x * log x) 0 = 0
  proof: deriv_zero_of_not_differentiableAt not_DifferentiableAt_log_mul_zero

中文:
引理 deriv_mul_log_zero
  结论: deriv (fun x => x * log x) 0 = 0
  证明: deriv_zero_of_not_differentiableAt not_DifferentiableAt_log_mul_zero

Depends on / 依赖: deriv_zero_of_not_differentiableAt, not_DifferentiableAt_log_mul_zero
-/
lemma deriv_mul_log_zero : deriv (fun x => x * log x) 0 = 0 :=
  deriv_zero_of_not_differentiableAt not_DifferentiableAt_log_mul_zero

/--
lemma `not_continuousAt_deriv_mul_log_zero` / 引理 `not_continuousAt_deriv_mul_log_zero`

English:
lemma not_continuousAt_deriv_mul_log_zero
  proof: not_continuousAt_of_tendsto tendsto_deriv_mul_log_nhdsWithin_zero nhdsWithin_le_nhds (by simp)

中文:
引理 not_continuousAt_deriv_mul_log_zero
  证明: not_continuousAt_of_tendsto tendsto_deriv_mul_log_nhdsWithin_zero nhdsWithin_le_nhds (by simp)

Depends on / 依赖: nhdsWithin_le_nhds, not_continuousAt_of_tendsto, tendsto_deriv_mul_log_nhdsWithin_zero
-/
lemma not_continuousAt_deriv_mul_log_zero :
    ¬ ContinuousAt (deriv (fun (x : Real) => x * log x)) 0 :=
  not_continuousAt_of_tendsto tendsto_deriv_mul_log_nhdsWithin_zero nhdsWithin_le_nhds (by simp)

/--
lemma `deriv2_mul_log` / 引理 `deriv2_mul_log`

English:
lemma deriv2_mul_log
  given: (x : Real)
  statement: deriv^[2] (fun x => x * log x) x = x⁻¹
  proof: by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases hx : x = 0
  · rw [hx, inv_zero]
    exact deriv_zero_of_not_differentiableAt
      (fun h => not_continuousAt_deriv_mul_log_zero h.continuousAt)
  · suffices forallᶠ y in (𝓝 x), deriv (fu

中文:
引理 deriv2_mul_log
  条件: (x : 实数)
  结论: deriv^[2] (fun x => x * log x) x = x⁻¹
  证明: by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases hx : x = 0
  · rw [hx, inv_zero]
    exact deriv_zero_of_not_differentiableAt
      (fun h => not_continuousAt_deriv_mul_log_zero h.continuousAt)
  · suffices forallᶠ y in (𝓝 x), deriv (fu

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.deriv_eq, Function, Function.comp_apply, Function.id_comp, Function.iterate_succ, Function.iterate_zero, comp_apply, continuousAt, deriv_add_const, deriv_eq, deriv_log, deriv_mul_log, deriv_zero_of_not_differentiableAt, eventually_ne_nhds, filter_upwards, h.continuousAt, id_comp, inv_zero
-/
lemma deriv2_mul_log (x : Real) : deriv^[2] (fun x => x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases hx : x = 0
  · rw [hx, inv_zero]
    exact deriv_zero_of_not_differentiableAt
      (fun h => not_continuousAt_deriv_mul_log_zero h.continuousAt)
  · suffices forallᶠ y in (𝓝 x), deriv (fun x => x * log x) y = log y + 1 by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_add_const]; rw [deriv_log x]
    filter_upwards [eventually_ne_nhds hx] with y hy using deriv_mul_log hy

/--
lemma `strictConvexOn_mul_log` / 引理 `strictConvexOn_mul_log`

English:
lemma strictConvexOn_mul_log
  statement: StrictConvexOn Real (Set.Ici (0 : Real)) (fun x => x * log x)
  proof: by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log]
  positivity

中文:
引理 strictConvexOn_mul_log
  结论: StrictConvexOn 实数 (集合.左闭右无界区间 (0 : 实数)) (fun x => x * log x)
  证明: by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log]
  positivity

Depends on / 依赖: Set.mem_Ioi, Set.nonempty_Iio, continuousOn, continuous_mul_log, continuous_mul_log.continuousOn, convex_Ici, deriv2_mul_log, interior_Ici, mem_Ioi, nonempty_Iio, strictConvexOn_of_deriv2_pos
-/
lemma strictConvexOn_mul_log : StrictConvexOn Real (Set.Ici (0 : Real)) (fun x => x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log]
  positivity

/--
lemma `convexOn_mul_log` / 引理 `convexOn_mul_log`

English:
lemma convexOn_mul_log
  statement: ConvexOn Real (Set.Ici (0 : Real)) (fun x => x * log x)
  proof: strictConvexOn_mul_log.convexOn

中文:
引理 convexOn_mul_log
  结论: ConvexOn 实数 (集合.左闭右无界区间 (0 : 实数)) (fun x => x * log x)
  证明: strictConvexOn_mul_log.convexOn

Depends on / 依赖: convexOn, strictConvexOn_mul_log, strictConvexOn_mul_log.convexOn
-/
lemma convexOn_mul_log : ConvexOn Real (Set.Ici (0 : Real)) (fun x => x * log x) :=
  strictConvexOn_mul_log.convexOn

/--
lemma `mul_log_nonneg` / 引理 `mul_log_nonneg`

English:
lemma mul_log_nonneg
  given: {x : Real} (hx : 1 <= x)
  statement: 0 <= x * log x
  proof: mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

中文:
引理 mul_log_nonneg
  条件: {x : 实数} (hx : 1 <= x)
  结论: 0 <= x * log x
  证明: mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

Depends on / 依赖: log_nonneg, mul_nonneg, zero_le_one, zero_le_one.trans
-/
lemma mul_log_nonneg {x : Real} (hx : 1 <= x) : 0 <= x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

/--
lemma `mul_log_pos` / 引理 `mul_log_pos`

English:
lemma mul_log_pos
  given: {x : Real} (hx : 1 < x)
  statement: 0 < x * log x
  proof: mul_pos (zero_lt_one.trans hx) (log_pos hx)

中文:
引理 mul_log_pos
  条件: {x : 实数} (hx : 1 < x)
  结论: 0 < x * log x
  证明: mul_pos (zero_lt_one.trans hx) (log_pos hx)

Depends on / 依赖: log_pos, mul_pos, zero_lt_one, zero_lt_one.trans
-/
lemma mul_log_pos {x : Real} (hx : 1 < x) : 0 < x * log x :=
  mul_pos (zero_lt_one.trans hx) (log_pos hx)

/--
lemma `mul_log_nonpos` / 引理 `mul_log_nonpos`

English:
lemma mul_log_nonpos
  given: {x : Real} (hx₀ : 0 <= x) (hx₁ : x <= 1)
  statement: x * log x <= 0
  proof: mul_nonpos_of_nonneg_of_nonpos hx₀ (log_nonpos hx₀ hx₁)

中文:
引理 mul_log_nonpos
  条件: {x : 实数} (hx₀ : 0 <= x) (hx₁ : x <= 1)
  结论: x * log x <= 0
  证明: mul_nonpos_of_nonneg_of_nonpos hx₀ (log_nonpos hx₀ hx₁)

Depends on / 依赖: log_nonpos, mul_nonpos_of_nonneg_of_nonpos
-/
lemma mul_log_nonpos {x : Real} (hx₀ : 0 <= x) (hx₁ : x <= 1) : x * log x <= 0 :=
  mul_nonpos_of_nonneg_of_nonpos hx₀ (log_nonpos hx₀ hx₁)

/--
lemma `mul_log_neg` / 引理 `mul_log_neg`

English:
lemma mul_log_neg
  given: {x : Real} (hx₀ : 0 < x) (hx₁ : x < 1)
  statement: x * log x < 0
  proof: mul_neg_of_pos_of_neg hx₀ (log_neg hx₀ hx₁)

中文:
引理 mul_log_neg
  条件: {x : 实数} (hx₀ : 0 < x) (hx₁ : x < 1)
  结论: x * log x < 0
  证明: mul_neg_of_pos_of_neg hx₀ (log_neg hx₀ hx₁)

Depends on / 依赖: log_neg, mul_neg_of_pos_of_neg
-/
lemma mul_log_neg {x : Real} (hx₀ : 0 < x) (hx₁ : x < 1) : x * log x < 0 :=
    mul_neg_of_pos_of_neg hx₀ (log_neg hx₀ hx₁)

end mulLog

section negMulLog

/--
Definition of `negMulLog` / `negMulLog` 的定义

English:
definition negMulLog
  signature: (x : Real)
  body: - x * log x

中文:
定义 negMulLog
  签名: (x : 实数)
  定义体: - x * log x
-/
noncomputable def negMulLog (x : Real) : Real := - x * log x

/--
lemma `negMulLog_def` / 引理 `negMulLog_def`

English:
lemma negMulLog_def
  statement: negMulLog = fun x => - x * log x
  proof: rfl

中文:
引理 negMulLog_def
  结论: negMulLog = fun x => - x * log x
  证明: rfl
-/
lemma negMulLog_def : negMulLog = fun x => - x * log x := rfl

/--
lemma `negMulLog_eq_neg` / 引理 `negMulLog_eq_neg`

English:
lemma negMulLog_eq_neg
  statement: negMulLog = fun x => -(x * log x)
  proof: by simp [negMulLog_def]

中文:
引理 negMulLog_eq_neg
  结论: negMulLog = fun x => -(x * log x)
  证明: by simp [negMulLog_def]

Depends on / 依赖: negMulLog_def
-/
lemma negMulLog_eq_neg : negMulLog = fun x => -(x * log x) := by simp [negMulLog_def]

/--
lemma `negMulLog_zero` / 引理 `negMulLog_zero`

English:
lemma negMulLog_zero
  statement: negMulLog (0 : Real) = 0
  proof: by simp [negMulLog]

中文:
引理 negMulLog_zero
  结论: negMulLog (0 : 实数) = 0
  证明: by simp [negMulLog]
-/
@[simp] lemma negMulLog_zero : negMulLog (0 : Real) = 0 := by simp [negMulLog]

/--
lemma `negMulLog_one` / 引理 `negMulLog_one`

English:
lemma negMulLog_one
  statement: negMulLog (1 : Real) = 0
  proof: by simp [negMulLog]

中文:
引理 negMulLog_one
  结论: negMulLog (1 : 实数) = 0
  证明: by simp [negMulLog]
-/
@[simp] lemma negMulLog_one : negMulLog (1 : Real) = 0 := by simp [negMulLog]

/--
lemma `negMulLog_nonneg` / 引理 `negMulLog_nonneg`

English:
lemma negMulLog_nonneg
  given: {x : Real} (h1 : 0 <= x) (h2 : x <= 1)
  statement: 0 <= negMulLog x
  proof: by
  simpa only [negMulLog_eq_neg, neg_nonneg] using mul_log_nonpos h1 h2

中文:
引理 negMulLog_nonneg
  条件: {x : 实数} (h1 : 0 <= x) (h2 : x <= 1)
  结论: 0 <= negMulLog x
  证明: by
  simpa only [negMulLog_eq_neg, neg_nonneg] using mul_log_nonpos h1 h2

Depends on / 依赖: mul_log_nonpos, negMulLog_eq_neg, neg_nonneg
-/
lemma negMulLog_nonneg {x : Real} (h1 : 0 <= x) (h2 : x <= 1) : 0 <= negMulLog x := by
  simpa only [negMulLog_eq_neg, neg_nonneg] using mul_log_nonpos h1 h2

/--
lemma `negMulLog_mul` / 引理 `negMulLog_mul`

English:
lemma negMulLog_mul
  given: (x y : Real)
  statement: negMulLog (x * y) = y * negMulLog x + x * negMulLog y
  proof: by
  simp only [negMulLog, neg_mul]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring

中文:
引理 negMulLog_mul
  条件: (x y : 实数)
  结论: negMulLog (x * y) = y * negMulLog x + x * negMulLog y
  证明: by
  simp only [negMulLog, neg_mul]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring

Depends on / 依赖: log_mul, negMulLog, neg_mul
-/
lemma negMulLog_mul (x y : Real) : negMulLog (x * y) = y * negMulLog x + x * negMulLog y := by
  simp only [negMulLog, neg_mul]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring

/--
lemma `continuous_negMulLog` / 引理 `continuous_negMulLog`

English:
lemma continuous_negMulLog
  statement: Continuous negMulLog
  proof: by
  simpa only [negMulLog_eq_neg] using continuous_mul_log.fun_neg

中文:
引理 continuous_negMulLog
  结论: 连续 negMulLog
  证明: by
  simpa only [negMulLog_eq_neg] using continuous_mul_log.fun_neg
-/
@[fun_prop] lemma continuous_negMulLog : Continuous negMulLog := by
  simpa only [negMulLog_eq_neg] using continuous_mul_log.fun_neg

/--
lemma `differentiableOn_negMulLog` / 引理 `differentiableOn_negMulLog`

English:
lemma differentiableOn_negMulLog
  statement: DifferentiableOn Real negMulLog {0}ᶜ
  proof: by
  simpa only [negMulLog_eq_neg] using! differentiableOn_mul_log.neg

中文:
引理 differentiableOn_negMulLog
  结论: DifferentiableOn 实数 negMulLog {0}ᶜ
  证明: by
  simpa only [negMulLog_eq_neg] using! differentiableOn_mul_log.neg

Depends on / 依赖: differentiableOn_mul_log, differentiableOn_mul_log.neg, negMulLog_eq_neg
-/
lemma differentiableOn_negMulLog : DifferentiableOn Real negMulLog {0}ᶜ := by
  simpa only [negMulLog_eq_neg] using! differentiableOn_mul_log.neg

/--
lemma `differentiableAt_negMulLog_iff` / 引理 `differentiableAt_negMulLog_iff`

English:
lemma differentiableAt_negMulLog_iff
  given: {x : Real}
  statement: DifferentiableAt Real negMulLog x ↔ x != 0
  proof: by
  constructor
  · unfold negMulLog
    intro h eq0
    simp only [neg_mul, differentiableAt_fun_neg_iff, eq0] at h
    exact not_DifferentiableAt_log_mul_zero h
  · intro hx
    have : x in ({0} : Set Real)ᶜ := by
      simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_

中文:
引理 differentiableAt_negMulLog_iff
  条件: {x : 实数}
  结论: DifferentiableAt 实数 negMulLog x ↔ x != 0
  证明: by
  constructor
  · unfold negMulLog
    intro h eq0
    simp only [neg_mul, differentiableAt_fun_neg_iff, eq0] at h
    exact not_DifferentiableAt_log_mul_zero h
  · intro hx
    have : x in ({0} : Set Real)ᶜ := by
      simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.differentiableAt, Set.mem_compl_iff, Set.mem_singleton_iff, compl_singleton_mem_nhds_iff, differentiableAt, differentiableAt_fun_neg_iff, differentiableOn_negMulLog, mem_compl_iff, mem_singleton_iff, ne_eq, negMulLog, neg_mul, not_DifferentiableAt_log_mul_zero, not_false_eq_true
-/
lemma differentiableAt_negMulLog_iff {x : Real} : DifferentiableAt Real negMulLog x ↔ x != 0 := by
  constructor
  · unfold negMulLog
    intro h eq0
    simp only [neg_mul, differentiableAt_fun_neg_iff, eq0] at h
    exact not_DifferentiableAt_log_mul_zero h
  · intro hx
    have : x in ({0} : Set Real)ᶜ := by
      simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true]
    have := differentiableOn_negMulLog x this
    apply DifferentiableWithinAt.differentiableAt (s := {0}ᶜ) <;>
    simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true,
      compl_singleton_mem_nhds_iff]

@[fun_prop] alias ⟨_, differentiableAt_negMulLog⟩ := differentiableAt_negMulLog_iff

/--
lemma `deriv_negMulLog` / 引理 `deriv_negMulLog`

English:
lemma deriv_negMulLog
  given: {x : Real} (hx : x != 0)
  statement: deriv negMulLog x = - log x - 1
  proof: by
  rw [negMulLog_eq_neg]; rw [deriv.fun_neg]; rw [deriv_mul_log hx]
  ring

中文:
引理 deriv_negMulLog
  条件: {x : 实数} (hx : x != 0)
  结论: deriv negMulLog x = - log x - 1
  证明: by
  rw [negMulLog_eq_neg]; rw [deriv.fun_neg]; rw [deriv_mul_log hx]
  ring

Depends on / 依赖: deriv.fun_neg, deriv_mul_log, fun_neg, negMulLog_eq_neg
-/
lemma deriv_negMulLog {x : Real} (hx : x != 0) : deriv negMulLog x = - log x - 1 := by
  rw [negMulLog_eq_neg]; rw [deriv.fun_neg]; rw [deriv_mul_log hx]
  ring

/--
lemma `hasDerivAt_negMulLog` / 引理 `hasDerivAt_negMulLog`

English:
lemma hasDerivAt_negMulLog
  given: {x : Real} (hx : x != 0)
  statement: HasDerivAt negMulLog (- log x - 1) x
  proof: by
  rw [← deriv_negMulLog hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]

中文:
引理 hasDerivAt_negMulLog
  条件: {x : 实数} (hx : x != 0)
  结论: 在点处可导 negMulLog (- log x - 1) x
  证明: by
  rw [← deriv_negMulLog hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]

Depends on / 依赖: DifferentiableOn, DifferentiableOn.differentiableAt, deriv_negMulLog, differentiableAt, differentiableOn_negMulLog, hasDerivAt_deriv_iff
-/
lemma hasDerivAt_negMulLog {x : Real} (hx : x != 0) : HasDerivAt negMulLog (- log x - 1) x := by
  rw [← deriv_negMulLog hx]; rw [hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]

/--
lemma `deriv2_negMulLog` / 引理 `deriv2_negMulLog`

English:
lemma deriv2_negMulLog
  given: (x : Real)
  statement: deriv^[2] negMulLog x = -x⁻¹
  proof: by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, deriv.fun_neg',
    Function.comp_apply] at h ⊢
  rw [h]

中文:
引理 deriv2_negMulLog
  条件: (x : 实数)
  结论: deriv^[2] negMulLog x = -x⁻¹
  证明: by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, deriv.fun_neg',
    Function.comp_apply] at h ⊢
  rw [h]

Depends on / 依赖: Function, Function.comp_apply, Function.id_comp, Function.iterate_succ, Function.iterate_zero, comp_apply, deriv.fun_neg, deriv2_mul_log, fun_neg, id_comp, iterate_succ, iterate_zero, negMulLog_eq_neg
-/
lemma deriv2_negMulLog (x : Real) : deriv^[2] negMulLog x = -x⁻¹ := by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, deriv.fun_neg',
    Function.comp_apply] at h ⊢
  rw [h]

/--
lemma `strictConcaveOn_negMulLog` / 引理 `strictConcaveOn_negMulLog`

English:
lemma strictConcaveOn_negMulLog
  statement: StrictConcaveOn Real (Set.Ici (0 : Real)) negMulLog
  proof: by
  simpa only [negMulLog_eq_neg] using! strictConvexOn_mul_log.neg

中文:
引理 strictConcaveOn_negMulLog
  结论: StrictConcaveOn 实数 (集合.左闭右无界区间 (0 : 实数)) negMulLog
  证明: by
  simpa only [negMulLog_eq_neg] using! strictConvexOn_mul_log.neg

Depends on / 依赖: negMulLog_eq_neg, strictConvexOn_mul_log, strictConvexOn_mul_log.neg
-/
lemma strictConcaveOn_negMulLog : StrictConcaveOn Real (Set.Ici (0 : Real)) negMulLog := by
  simpa only [negMulLog_eq_neg] using! strictConvexOn_mul_log.neg

/--
lemma `concaveOn_negMulLog` / 引理 `concaveOn_negMulLog`

English:
lemma concaveOn_negMulLog
  statement: ConcaveOn Real (Set.Ici (0 : Real)) negMulLog
  proof: strictConcaveOn_negMulLog.concaveOn

中文:
引理 concaveOn_negMulLog
  结论: ConcaveOn 实数 (集合.左闭右无界区间 (0 : 实数)) negMulLog
  证明: strictConcaveOn_negMulLog.concaveOn

Depends on / 依赖: concaveOn, strictConcaveOn_negMulLog, strictConcaveOn_negMulLog.concaveOn
-/
lemma concaveOn_negMulLog : ConcaveOn Real (Set.Ici (0 : Real)) negMulLog :=
  strictConcaveOn_negMulLog.concaveOn

/--
lemma `negMulLog_lt_one_sub_self` / 引理 `negMulLog_lt_one_sub_self`

English:
lemma negMulLog_lt_one_sub_self
  given: {x : Real} (h0 : 0 <= x) (h1 : x != 1)
  statement: x.negMulLog < 1 - x
  proof: by
  unfold negMulLog
  linarith [self_sub_one_lt_mul_log h0 h1]

中文:
引理 negMulLog_lt_one_sub_self
  条件: {x : 实数} (h0 : 0 <= x) (h1 : x != 1)
  结论: x.negMulLog < 1 - x
  证明: by
  unfold negMulLog
  linarith [self_sub_one_lt_mul_log h0 h1]

Depends on / 依赖: negMulLog, self_sub_one_lt_mul_log
-/
lemma negMulLog_lt_one_sub_self {x : Real} (h0 : 0 <= x) (h1 : x != 1) : x.negMulLog < 1 - x := by
  unfold negMulLog
  linarith [self_sub_one_lt_mul_log h0 h1]

/--
lemma `negMulLog_le_one_sub_self` / 引理 `negMulLog_le_one_sub_self`

English:
lemma negMulLog_le_one_sub_self
  given: {x : Real} (h0 : 0 <= x)
  statement: x.negMulLog <= 1 - x
  proof: by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (negMulLog_lt_one_sub_self h0 h1)

中文:
引理 negMulLog_le_one_sub_self
  条件: {x : 实数} (h0 : 0 <= x)
  结论: x.negMulLog <= 1 - x
  证明: by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (negMulLog_lt_one_sub_self h0 h1)

Depends on / 依赖: eq_or_ne, le_of_lt, negMulLog_lt_one_sub_self
-/
lemma negMulLog_le_one_sub_self {x : Real} (h0 : 0 <= x) : x.negMulLog <= 1 - x :=by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  · exact le_of_lt (negMulLog_lt_one_sub_self h0 h1)

end negMulLog

end Real
