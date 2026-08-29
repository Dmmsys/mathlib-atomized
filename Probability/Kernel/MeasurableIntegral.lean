/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Measurability of the integral against a kernel

The Bochner integral of a strongly measurable function against a kernel is strongly measurable.

## Main statements

* `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right`: the function
  `a ↦ ∫ b, f a b ∂(κ a)` is measurable, for an s-finite kernel `κ : Kernel α β` and a function
  `f : α → β → E` such that `uncurry f` is measurable.

-/

public section


open MeasureTheory ProbabilityTheory Function Set Filter

open scoped MeasureTheory ENNReal Topology

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : Kernel α β} {η : Kernel β γ} {a : α} {E : Type*} [NormedAddCommGroup E]

/--
theorem `ProbabilityTheory.measurableSet_integrable` / 定理 `ProbabilityTheory.measurableSet_integrable`

English:
theorem ProbabilityTheory.measurableSet_integrable
  given: ⦃f
  statement: β -> E⦄ (hf : StronglyMeasurable f) :
  proof: by
  simp_rw [Integrable, hf.aestronglyMeasurable, true_and]
  exact measurableSet_lt hf.enorm.lintegral_kernel measurable_const

中文:
定理 ProbabilityTheory.measurableSet_integrable
  条件: ⦃f
  结论: β -> E⦄ (hf : StronglyMeasurable f) :
  证明: by
  simp_rw [Integrable, hf.aestronglyMeasurable, true_and]
  exact measurableSet_lt hf.enorm.lintegral_kernel measurable_const

Depends on / 依赖: Integrable, aestronglyMeasurable, hf.aestronglyMeasurable, hf.enorm.lintegral_kernel, lintegral_kernel, measurableSet_lt, measurable_const, simp_rw, true_and
-/
theorem ProbabilityTheory.measurableSet_integrable ⦃f : β -> E⦄ (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable f (κ a)} := by
  simp_rw [Integrable, hf.aestronglyMeasurable, true_and]
  exact measurableSet_lt hf.enorm.lintegral_kernel measurable_const

variable [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

/--
theorem `ProbabilityTheory.measurableSet_kernel_integrable` / 定理 `ProbabilityTheory.measurableSet_kernel_integrable`

English:
theorem ProbabilityTheory.measurableSet_kernel_integrable
  given: ⦃f
  statement: α -> β -> E⦄
  proof: by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_kernel_prod_right hf.enorm) measurable_const

中文:
定理 ProbabilityTheory.measurableSet_kernel_integrable
  条件: ⦃f
  结论: α -> β -> E⦄
  证明: by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_kernel_prod_right hf.enorm) measurable_const

Depends on / 依赖: Integrable, Measurable, Measurable.lintegral_kernel_prod_right, aestronglyMeasurable, hf.enorm, hf.of_uncurry_left.aestronglyMeasurable, lintegral_kernel_prod_right, measurableSet_lt, measurable_const, of_uncurry_left, simp_rw, true_and
-/
theorem ProbabilityTheory.measurableSet_kernel_integrable ⦃f : α -> β -> E⦄
    (hf : StronglyMeasurable (uncurry f)) :
    MeasurableSet {x | Integrable (f x) (κ x)} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_kernel_prod_right hf.enorm) measurable_const

open ProbabilityTheory.Kernel

namespace MeasureTheory

variable [NormedSpace Real E]

set_option backward.isDefEq.respectTransparency.types false in
omit [IsSFiniteKernel κ] in
@[fun_prop]
/--
theorem `StronglyMeasurable.integral_kernel` / 定理 `StronglyMeasurable.integral_kernel`

English:
theorem StronglyMeasurable.integral_kernel
  given: ⦃f
  statement: β -> E⦄
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range f union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc β E := SimpleFunc.approxOn _ hf.measurable (range f 

中文:
定理 StronglyMeasurable.integral_kernel
  条件: ⦃f
  结论: β -> E⦄
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range f union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc β E := SimpleFunc.approxOn _ hf.measurable (range f 

Depends on / 依赖: CompleteSpace, Integrable, SeparableSpace, SimpleFunc, SimpleFunc.approxOn, StronglyMeasurable, StronglyMeasurable.indicat, TopologicalSpace, TopologicalSpace.SeparableSpace, approxOn, borelize, hf.measurable, hf.separableSpace_range_union_singleton, indicat, indicator, integral, measurable, separableSpace_range_union_singleton, stronglyMeasurable_const, stronglyMeasurable_of_tendsto
-/
theorem StronglyMeasurable.integral_kernel ⦃f : β -> E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f y ∂κ x := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range f union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc β E := SimpleFunc.approxOn _ hf.measurable (range f union {0}) 0 (by simp)
  let f' n : α -> E := {x | Integrable f (κ x)}.indicator fun x => (s n).integral (κ x)
  refine stronglyMeasurable_of_tendsto (f := f') atTop (fun n => ?_) ?_
  · refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    simp_rw [SimpleFunc.integral_eq]
    refine Finset.stronglyMeasurable_fun_sum _ fun _ _ => ?_
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    exact κ.measurable_coe ((s n).measurableSet_fiber _)
  · rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable f (κ x)
    · simp only [mem_ofPred_eq, hfx, indicator_of_mem, f']
      apply tendsto_integral_approxOn_of_measurable_of_range_subset _ hfx
      exact subset_rfl
    · simp [f', hfx, integral_undef]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `StronglyMeasurable.integral_kernel_prod_right` / 定理 `StronglyMeasurable.integral_kernel_prod_right`

English:
theorem StronglyMeasurable.integral_kernel_prod_right
  given: ⦃f
  statement: α -> β -> E⦄
  proof: by
  classical
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range (uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (α × β) E :=
    SimpleFunc.ap

中文:
定理 StronglyMeasurable.integral_kernel_prod_right
  条件: ⦃f
  结论: α -> β -> E⦄
  证明: by
  classical
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range (uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (α × β) E :=
    SimpleFunc.ap

Depends on / 依赖: CompleteSpace, Integrable, Prod.mk, SeparableSpace, SimpleFunc, SimpleFunc.approxOn, TopologicalSpace, TopologicalSpace.SeparableSpace, approxOn, borelize, classical, hf.measurable, hf.separableSpace_range_union_singleton, integral, measurable, measurable_prodMk_left, separableSpace_range_union_singleton, stronglyMeasurable_const, uncurry
-/
theorem StronglyMeasurable.integral_kernel_prod_right ⦃f : α -> β -> E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂κ x := by
  classical
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range (uncurry f) union {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : Nat -> SimpleFunc (α × β) E :=
    SimpleFunc.approxOn _ hf.measurable (range (uncurry f) union {0}) 0 (by simp)
  let s' : Nat -> α -> SimpleFunc β E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : Nat -> α -> E := fun n =>
    {x | Integrable (f x) (κ x)}.indicator fun x => (s' n x).integral (κ x)
  have hf' : forall n, StronglyMeasurable (f' n) := by
    intro n; refine StronglyMeasurable.indicator ?_ (measurableSet_kernel_integrable hf)
    have : forall x, ((s' n x).range.filter fun x => x != 0) subseteq (s n).range := by
      intro
      exact Finset.Subset.trans (Finset.filter_subset _ _) (SimpleFunc.range_comp_subset_range _ _)
    simp only [SimpleFunc.integral_eq_sum_of_subset (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply Kernel.measurable_kernel_prodMk_left
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : α => ∫ y : β, f x y ∂κ x) := by
    rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable (f x) (κ x)
    · have (n : _) : Integrable (s' n x) (κ x) := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [f', hfx, SimpleFunc.integral_eq_integral _ (this _), indicator_of_mem,
        mem_ofPred_eq]
      refine
        tendsto_integral_of_dominated_convergence (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · -- Porting note: was
        -- exact fun n => Eventually.of_forall fun y =>
        -- SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
        exact fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le hf.measurable (by simp) (x, y) n
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn hf.measurable (by simp) ?_
        apply subset_closure
        simp [-uncurry_apply_pair]
    · simp [f', hfx, integral_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

/--
theorem `StronglyMeasurable.integral_kernel_prod_right'` / 定理 `StronglyMeasurable.integral_kernel_prod_right'`

English:
theorem StronglyMeasurable.integral_kernel_prod_right'
  given: ⦃f
  statement: α × β -> E⦄ (hf : StronglyMeasurable f) :
  proof: by
  rw [← uncurry_curry f] at hf
  exact hf.integral_kernel_prod_right

中文:
定理 StronglyMeasurable.integral_kernel_prod_right'
  条件: ⦃f
  结论: α × β -> E⦄ (hf : StronglyMeasurable f) :
  证明: by
  rw [← uncurry_curry f] at hf
  exact hf.integral_kernel_prod_right

Depends on / 依赖: hf.integral_kernel_prod_right, integral_kernel_prod_right, uncurry_curry
-/
theorem StronglyMeasurable.integral_kernel_prod_right' ⦃f : α × β -> E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => ∫ y, f (x, y) ∂κ x := by
  rw [← uncurry_curry f] at hf
  exact hf.integral_kernel_prod_right

/--
theorem `StronglyMeasurable.integral_kernel_prod_right''` / 定理 `StronglyMeasurable.integral_kernel_prod_right''`

English:
theorem StronglyMeasurable.integral_kernel_prod_right''
  statement: {f : β × γ -> E}
  proof: by
  change
    StronglyMeasurable
      ((fun x => ∫ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := η)
      (hf

中文:
定理 StronglyMeasurable.integral_kernel_prod_right''
  结论: {f : β × γ -> E}
  证明: by
  change
    StronglyMeasurable
      ((fun x => ∫ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := η)
      (hf

Depends on / 依赖: MeasureTheory, MeasureTheory.StronglyMeasurable.integral_kernel_prod_right, StronglyMeasurable, StronglyMeasurable.comp_measurable, comp_measurable, hf.comp_measurable, integral_kernel_prod_right, measurable_fst, measurable_fst.snd.prodMk, measurable_prodMk_left, measurable_snd, prodMk
-/
theorem StronglyMeasurable.integral_kernel_prod_right'' {f : β × γ -> E}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂η (a, x) := by
  change
    StronglyMeasurable
      ((fun x => ∫ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := η)
      (hf.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
    simpa using this

/--
theorem `StronglyMeasurable.integral_kernel_prod_left` / 定理 `StronglyMeasurable.integral_kernel_prod_left`

English:
theorem StronglyMeasurable.integral_kernel_prod_left
  given: ⦃f
  statement: β -> α -> E⦄
  proof: (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

中文:
定理 StronglyMeasurable.integral_kernel_prod_left
  条件: ⦃f
  结论: β -> α -> E⦄
  证明: (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

Depends on / 依赖: comp_measurable, hf.comp_measurable, integral_kernel_prod_right, measurable_swap
-/
theorem StronglyMeasurable.integral_kernel_prod_left ⦃f : β -> α -> E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

/--
theorem `StronglyMeasurable.integral_kernel_prod_left'` / 定理 `StronglyMeasurable.integral_kernel_prod_left'`

English:
theorem StronglyMeasurable.integral_kernel_prod_left'
  given: ⦃f
  statement: β × α -> E⦄ (hf : StronglyMeasurable f) :
  proof: (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

中文:
定理 StronglyMeasurable.integral_kernel_prod_left'
  条件: ⦃f
  结论: β × α -> E⦄ (hf : StronglyMeasurable f) :
  证明: (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

Depends on / 依赖: comp_measurable, hf.comp_measurable, integral_kernel_prod_right, measurable_swap
-/
theorem StronglyMeasurable.integral_kernel_prod_left' ⦃f : β × α -> E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'

/--
theorem `StronglyMeasurable.integral_kernel_prod_left''` / 定理 `StronglyMeasurable.integral_kernel_prod_left''`

English:
theorem StronglyMeasurable.integral_kernel_prod_left''
  given: {f : γ × β -> E} (hf : StronglyMeasurable f)
  proof: by
  change
    StronglyMeasurable
      ((fun y => ∫ x, (fun u : γ × α × β => f (u.1, u.2.2)) (x, y) ∂η y) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' (κ := η)
      (hf.co

中文:
定理 StronglyMeasurable.integral_kernel_prod_left''
  条件: {f : γ × β -> E} (hf : StronglyMeasurable f)
  证明: by
  change
    StronglyMeasurable
      ((fun y => ∫ x, (fun u : γ × α × β => f (u.1, u.2.2)) (x, y) ∂η y) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' (κ := η)
      (hf.co

Depends on / 依赖: MeasureTheory, MeasureTheory.StronglyMeasurable.integral_kernel_prod_left, StronglyMeasurable, StronglyMeasurable.comp_measurable, comp_measurable, hf.comp_measurable, integral_kernel_prod_left, measurable_fst, measurable_fst.prodMk, measurable_prodMk_left, measurable_snd, measurable_snd.snd, prodMk
-/
theorem StronglyMeasurable.integral_kernel_prod_left'' {f : γ × β -> E} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂η (a, y) := by
  change
    StronglyMeasurable
      ((fun y => ∫ x, (fun u : γ × α × β => f (u.1, u.2.2)) (x, y) ∂η y) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' (κ := η)
      (hf.comp_measurable (measurable_fst.prodMk measurable_snd.snd))
    simpa using this

end MeasureTheory
