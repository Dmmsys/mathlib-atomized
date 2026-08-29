/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Patrick Massot, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# The dominated convergence theorem

This file collects various results related to the Lebesgue dominated convergence theorem
for the Bochner integral.

## Main results
- `MeasureTheory.tendsto_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for the Bochner integral
- `MeasureTheory.hasSum_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for series
- `MeasureTheory.integral_tsum`, `MeasureTheory.integral_tsum_of_summable_integral_norm`:
  the integral and `tsum`s commute, if the norms of the functions form a summable series
- `intervalIntegral.hasSum_integral_of_dominated_convergence`: the Lebesgue dominated convergence
  theorem for parametric interval integrals
- `intervalIntegral.continuous_of_dominated_interval`: continuity of the interval integral
  w.r.t. a parameter
- `intervalIntegral.continuous_primitive` and friends: primitives of interval integrable
  measurable functions are continuous

-/

public section

open MeasureTheory Metric

/-!
## The Lebesgue dominated convergence theorem for the Bochner integral
-/
section DominatedConvergenceTheorem

open Set Filter TopologicalSpace ENNReal
open scoped Topology Interval

namespace MeasureTheory

variable {α E G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup G] [NormedSpace Real G]
  {m : MeasurableSpace α} {μ : Measure α}

/--
theorem `tendsto_integral_of_dominated_convergence` / 定理 `tendsto_integral_of_dominated_convergence`

English:
theorem tendsto_integral_of_dominated_convergence
  statement: {F : Nat -> α -> G} {f : α -> G} (bound : α -> Real)
  proof: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound F_measurable bound_integrable h_bound h_lim

中文:
定理 tendsto_integral_of_dominated_convergence
  结论: {F : 自然数 -> α -> G} {f : α -> G} (bound : α -> 实数)
  证明: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound F_measurable bound_integrable h_bound h_lim

Depends on / 依赖: F_measurable, bound_integrable, dominatedFinMeasAdditive_weightedSMul, h_bound, h_lim, integral_eq_setToFun, tendsto_setToFun_of_dominated_convergence
-/
theorem tendsto_integral_of_dominated_convergence {F : Nat -> α -> G} {f : α -> G} (bound : α -> Real)
    (F_measurable : forall n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound F_measurable bound_integrable h_bound h_lim

/--
theorem `tendsto_integral_filter_of_dominated_convergence` / 定理 `tendsto_integral_filter_of_dominated_convergence`

English:
theorem tendsto_integral_filter_of_dominated_convergence
  statement: {ι} {l : Filter ι} [l.IsCountablyGenerated]
  proof: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound hF_meas h_bound bound_integrable h_lim

中文:
定理 tendsto_integral_filter_of_dominated_convergence
  结论: {ι} {l : 滤子 ι} [l.是余untablyGenerated]
  证明: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound hF_meas h_bound bound_integrable h_lim

Depends on / 依赖: bound_integrable, dominatedFinMeasAdditive_weightedSMul, hF_meas, h_bound, h_lim, integral_eq_setToFun, tendsto_setToFun_filter_of_dominated_convergence
-/
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι -> α -> G} {f : α -> G} (bound : α -> Real) (hF_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : forallᶠ n in l, forallᵐ a ∂μ, ‖F n a‖ <= bound a) (bound_integrable : Integrable bound μ)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound hF_meas h_bound bound_integrable h_lim

/--
theorem `hasSum_integral_of_dominated_convergence` / 定理 `hasSum_integral_of_dominated_convergence`

English:
theorem hasSum_integral_of_dominated_convergence
  statement: {ι} [Countable ι] {F : ι -> α -> G} {f : α -> G}
  proof: by
  simp only [integral_eq_setToFun]
  exact hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable
    bound_integrable h_lim

中文:
定理 hasSum_integral_of_dominated_convergence
  结论: {ι} [可数 ι] {F : ι -> α -> G} {f : α -> G}
  证明: by
  simp only [integral_eq_setToFun]
  exact hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable
    bound_integrable h_lim

Depends on / 依赖: bound_integrable, bound_summable, hF_meas, h_bound, h_lim, hasSum_setToFun_of_dominated_convergence, integral_eq_setToFun
-/
theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι -> α -> G} {f : α -> G}
    (bound : ι -> α -> Real) (hF_meas : forall n, AEStronglyMeasurable (F n) μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a)
    (bound_summable : forallᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable
    bound_integrable h_lim

/--
theorem `integral_tsum` / 定理 `integral_tsum`

English:
theorem integral_tsum
  statement: {ι} [Countable ι] {f : ι -> α -> G} (hf : forall i, AEStronglyMeasurable (f i) μ)
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp only [integral_eq_setToFun]
  exact setToFun_tsum _ hf hf'

中文:
定理 integral_tsum
  结论: {ι} [可数 ι] {f : ι -> α -> G} (hf : 对任意 i, AEStronglyMeasurable (f i) μ)
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp only [integral_eq_setToFun]
  exact setToFun_tsum _ hf hf'

Depends on / 依赖: CompleteSpace, integral, integral_eq_setToFun, setToFun_tsum
-/
theorem integral_tsum {ι} [Countable ι] {f : ι -> α -> G} (hf : forall i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞) :
    ∫ a, ∑' i, f i a ∂μ = ∑' i, ∫ a, f i a ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp only [integral_eq_setToFun]
  exact setToFun_tsum _ hf hf'

/--
lemma `hasSum_integral_of_summable_integral_norm` / 引理 `hasSum_integral_of_summable_integral_norm`

English:
lemma hasSum_integral_of_summable_integral_norm
  statement: {ι} [Countable ι] {F : ι -> α -> E}
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i => (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i => norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm]; rw [coe_nnreal_eq]; rw [coe_nnnorm]; rw [Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
exact ENNReal.tsum_coe_ne_top_iff_summable.2 NNReal.summable_coe.1 hF_sum.abs

中文:
引理 hasSum_integral_of_summable_integral_norm
  结论: {ι} [可数 ι] {F : ι -> α -> E}
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i => (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i => norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm]; rw [coe_nnreal_eq]; rw [coe_nnnorm]; rw [Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
exact ENNReal.tsum_coe_ne_top_iff_summable.2 NNReal.summable_coe.1 hF_sum.abs

Depends on / 依赖: CompleteSpace, ENNReal, ENNReal.tsum_coe_ne_, Real.norm_of_nonneg, coe_nnnorm, coe_nnreal_eq, hF_int, hF_sum, hF_sum.of_norm_bounded, hasSum, hasSum_zero, integral, integral_nonneg, integral_tsum, lintegral_coe_eq_integral, norm_integral_le_integral_norm, norm_nonneg, norm_of_nonneg, of_norm_bounded, tsum_coe_ne_
-/
lemma hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι -> α -> E}
    (hF_int : forall i : ι, Integrable (F i) μ) (hF_sum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ) := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i => (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i => norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm]; rw [coe_nnreal_eq]; rw [coe_nnnorm]; rw [Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
exact ENNReal.tsum_coe_ne_top_iff_summable.2 NNReal.summable_coe.1 hF_sum.abs

/--
lemma `integral_tsum_of_summable_integral_norm` / 引理 `integral_tsum_of_summable_integral_norm`

English:
lemma integral_tsum_of_summable_integral_norm
  statement: {ι} [Countable ι] {F : ι -> α -> E}
  proof: (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

中文:
引理 integral_tsum_of_summable_integral_norm
  结论: {ι} [可数 ι] {F : ι -> α -> E}
  证明: (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

Depends on / 依赖: hF_int, hF_sum, hasSum_integral_of_summable_integral_norm, tsum_eq
-/
lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι -> α -> E}
    (hF_int : forall i : ι, Integrable (F i) μ) (hF_sum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

/--
theorem `tendsto_integral_filter_of_norm_le_const` / 定理 `tendsto_integral_filter_of_norm_le_const`

English:
theorem tendsto_integral_filter_of_norm_le_const
  statement: {ι} {l : Filter ι} [l.IsCountablyGenerated]
  proof: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

中文:
定理 tendsto_integral_filter_of_norm_le_const
  结论: {ι} {l : 滤子 ι} [l.是余untablyGenerated]
  证明: by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

Depends on / 依赖: PartialOrder, PartialOrder.lift, Subtype, Subtype.coe_injective, coe_injective, fast_instance, h_bound, h_lim, h_meas, integral_eq_setToFun, tendsto_setToFun_filter_of_norm_le_const
-/
theorem tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι -> α -> G} [IsFiniteMeasure μ] {f : α -> G}
    (h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : exists C, forallᶠ n in l, (forallᵐ ω ∂μ, ‖F n ω‖ <= C))
    (h_lim : forallᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ)) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

end MeasureTheory

section TendstoMono

variable {α E : Type*} [MeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace Real E] {s : Nat -> Set α}
  {f : α -> E}

/--
theorem `_root_.Antitone.tendsto_setIntegral` / 定理 `_root_.Antitone.tendsto_setIntegral`

English:
theorem _root_.Antitone.tendsto_setIntegral
  statement: (hsm : forall i, MeasurableSet (s i)) (h_anti : Antitone s)
  proof: by
  let bound : α -> Real := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti zero_le)).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [h_anti zero_le]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

中文:
定理 _root_.递减.tendsto_set整数egral
  结论: (hsm : 对任意 i, 可测集 (s i)) (h_anti : 递减 s)
  证明: by
  let bound : α -> Real := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti zero_le)).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [h_anti zero_le]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

Depends on / 依赖: IntegrableOn, IntegrableOn.mono_set, MeasurableSet, MeasurableSet.iInter, aestronglyMeasurable_indicator_iff, h_anti, h_int_eq, hfi.norm, iInter, indicator, integrable_indicator_iff, integral_indicator, mono_set, tendsto_integral_of_dominated_convergence, zero_le
-/
theorem _root_.Antitone.tendsto_setIntegral (hsm : forall i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α -> Real := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti zero_le)).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [h_anti zero_le]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

end TendstoMono

/-!
## The Lebesgue dominated convergence theorem for interval integrals
As an application, we show continuity of parametric integrals.
-/
namespace intervalIntegral

section DCT

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {a b : Real} {f : Real -> E} {μ : Measure Real}

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
nonrec theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι -> Real -> E} (bound : Real -> Real)
    (hF_meas : forallᶠ n in l, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : forallᶠ n in l, forallᵐ x ∂μ, x in Ι a b -> ‖F n x‖ <= bound x)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_lim : forallᵐ x ∂μ, x in Ι a b -> Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc,
    ← ae_restrict_iff' (α := Real) (μ := μ) measurableSet_uIoc] at *
exact tendsto_const_nhds.smul
    tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim

/--
theorem `_root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn` / 定理 `_root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn`

English:
theorem _root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  proof: by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases isCompact_uIcc.bddAbove_image (h_lim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C + 1)
  case hF_meas =>
.aestronglyMeasurable measurableSet_uIoc exact hF.mono fun i hi => hi.mono uIoc_subset_uIcc
  case h_bound =>
    have := uniformContinuous_norm.comp_tendstoUniformlyOn h_lim
.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
exact this.mono fun i hi => .of_forall fun x hx => hi x uIoc_subset_uIcc hx
  case bound_integrable =>
    exact intervalIntegrable_const
  case h_lim =>
exact .of_forall fun x hx => h_lim.tendsto_at uIoc_subset_uIcc hx

中文:
定理 _root_.TendstoUniformlyOn.tendsto_interval整数egral_of_continuousOn
  证明: by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases isCompact_uIcc.bddAbove_image (h_lim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C + 1)
  case hF_meas =>
.aestronglyMeasurable measurableSet_uIoc exact hF.mono fun i hi => hi.mono uIoc_subset_uIcc
  case h_bound =>
    have := uniformContinuous_norm.comp_tendstoUniformlyOn h_lim
.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
exact this.mono fun i hi => .of_forall fun x hx => hi x uIoc_subset_uIcc hx
  case bound_integrable =>
    exact intervalIntegrable_const
  case h_lim =>
exact .of_forall fun x hx => h_lim.tendsto_at uIoc_subset_uIcc hx

Depends on / 依赖: aestronglyMeasurable, bddAbove_image, comp_tendstoUniformlyOn, continuousOn, eq_or_neBot, eventually_forall_le, frequently, hF.frequently, hF.mono, hF_meas, h_bound, h_lim, h_lim.continuousOn, hi.mono, isCompact_uIcc, isCompact_uIcc.bddAbove_image, l.eq_or_neBot, measurableSet_uIoc, tendsto_integral_filter_of_dominated_convergence, this.mono
-/
theorem _root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    {l : Filter ι} [l.IsCountablyGenerated] {F : ι -> Real -> E}
    [IsLocallyFiniteMeasure μ] (hF : forallᶠ i in l, ContinuousOn (F i) [[a, b]])
    (h_lim : TendstoUniformlyOn F f l [[a, b]]) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases isCompact_uIcc.bddAbove_image (h_lim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C + 1)
  case hF_meas =>
.aestronglyMeasurable measurableSet_uIoc exact hF.mono fun i hi => hi.mono uIoc_subset_uIcc
  case h_bound =>
    have := uniformContinuous_norm.comp_tendstoUniformlyOn h_lim
.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
exact this.mono fun i hi => .of_forall fun x hx => hi x uIoc_subset_uIcc hx
  case bound_integrable =>
    exact intervalIntegrable_const
  case h_lim =>
exact .of_forall fun x hx => h_lim.tendsto_at uIoc_subset_uIcc hx

/-- Lebesgue dominated convergence theorem for parametric interval integrals. -/
nonrec theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι -> Real -> E}
    (bound : ι -> Real -> Real) (hF_meas : forall n, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : forall n, forallᵐ t ∂μ, t in Ι a b -> ‖F n t‖ <= bound n t)
    (bound_summable : forallᵐ t ∂μ, t in Ι a b -> Summable fun n => bound n t)
    (bound_integrable : IntervalIntegrable (fun t => ∑' n, bound n t) μ a b)
    (h_lim : forallᵐ t ∂μ, t in Ι a b -> HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc, ←
    ae_restrict_iff' (α := Real) (μ := μ) measurableSet_uIoc] at *
  exact
    (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable bound_integrable
          h_lim).const_smul
      _

/--
theorem `hasSum_intervalIntegral_of_summable_norm` / 定理 `hasSum_intervalIntegral_of_summable_norm`

English:
theorem hasSum_intervalIntegral_of_summable_norm
  statement: [Countable ι] {f : ι -> C(Real, E)}
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : Real) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x

中文:
定理 hasSum_interval整数egral_of_summable_norm
  结论: [可数 ι] {f : ι -> C(实数, E)}
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : Real) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x

Depends on / 依赖: Compacts, CompleteSpace, ContinuousMap, ContinuousMap.norm_coe_le_norm, ae_of_all, aestronglyMeasurable, filter_upwards, hasSum_integral_of_dominated_convergence, hasSum_zero, hf_sum, integral, intervalIntegrable_const, intervalIntegral, isCompact_uIcc, map_continuous, norm_coe_le_norm, restrict
-/
theorem hasSum_intervalIntegral_of_summable_norm [Countable ι] {f : ι -> C(Real, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real)‖) :
    HasSum (fun i : ι => ∫ x in a..b, f i x) (∫ x in a..b, ∑' i : ι, f i x) := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : Real) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x

/--
theorem `tsum_intervalIntegral_eq_of_summable_norm` / 定理 `tsum_intervalIntegral_eq_of_summable_norm`

English:
theorem tsum_intervalIntegral_eq_of_summable_norm
  statement: [Countable ι] {f : ι -> C(Real, E)}
  proof: (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

中文:
定理 tsum_interval整数egral_eq_of_summable_norm
  结论: [可数 ι] {f : ι -> C(实数, E)}
  证明: (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

Depends on / 依赖: hasSum_intervalIntegral_of_summable_norm, hf_sum, tsum_eq
-/
theorem tsum_intervalIntegral_eq_of_summable_norm [Countable ι] {f : ι -> C(Real, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts Real)‖) :
    ∑' i : ι, ∫ x in a..b, f i x = ∫ x in a..b, ∑' i : ι, f i x :=
  (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/--
theorem `continuousWithinAt_of_dominated_interval` / 定理 `continuousWithinAt_of_dominated_interval`

English:
theorem continuousWithinAt_of_dominated_interval
  statement: {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real} {a b : Real}
  proof: tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousWithinAt_of_dominated_interval
  结论: {F : X -> 实数 -> E} {x₀ : X} {bound : 实数 -> 实数} {a b : 实数}
  证明: tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, hF_meas, h_bound, h_cont, tendsto_integral_filter_of_dominated_convergence
-/
theorem continuousWithinAt_of_dominated_interval {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real} {a b : Real}
    {s : Set X} (hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : forallᵐ t ∂μ, t in Ι a b -> ContinuousWithinAt (fun x => F x t) s x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/--
theorem `continuousAt_of_dominated_interval` / 定理 `continuousAt_of_dominated_interval`

English:
theorem continuousAt_of_dominated_interval
  statement: {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real} {a b : Real}
  proof: tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

中文:
定理 continuousAt_of_dominated_interval
  结论: {F : X -> 实数 -> E} {x₀ : X} {bound : 实数 -> 实数} {a b : 实数}
  证明: tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

Depends on / 依赖: bound_integrable, hF_meas, h_bound, h_cont, tendsto_integral_filter_of_dominated_convergence
-/
theorem continuousAt_of_dominated_interval {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real} {a b : Real}
    (hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : forallᵐ t ∂μ, t in Ι a b -> ContinuousAt (fun x => F x t) x₀) :
    ContinuousAt (fun x => ∫ t in a..b, F x t ∂μ) x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/--
theorem `continuous_of_dominated_interval` / 定理 `continuous_of_dominated_interval`

English:
theorem continuous_of_dominated_interval
  statement: {F : X -> Real -> E} {bound : Real -> Real} {a b : Real}
  proof: continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
bound_integrable
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

中文:
定理 continuous_of_dominated_interval
  结论: {F : X -> 实数 -> E} {bound : 实数 -> 实数} {a b : 实数}
  证明: continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
bound_integrable
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

Depends on / 依赖: Eventually, Eventually.of_forall, bound_integrable, continuousAt, continuousAt_of_dominated_interval, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, hF_meas, h_bound, h_cont, h_cont.mono, of_forall
-/
theorem continuous_of_dominated_interval {F : X -> Real -> E} {bound : Real -> Real} {a b : Real}
    (hF_meas : forall x, AEStronglyMeasurable (F x) <| μ.restrict <| Ι a b)
    (h_bound : forall x, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : forallᵐ t ∂μ, t in Ι a b -> Continuous fun x => F x t) :
    Continuous fun x => ∫ t in a..b, F x t ∂μ :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
bound_integrable
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

end DCT

section ContinuousPrimitive

open scoped Interval

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace X]
  {a b b₀ b₁ b₂ : Real} {μ : Measure Real} {f : Real -> E}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `continuousWithinAt_primitive` / 定理 `continuousWithinAt_primitive`

English:
theorem continuousWithinAt_primitive
  statement: (hb₀ : μ {b₀} = 0)
  proof: by
  by_cases h₀ : b₀ in Icc b₁ b₂
  · have h₁₂ : b₁ <= b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : forall {x}, x in Icc b₁ b₂ -> IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
· exact ⟨min_le_of_left_le (min_le_right _ _).trans h₁,
le_max_of_le_right h₂.trans le_max_right _ _⟩
    have : forall b in Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁]; rw [h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x <= b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff]; rw [Measure.restrict_restrict]; rw [uIoc]; rw [Iic_def]; rw [Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : forallᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]

中文:
定理 continuousWithinAt_primitive
  结论: (hb₀ : μ {b₀} = 0)
  证明: by
  by_cases h₀ : b₀ in Icc b₁ b₂
  · have h₁₂ : b₁ <= b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : forall {x}, x in Icc b₁ b₂ -> IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
· exact ⟨min_le_of_left_le (min_le_right _ _).trans h₁,
le_max_of_le_right h₂.trans le_max_right _ _⟩
    have : forall b in Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁]; rw [h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x <= b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff]; rw [Measure.restrict_restrict]; rw [uIoc]; rw [Iic_def]; rw [Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : forallᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]

Depends on / 依赖: IntervalIntegrable, h_int, h_int.mono_set, le_max_of_le_right, le_max_right, min_eq_left, min_le_of_left_le, min_le_right, mono_set, uIcc_subset_uIcc
-/
theorem continuousWithinAt_primitive (hb₀ : μ {b₀} = 0)
    (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) :
    ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ) (Icc b₁ b₂) b₀ := by
  by_cases h₀ : b₀ in Icc b₁ b₂
  · have h₁₂ : b₁ <= b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : forall {x}, x in Icc b₁ b₂ -> IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
· exact ⟨min_le_of_left_le (min_le_right _ _).trans h₁,
le_max_of_le_right h₂.trans le_max_right _ _⟩
    have : forall b in Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁]; rw [h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x <= b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff]; rw [Measure.restrict_restrict]; rw [uIoc]; rw [Iic_def]; rw [Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : forallᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : forallᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : Real | t <= x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]

/--
theorem `continuousAt_parametric_primitive_of_dominated` / 定理 `continuousAt_parametric_primitive_of_dominated`

English:
theorem continuousAt_parametric_primitive_of_dominated
  statement: [FirstCountableTopology X]
  proof: by
  have hsub : forall {a₀ b₀}, a₀ in Ioo a b -> b₀ in Ioo a b -> Ι a₀ b₀ subseteq Ι a b := fun ha₀ hb₀ =>
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b in 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b in 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x₀ t‖ <= bound t := h_bound.self_of_nhds
  have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
    dsimp
    have hiF : forall {x a₀ b₀},
        (forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t) -> a₀ in Ioo a b -> b₀ in Ioo a b ->
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ =>
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub]; rw [add_assoc]; rw [add_sub_cancel]; rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x => (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx =>
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
(bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀)
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t => ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × Real => ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ <= |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : forallᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
      have H : forallᵐ t : Real ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ <= 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ <= ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ <= 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

中文:
定理 continuousAt_parametric_primitive_of_dominated
  结论: [第一可数拓扑 X]
  证明: by
  have hsub : forall {a₀ b₀}, a₀ in Ioo a b -> b₀ in Ioo a b -> Ι a₀ b₀ subseteq Ι a b := fun ha₀ hb₀ =>
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b in 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b in 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x₀ t‖ <= bound t := h_bound.self_of_nhds
  have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
    dsimp
    have hiF : forall {x a₀ b₀},
        (forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t) -> a₀ in Ioo a b -> b₀ in Ioo a b ->
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ =>
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub]; rw [add_assoc]; rw [add_sub_cancel]; rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x => (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx =>
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
(bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀)
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t => ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × Real => ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ <= |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : forallᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
      have H : forallᵐ t : Real ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ <= 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ <= ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ <= 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

Depends on / 依赖: Icc_mem_nhds, Icc_nhds, Ioc_subset_uIoc, Ioo_mem_nhds, Ioo_nhds, Ioo_subset_Ioc_self, Ioo_subset_Ioc_self.trans, h_bound, h_bound.self_of_nhds, ordConnected_Ioo, ordConnected_Ioo.uIoc_subset, restrict, self_of_nhds, subseteq, uIoc_subset
-/
theorem continuousAt_parametric_primitive_of_dominated [FirstCountableTopology X]
    {F : X -> Real -> E} (bound : Real -> Real) (a b : Real)
    {a₀ b₀ : Real} {x₀ : X} (hF_meas : forall x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ <= bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : forallᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x => F x t) x₀) (ha₀ : a₀ in Ioo a b)
    (hb₀ : b₀ in Ioo a b) (hμb₀ : μ {b₀} = 0) :
    ContinuousAt (fun p : X × Real => ∫ t : Real in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) := by
  have hsub : forall {a₀ b₀}, a₀ in Ioo a b -> b₀ in Ioo a b -> Ι a₀ b₀ subseteq Ι a b := fun ha₀ hb₀ =>
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b in 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b in 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x₀ t‖ <= bound t := h_bound.self_of_nhds
  have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
    dsimp
    have hiF : forall {x a₀ b₀},
        (forallᵐ t : Real ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t) -> a₀ in Ioo a b -> b₀ in Ioo a b ->
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ =>
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub]; rw [add_assoc]; rw [add_sub_cancel]; rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x => (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx =>
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
(bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀)
ae_imp_of_ae_restrict ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t => ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × Real => ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : forallᶠ p : X × Real in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ <= |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : forallᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ <= bound t, ht : t in Ioo a b⟩
      have H : forallᵐ t : Real ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ <= 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ <= ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ <= 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t => ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le]; rw [max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

variable [NullSingletonClass μ]

/--
theorem `continuousOn_primitive` / 定理 `continuousOn_primitive`

English:
theorem continuousOn_primitive
  given: (h_int : IntegrableOn f (Icc a b) μ)
  proof: by
  by_cases h : a <= b
  · have : forall x in Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _

中文:
定理 continuousOn_primitive
  条件: (h_int : 整数egrableOn f (闭区间 a b) μ)
  证明: by
  by_cases h : a <= b
  · have : forall x in Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _

Depends on / 依赖: Icc_eq_empty, Ioc_subset_Icc_self, continuousOn_congr, continuousOn_empty, continuousWithinAt_primitive, h_int, h_int.mono, integral_of_le, intervalIntegrable_iff_integrableOn_Ioc_of_le, le_rfl, max_eq_right, measure_singleton, min_self, simp_rw, x_in
-/
theorem continuousOn_primitive (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b) := by
  by_cases h : a <= b
  · have : forall x in Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _

/--
theorem `continuousOn_primitive_Icc` / 定理 `continuousOn_primitive_Icc`

English:
theorem continuousOn_primitive_Icc
  given: (h_int : IntegrableOn f (Icc a b) μ)
  proof: by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

中文:
定理 continuousOn_primitive_Icc
  条件: (h_int : 整数egrableOn f (闭区间 a b) μ)
  证明: by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

Depends on / 依赖: continuousOn_primitive, h_int, integral_Icc_eq_integral_Ioc
-/
theorem continuousOn_primitive_Icc (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b) := by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

/--
theorem `continuousOn_primitive_interval'` / 定理 `continuousOn_primitive_interval'`

English:
theorem continuousOn_primitive_interval'
  statement: (h_int : IntervalIntegrable f μ b₁ b₂)
  proof: fun _ _ => by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1]; rw [max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int

中文:
定理 continuousOn_primitive_interval'
  结论: (h_int : 整数erval整数egrable f μ b₁ b₂)
  证明: fun _ _ => by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1]; rw [max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int

Depends on / 依赖: continuousWithinAt_primitive, h_int, intervalIntegrable_iff, max_eq_right, measure_singleton, min_eq_right
-/
theorem continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂)
    (ha : a in [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x ∂μ) [[b₁, b₂]] := fun _ _ => by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1]; rw [max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int

/--
theorem `continuousOn_primitive_interval` / 定理 `continuousOn_primitive_interval`

English:
theorem continuousOn_primitive_interval
  given: (h_int : IntegrableOn f (uIcc a b) μ)
  proof: continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc

中文:
定理 continuousOn_primitive_interval
  条件: (h_int : 整数egrableOn f (uIcc a b) μ)
  证明: continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc

Depends on / 依赖: continuousOn_primitive_interval, h_int, h_int.intervalIntegrable, intervalIntegrable, left_mem_uIcc
-/
theorem continuousOn_primitive_interval (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in a..x, f t ∂μ) (uIcc a b) :=
  continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc

/--
theorem `continuousOn_primitive_interval_left` / 定理 `continuousOn_primitive_interval_left`

English:
theorem continuousOn_primitive_interval_left
  given: (h_int : IntegrableOn f (uIcc a b) μ)
  proof: by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg

中文:
定理 continuousOn_primitive_interval_left
  条件: (h_int : 整数egrableOn f (uIcc a b) μ)
  证明: by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg

Depends on / 依赖: continuousOn_primitive_interval, h_int, integral_symm, uIcc_comm
-/
theorem continuousOn_primitive_interval_left (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (uIcc a b) := by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg

/--
theorem `continuous_primitive` / 定理 `continuous_primitive`

English:
theorem continuous_primitive
  given: (h_int : forall a b, IntervalIntegrable f μ a b) (a : Real)
  proof: by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : Real) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

中文:
定理 continuous_primitive
  条件: (h_int : 对任意 a b, 整数erval整数egrable f μ a b) (a : 实数)
  证明: by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : Real) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.continuousAt, Icc_mem_nhds, continuousAt, continuousWithinAt_primitive, continuous_iff_continuousAt, exists_gt, exists_lt, h_int, measure_singleton
-/
theorem continuous_primitive (h_int : forall a b, IntervalIntegrable f μ a b) (a : Real) :
    Continuous fun b => ∫ x in a..b, f x ∂μ := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : Real) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

variable [IsLocallyFiniteMeasure μ] {f : X -> Real -> E}

/--
theorem `continuous_parametric_primitive_of_continuous` / 定理 `continuous_parametric_primitive_of_continuous`

English:
theorem continuous_parametric_primitive_of_continuous
  proof: by
  -- We will prove continuity at a point `(q, b₀)`.
  rw [continuous_iff_continuousAt]
  rintro ⟨q, b₀⟩
  apply Metric.continuousAt_iff'.2 (fun ε εpos => ?_)
  -- choose `a` and `b` such that `(a, b)` contains both `a₀` and `b₀`. We will use uniform
  -- estimates on a neighborhood of the compact set `{q} × [a, b]`.
  obtain ⟨a, a_lt⟩ := exists_lt (min a₀ b₀)
  obtain ⟨b, lt_b⟩ := exists_gt (max a₀ b₀)
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have : IsCompact ({q} ×ˢ (Icc a b)) := isCompact_singleton.prod isCompact_Icc
  -- let `M` be a bound for `f` on the compact set `{q} × [a, b]`.
  obtain ⟨M, hM⟩ := this.bddAbove_image hf.norm.continuousOn
  -- let `δ` be small enough to satisfy several properties that will show up later.
  obtain ⟨δ, δpos, hδ, h'δ, h''δ⟩ : exists (δ : Real), 0 < δ ∧ δ < 1 ∧ Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b ∧
      (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
    have A : forallᶠ δ in 𝓝[>] (0 : Real), δ in Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have B : forallᶠ δ in 𝓝 0, Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b := by
      have I : Tendsto (fun δ => b₀ - δ) (𝓝 0) (𝓝 (b₀ - 0)) := tendsto_const_nhds.sub tendsto_id
      have J : Tendsto (fun δ => b₀ + δ) (𝓝 0) (𝓝 (b₀ + 0)) := tendsto_const_nhds.add tendsto_id
      simp only [sub_zero, add_zero] at I J
      filter_upwards [(tendsto_order.1 I).1 _ a_lt.2, (tendsto_order.1 J).2 _ lt_b.2] with δ hδ h'δ
      exact Icc_subset_Icc hδ.le h'δ.le
    have C : forallᶠ δ in 𝓝 0,
        (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
      suffices Tendsto
        (fun δ => (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b))
          (𝓝 0) (𝓝 ((M + 1) * (0 : Real>=0∞).toReal + 0 * μ.real (Icc a b))) by
        simp only [toReal_zero, mul_zero, zero_mul, add_zero] at this
        exact (tendsto_order.1 this).2 _ εpos
      apply Tendsto.add (Tendsto.mul tendsto_const_nhds _)
        (Tendsto.mul tendsto_id tendsto_const_nhds)
      exact (tendsto_toReal zero_ne_top).comp (tendsto_measure_Icc _ _)
    rcases (A.and ((B.and C).filter_mono nhdsWithin_le_nhds)).exists with ⟨δ, hδ, h'δ, h''δ⟩
    exact ⟨δ, hδ.1, hδ.2, h'δ, h''δ⟩
  -- By compactness of `[a, b]` and continuity of `f` there, if `p` is close enough to `q`
  -- then `f p x` is `δ`-close to `f q x`, uniformly in `x ∈ [a, b]`.
  -- (Note in particular that this implies a bound `M + δ ≤ M + 1` for `f p x`).
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[univ] q, forall p in v, forall x in Icc a b, dist (f p x) (f q x) < δ :=
    IsCompact.mem_uniformity_of_prod isCompact_Icc hf.continuousOn (mem_univ _)
      (dist_mem_uniformity δpos)
  -- for `p` in this neighborhood and `s` which is `δ`-close to `b₀`, we will show that the
  -- integrals are `ε`-close.
  have : v ×ˢ (Ioo (b₀ - δ) (b₀ + δ)) in 𝓝 (q, b₀) := by
    rw [nhdsWithin_univ] at v_mem
    simp only [prod_mem_nhds_iff, v_mem, true_and]
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [this]
  rintro ⟨p, s⟩ ⟨hp : p in v, hs : s in Ioo (b₀ - δ) (b₀ + δ)⟩
  simp only [dist_eq_norm] at hv ⊢
  have J r u v : IntervalIntegrable (f r) μ u v := (hf.uncurry_left _).intervalIntegrable _ _
  /- we compute the difference between the integrals by splitting the contribution of the change
  from `b₀` to `s` (which gives a contribution controlled by the measure of `(b₀ - δ, b₀ + δ)`,
  small enough thanks to our choice of `δ`) and the change from `q` to `p`, which is small as
  `f p x` and `f q x` are uniformly close by design. -/
  calc
  ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖
    = ‖(∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ)
        + (∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ)‖ := by congr 1; abel
  _ <= ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ‖
        + ‖∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖ := norm_add_le _ _
  _ = ‖∫ t in b₀..s, f p t ∂μ‖ + ‖∫ t in a₀..b₀, (f p t - f q t) ∂μ‖ := by
      congr 2
      · rw [integral_interval_sub_left (J _ _ _) (J _ _ _)]
      · rw [integral_sub (J _ _ _) (J _ _ _)]
  _ <= ∫ t in Ι b₀ s, ‖f p t‖ ∂μ + ∫ t in Ι a₀ b₀, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact norm_integral_le_integral_norm_uIoc
      · exact norm_integral_le_integral_norm_uIoc
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), ‖f p t‖ ∂μ + ∫ t in Icc a b, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · apply uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ⟨hs.1.le, hs.2.le⟩ )
        simp [δpos.le]
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨a_lt.1.le, lt_b.1.le⟩ ⟨a_lt.2.le, lt_b.2.le⟩)
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), M + 1 ∂μ + ∫ _t in Icc a b, δ ∂μ := by
      gcongr with x hx x hx
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · calc ‖f p x‖ = ‖f q x + (f p x - f q x)‖ := by congr; abel
        _ <= ‖f q x‖ + ‖f p x - f q x‖ := norm_add_le _ _
        _ <= M + δ := by
            gcongr
            · apply hM
              change (fun x => ‖Function.uncurry f x‖) (q, x) in _
              apply mem_image_of_mem
              simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
              exact h'δ hx
            · exact le_of_lt (hv _ hp _ (h'δ hx))
        _ <= M + 1 := by linarith
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · exact le_of_lt (hv _ hp _ hx)
  _ = (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) := by simp [mul_comm]
  _ < ε := h''δ

@[fun_prop]

中文:
定理 continuous_parametric_primitive_of_continuous
  证明: by
  -- We will prove continuity at a point `(q, b₀)`.
  rw [continuous_iff_continuousAt]
  rintro ⟨q, b₀⟩
  apply Metric.continuousAt_iff'.2 (fun ε εpos => ?_)
  -- choose `a` and `b` such that `(a, b)` contains both `a₀` and `b₀`. We will use uniform
  -- estimates on a neighborhood of the compact set `{q} × [a, b]`.
  obtain ⟨a, a_lt⟩ := exists_lt (min a₀ b₀)
  obtain ⟨b, lt_b⟩ := exists_gt (max a₀ b₀)
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have : IsCompact ({q} ×ˢ (Icc a b)) := isCompact_singleton.prod isCompact_Icc
  -- let `M` be a bound for `f` on the compact set `{q} × [a, b]`.
  obtain ⟨M, hM⟩ := this.bddAbove_image hf.norm.continuousOn
  -- let `δ` be small enough to satisfy several properties that will show up later.
  obtain ⟨δ, δpos, hδ, h'δ, h''δ⟩ : exists (δ : Real), 0 < δ ∧ δ < 1 ∧ Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b ∧
      (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
    have A : forallᶠ δ in 𝓝[>] (0 : Real), δ in Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have B : forallᶠ δ in 𝓝 0, Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b := by
      have I : Tendsto (fun δ => b₀ - δ) (𝓝 0) (𝓝 (b₀ - 0)) := tendsto_const_nhds.sub tendsto_id
      have J : Tendsto (fun δ => b₀ + δ) (𝓝 0) (𝓝 (b₀ + 0)) := tendsto_const_nhds.add tendsto_id
      simp only [sub_zero, add_zero] at I J
      filter_upwards [(tendsto_order.1 I).1 _ a_lt.2, (tendsto_order.1 J).2 _ lt_b.2] with δ hδ h'δ
      exact Icc_subset_Icc hδ.le h'δ.le
    have C : forallᶠ δ in 𝓝 0,
        (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
      suffices Tendsto
        (fun δ => (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b))
          (𝓝 0) (𝓝 ((M + 1) * (0 : Real>=0∞).toReal + 0 * μ.real (Icc a b))) by
        simp only [toReal_zero, mul_zero, zero_mul, add_zero] at this
        exact (tendsto_order.1 this).2 _ εpos
      apply Tendsto.add (Tendsto.mul tendsto_const_nhds _)
        (Tendsto.mul tendsto_id tendsto_const_nhds)
      exact (tendsto_toReal zero_ne_top).comp (tendsto_measure_Icc _ _)
    rcases (A.and ((B.and C).filter_mono nhdsWithin_le_nhds)).exists with ⟨δ, hδ, h'δ, h''δ⟩
    exact ⟨δ, hδ.1, hδ.2, h'δ, h''δ⟩
  -- By compactness of `[a, b]` and continuity of `f` there, if `p` is close enough to `q`
  -- then `f p x` is `δ`-close to `f q x`, uniformly in `x ∈ [a, b]`.
  -- (Note in particular that this implies a bound `M + δ ≤ M + 1` for `f p x`).
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[univ] q, forall p in v, forall x in Icc a b, dist (f p x) (f q x) < δ :=
    IsCompact.mem_uniformity_of_prod isCompact_Icc hf.continuousOn (mem_univ _)
      (dist_mem_uniformity δpos)
  -- for `p` in this neighborhood and `s` which is `δ`-close to `b₀`, we will show that the
  -- integrals are `ε`-close.
  have : v ×ˢ (Ioo (b₀ - δ) (b₀ + δ)) in 𝓝 (q, b₀) := by
    rw [nhdsWithin_univ] at v_mem
    simp only [prod_mem_nhds_iff, v_mem, true_and]
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [this]
  rintro ⟨p, s⟩ ⟨hp : p in v, hs : s in Ioo (b₀ - δ) (b₀ + δ)⟩
  simp only [dist_eq_norm] at hv ⊢
  have J r u v : IntervalIntegrable (f r) μ u v := (hf.uncurry_left _).intervalIntegrable _ _
  /- we compute the difference between the integrals by splitting the contribution of the change
  from `b₀` to `s` (which gives a contribution controlled by the measure of `(b₀ - δ, b₀ + δ)`,
  small enough thanks to our choice of `δ`) and the change from `q` to `p`, which is small as
  `f p x` and `f q x` are uniformly close by design. -/
  calc
  ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖
    = ‖(∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ)
        + (∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ)‖ := by congr 1; abel
  _ <= ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ‖
        + ‖∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖ := norm_add_le _ _
  _ = ‖∫ t in b₀..s, f p t ∂μ‖ + ‖∫ t in a₀..b₀, (f p t - f q t) ∂μ‖ := by
      congr 2
      · rw [integral_interval_sub_left (J _ _ _) (J _ _ _)]
      · rw [integral_sub (J _ _ _) (J _ _ _)]
  _ <= ∫ t in Ι b₀ s, ‖f p t‖ ∂μ + ∫ t in Ι a₀ b₀, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact norm_integral_le_integral_norm_uIoc
      · exact norm_integral_le_integral_norm_uIoc
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), ‖f p t‖ ∂μ + ∫ t in Icc a b, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · apply uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ⟨hs.1.le, hs.2.le⟩ )
        simp [δpos.le]
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨a_lt.1.le, lt_b.1.le⟩ ⟨a_lt.2.le, lt_b.2.le⟩)
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), M + 1 ∂μ + ∫ _t in Icc a b, δ ∂μ := by
      gcongr with x hx x hx
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · calc ‖f p x‖ = ‖f q x + (f p x - f q x)‖ := by congr; abel
        _ <= ‖f q x‖ + ‖f p x - f q x‖ := norm_add_le _ _
        _ <= M + δ := by
            gcongr
            · apply hM
              change (fun x => ‖Function.uncurry f x‖) (q, x) in _
              apply mem_image_of_mem
              simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
              exact h'δ hx
            · exact le_of_lt (hv _ hp _ (h'δ hx))
        _ <= M + 1 := by linarith
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · exact le_of_lt (hv _ hp _ hx)
  _ = (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) := by simp [mul_comm]
  _ < ε := h''δ

@[fun_prop]
-/
theorem continuous_parametric_primitive_of_continuous
    {a₀ : Real} (hf : Continuous f.uncurry) :
    Continuous fun p : X × Real => ∫ t in a₀..p.2, f p.1 t ∂μ := by
  -- We will prove continuity at a point `(q, b₀)`.
  rw [continuous_iff_continuousAt]
  rintro ⟨q, b₀⟩
  apply Metric.continuousAt_iff'.2 (fun ε εpos => ?_)
  -- choose `a` and `b` such that `(a, b)` contains both `a₀` and `b₀`. We will use uniform
  -- estimates on a neighborhood of the compact set `{q} × [a, b]`.
  obtain ⟨a, a_lt⟩ := exists_lt (min a₀ b₀)
  obtain ⟨b, lt_b⟩ := exists_gt (max a₀ b₀)
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have : IsCompact ({q} ×ˢ (Icc a b)) := isCompact_singleton.prod isCompact_Icc
  -- let `M` be a bound for `f` on the compact set `{q} × [a, b]`.
  obtain ⟨M, hM⟩ := this.bddAbove_image hf.norm.continuousOn
  -- let `δ` be small enough to satisfy several properties that will show up later.
  obtain ⟨δ, δpos, hδ, h'δ, h''δ⟩ : exists (δ : Real), 0 < δ ∧ δ < 1 ∧ Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b ∧
      (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
    have A : forallᶠ δ in 𝓝[>] (0 : Real), δ in Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have B : forallᶠ δ in 𝓝 0, Icc (b₀ - δ) (b₀ + δ) subseteq Icc a b := by
      have I : Tendsto (fun δ => b₀ - δ) (𝓝 0) (𝓝 (b₀ - 0)) := tendsto_const_nhds.sub tendsto_id
      have J : Tendsto (fun δ => b₀ + δ) (𝓝 0) (𝓝 (b₀ + 0)) := tendsto_const_nhds.add tendsto_id
      simp only [sub_zero, add_zero] at I J
      filter_upwards [(tendsto_order.1 I).1 _ a_lt.2, (tendsto_order.1 J).2 _ lt_b.2] with δ hδ h'δ
      exact Icc_subset_Icc hδ.le h'δ.le
    have C : forallᶠ δ in 𝓝 0,
        (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
      suffices Tendsto
        (fun δ => (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b))
          (𝓝 0) (𝓝 ((M + 1) * (0 : Real>=0∞).toReal + 0 * μ.real (Icc a b))) by
        simp only [toReal_zero, mul_zero, zero_mul, add_zero] at this
        exact (tendsto_order.1 this).2 _ εpos
      apply Tendsto.add (Tendsto.mul tendsto_const_nhds _)
        (Tendsto.mul tendsto_id tendsto_const_nhds)
      exact (tendsto_toReal zero_ne_top).comp (tendsto_measure_Icc _ _)
    rcases (A.and ((B.and C).filter_mono nhdsWithin_le_nhds)).exists with ⟨δ, hδ, h'δ, h''δ⟩
    exact ⟨δ, hδ.1, hδ.2, h'δ, h''δ⟩
  -- By compactness of `[a, b]` and continuity of `f` there, if `p` is close enough to `q`
  -- then `f p x` is `δ`-close to `f q x`, uniformly in `x ∈ [a, b]`.
  -- (Note in particular that this implies a bound `M + δ ≤ M + 1` for `f p x`).
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[univ] q, forall p in v, forall x in Icc a b, dist (f p x) (f q x) < δ :=
    IsCompact.mem_uniformity_of_prod isCompact_Icc hf.continuousOn (mem_univ _)
      (dist_mem_uniformity δpos)
  -- for `p` in this neighborhood and `s` which is `δ`-close to `b₀`, we will show that the
  -- integrals are `ε`-close.
  have : v ×ˢ (Ioo (b₀ - δ) (b₀ + δ)) in 𝓝 (q, b₀) := by
    rw [nhdsWithin_univ] at v_mem
    simp only [prod_mem_nhds_iff, v_mem, true_and]
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [this]
  rintro ⟨p, s⟩ ⟨hp : p in v, hs : s in Ioo (b₀ - δ) (b₀ + δ)⟩
  simp only [dist_eq_norm] at hv ⊢
  have J r u v : IntervalIntegrable (f r) μ u v := (hf.uncurry_left _).intervalIntegrable _ _
  /- we compute the difference between the integrals by splitting the contribution of the change
  from `b₀` to `s` (which gives a contribution controlled by the measure of `(b₀ - δ, b₀ + δ)`,
  small enough thanks to our choice of `δ`) and the change from `q` to `p`, which is small as
  `f p x` and `f q x` are uniformly close by design. -/
  calc
  ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖
    = ‖(∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ)
        + (∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ)‖ := by congr 1; abel
  _ <= ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ‖
        + ‖∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖ := norm_add_le _ _
  _ = ‖∫ t in b₀..s, f p t ∂μ‖ + ‖∫ t in a₀..b₀, (f p t - f q t) ∂μ‖ := by
      congr 2
      · rw [integral_interval_sub_left (J _ _ _) (J _ _ _)]
      · rw [integral_sub (J _ _ _) (J _ _ _)]
  _ <= ∫ t in Ι b₀ s, ‖f p t‖ ∂μ + ∫ t in Ι a₀ b₀, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact norm_integral_le_integral_norm_uIoc
      · exact norm_integral_le_integral_norm_uIoc
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), ‖f p t‖ ∂μ + ∫ t in Icc a b, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · apply uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ⟨hs.1.le, hs.2.le⟩ )
        simp [δpos.le]
      · exact Eventually.of_forall (fun x => norm_nonneg _)
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨a_lt.1.le, lt_b.1.le⟩ ⟨a_lt.2.le, lt_b.2.le⟩)
  _ <= ∫ t in Icc (b₀ - δ) (b₀ + δ), M + 1 ∂μ + ∫ _t in Icc a b, δ ∂μ := by
      gcongr with x hx x hx
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · calc ‖f p x‖ = ‖f q x + (f p x - f q x)‖ := by congr; abel
        _ <= ‖f q x‖ + ‖f p x - f q x‖ := norm_add_le _ _
        _ <= M + δ := by
            gcongr
            · apply hM
              change (fun x => ‖Function.uncurry f x‖) (q, x) in _
              apply mem_image_of_mem
              simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
              exact h'δ hx
            · exact le_of_lt (hv _ hp _ (h'δ hx))
        _ <= M + 1 := by linarith
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · exact le_of_lt (hv _ hp _ hx)
  _ = (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) := by simp [mul_comm]
  _ < ε := h''δ

@[fun_prop]
/--
theorem `continuous_parametric_intervalIntegral_of_continuous` / 定理 `continuous_parametric_intervalIntegral_of_continuous`

English:
theorem continuous_parametric_intervalIntegral_of_continuous
  statement: {a₀ : Real}
  proof: show Continuous ((fun p : X × Real => ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x => (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs

中文:
定理 continuous_parametric_interval整数egral_of_continuous
  结论: {a₀ : 实数}
  证明: show Continuous ((fun p : X × Real => ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x => (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs

Depends on / 依赖: Continuous, continuous_id, continuous_parametric_primitive_of_continuous
-/
theorem continuous_parametric_intervalIntegral_of_continuous {a₀ : Real}
    (hf : Continuous f.uncurry) {s : X -> Real} (hs : Continuous s) :
    Continuous fun x => ∫ t in a₀..s x, f x t ∂μ :=
  show Continuous ((fun p : X × Real => ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x => (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs

/--
theorem `continuous_parametric_intervalIntegral_of_continuous'` / 定理 `continuous_parametric_intervalIntegral_of_continuous'`

English:
theorem continuous_parametric_intervalIntegral_of_continuous'
  proof: by fun_prop

中文:
定理 continuous_parametric_interval整数egral_of_continuous'
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem continuous_parametric_intervalIntegral_of_continuous'
    (hf : Continuous f.uncurry) (a₀ b₀ : Real) :
    Continuous fun x => ∫ t in a₀..b₀, f x t ∂μ := by fun_prop

end ContinuousPrimitive

end intervalIntegral

namespace MeasureTheory

namespace IntegrableOn

open intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {μ : Measure Real} {f : Real -> E}

/--
theorem `continuousWithinAt_Ici_primitive_Ioi` / 定理 `continuousWithinAt_Ici_primitive_Ioi`

English:
theorem continuousWithinAt_Ici_primitive_Ioi
  given: {a₀ : Real} (hf : IntegrableOn f (Ioi a₀) μ)
  proof: by
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence ((Ioi a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact (hf.mono_set (Ioi_subset_Ioi ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Ioi_subset_Ioi (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Ioi] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : a₀ < x <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

中文:
定理 continuousWithinAt_Ici_primitive_Ioi
  条件: {a₀ : 实数} (hf : 整数egrableOn f (左开右无界区间 a₀) μ)
  证明: by
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence ((Ioi a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact (hf.mono_set (Ioi_subset_Ioi ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Ioi_subset_Ioi (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Ioi] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : a₀ < x <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

Depends on / 依赖: Ioi_subset_Ioi, ae_of_all, aestronglyMeasurable, aestronglyMeasurable_indicator_iff, filter_upwards, hf.mono_set, indicator, indicator_le_indicator_of_subset, integral_indicator, measurableSet_Ioi, mono_set, norm_indicator_eq_indicator_norm, self_mem_nhdsWithin, simp_rw, tendsto_integral_filter_of_dominated_convergence
-/
theorem continuousWithinAt_Ici_primitive_Ioi {a₀ : Real} (hf : IntegrableOn f (Ioi a₀) μ) :
    ContinuousWithinAt (fun b => ∫ x in Ioi b, f x ∂μ) (Ici a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence ((Ioi a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact (hf.mono_set (Ioi_subset_Ioi ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Ioi_subset_Ioi (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Ioi] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : a₀ < x <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

/--
theorem `continuousOn_Ici_primitive_Ioi` / 定理 `continuousOn_Ici_primitive_Ioi`

English:
theorem continuousOn_Ici_primitive_Ioi
  statement: [NullSingletonClass μ] {a₀ : Real}
  proof: by
  intro a (ha : a₀ <= a)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · rw [Ici_inter_Iic]
    have h_int : IntervalIntegrable f μ a₀ a :=
(intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 hf.mono_set Ioc_subset_Ioi_self
    have h_split : forall b in Icc a₀ a, ∫ x in Ioi b, f x ∂μ =
        (∫ x in Ioi a₀, f x ∂μ) - ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [← integral_Ioi_sub_Ioi hf hb.1]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a₀ a) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.sub h_cwa).congr h_split (h_split a (right_mem_Icc.2 ha))
  · simpa [ha] using (hf.mono_set (Ioi_subset_Ioi ha)).continuousWithinAt_Ici_primitive_Ioi

中文:
定理 continuousOn_Ici_primitive_Ioi
  结论: [NullSingleton类 μ] {a₀ : 实数}
  证明: by
  intro a (ha : a₀ <= a)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · rw [Ici_inter_Iic]
    have h_int : IntervalIntegrable f μ a₀ a :=
(intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 hf.mono_set Ioc_subset_Ioi_self
    have h_split : forall b in Icc a₀ a, ∫ x in Ioi b, f x ∂μ =
        (∫ x in Ioi a₀, f x ∂μ) - ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [← integral_Ioi_sub_Ioi hf hb.1]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a₀ a) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.sub h_cwa).congr h_split (h_split a (right_mem_Icc.2 ha))
  · simpa [ha] using (hf.mono_set (Ioi_subset_Ioi ha)).continuousWithinAt_Ici_primitive_Ioi

Depends on / 依赖: ContinuousWithinAt, Ici_inter_Iic, IntervalIntegrable, Ioc_subset_Ioi_self, continuousWithinAt_iff_continuous_left_right, continuousWithinAt_p, h_cwa, h_int, h_split, hf.mono_set, integral_Ioi_sub_Ioi, intervalIntegrable_iff_integrableOn_Ioc_of_le, mono_set
-/
theorem continuousOn_Ici_primitive_Ioi [NullSingletonClass μ] {a₀ : Real}
    (hf : IntegrableOn f (Ioi a₀) μ) : ContinuousOn (fun b => ∫ x in Ioi b, f x ∂μ) (Ici a₀) := by
  intro a (ha : a₀ <= a)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · rw [Ici_inter_Iic]
    have h_int : IntervalIntegrable f μ a₀ a :=
(intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 hf.mono_set Ioc_subset_Ioi_self
    have h_split : forall b in Icc a₀ a, ∫ x in Ioi b, f x ∂μ =
        (∫ x in Ioi a₀, f x ∂μ) - ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [← integral_Ioi_sub_Ioi hf hb.1]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a₀ a) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.sub h_cwa).congr h_split (h_split a (right_mem_Icc.2 ha))
  · simpa [ha] using (hf.mono_set (Ioi_subset_Ioi ha)).continuousWithinAt_Ici_primitive_Ioi

/--
theorem `continuousWithinAt_Iic_primitive_Iio` / 定理 `continuousWithinAt_Iic_primitive_Iio`

English:
theorem continuousWithinAt_Iic_primitive_Iio
  given: {a₀ : Real} (hf : IntegrableOn f (Iio a₀) μ)
  proof: by
  simp_rw [← integral_indicator measurableSet_Iio]
  apply tendsto_integral_filter_of_dominated_convergence ((Iio a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iio]
    exact (hf.mono_set (Iio_subset_Iio ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Iio_subset_Iio (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Iio] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Iio]
    by_cases hx : x < a₀ <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

中文:
定理 continuousWithinAt_Iic_primitive_Iio
  条件: {a₀ : 实数} (hf : 整数egrableOn f (左无界右开区间 a₀) μ)
  证明: by
  simp_rw [← integral_indicator measurableSet_Iio]
  apply tendsto_integral_filter_of_dominated_convergence ((Iio a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iio]
    exact (hf.mono_set (Iio_subset_Iio ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Iio_subset_Iio (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Iio] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Iio]
    by_cases hx : x < a₀ <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

Depends on / 依赖: Iio_subset_Iio, ae_of_all, aestronglyMeasurable, aestronglyMeasurable_indicator_iff, filter_upwards, hf.mono_set, indicator, indicator_le_indicator_of_subset, integral_indicator, measurableSet_Iio, mono_set, norm_indicator_eq_indicator_norm, self_mem_nhdsWithin, simp_rw, tendsto_integral_filter_of_dominated_convergence
-/
theorem continuousWithinAt_Iic_primitive_Iio {a₀ : Real} (hf : IntegrableOn f (Iio a₀) μ) :
    ContinuousWithinAt (fun b => ∫ x in Iio b, f x ∂μ) (Iic a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Iio]
  apply tendsto_integral_filter_of_dominated_convergence ((Iio a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iio]
    exact (hf.mono_set (Iio_subset_Iio ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x => ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Iio_subset_Iio (by grind)) (fun a => norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Iio] using! hf.norm
  · refine ae_of_all _ fun x => ?_
    simp only [indicator_apply, mem_Iio]
    by_cases hx : x < a₀ <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

/--
theorem `continuousOn_Iic_primitive_Iio` / 定理 `continuousOn_Iic_primitive_Iio`

English:
theorem continuousOn_Iic_primitive_Iio
  statement: [NullSingletonClass μ] {a₀ : Real}
  proof: by
  intro a (ha : a <= a₀)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · simpa [ha] using (hf.mono_set (Iio_subset_Iio ha)).continuousWithinAt_Iic_primitive_Iio
  · rw [Iic_inter_Ici]
    have h_int : IntervalIntegrable f μ a a₀ :=
(intervalIntegrable_iff_integrableOn_Ico_of_le ha).2 hf.mono_set Ico_subset_Iio_self
    have h_split : forall b in Icc a a₀, ∫ x in Iio b, f x ∂μ =
        (∫ x in Iio a₀, f x ∂μ) + ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [integral_symm b a₀, ← integral_Iio_sub_Iio' hf (hf.mono_set (Iio_subset_Iio hb.2))]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a a₀) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.add h_cwa).congr h_split (h_split a (left_mem_Icc.2 ha))

中文:
定理 continuousOn_Iic_primitive_Iio
  结论: [NullSingleton类 μ] {a₀ : 实数}
  证明: by
  intro a (ha : a <= a₀)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · simpa [ha] using (hf.mono_set (Iio_subset_Iio ha)).continuousWithinAt_Iic_primitive_Iio
  · rw [Iic_inter_Ici]
    have h_int : IntervalIntegrable f μ a a₀ :=
(intervalIntegrable_iff_integrableOn_Ico_of_le ha).2 hf.mono_set Ico_subset_Iio_self
    have h_split : forall b in Icc a a₀, ∫ x in Iio b, f x ∂μ =
        (∫ x in Iio a₀, f x ∂μ) + ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [integral_symm b a₀, ← integral_Iio_sub_Iio' hf (hf.mono_set (Iio_subset_Iio hb.2))]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a a₀) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.add h_cwa).congr h_split (h_split a (left_mem_Icc.2 ha))

Depends on / 依赖: Ico_subset_Iio_self, Iic_inter_Ici, Iio_subset_Iio, IntervalIntegrable, continuousWithinAt_Iic_primitive_Iio, continuousWithinAt_iff_continuous_left_right, h_int, h_split, hf.mono_set, integral_Iio_sub_Iio, integral_symm, intervalIntegrable_iff_integrableOn_Ico_of_le, mono_set
-/
theorem continuousOn_Iic_primitive_Iio [NullSingletonClass μ] {a₀ : Real}
    (hf : IntegrableOn f (Iio a₀) μ) : ContinuousOn (fun b => ∫ x in Iio b, f x ∂μ) (Iic a₀) := by
  intro a (ha : a <= a₀)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · simpa [ha] using (hf.mono_set (Iio_subset_Iio ha)).continuousWithinAt_Iic_primitive_Iio
  · rw [Iic_inter_Ici]
    have h_int : IntervalIntegrable f μ a a₀ :=
(intervalIntegrable_iff_integrableOn_Ico_of_le ha).2 hf.mono_set Ico_subset_Iio_self
    have h_split : forall b in Icc a a₀, ∫ x in Iio b, f x ∂μ =
        (∫ x in Iio a₀, f x ∂μ) + ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [integral_symm b a₀, ← integral_Iio_sub_Iio' hf (hf.mono_set (Iio_subset_Iio hb.2))]
    have h_cwa : ContinuousWithinAt (fun b => ∫ x in a₀..b, f x ∂μ) (Icc a a₀) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.add h_cwa).congr h_split (h_split a (left_mem_Icc.2 ha))

/--
theorem `continuousOn_Ici_primitive_Ici` / 定理 `continuousOn_Ici_primitive_Ici`

English:
theorem continuousOn_Ici_primitive_Ici
  statement: [NullSingletonClass μ] {a₀ : Real}
  proof: by
  simp_rw [integral_Ici_eq_integral_Ioi]
  exact (hf.mono_set Ioi_subset_Ici_self).continuousOn_Ici_primitive_Ioi

中文:
定理 continuousOn_Ici_primitive_Ici
  结论: [NullSingleton类 μ] {a₀ : 实数}
  证明: by
  simp_rw [integral_Ici_eq_integral_Ioi]
  exact (hf.mono_set Ioi_subset_Ici_self).continuousOn_Ici_primitive_Ioi

Depends on / 依赖: Ioi_subset_Ici_self, continuousOn_Ici_primitive_Ioi, hf.mono_set, integral_Ici_eq_integral_Ioi, mono_set, simp_rw
-/
theorem continuousOn_Ici_primitive_Ici [NullSingletonClass μ] {a₀ : Real}
    (hf : IntegrableOn f (Ici a₀) μ) : ContinuousOn (fun b => ∫ x in Ici b, f x ∂μ) (Ici a₀) := by
  simp_rw [integral_Ici_eq_integral_Ioi]
  exact (hf.mono_set Ioi_subset_Ici_self).continuousOn_Ici_primitive_Ioi

/--
theorem `continuousOn_Iic_primitive_Iic` / 定理 `continuousOn_Iic_primitive_Iic`

English:
theorem continuousOn_Iic_primitive_Iic
  statement: [NullSingletonClass μ] {a₀ : Real}
  proof: by
  simp_rw [integral_Iic_eq_integral_Iio]
  exact (hf.mono_set Iio_subset_Iic_self).continuousOn_Iic_primitive_Iio

中文:
定理 continuousOn_Iic_primitive_Iic
  结论: [NullSingleton类 μ] {a₀ : 实数}
  证明: by
  simp_rw [integral_Iic_eq_integral_Iio]
  exact (hf.mono_set Iio_subset_Iic_self).continuousOn_Iic_primitive_Iio

Depends on / 依赖: Iio_subset_Iic_self, continuousOn_Iic_primitive_Iio, hf.mono_set, integral_Iic_eq_integral_Iio, mono_set, simp_rw
-/
theorem continuousOn_Iic_primitive_Iic [NullSingletonClass μ] {a₀ : Real}
    (hf : IntegrableOn f (Iic a₀) μ) : ContinuousOn (fun b => ∫ x in Iic b, f x ∂μ) (Iic a₀) := by
  simp_rw [integral_Iic_eq_integral_Iio]
  exact (hf.mono_set Iio_subset_Iic_self).continuousOn_Iic_primitive_Iio

end IntegrableOn

end MeasureTheory

end DominatedConvergenceTheorem
