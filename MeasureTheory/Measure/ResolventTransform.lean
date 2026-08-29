/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Resolvent Transform of a Measure

Given a normed algebra `A` over a normed field `𝕜`, and `μ : Measure 𝕜`, we define the
resolvent transform of `μ` by the formula

`resolventTransform μ a = ∫ x, resolvent a x ∂μ = ∫ x, (↑ₐ x - a)⁻¹ʳ ∂μ`

This is not a standard notion in the literature, but specializes to a few standard notions,
namely the case `𝕜 = ℝ` and `A = ℂ` is the Stieltjes transform, and the case `𝕜 = A = ℂ` is the
Cauchy transform, given by the formulas:

`∫ (x : ℝ), (↑x - a)⁻¹ ∂μ` and `∫ (x : ℂ), (↑x - a)⁻¹ ∂μ` respectively.

## Main definitions

* `resolventTransform μ a`: The resolvent transform of a measure `μ` at `a`

## Main statements

* `hasDerivAt_resolventTransform`: For any `a` not in the support of `μ`,
  the `resolventTransform` has derivative `∫ x, resolvent a x ^ 2 ∂u` at `a`.
* `analyticOn_resolventTransform`: In the case `A = ℂ`, the `resolventTransform`
  is holomorphic on the complement of `μ.support`.

## Tags

resolvent transform, Stieljes transform, Cauchy transform
-/

public section

variable {𝕜 A : Type*}

open MeasureTheory Measure Metric Complex spectrum

open scoped Topology

namespace MeasureTheory

section resolvent

variable [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]

set_option backward.isDefEq.respectTransparency.types false in
@[fun_prop]
/--
theorem `measurable_resolvent` / 定理 `measurable_resolvent`

English:
theorem measurable_resolvent
  statement: {a : A} [OpensMeasurableSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  proof: by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx => hasDerivAt_resolvent_const_left hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert con

中文:
定理 measurable_resolvent
  结论: {a : A} [OpensMeasurable空间 𝕜] [赋范环 A] [赋范代数 𝕜 A]
  证明: by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx => hasDerivAt_resolvent_const_left hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert con

Depends on / 依赖: ContinuousOn, HasDerivAt, HasDerivAt.continuousOn, MeasurableSet, classical, continuousOn, continuousOn_iff_continuous_domRestrict, continuous_const, convert, h1.measurable_piecewise, hasDerivAt_resolvent_const_left, isOpen_resolventSet, measurableSet, measurable_piecewise, resolvent, resolventSet
-/
theorem measurable_resolvent {a : A} [OpensMeasurableSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] :
    Measurable (resolvent (R := 𝕜) a) := by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx => hasDerivAt_resolvent_const_left hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_const (y := (0 : A)) with x
    simp
  have h3 : MeasurableSet (resolventSet 𝕜 a) := (isOpen_resolventSet a).measurableSet
  simpa using h1.measurable_piecewise h2 h3

variable [CompleteSpace 𝕜] [NormedDivisionRing A] [NormedAlgebra 𝕜 A]

/--
theorem `norm_resolvent_le_inv_infDist_support` / 定理 `norm_resolvent_le_inv_infDist_support`

English:
theorem norm_resolvent_le_inv_infDist_support
  statement: {μ : Measure 𝕜} {a : A}
  proof: by
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  ha

中文:
定理 norm_resolvent_le_inv_infDist_support
  结论: {μ : 测度 𝕜} {a : A}
  证明: by
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  ha

Depends on / 依赖: IsClosed, IsClosed.notMem_iff_infDist_pos, IsClosedEmbedding, Ring.inverse_eq_inv, Set.nonempty_of_mem, Topology, Topology.IsClosedEmbedding.isClosed_iff_image_isClosed, algebraMap, algebraMap_isometry, dist_comm, dist_eq_norm, infDist, infDist_le_dist_of_mem, inverse_eq_inv, isClosedEmbedding, isClosed_iff_image_isClosed, isClosed_support, nonempty_of_mem, norm_in, notMem_iff_infDist_pos
-/
theorem norm_resolvent_le_inv_infDist_support {μ : Measure 𝕜} {a : A}
    (hz : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x in μ.support) :
    ‖resolvent a x‖ <= (infDist a (algebraMap 𝕜 A '' μ.support))⁻¹ := by
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  have : infDist a (algebraMap 𝕜 A '' μ.support) <= ‖(algebraMap 𝕜 A) x - a‖ := by
    grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x), ← dist_eq_norm, dist_comm]
    simp [hx]
  grw [resolvent, Ring.inverse_eq_inv', norm_inv, inv_le_inv₀ (by linarith) (by positivity), this]

/--
theorem `integrable_resolvent` / 定理 `integrable_resolvent`

English:
theorem integrable_resolvent
  statement: [HereditarilyLindelofSpace 𝕜] [OpensMeasurableSpace 𝕜]
  proof: by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

中文:
定理 integrable_resolvent
  结论: [HereditarilyLindelof空间 𝕜] [OpensMeasurable空间 𝕜]
  证明: by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

Depends on / 依赖: HasFiniteIntegral, HasFiniteIntegral.of_bounded, filter_upwards, fun_prop, norm_resolvent_le_inv_infDist_support, of_bounded, support_mem_ae
-/
theorem integrable_resolvent [HereditarilyLindelofSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.support) :
    Integrable (resolvent a) μ := by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

end resolvent

section Definition

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra Real A] [NormedAlgebra 𝕜 A]
  {m𝕜 : MeasurableSpace 𝕜}

/-- The resolvent transform of a measure. -/
noncomputable
/--
Definition of `resolventTransform` / `resolventTransform` 的定义

English:
definition resolventTransform
  signature: (μ : Measure 𝕜) (a : A)
  body: ∫ x, resolvent a x ∂μ

中文:
定义 resolventTransform
  签名: (μ : 测度 𝕜) (a : A)
  定义体: ∫ x, resolvent a x ∂μ

Depends on / 依赖: resolvent
-/
def resolventTransform (μ : Measure 𝕜) (a : A) :=
  ∫ x, resolvent a x ∂μ

/--
lemma `resolventTransform_def` / 引理 `resolventTransform_def`

English:
lemma resolventTransform_def
  given: (μ : Measure 𝕜)
  proof: by rfl

中文:
引理 resolventTransform_def
  条件: (μ : 测度 𝕜)
  证明: by rfl
-/
lemma resolventTransform_def (μ : Measure 𝕜) :
    resolventTransform μ = fun (a : A) => (∫ x, resolvent a x ∂μ) := by rfl

/--
lemma `resolventTransform_apply` / 引理 `resolventTransform_apply`

English:
lemma resolventTransform_apply
  given: (μ : Measure 𝕜) (a : A)
  proof: by rfl

@[simp]

中文:
引理 resolventTransform_apply
  条件: (μ : 测度 𝕜) (a : A)
  证明: by rfl

@[simp]
-/
lemma resolventTransform_apply (μ : Measure 𝕜) (a : A) :
    resolventTransform μ a = ∫ x, resolvent a x ∂μ := by rfl

@[simp]
/--
lemma `resolventTransform_zero_measure` / 引理 `resolventTransform_zero_measure`

English:
lemma resolventTransform_zero_measure
  statement: resolventTransform (0 : Measure 𝕜) = (0 : A -> A)
  proof: by
  ext
  simp [resolventTransform_def]

@[simp]

中文:
引理 resolventTransform_zero_measure
  结论: resolventTransform (0 : 测度 𝕜) = (0 : A -> A)
  证明: by
  ext
  simp [resolventTransform_def]

@[simp]

Depends on / 依赖: resolventTransform_def
-/
lemma resolventTransform_zero_measure : resolventTransform (0 : Measure 𝕜) = (0 : A -> A) := by
  ext
  simp [resolventTransform_def]

@[simp]
/--
lemma `resolventTransform_dirac` / 引理 `resolventTransform_dirac`

English:
lemma resolventTransform_dirac
  statement: [MeasurableSingletonClass 𝕜] [CompleteSpace A]
  proof: by
  simp [resolventTransform_def]

中文:
引理 resolventTransform_dirac
  结论: [MeasurableSingleton类 𝕜] [完备空间 A]
  证明: by
  simp [resolventTransform_def]

Depends on / 依赖: resolventTransform_def
-/
lemma resolventTransform_dirac [MeasurableSingletonClass 𝕜] [CompleteSpace A]
    (x : 𝕜) (a : A) : resolventTransform (.dirac x) a = resolvent a x := by
  simp [resolventTransform_def]

end Definition

section Deriv

variable [NontriviallyNormedField 𝕜] [HereditarilyLindelofSpace 𝕜] [CompleteSpace 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/--
theorem `hasDerivAt_resolventTransform` / 定理 `hasDerivAt_resolventTransform`

English:
theorem hasDerivAt_resolventTransform
  statement: [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 𝕜}
  proof: by
  by_cases! h : μ.support.Nonempty; swap
  · simp [support_eq_empty_iff.mp h]
  rw [resolventTransform_def]
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (h.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClos

中文:
定理 hasDerivAt_resolventTransform
  结论: [RCLike A] [赋范代数 𝕜 A] {μ : 测度 𝕜}
  证明: by
  by_cases! h : μ.support.Nonempty; swap
  · simp [support_eq_empty_iff.mp h]
  rw [resolventTransform_def]
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (h.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClos

Depends on / 依赖: IsClosed, IsClosed.notMem_iff_infDist_pos, IsClosedEmbedding, Nonempty, Topology, Topology.IsClosedEmbedding.isClosed_iff_image_isClosed, algebraMap, algebraMap_isometry, ball_mem_nhds, h.image, hs_z, infDist, isClosedEmbedding, isClosed_iff_image_isClosed, isClosed_support, notMem_iff_infDist_pos, resolventTransform_def, support, support.Nonempty, support_eq_empty_iff
-/
theorem hasDerivAt_resolventTransform [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 𝕜}
    [IsFiniteMeasure μ] (a : A) (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    HasDerivAt (resolventTransform μ) (∫ x, resolvent a x ^ 2 ∂μ) a := by
  by_cases! h : μ.support.Nonempty; swap
  · simp [support_eq_empty_iff.mp h]
  rw [resolventTransform_def]
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (h.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  let s : Set A := ball a ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)
  have hs_z : s in 𝓝 a := ball_mem_nhds _ (by positivity)
  have hs_μ : s subseteq (algebraMap 𝕜 A '' μ.support)ᶜ := by
    unfold s
    grw [ball_subset_ball, ball_infDist_subset_compl]
    grind
  have resolvent_meas : forallᶠ w in nhds a, AEStronglyMeasurable (resolvent w) μ := by
    filter_upwards with _ using by fun_prop
  have resolvent'_bound : forallᵐ x ∂μ, forall w in s,
      ‖(resolvent w x) ^ 2‖ <= ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)⁻¹ ^ 2 := by
    filter_upwards [support_mem_ae] with x hx w hw
    grw [resolvent, Ring.inverse_eq_inv, norm_pow, norm_inv]
    gcongr
    calc infDist a (algebraMap 𝕜 A '' μ.support) / 2
      _ <= infDist a (algebraMap 𝕜 A '' μ.support)
        - infDist a (algebraMap 𝕜 A '' μ.support) / 2 := by grind
      _ <= ‖(algebraMap 𝕜 A) x - a‖ - ‖a - w‖ := by
        gcongr
        · grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x) (by simp [hx]), dist_comm,
            dist_eq_norm]
        · apply le_of_lt
          simpa [s, ← dist_eq_norm, dist_comm w a] using hw
      _ <= ‖(algebraMap 𝕜 A) x - w‖ := by grw [norm_sub_le_norm_add]; grind
  have h_deriv : forallᵐ x ∂μ, forall w in s, HasDerivAt (fun w => resolvent w x) (resolvent w x ^ 2) w := by
    filter_upwards [support_mem_ae] with x hx w hw
    apply hasDerivAt_resolvent_const_right
    replace hw := hs_μ hw
    contrapose! hw
    rw [Set.notMem_compl_iff]
    use x, hx
    simpa [resolventSet, sub_eq_zero] using hw
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
.2 (integrable_resolvent (by simp [ha])) (by fun_prop) resolvent'_bound (by fun_prop) h_deriv

/--
theorem `analyticOn_resolventTransform` / 定理 `analyticOn_resolventTransform`

English:
theorem analyticOn_resolventTransform
  given: [NormedAlgebra 𝕜 Complex] {μ : Measure 𝕜} [IsFiniteMeasure μ]
  proof: by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_resolventTransform z hz).differentiableAt.differentiableWithinAt
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
  exact (algebraMap_isometry 𝕜 Complex

中文:
定理 analyticOn_resolventTransform
  条件: [赋范代数 𝕜 复形] {μ : 测度 𝕜} [是有限测度 μ]
  证明: by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_resolventTransform z hz).differentiableAt.differentiableWithinAt
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
  exact (algebraMap_isometry 𝕜 Complex

Depends on / 依赖: IsClosedEmbedding, Topology, Topology.IsClosedEmbedding.isClosed_iff_image_isClosed, algebraMap_isometry, analyticOn_iff_differentiableOn, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, hasDerivAt_resolventTransform, isClosedEmbedding, isClosed_iff_image_isClosed, isClosed_support, isOpen_compl_iff, isOpen_compl_iff.mpr
-/
theorem analyticOn_resolventTransform [NormedAlgebra 𝕜 Complex] {μ : Measure 𝕜} [IsFiniteMeasure μ] :
    AnalyticOn Complex (resolventTransform μ) (algebraMap 𝕜 Complex '' μ.support)ᶜ := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_resolventTransform z hz).differentiableAt.differentiableWithinAt
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
  exact (algebraMap_isometry 𝕜 Complex).isClosedEmbedding

end Deriv

end MeasureTheory
