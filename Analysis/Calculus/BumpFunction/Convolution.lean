/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Convolution with a bump function

In this file we prove lemmas about convolutions `(φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀`,
where `φ : ContDiffBump 0` is a smooth bump function.

We prove that this convolution is equal to `g x₀`
if `g` is a constant on `Metric.ball x₀ φ.rOut`.
We also provide estimates in the case if `g x` is close to `g x₀` on this ball.

## Main results

- `ContDiffBump.convolution_tendsto_right_of_continuous`:
  Let `g` be a continuous function; let `φ i` be a family of `ContDiffBump 0` functions with.
  If `(φ i).rOut` tends to zero along a filter `l`,
  then `((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀` tends to `g x₀` along the same filter.
- `ContDiffBump.convolution_tendsto_right`: generalization of the above lemma.
- `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`: let `g` be a locally
  integrable function. Then the convolution of `g` with a family of bump functions with
  support tending to `0` converges almost everywhere to `g`.

## Keywords

convolution, smooth function, bump function
-/

public section

universe uG uE'

open ContinuousLinearMap Metric MeasureTheory Filter Function Measure Set
open scoped Convolution Topology

namespace ContDiffBump

variable {G : Type uG} {E' : Type uE'} [NormedAddCommGroup E'] {g : G -> E'} [MeasurableSpace G]
  {μ : MeasureTheory.Measure G} [NormedSpace Real E'] [NormedAddCommGroup G] [NormedSpace Real G]
  [CompleteSpace E'] {φ : ContDiffBump (0 : G)} {x₀ : G}

/--
theorem `convolution_eq_right` / 定理 `convolution_eq_right`

English:
theorem convolution_eq_right
  given: [HasContDiffBump G] {x₀ : G} (hg : forall x in ball x₀ φ.rOut, g x = g x₀)
  proof: by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

中文:
定理 convolution_eq_right
  条件: [有余ntDiffBump G] {x₀ : G} (hg : 对任意 x in ball x₀ φ.rOut, g x = g x₀)
  证明: by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

Depends on / 依赖: convolution_eq_right, integral_smul_const, lsmul_apply, simp_rw, subset, support_eq, support_eq.subset
-/
theorem convolution_eq_right [HasContDiffBump G] {x₀ : G} (hg : forall x in ball x₀ φ.rOut, g x = g x₀) :
    (φ ⋆[lsmul Real Real, μ] g : G -> E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variable [BorelSpace G] [FiniteDimensional Real G]

/--
theorem `normed_convolution_eq_right` / 定理 `normed_convolution_eq_right`

English:
theorem normed_convolution_eq_right
  statement: [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {x₀ : G}
  proof: by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)

中文:
定理 normed_convolution_eq_right
  结论: [是局部有限测度 μ] [μ.是OpenPosMeasure] {x₀ : G}
  证明: by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)

Depends on / 依赖: convolution_eq_right, integral_normed_smul, subset, support_normed_eq, support_normed_eq.subset
-/
theorem normed_convolution_eq_right [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {x₀ : G}
    (hg : forall x in ball x₀ φ.rOut, g x = g x₀) :
    (φ.normed μ ⋆[lsmul Real Real, μ] g : G -> E') x₀ = g x₀ := by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)

variable [μ.IsAddHaarMeasure]

/--
theorem `dist_normed_convolution_le` / 定理 `dist_normed_convolution_le`

English:
theorem dist_normed_convolution_le
  statement: {x₀ : G} {ε : Real} (hmg : AEStronglyMeasurable g μ)
  proof: dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

中文:
定理 dist_normed_convolution_le
  结论: {x₀ : G} {ε : 实数} (hmg : AEStronglyMeasurable g μ)
  证明: dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

Depends on / 依赖: dist_convolution_le, dist_self, integral_normed, mem_ball_self, nonneg_normed, rOut_pos, simp_rw, subset, support_normed_eq, support_normed_eq.subset
-/
theorem dist_normed_convolution_le {x₀ : G} {ε : Real} (hmg : AEStronglyMeasurable g μ)
    (hg : forall x in ball x₀ φ.rOut, dist (g x) (g x₀) <= ε) :
    dist ((φ.normed μ ⋆[lsmul Real Real, μ] g : G -> E') x₀) (g x₀) <= ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions
  such that `(φ i).rOut` tends to `0` as `i` tends to `l`;
* `g i` is `μ`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
nonrec theorem convolution_tendsto_right {ι} {φ : ι -> ContDiffBump (0 : G)} {g : ι -> G -> E'}
    {k : ι -> G} {x₀ : G} {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hig : forallᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul Real Real, μ] g i) (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (Eventually.of_forall fun i => (φ i).nonneg_normed)
    (Eventually.of_forall fun i => (φ i).integral_normed) (tendsto_support_normed_smallSets hφ) hig
    hcg hk

/--
theorem `convolution_tendsto_right_of_continuous` / 定理 `convolution_tendsto_right_of_continuous`

English:
theorem convolution_tendsto_right_of_continuous
  statement: {ι} {φ : ι -> ContDiffBump (0 : G)} {l : Filter ι}
  proof: convolution_tendsto_right hφ (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

中文:
定理 convolution_tendsto_right_of_continuous
  结论: {ι} {φ : ι -> 余ntDiffBump (0 : G)} {l : 滤子 ι}
  证明: convolution_tendsto_right hφ (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, convolution_tendsto_right, hg.aestronglyMeasurable, hg.tendsto, of_forall, tendsto, tendsto_const_nhds, tendsto_snd
-/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι -> ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul Real Real, μ] g) x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

/--
theorem `ae_convolution_tendsto_right_of_locallyIntegrable` / 定理 `ae_convolution_tendsto_right_of_locallyIntegrable`

English:
theorem ae_convolution_tendsto_right_of_locallyIntegrable
  proof: by
  -- By Lebesgue differentiation theorem, the average of `g` on a small ball converges
  -- almost everywhere to the value of `g` as the radius shrinks to zero.
  -- We will see that this set of points satisfies the desired conclusion.
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_ave

中文:
定理 ae_convolution_tendsto_right_of_locally整数egrable
  证明: by
  -- By Lebesgue differentiation theorem, the average of `g` on a small ball converges
  -- almost everywhere to the value of `g` as the radius shrinks to zero.
  -- We will see that this set of points satisfies the desired conclusion.
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_ave
-/
theorem ae_convolution_tendsto_right_of_locallyIntegrable
    {ι} {φ : ι -> ContDiffBump (0 : G)} {l : Filter ι} {K : Real}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (h'φ : forallᶠ i in l, (φ i).rOut <= K * (φ i).rIn) (hg : LocallyIntegrable g μ) : forallᵐ x₀ ∂μ,
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul Real Real, μ] g) x₀) l (𝓝 (g x₀)) := by
  -- By Lebesgue differentiation theorem, the average of `g` on a small ball converges
  -- almost everywhere to the value of `g` as the radius shrinks to zero.
  -- We will see that this set of points satisfies the desired conclusion.
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hg] with x₀ h₀
  simp only [convolution_eq_swap, lsmul_apply]
  have hφ' : Tendsto (fun i => (φ i).rOut) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ, Eventually.of_forall (fun i => (φ i).rOut_pos)⟩
  have := (h₀.comp (Besicovitch.tendsto_filterAt μ x₀)).comp hφ'
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (K ^ (Module.finrank Real G)) this
  · filter_upwards with i using
      hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr (fun i => ?_)
    rw [← integral_neg_eq_self]
    simp only [sub_neg_eq_add, integral_add_left_eq_self, integral_normed]
  · filter_upwards with i
    change support ((ContDiffBump.normed (φ i) μ) ∘ (fun y => x₀ - y)) subseteq closedBall x₀ (φ i).rOut
    simp only [support_comp_eq_preimage, support_normed_eq]
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right] at hx
    simpa [dist_eq_norm_sub'] using hx.le
  · filter_upwards [h'φ] with i hi x
    rw [abs_of_nonneg (nonneg_normed _ _)]; rw [addHaar_real_closedBall_center]
    exact (φ i).normed_le_div_measure_closedBall_rOut _ _ hi _

end ContDiffBump
