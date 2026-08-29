/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Measurable
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Rademacher's theorem: a Lipschitz function is differentiable almost everywhere

This file proves Rademacher's theorem: a Lipschitz function between finite-dimensional real vector
spaces is differentiable almost everywhere with respect to the Lebesgue measure. This is the content
of `LipschitzWith.ae_differentiableAt`. Versions for functions which are Lipschitz on sets are also
given (see `LipschitzOnWith.ae_differentiableWithinAt`).

## Implementation

There are many proofs of Rademacher's theorem. We follow the one by Morrey, which is not the most
elementary but maybe the most elegant once necessary prerequisites are set up.
* Step 0: without loss of generality, one may assume that `f` is real-valued.
* Step 1: Since a one-dimensional Lipschitz function has bounded variation, it is differentiable
  almost everywhere. With a Fubini argument, it follows that given any vector `v` then `f` is ae
  differentiable in the direction of `v`. See `LipschitzWith.ae_lineDifferentiableAt`.
* Step 2: the line derivative `LineDeriv ℝ f x v` is ae linear in `v`. Morrey proves this by a
  duality argument, integrating against a smooth compactly supported function `g`, passing the
  derivative to `g` by integration by parts, and using the linearity of the derivative of `g`.
  See `LipschitzWith.ae_lineDeriv_sum_eq`.
* Step 3: consider a countable dense set `s` of directions. Almost everywhere, the function `f`
  is line-differentiable in all these directions and the line derivative is linear. Approximating
  any direction by a direction in `s` and using the fact that `f` is Lipschitz to control the error,
  it follows that `f` is Fréchet-differentiable at these points.
  See `LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`.

## References

* [Pertti Mattila, Geometry of sets and measures in Euclidean spaces, Theorem 7.3][Federer1996]
-/

public section

open Filter MeasureTheory Measure Module Metric Set Asymptotics

open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] {C D : Real>=0} {f g : E -> Real} {s : Set E}
  {μ : Measure E}

namespace LipschitzWith



/--
theorem `memLp_lineDeriv` / 定理 `memLp_lineDeriv`

English:
theorem memLp_lineDeriv
  given: (hf : LipschitzWith C f) (v : E)
  proof: memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (.of_forall fun _x => norm_lineDeriv_le_of_lipschitz Real hf)

中文:
定理 memLp_lineDeriv
  条件: (hf : LipschitzWith C f) (v : E)
  证明: memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (.of_forall fun _x => norm_lineDeriv_le_of_lipschitz Real hf)

Depends on / 依赖: aestronglyMeasurable_lineDeriv, continuous, hf.continuous, memLp_top_of_bound, norm_lineDeriv_le_of_lipschitz, of_forall
-/
theorem memLp_lineDeriv (hf : LipschitzWith C f) (v : E) :
    MemLp (fun x => lineDeriv Real f x v) ∞ μ :=
  memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (.of_forall fun _x => norm_lineDeriv_le_of_lipschitz Real hf)

variable [FiniteDimensional Real E] [IsAddHaarMeasure μ]

/--
theorem `ae_lineDifferentiableAt` / 定理 `ae_lineDifferentiableAt`

English:
theorem ae_lineDifferentiableAt
  proof: by
  let L : Real ->L[Real] E := ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) v
  suffices A : forall p, forallᵐ (t : Real) ∂volume, LineDifferentiableAt Real f (p + t • v) v from
    ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
      (measurableSet_lineDifferentiableAt hf.contin

中文:
定理 ae_lineDifferentiableAt
  证明: by
  let L : Real ->L[Real] E := ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) v
  suffices A : forall p, forallᵐ (t : Real) ∂volume, LineDifferentiableAt Real f (p + t • v) v from
    ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
      (measurableSet_lineDifferentiableAt hf.contin

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRight, DifferentiableAt, L.lipschitz, L.toLinearMap, LineDifferentiableAt, LipschitzWith, LipschitzWith.const, ae_differentiableAt_real, ae_mem_of_ae_add_linearMap_mem, continuous, filter_upwards, hf.comp, hf.continuous, lipschitz, measurableSet_lineDifferentiableAt, smulRight, toLinearMap, volume
-/
theorem ae_lineDifferentiableAt
    (hf : LipschitzWith C f) (v : E) :
    forallᵐ p ∂μ, LineDifferentiableAt Real f p v := by
  let L : Real ->L[Real] E := ContinuousLinearMap.smulRight (1 : Real ->L[Real] Real) v
  suffices A : forall p, forallᵐ (t : Real) ∂volume, LineDifferentiableAt Real f (p + t • v) v from
    ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
      (measurableSet_lineDifferentiableAt hf.continuous) A
  intro p
  have : forallᵐ (s : Real), DifferentiableAt Real (fun t => f (p + t • v)) s :=
    (hf.comp ((LipschitzWith.const p).add L.lipschitz)).ae_differentiableAt_real
  filter_upwards [this] with s hs
  have h's : DifferentiableAt Real (fun t => f (p + t • v)) (s + 0) := by simpa using hs
  have : DifferentiableAt Real (fun t => s + t) 0 := differentiableAt_id.const_add _
  simp only [LineDifferentiableAt]
  convert! h's.comp 0 this with _ t
  simp only [add_assoc, Function.comp_apply, add_smul]

/--
theorem `locallyIntegrable_lineDeriv` / 定理 `locallyIntegrable_lineDeriv`

English:
theorem locallyIntegrable_lineDeriv
  given: (hf : LipschitzWith C f) (v : E)
  proof: (hf.memLp_lineDeriv v).locallyIntegrable le_top

中文:
定理 locallyIntegrable_lineDeriv
  条件: (hf : LipschitzWith C f) (v : E)
  证明: (hf.memLp_lineDeriv v).locallyIntegrable le_top

Depends on / 依赖: hf.memLp_lineDeriv, le_top, locallyIntegrable, memLp_lineDeriv
-/
theorem locallyIntegrable_lineDeriv (hf : LipschitzWith C f) (v : E) :
    LocallyIntegrable (fun x => lineDeriv Real f x v) μ :=
  (hf.memLp_lineDeriv v).locallyIntegrable le_top


/--
theorem `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul` / 定理 `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul`

English:
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
  proof: by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasu

中文:
定理 integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
  证明: by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasu

Depends on / 依赖: AEMeasurable, AEMeasurable.aestronglyMeasurable, AEStronglyMeasurable, AEStronglyMeasurable.mul, AEStronglyMeasurable.sub, add_const, aemeasurable_id, aestronglyMeasurable, aestronglyMeasurable_const, aestronglyMeasurable_const.fun_smul, comp_aemeasurable, continuous, filter_upwards, fun_smul, hf.continuous.measurable.aestronglyMeasurable, hf.continuous.measurable.comp_aemeasurable, hg.aestronglyMeasurable, measurable, self_mem_nhdsWithin, tendsto_integral_filter_of_dominated_convergence
-/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
    (hf : LipschitzWith C f) (hg : Integrable g μ) (v : E) :
    Tendsto (fun (t : Real) => ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv Real f x v * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    filter_upwards with x
    calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
      = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, ht.le]
    _ <= (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
      gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
    _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg ht.le]
  · exact hg.norm.const_mul _
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/--
theorem `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'` / 定理 `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'`

English:
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
  proof: by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x => (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
 

中文:
定理 integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
  证明: by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x => (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
 

Depends on / 依赖: AEMeasurable, AEMeasurable.aestronglyMeasurable, AEStronglyMeasurable, AEStronglyMeasurable.mul, AEStronglyMeasurable.sub, IsCompact, IsCompact.cthickening, K.indicator, K_compact, aemeasu, aestronglyMeasurable, aestronglyMeasurable_const, aestronglyMeasurable_const.fun_smul, comp_aemeasurable, continuous, cthickening, filter_upwards, fun_smul, hf.continuous.measurable.aestronglyMeasurable, hf.continuous.measurable.comp_aemeasurable
-/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (hf : LipschitzWith C f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) :
    Tendsto (fun (t : Real) => ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv Real f x v * g x ∂μ)) := by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x => (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have t_pos : 0 < t := ht.1
    filter_upwards with x
    by_cases hx : x in K
    · calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, t_pos.le]
      _ <= (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg t_pos.le]
      _ = K.indicator (fun x => (C * ‖v‖) * ‖g x‖) x := by rw [indicator_of_mem hx]
    · have A : f x = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : f (x + t • v) = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        apply mem_cthickening_of_dist_le _ _ (‖v‖) (tsupport f) (subset_tsupport _ hx)
        simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t_pos.le]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B, A, _root_.sub_self, smul_eq_mul, mul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun y _hy => by positivity) _
  · rw [integrable_indicator_iff K_compact.measurableSet]
    exact ContinuousOn.integrableOn_compact K_compact (by fun_prop)
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/--
theorem `integral_lineDeriv_mul_eq` / 定理 `integral_lineDeriv_mul_eq`

English:
theorem integral_lineDeriv_mul_eq
  proof: by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of va

中文:
定理 integral_lineDeriv_mul_eq
  证明: by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of va
-/
theorem integral_lineDeriv_mul_eq
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv Real f x v * g x ∂μ = ∫ x, lineDeriv Real g x (-v) * f x ∂μ := by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of variables `y = x + t v`), so the limits also coincide. -/
  have A : Tendsto (fun (t : Real) => ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv Real f x v * g x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
      hf (hg.continuous.integrable_of_hasCompactSupport h'g) v
  have B : Tendsto (fun (t : Real) => ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv Real g x (-v) * f x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' hg h'g hf.continuous (-v)
  suffices S1 : forall (t : Real), ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ =
                            ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ by
    simp only [S1] at A; exact tendsto_nhds_unique A B
  intro t
  suffices S2 : ∫ x, (f (x + t • v) - f x) * g x ∂μ = ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ by
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, S2, mul_comm (f _)]
  have S3 : ∫ x, f (x + t • v) * g x ∂μ = ∫ x, f x * g (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]; simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub]; rw [integral_sub]; rw [S3]
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hf.continuous.mul (hg.continuous.comp (continuous_add_const _))
    · exact (h'g.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left
  · apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_add_const _)).mul hg.continuous
    · exact h'g.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left

/--
theorem `ae_lineDeriv_sum_eq` / 定理 `ae_lineDeriv_sum_eq`

English:
theorem ae_lineDeriv_sum_eq
  proof: by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.

中文:
定理 ae_lineDeriv_sum_eq
  证明: by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.
-/
theorem ae_lineDeriv_sum_eq
    (hf : LipschitzWith C f) {ι : Type*} (s : Finset ι) (a : ι -> Real) (v : ι -> E) :
    forallᵐ x ∂μ, lineDeriv Real f x (∑ i in s, a i • v i) = ∑ i in s, a i • lineDeriv Real f x (v i) := by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.locallyIntegrable_lineDeriv _)
    (locallyIntegrable_finsetSum _ (fun i hi => (hf.locallyIntegrable_lineDeriv (v i)).smul (a i)))
    (fun g g_smooth g_comp => ?_)
  simp_rw [Finset.smul_sum]
  have A : forall i in s, Integrable (fun x => g x • (a i • fun x => lineDeriv Real f x (v i)) x) μ :=
    fun i hi => (g_smooth.continuous.integrable_of_hasCompactSupport g_comp).smul_of_top_left
      ((hf.memLp_lineDeriv (v i)).const_smul (a i))
  rw [integral_finsetSum _ A]
  suffices S1 : ∫ x, lineDeriv Real f x (∑ i in s, a i • v i) * g x ∂μ
      = ∑ i in s, a i * ∫ x, lineDeriv Real f x (v i) * g x ∂μ by
    dsimp only [smul_eq_mul, Pi.smul_apply]
    simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc, integral_const_mul, mul_comm (g _), S1]
  suffices S2 : ∫ x, (∑ i in s, a i * fderiv Real g x (v i)) * f x ∂μ =
                  ∑ i in s, a i * ∫ x, fderiv Real g x (v i) * f x ∂μ by
    obtain ⟨D, g_lip⟩ : exists D, LipschitzWith D g :=
      ContDiff.lipschitzWith_of_hasCompactSupport g_comp g_smooth (by simp)
    simp_rw [integral_lineDeriv_mul_eq hf g_lip g_comp]
    simp_rw [(g_smooth.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp only [map_neg, _root_.map_sum, map_smul, smul_eq_mul, neg_mul]
    simp only [integral_neg, mul_neg, Finset.sum_neg_distrib, neg_inj]
    exact S2
  suffices B : forall i in s, Integrable (fun x => a i * (fderiv Real g x (v i) * f x)) μ by
    simp_rw [Finset.sum_mul, mul_assoc, integral_finsetSum s B, integral_const_mul]
  intro i _hi
  let L : StrongDual Real E -> Real := fun f => f (v i)
  change Integrable (fun x => a i * ((L ∘ (fderiv Real g)) x * f x)) μ
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
  · exact ((g_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hf.continuous
  · exact ((g_comp.fderiv Real).comp_left rfl).mul_right


/--
theorem `ae_exists_fderiv_of_countable` / 定理 `ae_exists_fderiv_of_countable`

English:
theorem ae_exists_fderiv_of_countable
  proof: by
  have B := Basis.ofVectorSpace Real E
  have I1 : forallᵐ (x : E) ∂μ, forall v in s, lineDeriv Real f x (∑ i, (B.repr v i) • B i) =
                                  ∑ i, B.repr v i • lineDeriv Real f x (B i) :=
    (ae_ball_iff hs).2 (fun v _ => hf.ae_lineDeriv_sum_eq _ _ _)
  have I2 : forallᵐ

中文:
定理 ae_exists_fderiv_of_countable
  证明: by
  have B := Basis.ofVectorSpace Real E
  have I1 : forallᵐ (x : E) ∂μ, forall v in s, lineDeriv Real f x (∑ i, (B.repr v i) • B i) =
                                  ∑ i, B.repr v i • lineDeriv Real f x (B i) :=
    (ae_ball_iff hs).2 (fun v _ => hf.ae_lineDeriv_sum_eq _ _ _)
  have I2 : forallᵐ

Depends on / 依赖: B.constr, B.repr, Basis.ofVectorSpace, LineDifferentiableAt, LinearMap, LinearMap.toContinuousLinearMap, StrongDual, ae_ball_iff, ae_lineDeriv_sum_eq, ae_lineDifferentiableAt, constr, filter_upwards, hf.ae_lineDeriv_sum_eq, hf.ae_lineDifferentiableAt, lineDeriv, ofVectorSpace, toContinuousLinearMap
-/
theorem ae_exists_fderiv_of_countable
    (hf : LipschitzWith C f) {s : Set E} (hs : s.Countable) :
    forallᵐ x ∂μ, exists (L : StrongDual Real E), forall v in s, HasLineDerivAt Real f (L v) x v := by
  have B := Basis.ofVectorSpace Real E
  have I1 : forallᵐ (x : E) ∂μ, forall v in s, lineDeriv Real f x (∑ i, (B.repr v i) • B i) =
                                  ∑ i, B.repr v i • lineDeriv Real f x (B i) :=
    (ae_ball_iff hs).2 (fun v _ => hf.ae_lineDeriv_sum_eq _ _ _)
  have I2 : forallᵐ (x : E) ∂μ, forall v in s, LineDifferentiableAt Real f x v :=
    (ae_ball_iff hs).2 (fun v _ => hf.ae_lineDifferentiableAt v)
  filter_upwards [I1, I2] with x hx h'x
  let L : StrongDual Real E :=
    LinearMap.toContinuousLinearMap (B.constr Real (fun i => lineDeriv Real f x (B i)))
  refine ⟨L, fun v hv => ?_⟩
  have J : L v = lineDeriv Real f x v := by convert! (hx v hv).symm <;> simp [L, B.sum_repr v]
  simpa [J] using (h'x v hv).hasLineDerivAt

omit [MeasurableSpace E] in
/--
theorem `hasFDerivAt_of_hasLineDerivAt_of_closure` / 定理 `hasFDerivAt_of_hasLineDerivAt_of_closure`

English:
theorem hasFDerivAt_of_hasLineDerivAt_of_closure
  proof: by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]; rw [isLittleO_iff]
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ (C + ‖L‖ + 1) * δ = ε :=
    ⟨ε / (C + ‖L‖ + 1), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨q, hqs, q_fin, hq⟩ : exists q, q subseteq s ∧ q.Finite ∧ sphere 0 1

中文:
定理 hasFDerivAt_of_hasLineDerivAt_of_closure
  证明: by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]; rw [isLittleO_iff]
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ (C + ‖L‖ + 1) * δ = ε :=
    ⟨ε / (C + ‖L‖ + 1), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨q, hqs, q_fin, hq⟩ : exists q, q subseteq s ∧ q.Finite ∧ sphere 0 1

Depends on / 依赖: Finite, Metric, Metric.mem_closure_iff, hasFDerivAt_iff_isLittleO_nhds_zero, hs.trans, isLittleO_iff, mem_closure_iff, q.Finite, q_fin, sphere, subseteq
-/
theorem hasFDerivAt_of_hasLineDerivAt_of_closure
    {f : E -> F} (hf : LipschitzWith C f) {s : Set E} (hs : sphere 0 1 subseteq closure s)
    {L : E ->L[Real] F} {x : E} (hL : forall v in s, HasLineDerivAt Real f (L v) x v) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]; rw [isLittleO_iff]
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ (C + ‖L‖ + 1) * δ = ε :=
    ⟨ε / (C + ‖L‖ + 1), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨q, hqs, q_fin, hq⟩ : exists q, q subseteq s ∧ q.Finite ∧ sphere 0 1 subseteq ⋃ y in q, ball y δ := by
    have : sphere 0 1 subseteq ⋃ y in s, ball y δ := by
      apply hs.trans (fun z hz => ?_)
      obtain ⟨y, ys, hy⟩ : exists y in s, dist z y < δ := Metric.mem_closure_iff.1 hz δ δpos
      exact mem_biUnion ys hy
    exact (isCompact_sphere 0 1).elim_finite_subcover_image (fun y _hy => isOpen_ball) this
  have I : forallᶠ t in 𝓝 (0 : Real), forall v in q, ‖f (x + t • v) - f x - t • L v‖ <= δ * ‖t‖ := by
    apply (Finite.eventually_all q_fin).2 (fun v hv => ?_)
    apply Asymptotics.IsLittleO.def ?_ δpos
    exact hasLineDerivAt_iff_isLittleO_nhds_zero.1 (hL v (hqs hv))
  obtain ⟨r, r_pos, hr⟩ : exists (r : Real), 0 < r ∧ forall (t : Real), ‖t‖ < r ->
      forall v in q, ‖f (x + t • v) - f x - t • L v‖ <= δ * ‖t‖ := by
    rcases Metric.mem_nhds_iff.1 I with ⟨r, r_pos, hr⟩
    exact ⟨r, r_pos, fun t ht v hv => hr (mem_ball_zero_iff.2 ht) v hv⟩
  apply Metric.mem_nhds_iff.2 ⟨r, r_pos, fun v hv => ?_⟩
  rcases eq_or_ne v 0 with rfl | v_ne
  · simp
  obtain ⟨w, ρ, w_mem, hvw, hρ⟩ : exists w ρ, w in sphere 0 1 ∧ v = ρ • w ∧ ρ = ‖v‖ := by
    refine ⟨‖v‖⁻¹ • v, ‖v‖, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 v_ne)], ?_, rfl⟩
    simp [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 v_ne)]
  have norm_rho : ‖ρ‖ = ρ := by rw [hρ, norm_norm]
  have rho_pos : 0 <= ρ := by simp [hρ]
  obtain ⟨y, yq, hy⟩ : exists y in q, ‖w - y‖ < δ := by simpa [← dist_eq_norm] using hq w_mem
  have : ‖y - w‖ < δ := by rwa [norm_sub_rev]
  calc ‖f (x + v) - f x - L v‖
      = ‖f (x + ρ • w) - f x - ρ • L w‖ := by simp [hvw]
    _ = ‖(f (x + ρ • w) - f (x + ρ • y)) + (ρ • L y - ρ • L w)
          + (f (x + ρ • y) - f x - ρ • L y)‖ := by congr; abel
    _ <= ‖f (x + ρ • w) - f (x + ρ • y)‖ + ‖ρ • L y - ρ • L w‖
          + ‖f (x + ρ • y) - f x - ρ • L y‖ := norm_add₃_le
    _ <= C * ‖(x + ρ • w) - (x + ρ • y)‖ + ρ * (‖L‖ * ‖y - w‖) + δ * ρ := by
      gcongr
      · exact hf.norm_sub_le _ _
      · rw [← smul_sub, norm_smul, norm_rho]
        gcongr
        exact L.lipschitz.norm_sub_le _ _
      · conv_rhs => rw [← norm_rho]
        apply hr _ _ _ yq
        simpa [norm_rho, hρ] using hv
    _ <= C * (ρ * δ) + ρ * (‖L‖ * δ) + δ * ρ := by
      simp only [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_rho]; gcongr
    _ = ((C + ‖L‖ + 1) * δ) * ρ := by ring
    _ = ε * ‖v‖ := by rw [hδ, hρ]

/--
theorem `ae_differentiableAt_of_real` / 定理 `ae_differentiableAt_of_real`

English:
theorem ae_differentiableAt_of_real
  given: (hf : LipschitzWith C f)
  proof: by
  obtain ⟨s, s_count, s_dense⟩ : exists (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 subseteq closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
 

中文:
定理 ae_differentiableAt_of_real
  条件: (hf : LipschitzWith C f)
  证明: by
  obtain ⟨s, s_count, s_dense⟩ : exists (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 subseteq closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
 

Depends on / 依赖: Countable, TopologicalSpace, TopologicalSpace.exists_countable_dense, ae_exists_fderiv_of_countable, closure, closure_eq, differentiableAt, exists_countable_dense, filter_upwards, hasFDerivAt_of_hasLineDerivAt_of_closure, hf.ae_exists_fderiv_of_countable, hf.hasFDerivAt_of_hasLineDerivAt_of_closure, s.Countable, s_count, s_dense, s_dense.closure_eq, sphere, subset_univ, subseteq
-/
theorem ae_differentiableAt_of_real (hf : LipschitzWith C f) :
    forallᵐ x ∂μ, DifferentiableAt Real f x := by
  obtain ⟨s, s_count, s_dense⟩ : exists (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 subseteq closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
  exact (hf.hasFDerivAt_of_hasLineDerivAt_of_closure hs hL).differentiableAt

end LipschitzWith

variable [FiniteDimensional Real E] [FiniteDimensional Real F] [IsAddHaarMeasure μ]

namespace LipschitzOnWith

/--
theorem `ae_differentiableWithinAt_of_mem_of_real` / 定理 `ae_differentiableWithinAt_of_mem_of_real`

English:
theorem ae_differentiableWithinAt_of_mem_of_real
  given: (hf : LipschitzOnWith C f s)
  proof: by
  obtain ⟨g, g_lip, hg⟩ : exists (g : E -> Real), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

中文:
定理 ae_differentiableWithinAt_of_mem_of_real
  条件: (hf : LipschitzOnWith C f s)
  证明: by
  obtain ⟨g, g_lip, hg⟩ : exists (g : E -> Real), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

Depends on / 依赖: LipschitzWith, ae_differentiableAt_of_real, differentiableWithinAt, extend_real, filter_upwards, g_lip, g_lip.ae_differentiableAt_of_real, hf.extend_real, hx.differentiableWithinAt.congr
-/
theorem ae_differentiableWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) :
    forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real f s x := by
  obtain ⟨g, g_lip, hg⟩ : exists (g : E -> Real), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

/--
theorem `ae_differentiableWithinAt_of_mem_pi` / 定理 `ae_differentiableWithinAt_of_mem_pi`

English:
theorem ae_differentiableWithinAt_of_mem_pi
  proof: by
  have A : forall i : ι, LipschitzWith 1 (fun x : ι -> Real => x i) := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (fun x : E => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_l

中文:
定理 ae_differentiableWithinAt_of_mem_pi
  证明: by
  have A : forall i : ι, LipschitzWith 1 (fun x : ι -> Real => x i) := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (fun x : E => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_l

Depends on / 依赖: DifferentiableWithinAt, LipschitzWith, LipschitzWith.comp_lipschitzOnWith, LipschitzWith.eval, ae_all_iff, ae_differentiableWithinAt_of_mem_of_real, comp_lipschitzOnWith, differentiableWithinAt_pi, filter_upwards
-/
theorem ae_differentiableWithinAt_of_mem_pi
    {ι : Type*} [Fintype ι] {f : E -> ι -> Real} {s : Set E}
    (hf : LipschitzOnWith C f s) : forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real f s x := by
  have A : forall i : ι, LipschitzWith 1 (fun x : ι -> Real => x i) := fun i => LipschitzWith.eval i
  have : forall i : ι, forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (fun x : E => f x i) s x := fun i => by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_lipschitzOnWith (A i) hf
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 (fun i => hx i xs)

/--
theorem `ae_differentiableWithinAt_of_mem` / 定理 `ae_differentiableWithinAt_of_mem`

English:
theorem ae_differentiableWithinAt_of_mem
  given: {f : E -> F} (hf : LipschitzOnWith C f s)
  proof: by
  have A := (Basis.ofVectorSpace Real F).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.id_

中文:
定理 ae_differentiableWithinAt_of_mem
  条件: {f : E -> F} (hf : LipschitzOnWith C f s)
  证明: by
  have A := (Basis.ofVectorSpace Real F).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.id_

Depends on / 依赖: A.lipschitz.comp_lipschitzOnWith, A.symm, A.symm.differentiableAt.comp_differentiableWithinAt, Basis.ofVectorSpace, ContinuousLinearEquiv, ContinuousLinearEquiv.symm_comp_self, DifferentiableWithinAt, Function, Function.id_comp, ae_differentiableWithinAt_of_mem_pi, comp_differentiableWithinAt, comp_lipschitzOnWith, differentiableAt, equivFun, equivFun.toContinuousLinearEquiv, filter_upwards, id_comp, lipschitz, ofVectorSpace, symm_comp_self
-/
theorem ae_differentiableWithinAt_of_mem {f : E -> F} (hf : LipschitzOnWith C f s) :
    forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real f s x := by
  have A := (Basis.ofVectorSpace Real F).equivFun.toContinuousLinearEquiv
  suffices H : forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.id_comp]
    rw [this]
    exact A.symm.differentiableAt.comp_differentiableWithinAt x (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_lipschitzOnWith hf

/--
theorem `ae_differentiableWithinAt` / 定理 `ae_differentiableWithinAt`

English:
theorem ae_differentiableWithinAt
  statement: {f : E -> F} (hf : LipschitzOnWith C f s)
  proof: by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

中文:
定理 ae_differentiableWithinAt
  结论: {f : E -> F} (hf : LipschitzOnWith C f s)
  证明: by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

Depends on / 依赖: ae_differentiableWithinAt_of_mem, ae_restrict_iff, hf.ae_differentiableWithinAt_of_mem
-/
theorem ae_differentiableWithinAt {f : E -> F} (hf : LipschitzOnWith C f s)
    (hs : MeasurableSet s) :
    forallᵐ x ∂(μ.restrict s), DifferentiableWithinAt Real f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

end LipschitzOnWith

/--
theorem `LipschitzWith.ae_differentiableAt` / 定理 `LipschitzWith.ae_differentiableAt`

English:
theorem LipschitzWith.ae_differentiableAt
  given: {f : E -> F} (h : LipschitzWith C f)
  proof: by
  rw [← lipschitzOnWith_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem

中文:
定理 LipschitzWith.ae_differentiableAt
  条件: {f : E -> F} (h : LipschitzWith C f)
  证明: by
  rw [← lipschitzOnWith_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem

Depends on / 依赖: ae_differentiableWithinAt_of_mem, differentiableWithinAt_univ, h.ae_differentiableWithinAt_of_mem, lipschitzOnWith_univ
-/
theorem LipschitzWith.ae_differentiableAt {f : E -> F} (h : LipschitzWith C f) :
    forallᵐ x ∂μ, DifferentiableAt Real f x := by
  rw [← lipschitzOnWith_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem

/--
theorem `ae_differentiableAt_norm` / 定理 `ae_differentiableAt_norm`

English:
theorem ae_differentiableAt_norm
  proof: lipschitzWith_one_norm.ae_differentiableAt

omit [MeasurableSpace E] in

中文:
定理 ae_differentiableAt_norm
  证明: lipschitzWith_one_norm.ae_differentiableAt

omit [MeasurableSpace E] in

Depends on / 依赖: ae_differentiableAt, lipschitzWith_one_norm, lipschitzWith_one_norm.ae_differentiableAt
-/
theorem ae_differentiableAt_norm :
    forallᵐ x ∂μ, DifferentiableAt Real (‖·‖) x := lipschitzWith_one_norm.ae_differentiableAt

omit [MeasurableSpace E] in
/--
theorem `dense_differentiableAt_norm` / 定理 `dense_differentiableAt_norm`

English:
theorem dense_differentiableAt_norm
  proof: let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Basis.ofVectorSpace Real E
  MeasureTheory.Measure.dense_of_ae (ae_differentiableAt_norm (μ := w.addHaar))

中文:
定理 dense_differentiableAt_norm
  证明: let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Basis.ofVectorSpace Real E
  MeasureTheory.Measure.dense_of_ae (ae_differentiableAt_norm (μ := w.addHaar))

Depends on / 依赖: Basis.ofVectorSpace, BorelSpace, MeasurableSpace, Measure, MeasureTheory, MeasureTheory.Measure.dense_of_ae, addHaar, ae_differentiableAt_norm, dense_of_ae, ofVectorSpace, w.addHaar
-/
theorem dense_differentiableAt_norm :
    Dense {x : E | DifferentiableAt Real (‖·‖) x} :=
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Basis.ofVectorSpace Real E
  MeasureTheory.Measure.dense_of_ae (ae_differentiableAt_norm (μ := w.addHaar))
