/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Displacement is at most the integral of the speed

In this file we prove several version of the following fact:
the displacement (`dist (f a) (f b)`) is at most the integral of `‖deriv f‖` over `[a, b]`.
-/


public section

open Filter Set MeasureTheory Measure Metric
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]

section Line

variable {f : Real -> E} {a b : Real}

/--
lemma `norm_sub_le_integral_of_norm_deriv_le_of_le` / 引理 `norm_sub_le_integral_of_norm_deriv_le_of_le`

English:
lemma norm_sub_le_integral_of_norm_deriv_le_of_le
  statement: {B : Real -> Real} (hab : a <= b)
  proof: by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : Real -> UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableO

中文:
引理 norm_sub_le_integral_of_norm_deriv_le_of_le
  结论: {B : 实数 -> 实数} (hab : a <= b)
  证明: by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : Real -> UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableO
-/
lemma norm_sub_le_integral_of_norm_deriv_le_of_le {B : Real -> Real} (hab : a <= b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn Real f (Ioo a b))
    (hfB : forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= B t)
    (hBi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ <= ∫ t in a..b, B t := by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : Real -> UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn Real g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg t (ht : t in Ioo a b) : deriv g t = deriv f t := by
      have : HasFDerivAt (𝕜 := Real) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := Real)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := Real)).hasFDerivAt
have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt Ioo_mem_nhds ht.1 ht.2
      rw [hg]; rw [(this.comp_hasDerivAt t hdft).deriv]; rw [UniformSpace.Completion.coe_toComplL]
    have hgn : forallᵐ t, t in Ioo a b -> ‖deriv g t‖ <= B t :=
      hfB.mono fun t htB ht => by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g, ← dist_eq_norm_sub] using this hgc hgd hgn inferInstance
  -- In a complete space, we have
  -- `‖f b - f a‖ = ‖∫ t in a..b, deriv f t‖ ≤ ∫ t in a..b, ‖deriv f t‖`
  have hfB' : (‖deriv f ·‖) <=ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
.hasDerivWithinAt exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht)
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
exact hfB'.trans .of_forall fun _ => le_abs_self _

/--
lemma `norm_sub_le_mul_volume_of_norm_deriv_le_of_le` / 引理 `norm_sub_le_mul_volume_of_norm_deriv_le_of_le`

English:
lemma norm_sub_le_mul_volume_of_norm_deriv_le_of_le
  statement: {C : Real} (hab : a <= b)
  proof: by
  set s := toMeasurable volume {x | deriv f x != 0}
  have hsm : MeasurableSet s := by measurability
  calc
    ‖f b - f a‖ <= ∫ t in a..b, indicator s (fun _ => C) t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem => ?_
        

中文:
引理 norm_sub_le_mul_volume_of_norm_deriv_le_of_le
  结论: {C : 实数} (hab : a <= b)
  证明: by
  set s := toMeasurable volume {x | deriv f x != 0}
  have hsm : MeasurableSet s := by measurability
  calc
    ‖f b - f a‖ <= ∫ t in a..b, indicator s (fun _ => C) t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem => ?_
        

Depends on / 依赖: MeasurableSet, hnorm.mono, ht_mem, indicator, integrableOn_const, intervalIntegrable_iff_integrableOn_Ioo_of_le, le_indicator_apply, measurability, norm_le_zero_iff, norm_sub_le_integral_of_norm_deriv_le_of_le, not_imp_comm, subset_toMeasurable, toMeasurable, volume
-/
lemma norm_sub_le_mul_volume_of_norm_deriv_le_of_le {C : Real} (hab : a <= b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn Real f (Ioo a b))
    (hnorm : forallᵐ t, t in Ioo a b -> ‖deriv f t‖ <= C) :
    ‖f b - f a‖ <= C * volume.real {x in Ioo a b | deriv f x != 0} := by
  set s := toMeasurable volume {x | deriv f x != 0}
  have hsm : MeasurableSet s := by measurability
  calc
    ‖f b - f a‖ <= ∫ t in a..b, indicator s (fun _ => C) t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem => ?_
        apply le_indicator_apply
        · exact fun ht' => ht ht_mem
        · simp only [s, norm_le_zero_iff]
          exact not_imp_comm.2 fun h => subset_toMeasurable _ _ h
      · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
        refine (integrableOn_const ?_ ?_).indicator hsm <;> simp
    _ = C * volume.real {x in Ioo a b | deriv f x != 0} := by
      rw [intervalIntegral.integral_of_le hab]; rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]; rw [integral_indicator hsm]; rw [Measure.restrict_restrict hsm]; rw [setIntegral_const]; rw [smul_eq_mul]; rw [mul_comm]
      simp only [s, Measure.real,
        Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Ioo]
      simp only [inter_def, mem_ofPred_eq, and_comm]

end Line

section NormedSpace

open AffineMap
variable {f : E -> F} {a b : E} {C r : Real} {s : Set E}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `norm_sub_le_mul_volume_of_norm_lineDeriv_le` / 引理 `norm_sub_le_mul_volume_of_norm_lineDeriv_le`

English:
lemma norm_sub_le_mul_volume_of_norm_lineDeriv_le
  proof: by
  set g : Real -> F := fun t => f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : Real) (ht : t in Ioo 0 1) : HasDerivAt g (lineDeriv Rea

中文:
引理 norm_sub_le_mul_volume_of_norm_lineDeriv_le
  证明: by
  set g : Real -> F := fun t => f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : Real) (ht : t in Ioo 0 1) : HasDerivAt g (lineDeriv Rea

Depends on / 依赖: AffineMap, AffineMap.lineMap_continuous.continuousOn, ContinuousOn, Function, Function.comp_def, HasDerivAt, add_comm, comp_def, continuousOn, hasDerivAt_id, hasLineDerivAt, hasLineDerivAt.scomp_of_eq, hfc.comp, lineDeriv, lineMap, lineMap_apply_module, lineMap_continuous, mapsTo_image, scomp_of_eq, segment_eq_image_lineMap
-/
lemma norm_sub_le_mul_volume_of_norm_lineDeriv_le
    (hfc : ContinuousOn f (segment Real a b))
    (hfd : forall t in Ioo (0 : Real) 1, LineDifferentiableAt Real f (lineMap a b t) (b - a))
    (hf' : forallᵐ t : Real, t in Ioo (0 : Real) 1 -> ‖lineDeriv Real f (lineMap a b t) (b - a)‖ <= C) :
    ‖f b - f a‖ <=
      C * volume.real {t in Ioo (0 : Real) 1 | lineDeriv Real f (lineMap a b t) (b - a) != 0} := by
  set g : Real -> F := fun t => f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : Real) (ht : t in Ioo 0 1) : HasDerivAt g (lineDeriv Real f (lineMap a b t) (b - a)) t := by
    have := (hfd t ht).hasLineDerivAt.scomp_of_eq (𝕜 := Real) t ((hasDerivAt_id t).sub_const t)
    simpa [g, lineMap_apply_module', Function.comp_def, sub_smul, add_comm _ a] using this
  suffices ‖g 1 - g 0‖ <= C * volume.real {t in Ioo 0 1 | deriv g t != 0} by
    convert! this using 1
    · simp [g]
    · congr 2 with t
      simp +contextual [(hdg _ _).deriv]
  apply norm_sub_le_mul_volume_of_norm_deriv_le_of_le zero_le_one hgc
  · exact fun t ht => (hdg t ht).differentiableAt.differentiableWithinAt
  · exact hf'.mono fun t ht ht_mem => by simpa only [(hdg t ht_mem).deriv] using ht ht_mem

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `norm_sub_le_mul_volume_of_norm_fderiv_le` / 引理 `norm_sub_le_mul_volume_of_norm_fderiv_le`

English:
lemma norm_sub_le_mul_volume_of_norm_fderiv_le
  statement: (hs : IsOpen s) (hf : DiffContOnCl Real f s)
  proof: by
  have hmem_s : forall t in Ioo (0 : Real) 1, lineMap a b t in s := fun t ht =>
hab lineMap_mem_openSegment _ a b ht
have hC₀ : 0 <= C := (norm_nonneg _).trans hC _ hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment Real a b) :=
hf.continuousOn.mono segment_subset_closure_openSegme

中文:
引理 norm_sub_le_mul_volume_of_norm_fderiv_le
  结论: (hs : 是开集 s) (hf : DiffContOnCl 实数 f s)
  证明: by
  have hmem_s : forall t in Ioo (0 : Real) 1, lineMap a b t in s := fun t ht =>
hab lineMap_mem_openSegment _ a b ht
have hC₀ : 0 <= C := (norm_nonneg _).trans hC _ hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment Real a b) :=
hf.continuousOn.mono segment_subset_closure_openSegme

Depends on / 依赖: ContinuousOn, LineDifferentiableAt, closure_mono, continuousOn, differentiableAt, hf.continuousOn.mono, hf.differentiableAt, hmem_s, lineDifferentiableAt, lineMap, lineMap_mem_openSegment, norm_nonneg, segment, segment_subset_closure_openSegment, segment_subset_closure_openSegment.trans
-/
lemma norm_sub_le_mul_volume_of_norm_fderiv_le (hs : IsOpen s) (hf : DiffContOnCl Real f s)
    (hab : openSegment Real a b subseteq s) (hC : forall x in s, ‖fderiv Real f x‖ <= C) :
    ‖f b - f a‖ <=
      C * ‖b - a‖ * volume.real {t in Ioo (0 : Real) 1 | fderiv Real f (lineMap a b t) != 0} := by
  have hmem_s : forall t in Ioo (0 : Real) 1, lineMap a b t in s := fun t ht =>
hab lineMap_mem_openSegment _ a b ht
have hC₀ : 0 <= C := (norm_nonneg _).trans hC _ hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment Real a b) :=
hf.continuousOn.mono segment_subset_closure_openSegment.trans closure_mono hab
  have hfd : forall t in Ioo (0 : Real) 1, LineDifferentiableAt Real f (lineMap a b t) (b - a) := fun t ht =>
    (hf.differentiableAt hs <| hmem_s t ht).lineDifferentiableAt
  have hfC : forall t in Ioo (0 : Real) 1, ‖lineDeriv Real f (lineMap a b t) (b - a)‖ <= C * ‖b - a‖ := by
    intro t ht
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    · exact ContinuousLinearMap.le_of_opNorm_le _ (hC _ <| hmem_s t ht) _
· exact hf.differentiableAt hs hmem_s t ht
.trans ?_ refine norm_sub_le_mul_volume_of_norm_lineDeriv_le hfc hfd (.of_forall hfC)
  gcongr
  · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    simp
  · simp +contextual [(hf.differentiableAt hs <| hmem_s _ ‹_›).lineDeriv_eq_fderiv]

/--
theorem `sub_isBigO_norm_rpow_add_one_of_fderiv` / 定理 `sub_isBigO_norm_rpow_add_one_of_fderiv`

English:
theorem sub_isBigO_norm_rpow_add_one_of_fderiv
  statement: (hr : 0 <= r)
  proof: by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy => ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.r

中文:
定理 sub_isBigO_norm_rpow_add_one_of_fderiv
  结论: (hr : 0 <= r)
  证明: by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy => ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.r

Depends on / 依赖: Asymptotics, Asymptotics.IsBigOWith_def, IsBigOWith_def, Real.norm_of_nonneg, Real.rpow_add_one, closedBall, closedBall_subset_ball, convex_closedBall, eventually_nhds_iff_ball, eventually_nhds_iff_ball.mp, exists_pos, hderiv, hderiv.exists_pos, hdf.and, mem_ball_iff_norm, mem_ball_iff_norm.mp, mul_assoc, norm_image_, norm_of_nonneg, of_bound
-/
theorem sub_isBigO_norm_rpow_add_one_of_fderiv (hr : 0 <= r)
    (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x) (hderiv : fderiv Real f =O[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy => ?_⟩
  rw [Real.norm_of_nonneg (by positivity)]; rw [Real.rpow_add_one' (by positivity) (by positivity)]; rw [← mul_assoc]
  have hsub : closedBall a ‖y - a‖ subseteq ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := Real)
  · exact fun z hz => (hε z <| hsub hz).1
  · intro z hz
    grw [(hε z <| hsub hz).2, Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

/--
theorem `isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero` / 定理 `isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero`

English:
theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero
  statement: (hr : 0 <= r)
  proof: by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

中文:
定理 isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero
  结论: (hr : 0 <= r)
  证明: by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

Depends on / 依赖: hderiv, sub_isBigO_norm_rpow_add_one_of_fderiv
-/
theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (hr : 0 <= r)
    (hdf : forallᶠ x in 𝓝 a, DifferentiableAt Real f x) (hderiv : fderiv Real f =O[𝓝 a] (‖· - a‖ ^ r))
    (hf₀ : f a = 0) :
    f =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

end NormedSpace
