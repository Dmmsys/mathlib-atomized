/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for `C^1` functions

We give versions of the second fundamental theorem of calculus under the strong assumption
that the function is `C^1` on the interval. This is restrictive, but satisfied in many situations.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {f : Real -> E} {a b : Real}

namespace intervalIntegral

variable [CompleteSpace E]

/--
theorem `integral_deriv_of_contDiffOn_Icc` / 定理 `integral_deriv_of_contDiffOn_Icc`

English:
theorem integral_deriv_of_contDiffOn_Icc
  given: (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b)
  proof: by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

中文:
定理 integral_deriv_of_contDiffOn_Icc
  条件: (h : ContDiffOn 实数 1 f (闭区间 a b)) (hab : a <= b)
  证明: by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.hasDerivAt, Icc_mem_nhds, congr_ae, continuousOn, derivWithin, differentiableAt, differentiableWithinAt, eq_or_lt, filter_upwards, h.continuousOn, h.derivWithin, hab.eq_or_lt, hasDerivAt, integral_eq_sub_of_hasDerivAt_of_le, intervalIntegrable_of_Icc, one_ne_zero, restrict_Ioo_eq_restrict_Ioc, this.intervalIntegrable_of_Icc, uIoc_of_le
-/
theorem integral_deriv_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/--
theorem `integral_derivWithin_Icc_of_contDiffOn_Icc` / 定理 `integral_derivWithin_Icc_of_contDiffOn_Icc`

English:
theorem integral_derivWithin_Icc_of_contDiffOn_Icc
  given: (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b)
  proof: by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab]; rw [integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

中文:
定理 integral_derivWithin_Icc_of_contDiffOn_Icc
  条件: (h : ContDiffOn 实数 1 f (闭区间 a b)) (hab : a <= b)
  证明: by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab]; rw [integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

Depends on / 依赖: Icc_mem_nhds, MeasureTheory, MeasureTheory.integral_congr_ae, derivWithin_of_mem_nhds, filter_upwards, integral_congr_ae, integral_deriv_of_contDiffOn_Icc, integral_of_le, measurableSet_Ioo, restrict_Ioo_eq_restrict_Ioc, self_mem_ae_restrict
-/
theorem integral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) :
    ∫ x in a..b, derivWithin f (Icc a b) x = f b - f a := by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab]; rw [integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/--
theorem `integral_deriv_of_contDiffOn_uIcc` / 定理 `integral_deriv_of_contDiffOn_uIcc`

English:
theorem integral_deriv_of_contDiffOn_uIcc
  given: (h : ContDiffOn Real 1 f (uIcc a b))
  proof: by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm]; rw [integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

中文:
定理 integral_deriv_of_contDiffOn_uIcc
  条件: (h : ContDiffOn 实数 1 f (uIcc a b))
  证明: by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm]; rw [integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

Depends on / 依赖: hab.le, integral_deriv_of_contDiffOn_Icc, integral_symm, le_or_gt, uIcc_of_ge, uIcc_of_le
-/
theorem integral_deriv_of_contDiffOn_uIcc (h : ContDiffOn Real 1 f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm]; rw [integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

/--
theorem `integral_derivWithin_uIcc_of_contDiffOn_uIcc` / 定理 `integral_derivWithin_uIcc_of_contDiffOn_uIcc`

English:
theorem integral_derivWithin_uIcc_of_contDiffOn_uIcc
  given: (h : ContDiffOn Real 1 f (uIcc a b))
  proof: by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm]; rw [integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

中文:
定理 integral_derivWithin_uIcc_of_contDiffOn_uIcc
  条件: (h : ContDiffOn 实数 1 f (uIcc a b))
  证明: by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm]; rw [integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

Depends on / 依赖: hab.le, integral_derivWithin_Icc_of_contDiffOn_Icc, integral_symm, le_or_gt, uIcc_of_ge, uIcc_of_le
-/
theorem integral_derivWithin_uIcc_of_contDiffOn_uIcc (h : ContDiffOn Real 1 f (uIcc a b)) :
    ∫ x in a..b, derivWithin f (uIcc a b) x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm]; rw [integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

end intervalIntegral

open intervalIntegral

/--
theorem `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` / 定理 `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`

English:
theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
  statement: (h : ContDiffOn Real 1 f (Icc a b))
  proof: by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := Real) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub]; rw [Function.comp_def]; rw [g.isometry.edist_eq]; rw [edist_eq_enorm_sub]
  rw [← this]; rw [← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab]; rw [integral_of_le hab]; rw [restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable one_ne_zero).differentiableAt
  · exact (h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)
.differentiableAt one_ne_zero
  have : fderiv Real g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]

中文:
定理 enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
  结论: (h : ContDiffOn 实数 1 f (闭区间 a b))
  证明: by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := Real) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub]; rw [Function.comp_def]; rw [g.isometry.edist_eq]; rw [edist_eq_enorm_sub]
  rw [← this]; rw [← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab]; rw [integral_of_le hab]; rw [restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable one_ne_zero).differentiableAt
  · exact (h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)
.differentiableAt one_ne_zero
  have : fderiv Real g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]
-/
theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b))
    (hab : a <= b) :
    ‖f b - f a‖ₑ <= ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := Real) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub]; rw [Function.comp_def]; rw [g.isometry.edist_eq]; rw [edist_eq_enorm_sub]
  rw [← this]; rw [← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab]; rw [integral_of_le hab]; rw [restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable one_ne_zero).differentiableAt
  · exact (h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)
.differentiableAt one_ne_zero
  have : fderiv Real g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]

/--
theorem `enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc` / 定理 `enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc`

English:
theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
  statement: (h : ContDiffOn Real 1 f (Icc a b))
  proof: by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]

中文:
定理 enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
  结论: (h : ContDiffOn 实数 1 f (闭区间 a b))
  证明: by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]

Depends on / 依赖: Icc_mem_nhds, derivWithin_of_mem_nhds, enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc, filter_upwards, lintegral_congr_ae, measurableSet_Ioo, restrict_Ioo_eq_restrict_Icc, self_mem_ae_restrict, trans_eq
-/
theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b))
    (hab : a <= b) :
    ‖f b - f a‖ₑ <= ∫⁻ x in Icc a b, ‖derivWithin f (Icc a b) x‖ₑ := by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
