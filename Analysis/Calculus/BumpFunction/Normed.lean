/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Normed bump function

In this file we define `ContDiffBump.normed f μ` to be the bump function `f` normalized so that
`∫ x, f.normed μ x ∂μ = 1` and prove some properties of this function.
-/

@[expose] public section

noncomputable section

open Function Filter Set Metric MeasureTheory Module Measure
open scoped Topology

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [HasContDiffBump E]
  [MeasurableSpace E] {c : E} (f : ContDiffBump c) {x : E} {n : Nat∞} {μ : Measure E}

/--
Definition of `normed` / `normed` 的定义

English:
definition normed
  signature: (μ : Measure E)
  body: fun x => f x / ∫ x, f x ∂μ

中文:
定义 normed
  签名: (μ : 测度 E)
  定义体: fun x => f x / ∫ x, f x ∂μ
-/
protected def normed (μ : Measure E) : E -> Real := fun x => f x / ∫ x, f x ∂μ

/--
theorem `normed_def` / 定理 `normed_def`

English:
theorem normed_def
  given: {μ : Measure E} (x : E)
  statement: f.normed μ x = f x / ∫ x, f x ∂μ
  proof: rfl

中文:
定理 normed_def
  条件: {μ : 测度 E} (x : E)
  结论: f.normed μ x = f x / ∫ x, f x ∂μ
  证明: rfl
-/
theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl

/--
theorem `nonneg_normed` / 定理 `nonneg_normed`

English:
theorem nonneg_normed
  given: (x : E)
  statement: 0 <= f.normed μ x
  proof: div_nonneg f.nonneg integral_nonneg f.nonneg'

中文:
定理 nonneg_normed
  条件: (x : E)
  结论: 0 <= f.normed μ x
  证明: div_nonneg f.nonneg integral_nonneg f.nonneg'

Depends on / 依赖: div_nonneg, f.nonneg, integral_nonneg, nonneg
-/
theorem nonneg_normed (x : E) : 0 <= f.normed μ x :=
div_nonneg f.nonneg integral_nonneg f.nonneg'

/--
theorem `contDiff_normed` / 定理 `contDiff_normed`

English:
theorem contDiff_normed
  given: {n : Nat∞}
  statement: ContDiff Real n (f.normed μ)
  proof: f.contDiff.div_const _

中文:
定理 contDiff_normed
  条件: {n : 自然数∞}
  结论: 连续可微 实数 n (f.normed μ)
  证明: f.contDiff.div_const _

Depends on / 依赖: contDiff, div_const, f.contDiff.div_const
-/
theorem contDiff_normed {n : Nat∞} : ContDiff Real n (f.normed μ) :=
  f.contDiff.div_const _

/--
theorem `continuous_normed` / 定理 `continuous_normed`

English:
theorem continuous_normed
  statement: Continuous (f.normed μ)
  proof: f.continuous.div_const _

中文:
定理 continuous_normed
  结论: 连续 (f.normed μ)
  证明: f.continuous.div_const _

Depends on / 依赖: continuous, div_const, f.continuous.div_const
-/
theorem continuous_normed : Continuous (f.normed μ) :=
  f.continuous.div_const _

/--
theorem `normed_sub` / 定理 `normed_sub`

English:
theorem normed_sub
  given: (x : E)
  statement: f.normed μ (c - x) = f.normed μ (c + x)
  proof: by
  simp_rw [f.normed_def, f.sub]

中文:
定理 normed_sub
  条件: (x : E)
  结论: f.normed μ (c - x) = f.normed μ (c + x)
  证明: by
  simp_rw [f.normed_def, f.sub]

Depends on / 依赖: f.normed_def, f.sub, normed_def, simp_rw
-/
theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]

/--
theorem `normed_neg` / 定理 `normed_neg`

English:
theorem normed_neg
  given: (f : ContDiffBump (0 : E)) (x : E)
  statement: f.normed μ (-x) = f.normed μ x
  proof: by
  simp_rw [f.normed_def, f.neg]

中文:
定理 normed_neg
  条件: (f : 余ntDiffBump (0 : E)) (x : E)
  结论: f.normed μ (-x) = f.normed μ x
  证明: by
  simp_rw [f.normed_def, f.neg]

Depends on / 依赖: f.neg, f.normed_def, normed_def, simp_rw
-/
theorem normed_neg (f : ContDiffBump (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]

variable [BorelSpace E] [FiniteDimensional Real E] [IsLocallyFiniteMeasure μ]

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  statement: Integrable f μ
  proof: f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

中文:
定理 integrable
  结论: 可积 f μ
  证明: f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
-/
protected theorem integrable : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/--
theorem `integrable_normed` / 定理 `integrable_normed`

English:
theorem integrable_normed
  statement: Integrable (f.normed μ) μ
  proof: f.integrable.div_const _

中文:
定理 integrable_normed
  结论: 可积 (f.normed μ) μ
  证明: f.integrable.div_const _
-/
protected theorem integrable_normed : Integrable (f.normed μ) μ :=
  f.integrable.div_const _

section
variable [μ.IsOpenPosMeasure]

/--
theorem `integral_pos` / 定理 `integral_pos`

English:
theorem integral_pos
  statement: 0 < ∫ x, f x ∂μ
  proof: by
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr ?_
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos

中文:
定理 integral_pos
  结论: 0 < ∫ x, f x ∂μ
  证明: by
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr ?_
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos

Depends on / 依赖: f.integrable, f.nonneg, f.rOut_pos, f.support_eq, integrable, integral_pos_iff_support_of_nonneg, measure_ball_pos, nonneg, rOut_pos, support_eq
-/
theorem integral_pos : 0 < ∫ x, f x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr ?_
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos

/--
theorem `integral_normed` / 定理 `integral_normed`

English:
theorem integral_normed
  statement: ∫ x, f.normed μ x ∂μ = 1
  proof: by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ f.integral_pos.ne'

中文:
定理 integral_normed
  结论: ∫ x, f.normed μ x ∂μ = 1
  证明: by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ f.integral_pos.ne'

Depends on / 依赖: ContDiffBump, ContDiffBump.normed, div_eq_mul_inv, f.integral_pos.ne, integral_pos, integral_smul, mul_comm, normed, simp_rw, smul_eq_mul
-/
theorem integral_normed : ∫ x, f.normed μ x ∂μ = 1 := by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ f.integral_pos.ne'

/--
theorem `support_normed_eq` / 定理 `support_normed_eq`

English:
theorem support_normed_eq
  statement: Function.support (f.normed μ) = Metric.ball c f.rOut
  proof: by
  unfold ContDiffBump.normed
  rw [support_div]; rw [f.support_eq]; rw [support_const f.integral_pos.ne']; rw [inter_univ]

中文:
定理 support_normed_eq
  结论: 函数.support (f.normed μ) = Metric.ball c f.rOut
  证明: by
  unfold ContDiffBump.normed
  rw [support_div]; rw [f.support_eq]; rw [support_const f.integral_pos.ne']; rw [inter_univ]

Depends on / 依赖: ContDiffBump, ContDiffBump.normed, f.integral_pos.ne, f.support_eq, integral_pos, inter_univ, normed, support_const, support_div, support_eq
-/
theorem support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut := by
  unfold ContDiffBump.normed
  rw [support_div]; rw [f.support_eq]; rw [support_const f.integral_pos.ne']; rw [inter_univ]

/--
theorem `tsupport_normed_eq` / 定理 `tsupport_normed_eq`

English:
theorem tsupport_normed_eq
  statement: tsupport (f.normed μ) = Metric.closedBall c f.rOut
  proof: by
  rw [tsupport]; rw [f.support_normed_eq]; rw [closure_ball _ f.rOut_pos.ne']

中文:
定理 tsupport_normed_eq
  结论: tsupport (f.normed μ) = Metric.closedBall c f.rOut
  证明: by
  rw [tsupport]; rw [f.support_normed_eq]; rw [closure_ball _ f.rOut_pos.ne']

Depends on / 依赖: closure_ball, f.rOut_pos.ne, f.support_normed_eq, rOut_pos, support_normed_eq, tsupport
-/
theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.rOut := by
  rw [tsupport]; rw [f.support_normed_eq]; rw [closure_ball _ f.rOut_pos.ne']

/--
theorem `hasCompactSupport_normed` / 定理 `hasCompactSupport_normed`

English:
theorem hasCompactSupport_normed
  statement: HasCompactSupport (f.normed μ)
  proof: by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]

中文:
定理 hasCompactSupport_normed
  结论: HasCompactSupport (f.normed μ)
  证明: by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]

Depends on / 依赖: HasCompactSupport, f.tsupport_normed_eq, isCompact_closedBall, tsupport_normed_eq
-/
theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]

/--
theorem `tendsto_support_normed_smallSets` / 定理 `tendsto_support_normed_smallSets`

English:
theorem tendsto_support_normed_smallSets
  statement: {ι} {φ : ι -> ContDiffBump c} {l : Filter ι}
  proof: by
  simp_rw [NormedAddGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε => (hφ ε hε).mono fun i hi => ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le

中文:
定理 tendsto_support_normed_smallSets
  结论: {ι} {φ : ι -> 余ntDiffBump c} {l : 滤子 ι}
  证明: by
  simp_rw [NormedAddGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε => (hφ ε hε).mono fun i hi => ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le

Depends on / 依赖: NormedAddGroup, NormedAddGroup.tendsto_nhds_zero, Real.norm_eq_abs, abs_eq_self, abs_eq_self.mpr, ball_subset_ball, hi.le, nhds_basis_ball, nhds_basis_ball.smallSets.tendsto_right_iff, norm_eq_abs, rOut_pos, rOut_pos.le, simp_rw, smallSets, support_normed_eq, tendsto_nhds_zero, tendsto_right_iff
-/
theorem tendsto_support_normed_smallSets {ι} {φ : ι -> ContDiffBump c} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => Function.support fun x => (φ i).normed μ x) l (𝓝 c).smallSets := by
  simp_rw [NormedAddGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε => (hφ ε hε).mono fun i hi => ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le

variable (μ)

/--
theorem `integral_normed_smul` / 定理 `integral_normed_smul`

English:
theorem integral_normed_smul
  statement: {X} [NormedAddCommGroup X] [NormedSpace Real X]
  proof: by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]

中文:
定理 integral_normed_smul
  结论: {X} [赋范交换加群 X] [赋范空间 实数 X]
  证明: by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]

Depends on / 依赖: f.integral_normed, integral_normed, integral_smul_const, one_smul, simp_rw
-/
theorem integral_normed_smul {X} [NormedAddCommGroup X] [NormedSpace Real X]
    [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • z ∂μ = z := by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]

end

variable (μ)

/--
theorem `measure_closedBall_le_integral` / 定理 `measure_closedBall_le_integral`

English:
theorem measure_closedBall_le_integral
  statement: μ.real (closedBall c f.rIn) <= ∫ x, f x ∂μ
  proof: by calc
  μ.real (closedBall c f.rIn) = ∫ x in closedBall c f.rIn, 1 ∂μ := by simp
  _ = ∫ x in closedBall c f.rIn, f x ∂μ := setIntegral_congr_fun measurableSet_closedBall
        (fun x hx => (one_of_mem_closedBall f hx).symm)
  _ <= ∫ x, f x ∂μ := setIntegral_le_integral f.integrable (Eventually.

中文:
定理 measure_closedBall_le_integral
  结论: μ.real (closedBall c f.rIn) <= ∫ x, f x ∂μ
  证明: by calc
  μ.real (closedBall c f.rIn) = ∫ x in closedBall c f.rIn, 1 ∂μ := by simp
  _ = ∫ x in closedBall c f.rIn, f x ∂μ := setIntegral_congr_fun measurableSet_closedBall
        (fun x hx => (one_of_mem_closedBall f hx).symm)
  _ <= ∫ x, f x ∂μ := setIntegral_le_integral f.integrable (Eventually.

Depends on / 依赖: Eventually, Eventually.of_forall, closedBall, f.integrable, f.nonneg, f.rIn, integrable, measurableSet_closedBall, nonneg, of_forall, one_of_mem_closedBall, setIntegral_congr_fun, setIntegral_le_integral
-/
theorem measure_closedBall_le_integral : μ.real (closedBall c f.rIn) <= ∫ x, f x ∂μ := by calc
  μ.real (closedBall c f.rIn) = ∫ x in closedBall c f.rIn, 1 ∂μ := by simp
  _ = ∫ x in closedBall c f.rIn, f x ∂μ := setIntegral_congr_fun measurableSet_closedBall
        (fun x hx => (one_of_mem_closedBall f hx).symm)
  _ <= ∫ x, f x ∂μ := setIntegral_le_integral f.integrable (Eventually.of_forall (fun x => f.nonneg))

/--
theorem `normed_le_div_measure_closedBall_rIn` / 定理 `normed_le_div_measure_closedBall_rIn`

English:
theorem normed_le_div_measure_closedBall_rIn
  given: [μ.IsOpenPosMeasure] (x : E)
  proof: by
  rw [normed_def]
  gcongr
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rIn_pos).ne' measure_closedBall_lt_top.ne
  · exact f.le_one
  · exact f.measure_closedBall_le_integral μ

中文:
定理 normed_le_div_measure_closedBall_rIn
  条件: [μ.是OpenPosMeasure] (x : E)
  证明: by
  rw [normed_def]
  gcongr
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rIn_pos).ne' measure_closedBall_lt_top.ne
  · exact f.le_one
  · exact f.measure_closedBall_le_integral μ

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, f.le_one, f.measure_closedBall_le_integral, f.rIn_pos, le_one, measure_closedBall_le_integral, measure_closedBall_lt_top, measure_closedBall_lt_top.ne, measure_closedBall_pos, normed_def, rIn_pos, toReal_pos
-/
theorem normed_le_div_measure_closedBall_rIn [μ.IsOpenPosMeasure] (x : E) :
    f.normed μ x <= 1 / μ.real (closedBall c f.rIn) := by
  rw [normed_def]
  gcongr
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rIn_pos).ne' measure_closedBall_lt_top.ne
  · exact f.le_one
  · exact f.measure_closedBall_le_integral μ

/--
theorem `integral_le_measure_closedBall` / 定理 `integral_le_measure_closedBall`

English:
theorem integral_le_measure_closedBall
  statement: ∫ x, f x ∂μ <= μ.real (closedBall c f.rOut)
  proof: by calc
  ∫ x, f x ∂μ = ∫ x in closedBall c f.rOut, f x ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    apply f.zero_of_le_dist (le_of_lt _)
    simpa using hx
  _ <= ∫ x in closedBall c f.rOut, 1 ∂μ := by
    apply setIntegral_mono f.integrable.integra

中文:
定理 integral_le_measure_closedBall
  结论: ∫ x, f x ∂μ <= μ.real (closedBall c f.rOut)
  证明: by calc
  ∫ x, f x ∂μ = ∫ x in closedBall c f.rOut, f x ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    apply f.zero_of_le_dist (le_of_lt _)
    simpa using hx
  _ <= ∫ x in closedBall c f.rOut, 1 ∂μ := by
    apply setIntegral_mono f.integrable.integra

Depends on / 依赖: closedBall, f.integrable.integrableOn, f.le_one, f.rOut, f.zero_of_le_dist, integrable, integrableOn, le_of_lt, le_one, measure_closedBall_lt_top, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_mono, zero_of_le_dist
-/
theorem integral_le_measure_closedBall : ∫ x, f x ∂μ <= μ.real (closedBall c f.rOut) := by calc
  ∫ x, f x ∂μ = ∫ x in closedBall c f.rOut, f x ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    apply f.zero_of_le_dist (le_of_lt _)
    simpa using hx
  _ <= ∫ x in closedBall c f.rOut, 1 ∂μ := by
    apply setIntegral_mono f.integrable.integrableOn _ (fun x => f.le_one)
    simp [measure_closedBall_lt_top]
  _ = μ.real (closedBall c f.rOut) := by simp

/--
theorem `measure_closedBall_div_le_integral` / 定理 `measure_closedBall_div_le_integral`

English:
theorem measure_closedBall_div_le_integral
  given: [IsAddHaarMeasure μ] (K : Real) (h : f.rOut <= K * f.rIn)
  proof: by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  apply le_trans _ (f.measure_closedBall_le_integral μ)
  rw [div_le_iff₀ (pow_pos K_pos _)]; rw [addHaar_real_closedBall' _ _ f.rIn_pos.le]; rw [addHaar_real_closedBall' _ _ f.rOut

中文:
定理 measure_closedBall_div_le_integral
  条件: [是加法Haar测度 μ] (K : 实数) (h : f.rOut <= K * f.rIn)
  证明: by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  apply le_trans _ (f.measure_closedBall_le_integral μ)
  rw [div_le_iff₀ (pow_pos K_pos _)]; rw [addHaar_real_closedBall' _ _ f.rIn_pos.le]; rw [addHaar_real_closedBall' _ _ f.rOut

Depends on / 依赖: K_pos, addHaar_real_closedBall, f.measure_closedBall_le_integral, f.rIn_pos, f.rIn_pos.le, f.rOut_pos.le, f.rOut_pos.trans_le, le_trans, measure_closedBall_le_integral, mul_assoc, mul_comm, mul_pos_iff, mul_pow, not_lt, pow_pos, rIn_pos, rOut_pos, trans_le
-/
theorem measure_closedBall_div_le_integral [IsAddHaarMeasure μ] (K : Real) (h : f.rOut <= K * f.rIn) :
    μ.real (closedBall c f.rOut) / K ^ finrank Real E <= ∫ x, f x ∂μ := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  apply le_trans _ (f.measure_closedBall_le_integral μ)
  rw [div_le_iff₀ (pow_pos K_pos _)]; rw [addHaar_real_closedBall' _ _ f.rIn_pos.le]; rw [addHaar_real_closedBall' _ _ f.rOut_pos.le]; rw [mul_assoc]; rw [mul_comm _ (K ^ _)]; rw [← mul_assoc]; rw [← mul_pow]; rw [mul_comm _ K]
  gcongr
  exact f.rOut_pos.le

/--
theorem `normed_le_div_measure_closedBall_rOut` / 定理 `normed_le_div_measure_closedBall_rOut`

English:
theorem normed_le_div_measure_closedBall_rOut
  statement: [IsAddHaarMeasure μ] (K : Real) (h : f.rOut <= K * f.rIn)
  proof: by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  have : f x / ∫ y, f y ∂μ <= 1 / ∫ y, f y ∂μ := by
    gcongr
    · exact f.integral_pos.le
    · exact f.le_one
  apply this.trans
  rw [div_le_div_iff₀ f.integral_pos]; rw [one_m

中文:
定理 normed_le_div_measure_closedBall_rOut
  结论: [是加法Haar测度 μ] (K : 实数) (h : f.rOut <= K * f.rIn)
  证明: by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  have : f x / ∫ y, f y ∂μ <= 1 / ∫ y, f y ∂μ := by
    gcongr
    · exact f.integral_pos.le
    · exact f.le_one
  apply this.trans
  rw [div_le_div_iff₀ f.integral_pos]; rw [one_m

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, K_pos, f.integral_pos, f.integral_pos.le, f.le_one, f.measure_closedBall_div_le_integral, f.rIn_pos, f.rIn_pos.le, f.rOut_pos, f.rOut_pos.trans_le, integral_pos, le_one, measure_closedBall_div_le_integral, measure_closedBall_lt_top, measure_closedBall_lt_top.ne, measure_closedBall_pos, mul_pos_iff, not_lt, one_mul
-/
theorem normed_le_div_measure_closedBall_rOut [IsAddHaarMeasure μ] (K : Real) (h : f.rOut <= K * f.rIn)
    (x : E) :
    f.normed μ x <= K ^ finrank Real E / μ.real (closedBall c f.rOut) := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  have : f x / ∫ y, f y ∂μ <= 1 / ∫ y, f y ∂μ := by
    gcongr
    · exact f.integral_pos.le
    · exact f.le_one
  apply this.trans
  rw [div_le_div_iff₀ f.integral_pos]; rw [one_mul]; rw [← div_le_iff₀' (pow_pos K_pos _)]
  · exact f.measure_closedBall_div_le_integral μ K h
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rOut_pos).ne'
      measure_closedBall_lt_top.ne

end ContDiffBump
