/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Probability.Independence.Integrable

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`ProbabilityTheory` locale).

## Main definitions

* `ProbabilityTheory.evariance`: the variance of a real-valued random variable as an extended
  non-negative real.
* `ProbabilityTheory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `ProbabilityTheory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `ProbabilityTheory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2)`.
* `ProbabilityTheory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `ProbabilityTheory.IndepFun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `ProbabilityTheory.IndepFun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
* `ProbabilityTheory.variance_le_sub_mul_sub`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `(b - 𝔼 X) * (𝔼 X - a)`.
* `ProbabilityTheory.variance_le_sq_of_bounded`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `((b - a) / 2) ^ 2`.
-/

@[expose] public section

open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω -> Real} {μ : Measure Ω}

variable (X μ) in
-- TODO: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/--
Definition of `evariance` / `evariance` 的定义

English:
definition evariance
  signature: : Real>=0∞
  body: ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

中文:
定义 evariance
  签名: : 实数>=0∞
  定义体: ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ
-/
def evariance : Real>=0∞ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

variable (X μ) in
/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
@[wikidata Q175199]
/--
Definition of `variance` / `variance` 的定义

English:
definition variance
  signature: : Real
  body: (evariance X μ).toReal

中文:
定义 variance
  签名: : 实数
  定义体: (evariance X μ).toReal

Depends on / 依赖: evariance, toReal
-/
def variance : Real := (evariance X μ).toReal

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the measure `μ`.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "; " μ "]" => ProbabilityTheory.evariance X μ

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the volume
measure.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "]" => eVar[X; MeasureTheory.MeasureSpace.volume]

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the measure `μ`.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "; " μ "]" => ProbabilityTheory.variance X μ

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the volume measure.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "]" => Var[X; MeasureTheory.MeasureSpace.volume]

/--
theorem `evariance_congr` / 定理 `evariance_congr`

English:
theorem evariance_congr
  given: (h : X =ᵐ[μ] Y)
  statement: eVar[X; μ] = eVar[Y; μ]
  proof: by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]

中文:
定理 evariance_congr
  条件: (h : X =ᵐ[μ] Y)
  结论: eVar[X; μ] = eVar[Y; μ]
  证明: by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]

Depends on / 依赖: evariance, filter_upwards, integral_congr_ae, lintegral_congr_ae, simp_rw
-/
theorem evariance_congr (h : X =ᵐ[μ] Y) : eVar[X; μ] = eVar[Y; μ] := by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]

/--
theorem `variance_congr` / 定理 `variance_congr`

English:
theorem variance_congr
  given: (h : X =ᵐ[μ] Y)
  statement: Var[X; μ] = Var[Y; μ]
  proof: by
  simp_rw [variance, evariance_congr h]

中文:
定理 variance_congr
  条件: (h : X =ᵐ[μ] Y)
  结论: Var[X; μ] = Var[Y; μ]
  证明: by
  simp_rw [variance, evariance_congr h]

Depends on / 依赖: evariance_congr, simp_rw, variance
-/
theorem variance_congr (h : X =ᵐ[μ] Y) : Var[X; μ] = Var[Y; μ] := by
  simp_rw [variance, evariance_congr h]

/--
lemma `evariance_zero_measure` / 引理 `evariance_zero_measure`

English:
lemma evariance_zero_measure
  statement: eVar[X; (0 : Measure Ω)] = 0
  proof: by simp [evariance]

中文:
引理 evariance_zero_measure
  结论: eVar[X; (0 : Measure Ω)] = 0
  证明: by simp [evariance]
-/
@[simp] lemma evariance_zero_measure : eVar[X; (0 : Measure Ω)] = 0 := by simp [evariance]
/--
lemma `variance_zero_measure` / 引理 `variance_zero_measure`

English:
lemma variance_zero_measure
  statement: Var[X; (0 : Measure Ω)] = 0
  proof: by simp [variance]

中文:
引理 variance_zero_measure
  结论: Var[X; (0 : Measure Ω)] = 0
  证明: by simp [variance]
-/
@[simp] lemma variance_zero_measure : Var[X; (0 : Measure Ω)] = 0 := by simp [variance]

/--
theorem `evariance_lt_top` / 定理 `evariance_lt_top`

English:
theorem evariance_lt_top
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  statement: evariance X μ < ∞
  proof: by
  have := ENNReal.pow_lt_top (hX.sub <| memLp_const <| μ[X]).2 (n := 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]; rw [← ENNReal.rpow_two]
    at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, one_div] at this
  rw [← ENNReal.rpow_mul]; rw [inv_mul_canc

中文:
定理 evariance_lt_top
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  结论: evariance X μ < ∞
  证明: by
  have := ENNReal.pow_lt_top (hX.sub <| memLp_const <| μ[X]).2 (n := 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]; rw [← ENNReal.rpow_two]
    at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, one_div] at this
  rw [← ENNReal.rpow_mul]; rw [inv_mul_canc

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, ENNReal.pow_lt_top, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.rpow_two, ENNReal.toReal_ofNat, Pi.sub_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal, hX.sub, memLp_const, ofNat_ne_top, one_div, pow_lt_top, rpow_mul, rpow_one, rpow_two, simp_rw, sub_apply, toReal_ofNat
-/
theorem evariance_lt_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ < ∞ := by
  have := ENNReal.pow_lt_top (hX.sub <| memLp_const <| μ[X]).2 (n := 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]; rw [← ENNReal.rpow_two]
    at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, one_div] at this
  rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (two_ne_zero : (2 : Real) != 0)]; rw [ENNReal.rpow_one] at this
  simp_rw [ENNReal.rpow_two] at this
  exact this

/--
lemma `evariance_ne_top` / 引理 `evariance_ne_top`

English:
lemma evariance_ne_top
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  statement: evariance X μ != ∞
  proof: (evariance_lt_top hX).ne

中文:
引理 evariance_ne_top
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  结论: evariance X μ != ∞
  证明: (evariance_lt_top hX).ne

Depends on / 依赖: evariance_lt_top
-/
lemma evariance_ne_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ != ∞ :=
  (evariance_lt_top hX).ne

/--
theorem `evariance_eq_top` / 定理 `evariance_eq_top`

English:
theorem evariance_eq_top
  given: [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ)
  proof: by
  by_contra h
  rw [← Ne]; rw [← lt_top_iff_ne_top] at h
  have : MemLp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_to

中文:
定理 evariance_eq_top
  条件: [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ)
  证明: by
  by_contra h
  rw [← Ne]; rw [← lt_top_iff_ne_top] at h
  have : MemLp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_to

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, ENNReal.rpow_lt_top_of_nonneg, ENNReal.rpow_two, ENNReal.toReal_ofNat, Pi.add_apply, add_apply, convert, eLpNorm_eq_lintegral_rpow_enorm_toReal, fun_prop, h.ne, lt_top_iff_ne_top, memLp_const, ofNat_ne_top, rpow_lt_top_of_nonneg, rpow_two, sub_add_cancel, this.add, toReal_ofNat, two_ne_zero
-/
theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne]; rw [← lt_top_iff_ne_top] at h
  have : MemLp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine hX ?_
  convert! this.add (memLp_const μ[X])
  ext ω
  rw [Pi.add_apply]; rw [sub_add_cancel]

/--
theorem `evariance_lt_top_iff_memLp` / 定理 `evariance_lt_top_iff_memLp`

English:
theorem evariance_lt_top_iff_memLp
  given: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  proof: by contrapose!; rw [top_le_iff]; exact evariance_eq_top hX
  mpr := evariance_lt_top

中文:
定理 evariance_lt_top_iff_memLp
  条件: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  证明: by contrapose!; rw [top_le_iff]; exact evariance_eq_top hX
  mpr := evariance_lt_top

Depends on / 依赖: contrapose, evariance_eq_top, evariance_lt_top, top_le_iff
-/
theorem evariance_lt_top_iff_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ MemLp X 2 μ where
  mp := by contrapose!; rw [top_le_iff]; exact evariance_eq_top hX
  mpr := evariance_lt_top

/--
lemma `evariance_eq_top_iff` / 引理 `evariance_eq_top_iff`

English:
lemma evariance_eq_top_iff
  given: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  proof: by simp [← evariance_lt_top_iff_memLp hX]

中文:
引理 evariance_eq_top_iff
  条件: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  证明: by simp [← evariance_lt_top_iff_memLp hX]

Depends on / 依赖: evariance_lt_top_iff_memLp
-/
lemma evariance_eq_top_iff [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ = ∞ ↔ ¬ MemLp X 2 μ := by simp [← evariance_lt_top_iff_memLp hX]

/--
lemma `variance_of_not_memLp` / 引理 `variance_of_not_memLp`

English:
lemma variance_of_not_memLp
  statement: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  proof: by simp [variance, (evariance_eq_top_iff hX).mpr hX_not]

中文:
引理 variance_of_not_memLp
  结论: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  证明: by simp [variance, (evariance_eq_top_iff hX).mpr hX_not]

Depends on / 依赖: evariance_eq_top_iff, hX_not, variance
-/
lemma variance_of_not_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (hX_not : ¬ MemLp X 2 μ) :
    variance X μ = 0 := by simp [variance, (evariance_eq_top_iff hX).mpr hX_not]

/--
lemma `memLp_two_of_variance_ne_zero` / 引理 `memLp_two_of_variance_ne_zero`

English:
lemma memLp_two_of_variance_ne_zero
  statement: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  proof: by
  contrapose h
  exact variance_of_not_memLp hX h

中文:
引理 memLp_two_of_variance_ne_zero
  结论: [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
  证明: by
  contrapose h
  exact variance_of_not_memLp hX h

Depends on / 依赖: contrapose, variance_of_not_memLp
-/
lemma memLp_two_of_variance_ne_zero [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (h : Var[X; μ] != 0) : MemLp X 2 μ := by
  contrapose h
  exact variance_of_not_memLp hX h

/--
theorem `ofReal_variance` / 定理 `ofReal_variance`

English:
theorem ofReal_variance
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  proof: by
  rw [variance]; rw [ENNReal.ofReal_toReal]
  exact evariance_ne_top hX

protected alias _root_.MeasureTheory.MemLp.evariance_lt_top := evariance_lt_top
protected alias _root_.MeasureTheory.MemLp.evariance_ne_top := evariance_ne_top
protected alias _root_.MeasureTheory.MemLp.ofReal_variance_eq :=

中文:
定理 ofReal_variance
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  证明: by
  rw [variance]; rw [ENNReal.ofReal_toReal]
  exact evariance_ne_top hX

protected alias _root_.MeasureTheory.MemLp.evariance_lt_top := evariance_lt_top
protected alias _root_.MeasureTheory.MemLp.evariance_ne_top := evariance_ne_top
protected alias _root_.MeasureTheory.MemLp.ofReal_variance_eq :=

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, evariance_ne_top, ofReal_toReal, variance
-/
theorem ofReal_variance [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    .ofReal (variance X μ) = evariance X μ := by
  rw [variance]; rw [ENNReal.ofReal_toReal]
  exact evariance_ne_top hX

protected alias _root_.MeasureTheory.MemLp.evariance_lt_top := evariance_lt_top
protected alias _root_.MeasureTheory.MemLp.evariance_ne_top := evariance_ne_top
protected alias _root_.MeasureTheory.MemLp.ofReal_variance_eq := ofReal_variance

variable (X μ) in
/--
theorem `evariance_eq_lintegral_ofReal` / 定理 `evariance_eq_lintegral_ofReal`

English:
theorem evariance_eq_lintegral_ofReal
  proof: by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

中文:
定理 evariance_eq_lintegral_ofReal
  证明: by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

Depends on / 依赖: Real.enorm_of_nonneg, enorm_of_nonneg, enorm_pow, evariance, sq_nonneg
-/
theorem evariance_eq_lintegral_ofReal :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

/--
lemma `variance_eq_integral` / 引理 `variance_eq_integral`

English:
lemma variance_eq_integral
  given: (hX : AEMeasurable X μ)
  statement: Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
  proof: by
  simp [variance, evariance, toReal_enorm, ← integral_toReal ((hX.sub_const _).enorm.pow_const _) <|
    .of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top]

中文:
引理 variance_eq_integral
  条件: (hX : AEMeasurable X μ)
  结论: Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
  证明: by
  simp [variance, evariance, toReal_enorm, ← integral_toReal ((hX.sub_const _).enorm.pow_const _) <|
    .of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top]

Depends on / 依赖: ENNReal, ENNReal.pow_lt_top, enorm.pow_const, enorm_lt_top, evariance, hX.sub_const, integral_toReal, of_forall, pow_const, pow_lt_top, sub_const, toReal_enorm, variance
-/
lemma variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ := by
  simp [variance, evariance, toReal_enorm, ← integral_toReal ((hX.sub_const _).enorm.pow_const _) <|
    .of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top]

/--
lemma `ae_eq_integral_of_variance_eq_zero` / 引理 `ae_eq_integral_of_variance_eq_zero`

English:
lemma ae_eq_integral_of_variance_eq_zero
  statement: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  proof: by
  rw [variance_eq_integral hX.aemeasurable]; rw [integral_eq_zero_iff_of_nonneg] at h
  · filter_upwards [h] with ω hω
    simp at hω
    grind
  · exact fun _ => by positivity
  · simp_rw [sub_sq]
    exact (hX.integrable_sq.sub (((hX.integrable (by simp)).const_mul _).mul_const _)).add
      (i

中文:
引理 ae_eq_integral_of_variance_eq_zero
  结论: [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  证明: by
  rw [variance_eq_integral hX.aemeasurable]; rw [integral_eq_zero_iff_of_nonneg] at h
  · filter_upwards [h] with ω hω
    simp at hω
    grind
  · exact fun _ => by positivity
  · simp_rw [sub_sq]
    exact (hX.integrable_sq.sub (((hX.integrable (by simp)).const_mul _).mul_const _)).add
      (i

Depends on / 依赖: aemeasurable, const_mul, filter_upwards, hX.aemeasurable, hX.integrable, hX.integrable_sq.sub, integrable, integrable_const, integrable_sq, integral_eq_zero_iff_of_nonneg, mul_const, simp_rw, sub_sq, variance_eq_integral
-/
lemma ae_eq_integral_of_variance_eq_zero [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
    (h : Var[X; μ] = 0) :
    forallᵐ ω ∂μ, X ω = μ[X] := by
  rw [variance_eq_integral hX.aemeasurable]; rw [integral_eq_zero_iff_of_nonneg] at h
  · filter_upwards [h] with ω hω
    simp at hω
    grind
  · exact fun _ => by positivity
  · simp_rw [sub_sq]
    exact (hX.integrable_sq.sub (((hX.integrable (by simp)).const_mul _).mul_const _)).add
      (integrable_const _)

/--
lemma `variance_of_integral_eq_zero` / 引理 `variance_of_integral_eq_zero`

English:
lemma variance_of_integral_eq_zero
  given: (hX : AEMeasurable X μ) (hXint : μ[X] = 0)
  proof: by
  simp [variance_eq_integral hX, hXint]

@[simp]

中文:
引理 variance_of_integral_eq_zero
  条件: (hX : AEMeasurable X μ) (hXint : μ[X] = 0)
  证明: by
  simp [variance_eq_integral hX, hXint]

@[simp]

Depends on / 依赖: variance_eq_integral
-/
lemma variance_of_integral_eq_zero (hX : AEMeasurable X μ) (hXint : μ[X] = 0) :
    variance X μ = ∫ ω, X ω ^ 2 ∂μ := by
  simp [variance_eq_integral hX, hXint]

@[simp]
/--
theorem `evariance_zero` / 定理 `evariance_zero`

English:
theorem evariance_zero
  statement: evariance 0 μ = 0
  proof: by simp [evariance]

中文:
定理 evariance_zero
  结论: evariance 0 μ = 0
  证明: by simp [evariance]

Depends on / 依赖: evariance
-/
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]

/--
theorem `evariance_eq_zero_iff` / 定理 `evariance_eq_zero_iff`

English:
theorem evariance_eq_zero_iff
  given: (hX : AEMeasurable X μ)
  proof: by
  simp [evariance, lintegral_eq_zero_iff' ((hX.sub_const _).enorm.pow_const _), EventuallyEq,
    sub_eq_zero]

中文:
定理 evariance_eq_zero_iff
  条件: (hX : AEMeasurable X μ)
  证明: by
  simp [evariance, lintegral_eq_zero_iff' ((hX.sub_const _).enorm.pow_const _), EventuallyEq,
    sub_eq_zero]

Depends on / 依赖: EventuallyEq, enorm.pow_const, evariance, hX.sub_const, lintegral_eq_zero_iff, pow_const, sub_const, sub_eq_zero
-/
theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  simp [evariance, lintegral_eq_zero_iff' ((hX.sub_const _).enorm.pow_const _), EventuallyEq,
    sub_eq_zero]

/--
theorem `evariance_mul` / 定理 `evariance_mul`

English:
theorem evariance_mul
  given: (c : Real) (X : Ω -> Real) (μ : Measure Ω)
  proof: by
  rw [evariance]; rw [evariance]; rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr with ω
  rw [integral_const_mul]; rw [← mul_sub]; rw [enorm_mul]; rw [mul_pow]; rw [← enorm_pow]; rw [Real.enorm_of_nonneg (sq_nonneg _)]

@[simp]

中文:
定理 evariance_mul
  条件: (c : 实数) (X : Ω -> 实数) (μ : Measure Ω)
  证明: by
  rw [evariance]; rw [evariance]; rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr with ω
  rw [integral_const_mul]; rw [← mul_sub]; rw [enorm_mul]; rw [mul_pow]; rw [← enorm_pow]; rw [Real.enorm_of_nonneg (sq_nonneg _)]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top.ne, Real.enorm_of_nonneg, enorm_mul, enorm_of_nonneg, enorm_pow, evariance, integral_const_mul, lintegral_const_mul, mul_pow, mul_sub, ofReal_lt_top, sq_nonneg
-/
theorem evariance_mul (c : Real) (X : Ω -> Real) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ := by
  rw [evariance]; rw [evariance]; rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr with ω
  rw [integral_const_mul]; rw [← mul_sub]; rw [enorm_mul]; rw [mul_pow]; rw [← enorm_pow]; rw [Real.enorm_of_nonneg (sq_nonneg _)]

@[simp]
/--
theorem `variance_zero` / 定理 `variance_zero`

English:
theorem variance_zero
  given: (μ : Measure Ω)
  statement: variance 0 μ = 0
  proof: by
  simp only [variance, evariance_zero, ENNReal.toReal_zero]

中文:
定理 variance_zero
  条件: (μ : Measure Ω)
  结论: variance 0 μ = 0
  证明: by
  simp only [variance, evariance_zero, ENNReal.toReal_zero]

Depends on / 依赖: ENNReal, ENNReal.toReal_zero, evariance_zero, toReal_zero, variance
-/
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.toReal_zero]

/--
lemma `covariance_self` / 引理 `covariance_self`

English:
lemma covariance_self
  given: {X : Ω -> Real} (hX : AEMeasurable X μ)
  proof: by
  rw [covariance]; rw [variance_eq_integral hX]
  congr with x
  ring

@[simp]

中文:
引理 covariance_self
  条件: {X : Ω -> 实数} (hX : AEMeasurable X μ)
  证明: by
  rw [covariance]; rw [variance_eq_integral hX]
  congr with x
  ring

@[simp]

Depends on / 依赖: covariance, variance_eq_integral
-/
lemma covariance_self {X : Ω -> Real} (hX : AEMeasurable X μ) :
    cov[X, X; μ] = Var[X; μ] := by
  rw [covariance]; rw [variance_eq_integral hX]
  congr with x
  ring

@[simp]
/--
theorem `variance_nonneg` / 定理 `variance_nonneg`

English:
theorem variance_nonneg
  given: (X : Ω -> Real) (μ : Measure Ω)
  statement: 0 <= variance X μ
  proof: ENNReal.toReal_nonneg

中文:
定理 variance_nonneg
  条件: (X : Ω -> 实数) (μ : Measure Ω)
  结论: 0 <= variance X μ
  证明: ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, toReal_nonneg
-/
theorem variance_nonneg (X : Ω -> Real) (μ : Measure Ω) : 0 <= variance X μ :=
  ENNReal.toReal_nonneg

/--
theorem `variance_const_mul` / 定理 `variance_const_mul`

English:
theorem variance_const_mul
  given: (c : Real) (X : Ω -> Real) (μ : Measure Ω)
  proof: by
  rw [variance]; rw [evariance_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

中文:
定理 variance_const_mul
  条件: (c : 实数) (X : Ω -> 实数) (μ : Measure Ω)
  证明: by
  rw [variance]; rw [evariance_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal, evariance_mul, sq_nonneg, toReal_mul, toReal_ofReal, variance
-/
theorem variance_const_mul (c : Real) (X : Ω -> Real) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ := by
  rw [variance]; rw [evariance_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

/--
theorem `variance_mul_const` / 定理 `variance_mul_const`

English:
theorem variance_mul_const
  given: (c : Real) (X : Ω -> Real) (μ : Measure Ω)
  proof: by
  simp [mul_comm, variance_const_mul]

中文:
定理 variance_mul_const
  条件: (c : 实数) (X : Ω -> 实数) (μ : Measure Ω)
  证明: by
  simp [mul_comm, variance_const_mul]

Depends on / 依赖: mul_comm, variance_const_mul
-/
theorem variance_mul_const (c : Real) (X : Ω -> Real) (μ : Measure Ω) :
    variance (fun ω => X ω * c) μ = variance X μ * c ^ 2 := by
  simp [mul_comm, variance_const_mul]

/--
theorem `variance_smul` / 定理 `variance_smul`

English:
theorem variance_smul
  given: (c : Real) (X : Ω -> Real) (μ : Measure Ω)
  proof: variance_const_mul c X μ

中文:
定理 variance_smul
  条件: (c : 实数) (X : Ω -> 实数) (μ : Measure Ω)
  证明: variance_const_mul c X μ

Depends on / 依赖: variance_const_mul
-/
theorem variance_smul (c : Real) (X : Ω -> Real) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_const_mul c X μ

/--
theorem `variance_smul'` / 定理 `variance_smul'`

English:
theorem variance_smul'
  statement: {A : Type*} [CommSemiring A] [Algebra A Real] (c : A) (X : Ω -> Real)
  proof: by
  convert! variance_smul (algebraMap A Real c) X μ using 1
  · simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]

中文:
定理 variance_smul'
  结论: {A : 类型} [CommSemiring A] [Algebra A 实数] (c : A) (X : Ω -> 实数)
  证明: by
  convert! variance_smul (algebraMap A Real c) X μ using 1
  · simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, algebraMap_smul, convert, map_pow, smul_def, variance_smul
-/
theorem variance_smul' {A : Type*} [CommSemiring A] [Algebra A Real] (c : A) (X : Ω -> Real)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ := by
  convert! variance_smul (algebraMap A Real c) X μ using 1
  · simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]

/--
theorem `variance_eq_sub` / 定理 `variance_eq_sub`

English:
theorem variance_eq_sub
  given: [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : MemLp X 2 μ)
  proof: by
  rw [← covariance_self hX.aemeasurable]; rw [covariance_eq_sub hX hX]; rw [pow_two]; rw [pow_two]

中文:
定理 variance_eq_sub
  条件: [IsProbabilityMeasure μ] {X : Ω -> 实数} (hX : MemLp X 2 μ)
  证明: by
  rw [← covariance_self hX.aemeasurable]; rw [covariance_eq_sub hX hX]; rw [pow_two]; rw [pow_two]

Depends on / 依赖: aemeasurable, covariance_eq_sub, covariance_self, hX.aemeasurable, pow_two
-/
theorem variance_eq_sub [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  rw [← covariance_self hX.aemeasurable]; rw [covariance_eq_sub hX hX]; rw [pow_two]; rw [pow_two]

/--
lemma `variance_add_const` / 引理 `variance_add_const`

English:
lemma variance_add_const
  given: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real)
  proof: by
  by_cases hX_Lp : MemLp X 2 μ
  · have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
    rw [variance_eq_integral (hX.add_const _).aemeasurable]; rw [integral_add hX_int (by fun_prop)]; rw [integral_const]; rw [variance_eq_integral hX.aemeasurable]
    simp
  · rw [variance_of_not_memLp

中文:
引理 variance_add_const
  条件: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : 实数)
  证明: by
  by_cases hX_Lp : MemLp X 2 μ
  · have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
    rw [variance_eq_integral (hX.add_const _).aemeasurable]; rw [integral_add hX_int (by fun_prop)]; rw [integral_const]; rw [variance_eq_integral hX.aemeasurable]
    simp
  · rw [variance_of_not_memLp

Depends on / 依赖: Integrable, add_const, aemeasurable, fun_prop, hX.add_const, hX.aemeasurable, hX_Lp, hX_Lp.integrable, hX_int, h_memLp, h_memLp.sub, integrable, integral_add, integral_const, memLp_const, one_le_two, variance_eq_integral, variance_of_not_memLp
-/
lemma variance_add_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real) :
    Var[fun ω => X ω + c; μ] = Var[X; μ] := by
  by_cases hX_Lp : MemLp X 2 μ
  · have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
    rw [variance_eq_integral (hX.add_const _).aemeasurable]; rw [integral_add hX_int (by fun_prop)]; rw [integral_const]; rw [variance_eq_integral hX.aemeasurable]
    simp
  · rw [variance_of_not_memLp (hX.add_const _), variance_of_not_memLp hX hX_Lp]
    refine fun h_memLp => hX_Lp ?_
    have : X = fun ω => X ω + c - c := by ext; ring
    rw [this]
    exact h_memLp.sub (memLp_const c)

/--
lemma `variance_const_add` / 引理 `variance_const_add`

English:
lemma variance_const_add
  given: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real)
  proof: by
  simp_rw [add_comm c, variance_add_const hX c]

中文:
引理 variance_const_add
  条件: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : 实数)
  证明: by
  simp_rw [add_comm c, variance_add_const hX c]

Depends on / 依赖: add_comm, simp_rw, variance_add_const
-/
lemma variance_const_add [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real) :
    Var[fun ω => c + X ω; μ] = Var[X; μ] := by
  simp_rw [add_comm c, variance_add_const hX c]

/--
lemma `variance_fun_neg` / 引理 `variance_fun_neg`

English:
lemma variance_fun_neg
  statement: Var[fun ω => -X ω; μ] = Var[X; μ]
  proof: by
  convert! variance_const_mul (-1) X μ
  · ext; ring
  · simp

中文:
引理 variance_fun_neg
  结论: Var[fun ω => -X ω; μ] = Var[X; μ]
  证明: by
  convert! variance_const_mul (-1) X μ
  · ext; ring
  · simp

Depends on / 依赖: convert, variance_const_mul
-/
lemma variance_fun_neg : Var[fun ω => -X ω; μ] = Var[X; μ] := by
  convert! variance_const_mul (-1) X μ
  · ext; ring
  · simp

/--
lemma `variance_neg` / 引理 `variance_neg`

English:
lemma variance_neg
  statement: Var[-X; μ] = Var[X; μ]
  proof: variance_fun_neg

中文:
引理 variance_neg
  结论: Var[-X; μ] = Var[X; μ]
  证明: variance_fun_neg

Depends on / 依赖: variance_fun_neg
-/
lemma variance_neg : Var[-X; μ] = Var[X; μ] := variance_fun_neg

/--
lemma `variance_sub_const` / 引理 `variance_sub_const`

English:
lemma variance_sub_const
  given: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real)
  proof: by
  simp_rw [sub_eq_add_neg, variance_add_const hX (-c)]

中文:
引理 variance_sub_const
  条件: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : 实数)
  证明: by
  simp_rw [sub_eq_add_neg, variance_add_const hX (-c)]

Depends on / 依赖: simp_rw, sub_eq_add_neg, variance_add_const
-/
lemma variance_sub_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real) :
    Var[fun ω => X ω - c; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg, variance_add_const hX (-c)]

/--
lemma `variance_const_sub` / 引理 `variance_const_sub`

English:
lemma variance_const_sub
  given: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real)
  proof: by
  simp_rw [sub_eq_add_neg]
  rw [variance_const_add (by fun_prop) c]; rw [variance_fun_neg]

中文:
引理 variance_const_sub
  条件: [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : 实数)
  证明: by
  simp_rw [sub_eq_add_neg]
  rw [variance_const_add (by fun_prop) c]; rw [variance_fun_neg]

Depends on / 依赖: fun_prop, simp_rw, sub_eq_add_neg, variance_const_add, variance_fun_neg
-/
lemma variance_const_sub [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : Real) :
    Var[fun ω => c - X ω; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg]
  rw [variance_const_add (by fun_prop) c]; rw [variance_fun_neg]

/--
lemma `variance_add` / 引理 `variance_add`

English:
lemma variance_add
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  rw [← covariance_self]; rw [covariance_add_left hX hY (hX.add hY)]; rw [covariance_add_right hX hX hY]; rw [covariance_add_right hY hX hY]; rw [covariance_self]; rw [covariance_self]; rw [covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.add

中文:
引理 variance_add
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  rw [← covariance_self]; rw [covariance_add_left hX hY (hX.add hY)]; rw [covariance_add_right hX hX hY]; rw [covariance_add_right hY hX hY]; rw [covariance_self]; rw [covariance_self]; rw [covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.add

Depends on / 依赖: aemeasurable, covariance_add_left, covariance_add_right, covariance_comm, covariance_self, hX.add, hX.aemeasurable, hX.aemeasurable.add, hY.aemeasurable
-/
lemma variance_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] := by
  rw [← covariance_self]; rw [covariance_add_left hX hY (hX.add hY)]; rw [covariance_add_right hX hX hY]; rw [covariance_add_right hY hX hY]; rw [covariance_self]; rw [covariance_self]; rw [covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.add hY.aemeasurable

/--
lemma `variance_fun_add` / 引理 `variance_fun_add`

English:
lemma variance_fun_add
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: variance_add hX hY

中文:
引理 variance_fun_add
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: variance_add hX hY

Depends on / 依赖: variance_add
-/
lemma variance_fun_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω => X ω + Y ω; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_add hX hY

/--
lemma `variance_sub` / 引理 `variance_sub`

English:
lemma variance_sub
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: by
   rw [sub_eq_add_neg]; rw [variance_add hX hY.neg]; rw [variance_neg]; rw [covariance_neg_right]
   ring

中文:
引理 variance_sub
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: by
   rw [sub_eq_add_neg]; rw [variance_add hX hY.neg]; rw [variance_neg]; rw [covariance_neg_right]
   ring

Depends on / 依赖: covariance_neg_right, hY.neg, sub_eq_add_neg, variance_add, variance_neg
-/
lemma variance_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     Var[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] := by
   rw [sub_eq_add_neg]; rw [variance_add hX hY.neg]; rw [variance_neg]; rw [covariance_neg_right]
   ring

/--
lemma `variance_fun_sub` / 引理 `variance_fun_sub`

English:
lemma variance_fun_sub
  given: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: variance_sub hX hY

中文:
引理 variance_fun_sub
  条件: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: variance_sub hX hY

Depends on / 依赖: variance_sub
-/
lemma variance_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω => X ω - Y ω; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_sub hX hY

variable {ι : Type*} {s : Finset ι} {X : (i : ι) -> Ω -> Real}

/--
lemma `variance_sum'` / 引理 `variance_sum'`

English:
lemma variance_sum'
  given: [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ)
  proof: by
  rw [← covariance_self]; rw [covariance_sum_left' (by simpa)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [covariance_sum_right' (by simpa) (hX i hi)]
  · exact memLp_finsetSum' _ (by simpa)
  · exact (memLp_finsetSum' _ (by simpa)).aemeasurable

中文:
引理 variance_sum'
  条件: [IsFiniteMeasure μ] (hX : 对任意 i in s, MemLp (X i) 2 μ)
  证明: by
  rw [← covariance_self]; rw [covariance_sum_left' (by simpa)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [covariance_sum_right' (by simpa) (hX i hi)]
  · exact memLp_finsetSum' _ (by simpa)
  · exact (memLp_finsetSum' _ (by simpa)).aemeasurable

Depends on / 依赖: Finset, Finset.sum_congr, aemeasurable, covariance_self, covariance_sum_left, covariance_sum_right, memLp_finsetSum, sum_congr
-/
lemma variance_sum' [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ) :
    Var[∑ i in s, X i; μ] = ∑ i in s, ∑ j in s, cov[X i, X j; μ] := by
  rw [← covariance_self]; rw [covariance_sum_left' (by simpa)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [covariance_sum_right' (by simpa) (hX i hi)]
  · exact memLp_finsetSum' _ (by simpa)
  · exact (memLp_finsetSum' _ (by simpa)).aemeasurable

/--
lemma `variance_sum` / 引理 `variance_sum`

English:
lemma variance_sum
  given: [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X i) 2 μ)
  proof: variance_sum' (fun _ _ => hX _)

中文:
引理 variance_sum
  条件: [IsFiniteMeasure μ] [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ)
  证明: variance_sum' (fun _ _ => hX _)

Depends on / 依赖: variance_sum
-/
lemma variance_sum [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) :
    Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ] :=
  variance_sum' (fun _ _ => hX _)

/--
lemma `variance_fun_sum'` / 引理 `variance_fun_sum'`

English:
lemma variance_fun_sum'
  given: [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ)
  proof: by
  convert! variance_sum' hX
  simp

中文:
引理 variance_fun_sum'
  条件: [IsFiniteMeasure μ] (hX : 对任意 i in s, MemLp (X i) 2 μ)
  证明: by
  convert! variance_sum' hX
  simp

Depends on / 依赖: convert, variance_sum
-/
lemma variance_fun_sum' [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ) :
    Var[fun ω => ∑ i in s, X i ω; μ] = ∑ i in s, ∑ j in s, cov[X i, X j; μ] := by
  convert! variance_sum' hX
  simp

/--
lemma `variance_fun_sum` / 引理 `variance_fun_sum`

English:
lemma variance_fun_sum
  given: [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X i) 2 μ)
  proof: by
  convert! variance_sum hX
  simp

中文:
引理 variance_fun_sum
  条件: [IsFiniteMeasure μ] [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ)
  证明: by
  convert! variance_sum hX
  simp

Depends on / 依赖: convert, variance_sum
-/
lemma variance_fun_sum [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) :
    Var[fun ω => ∑ i, X i ω; μ] = ∑ i, ∑ j, cov[X i, X j; μ] := by
  convert! variance_sum hX
  simp

variable {X : Ω -> Real}

@[simp]
/--
lemma `variance_dirac` / 引理 `variance_dirac`

English:
lemma variance_dirac
  given: [MeasurableSingletonClass Ω] (x : Ω)
  statement: Var[X; Measure.dirac x] = 0
  proof: by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac

中文:
引理 variance_dirac
  条件: [MeasurableSingletonClass Ω] (x : Ω)
  结论: Var[X; Measure.dirac x] = 0
  证明: by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac

Depends on / 依赖: aemeasurable_dirac, variance_eq_integral
-/
lemma variance_dirac [MeasurableSingletonClass Ω] (x : Ω) : Var[X; Measure.dirac x] = 0 := by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac

/--
lemma `variance_map` / 引理 `variance_map`

English:
lemma variance_map
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  proof: by
  rw [variance_eq_integral hX]; rw [integral_map hY]; rw [variance_eq_integral (hX.comp_aemeasurable hY)]; rw [integral_map hY]
  · congr
  · exact hX.aestronglyMeasurable
  · refine AEStronglyMeasurable.pow ?_ _
    exact AEMeasurable.aestronglyMeasurable (by fun_prop)

中文:
引理 variance_map
  结论: {Ω' : 类型} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  证明: by
  rw [variance_eq_integral hX]; rw [integral_map hY]; rw [variance_eq_integral (hX.comp_aemeasurable hY)]; rw [integral_map hY]
  · congr
  · exact hX.aestronglyMeasurable
  · refine AEStronglyMeasurable.pow ?_ _
    exact AEMeasurable.aestronglyMeasurable (by fun_prop)

Depends on / 依赖: AEMeasurable, AEMeasurable.aestronglyMeasurable, AEStronglyMeasurable, AEStronglyMeasurable.pow, aestronglyMeasurable, comp_aemeasurable, fun_prop, hX.aestronglyMeasurable, hX.comp_aemeasurable, integral_map, variance_eq_integral
-/
lemma variance_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY : AEMeasurable Y μ) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  rw [variance_eq_integral hX]; rw [integral_map hY]; rw [variance_eq_integral (hX.comp_aemeasurable hY)]; rw [integral_map hY]
  · congr
  · exact hX.aestronglyMeasurable
  · refine AEStronglyMeasurable.pow ?_ _
    exact AEMeasurable.aestronglyMeasurable (by fun_prop)

/--
lemma `_root_.MeasureTheory.MeasurePreserving.variance_fun_comp` / 引理 `_root_.MeasureTheory.MeasurePreserving.variance_fun_comp`

English:
lemma _root_.MeasureTheory.MeasurePreserving.variance_fun_comp
  statement: {Ω' : Type*}
  proof: by
  rw [← hX.map_eq]; rw [variance_map (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.comp_def]

中文:
引理 _root_.MeasureTheory.MeasurePreserving.variance_fun_comp
  结论: {Ω' : 类型}
  证明: by
  rw [← hX.map_eq]; rw [variance_map (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, aemeasurable, comp_def, hX.aemeasurable, hX.map_eq, map_eq, variance_map
-/
lemma _root_.MeasureTheory.MeasurePreserving.variance_fun_comp {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {X : Ω -> Ω'}
    (hX : MeasurePreserving X μ ν) {f : Ω' -> Real} (hf : AEMeasurable f ν) :
    Var[fun ω => f (X ω); μ] = Var[f; ν] := by
  rw [← hX.map_eq]; rw [variance_map (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.comp_def]

/--
lemma `variance_map_equiv` / 引理 `variance_map_equiv`

English:
lemma variance_map_equiv
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  proof: by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv, Function.comp_apply]

中文:
引理 variance_map_equiv
  结论: {Ω' : 类型} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  证明: by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, evariance, integral_map_equiv, lintegral_map_equiv, simp_rw, variance
-/
lemma variance_map_equiv {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    (X : Ω -> Real) (Y : Ω' ≃ᵐ Ω) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv, Function.comp_apply]

/--
lemma `variance_id_map` / 引理 `variance_id_map`

English:
lemma variance_id_map
  given: (hX : AEMeasurable X μ)
  statement: Var[id; μ.map X] = Var[X; μ]
  proof: by
  simp [variance_map measurable_id.aemeasurable hX]

中文:
引理 variance_id_map
  条件: (hX : AEMeasurable X μ)
  结论: Var[id; μ.map X] = Var[X; μ]
  证明: by
  simp [variance_map measurable_id.aemeasurable hX]

Depends on / 依赖: aemeasurable, measurable_id, measurable_id.aemeasurable, variance_map
-/
lemma variance_id_map (hX : AEMeasurable X μ) : Var[id; μ.map X] = Var[X; μ] := by
  simp [variance_map measurable_id.aemeasurable hX]

/--
theorem `variance_le_expectation_sq` / 定理 `variance_le_expectation_sq`

English:
theorem variance_le_expectation_sq
  statement: [IsProbabilityMeasure μ] {X : Ω -> Real}
  proof: by
  by_cases hX : MemLp X 2 μ
  · rw [variance_eq_sub hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance]; rw [evariance_eq_lintegral_ofReal]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, sub_zero]


中文:
定理 variance_le_expectation_sq
  结论: [IsProbabilityMeasure μ] {X : Ω -> 实数}
  证明: by
  by_cases hX : MemLp X 2 μ
  · rw [variance_eq_sub hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance]; rw [evariance_eq_lintegral_ofReal]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, sub_zero]


Depends on / 依赖: Integrable, Pi.pow_apply, evariance_eq_lintegral_ofReal, fun_prop, integral_eq_lintegral_of_nonneg_ae, integral_nonneg, integral_undef, le_rfl, memLp_two_iff_integrable_sq, pow_apply, sq_nonneg, sub_le_self_iff, sub_zero, variance, variance_eq_sub
-/
theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω -> Real}
    (hm : AEStronglyMeasurable X μ) : variance X μ <= μ[X ^ 2] := by
  by_cases hX : MemLp X 2 μ
  · rw [variance_eq_sub hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance]; rw [evariance_eq_lintegral_ofReal]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, sub_zero]
      exact le_rfl
    · rw [integral_undef]
      · exact integral_nonneg fun a => sq_nonneg _
      intro h
      have A : MemLp (X - fun ω : Ω => μ[X]) 2 μ :=
        (memLp_two_iff_integrable_sq (by fun_prop)).2 h
      have B : MemLp (fun _ : Ω => μ[X]) 2 μ := memLp_const _
      apply hX
      convert! A.add B
      simp
  · exact Eventually.of_forall fun x => sq_nonneg _
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable

/--
theorem `evariance_def'` / 定理 `evariance_def'`

English:
theorem evariance_def'
  given: [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : AEStronglyMeasurable X μ)
  proof: by
  by_cases hℒ : MemLp X 2 μ
  · rw [← ofReal_variance hℒ, variance_eq_sub hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← enorm_pow, enorm]
    rw [lintegral_coe_eq_integral]
    · simp
    · simpa using hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ]; rw [ENNReal.s

中文:
定理 evariance_def'
  条件: [IsProbabilityMeasure μ] {X : Ω -> 实数} (hX : AEStronglyMeasurable X μ)
  证明: by
  by_cases hℒ : MemLp X 2 μ
  · rw [← ofReal_variance hℒ, variance_eq_sub hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← enorm_pow, enorm]
    rw [lintegral_coe_eq_integral]
    · simp
    · simpa using hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ]; rw [ENNReal.s

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, ENNReal.ofReal_ne_top, ENNReal.ofReal_sub, ENNReal.sub_eq_top_iff, ENNReal.toReal_ofNat, abs.integrable_sq, eLpNorm_eq_lintegral_rpow_enorm_toReal, enorm_pow, evariance_eq_top, integrable_sq, lintegral_coe_eq_integral, not_and, not_lt, ofNat_ne_top, ofReal_ne_top, ofReal_sub, ofReal_variance, one_di, simp_rw
-/
theorem evariance_def' [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : AEStronglyMeasurable X μ) :
    evariance X μ = (∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) - ENNReal.ofReal (μ[X] ^ 2) := by
  by_cases hℒ : MemLp X 2 μ
  · rw [← ofReal_variance hℒ, variance_eq_sub hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← enorm_pow, enorm]
    rw [lintegral_coe_eq_integral]
    · simp
    · simpa using hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ]; rw [ENNReal.sub_eq_top_iff]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [MemLp]; rw [not_and] at hℒ
    specialize hℒ hX
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, not_lt,
      top_le_iff, ENNReal.toReal_ofNat, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos,
      and_true, or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact mod_cast hℒ fun _ => zero_le_two

/--
theorem `meas_ge_le_evariance_div_sq` / 定理 `meas_ge_le_evariance_div_sq`

English:
theorem meas_ge_le_evariance_div_sq
  statement: {X : Ω -> Real} (hX : AEStronglyMeasurable X μ) {c : Real>=0}
  proof: by
  have A : (c : Real>=0∞) != 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert!
      meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top (hX.sub B) A (by simp)
    using 1
  · norm_cast
  rw [eLpNor

中文:
定理 meas_ge_le_evariance_div_sq
  结论: {X : Ω -> 实数} (hX : AEStronglyMeasurable X μ) {c : 实数>=0}
  证明: by
  have A : (c : Real>=0∞) != 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert!
      meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top (hX.sub B) A (by simp)
    using 1
  · norm_cast
  rw [eLpNor

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.coe_eq_zero, ENNReal.inv_pow, ENNReal.ofNat_ne_top, ENNReal.rpow_two, ENNReal.toReal_ofNat, Pi.sub_apply, aestronglyMeasurable_const, coe_eq_zero, convert, div_eq_mul_inv, eLpNorm_eq_lintegral_rpow_enorm_toReal, hX.sub, inv_pow, meas_ge_le_mul_pow_eLpNorm_enorm, mul_comm, ofNat_ne_top, one_div, rpow_two
-/
theorem meas_ge_le_evariance_div_sq {X : Ω -> Real} (hX : AEStronglyMeasurable X μ) {c : Real>=0}
    (hc : c != 0) : μ {ω | ↑c <= |X ω - μ[X]|} <= evariance X μ / c ^ 2 := by
  have A : (c : Real>=0∞) != 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert!
      meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top (hX.sub B) A (by simp)
    using 1
  · norm_cast
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div, Pi.sub_apply]
  rw [div_eq_mul_inv]; rw [ENNReal.inv_pow]; rw [mul_comm]; rw [ENNReal.rpow_two]
  congr
  simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : Real) != 0), ENNReal.rpow_two,
    ENNReal.rpow_one, evariance]

/--
theorem `meas_ge_le_variance_div_sq` / 定理 `meas_ge_le_variance_div_sq`

English:
theorem meas_ge_le_variance_div_sq
  statement: [IsFiniteMeasure μ] {X : Ω -> Real} (hX : MemLp X 2 μ) {c : Real}
  proof: by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm)]; rw [hX.ofReal_variance_eq]
  convert! @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

中文:
定理 meas_ge_le_variance_div_sq
  结论: [IsFiniteMeasure μ] {X : Ω -> 实数} (hX : MemLp X 2 μ) {c : 实数}
  证明: by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm)]; rw [hX.ofReal_variance_eq]
  convert! @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

Depends on / 依赖: ENNReal, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_pow, c.toNNReal, convert, hX.ofReal_variance_eq, hc.le, hc.ne.symm, meas_ge_le_evariance_div_sq, ofReal_div_of_pos, ofReal_pow, ofReal_variance_eq, sq_pos_of_ne_zero, toNNReal
-/
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω -> Real} (hX : MemLp X 2 μ) {c : Real}
    (hc : 0 < c) : μ {ω | c <= |X ω - μ[X]|} <= ENNReal.ofReal (variance X μ / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm)]; rw [hX.ofReal_variance_eq]
  convert! @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
nonrec theorem IndepFun.variance_add {X Y : Ω -> Real} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := by
  by_cases h' : X =ᵐ[μ] 0
  · rw [variance_congr h', variance_congr h'.add_right]
    simp
  have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
  rw [variance_add hX hY]; rw [h.covariance_eq_zero hX hY]
  simp

/--
lemma `IndepFun.variance_fun_add` / 引理 `IndepFun.variance_fun_add`

English:
lemma IndepFun.variance_fun_add
  statement: {X Y : Ω -> Real} (hX : MemLp X 2 μ)
  proof: h.variance_add hX hY

中文:
引理 IndepFun.variance_fun_add
  结论: {X Y : Ω -> 实数} (hX : MemLp X 2 μ)
  证明: h.variance_add hX hY

Depends on / 依赖: h.variance_add, variance_add
-/
lemma IndepFun.variance_fun_add {X Y : Ω -> Real} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[fun ω => X ω + Y ω; μ] = Var[X; μ] + Var[Y; μ] :=
  h.variance_add hX hY

/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι -> Ω -> Real} {s : Finset ι}
    (hs : forall i in s, MemLp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i in s, X i) μ = ∑ i in s, variance (X i) μ := by
  by_cases h'' : forall i in s, X i =ᵐ[μ] 0
  · rw [variance_congr (Y := 0), variance_zero]
    · symm
      refine Finset.sum_eq_zero fun i hi => ?_
      simp [variance_congr (h'' i hi)]
    · have := fun (i : s) => h'' i.1 i.2
      filter_upwards [ae_all_iff.2 this] with ω hω
      simp only [Finset.sum_apply, Pi.zero_apply]
      exact Finset.sum_eq_zero fun i hi => hω ⟨i, hi⟩
  obtain ⟨j, hj1, hj2⟩ := not_forall₂.1 h''
  obtain rfl | h' := s.eq_singleton_or_nontrivial hj1
  · simp
  obtain ⟨k, hk1, hk2⟩ := h'.exists_ne j
  have := (hs j hj1).isProbabilityMeasure_of_indepFun (X j) (X k) (by simp) (by simp) hj2
    (h hj1 hk1 hk2.symm)
  rw [variance_sum' hs]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← covariance_self (hs i hi).aemeasurable]
  refine Finset.sum_eq_single_of_mem i hi fun j hj1 hj2 => ?_
  exact (h hi hj1 hj2.symm).covariance_eq_zero (hs i hi) (hs j hj1)

/--
lemma `variance_sum_pi` / 引理 `variance_sum_pi`

English:
lemma variance_sum_pi
  statement: [Fintype ι] {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i)}
  proof: by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω => ω i); Measure.pi μ] = _
    rw [← variance_map]; rw [(measurePreserving_eval _ i).map_eq]
    · rw [(measurePreserving_eval _ i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeas

中文:
引理 variance_sum_pi
  结论: [Fintype ι] {Ω : ι -> 类型} {mΩ : 对任意 i, MeasurableSpace (Ω i)}
  证明: by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω => ω i); Measure.pi μ] = _
    rw [← variance_map]; rw [(measurePreserving_eval _ i).map_eq]
    · rw [(measurePreserving_eval _ i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeas

Depends on / 依赖: IndepFun, IndepFun.variance_sum, Measurable, Measurable.aemeasurable, Measure, Measure.pi, aemeasurable, aestronglyMeasurable, aestronglyMeasurable.aemeasurable, comp_measurePreserving, fun_prop, iIndepFun_pi, indepFun, map_eq, measurePreserving_eval, variance_map, variance_sum
-/
lemma variance_sum_pi [Fintype ι] {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i)}
    {μ : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (μ i)]
    {X : Π i, Ω i -> Real} (h : forall i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω => X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω => ω i); Measure.pi μ] = _
    rw [← variance_map]; rw [(measurePreserving_eval _ i).map_eq]
    · rw [(measurePreserving_eval _ i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ => (h i).comp_measurePreserving (measurePreserving_eval _ i)
  · exact fun i _ j _ hij =>
      (iIndepFun_pi fun i => (h i).aestronglyMeasurable.aemeasurable).indepFun hij

/--
lemma `variance_le_sub_mul_sub` / 引理 `variance_le_sub_mul_sub`

English:
lemma variance_le_sub_mul_sub
  statement: [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Real}
  proof: by
  have ha : forallᵐ ω ∂μ, a <= X ω := h.mono fun ω h => h.1
  have hb : forallᵐ ω ∂μ, X ω <= b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω => -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω => (a + b) * X ω) μ 

中文:
引理 variance_le_sub_mul_sub
  结论: [IsProbabilityMeasure μ] {a b : 实数} {X : Ω -> 实数}
  证明: by
  have ha : forallᵐ ω ∂μ, a <= X ω := h.mono fun ω h => h.1
  have hb : forallᵐ ω ∂μ, X ω <= b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω => -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω => (a + b) * X ω) μ 

Depends on / 依赖: Integrable, abs_le_max_abs_abs, aestronglyMeasurable, const_mul, filter_upwards, h.mono, hX.aestronglyMeasurable, integrable_const, integrable_sq, integrable_sq.neg, memLp_of_bounded
-/
lemma variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Real}
    (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ <= (b - μ[X]) * (μ[X] - a) := by
  have ha : forallᵐ ω ∂μ, a <= X ω := h.mono fun ω h => h.1
  have hb : forallᵐ ω ∂μ, X ω <= b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω => -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω => (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 <= -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ <= ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 <= b - X ω) (by linarith : 0 <= X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
integral_congr_ae ae_of_all μ fun ω => by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (by fun_prop) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_const_mul, integral_add hX_int₂ hX_int₁]
  calc
    _ <= (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_eq_sub (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring

/--
lemma `variance_le_sq_of_bounded` / 引理 `variance_le_sq_of_bounded`

English:
lemma variance_le_sq_of_bounded
  statement: [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Real}
  proof: calc
    _ <= (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ <= ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)

中文:
引理 variance_le_sq_of_bounded
  结论: [IsProbabilityMeasure μ] {a b : 实数} {X : Ω -> 实数}
  证明: calc
    _ <= (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ <= ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)

Depends on / 依赖: sq_nonneg, sub_le_self, variance_le_sub_mul_sub
-/
lemma variance_le_sq_of_bounded [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Real}
    (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ <= ((b - a) / 2) ^ 2 :=
  calc
    _ <= (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ <= ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)

section Prod

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {X : Ω -> Real} {Y : Ω' -> Real}

/--
lemma `variance_add_prod` / 引理 `variance_add_prod`

English:
lemma variance_add_prod
  given: (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν)
  proof: by
  refine (IndepFun.variance_fun_add (hfμ.comp_fst ν) (hgν.comp_snd μ) ?_).trans ?_
  · exact indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable
  · rw [measurePreserving_fst.variance_fun_comp hfμ.aemeasurable,
      measurePreserving_snd.variance_fun_comp hgν.aemeasurable]

中文:
引理 variance_add_prod
  条件: (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν)
  证明: by
  refine (IndepFun.variance_fun_add (hfμ.comp_fst ν) (hgν.comp_snd μ) ?_).trans ?_
  · exact indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable
  · rw [measurePreserving_fst.variance_fun_comp hfμ.aemeasurable,
      measurePreserving_snd.variance_fun_comp hgν.aemeasurable]

Depends on / 依赖: IndepFun, IndepFun.variance_fun_add, aemeasurable, comp_fst, comp_snd, measurePreserving_fst, measurePreserving_fst.variance_fun_comp, measurePreserving_snd, measurePreserving_snd.variance_fun_comp, variance_fun_add, variance_fun_comp
-/
lemma variance_add_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    Var[fun p => X p.1 + Y p.2; μ.prod ν] = Var[X; μ] + Var[Y; ν] := by
  refine (IndepFun.variance_fun_add (hfμ.comp_fst ν) (hgν.comp_snd μ) ?_).trans ?_
  · exact indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable
  · rw [measurePreserving_fst.variance_fun_comp hfμ.aemeasurable,
      measurePreserving_snd.variance_fun_comp hgν.aemeasurable]

end Prod

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace Real F] {mF : MeasurableSpace F}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]

/--
lemma `variance_dual_prod'` / 引理 `variance_dual_prod'`

English:
lemma variance_dual_prod'
  statement: {L : StrongDual Real (E × F)}
  proof: by
  have : L = fun x : E × F => L.comp (.inl Real E F) x.1 + L.comp (.inr Real E F) x.2 := by
    ext; rw [L.comp_inl_add_comp_inr]
  rw [this]; rw [variance_add_prod hLμ hLν]

中文:
引理 variance_dual_prod'
  结论: {L : StrongDual 实数 (E × F)}
  证明: by
  have : L = fun x : E × F => L.comp (.inl Real E F) x.1 + L.comp (.inr Real E F) x.2 := by
    ext; rw [L.comp_inl_add_comp_inr]
  rw [this]; rw [variance_add_prod hLμ hLν]

Depends on / 依赖: L.comp, L.comp_inl_add_comp_inr, comp_inl_add_comp_inr, variance_add_prod
-/
lemma variance_dual_prod' {L : StrongDual Real (E × F)}
    (hLμ : MemLp (L.comp (.inl Real E F)) 2 μ) (hLν : MemLp (L.comp (.inr Real E F)) 2 ν) :
    Var[L; μ.prod ν] = Var[L.comp (.inl Real E F); μ] + Var[L.comp (.inr Real E F); ν] := by
  have : L = fun x : E × F => L.comp (.inl Real E F) x.1 + L.comp (.inr Real E F) x.2 := by
    ext; rw [L.comp_inl_add_comp_inr]
  rw [this]; rw [variance_add_prod hLμ hLν]

/--
lemma `variance_dual_prod` / 引理 `variance_dual_prod`

English:
lemma variance_dual_prod
  given: {L : StrongDual Real (E × F)} (hLμ : MemLp id 2 μ) (hLν : MemLp id 2 ν)
  proof: variance_dual_prod' (ContinuousLinearMap.comp_memLp' _ hLμ)
    (ContinuousLinearMap.comp_memLp' _ hLν)

中文:
引理 variance_dual_prod
  条件: {L : StrongDual 实数 (E × F)} (hLμ : MemLp id 2 μ) (hLν : MemLp id 2 ν)
  证明: variance_dual_prod' (ContinuousLinearMap.comp_memLp' _ hLμ)
    (ContinuousLinearMap.comp_memLp' _ hLν)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_memLp, comp_memLp, variance_dual_prod
-/
lemma variance_dual_prod {L : StrongDual Real (E × F)} (hLμ : MemLp id 2 μ) (hLν : MemLp id 2 ν) :
    Var[L; μ.prod ν] = Var[L.comp (.inl Real E F); μ] + Var[L.comp (.inr Real E F); ν] :=
  variance_dual_prod' (ContinuousLinearMap.comp_memLp' _ hLμ)
    (ContinuousLinearMap.comp_memLp' _ hLν)

end NormedSpace

end ProbabilityTheory
