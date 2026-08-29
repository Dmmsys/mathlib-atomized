/-
Copyright (c) 2025 Tommy Löfgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `0 < α` and `0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

/--
Definition of `beta` / `beta` 的定义

English:
definition beta
  signature: (α β : Real)
  body: Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

中文:
定义 beta
  签名: (α β : 实数)
  定义体: Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

Depends on / 依赖: Real.Gamma
-/
noncomputable def beta (α β : Real) : Real :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

/--
lemma `beta_pos` / 引理 `beta_pos`

English:
lemma beta_pos
  given: {α β : Real} (hα : 0 < α) (hβ : 0 < β)
  statement: 0 < beta α β
  proof: div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

中文:
引理 beta_pos
  条件: {α β : 实数} (hα : 0 < α) (hβ : 0 < β)
  结论: 0 < beta α β
  证明: div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

Depends on / 依赖: Gamma_pos_of_pos, Real.Gamma_pos_of_pos, add_pos, div_pos, mul_pos
-/
lemma beta_pos {α β : Real} (hα : 0 < α) (hβ : 0 < β) : 0 < beta α β :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

/--
theorem `beta_eq_betaIntegralReal` / 定理 `beta_eq_betaIntegralReal`

English:
theorem beta_eq_betaIntegralReal
  given: (α β : Real) (hα : 0 < α) (hβ : 0 < β)
  proof: by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

中文:
定理 beta_eq_beta整数egral实数
  条件: (α β : 实数) (hα : 0 < α) (hβ : 0 < β)
  证明: by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

Depends on / 依赖: Gamma_ofReal, all_goals, betaIntegral_eq_Gamma_mul_div, ofReal_add, simp_rw
-/
theorem beta_eq_betaIntegralReal (α β : Real) (hα : 0 < α) (hβ : 0 < β) :
    beta α β = (betaIntegral α β).re := by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

/--
Definition of `betaPDFReal` / `betaPDFReal` 的定义

English:
definition betaPDFReal
  signature: (α β x : Real)
  body: if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

中文:
定义 betaPDF实数
  签名: (α β x : 实数)
  定义体: if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0
-/
noncomputable def betaPDFReal (α β x : Real) : Real :=
  if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

/--
Definition of `betaPDF` / `betaPDF` 的定义

English:
definition betaPDF
  signature: (α β x : Real)
  body: ENNReal.ofReal (betaPDFReal α β x)

中文:
定义 betaPDF
  签名: (α β x : 实数)
  定义体: ENNReal.ofReal (betaPDFReal α β x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, betaPDFReal, ofReal
-/
noncomputable def betaPDF (α β x : Real) : Real>=0∞ :=
  ENNReal.ofReal (betaPDFReal α β x)

/--
lemma `betaPDF_eq` / 引理 `betaPDF_eq`

English:
lemma betaPDF_eq
  given: (α β x : Real)
  proof: rfl

中文:
引理 betaPDF_eq
  条件: (α β x : 实数)
  证明: rfl
-/
lemma betaPDF_eq (α β x : Real) :
    betaPDF α β x =
      ENNReal.ofReal (if 0 < x ∧ x < 1 then
        (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1) else 0) := rfl

/--
lemma `betaPDF_eq_zero_of_nonpos` / 引理 `betaPDF_eq_zero_of_nonpos`

English:
lemma betaPDF_eq_zero_of_nonpos
  given: {α β x : Real} (hx : x <= 0)
  proof: by
  simp [betaPDF_eq, hx.not_gt]

中文:
引理 betaPDF_eq_zero_of_nonpos
  条件: {α β x : 实数} (hx : x <= 0)
  证明: by
  simp [betaPDF_eq, hx.not_gt]

Depends on / 依赖: betaPDF_eq, hx.not_gt, not_gt
-/
lemma betaPDF_eq_zero_of_nonpos {α β x : Real} (hx : x <= 0) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

/--
lemma `betaPDF_eq_zero_of_one_le` / 引理 `betaPDF_eq_zero_of_one_le`

English:
lemma betaPDF_eq_zero_of_one_le
  given: {α β x : Real} (hx : 1 <= x)
  proof: by
  simp [betaPDF_eq, hx.not_gt]

中文:
引理 betaPDF_eq_zero_of_one_le
  条件: {α β x : 实数} (hx : 1 <= x)
  证明: by
  simp [betaPDF_eq, hx.not_gt]

Depends on / 依赖: betaPDF_eq, hx.not_gt, not_gt
-/
lemma betaPDF_eq_zero_of_one_le {α β x : Real} (hx : 1 <= x) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

/--
lemma `betaPDF_of_pos_lt_one` / 引理 `betaPDF_of_pos_lt_one`

English:
lemma betaPDF_of_pos_lt_one
  given: {α β x : Real} (hx_pos : 0 < x) (hx_lt : x < 1)
  proof: by
  rw [betaPDF_eq]; rw [if_pos ⟨hx_pos]; rw [hx_lt⟩]

中文:
引理 betaPDF_of_pos_lt_one
  条件: {α β x : 实数} (hx_pos : 0 < x) (hx_lt : x < 1)
  证明: by
  rw [betaPDF_eq]; rw [if_pos ⟨hx_pos]; rw [hx_lt⟩]

Depends on / 依赖: betaPDF_eq, hx_lt, hx_pos, if_pos
-/
lemma betaPDF_of_pos_lt_one {α β x : Real} (hx_pos : 0 < x) (hx_lt : x < 1) :
    betaPDF α β x = ENNReal.ofReal ((1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [betaPDF_eq]; rw [if_pos ⟨hx_pos]; rw [hx_lt⟩]

/--
lemma `lintegral_betaPDF` / 引理 `lintegral_betaPDF`

English:
lemma lintegral_betaPDF
  given: {α β : Real}
  proof: by
  rw [← lintegral_add_compl _ measurableSet_Iic]; rw [setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x <= 0) => betaPDF_eq_zero_of_nonpos hx)]; rw [zero_add]; rw [compl_Iic]; rw [← lintegral_add_compl _ measurableSet_Ici]; rw [setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 <= x) => be

中文:
引理 lintegral_betaPDF
  条件: {α β : 实数}
  证明: by
  rw [← lintegral_add_compl _ measurableSet_Iic]; rw [setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x <= 0) => betaPDF_eq_zero_of_nonpos hx)]; rw [zero_add]; rw [compl_Iic]; rw [← lintegral_add_compl _ measurableSet_Ici]; rw [setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 <= x) => be

Depends on / 依赖: Iio_inter_Ioi, Measure, Measure.restrict_restrict, betaPDF_eq_zero_of_nonpos, betaPDF_eq_zero_of_one_le, compl_Ici, compl_Iic, hx_lt, hx_pos, lintegral_add_compl, measurableSet_Ici, measurableSet_Iic, measurableSet_Iio, measurableSet_Ioo, restrict_restrict, setLIntegral_congr_fun, setLIntegral_eq_zero, zero_add
-/
lemma lintegral_betaPDF {α β : Real} :
    ∫⁻ x, betaPDF α β x =
      ∫⁻ (x : Real) in Ioo 0 1, ENNReal.ofReal (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [← lintegral_add_compl _ measurableSet_Iic]; rw [setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x <= 0) => betaPDF_eq_zero_of_nonpos hx)]; rw [zero_add]; rw [compl_Iic]; rw [← lintegral_add_compl _ measurableSet_Ici]; rw [setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 <= x) => betaPDF_eq_zero_of_one_le hx)]; rw [zero_add]; rw [compl_Ici]; rw [Measure.restrict_restrict measurableSet_Iio]; rw [Iio_inter_Ioi]; rw [setLIntegral_congr_fun measurableSet_Ioo
      (fun x ⟨hx_pos]; rw [hx_lt⟩ => betaPDF_of_pos_lt_one hx_pos hx_lt)]

/--
lemma `betaPDFReal_pos` / 引理 `betaPDFReal_pos`

English:
lemma betaPDFReal_pos
  given: {α β x : Real} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β)
  proof: by
  rw [betaPDFReal]; rw [if_pos ⟨hx1]; rw [hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

中文:
引理 betaPDF实数_pos
  条件: {α β x : 实数} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β)
  证明: by
  rw [betaPDFReal]; rw [if_pos ⟨hx1]; rw [hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

Depends on / 依赖: Real.rpow_pos_of_pos, betaPDFReal, beta_pos, if_pos, mul_pos, one_div_pos, rpow_pos_of_pos
-/
lemma betaPDFReal_pos {α β x : Real} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < betaPDFReal α β x := by
  rw [betaPDFReal]; rw [if_pos ⟨hx1]; rw [hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

/-- The beta pdf is measurable. -/
@[fun_prop]
/--
lemma `measurable_betaPDFReal` / 引理 `measurable_betaPDFReal`

English:
lemma measurable_betaPDFReal
  given: (α β : Real)
  statement: Measurable (betaPDFReal α β)
  proof: Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

中文:
引理 measurable_betaPDF实数
  条件: (α β : 实数)
  结论: 可测 (betaPDF实数 α β)
  证明: Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

Depends on / 依赖: Measurable, Measurable.ite, fun_prop, measurableSet_Ioo
-/
lemma measurable_betaPDFReal (α β : Real) : Measurable (betaPDFReal α β) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

/-- The beta pdf is strongly measurable. -/
@[fun_prop]
/--
lemma `stronglyMeasurable_betaPDFReal` / 引理 `stronglyMeasurable_betaPDFReal`

English:
lemma stronglyMeasurable_betaPDFReal
  given: (α β : Real)
  proof: (measurable_betaPDFReal α β).stronglyMeasurable

中文:
引理 stronglyMeasurable_betaPDF实数
  条件: (α β : 实数)
  证明: (measurable_betaPDFReal α β).stronglyMeasurable

Depends on / 依赖: measurable_betaPDFReal, stronglyMeasurable
-/
lemma stronglyMeasurable_betaPDFReal (α β : Real) :
    StronglyMeasurable (betaPDFReal α β) := (measurable_betaPDFReal α β).stronglyMeasurable

/-- The pdf of the beta distribution integrates to 1. -/
@[simp]
/--
lemma `lintegral_betaPDF_eq_one` / 引理 `lintegral_betaPDF_eq_one`

English:
lemma lintegral_betaPDF_eq_one
  given: {α β : Real} (hα : 0 < α) (hβ : 0 < β)
  proof: by
  rw [lintegral_betaPDF]; rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ))]; rw [beta_eq_betaIntegralReal α β hα hβ]; rw [betaIntegral]; rw [intervalIntegral

中文:
引理 lintegral_betaPDF_eq_one
  条件: {α β : 实数} (hα : 0 < α) (hβ : 0 < β)
  证明: by
  rw [lintegral_betaPDF]; rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ))]; rw [beta_eq_betaIntegralReal α β hα hβ]; rw [betaIntegral]; rw [intervalIntegral

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, RCLike, RCLike.re_to_complex, betaIntegral, beta_eq_betaIntegralReal, beta_pos, div_eq_one_iff_eq, integral_Ioc_eq_integral_Ioo, integral_const_mul, integral_eq_lintegral_of_nonneg_ae, integral_of_le, integral_re, intervalIntegral, intervalIntegral.integral_of_le, lintegral_betaPDF, measurableSet_Ioc, mul_assoc, ne_of_gt, re_to_complex
-/
lemma lintegral_betaPDF_eq_one {α β : Real} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β x = 1 := by
  rw [lintegral_betaPDF]; rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ))]; rw [beta_eq_betaIntegralReal α β hα hβ]; rw [betaIntegral]; rw [intervalIntegral.integral_of_le (by norm_num)]; rw [← integral_Ioc_eq_integral_Ioo]; rw [← RCLike.re_to_complex]; rw [← integral_re]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ => ?_
      norm_cast
      rw [← Complex.ofReal_cpow]; rw [← Complex.ofReal_cpow]; rw [RCLike.re_to_complex]; rw [Complex.re_mul_ofReal]; rw [Complex.ofReal_re]
      all_goals linarith
    convert! betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp)]; rw [IntegrableOn]
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
.le using 1 convert! betaPDFReal_pos hx.1 hx.2 hα hβ
    rw [betaPDFReal]; rw [if_pos ⟨hx.1]; rw [hx.2⟩]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

end BetaPDF

/-- Measure defined by the beta distribution. -/
noncomputable
/--
Definition of `betaMeasure` / `betaMeasure` 的定义

English:
definition betaMeasure
  signature: (α β : Real)
  body: volume.withDensity (betaPDF α β)

中文:
定义 betaMeasure
  签名: (α β : 实数)
  定义体: volume.withDensity (betaPDF α β)

Depends on / 依赖: betaPDF, volume, volume.withDensity, withDensity
-/
def betaMeasure (α β : Real) : Measure Real :=
  volume.withDensity (betaPDF α β)

/--
lemma `isProbabilityMeasureBeta` / 引理 `isProbabilityMeasureBeta`

English:
lemma isProbabilityMeasureBeta
  given: {α β : Real} (hα : 0 < α) (hβ : 0 < β)
  proof: by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

中文:
引理 isProbabilityMeasureBeta
  条件: {α β : 实数} (hα : 0 < α) (hβ : 0 < β)
  证明: by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

Depends on / 依赖: betaMeasure, lintegral_betaPDF_eq_one
-/
lemma isProbabilityMeasureBeta {α β : Real} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

end ProbabilityTheory
