/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen, Patrick Massot
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Tactic.CrossRefAttribute

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of an exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (exponentialPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.

## Main results
* `cdf_expMeasure_eq`: Proof that the CDF of the exponential measure equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPDF

/-- The pdf of the exponential distribution depending on its rate -/
noncomputable
/--
Definition of `exponentialPDFReal` / `exponentialPDFReal` 的定义

English:
definition exponentialPDFReal
  signature: (r x : Real)
  body: gammaPDFReal 1 r x

中文:
定义 exponentialPDF实数
  签名: (r x : 实数)
  定义体: gammaPDFReal 1 r x

Depends on / 依赖: gammaPDFReal
-/
def exponentialPDFReal (r x : Real) : Real :=
  gammaPDFReal 1 r x

/-- The pdf of the exponential distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
/--
Definition of `exponentialPDF` / `exponentialPDF` 的定义

English:
definition exponentialPDF
  signature: (r x : Real)
  body: ENNReal.ofReal (exponentialPDFReal r x)

中文:
定义 exponentialPDF
  签名: (r x : 实数)
  定义体: ENNReal.ofReal (exponentialPDFReal r x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, exponentialPDFReal, ofReal
-/
def exponentialPDF (r x : Real) : Real>=0∞ :=
  ENNReal.ofReal (exponentialPDFReal r x)

/--
lemma `exponentialPDF_eq` / 引理 `exponentialPDF_eq`

English:
lemma exponentialPDF_eq
  given: (r x : Real)
  proof: by
  rw [exponentialPDF]; rw [exponentialPDFReal]; rw [gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

中文:
引理 exponentialPDF_eq
  条件: (r x : 实数)
  证明: by
  rw [exponentialPDF]; rw [exponentialPDFReal]; rw [gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

Depends on / 依赖: Gamma_one, div_one, exponentialPDF, exponentialPDFReal, gammaPDFReal, mul_one, rpow_one, rpow_zero, sub_self
-/
lemma exponentialPDF_eq (r x : Real) :
    exponentialPDF r x = ENNReal.ofReal (if 0 <= x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPDF]; rw [exponentialPDFReal]; rw [gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

/--
lemma `exponentialPDF_of_neg` / 引理 `exponentialPDF_of_neg`

English:
lemma exponentialPDF_of_neg
  given: {r x : Real} (hx : x < 0)
  statement: exponentialPDF r x = 0
  proof: gammaPDF_of_neg hx

中文:
引理 exponentialPDF_of_neg
  条件: {r x : 实数} (hx : x < 0)
  结论: exponentialPDF r x = 0
  证明: gammaPDF_of_neg hx

Depends on / 依赖: gammaPDF_of_neg
-/
lemma exponentialPDF_of_neg {r x : Real} (hx : x < 0) : exponentialPDF r x = 0 := gammaPDF_of_neg hx

/--
lemma `exponentialPDF_of_nonneg` / 引理 `exponentialPDF_of_nonneg`

English:
lemma exponentialPDF_of_nonneg
  given: {r x : Real} (hx : 0 <= x)
  proof: by
  simp only [exponentialPDF_eq, if_pos hx]

中文:
引理 exponentialPDF_of_nonneg
  条件: {r x : 实数} (hx : 0 <= x)
  证明: by
  simp only [exponentialPDF_eq, if_pos hx]

Depends on / 依赖: exponentialPDF_eq, if_pos
-/
lemma exponentialPDF_of_nonneg {r x : Real} (hx : 0 <= x) :
    exponentialPDF r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPDF_eq, if_pos hx]

/--
lemma `lintegral_exponentialPDF_of_nonpos` / 引理 `lintegral_exponentialPDF_of_nonpos`

English:
lemma lintegral_exponentialPDF_of_nonpos
  given: {x r : Real} (hx : x <= 0)
  proof: lintegral_gammaPDF_of_nonpos hx

中文:
引理 lintegral_exponentialPDF_of_nonpos
  条件: {x r : 实数} (hx : x <= 0)
  证明: lintegral_gammaPDF_of_nonpos hx

Depends on / 依赖: lintegral_gammaPDF_of_nonpos
-/
lemma lintegral_exponentialPDF_of_nonpos {x r : Real} (hx : x <= 0) :
    ∫⁻ y in Iio x, exponentialPDF r y = 0 := lintegral_gammaPDF_of_nonpos hx

/-- The exponential pdf is measurable. -/
@[fun_prop]
/--
lemma `measurable_exponentialPDFReal` / 引理 `measurable_exponentialPDFReal`

English:
lemma measurable_exponentialPDFReal
  given: (r : Real)
  statement: Measurable (exponentialPDFReal r)
  proof: measurable_gammaPDFReal 1 r

中文:
引理 measurable_exponentialPDF实数
  条件: (r : 实数)
  结论: 可测 (exponentialPDF实数 r)
  证明: measurable_gammaPDFReal 1 r

Depends on / 依赖: measurable_gammaPDFReal
-/
lemma measurable_exponentialPDFReal (r : Real) : Measurable (exponentialPDFReal r) :=
  measurable_gammaPDFReal 1 r

-- The exponential pdf is strongly measurable -/
@[fun_prop]
/--
lemma `stronglyMeasurable_exponentialPDFReal` / 引理 `stronglyMeasurable_exponentialPDFReal`

English:
lemma stronglyMeasurable_exponentialPDFReal
  given: (r : Real)
  proof: stronglyMeasurable_gammaPDFReal 1 r

中文:
引理 stronglyMeasurable_exponentialPDF实数
  条件: (r : 实数)
  证明: stronglyMeasurable_gammaPDFReal 1 r

Depends on / 依赖: stronglyMeasurable_gammaPDFReal
-/
lemma stronglyMeasurable_exponentialPDFReal (r : Real) :
    StronglyMeasurable (exponentialPDFReal r) := stronglyMeasurable_gammaPDFReal 1 r

/--
lemma `exponentialPDFReal_pos` / 引理 `exponentialPDFReal_pos`

English:
lemma exponentialPDFReal_pos
  given: {x r : Real} (hr : 0 < r) (hx : 0 < x)
  proof: gammaPDFReal_pos zero_lt_one hr hx

中文:
引理 exponentialPDF实数_pos
  条件: {x r : 实数} (hr : 0 < r) (hx : 0 < x)
  证明: gammaPDFReal_pos zero_lt_one hr hx

Depends on / 依赖: gammaPDFReal_pos, zero_lt_one
-/
lemma exponentialPDFReal_pos {x r : Real} (hr : 0 < r) (hx : 0 < x) :
    0 < exponentialPDFReal r x := gammaPDFReal_pos zero_lt_one hr hx

/--
lemma `exponentialPDFReal_nonneg` / 引理 `exponentialPDFReal_nonneg`

English:
lemma exponentialPDFReal_nonneg
  given: {r : Real} (hr : 0 < r) (x : Real)
  proof: gammaPDFReal_nonneg zero_lt_one hr x

中文:
引理 exponentialPDF实数_nonneg
  条件: {r : 实数} (hr : 0 < r) (x : 实数)
  证明: gammaPDFReal_nonneg zero_lt_one hr x

Depends on / 依赖: gammaPDFReal_nonneg, zero_lt_one
-/
lemma exponentialPDFReal_nonneg {r : Real} (hr : 0 < r) (x : Real) :
    0 <= exponentialPDFReal r x := gammaPDFReal_nonneg zero_lt_one hr x

open Measure

/-- The pdf of the exponential distribution integrates to 1 -/
@[simp]
/--
lemma `lintegral_exponentialPDF_eq_one` / 引理 `lintegral_exponentialPDF_eq_one`

English:
lemma lintegral_exponentialPDF_eq_one
  given: {r : Real} (hr : 0 < r)
  statement: ∫⁻ x, exponentialPDF r x = 1
  proof: lintegral_gammaPDF_eq_one zero_lt_one hr

中文:
引理 lintegral_exponentialPDF_eq_one
  条件: {r : 实数} (hr : 0 < r)
  结论: ∫⁻ x, exponentialPDF r x = 1
  证明: lintegral_gammaPDF_eq_one zero_lt_one hr

Depends on / 依赖: lintegral_gammaPDF_eq_one, zero_lt_one
-/
lemma lintegral_exponentialPDF_eq_one {r : Real} (hr : 0 < r) : ∫⁻ x, exponentialPDF r x = 1 :=
  lintegral_gammaPDF_eq_one zero_lt_one hr

end ExponentialPDF

open MeasureTheory

/-- Measure defined by the exponential distribution -/
@[wikidata Q237193]
noncomputable
/--
Definition of `expMeasure` / `expMeasure` 的定义

English:
definition expMeasure
  signature: (r : Real)
  body: gammaMeasure 1 r

中文:
定义 expMeasure
  签名: (r : 实数)
  定义体: gammaMeasure 1 r

Depends on / 依赖: gammaMeasure
-/
def expMeasure (r : Real) : Measure Real := gammaMeasure 1 r

/--
lemma `isProbabilityMeasure_expMeasure` / 引理 `isProbabilityMeasure_expMeasure`

English:
lemma isProbabilityMeasure_expMeasure
  given: {r : Real} (hr : 0 < r)
  proof: isProbabilityMeasure_gammaMeasure zero_lt_one hr

中文:
引理 isProbabilityMeasure_expMeasure
  条件: {r : 实数} (hr : 0 < r)
  证明: isProbabilityMeasure_gammaMeasure zero_lt_one hr

Depends on / 依赖: isProbabilityMeasure_gammaMeasure, zero_lt_one
-/
lemma isProbabilityMeasure_expMeasure {r : Real} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_gammaMeasure zero_lt_one hr

section ExponentialCDF

/--
lemma `cdf_expMeasure_eq_integral` / 引理 `cdf_expMeasure_eq_integral`

English:
lemma cdf_expMeasure_eq_integral
  given: {r : Real} (hr : 0 < r) (x : Real)
  proof: cdf_gammaMeasure_eq_integral zero_lt_one hr x

中文:
引理 cdf_expMeasure_eq_integral
  条件: {r : 实数} (hr : 0 < r) (x : 实数)
  证明: cdf_gammaMeasure_eq_integral zero_lt_one hr x

Depends on / 依赖: cdf_gammaMeasure_eq_integral, zero_lt_one
-/
lemma cdf_expMeasure_eq_integral {r : Real} (hr : 0 < r) (x : Real) :
    cdf (expMeasure r) x = ∫ x in Iic x, exponentialPDFReal r x :=
  cdf_gammaMeasure_eq_integral zero_lt_one hr x

/--
lemma `cdf_expMeasure_eq_lintegral` / 引理 `cdf_expMeasure_eq_lintegral`

English:
lemma cdf_expMeasure_eq_lintegral
  given: {r : Real} (hr : 0 < r) (x : Real)
  proof: cdf_gammaMeasure_eq_lintegral zero_lt_one hr x

中文:
引理 cdf_expMeasure_eq_lintegral
  条件: {r : 实数} (hr : 0 < r) (x : 实数)
  证明: cdf_gammaMeasure_eq_lintegral zero_lt_one hr x

Depends on / 依赖: cdf_gammaMeasure_eq_lintegral, zero_lt_one
-/
lemma cdf_expMeasure_eq_lintegral {r : Real} (hr : 0 < r) (x : Real) :
    cdf (expMeasure r) x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPDF r x) :=
  cdf_gammaMeasure_eq_lintegral zero_lt_one hr x

open Topology

/--
lemma `hasDerivAt_neg_exp_mul_exp` / 引理 `hasDerivAt_neg_exp_mul_exp`

English:
lemma hasDerivAt_neg_exp_mul_exp
  given: {r x : Real}
  proof: by
  convert! (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

中文:
引理 hasDerivAt_neg_exp_mul_exp
  条件: {r x : 实数}
  证明: by
  convert! (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

Depends on / 依赖: const_mul, convert, exp.const_mul, hasDerivAt_id, id_eq, mul_comm, mul_neg, mul_one, neg_mul, neg_neg, one_mul
-/
lemma hasDerivAt_neg_exp_mul_exp {r x : Real} :
    HasDerivAt (fun a => -exp (-(r * a))) (r * exp (-(r * x))) x := by
  convert! (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

/--
lemma `exp_neg_integrableOn_Ioc` / 引理 `exp_neg_integrableOn_Ioc`

English:
lemma exp_neg_integrableOn_Ioc
  given: {b x : Real} (hb : 0 < b)
  proof: by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

中文:
引理 exp_neg_integrableOn_Ioc
  条件: {b x : 实数} (hb : 0 < b)
  证明: by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

Depends on / 依赖: Ioc_subset_Ioi_self, exp_neg_integrableOn_Ioi, mono_set, neg_mul_eq_neg_mul
-/
lemma exp_neg_integrableOn_Ioc {b x : Real} (hb : 0 < b) :
    IntegrableOn (fun x => rexp (-(b * x))) (Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

/--
lemma `lintegral_exponentialPDF_eq_antiDeriv` / 引理 `lintegral_exponentialPDF_eq_antiDeriv`

English:
lemma lintegral_exponentialPDF_eq_antiDeriv
  given: {r : Real} (hr : 0 < r) (x : Real)
  proof: by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic]; rw [lintegral_zero]; rw [ENNReal.ofReal_zero]
    exact fun a (_ : a <= _) => by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral

中文:
引理 lintegral_exponentialPDF_eq_antiDeriv
  条件: {r : 实数} (hr : 0 < r) (x : 实数)
  证明: by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic]; rw [lintegral_zero]; rw [ENNReal.ofReal_zero]
    exact fun a (_ : a <= _) => by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_zero, exponentialPDF_eq, if_neg, le_refl, lintegral_Iic_eq_lintegral_Iio_add_Icc, lintegral_exponentialPDF_of_nonpos, lintegral_zero, measurableSet_Icc, measurableSet_Iic, ofReal, ofReal_eq_zero, ofReal_zero, setLIntegral_congr_fun, split_ifs, zero_add
-/
lemma lintegral_exponentialPDF_eq_antiDeriv {r : Real} (hr : 0 < r) (x : Real) :
    ∫⁻ y in Iic x, exponentialPDF r y
    = ENNReal.ofReal (if 0 <= x then 1 - exp (-(r * x)) else 0) := by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic]; rw [lintegral_zero]; rw [ENNReal.ofReal_zero]
    exact fun a (_ : a <= _) => by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ h]; rw [lintegral_exponentialPDF_of_nonpos (le_refl 0)]; rw [zero_add]
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun x => ENNReal.ofReal (r * rexp (-(r * x))))
      (by intro a ha; simp [ha.1])]
    rw [← ENNReal.toReal_eq_toReal_iff' _ ENNReal.ofReal_ne_top]; rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => le_of_lt
        (mul_pos hr (exp_pos _)))]
    · have : ∫ a in uIoc 0 x, r * rexp (-(r * a)) = ∫ a in 0..x, r * rexp (-(r * a)) := by
        rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]; rw [smul_eq_mul]; rw [if_pos h]; rw [one_mul]
      rw [integral_Icc_eq_integral_Ioc]; rw [← uIoc_of_le h]; rw [this]
      rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
        (f := fun a => -1 * rexp (-(r * a))) _ _]
      · rw [ENNReal.toReal_ofReal_eq_iff.2
          (sub_nonneg.2 (Real.exp_le_one_iff.2 <| by nlinarith))]
        norm_num; ring
      · simp only [intervalIntegrable_iff, uIoc_of_le h]
        exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _
      · have : Continuous (fun a => rexp (-(r * a))) := by
          simp only [← neg_mul]; exact (continuous_const_mul (-r)).rexp
        exact Continuous.continuousOn (Continuous.comp' (continuous_const_mul (-1)) this)
      · simp only [neg_mul, one_mul]
        exact fun _ _ => HasDerivAt.hasDerivWithinAt hasDerivAt_neg_exp_mul_exp
    · refine Integrable.aestronglyMeasurable (Integrable.const_mul ?_ _)
      rw [← IntegrableOn]; rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact exp_neg_integrableOn_Ioc hr
    · refine ne_of_lt (IntegrableOn.setLIntegral_lt_top ?_)
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _

/--
lemma `cdf_expMeasure_eq` / 引理 `cdf_expMeasure_eq`

English:
lemma cdf_expMeasure_eq
  given: {r : Real} (hr : 0 < r) (x : Real)
  proof: by
  rw [cdf_expMeasure_eq_lintegral hr]; rw [lintegral_exponentialPDF_eq_antiDeriv hr x]; rw [ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

中文:
引理 cdf_expMeasure_eq
  条件: {r : 实数} (hr : 0 < r) (x : 实数)
  证明: by
  rw [cdf_expMeasure_eq_lintegral hr]; rw [lintegral_exponentialPDF_eq_antiDeriv hr x]; rw [ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal_eq_iff, Left.neg_nonpos_iff, cdf_expMeasure_eq_lintegral, exp_le_one_iff, hr.le, le_rfl, lintegral_exponentialPDF_eq_antiDeriv, mul_nonneg, neg_nonpos_iff, split_ifs, sub_nonneg, toReal_ofReal_eq_iff
-/
lemma cdf_expMeasure_eq {r : Real} (hr : 0 < r) (x : Real) :
    cdf (expMeasure r) x = if 0 <= x then 1 - exp (-(r * x)) else 0 := by
  rw [cdf_expMeasure_eq_lintegral hr]; rw [lintegral_exponentialPDF_eq_antiDeriv hr x]; rw [ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

end ExponentialCDF

end ProbabilityTheory
