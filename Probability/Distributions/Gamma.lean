/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Gamma distributions over ℝ

Define the gamma measure over the reals.

## Main definitions
* `gammaPDFReal`: the function `a r x ↦ r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))`
  for `0 ≤ x` or `0` else, which is the probability density function of a gamma distribution with
  shape `a` and rate `r` (when `ha : 0 < a ` and `hr : 0 < r`).
* `gammaPDF`: `ℝ≥0∞`-valued pdf,
  `gammaPDF a r = ENNReal.ofReal (gammaPDFReal a r)`.
* `gammaMeasure`: a gamma measure on `ℝ`, parametrized by its shape `a` and rate `r`.

-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

/--
lemma `lintegral_Iic_eq_lintegral_Iio_add_Icc` / 引理 `lintegral_Iic_eq_lintegral_Iio_add_Icc`

English:
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc
  given: {y z : Real} (f : Real -> Real>=0∞) (hzy : z <= y)
  proof: by
  rw [← Iio_union_Icc_eq_Iic hzy]; rw [lintegral_union measurableSet_Icc]
  simp_rw [Set.disjoint_iff_forall_ne, mem_Iio, mem_Icc]
  intros
  linarith

中文:
引理 lintegral_Iic_eq_lintegral_Iio_add_Icc
  条件: {y z : 实数} (f : 实数 -> 实数>=0∞) (hzy : z <= y)
  证明: by
  rw [← Iio_union_Icc_eq_Iic hzy]; rw [lintegral_union measurableSet_Icc]
  simp_rw [Set.disjoint_iff_forall_ne, mem_Iio, mem_Icc]
  intros
  linarith

Depends on / 依赖: Iio_union_Icc_eq_Iic, Set.disjoint_iff_forall_ne, disjoint_iff_forall_ne, intros, lintegral_union, measurableSet_Icc, mem_Icc, mem_Iio, simp_rw
-/
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc {y z : Real} (f : Real -> Real>=0∞) (hzy : z <= y) :
    ∫⁻ x in Iic y, f x = (∫⁻ x in Iio z, f x) + ∫⁻ x in Icc z y, f x := by
  rw [← Iio_union_Icc_eq_Iic hzy]; rw [lintegral_union measurableSet_Icc]
  simp_rw [Set.disjoint_iff_forall_ne, mem_Iio, mem_Icc]
  intros
  linarith

namespace ProbabilityTheory

section GammaPDF

/-- The pdf of the gamma distribution depending on its scale and rate -/
noncomputable
/--
Definition of `gammaPDFReal` / `gammaPDFReal` 的定义

English:
definition gammaPDFReal
  signature: (a r x : Real)
  body: if 0 <= x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0

中文:
定义 gammaPDFReal
  签名: (a r x : 实数)
  定义体: if 0 <= x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0
-/
def gammaPDFReal (a r x : Real) : Real :=
  if 0 <= x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
/--
Definition of `gammaPDF` / `gammaPDF` 的定义

English:
definition gammaPDF
  signature: (a r x : Real)
  body: ENNReal.ofReal (gammaPDFReal a r x)

中文:
定义 gammaPDF
  签名: (a r x : 实数)
  定义体: ENNReal.ofReal (gammaPDFReal a r x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, gammaPDFReal, ofReal
-/
def gammaPDF (a r x : Real) : Real>=0∞ :=
  ENNReal.ofReal (gammaPDFReal a r x)

/--
lemma `gammaPDF_eq` / 引理 `gammaPDF_eq`

English:
lemma gammaPDF_eq
  given: (a r x : Real)
  proof: rfl

中文:
引理 gammaPDF_eq
  条件: (a r x : 实数)
  证明: rfl
-/
lemma gammaPDF_eq (a r x : Real) :
    gammaPDF a r x =
      ENNReal.ofReal (if 0 <= x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0) :=
  rfl

/--
lemma `gammaPDF_of_neg` / 引理 `gammaPDF_of_neg`

English:
lemma gammaPDF_of_neg
  given: {a r x : Real} (hx : x < 0)
  statement: gammaPDF a r x = 0
  proof: by
  simp only [gammaPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

中文:
引理 gammaPDF_of_neg
  条件: {a r x : 实数} (hx : x < 0)
  结论: gammaPDF a r x = 0
  证明: by
  simp only [gammaPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, gammaPDF_eq, if_neg, not_le, not_le.mpr, ofReal_zero
-/
lemma gammaPDF_of_neg {a r x : Real} (hx : x < 0) : gammaPDF a r x = 0 := by
  simp only [gammaPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

/--
lemma `gammaPDF_of_nonneg` / 引理 `gammaPDF_of_nonneg`

English:
lemma gammaPDF_of_nonneg
  given: {a r x : Real} (hx : 0 <= x)
  proof: by
  simp only [gammaPDF_eq, if_pos hx]

中文:
引理 gammaPDF_of_nonneg
  条件: {a r x : 实数} (hx : 0 <= x)
  证明: by
  simp only [gammaPDF_eq, if_pos hx]

Depends on / 依赖: gammaPDF_eq, if_pos
-/
lemma gammaPDF_of_nonneg {a r x : Real} (hx : 0 <= x) :
    gammaPDF a r x = ENNReal.ofReal (r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))) := by
  simp only [gammaPDF_eq, if_pos hx]

/--
lemma `lintegral_gammaPDF_of_nonpos` / 引理 `lintegral_gammaPDF_of_nonpos`

English:
lemma lintegral_gammaPDF_of_nonpos
  given: {x a r : Real} (hx : x <= 0)
  proof: by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [gammaPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

中文:
引理 lintegral_gammaPDF_of_nonpos
  条件: {x a r : 实数} (hx : x <= 0)
  证明: by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [gammaPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_zero, gammaPDF_eq, if_neg, lintegral_zero, measurableSet_Iio, ofReal_eq_zero, ofReal_zero, setLIntegral_congr_fun
-/
lemma lintegral_gammaPDF_of_nonpos {x a r : Real} (hx : x <= 0) :
    ∫⁻ y in Iio x, gammaPDF a r y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [gammaPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

/-- The gamma pdf is measurable. -/
@[fun_prop]
/--
lemma `measurable_gammaPDFReal` / 引理 `measurable_gammaPDFReal`

English:
lemma measurable_gammaPDFReal
  given: (a r : Real)
  statement: Measurable (gammaPDFReal a r)
  proof: Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

中文:
引理 measurable_gammaPDFReal
  条件: (a r : 实数)
  结论: Measurable (gammaPDF实数 a r)
  证明: Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

Depends on / 依赖: Measurable, Measurable.ite, const_mul, measurableSet_Ici, measurable_const, measurable_id, neg.exp, pow_const
-/
lemma measurable_gammaPDFReal (a r : Real) : Measurable (gammaPDFReal a r) :=
  Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

/-- The gamma pdf is strongly measurable -/
@[fun_prop]
/--
lemma `stronglyMeasurable_gammaPDFReal` / 引理 `stronglyMeasurable_gammaPDFReal`

English:
lemma stronglyMeasurable_gammaPDFReal
  given: (a r : Real)
  proof: (measurable_gammaPDFReal a r).stronglyMeasurable

中文:
引理 stronglyMeasurable_gammaPDFReal
  条件: (a r : 实数)
  证明: (measurable_gammaPDFReal a r).stronglyMeasurable

Depends on / 依赖: measurable_gammaPDFReal, stronglyMeasurable
-/
lemma stronglyMeasurable_gammaPDFReal (a r : Real) :
    StronglyMeasurable (gammaPDFReal a r) :=
  (measurable_gammaPDFReal a r).stronglyMeasurable

/--
lemma `gammaPDFReal_pos` / 引理 `gammaPDFReal_pos`

English:
lemma gammaPDFReal_pos
  given: {x a r : Real} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x)
  proof: by
  simp only [gammaPDFReal, if_pos hx.le]
  positivity

中文:
引理 gammaPDFReal_pos
  条件: {x a r : 实数} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x)
  证明: by
  simp only [gammaPDFReal, if_pos hx.le]
  positivity

Depends on / 依赖: gammaPDFReal, hx.le, if_pos
-/
lemma gammaPDFReal_pos {x a r : Real} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    0 < gammaPDFReal a r x := by
  simp only [gammaPDFReal, if_pos hx.le]
  positivity

/--
lemma `gammaPDFReal_nonneg` / 引理 `gammaPDFReal_nonneg`

English:
lemma gammaPDFReal_nonneg
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real)
  proof: by
  unfold gammaPDFReal
  split_ifs <;> positivity

中文:
引理 gammaPDFReal_nonneg
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r) (x : 实数)
  证明: by
  unfold gammaPDFReal
  split_ifs <;> positivity

Depends on / 依赖: gammaPDFReal, split_ifs
-/
lemma gammaPDFReal_nonneg {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real) :
    0 <= gammaPDFReal a r x := by
  unfold gammaPDFReal
  split_ifs <;> positivity

open Measure

/-- The pdf of the gamma distribution integrates to 1 -/
@[simp]
/--
lemma `lintegral_gammaPDF_eq_one` / 引理 `lintegral_gammaPDF_eq_one`

English:
lemma lintegral_gammaPDF_eq_one
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r)
  proof: by
  have leftSide : ∫⁻ x in Iio 0, gammaPDF a r x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio
      (fun x (hx : x < 0) => gammaPDF_of_neg hx)]; rw [lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPDF a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) *

中文:
引理 lintegral_gammaPDF_eq_one
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r)
  证明: by
  have leftSide : ∫⁻ x in Iio 0, gammaPDF a r x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio
      (fun x (hx : x < 0) => gammaPDF_of_neg hx)]; rw [lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPDF a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) *

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal_eq_one_iff, compl_Ici, gammaPDF, gammaPDF_of_neg, gammaPDF_of_nonneg, leftSide, lintegral_add_compl, lintegral_zero, measurableSet_Ici, measurableSet_Iio, ofReal, rightSide, setLIntegral_congr_fun, toReal_eq_one_iff
-/
lemma lintegral_gammaPDF_eq_one {a r : Real} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, gammaPDF a r x = 1 := by
  have leftSide : ∫⁻ x in Iio 0, gammaPDF a r x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio
      (fun x (hx : x < 0) => gammaPDF_of_neg hx)]; rw [lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPDF a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ => gammaPDF_of_nonneg)
  rw [← ENNReal.toReal_eq_one_iff]; rw [← lintegral_add_compl _ measurableSet_Ici]; rw [compl_Ici]; rw [leftSide]; rw [rightSide]; rw [add_zero]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [integral_Ici_eq_integral_Ioi, mul_assoc]
    rw [integral_const_mul]; rw [integral_rpow_mul_exp_neg_mul_Ioi ha hr]; rw [div_mul_eq_mul_div]; rw [← mul_assoc]; rw [mul_div_assoc]; rw [div_self (Gamma_pos_of_pos ha).ne']; rw [mul_one]; rw [div_rpow zero_le_one hr.le]; rw [one_rpow]; rw [mul_one_div]; rw [div_self (rpow_pos_of_pos hr _).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : 0 <= x) => by positivity)
  · apply (measurable_gammaPDFReal a r).aestronglyMeasurable.congr
refine (ae_restrict_iff' measurableSet_Ici).mpr ae_of_all _ fun x (hx : 0 <= x) => ?_
    simp_rw [gammaPDFReal, eq_true_intro hx, ite_true]

end GammaPDF

open MeasureTheory

/-- Measure defined by the gamma distribution -/
noncomputable
/--
Definition of `gammaMeasure` / `gammaMeasure` 的定义

English:
definition gammaMeasure
  signature: (a r : Real)
  body: volume.withDensity (gammaPDF a r)

中文:
定义 gammaMeasure
  签名: (a r : 实数)
  定义体: volume.withDensity (gammaPDF a r)

Depends on / 依赖: gammaPDF, volume, volume.withDensity, withDensity
-/
def gammaMeasure (a r : Real) : Measure Real :=
  volume.withDensity (gammaPDF a r)

/--
lemma `isProbabilityMeasure_gammaMeasure` / 引理 `isProbabilityMeasure_gammaMeasure`

English:
lemma isProbabilityMeasure_gammaMeasure
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r)
  proof: by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]

中文:
引理 isProbabilityMeasure_gammaMeasure
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r)
  证明: by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]

Depends on / 依赖: gammaMeasure, lintegral_gammaPDF_eq_one
-/
lemma isProbabilityMeasure_gammaMeasure {a r : Real} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]

section GammaCDF

/--
lemma `cdf_gammaMeasure_eq_integral` / 引理 `cdf_gammaMeasure_eq_integral`

English:
lemma cdf_gammaMeasure_eq_integral
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real)
  proof: by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [cdf_eq_real]; rw [gammaMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b => by simp [gamm

中文:
引理 cdf_gammaMeasure_eq_integral
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r) (x : 实数)
  证明: by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [cdf_eq_real]; rw [gammaMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b => by simp [gamm

Depends on / 依赖: IsProbabilityMeasure, ae_of_all, cdf_eq_real, fun_prop, gammaMeasure, gammaPDFReal_nonneg, integral_eq_lintegral_of_nonneg_ae, isProbabilityMeasure_gammaMeasure, measurableSet_Iic, measureReal_def, withDensity_apply
-/
lemma cdf_gammaMeasure_eq_integral {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real) :
    cdf (gammaMeasure a r) x = ∫ x in Iic x, gammaPDFReal a r x := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [cdf_eq_real]; rw [gammaMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b => by simp [gammaPDFReal_nonneg ha hr]
  · fun_prop

/--
lemma `cdf_gammaMeasure_eq_lintegral` / 引理 `cdf_gammaMeasure_eq_lintegral`

English:
lemma cdf_gammaMeasure_eq_lintegral
  given: {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real)
  proof: by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  simp only [gammaPDF, cdf_eq_real]
  simp [gammaMeasure, gammaPDF, measureReal_def]

中文:
引理 cdf_gammaMeasure_eq_lintegral
  条件: {a r : 实数} (ha : 0 < a) (hr : 0 < r) (x : 实数)
  证明: by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  simp only [gammaPDF, cdf_eq_real]
  simp [gammaMeasure, gammaPDF, measureReal_def]

Depends on / 依赖: IsProbabilityMeasure, cdf_eq_real, gammaMeasure, gammaPDF, isProbabilityMeasure_gammaMeasure, measureReal_def
-/
lemma cdf_gammaMeasure_eq_lintegral {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real) :
    cdf (gammaMeasure a r) x = ENNReal.toReal (∫⁻ x in Iic x, gammaPDF a r x) := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  simp only [gammaPDF, cdf_eq_real]
  simp [gammaMeasure, gammaPDF, measureReal_def]

end GammaCDF

end ProbabilityTheory
