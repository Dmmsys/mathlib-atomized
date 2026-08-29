/-
Copyright (c) 2024 Alvan Caleb Arulandu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvan Caleb Arulandu
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Pareto distributions over ℝ

Define the Pareto measure over the reals.

## Main definitions
* `paretoPDFReal`: the function `t r x ↦ r * t ^ r * x ^ -(r + 1)`
  for `t ≤ x` or `0` else, which is the probability density function of a Pareto distribution with
  scale `t` and shape `r` (when `ht : 0 < t` and `hr : 0 < r`).
* `paretoPDF`: `ℝ≥0∞`-valued pdf,
  `paretoPDF t r = ENNReal.ofReal (paretoPDFReal t r)`.
* `paretoMeasure`: a Pareto measure on `ℝ`, parametrized by its scale `t` and shape `r`.

-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory
variable {t r x : Real}

section ParetoPDF

/--
Definition of `paretoPDFReal` / `paretoPDFReal` 的定义

English:
definition paretoPDFReal
  signature: (t r x : Real)
  body: if t <= x then r * t ^ r * x ^ (-(r + 1)) else 0

中文:
定义 paretoPDFReal
  签名: (t r x : 实数)
  定义体: if t <= x then r * t ^ r * x ^ (-(r + 1)) else 0
-/
noncomputable def paretoPDFReal (t r x : Real) : Real :=
  if t <= x then r * t ^ r * x ^ (-(r + 1)) else 0

/--
Definition of `paretoPDF` / `paretoPDF` 的定义

English:
definition paretoPDF
  signature: (t r x : Real)
  body: ENNReal.ofReal (paretoPDFReal t r x)

中文:
定义 paretoPDF
  签名: (t r x : 实数)
  定义体: ENNReal.ofReal (paretoPDFReal t r x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, ofReal, paretoPDFReal
-/
noncomputable def paretoPDF (t r x : Real) : Real>=0∞ :=
  ENNReal.ofReal (paretoPDFReal t r x)

/--
lemma `paretoPDF_eq` / 引理 `paretoPDF_eq`

English:
lemma paretoPDF_eq
  given: (t r x : Real)
  proof: rfl

中文:
引理 paretoPDF_eq
  条件: (t r x : 实数)
  证明: rfl
-/
lemma paretoPDF_eq (t r x : Real) :
    paretoPDF t r x = ENNReal.ofReal (if t <= x then r * t ^ r * x ^ (-(r + 1)) else 0) := rfl

/--
lemma `paretoPDF_of_lt` / 引理 `paretoPDF_of_lt`

English:
lemma paretoPDF_of_lt
  given: (hx : x < t)
  statement: paretoPDF t r x = 0
  proof: by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

中文:
引理 paretoPDF_of_lt
  条件: (hx : x < t)
  结论: paretoPDF t r x = 0
  证明: by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, if_neg, not_le, not_le.mpr, ofReal_zero, paretoPDF_eq
-/
lemma paretoPDF_of_lt (hx : x < t) : paretoPDF t r x = 0 := by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

/--
lemma `paretoPDF_of_le` / 引理 `paretoPDF_of_le`

English:
lemma paretoPDF_of_le
  given: (hx : t <= x)
  proof: by
  simp only [paretoPDF_eq, if_pos hx]

中文:
引理 paretoPDF_of_le
  条件: (hx : t <= x)
  证明: by
  simp only [paretoPDF_eq, if_pos hx]

Depends on / 依赖: if_pos, paretoPDF_eq
-/
lemma paretoPDF_of_le (hx : t <= x) :
    paretoPDF t r x = ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) := by
  simp only [paretoPDF_eq, if_pos hx]

/--
lemma `lintegral_paretoPDF_of_le` / 引理 `lintegral_paretoPDF_of_le`

English:
lemma lintegral_paretoPDF_of_le
  given: (hx : x <= t)
  proof: by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [paretoPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

中文:
引理 lintegral_paretoPDF_of_le
  条件: (hx : x <= t)
  证明: by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [paretoPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_zero, if_neg, lintegral_zero, measurableSet_Iio, ofReal_eq_zero, ofReal_zero, paretoPDF_eq, setLIntegral_congr_fun
-/
lemma lintegral_paretoPDF_of_le (hx : x <= t) :
    ∫⁻ y in Iio x, paretoPDF t r y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [paretoPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

/-- The Pareto pdf is measurable. -/
@[fun_prop]
/--
lemma `measurable_paretoPDFReal` / 引理 `measurable_paretoPDFReal`

English:
lemma measurable_paretoPDFReal
  given: (t r : Real)
  statement: Measurable (paretoPDFReal t r)
  proof: Measurable.ite measurableSet_Ici ((measurable_id.pow_const _).const_mul _) measurable_const

中文:
引理 measurable_paretoPDFReal
  条件: (t r : 实数)
  结论: Measurable (paretoPDF实数 t r)
  证明: Measurable.ite measurableSet_Ici ((measurable_id.pow_const _).const_mul _) measurable_const

Depends on / 依赖: Measurable, Measurable.ite, const_mul, measurableSet_Ici, measurable_const, measurable_id, measurable_id.pow_const, pow_const
-/
lemma measurable_paretoPDFReal (t r : Real) : Measurable (paretoPDFReal t r) :=
  Measurable.ite measurableSet_Ici ((measurable_id.pow_const _).const_mul _) measurable_const

/-- The Pareto pdf is strongly measurable. -/
@[fun_prop]
/--
lemma `stronglyMeasurable_paretoPDFReal` / 引理 `stronglyMeasurable_paretoPDFReal`

English:
lemma stronglyMeasurable_paretoPDFReal
  given: (t r : Real)
  proof: (measurable_paretoPDFReal t r).stronglyMeasurable

中文:
引理 stronglyMeasurable_paretoPDFReal
  条件: (t r : 实数)
  证明: (measurable_paretoPDFReal t r).stronglyMeasurable

Depends on / 依赖: measurable_paretoPDFReal, stronglyMeasurable
-/
lemma stronglyMeasurable_paretoPDFReal (t r : Real) :
    StronglyMeasurable (paretoPDFReal t r) :=
  (measurable_paretoPDFReal t r).stronglyMeasurable

/--
lemma `paretoPDFReal_pos` / 引理 `paretoPDFReal_pos`

English:
lemma paretoPDFReal_pos
  given: (ht : 0 < t) (hr : 0 < r) (hx : t <= x)
  proof: by
  rw [paretoPDFReal]; rw [if_pos hx]
  have _ : 0 < x := by linarith
  positivity

中文:
引理 paretoPDFReal_pos
  条件: (ht : 0 < t) (hr : 0 < r) (hx : t <= x)
  证明: by
  rw [paretoPDFReal]; rw [if_pos hx]
  have _ : 0 < x := by linarith
  positivity

Depends on / 依赖: if_pos, paretoPDFReal
-/
lemma paretoPDFReal_pos (ht : 0 < t) (hr : 0 < r) (hx : t <= x) :
    0 < paretoPDFReal t r x := by
  rw [paretoPDFReal]; rw [if_pos hx]
  have _ : 0 < x := by linarith
  positivity

/--
lemma `paretoPDFReal_nonneg` / 引理 `paretoPDFReal_nonneg`

English:
lemma paretoPDFReal_nonneg
  given: (ht : 0 <= t) (hr : 0 <= r) (x : Real)
  proof: by
  unfold paretoPDFReal
  split_ifs with h
  · cases le_iff_eq_or_lt.1 ht with
    | inl ht0 =>
      rw [← ht0] at h
      positivity
    | inr htp =>
      positivity [lt_of_lt_of_le htp h]
  · positivity

中文:
引理 paretoPDFReal_nonneg
  条件: (ht : 0 <= t) (hr : 0 <= r) (x : 实数)
  证明: by
  unfold paretoPDFReal
  split_ifs with h
  · cases le_iff_eq_or_lt.1 ht with
    | inl ht0 =>
      rw [← ht0] at h
      positivity
    | inr htp =>
      positivity [lt_of_lt_of_le htp h]
  · positivity

Depends on / 依赖: le_iff_eq_or_lt, lt_of_lt_of_le, paretoPDFReal, split_ifs
-/
lemma paretoPDFReal_nonneg (ht : 0 <= t) (hr : 0 <= r) (x : Real) :
    0 <= paretoPDFReal t r x := by
  unfold paretoPDFReal
  split_ifs with h
  · cases le_iff_eq_or_lt.1 ht with
    | inl ht0 =>
      rw [← ht0] at h
      positivity
    | inr htp =>
      positivity [lt_of_lt_of_le htp h]
  · positivity

open Measure

/-- The pdf of the Pareto distribution integrates to `1`. -/
@[simp]
/--
lemma `lintegral_paretoPDF_eq_one` / 引理 `lintegral_paretoPDF_eq_one`

English:
lemma lintegral_paretoPDF_eq_one
  given: (ht : 0 < t) (hr : 0 < r)
  proof: by
  have leftSide : ∫⁻ x in Iio t, paretoPDF t r x = 0 := lintegral_paretoPDF_of_le (le_refl t)
  have rightSide : ∫⁻ x in Ici t, paretoPDF t r x =
      ∫⁻ x in Ici t, ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ => paretoPDF_of_le)
  rw [← ENN

中文:
引理 lintegral_paretoPDF_eq_one
  条件: (ht : 0 < t) (hr : 0 < r)
  证明: by
  have leftSide : ∫⁻ x in Iio t, paretoPDF t r x = 0 := lintegral_paretoPDF_of_le (le_refl t)
  have rightSide : ∫⁻ x in Ici t, paretoPDF t r x =
      ∫⁻ x in Ici t, ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ => paretoPDF_of_le)
  rw [← ENN

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal_eq_one_iff, add_zero, compl_Ici, integral_Ici_eq_integral_Ioi, integral_eq_lintegral_of_nonneg_ae, le_refl, leftSide, lintegral_add_compl, lintegral_paretoPDF_of_le, measurableSet_Ici, ofReal, paretoPDF, paretoPDF_of_le, rightSide, setLIntegral_congr_fun, toReal_eq_one_iff
-/
lemma lintegral_paretoPDF_eq_one (ht : 0 < t) (hr : 0 < r) :
    ∫⁻ x, paretoPDF t r x = 1 := by
  have leftSide : ∫⁻ x in Iio t, paretoPDF t r x = 0 := lintegral_paretoPDF_of_le (le_refl t)
  have rightSide : ∫⁻ x in Ici t, paretoPDF t r x =
      ∫⁻ x in Ici t, ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ => paretoPDF_of_le)
  rw [← ENNReal.toReal_eq_one_iff]; rw [← lintegral_add_compl _ measurableSet_Ici]; rw [compl_Ici]; rw [leftSide]; rw [rightSide]; rw [add_zero]; rw [← integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_Ioi_rpow_of_lt _ ht]
    · simp [field, ← rpow_add ht]
    linarith
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    filter_upwards with x hx using by positivity [lt_of_lt_of_le ht hx]
  · apply (measurable_paretoPDFReal t r).aestronglyMeasurable.congr
refine (ae_restrict_iff' measurableSet_Ici).mpr ae_of_all _ fun x (hx : t <= x) => ?_
    simp_rw [paretoPDFReal, eq_true_intro hx, ite_true]

end ParetoPDF

open MeasureTheory

/--
Definition of `paretoMeasure` / `paretoMeasure` 的定义

English:
definition paretoMeasure
  signature: (t r : Real)
  body: volume.withDensity (paretoPDF t r)

中文:
定义 paretoMeasure
  签名: (t r : 实数)
  定义体: volume.withDensity (paretoPDF t r)

Depends on / 依赖: paretoPDF, volume, volume.withDensity, withDensity
-/
noncomputable def paretoMeasure (t r : Real) : Measure Real :=
  volume.withDensity (paretoPDF t r)

/--
lemma `isProbabilityMeasure_paretoMeasure` / 引理 `isProbabilityMeasure_paretoMeasure`

English:
lemma isProbabilityMeasure_paretoMeasure
  given: (ht : 0 < t) (hr : 0 < r)
  proof: by simp [paretoMeasure, lintegral_paretoPDF_eq_one ht hr]

中文:
引理 isProbabilityMeasure_paretoMeasure
  条件: (ht : 0 < t) (hr : 0 < r)
  证明: by simp [paretoMeasure, lintegral_paretoPDF_eq_one ht hr]

Depends on / 依赖: lintegral_paretoPDF_eq_one, paretoMeasure
-/
lemma isProbabilityMeasure_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
    IsProbabilityMeasure (paretoMeasure t r) where
  measure_univ := by simp [paretoMeasure, lintegral_paretoPDF_eq_one ht hr]

section ParetoCDF

/--
lemma `cdf_paretoMeasure_eq_integral` / 引理 `cdf_paretoMeasure_eq_integral`

English:
lemma cdf_paretoMeasure_eq_integral
  given: (ht : 0 < t) (hr : 0 < r) (x : Real)
  proof: by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun _ => by simp on

中文:
引理 cdf_paretoMeasure_eq_integral
  条件: (ht : 0 < t) (hr : 0 < r) (x : 实数)
  证明: by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun _ => by simp on

Depends on / 依赖: IsProbabilityMeasure, Pi.zero_apply, ae_of_all, cdf_eq_real, fun_prop, hr.le, ht.le, integral_eq_lintegral_of_nonneg_ae, isProbabilityMeasure_paretoMeasure, measurableSet_Iic, measureReal_def, paretoMeasure, paretoPDFReal_nonneg, withDensity_apply, zero_apply
-/
lemma cdf_paretoMeasure_eq_integral (ht : 0 < t) (hr : 0 < r) (x : Real) :
    cdf (paretoMeasure t r) x = ∫ x in Iic x, paretoPDFReal t r x := by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun _ => by simp only [Pi.zero_apply, paretoPDFReal_nonneg ht.le hr.le]
  · fun_prop

/--
lemma `cdf_paretoMeasure_eq_lintegral` / 引理 `cdf_paretoMeasure_eq_lintegral`

English:
lemma cdf_paretoMeasure_eq_lintegral
  given: (ht : 0 < t) (hr : 0 < r) (x : Real)
  proof: by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]

中文:
引理 cdf_paretoMeasure_eq_lintegral
  条件: (ht : 0 < t) (hr : 0 < r) (x : 实数)
  证明: by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]

Depends on / 依赖: IsProbabilityMeasure, cdf_eq_real, isProbabilityMeasure_paretoMeasure, measurableSet_Iic, measureReal_def, paretoMeasure, withDensity_apply
-/
lemma cdf_paretoMeasure_eq_lintegral (ht : 0 < t) (hr : 0 < r) (x : Real) :
    cdf (paretoMeasure t r) x = ENNReal.toReal (∫⁻ x in Iic x, paretoPDF t r x) := by
  have : IsProbabilityMeasure (paretoMeasure t r) := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real]; rw [paretoMeasure]; rw [measureReal_def]; rw [withDensity_apply _ measurableSet_Iic]

end ParetoCDF
end ProbabilityTheory
