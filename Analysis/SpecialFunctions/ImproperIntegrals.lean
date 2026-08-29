/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`).

## See also

- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: specific integrals over finite intervals
- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: integral of `exp (-x ^ 2)`
- `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`: integrability of `(1+‖x‖)^(-r)`.
-/

public section


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

/--
theorem `integrableOn_exp_Iic` / 定理 `integrableOn_exp_Iic`

English:
theorem integrableOn_exp_Iic
  given: (c : Real)
  statement: IntegrableOn exp (Iic c)
  proof: by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

中文:
定理 integrableOn_exp_Iic
  条件: (c : 实数)
  结论: 整数egrableOn exp (Iic c)
  证明: by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

Depends on / 依赖: Iic_mem_atBot, eventually_of_mem, exp_pos, integrableOn_Iic_of_intervalIntegral_norm_bounded, integral_exp, intervalIntegrable_exp, norm_of_nonneg, simp_rw, sub_le_self_iff, tendsto_id
-/
theorem integrableOn_exp_Iic (c : Real) : IntegrableOn exp (Iic c) := by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

/--
theorem `integrableOn_exp_neg_Ioi` / 定理 `integrableOn_exp_neg_Ioi`

English:
theorem integrableOn_exp_neg_Ioi
  given: (c : Real)
  statement: IntegrableOn (fun (x : Real) => exp (-x)) (Ioi c)
  proof: Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

中文:
定理 integrableOn_exp_neg_Ioi
  条件: (c : 实数)
  结论: 整数egrableOn (fun (x : 实数) => exp (-x)) (Ioi c)
  证明: Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

Depends on / 依赖: Iff.mp, comp_neg_Ici, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_exp_Iic
-/
theorem integrableOn_exp_neg_Ioi (c : Real) : IntegrableOn (fun (x : Real) => exp (-x)) (Ioi c) :=
  Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

/--
theorem `integral_exp_Iic` / 定理 `integral_exp_Iic`

English:
theorem integral_exp_Iic
  given: (c : Real)
  statement: ∫ x : Real in Iic c, exp x = exp c
  proof: by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

中文:
定理 integral_exp_Iic
  条件: (c : 实数)
  结论: ∫ x : 实数 in Iic c, exp x = exp c
  证明: by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

Depends on / 依赖: const_sub, integrableOn_exp_Iic, integral_exp, intervalIntegral_tendsto_integral_Iic, simp_rw, sub_zero, tendsto_exp_atBot, tendsto_exp_atBot.const_sub, tendsto_id, tendsto_nhds_unique
-/
theorem integral_exp_Iic (c : Real) : ∫ x : Real in Iic c, exp x = exp c := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

/--
theorem `integral_exp_Iic_zero` / 定理 `integral_exp_Iic_zero`

English:
theorem integral_exp_Iic_zero
  statement: ∫ x : Real in Iic 0, exp x = 1
  proof: exp_zero ▸ integral_exp_Iic 0

中文:
定理 integral_exp_Iic_zero
  结论: ∫ x : 实数 in Iic 0, exp x = 1
  证明: exp_zero ▸ integral_exp_Iic 0

Depends on / 依赖: exp_zero, integral_exp_Iic
-/
theorem integral_exp_Iic_zero : ∫ x : Real in Iic 0, exp x = 1 :=
  exp_zero ▸ integral_exp_Iic 0

/--
theorem `integral_exp_neg_Ioi` / 定理 `integral_exp_neg_Ioi`

English:
theorem integral_exp_neg_Ioi
  given: (c : Real)
  statement: (∫ x : Real in Ioi c, exp (-x)) = exp (-c)
  proof: by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

中文:
定理 integral_exp_neg_Ioi
  条件: (c : 实数)
  结论: (∫ x : 实数 in Ioi c, exp (-x)) = exp (-c)
  证明: by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

Depends on / 依赖: integral_comp_neg_Ioi, integral_exp_Iic
-/
theorem integral_exp_neg_Ioi (c : Real) : (∫ x : Real in Ioi c, exp (-x)) = exp (-c) := by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

/--
theorem `integral_exp_neg_Ioi_zero` / 定理 `integral_exp_neg_Ioi_zero`

English:
theorem integral_exp_neg_Ioi_zero
  statement: (∫ x : Real in Ioi 0, exp (-x)) = 1
  proof: by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

中文:
定理 integral_exp_neg_Ioi_zero
  结论: (∫ x : 实数 in Ioi 0, exp (-x)) = 1
  证明: by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

Depends on / 依赖: exp_zero, integral_exp_neg_Ioi, neg_zero
-/
theorem integral_exp_neg_Ioi_zero : (∫ x : Real in Ioi 0, exp (-x)) = 1 := by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

/--
theorem `integrableOn_exp_mul_complex_Ioi` / 定理 `integrableOn_exp_mul_complex_Ioi`

English:
theorem integrableOn_exp_mul_complex_Ioi
  given: {a : Complex} (ha : a.re < 0) (c : Real)
  proof: by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using!
(integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr
        integrableOn_exp_neg_Ioi _

中文:
定理 integrableOn_exp_mul_complex_Ioi
  条件: {a : Complex} (ha : a.re < 0) (c : 实数)
  证明: by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using!
(integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr
        integrableOn_exp_neg_Ioi _

Depends on / 依赖: Complex.norm_exp, Continuous, Continuous.aestronglyMeasurable, a.re, aestronglyMeasurable, fun_prop, integrableOn_Ioi_comp_mul_left_iff, integrableOn_exp_neg_Ioi, integrable_norm_iff, norm_exp
-/
theorem integrableOn_exp_mul_complex_Ioi {a : Complex} (ha : a.re < 0) (c : Real) :
    IntegrableOn (fun x : Real => Complex.exp (a * x)) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using!
(integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr
        integrableOn_exp_neg_Ioi _

/--
theorem `integrableOn_exp_mul_complex_Iic` / 定理 `integrableOn_exp_mul_complex_Iic`

English:
theorem integrableOn_exp_mul_complex_Iic
  given: {a : Complex} (ha : 0 < a.re) (c : Real)
  proof: by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

中文:
定理 integrableOn_exp_mul_complex_Iic
  条件: {a : Complex} (ha : 0 < a.re) (c : 实数)
  证明: by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

Depends on / 依赖: Iff.mpr, comp_neg_Iio, integrableOn_Iic_iff_integrableOn_Iio, integrableOn_exp_mul_complex_Ioi
-/
theorem integrableOn_exp_mul_complex_Iic {a : Complex} (ha : 0 < a.re) (c : Real) :
    IntegrableOn (fun x : Real => Complex.exp (a * x)) (Iic c) := by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

/--
theorem `integrableOn_exp_mul_Ioi` / 定理 `integrableOn_exp_mul_Ioi`

English:
theorem integrableOn_exp_mul_Ioi
  given: {a : Real} (ha : a < 0) (c : Real)
  proof: by
have := Integrable.norm integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

中文:
定理 integrableOn_exp_mul_Ioi
  条件: {a : 实数} (ha : a < 0) (c : 实数)
  证明: by
have := Integrable.norm integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

Depends on / 依赖: Complex.norm_exp, Integrable, Integrable.norm, integrableOn_exp_mul_complex_Ioi, norm_exp
-/
theorem integrableOn_exp_mul_Ioi {a : Real} (ha : a < 0) (c : Real) :
    IntegrableOn (fun x : Real => Real.exp (a * x)) (Ioi c) := by
have := Integrable.norm integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

/--
theorem `integrableOn_exp_mul_Iic` / 定理 `integrableOn_exp_mul_Iic`

English:
theorem integrableOn_exp_mul_Iic
  given: {a : Real} (ha : 0 < a) (c : Real)
  proof: by
have := Integrable.norm integrableOn_exp_mul_complex_Iic (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

中文:
定理 integrableOn_exp_mul_Iic
  条件: {a : 实数} (ha : 0 < a) (c : 实数)
  证明: by
have := Integrable.norm integrableOn_exp_mul_complex_Iic (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

Depends on / 依赖: Complex.norm_exp, Integrable, Integrable.norm, integrableOn_exp_mul_complex_Iic, norm_exp
-/
theorem integrableOn_exp_mul_Iic {a : Real} (ha : 0 < a) (c : Real) :
    IntegrableOn (fun x : Real => Real.exp (a * x)) (Iic c) := by
have := Integrable.norm integrableOn_exp_mul_complex_Iic (a := a) (by simpa using! ha) c
  simpa [Complex.norm_exp] using! this

/--
theorem `integral_exp_mul_complex_Ioi` / 定理 `integral_exp_mul_complex_Ioi`

English:
theorem integral_exp_mul_complex_Ioi
  given: {a : Complex} (ha : a.re < 0) (c : Real)
  proof: by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) (by aesop), id_eq]
  suffices Tendsto (fun x : Real => Complex.exp (a * x)) atTop (𝓝 0) by
.div_const _ simpa using this.su

中文:
定理 integral_exp_mul_complex_Ioi
  条件: {a : Complex} (ha : a.re < 0) (c : 实数)
  证明: by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) (by aesop), id_eq]
  suffices Tendsto (fun x : Real => Complex.exp (a * x)) atTop (𝓝 0) by
.div_const _ simpa using this.su

Depends on / 依赖: Complex.exp, Complex.tendsto_exp_nhds_zero_iff, Tendsto, div_const, id_eq, integrableOn_exp_mul_complex_Ioi, integral_exp_mul_complex, intervalIntegral_tendsto_integral_Ioi, neg_mul_atTop, simp_rw, sub_const, tendsto_const_nhds, tendsto_const_nhds.neg_mul_atTop, tendsto_exp_nhds_zero_iff, tendsto_id, tendsto_nhds_unique, this.sub_const
-/
theorem integral_exp_mul_complex_Ioi {a : Complex} (ha : a.re < 0) (c : Real) :
    ∫ x : Real in Set.Ioi c, Complex.exp (a * x) = - Complex.exp (a * c) / a := by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) (by aesop), id_eq]
  suffices Tendsto (fun x : Real => Complex.exp (a * x)) atTop (𝓝 0) by
.div_const _ simpa using this.sub_const _
  simpa [Complex.tendsto_exp_nhds_zero_iff] using tendsto_const_nhds.neg_mul_atTop ha tendsto_id

/--
theorem `integral_exp_mul_complex_Iic` / 定理 `integral_exp_mul_complex_Iic`

English:
theorem integral_exp_mul_complex_Iic
  given: {a : Complex} (ha : 0 < a.re) (c : Real)
  proof: by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg,
    integral_comp_neg_Ioi (f := fun x : Real => Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

中文:
定理 integral_exp_mul_complex_Iic
  条件: {a : Complex} (ha : 0 < a.re) (c : 实数)
  证明: by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg,
    integral_comp_neg_Ioi (f := fun x : Real => Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

Depends on / 依赖: Complex.exp, Complex.ofReal_neg, integral_comp_neg_Ioi, integral_exp_mul_complex_Ioi, mul_neg, neg_mul, ofReal_neg
-/
theorem integral_exp_mul_complex_Iic {a : Complex} (ha : 0 < a.re) (c : Real) :
    ∫ x : Real in Set.Iic c, Complex.exp (a * x) = Complex.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg,
    integral_comp_neg_Ioi (f := fun x : Real => Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

/--
theorem `integral_exp_mul_Ioi` / 定理 `integral_exp_mul_Ioi`

English:
theorem integral_exp_mul_Ioi
  given: {a : Real} (ha : a < 0) (c : Real)
  proof: by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re]; rw [integral_exp_mul_complex_Ioi (by simpa using ha)]; rw [RCLike.re_to_complex]; rw [RCLike.re_to_complex]; rw [Complex.div_ofReal_re]; rw [Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa usin

中文:
定理 integral_exp_mul_Ioi
  条件: {a : 实数} (ha : a < 0) (c : 实数)
  证明: by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re]; rw [integral_exp_mul_complex_Ioi (by simpa using ha)]; rw [RCLike.re_to_complex]; rw [RCLike.re_to_complex]; rw [Complex.div_ofReal_re]; rw [Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa usin

Depends on / 依赖: Complex.div_ofReal_re, Complex.neg_re, Complex.ofReal_mul, RCLike, RCLike.re_to_complex, Real.exp, div_ofReal_re, integrableOn_exp_mul_complex_Ioi, integral_exp_mul_complex_Ioi, integral_re, neg_re, ofReal_mul, re_to_complex, simp_rw
-/
theorem integral_exp_mul_Ioi {a : Real} (ha : a < 0) (c : Real) :
    ∫ x : Real in Set.Ioi c, Real.exp (a * x) = - Real.exp (a * c) / a := by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re]; rw [integral_exp_mul_complex_Ioi (by simpa using ha)]; rw [RCLike.re_to_complex]; rw [RCLike.re_to_complex]; rw [Complex.div_ofReal_re]; rw [Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using ha) _

/--
theorem `integral_exp_mul_Iic` / 定理 `integral_exp_mul_Iic`

English:
theorem integral_exp_mul_Iic
  given: {a : Real} (ha : 0 < a) (c : Real)
  proof: by
  simpa [neg_mul, ← mul_neg, integral_comp_neg_Ioi (f := fun x : Real => Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

中文:
定理 integral_exp_mul_Iic
  条件: {a : 实数} (ha : 0 < a) (c : 实数)
  证明: by
  simpa [neg_mul, ← mul_neg, integral_comp_neg_Ioi (f := fun x : Real => Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

Depends on / 依赖: Real.exp, integral_comp_neg_Ioi, integral_exp_mul_Ioi, mul_neg, neg_mul
-/
theorem integral_exp_mul_Iic {a : Real} (ha : 0 < a) (c : Real) :
    ∫ x : Real in Set.Iic c, Real.exp (a * x) = Real.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, integral_comp_neg_Ioi (f := fun x : Real => Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

/--
theorem `integrableOn_add_rpow_Ioi_of_lt` / 定理 `integrableOn_add_rpow_Ioi_of_lt`

English:
theorem integrableOn_add_rpow_Ioi_of_lt
  given: {a c m : Real} (ha : a < -1) (hc : -m < c)
  proof: by
  have hd : forall x in Ici c, HasDerivAt (fun t => (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert! (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 != 0 by linarith]
    left; linarith [mem_Ici.mp hx, id_eq x]
  have ht : Te

中文:
定理 integrableOn_add_rpow_Ioi_of_lt
  条件: {a c m : 实数} (ha : a < -1) (hc : -m < c)
  证明: by
  have hd : forall x in Ici c, HasDerivAt (fun t => (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert! (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 != 0 by linarith]
    left; linarith [mem_Ici.mp hx, id_eq x]
  have ht : Te

Depends on / 依赖: HasDerivAt, Tendsto, add_const, convert, div_const, hasDerivAt_id, id_eq, mem_Ici, mem_Ici.mp, neg_neg, rpow_const, tendsto_atTop_add_const_right, tendsto_id, tendsto_rpow_neg_atTop
-/
theorem integrableOn_add_rpow_Ioi_of_lt {a c m : Real} (ha : a < -1) (hc : -m < c) :
    IntegrableOn (fun (x : Real) => (x + m) ^ a) (Ioi c) := by
  have hd : forall x in Ici c, HasDerivAt (fun t => (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert! (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 != 0 by linarith]
    left; linarith [mem_Ici.mp hx, id_eq x]
  have ht : Tendsto (fun t => ((t + m) ^ (a + 1)) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
.div_const _ (tendsto_atTop_add_const_right _ m tendsto_id)
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht => rpow_nonneg (by linarith [mem_Ioi.mp ht]) a) ht

/--
theorem `integrableOn_Ioi_rpow_of_lt` / 定理 `integrableOn_Ioi_rpow_of_lt`

English:
theorem integrableOn_Ioi_rpow_of_lt
  given: {a c : Real} (ha : a < -1) (hc : 0 < c)
  proof: by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

中文:
定理 integrableOn_Ioi_rpow_of_lt
  条件: {a c : 实数} (ha : a < -1) (hc : 0 < c)
  证明: by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

Depends on / 依赖: integrableOn_add_rpow_Ioi_of_lt
-/
theorem integrableOn_Ioi_rpow_of_lt {a c : Real} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : Real => t ^ a) (Ioi c) := by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

/--
theorem `integrableOn_Ioi_rpow_iff` / 定理 `integrableOn_Ioi_rpow_iff`

English:
theorem integrableOn_Ioi_rpow_iff
  given: {s t : Real} (ht : 0 < t)
  proof: by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x => x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x => x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurab

中文:
定理 integrableOn_Ioi_rpow_iff
  条件: {s t : 实数} (ht : 0 < t)
  证明: by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x => x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x => x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurab

Depends on / 依赖: H.mono, IntegrableOn, Ioi_subset_Ioi, Real.norm_eq_abs, Set.Ioi_subset_Ioi, abs_of_nonneg, ae_restrict_mem, aestronglyMeasurable, contrapose, filter_upwards, integrableOn_Ioi_rpow_of_lt, le_max_left, le_max_right, le_rfl, measurableSet_Ioi, measurable_inv, measurable_inv.aestronglyMeasurable, mem_Ioi, norm_eq_abs, norm_inv
-/
theorem integrableOn_Ioi_rpow_iff {s t : Real} (ht : 0 < t) :
    IntegrableOn (fun x => x ^ s) (Ioi t) ↔ s < -1 := by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x => x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x => x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have x_one : 1 <= x := ((le_max_left _ _).trans_lt (mem_Ioi.1 hx)).le
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans x_one)]
    rw [← Real.rpow_neg_one x]
    exact Real.rpow_le_rpow_of_exponent_le x_one h
  exact not_integrableOn_Ioi_inv this

/--
theorem `integrableAtFilter_rpow_atTop_iff` / 定理 `integrableAtFilter_rpow_atTop_iff`

English:
theorem integrableAtFilter_rpow_atTop_iff
  given: {s : Real}
  proof: by
  refine ⟨fun ⟨t, ht, hint⟩ => ?_, fun h =>
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
exact hint.mono_set fun x hx => ha _ (le_max_l

中文:
定理 integrableAtFilter_rpow_atTop_iff
  条件: {s : 实数}
  证明: by
  refine ⟨fun ⟨t, ht, hint⟩ => ?_, fun h =>
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
exact hint.mono_set fun x hx => ha _ (le_max_l

Depends on / 依赖: Ioi_mem_atTop, Set.Ioi, hint.mono_set, hx.le, integrableOn_Ioi_rpow_iff, le_max_left, le_max_right, mem_atTop_sets, mem_atTop_sets.mp, mono_set, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem integrableAtFilter_rpow_atTop_iff {s : Real} :
    IntegrableAtFilter (fun x : Real => x ^ s) atTop ↔ s < -1 := by
  refine ⟨fun ⟨t, ht, hint⟩ => ?_, fun h =>
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
exact hint.mono_set fun x hx => ha _ (le_max_left a 1).trans hx.le

/--
theorem `not_integrableOn_Ioi_rpow` / 定理 `not_integrableOn_Ioi_rpow`

English:
theorem not_integrableOn_Ioi_rpow
  given: (s : Real)
  statement: ¬ IntegrableOn (fun x => x ^ s) (Ioi (0 : Real))
  proof: by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x => x ^ s) (Ioi (1 : Real)) := h.mono (Ioi

中文:
定理 not_integrableOn_Ioi_rpow
  条件: (s : 实数)
  结论: ¬ 整数egrableOn (fun x => x ^ s) (Ioi (0 : 实数))
  证明: by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x => x ^ s) (Ioi (1 : Real)) := h.mono (Ioi

Depends on / 依赖: IntegrableOn, Ioi_subset_Ioi, Ioo_subset_Ioi_self, h.mono, hs.not_gt, integrableOn_Ioi_rpow_iff, integrableOn_Ioo_rpow_iff, le_or_gt, le_rfl, not_gt, zero_le_one, zero_lt_one
-/
theorem not_integrableOn_Ioi_rpow (s : Real) : ¬ IntegrableOn (fun x => x ^ s) (Ioi (0 : Real)) := by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x => x ^ s) (Ioo (0 : Real) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x => x ^ s) (Ioi (1 : Real)) := h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_rpow_iff zero_lt_one] at this
    exact hs.not_gt this

/--
theorem `setIntegral_Ioi_zero_rpow` / 定理 `setIntegral_Ioi_zero_rpow`

English:
theorem setIntegral_Ioi_zero_rpow
  given: (s : Real)
  statement: ∫ x in Ioi (0 : Real), x ^ s = 0
  proof: MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

中文:
定理 setIntegral_Ioi_zero_rpow
  条件: (s : 实数)
  结论: ∫ x in Ioi (0 : 实数), x ^ s = 0
  证明: MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_undef, integral_undef, not_integrableOn_Ioi_rpow
-/
theorem setIntegral_Ioi_zero_rpow (s : Real) : ∫ x in Ioi (0 : Real), x ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

/--
theorem `integral_Ioi_rpow_of_lt` / 定理 `integral_Ioi_rpow_of_lt`

English:
theorem integral_Ioi_rpow_of_lt
  given: {a : Real} (ha : a < -1) {c : Real} (hc : 0 < c)
  proof: by
  have hd : forall x in Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert! (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    simp [show a + 1 != 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t

中文:
定理 integral_Ioi_rpow_of_lt
  条件: {a : 实数} (ha : a < -1) {c : 实数} (hc : 0 < c)
  证明: by
  have hd : forall x in Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert! (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    simp [show a + 1 != 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t

Depends on / 依赖: HasDerivAt, Or.inl, Tendsto, Tendsto.div_const, convert, div_const, hasDerivAt_rpow_const, hc.trans_le, integral_Ioi_of_hasDerivAt_of_tendsto, mul_comm, ne_of_lt, neg_neg, tendsto_rpow_neg_atTop, trans_le
-/
theorem integral_Ioi_rpow_of_lt {a : Real} (ha : a < -1) {c : Real} (hc : 0 < c) :
    ∫ t : Real in Ioi c, t ^ a = -c ^ (a + 1) / (a + 1) := by
  have hd : forall x in Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert! (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    simp [show a + 1 != 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht using 1
  simp only [neg_div, zero_div, zero_sub]

/--
theorem `integrableOn_Ioi_norm_cpow_of_lt` / 定理 `integrableOn_Ioi_norm_cpow_of_lt`

English:
theorem integrableOn_Ioi_norm_cpow_of_lt
  given: {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c)
  proof: by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

中文:
定理 integrableOn_Ioi_norm_cpow_of_lt
  条件: {a : Complex} (ha : a.re < -1) {c : 实数} (hc : 0 < c)
  证明: by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

Depends on / 依赖: Complex.norm_cpow_eq_rpow_re_of_pos, congr_fun, hc.trans, integrableOn_Ioi_rpow_of_lt, measurableSet_Ioi, norm_cpow_eq_rpow_re_of_pos
-/
theorem integrableOn_Ioi_norm_cpow_of_lt {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c) :
    IntegrableOn (fun t : Real => ‖(t : Complex) ^ a‖) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

/--
theorem `integrableOn_Ioi_cpow_of_lt` / 定理 `integrableOn_Ioi_cpow_of_lt`

English:
theorem integrableOn_Ioi_cpow_of_lt
  given: {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c)
  proof: by
refine (integrable_norm_iff ?_).mp integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

中文:
定理 integrableOn_Ioi_cpow_of_lt
  条件: {a : Complex} (ha : a.re < -1) {c : 实数} (hc : 0 < c)
  证明: by
refine (integrable_norm_iff ?_).mp integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

Depends on / 依赖: Complex.continuousAt_ofReal_cpow_const, ContinuousOn, ContinuousOn.aestronglyMeasurable, Or.inr, aestronglyMeasurable, continuousAt_ofReal_cpow_const, continuousWithinAt, hc.trans, integrableOn_Ioi_norm_cpow_of_lt, integrable_norm_iff, measurableSet_Ioi
-/
theorem integrableOn_Ioi_cpow_of_lt {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c) :
    IntegrableOn (fun t : Real => (t : Complex) ^ a) (Ioi c) := by
refine (integrable_norm_iff ?_).mp integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

/--
theorem `integrableOn_Ioi_norm_cpow_iff` / 定理 `integrableOn_Ioi_norm_cpow_iff`

English:
theorem integrableOn_Ioi_norm_cpow_iff
  given: {s : Complex} {t : Real} (ht : 0 < t)
  proof: by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_norm_cpow_of_lt h ht⟩
refine (integrableOn_Ioi_rpow_iff ht).mp h.congr_fun (fun a ha => ?_) measurableSet_Ioi
  #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
  instantiation order leads to a term with a beta

中文:
定理 integrableOn_Ioi_norm_cpow_iff
  条件: {s : Complex} {t : 实数} (ht : 0 < t)
  证明: by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_norm_cpow_of_lt h ht⟩
refine (integrableOn_Ioi_rpow_iff ht).mp h.congr_fun (fun a ha => ?_) measurableSet_Ioi
  #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
  instantiation order leads to a term with a beta

Depends on / 依赖: Complex.norm_cpow_eq_rpow_re_of_pos, adaptation_note, because, congr_fun, different, elaboration, github, github.com, h.congr_fun, ht.trans, instantiation, integrableOn_Ioi_norm_cpow_of_lt, integrableOn_Ioi_rpow_iff, itself, leanprover, measurableSet_Ioi, norm_cpow_eq_rpow_re_of_pos, reduction, removed, slightly
-/
theorem integrableOn_Ioi_norm_cpow_iff {s : Complex} {t : Real} (ht : 0 < t) :
    IntegrableOn (fun x : Real => ‖(x : Complex) ^ s‖) (Ioi t) ↔ s.re < -1 := by
  refine ⟨fun h => ?_, fun h => integrableOn_Ioi_norm_cpow_of_lt h ht⟩
refine (integrableOn_Ioi_rpow_iff ht).mp h.congr_fun (fun a ha => ?_) measurableSet_Ioi
  #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
  instantiation order leads to a term with a beta redex.
  https://github.com/leanprover/lean4/pull/13762
  This will be removed once app elaboration itself does beta reduction. -/
  dsimp only
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht.trans ha)]

/--
theorem `integrableOn_Ioi_cpow_iff` / 定理 `integrableOn_Ioi_cpow_iff`

English:
theorem integrableOn_Ioi_cpow_iff
  given: {s : Complex} {t : Real} (ht : 0 < t)
  proof: ⟨fun h => (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h => integrableOn_Ioi_cpow_of_lt h ht⟩

中文:
定理 integrableOn_Ioi_cpow_iff
  条件: {s : Complex} {t : 实数} (ht : 0 < t)
  证明: ⟨fun h => (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h => integrableOn_Ioi_cpow_of_lt h ht⟩

Depends on / 依赖: h.norm, integrableOn_Ioi_cpow_of_lt, integrableOn_Ioi_norm_cpow_iff
-/
theorem integrableOn_Ioi_cpow_iff {s : Complex} {t : Real} (ht : 0 < t) :
    IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioi t) ↔ s.re < -1 :=
  ⟨fun h => (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h => integrableOn_Ioi_cpow_of_lt h ht⟩

/--
theorem `integrableOn_Ioi_deriv_ofReal_cpow` / 定理 `integrableOn_Ioi_deriv_ofReal_cpow`

English:
theorem integrableOn_Ioi_deriv_ofReal_cpow
  given: {s : Complex} {t : Real} (ht : 0 < t) (hs : s.re < 0)
  proof: by
  have h : IntegrableOn (fun x : Real => s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpo

中文:
定理 integrableOn_Ioi_deriv_ofReal_cpow
  条件: {s : Complex} {t : 实数} (ht : 0 < t) (hs : s.re < 0)
  证明: by
  have h : IntegrableOn (fun x : Real => s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpo

Depends on / 依赖: Complex.deriv_ofReal_cpow_const, Complex.one_re, Complex.sub_re, Complex.zero_re, IntegrableOn, Set.Ioi, congr_fun, const_mul, deriv_ofReal_cpow_const, h.congr_fun, ht.trans, integrableOn_Ioi_cpow_of_lt, measurableSet_Ioi, neg_add_cancel, one_re, sub_lt_iff_lt_add, sub_re, zero_re
-/
theorem integrableOn_Ioi_deriv_ofReal_cpow {s : Complex} {t : Real} (ht : 0 < t) (hs : s.re < 0) :
    IntegrableOn (deriv fun x : Real => (x : Complex) ^ s) (Set.Ioi t) := by
  have h : IntegrableOn (fun x : Real => s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpow_const (ht.trans hx).ne' (fun h => (Complex.zero_re ▸ h ▸ hs).false)]

/--
theorem `integrableOn_Ioi_deriv_norm_ofReal_cpow` / 定理 `integrableOn_Ioi_deriv_norm_ofReal_cpow`

English:
theorem integrableOn_Ioi_deriv_norm_ofReal_cpow
  given: {s : Complex} {t : Real} (ht : 0 < t) (hs : s.re <= 0)
  proof: by
  rw [integrableOn_congr_fun (fun x hx => by
    rw [deriv_norm_ofReal_cpow _ (ht.trans hx)]) measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (int

中文:
定理 integrableOn_Ioi_deriv_norm_ofReal_cpow
  条件: {s : Complex} {t : 实数} (ht : 0 < t) (hs : s.re <= 0)
  证明: by
  rw [integrableOn_congr_fun (fun x hx => by
    rw [deriv_norm_ofReal_cpow _ (ht.trans hx)]) measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (int

Depends on / 依赖: const_mul, deriv_norm_ofReal_cpow, eq_or_lt_of_le, ht.trans, integrableOn_Ioi_rpow_of_lt, integrableOn_congr_fun, integrableOn_zero, measurableSet_Ioi, neg_add_cancel, replace, s.re, simp_rw, sub_lt_iff_lt_add, zero_mul
-/
theorem integrableOn_Ioi_deriv_norm_ofReal_cpow {s : Complex} {t : Real} (ht : 0 < t) (hs : s.re <= 0) :
    IntegrableOn (deriv fun x : Real => ‖(x : Complex) ^ s‖) (Set.Ioi t) := by
  rw [integrableOn_congr_fun (fun x hx => by
    rw [deriv_norm_ofReal_cpow _ (ht.trans hx)]) measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (integrableOn_Ioi_rpow_of_lt hs ht).const_mul s.re

/--
theorem `not_integrableOn_Ioi_cpow` / 定理 `not_integrableOn_Ioi_cpow`

English:
theorem not_integrableOn_Ioi_cpow
  given: (s : Complex)
  proof: by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioo (0 : Real) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : Real => (x 

中文:
定理 not_integrableOn_Ioi_cpow
  条件: (s : Complex)
  证明: by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioo (0 : Real) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : Real => (x 

Depends on / 依赖: IntegrableOn, Ioi_subset_Ioi, Ioo_subset_Ioi_self, h.mono, hs.not_gt, integrableOn_Ioi_cpow_iff, integrableOn_Ioo_cpow_iff, le_or_gt, le_rfl, not_gt, s.re, zero_le_one, zero_lt_one
-/
theorem not_integrableOn_Ioi_cpow (s : Complex) :
    ¬ IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioi (0 : Real)) := by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioo (0 : Real) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : Real => (x : Complex) ^ s) (Ioi 1) :=
      h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_cpow_iff zero_lt_one] at this
    exact hs.not_gt this

/--
theorem `setIntegral_Ioi_zero_cpow` / 定理 `setIntegral_Ioi_zero_cpow`

English:
theorem setIntegral_Ioi_zero_cpow
  given: (s : Complex)
  statement: ∫ x in Ioi (0 : Real), (x : Complex) ^ s = 0
  proof: MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

中文:
定理 setIntegral_Ioi_zero_cpow
  条件: (s : Complex)
  结论: ∫ x in Ioi (0 : 实数), (x : Complex) ^ s = 0
  证明: MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_undef, integral_undef, not_integrableOn_Ioi_cpow
-/
theorem setIntegral_Ioi_zero_cpow (s : Complex) : ∫ x in Ioi (0 : Real), (x : Complex) ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

/--
theorem `integral_Ioi_cpow_of_lt` / 定理 `integral_Ioi_cpow_of_lt`

English:
theorem integral_Ioi_cpow_of_lt
  given: {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c)
  proof: by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : Real => ((x : Complex) ^ (a + 1) - (c : Complex) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.co

中文:
定理 integral_Ioi_cpow_of_lt
  条件: {a : Complex} (ha : a.re < -1) {c : 实数} (hc : 0 < c)
  证明: by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : Real => ((x : Complex) ^ (a + 1) - (c : Complex) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.co

Depends on / 依赖: Complex.neg_re, Complex.one_re, Complex.re, Eventually, Eventually.of_forall, Or.inr, Tendsto, apply_fun, eventually_gt_atTop, ha.ne, integrableOn_Ioi_cpow_of_lt, integral_cpow, intervalIntegral_tendsto_integral_Ioi, neg_re, notMem_uIcc_of_lt, of_forall, one_re, tendsto_id, tendsto_nhds_unique, this.congr
-/
theorem integral_Ioi_cpow_of_lt {a : Complex} (ha : a.re < -1) {c : Real} (hc : 0 < c) :
    (∫ t : Real in Ioi c, (t : Complex) ^ a) = -(c : Complex) ^ (a + 1) / (a + 1) := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : Real => ((x : Complex) ^ (a + 1) - (c : Complex) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.congr' ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
    dsimp only
    rw [integral_cpow]; rw [id]
    refine Or.inr ⟨?_, notMem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re]; rw [Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine (Tendsto.div_const ?_ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
  simp_rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

/--
theorem `integrable_inv_one_add_sq` / 定理 `integrable_inv_one_add_sq`

English:
theorem integrable_inv_one_add_sq
  statement: Integrable fun (x : Real) => (1 + x ^ 2)⁻¹
  proof: by
  suffices Integrable fun (x : Real) => (1 + ‖x‖ ^ 2) ^ ((-2 : Real) / 2) by simpa [rpow_neg_one]
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]

中文:
定理 integrable_inv_one_add_sq
  结论: 整数egrable fun (x : 实数) => (1 + x ^ 2)⁻¹
  证明: by
  suffices Integrable fun (x : Real) => (1 + ‖x‖ ^ 2) ^ ((-2 : Real) / 2) by simpa [rpow_neg_one]
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]

Depends on / 依赖: Integrable, integrable_rpow_neg_one_add_norm_sq, rpow_neg_one
-/
theorem integrable_inv_one_add_sq : Integrable fun (x : Real) => (1 + x ^ 2)⁻¹ := by
  suffices Integrable fun (x : Real) => (1 + ‖x‖ ^ 2) ^ ((-2 : Real) / 2) by simpa [rpow_neg_one]
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]
/--
theorem `integral_Iic_inv_one_add_sq` / 定理 `integral_Iic_inv_one_add_sq`

English:
theorem integral_Iic_inv_one_add_sq
  given: {i : Real}
  proof: integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
.trans (sub_neg_eq_add _ _)

@[simp]

中文:
定理 integral_Iic_inv_one_add_sq
  条件: {i : 实数}
  证明: integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
.trans (sub_neg_eq_add _ _)

@[simp]

Depends on / 依赖: hasDerivAt_arctan, integrableOn, integrable_inv_one_add_sq, integrable_inv_one_add_sq.integrableOn, integral_Iic_of_hasDerivAt_of_tendsto, sub_neg_eq_add, tendsto_arctan_atBot, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem integral_Iic_inv_one_add_sq {i : Real} :
    ∫ (x : Real) in Set.Iic i, (1 + x ^ 2)⁻¹ = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
.trans (sub_neg_eq_add _ _)

@[simp]
/--
theorem `integral_Ioi_inv_one_add_sq` / 定理 `integral_Ioi_inv_one_add_sq`

English:
theorem integral_Ioi_inv_one_add_sq
  given: {i : Real}
  proof: integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]

中文:
定理 integral_Ioi_inv_one_add_sq
  条件: {i : 实数}
  证明: integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]

Depends on / 依赖: hasDerivAt_arctan, integrableOn, integrable_inv_one_add_sq, integrable_inv_one_add_sq.integrableOn, integral_Ioi_of_hasDerivAt_of_tendsto, tendsto_arctan_atTop, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem integral_Ioi_inv_one_add_sq {i : Real} :
    ∫ (x : Real) in Set.Ioi i, (1 + x ^ 2)⁻¹ = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]
/--
theorem `integral_univ_inv_one_add_sq` / 定理 `integral_univ_inv_one_add_sq`

English:
theorem integral_univ_inv_one_add_sq
  statement: ∫ (x : Real), (1 + x ^ 2)⁻¹ = π
  proof: (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]

中文:
定理 integral_univ_inv_one_add_sq
  结论: ∫ (x : 实数), (1 + x ^ 2)⁻¹ = π
  证明: (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]

Depends on / 依赖: hasDerivAt_arctan, integrable_inv_one_add_sq, integral_of_hasDerivAt_of_tendsto, tendsto_arctan_atBot, tendsto_arctan_atTop, tendsto_nhds_of_tendsto_nhdsWithin
-/
theorem integral_univ_inv_one_add_sq : ∫ (x : Real), (1 + x ^ 2)⁻¹ = π :=
  (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]
/--
theorem `integrableOn_inv_div_log_sq_Ioi` / 定理 `integrableOn_inv_div_log_sq_Ioi`

English:
theorem integrableOn_inv_div_log_sq_Ioi
  given: {c : Real} (hc : 1 < c)
  proof: by
  apply integrableOn_Ioi_deriv_of_nonneg' _ _ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  · intro t _
    have : 0 < t := by grind
    positivity

@[simp]

中文:
定理 integrableOn_inv_div_log_sq_Ioi
  条件: {c : 实数} (hc : 1 < c)
  证明: by
  apply integrableOn_Ioi_deriv_of_nonneg' _ _ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  · intro t _
    have : 0 < t := by grind
    positivity

@[simp]

Depends on / 依赖: convert, hasDerivAt_inv_log, integrableOn_Ioi_deriv_of_nonneg, inv_tendsto_atTop, tendsto_log_atTop, tendsto_log_atTop.inv_tendsto_atTop.neg
-/
theorem integrableOn_inv_div_log_sq_Ioi {c : Real} (hc : 1 < c) :
    IntegrableOn (fun t => t⁻¹ / (log t) ^ 2) (.Ioi c) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' _ _ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  · intro t _
    have : 0 < t := by grind
    positivity

@[simp]
/--
theorem `integral_inv_div_log_sq_Ioi` / 定理 `integral_inv_div_log_sq_Ioi`

English:
theorem integral_inv_div_log_sq_Ioi
  given: {c : Real} (hc : 1 < c)
  proof: by
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun t => -(log t)⁻¹) ?_
    (integrableOn_inv_div_log_sq_Ioi hc) ?_ using 1
  · simp
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  convert! tendsto_log_atTop.inv_te

中文:
定理 integral_inv_div_log_sq_Ioi
  条件: {c : 实数} (hc : 1 < c)
  证明: by
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun t => -(log t)⁻¹) ?_
    (integrableOn_inv_div_log_sq_Ioi hc) ?_ using 1
  · simp
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  convert! tendsto_log_atTop.inv_te

Depends on / 依赖: convert, hasDerivAt_inv_log, integrableOn_inv_div_log_sq_Ioi, integral_Ioi_of_hasDerivAt_of_tendsto, inv_tendsto_atTop, tendsto_log_atTop, tendsto_log_atTop.inv_tendsto_atTop.neg
-/
theorem integral_inv_div_log_sq_Ioi {c : Real} (hc : 1 < c) :
    ∫ (t : Real) in .Ioi c, t⁻¹ / (log t) ^ 2 = (log c)⁻¹ := by
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun t => -(log t)⁻¹) ?_
    (integrableOn_inv_div_log_sq_Ioi hc) ?_ using 1
  · simp
  · intro t _
    convert! (hasDerivAt_inv_log (by grind : t != 0) (by grind) (by grind)).neg using 1
    field
  convert! tendsto_log_atTop.inv_tendsto_atTop.neg using 1
  simp
