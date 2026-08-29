/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPDF`: `ℝ≥0∞`-valued pdf, `gaussianPDF μ v x = ENNReal.ofReal (gaussianPDFReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c ^ 2 * v`.

-/

@[expose] public section

open scoped ENNReal NNReal Real Complex

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

/-- Probability density function of the Gaussian distribution with mean `μ` and variance `v`. -/
noncomputable
/--
Definition of `gaussianPDFReal` / `gaussianPDFReal` 的定义

English:
definition gaussianPDFReal
  signature: (μ : Real) (v : Real>=0) (x : Real)
  body: (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))

中文:
定义 gaussianPDF实数
  签名: (μ : 实数) (v : 实数>=0) (x : 实数)
  定义体: (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))
-/
def gaussianPDFReal (μ : Real) (v : Real>=0) (x : Real) : Real :=
  (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))

/--
lemma `gaussianPDFReal_def` / 引理 `gaussianPDFReal_def`

English:
lemma gaussianPDFReal_def
  given: (μ : Real) (v : Real>=0)
  proof: rfl

@[simp]

中文:
引理 gaussianPDF实数_def
  条件: (μ : 实数) (v : 实数>=0)
  证明: rfl

@[simp]
-/
lemma gaussianPDFReal_def (μ : Real) (v : Real>=0) :
    gaussianPDFReal μ v =
      fun x => (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v)) := rfl

@[simp]
/--
lemma `gaussianPDFReal_zero_var` / 引理 `gaussianPDFReal_zero_var`

English:
lemma gaussianPDFReal_zero_var
  given: (m : Real)
  statement: gaussianPDFReal m 0 = 0
  proof: by
  ext1 x
  simp [gaussianPDFReal]

中文:
引理 gaussianPDF实数_zero_var
  条件: (m : 实数)
  结论: gaussianPDF实数 m 0 = 0
  证明: by
  ext1 x
  simp [gaussianPDFReal]

Depends on / 依赖: gaussianPDFReal
-/
lemma gaussianPDFReal_zero_var (m : Real) : gaussianPDFReal m 0 = 0 := by
  ext1 x
  simp [gaussianPDFReal]

/--
lemma `gaussianPDFReal_pos` / 引理 `gaussianPDFReal_pos`

English:
lemma gaussianPDFReal_pos
  given: (μ : Real) (v : Real>=0) (x : Real) (hv : v != 0)
  statement: 0 < gaussianPDFReal μ v x
  proof: by
  rw [gaussianPDFReal]
  positivity

中文:
引理 gaussianPDF实数_pos
  条件: (μ : 实数) (v : 实数>=0) (x : 实数) (hv : v != 0)
  结论: 0 < gaussianPDF实数 μ v x
  证明: by
  rw [gaussianPDFReal]
  positivity

Depends on / 依赖: gaussianPDFReal
-/
lemma gaussianPDFReal_pos (μ : Real) (v : Real>=0) (x : Real) (hv : v != 0) : 0 < gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/--
lemma `gaussianPDFReal_nonneg` / 引理 `gaussianPDFReal_nonneg`

English:
lemma gaussianPDFReal_nonneg
  given: (μ : Real) (v : Real>=0) (x : Real)
  statement: 0 <= gaussianPDFReal μ v x
  proof: by
  rw [gaussianPDFReal]
  positivity

中文:
引理 gaussianPDF实数_nonneg
  条件: (μ : 实数) (v : 实数>=0) (x : 实数)
  结论: 0 <= gaussianPDF实数 μ v x
  证明: by
  rw [gaussianPDFReal]
  positivity

Depends on / 依赖: gaussianPDFReal
-/
lemma gaussianPDFReal_nonneg (μ : Real) (v : Real>=0) (x : Real) : 0 <= gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is measurable. -/
@[fun_prop]
/--
lemma `measurable_uncurry_gaussianPDFReal` / 引理 `measurable_uncurry_gaussianPDFReal`

English:
lemma measurable_uncurry_gaussianPDFReal
  statement: Measurable (fun (μ, v, x) => gaussianPDFReal μ v x)
  proof: by
  unfold gaussianPDFReal
  fun_prop

中文:
引理 measurable_uncurry_gaussianPDF实数
  结论: 可测 (fun (μ, v, x) => gaussianPDF实数 μ v x)
  证明: by
  unfold gaussianPDFReal
  fun_prop

Depends on / 依赖: fun_prop, gaussianPDFReal
-/
lemma measurable_uncurry_gaussianPDFReal : Measurable (fun (μ, v, x) => gaussianPDFReal μ v x) := by
  unfold gaussianPDFReal
  fun_prop

/--
lemma `measurable_gaussianPDFReal` / 引理 `measurable_gaussianPDFReal`

English:
lemma measurable_gaussianPDFReal
  given: (μ : Real) (v : Real>=0)
  statement: Measurable (gaussianPDFReal μ v)
  proof: by
  fun_prop

中文:
引理 measurable_gaussianPDF实数
  条件: (μ : 实数) (v : 实数>=0)
  结论: 可测 (gaussianPDF实数 μ v)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
lemma measurable_gaussianPDFReal (μ : Real) (v : Real>=0) : Measurable (gaussianPDFReal μ v) := by
  fun_prop

/-- The Gaussian pdf is strongly measurable. -/
@[fun_prop]
/--
lemma `stronglyMeasurable_uncurry_gaussianPDFReal` / 引理 `stronglyMeasurable_uncurry_gaussianPDFReal`

English:
lemma stronglyMeasurable_uncurry_gaussianPDFReal
  proof: measurable_uncurry_gaussianPDFReal.stronglyMeasurable

中文:
引理 stronglyMeasurable_uncurry_gaussianPDF实数
  证明: measurable_uncurry_gaussianPDFReal.stronglyMeasurable

Depends on / 依赖: measurable_uncurry_gaussianPDFReal, measurable_uncurry_gaussianPDFReal.stronglyMeasurable, stronglyMeasurable
-/
lemma stronglyMeasurable_uncurry_gaussianPDFReal :
    StronglyMeasurable (fun (μ, v, x) => gaussianPDFReal μ v x) :=
  measurable_uncurry_gaussianPDFReal.stronglyMeasurable

/--
lemma `stronglyMeasurable_gaussianPDFReal` / 引理 `stronglyMeasurable_gaussianPDFReal`

English:
lemma stronglyMeasurable_gaussianPDFReal
  given: (μ : Real) (v : Real>=0)
  proof: by
  fun_prop

@[fun_prop]

中文:
引理 stronglyMeasurable_gaussianPDF实数
  条件: (μ : 实数) (v : 实数>=0)
  证明: by
  fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
lemma stronglyMeasurable_gaussianPDFReal (μ : Real) (v : Real>=0) :
    StronglyMeasurable (gaussianPDFReal μ v) := by
  fun_prop

@[fun_prop]
/--
lemma `integrable_gaussianPDFReal` / 引理 `integrable_gaussianPDFReal`

English:
lemma integrable_gaussianPDFReal
  given: (μ : Real) (v : Real>=0)
  proof: by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : Real -> Real := fun x => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x => (√(2 * π * v))⁻¹ * rexp (-(2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simpa [pos_iff_ne_zero]
    ext x
    simp only [g, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field
  exact Integrable.comp_sub_right hg μ

中文:
引理 integrable_gaussianPDF实数
  条件: (μ : 实数) (v : 实数>=0)
  证明: by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : Real -> Real := fun x => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x => (√(2 * π * v))⁻¹ * rexp (-(2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simpa [pos_iff_ne_zero]
    ext x
    simp only [g, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field
  exact Integrable.comp_sub_right hg μ

Depends on / 依赖: Integrable, NNReal, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.zero_le_coe, Real.exp_eq_exp, Real.sqrt_mul, coe_inv, coe_mul, coe_ofNat, const_mul, exp_eq_exp, gaussianPDFReal_def, integrable_exp_neg_mul_sq, mul_eq_mul_left_iff, mul_inv_rev, neg_mul, pos_iff_ne_zero, sqrt_mul
-/
lemma integrable_gaussianPDFReal (μ : Real) (v : Real>=0) :
    Integrable (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : Real -> Real := fun x => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x => (√(2 * π * v))⁻¹ * rexp (-(2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simpa [pos_iff_ne_zero]
    ext x
    simp only [g, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field
  exact Integrable.comp_sub_right hg μ

/--
lemma `lintegral_gaussianPDFReal_eq_one` / 引理 `lintegral_gaussianPDFReal_eq_one`

English:
lemma lintegral_gaussianPDFReal_eq_one
  given: (μ : Real) {v : Real>=0} (h : v != 0)
  proof: by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume := by fun_prop
  have hf : 0 <=ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a => rexp (-a ^ 2 / ((2 : Real) * v))) μ]
  simp only [div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul]; rw [integral_gaussian]; rw [← Real.sqrt_inv]; rw [← Real.sqrt_mul]
  · simp [field]
  · positivity

中文:
引理 lintegral_gaussianPDF实数_eq_one
  条件: (μ : 实数) {v : 实数>=0} (h : v != 0)
  证明: by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume := by fun_prop
  have hf : 0 <=ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a => rexp (-a ^ 2 / ((2 : Real) * v))) μ]
  simp only [div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul]; rw [integral_gaussian]; rw [← Real.sqrt_inv]; rw [← Real.sqrt_mul]
  · simp [field]
  · positivity

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.toReal_eq_one_iff, ae_of_all, div_eq_inv_mul, fun_prop, gaussianPDFReal, gaussianPDFReal_nonneg, integral_const_mul, integral_eq_lintegral_of_nonneg_ae, integral_gaussian, integral_sub_right_eq_self, mul_inv_rev, mul_neg, neg_mul, simp_rw, toReal_eq_one_iff, volume
-/
lemma lintegral_gaussianPDFReal_eq_one (μ : Real) {v : Real>=0} (h : v != 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume := by fun_prop
  have hf : 0 <=ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a => rexp (-a ^ 2 / ((2 : Real) * v))) μ]
  simp only [div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul]; rw [integral_gaussian]; rw [← Real.sqrt_inv]; rw [← Real.sqrt_mul]
  · simp [field]
  · positivity

/--
lemma `integral_gaussianPDFReal_eq_one` / 引理 `integral_gaussianPDFReal_eq_one`

English:
lemma integral_gaussianPDFReal_eq_one
  given: (μ : Real) {v : Real>=0} (hv : v != 0)
  proof: by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _))]; rw [← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ _)) zero_le_one]

中文:
引理 integral_gaussianPDF实数_eq_one
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0)
  证明: by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _))]; rw [← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ _)) zero_le_one]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_ofReal_iff, ENNReal.ofReal_one, ae_of_all, gaussianPDFReal_nonneg, integrable_gaussianPDFReal, integral_nonneg, lintegral_gaussianPDFReal_eq_one, ofReal_eq_ofReal_iff, ofReal_integral_eq_lintegral_ofReal, ofReal_one, zero_le_one
-/
lemma integral_gaussianPDFReal_eq_one (μ : Real) {v : Real>=0} (hv : v != 0) :
    ∫ x, gaussianPDFReal μ v x = 1 := by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _))]; rw [← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ _)) zero_le_one]

/--
lemma `gaussianPDFReal_sub` / 引理 `gaussianPDFReal_sub`

English:
lemma gaussianPDFReal_sub
  given: {μ : Real} {v : Real>=0} (x y : Real)
  proof: by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

中文:
引理 gaussianPDF实数_sub
  条件: {μ : 实数} {v : 实数>=0} (x y : 实数)
  证明: by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

Depends on / 依赖: gaussianPDFReal, sub_add_eq_sub_sub_swap
-/
lemma gaussianPDFReal_sub {μ : Real} {v : Real>=0} (x y : Real) :
    gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y) v x := by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

/--
lemma `gaussianPDFReal_add` / 引理 `gaussianPDFReal_add`

English:
lemma gaussianPDFReal_add
  given: {μ : Real} {v : Real>=0} (x y : Real)
  proof: by
  rw [sub_eq_add_neg]; rw [← gaussianPDFReal_sub]; rw [sub_eq_add_neg]; rw [neg_neg]

中文:
引理 gaussianPDF实数_add
  条件: {μ : 实数} {v : 实数>=0} (x y : 实数)
  证明: by
  rw [sub_eq_add_neg]; rw [← gaussianPDFReal_sub]; rw [sub_eq_add_neg]; rw [neg_neg]

Depends on / 依赖: gaussianPDFReal_sub, neg_neg, sub_eq_add_neg
-/
lemma gaussianPDFReal_add {μ : Real} {v : Real>=0} (x y : Real) :
    gaussianPDFReal μ v (x + y) = gaussianPDFReal (μ - y) v x := by
  rw [sub_eq_add_neg]; rw [← gaussianPDFReal_sub]; rw [sub_eq_add_neg]; rw [neg_neg]

/--
lemma `gaussianPDFReal_inv_mul` / 引理 `gaussianPDFReal_inv_mul`

English:
lemma gaussianPDFReal_inv_mul
  given: {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) (x : Real)
  proof: by
  simp only [gaussianPDFReal.eq_1, NNReal.zero_le_coe,
    Real.sqrt_mul', mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · simp (disch := positivity) only [Real.sqrt_mul, mul_inv_rev, field]
    rw [Real.sqrt_sq_eq_abs]
  · congr 1
    field

中文:
引理 gaussianPDF实数_inv_mul
  条件: {μ : 实数} {v : 实数>=0} {c : 实数} (hc : c != 0) (x : 实数)
  证明: by
  simp only [gaussianPDFReal.eq_1, NNReal.zero_le_coe,
    Real.sqrt_mul', mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · simp (disch := positivity) only [Real.sqrt_mul, mul_inv_rev, field]
    rw [Real.sqrt_sq_eq_abs]
  · congr 1
    field

Depends on / 依赖: NNReal, NNReal.coe_mk, NNReal.coe_mul, NNReal.zero_le_coe, Real.sqrt_mul, Real.sqrt_sq_eq_abs, coe_mk, coe_mul, eq_1, gaussianPDFReal, gaussianPDFReal.eq_1, mul_assoc, mul_inv_rev, sqrt_mul, sqrt_sq_eq_abs, zero_le_coe
-/
lemma gaussianPDFReal_inv_mul {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) (x : Real) :
    gaussianPDFReal μ v (c⁻¹ * x)
      = |c| * gaussianPDFReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) x := by
  simp only [gaussianPDFReal.eq_1, NNReal.zero_le_coe,
    Real.sqrt_mul', mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · simp (disch := positivity) only [Real.sqrt_mul, mul_inv_rev, field]
    rw [Real.sqrt_sq_eq_abs]
  · congr 1
    field

/--
lemma `gaussianPDFReal_mul` / 引理 `gaussianPDFReal_mul`

English:
lemma gaussianPDFReal_mul
  given: {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) (x : Real)
  proof: by
  conv_lhs => rw [← inv_inv c, gaussianPDFReal_inv_mul (inv_ne_zero hc)]
  simp

中文:
引理 gaussianPDF实数_mul
  条件: {μ : 实数} {v : 实数>=0} {c : 实数} (hc : c != 0) (x : 实数)
  证明: by
  conv_lhs => rw [← inv_inv c, gaussianPDFReal_inv_mul (inv_ne_zero hc)]
  simp

Depends on / 依赖: conv_lhs, gaussianPDFReal_inv_mul, inv_inv, inv_ne_zero
-/
lemma gaussianPDFReal_mul {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) (x : Real) :
    gaussianPDFReal μ v (c * x)
      = |c⁻¹| * gaussianPDFReal (c⁻¹ * μ) (.mk (c ^ 2)⁻¹ (inv_nonneg.mpr (sq_nonneg _)) * v) x := by
  conv_lhs => rw [← inv_inv c, gaussianPDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The pdf of a Gaussian distribution on ℝ with mean `μ` and variance `v`. -/
noncomputable
/--
Definition of `gaussianPDF` / `gaussianPDF` 的定义

English:
definition gaussianPDF
  signature: (μ : Real) (v : Real>=0) (x : Real)
  body: ENNReal.ofReal (gaussianPDFReal μ v x)

中文:
定义 gaussianPDF
  签名: (μ : 实数) (v : 实数>=0) (x : 实数)
  定义体: ENNReal.ofReal (gaussianPDFReal μ v x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, gaussianPDFReal, ofReal
-/
def gaussianPDF (μ : Real) (v : Real>=0) (x : Real) : Real>=0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)

/--
lemma `gaussianPDF_def` / 引理 `gaussianPDF_def`

English:
lemma gaussianPDF_def
  given: (μ : Real) (v : Real>=0)
  proof: rfl

@[simp]

中文:
引理 gaussianPDF_def
  条件: (μ : 实数) (v : 实数>=0)
  证明: rfl

@[simp]
-/
lemma gaussianPDF_def (μ : Real) (v : Real>=0) :
    gaussianPDF μ v = fun x => ENNReal.ofReal (gaussianPDFReal μ v x) := rfl

@[simp]
/--
lemma `gaussianPDF_zero_var` / 引理 `gaussianPDF_zero_var`

English:
lemma gaussianPDF_zero_var
  given: (μ : Real)
  statement: gaussianPDF μ 0 = 0
  proof: by ext; simp [gaussianPDF]

@[simp]

中文:
引理 gaussianPDF_zero_var
  条件: (μ : 实数)
  结论: gaussianPDF μ 0 = 0
  证明: by ext; simp [gaussianPDF]

@[simp]

Depends on / 依赖: gaussianPDF
-/
lemma gaussianPDF_zero_var (μ : Real) : gaussianPDF μ 0 = 0 := by ext; simp [gaussianPDF]

@[simp]
/--
lemma `toReal_gaussianPDF` / 引理 `toReal_gaussianPDF`

English:
lemma toReal_gaussianPDF
  given: {μ : Real} {v : Real>=0} (x : Real)
  proof: by
  rw [gaussianPDF]; rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ v x)]

中文:
引理 to实数_gaussianPDF
  条件: {μ : 实数} {v : 实数>=0} (x : 实数)
  证明: by
  rw [gaussianPDF]; rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ v x)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, gaussianPDF, gaussianPDFReal_nonneg, toReal_ofReal
-/
lemma toReal_gaussianPDF {μ : Real} {v : Real>=0} (x : Real) :
    (gaussianPDF μ v x).toReal = gaussianPDFReal μ v x := by
  rw [gaussianPDF]; rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ v x)]

/--
lemma `gaussianPDF_pos` / 引理 `gaussianPDF_pos`

English:
lemma gaussianPDF_pos
  given: (μ : Real) {v : Real>=0} (hv : v != 0) (x : Real)
  statement: 0 < gaussianPDF μ v x
  proof: by
  rw [gaussianPDF]; rw [ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv

中文:
引理 gaussianPDF_pos
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0) (x : 实数)
  结论: 0 < gaussianPDF μ v x
  证明: by
  rw [gaussianPDF]; rw [ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv

Depends on / 依赖: ENNReal, ENNReal.ofReal_pos, gaussianPDF, gaussianPDFReal_pos, ofReal_pos
-/
lemma gaussianPDF_pos (μ : Real) {v : Real>=0} (hv : v != 0) (x : Real) : 0 < gaussianPDF μ v x := by
  rw [gaussianPDF]; rw [ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv

/--
lemma `gaussianPDF_lt_top` / 引理 `gaussianPDF_lt_top`

English:
lemma gaussianPDF_lt_top
  given: {μ : Real} {v : Real>=0} {x : Real}
  statement: gaussianPDF μ v x < ∞
  proof: by simp [gaussianPDF]

中文:
引理 gaussianPDF_lt_top
  条件: {μ : 实数} {v : 实数>=0} {x : 实数}
  结论: gaussianPDF μ v x < ∞
  证明: by simp [gaussianPDF]

Depends on / 依赖: gaussianPDF
-/
lemma gaussianPDF_lt_top {μ : Real} {v : Real>=0} {x : Real} : gaussianPDF μ v x < ∞ := by simp [gaussianPDF]

/--
lemma `gaussianPDF_ne_top` / 引理 `gaussianPDF_ne_top`

English:
lemma gaussianPDF_ne_top
  given: {μ : Real} {v : Real>=0} {x : Real}
  statement: gaussianPDF μ v x != ∞
  proof: by simp [gaussianPDF]

@[simp]

中文:
引理 gaussianPDF_ne_top
  条件: {μ : 实数} {v : 实数>=0} {x : 实数}
  结论: gaussianPDF μ v x != ∞
  证明: by simp [gaussianPDF]

@[simp]

Depends on / 依赖: gaussianPDF
-/
lemma gaussianPDF_ne_top {μ : Real} {v : Real>=0} {x : Real} : gaussianPDF μ v x != ∞ := by simp [gaussianPDF]

@[simp]
/--
lemma `support_gaussianPDF` / 引理 `support_gaussianPDF`

English:
lemma support_gaussianPDF
  given: {μ : Real} {v : Real>=0} (hv : v != 0)
  proof: by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

@[fun_prop]

中文:
引理 support_gaussianPDF
  条件: {μ : 实数} {v : 实数>=0} (hv : v != 0)
  证明: by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

@[fun_prop]

Depends on / 依赖: Set.mem_univ, gaussianPDF_pos, iff_true, mem_univ
-/
lemma support_gaussianPDF {μ : Real} {v : Real>=0} (hv : v != 0) :
    Function.support (gaussianPDF μ v) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

@[fun_prop]
/--
lemma `measurable_uncurry_gaussianPDF` / 引理 `measurable_uncurry_gaussianPDF`

English:
lemma measurable_uncurry_gaussianPDF
  statement: Measurable (fun (μ, v, x) => gaussianPDF μ v x)
  proof: Measurable.ennreal_ofReal (by fun_prop)

中文:
引理 measurable_uncurry_gaussianPDF
  结论: 可测 (fun (μ, v, x) => gaussianPDF μ v x)
  证明: Measurable.ennreal_ofReal (by fun_prop)

Depends on / 依赖: Measurable, Measurable.ennreal_ofReal, ennreal_ofReal, fun_prop
-/
lemma measurable_uncurry_gaussianPDF : Measurable (fun (μ, v, x) => gaussianPDF μ v x) :=
  Measurable.ennreal_ofReal (by fun_prop)

/--
lemma `measurable_gaussianPDF` / 引理 `measurable_gaussianPDF`

English:
lemma measurable_gaussianPDF
  given: (μ : Real) (v : Real>=0)
  statement: Measurable (gaussianPDF μ v)
  proof: by
  fun_prop

@[fun_prop]

中文:
引理 measurable_gaussianPDF
  条件: (μ : 实数) (v : 实数>=0)
  结论: 可测 (gaussianPDF μ v)
  证明: by
  fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
lemma measurable_gaussianPDF (μ : Real) (v : Real>=0) : Measurable (gaussianPDF μ v) := by
  fun_prop

@[fun_prop]
/--
lemma `stronglyMeasurable_uncurry_gaussianPDF` / 引理 `stronglyMeasurable_uncurry_gaussianPDF`

English:
lemma stronglyMeasurable_uncurry_gaussianPDF
  proof: measurable_uncurry_gaussianPDF.stronglyMeasurable

中文:
引理 stronglyMeasurable_uncurry_gaussianPDF
  证明: measurable_uncurry_gaussianPDF.stronglyMeasurable

Depends on / 依赖: measurable_uncurry_gaussianPDF, measurable_uncurry_gaussianPDF.stronglyMeasurable, stronglyMeasurable
-/
lemma stronglyMeasurable_uncurry_gaussianPDF :
    StronglyMeasurable (fun (μ, v, x) => gaussianPDF μ v x) :=
  measurable_uncurry_gaussianPDF.stronglyMeasurable

/--
lemma `stronglyMeasurable_gaussianPDF` / 引理 `stronglyMeasurable_gaussianPDF`

English:
lemma stronglyMeasurable_gaussianPDF
  given: (μ : Real) (v : Real>=0)
  proof: by
  fun_prop

@[simp]

中文:
引理 stronglyMeasurable_gaussianPDF
  条件: (μ : 实数) (v : 实数>=0)
  证明: by
  fun_prop

@[simp]

Depends on / 依赖: fun_prop
-/
lemma stronglyMeasurable_gaussianPDF (μ : Real) (v : Real>=0) :
    StronglyMeasurable (gaussianPDF μ v) := by
  fun_prop

@[simp]
/--
lemma `lintegral_gaussianPDF_eq_one` / 引理 `lintegral_gaussianPDF_eq_one`

English:
lemma lintegral_gaussianPDF_eq_one
  given: (μ : Real) {v : Real>=0} (h : v != 0)
  proof: lintegral_gaussianPDFReal_eq_one μ h

中文:
引理 lintegral_gaussianPDF_eq_one
  条件: (μ : 实数) {v : 实数>=0} (h : v != 0)
  证明: lintegral_gaussianPDFReal_eq_one μ h

Depends on / 依赖: lintegral_gaussianPDFReal_eq_one
-/
lemma lintegral_gaussianPDF_eq_one (μ : Real) {v : Real>=0} (h : v != 0) :
    ∫⁻ x, gaussianPDF μ v x = 1 :=
  lintegral_gaussianPDFReal_eq_one μ h

end GaussianPDF

section GaussianReal

/-- A Gaussian distribution on `ℝ` with mean `μ` and variance `v`. -/
@[wikidata Q133871]
noncomputable
/--
Definition of `gaussianReal` / `gaussianReal` 的定义

English:
definition gaussianReal
  signature: (μ : Real) (v : Real>=0)
  body: if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)

中文:
定义 gaussian实数
  签名: (μ : 实数) (v : 实数>=0)
  定义体: if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)

Depends on / 依赖: Measure, Measure.dirac, gaussianPDF, volume, volume.withDensity, withDensity
-/
def gaussianReal (μ : Real) (v : Real>=0) : Measure Real :=
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)

/--
lemma `gaussianReal_of_var_ne_zero` / 引理 `gaussianReal_of_var_ne_zero`

English:
lemma gaussianReal_of_var_ne_zero
  given: (μ : Real) {v : Real>=0} (hv : v != 0)
  proof: if_neg hv

@[simp]

中文:
引理 gaussian实数_of_var_ne_zero
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0)
  证明: if_neg hv

@[simp]

Depends on / 依赖: if_neg
-/
lemma gaussianReal_of_var_ne_zero (μ : Real) {v : Real>=0} (hv : v != 0) :
    gaussianReal μ v = volume.withDensity (gaussianPDF μ v) := if_neg hv

@[simp]
/--
lemma `gaussianReal_zero_var` / 引理 `gaussianReal_zero_var`

English:
lemma gaussianReal_zero_var
  given: (μ : Real)
  statement: gaussianReal μ 0 = Measure.dirac μ
  proof: if_pos rfl

中文:
引理 gaussian实数_zero_var
  条件: (μ : 实数)
  结论: gaussian实数 μ 0 = 测度.dirac μ
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
lemma gaussianReal_zero_var (μ : Real) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl

/--
Instance `instIsProbabilityMeasureGaussianReal` / 实例 `instIsProbabilityMeasureGaussianReal`

English:
instance instIsProbabilityMeasureGaussianReal
  signature: (μ : Real) (v : Real>=0)
  body: by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

中文:
实例 instIsProbabilityMeasureGaussian实数
  签名: (μ : 实数) (v : 实数>=0)
  定义体: by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

Depends on / 依赖: gaussianReal_of_var_ne_zero
-/
instance instIsProbabilityMeasureGaussianReal (μ : Real) (v : Real>=0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

/--
lemma `nullSingletonClass_gaussianReal` / 引理 `nullSingletonClass_gaussianReal`

English:
lemma nullSingletonClass_gaussianReal
  given: {μ : Real} {v : Real>=0} (h : v != 0)
  proof: by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

@[deprecated (since := "2026-06-09")]
alias noAtoms_gaussianReal := nullSingletonClass_gaussianReal

中文:
引理 nullSingletonClass_gaussian实数
  条件: {μ : 实数} {v : 实数>=0} (h : v != 0)
  证明: by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

@[deprecated (since := "2026-06-09")]
alias noAtoms_gaussianReal := nullSingletonClass_gaussianReal

Depends on / 依赖: gaussianReal_of_var_ne_zero, infer_instance
-/
lemma nullSingletonClass_gaussianReal {μ : Real} {v : Real>=0} (h : v != 0) :
    NullSingletonClass (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

@[deprecated (since := "2026-06-09")]
alias noAtoms_gaussianReal := nullSingletonClass_gaussianReal

/--
lemma `gaussianReal_apply` / 引理 `gaussianReal_apply`

English:
lemma gaussianReal_apply
  given: (μ : Real) {v : Real>=0} (hv : v != 0) (s : Set Real)
  proof: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [withDensity_apply' _ s]

中文:
引理 gaussian实数_apply
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0) (s : 集合 实数)
  证明: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [withDensity_apply' _ s]

Depends on / 依赖: gaussianReal_of_var_ne_zero, withDensity_apply
-/
lemma gaussianReal_apply (μ : Real) {v : Real>=0} (hv : v != 0) (s : Set Real) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v x := by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [withDensity_apply' _ s]

/--
lemma `gaussianReal_apply_eq_integral` / 引理 `gaussianReal_apply_eq_integral`

English:
lemma gaussianReal_apply_eq_integral
  given: (μ : Real) {v : Real>=0} (hv : v != 0) (s : Set Real)
  proof: by
  rw [gaussianReal_apply _ hv s]; rw [ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ _).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ _)

中文:
引理 gaussian实数_apply_eq_integral
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0) (s : 集合 实数)
  证明: by
  rw [gaussianReal_apply _ hv s]; rw [ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ _).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ _)

Depends on / 依赖: ae_of_all, gaussianPDFReal_nonneg, gaussianReal_apply, integrable_gaussianPDFReal, ofReal_integral_eq_lintegral_ofReal, restrict
-/
lemma gaussianReal_apply_eq_integral (μ : Real) {v : Real>=0} (hv : v != 0) (s : Set Real) :
    gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x) := by
  rw [gaussianReal_apply _ hv s]; rw [ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ _).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ _)

/--
lemma `gaussianReal_absolutelyContinuous` / 引理 `gaussianReal_absolutelyContinuous`

English:
lemma gaussianReal_absolutelyContinuous
  given: (μ : Real) {v : Real>=0} (hv : v != 0)
  proof: by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

中文:
引理 gaussian实数_absolutelyContinuous
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0)
  证明: by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

Depends on / 依赖: gaussianReal_of_var_ne_zero, withDensity_absolutelyContinuous
-/
lemma gaussianReal_absolutelyContinuous (μ : Real) {v : Real>=0} (hv : v != 0) :
    gaussianReal μ v ≪ volume := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

/--
lemma `gaussianReal_absolutelyContinuous'` / 引理 `gaussianReal_absolutelyContinuous'`

English:
lemma gaussianReal_absolutelyContinuous'
  given: (μ : Real) {v : Real>=0} (hv : v != 0)
  proof: by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ _).aemeasurable
  · exact ae_of_all _ (fun _ => (gaussianPDF_pos _ hv _).ne')

中文:
引理 gaussian实数_absolutelyContinuous'
  条件: (μ : 实数) {v : 实数>=0} (hv : v != 0)
  证明: by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ _).aemeasurable
  · exact ae_of_all _ (fun _ => (gaussianPDF_pos _ hv _).ne')

Depends on / 依赖: ae_of_all, aemeasurable, gaussianPDF_pos, gaussianReal_of_var_ne_zero, measurable_gaussianPDF, withDensity_absolutelyContinuous
-/
lemma gaussianReal_absolutelyContinuous' (μ : Real) {v : Real>=0} (hv : v != 0) :
    volume ≪ gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ _).aemeasurable
  · exact ae_of_all _ (fun _ => (gaussianPDF_pos _ hv _).ne')

/--
lemma `rnDeriv_gaussianReal` / 引理 `rnDeriv_gaussianReal`

English:
lemma rnDeriv_gaussianReal
  given: (μ : Real) (v : Real>=0)
  proof: by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero]; rw [add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)

中文:
引理 rnDeriv_gaussian实数
  条件: (μ : 实数) (v : 实数>=0)
  证明: by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero]; rw [add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)

Depends on / 依赖: Measure, Measure.eq_rnDeriv, Measure.rnDeriv_withDensity, add_zero, eq_rnDeriv, gaussianPDF_zero_var, gaussianReal_of_var_ne_zero, gaussianReal_zero_var, measurable_gaussianPDF, measurable_zero, mutuallySingular_dirac, rnDeriv_withDensity, volume, withDensity_zero
-/
lemma rnDeriv_gaussianReal (μ : Real) (v : Real>=0) :
    ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero]; rw [add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)

/--
lemma `integral_gaussianReal_eq_integral_smul` / 引理 `integral_gaussianReal_eq_integral_smul`

English:
lemma integral_gaussianReal_eq_integral_smul
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  simp [gaussianReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]

@[fun_prop]

中文:
引理 integral_gaussian实数_eq_integral_smul
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  simp [gaussianReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]

@[fun_prop]

Depends on / 依赖: ae_of_all, gaussianPDF_lt_top, gaussianReal, integral_withDensity_eq_integral_toReal_smul, measurable_gaussianPDF
-/
lemma integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {μ : Real} {v : Real>=0} {f : Real -> E} (hv : v != 0) :
    ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x := by
  simp [gaussianReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]

@[fun_prop]
/--
lemma `measurable_gaussianReal` / 引理 `measurable_gaussianReal`

English:
lemma measurable_gaussianReal
  proof: Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

中文:
引理 measurable_gaussian实数
  证明: Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

Depends on / 依赖: Measurable, Measurable.ite, fun_prop, measurability
-/
lemma measurable_gaussianReal :
    Measurable gaussianReal.uncurry :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

section Transformations

variable {μ : Real} {v : Real>=0}

/--
lemma `_root_.MeasurableEmbedding.gaussianReal_comap_apply` / 引理 `_root_.MeasurableEmbedding.gaussianReal_comap_apply`

English:
lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply
  statement: (hv : v != 0)
  proof: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

中文:
引理 _root_.可测嵌入.gaussian实数_comap_apply
  结论: (hv : v != 0)
  证明: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

Depends on / 依赖: ae_of_all, gaussianPDFReal_nonneg, gaussianPDF_def, gaussianReal_of_var_ne_zero, h_deriv, hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul, integrable_gaussianPDFReal, withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
-/
lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply (hv : v != 0)
    {f : Real -> Real} (hf : MeasurableEmbedding f)
    {f' : Real -> Real} (h_deriv : forall x, HasDerivAt f (f' x) x) {s : Set Real} (hs : MeasurableSet s) :
    (gaussianReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

/--
lemma `_root_.MeasurableEquiv.gaussianReal_map_symm_apply` / 引理 `_root_.MeasurableEquiv.gaussianReal_map_symm_apply`

English:
lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply
  statement: (hv : v != 0) (f : Real ≃ᵐ Real) {f' : Real -> Real}
  proof: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

中文:
引理 _root_.可测等价.gaussian实数_map_symm_apply
  结论: (hv : v != 0) (f : 实数 ≃ᵐ 实数) {f' : 实数 -> 实数}
  证明: by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

Depends on / 依赖: ae_of_all, f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul, gaussianPDFReal_nonneg, gaussianPDF_def, gaussianReal_of_var_ne_zero, h_deriv, integrable_gaussianPDFReal, withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul
-/
lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply (hv : v != 0) (f : Real ≃ᵐ Real) {f' : Real -> Real}
    (h_deriv : forall x, HasDerivAt f (f' x) x) {s : Set Real} (hs : MeasurableSet s) :
    (gaussianReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv]; rw [gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

/--
lemma `gaussianReal_map_add_const` / 引理 `gaussianReal_map_add_const`

English:
lemma gaussianReal_map_add_const
  given: (y : Real)
  proof: by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  let e : Real ≃ᵐ Real := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => 1) x) x := fun _ => (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

中文:
引理 gaussian实数_map_add_const
  条件: (y : 实数)
  证明: by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  let e : Real ≃ᵐ Real := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => 1) x) x := fun _ => (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

Depends on / 依赖: HasDerivAt, Homeomorph, Homeomorph.addRight, MeasurableEquiv, MeasurableEquiv.gaussianReal_map_symm_apply, abs_one, addRight, e.symm, gaussianPDFReal_sub, gaussianReal, gaussianReal_apply_eq_integral, gaussianReal_map_symm_apply, gaussianReal_zero_var, hasDerivAt_id, one_mul, sub_const, sub_eq_add_, symm.toMeasurableEquiv, toMeasurableEquiv
-/
lemma gaussianReal_map_add_const (y : Real) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  let e : Real ≃ᵐ Real := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => 1) x) x := fun _ => (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/--
lemma `gaussianReal_map_const_add` / 引理 `gaussianReal_map_const_add`

English:
lemma gaussianReal_map_const_add
  given: (y : Real)
  proof: by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

中文:
引理 gaussian实数_map_const_add
  条件: (y : 实数)
  证明: by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

Depends on / 依赖: add_comm, gaussianReal_map_add_const, simp_rw
-/
lemma gaussianReal_map_const_add (y : Real) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `gaussianReal_map_const_mul` / 引理 `gaussianReal_map_const_mul`

English:
lemma gaussianReal_map_const_mul
  given: (c : Real)
  proof: by
  by_cases hv : v = 0
  · simp [hv, mul_zero, gaussianReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : Real ≃ᵐ Real := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => c⁻¹) x) x := by
    suffices forall x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ => HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']; rw [gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv]; rw [inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

中文:
引理 gaussian实数_map_const_mul
  条件: (c : 实数)
  证明: by
  by_cases hv : v = 0
  · simp [hv, mul_zero, gaussianReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : Real ≃ᵐ Real := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => c⁻¹) x) x := by
    suffices forall x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ => HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']; rw [gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv]; rw [inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

Depends on / 依赖: HasDerivAt, HasDerivAt.const_mul, Homeomorph, Homeomorph.mulLeft, Measur, const_mul, e.symm, gaussianReal, gaussianReal_zero_var, hasDerivAt_id, mul_one, mul_zero, sq_nonneg, symm.toMeasurableEquiv, toMeasurableEquiv, zero_mul
-/
lemma gaussianReal_map_const_mul (c : Real) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, gaussianReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : Real ≃ᵐ Real := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : forall x, HasDerivAt e ((fun _ => c⁻¹) x) x := by
    suffices forall x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ => HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']; rw [gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv]; rw [inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/--
lemma `gaussianReal_map_mul_const` / 引理 `gaussianReal_map_mul_const`

English:
lemma gaussianReal_map_mul_const
  given: (c : Real)
  proof: by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

中文:
引理 gaussian实数_map_mul_const
  条件: (c : 实数)
  证明: by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

Depends on / 依赖: gaussianReal_map_const_mul, mul_comm, simp_rw
-/
lemma gaussianReal_map_mul_const (c : Real) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

/--
lemma `gaussianReal_map_neg` / 引理 `gaussianReal_map_neg`

English:
lemma gaussianReal_map_neg
  statement: (gaussianReal μ v).map (fun x => -x) = gaussianReal (-μ) v
  proof: by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

中文:
引理 gaussian实数_map_neg
  结论: (gaussian实数 μ v).map (fun x => -x) = gaussian实数 (-μ) v
  证明: by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

Depends on / 依赖: gaussianReal_map_const_mul
-/
lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x => -x) = gaussianReal (-μ) v := by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

/--
lemma `gaussianReal_map_div_const` / 引理 `gaussianReal_map_div_const`

English:
lemma gaussianReal_map_div_const
  given: (c : Real)
  proof: by
  simp_rw [div_eq_mul_inv]
  convert! gaussianReal_map_mul_const c⁻¹ using 2 <;> rw [mul_comm]
  ext; simp

中文:
引理 gaussian实数_map_div_const
  条件: (c : 实数)
  证明: by
  simp_rw [div_eq_mul_inv]
  convert! gaussianReal_map_mul_const c⁻¹ using 2 <;> rw [mul_comm]
  ext; simp

Depends on / 依赖: convert, div_eq_mul_inv, gaussianReal_map_mul_const, mul_comm, simp_rw
-/
lemma gaussianReal_map_div_const (c : Real) :
    (gaussianReal μ v).map (· / c) = gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _)) := by
  simp_rw [div_eq_mul_inv]
  convert! gaussianReal_map_mul_const c⁻¹ using 2 <;> rw [mul_comm]
  ext; simp

/--
lemma `gaussianReal_map_sub_const` / 引理 `gaussianReal_map_sub_const`

English:
lemma gaussianReal_map_sub_const
  given: (y : Real)
  proof: by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]

中文:
引理 gaussian实数_map_sub_const
  条件: (y : 实数)
  证明: by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]

Depends on / 依赖: gaussianReal_map_add_const, simp_rw, sub_eq_add_neg
-/
lemma gaussianReal_map_sub_const (y : Real) :
    (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]

/--
lemma `gaussianReal_map_const_sub` / 引理 `gaussianReal_map_const_sub`

English:
lemma gaussianReal_map_const_sub
  given: (y : Real)
  proof: by
  simp_rw [sub_eq_add_neg]
  have : (fun x => y + -x) = (fun x => y + x) ∘ fun x => -x := by ext; simp
  rw [this]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [gaussianReal_map_neg]; rw [gaussianReal_map_const_add]; rw [add_comm]

中文:
引理 gaussian实数_map_const_sub
  条件: (y : 实数)
  证明: by
  simp_rw [sub_eq_add_neg]
  have : (fun x => y + -x) = (fun x => y + x) ∘ fun x => -x := by ext; simp
  rw [this]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [gaussianReal_map_neg]; rw [gaussianReal_map_const_add]; rw [add_comm]

Depends on / 依赖: Measure, Measure.map_map, add_comm, fun_prop, gaussianReal_map_const_add, gaussianReal_map_neg, map_map, simp_rw, sub_eq_add_neg
-/
lemma gaussianReal_map_const_sub (y : Real) :
    (gaussianReal μ v).map (y - ·) = gaussianReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x => y + -x) = (fun x => y + x) ∘ fun x => -x := by ext; simp
  rw [this]; rw [← Measure.map_map (by fun_prop) (by fun_prop)]; rw [gaussianReal_map_neg]; rw [gaussianReal_map_const_add]; rw [add_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω -> Real}

/--
lemma `gaussianReal_add_const` / 引理 `gaussianReal_add_const`

English:
lemma gaussianReal_add_const
  given: (hX : HasLaw X (gaussianReal μ v) P) (y : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_add_const y⟩ hX

中文:
引理 gaussian实数_add_const
  条件: (hX : 有Law X (gaussian实数 μ v) P) (y : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_add_const y⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_add_const
-/
lemma gaussianReal_add_const (hX : HasLaw X (gaussianReal μ v) P) (y : Real) :
    HasLaw (fun ω => X ω + y) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_add_const y⟩ hX

/--
lemma `gaussianReal_const_add` / 引理 `gaussianReal_const_add`

English:
lemma gaussianReal_const_add
  given: (hX : HasLaw X (gaussianReal μ v) P) (y : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_add y⟩ hX

中文:
引理 gaussian实数_const_add
  条件: (hX : 有Law X (gaussian实数 μ v) P) (y : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_add y⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_const_add
-/
lemma gaussianReal_const_add (hX : HasLaw X (gaussianReal μ v) P) (y : Real) :
    HasLaw (fun ω => y + X ω) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_add y⟩ hX

/--
lemma `gaussianReal_sub_const` / 引理 `gaussianReal_sub_const`

English:
lemma gaussianReal_sub_const
  given: (hX : HasLaw X (gaussianReal μ v) P) (y : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_sub_const y⟩ hX

中文:
引理 gaussian实数_sub_const
  条件: (hX : 有Law X (gaussian实数 μ v) P) (y : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_sub_const y⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_sub_const
-/
lemma gaussianReal_sub_const (hX : HasLaw X (gaussianReal μ v) P) (y : Real) :
    HasLaw (fun ω => X ω - y) (gaussianReal (μ - y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_sub_const y⟩ hX

/--
lemma `gaussianReal_const_mul` / 引理 `gaussianReal_const_mul`

English:
lemma gaussianReal_const_mul
  given: (hX : HasLaw X (gaussianReal μ v) P) (c : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul c⟩ hX

中文:
引理 gaussian实数_const_mul
  条件: (hX : 有Law X (gaussian实数 μ v) P) (c : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul c⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_const_mul
-/
lemma gaussianReal_const_mul (hX : HasLaw X (gaussianReal μ v) P) (c : Real) :
    HasLaw (fun ω => c * X ω) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul c⟩ hX

/--
lemma `gaussianReal_mul_const` / 引理 `gaussianReal_mul_const`

English:
lemma gaussianReal_mul_const
  given: (hX : HasLaw X (gaussianReal μ v) P) (c : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_mul_const c⟩ hX

中文:
引理 gaussian实数_mul_const
  条件: (hX : 有Law X (gaussian实数 μ v) P) (c : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_mul_const c⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_mul_const
-/
lemma gaussianReal_mul_const (hX : HasLaw X (gaussianReal μ v) P) (c : Real) :
    HasLaw (fun ω => X ω * c) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_mul_const c⟩ hX

/--
lemma `gaussianReal_neg` / 引理 `gaussianReal_neg`

English:
lemma gaussianReal_neg
  given: (hX : HasLaw X (gaussianReal μ v) P)
  proof: by
  rw [Pi.neg_def]; rw [← Function.comp_def]
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_neg⟩ hX

中文:
引理 gaussian实数_neg
  条件: (hX : 有Law X (gaussian实数 μ v) P)
  证明: by
  rw [Pi.neg_def]; rw [← Function.comp_def]
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_neg⟩ hX

Depends on / 依赖: Function, Function.comp_def, HasLaw, HasLaw.comp, Pi.neg_def, comp_def, fun_prop, gaussianReal_map_neg, neg_def
-/
lemma gaussianReal_neg (hX : HasLaw X (gaussianReal μ v) P) :
    HasLaw (-X) (gaussianReal (-μ) v) P := by
  rw [Pi.neg_def]; rw [← Function.comp_def]
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_neg⟩ hX

/--
lemma `gaussianReal_div_const` / 引理 `gaussianReal_div_const`

English:
lemma gaussianReal_div_const
  given: (hX : HasLaw X (gaussianReal μ v) P) (c : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_div_const c⟩ hX

中文:
引理 gaussian实数_div_const
  条件: (hX : 有Law X (gaussian实数 μ v) P) (c : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_div_const c⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_div_const
-/
lemma gaussianReal_div_const (hX : HasLaw X (gaussianReal μ v) P) (c : Real) :
    HasLaw (fun ω => X ω / c) (gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_div_const c⟩ hX

/--
lemma `gaussianReal_const_sub` / 引理 `gaussianReal_const_sub`

English:
lemma gaussianReal_const_sub
  given: (hX : HasLaw X (gaussianReal μ v) P) (y : Real)
  proof: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_sub y⟩ hX

中文:
引理 gaussian实数_const_sub
  条件: (hX : 有Law X (gaussian实数 μ v) P) (y : 实数)
  证明: HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_sub y⟩ hX

Depends on / 依赖: HasLaw, HasLaw.comp, fun_prop, gaussianReal_map_const_sub
-/
lemma gaussianReal_const_sub (hX : HasLaw X (gaussianReal μ v) P) (y : Real) :
    HasLaw (fun ω => y - X ω) (gaussianReal (y - μ) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_sub y⟩ hX

end Transformations

section CharacteristicFunction

open Real Complex

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : Measure Ω} {μ : Real} {v : Real>=0} {X : Ω -> Real}

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `complexMGF_id_gaussianReal` / 定理 `complexMGF_id_gaussianReal`

English:
theorem complexMGF_id_gaussianReal
  given: (z : Complex)
  proof: by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : Real, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : Complex)
        * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv)]; rw [← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : Complex) != 0 := by simpa
      simp [field]
      ring

中文:
定理 complexMGF_id_gaussian实数
  条件: (z : 复形)
  证明: by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : Real, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : Complex)
        * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv)]; rw [← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : Complex) != 0 := by simpa
      simp [field]
      ring

Depends on / 依赖: Complex.exp_add, Complex.real_smul, complexMGF, exp_add, gaussianPDFReal, gaussianReal, integral_const_mul, integral_gaussianReal_eq_integral_smul, mul_assoc, real_smul, simp_rw
-/
theorem complexMGF_id_gaussianReal (z : Complex) :
    complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 2) := by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : Real, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : Complex)
        * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv)]; rw [← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : Complex) != 0 := by simpa
      simp [field]
      ring

/--
theorem `complexMGF_gaussianReal` / 定理 `complexMGF_gaussianReal`

English:
theorem complexMGF_gaussianReal
  given: (hX : p.map X = gaussianReal μ v) (z : Complex)
  proof: by
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← complexMGF_id_map hX_meas]; rw [hX]; rw [complexMGF_id_gaussianReal]

中文:
定理 complexMGF_gaussian实数
  条件: (hX : p.map X = gaussian实数 μ v) (z : 复形)
  证明: by
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← complexMGF_id_map hX_meas]; rw [hX]; rw [complexMGF_id_gaussianReal]

Depends on / 依赖: AEMeasurable, aemeasurable_of_map_neZero, complexMGF_id_gaussianReal, complexMGF_id_map, hX_meas, infer_instance
-/
theorem complexMGF_gaussianReal (hX : p.map X = gaussianReal μ v) (z : Complex) :
    complexMGF X p z = cexp (z * μ + v * z ^ 2 / 2) := by
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← complexMGF_id_map hX_meas]; rw [hX]; rw [complexMGF_id_gaussianReal]

/--
theorem `charFun_gaussianReal` / 定理 `charFun_gaussianReal`

English:
theorem charFun_gaussianReal
  given: (t : Real)
  proof: by
  rw [← complexMGF_id_mul_I]; rw [complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  ring_nf

中文:
定理 charFun_gaussian实数
  条件: (t : 实数)
  证明: by
  rw [← complexMGF_id_mul_I]; rw [complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  ring_nf

Depends on / 依赖: I_sq, complexMGF_id_gaussianReal, complexMGF_id_mul_I, mul_neg, mul_one, mul_pow, ring_nf, sub_eq_add_neg
-/
theorem charFun_gaussianReal (t : Real) :
    charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2) := by
  rw [← complexMGF_id_mul_I]; rw [complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  ring_nf

/--
theorem `mgf_gaussianReal` / 定理 `mgf_gaussianReal`

English:
theorem mgf_gaussianReal
  given: (hX : p.map X = gaussianReal μ v) (t : Real)
  proof: by
  suffices (mgf X p t : Complex) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← mgf_id_map hX_meas]; rw [← complexMGF_ofReal]; rw [hX]; rw [complexMGF_id_gaussianReal]; rw [mul_comm μ]
  norm_cast

中文:
定理 mgf_gaussian实数
  条件: (hX : p.map X = gaussian实数 μ v) (t : 实数)
  证明: by
  suffices (mgf X p t : Complex) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← mgf_id_map hX_meas]; rw [← complexMGF_ofReal]; rw [hX]; rw [complexMGF_id_gaussianReal]; rw [mul_comm μ]
  norm_cast

Depends on / 依赖: AEMeasurable, aemeasurable_of_map_neZero, complexMGF_id_gaussianReal, complexMGF_ofReal, hX_meas, infer_instance, mgf_id_map, mod_cast, mul_comm
-/
theorem mgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : Real) :
    mgf X p t = rexp (μ * t + v * t ^ 2 / 2) := by
  suffices (mgf X p t : Complex) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← mgf_id_map hX_meas]; rw [← complexMGF_ofReal]; rw [hX]; rw [complexMGF_id_gaussianReal]; rw [mul_comm μ]
  norm_cast

/--
theorem `mgf_fun_id_gaussianReal` / 定理 `mgf_fun_id_gaussianReal`

English:
theorem mgf_fun_id_gaussianReal
  proof: by
  ext t
  rw [mgf_gaussianReal]
  simp

中文:
定理 mgf_fun_id_gaussian实数
  证明: by
  ext t
  rw [mgf_gaussianReal]
  simp

Depends on / 依赖: mgf_gaussianReal
-/
theorem mgf_fun_id_gaussianReal :
    mgf (fun x => x) (gaussianReal μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2) := by
  ext t
  rw [mgf_gaussianReal]
  simp

/--
theorem `mgf_id_gaussianReal` / 定理 `mgf_id_gaussianReal`

English:
theorem mgf_id_gaussianReal
  statement: mgf id (gaussianReal μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2)
  proof: mgf_fun_id_gaussianReal

中文:
定理 mgf_id_gaussian实数
  结论: mgf id (gaussian实数 μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2)
  证明: mgf_fun_id_gaussianReal

Depends on / 依赖: mgf_fun_id_gaussianReal
-/
theorem mgf_id_gaussianReal : mgf id (gaussianReal μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2) :=
  mgf_fun_id_gaussianReal

/--
theorem `cgf_gaussianReal` / 定理 `cgf_gaussianReal`

English:
theorem cgf_gaussianReal
  given: (hX : p.map X = gaussianReal μ v) (t : Real)
  proof: by
  rw [cgf]; rw [mgf_gaussianReal hX t]; rw [Real.log_exp]

中文:
定理 cgf_gaussian实数
  条件: (hX : p.map X = gaussian实数 μ v) (t : 实数)
  证明: by
  rw [cgf]; rw [mgf_gaussianReal hX t]; rw [Real.log_exp]

Depends on / 依赖: Real.log_exp, log_exp, mgf_gaussianReal
-/
theorem cgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : Real) :
    cgf X p t = μ * t + v * t ^ 2 / 2 := by
  rw [cgf]; rw [mgf_gaussianReal hX t]; rw [Real.log_exp]

/--
lemma `integrable_exp_mul_gaussianReal` / 引理 `integrable_exp_mul_gaussianReal`

English:
lemma integrable_exp_mul_gaussianReal
  given: (t : Real)
  proof: by
  rw [← mgf_pos_iff]; rw [mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]

中文:
引理 integrable_exp_mul_gaussian实数
  条件: (t : 实数)
  证明: by
  rw [← mgf_pos_iff]; rw [mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]

Depends on / 依赖: Real.exp_pos, exp_pos, mgf_gaussianReal, mgf_pos_iff
-/
lemma integrable_exp_mul_gaussianReal (t : Real) :
    Integrable (fun x => rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff]; rw [mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
/--
lemma `integrableExpSet_id_gaussianReal` / 引理 `integrableExpSet_id_gaussianReal`

English:
lemma integrableExpSet_id_gaussianReal
  statement: integrableExpSet id (gaussianReal μ v) = Set.univ
  proof: by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]

中文:
引理 integrableExpSet_id_gaussian实数
  结论: integrableExpSet id (gaussian实数 μ v) = 集合.univ
  证明: by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]

Depends on / 依赖: integrableExpSet, integrable_exp_mul_gaussianReal
-/
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]
/--
lemma `integrableExpSet_fun_id_gaussianReal` / 引理 `integrableExpSet_fun_id_gaussianReal`

English:
lemma integrableExpSet_fun_id_gaussianReal
  proof: integrableExpSet_id_gaussianReal

中文:
引理 integrableExpSet_fun_id_gaussian实数
  证明: integrableExpSet_id_gaussianReal

Depends on / 依赖: integrableExpSet_id_gaussianReal
-/
lemma integrableExpSet_fun_id_gaussianReal :
    integrableExpSet (fun x => x) (gaussianReal μ v) = Set.univ :=
  integrableExpSet_id_gaussianReal

end CharacteristicFunction

section Moments

variable {μ : Real} {v : Real>=0}

/-- The mean of a real Gaussian distribution `gaussianReal μ v` is its mean parameter `μ`. -/
@[simp]
/--
lemma `integral_id_gaussianReal` / 引理 `integral_id_gaussianReal`

English:
lemma integral_id_gaussianReal
  statement: ∫ x, x ∂gaussianReal μ v = μ
  proof: by
  rw [← deriv_mgf_zero (by simp)]; rw [mgf_fun_id_gaussianReal]; rw [_root_.deriv_exp (by fun_prop)]
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.exp_zero, one_mul]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

中文:
引理 integral_id_gaussian实数
  结论: ∫ x, x ∂gaussian实数 μ v = μ
  证明: by
  rw [← deriv_mgf_zero (by simp)]; rw [mgf_fun_id_gaussianReal]; rw [_root_.deriv_exp (by fun_prop)]
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.exp_zero, one_mul]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

Depends on / 依赖: OfNat.ofNat_ne_zero, Real.exp_zero, _root_, _root_.deriv_exp, add_zero, deriv_exp, deriv_fun_add, deriv_fun_mul, deriv_mgf_zero, exp_zero, fun_prop, mgf_fun_id_gaussianReal, mul_zero, ne_eq, not_false_eq_true, ofNat_ne_zero, one_mul, zero_div, zero_pow
-/
lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ := by
  rw [← deriv_mgf_zero (by simp)]; rw [mgf_fun_id_gaussianReal]; rw [_root_.deriv_exp (by fun_prop)]
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.exp_zero, one_mul]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
/--
lemma `variance_fun_id_gaussianReal` / 引理 `variance_fun_id_gaussianReal`

English:
lemma variance_fun_id_gaussianReal
  statement: Var[fun x => x; gaussianReal μ v] = v
  proof: by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x => x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal]; rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have : deriv (fun t => rexp (v * t ^ 2 / 2)) = fun t => v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp

中文:
引理 variance_fun_id_gaussian实数
  结论: Var[fun x => x; gaussian实数 μ v] = v
  证明: by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x => x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal]; rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have : deriv (fun t => rexp (v * t ^ 2 / 2)) = fun t => v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp

Depends on / 依赖: aemeasurable, fun_prop, gaussianReal, gaussianReal_map_sub_const, integral_id_gaussianReal, integral_map, iteratedD, iteratedDeriv, iteratedDeriv_mgf_zero, iteratedDeriv_succ, measurable_id, mgf_fun_id_gaussianReal, variance_eq_integral
-/
lemma variance_fun_id_gaussianReal : Var[fun x => x; gaussianReal μ v] = v := by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x => x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal]; rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have : deriv (fun t => rexp (v * t ^ 2 / 2)) = fun t => v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
/--
lemma `variance_id_gaussianReal` / 引理 `variance_id_gaussianReal`

English:
lemma variance_id_gaussianReal
  statement: Var[id; gaussianReal μ v] = v
  proof: variance_fun_id_gaussianReal

中文:
引理 variance_id_gaussian实数
  结论: Var[id; gaussian实数 μ v] = v
  证明: variance_fun_id_gaussianReal

Depends on / 依赖: variance_fun_id_gaussianReal
-/
lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v :=
  variance_fun_id_gaussianReal

/--
lemma `memLp_id_gaussianReal` / 引理 `memLp_id_gaussianReal`

English:
lemma memLp_id_gaussianReal
  given: (p : Real>=0)
  statement: MemLp id p (gaussianReal μ v)
  proof: memLp_of_mem_interior_integrableExpSet (by simp) p

中文:
引理 memLp_id_gaussian实数
  条件: (p : 实数>=0)
  结论: MemLp id p (gaussian实数 μ v)
  证明: memLp_of_mem_interior_integrableExpSet (by simp) p

Depends on / 依赖: memLp_of_mem_interior_integrableExpSet
-/
lemma memLp_id_gaussianReal (p : Real>=0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/--
lemma `memLp_id_gaussianReal'` / 引理 `memLp_id_gaussianReal'`

English:
lemma memLp_id_gaussianReal'
  given: (p : Real>=0∞) (hp : p != ∞)
  statement: MemLp id p (gaussianReal μ v)
  proof: by
  lift p to Real>=0 using hp
  exact memLp_id_gaussianReal p

中文:
引理 memLp_id_gaussian实数'
  条件: (p : 实数>=0∞) (hp : p != ∞)
  结论: MemLp id p (gaussian实数 μ v)
  证明: by
  lift p to Real>=0 using hp
  exact memLp_id_gaussianReal p

Depends on / 依赖: memLp_id_gaussianReal
-/
lemma memLp_id_gaussianReal' (p : Real>=0∞) (hp : p != ∞) : MemLp id p (gaussianReal μ v) := by
  lift p to Real>=0 using hp
  exact memLp_id_gaussianReal p

end Moments

/--
lemma `gaussianReal_ext_iff` / 引理 `gaussianReal_ext_iff`

English:
lemma gaussianReal_ext_iff
  given: {μ₁ μ₂ : Real} {v₁ v₂ : Real>=0}
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← integral_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : Real) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← variance_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]

中文:
引理 gaussian实数_ext_iff
  条件: {μ₁ μ₂ : 实数} {v₁ v₂ : 实数>=0}
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← integral_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : Real) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← variance_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]

Depends on / 依赖: integral_id_gaussianReal, true_and, variance_id_gaussianReal
-/
lemma gaussianReal_ext_iff {μ₁ μ₂ : Real} {v₁ v₂ : Real>=0} :
    gaussianReal μ₁ v₁ = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← integral_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : Real) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁)]; rw [← variance_id_gaussianReal (μ := μ₂) (v := v₂)]; rw [h]

section LinearMap

variable {μ : Real} {v : Real>=0}

/--
lemma `gaussianReal_map_linearMap` / 引理 `gaussianReal_map_linearMap`

English:
lemma gaussianReal_map_linearMap
  given: (L : Real ->ₗ[Real] Real)
  proof: by
  have : (L : Real -> Real) = fun x => L 1 * x := by simp
  rw [this]; rw [gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity

中文:
引理 gaussian实数_map_linearMap
  条件: (L : 实数 ->ₗ[实数] 实数)
  证明: by
  have : (L : Real -> Real) = fun x => L 1 * x := by simp
  rw [this]; rw [gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity

Depends on / 依赖: gaussianReal_map_const_mul, left_eq_sup, mul_one
-/
lemma gaussianReal_map_linearMap (L : Real ->ₗ[Real] Real) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) := by
  have : (L : Real -> Real) = fun x => L 1 * x := by simp
  rw [this]; rw [gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity

/--
lemma `gaussianReal_map_continuousLinearMap` / 引理 `gaussianReal_map_continuousLinearMap`

English:
lemma gaussianReal_map_continuousLinearMap
  given: (L : Real ->L[Real] Real)
  proof: gaussianReal_map_linearMap L

@[simp]

中文:
引理 gaussian实数_map_continuousLinearMap
  条件: (L : 实数 ->L[实数] 实数)
  证明: gaussianReal_map_linearMap L

@[simp]

Depends on / 依赖: gaussianReal_map_linearMap
-/
lemma gaussianReal_map_continuousLinearMap (L : Real ->L[Real] Real) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) :=
  gaussianReal_map_linearMap L

@[simp]
/--
lemma `integral_linearMap_gaussianReal` / 引理 `integral_linearMap_gaussianReal`

English:
lemma integral_linearMap_gaussianReal
  given: (L : Real ->ₗ[Real] Real)
  proof: by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]

中文:
引理 integral_linearMap_gaussian实数
  条件: (L : 实数 ->ₗ[实数] 实数)
  证明: by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]

Depends on / 依赖: fun_prop, gaussianReal, gaussianReal_map_linearMap, integral_map
-/
lemma integral_linearMap_gaussianReal (L : Real ->ₗ[Real] Real) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]
/--
lemma `integral_continuousLinearMap_gaussianReal` / 引理 `integral_continuousLinearMap_gaussianReal`

English:
lemma integral_continuousLinearMap_gaussianReal
  given: (L : Real ->L[Real] Real)
  proof: integral_linearMap_gaussianReal L

@[simp]

中文:
引理 integral_continuousLinearMap_gaussian实数
  条件: (L : 实数 ->L[实数] 实数)
  证明: integral_linearMap_gaussianReal L

@[simp]

Depends on / 依赖: integral_linearMap_gaussianReal
-/
lemma integral_continuousLinearMap_gaussianReal (L : Real ->L[Real] Real) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := integral_linearMap_gaussianReal L

@[simp]
/--
lemma `variance_linearMap_gaussianReal` / 引理 `variance_linearMap_gaussianReal`

English:
lemma variance_linearMap_gaussianReal
  given: (L : Real ->ₗ[Real] Real)
  proof: by
  rw [← variance_id_map]; rw [gaussianReal_map_linearMap]; rw [variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]

中文:
引理 variance_linearMap_gaussian实数
  条件: (L : 实数 ->ₗ[实数] 实数)
  证明: by
  rw [← variance_id_map]; rw [gaussianReal_map_linearMap]; rw [variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_mul, Real.coe_toNNReal, coe_mul, coe_toNNReal, fun_prop, gaussianReal_map_linearMap, variance_id_gaussianReal, variance_id_map
-/
lemma variance_linearMap_gaussianReal (L : Real ->ₗ[Real] Real) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v := by
  rw [← variance_id_map]; rw [gaussianReal_map_linearMap]; rw [variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]
/--
lemma `variance_continuousLinearMap_gaussianReal` / 引理 `variance_continuousLinearMap_gaussianReal`

English:
lemma variance_continuousLinearMap_gaussianReal
  given: (L : Real ->L[Real] Real)
  proof: variance_linearMap_gaussianReal L

中文:
引理 variance_continuousLinearMap_gaussian实数
  条件: (L : 实数 ->L[实数] 实数)
  证明: variance_linearMap_gaussianReal L

Depends on / 依赖: variance_linearMap_gaussianReal
-/
lemma variance_continuousLinearMap_gaussianReal (L : Real ->L[Real] Real) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v :=
  variance_linearMap_gaussianReal L

end LinearMap

/--
lemma `gaussianReal_conv_gaussianReal` / 引理 `gaussianReal_conv_gaussianReal`

English:
lemma gaussianReal_conv_gaussianReal
  given: {m₁ m₂ : Real} {v₁ v₂ : Real>=0}
  proof: by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  ring_nf

中文:
引理 gaussian实数_conv_gaussian实数
  条件: {m₁ m₂ : 实数} {v₁ v₂ : 实数>=0}
  证明: by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  ring_nf

Depends on / 依赖: Complex.exp_add, Complex.ofReal_add, Measure, Measure.ext_of_charFun, NNReal, NNReal.coe_add, charFun_conv, charFun_gaussianReal, coe_add, exp_add, ext_of_charFun, ofReal_add, ring_nf, simp_rw
-/
lemma gaussianReal_conv_gaussianReal {m₁ m₂ : Real} {v₁ v₂ : Real>=0} :
    (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  ring_nf

/--
lemma `gaussianReal_add_gaussianReal_of_indepFun` / 引理 `gaussianReal_add_gaussianReal_of_indepFun`

English:
lemma gaussianReal_add_gaussianReal_of_indepFun
  statement: {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  proof: by
  rw [hXY.map_add_eq_map_conv_map₀']; rw [hX]; rw [hY]; rw [gaussianReal_conv_gaussianReal]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

中文:
引理 gaussian实数_add_gaussian实数_of_indepFun
  结论: {Ω} {mΩ : 可测空间 Ω} {P : 测度 Ω}
  证明: by
  rw [hXY.map_add_eq_map_conv_map₀']; rw [hX]; rw [hY]; rw [gaussianReal_conv_gaussianReal]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

Depends on / 依赖: AEMeasurable, AEMeasurable.of_map_ne_zero, IsFiniteMeasure, IsFiniteMeasure.toSigmaFinite, NeZero, NeZero.ne, gaussianReal_conv_gaussianReal, hXY.map_add_eq_map_conv_map, of_map_ne_zero, toSigmaFinite
-/
lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {m₁ m₂ : Real} {v₁ v₂ : Real>=0} {X Y : Ω -> Real} (hXY : IndepFun X Y P)
    (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  rw [hXY.map_add_eq_map_conv_map₀']; rw [hX]; rw [hY]; rw [gaussianReal_conv_gaussianReal]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

end GaussianReal

end ProbabilityTheory
