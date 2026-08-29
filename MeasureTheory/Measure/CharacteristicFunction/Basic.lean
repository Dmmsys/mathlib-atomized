/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
module

public import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space `V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

The integral is expressed as `∫ v, char he hL w v ∂P`, where `char he hL w` is the
bounded continuous function `fun v ↦ e (L v w)` and `he`, `hL` are continuity hypotheses on `e`
and `L`.

## Main definitions

* `innerProbChar`: the bounded continuous map `x ↦ exp(⟪x, t⟫ * I)` in an inner product space.
  This is `char` for the inner product bilinear map and the additive character `e = probChar`.
* `charFun μ t`: the characteristic function of a measure `μ` at `t` in an inner product space `E`.
  This is defined as `∫ x, exp (⟪x, t⟫ * I) ∂μ`, where `⟪x, t⟫` is the inner product on `E`.
  It is equal to `∫ v, innerProbChar w v ∂P` (see `charFun_eq_integral_innerProbChar`).
* `probCharDual`: the bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`.
* `charFunDual μ L`: the characteristic function of a measure `μ` at `L : Dual ℝ E` in
  a normed space `E`. This is the integral `∫ v, exp (L v * I) ∂μ`.

## Main statements

* `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
* `Measure.ext_of_charFun`: If the characteristic functions `charFun` of two finite measures
  `μ` and `ν` on a complete second-countable inner product space coincide, then `μ = ν`.
* `Measure.ext_of_charFunDual`: If the characteristic functions `charFunDual` of two finite measures
  `μ` and `ν` on a Banach space coincide, then `μ = ν`.

-/

@[expose] public section

open BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate WithLp

open scoped ENNReal

namespace BoundedContinuousFunction

variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace Real E]
  [SeminormedAddCommGroup F] [NormedSpace Real F]

/-- The bounded continuous map `x ↦ exp(⟪x, t⟫ * I)`. -/
noncomputable
/--
Definition of `innerProbChar` / `innerProbChar` 的定义

English:
definition innerProbChar
  signature: (t : E)
  body: char continuous_probChar (L := innerₗ E) continuous_inner t

中文:
定义 innerProbChar
  签名: (t : E)
  定义体: char continuous_probChar (L := innerₗ E) continuous_inner t

Depends on / 依赖: continuous_inner, continuous_probChar
-/
def innerProbChar (t : E) : E ->ᵇ Complex :=
  char continuous_probChar (L := innerₗ E) continuous_inner t

/--
lemma `innerProbChar_apply` / 引理 `innerProbChar_apply`

English:
lemma innerProbChar_apply
  given: (t x : E)
  statement: innerProbChar t x = exp (⟪x, t⟫ * I)
  proof: rfl

中文:
引理 innerProbChar_apply
  条件: (t x : E)
  结论: innerProbChar t x = exp (⟪x, t⟫ * I)
  证明: rfl
-/
lemma innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `innerProbChar_zero` / 引理 `innerProbChar_zero`

English:
lemma innerProbChar_zero
  statement: innerProbChar (0 : E) = 1
  proof: by simp [innerProbChar]

中文:
引理 innerProbChar_zero
  结论: innerProbChar (0 : E) = 1
  证明: by simp [innerProbChar]

Depends on / 依赖: innerProbChar
-/
lemma innerProbChar_zero : innerProbChar (0 : E) = 1 := by simp [innerProbChar]

/-- The bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`. -/
noncomputable
/--
Definition of `probCharDual` / `probCharDual` 的定义

English:
definition probCharDual
  signature: (L : StrongDual Real F)
  body: char continuous_probChar
    (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂)
    isBoundedBilinearMap_apply.symm.continuous L

中文:
定义 probCharDual
  签名: (L : StrongDual 实数 F)
  定义体: char continuous_probChar
    (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂)
    isBoundedBilinearMap_apply.symm.continuous L

Depends on / 依赖: continuous, continuous_probChar, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.symm.continuous, isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap, toContinuousLinearMap
-/
def probCharDual (L : StrongDual Real F) : F ->ᵇ Complex :=
  char continuous_probChar
    (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂)
    isBoundedBilinearMap_apply.symm.continuous L

/--
lemma `probCharDual_apply` / 引理 `probCharDual_apply`

English:
lemma probCharDual_apply
  given: (L : StrongDual Real F) (x : F)
  statement: probCharDual L x = exp (L x * I)
  proof: rfl

中文:
引理 probCharDual_apply
  条件: (L : StrongDual 实数 F) (x : F)
  结论: probCharDual L x = exp (L x * I)
  证明: rfl
-/
lemma probCharDual_apply (L : StrongDual Real F) (x : F) : probCharDual L x = exp (L x * I) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `probCharDual_zero` / 引理 `probCharDual_zero`

English:
lemma probCharDual_zero
  statement: probCharDual (0 : StrongDual Real F) = 1
  proof: by simp [probCharDual]

中文:
引理 probCharDual_zero
  结论: probCharDual (0 : StrongDual 实数 F) = 1
  证明: by simp [probCharDual]

Depends on / 依赖: probCharDual
-/
lemma probCharDual_zero : probCharDual (0 : StrongDual Real F) = 1 := by simp [probCharDual]

end BoundedContinuousFunction

namespace MeasureTheory

variable {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    {e : AddChar Real Circle}

section ext

variable {V : Type*} [AddCommGroup V] [Module Real V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V ->ₗ[Real] W ->ₗ[Real] Real}

/--
theorem `ext_of_integral_char_eq` / 定理 `ext_of_integral_char_eq`

English:
theorem ext_of_integral_char_eq
  statement: (he : Continuous e) (he' : e != 1)
  proof: by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, w.coeff.sum (fun a z => z

中文:
定理 ext_of_integral_char_eq
  结论: (he : Continuous e) (he' : e != 1)
  证明: by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, w.coeff.sum (fun a z => z

Depends on / 依赖: Finset, Finset.sum_congr, IsFiniteMeasure, Measure, const_mul, ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable, integrable, integral_finsetSum, mem_charPoly, separatesPoints_charPoly, sum_congr, w.coeff.sum
-/
theorem ext_of_integral_char_eq (he : Continuous e) (he' : e != 1)
    (hL' : forall v != 0, L v != 0) (hL : Continuous fun p : V × W => L p.1 p.2)
    {P P' : Measure V} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : forall w, ∫ v, char he hL w v ∂P = ∫ v, char he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, w.coeff.sum (fun a z => z * e (L v a)) ∂P =
        w.coeff.sum (fun a z => ∫ v, z * e (L v a) ∂P) :=
    integral_finsetSum _ fun a ha => ((char he hL a).integrable P).const_mul _
  rw [hsum P]; rw [hsum P']
  apply Finset.sum_congr rfl fun i _ => ?_
  simp only [MeasureTheory.integral_const_mul, mul_eq_mul_left_iff]
  exact Or.inl (h i)

end ext

section InnerProductSpace

variable {E : Type*} {mE : MeasurableSpace E} {μ : Measure E} {t : E}

/--
Definition of `charFun` / `charFun` 的定义

English:
definition charFun
  signature: [Inner Real E] (μ : Measure E) (t : E)
  body: ∫ x, exp (⟪x, t⟫ * I) ∂μ

中文:
定义 charFun
  签名: [Inner 实数 E] (μ : Measure E) (t : E)
  定义体: ∫ x, exp (⟪x, t⟫ * I) ∂μ
-/
noncomputable def charFun [Inner Real E] (μ : Measure E) (t : E) : Complex := ∫ x, exp (⟪x, t⟫ * I) ∂μ

/--
lemma `charFun_apply` / 引理 `charFun_apply`

English:
lemma charFun_apply
  given: [Inner Real E] (t : E)
  statement: charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
  proof: rfl

中文:
引理 charFun_apply
  条件: [Inner 实数 E] (t : E)
  结论: charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
  证明: rfl
-/
lemma charFun_apply [Inner Real E] (t : E) : charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ := rfl

/--
lemma `charFun_apply_real` / 引理 `charFun_apply_real`

English:
lemma charFun_apply_real
  given: {μ : Measure Real} (t : Real)
  proof: by simp [charFun_apply]

中文:
引理 charFun_apply_real
  条件: {μ : Measure 实数} (t : 实数)
  证明: by simp [charFun_apply]

Depends on / 依赖: charFun_apply
-/
lemma charFun_apply_real {μ : Measure Real} (t : Real) :
    charFun μ t = ∫ x, exp (t * x * I) ∂μ := by simp [charFun_apply]

variable [SeminormedAddCommGroup E] [InnerProductSpace Real E]

@[simp]
/--
lemma `charFun_zero` / 引理 `charFun_zero`

English:
lemma charFun_zero
  given: (μ : Measure E)
  statement: charFun μ 0 = μ.real Set.univ
  proof: by
  simp [charFun_apply]

@[simp]

中文:
引理 charFun_zero
  条件: (μ : Measure E)
  结论: charFun μ 0 = μ.real Set.univ
  证明: by
  simp [charFun_apply]

@[simp]

Depends on / 依赖: charFun_apply
-/
lemma charFun_zero (μ : Measure E) : charFun μ 0 = μ.real Set.univ := by
  simp [charFun_apply]

@[simp]
/--
lemma `charFun_zero_measure` / 引理 `charFun_zero_measure`

English:
lemma charFun_zero_measure
  statement: charFun (0 : Measure E) t = 0
  proof: by simp [charFun_apply]

@[simp]

中文:
引理 charFun_zero_measure
  结论: charFun (0 : Measure E) t = 0
  证明: by simp [charFun_apply]

@[simp]

Depends on / 依赖: charFun_apply
-/
lemma charFun_zero_measure : charFun (0 : Measure E) t = 0 := by simp [charFun_apply]

@[simp]
/--
lemma `charFun_neg` / 引理 `charFun_neg`

English:
lemma charFun_neg
  given: (t : E)
  statement: charFun μ (-t) = conj (charFun μ t)
  proof: by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

中文:
引理 charFun_neg
  条件: (t : E)
  结论: charFun μ (-t) = conj (charFun μ t)
  证明: by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

Depends on / 依赖: charFun_apply, exp_conj, integral_conj
-/
lemma charFun_neg (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

/--
lemma `charFun_eq_integral_innerProbChar` / 引理 `charFun_eq_integral_innerProbChar`

English:
lemma charFun_eq_integral_innerProbChar
  statement: charFun μ t = ∫ v, innerProbChar t v ∂μ
  proof: by
  simp [charFun_apply, innerProbChar_apply]

中文:
引理 charFun_eq_integral_innerProbChar
  结论: charFun μ t = ∫ v, innerProbChar t v ∂μ
  证明: by
  simp [charFun_apply, innerProbChar_apply]

Depends on / 依赖: charFun_apply, innerProbChar_apply
-/
lemma charFun_eq_integral_innerProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ := by
  simp [charFun_apply, innerProbChar_apply]

/--
lemma `charFun_eq_integral_probChar` / 引理 `charFun_eq_integral_probChar`

English:
lemma charFun_eq_integral_probChar
  given: (t : E)
  statement: charFun μ t = ∫ x, (probChar ⟪x, t⟫ : Complex) ∂μ
  proof: by
  simp [charFun_apply, probChar_apply]

中文:
引理 charFun_eq_integral_probChar
  条件: (t : E)
  结论: charFun μ t = ∫ x, (probChar ⟪x, t⟫ : Complex) ∂μ
  证明: by
  simp [charFun_apply, probChar_apply]

Depends on / 依赖: charFun_apply, probChar_apply
-/
lemma charFun_eq_integral_probChar (t : E) : charFun μ t = ∫ x, (probChar ⟪x, t⟫ : Complex) ∂μ := by
  simp [charFun_apply, probChar_apply]

/--
lemma `charFun_eq_fourierIntegral` / 引理 `charFun_eq_fourierIntegral`

English:
lemma charFun_eq_fourierIntegral
  given: (t : E)
  proof: by
  simp [charFun_apply, VectorFourier.fourierIntegral_probChar]

中文:
引理 charFun_eq_fourierIntegral
  条件: (t : E)
  证明: by
  simp [charFun_apply, VectorFourier.fourierIntegral_probChar]

Depends on / 依赖: VectorFourier, VectorFourier.fourierIntegral_probChar, charFun_apply, fourierIntegral_probChar
-/
lemma charFun_eq_fourierIntegral (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probChar μ (innerₗ E) 1 (-t) := by
  simp [charFun_apply, VectorFourier.fourierIntegral_probChar]

/--
lemma `charFun_eq_fourierIntegral'` / 引理 `charFun_eq_fourierIntegral'`

English:
lemma charFun_eq_fourierIntegral'
  given: (t : E)
  proof: by
  simp only [charFun_apply, VectorFourier.fourierIntegral, neg_smul,
    innerₗ_apply_apply, inner_neg_right, inner_smul_right, neg_neg,
    fourierChar_apply', Pi.ofNat_apply, Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat,
    ofReal_inv, smul_eq_mul, mul_one]
  congr with x
  rw [← 

中文:
引理 charFun_eq_fourierIntegral'
  条件: (t : E)
  证明: by
  simp only [charFun_apply, VectorFourier.fourierIntegral, neg_smul,
    innerₗ_apply_apply, inner_neg_right, inner_smul_right, neg_neg,
    fourierChar_apply', Pi.ofNat_apply, Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat,
    ofReal_inv, smul_eq_mul, mul_one]
  congr with x
  rw [← 

Depends on / 依赖: Circle, Circle.coe_exp, Circle.smul_def, Pi.ofNat_apply, VectorFourier, VectorFourier.fourierIntegral, charFun_apply, coe_exp, fourierChar_apply, fourierIntegral, inner_neg_right, inner_smul_right, mul_assoc, mul_one, neg_neg, neg_smul, ofNat_apply, ofReal_inv, ofReal_mul, ofReal_ofNat
-/
lemma charFun_eq_fourierIntegral' (t : E) :
    charFun μ t
      = VectorFourier.fourierIntegral fourierChar μ (innerₗ E) 1 (-(2 * π)⁻¹ • t) := by
  simp only [charFun_apply, VectorFourier.fourierIntegral, neg_smul,
    innerₗ_apply_apply, inner_neg_right, inner_smul_right, neg_neg,
    fourierChar_apply', Pi.ofNat_apply, Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat,
    ofReal_inv, smul_eq_mul, mul_one]
  congr with x
  rw [← mul_assoc]; rw [mul_inv_cancel₀ (by simp [pi_ne_zero]), one_mul]

/--
lemma `norm_charFun_le` / 引理 `norm_charFun_le`

English:
lemma norm_charFun_le
  given: (t : E)
  statement: ‖charFun μ t‖ <= μ.real Set.univ
  proof: by
  rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq (by simp)

中文:
引理 norm_charFun_le
  条件: (t : E)
  结论: ‖charFun μ t‖ <= μ.real Set.univ
  证明: by
  rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq (by simp)

Depends on / 依赖: VectorFourier, VectorFourier.norm_fourierIntegral_le_integral_norm, charFun_eq_fourierIntegral, norm_fourierIntegral_le_integral_norm, trans_eq
-/
lemma norm_charFun_le (t : E) : ‖charFun μ t‖ <= μ.real Set.univ := by
  rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq (by simp)

/--
lemma `norm_charFun_le_one` / 引理 `norm_charFun_le_one`

English:
lemma norm_charFun_le_one
  given: [IsProbabilityMeasure μ] (t : E)
  statement: ‖charFun μ t‖ <= 1
  proof: (norm_charFun_le _).trans_eq (by simp)

中文:
引理 norm_charFun_le_one
  条件: [IsProbabilityMeasure μ] (t : E)
  结论: ‖charFun μ t‖ <= 1
  证明: (norm_charFun_le _).trans_eq (by simp)

Depends on / 依赖: norm_charFun_le, trans_eq
-/
lemma norm_charFun_le_one [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ <= 1 :=
  (norm_charFun_le _).trans_eq (by simp)

/--
lemma `norm_one_sub_charFun_le_two` / 引理 `norm_one_sub_charFun_le_two`

English:
lemma norm_one_sub_charFun_le_two
  given: [IsProbabilityMeasure μ]
  statement: ‖1 - charFun μ t‖ <= 2
  proof: calc ‖1 - charFun μ t‖
  _ <= ‖(1 : Complex)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ <= 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

@[fun_prop]

中文:
引理 norm_one_sub_charFun_le_two
  条件: [IsProbabilityMeasure μ]
  结论: ‖1 - charFun μ t‖ <= 2
  证明: calc ‖1 - charFun μ t‖
  _ <= ‖(1 : Complex)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ <= 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

@[fun_prop]

Depends on / 依赖: charFun, norm_charFun_le_one, norm_sub_le
-/
lemma norm_one_sub_charFun_le_two [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ <= 2 :=
  calc ‖1 - charFun μ t‖
  _ <= ‖(1 : Complex)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ <= 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

@[fun_prop]
/--
lemma `stronglyMeasurable_charFun` / 引理 `stronglyMeasurable_charFun`

English:
lemma stronglyMeasurable_charFun
  given: [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ]
  proof: (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop]

中文:
引理 stronglyMeasurable_charFun
  条件: [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ]
  证明: (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.stronglyMeasurable, fun_prop, integral_prod_left, stronglyMeasurable
-/
lemma stronglyMeasurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    StronglyMeasurable (charFun μ) :=
  (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop]
/--
lemma `measurable_charFun` / 引理 `measurable_charFun`

English:
lemma measurable_charFun
  given: [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ]
  proof: stronglyMeasurable_charFun.measurable

中文:
引理 measurable_charFun
  条件: [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ]
  证明: stronglyMeasurable_charFun.measurable

Depends on / 依赖: measurable, stronglyMeasurable_charFun, stronglyMeasurable_charFun.measurable
-/
lemma measurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    Measurable (charFun μ) :=
  stronglyMeasurable_charFun.measurable

/--
lemma `intervalIntegrable_charFun` / 引理 `intervalIntegrable_charFun`

English:
lemma intervalIntegrable_charFun
  given: {μ : Measure Real} [IsFiniteMeasure μ] {a b : Real}
  proof: IntervalIntegrable.mono_fun' (g := fun _ => μ.real Set.univ) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)

中文:
引理 intervalIntegrable_charFun
  条件: {μ : Measure 实数} [IsFiniteMeasure μ] {a b : 实数}
  证明: IntervalIntegrable.mono_fun' (g := fun _ => μ.real Set.univ) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.mono_fun, Set.univ, ae_of_all, aestronglyMeasurable, mono_fun, norm_charFun_le, stronglyMeasurable_charFun, stronglyMeasurable_charFun.aestronglyMeasurable
-/
lemma intervalIntegrable_charFun {μ : Measure Real} [IsFiniteMeasure μ] {a b : Real} :
    IntervalIntegrable (charFun μ) volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => μ.real Set.univ) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)

/--
lemma `charFun_map_smul` / 引理 `charFun_map_smul`

English:
lemma charFun_map_smul
  given: [BorelSpace E] (r : Real) (t : E)
  proof: by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_smul_right, ← real_inner_smul_left]

中文:
引理 charFun_map_smul
  条件: [BorelSpace E] (r : 实数) (t : E)
  证明: by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_smul_right, ← real_inner_smul_left]

Depends on / 依赖: charFun_apply, fun_prop, inner_smul_right, integral_map, real_inner_smul_left, simp_rw
-/
lemma charFun_map_smul [BorelSpace E] (r : Real) (t : E) :
    charFun (μ.map (r • ·)) t = charFun μ (r • t) := by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_smul_right, ← real_inner_smul_left]

/--
lemma `charFun_map_smul_comp` / 引理 `charFun_map_smul_comp`

English:
lemma charFun_map_smul_comp
  statement: {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} [BorelSpace E]
  proof: by
  rw [show (fun x => r • (f x)) = (r • ·) ∘ f from rfl]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [charFun_map_smul]
  all_goals fun_prop

中文:
引理 charFun_map_smul_comp
  结论: {X : 类型} {mX : MeasurableSpace X} {μ : Measure X} [BorelSpace E]
  证明: by
  rw [show (fun x => r • (f x)) = (r • ·) ∘ f from rfl]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [charFun_map_smul]
  all_goals fun_prop

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, all_goals, charFun_map_smul, fun_prop, map_map_of_aemeasurable
-/
lemma charFun_map_smul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} [BorelSpace E]
    {f : X -> E} (hf : AEMeasurable f μ) (r : Real) (t : E) :
    charFun (μ.map (fun x => r • (f x))) t = charFun (μ.map f) (r • t) := by
  rw [show (fun x => r • (f x)) = (r • ·) ∘ f from rfl]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [charFun_map_smul]
  all_goals fun_prop

/--
lemma `charFun_map_mul` / 引理 `charFun_map_mul`

English:
lemma charFun_map_mul
  given: {μ : Measure Real} (r t : Real)
  proof: charFun_map_smul r t

中文:
引理 charFun_map_mul
  条件: {μ : Measure 实数} (r t : 实数)
  证明: charFun_map_smul r t

Depends on / 依赖: charFun_map_smul
-/
lemma charFun_map_mul {μ : Measure Real} (r t : Real) :
    charFun (μ.map (r * ·)) t = charFun μ (r * t) := charFun_map_smul r t

/--
lemma `charFun_map_mul_comp` / 引理 `charFun_map_mul_comp`

English:
lemma charFun_map_mul_comp
  statement: {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
  proof: charFun_map_smul_comp hf r t

中文:
引理 charFun_map_mul_comp
  结论: {X : 类型} {mX : MeasurableSpace X} {μ : Measure X}
  证明: charFun_map_smul_comp hf r t

Depends on / 依赖: charFun_map_smul_comp
-/
lemma charFun_map_mul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    {f : X -> Real} (hf : AEMeasurable f μ) (r t : Real) :
    charFun (μ.map (fun x => r * (f x))) t = charFun (μ.map f) (r * t) :=
  charFun_map_smul_comp hf r t

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

@[simp]
/--
lemma `charFun_dirac` / 引理 `charFun_dirac`

English:
lemma charFun_dirac
  given: [OpensMeasurableSpace E] {x : E} (t : E)
  proof: by
  rw [charFun_apply]; rw [integral_dirac]

中文:
引理 charFun_dirac
  条件: [OpensMeasurableSpace E] {x : E} (t : E)
  证明: by
  rw [charFun_apply]; rw [integral_dirac]

Depends on / 依赖: charFun_apply, integral_dirac
-/
lemma charFun_dirac [OpensMeasurableSpace E] {x : E} (t : E) :
    charFun (Measure.dirac x) t = cexp (⟪x, t⟫ * I) := by
  rw [charFun_apply]; rw [integral_dirac]

/--
lemma `charFun_map_add_const` / 引理 `charFun_map_add_const`

English:
lemma charFun_map_add_const
  given: [BorelSpace E] (r t : E)
  proof: by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  rw [inner_add_left]
  simp only [ofReal_add]
  ring

中文:
引理 charFun_map_add_const
  条件: [BorelSpace E] (r t : E)
  证明: by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  rw [inner_add_left]
  simp only [ofReal_add]
  ring

Depends on / 依赖: Complex.exp_add, charFun_apply, exp_add, fun_prop, inner_add_left, integral_map, integral_mul_const, ofReal_add
-/
lemma charFun_map_add_const [BorelSpace E] (r t : E) :
    charFun (μ.map (· + r)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  rw [charFun_apply]; rw [charFun_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  rw [inner_add_left]
  simp only [ofReal_add]
  ring

/--
lemma `charFun_map_const_add` / 引理 `charFun_map_const_add`

English:
lemma charFun_map_const_add
  given: [BorelSpace E] (r t : E)
  proof: by
  simp_rw [add_comm r]
  exact charFun_map_add_const _ _

中文:
引理 charFun_map_const_add
  条件: [BorelSpace E] (r t : E)
  证明: by
  simp_rw [add_comm r]
  exact charFun_map_add_const _ _

Depends on / 依赖: add_comm, charFun_map_add_const, simp_rw
-/
lemma charFun_map_const_add [BorelSpace E] (r t : E) :
    charFun (μ.map (r + ·)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  simp_rw [add_comm r]
  exact charFun_map_add_const _ _

variable [BorelSpace E] [SecondCountableTopology E]

/--
theorem `Measure.ext_of_charFun` / 定理 `Measure.ext_of_charFun`

English:
theorem Measure.ext_of_charFun
  statement: [CompleteSpace E]
  proof: by
  simp_rw [funext_iff, charFun_eq_integral_innerProbChar] at h
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one (L := innerₗ E)
    ?_ ?_ h
  · exact fun v hv => DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner

中文:
定理 Measure.ext_of_charFun
  结论: [CompleteSpace E]
  证明: by
  simp_rw [funext_iff, charFun_eq_integral_innerProbChar] at h
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one (L := innerₗ E)
    ?_ ?_ h
  · exact fun v hv => DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mpr, charFun_eq_integral_innerProbChar, continuous_inner, continuous_probChar, ext_of_integral_char_eq, funext_iff, inner_self_ne_zero, inner_self_ne_zero.mpr, ne_iff, probChar_ne_one, simp_rw
-/
theorem Measure.ext_of_charFun [CompleteSpace E]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFun μ = charFun ν) :
    μ = ν := by
  simp_rw [funext_iff, charFun_eq_integral_innerProbChar] at h
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one (L := innerₗ E)
    ?_ ?_ h
  · exact fun v hv => DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner

/--
lemma `charFun_conv` / 引理 `charFun_conv`

English:
lemma charFun_conv
  given: [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E)
  proof: by
  simp_rw [charFun_apply]
  rw [integral_conv]
  · simp [inner_add_left, add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

中文:
引理 charFun_conv
  条件: [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E)
  证明: by
  simp_rw [charFun_apply]
  rw [integral_conv]
  · simp [inner_add_left, add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

Depends on / 依赖: Complex.exp_add, add_mul, charFun_apply, exp_add, fun_prop, inner_add_left, integrable_const, integral_const_mul, integral_conv, integral_mul_const, simp_rw
-/
lemma charFun_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  simp_rw [charFun_apply]
  rw [integral_conv]
  · simp [inner_add_left, add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace Real E] [InnerProductSpace Real F] {mE : MeasurableSpace E}
    {mF : MeasurableSpace F}

/--
lemma `charFun_prod` / 引理 `charFun_prod`

English:
lemma charFun_prod
  statement: {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
  proof: by
  simp_rw [charFun, prod_inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_prod_mul,
    integral_map_equiv]
  simp [ofReal_add, add_mul, Complex.exp_add]

中文:
引理 charFun_prod
  结论: {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
  证明: by
  simp_rw [charFun, prod_inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_prod_mul,
    integral_map_equiv]
  simp [ofReal_add, add_mul, Complex.exp_add]

Depends on / 依赖: Complex.exp_add, MeasurableEquiv, MeasurableEquiv.coe_toLp, add_mul, charFun, coe_toLp, exp_add, integral_map_equiv, integral_prod_mul, ofReal_add, prod_inner_apply, simp_rw
-/
lemma charFun_prod {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    (t : WithLp 2 (E × F)) :
    charFun ((μ.prod ν).map (toLp 2)) t =
      charFun μ (ofLp t).1 * charFun ν (ofLp t).2 := by
  simp_rw [charFun, prod_inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_prod_mul,
    integral_map_equiv]
  simp [ofReal_add, add_mul, Complex.exp_add]

variable [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    [BorelSpace E] [BorelSpace F]

/--
lemma `charFun_eq_prod_iff` / 引理 `charFun_eq_prod_iff`

English:
lemma charFun_eq_prod_iff
  statement: {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)}
  proof: by
    refine (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_prod]
  mpr h := by rw [h]; exact charFun_prod

中文:
引理 charFun_eq_prod_iff
  结论: {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)}
  证明: by
    refine (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_prod]
  mpr h := by rw [h]; exact charFun_prod

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, Measure, Measure.ext_of_charFun, charFun_prod, coe_toLp, ext_of_charFun, map_measurableEquiv_injective
-/
lemma charFun_eq_prod_iff {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (forall t, charFun (ξ.map (toLp 2)) t = charFun μ (ofLp t).1 * charFun ν (ofLp t).2) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_prod]
  mpr h := by rw [h]; exact charFun_prod

variable {ι : Type*} [Fintype ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)]
    [forall i, InnerProductSpace Real (E i)] {mE : forall i, MeasurableSpace (E i)}

/--
lemma `charFun_pi` / 引理 `charFun_pi`

English:
lemma charFun_pi
  given: {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)] (t : PiLp 2 E)
  proof: by
  simp_rw [charFun, PiLp.inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
    integral_map_equiv]
  simp [ofReal_sum, Finset.sum_mul, Complex.exp_sum]

中文:
引理 charFun_pi
  条件: {μ : (i : ι) -> Measure (E i)} [对任意 i, SigmaFinite (μ i)] (t : PiLp 2 E)
  证明: by
  simp_rw [charFun, PiLp.inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
    integral_map_equiv]
  simp [ofReal_sum, Finset.sum_mul, Complex.exp_sum]

Depends on / 依赖: Complex.exp_sum, Finset, Finset.sum_mul, MeasurableEquiv, MeasurableEquiv.coe_toLp, PiLp.inner_apply, charFun, coe_toLp, exp_sum, inner_apply, integral_fintype_prod_eq_prod, integral_map_equiv, ofReal_sum, simp_rw, sum_mul
-/
lemma charFun_pi {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)] (t : PiLp 2 E) :
    charFun ((Measure.pi μ).map (toLp 2)) t = ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
    integral_map_equiv]
  simp [ofReal_sum, Finset.sum_mul, Complex.exp_sum]

variable [forall i, CompleteSpace (E i)] [forall i, SecondCountableTopology (E i)] [forall i, BorelSpace (E i)]

/--
lemma `charFun_eq_pi_iff` / 引理 `charFun_eq_pi_iff`

English:
lemma charFun_eq_pi_iff
  statement: {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)}
  proof: by
    refine (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_pi]
  mpr h := by rw [h]; exact charFun_pi

中文:
引理 charFun_eq_pi_iff
  结论: {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)}
  证明: by
    refine (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_pi]
  mpr h := by rw [h]; exact charFun_pi

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, Measure, Measure.ext_of_charFun, charFun_pi, coe_toLp, ext_of_charFun, map_measurableEquiv_injective
-/
lemma charFun_eq_pi_iff {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)}
    [forall i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (forall t, charFun (ν.map (toLp 2)) t = ∏ i, charFun (μ i) (t i)) ↔ ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFun funext fun t => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFun_pi]
  mpr h := by rw [h]; exact charFun_pi

end InnerProductSpace

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace Real F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `StrongDual ℝ E` to
`ℂ` with `charFunDual μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
/--
Definition of `charFunDual` / `charFunDual` 的定义

English:
definition charFunDual
  signature: (μ : Measure E) (L : StrongDual Real E)
  body: ∫ v, probCharDual L v ∂μ

中文:
定义 charFunDual
  签名: (μ : Measure E) (L : StrongDual 实数 E)
  定义体: ∫ v, probCharDual L v ∂μ

Depends on / 依赖: probCharDual
-/
def charFunDual (μ : Measure E) (L : StrongDual Real E) : Complex := ∫ v, probCharDual L v ∂μ

/--
lemma `charFunDual_apply` / 引理 `charFunDual_apply`

English:
lemma charFunDual_apply
  given: (L : StrongDual Real E)
  statement: charFunDual μ L = ∫ v, exp (L v * I) ∂μ
  proof: rfl

中文:
引理 charFunDual_apply
  条件: (L : StrongDual 实数 E)
  结论: charFunDual μ L = ∫ v, exp (L v * I) ∂μ
  证明: rfl
-/
lemma charFunDual_apply (L : StrongDual Real E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ := rfl

/--
lemma `charFunDual_eq_charFun_map_one` / 引理 `charFunDual_eq_charFun_map_one`

English:
lemma charFunDual_eq_charFun_map_one
  given: [OpensMeasurableSpace E] (L : StrongDual Real E)
  proof: by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

中文:
引理 charFunDual_eq_charFun_map_one
  条件: [OpensMeasurableSpace E] (L : StrongDual 实数 E)
  证明: by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aestronglyMeasurable, charFunDual_apply, charFun_apply, fun_prop, integral_map
-/
lemma charFunDual_eq_charFun_map_one [OpensMeasurableSpace E] (L : StrongDual Real E) :
    charFunDual μ L = charFun (μ.map L) 1 := by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

/--
lemma `charFun_map_eq_charFunDual_smul` / 引理 `charFun_map_eq_charFunDual_smul`

English:
lemma charFun_map_eq_charFunDual_smul
  given: [OpensMeasurableSpace E] (L : StrongDual Real E) (u : Real)
  proof: by
  rw [charFunDual_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

中文:
引理 charFun_map_eq_charFunDual_smul
  条件: [OpensMeasurableSpace E] (L : StrongDual 实数 E) (u : 实数)
  证明: by
  rw [charFunDual_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, aestronglyMeasurable, charFunDual_apply, charFun_apply, fun_prop, integral_map
-/
lemma charFun_map_eq_charFunDual_smul [OpensMeasurableSpace E] (L : StrongDual Real E) (u : Real) :
    charFun (μ.map L) u = charFunDual μ (u • L) := by
  rw [charFunDual_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
· exact Measurable.aestronglyMeasurable by fun_prop
  rw [this]; rw [charFun_apply]
  simp

/--
lemma `charFun_eq_charFunDual_toDualMap` / 引理 `charFun_eq_charFunDual_toDualMap`

English:
lemma charFun_eq_charFunDual_toDualMap
  statement: {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  proof: by
  simp [charFunDual_apply, charFun_apply, real_inner_comm]

@[simp]

中文:
引理 charFun_eq_charFunDual_toDualMap
  结论: {E : 类型} [NormedAddCommGroup E] [InnerProductSpace 实数 E]
  证明: by
  simp [charFunDual_apply, charFun_apply, real_inner_comm]

@[simp]

Depends on / 依赖: charFunDual_apply, charFun_apply, real_inner_comm
-/
lemma charFun_eq_charFunDual_toDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {mE : MeasurableSpace E} {μ : Measure E} (t : E) :
    charFun μ t = charFunDual μ (InnerProductSpace.toDualMap Real E t) := by
  simp [charFunDual_apply, charFun_apply, real_inner_comm]

@[simp]
/--
lemma `charFun_toDual_symm_eq_charFunDual` / 引理 `charFun_toDual_symm_eq_charFunDual`

English:
lemma charFun_toDual_symm_eq_charFunDual
  statement: {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  proof: by
  rw [charFun_eq_charFunDual_toDualMap]; rw [← InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  simp

中文:
引理 charFun_toDual_symm_eq_charFunDual
  结论: {E : 类型} [NormedAddCommGroup E] [CompleteSpace E]
  证明: by
  rw [charFun_eq_charFunDual_toDualMap]; rw [← InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  simp

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toDual_apply_eq_toDualMap_apply, charFun_eq_charFunDual_toDualMap, toDual_apply_eq_toDualMap_apply
-/
lemma charFun_toDual_symm_eq_charFunDual {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace Real E] {mE : MeasurableSpace E} {μ : Measure E} (L : StrongDual Real E) :
    charFun μ ((InnerProductSpace.toDual Real E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap]; rw [← InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  simp

/--
lemma `charFunDual_map` / 引理 `charFunDual_map`

English:
lemma charFunDual_map
  statement: [OpensMeasurableSpace E] [BorelSpace F] (L : E ->L[Real] F)
  proof: by
  rw [charFunDual_eq_charFun_map_one]; rw [charFunDual_eq_charFun_map_one]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rw [ContinuousLinearMap.coe_comp]

@[simp]

中文:
引理 charFunDual_map
  结论: [OpensMeasurableSpace E] [BorelSpace F] (L : E ->L[实数] F)
  证明: by
  rw [charFunDual_eq_charFun_map_one]; rw [charFunDual_eq_charFun_map_one]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rw [ContinuousLinearMap.coe_comp]

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_comp, Measure, Measure.map_map, charFunDual_eq_charFun_map_one, coe_comp, fun_prop, map_map
-/
lemma charFunDual_map [OpensMeasurableSpace E] [BorelSpace F] (L : E ->L[Real] F)
    (L' : StrongDual Real F) : charFunDual (μ.map L) L' = charFunDual μ (L'.comp L) := by
  rw [charFunDual_eq_charFun_map_one]; rw [charFunDual_eq_charFun_map_one]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rw [ContinuousLinearMap.coe_comp]

@[simp]
/--
lemma `charFunDual_dirac` / 引理 `charFunDual_dirac`

English:
lemma charFunDual_dirac
  given: [OpensMeasurableSpace E] {x : E} (L : StrongDual Real E)
  proof: by
  rw [charFunDual_apply]; rw [integral_dirac]

中文:
引理 charFunDual_dirac
  条件: [OpensMeasurableSpace E] {x : E} (L : StrongDual 实数 E)
  证明: by
  rw [charFunDual_apply]; rw [integral_dirac]

Depends on / 依赖: charFunDual_apply, integral_dirac
-/
lemma charFunDual_dirac [OpensMeasurableSpace E] {x : E} (L : StrongDual Real E) :
    charFunDual (Measure.dirac x) L = cexp (L x * I) := by
  rw [charFunDual_apply]; rw [integral_dirac]

/--
lemma `charFunDual_map_add_const` / 引理 `charFunDual_map_add_const`

English:
lemma charFunDual_map_add_const
  given: [BorelSpace E] (r : E) (L : StrongDual Real E)
  proof: by
  rw [charFunDual_apply]; rw [charFunDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  simp only [map_add, ofReal_add]
  ring

中文:
引理 charFunDual_map_add_const
  条件: [BorelSpace E] (r : E) (L : StrongDual 实数 E)
  证明: by
  rw [charFunDual_apply]; rw [charFunDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  simp only [map_add, ofReal_add]
  ring

Depends on / 依赖: Complex.exp_add, charFunDual_apply, exp_add, fun_prop, integral_map, integral_mul_const, map_add, ofReal_add
-/
lemma charFunDual_map_add_const [BorelSpace E] (r : E) (L : StrongDual Real E) :
    charFunDual (μ.map (· + r)) L = charFunDual μ L * cexp (L r * I) := by
  rw [charFunDual_apply]; rw [charFunDual_apply]; rw [integral_map (by fun_prop) (by fun_prop)]; rw [← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  simp only [map_add, ofReal_add]
  ring

/--
lemma `charFunDual_map_const_add` / 引理 `charFunDual_map_const_add`

English:
lemma charFunDual_map_const_add
  given: [BorelSpace E] (r : E) (L : StrongDual Real E)
  proof: by
  simp_rw [add_comm r]
  exact charFunDual_map_add_const _ _

中文:
引理 charFunDual_map_const_add
  条件: [BorelSpace E] (r : E) (L : StrongDual 实数 E)
  证明: by
  simp_rw [add_comm r]
  exact charFunDual_map_add_const _ _

Depends on / 依赖: add_comm, charFunDual_map_add_const, simp_rw
-/
lemma charFunDual_map_const_add [BorelSpace E] (r : E) (L : StrongDual Real E) :
    charFunDual (μ.map (r + ·)) L = charFunDual μ L * cexp (L r * I) := by
  simp_rw [add_comm r]
  exact charFunDual_map_add_const _ _

/--
lemma `charFunDual_prod` / 引理 `charFunDual_prod`

English:
lemma charFunDual_prod
  given: [SFinite μ] [SFinite ν] (L : StrongDual Real (E × F))
  proof: by
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add, ← integral_prod_mul]

中文:
引理 charFunDual_prod
  条件: [SFinite μ] [SFinite ν] (L : StrongDual 实数 (E × F))
  证明: by
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add, ← integral_prod_mul]

Depends on / 依赖: Complex.exp_add, L.comp_inl_add_comp_inr, add_mul, charFunDual_apply, comp_inl_add_comp_inr, exp_add, integral_prod_mul, ofReal_add, simp_rw
-/
lemma charFunDual_prod [SFinite μ] [SFinite ν] (L : StrongDual Real (E × F)) :
    charFunDual (μ.prod ν) L
      = charFunDual μ (L.comp (.inl Real E F)) * charFunDual ν (L.comp (.inr Real E F)) := by
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add, ← integral_prod_mul]

/--
lemma `charFunDual_prod'` / 引理 `charFunDual_prod'`

English:
lemma charFunDual_prod'
  statement: (p : Real>=0∞) [Fact (1 <= p)] [SFinite μ] [SFinite ν]
  proof: by
  simp_rw [charFunDual_apply, ← integral_prod_mul, ← Complex.exp_add, ← add_mul, ← ofReal_add,
    L.comp_apply, ← map_add, ContinuousLinearMap.comp_inl_add_comp_inr]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

中文:
引理 charFunDual_prod'
  结论: (p : 实数>=0∞) [Fact (1 <= p)] [SFinite μ] [SFinite ν]
  证明: by
  simp_rw [charFunDual_apply, ← integral_prod_mul, ← Complex.exp_add, ← add_mul, ← ofReal_add,
    L.comp_apply, ← map_add, ContinuousLinearMap.comp_inl_add_comp_inr]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

Depends on / 依赖: Complex.exp_add, ContinuousLinearMap, ContinuousLinearMap.comp_inl_add_comp_inr, L.comp_apply, MeasurableEquiv, MeasurableEquiv.coe_toLp, add_mul, charFunDual_apply, coe_toLp, comp_apply, comp_inl_add_comp_inr, exp_add, integral_map_equiv, integral_prod_mul, map_add, ofReal_add, simp_rw
-/
lemma charFunDual_prod' (p : Real>=0∞) [Fact (1 <= p)] [SFinite μ] [SFinite ν]
    (L : StrongDual Real (WithLp p (E × F))) :
    charFunDual ((μ.prod ν).map (toLp p)) L =
      charFunDual μ (L.comp
        ((prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inl Real E F))) *
      charFunDual ν (L.comp
        ((prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inr Real E F))) := by
  simp_rw [charFunDual_apply, ← integral_prod_mul, ← Complex.exp_add, ← add_mul, ← ofReal_add,
    L.comp_apply, ← map_add, ContinuousLinearMap.comp_inl_add_comp_inr]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

/--
lemma `charFunDual_pi` / 引理 `charFunDual_pi`

English:
lemma charFunDual_pi
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*}
  proof: by
  simp_rw [charFunDual_apply, ← L.sum_comp_single, ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← integral_fintype_prod_eq_prod]

中文:
引理 charFunDual_pi
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] {E : ι -> 类型}
  证明: by
  simp_rw [charFunDual_apply, ← L.sum_comp_single, ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← integral_fintype_prod_eq_prod]

Depends on / 依赖: Complex.exp_sum, Finset, Finset.sum_mul, L.sum_comp_single, charFunDual_apply, exp_sum, integral_fintype_prod_eq_prod, ofReal_sum, simp_rw, sum_comp_single, sum_mul
-/
lemma charFunDual_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*}
    [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)] {mE : forall i, MeasurableSpace (E i)}
    {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)] (L : StrongDual Real (Π i, E i)) :
    charFunDual (Measure.pi μ) L =
      ∏ i, charFunDual (μ i) (L.comp (.single Real E i)) := by
  simp_rw [charFunDual_apply, ← L.sum_comp_single, ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← integral_fintype_prod_eq_prod]

/--
lemma `charFunDual_pi'` / 引理 `charFunDual_pi'`

English:
lemma charFunDual_pi'
  statement: (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
  simp_rw [charFunDual_apply, ← integral_fintype_prod_eq_prod, ← Complex.exp_sum, ← Finset.sum_mul,
    ← ofReal_sum, L.comp_apply, ← map_sum, ContinuousLinearMap.sum_comp_single]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

中文:
引理 charFunDual_pi'
  结论: (p : 实数>=0∞) [Fact (1 <= p)] {ι : 类型} [Fintype ι] [DecidableEq ι]
  证明: by
  simp_rw [charFunDual_apply, ← integral_fintype_prod_eq_prod, ← Complex.exp_sum, ← Finset.sum_mul,
    ← ofReal_sum, L.comp_apply, ← map_sum, ContinuousLinearMap.sum_comp_single]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

Depends on / 依赖: Complex.exp_sum, ContinuousLinearMap, ContinuousLinearMap.sum_comp_single, Finset, Finset.sum_mul, L.comp_apply, MeasurableEquiv, MeasurableEquiv.coe_toLp, charFunDual_apply, coe_toLp, comp_apply, exp_sum, integral_fintype_prod_eq_prod, integral_map_equiv, map_sum, ofReal_sum, simp_rw, sum_comp_single, sum_mul
-/
lemma charFunDual_pi' (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)]
    {mE : forall i, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)]
    (L : StrongDual Real (PiLp p E)) :
    charFunDual ((Measure.pi μ).map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p Real E).symm.toContinuousLinearMap.comp (.single Real E i))) := by
  simp_rw [charFunDual_apply, ← integral_fintype_prod_eq_prod, ← Complex.exp_sum, ← Finset.sum_mul,
    ← ofReal_sum, L.comp_apply, ← map_sum, ContinuousLinearMap.sum_comp_single]
  rw [← MeasurableEquiv.coe_toLp]; rw [integral_map_equiv]
  simp

variable [BorelSpace E] [SecondCountableTopology E]

/--
theorem `Measure.ext_of_charFunDual` / 定理 `Measure.ext_of_charFunDual`

English:
theorem Measure.ext_of_charFunDual
  statement: [CompleteSpace E]
  proof: by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L => funext_iff.mp h L)
· exact fun v hv => DFunLike.ne_iff.mpr SeparatingDual.exists_ne_zero hv
  · exact isBoundedBilinearMap_apply.symm.continuous

中文:
定理 Measure.ext_of_charFunDual
  结论: [CompleteSpace E]
  证明: by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L => funext_iff.mp h L)
· exact fun v hv => DFunLike.ne_iff.mpr SeparatingDual.exists_ne_zero hv
  · exact isBoundedBilinearMap_apply.symm.continuous

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mpr, SeparatingDual, SeparatingDual.exists_ne_zero, continuous, continuous_probChar, exists_ne_zero, ext_of_integral_char_eq, funext_iff, funext_iff.mp, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.symm.continuous, ne_iff, probChar_ne_one
-/
theorem Measure.ext_of_charFunDual [CompleteSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunDual μ = charFunDual ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L => funext_iff.mp h L)
· exact fun v hv => DFunLike.ne_iff.mpr SeparatingDual.exists_ne_zero hv
  · exact isBoundedBilinearMap_apply.symm.continuous

/--
lemma `charFunDual_eq_prod_iff` / 引理 `charFunDual_eq_prod_iff`

English:
lemma charFunDual_eq_prod_iff
  statement: [BorelSpace F] [SecondCountableTopology F] [CompleteSpace E]
  proof: by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_prod]
  mpr h := by rw [h]; exact charFunDual_prod

中文:
引理 charFunDual_eq_prod_iff
  结论: [BorelSpace F] [SecondCountableTopology F] [CompleteSpace E]
  证明: by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_prod]
  mpr h := by rw [h]; exact charFunDual_prod

Depends on / 依赖: Measure, Measure.ext_of_charFunDual, charFunDual_prod, ext_of_charFunDual
-/
lemma charFunDual_eq_prod_iff [BorelSpace F] [SecondCountableTopology F] [CompleteSpace E]
    [CompleteSpace F] {ξ : Measure (E × F)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] :
    (forall L, charFunDual ξ L =
      charFunDual μ (L.comp (.inl Real E F)) * charFunDual ν (L.comp (.inr Real E F))) ↔
    ξ = μ.prod ν where
  mp h := by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_prod]
  mpr h := by rw [h]; exact charFunDual_prod

/--
lemma `charFunDual_eq_prod_iff'` / 引理 `charFunDual_eq_prod_iff'`

English:
lemma charFunDual_eq_prod_iff'
  statement: (p : Real>=0∞) [Fact (1 <= p)] [BorelSpace F]
  proof: by
    refine (MeasurableEquiv.toLp p (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_prod']
  mpr h := by rw [h]; exact charFunDual_prod' p

中文:
引理 charFunDual_eq_prod_iff'
  结论: (p : 实数>=0∞) [Fact (1 <= p)] [BorelSpace F]
  证明: by
    refine (MeasurableEquiv.toLp p (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_prod']
  mpr h := by rw [h]; exact charFunDual_prod' p

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, Measure, Measure.ext_of_charFunDual, charFunDual_prod, coe_toLp, ext_of_charFunDual, map_measurableEquiv_injective
-/
lemma charFunDual_eq_prod_iff' (p : Real>=0∞) [Fact (1 <= p)] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace E] [CompleteSpace F] {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (forall L, charFunDual (ξ.map (toLp p)) L =
      charFunDual μ (L.comp
        ((WithLp.prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inl Real E F))) *
      charFunDual ν (L.comp
        ((WithLp.prodContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp
          (.inr Real E F)))) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp p (E × F)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_prod']
  mpr h := by rw [h]; exact charFunDual_prod' p

/--
lemma `charFunDual_eq_pi_iff` / 引理 `charFunDual_eq_pi_iff`

English:
lemma charFunDual_eq_pi_iff
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*}
  proof: by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_pi]
  mpr h := by rw [h]; exact charFunDual_pi

中文:
引理 charFunDual_eq_pi_iff
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] {E : ι -> 类型}
  证明: by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_pi]
  mpr h := by rw [h]; exact charFunDual_pi

Depends on / 依赖: Measure, Measure.ext_of_charFunDual, charFunDual_pi, ext_of_charFunDual
-/
lemma charFunDual_eq_pi_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*}
    [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)] {mE : forall i, MeasurableSpace (E i)}
    [forall i, BorelSpace (E i)] [forall i, SecondCountableTopology (E i)] [forall i, CompleteSpace (E i)]
    {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)} [forall i, IsFiniteMeasure (μ i)]
    [IsFiniteMeasure ν] :
    (forall L, charFunDual ν L = ∏ i, charFunDual (μ i) (L.comp (.single Real E i))) ↔
    ν = Measure.pi μ where
  mp h := by
refine Measure.ext_of_charFunDual funext fun t => ?_
    rw [h]; rw [charFunDual_pi]
  mpr h := by rw [h]; exact charFunDual_pi

/--
lemma `charFunDual_eq_pi_iff'` / 引理 `charFunDual_eq_pi_iff'`

English:
lemma charFunDual_eq_pi_iff'
  statement: (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
    refine (MeasurableEquiv.toLp p (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_pi']
  mpr h := by rw [h]; exact charFunDual_pi' p

中文:
引理 charFunDual_eq_pi_iff'
  结论: (p : 实数>=0∞) [Fact (1 <= p)] {ι : 类型} [Fintype ι] [DecidableEq ι]
  证明: by
    refine (MeasurableEquiv.toLp p (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_pi']
  mpr h := by rw [h]; exact charFunDual_pi' p

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.coe_toLp, MeasurableEquiv.toLp, Measure, Measure.ext_of_charFunDual, charFunDual_pi, coe_toLp, ext_of_charFunDual, map_measurableEquiv_injective
-/
lemma charFunDual_eq_pi_iff' (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)]
    {mE : forall i, MeasurableSpace (E i)} [forall i, BorelSpace (E i)] [forall i, SecondCountableTopology (E i)]
    [forall i, CompleteSpace (E i)] {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)}
    [forall i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (forall L, charFunDual (ν.map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p Real E).symm.toContinuousLinearMap.comp (.single Real E i)))) ↔
    ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp p (Π i, E i)).map_measurableEquiv_injective
 Measure.ext_of_charFunDual funext fun L => ?_
    rw [MeasurableEquiv.coe_toLp]; rw [h]; rw [charFunDual_pi']
  mpr h := by rw [h]; exact charFunDual_pi' p

/--
lemma `charFunDual_conv` / 引理 `charFunDual_conv`

English:
lemma charFunDual_conv
  statement: {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  simp_rw [charFunDual_apply]
  rw [integral_conv]
  · simp [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

中文:
引理 charFunDual_conv
  结论: {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  证明: by
  simp_rw [charFunDual_apply]
  rw [integral_conv]
  · simp [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

Depends on / 依赖: Complex.exp_add, add_mul, charFunDual_apply, exp_add, fun_prop, integrable_const, integral_const_mul, integral_conv, integral_mul_const, simp_rw
-/
lemma charFunDual_conv {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual Real E) : charFunDual (μ ∗ ν) L = charFunDual μ L * charFunDual ν L := by
  simp_rw [charFunDual_apply]
  rw [integral_conv]
  · simp [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : Real)).mono (by fun_prop) (by simp)

end NormedSpace

end MeasureTheory
