/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration

/-!
# Moments and moment-generating function

## Main definitions

* `ProbabilityTheory.moment X p μ`: `p`th moment of a real random variable `X` with respect to
  measure `μ`, `μ[X^p]`
* `ProbabilityTheory.centralMoment X p μ`:`p`th central moment of `X` with respect to measure `μ`,
  `μ[(X - μ[X])^p]`
* `ProbabilityTheory.mgf X μ t`: moment-generating function of `X` with respect to measure `μ`,
  `μ[exp(t*X)]`
* `ProbabilityTheory.cgf X μ t`: cumulant-generating function, logarithm of the moment-generating
  function

## Main results

* `ProbabilityTheory.IndepFun.mgf_add`: if two real random variables `X` and `Y` are independent
  and their moment-generating functions are defined at `t`, then
  `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `ProbabilityTheory.IndepFun.cgf_add`: if two real random variables `X` and `Y` are independent
  and their cumulant-generating functions are defined at `t`, then
  `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `ProbabilityTheory.measure_ge_le_exp_cgf` and `ProbabilityTheory.measure_le_le_exp_cgf`:
  Chernoff bound on the upper (resp. lower) tail of a random variable. For `t` nonnegative such that
  the cumulant-generating function exists, `ℙ(ε ≤ X) ≤ exp(- t*ε + cgf X ℙ t)`. See also
  `ProbabilityTheory.measure_ge_le_exp_mul_mgf` and
  `ProbabilityTheory.measure_le_le_exp_mul_mgf` for versions of these results using `mgf` instead
  of `cgf`.
-/

@[expose] public section


open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω -> Real} {p : Nat} {μ : Measure Ω}

/--
Definition of `moment` / `moment` 的定义

English:
definition moment
  signature: (X : Ω -> Real) (p : Nat) (μ : Measure Ω)
  body: μ[X ^ p]

中文:
定义 moment
  签名: (X : Ω -> 实数) (p : 自然数) (μ : 测度 Ω)
  定义体: μ[X ^ p]

Depends on / 依赖: Submodule, Submodule.nontrivial_iff_ne_bot.mpr, bot_lt_isotypicComponents, nontrivial_iff_ne_bot
-/
def moment (X : Ω -> Real) (p : Nat) (μ : Measure Ω) : Real :=
  μ[X ^ p]

/--
lemma `moment_def` / 引理 `moment_def`

English:
lemma moment_def
  given: (X : Ω -> Real) (p : Nat) (μ : Measure Ω)
  proof: rfl

中文:
引理 moment_def
  条件: (X : Ω -> 实数) (p : 自然数) (μ : 测度 Ω)
  证明: rfl
-/
lemma moment_def (X : Ω -> Real) (p : Nat) (μ : Measure Ω) :
    moment X p μ = μ[X ^ p] := rfl

/--
Definition of `centralMoment` / `centralMoment` 的定义

English:
definition centralMoment
  signature: (X : Ω -> Real) (p : Nat) (μ : Measure Ω)
  body: μ[(X - fun (_ : Ω) => μ[X]) ^ p]

@[simp]

中文:
定义 centralMoment
  签名: (X : Ω -> 实数) (p : 自然数) (μ : 测度 Ω)
  定义体: μ[(X - fun (_ : Ω) => μ[X]) ^ p]

@[simp]

Depends on / 依赖: infer_instance
-/
def centralMoment (X : Ω -> Real) (p : Nat) (μ : Measure Ω) : Real :=
  μ[(X - fun (_ : Ω) => μ[X]) ^ p]

@[simp]
/--
theorem `moment_zero` / 定理 `moment_zero`

English:
theorem moment_zero
  given: (hp : p != 0)
  statement: moment 0 p μ = 0
  proof: by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero]

@[simp]

中文:
定理 moment_zero
  条件: (hp : p != 0)
  结论: moment 0 p μ = 0
  证明: by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero]

@[simp]

Depends on / 依赖: Pi.zero_apply, integral_const, moment, mul_zero, not_false_iff, smul_eq_mul, zero_apply, zero_pow
-/
theorem moment_zero (hp : p != 0) : moment 0 p μ = 0 := by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero]

@[simp]
/--
lemma `moment_zero_measure` / 引理 `moment_zero_measure`

English:
lemma moment_zero_measure
  statement: moment X p (0 : Measure Ω) = 0
  proof: by simp [moment]

@[simp]

中文:
引理 moment_zero_measure
  结论: moment X p (0 : 测度 Ω) = 0
  证明: by simp [moment]

@[simp]

Depends on / 依赖: moment
-/
lemma moment_zero_measure : moment X p (0 : Measure Ω) = 0 := by simp [moment]

@[simp]
/--
theorem `centralMoment_zero` / 定理 `centralMoment_zero`

English:
theorem centralMoment_zero
  given: (hp : p != 0)
  statement: centralMoment 0 p μ = 0
  proof: by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]

中文:
定理 centralMoment_zero
  条件: (hp : p != 0)
  结论: centralMoment 0 p μ = 0
  证明: by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]

Depends on / 依赖: Pi.neg_apply, Pi.pow_apply, Pi.zero_apply, centralMoment, integral_const, mul_zero, neg_apply, neg_zero, not_false_iff, pow_apply, smul_eq_mul, zero_apply, zero_pow, zero_sub
-/
theorem centralMoment_zero (hp : p != 0) : centralMoment 0 p μ = 0 := by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]

/--
lemma `moment_one` / 引理 `moment_one`

English:
lemma moment_one
  given: (X : Ω -> Real) (μ : Measure Ω)
  proof: by simp [moment]

@[simp]

中文:
引理 moment_one
  条件: (X : Ω -> 实数) (μ : 测度 Ω)
  证明: by simp [moment]

@[simp]

Depends on / 依赖: moment
-/
lemma moment_one (X : Ω -> Real) (μ : Measure Ω) :
    moment X 1 μ = μ[X] := by simp [moment]

@[simp]
/--
lemma `centralMoment_zero_measure` / 引理 `centralMoment_zero_measure`

English:
lemma centralMoment_zero_measure
  statement: centralMoment X p (0 : Measure Ω) = 0
  proof: by
  simp [centralMoment]

中文:
引理 centralMoment_zero_measure
  结论: centralMoment X p (0 : 测度 Ω) = 0
  证明: by
  simp [centralMoment]

Depends on / 依赖: centralMoment
-/
lemma centralMoment_zero_measure : centralMoment X p (0 : Measure Ω) = 0 := by
  simp [centralMoment]

/--
theorem `centralMoment_one'` / 定理 `centralMoment_one'`

English:
theorem centralMoment_one'
  given: [IsFiniteMeasure μ] (h_int : Integrable X μ)
  proof: by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]

中文:
定理 centralMoment_one'
  条件: [是有限测度 μ] (h_int : 可积 X μ)
  证明: by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]

Depends on / 依赖: Pi.sub_apply, centralMoment, h_int, integrable_const, integral_const, integral_sub, one_mul, pow_one, smul_eq_mul, sub_apply, sub_mul
-/
theorem centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - μ.real Set.univ) * μ[X] := by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]
/--
theorem `centralMoment_one` / 定理 `centralMoment_one`

English:
theorem centralMoment_one
  given: [IsZeroOrProbabilityMeasure μ]
  statement: centralMoment X 1 μ = 0
  proof: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      fun_prop
    rw [integral_undef this]

中文:
定理 centralMoment_one
  条件: [是ZeroOrProbabilityMeasure μ]
  结论: centralMoment X 1 μ = 0
  证明: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      fun_prop
    rw [integral_undef this]

Depends on / 依赖: Integrable, Pi.sub_apply, centralMoment, centralMoment_one, eq_zero_or_isProbabilityMeasure, fun_prop, h_add, h_int, h_sub, integral, integral_undef, pow_one, sub_apply
-/
theorem centralMoment_one [IsZeroOrProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      fun_prop
    rw [integral_undef this]

/--
lemma `centralMoment_two_eq_variance` / 引理 `centralMoment_two_eq_variance`

English:
lemma centralMoment_two_eq_variance
  given: (hX : AEMeasurable X μ)
  statement: centralMoment X 2 μ = variance X μ
  proof: (variance_eq_integral hX).symm

中文:
引理 centralMoment_two_eq_variance
  条件: (hX : 几乎处处可测 X μ)
  结论: centralMoment X 2 μ = variance X μ
  证明: (variance_eq_integral hX).symm

Depends on / 依赖: variance_eq_integral
-/
lemma centralMoment_two_eq_variance (hX : AEMeasurable X μ) : centralMoment X 2 μ = variance X μ :=
  (variance_eq_integral hX).symm

/--
lemma `centralMoment_congr_ae` / 引理 `centralMoment_congr_ae`

English:
lemma centralMoment_congr_ae
  given: {X Y : Ω -> Real} (hXY : X =ᵐ[μ] Y)
  proof: by
  simp only [centralMoment, integral_congr_ae hXY]
  refine integral_congr_ae ?_
  filter_upwards [hXY] with x hx using by simp [hx]

中文:
引理 centralMoment_congr_ae
  条件: {X Y : Ω -> 实数} (hXY : X =ᵐ[μ] Y)
  证明: by
  simp only [centralMoment, integral_congr_ae hXY]
  refine integral_congr_ae ?_
  filter_upwards [hXY] with x hx using by simp [hx]

Depends on / 依赖: centralMoment, filter_upwards, integral_congr_ae
-/
lemma centralMoment_congr_ae {X Y : Ω -> Real} (hXY : X =ᵐ[μ] Y) :
    centralMoment X p μ = centralMoment Y p μ := by
  simp only [centralMoment, integral_congr_ae hXY]
  refine integral_congr_ae ?_
  filter_upwards [hXY] with x hx using by simp [hx]

section MomentGeneratingFunction

variable {t : Real}

/--
Definition of `mgf` / `mgf` 的定义

English:
definition mgf
  signature: (X : Ω -> Real) (μ : Measure Ω) (t : Real)
  body: μ[fun ω => exp (t * X ω)]

中文:
定义 mgf
  签名: (X : Ω -> 实数) (μ : 测度 Ω) (t : 实数)
  定义体: μ[fun ω => exp (t * X ω)]
-/
def mgf (X : Ω -> Real) (μ : Measure Ω) (t : Real) : Real :=
  μ[fun ω => exp (t * X ω)]

/--
Definition of `cgf` / `cgf` 的定义

English:
definition cgf
  signature: (X : Ω -> Real) (μ : Measure Ω) (t : Real)
  body: log (mgf X μ t)

@[simp]

中文:
定义 cgf
  签名: (X : Ω -> 实数) (μ : 测度 Ω) (t : 实数)
  定义体: log (mgf X μ t)

@[simp]
-/
def cgf (X : Ω -> Real) (μ : Measure Ω) (t : Real) : Real :=
  log (mgf X μ t)

@[simp]
/--
theorem `mgf_zero_fun` / 定理 `mgf_zero_fun`

English:
theorem mgf_zero_fun
  statement: mgf 0 μ t = μ.real Set.univ
  proof: by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]

中文:
定理 mgf_zero_fun
  结论: mgf 0 μ t = μ.real 集合.univ
  证明: by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]

Depends on / 依赖: Pi.zero_apply, exp_zero, integral_const, mul_one, mul_zero, smul_eq_mul, zero_apply
-/
theorem mgf_zero_fun : mgf 0 μ t = μ.real Set.univ := by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]
/--
theorem `cgf_zero_fun` / 定理 `cgf_zero_fun`

English:
theorem cgf_zero_fun
  statement: cgf 0 μ t = log (μ.real Set.univ)
  proof: by simp only [cgf, mgf_zero_fun]

@[simp]

中文:
定理 cgf_zero_fun
  结论: cgf 0 μ t = log (μ.real 集合.univ)
  证明: by simp only [cgf, mgf_zero_fun]

@[simp]

Depends on / 依赖: mgf_zero_fun
-/
theorem cgf_zero_fun : cgf 0 μ t = log (μ.real Set.univ) := by simp only [cgf, mgf_zero_fun]

@[simp]
/--
theorem `mgf_zero_measure` / 定理 `mgf_zero_measure`

English:
theorem mgf_zero_measure
  statement: mgf X (0 : Measure Ω) = 0
  proof: by ext; simp [mgf]

@[simp]

中文:
定理 mgf_zero_measure
  结论: mgf X (0 : 测度 Ω) = 0
  证明: by ext; simp [mgf]

@[simp]
-/
theorem mgf_zero_measure : mgf X (0 : Measure Ω) = 0 := by ext; simp [mgf]

@[simp]
/--
theorem `cgf_zero_measure` / 定理 `cgf_zero_measure`

English:
theorem cgf_zero_measure
  statement: cgf X (0 : Measure Ω) = 0
  proof: by ext; simp [cgf]

@[simp]

中文:
定理 cgf_zero_measure
  结论: cgf X (0 : 测度 Ω) = 0
  证明: by ext; simp [cgf]

@[simp]
-/
theorem cgf_zero_measure : cgf X (0 : Measure Ω) = 0 := by ext; simp [cgf]

@[simp]
/--
theorem `mgf_const'` / 定理 `mgf_const'`

English:
theorem mgf_const'
  given: (c : Real)
  statement: mgf (fun _ => c) μ t = μ.real Set.univ * exp (t * c)
  proof: by
  simp only [mgf, integral_const, smul_eq_mul]

中文:
定理 mgf_const'
  条件: (c : 实数)
  结论: mgf (fun _ => c) μ t = μ.real 集合.univ * exp (t * c)
  证明: by
  simp only [mgf, integral_const, smul_eq_mul]

Depends on / 依赖: integral_const, smul_eq_mul
-/
theorem mgf_const' (c : Real) : mgf (fun _ => c) μ t = μ.real Set.univ * exp (t * c) := by
  simp only [mgf, integral_const, smul_eq_mul]

/--
theorem `mgf_const` / 定理 `mgf_const`

English:
theorem mgf_const
  given: (c : Real) [IsProbabilityMeasure μ]
  statement: mgf (fun _ => c) μ t = exp (t * c)
  proof: by
  simp

@[simp]

中文:
定理 mgf_const
  条件: (c : 实数) [是概率测度 μ]
  结论: mgf (fun _ => c) μ t = exp (t * c)
  证明: by
  simp

@[simp]
-/
theorem mgf_const (c : Real) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp (t * c) := by
  simp

@[simp]
/--
theorem `cgf_const'` / 定理 `cgf_const'`

English:
theorem cgf_const'
  given: [IsFiniteMeasure μ] (hμ : μ != 0) (c : Real)
  proof: by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, not_false_iff]

@[simp]

中文:
定理 cgf_const'
  条件: [是有限测度 μ] (hμ : μ != 0) (c : 实数)
  证明: by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, not_false_iff]

@[simp]

Depends on / 依赖: Measure, Measure.measure_univ_eq_zero, exp_pos, log_exp, log_mul, measureReal_eq_zero_iff, measure_univ_eq_zero, mgf_const, not_false_iff
-/
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ != 0) (c : Real) :
    cgf (fun _ => c) μ t = log (μ.real Set.univ) + t * c := by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, not_false_iff]

@[simp]
/--
theorem `cgf_const` / 定理 `cgf_const`

English:
theorem cgf_const
  given: [IsProbabilityMeasure μ] (c : Real)
  statement: cgf (fun _ => c) μ t = t * c
  proof: by
  simp only [cgf, mgf_const, log_exp]

@[simp]

中文:
定理 cgf_const
  条件: [是概率测度 μ] (c : 实数)
  结论: cgf (fun _ => c) μ t = t * c
  证明: by
  simp only [cgf, mgf_const, log_exp]

@[simp]

Depends on / 依赖: log_exp, mgf_const
-/
theorem cgf_const [IsProbabilityMeasure μ] (c : Real) : cgf (fun _ => c) μ t = t * c := by
  simp only [cgf, mgf_const, log_exp]

@[simp]
/--
theorem `mgf_zero'` / 定理 `mgf_zero'`

English:
theorem mgf_zero'
  statement: mgf X μ 0 = μ.real Set.univ
  proof: by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]

中文:
定理 mgf_zero'
  结论: mgf X μ 0 = μ.real 集合.univ
  证明: by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]

Depends on / 依赖: exp_zero, integral_const, mul_one, smul_eq_mul, zero_mul
-/
theorem mgf_zero' : mgf X μ 0 = μ.real Set.univ := by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]

/--
theorem `mgf_zero` / 定理 `mgf_zero`

English:
theorem mgf_zero
  given: [IsProbabilityMeasure μ]
  statement: mgf X μ 0 = 1
  proof: by
  simp [mgf_zero']

中文:
定理 mgf_zero
  条件: [是概率测度 μ]
  结论: mgf X μ 0 = 1
  证明: by
  simp [mgf_zero']

Depends on / 依赖: mgf_zero
-/
theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp [mgf_zero']

/--
theorem `cgf_zero'` / 定理 `cgf_zero'`

English:
theorem cgf_zero'
  statement: cgf X μ 0 = log (μ.real Set.univ)
  proof: by simp only [cgf, mgf_zero']

@[simp]

中文:
定理 cgf_zero'
  结论: cgf X μ 0 = log (μ.real 集合.univ)
  证明: by simp only [cgf, mgf_zero']

@[simp]

Depends on / 依赖: mgf_zero
-/
theorem cgf_zero' : cgf X μ 0 = log (μ.real Set.univ) := by simp only [cgf, mgf_zero']

@[simp]
/--
theorem `cgf_zero` / 定理 `cgf_zero`

English:
theorem cgf_zero
  given: [IsZeroOrProbabilityMeasure μ]
  statement: cgf X μ 0 = 0
  proof: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h <;> simp [cgf_zero']

中文:
定理 cgf_zero
  条件: [是ZeroOrProbabilityMeasure μ]
  结论: cgf X μ 0 = 0
  证明: by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h <;> simp [cgf_zero']

Depends on / 依赖: cgf_zero, eq_zero_or_isProbabilityMeasure
-/
theorem cgf_zero [IsZeroOrProbabilityMeasure μ] : cgf X μ 0 = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h <;> simp [cgf_zero']

/--
theorem `mgf_undef` / 定理 `mgf_undef`

English:
theorem mgf_undef
  given: (hX : ¬Integrable (fun ω => exp (t * X ω)) μ)
  statement: mgf X μ t = 0
  proof: by
  simp only [mgf, integral_undef hX]

中文:
定理 mgf_undef
  条件: (hX : ¬可积 (fun ω => exp (t * X ω)) μ)
  结论: mgf X μ t = 0
  证明: by
  simp only [mgf, integral_undef hX]

Depends on / 依赖: integral_undef
-/
theorem mgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : mgf X μ t = 0 := by
  simp only [mgf, integral_undef hX]

/--
theorem `cgf_undef` / 定理 `cgf_undef`

English:
theorem cgf_undef
  given: (hX : ¬Integrable (fun ω => exp (t * X ω)) μ)
  statement: cgf X μ t = 0
  proof: by
  simp only [cgf, mgf_undef hX, log_zero]

中文:
定理 cgf_undef
  条件: (hX : ¬可积 (fun ω => exp (t * X ω)) μ)
  结论: cgf X μ t = 0
  证明: by
  simp only [cgf, mgf_undef hX, log_zero]

Depends on / 依赖: log_zero, mgf_undef
-/
theorem cgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : cgf X μ t = 0 := by
  simp only [cgf, mgf_undef hX, log_zero]

/--
theorem `mgf_nonneg` / 定理 `mgf_nonneg`

English:
theorem mgf_nonneg
  statement: 0 <= mgf X μ t
  proof: by
  unfold mgf; positivity

中文:
定理 mgf_nonneg
  结论: 0 <= mgf X μ t
  证明: by
  unfold mgf; positivity
-/
theorem mgf_nonneg : 0 <= mgf X μ t := by
  unfold mgf; positivity

/--
theorem `mgf_pos'` / 定理 `mgf_pos'`

English:
theorem mgf_pos'
  given: (hμ : μ != 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this]; rw [setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (exp_pos _).ne'
    rw [h_eq_univ]; rw [Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]

中文:
定理 mgf_pos'
  条件: (hμ : μ != 0) (h_int_X : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this]; rw [setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (exp_pos _).ne'
    rw [h_eq_univ]; rw [Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]

Depends on / 依赖: ENNReal, ENNReal.bot_eq_zero, Function, Function.mem_support, Function.support, Measure, Measure.measure_univ_eq_zero, Measure.restrict_univ, Ne.bot_lt, Set.inter_univ, Set.mem_univ, Set.univ, bot_eq_zero, bot_lt, exp_pos, h_eq_univ, iff_true, inter_univ, measure_univ_eq_zero, mem_support
-/
theorem mgf_pos' (hμ : μ != 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t := by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this]; rw [setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (exp_pos _).ne'
    rw [h_eq_univ]; rw [Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]

/--
theorem `mgf_pos` / 定理 `mgf_pos`

English:
theorem mgf_pos
  given: [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
  proof: mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X

中文:
定理 mgf_pos
  条件: [是概率测度 μ] (h_int_X : 可积 (fun ω => exp (t * X ω)) μ)
  证明: mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, h_int_X, mgf_pos, ne_zero
-/
theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t :=
  mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X

/--
lemma `mgf_pos_iff` / 引理 `mgf_pos_iff`

English:
lemma mgf_pos_iff
  given: [hμ : NeZero μ]
  proof: by
  refine ⟨fun h => ?_, fun h => mgf_pos' hμ.out h⟩
  contrapose! h with h
  simp [mgf_undef h]

中文:
引理 mgf_pos_iff
  条件: [hμ : NeZero μ]
  证明: by
  refine ⟨fun h => ?_, fun h => mgf_pos' hμ.out h⟩
  contrapose! h with h
  simp [mgf_undef h]

Depends on / 依赖: contrapose, mgf_pos, mgf_undef
-/
lemma mgf_pos_iff [hμ : NeZero μ] :
    0 < mgf X μ t ↔ Integrable (fun ω => exp (t * X ω)) μ := by
  refine ⟨fun h => ?_, fun h => mgf_pos' hμ.out h⟩
  contrapose! h with h
  simp [mgf_undef h]

/--
lemma `exp_cgf` / 引理 `exp_cgf`

English:
lemma exp_cgf
  given: [hμ : NeZero μ] (hX : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by rw [cgf, exp_log (mgf_pos' hμ.out hX)]

中文:
引理 exp_cgf
  条件: [hμ : NeZero μ] (hX : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by rw [cgf, exp_log (mgf_pos' hμ.out hX)]

Depends on / 依赖: exp_log, mgf_pos
-/
lemma exp_cgf [hμ : NeZero μ] (hX : Integrable (fun ω => exp (t * X ω)) μ) :
    exp (cgf X μ t) = mgf X μ t := by rw [cgf, exp_log (mgf_pos' hμ.out hX)]

/--
lemma `mgf_map` / 引理 `mgf_map`

English:
lemma mgf_map
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real}
  proof: by
  simp_rw [mgf, integral_map hY hX, Function.comp_apply]

中文:
引理 mgf_map
  结论: {Ω' : 类型} {mΩ' : 可测空间 Ω'} {μ : 测度 Ω'} {Y : Ω' -> Ω} {X : Ω -> 实数}
  证明: by
  simp_rw [mgf, integral_map hY hX, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, integral_map, simp_rw
-/
lemma mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real}
    (hY : AEMeasurable Y μ) {t : Real} (hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) (μ.map Y)) :
    mgf X (μ.map Y) t = mgf (X ∘ Y) μ t := by
  simp_rw [mgf, integral_map hY hX, Function.comp_apply]

/--
lemma `mgf_id_map` / 引理 `mgf_id_map`

English:
lemma mgf_id_map
  given: (hX : AEMeasurable X μ)
  statement: mgf id (μ.map X) = mgf X μ
  proof: by
  ext t
  rw [mgf_map hX]; rw [Function.id_comp]
  exact (measurable_const_mul _).exp.aestronglyMeasurable

中文:
引理 mgf_id_map
  条件: (hX : 几乎处处可测 X μ)
  结论: mgf id (μ.map X) = mgf X μ
  证明: by
  ext t
  rw [mgf_map hX]; rw [Function.id_comp]
  exact (measurable_const_mul _).exp.aestronglyMeasurable

Depends on / 依赖: Function, Function.id_comp, aestronglyMeasurable, exp.aestronglyMeasurable, id_comp, measurable_const_mul, mgf_map
-/
lemma mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ := by
  ext t
  rw [mgf_map hX]; rw [Function.id_comp]
  exact (measurable_const_mul _).exp.aestronglyMeasurable

/--
lemma `mgf_congr` / 引理 `mgf_congr`

English:
lemma mgf_congr
  given: {Y : Ω -> Real} (h : X =ᵐ[μ] Y)
  statement: mgf X μ t = mgf Y μ t
  proof: integral_congr_ae by filter_upwards [h] with ω hω using by rw [hω]

中文:
引理 mgf_congr
  条件: {Y : Ω -> 实数} (h : X =ᵐ[μ] Y)
  结论: mgf X μ t = mgf Y μ t
  证明: integral_congr_ae by filter_upwards [h] with ω hω using by rw [hω]

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
lemma mgf_congr {Y : Ω -> Real} (h : X =ᵐ[μ] Y) : mgf X μ t = mgf Y μ t :=
integral_congr_ae by filter_upwards [h] with ω hω using by rw [hω]

/--
lemma `mgf_congr_identDistrib` / 引理 `mgf_congr_identDistrib`

English:
lemma mgf_congr_identDistrib
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
  proof: by
  rw [← mgf_id_map h.aemeasurable_fst]; rw [← mgf_id_map h.aemeasurable_snd]; rw [h.map_eq]

中文:
引理 mgf_congr_identDistrib
  结论: {Ω' : 类型} {mΩ' : 可测空间 Ω'} {μ' : 测度 Ω'}
  证明: by
  rw [← mgf_id_map h.aemeasurable_fst]; rw [← mgf_id_map h.aemeasurable_snd]; rw [h.map_eq]

Depends on / 依赖: IsSemisimpleRing, aemeasurable_fst, aemeasurable_snd, h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq, map_eq, mgf_id_map
-/
lemma mgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' -> Real} (h : IdentDistrib X Y μ μ') :
    mgf X μ = mgf Y μ' := by
  rw [← mgf_id_map h.aemeasurable_fst]; rw [← mgf_id_map h.aemeasurable_snd]; rw [h.map_eq]

/--
theorem `mgf_neg` / 定理 `mgf_neg`

English:
theorem mgf_neg
  statement: mgf (-X) μ t = mgf X μ (-t)
  proof: by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

中文:
定理 mgf_neg
  结论: mgf (-X) μ t = mgf X μ (-t)
  证明: by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

Depends on / 依赖: Pi.neg_apply, mul_neg, neg_apply, neg_mul, simp_rw
-/
theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

/--
theorem `cgf_neg` / 定理 `cgf_neg`

English:
theorem cgf_neg
  statement: cgf (-X) μ t = cgf X μ (-t)
  proof: by simp_rw [cgf, mgf_neg]

中文:
定理 cgf_neg
  结论: cgf (-X) μ t = cgf X μ (-t)
  证明: by simp_rw [cgf, mgf_neg]

Depends on / 依赖: mgf_neg, simp_rw
-/
theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

/--
theorem `mgf_smul_left` / 定理 `mgf_smul_left`

English:
theorem mgf_smul_left
  given: (α : Real)
  statement: mgf (α • X) μ t = mgf X μ (α * t)
  proof: by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

中文:
定理 mgf_smul_left
  条件: (α : 实数)
  结论: mgf (α • X) μ t = mgf X μ (α * t)
  证明: by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

Depends on / 依赖: Pi.smul_apply, mul_assoc, mul_comm, simp_rw, smul_apply, smul_eq_mul
-/
theorem mgf_smul_left (α : Real) : mgf (α • X) μ t = mgf X μ (α * t) := by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

/--
theorem `mgf_const_mul` / 定理 `mgf_const_mul`

English:
theorem mgf_const_mul
  given: (α : Real)
  statement: mgf (fun ω => α * X ω) μ t = mgf X μ (α * t)
  proof: mgf_smul_left α

中文:
定理 mgf_const_mul
  条件: (α : 实数)
  结论: mgf (fun ω => α * X ω) μ t = mgf X μ (α * t)
  证明: mgf_smul_left α

Depends on / 依赖: mgf_smul_left
-/
theorem mgf_const_mul (α : Real) : mgf (fun ω => α * X ω) μ t = mgf X μ (α * t) := mgf_smul_left α

/--
theorem `mgf_const_add` / 定理 `mgf_const_add`

English:
theorem mgf_const_add
  given: (α : Real)
  statement: mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf X μ t
  proof: by
  rw [mgf]; rw [mgf]; rw [← integral_const_mul]
  congr with x
  dsimp
  rw [mul_add]; rw [exp_add]

中文:
定理 mgf_const_add
  条件: (α : 实数)
  结论: mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf X μ t
  证明: by
  rw [mgf]; rw [mgf]; rw [← integral_const_mul]
  congr with x
  dsimp
  rw [mul_add]; rw [exp_add]

Depends on / 依赖: exp_add, integral_const_mul, mul_add
-/
theorem mgf_const_add (α : Real) : mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf X μ t := by
  rw [mgf]; rw [mgf]; rw [← integral_const_mul]
  congr with x
  dsimp
  rw [mul_add]; rw [exp_add]

/--
theorem `mgf_add_const` / 定理 `mgf_add_const`

English:
theorem mgf_add_const
  given: (α : Real)
  statement: mgf (fun ω => X ω + α) μ t = mgf X μ t * exp (t * α)
  proof: by
  simp only [add_comm, mgf_const_add, mul_comm]

中文:
定理 mgf_add_const
  条件: (α : 实数)
  结论: mgf (fun ω => X ω + α) μ t = mgf X μ t * exp (t * α)
  证明: by
  simp only [add_comm, mgf_const_add, mul_comm]

Depends on / 依赖: add_comm, mgf_const_add, mul_comm
-/
theorem mgf_add_const (α : Real) : mgf (fun ω => X ω + α) μ t = mgf X μ t * exp (t * α) := by
  simp only [add_comm, mgf_const_add, mul_comm]

/--
lemma `mgf_add_measure` / 引理 `mgf_add_measure`

English:
lemma mgf_add_measure
  statement: {ν : Measure Ω}
  proof: by
  rw [mgf]; rw [integral_add_measure hμ hν]; rw [mgf]; rw [mgf]

中文:
引理 mgf_add_measure
  结论: {ν : 测度 Ω}
  证明: by
  rw [mgf]; rw [integral_add_measure hμ hν]; rw [mgf]; rw [mgf]

Depends on / 依赖: integral_add_measure
-/
lemma mgf_add_measure {ν : Measure Ω}
    (hμ : Integrable (fun ω => exp (t * X ω)) μ) (hν : Integrable (fun ω => exp (t * X ω)) ν) :
    mgf X (μ + ν) t = mgf X μ t + mgf X ν t := by
  rw [mgf]; rw [integral_add_measure hμ hν]; rw [mgf]; rw [mgf]

/--
lemma `mgf_sum_measure` / 引理 `mgf_sum_measure`

English:
lemma mgf_sum_measure
  statement: {ι : Type*} {μ : ι -> Measure Ω}
  proof: by
  simp_rw [mgf, integral_sum_measure hμ]

中文:
引理 mgf_sum_measure
  结论: {ι : 类型} {μ : ι -> 测度 Ω}
  证明: by
  simp_rw [mgf, integral_sum_measure hμ]

Depends on / 依赖: integral_sum_measure, simp_rw
-/
lemma mgf_sum_measure {ι : Type*} {μ : ι -> Measure Ω}
    (hμ : Integrable (fun ω => exp (t * X ω)) (Measure.sum μ)) :
    mgf X (Measure.sum μ) t = ∑' i, mgf X (μ i) t := by
  simp_rw [mgf, integral_sum_measure hμ]

/--
lemma `mgf_smul_measure` / 引理 `mgf_smul_measure`

English:
lemma mgf_smul_measure
  given: (c : Real>=0∞)
  statement: mgf X (c • μ) t = c.toReal * mgf X μ t
  proof: by
  rw [mgf]; rw [integral_smul_measure]; rw [mgf]; rw [smul_eq_mul]

中文:
引理 mgf_smul_measure
  条件: (c : 实数>=0∞)
  结论: mgf X (c • μ) t = c.to实数 * mgf X μ t
  证明: by
  rw [mgf]; rw [integral_smul_measure]; rw [mgf]; rw [smul_eq_mul]

Depends on / 依赖: integral_smul_measure, smul_eq_mul
-/
lemma mgf_smul_measure (c : Real>=0∞) : mgf X (c • μ) t = c.toReal * mgf X μ t := by
  rw [mgf]; rw [integral_smul_measure]; rw [mgf]; rw [smul_eq_mul]

/--
lemma `mgf_mono_of_nonneg` / 引理 `mgf_mono_of_nonneg`

English:
lemma mgf_mono_of_nonneg
  statement: {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : 0 <= t)
  proof: by
  by_cases htX : Integrable (fun ω => exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

中文:
引理 mgf_mono_of_nonneg
  结论: {Y : Ω -> 实数} (hXY : X <=ᵐ[μ] Y) (ht : 0 <= t)
  证明: by
  by_cases htX : Integrable (fun ω => exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

Depends on / 依赖: Integrable, filter_upwards, integral_mono_ae, mgf_nonneg, mgf_undef
-/
lemma mgf_mono_of_nonneg {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : 0 <= t)
    (htY : Integrable (fun ω => exp (t * Y ω)) μ) :
    mgf X μ t <= mgf Y μ t := by
  by_cases htX : Integrable (fun ω => exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

/--
lemma `mgf_anti_of_nonpos` / 引理 `mgf_anti_of_nonpos`

English:
lemma mgf_anti_of_nonpos
  statement: {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : t <= 0)
  proof: by
  by_cases htY : Integrable (fun ω => exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
filter_upwards [hXY] with ω hω using exp_monotone mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

中文:
引理 mgf_anti_of_nonpos
  结论: {Y : Ω -> 实数} (hXY : X <=ᵐ[μ] Y) (ht : t <= 0)
  证明: by
  by_cases htY : Integrable (fun ω => exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
filter_upwards [hXY] with ω hω using exp_monotone mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

Depends on / 依赖: Integrable, exp_monotone, filter_upwards, integral_mono_ae, mgf_nonneg, mgf_undef, mul_le_mul_of_nonpos_left
-/
lemma mgf_anti_of_nonpos {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : t <= 0)
    (htX : Integrable (fun ω => exp (t * X ω)) μ) :
    mgf Y μ t <= mgf X μ t := by
  by_cases htY : Integrable (fun ω => exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
filter_upwards [hXY] with ω hω using exp_monotone mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

section IndepFun

/--
theorem `IndepFun.exp_mul` / 定理 `IndepFun.exp_mul`

English:
theorem IndepFun.exp_mul
  given: {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y) (s t : Real)
  proof: by
  have h_meas : forall t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)

中文:
定理 IndepFun.exp_mul
  条件: {X Y : Ω -> 实数} (h_indep : X ⟂ᵢ[μ] Y) (s t : 实数)
  证明: by
  have h_meas : forall t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)

Depends on / 依赖: IndepFun, IndepFun.comp, Measurable, const_mul, h_indep, h_meas, measurable_id
-/
theorem IndepFun.exp_mul {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y) (s t : Real) :
    (fun ω => exp (s * X ω)) ⟂ᵢ[μ] (fun ω => exp (t * Y ω)) := by
  have h_meas : forall t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)

/--
theorem `IndepFun.mgf_add` / 定理 `IndepFun.mgf_add`

English:
theorem IndepFun.mgf_add
  statement: {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
  proof: by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul_eq_mul_integral hX hY

中文:
定理 IndepFun.mgf_add
  结论: {X Y : Ω -> 实数} (h_indep : X ⟂ᵢ[μ] Y)
  证明: by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul_eq_mul_integral hX hY

Depends on / 依赖: Pi.add_apply, add_apply, exp_add, exp_mul, h_indep, h_indep.exp_mul, integral_mul_eq_mul_integral, mul_add, simp_rw
-/
theorem IndepFun.mgf_add {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (hY : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul_eq_mul_integral hX hY

/--
theorem `IndepFun.mgf_add'` / 定理 `IndepFun.mgf_add'`

English:
theorem IndepFun.mgf_add'
  statement: {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
  proof: by
  have A : Continuous fun x : Real => exp (t * x) := by fun_prop
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y

中文:
定理 IndepFun.mgf_add'
  结论: {X Y : Ω -> 实数} (h_indep : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
  证明: by
  have A : Continuous fun x : Real => exp (t * x) := by fun_prop
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y

Depends on / 依赖: A.aestronglyMeasurable.comp_aemeasurable, AEStronglyMeasurable, Continuous, aemeasurable, aestronglyMeasurable, comp_aemeasurable, fun_prop, hX.aemeasurable, hY.aemeasurable, h_indep, h_indep.mgf_add, mgf_add
-/
theorem IndepFun.mgf_add' {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  have A : Continuous fun x : Real => exp (t * x) := by fun_prop
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y

/--
theorem `IndepFun.cgf_add` / 定理 `IndepFun.cgf_add`

English:
theorem IndepFun.cgf_add
  statement: {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'

中文:
定理 IndepFun.cgf_add
  结论: {X Y : Ω -> 实数} (h_indep : X ⟂ᵢ[μ] Y)
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'

Depends on / 依赖: aestronglyMeasurable, h_indep, h_indep.mgf_add, h_int_X, h_int_X.aestronglyMeasurable, h_int_Y, h_int_Y.aestronglyMeasurable, log_mul, mgf_add, mgf_pos
-/
theorem IndepFun.cgf_add {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'

/--
theorem `aestronglyMeasurable_exp_mul_add` / 定理 `aestronglyMeasurable_exp_mul_add`

English:
theorem aestronglyMeasurable_exp_mul_add
  statement: {X Y : Ω -> Real}
  proof: by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y

中文:
定理 aestronglyMeasurable_exp_mul_add
  结论: {X Y : Ω -> 实数}
  证明: by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mul, Pi.add_apply, add_apply, exp_add, h_int_X, h_int_Y, mul_add, simp_rw
-/
theorem aestronglyMeasurable_exp_mul_add {X Y : Ω -> Real}
    (h_int_X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y

/--
theorem `aestronglyMeasurable_exp_mul_sum` / 定理 `aestronglyMeasurable_exp_mul_sum`

English:
theorem aestronglyMeasurable_exp_mul_sum
  statement: {X : ι -> Ω -> Real} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    apply aestronglyMeasurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec

中文:
定理 aestronglyMeasurable_exp_mul_sum
  结论: {X : ι -> Ω -> 实数} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    apply aestronglyMeasurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec

Depends on / 依赖: AEStronglyMeasurable, Finset, Finset.induction_on, Finset.sum_apply, Matrix, Matrix.piRingEquiv, aestronglyMeasurable_const, aestronglyMeasurable_exp_mul_add, classical, e.mapMatrix, exists_ringEquiv_pi_matrix_divisionRing, exp_zero, h_int, h_rec, hi_notin_s, induction_on, insert, isEmpty_or_nonempty, isSemisimpleRing, mapMatrix
-/
theorem aestronglyMeasurable_exp_mul_sum {X : ι -> Ω -> Real} {s : Finset ι}
    (h_int : forall i in s, AEStronglyMeasurable (fun ω => exp (t * X i ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (∑ i in s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    apply aestronglyMeasurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec

/--
theorem `IndepFun.integrable_exp_mul_add` / 定理 `IndepFun.integrable_exp_mul_add`

English:
theorem IndepFun.integrable_exp_mul_add
  statement: {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
  proof: by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y

中文:
定理 IndepFun.integrable_exp_mul_add
  结论: {X Y : Ω -> 实数} (h_indep : X ⟂ᵢ[μ] Y)
  证明: by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y

Depends on / 依赖: Pi.add_apply, add_apply, exp_add, exp_mul, h_indep, h_indep.exp_mul, h_int_X, h_int_Y, integrable_mul, mul_add, simp_rw
-/
theorem IndepFun.integrable_exp_mul_add {X Y : Ω -> Real} (h_indep : X ⟂ᵢ[μ] Y)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    Integrable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y

/--
theorem `iIndepFun.integrable_exp_mul_sum` / 定理 `iIndepFun.integrable_exp_mul_sum`

English:
theorem iIndepFun.integrable_exp_mul_sum
  statement: [IsFiniteMeasure μ] {X : ι -> Ω -> Real}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm

中文:
定理 iIndepFun.integrable_exp_mul_sum
  结论: [是有限测度 μ] {X : ι -> Ω -> 实数}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_apply, IndepFun, IndepFun.integrable_exp_mul_add, Integrable, classical, exp_zero, h_indep, h_indep.indepFun_finsetSum_of_notMem, h_int, h_meas, h_rec, hi_notin_s, indepFun_finsetSum_of_notMem, induction_on, insert, integrable_const, integrable_exp_mul_add, mem_insert_of_mem
-/
theorem iIndepFun.integrable_exp_mul_sum [IsFiniteMeasure μ] {X : ι -> Ω -> Real}
    (h_indep : iIndepFun X μ) (h_meas : forall i, Measurable (X i))
    {s : Finset ι} (h_int : forall i in s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i in s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  | insert i s hi_notin_s h_rec =>
    have : forall i : ι, i in s -> Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm

/--
theorem `iIndepFun.mgf_sum₀` / 定理 `iIndepFun.mgf_sum₀`

English:
theorem iIndepFun.mgf_sum₀
  statement: {X : ι -> Ω -> Real}
  proof: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    have h_int' : forall i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s]; rw [IndepFun.mgf_add (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i)]; rw [h_rec]; rw [prod_insert hi_notin_s]

中文:
定理 iIndepFun.mgf_sum₀
  结论: {X : ι -> Ω -> 实数}
  证明: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    have h_int' : forall i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s]; rw [IndepFun.mgf_add (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i)]; rw [h_rec]; rw [prod_insert hi_notin_s]

Depends on / 依赖: AEStronglyMeasurable, Finset, Finset.induction_on, IndepFun, IndepFun.mgf_add, IsProbabilityMeasure, aestronglyMeasurable, aestronglyMeasurable_exp_mul_sum, classical, const_mul, exp.aestronglyMeasurable, h_indep, h_indep.indepFun_finsetSum_of_notMem, h_indep.isProbabilityMeasure, h_int, h_meas, h_rec, hi_notin_s, induction_on, insert
-/
theorem iIndepFun.mgf_sum₀ {X : ι -> Ω -> Real}
    (h_indep : iIndepFun X μ) (h_meas : forall i, AEMeasurable (X i) μ)
    (s : Finset ι) : mgf (∑ i in s, X i) μ t = ∏ i in s, mgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    have h_int' : forall i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s]; rw [IndepFun.mgf_add (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i)]; rw [h_rec]; rw [prod_insert hi_notin_s]

/--
theorem `iIndepFun.mgf_sum` / 定理 `iIndepFun.mgf_sum`

English:
theorem iIndepFun.mgf_sum
  statement: {X : ι -> Ω -> Real}
  proof: h_indep.mgf_sum₀ (by fun_prop) s

中文:
定理 iIndepFun.mgf_sum
  结论: {X : ι -> Ω -> 实数}
  证明: h_indep.mgf_sum₀ (by fun_prop) s

Depends on / 依赖: fun_prop, h_indep, h_indep.mgf_sum
-/
theorem iIndepFun.mgf_sum {X : ι -> Ω -> Real}
    (h_indep : iIndepFun X μ) (h_meas : forall i, Measurable (X i))
    (s : Finset ι) : mgf (∑ i in s, X i) μ t = ∏ i in s, mgf (X i) μ t :=
  h_indep.mgf_sum₀ (by fun_prop) s

/--
theorem `iIndepFun.cgf_sum₀` / 定理 `iIndepFun.cgf_sum₀`

English:
theorem iIndepFun.cgf_sum₀
  statement: {X : ι -> Ω -> Real}
  proof: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod fun j hj => ?_]
  · rw [h_indep.mgf_sum₀ h_meas]
  · exact (mgf_pos (h_int j hj)).ne'

中文:
定理 iIndepFun.cgf_sum₀
  结论: {X : ι -> Ω -> 实数}
  证明: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod fun j hj => ?_]
  · rw [h_indep.mgf_sum₀ h_meas]
  · exact (mgf_pos (h_int j hj)).ne'

Depends on / 依赖: IsProbabilityMeasure, h_indep, h_indep.isProbabilityMeasure, h_indep.mgf_sum, h_int, h_meas, isProbabilityMeasure, log_prod, mgf_pos, simp_rw
-/
theorem iIndepFun.cgf_sum₀ {X : ι -> Ω -> Real}
    (h_indep : iIndepFun X μ) (h_meas : forall i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_int : forall i in s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i in s, X i) μ t = ∑ i in s, cgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod fun j hj => ?_]
  · rw [h_indep.mgf_sum₀ h_meas]
  · exact (mgf_pos (h_int j hj)).ne'

/--
theorem `iIndepFun.cgf_sum` / 定理 `iIndepFun.cgf_sum`

English:
theorem iIndepFun.cgf_sum
  statement: {X : ι -> Ω -> Real}
  proof: h_indep.cgf_sum₀ (by fun_prop) h_int

中文:
定理 iIndepFun.cgf_sum
  结论: {X : ι -> Ω -> 实数}
  证明: h_indep.cgf_sum₀ (by fun_prop) h_int

Depends on / 依赖: fun_prop, h_indep, h_indep.cgf_sum, h_int
-/
theorem iIndepFun.cgf_sum {X : ι -> Ω -> Real}
    (h_indep : iIndepFun X μ) (h_meas : forall i, Measurable (X i))
    {s : Finset ι} (h_int : forall i in s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i in s, X i) μ t = ∑ i in s, cgf (X i) μ t :=
  h_indep.cgf_sum₀ (by fun_prop) h_int

end IndepFun

/--
theorem `mgf_congr_of_identDistrib` / 定理 `mgf_congr_of_identDistrib`

English:
theorem mgf_congr_of_identDistrib
  proof: hident.comp (measurable_const_mul t).exp

中文:
定理 mgf_congr_of_identDistrib
  证明: hident.comp (measurable_const_mul t).exp

Depends on / 依赖: hident, hident.comp, measurable_const_mul
-/
theorem mgf_congr_of_identDistrib
    (X : Ω -> Real) {Ω' : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} (X' : Ω' -> Real)
    (hident : IdentDistrib X X' μ μ') (t : Real) :
.integral_eq mgf X μ t = mgf X' μ' t := hident.comp (measurable_const_mul t).exp

/--
theorem `mgf_sum_of_identDistrib₀` / 定理 `mgf_sum_of_identDistrib₀`

English:
theorem mgf_sum_of_identDistrib₀
  proof: by
  rw [h_indep.mgf_sum₀ h_meas]
  exact Finset.prod_eq_pow_card fun i hi =>
    mgf_congr_of_identDistrib (X i) (X j) (hident i hi j hj) t

中文:
定理 mgf_sum_of_identDistrib₀
  证明: by
  rw [h_indep.mgf_sum₀ h_meas]
  exact Finset.prod_eq_pow_card fun i hi =>
    mgf_congr_of_identDistrib (X i) (X j) (hident i hi j hj) t

Depends on / 依赖: Finset, Finset.prod_eq_pow_card, h_indep, h_indep.mgf_sum, h_meas, hident, mgf_congr_of_identDistrib, prod_eq_pow_card
-/
theorem mgf_sum_of_identDistrib₀
    {X : ι -> Ω -> Real}
    {s : Finset ι} {j : ι}
    (h_meas : forall i, AEMeasurable (X i) μ)
    (h_indep : iIndepFun X μ)
    (hident : forall i in s, forall j in s, IdentDistrib (X i) (X j) μ μ)
    (hj : j in s) (t : Real) : mgf (∑ i in s, X i) μ t = mgf (X j) μ t ^ #s := by
  rw [h_indep.mgf_sum₀ h_meas]
  exact Finset.prod_eq_pow_card fun i hi =>
    mgf_congr_of_identDistrib (X i) (X j) (hident i hi j hj) t

/--
theorem `mgf_sum_of_identDistrib` / 定理 `mgf_sum_of_identDistrib`

English:
theorem mgf_sum_of_identDistrib
  proof: mgf_sum_of_identDistrib₀ (by fun_prop) h_indep hident hj t

中文:
定理 mgf_sum_of_identDistrib
  证明: mgf_sum_of_identDistrib₀ (by fun_prop) h_indep hident hj t

Depends on / 依赖: fun_prop, h_indep, hident
-/
theorem mgf_sum_of_identDistrib
    {X : ι -> Ω -> Real}
    {s : Finset ι} {j : ι}
    (h_meas : forall i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (hident : forall i in s, forall j in s, IdentDistrib (X i) (X j) μ μ)
    (hj : j in s) (t : Real) : mgf (∑ i in s, X i) μ t = mgf (X j) μ t ^ #s :=
  mgf_sum_of_identDistrib₀ (by fun_prop) h_indep hident hj t

section Chernoff

/--
theorem `measure_ge_le_exp_mul_mgf` / 定理 `measure_ge_le_exp_mul_mgf`

English:
theorem measure_ge_le_exp_mul_mgf
  statement: [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t)
  proof: by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    μ.real {ω | ε <= X ω} = μ.real {ω | exp (t * ε) <= exp (t * X ω)} := by
      congr 1 with ω
      simp only [Set.mem_ofPred_eq, exp_le_exp]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ <= (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * μ.real {ω | exp (t * ε) <= exp (t * X ω)} <=
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

中文:
定理 measure_ge_le_exp_mul_mgf
  结论: [是有限测度 μ] (ε : 实数) (ht : 0 <= t)
  证明: by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    μ.real {ω | ε <= X ω} = μ.real {ω | exp (t * ε) <= exp (t * X ω)} := by
      congr 1 with ω
      simp only [Set.mem_ofPred_eq, exp_le_exp]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ <= (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * μ.real {ω | exp (t * ε) <= exp (t * X ω)} <=
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

Depends on / 依赖: Set.mem_ofPred_eq, Set.subset_univ, eq_or_lt, exacts, exp_le_exp, exp_zero, ht.eq_or_lt, ht_pos, ht_pos.le, ht_zero_eq, ht_zero_eq.symm, le_of_mul_le_mul_left, measure_ne_top, mem_ofPred_eq, mgf_zero, mul_le_mul_of_nonneg_left, neg_zero, one_mul, subset_univ, zero_mul
-/
theorem measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε <= X ω} <= exp (-t * ε) * mgf X μ t := by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    μ.real {ω | ε <= X ω} = μ.real {ω | exp (t * ε) <= exp (t * X ω)} := by
      congr 1 with ω
      simp only [Set.mem_ofPred_eq, exp_le_exp]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ <= (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * μ.real {ω | exp (t * ε) <= exp (t * X ω)} <=
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

/--
theorem `measure_le_le_exp_mul_mgf` / 定理 `measure_le_le_exp_mul_mgf`

English:
theorem measure_le_le_exp_mul_mgf
  statement: [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0)
  proof: by
  rw [← neg_neg t]; rw [← mgf_neg]; rw [neg_neg]; rw [← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

中文:
定理 measure_le_le_exp_mul_mgf
  结论: [是有限测度 μ] (ε : 实数) (ht : t <= 0)
  证明: by
  rw [← neg_neg t]; rw [← mgf_neg]; rw [neg_neg]; rw [← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

Depends on / 依赖: Eq.trans_le, Pi.neg_apply, h_int, measure_ge_le_exp_mul_mgf, mgf_neg, neg_apply, neg_le_neg_iff, neg_mul_neg, neg_neg, neg_nonneg, neg_nonneg.mpr, simp_rw, trans_le
-/
theorem measure_le_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω <= ε} <= exp (-t * ε) * mgf X μ t := by
  rw [← neg_neg t]; rw [← mgf_neg]; rw [neg_neg]; rw [← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

/--
theorem `measure_ge_le_exp_cgf` / 定理 `measure_ge_le_exp_cgf`

English:
theorem measure_ge_le_exp_cgf
  statement: [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t)
  proof: by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

中文:
定理 measure_ge_le_exp_cgf
  结论: [是有限测度 μ] (ε : 实数) (ht : 0 <= t)
  证明: by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

Depends on / 依赖: exp_add, exp_pos, h_int, le_exp_log, le_rfl, measure_ge_le_exp_mul_mgf, mgf_nonneg, mul_le_mul
-/
theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε <= X ω} <= exp (-t * ε + cgf X μ t) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

/--
theorem `measure_le_le_exp_cgf` / 定理 `measure_le_le_exp_cgf`

English:
theorem measure_le_le_exp_cgf
  statement: [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0)
  proof: by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

中文:
定理 measure_le_le_exp_cgf
  结论: [是有限测度 μ] (ε : 实数) (ht : t <= 0)
  证明: by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

Depends on / 依赖: exp_add, exp_pos, h_int, le_exp_log, le_rfl, measure_le_le_exp_mul_mgf, mgf_nonneg, mul_le_mul
-/
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω <= ε} <= exp (-t * ε + cgf X μ t) := by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

end Chernoff

/--
lemma `mgf_dirac` / 引理 `mgf_dirac`

English:
lemma mgf_dirac
  given: {x : Real} (hX : μ.map X = .dirac x) (t : Real)
  statement: mgf X μ t = exp (x * t)
  proof: by
  have : IsProbabilityMeasure (μ.map X) := by rw [hX]; infer_instance
  rw [← mgf_id_map (.of_map_ne_zero <| IsProbabilityMeasure.ne_zero _)]; rw [mgf]; rw [hX]; rw [integral_dirac]; rw [mul_comm]; rw [id_def]

中文:
引理 mgf_dirac
  条件: {x : 实数} (hX : μ.map X = .dirac x) (t : 实数)
  结论: mgf X μ t = exp (x * t)
  证明: by
  have : IsProbabilityMeasure (μ.map X) := by rw [hX]; infer_instance
  rw [← mgf_id_map (.of_map_ne_zero <| IsProbabilityMeasure.ne_zero _)]; rw [mgf]; rw [hX]; rw [integral_dirac]; rw [mul_comm]; rw [id_def]

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, id_def, infer_instance, integral_dirac, mgf_id_map, mul_comm, ne_zero, of_map_ne_zero
-/
lemma mgf_dirac {x : Real} (hX : μ.map X = .dirac x) (t : Real) : mgf X μ t = exp (x * t) := by
  have : IsProbabilityMeasure (μ.map X) := by rw [hX]; infer_instance
  rw [← mgf_id_map (.of_map_ne_zero <| IsProbabilityMeasure.ne_zero _)]; rw [mgf]; rw [hX]; rw [integral_dirac]; rw [mul_comm]; rw [id_def]

/--
lemma `mgf_dirac'` / 引理 `mgf_dirac'`

English:
lemma mgf_dirac'
  given: [MeasurableSingletonClass Ω] {ω : Ω}
  proof: by
  rw [mgf]; rw [integral_dirac]

中文:
引理 mgf_dirac'
  条件: [MeasurableSingleton类 Ω] {ω : Ω}
  证明: by
  rw [mgf]; rw [integral_dirac]

Depends on / 依赖: integral_dirac
-/
lemma mgf_dirac' [MeasurableSingletonClass Ω] {ω : Ω} :
    mgf X (Measure.dirac ω) t = exp (t * X ω) := by
  rw [mgf]; rw [integral_dirac]

end MomentGeneratingFunction

/--
lemma `aemeasurable_exp_mul` / 引理 `aemeasurable_exp_mul`

English:
lemma aemeasurable_exp_mul
  given: {X : Ω -> Real} (t : Real) (hX : AEMeasurable X μ)
  proof: (measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable

中文:
引理 aemeasurable_exp_mul
  条件: {X : Ω -> 实数} (t : 实数) (hX : 几乎处处可测 X μ)
  证明: (measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, comp_aemeasurable, const_mul, hX.const_mul, measurable_exp, measurable_exp.comp_aemeasurable
-/
lemma aemeasurable_exp_mul {X : Ω -> Real} (t : Real) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω => rexp (t * X ω)) μ :=
  (measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable

/--
lemma `integrable_exp_mul_of_le` / 引理 `integrable_exp_mul_of_le`

English:
lemma integrable_exp_mul_of_le
  statement: [IsFiniteMeasure μ] {X : Ω -> Real} (t b : Real) (ht : 0 <= t)
  proof: by
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb
  exact ⟨by positivity, by gcongr⟩

中文:
引理 integrable_exp_mul_of_le
  结论: [是有限测度 μ] {X : Ω -> 实数} (t b : 实数) (ht : 0 <= t)
  证明: by
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb
  exact ⟨by positivity, by gcongr⟩

Depends on / 依赖: comp_aemeasurable, const_mul, filter_upwards, hX.const_mul, measurable_exp, measurable_exp.comp_aemeasurable, of_mem_Icc
-/
lemma integrable_exp_mul_of_le [IsFiniteMeasure μ] {X : Ω -> Real} (t b : Real) (ht : 0 <= t)
    (hX : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω <= b) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb
  exact ⟨by positivity, by gcongr⟩

/--
lemma `integrable_exp_mul_of_mem_Icc` / 引理 `integrable_exp_mul_of_mem_Icc`

English:
lemma integrable_exp_mul_of_mem_Icc
  statement: [IsFiniteMeasure μ] {X : Ω -> Real} {a b t : Real}
  proof: by
  apply Integrable.of_mem_Icc (exp (min (a * t) (b * t))) (exp (max (a * t) (b * t)))
  · exact (measurable_exp.comp_aemeasurable (hm.const_mul t))
  filter_upwards [hb] with ω ⟨hl, hr⟩
  simp only [Set.mem_Icc, exp_le_exp, inf_le_iff, le_sup_iff]
  by_cases ht : 0 <= t
  · exact ⟨Or.inl (by nlinarith), Or.inr (by nlinarith)⟩
  · exact ⟨Or.inr (by nlinarith), Or.inl (by nlinarith)⟩

中文:
引理 integrable_exp_mul_of_mem_Icc
  结论: [是有限测度 μ] {X : Ω -> 实数} {a b t : 实数}
  证明: by
  apply Integrable.of_mem_Icc (exp (min (a * t) (b * t))) (exp (max (a * t) (b * t)))
  · exact (measurable_exp.comp_aemeasurable (hm.const_mul t))
  filter_upwards [hb] with ω ⟨hl, hr⟩
  simp only [Set.mem_Icc, exp_le_exp, inf_le_iff, le_sup_iff]
  by_cases ht : 0 <= t
  · exact ⟨Or.inl (by nlinarith), Or.inr (by nlinarith)⟩
  · exact ⟨Or.inr (by nlinarith), Or.inl (by nlinarith)⟩

Depends on / 依赖: Integrable, Integrable.of_mem_Icc, Or.inl, Or.inr, Set.mem_Icc, comp_aemeasurable, const_mul, exp_le_exp, filter_upwards, hm.const_mul, inf_le_iff, le_sup_iff, measurable_exp, measurable_exp.comp_aemeasurable, mem_Icc, of_mem_Icc
-/
lemma integrable_exp_mul_of_mem_Icc [IsFiniteMeasure μ] {X : Ω -> Real} {a b t : Real}
    (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  apply Integrable.of_mem_Icc (exp (min (a * t) (b * t))) (exp (max (a * t) (b * t)))
  · exact (measurable_exp.comp_aemeasurable (hm.const_mul t))
  filter_upwards [hb] with ω ⟨hl, hr⟩
  simp only [Set.mem_Icc, exp_le_exp, inf_le_iff, le_sup_iff]
  by_cases ht : 0 <= t
  · exact ⟨Or.inl (by nlinarith), Or.inr (by nlinarith)⟩
  · exact ⟨Or.inr (by nlinarith), Or.inl (by nlinarith)⟩

end ProbabilityTheory

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace Real E] [NormedSpace 𝕜 F] [NormedSpace Real F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E}

/--
lemma `integral_comp_id_comm'` / 引理 `integral_comp_id_comm'`

English:
lemma integral_comp_id_comm'
  given: (h : Integrable id μ) (L : E ->L[𝕜] F)
  proof: by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]

中文:
引理 integral_comp_id_comm'
  条件: (h : 可积 id μ) (L : E ->L[𝕜] F)
  证明: by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]

Depends on / 依赖: L.integral_comp_comm, integral_comp_comm
-/
lemma integral_comp_id_comm' (h : Integrable id μ) (L : E ->L[𝕜] F) :
    μ[L] = L μ[id] := by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]

/--
lemma `integral_comp_id_comm` / 引理 `integral_comp_id_comm`

English:
lemma integral_comp_id_comm
  given: (h : Integrable id μ) (L : E ->L[𝕜] F)
  proof: L.integral_comp_id_comm' h

中文:
引理 integral_comp_id_comm
  条件: (h : 可积 id μ) (L : E ->L[𝕜] F)
  证明: L.integral_comp_id_comm' h

Depends on / 依赖: L.integral_comp_id_comm, integral_comp_id_comm
-/
lemma integral_comp_id_comm (h : Integrable id μ) (L : E ->L[𝕜] F) :
    μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_id_comm' h

variable [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/--
lemma `integral_id_map` / 引理 `integral_id_map`

English:
lemma integral_id_map
  given: (h : Integrable id μ) (L : E ->L[𝕜] F)
  proof: by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]

中文:
引理 integral_id_map
  条件: (h : 可积 id μ) (L : E ->L[𝕜] F)
  证明: by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]

Depends on / 依赖: L.integral_comp_id_comm, fun_prop, integral_comp_id_comm, integral_map
-/
lemma integral_id_map (h : Integrable id μ) (L : E ->L[𝕜] F) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace Real E] [NormedSpace 𝕜 F] [NormedSpace Real F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E}

/--
lemma `integral_comp_id_comm'` / 引理 `integral_comp_id_comm'`

English:
lemma integral_comp_id_comm'
  given: (L : E ≃L[𝕜] F)
  proof: by
  by_cases h : Integrable (fun x => x) μ
  · exact ContinuousLinearMap.integral_comp_id_comm' h L.toContinuousLinearMap
  have : ¬ Integrable L μ := mt L.integrable_comp_iff.1 h
  simp_all [integral_undef]

中文:
引理 integral_comp_id_comm'
  条件: (L : E ≃L[𝕜] F)
  证明: by
  by_cases h : Integrable (fun x => x) μ
  · exact ContinuousLinearMap.integral_comp_id_comm' h L.toContinuousLinearMap
  have : ¬ Integrable L μ := mt L.integrable_comp_iff.1 h
  simp_all [integral_undef]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integral_comp_id_comm, Integrable, L.integrable_comp_iff, L.toContinuousLinearMap, integrable_comp_iff, integral_comp_id_comm, integral_undef, toContinuousLinearMap
-/
lemma integral_comp_id_comm' (L : E ≃L[𝕜] F) :
    μ[L] = L μ[id] := by
  by_cases h : Integrable (fun x => x) μ
  · exact ContinuousLinearMap.integral_comp_id_comm' h L.toContinuousLinearMap
  have : ¬ Integrable L μ := mt L.integrable_comp_iff.1 h
  simp_all [integral_undef]

/--
lemma `integral_comp_id_comm` / 引理 `integral_comp_id_comm`

English:
lemma integral_comp_id_comm
  given: (L : E ≃L[𝕜] F)
  proof: L.integral_comp_id_comm'

中文:
引理 integral_comp_id_comm
  条件: (L : E ≃L[𝕜] F)
  证明: L.integral_comp_id_comm'

Depends on / 依赖: L.integral_comp_id_comm, integral_comp_id_comm
-/
lemma integral_comp_id_comm (L : E ≃L[𝕜] F) :
    μ[L] = L (∫ x, x ∂μ) := L.integral_comp_id_comm'

variable [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/--
lemma `integral_id_map` / 引理 `integral_id_map`

English:
lemma integral_id_map
  given: (L : E ≃L[𝕜] F)
  proof: by
  rw [show ⇑L = ⇑L.toHomeomorph.toMeasurableEquiv from rfl]; rw [integral_map_equiv]
  simp [L.integral_comp_id_comm]

中文:
引理 integral_id_map
  条件: (L : E ≃L[𝕜] F)
  证明: by
  rw [show ⇑L = ⇑L.toHomeomorph.toMeasurableEquiv from rfl]; rw [integral_map_equiv]
  simp [L.integral_comp_id_comm]

Depends on / 依赖: L.integral_comp_id_comm, L.toHomeomorph.toMeasurableEquiv, integral_comp_id_comm, integral_map_equiv, toHomeomorph, toMeasurableEquiv
-/
lemma integral_id_map (L : E ≃L[𝕜] F) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [show ⇑L = ⇑L.toHomeomorph.toMeasurableEquiv from rfl]; rw [integral_map_equiv]
  simp [L.integral_comp_id_comm]

end ContinuousLinearEquiv
