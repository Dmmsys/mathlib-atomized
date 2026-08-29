/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.Moments.Variance

/-!
# Conditional variance

This file defines the variance of a real-valued random variable conditional to a sigma-algebra.

## TODO

Define the Lebesgue conditional variance. See
[GibbsMeasure](https://github.com/james18lpc/GibbsMeasure) for a definition of the Lebesgue
conditional expectation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory
variable {Ω : Type*} {m₀ m m' : MeasurableSpace Ω} {hm : m <= m₀} {X Y : Ω -> Real} {μ : Measure[m₀] Ω}
  {s : Set Ω}

variable (m X μ) in
/--
Definition of `condVar` / `condVar` 的定义

English:
definition condVar
  signature: : Ω -> Real
  body: μ[(X - μ[X | m]) ^ 2 | m]

@[inherit_doc] scoped notation "Var[" X "; " μ " | " m "]" => condVar m X μ

中文:
定义 condVar
  签名: : Ω -> 实数
  定义体: μ[(X - μ[X | m]) ^ 2 | m]

@[inherit_doc] scoped notation "Var[" X "; " μ " | " m "]" => condVar m X μ
-/
noncomputable def condVar : Ω -> Real := μ[(X - μ[X | m]) ^ 2 | m]

@[inherit_doc] scoped notation "Var[" X "; " μ " | " m "]" => condVar m X μ

/-- Conditional variance of a real-valued random variable. It is defined as `0` if any one of the
following conditions is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `volume` is not σ-finite with respect to `m`,
- `X - 𝔼[X | m]` is not square-integrable. -/
scoped notation "Var[" f "|" m "]" => Var[f; MeasureTheory.volume | m]

/--
lemma `condVar_of_not_le` / 引理 `condVar_of_not_le`

English:
lemma condVar_of_not_le
  given: (hm : ¬m <= m₀)
  statement: Var[X; μ | m] = 0
  proof: by rw [condVar, condExp_of_not_le hm]

中文:
引理 condVar_of_not_le
  条件: (hm : ¬m <= m₀)
  结论: Var[X; μ | m] = 0
  证明: by rw [condVar, condExp_of_not_le hm]

Depends on / 依赖: condExp_of_not_le, condVar
-/
lemma condVar_of_not_le (hm : ¬m <= m₀) : Var[X; μ | m] = 0 := by rw [condVar, condExp_of_not_le hm]

/--
lemma `condVar_of_not_sigmaFinite` / 引理 `condVar_of_not_sigmaFinite`

English:
lemma condVar_of_not_sigmaFinite
  given: (hμm : ¬SigmaFinite (μ.trim hm))
  proof: by rw [condVar, condExp_of_not_sigmaFinite hm hμm]

中文:
引理 condVar_of_not_sigmaFinite
  条件: (hμm : ¬σ有限 (μ.trim hm))
  证明: by rw [condVar, condExp_of_not_sigmaFinite hm hμm]

Depends on / 依赖: condExp_of_not_sigmaFinite, condVar
-/
lemma condVar_of_not_sigmaFinite (hμm : ¬SigmaFinite (μ.trim hm)) :
    Var[X; μ | m] = 0 := by rw [condVar, condExp_of_not_sigmaFinite hm hμm]

open scoped Classical in
/--
lemma `condVar_of_sigmaFinite` / 引理 `condVar_of_sigmaFinite`

English:
lemma condVar_of_sigmaFinite
  given: [SigmaFinite (μ.trim hm)]
  proof: condExp_of_sigmaFinite _

中文:
引理 condVar_of_sigmaFinite
  条件: [σ有限 (μ.trim hm)]
  证明: condExp_of_sigmaFinite _

Depends on / 依赖: condExp_of_sigmaFinite
-/
lemma condVar_of_sigmaFinite [SigmaFinite (μ.trim hm)] :
    Var[X; μ | m] =
      if Integrable (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ then
        if StronglyMeasurable[m] (fun ω => (X ω - (μ[X | m]) ω) ^ 2) then
          fun ω => (X ω - (μ[X | m]) ω) ^ 2
        else aestronglyMeasurable_condExpL1.mk (condExpL1 hm μ fun ω => (X ω - (μ[X | m]) ω) ^ 2)
      else 0 := condExp_of_sigmaFinite _

/--
lemma `condVar_of_stronglyMeasurable` / 引理 `condVar_of_stronglyMeasurable`

English:
lemma condVar_of_stronglyMeasurable
  statement: [SigmaFinite (μ.trim hm)]
  proof: condExp_of_stronglyMeasurable _ ((hX.sub stronglyMeasurable_condExp).pow _) hXint

中文:
引理 condVar_of_stronglyMeasurable
  结论: [σ有限 (μ.trim hm)]
  证明: condExp_of_stronglyMeasurable _ ((hX.sub stronglyMeasurable_condExp).pow _) hXint

Depends on / 依赖: condExp_of_stronglyMeasurable, hX.sub, stronglyMeasurable_condExp
-/
lemma condVar_of_stronglyMeasurable [SigmaFinite (μ.trim hm)]
    (hX : StronglyMeasurable[m] X) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) :
    Var[X; μ | m] = fun ω => (X ω - (μ[X | m]) ω) ^ 2 :=
  condExp_of_stronglyMeasurable _ ((hX.sub stronglyMeasurable_condExp).pow _) hXint

/--
lemma `condVar_of_not_integrable` / 引理 `condVar_of_not_integrable`

English:
lemma condVar_of_not_integrable
  given: (hXint : ¬ Integrable (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ)
  proof: condExp_of_not_integrable hXint

中文:
引理 condVar_of_not_integrable
  条件: (hXint : ¬ 可积 (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ)
  证明: condExp_of_not_integrable hXint

Depends on / 依赖: condExp_of_not_integrable
-/
lemma condVar_of_not_integrable (hXint : ¬ Integrable (fun ω => (X ω - (μ[X | m]) ω) ^ 2) μ) :
    Var[X; μ | m] = 0 := condExp_of_not_integrable hXint

/--
lemma `condVar_zero` / 引理 `condVar_zero`

English:
lemma condVar_zero
  statement: Var[0; μ | m] = 0
  proof: by simp [condVar]

@[simp]

中文:
引理 condVar_zero
  结论: Var[0; μ | m] = 0
  证明: by simp [condVar]

@[simp]
-/
@[simp] lemma condVar_zero : Var[0; μ | m] = 0 := by simp [condVar]

@[simp]
/--
lemma `condVar_const` / 引理 `condVar_const`

English:
lemma condVar_const
  given: (hm : m <= m₀) (c : Real)
  statement: Var[fun _ => c; μ | m] = 0
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simp [← Pi.zero_def]
  by_cases hμm : IsFiniteMeasure μ
  · simp [condVar, hm]
  · simp [condVar, condExp_of_not_integrable, integrable_const_iff_isFiniteMeasure hc,
integrable_const_iff_isFiniteMeasure pow_ne_zero _ hc, hμm, Pi.pow_def]

中文:
引理 condVar_const
  条件: (hm : m <= m₀) (c : 实数)
  结论: Var[fun _ => c; μ | m] = 0
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simp [← Pi.zero_def]
  by_cases hμm : IsFiniteMeasure μ
  · simp [condVar, hm]
  · simp [condVar, condExp_of_not_integrable, integrable_const_iff_isFiniteMeasure hc,
integrable_const_iff_isFiniteMeasure pow_ne_zero _ hc, hμm, Pi.pow_def]

Depends on / 依赖: IsFiniteMeasure, Pi.pow_def, Pi.zero_def, condExp_of_not_integrable, condVar, eq_or_ne, integrable_const_iff_isFiniteMeasure, pow_def, pow_ne_zero, zero_def
-/
lemma condVar_const (hm : m <= m₀) (c : Real) : Var[fun _ => c; μ | m] = 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [← Pi.zero_def]
  by_cases hμm : IsFiniteMeasure μ
  · simp [condVar, hm]
  · simp [condVar, condExp_of_not_integrable, integrable_const_iff_isFiniteMeasure hc,
integrable_const_iff_isFiniteMeasure pow_ne_zero _ hc, hμm, Pi.pow_def]

/--
lemma `stronglyMeasurable_condVar` / 引理 `stronglyMeasurable_condVar`

English:
lemma stronglyMeasurable_condVar
  statement: StronglyMeasurable[m] (Var[X; μ | m])
  proof: stronglyMeasurable_condExp

中文:
引理 stronglyMeasurable_condVar
  结论: StronglyMeasurable[m] (Var[X; μ | m])
  证明: stronglyMeasurable_condExp

Depends on / 依赖: stronglyMeasurable_condExp
-/
lemma stronglyMeasurable_condVar : StronglyMeasurable[m] (Var[X; μ | m]) :=
  stronglyMeasurable_condExp

/--
lemma `condVar_congr_ae` / 引理 `condVar_congr_ae`

English:
lemma condVar_congr_ae
  given: (h : X =ᵐ[μ] Y)
  statement: Var[X; μ | m] =ᵐ[μ] Var[Y; μ | m]
  proof: condExp_congr_ae by filter_upwards [h, condExp_congr_ae h] with ω hω hω'; dsimp; rw [hω, hω']

中文:
引理 condVar_congr_ae
  条件: (h : X =ᵐ[μ] Y)
  结论: Var[X; μ | m] =ᵐ[μ] Var[Y; μ | m]
  证明: condExp_congr_ae by filter_upwards [h, condExp_congr_ae h] with ω hω hω'; dsimp; rw [hω, hω']

Depends on / 依赖: condExp_congr_ae, filter_upwards
-/
lemma condVar_congr_ae (h : X =ᵐ[μ] Y) : Var[X; μ | m] =ᵐ[μ] Var[Y; μ | m] :=
condExp_congr_ae by filter_upwards [h, condExp_congr_ae h] with ω hω hω'; dsimp; rw [hω, hω']

/--
lemma `condVar_of_aestronglyMeasurable` / 引理 `condVar_of_aestronglyMeasurable`

English:
lemma condVar_of_aestronglyMeasurable
  statement: [hμm : SigmaFinite (μ.trim hm)]
  proof: condExp_of_aestronglyMeasurable' _ ((continuous_pow _).comp_aestronglyMeasurable
    (hX.sub stronglyMeasurable_condExp.aestronglyMeasurable)) hXint

中文:
引理 condVar_of_aestronglyMeasurable
  结论: [hμm : σ有限 (μ.trim hm)]
  证明: condExp_of_aestronglyMeasurable' _ ((continuous_pow _).comp_aestronglyMeasurable
    (hX.sub stronglyMeasurable_condExp.aestronglyMeasurable)) hXint

Depends on / 依赖: aestronglyMeasurable, comp_aestronglyMeasurable, condExp_of_aestronglyMeasurable, continuous_pow, hX.sub, stronglyMeasurable_condExp, stronglyMeasurable_condExp.aestronglyMeasurable
-/
lemma condVar_of_aestronglyMeasurable [hμm : SigmaFinite (μ.trim hm)]
    (hX : AEStronglyMeasurable[m] X μ) (hXint : Integrable ((X - μ[X | m]) ^ 2) μ) :
    Var[X; μ | m] =ᵐ[μ] (X - μ[X | m]) ^ 2 :=
  condExp_of_aestronglyMeasurable' _ ((continuous_pow _).comp_aestronglyMeasurable
    (hX.sub stronglyMeasurable_condExp.aestronglyMeasurable)) hXint

/--
lemma `integrable_condVar` / 引理 `integrable_condVar`

English:
lemma integrable_condVar
  statement: Integrable Var[X; μ | m] μ
  proof: integrable_condExp

中文:
引理 integrable_condVar
  结论: 可积 Var[X; μ | m] μ
  证明: integrable_condExp

Depends on / 依赖: integrable_condExp
-/
lemma integrable_condVar : Integrable Var[X; μ | m] μ := integrable_condExp

/--
lemma `setIntegral_condVar` / 引理 `setIntegral_condVar`

English:
lemma setIntegral_condVar
  statement: [SigmaFinite (μ.trim hm)] (hX : Integrable ((X - μ[X | m]) ^ 2) μ)
  proof: setIntegral_condExp _ hX hs

中文:
引理 set整数egral_condVar
  结论: [σ有限 (μ.trim hm)] (hX : 可积 ((X - μ[X | m]) ^ 2) μ)
  证明: setIntegral_condExp _ hX hs

Depends on / 依赖: setIntegral_condExp
-/
lemma setIntegral_condVar [SigmaFinite (μ.trim hm)] (hX : Integrable ((X - μ[X | m]) ^ 2) μ)
    (hs : MeasurableSet[m] s) :
    ∫ ω in s, (Var[X; μ | m]) ω ∂μ = ∫ ω in s, (X ω - (μ[X | m]) ω) ^ 2 ∂μ :=
  setIntegral_condExp _ hX hs

-- `(· ^ 2)` is a postfix operator called `_sq` in lemma names, but
-- `condVar_ae_eq_condExp_sq_sub_condExp_sq` is a bit ridiculous, so we exceptionally denote it by
-- `sq_` as it were a prefix.
/--
lemma `condVar_ae_eq_condExp_sq_sub_sq_condExp` / 引理 `condVar_ae_eq_condExp_sq_sub_sq_condExp`

English:
lemma condVar_ae_eq_condExp_sq_sub_sq_condExp
  given: (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  proof: by
  calc
    Var[X; μ | m]
    _ = μ[X ^ 2 - 2 * X * μ[X | m] + μ[X | m] ^ 2 | m] := by rw [condVar, sub_sq]
    _ =ᵐ[μ] μ[X ^ 2 | m] - 2 * μ[X | m] ^ 2 + μ[X | m] ^ 2 := by
      have aux₀ : Integrable (X ^ 2) μ := hX.integrable_sq
      have aux₁ : Integrable (2 * X * μ[X | m]) μ := by
        rw

中文:
引理 condVar_ae_eq_condExp_sq_sub_sq_condExp
  条件: (hm : m <= m₀) [是有限测度 μ] (hX : MemLp X 2 μ)
  证明: by
  calc
    Var[X; μ | m]
    _ = μ[X ^ 2 - 2 * X * μ[X | m] + μ[X | m] ^ 2 | m] := by rw [condVar, sub_sq]
    _ =ᵐ[μ] μ[X ^ 2 | m] - 2 * μ[X | m] ^ 2 + μ[X | m] ^ 2 := by
      have aux₀ : Integrable (X ^ 2) μ := hX.integrable_sq
      have aux₁ : Integrable (2 * X * μ[X | m]) μ := by
        rw

Depends on / 依赖: Integrable, condExp, condExp_add, condVar, const_mul, filter_upwards, hX.condExp, hX.integrable_sq, integrable_sq, memLp_one_iff_integrable, mul_assoc, one_le_two, sub_sq
-/
lemma condVar_ae_eq_condExp_sq_sub_sq_condExp (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 := by
  calc
    Var[X; μ | m]
    _ = μ[X ^ 2 - 2 * X * μ[X | m] + μ[X | m] ^ 2 | m] := by rw [condVar, sub_sq]
    _ =ᵐ[μ] μ[X ^ 2 | m] - 2 * μ[X | m] ^ 2 + μ[X | m] ^ 2 := by
      have aux₀ : Integrable (X ^ 2) μ := hX.integrable_sq
      have aux₁ : Integrable (2 * X * μ[X | m]) μ := by
        rw [mul_assoc]
        exact (memLp_one_iff_integrable.1 <| (hX.condExp one_le_two).mul hX).const_mul _
      have aux₂ : Integrable (μ[X | m] ^ 2) μ := (hX.condExp one_le_two).integrable_sq
      filter_upwards [condExp_add (m := m) (aux₀.sub aux₁) aux₂, condExp_sub (m := m) aux₀ aux₁,
        condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp aux₁
          ((hX.integrable one_le_two).const_mul _), condExp_ofNat (m := m) 2 X]
        with ω hω₀ hω₁ hω₂ hω₃
      simp [hω₀, hω₁, hω₂, hω₃,
        condExp_of_stronglyMeasurable hm (stronglyMeasurable_condExp.pow _) aux₂]
      simp [mul_assoc, sq]
    _ = μ[X ^ 2 | m] - μ[X | m] ^ 2 := by ring

/--
lemma `condVar_ae_le_condExp_sq` / 引理 `condVar_ae_le_condExp_sq`

English:
lemma condVar_ae_le_condExp_sq
  given: (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
  proof: by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX] with ω hω
  dsimp at hω
  nlinarith

中文:
引理 condVar_ae_le_condExp_sq
  条件: (hm : m <= m₀) [是有限测度 μ] (hX : MemLp X 2 μ)
  证明: by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX] with ω hω
  dsimp at hω
  nlinarith

Depends on / 依赖: condVar_ae_eq_condExp_sq_sub_sq_condExp, filter_upwards
-/
lemma condVar_ae_le_condExp_sq (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ | m] <=ᵐ[μ] μ[X ^ 2 | m] := by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX] with ω hω
  dsimp at hω
  nlinarith

/--
lemma `integral_condVar_add_variance_condExp` / 引理 `integral_condVar_add_variance_condExp`

English:
lemma integral_condVar_add_variance_condExp
  statement: (hm : m <= m₀) [IsProbabilityMeasure μ]
  proof: by
  calc
    μ[Var[X; μ | m]] + Var[μ[X | m]; μ]
    _ = μ[(μ[X ^ 2 | m] - μ[X | m] ^ 2 : Ω -> Real)] + (μ[μ[X | m] ^ 2] - μ[μ[X | m]] ^ 2) := by
      congr 1
· exact integral_congr_ae condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX
      · exact variance_eq_sub (hX.condExp one_le_two)
    _ = μ[X ^

中文:
引理 integral_condVar_add_variance_condExp
  结论: (hm : m <= m₀) [是概率测度 μ]
  证明: by
  calc
    μ[Var[X; μ | m]] + Var[μ[X | m]; μ]
    _ = μ[(μ[X ^ 2 | m] - μ[X | m] ^ 2 : Ω -> Real)] + (μ[μ[X | m] ^ 2] - μ[μ[X | m]] ^ 2) := by
      congr 1
· exact integral_congr_ae condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX
      · exact variance_eq_sub (hX.condExp one_le_two)
    _ = μ[X ^

Depends on / 依赖: condExp, condVar_ae_eq_condExp_sq_sub_sq_condExp, hX.condExp, integrable_condExp, integrable_sq, integral_condExp, integral_congr_ae, integral_sub, one_le_two, variance_, variance_eq_sub
-/
lemma integral_condVar_add_variance_condExp (hm : m <= m₀) [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) : μ[Var[X; μ | m]] + Var[μ[X | m]; μ] = Var[X; μ] := by
  calc
    μ[Var[X; μ | m]] + Var[μ[X | m]; μ]
    _ = μ[(μ[X ^ 2 | m] - μ[X | m] ^ 2 : Ω -> Real)] + (μ[μ[X | m] ^ 2] - μ[μ[X | m]] ^ 2) := by
      congr 1
· exact integral_congr_ae condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX
      · exact variance_eq_sub (hX.condExp one_le_two)
    _ = μ[X ^ 2] - μ[μ[X | m] ^ 2] + (μ[μ[X | m] ^ 2] - μ[X] ^ 2) := by
      rw [integral_sub' integrable_condExp]; rw [integral_condExp hm]; rw [integral_condExp hm]
      exact (hX.condExp one_le_two).integrable_sq
    _ = Var[X; μ] := by rw [variance_eq_sub hX]; ring

/--
lemma `condVar_bot'` / 引理 `condVar_bot'`

English:
lemma condVar_bot'
  given: [NeZero μ] (X : Ω -> Real)
  proof: by
  simp [condVar, condExp_bot', average, measureReal_def]

中文:
引理 condVar_bot'
  条件: [NeZero μ] (X : Ω -> 实数)
  证明: by
  simp [condVar, condExp_bot', average, measureReal_def]

Depends on / 依赖: average, condExp_bot, condVar, measureReal_def
-/
lemma condVar_bot' [NeZero μ] (X : Ω -> Real) :
    Var[X; μ | ⊥] = fun _ => ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ := by
  simp [condVar, condExp_bot', average, measureReal_def]

/--
lemma `condVar_bot_ae_eq` / 引理 `condVar_bot_ae_eq`

English:
lemma condVar_bot_ae_eq
  given: (X : Ω -> Real)
  proof: by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · rw [ae_zero]
    exact eventually_bot
· exact .of_forall congr_fun (condVar_bot' X)

@[simp]

中文:
引理 condVar_bot_ae_eq
  条件: (X : Ω -> 实数)
  证明: by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · rw [ae_zero]
    exact eventually_bot
· exact .of_forall congr_fun (condVar_bot' X)

@[simp]

Depends on / 依赖: ae_zero, condVar_bot, congr_fun, eq_zero_or_neZero, eventually_bot, of_forall
-/
lemma condVar_bot_ae_eq (X : Ω -> Real) :
    Var[X; μ | ⊥] =ᵐ[μ] fun _ => ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ := by
  obtain rfl | hμ := eq_zero_or_neZero μ
  · rw [ae_zero]
    exact eventually_bot
· exact .of_forall congr_fun (condVar_bot' X)

@[simp]
/--
lemma `condVar_bot` / 引理 `condVar_bot`

English:
lemma condVar_bot
  given: [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
  proof: by
  simp [condVar_bot', average_eq_integral, variance_eq_integral hX]

中文:
引理 condVar_bot
  条件: [是概率测度 μ] (hX : 几乎处处可测 X μ)
  证明: by
  simp [condVar_bot', average_eq_integral, variance_eq_integral hX]

Depends on / 依赖: average_eq_integral, condVar_bot, variance_eq_integral
-/
lemma condVar_bot [IsProbabilityMeasure μ] (hX : AEMeasurable X μ) :
    Var[X; μ | ⊥] = fun _ω => Var[X; μ] := by
  simp [condVar_bot', average_eq_integral, variance_eq_integral hX]

/--
lemma `condVar_smul` / 引理 `condVar_smul`

English:
lemma condVar_smul
  given: (c : Real) (X : Ω -> Real)
  statement: Var[c • X; μ | m] =ᵐ[μ] c ^ 2 • Var[X; μ | m]
  proof: by
  calc
    Var[c • X; μ | m]
    _ =ᵐ[μ] μ[c ^ 2 • (X - μ[X | m]) ^ 2 | m] := by
      rw [condVar]
      refine condExp_congr_ae ?_
      filter_upwards [condExp_smul (m := m) c X] with ω hω
      simp [hω, ← mul_sub, mul_pow]
    _ =ᵐ[μ] c ^ 2 • Var[X; μ | m] := condExp_smul ..

中文:
引理 condVar_smul
  条件: (c : 实数) (X : Ω -> 实数)
  结论: Var[c • X; μ | m] =ᵐ[μ] c ^ 2 • Var[X; μ | m]
  证明: by
  calc
    Var[c • X; μ | m]
    _ =ᵐ[μ] μ[c ^ 2 • (X - μ[X | m]) ^ 2 | m] := by
      rw [condVar]
      refine condExp_congr_ae ?_
      filter_upwards [condExp_smul (m := m) c X] with ω hω
      simp [hω, ← mul_sub, mul_pow]
    _ =ᵐ[μ] c ^ 2 • Var[X; μ | m] := condExp_smul ..

Depends on / 依赖: condExp_congr_ae, condExp_smul, condVar, filter_upwards, mul_pow, mul_sub
-/
lemma condVar_smul (c : Real) (X : Ω -> Real) : Var[c • X; μ | m] =ᵐ[μ] c ^ 2 • Var[X; μ | m] := by
  calc
    Var[c • X; μ | m]
    _ =ᵐ[μ] μ[c ^ 2 • (X - μ[X | m]) ^ 2 | m] := by
      rw [condVar]
      refine condExp_congr_ae ?_
      filter_upwards [condExp_smul (m := m) c X] with ω hω
      simp [hω, ← mul_sub, mul_pow]
    _ =ᵐ[μ] c ^ 2 • Var[X; μ | m] := condExp_smul ..

/--
lemma `condVar_neg` / 引理 `condVar_neg`

English:
lemma condVar_neg
  given: (X : Ω -> Real)
  statement: Var[-X; μ | m] =ᵐ[μ] Var[X; μ | m]
  proof: by
  refine condExp_congr_ae ?_
  filter_upwards [condExp_neg (m := m) X] with ω hω
  simp [hω]
  ring

中文:
引理 condVar_neg
  条件: (X : Ω -> 实数)
  结论: Var[-X; μ | m] =ᵐ[μ] Var[X; μ | m]
  证明: by
  refine condExp_congr_ae ?_
  filter_upwards [condExp_neg (m := m) X] with ω hω
  simp [hω]
  ring
-/
@[simp] lemma condVar_neg (X : Ω -> Real) : Var[-X; μ | m] =ᵐ[μ] Var[X; μ | m] := by
  refine condExp_congr_ae ?_
  filter_upwards [condExp_neg (m := m) X] with ω hω
  simp [hω]
  ring

end ProbabilityTheory
