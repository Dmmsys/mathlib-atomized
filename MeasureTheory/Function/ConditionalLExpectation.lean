/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Notation

/-! # Conditional Lebesgue expectation

We define the conditional expectation of a `ℝ≥0∞`-valued function using the Lebesgue integral.
Given a measure `P : Measure[mΩ₀] Ω` and a sub-σ-algebra `mΩ` of `mΩ₀` (meaning `hm : mΩ ≤ mΩ₀`)
and a function `X : Ω → ℝ≥0∞`, if `P.trim hm` is σ-finite, then the conditional (Lebesgue)
expectation `P⁻[X|mΩ]` of `X` is the `mΩ`-measurable function such that for all
`mΩ`-measurable sets `s`, `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`
(see `setLIntegral_condLExp`). This is unique up to `P`-ae equality (see `ae_eq_condLExp`).

## Main definitions

* `condLExp` : conditional (Lebesgue) expectation of `X` with respect to `mΩ`.
* `setLIntegral_condLExp`: For any `mΩ`-measurable set `s`,
  `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`.
* `ae_eq_condLExp` : the conditional (Lebesgue) expectation is characterized by its (Lebesgue)
  integral on `mΩ`-measurable sets up to `P`-ae equality.

## Notation

For a measure `P : Measure[mΩ₀] Ω`, and another `mΩ : MeasurableSpace Ω`, we define the notation
* `P⁻[X|mΩ] = condLExp mΩ P X`

## Design decisions

`P⁻[X|mΩ]` is assigned the junk value `0` when either `¬ mΩ ≤ mΩ₀` (`mΩ` is not a sub-σ-algebra)
or `h : mΩ ≤ mΩ₀` but `¬ SigmaFinite (P.trim hm)` (the latter always holds when `P` is a
probability measure). When both these hold, in some sense the "user definition" of `P⁻[X|mΩ]`
should be considered "the" measurable function which satisfies `setLIntegral_condLExp`
(which is proven unique up to `P`-ae measurable equality in `ae_eq_condLExp`). The actual definition
is just used to show existence. However for (potential) convenience the actual definition assigns
`P⁻[X|mΩ] := X` in the case when `X` is `mΩ`-measurable (which can be invoked using
`condLExp_eq_self`).

## To do

* Prove the pullout property
* Prove a dominated convergence theorem.

-/

public section

open MeasureTheory ProbabilityTheory Measure

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ₀ mΩ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞}

open scoped Classical in
/-- Conditional (Lebesgue) expectation of a function, with notation `P⁻[X|mΩ]`.

It is defined as `0` if either `¬ mΩ ≤ mΩ₀` or `hm : mΩ ≤ mΩ₀` but `¬ SigmaFinite (P.trim hm)`.

One should typically not use the definition directly.
-/
noncomputable irreducible_def condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω)
    (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  if hm : mΩ ≤ mΩ₀ then
    if SigmaFinite (P.trim hm) then
      if Measurable[mΩ] X then X else
      ∂((P.withDensity X).trim hm)/∂(P.trim hm)
    else 0
  else 0

@[inherit_doc MeasureTheory.condLExp]
scoped macro:max P:term noWs "⁻[" X:term " | " mΩ:term "]" : term =>
  `(MeasureTheory.condLExp $mΩ $P $X)

/-- Unexpander for `μ⁻[f|m]` notation. -/
@[app_unexpander MeasureTheory.condLExp]
meta def condLExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $mΩ $P $X) => `($P⁻[$X|$mΩ])
  | _ => throw ()

/-- info: P⁻[X | mΩ] : Ω → ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ]
/-- info: P⁻[X | mΩ] sorry : ℝ≥0∞ -/
#guard_msgs in
#check P⁻[X|mΩ] (sorry : Ω)

/-
**MeasureTheory.condLExp_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ₀) : P⁻[X|mΩ] = 0
参数：hm_not : ¬mΩ <= mΩ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_def`：∀ {Ω : Type u_2} {mΩ₀ : MeasurableSpace Ω} (
mΩ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (X : Ω → ENNReal),   P⁻[X 
| mΩ] =     if h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem condLExp_of_not_le (hm_not : ¬mΩ ≤ mΩ₀) : P⁻[X|mΩ] = 0 := by
  rw [condLExp, dif_neg hm_not]
/-
**MeasureTheory.condLExp_of_not_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：condLExp_of_not_sigmaFinite (hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.tr
im hm)) : P⁻[X|mΩ] = 0
参数：hm : mΩ <= mΩ₀；hμm_not : ¬SigmaFinite (P.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_def`：∀ {Ω : Type u_2} {mΩ₀ : MeasurableSpace Ω} (
mΩ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (X : Ω → ENNReal),   P⁻[X 
| mΩ] =     if h…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condLExp_of_not_sigmaFinite (hm : mΩ ≤ mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) :
    P⁻[X|mΩ] = 0 := by simp [condLExp, dif_pos hm, hμm_not]
/-
**MeasureTheory.condLExp_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_eq_self (hm : mΩ <= mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (
P.trim hm)] (hX : Measurable[mΩ] X) : P⁻[X|mΩ] = X
参数：hm : mΩ <= mΩ₀；P : Measure[mΩ₀] Ω；P.trim hm；hX : Measurable[mΩ] X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_def`：∀ {Ω : Type u_2} {mΩ₀ : MeasurableSpace Ω} (
mΩ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (X : Ω → ENNReal),   P⁻[X 
| mΩ] =     if h…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condLExp_eq_self (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (hX : Measurable[mΩ] X) : P⁻[X|mΩ] = X := by
  simp [condLExp, hm, hσ, hX]
/-
**MeasureTheory.condLExp_of_not_sub_sigma_measurable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：condLExp_of_not_sub_sigma_measurable (hm : mΩ <= mΩ₀) (P : Measure[mΩ₀] Ω)
 [hσ : SigmaFinite (P.trim hm)] {X : Ω -> Real>=0∞} (hX : ¬Measurable[mΩ] X) : P
⁻[X|mΩ] = ∂((P.withDensity X).trim hm)/∂(P.trim hm)
参数：hm : mΩ <= mΩ₀；P : Measure[mΩ₀] Ω；P.trim hm；hX : ¬Measurable[mΩ] X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_def`：∀ {Ω : Type u_2} {mΩ₀ : MeasurableSpace Ω} (
mΩ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω) (X : Ω → ENNReal),   P⁻[X 
| mΩ] =     if h…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condLExp_of_not_sub_sigma_measurable (hm : mΩ ≤ mΩ₀) (P : Measure[mΩ₀] Ω)
    [hσ : SigmaFinite (P.trim hm)] {X : Ω → ℝ≥0∞} (hX : ¬Measurable[mΩ] X) :
    P⁻[X|mΩ] = ∂((P.withDensity X).trim hm)/∂(P.trim hm) := by
  simp [condLExp, hm, hσ, hX]

@[fun_prop]
/-
**MeasureTheory.measurable_condLExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -
> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
参数：mΩ : MeasurableSpace Ω；P : Measure[mΩ₀] Ω；X : Ω -> Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_eq_self`：condLExp_eq_self (hm : mΩ <= mΩ₀) (P : M
easure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (hX : Measurable[mΩ] X) : P⁻[X|mΩ]
 = X
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.condLExp_of_not_sub_sigma_measurable`：condLExp_of_not_sub_
sigma_measurable (hm : mΩ <= mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim
 hm)] {X : Ω -> Real>=0∞} (hX : ¬Measura…
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem measurable_condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · by_cases hX : Measurable[mΩ] X
      · simp [condLExp_eq_self hm, hX]
      simp [condLExp_of_not_sub_sigma_measurable hm _ hX, measurable_rnDeriv]
    simp [condLExp_of_not_sigmaFinite hm hσ, measurable_zero]
  simp [condLExp_of_not_le hm, measurable_zero]

@[fun_prop]
/-
**MeasureTheory.measurable_condLExp'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_condLExp' (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω 
-> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
参数：mΩ : MeasurableSpace Ω；P : Measure[mΩ₀] Ω；X : Ω -> Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem measurable_condLExp' (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    Measurable[mΩ₀] P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · exact (measurable_condLExp _ _ _).mono hm (le_refl _)
  · simp [condLExp_of_not_le hm, measurable_zero]

variable (hm : mΩ ≤ mΩ₀)

/-- The (Lebesgue) integral of the conditional (Lebesgue) expectation `P⁻[X|mΩ]` over an
`mΩ`-measurable set is equal to the integral of `X` on that set. -/
/-
**MeasureTheory.setLIntegral_condLExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] 
(X : Ω -> Real>=0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) : ∫⁻ ω in s, P⁻[X|mΩ]
 ω ∂P = ∫⁻ ω in s, X ω ∂P
参数：P : Measure[mΩ₀] Ω；P.trim hm；X : Ω -> Real>=0∞；hs : MeasurableSet[mΩ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condLExp_eq_self`：condLExp_eq_self (hm : mΩ <= mΩ₀) (P : M
easure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (hX : Measurable[mΩ] X) : P⁻[X|mΩ]
 = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trim`：∀ {α : Type u_1} {m m0 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν
 → ∀ (hm : m ≤ m0), (μ.trim hm).Absol…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.sFinite_of_absolutelyContinuous`：sFinite_of_absolutelyCont
inuous {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν) : SFinite μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.condLExp_of_not_sub_sigma_measurable`：condLExp_of_not_sub_
sigma_measurable (hm : mΩ <= mΩ₀) (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim
 hm)] {X : Ω -> Real>=0∞} (hX : ¬Measura…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_trim`：lintegral_trim {μ : Measure α} (hm : m <= 
m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f 
a ∂μ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv'`：setLIntegral_rnDeriv' [Have
LebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) : ∫⁻
 x in s, μ.rnDeriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ

--- 原说明 ---
The (Lebesgue) integral of the conditional (Lebesgue) expectation `P⁻[X|mΩ]` ove
r an
`mΩ`-measurable set is equal to the integral of `X` on that set.
-/
theorem setLIntegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P := by
  by_cases hX : Measurable[mΩ] X
  · simp [condLExp_eq_self hm _ hX]
  have h := AbsolutelyContinuous.trim (withDensity_absolutelyContinuous P X) hm
  have : SFinite ((P.withDensity X).trim hm) := sFinite_of_absolutelyContinuous h
  rw [condLExp_of_not_sub_sigma_measurable hm _ hX, ← lintegral_indicator (hm s hs),
    ← lintegral_trim hm (by measurability), lintegral_indicator hs, setLIntegral_rnDeriv' h hs,
    trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs)]
/-
**MeasureTheory.setLIntegral_condLExp_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setLIntegral_condLExp_trim (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim 
hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) : ∫⁻ ω in s, P⁻[
X|mΩ] ω ∂P.trim hm = ∫⁻ ω in s, X ω ∂P
参数：P : Measure[mΩ₀] Ω；P.trim hm；X : Ω -> Real>=0∞；hs : MeasurableSet[mΩ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_trim`：setLIntegral_trim {μ : Measure α} (hm :
 m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) {s : Set α} (hs : Measurabl
eSet[m] s) : ∫⁻ x in …
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
-/
theorem setLIntegral_condLExp_trim (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    ∫⁻ ω in s, P⁻[X|mΩ] ω ∂P.trim hm = ∫⁻ ω in s, X ω ∂P := by
  rw [setLIntegral_trim hm (measurable_condLExp _ _ _) hs, setLIntegral_condLExp _ _ _ hs]
/-
**MeasureTheory.lintegral_condLExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X 
: Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ ω, X ω ∂P
参数：P : Measure[mΩ₀] Ω；P.trim hm；X : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem lintegral_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) :
    ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ ω, X ω ∂P := by
  simpa [← setLIntegral_univ] using setLIntegral_condLExp _ _ _ .univ
/-
**MeasureTheory.condLExp_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_lt_top {f : Ω -> Real>=0∞} (hf : ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂
P, P⁻[f|mΩ] x < ∞
参数：hf : ∫⁻ x, f x ∂P != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_lt_top'`：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_condLExp`：lintegral_condLExp (P : Measure[mΩ₀] Ω
) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ 
ω, X ω ∂P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
lemma condLExp_lt_top {f : Ω → ℝ≥0∞} (hf : ∫⁻ x, f x ∂P ≠ ∞) : ∀ᵐ x ∂P, P⁻[f|mΩ] x < ∞ := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  · exact ae_lt_top' (by fun_prop) (by rwa [lintegral_condLExp])
  · simp [condLExp_of_not_sigmaFinite hm hσ]
/-
**MeasureTheory.condLExp_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_ne_top {f : Ω -> Real>=0∞} (hf : ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂
P, P⁻[f|mΩ] x != ∞
参数：hf : ∫⁻ x, f x ∂P != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.condLExp_lt_top`：condLExp_lt_top {f : Ω -> Real>=0∞} (hf :
 ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂P, P⁻[f|mΩ] x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma condLExp_ne_top {f : Ω → ℝ≥0∞} (hf : ∫⁻ x, f x ∂P ≠ ∞) : ∀ᵐ x ∂P, P⁻[f|mΩ] x ≠ ∞ := by
  filter_upwards [condLExp_lt_top hf] with x hx using hx.ne
/-
**MeasureTheory.ae_eq_condLExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω 
-> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : forall s, MeasurableSet[mΩ] s -> ∫⁻ 
ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) : Y =ᵐ[P] P⁻[X|mΩ]
参数：P : Measure[mΩ₀] Ω；P.trim hm；X : Ω -> Real>=0∞；hY : Measurable[mΩ] Y；hXY : fo
rall s, MeasurableSet[mΩ] s -> ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_condLExp₀`：ae_eq_condLExp₀ {P : Measure[mΩ₀] Ω} [hσ 
: SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : AEMeasurable[mΩ] Y (P.trim 
hm)) (hXY : forall …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_eq_condLExp₀ {P : Measure[mΩ₀] Ω} [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) (hY : AEMeasurable[mΩ] Y (P.trim hm))
    (hXY : ∀ s, MeasurableSet[mΩ] s → ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) :
    Y =ᵐ[P] P⁻[X|mΩ] := by
  apply ae_eq_of_ae_eq_trim
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hY (by fun_prop)
  intro s hs _
  rw [setLIntegral_trim_ae hm hY hs, setLIntegral_condLExp_trim _ _ _ hs]
  exact hXY s hs

/-- The conditional (Lebesgue) expectation `P⁻[X|mΩ]` is defined uniquely as an `mΩ`-measurable
function up to `P`-ae equality by its (Lebesgue) integral over all `mΩ`-measurable sets. -/
/-
**MeasureTheory.ae_eq_condLExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω 
-> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : forall s, MeasurableSet[mΩ] s -> ∫⁻ 
ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) : Y =ᵐ[P] P⁻[X|mΩ]
参数：P : Measure[mΩ₀] Ω；P.trim hm；X : Ω -> Real>=0∞；hY : Measurable[mΩ] Y；hXY : fo
rall s, MeasurableSet[mΩ] s -> ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_condLExp₀`：ae_eq_condLExp₀ {P : Measure[mΩ₀] Ω} [hσ 
: SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : AEMeasurable[mΩ] Y (P.trim 
hm)) (hXY : forall …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
The conditional (Lebesgue) expectation `P⁻[X|mΩ]` is defined uniquely as an `mΩ`
-measurable
function up to `P`-ae equality by its (Lebesgue) integral over all `mΩ`-measurab
le sets.
-/
theorem ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)]
    (X : Ω → ℝ≥0∞) (hY : Measurable[mΩ] Y)
    (hXY : ∀ s, MeasurableSet[mΩ] s → ∫⁻ ω in s, Y ω ∂P = ∫⁻ ω in s, X ω ∂P) :
    Y =ᵐ[P] P⁻[X|mΩ] := ae_eq_condLExp₀ _ _ hY.aemeasurable hXY
/-
**MeasureTheory.condLExp_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_const (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (c : Re
al>=0∞) : P⁻[fun _ : Ω => c|mΩ] = fun _ => c
参数：P : Measure[mΩ₀] Ω；P.trim hm；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condLExp_eq_self`：condLExp_eq_self (hm : mΩ <= mΩ₀) (P : M
easure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (hX : Measurable[mΩ] X) : P⁻[X|mΩ]
 = X
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem condLExp_const (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (c : ℝ≥0∞) :
    P⁻[fun _ : Ω ↦ c|mΩ] = fun _ ↦ c := condLExp_eq_self _ _ (measurable_const)

@[gcongr]
/-
**MeasureTheory.condLExp_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_congr_ae {P : Measure[mΩ₀] Ω} {X Y : Ω -> Real>=0∞} (hXY : X =ᵐ[P
] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ]
参数：hXY : X =ᵐ[P] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_condLExp`：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : fora
ll s, MeasurableSe…
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_congr_ae {P : Measure[mΩ₀] Ω}
    {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  · by_cases hσ : SigmaFinite (P.trim hm)
    · refine ae_eq_condLExp _ _ _ (measurable_condLExp _ _ _) (fun s hs ↦ ?_)
      rw [setLIntegral_condLExp _ _ _ hs]
      apply setLIntegral_congr_fun_ae (hm s hs)
      filter_upwards [hXY] with _ h _ using h
    simp [condLExp_of_not_sigmaFinite hm hσ]
  simp [condLExp_of_not_le hm]

@[simp]
/-
**MeasureTheory.condLExp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_zero (P : Measure[mΩ₀] Ω) : P⁻[0|mΩ] = 0
参数：P : Measure[mΩ₀] Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condLExp_const`：condLExp_const (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (c : Real>=0∞) : P⁻[fun _ : Ω => c|mΩ] = fun _ => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_zero (P : Measure[mΩ₀] Ω) : P⁻[0|mΩ] = 0 := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  exact condLExp_const hm P 0

@[simp]
/-
**MeasureTheory.condLExp_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_one (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] : P⁻[1|mΩ
] = 1
参数：P : Measure[mΩ₀] Ω；P.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.condLExp_const`：condLExp_const (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (c : Real>=0∞) : P⁻[fun _ : Ω => c|mΩ] = fun _ => c
-/
theorem condLExp_one (P : Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] :
    P⁻[1|mΩ] = 1 := condLExp_const hm P 1

@[gcongr]
/-
**MeasureTheory.condLExp_congr_ae_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：condLExp_congr_ae_trim {P : Measure[mΩ₀] Ω} {X Y : Ω -> Real>=0∞} (hXY : X
 =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P.trim hm] P⁻[Y|mΩ]
参数：hXY : X =ᵐ[P] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ae_eq_trim_of_measurable`：∀ {α : Type u_3} {β : Type u_4} {m m0 : Measur
ableSpace α} {μ : MeasureTheory.Measure α} [inst : MeasurableSpace β]   [Measura
bleEq β] (hm :…
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `MeasureTheory.condLExp_congr_ae`：condLExp_congr_ae {P : Measure[mΩ₀] Ω} 
{X Y : Ω -> Real>=0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ]
-/
theorem condLExp_congr_ae_trim {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞} (hXY : X =ᵐ[P] Y) :
    P⁻[X|mΩ] =ᵐ[P.trim hm] P⁻[Y|mΩ] := by
  apply ae_eq_trim_of_measurable hm (measurable_condLExp _ _ X) (measurable_condLExp _ _ Y)
  exact condLExp_congr_ae hXY
/-
**MeasureTheory.condLExp_bot'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_bot' (P : Measure[mΩ₀] Ω) [NeZero P] (X : Ω -> Real>=0∞) : P⁻[X|⊥
] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P
参数：P : Measure[mΩ₀] Ω；X : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_const_of_measurable_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace β] [Nonempty β] [MeasurableSpace.SeparatesPoints β] {f : α → β},   M
easurable f → ∃ …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_condLExp`：lintegral_condLExp (P : Measure[mΩ₀] Ω
) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ 
ω, X ω ∂P
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.sigmaFinite_trim_bot_iff`：sigmaFinite_trim_bot_iff : Sigma
Finite (μ.trim bot_le) ↔ IsFiniteMeasure μ
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.not_isFiniteMeasure_iff`：not_isFiniteMeasure_iff : ¬IsFini
teMeasure μ ↔ μ univ = ∞
（共 32 条，此处仅展示前 30 条）
-/
theorem condLExp_bot' (P : Measure[mΩ₀] Ω) [NeZero P] (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P := by
  by_cases hP : IsFiniteMeasure P; swap
  · have hσ : ¬SigmaFinite (P.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hP
    rw [condLExp_of_not_sigmaFinite bot_le hσ]
    simp [hP, Pi.zero_def]
  obtain ⟨c, h_eq⟩ := eq_const_of_measurable_bot (measurable_condLExp ⊥ P X)
  ext _
  rw [← lintegral_condLExp bot_le]
  simp [h_eq, mul_comm, mul_assoc, ENNReal.mul_inv_cancel
    (NeZero.ne (P .univ)) (measure_ne_top _ _)]
/-
**MeasureTheory.condLExp_bot_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_bot_ae_eq (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : P⁻[X|⊥] =ᵐ[P
] fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P
参数：P : Measure[mΩ₀] Ω；X : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condLExp_bot'`：condLExp_bot' (P : Measure[mΩ₀] Ω) [NeZero 
P] (X : Ω -> Real>=0∞) : P⁻[X|⊥] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P
-/
theorem condLExp_bot_ae_eq (P : Measure[mΩ₀] Ω) (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] =ᵐ[P] fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P := by
  rcases eq_zero_or_neZero P with rfl | hP
  · rw [ae_zero]; exact Filter.eventually_bot
  exact ae_of_all P <| congr_fun (condLExp_bot' P X)
/-
**MeasureTheory.condLExp_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_bot (P : Measure[mΩ₀] Ω) [IsProbabilityMeasure P] (X : Ω -> Real>
=0∞) : P⁻[X|⊥] = fun _ => ∫⁻ ω, X ω ∂P
参数：P : Measure[mΩ₀] Ω；X : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.condLExp_bot'`：condLExp_bot' (P : Measure[mΩ₀] Ω) [NeZero 
P] (X : Ω -> Real>=0∞) : P⁻[X|⊥] = fun _ => (P .univ)⁻¹ • ∫⁻ ω, X ω ∂P
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condLExp_bot (P : Measure[mΩ₀] Ω) [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) :
    P⁻[X|⊥] = fun _ => ∫⁻ ω, X ω ∂P :=
  (condLExp_bot' P X).trans (by simp)
/-
**MeasureTheory.condLExp_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_mono (hXY : X <=ᵐ[P] Y) : P⁻[X|mΩ] <=ᵐ[P] P⁻[Y|mΩ]
参数：hXY : X <=ᵐ[P] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_condLExp_trim`：setLIntegral_condLExp_trim (P 
: Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω}
 (hs : MeasurableSet[mΩ] s) : …
· 使用定理 `MeasureTheory.setLIntegral_mono_ae'`：setLIntegral_mono_ae' {s : Set α} {
f g : α -> Real>=0∞} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s -> f x <
= g x) : ∫⁻ x in s, f x ∂…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_mono (hXY : X ≤ᵐ[P] Y) :
    P⁻[X|mΩ] ≤ᵐ[P] P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp_rw [condLExp_of_not_le hm, Filter.EventuallyLE.rfl]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp_rw [condLExp_of_not_sigmaFinite hm hσ, Filter.EventuallyLE.rfl]
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  repeat rw [setLIntegral_condLExp_trim hm _ _ hs]
  apply setLIntegral_mono_ae' (hm s hs)
  filter_upwards [hXY] using fun _ h _ ↦ h
/-
**MeasureTheory.condLExp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_add_le (X Y : Ω -> Real>=0∞) : P⁻[X|mΩ] + P⁻[Y|mΩ] <=ᵐ[P] P⁻[X + 
Y|mΩ]
参数：X Y : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_condLExp_trim`：setLIntegral_condLExp_trim (P 
: Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω}
 (hs : MeasurableSet[mΩ] s) : …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.le_lintegral_add`：le_lintegral_add (f g : α -> Real>=0∞) :
 ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ <= ∫⁻ a, f a + g a ∂μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_add_le (X Y : Ω → ℝ≥0∞) :
    P⁻[X|mΩ] + P⁻[Y|mΩ] ≤ᵐ[P] P⁻[X + Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  simp only [Pi.add_apply]
  rw [lintegral_add_left (by fun_prop)]
  repeat rw [setLIntegral_condLExp_trim hm _ _ hs]
  grw [le_lintegral_add]
  simp
/-
**MeasureTheory.condLExp_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_add_left {X : Ω -> Real>=0∞} (Y : Ω -> Real>=0∞) (hX : AEMeasurab
le[mΩ₀] X P) : P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ]
参数：Y : Ω -> Real>=0∞；hX : AEMeasurable[mΩ₀] X P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_condLExp`：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : fora
ll s, MeasurableSe…
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_add_left {X : Ω → ℝ≥0∞} (Y : Ω → ℝ≥0∞) (hX : AEMeasurable[mΩ₀] X P) :
    P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp_rw [condLExp_of_not_le hm]; simp
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; simp
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.add_apply]
  rw [lintegral_add_left (by measurability)]
  repeat rw [setLIntegral_condLExp hm _ _ hs]
  rw [lintegral_add_left' (by fun_prop)]
/-
**MeasureTheory.condLExp_add_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_add_right (X : Ω -> Real>=0∞) {Y : Ω -> Real>=0∞} (hY : AEMeasura
ble[mΩ₀] Y P) : P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ]
参数：X : Ω -> Real>=0∞；hY : AEMeasurable[mΩ₀] Y P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.condLExp_add_left`：condLExp_add_left {X : Ω -> Real>=0∞} (
Y : Ω -> Real>=0∞) (hX : AEMeasurable[mΩ₀] X P) : P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + 
P⁻[Y|mΩ]
-/
theorem condLExp_add_right (X : Ω → ℝ≥0∞) {Y : Ω → ℝ≥0∞} (hY : AEMeasurable[mΩ₀] Y P) :
    P⁻[X + Y|mΩ] =ᵐ[P] P⁻[X|mΩ] + P⁻[Y|mΩ] := by
  rw [add_comm, add_comm P⁻[X|mΩ]]
  exact condLExp_add_left X hY
/-
**MeasureTheory.condLExp_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_smul (X : Ω -> Real>=0∞) (hX : AEMeasurable[mΩ₀] X P) (c : Real>=
0∞) : P⁻[c • X|mΩ] =ᵐ[P] c • P⁻[X|mΩ]
参数：X : Ω -> Real>=0∞；hX : AEMeasurable[mΩ₀] X P；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_condLExp`：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : fora
ll s, MeasurableSe…
· 使用定理 `Measurable.smul`：Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable 
f) (hg : Measurable g) : Measurable (f • g)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_smul (X : Ω → ℝ≥0∞) (hX : AEMeasurable[mΩ₀] X P) (c : ℝ≥0∞) :
    P⁻[c • X|mΩ] =ᵐ[P] c • P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul, lintegral_const_mul'', setLIntegral_condLExp _ _ _ hs]
  all_goals fun_prop
/-
**MeasureTheory.condLExp_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_smul_le (X : Ω -> Real>=0∞) {c : Real>=0∞} : c • P⁻[X|mΩ] <=ᵐ[P] 
P⁻[c • X|mΩ]
参数：X : Ω -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `Measurable.smul`：Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable 
f) (hg : Measurable g) : Measurable (f • g)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_condLExp_trim`：setLIntegral_condLExp_trim (P 
: Measure[mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω}
 (hs : MeasurableSet[mΩ] s) : …
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_smul_le (X : Ω → ℝ≥0∞) {c : ℝ≥0∞} :
    c • P⁻[X|mΩ] ≤ᵐ[P] P⁻[c • X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := P.trim hm) (by fun_prop)
  intro s hs _
  simp [setLIntegral_condLExp_trim _ _ _ hs, lintegral_const_mul _ (measurable_condLExp _ P X),
    lintegral_const_mul_le]
/-
**MeasureTheory.condLExp_smul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_smul' (X : Ω -> Real>=0∞) {c : Real>=0∞} (hc : c != ∞) : P⁻[c • X
|mΩ] =ᵐ[P] c • P⁻[X|mΩ]
参数：X : Ω -> Real>=0∞；hc : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_condLExp`：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : fora
ll s, MeasurableSe…
· 使用定理 `Measurable.smul`：Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable 
f) (hg : Measurable g) : Measurable (f • g)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.condLExp_of_not_le`：condLExp_of_not_le (hm_not : ¬mΩ <= mΩ
₀) : P⁻[X|mΩ] = 0
-/
theorem condLExp_smul' (X : Ω → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    P⁻[c • X|mΩ] =ᵐ[P] c • P⁻[X|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀
  swap; · simp [condLExp_of_not_le hm]
  by_cases hσ : SigmaFinite (P.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hσ]
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc, lintegral_const_mul' _ _ hc, setLIntegral_condLExp _ _ _ hs]

section Sum

variable {ι : Type*} (mΩ : MeasurableSpace Ω)

/-
**MeasureTheory.condLExp_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_tsum [Countable ι] {X : ι -> Ω -> Real>=0∞} (hX : forall i, AEMea
surable[mΩ₀] (X i) P) : P⁻[∑' i, X i|mΩ] =ᵐ[P] ∑' i, P⁻[X i|mΩ]
参数：hX : forall i, AEMeasurable[mΩ₀] (X i) P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_condLExp`：ae_eq_condLExp (P : Measure[mΩ₀] Ω) [hσ : 
SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) (hY : Measurable[mΩ] Y) (hXY : fora
ll s, MeasurableSe…
· 使用定理 `Measurable.tsum'`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst :
 MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] [
Topolo…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_apply`：∀ {ι : Type u_4} {α : Type u_5} {f : ι → α → ENNReal
} {x : α}, (∑' (i : ι), f i) x = ∑' (i : ι), f i x
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `MeasureTheory.condLExp_of_not_sigmaFinite`：condLExp_of_not_sigmaFinite (
hm : mΩ <= mΩ₀) (hμm_not : ¬SigmaFinite (P.trim hm)) : P⁻[X|mΩ] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 32 条，此处仅展示前 30 条）
-/
theorem condLExp_tsum [Countable ι] {X : ι → Ω → ℝ≥0∞}
    (hX : ∀ i, AEMeasurable[mΩ₀] (X i) P) :
    P⁻[∑' i, X i|mΩ] =ᵐ[P] ∑' i, P⁻[X i|mΩ] := by
  by_cases hm : mΩ ≤ mΩ₀; swap
  · simp_rw [condLExp_of_not_le hm]; filter_upwards; simp
  by_cases hσ : SigmaFinite (P.trim hm); swap
  · simp_rw [condLExp_of_not_sigmaFinite hm hσ]; filter_upwards; simp
  refine (ae_eq_condLExp _ _ _ (by fun_prop) ?_).symm
  intro s hs
  simp only [ENNReal.tsum_apply]
  repeat rw [lintegral_tsum (by measurability)]
  congr with i
  exact setLIntegral_condLExp hm P (X i) hs
/-
**MeasureTheory.condLExp_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_finsetSum (s : Finset ι) {X : ι -> Ω -> Real>=0∞} (hX : forall i,
 AEMeasurable[mΩ₀] (X i) P) : P⁻[∑ i in s, X i|mΩ] =ᵐ[P] ∑ i in s, P⁻[X i|mΩ]
参数：s : Finset ι；hX : forall i, AEMeasurable[mΩ₀] (X i) P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.condLExp_tsum`：condLExp_tsum [Countable ι] {X : ι -> Ω -> 
Real>=0∞} (hX : forall i, AEMeasurable[mΩ₀] (X i) P) : P⁻[∑' i, X i|mΩ] =ᵐ[P] ∑'
 i, P⁻[X i|mΩ]
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem condLExp_finsetSum (s : Finset ι) {X : ι → Ω → ℝ≥0∞}
    (hX : ∀ i, AEMeasurable[mΩ₀] (X i) P) :
    P⁻[∑ i ∈ s, X i|mΩ] =ᵐ[P] ∑ i ∈ s, P⁻[X i|mΩ] := by
  convert! condLExp_tsum mΩ (fun i : s ↦ hX i)
  · simp [Finset.sum_attach]
  · simp [Finset.sum_attach _ (f := (P⁻[X ·|mΩ]))]

@[deprecated (since := "2026-04-08")] alias condLExp_finset_sum := condLExp_finsetSum

end Sum

end MeasureTheory

