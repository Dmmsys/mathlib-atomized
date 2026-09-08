/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.Risk.Defs

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Risk in countable spaces

In countable spaces, we can write integrals as sums, hence we can write the average or Bayes risk
with sums instead of integrals.

-/

public section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

/-
**ProbabilityTheory.avgRisk_countable** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：avgRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] : avgRisk ℓ P
 κ π = ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_countable'`：lintegral_countable' [Countable α] [
MeasurableSingletonClass α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂μ = ∑' a, f a * μ {
a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma avgRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    avgRisk ℓ P κ π = ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [avgRisk, lintegral_countable']
/-
**ProbabilityTheory.avgRisk_fintype** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：avgRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] : avgRisk ℓ P κ π
 = ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_fintype`：lintegral_fintype [MeasurableSingletonC
lass α] [Fintype α] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma avgRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    avgRisk ℓ P κ π = ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [avgRisk, lintegral_fintype]
/-
**ProbabilityTheory.avgRisk_countable'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：avgRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measur
able ℓ) : avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
参数：hℓ : Measurable ℓ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_countable'`：lintegral_countable' [Countable α] [
MeasurableSingletonClass α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂μ = ∑' a, f a * μ {
a}
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
lemma avgRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp only [avgRisk, lintegral_countable']
  rw [lintegral_tsum]
  · rfl
  · refine fun y ↦ Measurable.aemeasurable ?_
    exact Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))
/-
**ProbabilityTheory.avgRisk_fintype'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：avgRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable
 ℓ) : avgRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
参数：hℓ : Measurable ℓ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_countable'`：avgRisk_countable' [Countable 𝓨] [
MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) : avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, 
ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
lemma avgRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    avgRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  rw [avgRisk_countable' hℓ, tsum_fintype]
/-
**ProbabilityTheory.bayesRisk_countable** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：bayesRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] : bayesRisk
 ℓ P π = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P
) θ)) * π {θ}
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_countable`：avgRisk_countable [Countable Θ] [Me
asurableSingletonClass Θ] : avgRisk ℓ P κ π = ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) 
* π {θ}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRisk, avgRisk_countable]
/-
**ProbabilityTheory.bayesRisk_fintype** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：bayesRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] : bayesRisk ℓ P
 π = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ))
 * π {θ}
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_fintype`：avgRisk_fintype [Fintype Θ] [Measurab
leSingletonClass Θ] : avgRisk ℓ P κ π = ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRisk, avgRisk_fintype]
/-
**ProbabilityTheory.bayesRisk_countable'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：bayesRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Meas
urable ℓ) : bayesRisk ℓ P π = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' y, ∫
⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
参数：hℓ : Measurable ℓ。
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_countable'`：avgRisk_countable' [Countable 𝓨] [
MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) : avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, 
ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRisk, avgRisk_countable' hℓ]
/-
**ProbabilityTheory.bayesRisk_fintype'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：bayesRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurab
le ℓ) : bayesRisk ℓ P π = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ y, ∫⁻ θ, 
ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
参数：hℓ : Measurable ℓ。
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
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ProbabilityTheory.avgRisk_fintype'`：avgRisk_fintype' [Fintype 𝓨] [Measur
ableSingletonClass 𝓨] (hℓ : Measurable ℓ) : avgRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y *
 (κ ∘ₘ P θ) {y} ∂π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bayesRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRisk, avgRisk_fintype' hℓ]

section Const

/-
**ProbabilityTheory.avgRisk_const_of_countable** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：avgRisk_const_of_countable [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ 
: Measurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : avgRisk ℓ (Ke
rnel.const Θ μ) κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π
参数：hℓ : Measurable ℓ；μ : Measure 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_countable'`：avgRisk_countable' [Countable 𝓨] [
MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) : avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, 
ℓ θ y * (κ ∘ₘ P θ) {y} ∂π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma avgRisk_const_of_countable [Countable 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [avgRisk_countable' hℓ]
/-
**ProbabilityTheory.avgRisk_const_of_fintype** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：avgRisk_const_of_fintype [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Me
asurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : avgRisk ℓ (Kernel
.const Θ μ) κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π
参数：hℓ : Measurable ℓ；μ : Measure 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_fintype'`：avgRisk_fintype' [Fintype 𝓨] [Measur
ableSingletonClass 𝓨] (hℓ : Measurable ℓ) : avgRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y *
 (κ ∘ₘ P θ) {y} ∂π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma avgRisk_const_of_fintype [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [avgRisk_fintype' hℓ]

end Const

end ProbabilityTheory

