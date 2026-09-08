/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurability and integrability of the sinc function

## Main statements

* `measurable_sinc`: the sinc function is measurable.
* `integrable_sinc`: the sinc function is integrable with respect to any finite measure on `ℝ`.

-/

public section

open MeasureTheory

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : Measure α}

namespace Real

@[fun_prop]
/-
**Real.measurable_sinc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：measurable_sinc : Measurable sinc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `Real.continuous_sinc`：continuous_sinc : Continuous sinc
-/
lemma measurable_sinc : Measurable sinc := continuous_sinc.measurable

@[fun_prop]
/-
**Real.stronglyMeasurable_sinc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：stronglyMeasurable_sinc : StronglyMeasurable sinc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `Real.measurable_sinc`：measurable_sinc : Measurable sinc
-/
lemma stronglyMeasurable_sinc : StronglyMeasurable sinc := measurable_sinc.stronglyMeasurable

@[fun_prop]
/-
**Real.integrable_sinc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：integrable_sinc {μ : Measure Real} [IsFiniteMeasure μ] : Integrable sinc μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用引理 `Real.stronglyMeasurable_sinc`：stronglyMeasurable_sinc : StronglyMeasurab
le sinc
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `Real.abs_sinc_le_one`：abs_sinc_le_one (x : Real) : |sinc x| <= 1
-/
lemma integrable_sinc {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Integrable sinc μ := by
  refine Integrable.mono' (g := fun _ ↦ 1) (by fun_prop) (by fun_prop) <| ae_of_all _ fun x ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

end Real

open Real

@[fun_prop]
/-
**Measurable.sinc** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.sinc (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `Real.measurable_sinc`：measurable_sinc : Measurable sinc
-/
protected theorem Measurable.sinc (hf : Measurable f) : Measurable fun x ↦ sinc (f x) :=
  Real.measurable_sinc.comp hf

@[fun_prop]
/-
**AEMeasurable.sinc** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ} {μ : MeasureTheory.Me
asure α},   AEMeasurable f μ → AEMeasurable (fun x => Real.sinc (f x)) μ
参数：fun x => Real.sinc (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用引理 `Real.measurable_sinc`：measurable_sinc : Measurable sinc
-/
protected theorem AEMeasurable.sinc (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ sinc (f x)) μ :=
  Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.sinc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ},   MeasureTheory.Stro
nglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => Real.sinc (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `Real.stronglyMeasurable_sinc`：stronglyMeasurable_sinc : StronglyMeasurab
le sinc
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
protected theorem MeasureTheory.StronglyMeasurable.sinc (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x ↦ sinc (f x) :=
  Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.sinc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ} {μ : MeasureTheory.Me
asure α},   MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.AEStronglyMea
surable (fun x => Real.sinc (f x)) μ
参数：fun x => Real.sinc (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aestronglyMeasurable_iff_aemeasurable`：∀ {α : Type u_1} {β : Type u_2} [
inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   {f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.sinc`：∀ {α : Type u_1} {x : MeasurableSpace α} {f : α → ℝ} 
{μ : MeasureTheory.Measure α},   AEMeasurable f μ → AEMeasurable (fun x => Real.
sinc (f…
-/
protected theorem MeasureTheory.AEStronglyMeasurable.sinc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ sinc (f x)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc
