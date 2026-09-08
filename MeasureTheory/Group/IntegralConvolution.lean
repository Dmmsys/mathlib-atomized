/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bochner integrals of convolutions

This file contains results about the Bochner integrals of convolutions of measures.

These results are not placed in the main convolution file because we don't want to import Bochner
integrals over there.

## Main statements

* `integrable_conv_iff`: A function is integrable with respect to the convolution `μ ∗ ν` iff
  the function `y ↦ f (x + y)` is integrable with respect to `ν` for `μ`-almost every `x` and
  the function `x ↦ ∫ y, ‖f (x + y)‖ ∂ν` is integrable with respect to `μ`.
* `integral_conv`: if `f` is integrable with respect to the convolution `μ ∗ ν`, then
  `∫ x, f x ∂(μ ∗ₘ ν) = ∫ x, ∫ y, f (x + y) ∂ν ∂μ`.
-/

public section

namespace MeasureTheory

variable {M F : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  [NormedAddCommGroup F] {μ ν : Measure M} {f : M → F}

@[to_additive]
/-
**MeasureTheory.integrable_mconv_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_mconv_iff [SFinite ν] (hf : AEStronglyMeasurable f (μ ∗ₘ ν)) : 
Integrable f (μ ∗ₘ ν) ↔ (forallᵐ x ∂μ, Integrable (fun y => f (x * y)) ν) ∧ Inte
grable (fun x => ∫ y, ‖f (x * y)‖ ∂ν) μ
参数：hf : AEStronglyMeasurable f (μ ∗ₘ ν)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `MeasureTheory.integrable_prod_iff`：integrable_prod_iff ⦃f : α × β -> E⦄ 
(h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ x
 ∂μ, Integrable (fun y …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_mconv_iff [SFinite ν] (hf : AEStronglyMeasurable f (μ ∗ₘ ν)) :
    Integrable f (μ ∗ₘ ν)
      ↔ (∀ᵐ x ∂μ, Integrable (fun y ↦ f (x * y)) ν)
        ∧ Integrable (fun x ↦ ∫ y, ‖f (x * y)‖ ∂ν) μ := by
  simp [Measure.mconv, integrable_map_measure hf (by fun_prop),
    integrable_prod_iff (hf.comp_measurable (by fun_prop))]

@[to_additive]
/-
**MeasureTheory.integral_mconv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mconv [NormedSpace Real F] [SFinite μ] [SFinite ν] (hf : Integrab
le f (μ ∗ₘ ν)) : ∫ x, f x ∂(μ ∗ₘ ν) = ∫ x, ∫ y, f (x * y) ∂ν ∂μ
参数：hf : Integrable f (μ ∗ₘ ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
-/
lemma integral_mconv [NormedSpace ℝ F] [SFinite μ] [SFinite ν] (hf : Integrable f (μ ∗ₘ ν)) :
    ∫ x, f x ∂(μ ∗ₘ ν) = ∫ x, ∫ y, f (x * y) ∂ν ∂μ := by
  unfold Measure.mconv
  rw [integral_map (by fun_prop) hf.1, integral_prod]
  exact (integrable_map_measure hf.1 (by fun_prop)).mp hf

end MeasureTheory

