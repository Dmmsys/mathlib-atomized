/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Kernel.Integral

/-! # Integral against a kernel over a set

This file contains lemmas about the integral against a kernel and over a set.

-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X Y E : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Kernel X Y)

/-
**ProbabilityTheory.Kernel.integral_integral_indicator** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：integral_integral_indicator (μ : Measure X) (f : X -> Y -> E) {s : Set X} 
(hs : MeasurableSet s) : ∫ x, ∫ y, s.indicator (f · y) x ∂κ x ∂μ = ∫ x in s, ∫ y
, f x y ∂κ x ∂μ
参数：μ : Measure X；f : X -> Y -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.integral_indicator₂`：integral_indicator₂ (f : α
 -> β -> E) (s : Set α) (a : α) : ∫ y, s.indicator (f · y) a ∂κ a = s.indicator 
(fun x => ∫ y, f x y ∂κ x) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_integral_indicator (μ : Measure X) (f : X → Y → E) {s : Set X}
    (hs : MeasurableSet s) :
    ∫ x, ∫ y, s.indicator (f · y) x ∂κ x ∂μ = ∫ x in s, ∫ y, f x y ∂κ x ∂μ := by
  simp_rw [← integral_indicator hs, Kernel.integral_indicator₂]

end ProbabilityTheory.Kernel

