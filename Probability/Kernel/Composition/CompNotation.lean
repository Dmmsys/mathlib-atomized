/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Notation for the composition of a measure and a kernel

This operation, for which we introduce the notation `∘ₘ`, takes `μ : Measure α` and
`κ : Kernel α β` and creates `κ ∘ₘ μ : Measure β`. The integral of a function against `κ ∘ₘ μ` is
`∫⁻ x, f x ∂(κ ∘ₘ μ) = ∫⁻ a, ∫⁻ b, f b ∂(κ a) ∂μ`.

This file does not define composition but only introduces notation for
`MeasureTheory.Measure.bind μ κ`.

## Notation

* `κ ∘ₘ μ = MeasureTheory.Measure.bind μ κ`, for `κ` a kernel.
-/

public section

/- This file is only for lemmas that are direct specializations of `Measure.bind` to kernels,
anything more involved should go elsewhere (for example the `MeasureComp` file). -/
assert_not_exists ProbabilityTheory.Kernel.compProd

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}

/-- Composition of a measure and a kernel.

Notation for `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] notation:100 κ:101 " ∘ₘ " μ:100 => MeasureTheory.Measure.bind μ κ

@[simp]
/-
**MeasureTheory.Measure.comp_apply_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) Set.univ = μ Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) Set.univ = μ Set.univ := by
  simp [bind_apply .univ κ.aemeasurable]
/-
**MeasureTheory.Measure.deterministic_comp_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：deterministic_comp_eq_map {f : α -> β} (hf : Measurable f) : Kernel.determ
inistic f hf ∘ₘ μ = μ.map f
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.bind_dirac_eq_map`：bind_dirac_eq_map (m : Measure 
α) {f : α -> β} (hf : Measurable f) : m.bind (fun x => Measure.dirac (f x)) = m.
map f
-/
lemma deterministic_comp_eq_map {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

@[simp]
/-
**MeasureTheory.Measure.id_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：id_comp : Kernel.id ∘ₘ μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
lemma id_comp : Kernel.id ∘ₘ μ = μ := by rw [Kernel.id, deterministic_comp_eq_map, Measure.map_id]
/-
**MeasureTheory.Measure.swap_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：swap_comp {μ : Measure (α × β)} : (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
lemma swap_comp {μ : Measure (α × β)} : (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap :=
  deterministic_comp_eq_map measurable_swap

@[simp]
/-
**MeasureTheory.Measure.const_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：const_comp {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.bind_const`：bind_const {m : Measure α} {ν : Measur
e β} : m.bind (fun _ => ν) = m Set.univ • ν
-/
lemma const_comp {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν := μ.bind_const

end MeasureTheory.Measure

