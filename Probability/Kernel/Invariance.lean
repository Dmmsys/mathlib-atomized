/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Invariance of measures along a kernel

We say that a measure `μ` is invariant with respect to a kernel `κ` if its push-forward along the
kernel `μ.bind κ` is the same measure.

## Main definitions

* `ProbabilityTheory.Kernel.Invariant`: invariance of a given measure with respect to a kernel.

-/

@[expose] public section


open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-! ### Invariant measures of kernels -/

/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
/-
**ProbabilityTheory.Kernel.Invariant** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：Invariant (κ : Kernel α α) (μ : Measure α) : Prop
参数：κ : Kernel α α；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is invariant with respect to the kernel `κ` if the push-forward me
asure of `μ`
along `κ` equals `μ`.
-/
def Invariant (κ : Kernel α α) (μ : Measure α) : Prop :=
  μ.bind κ = μ

variable {κ η : Kernel α α} {μ : Measure α}
/-
**ProbabilityTheory.Kernel.Invariant.def** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel.Invariant`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {κ : ProbabilityTheory.Kernel α 
α} {μ : MeasureTheory.Measure α},   κ.Invariant μ → μ.bind ⇑κ = μ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Invariant.def (hκ : Invariant κ μ) : μ.bind κ = μ :=
  hκ

nonrec theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [comp_const κ μ, hκ.def]
/-
**ProbabilityTheory.Kernel.Invariant.comp** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel.Invariant`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {κ η : ProbabilityTheory.Kernel 
α α} {μ : MeasureTheory.Measure α},   κ.Invariant μ → η.Invariant μ → (κ.comp η)
.Invariant μ
参数：κ.comp η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.Invariant.eq_1`：∀ {α : Type u_1} {mα : Measurab
leSpace α} (κ : ProbabilityTheory.Kernel α α) (μ : MeasureTheory.Measure α),   κ
.Invariant μ = (μ.bind ⇑κ = μ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
-/
theorem Invariant.comp (hκ : Invariant κ μ) (hη : Invariant η μ) :
    Invariant (κ ∘ₖ η) μ := by
  rcases isEmpty_or_nonempty α with _ | hα
  · exact Subsingleton.elim _ _
  · rw [Invariant, ← Measure.comp_assoc, hη, hκ]

/-! ### Reversibility of kernels -/

/-- Reversibility (detailed balance) of a Markov kernel `κ` w.r.t. a measure `π`:
for all measurable sets `A B`, the mass flowing from `A` to `B` equals that from `B` to `A`. -/
/-
**ProbabilityTheory.Kernel.IsReversible** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：IsReversible (κ : Kernel α α) (π : Measure α) : Prop
参数：κ : Kernel α α；π : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reversibility (detailed balance) of a Markov kernel `κ` w.r.t. a measure `π`:
for all measurable sets `A B`, the mass flowing from `A` to `B` equals that from
 `B` to `A`.
-/
def IsReversible (κ : Kernel α α) (π : Measure α) : Prop :=
  ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

/-- A reversible Markov kernel leaves the measure `π` invariant. -/
/-
**ProbabilityTheory.Kernel.IsReversible.invariant** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.IsReversible`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {κ : ProbabilityTheory.Kernel α 
α} [ProbabilityTheory.IsMarkovKernel κ]   {π : MeasureTheory.Measure α}, κ.IsRev
ersible π → κ.Invariant π
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A reversible Markov kernel leaves the measure `π` invariant.
-/
theorem IsReversible.invariant
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  calc
    (κ ∘ₘ π) s = ∫⁻ x, κ x s ∂π := by rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
             _ = ∫⁻ x in s, κ x Set.univ ∂π := by simpa [restrict_univ] using (h_rev hs .univ).symm
             _ = π s := by simp

end Kernel

end ProbabilityTheory

