/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Basic

/-!
# Bochner integrals of kernels

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : β → E} {a : α}

namespace Kernel

/-
**ProbabilityTheory.Kernel.IsFiniteKernel.integrable** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ : MeasureTheory.Measure α)   [MeasureTheory.IsFiniteMeasure μ] (κ : P
robabilityTheory.Kernel α β) [ProbabilityTheory.IsFiniteKernel κ] {s : Set β},  
 MeasurableSet s → MeasureTheory.Integrable (fun x => (κ x).real s) μ
参数：μ : MeasureTheory.Measure α；κ : ProbabilityTheory.Kernel α β；fun x => (κ x).r
eal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ProbabilityTheory.Kernel.bound_ne_top`：bound_ne_top (κ : Kernel α β) [Is
FiniteKernel κ] : κ.bound != ∞
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
-/
lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x ↦ (κ x).real s) μ := by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _ _)
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.integrable** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ : MeasureTheory.Measure α)   [MeasureTheory.IsFiniteMeasure μ] (κ : P
robabilityTheory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ] {s : Set β},  
 MeasurableSet s → MeasureTheory.Integrable (fun x => (κ x).real s) μ
参数：μ : MeasureTheory.Measure α；κ : ProbabilityTheory.Kernel α β；fun x => (κ x).r
eal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory
.Measure α)   [MeasureTheory.IsFiniteMea…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ :=
  IsFiniteKernel.integrable μ κ hs
/-
**ProbabilityTheory.Kernel.integral_congr_ae** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integral_congr_ae₂ {f g : α → β → E} {μ : Measure α} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb
/-
**ProbabilityTheory.Kernel.integral_indicator** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integral_indicator₂ (f : α → β → E) (s : Set α) (a : α) :
    ∫ y, s.indicator (f · y) a ∂κ a = s.indicator (fun x ↦ ∫ y, f x y ∂κ x) a := by
  by_cases ha : a ∈ s <;> simp [ha]

section Deterministic

variable [CompleteSpace E] {g : α → β}

/-
**ProbabilityTheory.Kernel.integral_deterministic'** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：integral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f) : 
∫ x, f x ∂deterministic g hg a = f (g a)
参数：hg : Measurable g；hf : StronglyMeasurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.integral_dirac'`：integral_dirac' [MeasurableSpace α] (f : 
α -> E) (a : α) (hfm : StronglyMeasurable f) : ∫ x, f x ∂Measure.dirac a = f a
-/
theorem integral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac' _ _ hf]

@[simp]
/-
**ProbabilityTheory.Kernel.integral_deterministic** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：integral_deterministic [MeasurableSingletonClass β] (hg : Measurable g) : 
∫ x, f x ∂deterministic g hg a = f (g a)
参数：hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
-/
theorem integral_deterministic [MeasurableSingletonClass β] (hg : Measurable g) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac _ (g a)]
/-
**ProbabilityTheory.Kernel.setIntegral_deterministic'** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：setIntegral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f)
 {s : Set β} (hs : MeasurableSet s) [Decidable (g a in s)] : ∫ x in s, f x ∂dete
rministic g hg a = if g a in s then f (g a) else 0
参数：hg : Measurable g；hf : StronglyMeasurable f；hs : MeasurableSet s；g a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.setIntegral_dirac'`：setIntegral_dirac' {mα : MeasurableSpa
ce α} {f : α -> E} (hf : StronglyMeasurable f) (a : α) {s : Set α} (hs : Measura
bleSet s) [Decidable (…
-/
theorem setIntegral_deterministic' (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac' hf _ hs]

@[simp]
/-
**ProbabilityTheory.Kernel.setIntegral_deterministic** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：setIntegral_deterministic [MeasurableSingletonClass β] (hg : Measurable g)
 (s : Set β) [Decidable (g a in s)] : ∫ x in s, f x ∂deterministic g hg a = if g
 a in s then f (g a) else 0
参数：hg : Measurable g；s : Set β；g a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `MeasureTheory.setIntegral_dirac`：setIntegral_dirac [MeasurableSpace α] [
MeasurableSingletonClass α] (f : α -> E) (a : α) (s : Set α) [Decidable (a in s)
] : ∫ x in s, f x ∂Me…
-/
theorem setIntegral_deterministic [MeasurableSingletonClass β] (hg : Measurable g)
    (s : Set β) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac f _ s]

end Deterministic

section Const

@[simp]
/-
**ProbabilityTheory.Kernel.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：integral_const {μ : Measure β} : ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
theorem integral_const {μ : Measure β} : ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ := by
  rw [const_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.setIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：setIntegral_const {μ : Measure β} {s : Set β} : ∫ x in s, f x ∂const α μ a
 = ∫ x in s, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
theorem setIntegral_const {μ : Measure β} {s : Set β} :
    ∫ x in s, f x ∂const α μ a = ∫ x in s, f x ∂μ := by rw [const_apply]

end Const

section Restrict

variable {s : Set β}

@[simp]
/-
**ProbabilityTheory.Kernel.integral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：integral_restrict (hs : MeasurableSet s) : ∫ x, f x ∂κ.restrict hs a = ∫ x
 in s, f x ∂κ a
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
-/
theorem integral_restrict (hs : MeasurableSet s) :
    ∫ x, f x ∂κ.restrict hs a = ∫ x in s, f x ∂κ a := by
  rw [restrict_apply]

@[simp]
/-
**ProbabilityTheory.Kernel.setIntegral_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：setIntegral_restrict (hs : MeasurableSet s) (t : Set β) : ∫ x in t, f x ∂κ
.restrict hs a = ∫ x in t inter s, f x ∂κ a
参数：hs : MeasurableSet s；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `MeasureTheory.Measure.restrict_restrict'`：restrict_restrict' (ht : Measu
rableSet t) : (μ.restrict t).restrict s = μ.restrict (s inter t)
-/
theorem setIntegral_restrict (hs : MeasurableSet s) (t : Set β) :
    ∫ x in t, f x ∂κ.restrict hs a = ∫ x in t ∩ s, f x ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]

end Restrict

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

/-
**ProbabilityTheory.Kernel.integral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：integral_piecewise (a : α) (g : β -> E) : ∫ b, g b ∂piecewise hs κ η a = i
f a in s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a
参数：a : α；g : β -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem integral_piecewise (a : α) (g : β → E) :
    ∫ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
/-
**ProbabilityTheory.Kernel.setIntegral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：setIntegral_piecewise (a : α) (g : β -> E) (t : Set β) : ∫ b in t, g b ∂pi
ecewise hs κ η a = if a in s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a
参数：a : α；g : β -> E；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem setIntegral_piecewise (a : α) (g : β → E) (t : Set β) :
    ∫ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

end Kernel
end ProbabilityTheory

