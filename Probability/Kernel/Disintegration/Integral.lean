/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Lebesgue and Bochner integrals of conditional kernels

Integrals of `ProbabilityTheory.Kernel.condKernel` and `MeasureTheory.Measure.condKernel`.

## Main statements

* `ProbabilityTheory.setIntegral_condKernel`: the integral
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)` is equal to
  `∫ x in s ×ˢ t, f x ∂(κ a)`.
* `MeasureTheory.Measure.setIntegral_condKernel`:
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ`

Corresponding statements for the Lebesgue integral and/or without the sets `s` and `t` are also
provided.
-/

public section

open MeasureTheory ProbabilityTheory MeasurableSpace

open scoped ENNReal

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
  {f : β × Ω → ℝ≥0∞}

/-
**ProbabilityTheory.lintegral_condKernel_mem** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) 
: ∫⁻ x, Kernel.condKernel κ (a, x) (Prod.mk x ⁻¹' s) ∂(Kernel.fst κ a) = κ a s
参数：a : α；β × Ω；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, Kernel.condKernel κ (a, x) (Prod.mk x ⁻¹' s) ∂(Kernel.fst κ a) = κ a s := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  simp_rw [Kernel.compProd_apply hs]
/-
**ProbabilityTheory.setLIntegral_condKernel_eq_measure_prod** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：setLIntegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : Measurab
leSet s) {t : Set Ω} (ht : MeasurableSet t) : ∫⁻ b in s, Kernel.condKernel κ (a,
 b) t ∂(Kernel.fst κ a) = κ a (s ×ˢ t)
参数：a : α；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.compProd_apply_prod`：compProd_apply_prod {κ : K
ernel α β} {η : Kernel (α × β) γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α
} {s : Set β} {t : Set γ} (hs : Me…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma setLIntegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, Kernel.condKernel κ (a, b) t ∂(Kernel.fst κ a) = κ a (s ×ˢ t) := by
  have : κ a (s ×ˢ t) = (Kernel.fst κ ⊗ₖ Kernel.condKernel κ) a (s ×ˢ t) := by
    congr; exact (κ.disintegrate _).symm
  simpa [this] using (Kernel.compProd_apply_prod hs ht).symm
/-
**ProbabilityTheory.lintegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：lintegral_condKernel (hf : Measurable f) (a : α) : ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(
Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫⁻ x, f x ∂(κ a)
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma lintegral_condKernel (hf : Measurable f) (a : α) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫⁻ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.lintegral_compProd _ _ _ hf]
/-
**ProbabilityTheory.setLIntegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：setLIntegral_condKernel (hf : Measurable f) (a : α) {s : Set β} (hs : Meas
urableSet s) {t : Set Ω} (ht : MeasurableSet t) : ∫⁻ b in s, ∫⁻ ω in t, f (b, ω)
 ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫⁻ x in s ×ˢ t, f x ∂(κ a)
参数：hf : Measurable f；a : α；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `ProbabilityTheory.Kernel.setLIntegral_compProd`：setLIntegral_compProd (κ
 : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a
 : α) {f : β × γ -> Real>=0∞} (hf : …
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma setLIntegral_condKernel (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]
/-
**ProbabilityTheory.setLIntegral_condKernel_univ_right** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：setLIntegral_condKernel_univ_right (hf : Measurable f) (a : α) {s : Set β}
 (hs : MeasurableSet s) : ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)
) ∂(Kernel.fst κ a) = ∫⁻ x in s ×ˢ Set.univ, f x ∂(κ a)
参数：hf : Measurable f；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setLIntegral_condKernel`：setLIntegral_condKernel (hf :
 Measurable f) (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : Meas
urableSet t) : ∫⁻ b in s, ∫⁻ ω …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_condKernel_univ_right (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel hf a hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]
/-
**ProbabilityTheory.setLIntegral_condKernel_univ_left** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：setLIntegral_condKernel_univ_left (hf : Measurable f) (a : α) {t : Set Ω} 
(ht : MeasurableSet t) : ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b))
 ∂(Kernel.fst κ a) = ∫⁻ x in Set.univ ×ˢ t, f x ∂(κ a)
参数：hf : Measurable f；a : α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setLIntegral_condKernel`：setLIntegral_condKernel (hf :
 Measurable f) (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : Meas
urableSet t) : ∫⁻ b in s, ∫⁻ ω …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_condKernel_univ_left (hf : Measurable f) (a : α) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel hf a MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_co
ndKernel** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel (a : α)
    (hf : AEStronglyMeasurable f (κ a)) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂(Kernel.condKernel κ (a, x)))
      (Kernel.fst κ a) := by
  rw [← κ.disintegrate κ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf
/-
**ProbabilityTheory.integral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：integral_condKernel (a : α) (hf : Integrable f (κ a)) : ∫ b, ∫ ω, f (b, ω)
 ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x, f x ∂(κ a)
参数：a : α；hf : Integrable f (κ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `ProbabilityTheory.integral_compProd`：integral_compProd : forall {f : β ×
 γ -> E} (_ : Integrable f ((κ otimesₖ η) a)), ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, 
∫ y, f (x, y) ∂η (a, x) ∂…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma integral_condKernel (a : α) (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [integral_compProd hf]
/-
**ProbabilityTheory.setIntegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：setIntegral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set
 Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) : ∫ b in s, ∫ ω 
in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x in s ×ˢ t, 
f x ∂(κ a)
参数：a : α；hs : MeasurableSet s；ht : MeasurableSet t；hf : IntegrableOn f (s ×ˢ t) 
(κ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.disintegrate`：disintegrate [κ.IsCondKernel κCon
d] : κ.fst otimesₖ κCond = κ
· 使用定理 `ProbabilityTheory.Kernel.condKernel.instIsCondKernel`：∀ {α : Type u_1} {
β : Type u_2} {Ω : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mΩ : MeasurableSpace Ω} [inst : Standard…
· 使用定理 `ProbabilityTheory.setIntegral_compProd`：setIntegral_compProd {f : β × γ 
-> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hf 
: IntegrableOn f (s ×ˢ t) ((…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.fst`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma setIntegral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]
/-
**ProbabilityTheory.setIntegral_condKernel_univ_right** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：setIntegral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet 
s) (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) : ∫ b in s, ∫ ω, f (b, ω) ∂(Kerne
l.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x in s ×ˢ Set.univ, f x ∂(κ a)
参数：a : α；hs : MeasurableSet s；hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setIntegral_condKernel`：setIntegral_condKernel (a : α)
 {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) (hf : Int
egrableOn f (s ×ˢ t) (κ a)) : …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setIntegral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
/-
**ProbabilityTheory.setIntegral_condKernel_univ_left** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：setIntegral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t
) (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) : ∫ b, ∫ ω in t, f (b, ω) ∂(Kernel
.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x in Set.univ ×ˢ t, f x ∂(κ a)
参数：a : α；ht : MeasurableSet t；hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setIntegral_condKernel`：setIntegral_condKernel (a : α)
 {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) (hf : Int
egrableOn f (s ×ˢ t) (κ a)) : …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setIntegral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {β Ω : Type*} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {f : β × Ω → ℝ≥0∞}

/-
**MeasureTheory.Measure.lintegral_condKernel_mem** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：lintegral_condKernel_mem {s : Set (β × Ω)} (hs : MeasurableSet s) : ∫⁻ x, 
ρ.condKernel x {y | (x, y) in s} ∂ρ.fst = ρ s
参数：β × Ω；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma lintegral_condKernel_mem {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, ρ.condKernel x {y | (x, y) ∈ s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  simp_rw [compProd_apply hs]
  rfl
/-
**MeasureTheory.Measure.setLIntegral_condKernel_eq_measure_prod** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：setLIntegral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s)
 {t : Set Ω} (ht : MeasurableSet t) : ∫⁻ b in s, ρ.condKernel b t ∂ρ.fst = ρ (s 
×ˢ t)
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma setLIntegral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b in s, ρ.condKernel b t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) = (ρ.fst ⊗ₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact (ρ.disintegrate _).symm
  simpa [this] using (compProd_apply_prod hs ht).symm
/-
**MeasureTheory.Measure.lintegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：lintegral_condKernel (hf : Measurable f) : ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(ρ.condKe
rnel b) ∂ρ.fst = ∫⁻ x, f x ∂ρ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma lintegral_condKernel (hf : Measurable f) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [lintegral_compProd hf]
/-
**MeasureTheory.Measure.setLIntegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：setLIntegral_condKernel (hf : Measurable f) {s : Set β} (hs : MeasurableSe
t s) {t : Set Ω} (ht : MeasurableSet t) : ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(ρ.con
dKernel b) ∂ρ.fst = ∫⁻ x in s ×ˢ t, f x ∂ρ
参数：hf : Measurable f；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.setLIntegral_compProd`：setLIntegral_compProd [SFin
ite μ] [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) {s : Set 
α} (hs : MeasurableSet s) {t : Se…
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma setLIntegral_condKernel (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [setLIntegral_compProd hf hs ht]
/-
**MeasureTheory.Measure.setLIntegral_condKernel_univ_right** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：setLIntegral_condKernel_univ_right (hf : Measurable f) {s : Set β} (hs : M
easurableSet s) : ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫⁻ x in s
 ×ˢ Set.univ, f x ∂ρ
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_condKernel`：setLIntegral_condKernel (
hf : Measurable f) {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : Measurab
leSet t) : ∫⁻ b in s, ∫⁻ ω in t, f …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_condKernel_univ_right (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setLIntegral_condKernel hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]
/-
**MeasureTheory.Measure.setLIntegral_condKernel_univ_left** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：setLIntegral_condKernel_univ_left (hf : Measurable f) {t : Set Ω} (ht : Me
asurableSet t) : ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫⁻ x in Se
t.univ ×ˢ t, f x ∂ρ
参数：hf : Measurable f；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_condKernel`：setLIntegral_condKernel (
hf : Measurable f) {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : Measurab
leSet t) : ∫⁻ b in s, ∫⁻ ω in t, f …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_condKernel_univ_left (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setLIntegral_condKernel hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**MeasureTheory.Measure._root_.MeasureTheory.AEStronglyMeasurable.integral_condK
ernel** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel
    (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst := by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf
/-
**MeasureTheory.Measure.integral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：integral_condKernel (hf : Integrable f ρ) : ∫ b, ∫ ω, f (b, ω) ∂(ρ.condKer
nel b) ∂ρ.fst = ∫ x, f x ∂ρ
参数：hf : Integrable f ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.integral_compProd`：integral_compProd [SFinite μ] [
IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : 
α × β -> E} (hf : Integrable …
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma integral_condKernel (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [integral_compProd hf]
/-
**MeasureTheory.Measure.setIntegral_condKernel** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：setIntegral_condKernel {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (ht 
: MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) : ∫ b in s, ∫ ω in t, f (b, 
ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ
参数：hs : MeasurableSet s；ht : MeasurableSet t；hf : IntegrableOn f (s ×ˢ t) ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.setIntegral_compProd`：setIntegral_compProd [SFinit
e μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
 {s : Set α} (hs : MeasurableSet…
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma setIntegral_condKernel {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]
/-
**MeasureTheory.Measure.setIntegral_condKernel_univ_right** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：setIntegral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s) (hf :
 IntegrableOn f (s ×ˢ Set.univ) ρ) : ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂
ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ
参数：hs : MeasurableSet s；hf : IntegrableOn f (s ×ˢ Set.univ) ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setIntegral_condKernel`：setIntegral_condKernel {s 
: Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) (hf : Integra
bleOn f (s ×ˢ t) ρ) : ∫ b in s, ∫ …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setIntegral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) ρ) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setIntegral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
/-
**MeasureTheory.Measure.setIntegral_condKernel_univ_left** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：setIntegral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t) (hf : 
IntegrableOn f (Set.univ ×ˢ t) ρ) : ∫ b, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ
.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ
参数：ht : MeasurableSet t；hf : IntegrableOn f (Set.univ ×ˢ t) ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setIntegral_condKernel`：setIntegral_condKernel {s 
: Set β} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) (hf : Integra
bleOn f (s ×ˢ t) ρ) : ∫ b in s, ∫ …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setIntegral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) ρ) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setIntegral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end MeasureTheory.Measure

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/

open ProbabilityTheory

variable {α Ω E F : Type*} {mα : MeasurableSpace α} [MeasurableSpace Ω]
  [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-
**MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [i
nst : MeasurableSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2 : Nonempty Ω]
 [inst_3 : NormedAddCommGroup F]   {ρ : MeasureTheory.Measure (α × Ω)} [inst_4 :
 MeasureTheory.IsFiniteMeasure ρ] {f : α × Ω → F},   MeasureTheory.AEStronglyMea
surable f ρ →     ((∀ᵐ (a : α) ∂ρ.fst, MeasureTheory.Integrable (fun ω => f (a, 
ω)) (ρ.condKernel a)) ∧         MeasureTheory.Integrable (fun a => ∫ (ω : Ω), ‖f
 (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔       MeasureTheory.Integrable f ρ)
参数：α × Ω；(∀ᵐ (a : α) ∂ρ.fst, MeasureTheory.Integrable (fun ω => f (a, ω)) (ρ.con
dKernel a)) ∧         MeasureTheory.Integrable (fun a => ∫ (ω : Ω), ‖f (a, ω)‖ ∂
ρ.condKernel a) ρ.fst ↔       MeasureTheory.Integrable f ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用引理 `MeasureTheory.Measure.integrable_compProd_iff`：integrable_compProd_iff [
SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E] {f : α × β -> 
E} (hf : AEStronglyMeasurable f (μ …
· 使用定理 `MeasureTheory.Measure.instSFiniteFstOfProd`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureTheory
.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instIsMarkovKernelCondKernel`：∀ {α : Type u_1} {Ω 
: Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBo
relSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω → F}
    (hf : AEStronglyMeasurable f ρ) :
    (∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a)) ∧
      Integrable (fun a ↦ ∫ ω, ‖f (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔ Integrable f ρ := by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.integrable_compProd_iff hf]
/-
**MeasureTheory.Integrable.condKernel_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [i
nst : MeasurableSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2 : Nonempty Ω]
 [inst_3 : NormedAddCommGroup F]   {ρ : MeasureTheory.Measure (α × Ω)} [inst_4 :
 MeasureTheory.IsFiniteMeasure ρ] {f : α × Ω → F},   MeasureTheory.Integrable f 
ρ → ∀ᵐ (a : α) ∂ρ.fst, MeasureTheory.Integrable (fun ω => f (a, ω)) (ρ.condKerne
l a)
参数：α × Ω；a : α；fun ω => f (a, ω)；ρ.condKernel a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff`：∀ {α : 
Type u_1} {Ω : Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [inst : Measura
bleSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2…
-/
theorem Integrable.condKernel_ae {f : α × Ω → F} (hf_int : Integrable f ρ) :
    ∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1
/-
**MeasureTheory.Integrable.integral_norm_condKernel** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [i
nst : MeasurableSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2 : Nonempty Ω]
 [inst_3 : NormedAddCommGroup F]   {ρ : MeasureTheory.Measure (α × Ω)} [inst_4 :
 MeasureTheory.IsFiniteMeasure ρ] {f : α × Ω → F},   MeasureTheory.Integrable f 
ρ → MeasureTheory.Integrable (fun x => ∫ (y : Ω), ‖f (x, y)‖ ∂ρ.condKernel x) ρ.
fst
参数：α × Ω；fun x => ∫ (y : Ω), ‖f (x, y)‖ ∂ρ.condKernel x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff`：∀ {α : 
Type u_1} {Ω : Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [inst : Measura
bleSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2…
-/
theorem Integrable.integral_norm_condKernel {f : α × Ω → F} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ρ.condKernel x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2
/-
**MeasureTheory.Integrable.norm_integral_condKernel** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {E : Type u_3} {mα : MeasurableSpace α} [i
nst : MeasurableSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2 : Nonempty Ω]
 [inst_3 : NormedAddCommGroup E] [inst_4 : NormedSpace ℝ E]   {ρ : MeasureTheory
.Measure (α × Ω)} [inst_5 : MeasureTheory.IsFiniteMeasure ρ] {f : α × Ω → E},   
MeasureTheory.Integrable f ρ → MeasureTheory.Integrable (fun x => ‖∫ (y : Ω), f 
(x, y) ∂ρ.condKernel x‖) ρ.fst
参数：α × Ω；fun x => ‖∫ (y : Ω), f (x, y) ∂ρ.condKernel x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.integral_norm_condKernel`：∀ {α : Type u_1} {Ω :
 Type u_2} {F : Type u_4} {mα : MeasurableSpace α} [inst : MeasurableSpace Ω]   
[inst_1 : StandardBorelSpace Ω] [inst_2…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_condKernel`：∀ {β : Type u_1}
 {Ω : Type u_2} {mβ : MeasurableSpace β} [inst : MeasurableSpace Ω] [inst_1 : St
andardBorelSpace Ω]   [inst_2 : Nonempty Ω] …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem Integrable.norm_integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ‖∫ y, f (x, y) ∂ρ.condKernel x‖) ρ.fst := by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y ↦ norm_nonneg _)
/-
**MeasureTheory.Integrable.integral_condKernel** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {Ω : Type u_2} {E : Type u_3} {mα : MeasurableSpace α} [i
nst : MeasurableSpace Ω]   [inst_1 : StandardBorelSpace Ω] [inst_2 : Nonempty Ω]
 [inst_3 : NormedAddCommGroup E] [inst_4 : NormedSpace ℝ E]   {ρ : MeasureTheory
.Measure (α × Ω)} [inst_5 : MeasureTheory.IsFiniteMeasure ρ] {f : α × Ω → E},   
MeasureTheory.Integrable f ρ → MeasureTheory.Integrable (fun x => ∫ (y : Ω), f (
x, y) ∂ρ.condKernel x) ρ.fst
参数：α × Ω；fun x => ∫ (y : Ω), f (x, y) ∂ρ.condKernel x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_condKernel`：∀ {β : Type u_1}
 {Ω : Type u_2} {mβ : MeasurableSpace β} [inst : MeasurableSpace Ω] [inst_1 : St
andardBorelSpace Ω]   [inst_2 : Nonempty Ω] …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Integrable.norm_integral_condKernel`：∀ {α : Type u_1} {Ω :
 Type u_2} {E : Type u_3} {mα : MeasurableSpace α} [inst : MeasurableSpace Ω]   
[inst_1 : StandardBorelSpace Ω] [inst_2…
-/
theorem Integrable.integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst :=
  (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel

end MeasureTheory

