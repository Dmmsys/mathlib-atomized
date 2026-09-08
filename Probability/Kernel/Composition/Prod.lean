/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Product and composition of kernels

We define the product `κ ×ₖ η` of s-finite kernels `κ : Kernel α β` and `η : Kernel α γ`, which is
a kernel from `α` to `β × γ`.

## Main definitions

* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_prod`: Lebesgue integral of a function against a product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by product.

## Notation

* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Product of two kernels. This is meaningful only when the kernels are s-finite. -/
/-
**ProbabilityTheory.Kernel.prod** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory.Ker
nel`。
形式化陈述：prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)
参数：κ : Kernel α β；η : Kernel α γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two kernels. This is meaningful only when the kernels are s-finite.
-/
noncomputable def prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ) :=
  (κ ∥ₖ η) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod
/-
**ProbabilityTheory.Kernel.parallelComp_comp_copy** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：parallelComp_comp_copy (κ : Kernel α β) (η : Kernel α γ) : (κ ∥ₖ η) ∘ₖ cop
y α = κ ×ₖ η
参数：κ : Kernel α β；η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma parallelComp_comp_copy (κ : Kernel α β) (η : Kernel α γ) :
    (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η := rfl

@[simp]
/-
**ProbabilityTheory.Kernel.zero_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：zero_prod (η : Kernel α γ) : (0 : Kernel α β) ×ₖ η = 0
参数：η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_zero_left`：parallelComp_zero_left 
(η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_prod (η : Kernel α γ) : (0 : Kernel α β) ×ₖ η = 0 := by simp [prod]

@[simp]
/-
**ProbabilityTheory.Kernel.prod_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：prod_zero (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_zero_right`：parallelComp_zero_righ
t (κ : Kernel α β) : κ ∥ₖ (0 : Kernel γ δ) = 0
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_zero (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0 := by simp [prod]

@[simp]
/-
**ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_left** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：prod_of_not_isSFiniteKernel_left {κ : Kernel α β} (η : Kernel α γ) (h : ¬ 
IsSFiniteKernel κ) : κ ×ₖ η = 0
参数：η : Kernel α γ；h : ¬ IsSFiniteKernel κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_of_not_isSFiniteKernel_left {κ : Kernel α β} (η : Kernel α γ) (h : ¬ IsSFiniteKernel κ) :
    κ ×ₖ η = 0 := by
  simp [prod, h]

@[simp]
/-
**ProbabilityTheory.Kernel.prod_of_not_isSFiniteKernel_right** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：prod_of_not_isSFiniteKernel_right (κ : Kernel α β) {η : Kernel α γ} (h : ¬
 IsSFiniteKernel η) : κ ×ₖ η = 0
参数：κ : Kernel α β；h : ¬ IsSFiniteKernel η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_of_not_isSFiniteKernel_right (κ : Kernel α β) {η : Kernel α γ}
    (h : ¬ IsSFiniteKernel η) :
    κ ×ₖ η = 0 := by
  simp [prod, h]
/-
**ProbabilityTheory.Kernel.prod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFini
teKernel η] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) : (κ ×ₖ η) a s = ∫⁻
 b : β, (η a) (Prod.mk b ⁻¹' s) ∂κ a
参数：κ : Kernel α β；η : Kernel α γ；a : α；β × γ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.Measure.dirac_bind`：dirac_bind {f : α -> Measure β} (hf : 
Measurable f) (a : α) : bind (dirac a) f = f a
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) (Prod.mk b ⁻¹' s) ∂κ a := by
  simp_rw [prod, comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _) (a, a),
    parallelComp_apply, Measure.prod_apply hs]
/-
**ProbabilityTheory.Kernel.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：prod_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFinit
eKernel η] (a : α) : (κ ×ₖ η) a = (κ a).prod (η a)
参数：κ : Kernel α β；η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod_apply'`：prod_apply' (κ : Kernel α β) [IsSF
initeKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {s : Set (β × γ)} (h
s : MeasurableSet s) : (κ …
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma prod_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply' _ _ _ hs, Measure.prod_apply hs]
/-
**ProbabilityTheory.Kernel.prod_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：prod_apply_prod {κ : Kernel α β} {η : Kernel α γ} [IsSFiniteKernel κ] [IsS
FiniteKernel η] {s : Set β} {t : Set γ} {a : α} : (κ ×ₖ η) a (s ×ˢ t) = (κ a s) 
* (η a t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  rw [prod_apply, Measure.prod_prod]
/-
**ProbabilityTheory.Kernel.prod_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：prod_const (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν] : const
 α μ ×ₖ const α ν = const α (μ.prod ν)
参数：μ : Measure β；ν : Measure γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
-/
lemma prod_const (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν] :
    const α μ ×ₖ const α ν = const α (μ.prod ν) := by
  ext x
  rw [const_apply, prod_apply, const_apply, const_apply]
/-
**ProbabilityTheory.Kernel.lintegral_prod** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：lintegral_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSF
initeKernel η] (a : α) {g : β × γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂
(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a
参数：κ : Kernel α β；η : Kernel α γ；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  simp_rw [prod, lintegral_comp _ _ _ hg, copy_apply]
  rw [lintegral_dirac' _ (by fun_prop)]
  simp_rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]
/-
**ProbabilityTheory.Kernel.lintegral_prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：lintegral_prod_symm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) 
[IsSFiniteKernel η] (a : α) {g : β × γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, 
g c ∂(κ ×ₖ η) a = ∫⁻ c, ∫⁻ b, g (b, c) ∂κ a ∂η a
参数：κ : Kernel α β；η : Kernel α γ；a : α；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem lintegral_prod_symm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] (a : α) {g : β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ c, ∫⁻ b, g (b, c) ∂κ a ∂η a := by
  rw [prod_apply, MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]
/-
**ProbabilityTheory.Kernel.lintegral_deterministic_prod** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：lintegral_deterministic_prod {f : α -> β} (hf : Measurable f) (κ : Kernel 
α γ) [IsSFiniteKernel κ] (a : α) {g : (β × γ) -> Real>=0∞} (hg : Measurable g) :
 ∫⁻ p, g p ∂((deterministic f hf) ×ₖ κ) a = ∫⁻ c, g (f a, c) ∂κ a
参数：hf : Measurable f；κ : Kernel α γ；a : α；β × γ；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod`：lintegral_prod (κ : Kernel α β)
 [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {g : β × γ -> 
Real>=0∞} (hg : Measurable g)…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic'`：lintegral_determinist
ic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g) (hf : Measurabl
e f) : ∫⁻ x, f x ∂deterministic g hg a …
· 使用定理 `Measurable.lintegral_prod_right'`：Measurable.lintegral_prod_right' [SFin
ite ν] : forall {f : α × β -> Real>=0∞}, Measurable f -> Measurable fun x => ∫⁻ 
y, f (x, y) ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
theorem lintegral_deterministic_prod {f : α → β} (hf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂((deterministic f hf) ×ₖ κ) a = ∫⁻ c, g (f a, c) ∂κ a := by
  rw [lintegral_prod _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_right']
/-
**ProbabilityTheory.Kernel.lintegral_prod_deterministic** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：lintegral_prod_deterministic {f : α -> γ} (hf : Measurable f) (κ : Kernel 
α β) [IsSFiniteKernel κ] (a : α) {g : (β × γ) -> Real>=0∞} (hg : Measurable g) :
 ∫⁻ p, g p ∂(κ ×ₖ (deterministic f hf)) a = ∫⁻ b, g (b, f a) ∂κ a
参数：hf : Measurable f；κ : Kernel α β；a : α；β × γ；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod_symm`：lintegral_prod_symm (κ : K
ernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {g :
 β × γ -> Real>=0∞} (hg : Measurab…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic'`：lintegral_determinist
ic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g) (hf : Measurabl
e f) : ∫⁻ x, f x ∂deterministic g hg a …
· 使用定理 `Measurable.lintegral_prod_left'`：Measurable.lintegral_prod_left' [SFinit
e μ] {f : α × β -> Real>=0∞} (hf : Measurable f) : Measurable fun y => ∫⁻ x, f (
x, y) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
theorem lintegral_prod_deterministic {f : α → γ} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂(κ ×ₖ (deterministic f hf)) a = ∫⁻ b, g (b, f a) ∂κ a := by
  rw [lintegral_prod_symm _ _ _ hg, lintegral_deterministic' _ hg.lintegral_prod_left']
/-
**ProbabilityTheory.Kernel.lintegral_id_prod** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：lintegral_id_prod {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kerne
l α β) [IsSFiniteKernel κ] (a : α) : ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a = ∫⁻ b, f (a,
 b) ∂κ a
参数：α × β；hf : Measurable f；κ : Kernel α β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic_prod`：lintegral_determi
nistic_prod {f : α -> β} (hf : Measurable f) (κ : Kernel α γ) [IsSFiniteKernel κ
] (a : α) {g : (β × γ) -> Real>=0∞} (hg : M…
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem lintegral_id_prod {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) :
    ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a = ∫⁻ b, f (a, b) ∂κ a := by
  rw [Kernel.id, lintegral_deterministic_prod _ _ _ hf, id_eq]
/-
**ProbabilityTheory.Kernel.lintegral_prod_id** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：lintegral_prod_id {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kerne
l β α) [IsSFiniteKernel κ] (b : β) : ∫⁻ p, f p ∂(κ ×ₖ Kernel.id) b = ∫⁻ a, f (a,
 b) ∂κ b
参数：α × β；hf : Measurable f；κ : Kernel β α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod_deterministic`：lintegral_prod_de
terministic {f : α -> γ} (hf : Measurable f) (κ : Kernel α β) [IsSFiniteKernel κ
] (a : α) {g : (β × γ) -> Real>=0∞} (hg : M…
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem lintegral_prod_id {f : (α × β) → ℝ≥0∞} (hf : Measurable f) (κ : Kernel β α)
    [IsSFiniteKernel κ] (b : β) :
    ∫⁻ p, f p ∂(κ ×ₖ Kernel.id) b = ∫⁻ a, f (a, b) ∂κ b := by
  rw [Kernel.id, lintegral_prod_deterministic _ _ _ hf, id_eq]
/-
**ProbabilityTheory.Kernel.deterministic_prod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：deterministic_prod_apply' {f : α -> β} (mf : Measurable f) (κ : Kernel α γ
) [IsSFiniteKernel κ] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) : ((Kerne
l.deterministic f mf) ×ₖ κ) a s = κ a (Prod.mk (f a) ⁻¹' s)
参数：mf : Measurable f；κ : Kernel α γ；a : α；β × γ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod_apply'`：prod_apply' (κ : Kernel α β) [IsSF
initeKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {s : Set (β × γ)} (h
s : MeasurableSet s) : (κ …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic'`：lintegral_determinist
ic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g) (hf : Measurabl
e f) : ∫⁻ x, f x ∂deterministic g hg a …
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
theorem deterministic_prod_apply' {f : α → β} (mf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ κ) a s = κ a (Prod.mk (f a) ⁻¹' s) := by
  rw [prod_apply' _ _ _ hs, lintegral_deterministic']
  exact measurable_measure_prodMk_left hs
/-
**ProbabilityTheory.Kernel.id_prod_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：id_prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × 
β)} (hs : MeasurableSet s) : (Kernel.id ×ₖ κ) a s = κ a (Prod.mk a ⁻¹' s)
参数：κ : Kernel α β；a : α；α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `ProbabilityTheory.Kernel.deterministic_prod_apply'`：deterministic_prod_a
pply' {f : α -> β} (mf : Measurable f) (κ : Kernel α γ) [IsSFiniteKernel κ] (a :
 α) {s : Set (β × γ)} (hs : MeasurableSe…
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem id_prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × β)}
    (hs : MeasurableSet s) : (Kernel.id ×ₖ κ) a s = κ a (Prod.mk a ⁻¹' s) := by
  rw [Kernel.id, deterministic_prod_apply' _ _ _ hs, id_eq]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.prod** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsMarkovKernel κ]   (η : ProbabilityTheory.Kernel α γ) [
ProbabilityTheory.IsMarkovKernel η], ProbabilityTheory.IsMarkovKernel (κ.prod η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel α γ；κ.prod η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα 
: MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdParallelComp`：∀ {α : Type
 u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α} {mβ 
: MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
-/
instance IsMarkovKernel.prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod]; infer_instance
  rcases eq_zero_or_isMarkovKernel η with rfl | h'
  · simp only [prod]; infer_instance
  infer_instance
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.prod** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsFiniteKernel κ]   (η : ProbabilityTheory.Kernel α γ) [
ProbabilityTheory.IsFiniteKernel η], ProbabilityTheory.IsFiniteKernel (κ.prod η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel α γ；κ.prod η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα 
: MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelProdParallelComp`：∀ {α : Type
 u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α} {mβ 
: MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_snd`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.snd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
-/
instance IsFiniteKernel.prod (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.prod** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) (η : ProbabilityTheory.Kernel α γ),   ProbabilityTheory.IsSFiniteKernel (κ.
prod η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel α γ；κ.prod η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα 
: MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelProdParallelComp`：∀ {α : Typ
e u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α} {mβ
 : MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_snd`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.snd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
-/
instance IsSFiniteKernel.prod (κ : Kernel α β) (η : Kernel α γ) :
    IsSFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance
/-
**ProbabilityTheory.Kernel.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsSFiniteKernel κ]   (η : ProbabilityTheory.Kernel α γ) 
[ProbabilityTheory.IsMarkovKernel η], (κ.prod η).fst = κ
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel α γ；κ.prod η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα 
: MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.fst_comp`：fst_comp (κ : Kernel α β) (η : Kernel
 β (γ × δ)) : (η ∘ₖ κ).fst = η.fst ∘ₖ κ
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.Measure.dirac_bind`：dirac_bind {f : α -> Measure β} (hf : 
Measurable f) (a : α) : bind (dirac a) f = f a
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用定理 `ProbabilityTheory.Kernel.fst_apply`：fst_apply (κ : Kernel α (β × γ)) (a 
: α) : fst κ a = (κ a).map Prod.fst
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma fst_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  rw [prod, fst_comp]
  ext a : 1
  rw [comp_apply, copy_apply, Measure.dirac_bind (by fun_prop), fst_apply, parallelComp_apply]
  simp
/-
**ProbabilityTheory.Kernel.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {γ : Type u_4}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsMarkovKernel κ]   (η : ProbabilityTheory.Kernel α γ) [
ProbabilityTheory.IsSFiniteKernel η], (κ.prod η).snd = η
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel α γ；κ.prod η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma snd_prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  ext x; simp [snd_apply, prod_apply]
/-
**ProbabilityTheory.Kernel.comap_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：comap_prod (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFinit
eKernel η] {f : α -> β} (hf : Measurable f) : (κ ×ₖ η).comap f hf = (κ.comap f h
f) ×ₖ (η.comap f hf)
参数：κ : Kernel β γ；η : Kernel β δ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
-/
lemma comap_prod (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) :
    (κ ×ₖ η).comap f hf = (κ.comap f hf) ×ₖ (η.comap f hf) := by
  ext1 x
  rw [comap_apply, prod_apply, prod_apply, comap_apply, comap_apply]
/-
**ProbabilityTheory.Kernel.map_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：map_prod_map {ε} {mε : MeasurableSpace ε} (κ : Kernel α β) [IsSFiniteKerne
l κ] (η : Kernel α δ) [IsSFiniteKernel η] {f : β -> γ} (hf : Measurable f) {g : 
δ -> ε} (hg : Measurable g) : (κ.map f) ×ₖ (η.map g) = (κ ×ₖ η).map (Prod.map f 
g)
参数：κ : Kernel α β；η : Kernel α δ；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
-/
lemma map_prod_map {ε} {mε : MeasurableSpace ε} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α δ) [IsSFiniteKernel η] {f : β → γ} (hf : Measurable f) {g : δ → ε}
    (hg : Measurable g) : (κ.map f) ×ₖ (η.map g) = (κ ×ₖ η).map (Prod.map f g) := by
  ext1 x
  rw [map_apply _ (hf.prodMap hg), prod_apply κ, ← Measure.map_prod_map _ _ hf hg, prod_apply,
    map_apply _ hf, map_apply _ hg]
/-
**ProbabilityTheory.Kernel.map_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：map_prod_eq (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFini
teKernel η] {f : β -> δ} (hf : Measurable f) : (κ.map f) ×ₖ η = (κ ×ₖ η).map (Pr
od.map f id)
参数：κ : Kernel α β；η : Kernel α γ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.map_prod_map`：map_prod_map {ε} {mε : Measurable
Space ε} (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α δ) [IsSFiniteKernel 
η] {f : β -> γ} (hf : Measu…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用引理 `ProbabilityTheory.Kernel.map_id`：map_id (κ : Kernel α β) : map κ id = κ
-/
lemma map_prod_eq (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    {f : β → δ} (hf : Measurable f) : (κ.map f) ×ₖ η = (κ ×ₖ η).map (Prod.map f id) := by
  rw [← map_prod_map _ _ hf measurable_id, map_id]
/-
**ProbabilityTheory.Kernel.comap_prod_swap** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsS
FiniteKernel η] : comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable
_swap = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap
参数：κ : Kernel α β；η : Kernel γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.ext_fun_iff`：ext_fun_iff : κ = η ↔ forall a f, 
Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comap`：lintegral_comap (κ : Kernel α 
β) (hg : Measurable g) (c : γ) (g' : β -> Real>=0∞) : ∫⁻ b, g' b ∂comap κ g hg c
 = ∫⁻ b, g' b ∂κ (g c)
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod`：lintegral_prod (κ : Kernel α β)
 [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {g : β × γ -> 
Real>=0∞} (hg : Measurable g)…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_lintegral_swap`：lintegral_lintegral_swap [SFinit
e μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x,
 ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
-/
lemma comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap, lintegral_map _ measurable_swap _ hf, lintegral_prod _ _ _ hf,
    lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop
/-
**ProbabilityTheory.Kernel.map_prod_swap** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFi
niteKernel η] : map (κ ×ₖ η) Prod.swap = η ×ₖ κ
参数：κ : Kernel α β；η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.ext_fun_iff`：ext_fun_iff : κ = η ↔ forall a f, 
Measurable f -> ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Measura
bleSpace γ} {f : β → γ} (κ :…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod`：lintegral_prod (κ : Kernel α β)
 [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {g : β × γ -> 
Real>=0∞} (hg : Measurable g)…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_lintegral_swap`：lintegral_lintegral_swap [SFinit
e μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x,
 ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
-/
lemma map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf, lintegral_prod, lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop
/-
**ProbabilityTheory.Kernel.prodComm_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：prodComm_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFi
niteKernel η] : (κ ×ₖ η).map MeasurableEquiv.prodComm = η ×ₖ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.map_prod_swap`：map_prod_swap (κ : Kernel α β) (
η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] : map (κ ×ₖ η) Prod.swap
 = η ×ₖ κ
-/
lemma prodComm_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (κ ×ₖ η).map MeasurableEquiv.prodComm = η ×ₖ κ :=
  map_prod_swap κ η

@[simp]
/-
**ProbabilityTheory.Kernel.swap_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.Kernel`。
形式化陈述：swap_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFinite
Kernel η] : (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.swap_comp_eq_map`：swap_comp_eq_map {κ : Kernel 
α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swap
· 使用引理 `ProbabilityTheory.Kernel.map_prod_swap`：map_prod_swap (κ : Kernel α β) (
η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] : map (κ ×ₖ η) Prod.swap
 = η ×ₖ κ
-/
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  rw [swap_comp_eq_map, map_prod_swap]
/-
**ProbabilityTheory.Kernel.deterministic_prod_deterministic** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：deterministic_prod_deterministic {f : α -> β} {g : α -> γ} (hf : Measurabl
e f) (hg : Measurable g) : deterministic f hf ×ₖ deterministic g hg = determinis
tic (fun a => (f a, g a)) (hf.prodMk hg)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.dirac_prod_dirac`：dirac_prod_dirac {x : α} {y : β}
 : (dirac x).prod (dirac y) = dirac (x, y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prodMk hg) := by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_prod_dirac]
/-
**ProbabilityTheory.Kernel.id_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：id_prod_eq : @Kernel.id (α × β) inferInstance = (deterministic Prod.fst me
asurable_fst) ×ₖ (deterministic Prod.snd measurable_snd)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.deterministic_prod_deterministic`：deterministic
_prod_deterministic {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurab
le g) : deterministic f hf ×ₖ deterministic g h…
-/
lemma id_prod_eq : @Kernel.id (α × β) inferInstance =
    (deterministic Prod.fst measurable_fst) ×ₖ (deterministic Prod.snd measurable_snd) := by
  rw [deterministic_prod_deterministic]
  rfl
/-
**ProbabilityTheory.Kernel.prodAssoc_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：prodAssoc_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSF
initeKernel η] (ξ : Kernel α δ) [IsSFiniteKernel ξ] : ((κ ×ₖ ξ) ×ₖ η).map Measur
ableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η)
参数：κ : Kernel α β；η : Kernel α γ；ξ : Kernel α δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.map_apply`：map_apply (κ : Kernel α β) (hf : Mea
surable f) (a : α) : map κ f a = (κ a).map f
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…
· 使用定理 `MeasureTheory.Measure.prodAssoc_prod`：prodAssoc_prod [SFinite τ] : map M
easurableEquiv.prodAssoc ((μ.prod ν).prod τ) = μ.prod (ν.prod τ)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma prodAssoc_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    ((κ ×ₖ ξ) ×ₖ η).map MeasurableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η) := by
  ext1 a
  rw [map_apply _ (by fun_prop), prod_apply, prod_apply, Measure.prodAssoc_prod, prod_apply,
    prod_apply]
/-
**ProbabilityTheory.Kernel.prodAssoc_symm_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：prodAssoc_symm_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) 
[IsSFiniteKernel η] (ξ : Kernel α δ) [IsSFiniteKernel ξ] : (κ ×ₖ (ξ ×ₖ η)).map M
easurableEquiv.prodAssoc.symm = (κ ×ₖ ξ) ×ₖ η
参数：κ : Kernel α β；η : Kernel α γ；ξ : Kernel α δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.prodAssoc_prod`：prodAssoc_prod (κ : Kernel α β)
 [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (ξ : Kernel α δ) [IsSF
initeKernel ξ] : ((κ ×ₖ ξ) ×ₖ…
· 使用引理 `ProbabilityTheory.Kernel.map_comp_right`：map_comp_right (κ : Kernel α β)
 {f : β -> γ} (hf : Measurable f) {g : γ -> δ} (hg : Measurable g) : κ.map (g ∘ 
f) = (κ.map f).map g
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用引理 `ProbabilityTheory.Kernel.map_id`：map_id (κ : Kernel α β) : map κ id = κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodAssoc_symm_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    (κ ×ₖ (ξ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm = (κ ×ₖ ξ) ×ₖ η := by
  rw [← prodAssoc_prod, ← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  simp
/-
**ProbabilityTheory.Kernel.prod_const_comp** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：prod_const_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKe
rnel κ] (η : Kernel β γ) [IsSFiniteKernel η] (μ : Measure δ) [SFinite μ] : (η ×ₖ
 (const β μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const α μ)
参数：κ : Kernel α β；η : Kernel β γ；μ : Measure δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.prod_apply'`：prod_apply' (κ : Kernel α β) [IsSF
initeKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {s : Set (β × γ)} (h
s : MeasurableSet s) : (κ …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_const_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] (μ : Measure δ) [SFinite μ] :
    (η ×ₖ (const β μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const α μ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]
/-
**ProbabilityTheory.Kernel.const_prod_comp** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：const_prod_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKe
rnel κ] (μ : Measure γ) [SFinite μ] (η : Kernel β δ) [IsSFiniteKernel η] : ((con
st β μ) ×ₖ η) ∘ₖ κ = (const α μ) ×ₖ (η ∘ₖ κ)
参数：κ : Kernel α β；μ : Measure γ；η : Kernel β δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `MeasureTheory.Measure.prod_apply_symm`：prod_apply_symm {s : Set (α × β)}
 (hs : MeasurableSet s) : μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `measurable_measure_prodMk_right`：measurable_measure_prodMk_right {μ : Me
asure α} [SFinite μ] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun y
 => μ ((fun x => (x, …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma const_prod_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (μ : Measure γ) [SFinite μ] (η : Kernel β δ) [IsSFiniteKernel η] :
    ((const β μ) ×ₖ η) ∘ₖ κ = (const α μ) ×ₖ (η ∘ₖ κ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.prod_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

end Kernel
end ProbabilityTheory

