/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : Kernel α β`, get a `Measure (α × β)`.

## Notation

* `μ ⊗ₘ κ = μ.compProd κ`
-/

@[expose] public section

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- The composition-product of a measure and a kernel. -/
noncomputable
/-
**MeasureTheory.Measure.compProd** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β)
参数：μ : Measure α；κ : Kernel α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) :=
  (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp]
/-
**MeasureTheory.Measure.compProd_of_not_sfinite** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：compProd_of_not_sfinite (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ)
 : μ otimesₘ κ = 0
参数：μ : Measure α；κ : Kernel α β；h : ¬ SFinite μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用引理 `ProbabilityTheory.Kernel.isSFiniteKernel_const`：isSFiniteKernel_const [N
onempty α] {μβ : Measure β} : IsSFiniteKernel (const α μβ) ↔ SFinite μβ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
-/
lemma compProd_of_not_sfinite (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_left, zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

@[simp]
/-
**MeasureTheory.Measure.compProd_of_not_isSFiniteKernel** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：compProd_of_not_isSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ Is
SFiniteKernel κ) : μ otimesₘ κ = 0
参数：μ : Measure α；κ : Kernel α β；h : ¬ IsSFiniteKernel κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用引理 `ProbabilityTheory.Kernel.isSFiniteKernel_prodMkLeft_unit`：isSFiniteKerne
l_prodMkLeft_unit {κ : Kernel α β} : IsSFiniteKernel (prodMkLeft Unit κ) ↔ IsSFi
niteKernel κ
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
-/
lemma compProd_of_not_isSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_right, zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]
/-
**MeasureTheory.Measure.compProd_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : Mea
surableSet s) : (μ otimesₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']

@[simp]
/-
**MeasureTheory.Measure.compProd_apply_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] : (μ otimesₘ κ) univ = 
μ univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.compProd_apply_univ`：compProd_apply_univ {κ : K
ernel α β} {η : Kernel (α × β) γ} [IsSFiniteKernel κ] [IsMarkovKernel η] {a : α}
 : (κ otimesₖ η) a Set.univ = κ a …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.prodMkLeft`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] : (μ ⊗ₘ κ) univ = μ univ := by
  simp [compProd]
/-
**MeasureTheory.Measure.compProd_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β
} (hs : MeasurableSet s) (ht : MeasurableSet t) : (μ otimesₘ κ) (s ×ˢ t) = ∫⁻ a 
in s, κ a t ∂μ
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.compProd_apply_prod`：compProd_apply_prod {κ : K
ernel α β} {η : Kernel (α × β) γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α
} {s : Set β} {t : Set γ} (hs : Me…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  simp [compProd, Kernel.compProd_apply_prod hs ht]
/-
**MeasureTheory.Measure.compProd_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：compProd_congr [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) : μ
 otimesₘ κ = μ otimesₘ η
参数：h : κ =ᵐ[μ] η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用引理 `ProbabilityTheory.Kernel.compProd_congr`：compProd_congr {κ : Kernel α β}
 {η η' : Kernel (α × β) γ} [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : forall 
a, forallᵐ b ∂(κ a), η (a, b)…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma compProd_congr [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) :
    μ ⊗ₘ κ = μ ⊗ₘ η := by
  rw [compProd, compProd]
  congr 1
  refine Kernel.compProd_congr ?_
  simpa
/-
**MeasureTheory.Measure.compProd_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β),   MeasureTheory.Measure.compProd 0 κ
 = 0
参数：κ : ProbabilityTheory.Kernel α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.const_zero`：const_zero : const α (0 : Measure β
) = 0
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_left`：compProd_zero_left (κ : Ker
nel (α × β) γ) : (0 : Kernel α β) otimesₖ κ = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]
/-
**MeasureTheory.Measure.compProd_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ : MeasureTheory.Measure α),   μ.compProd 0 = 0
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prodMkLeft_zero`：prodMkLeft_zero : Kernel.prodM
kLeft α (0 : Kernel β γ) = 0
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_right`：compProd_zero_right (κ : K
ernel α β) (γ : Type*) {mγ : MeasurableSpace γ} : κ otimesₖ (0 : Kernel (α × β) 
γ) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : Kernel α β) = 0 := by simp [compProd]
/-
**MeasureTheory.Measure.compProd_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：compProd_eq_zero_iff [SFinite μ] [IsSFiniteKernel κ] : μ otimesₘ κ = 0 ↔ f
orallᵐ a ∂μ, κ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.compProd_zero_right`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure 
α),   μ.compProd 0 = 0
· 使用引理 `MeasureTheory.Measure.compProd_congr`：compProd_congr [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) : μ otimesₘ κ = μ otimesₘ η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma compProd_eq_zero_iff [SFinite μ] [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = 0 ↔ ∀ᵐ a ∂μ, κ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← measure_univ_eq_zero]
    refine (lintegral_eq_zero_iff (Kernel.measurable_coe _ .univ)).mp ?_
    rw [← setLIntegral_univ, ← compProd_apply_prod .univ .univ, h]
    simp
  · rw [← compProd_zero_right μ]
    exact compProd_congr h
/-
**MeasureTheory.Measure._root_.ProbabilityTheory.Kernel.compProd_apply_eq_compPr
od_sectR** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR {γ : Type*}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a = (κ a) ⊗ₘ (Kernel.sectR η a) := by
  ext s hs
  simp_rw [Kernel.compProd_apply hs, compProd_apply hs, Kernel.sectR_apply]
/-
**MeasureTheory.Measure.compProd_id** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：compProd_id [SFinite μ] : μ otimesₘ Kernel.id = μ.map Function.diag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
-/
lemma compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map Function.diag := by
  ext s hs
  rw [compProd_apply hs, map_apply (measurable_id.prod measurable_id) hs]
  have h_meas a : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  simp_rw [Kernel.id_apply, dirac_apply' _ (h_meas _)]
  calc ∫⁻ a, (Prod.mk a ⁻¹' s).indicator 1 a ∂μ
  _ = ∫⁻ a, (Function.diag ⁻¹' s).indicator 1 a ∂μ := rfl
  _ = μ (Function.diag ⁻¹' s) := by
    rw [lintegral_indicator_one]
    exact (measurable_id.prod measurable_id) hs
/-
**MeasureTheory.Measure.ae_compProd_of_ae_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：ae_compProd_of_ae_ae {p : α × β -> Prop} (hp : MeasurableSet {x | p x}) (h
 : forallᵐ a ∂μ, forallᵐ b ∂(κ a), p (a, b)) : forallᵐ x ∂(μ otimesₘ κ), p x
参数：hp : MeasurableSet {x | p x}；h : forallᵐ a ∂μ, forallᵐ b ∂(κ a), p (a, b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.ae_compProd_of_ae_ae`：ae_compProd_of_ae_ae {κ :
 Kernel α β} {η : Kernel (α × β) γ} {p : β × γ -> Prop} (hp : MeasurableSet {x |
 p x}) (h : forallᵐ b ∂κ a, forallᵐ…
-/
lemma ae_compProd_of_ae_ae {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x :=
  Kernel.ae_compProd_of_ae_ae hp h
/-
**MeasureTheory.Measure.ae_ae_of_ae_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop} (
h : forallᵐ x ∂(μ otimesₘ κ), p x) : forallᵐ a ∂μ, forallᵐ b ∂κ a, p (a, b)
参数：h : forallᵐ x ∂(μ otimesₘ κ), p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_compProd`：ae_ae_of_ae_compProd {p :
 β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a, p bc) : forallᵐ b ∂κ a, forall
ᵐ c ∂η (a, b), p (b, c)
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) := by
  convert! Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`
/-
**MeasureTheory.Measure.ae_compProd_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β -> Prop} (hp : 
MeasurableSet {x | p x}) : (forallᵐ x ∂(μ otimesₘ κ), p x) ↔ forallᵐ a ∂μ, foral
lᵐ b ∂(κ a), p (a, b)
参数：hp : MeasurableSet {x | p x}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.ae_compProd_iff`：ae_compProd_iff {p : β × γ -> 
Prop} (hp : MeasurableSet {x | p x}) : (forallᵐ bc ∂(κ otimesₖ η) a, p bc) ↔ for
allᵐ b ∂κ a, forallᵐ c ∂η (a, …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  Kernel.ae_compProd_iff hp
/-
**MeasureTheory.Measure.ae_compProd_of_ae_fst** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：ae_compProd_of_ae_fst (κ : Kernel α β) {p : α -> Prop} (hp : MeasurableSet
 {x | p x}) (h : forallᵐ a ∂μ, p a) : forallᵐ x ∂(μ otimesₘ κ), p x.1
参数：κ : Kernel α β；hp : MeasurableSet {x | p x}；h : forallᵐ a ∂μ, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.ae_compProd_of_ae_ae`：ae_compProd_of_ae_ae {p : α 
× β -> Prop} (hp : MeasurableSet {x | p x}) (h : forallᵐ a ∂μ, forallᵐ b ∂(κ a),
 p (a, b)) : forallᵐ x ∂(μ otime…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma ae_compProd_of_ae_fst (κ : Kernel α β) {p : α → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x.1 :=
  ae_compProd_of_ae_ae (measurable_fst hp) <| by filter_upwards [h] with a ha using by simp [ha]
/-
**MeasureTheory.Measure.ae_eq_compProd_of_ae_eq_fst** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：ae_eq_compProd_of_ae_eq_fst {γ : Type*} {mγ : MeasurableSpace γ} [Measurab
leEq γ] (κ : Kernel α β) {f g : α -> γ} (hf : Measurable f) (hg : Measurable g) 
(h : f =ᵐ[μ] g) : (fun p => f p.1) =ᵐ[μ otimesₘ κ] (fun p => g p.1)
参数：κ : Kernel α β；hf : Measurable f；hg : Measurable g；h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.ae_compProd_of_ae_fst`：ae_compProd_of_ae_fst (κ : 
Kernel α β) {p : α -> Prop} (hp : MeasurableSet {x | p x}) (h : forallᵐ a ∂μ, p 
a) : forallᵐ x ∂(μ otimesₘ κ), p …
· 使用定理 `measurableSet_eq_fun`：measurableSet_eq_fun {m : MeasurableSpace α} [Meas
urableSpace β] [MeasurableEq β] {f g : α -> β} (hf : Measurable f) (hg : Measura
ble g) : M…
-/
lemma ae_eq_compProd_of_ae_eq_fst {γ : Type*} {mγ : MeasurableSpace γ} [MeasurableEq γ]
    (κ : Kernel α β) {f g : α → γ} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
/-
**MeasureTheory.Measure.compProd_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] : μ otimesₘ (Kernel
.const α ν) = μ.prod ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition product of a measure and a constant kernel is the product betwee
n the two
measures.
-/
lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  simp_rw [compProd_apply hs, prod_apply hs, Kernel.const_apply]
/-
**MeasureTheory.Measure.compProd_add_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α 
β) : (μ + ν) otimesₘ κ = μ otimesₘ κ + ν otimesₘ κ
参数：μ ν : Measure α；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.const_add`：const_add (β : Type*) [MeasurableSpa
ce β] (μ ν : Measure α) : const β (μ + ν) = const β μ + const β ν
· 使用引理 `ProbabilityTheory.Kernel.compProd_add_left`：compProd_add_left (μ κ : Ker
nel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel μ] [IsSFiniteKernel κ] : (μ + κ
) otimesₖ η = μ otimesₖ η + κ ot…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, _root_.add_apply]
  · simp [hκ]
/-
**MeasureTheory.Measure.compProd_add_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：compProd_add_right (μ : Measure α) (κ η : Kernel α β) [IsSFiniteKernel κ] 
[IsSFiniteKernel η] : μ otimesₘ (κ + η) = μ otimesₘ κ + μ otimesₘ η
参数：μ : Measure α；κ η : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.prodMkLeft_add`：prodMkLeft_add (κ η : Kernel α 
β) : prodMkLeft γ (κ + η) = prodMkLeft γ κ + prodMkLeft γ η
· 使用引理 `ProbabilityTheory.Kernel.compProd_add_right`：compProd_add_right (μ : Ker
nel α β) (κ η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] : μ ot
imesₖ (κ + η) = μ otimesₖ κ + μ o…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma compProd_add_right (μ : Measure α) (κ η : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η := by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, _root_.add_apply]
  · simp [hμ]
/-
**MeasureTheory.Measure.compProd_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：compProd_sum_left {ι : Type*} [Countable ι] {μ : ι -> Measure α} [forall i
, SFinite (μ i)] : (sum μ) otimesₘ κ = sum (fun i => (μ i) otimesₘ κ)
参数：μ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.sum_const`：sum_const [Countable ι] (μ : ι -> Me
asure β) : Kernel.sum (fun n => const α (μ n)) = const α (Measure.sum μ)
· 使用引理 `ProbabilityTheory.Kernel.compProd_sum_left`：compProd_sum_left {ι : Type*
} [Countable ι] {κ : ι -> Kernel α β} {η : Kernel (α × β) γ} [forall i, IsSFinit
eKernel (κ i)] : Kernel.sum κ ot…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
-/
lemma compProd_sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α} [∀ i, SFinite (μ i)] :
    (sum μ) ⊗ₘ κ = sum (fun i ↦ (μ i) ⊗ₘ κ) := by
  rw [compProd, ← Kernel.sum_const, Kernel.compProd_sum_left]
  rfl
/-
**MeasureTheory.Measure.compProd_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：compProd_sum_right {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} [h : fo
rall i, IsSFiniteKernel (κ i)] : μ otimesₘ (Kernel.sum κ) = sum (fun i => μ otim
esₘ (κ i))
参数：κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.sum_prodMkLeft`：sum_prodMkLeft {ι : Type*} [Cou
ntable ι] {κ : ι -> Kernel α β} : Kernel.sum (fun i => Kernel.prodMkLeft γ (κ i)
) = Kernel.prodMkLeft γ (Kern…
· 使用引理 `ProbabilityTheory.Kernel.compProd_sum_right`：compProd_sum_right {ι : Typ
e*} [Countable ι] {κ : Kernel α β} {η : ι -> Kernel (α × β) γ} [forall i, IsSFin
iteKernel (η i)] : κ otimesₖ Kern…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
-/
lemma compProd_sum_right {ι : Type*} [Countable ι] {κ : ι → Kernel α β}
    [h : ∀ i, IsSFiniteKernel (κ i)] :
    μ ⊗ₘ (Kernel.sum κ) = sum (fun i ↦ μ ⊗ₘ (κ i)) := by
  rw [compProd, ← Kernel.sum_prodMkLeft, Kernel.compProd_sum_right]
  rfl

@[simp]
/-
**MeasureTheory.Measure.fst_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel 
κ] : (μ otimesₘ κ).fst = μ
参数：μ : Measure α；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.fst_apply`：fst_apply (κ : Kernel α (β × γ)) (a 
: α) : fst κ a = (κ a).map Prod.fst
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd`：fst_compProd (κ : Kernel α β) (η 
: Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] : fst (κ otimesₖ η) =
 κ
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsMarkovKernel.prodMkLeft`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
lemma fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [compProd, Measure.fst, ← Kernel.fst_apply, Kernel.fst_compProd, Kernel.const_apply]
/-
**MeasureTheory.Measure.compProd_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：compProd_smul_left (a : Real>=0∞) [SFinite μ] [IsSFiniteKernel κ] : (a • μ
) otimesₘ κ = a • (μ otimesₘ κ)
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteHSMulMeasure`：∀ {α : Type u_1} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {R : Type u_2} 
  [inst : SMul R ENNReal] […
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) ⊗ₘ κ = a • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [compProd_apply hs, lintegral_smul_measure, smul_apply, smul_eq_mul]

section Integral

/-
**MeasureTheory.Measure.lintegral_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：lintegral_compProd [SFinite μ] [IsSFiniteKernel κ] {f : α × β -> Real>=0∞}
 (hf : Measurable f) : ∫⁻ x, f x ∂(μ otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.lintegral_compProd _ _ _ hf]
  simp
/-
**MeasureTheory.Measure.setLIntegral_compProd** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：setLIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {f : α × β -> Real>=
0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : Mea
surableSet t) : ∫⁻ x in s ×ˢ t, f x ∂(μ otimesₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a,
 b) ∂(κ a) ∂μ
参数：hf : Measurable f；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.setLIntegral_compProd`：setLIntegral_compProd (κ
 : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a
 : α) {f : β × γ -> Real>=0∞} (hf : …
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

end Integral

/-
**MeasureTheory.Measure.dirac_compProd_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：dirac_compProd_apply [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel
 κ] {s : Set (α × β)} (hs : MeasurableSet s) : (Measure.dirac a otimesₘ κ) s = κ
 a (Prod.mk a ⁻¹' s)
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
-/
lemma dirac_compProd_apply [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs, lintegral_dirac]
/-
**MeasureTheory.Measure.dirac_unit_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：dirac_unit_compProd (κ : Kernel Unit β) [IsSFiniteKernel κ] : Measure.dira
c () otimesₘ κ = (κ ()).map (Prod.mk ())
参数：κ : Kernel Unit β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.dirac_compProd_apply`：dirac_compProd_apply [Measur
ableSingletonClass α] {a : α} [IsSFiniteKernel κ] {s : Set (α × β)} (hs : Measur
ableSet s) : (Measure.dirac a ot…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma dirac_unit_compProd (κ : Kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
/-
**MeasureTheory.Measure.dirac_unit_compProd_const** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：dirac_unit_compProd_const (μ : Measure β) [SFinite μ] : Measure.dirac () o
timesₘ Kernel.const Unit μ = μ.map (Prod.mk ())
参数：μ : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.dirac_unit_compProd`：dirac_unit_compProd (κ : Kern
el Unit β) [IsSFiniteKernel κ] : Measure.dirac () otimesₘ κ = (κ ()).map (Prod.m
k ())
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ
-/
lemma dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    Measure.dirac () ⊗ₘ Kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, Kernel.const_apply]
/-
**MeasureTheory.Measure.snd_dirac_unit_compProd_const** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：snd_dirac_unit_compProd_const (μ : Measure β) [SFinite μ] : snd (Measure.d
irac () otimesₘ Kernel.const Unit μ) = μ
参数：μ : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_const`：compProd_const {ν : Measure β} [SF
inite μ] [SFinite ν] : μ otimesₘ (Kernel.const α ν) = μ.prod ν
· 使用定理 `MeasureTheory.instSFiniteOfCountable`：∀ {α : Type u_1} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} [Countable α], MeasureTheory.SFinite μ
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用引理 `MeasureTheory.Measure.snd_prod`：snd_prod [IsProbabilityMeasure μ] : (μ.p
rod ν).snd = ν
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_dirac_unit_compProd_const (μ : Measure β) [SFinite μ] :
    snd (Measure.dirac () ⊗ₘ Kernel.const Unit μ) = μ := by simp
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SFinite (μ ⊗ₘ κ) := by rw [compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]
  exact IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure ()

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
@[simp]
/-
**MeasureTheory.Measure.compProd_assoc** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：compProd_assoc {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ}
 : (μ otimesₘ (κ otimesₖ η)).map MeasurableEquiv.prodAssoc.symm = μ otimesₘ κ ot
imesₘ η
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteProdCompProd`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.compProd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.compProd_zero_right`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure 
α),   μ.compProd 0 = 0
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.compProd_zero_left`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kerne
l α β),   MeasureTheory.Measur…
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0

--- 原说明 ---
`Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different.
-/
lemma compProd_assoc {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ} :
    (μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm = μ ⊗ₘ κ ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.lintegral_compProd]
  swap; · exact Kernel.measurable_kernel_prodMk_left hs
  congr with a
  rw [Kernel.compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

/-- `Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
@[simp]
/-
**MeasureTheory.Measure.compProd_assoc'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：compProd_assoc' {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ
} : (μ otimesₘ κ otimesₘ η).map MeasurableEquiv.prodAssoc = μ otimesₘ (κ otimesₖ
 η)
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_map_symm`：map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm)
.map e = ν
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Measure.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc`
because the products of types `α × β × γ` and `(α × β) × γ` are different.
-/
lemma compProd_assoc' {γ : Type*} {mγ : MeasurableSpace γ} {η : Kernel (α × β) γ} :
    (μ ⊗ₘ κ ⊗ₘ η).map MeasurableEquiv.prodAssoc = μ ⊗ₘ (κ ⊗ₖ η) := by
  simp [← Measure.compProd_assoc]

section AbsolutelyContinuous

/-
**MeasureTheory.Measure.AbsolutelyContinuous.compProd_left** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   [MeasureTheory.SFinite ν],   μ.Absolut
elyContinuous ν → ∀ (κ : ProbabilityTheory.Kernel α β), (μ.compProd κ).Absolutel
yContinuous (ν.compProd κ)
参数：κ : ProbabilityTheory.Kernel α β；μ.compProd κ；ν.compProd κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.sFinite_of_absolutelyContinuous`：sFinite_of_absolutelyCont
inuous {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν) : SFinite μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma AbsolutelyContinuous.compProd_left [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    exact hμν.ae_eq hs_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.compProd_right** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β} [Me
asureTheory.SFinite μ] [ProbabilityTheory.IsSFiniteKernel η],   (∀ᵐ (a : α) ∂μ, 
(κ a).AbsolutelyContinuous (η a)) → (μ.compProd κ).AbsolutelyContinuous (μ.compP
rod η)
参数：∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)；μ.compProd κ；μ.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
-/
lemma AbsolutelyContinuous.compProd_right [SFinite μ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]
/-
**MeasureTheory.Measure.AbsolutelyContinuous.compProd** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β} [
MeasureTheory.SFinite ν] [ProbabilityTheory.IsSFiniteKernel η],   μ.AbsolutelyCo
ntinuous ν →     (∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)) → (μ.compProd
 κ).AbsolutelyContinuous (ν.compProd η)
参数：∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)；μ.compProd κ；ν.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.sFinite_of_absolutelyContinuous`：sFinite_of_absolutelyCont
inuous {ν : Measure α} [SFinite ν] (hμν : μ ≪ ν) : SFinite μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_right`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measur
eTheory.Measure α}   {κ η : ProbabilityTheory.K…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_left`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measu
reTheory.Measure α}   [MeasureTheory.SFinite ν…
-/
lemma AbsolutelyContinuous.compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.AbsolutelyContinuous.compProd_right hκη).trans (hμν.compProd_left _)
/-
**MeasureTheory.Measure.absolutelyContinuous_of_compProd** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero :
 forall a, NeZero (κ a)] (h : μ otimesₘ κ ≪ ν otimesₘ η) : μ ≪ ν
参数：κ a；h : μ otimesₘ κ ≪ ν otimesₘ η。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.setLIntegral_measure_zero`：setLIntegral_measure_zero (s : 
Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) : ∫⁻ x in s, f x ∂μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma absolutelyContinuous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : ∀ a, NeZero (κ a)]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  have h1 : (ν ⊗ₘ η) (s ×ˢ univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ ⊗ₘ κ) (s ×ˢ univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : ∃ a, κ a univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out
/-
**MeasureTheory.Measure.absolutelyContinuous_compProd_left_iff** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_compProd_left_iff [SFinite μ] [SFinite ν] [IsSFiniteK
ernel κ] [forall a, NeZero (κ a)] : μ otimesₘ κ ≪ ν otimesₘ κ ↔ μ ≪ ν
参数：κ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_of_compProd`：absolutelyContin
uous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : forall a, NeZero (κ a
)] (h : μ otimesₘ κ ≪ ν otimesₘ η) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_left`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measu
reTheory.Measure α}   [MeasureTheory.SFinite ν…
-/
lemma absolutelyContinuous_compProd_left_iff [SFinite μ] [SFinite ν]
    [IsSFiniteKernel κ] [∀ a, NeZero (κ a)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ ↔ μ ≪ ν :=
  ⟨absolutelyContinuous_of_compProd, fun h ↦ h.compProd_left κ⟩
/-
**MeasureTheory.Measure.AbsolutelyContinuous.compProd_of_compProd** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β} [
MeasureTheory.SFinite ν] [ProbabilityTheory.IsSFiniteKernel η],   μ.AbsolutelyCo
ntinuous ν →     (μ.compProd κ).AbsolutelyContinuous (μ.compProd η) → (μ.compPro
d κ).AbsolutelyContinuous (ν.compProd η)
参数：μ.compProd κ；μ.compProd η；μ.compProd κ；ν.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用引理 `MeasureTheory.Measure.ae_compProd_iff`：ae_compProd_iff [SFinite μ] [IsSF
initeKernel κ] {p : α × β -> Prop} (hp : MeasurableSet {x | p x}) : (forallᵐ x ∂
(μ otimesₘ κ), p x) ↔ foral…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma AbsolutelyContinuous.compProd_of_compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  suffices (μ ⊗ₘ η) s = 0 from hκη this
  rw [measure_eq_zero_iff_ae_notMem, ae_compProd_iff hs.compl] at hs_zero ⊢
  exact hμν.ae_le hs_zero

end AbsolutelyContinuous

section MutuallySingular

/-
**MeasureTheory.Measure.MutuallySingular.compProd_of_left** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α},   μ.MutuallySingular ν → ∀ (κ η : Proba
bilityTheory.Kernel α β), (μ.compProd κ).MutuallySingular (ν.compProd η)
参数：κ η : ProbabilityTheory.Kernel α β；μ.compProd κ；ν.compProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
· 使用引理 `Set.compl_prod_eq_union`：compl_prod_eq_union {α β : Type*} (s : Set α) (
t : Set β) : (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_nullSet`：restrict_nullSe
t (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_compl_nullSet`：restrict_
compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
-/
lemma MutuallySingular.compProd_of_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α β) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hη]; simp
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ, compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp
/-
**MeasureTheory.Measure.mutuallySingular_of_mutuallySingular_compProd** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α} [SFinite μ] 
[SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : μ otimesₘ κ ⟂ₘ ν otimes
ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) : forallᵐ x ∂ξ, κ x ⟂ₘ η x
参数：h : μ otimesₘ κ ⟂ₘ ν otimesₘ η；hμ : ξ ≪ μ；hν : ξ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_nullSet`：measure_nullSet 
(h : μ ⟂ₘ ν) : μ h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measure_compl_nullSet`：measure_co
mpl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma mutuallySingular_of_mutuallySingular_compProd {ξ : Measure α}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η) (hμ : ξ ≪ μ) (hν : ξ ≪ ν) :
    ∀ᵐ x ∂ξ, κ x ⟂ₘ η x := by
  have hs : MeasurableSet h.nullSet := h.measurableSet_nullSet
  have hμ_zero : (μ ⊗ₘ κ) h.nullSet = 0 := h.measure_nullSet
  have hν_zero : (ν ⊗ₘ η) h.nullSetᶜ = 0 := h.measure_compl_nullSet
  rw [compProd_apply, lintegral_eq_zero_iff'] at hμ_zero hν_zero
  · filter_upwards [hμ hμ_zero, hν hν_zero] with x hxμ hxν
    exact ⟨Prod.mk x ⁻¹' h.nullSet, measurable_prodMk_left hs, ⟨hxμ, hxν⟩⟩
  · exact (Kernel.measurable_kernel_prodMk_left hs.compl).aemeasurable
  · exact (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
  · exact hs.compl
  · exact hs
/-
**MeasureTheory.Measure.mutuallySingular_compProd_left_iff** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：mutuallySingular_compProd_left_iff [SFinite μ] [SigmaFinite ν] [IsSFiniteK
ernel κ] [hκ : forall x, NeZero (κ x)] : μ otimesₘ κ ⟂ₘ ν otimesₘ κ ↔ μ ⟂ₘ ν
参数：κ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.withDensity_rnDeriv_eq_zero`：withDensity_rnDeriv_e
q_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : ν.withDensity (μ.rnDe
riv ν) = 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.mutuallySingular_of_mutuallySingular_compProd`：mut
uallySingular_of_mutuallySingular_compProd {ξ : Measure α} [SFinite μ] [SFinite 
ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] (h : μ otimesₘ…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_eq_bot`：ae_eq_bot : ae μ = ⊥ ↔ μ = 0
· 使用定理 `Filter.eventually_false_iff_eq_bot`：eventually_false_iff_eq_bot {f : Fil
ter α} : (forallᶠ _ in f, False) ↔ f = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_left`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measur
eTheory.Measure α},   μ.MutuallySingular ν → …
-/
lemma mutuallySingular_compProd_left_iff [SFinite μ] [SigmaFinite ν]
    [IsSFiniteKernel κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compProd_of_left _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_
    (ξ := ν.withDensity (μ.rnDeriv ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)
/-
**MeasureTheory.Measure.AbsolutelyContinuous.mutuallySingular_compProd_iff** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β} [
MeasureTheory.SigmaFinite μ] [MeasureTheory.SigmaFinite ν],   μ.AbsolutelyContin
uous ν →     ((μ.compProd κ).MutuallySingular (ν.compProd η) ↔ (μ.compProd κ).Mu
tuallySingular (μ.compProd η))
参数：(μ.compProd κ).MutuallySingular (ν.compProd η) ↔ (μ.compProd κ).MutuallySingu
lar (μ.compProd η)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.compProd_add_left`：compProd_add_left (μ ν : Measur
e α) [SFinite μ] [SFinite ν] (κ : Kernel α β) : (μ + ν) otimesₘ κ = μ otimesₘ κ 
+ ν otimesₘ κ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_right_iff`：add_right_iff : μ 
⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_left`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measur
eTheory.Measure α},   μ.MutuallySingular ν → …
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_left`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measu
reTheory.Measure α}   [MeasureTheory.SFinite ν…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv`：absolute
lyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
 μ ≪ μ.withDensity (ν.rnDeriv μ)
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma AbsolutelyContinuous.mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η := by
  conv_lhs => rw [ν.haveLebesgueDecomposition_add μ]
  rw [compProd_add_left, MutuallySingular.add_right_iff]
  simp only [(mutuallySingular_singularPart ν μ).symm.compProd_of_left κ η, true_and]
  refine ⟨fun h ↦ h.mono_ac .rfl ?_, fun h ↦ h.mono_ac .rfl ?_⟩
  · exact (absolutelyContinuous_withDensity_rnDeriv hμν).compProd_left _
  · exact (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).compProd_left _
/-
**MeasureTheory.Measure.mutuallySingular_compProd_iff** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν] : μ otimesₘ 
κ ⟂ₘ ν otimesₘ η ↔ forall ξ, SFinite ξ -> ξ ≪ μ -> ξ ≪ ν -> ξ otimesₘ κ ⟂ₘ ξ oti
mesₘ η
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.compProd_add_left`：compProd_add_left (μ ν : Measur
e α) [SFinite μ] [SFinite ν] (κ : Kernel α β) : (μ + ν) otimesₘ κ = μ otimesₘ κ 
+ ν otimesₘ κ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_left`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measur
eTheory.Measure α},   μ.MutuallySingular ν → …
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mutuallySingular_compProd_iff
`：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace
 β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_left`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measu
reTheory.Measure α}   [MeasureTheory.SFinite ν…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.withDensity_rnDeriv`：∀ {α : T
ype u_1} {m : MeasurableSpace α} {μ ν ξ : MeasureTheory.Measure α} [μ.HaveLebesg
ueDecomposition ν],   ξ.AbsolutelyContinuous μ → ξ.A…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
lemma mutuallySingular_compProd_iff [SigmaFinite μ] [SigmaFinite ν] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η ↔ ∀ ξ, SFinite ξ → ξ ≪ μ → ξ ≪ ν → ξ ⊗ₘ κ ⟂ₘ ξ ⊗ₘ η := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  rw [compProd_add_left, MutuallySingular.add_left_iff]
  simp only [(mutuallySingular_singularPart μ ν).compProd_of_left κ η, true_and]
  rw [(withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).mutuallySingular_compProd_iff]
  refine ⟨fun h ξ hξ hξμ hξν ↦ ?_, fun h ↦ ?_⟩
  · exact h.mono_ac ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
      ((hξμ.withDensity_rnDeriv hξν).compProd_left _)
  · refine h _ ?_ ?_ ?_
    · infer_instance
    · exact absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _)
    · exact withDensity_absolutelyContinuous ν (μ.rnDeriv ν)

end MutuallySingular

/-
**MeasureTheory.Measure.absolutelyContinuous_compProd_of_compProd** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν] 
(hκη : μ otimesₘ κ ≪ ν otimesₘ η) : μ otimesₘ κ ≪ μ otimesₘ η
参数：hκη : μ otimesₘ κ ≪ ν otimesₘ η。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_of_add_of_mutuallySingular`：a
bsolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α} (h : μ ≪ ν₁ +
 ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeasureTheory.Measure.compProd_add_left`：compProd_add_left (μ ν : Measur
e α) [SFinite μ] [SFinite ν] (κ : Kernel α β) : (μ + ν) otimesₘ κ = μ otimesₘ κ 
+ ν otimesₘ κ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_left`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measur
eTheory.Measure α},   μ.MutuallySingular ν → …
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_left`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measu
reTheory.Measure α}   [MeasureTheory.SFinite ν…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma absolutelyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν]
    (hκη : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ, compProd_add_left, add_comm] at hκη
  have h := absolutelyContinuous_of_add_of_mutuallySingular hκη
    ((mutuallySingular_singularPart _ _).symm.compProd_of_left _ _)
  refine h.trans (AbsolutelyContinuous.compProd_left ?_ _)
  exact withDensity_absolutelyContinuous _ _
/-
**MeasureTheory.Measure.absolutelyContinuous_compProd_iff** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_compProd_iff [SigmaFinite μ] [SigmaFinite ν] [IsSFini
teKernel κ] [IsSFiniteKernel η] [forall x, NeZero (κ x)] : μ otimesₘ κ ≪ ν otime
sₘ η ↔ μ ≪ ν ∧ μ otimesₘ κ ≪ μ otimesₘ η
参数：κ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_of_compProd`：absolutelyContin
uous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : forall a, NeZero (κ a
)] (h : μ otimesₘ κ ≪ ν otimesₘ η) : μ ≪ ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_compProd_of_compProd`：absolut
elyContinuous_compProd_of_compProd [SigmaFinite μ] [SigmaFinite ν] (hκη : μ otim
esₘ κ ≪ ν otimesₘ η) : μ otimesₘ κ ≪ μ otimesₘ η
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.compProd_of_compProd`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν 
: MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma absolutelyContinuous_compProd_iff
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η] [∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
  ⟨fun h ↦ ⟨absolutelyContinuous_of_compProd h, absolutelyContinuous_compProd_of_compProd h⟩,
    fun h ↦ h.1.compProd_of_compProd h.2⟩

end MeasureTheory.Measure

