/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!

# Parallel composition of kernels

Two kernels `κ : Kernel α β` and `η : Kernel γ δ` can be applied in parallel to give a kernel
`κ ∥ₖ η` from `α × γ` to `β × δ`: `(κ ∥ₖ η) (a, c) = (κ a).prod (η c)`.

## Main definitions

* `parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ)`: parallel composition
  of two s-finite kernels. We define a notation `κ ∥ₖ η = parallelComp κ η`.
  `∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1`

## Notation

* `κ ∥ₖ η = ProbabilityTheory.Kernel.parallelComp κ η`

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {κ : Kernel α β} {η : Kernel γ δ} {x : α × γ}

open scoped Classical in
/-- Parallel product of two kernels. -/
noncomputable
irreducible_def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η then
  { toFun := fun x ↦ (κ x.1).prod (η x.2)
    measurable' := by
      have hκ := h.1
      have hη := h.2
      refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
      simp_rw [Measure.prod_apply hs]
      refine Measurable.lintegral_kernel_prod_right'
        (f := fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s)) (κ := prodMkRight γ κ) ?_
      have : (fun y ↦ prodMkLeft α η y.1 (Prod.mk y.2 ⁻¹' s))
          = fun y ↦ prodMkRight β (prodMkLeft α η) y (Prod.mk y.2 ⁻¹' s) := rfl
      rw [this]
      exact measurable_kernel_prodMk_left (measurable_fst.snd.prodMk measurable_snd hs) }
  else 0

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

@[simp]
/-
**ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFinite
Kernel κ) : κ ∥ₖ η = 0
参数：η : Kernel γ δ；h : ¬ IsSFiniteKernel κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.parallelComp_def`：∀ {α : Type u_5} {β : Type u_
6} {γ : Type u_7} {δ : Type u_8} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
lemma parallelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg (not_and_of_not_left _ h)]

@[simp]
/-
**ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFinit
eKernel η) : κ ∥ₖ η = 0
参数：κ : Kernel α β；h : ¬ IsSFiniteKernel η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.parallelComp_def`：∀ {α : Type u_5} {β : Type u_
6} {γ : Type u_7} {δ : Type u_8} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_and_of_not_right`：∀ (a : Prop) {b : Prop}, ¬b → ¬(a ∧ b)
-/
lemma parallelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η) :
    κ ∥ₖ η = 0 := by
  rw [parallelComp, dif_neg (not_and_of_not_right _ h)]
/-
**ProbabilityTheory.Kernel.parallelComp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [
IsSFiniteKernel η] (x : α × γ) : (κ ∥ₖ η) x = (κ x.1).prod (η x.2)
参数：κ : Kernel α β；η : Kernel γ δ；x : α × γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.parallelComp_def`：∀ {α : Type u_5} {β : Type u_
6} {γ : Type u_7} {δ : Type u_8} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ProbabilityTheory.Kernel.coe_mk`：∀ {α : Type u_1} {β : Type u_2} {mα : M
easurableSpace α} {mβ : MeasurableSpace β} (f : α → MeasureTheory.Measure β)   (
hf : Measurable f), ⇑…
-/
lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, dif_pos ⟨inferInstance, inferInstance⟩, coe_mk]
/-
**ProbabilityTheory.Kernel.parallelComp_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：parallelComp_apply' [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set (β × 
δ)} (hs : MeasurableSet s) : (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1
参数：β × δ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma parallelComp_apply' [IsSFiniteKernel κ] [IsSFiniteKernel η]
    {s : Set (β × δ)} (hs : MeasurableSet s) :
    (κ ∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b ⁻¹' s) ∂κ x.1 := by
  rw [parallelComp_apply, Measure.prod_apply hs]
/-
**ProbabilityTheory.Kernel.parallelComp_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：parallelComp_apply_prod [IsSFiniteKernel κ] [IsSFiniteKernel η] (s : Set β
) (t : Set δ) : (κ ∥ₖ η) x (s ×ˢ t) = (κ x.1 s) * (η x.2 t)
参数：s : Set β；t : Set δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma parallelComp_apply_prod [IsSFiniteKernel κ] [IsSFiniteKernel η] (s : Set β) (t : Set δ) :
    (κ ∥ₖ η) x (s ×ˢ t) = (κ x.1 s) * (η x.2 t) := by
  rw [parallelComp_apply, Measure.prod_prod]

@[simp]
/-
**ProbabilityTheory.Kernel.parallelComp_apply_univ** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：parallelComp_apply_univ [IsSFiniteKernel κ] [IsSFiniteKernel η] : (κ ∥ₖ η)
 x Set.univ = κ x.1 Set.univ * η x.2 Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma parallelComp_apply_univ [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) x Set.univ = κ x.1 Set.univ * η x.2 Set.univ := by
  rw [parallelComp_apply, Measure.prod_apply .univ, mul_comm]
  simp

@[simp]
/-
**ProbabilityTheory.Kernel.parallelComp_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：parallelComp_zero_left (η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0
参数：η : Kernel γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.zero_prod`：zero_prod (ν : Measure β) : (0 : Measur
e α).prod ν = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
-/
lemma parallelComp_zero_left (η : Kernel γ δ) : (0 : Kernel α β) ∥ₖ η = 0 := by
  by_cases h : IsSFiniteKernel η
  · ext; simp [parallelComp_apply]
  · exact parallelComp_of_not_isSFiniteKernel_right _ h

@[simp]
/-
**ProbabilityTheory.Kernel.parallelComp_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：parallelComp_zero_right (κ : Kernel α β) : κ ∥ₖ (0 : Kernel γ δ) = 0
参数：κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.prod_zero`：prod_zero (μ : Measure α) : μ.prod (0 :
 Measure β) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
-/
lemma parallelComp_zero_right (κ : Kernel α β) : κ ∥ₖ (0 : Kernel γ δ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext; simp [parallelComp_apply]
  · exact parallelComp_of_not_isSFiniteKernel_left _ h

@[simp]
/-
**ProbabilityTheory.Kernel.id_parallelComp_id** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：id_parallelComp_id : Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (α × β) 
(α × β))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.Measure.dirac_prod_dirac`：dirac_prod_dirac {x : α} {y : β}
 : (dirac x).prod (dirac y) = dirac (x, y)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_parallelComp_id :
    Kernel.id ∥ₖ Kernel.id = (Kernel.id : Kernel (α × β) (α × β)) := by
  ext : 1
  simp [parallelComp_apply, id_apply, Measure.dirac_prod_dirac]
/-
**ProbabilityTheory.Kernel.deterministic_parallelComp_deterministic** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：deterministic_parallelComp_deterministic {f : α -> γ} {g : β -> δ} (hf : M
easurable f) (hg : Measurable g) : (deterministic f hf) ∥ₖ (deterministic g hg) 
= deterministic (Prod.map f g) (hf.prodMap hg)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `MeasureTheory.Measure.dirac_prod_dirac`：dirac_prod_dirac {x : α} {y : β}
 : (dirac x).prod (dirac y) = dirac (x, y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deterministic_parallelComp_deterministic
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (deterministic f hf) ∥ₖ (deterministic g hg)
      = deterministic (Prod.map f g) (hf.prodMap hg) := by
  ext x : 1
  simp_rw [parallelComp_apply, deterministic_apply, Prod.map, Measure.dirac_prod_dirac]
/-
**ProbabilityTheory.Kernel.lintegral_parallelComp** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：lintegral_parallelComp [IsSFiniteKernel κ] [IsSFiniteKernel η] (ac : α × γ
) {g : β × δ -> Real>=0∞} (hg : Measurable g) : ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b,
 ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1
参数：ac : α × γ；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
lemma lintegral_parallelComp [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ b, ∫⁻ d, g (b, d) ∂η ac.2 ∂κ ac.1 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]
/-
**ProbabilityTheory.Kernel.lintegral_parallelComp_symm** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：lintegral_parallelComp_symm [IsSFiniteKernel κ] [IsSFiniteKernel η] (ac : 
α × γ) {g : β × δ -> Real>=0∞} (hg : Measurable g) : ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = 
∫⁻ d, ∫⁻ b, g (b, d) ∂κ ac.1 ∂η ac.2
参数：ac : α × γ；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
lemma lintegral_parallelComp_symm [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (ac : α × γ) {g : β × δ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ bd, g bd ∂(κ ∥ₖ η) ac = ∫⁻ d, ∫⁻ b, g (b, d) ∂κ ac.1 ∂η ac.2 := by
  rw [parallelComp_apply, MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]
/-
**ProbabilityTheory.Kernel.parallelComp_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：parallelComp_sum_left {ι : Type*} [Countable ι] (κ : ι -> Kernel α β) [for
all i, IsSFiniteKernel (κ i)] (η : Kernel γ δ) : Kernel.sum κ ∥ₖ η = Kernel.sum 
fun i => κ i ∥ₖ η
参数：κ : ι -> Kernel α β；κ i；η : Kernel γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.prod_sum_left`：prod_sum_left {ι : Type*} (m : ι ->
 Measure α) (μ : Measure β) [SFinite μ] : (Measure.sum m).prod μ = Measure.sum (
fun i => (m i).prod μ)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
-/
lemma parallelComp_sum_left {ι : Type*} [Countable ι] (κ : ι → Kernel α β)
    [∀ i, IsSFiniteKernel (κ i)] (η : Kernel γ δ) :
    Kernel.sum κ ∥ₖ η = Kernel.sum fun i ↦ κ i ∥ₖ η := by
  by_cases h : IsSFiniteKernel η
  swap; · simp [h]
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply, Measure.prod_sum_left]
/-
**ProbabilityTheory.Kernel.parallelComp_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：parallelComp_sum_right {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι -
> Kernel γ δ) [forall i, IsSFiniteKernel (η i)] : κ ∥ₖ Kernel.sum η = Kernel.sum
 fun i => κ ∥ₖ η i
参数：κ : Kernel α β；η : ι -> Kernel γ δ；η i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.prod_sum_right`：prod_sum_right {ι' : Type*} [Count
able ι'] (m : Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : m.p
rod (Measure.sum m') = Mea…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
-/
lemma parallelComp_sum_right {ι : Type*} [Countable ι] (κ : Kernel α β)
    (η : ι → Kernel γ δ) [∀ i, IsSFiniteKernel (η i)] :
    κ ∥ₖ Kernel.sum η = Kernel.sum fun i ↦ κ ∥ₖ η i := by
  by_cases h : IsSFiniteKernel κ
  swap; · simp [h]
  ext x
  simp_rw [Kernel.sum_apply, parallelComp_apply, Kernel.sum_apply, Measure.prod_sum_right]
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (κ ∥ₖ η) :=
  ⟨fun x ↦ ⟨by simp [parallelComp_apply_univ]⟩⟩
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ∥ₖ η) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (κ ∥ₖ η) := by
  refine ⟨⟨κ.bound * η.bound, ENNReal.mul_lt_top κ.bound_lt_top η.bound_lt_top, fun a ↦ ?_⟩⟩
  calc (κ ∥ₖ η) a Set.univ
  _ = κ a.1 Set.univ * η a.2 Set.univ := parallelComp_apply_univ
  _ ≤ κ.bound * η.bound := by
    gcongr
    · exact measure_le_bound κ a.1 Set.univ
    · exact measure_le_bound η a.2 Set.univ
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSFiniteKernel (κ ∥ₖ η) := by
  by_cases h : IsSFiniteKernel κ
  swap
  · simp only [h, not_false_eq_true, parallelComp_of_not_isSFiniteKernel_left]
    infer_instance
  by_cases h : IsSFiniteKernel η
  swap
  · simp only [h, not_false_eq_true, parallelComp_of_not_isSFiniteKernel_right]
    infer_instance
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, parallelComp_sum_left, parallelComp_sum_right]
  infer_instance

end ProbabilityTheory.Kernel

