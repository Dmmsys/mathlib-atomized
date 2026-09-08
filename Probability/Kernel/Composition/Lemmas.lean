/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Lemmas relating different ways to compose measures and kernels

This file contains lemmas about the composition of measures and kernels that do not fit in any of
the other files in this directory, because they involve several types of compositions/products.

-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} {ν : Measure β} {κ : Kernel α β}

namespace ProbabilityTheory.Kernel

/-- The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (κ ×ₖ ζ)` is the product of the
compositions `(ξ ∘ₖ (κ ×ₖ ζ)) ×ₖ (η' ∘ₖ (κ ×ₖ ζ))`, if `ζ` is deterministic (of the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkLeft β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkLeft β` was a more general
kernel since `κ ×ₖ Kernel.deterministic f hf` would be deterministic and commute with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy. -/
/-
**ProbabilityTheory.Kernel.prod_prodMkLeft_comp_prod_deterministic** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：prod_prodMkLeft_comp_prod_deterministic {β' ε : Type*} {mβ' : MeasurableSp
ace β'} {mε : MeasurableSpace ε} (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kerne
l ε β') [IsSFiniteKernel η] (ξ : Kernel (β × ε) δ) [IsSFiniteKernel ξ] {f : γ ->
 ε} (hf : Measurable f) : (ξ ×ₖ η.prodMkLeft β) ∘ₖ (κ ×ₖ deterministic f hf) = (
ξ ∘ₖ (κ ×ₖ deterministic f hf)) ×ₖ (η ∘ₖ deterministic f hf)
参数：κ : Kernel γ β；η : Kernel ε β'；ξ : Kernel (β × ε) δ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod_apply'`：prod_apply' (κ : Kernel α β) [IsSF
initeKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {s : Set (β × γ)} (h
s : MeasurableSet s) : (κ …
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_prod_deterministic`：lintegral_prod_de
terministic {f : α -> γ} (hf : Measurable f) (κ : Kernel α β) [IsSFiniteKernel κ
] (a : α) {g : (β × γ) -> Real>=0∞} (hg : M…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft_apply`：prodMkLeft_apply (κ : Kernel 
α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd
· 使用定理 `ProbabilityTheory.Kernel.comp_deterministic_eq_comap`：comp_deterministic
_eq_comap (κ : Kernel α β) (hg : Measurable g) : κ ∘ₖ deterministic g hg = comap
 κ g hg
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)

--- 原说明 ---
The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (κ ×ₖ ζ)` is the product of
 the
compositions `(ξ ∘ₖ (κ ×ₖ ζ)) ×ₖ (η' ∘ₖ (κ ×ₖ ζ))`, if `ζ` is deterministic (of 
the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkLeft β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkLeft β` was a more
 general
kernel since `κ ×ₖ Kernel.deterministic f hf` would be deterministic and commute
 with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy.
-/
lemma prod_prodMkLeft_comp_prod_deterministic {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (β × ε) δ) [IsSFiniteKernel ξ] {f : γ → ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkLeft β) ∘ₖ (κ ×ₖ deterministic f hf)
      = (ξ ∘ₖ (κ ×ₖ deterministic f hf)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs, comp_apply' _ _ _ hs, lintegral_prod_deterministic,
    lintegral_comp, lintegral_prod_deterministic]
  · congr with b
    rw [prod_apply' _ _ _ hs, prodMkLeft_apply, comp_deterministic_eq_comap, comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

/-- The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (ζ ×ₖ κ)` is the product of the
compositions, `(ξ ∘ₖ (ζ ×ₖ κ)) ×ₖ (η' ∘ₖ (ζ ×ₖ κ))`, if `ζ` is deterministic (of the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkRight β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkRight β` was a more general
kernel since `Kernel.deterministic f hf ×ₖ κ` would be deterministic and commute with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy. -/
/-
**ProbabilityTheory.Kernel.prod_prodMkRight_comp_deterministic_prod** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：prod_prodMkRight_comp_deterministic_prod {β' ε : Type*} {mβ' : MeasurableS
pace β'} {mε : MeasurableSpace ε} (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kern
el ε β') [IsSFiniteKernel η] (ξ : Kernel (ε × β) δ) [IsSFiniteKernel ξ] {f : γ -
> ε} (hf : Measurable f) : (ξ ×ₖ η.prodMkRight β) ∘ₖ (deterministic f hf ×ₖ κ) =
 (ξ ∘ₖ (deterministic f hf ×ₖ κ)) ×ₖ (η ∘ₖ deterministic f hf)
参数：κ : Kernel γ β；η : Kernel ε β'；ξ : Kernel (ε × β) δ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.prod_apply'`：prod_apply' (κ : Kernel α β) [IsSF
initeKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) {s : Set (β × γ)} (h
s : MeasurableSet s) : (κ …
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic_prod`：lintegral_determi
nistic_prod {f : α -> β} (hf : Measurable f) (κ : Kernel α γ) [IsSFiniteKernel κ
] (a : α) {g : (β × γ) -> Real>=0∞} (hg : M…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkRight`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}  
 {mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.prodMkRight_apply`：prodMkRight_apply (κ : Kerne
l α β) (ca : α × γ) : prodMkRight γ κ ca = κ ca.fst
· 使用定理 `ProbabilityTheory.Kernel.comp_deterministic_eq_comap`：comp_deterministic
_eq_comap (κ : Kernel α β) (hg : Measurable g) : κ ∘ₖ deterministic g hg = comap
 κ g hg
· 使用定理 `ProbabilityTheory.Kernel.comap_apply`：comap_apply (κ : Kernel α β) (hg :
 Measurable g) (c : γ) : comap κ g hg c = κ (g c)

--- 原说明 ---
The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (ζ ×ₖ κ)` is the product of
 the
compositions, `(ξ ∘ₖ (ζ ×ₖ κ)) ×ₖ (η' ∘ₖ (ζ ×ₖ κ))`, if `ζ` is deterministic (of
 the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkRight β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkRight β` was a mor
e general
kernel since `Kernel.deterministic f hf ×ₖ κ` would be deterministic and commute
 with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy.
-/
lemma prod_prodMkRight_comp_deterministic_prod {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (ε × β) δ) [IsSFiniteKernel ξ] {f : γ → ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkRight β) ∘ₖ (deterministic f hf ×ₖ κ)
      = (ξ ∘ₖ (deterministic f hf ×ₖ κ)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs, comp_apply' _ _ _ hs, lintegral_deterministic_prod,
    lintegral_comp, lintegral_deterministic_prod]
  · congr with b
    rw [prod_apply' _ _ _ hs, prodMkRight_apply, comp_deterministic_eq_comap, comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

/-
**MeasureTheory.Measure.compProd_eq_parallelComp_comp_copy_comp** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：compProd_eq_parallelComp_comp_copy_comp [SFinite μ] : μ otimesₘ κ = (Kerne
l.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_copy`：parallelComp_comp_copy 
(κ : Kernel α β) (η : Kernel α γ) : (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_right`：bind_zero_right (m : Measure α) :
 bind m (0 : α -> Measure β) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_eq_parallelComp_comp_copy_comp [SFinite μ] :
    μ ⊗ₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rw [compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy, Measure.comp_assoc]
/-
**MeasureTheory.Measure.prod_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：prod_comp_right [SFinite ν] {κ : Kernel β γ} [IsSFiniteKernel κ] : μ.prod 
(κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
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
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
-/
lemma prod_comp_right [SFinite ν] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Measure.bind_apply (measurable_prodMk_left hs) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply, Kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prodMk_left hs
/-
**MeasureTheory.Measure.prod_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：prod_comp_left [SFinite μ] [SFinite ν] {κ : Kernel α γ} [IsSFiniteKernel κ
] : (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.Measure.instSFiniteBindCoeKernelOfIsSFiniteKernel`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : 
MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `ProbabilityTheory.Kernel.swap.eq_1`：∀ (α : Type u_4) (β : Type u_5) [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β],   ProbabilityTheory.Kernel.
swap α β = ProbabilityTh…
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.swap_parallelComp`：swap_parallelComp : swap Y T
 ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.prod_comp_right`：prod_comp_right [SFinite ν] {κ : 
Kernel β γ} [IsSFiniteKernel κ] : μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod 
ν)
-/
lemma prod_comp_left [SFinite μ] [SFinite ν] {κ : Kernel α γ} [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap, Measure.deterministic_comp_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap, Measure.deterministic_comp_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm
/-
**MeasureTheory.Measure.parallelComp_comp_compProd** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：parallelComp_comp_compProd [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFinite
Kernel η] : (Kernel.id ∥ₖ η) ∘ₘ (μ otimesₘ κ) = μ otimesₘ (η ∘ₖ κ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_prod`：parallelComp_comp_prod 
[IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η] {κ' : Kernel X Y'} [IsS
FiniteKernel κ'] {η' : Kernel Y' Z'} …
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
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.compProd_of_not_sfinite`：compProd_of_not_sfinite (
μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) : μ otimesₘ κ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.bind_zero_left`：bind_zero_left (f : α -> Measure β
) : bind (0 : Measure α) f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma parallelComp_comp_compProd [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) = μ ⊗ₘ (η ∘ₖ κ) := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod, Measure.comp_assoc,
    Kernel.parallelComp_comp_prod, Kernel.id_comp]
/-
**MeasureTheory.Measure.compProd_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β -> γ} (hf : Measurable
 f) : μ otimesₘ (κ.map f) = (μ otimesₘ κ).map (Prod.map id f)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_prod`：parallelComp_comp_prod 
[IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η] {κ' : Kernel X Y'} [IsS
FiniteKernel κ'] {η' : Kernel Y' Z'} …
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
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.deterministic_comp_eq_map`：deterministic_comp_e
q_map (hf : Measurable f) (κ : Kernel α β) : deterministic f hf ∘ₖ κ = map κ f
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用引理 `ProbabilityTheory.Kernel.deterministic_parallelComp_deterministic`：deter
ministic_parallelComp_deterministic {f : α -> γ} {g : β -> δ} (hf : Measurable f
) (hg : Measurable g) : (deterministic f hf) ∥ₖ (determ…
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
-/
lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) :
    μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f) := by
  calc μ ⊗ₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc, Kernel.parallelComp_comp_prod, compProd_eq_comp_prod,
      Kernel.id_comp, Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ ⊗ₘ κ).map (Prod.map id f) := by
    rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic, deterministic_comp_eq_map]

end MeasureTheory.Measure

