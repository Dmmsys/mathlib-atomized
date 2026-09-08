/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Lemmas relating different ways to compose kernels

This file contains lemmas about the composition of kernels that involve several types of
compositions/products.

## Main statements

* `comp_eq_snd_compProd`: `η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η)`
* `parallelComp_comp_parallelComp`: `(η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ')`

-/

public section


open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {X Y Z T : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z} {mT : MeasurableSpace T}
  {μ : Measure X} {ν : Measure Y} {κ : Kernel X Y} {η : Kernel Z T}

namespace ProbabilityTheory.Kernel

/-
**ProbabilityTheory.Kernel.comp_eq_snd_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：comp_eq_snd_compProd (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
 [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ otimesₖ prodMkLeft X η)
参数：η : Kernel Y Z；κ : Kernel X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `ProbabilityTheory.Kernel.snd_apply'`：snd_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set γ} (hs : MeasurableSet s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_eq_snd_compProd (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]
/-
**ProbabilityTheory.Kernel.snd_compProd_prodMkLeft** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {mX : MeasurableSpace X} {m
Y : MeasurableSpace Y}   {mZ : MeasurableSpace Z} (κ : ProbabilityTheory.Kernel 
X Y) (η : ProbabilityTheory.Kernel Y Z)   [ProbabilityTheory.IsSFiniteKernel κ] 
[ProbabilityTheory.IsSFiniteKernel η],   (κ.compProd (ProbabilityTheory.Kernel.p
rodMkLeft X η)).snd = η.comp κ
参数：κ : ProbabilityTheory.Kernel X Y；η : ProbabilityTheory.Kernel Y Z；κ.compProd 
(ProbabilityTheory.Kernel.prodMkLeft X η)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.comp_eq_snd_compProd`：comp_eq_snd_compProd (η :
 Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y) [IsSFiniteKernel κ] : η ∘ₖ κ =
 snd (κ otimesₖ prodMkLeft X η)
-/
@[simp] lemma snd_compProd_prodMkLeft
    (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ ⊗ₖ prodMkLeft X η) = η ∘ₖ κ := (comp_eq_snd_compProd η κ).symm
/-
**ProbabilityTheory.Kernel.compProd_prodMkLeft_eq_comp** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_prodMkLeft_eq_comp (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kern
el Y Z) [IsSFiniteKernel η] : κ otimesₖ (prodMkLeft X η) = (Kernel.id ×ₖ η) ∘ₖ κ
参数：κ : Kernel X Y；η : Kernel Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_eq_snd_compProd`：comp_eq_snd_compProd (η :
 Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y) [IsSFiniteKernel κ] : η ∘ₖ κ =
 snd (κ otimesₖ prodMkLeft X η)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prod`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : 
MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.snd_apply'`：snd_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set γ} (hs : MeasurableSet s) : snd κ a s = κ a (Prod.snd ⁻¹' s)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.id_apply`：id_apply (a : α) : Kernel.id a = Meas
ure.dirac a
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma compProd_prodMkLeft_eq_comp
    (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η] :
    κ ⊗ₖ (prodMkLeft X η) = (Kernel.id ×ₖ η) ∘ₖ κ := by
  ext a s hs
  rw [comp_eq_snd_compProd, compProd_apply hs, snd_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs
/-
**ProbabilityTheory.Kernel.swap_parallelComp** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：swap_parallelComp : swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply`：parallelComp_apply (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) : 
(κ ∥ₖ η) x = (κ x.1).prod (η x.2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.swap_apply`：swap_apply (ab : α × β) : swap α β 
ab = Measure.dirac ab.swap
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply'`：parallelComp_apply' [IsSFi
niteKernel κ] [IsSFiniteKernel η] {s : Set (β × δ)} (hs : MeasurableSet s) : (κ 
∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b…
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 34 条，此处仅展示前 30 条）
-/
lemma swap_parallelComp : swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

section ParallelComp

variable {X' Y' Z' : Type*} {mX' : MeasurableSpace X'} {mY' : MeasurableSpace Y'}
  {mZ' : MeasurableSpace Z'}

/-
**ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel 
η] {ξ : Kernel Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ
 ∘ₖ η)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
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
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_apply'`：parallelComp_apply' [IsSFi
niteKernel κ] [IsSFiniteKernel η] {s : Set (β × δ)} (hs : MeasurableSet s) : (κ 
∥ₖ η) x s = ∫⁻ b, η x.2 (Prod.mk b…
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
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.comp_zero`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma parallelComp_id_left_comp_parallelComp
    {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs, parallelComp_apply,
    MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply, Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs, Kernel.id_apply,
    lintegral_dirac' _ (measurable_measure_prodMk_left hs)]
/-
**ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel
 η] {ξ : Kernel Z T} [IsSFiniteKernel ξ] : (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ 
η) ∥ₖ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.swap_parallelComp`：swap_parallelComp : swap Y T
 ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp`：paralle
lComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kerne
l Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.swap_swap`：swap_swap : (swap α β) ∘ₖ (swap β α)
 = Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
-/
lemma parallelComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η]
    {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]
/-
**ProbabilityTheory.Kernel.parallelComp_comp_parallelComp** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：parallelComp_comp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFi
niteKernel η] {κ' : Kernel X' Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSF
initeKernel η'] : (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp`：paralle
lComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kerne
l Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp`：parall
elComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Ker
nel Z T} [IsSFiniteKernel ξ] : (ξ ∥ₖ Kernel.id) ∘ₖ (η …
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
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
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
-/
lemma parallelComp_comp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X' Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_id_left_comp_parallelComp, ← parallelComp_id_right_comp_parallelComp,
    ← comp_assoc, parallelComp_id_left_comp_parallelComp, comp_id]
/-
**ProbabilityTheory.Kernel.parallelComp_comp_prod** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：parallelComp_comp_prod [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKern
el η] {κ' : Kernel X Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKern
el η'] : (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_copy`：parallelComp_comp_copy 
(κ : Kernel α β) (η : Kernel α γ) : (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η
· 使用定理 `ProbabilityTheory.Kernel.comp_assoc`：comp_assoc {δ : Type*} {mδ : Measur
ableSpace δ} (ξ : Kernel γ δ) (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = 
ξ ∘ₖ (η ∘ₖ κ)
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_parallelComp`：parallelComp_co
mp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η] {κ' : K
ernel X' Y'} [IsSFiniteKernel κ'] {η' : Kerne…
-/
lemma parallelComp_comp_prod [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_comp_copy, ← comp_assoc, parallelComp_comp_parallelComp,
    ← parallelComp_comp_copy]
/-
**ProbabilityTheory.Kernel.parallelComp_comm** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：parallelComp_comm : (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id
) ∘ₖ (Kernel.id ∥ₖ κ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp`：paralle
lComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kerne
l Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥…
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
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_right_comp_parallelComp`：parall
elComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Ker
nel Z T} [IsSFiniteKernel ξ] : (ξ ∥ₖ Kernel.id) ∘ₖ (η …
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.comp_zero`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
-/
lemma parallelComp_comm :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  rw [parallelComp_id_left_comp_parallelComp, parallelComp_id_right_comp_parallelComp,
    comp_id, comp_id]
/-
**ProbabilityTheory.Kernel.id_parallelComp_comp_parallelComp_id** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：id_parallelComp_comp_parallelComp_id [IsSFiniteKernel κ] : Kernel.id ∥ₖ κ 
∘ₖ (η ∥ₖ Kernel.id) = η ∥ₖ κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_id_left_comp_parallelComp`：paralle
lComp_id_left_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kerne
l Z T} [IsSFiniteKernel ξ] : (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥…
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
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…
-/
lemma id_parallelComp_comp_parallelComp_id [IsSFiniteKernel κ] :
    Kernel.id ∥ₖ κ ∘ₖ (η ∥ₖ Kernel.id) = η ∥ₖ κ := by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ

end ParallelComp

end ProbabilityTheory.Kernel

