/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Composition-product of kernels

We define the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : Kernel α β` and
`η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`

## Main statements

* `lintegral_compProd`: Lebesgue integral of a function against a composition-product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition-product.

## Notation

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`.
-/

variable {s : Set (β × γ)}

/-- Composition-Product of kernels. For s-finite kernels, it satisfies
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.Kernel.lintegral_compProd`).
If either of the kernels is not s-finite, `compProd` is given the junk value 0. -/
noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ) :=
  swap γ β ∘ₖ (η ∥ₖ Kernel.id)
    ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
    ∘ₖ (Kernel.id ∥ₖ copy β) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₖ " => ProbabilityTheory.Kernel.compProd

@[simp]
/-
**ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) 
γ) (h : ¬ IsSFiniteKernel κ) : κ otimesₖ η = 0
参数：κ : Kernel α β；η : Kernel (α × β) γ；h : ¬ IsSFiniteKernel κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_right`：para
llelComp_of_not_isSFiniteKernel_right (κ : Kernel α β) (h : ¬ IsSFiniteKernel η)
 : κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.comp_zero`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compProd_of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel κ) :
    κ ⊗ₖ η = 0 := by
  simp [compProd, h]

@[simp]
/-
**ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β)
 γ) (h : ¬ IsSFiniteKernel η) : κ otimesₖ η = 0
参数：κ : Kernel α β；η : Kernel (α × β) γ；h : ¬ IsSFiniteKernel η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_of_not_isSFiniteKernel_left`：paral
lelComp_of_not_isSFiniteKernel_left (η : Kernel γ δ) (h : ¬ IsSFiniteKernel κ) :
 κ ∥ₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.comp_zero`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.zero_comp`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableS
pace γ} (κ : Probability…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compProd_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel η) :
    κ ⊗ₖ η = 0 := by
  simp [compProd, h]

set_option backward.isDefEq.respectTransparency false in
/-
**ProbabilityTheory.Kernel.compProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：compProd_apply (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ]
 (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) : (κ otimesₖ η) a s = ∫⁻ b, 
η (a, b) (Prod.mk b ⁻¹' s) ∂κ a
参数：hs : MeasurableSet s；κ : Kernel α β；η : Kernel (α × β) γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用引理 `ProbabilityTheory.Kernel.copy_apply`：copy_apply (a : α) : copy α a = Mea
sure.dirac (a, a)
· 使用定理 `MeasureTheory.Measure.dirac_bind`：dirac_bind {f : α -> Measure β} (hf : 
Measurable f) (a : α) : bind (dirac a) f = f a
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
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
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Measurable.lintegral_prod_right`：Measurable.lintegral_prod_right [SFinit
e ν] {f : α -> β -> Real>=0∞} (hf : Measurable (uncurry f)) : Measurable fun x =
> ∫⁻ y, f x y ∂ν
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.isFiniteKernel_of_isFiniteKernel_snd`：∀ {α : Ty
pe u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} {κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.snd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
· 使用定理 `MeasureTheory.Measure.dirac_prod_dirac`：dirac_prod_dirac {x : α} {y : β}
 : (dirac x).prod (dirac y) = dirac (x, y)
· 使用定理 `ProbabilityTheory.Kernel.deterministic_apply`：deterministic_apply {f : α
 -> β} (hf : Measurable f) (a : α) : deterministic f hf a = Measure.dirac (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.prodAssoc_symm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u
_11) (p : α × β × γ), (Equiv.prodAssoc α β γ).symm p = ((p.1, p.2.1), p.2.2)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
（共 42 条，此处仅展示前 30 条）
-/
theorem compProd_apply (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a s = ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a := by
  rw [compProd, comp_apply, copy_apply, Measure.dirac_bind (by fun_prop), comp_apply,
    parallelComp_apply, Kernel.id_apply, Measure.bind_apply hs (by fun_prop),
    lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable, lintegral_dirac']
  swap
  · suffices Measurable fun p : α × β ↦
      (swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β)) p s by fun_prop
    exact Kernel.measurable_coe _ hs
  congr with b
  rw [comp_apply, parallelComp_apply, Kernel.id_apply, copy_apply, Measure.dirac_prod_dirac,
    Measure.dirac_bind (by fun_prop), comp_apply, deterministic_apply (by fun_prop),
    Measure.dirac_bind (by fun_prop), comp_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_symm_apply]
  rw [parallelComp_apply, Kernel.id_apply, Measure.bind_apply hs (by fun_prop),
    lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  classical
  have h_int x : ∫⁻ y, swap γ β (x, y) s ∂Measure.dirac b = (Prod.mk b ⁻¹' s).indicator 1 x := by
    rw [lintegral_dirac']
    · simp [swap_apply' _ hs, Set.indicator_apply]
    · simpa [swap_apply' _ hs, Prod.swap_prod_mk] using!
        measurable_const.indicator (measurable_prodMk_right hs)
  simp_rw [h_int]
  rw [lintegral_indicator_one]
  exact measurable_prodMk_left hs
/-
**ProbabilityTheory.Kernel.le_compProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：le_compProd_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β)
 γ) [IsSFiniteKernel η] (a : α) (s : Set (β × γ)) : ∫⁻ b, η (a, b) {c | (b, c) i
n s} ∂κ a <= (κ otimesₖ η) a s
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；s : Set (β × γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
theorem le_compProd_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (s : Set (β × γ)) :
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤ (κ ⊗ₖ η) a s :=
  calc
    ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a ≤
        ∫⁻ b, η (a, b) {c | (b, c) ∈ toMeasurable ((κ ⊗ₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ ⊗ₖ η) a (toMeasurable ((κ ⊗ₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s

@[simp]
/-
**ProbabilityTheory.Kernel.compProd_apply_univ** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：compProd_apply_univ {κ : Kernel α β} {η : Kernel (α × β) γ} [IsSFiniteKern
el κ] [IsMarkovKernel η] {a : α} : (κ otimesₖ η) a Set.univ = κ a Set.univ
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
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
lemma compProd_apply_univ {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsMarkovKernel η] {a : α} :
    (κ ⊗ₖ η) a Set.univ = κ a Set.univ := by
  rw [compProd_apply MeasurableSet.univ]
  simp
/-
**ProbabilityTheory.Kernel.compProd_apply_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：compProd_apply_prod {κ : Kernel α β} {η : Kernel (α × β) γ} [IsSFiniteKern
el κ] [IsSFiniteKernel η] {a : α} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
 (ht : MeasurableSet t) : (κ otimesₖ η) a (s ×ˢ t) = ∫⁻ b in s, η (a, b) t ∂(κ a
)
参数：α × β；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.mk_preimage_prod_right`：mk_preimage_prod_right (ha : a in s) : Prod.
mk a ⁻¹' s ×ˢ t = t
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mk_preimage_prod_right_eq_empty`：mk_preimage_prod_right_eq_empty (ha
 : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
lemma compProd_apply_prod {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α}
    {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (κ ⊗ₖ η) a (s ×ˢ t) = ∫⁻ b in s, η (a, b) t ∂(κ a) := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with a
  by_cases ha : a ∈ s <;> simp [ha]
/-
**ProbabilityTheory.Kernel.compProd_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：compProd_congr {κ : Kernel α β} {η η' : Kernel (α × β) γ} [IsSFiniteKernel
 η] [IsSFiniteKernel η'] (h : forall a, forallᵐ b ∂(κ a), η (a, b) = η' (a, b)) 
: κ otimesₖ η = κ otimesₖ η'
参数：α × β；h : forall a, forallᵐ b ∂(κ a), η (a, b) = η' (a, b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_congr {κ : Kernel α β} {η η' : Kernel (α × β) γ}
    [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = η' (a, b)) :
    κ ⊗ₖ η = κ ⊗ₖ η' := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext a s hs
  rw [compProd_apply hs, compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]
/-
**ProbabilityTheory.Kernel.compProd_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：compProd_zero_left (κ : Kernel (α × β) γ) : (0 : Kernel α β) otimesₖ κ = 0
参数：κ : Kernel (α × β) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
-/
lemma compProd_zero_left (κ : Kernel (α × β) γ) :
    (0 : Kernel α β) ⊗ₖ κ = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]
/-
**ProbabilityTheory.Kernel.compProd_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：compProd_zero_right (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} 
: κ otimesₖ (0 : Kernel (α × β) γ) = 0
参数：κ : Kernel α β；γ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
-/
lemma compProd_zero_right (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} :
    κ ⊗ₖ (0 : Kernel (α × β) γ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]
/-
**ProbabilityTheory.Kernel.compProd_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：compProd_eq_zero_iff {κ : Kernel α β} {η : Kernel (α × β) γ} [IsSFiniteKer
nel κ] [IsSFiniteKernel η] : κ otimesₖ η = 0 ↔ forall a, forallᵐ b ∂(κ a), η (a,
 b) = 0
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `ProbabilityTheory.Kernel.compProd_apply_prod`：compProd_apply_prod {κ : K
ernel α β} {η : Kernel (α × β) γ} [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α
} {s : Set β} {t : Set γ} (hs : Me…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_right`：compProd_zero_right (κ : K
ernel α β) (γ : Type*) {mγ : MeasurableSpace γ} : κ otimesₖ (0 : Kernel (α × β) 
γ) = 0
· 使用引理 `ProbabilityTheory.Kernel.compProd_congr`：compProd_congr {κ : Kernel α β}
 {η η' : Kernel (α × β) γ} [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : forall 
a, forallᵐ b ∂(κ a), η (a, b)…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
-/
lemma compProd_eq_zero_iff {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ⊗ₖ η = 0 ↔ ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a ↦ (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h
/-
**ProbabilityTheory.Kernel.compProd_preimage_fst** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：compProd_preimage_fst {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β) 
(η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] (x : α) : (κ otime
sₖ η) x (Prod.fst ⁻¹' s) = κ x s
参数：hs : MeasurableSet s；κ : Kernel α β；η : Kernel (α × β) γ；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.lintegral_indicator_const`：lintegral_indicator_const {s : 
Set α} (hs : MeasurableSet s) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) a 
∂μ = c * μ s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma compProd_preimage_fst {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β)
    (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] (x : α) :
    (κ ⊗ₖ η) x (Prod.fst ⁻¹' s) = κ x s := by
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]
/-
**ProbabilityTheory.Kernel.compProd_deterministic_apply** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_deterministic_apply [MeasurableSingletonClass γ] {f : α × β -> γ}
 (hf : Measurable f) {s : Set (β × γ)} (hs : MeasurableSet s) (κ : Kernel α β) [
IsSFiniteKernel κ] (x : α) : (κ otimesₖ deterministic f hf) x s = κ x {b | (b, f
 (x, b)) in s}
参数：hf : Measurable f；β × γ；hs : MeasurableSet s；κ : Kernel α β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma compProd_deterministic_apply [MeasurableSingletonClass γ] {f : α × β → γ} (hf : Measurable f)
    {s : Set (β × γ)} (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ] (x : α) :
    (κ ⊗ₖ deterministic f hf) x s = κ x {b | (b, f (x, b)) ∈ s} := by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) ∈ s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert! add_zero _
  · suffices ∀ b ∈ tᶜ, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this, lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_ofPred_eq] at hb
    simp [hb]
  · suffices ∀ b ∈ t, (if f (x, b) ∈ Prod.mk b ⁻¹' s then (1 : ℝ≥0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this, setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_ofPred_eq] at hb
    simp [hb]

section Ae

/-! ### `ae` filter of the composition-product -/


variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η] {a : α}

/-
**ProbabilityTheory.Kernel.ae_kernel_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：ae_kernel_lt_top (a : α) (h2s : (κ otimesₖ η) a s != ∞) : forallᵐ b ∂κ a, 
η (a, b) (Prod.mk b ⁻¹' s) < ∞
参数：a : α；h2s : (κ otimesₖ η) a s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem ae_kernel_lt_top (a : α) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞ := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  have : ∀ b : β, η (a, b) (Prod.mk b ⁻¹' s) ≤ η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ ⊗ₖ η) a t ≠ ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : ∀ᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    exact ae_lt_top (Kernel.measurable_kernel_prodMk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb
/-
**ProbabilityTheory.Kernel.compProd_null** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：compProd_null (a : α) (hs : MeasurableSet s) : (κ otimesₖ η) a s = 0 ↔ (fu
n b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0
参数：a : α；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [Kernel.compProd_apply hs, lintegral_eq_zero_iff]
  exact Kernel.measurable_kernel_prodMk_left' hs a
/-
**ProbabilityTheory.Kernel.ae_null_of_compProd_null** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：ae_null_of_compProd_null (h : (κ otimesₖ η) a s = 0) : (fun b => η (a, b) 
(Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0
参数：h : (κ otimesₖ η) a s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `ProbabilityTheory.Kernel.compProd_null`：compProd_null (a : α) (hs : Meas
urableSet s) : (κ otimesₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[
κ a] 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem ae_null_of_compProd_null (h : (κ ⊗ₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le⟩
/-
**ProbabilityTheory.Kernel.ae_ae_of_ae_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：ae_ae_of_ae_compProd {p : β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a,
 p bc) : forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p (b, c)
参数：h : forallᵐ bc ∂(κ otimesₖ η) a, p bc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_null_of_compProd_null`：ae_null_of_compProd_n
ull (h : (κ otimesₖ η) a s = 0) : (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 
0
-/
theorem ae_ae_of_ae_compProd {p : β × γ → Prop} (h : ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) :
    ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h
/-
**ProbabilityTheory.Kernel.ae_compProd_of_ae_ae** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：ae_compProd_of_ae_ae {κ : Kernel α β} {η : Kernel (α × β) γ} {p : β × γ ->
 Prop} (hp : MeasurableSet {x | p x}) (h : forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), 
p (b, c)) : forallᵐ bc ∂(κ otimesₖ η) a, p bc
参数：α × β；hp : MeasurableSet {x | p x}；h : forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p
 (b, c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_null`：compProd_null (a : α) (hs : Meas
urableSet s) : (κ otimesₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[
κ a] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
-/
lemma ae_compProd_of_ae_ae {κ : Kernel α β} {η : Kernel (α × β) γ}
    {p : β × γ → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c)) :
    ∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [compProd_of_not_isSFiniteKernel_right _ _ hη]
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl
/-
**ProbabilityTheory.Kernel.ae_compProd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：ae_compProd_iff {p : β × γ -> Prop} (hp : MeasurableSet {x | p x}) : (fora
llᵐ bc ∂(κ otimesₖ η) a, p bc) ↔ forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p (b, c)
参数：hp : MeasurableSet {x | p x}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_compProd`：ae_ae_of_ae_compProd {p :
 β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a, p bc) : forallᵐ b ∂κ a, forall
ᵐ c ∂η (a, b), p (b, c)
· 使用引理 `ProbabilityTheory.Kernel.ae_compProd_of_ae_ae`：ae_compProd_of_ae_ae {κ :
 Kernel α β} {η : Kernel (α × β) γ} {p : β × γ -> Prop} (hp : MeasurableSet {x |
 p x}) (h : forallᵐ b ∂κ a, forallᵐ…
-/
lemma ae_compProd_iff {p : β × γ → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ bc ∂(κ ⊗ₖ η) a, p bc) ↔ ∀ᵐ b ∂κ a, ∀ᵐ c ∂η (a, b), p (b, c) :=
  ⟨fun h ↦ ae_ae_of_ae_compProd h, fun h ↦ ae_compProd_of_ae_ae hp h⟩

end Ae

section Restrict

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

/-
**ProbabilityTheory.Kernel.compProd_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : Mea
surableSet t) : Kernel.restrict κ hs otimesₖ Kernel.restrict η ht = Kernel.restr
ict (κ otimesₖ η) (hs.prod ht)
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.restrict`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {s : Set β}   (κ : 
ProbabilityTheory.Kernel α β) [Probabil…
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply'`：restrict_apply' (κ : Kernel α 
β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) : κ.restrict hs a t = (
κ a) (t inter s)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
-/
theorem compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Kernel.restrict κ hs ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (hs.prod ht) := by
  ext a u hu
  rw [compProd_apply hu, restrict_apply' _ _ _ hu, compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) ∈ u ∧ b ∈ s ∧ c ∈ t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) ∈ u} ∩ t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_ofPred]
    · simp only [h, false_and, and_false, Set.ofPred_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]
/-
**ProbabilityTheory.Kernel.compProd_restrict_left** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：compProd_restrict_left {s : Set β} (hs : MeasurableSet s) : Kernel.restric
t κ hs otimesₖ η = Kernel.restrict (κ otimesₖ η) (hs.prod MeasurableSet.univ)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.compProd_restrict`：compProd_restrict {s : Set β
} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) : Kernel.restrict κ 
hs otimesₖ Kernel.restrict η ht …
· 使用定理 `ProbabilityTheory.Kernel.restrict_univ`：restrict_univ : κ.restrict Measu
rableSet.univ = κ
-/
theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    Kernel.restrict κ hs ⊗ₖ η = Kernel.restrict (κ ⊗ₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm
/-
**ProbabilityTheory.Kernel.compProd_restrict_right** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) : κ otimesₖ Ker
nel.restrict η ht = Kernel.restrict (κ otimesₖ η) (MeasurableSet.univ.prod ht)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.compProd_restrict`：compProd_restrict {s : Set β
} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) : Kernel.restrict κ 
hs otimesₖ Kernel.restrict η ht …
· 使用定理 `ProbabilityTheory.Kernel.restrict_univ`：restrict_univ : κ.restrict Measu
rableSet.univ = κ
-/
theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ ⊗ₖ Kernel.restrict η ht = Kernel.restrict (κ ⊗ₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

end Restrict

section Lintegral

/-! ### Lebesgue integral -/


/-- Lebesgue integral against the composition-product of two kernels. -/
/-
**ProbabilityTheory.Kernel.lintegral_compProd'** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：lintegral_compProd' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × 
β) γ) [IsSFiniteKernel η] (a : α) {f : β -> γ -> Real>=0∞} (hf : Measurable (Fun
ction.uncurry f)) : ∫⁻ bc, f bc.1 bc.2 ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (
a, b) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable (Function.uncurry f
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.SimpleFunc.iSup_eapprox_apply`：iSup_eapprox_apply (hf : Me
asurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Measurable.lintegral_kernel_prod_right''`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measu
rableSpace γ} {η : Probability…
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `MeasureTheory.lintegral_indicator_const`：lintegral_indicator_const {s : 
Set α} (hs : MeasurableSet s) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) a 
∂μ = c * μ s
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.lintegral_indicator_const_comp`：lintegral_indicator_const_
comp {f : α -> β} {s : Set β} (hf : Measurable f) (hs : MeasurableSet s) (c : Re
al>=0∞) : ∫⁻ a, s.indicator (fun _…
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ

--- 原说明 ---
Lebesgue integral against the composition-product of two kernels.
-/
theorem lintegral_compProd' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    ∫⁻ bc, f bc.1 bc.2 ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (a, b) ∂κ a := by
  let F : ℕ → SimpleFunc (β × γ) ℝ≥0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : ∀ a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : ∀ b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => h_mono hij _
  simp_rw [this]
  have h_some_meas_integral :
    ∀ f' : SimpleFunc (β × γ) ℝ≥0∞, Measurable fun b => ∫⁻ c, f' (b, c) ∂η (a, b) := by
    intro f'
    have :
      (fun b => ∫⁻ c, f' (b, c) ∂η (a, b)) =
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) := by
      ext1 ab; rfl
    rw [this]
    fun_prop
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c s hs
    simp +unfoldPartialApp only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply hs, ← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prodMk_left ((measurable_fst.snd.prodMk measurable_snd) hs)).comp
        measurable_prodMk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prodMk_left hs]
  · intro f f' _ hf_eq hf'_eq
    simp_rw [SimpleFunc.coe_add, Pi.add_apply]
    change
      ∫⁻ x, (f : β × γ → ℝ≥0∞) x + f' x ∂(κ ⊗ₖ η) a =
        ∫⁻ b, ∫⁻ c : γ, f (b, c) + f' (b, c) ∂η (a, b) ∂κ a
    rw [lintegral_add_left (SimpleFunc.measurable _), hf_eq, hf'_eq, ← lintegral_add_left]
    swap
    · exact h_some_meas_integral f
    congr with b
    rw [lintegral_add_left]
    exact (SimpleFunc.measurable _).comp measurable_prodMk_left

/-- Lebesgue integral against the composition-product of two kernels. -/
/-
**ProbabilityTheory.Kernel.lintegral_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β
) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) : ∫
⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd'`：lintegral_compProd' (κ : K
ernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α
) {f : β -> γ -> Real>=0∞} (hf : M…
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lebesgue integral against the composition-product of two kernels.
-/
theorem lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ ⊗ₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf

/-- Lebesgue integral against the composition-product of two kernels. -/
/-
**ProbabilityTheory.Kernel.lintegral_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β
) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) : ∫
⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd'`：lintegral_compProd' (κ : K
ernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α
) {f : β -> γ -> Real>=0∞} (hf : M…
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lebesgue integral against the composition-product of two kernels.
-/
theorem lintegral_compProd₀ (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : AEMeasurable f ((κ ⊗ₖ η) a)) :
    ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  have A : ∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ z, hf.mk f z ∂(κ ⊗ₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A, B, lintegral_compProd]
  exact hf.measurable_mk
/-
**ProbabilityTheory.Kernel.setLIntegral_compProd** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：setLIntegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α 
× β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) 
{s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) : ∫⁻ z in 
s ×ˢ t, f z ∂(κ otimesₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable f；hs : MeasurableSe
t s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.compProd_restrict`：compProd_restrict {s : Set β
} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) : Kernel.restrict κ 
hs otimesₖ Kernel.restrict η ht …
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.restrict`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {s : Set β}   (κ : 
ProbabilityTheory.Kernel α β) [Probabil…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLIntegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [← Kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, Kernel.restrict_apply]
/-
**ProbabilityTheory.Kernel.setLIntegral_compProd_univ_right** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：setLIntegral_compProd_univ_right (κ : Kernel α β) [IsSFiniteKernel κ] (η :
 Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Mea
surable f) {s : Set β} (hs : MeasurableSet s) : ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ o
timesₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable f；hs : MeasurableSe
t s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.setLIntegral_compProd`：setLIntegral_compProd (κ
 : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a
 : α) {f : β × γ -> Real>=0∞} (hf : …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLIntegral_compProd_univ_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ ⊗ₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]
/-
**ProbabilityTheory.Kernel.setLIntegral_compProd_univ_left** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：setLIntegral_compProd_univ_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : 
Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Meas
urable f) {t : Set γ} (ht : MeasurableSet t) : ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ot
imesₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hf : Measurable f；ht : MeasurableSe
t t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.setLIntegral_compProd`：setLIntegral_compProd (κ
 : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a
 : α) {f : β × γ -> Real>=0∞} (hf : …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLIntegral_compProd_univ_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ → ℝ≥0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

end Lintegral

/-
**ProbabilityTheory.Kernel.compProd_eq_sum_compProd_left** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_eq_sum_compProd_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Ke
rnel (α × β) γ) : κ otimesₖ η = Kernel.sum fun n => seq κ n otimesₖ η
参数：κ : Kernel α β；η : Kernel (α × β) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_left`：comp_sum_left {ι : Type*} [Count
able ι] (κ : Kernel α β) (η : ι -> Kernel β γ) : (Kernel.sum η) ∘ₖ κ = Kernel.su
m (fun i => (η i) ∘ₖ κ)
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_right`：comp_sum_right {ι : Type*} [Cou
ntable ι] (κ : ι -> Kernel α β) (η : Kernel β γ) : η ∘ₖ Kernel.sum κ = Kernel.su
m fun i => η ∘ₖ (κ i)
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_sum_right`：parallelComp_sum_right 
{ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι -> Kernel γ δ) [forall i, IsSF
initeKernel (η i)] : κ ∥ₖ Kernel.sum …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
-/
theorem compProd_eq_sum_compProd_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) :
    κ ⊗ₖ η = Kernel.sum fun n ↦ seq κ n ⊗ₖ η := by
  simp_rw [compProd_def]
  rw [← comp_sum_left, ← comp_sum_right, ← parallelComp_sum_right, kernel_sum_seq]
/-
**ProbabilityTheory.Kernel.compProd_eq_sum_compProd_right** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：compProd_eq_sum_compProd_right (κ : Kernel α β) (η : Kernel (α × β) γ) [Is
SFiniteKernel η] : κ otimesₖ η = Kernel.sum fun n => κ otimesₖ seq η n
参数：κ : Kernel α β；η : Kernel (α × β) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_left`：comp_sum_left {ι : Type*} [Count
able ι] (κ : Kernel α β) (η : ι -> Kernel β γ) : (Kernel.sum η) ∘ₖ κ = Kernel.su
m (fun i => (η i) ∘ₖ κ)
· 使用引理 `ProbabilityTheory.Kernel.comp_sum_right`：comp_sum_right {ι : Type*} [Cou
ntable ι] (κ : ι -> Kernel α β) (η : Kernel β γ) : η ∘ₖ Kernel.sum κ = Kernel.su
m fun i => η ∘ₖ (κ i)
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_sum_left`：parallelComp_sum_left {ι
 : Type*} [Countable ι] (κ : ι -> Kernel α β) [forall i, IsSFiniteKernel (κ i)] 
(η : Kernel γ δ) : Kernel.sum κ ∥ₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.kernel_sum_seq`：kernel_sum_seq (κ : Kernel α β)
 [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ
-/
theorem compProd_eq_sum_compProd_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n => κ ⊗ₖ seq η n := by
  simp_rw [compProd_def]
  rw [← comp_sum_left, ← comp_sum_left, ← comp_sum_left, ← comp_sum_left, ← comp_sum_right,
    ← parallelComp_sum_left, kernel_sum_seq]
/-
**ProbabilityTheory.Kernel.compProd_eq_sum_compProd** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：compProd_eq_sum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel 
(α × β) γ) [IsSFiniteKernel η] : κ otimesₖ η = Kernel.sum fun n => Kernel.sum fu
n m => seq κ n otimesₖ seq η m
参数：κ : Kernel α β；η : Kernel (α × β) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compProd_eq_sum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ ⊗ₖ η = Kernel.sum fun n ↦ Kernel.sum fun m ↦ seq κ n ⊗ₖ seq η m := by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]
/-
**ProbabilityTheory.Kernel.compProd_eq_tsum_compProd** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：compProd_eq_tsum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel
 (α × β) γ) [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) : (κ otimesₖ η) a
 s = ∑' (n : Nat) (m : Nat), (seq κ n otimesₖ seq η m) a s
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_eq_sum_compProd`：compProd_eq_sum_compP
rod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel
 η] : κ otimesₖ η = Kernel.sum fun n =>…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.sum_apply'`：sum_apply' [Countable ι] (κ : ι -> 
Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) : Kernel.sum κ a s = ∑' n
, κ n a s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compProd_eq_tsum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ ⊗ₖ η) a s = ∑' (n : ℕ) (m : ℕ), (seq κ n ⊗ₖ seq η m) a s := by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]
/-
**ProbabilityTheory.Kernel.IsMarkovKernel.compProd** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.IsMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsMarkovKernel κ]   (η : ProbabilityTheory.Kernel (α × β
) γ) [ProbabilityTheory.IsMarkovKernel η],   ProbabilityTheory.IsMarkovKernel (κ
.compProd η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel (α × β) γ；κ.com
pProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsMarkovKernel.compProd (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η) where
  isProbabilityMeasure a := ⟨by simp [compProd_apply]⟩
/-
**ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.compProd** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsZeroOrMarkovKernel κ]   (η : ProbabilityTheory.Kernel 
(α × β) γ) [ProbabilityTheory.IsZeroOrMarkovKernel η],   ProbabilityTheory.IsZer
oOrMarkovKernel (κ.compProd η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel (α × β) γ；κ.com
pProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsZeroOrMarkovKernel.comp`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroOrMarkovKernelProdParallelComp`：∀ {α 
: Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α
} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdSwap`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityThe
ory.IsMarkovKernel (ProbabilityTheory.Ker…
-/
instance IsZeroOrMarkovKernel.compProd (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel (α × β) γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance
/-
**ProbabilityTheory.Kernel.compProd_apply_univ_le** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：compProd_apply_univ_le (κ : Kernel α β) (η : Kernel (α × β) γ) [IsFiniteKe
rnel η] (a : α) : (κ otimesₖ η) a Set.univ <= κ a Set.univ * η.bound
参数：κ : Kernel α β；η : Kernel (α × β) γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measure_le_bound`：measure_le_bound (κ : Kernel 
α β) (a : α) (s : Set β) : κ a s <= κ.bound
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem compProd_apply_univ_le (κ : Kernel α β) (η : Kernel (α × β) γ) [IsFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a Set.univ ≤ κ a Set.univ * η.bound := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _
/-
**ProbabilityTheory.Kernel.IsFiniteKernel.compProd** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.IsFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) [ProbabilityTheory.IsFiniteKernel κ]   (η : ProbabilityTheory.Kernel (α × β
) γ) [ProbabilityTheory.IsFiniteKernel η],   ProbabilityTheory.IsFiniteKernel (κ
.compProd η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel (α × β) γ；κ.com
pProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.comp`：∀ {α : Type u_1} {β : Type
 u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : M
easurableSpace γ} (η : Probability…
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
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdSwap`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityThe
ory.IsMarkovKernel (ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelProdParallelComp`：∀ {α : Type
 u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α} {mβ 
: MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
-/
instance IsFiniteKernel.compProd (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance
/-
**ProbabilityTheory.Kernel.IsSFiniteKernel.compProd** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel.IsSFiniteKernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel 
α β) (η : ProbabilityTheory.Kernel (α × β) γ),   ProbabilityTheory.IsSFiniteKern
el (κ.compProd η)
参数：κ : ProbabilityTheory.Kernel α β；η : ProbabilityTheory.Kernel (α × β) γ；κ.com
pProd η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_def`：∀ {α : Type u_4} {β : Type u_5} {
γ : Type u_6} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measurab
leSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
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
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdSwap`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   ProbabilityThe
ory.IsMarkovKernel (ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelProdParallelComp`：∀ {α : Typ
e u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {mα : MeasurableSpace α} {mβ
 : MeasurableSpace β}   {mγ : MeasurableSpace γ} {…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelProdCopy`：∀ {α : Type u_1} {m
α : MeasurableSpace α}, ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kern
el.copy α)
-/
instance IsSFiniteKernel.compProd (κ : Kernel α β) (η : Kernel (α × β) γ) :
    IsSFiniteKernel (κ ⊗ₖ η) := by
  rw [compProd_def]
  infer_instance

/-- `Kernel.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc` in two places
because the products of types `α × β × γ` and `(α × β) × γ` are different. -/
/-
**ProbabilityTheory.Kernel.compProd_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：compProd_assoc {δ : Type*} {mδ : MeasurableSpace δ} {κ : Kernel α β} {η : 
Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ} : (κ otimesₖ (η otimesₖ (ξ.comap Me
asurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map MeasurableEquiv.pr
odAssoc.symm = κ otimesₖ η otimesₖ ξ
参数：α × β；α × β × γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.compProd`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ :
 MeasurableSpace γ} {g : γ → α} (κ :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasurableEquiv.self_comp_symm`：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm
 = id
· 使用定理 `ProbabilityTheory.Kernel.comap.congr_simp`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Meas
urableSpace γ} (κ κ_1 : Probabi…
· 使用引理 `ProbabilityTheory.Kernel.comap_id`：comap_id (κ : Kernel α β) : comap κ i
d measurable_id = κ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `ProbabilityTheory.Kernel.compProd_zero_right`：compProd_zero_right (κ : K
ernel α β) (γ : Type*) {mγ : MeasurableSpace γ} : κ otimesₖ (0 : Kernel (α × β) 
γ) = 0
· 使用引理 `ProbabilityTheory.Kernel.map_zero`：map_zero : Kernel.map (0 : Kernel α β
) f = 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`Kernel.compProd` is associative. We have to insert `MeasurableEquiv.prodAssoc` 
in two places
because the products of types `α × β × γ` and `(α × β) × γ` are different.
-/
lemma compProd_assoc {δ : Type*} {mδ : MeasurableSpace δ}
    {κ : Kernel α β} {η : Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ} :
    (κ ⊗ₖ (η ⊗ₖ (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map
        MeasurableEquiv.prodAssoc.symm
      = κ ⊗ₖ η ⊗ₖ ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  by_cases hξ : IsSFiniteKernel ξ
  swap
  · have : ¬ IsSFiniteKernel
        (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)) := by
      refine fun h_sfin ↦ hξ ?_
      have : ξ = (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)).comap
          MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _) := by
        simp [← comap_comp_right]
      rw [this]
      infer_instance
    simp [hξ, this]
  ext a s hs
  rw [compProd_apply hs, map_apply' _ (by fun_prop) _ hs,
    compProd_apply (hs.preimage (by fun_prop)), lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)
/-
**ProbabilityTheory.Kernel.compProd_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：compProd_add_left (μ κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKern
el μ] [IsSFiniteKernel κ] : (μ + κ) otimesₖ η = μ otimesₖ η + κ otimesₖ η
参数：μ κ : Kernel α β；η : Kernel (α × β) γ。
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
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma compProd_add_left (μ κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] :
    (μ + κ) ⊗ₖ η = μ ⊗ₖ η + κ ⊗ₖ η := by
  by_cases hη : IsSFiniteKernel η
  · ext _ _ hs
    simp [compProd_apply hs]
  · simp [hη]
/-
**ProbabilityTheory.Kernel.compProd_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：compProd_add_right (μ : Kernel α β) (κ η : Kernel (α × β) γ) [IsSFiniteKer
nel κ] [IsSFiniteKernel η] : μ otimesₖ (κ + η) = μ otimesₖ κ + μ otimesₖ η
参数：μ : Kernel α β；κ η : Kernel (α × β) γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_add_right (μ : Kernel α β) (κ η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₖ (κ + η) = μ ⊗ₖ κ + μ ⊗ₖ η := by
  by_cases hμ : IsSFiniteKernel μ
  swap; · simp [hμ]
  ext a s hs
  simp only [compProd_apply hs, FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a
/-
**ProbabilityTheory.Kernel.compProd_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：compProd_sum_left {ι : Type*} [Countable ι] {κ : ι -> Kernel α β} {η : Ker
nel (α × β) γ} [forall i, IsSFiniteKernel (κ i)] : Kernel.sum κ otimesₖ η = Kern
el.sum (fun i => (κ i) otimesₖ η)
参数：α × β；κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_right`：compProd
_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsS
FiniteKernel η) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
-/
lemma compProd_sum_left {ι : Type*} [Countable ι]
    {κ : ι → Kernel α β} {η : Kernel (α × β) γ} [∀ i, IsSFiniteKernel (κ i)] :
    Kernel.sum κ ⊗ₖ η = Kernel.sum (fun i ↦ (κ i) ⊗ₖ η) := by
  by_cases hη : IsSFiniteKernel η
  · ext a s hs
    simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]
  · simp [hη]
/-
**ProbabilityTheory.Kernel.compProd_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：compProd_sum_right {ι : Type*} [Countable ι] {κ : Kernel α β} {η : ι -> Ke
rnel (α × β) γ} [forall i, IsSFiniteKernel (η i)] : κ otimesₖ Kernel.sum η = Ker
nel.sum (fun i => κ otimesₖ (η i))
参数：α × β；η i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.Kernel.sum.congr_simp`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : Counta
ble ι]   (κ κ_1 : ι → Probabi…
· 使用定理 `ProbabilityTheory.Kernel.sum_zero`：sum_zero [Countable ι] : (Kernel.sum 
fun _ : ι => (0 : Kernel α β)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compProd_sum_right {ι : Type*} [Countable ι]
    {κ : Kernel α β} {η : ι → Kernel (α × β) γ} [∀ i, IsSFiniteKernel (η i)] :
    κ ⊗ₖ Kernel.sum η = Kernel.sum (fun i ↦ κ ⊗ₖ (η i)) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ ↦ (measurable_kernel_prodMk_left' hs a).aemeasurable
/-
**ProbabilityTheory.Kernel.comapRight_compProd_id_prod** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：comapRight_compProd_id_prod {δ : Type*} {mδ : MeasurableSpace δ} (κ : Kern
el α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] {f : δ ->
 γ} (hf : MeasurableEmbedding f) : comapRight (κ otimesₖ η) (MeasurableEmbedding
.id.prodMap hf) = κ otimesₖ (comapRight η hf)
参数：κ : Kernel α β；η : Kernel (α × β) γ；hf : MeasurableEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用引理 `MeasurableEmbedding.prodMap`：MeasurableEmbedding.prodMap {α β γ δ : Type
*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {m
δ : MeasurableSpa…
· 使用定理 `MeasurableEmbedding.id`：id : MeasurableEmbedding (id : α -> α)
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comapRight_apply'`：comapRight_apply' (κ : Kerne
l α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ} (ht : MeasurableSet t) :
 comapRight κ hf a t = κ a (f ''…
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comapRight`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   
{mγ : MeasurableSpace γ} {f : γ → β} (κ :…
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
lemma comapRight_compProd_id_prod {δ : Type*} {mδ : MeasurableSpace δ}
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η]
    {f : δ → γ} (hf : MeasurableEmbedding f) :
    comapRight (κ ⊗ₖ η) (MeasurableEmbedding.id.prodMap hf) = κ ⊗ₖ (comapRight η hf) := by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht, compProd_apply, compProd_apply ht]
  · refine lintegral_congr fun b ↦ ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

end CompositionProduct

open scoped ProbabilityTheory

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- If `η` is a Markov kernel, use instead `fst_compProd` to get `(κ ⊗ₖ η).fst = κ`. -/
/-
**ProbabilityTheory.Kernel.fst_compProd_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：fst_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKerne
l κ] [IsSFiniteKernel η] (x : α) {s : Set β} (hs : MeasurableSet s) : (κ otimesₖ
 η).fst x s = ∫⁻ b, s.indicator (fun b => η (x, b) Set.univ) b ∂(κ x)
参数：κ : Kernel α β；η : Kernel (α × β) γ；x : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.fst_apply'`：fst_apply' (κ : Kernel α (β × γ)) (
a : α) {s : Set β} (hs : MeasurableSet s) : fst κ a s = κ a {p | p.1 in s}
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If `η` is a Markov kernel, use instead `fst_compProd` to get `(κ ⊗ₖ η).fst = κ`.
-/
lemma fst_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (x : α) {s : Set β} (hs : MeasurableSet s) :
    (κ ⊗ₖ η).fst x s = ∫⁻ b, s.indicator (fun b ↦ η (x, b) Set.univ) b ∂(κ x) := by
  rw [Kernel.fst_apply' _ _ hs, Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b ∈ s} = s.indicator (fun b ↦ η (x, b) Set.univ) b := by
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_ofPred_eq, h_eq]

@[simp]
/-
**ProbabilityTheory.Kernel.fst_compProd** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：fst_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [
IsMarkovKernel η] : fst (κ otimesₖ η) = κ
参数：κ : Kernel α β；η : Kernel (α × β) γ。
该定理/引理给出了一组等式。
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
· 使用引理 `ProbabilityTheory.Kernel.fst_compProd_apply`：fst_compProd_apply (κ : Ker
nel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] (x : α) 
{s : Set β} (hs : MeasurableSet s…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fst_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs; simp [fst_compProd_apply, hs]

end FstSnd

end Kernel
end ProbabilityTheory

