/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Condition for two kernels to be equal almost everywhere

We prove that two finite kernels `κ, η : Kernel α β` are `μ`-a.e. equal for a finite measure `μ` iff
the composition-products `μ ⊗ₘ κ` and `μ ⊗ₘ η` are equal.
The result requires `α` to be countable or `β` to be a countably generated measurable space.

## Main statements

* `compProd_withDensity`: `μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)`
* `compProd_eq_iff`: `μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η`

-/

public section

open ProbabilityTheory MeasureTheory

open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}
  {f : α → β → ℝ≥0∞}

namespace MeasureTheory.Measure

/-- A composition-product of a measure with a kernel defined with `withDensity` is equal to the
`withDensity` of the composition-product. -/
/-
**MeasureTheory.Measure.compProd_withDensity** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：compProd_withDensity [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel (κ.w
ithDensity f)] (hf : Measurable (Function.uncurry f)) : μ otimesₘ (κ.withDensity
 f) = (μ otimesₘ κ).withDensity (fun p => f p.1 p.2)
参数：κ.withDensity f；hf : Measurable (Function.uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)

--- 原说明 ---
A composition-product of a measure with a kernel defined with `withDensity` is e
qual to the
`withDensity` of the composition-product.
-/
lemma compProd_withDensity [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2) := by
  ext s hs
  rw [compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_compProd]
  · congr with a
    rw [Kernel.withDensity_apply' _ hf, ← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {η : Kernel α β} [MeasurableSpace.CountableOrCountablyGenerated α β]

/-
**ProbabilityTheory.Kernel.ae_eq_of_compProd_eq** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：ae_eq_of_compProd_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKerne
l η] (h : μ otimesₘ κ = μ otimesₘ η) : κ =ᵐ[μ] η
参数：h : μ otimesₘ κ = μ otimesₘ η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.kernel_of_compProd`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : 
MeasureTheory.Measure α}   {κ η : ProbabilityTheory…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_eq`：absolutelyContinuous_o
f_eq (h : μ = ν) : μ ≪ ν
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq 
[IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) : η.withDensity (κ
.rnDeriv η) a = κ a
· 使用引理 `MeasureTheory.Measure.ae_ae_of_ae_compProd`：ae_ae_of_ae_compProd [SFinit
e μ] [IsSFiniteKernel κ] {p : α × β -> Prop} (h : forallᵐ x ∂(μ otimesₘ κ), p x)
 : forallᵐ a ∂μ, forallᵐ b ∂κ a,…
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`：ae_eq_of_f
orall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (hg : Measurable g) (h : forall s, …
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `MeasureTheory.Measure.compProd_congr`：compProd_congr [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) : μ otimesₘ κ = μ otimesₘ η
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelWithDensityRnDeriv`：∀ {α : Ty
pe u_1} {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : 
ProbabilityTheory.Kernel α γ}   [hαγ : MeasurableSp…
· 使用引理 `MeasureTheory.Measure.compProd_withDensity`：compProd_withDensity [SFinit
e μ] [IsSFiniteKernel κ] [IsSFiniteKernel (κ.withDensity f)] (hf : Measurable (F
unction.uncurry f)) : μ otimesₘ …
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_one_iff_eq`：rnDeriv_eq_one_iff_eq [I
sFiniteKernel κ] [IsFiniteKernel η] {a : α} (h_ac : κ a ≪ η a) : (forallᵐ b ∂(η 
a), κ.rnDeriv η a b = 1) ↔ κ a = η a
-/
lemma ae_eq_of_compProd_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : μ ⊗ₘ κ = μ ⊗ₘ η) :
    κ =ᵐ[μ] η := by
  have h_ac : ∀ᵐ a ∂μ, κ a ≪ η a := (Measure.absolutelyContinuous_of_eq h).kernel_of_compProd
  have hκ_eq : ∀ᵐ a ∂μ, κ a = η.withDensity (κ.rnDeriv η) a := by
    filter_upwards [h_ac] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  suffices ∀ᵐ a ∂μ, ∀ᵐ b ∂(η a), κ.rnDeriv η a b = 1 by
    filter_upwards [h_ac, this] with a h_ac h using (rnDeriv_eq_one_iff_eq h_ac).mp h
  refine Measure.ae_ae_of_ae_compProd (p := fun x ↦ κ.rnDeriv η x.1 x.2 = 1) ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, one_mul]
  calc ∫⁻ x in s, κ.rnDeriv η x.1 x.2 ∂μ ⊗ₘ η
  _ = (μ ⊗ₘ κ) s := by
    rw [Measure.compProd_congr hκ_eq, Measure.compProd_withDensity, withDensity_apply _ hs]
    fun_prop
  _ = (μ ⊗ₘ η) s := by rw [h]

/-- Two finite kernels `κ` and `η` are `μ`-a.e. equal iff the composition-products `μ ⊗ₘ κ`
and `μ ⊗ₘ η` are equal. -/
/-
**ProbabilityTheory.Kernel.compProd_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：compProd_eq_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] 
: μ otimesₘ κ = μ otimesₘ η ↔ κ =ᵐ[μ] η
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`：ae_eq_of_compProd_eq [IsF
initeMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (h : μ otimesₘ κ = μ otime
sₘ η) : κ =ᵐ[μ] η
· 使用引理 `MeasureTheory.Measure.compProd_congr`：compProd_congr [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) : μ otimesₘ κ = μ otimesₘ η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…

--- 原说明 ---
Two finite kernels `κ` and `η` are `μ`-a.e. equal iff the composition-products `
μ ⊗ₘ κ`
and `μ ⊗ₘ η` are equal.
-/
lemma compProd_eq_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ = μ ⊗ₘ η ↔ κ =ᵐ[μ] η :=
  ⟨Kernel.ae_eq_of_compProd_eq, Measure.compProd_congr⟩

end ProbabilityTheory.Kernel

