/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Lemmas about the composition of a measure and a kernel

Basic lemmas about the composition `κ ∘ₘ μ` of a kernel `κ` and a measure `μ`.

-/

public section

open scoped ENNReal

open ProbabilityTheory MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-
**MeasureTheory.Measure.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.bind_bind`：bind_bind {γ} [MeasurableSpace γ] {m : 
Measure α} {f : α -> Measure β} {g : β -> Measure γ} (hf : AEMeasurable f m) (hg
 : AEMeasurable g (m.…
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
-/
lemma comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.aemeasurable η.aemeasurable

/-- This lemma allows to rewrite the composition of a measure and a kernel as the composition
of two kernels, which allows to transfer properties of `∘ₖ` to `∘ₘ`. -/
/-
**MeasureTheory.Measure.comp_eq_comp_const_apply** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：comp_eq_comp_const_apply : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `ProbabilityTheory.Kernel.const_apply`：const_apply (μβ : Measure β) (a : 
α) : const α μβ a = μβ

--- 原说明 ---
This lemma allows to rewrite the composition of a measure and a kernel as the co
mposition
of two kernels, which allows to transfer properties of `∘ₖ` to `∘ₘ`.
-/
lemma comp_eq_comp_const_apply : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) () := by
  rw [Kernel.comp_apply, Kernel.const_apply]
/-
**MeasureTheory.Measure.comp_eq_sum_of_countable** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：comp_eq_sum_of_countable [Countable α] [MeasurableSingletonClass α] : κ ∘ₘ
 μ = Measure.sum (fun ω => μ {ω} • κ ω)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_countable'`：lintegral_countable' [Countable α] [
MeasurableSingletonClass α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂μ = ∑' a, f a * μ {
a}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_eq_sum_of_countable [Countable α] [MeasurableSingletonClass α] :
    κ ∘ₘ μ = Measure.sum (fun ω ↦ μ {ω} • κ ω) := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]

@[simp]
/-
**MeasureTheory.Measure.snd_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel
 κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
参数：μ : Measure α；κ : Kernel α β。
该定理/引理给出了一组等式。
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
· 使用定理 `MeasureTheory.Measure.snd_apply`：snd_apply {s : Set β} (hs : MeasurableS
et s) : ρ.snd s = ρ (Prod.snd ⁻¹' s)
· 使用引理 `MeasureTheory.Measure.compProd_apply`：compProd_apply [SFinite μ] [IsSFin
iteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) : (μ otimesₘ κ) s = ∫⁻ a, 
κ a (Prod.mk a ⁻¹' s) ∂μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := by
  ext s hs
  rw [bind_apply hs κ.aemeasurable, snd_apply hs, compProd_apply]
  · rfl
  · exact measurable_snd hs
/-
**MeasureTheory.Measure.comp_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：comp_congr (h : forallᵐ a ∂μ, κ a = η a) : κ ∘ₘ μ = η ∘ₘ μ
参数：h : forallᵐ a ∂μ, κ a = η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.bind_congr_right`：bind_congr_right {μ : Measure α}
 {f g : α -> Measure β} (h : f =ᵐ[μ] g) : μ.bind f = μ.bind g
-/
lemma comp_congr (h : ∀ᵐ a ∂μ, κ a = η a) : κ ∘ₘ μ = η ∘ₘ μ := bind_congr_right h
/-
**MeasureTheory.Measure.ae_ae_of_ae_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ae_ae_of_ae_comp {p : β -> Prop} (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω) : forallᵐ 
ω' ∂μ, forallᵐ ω ∂(κ ω'), p ω
参数：h : forallᵐ ω ∂(κ ∘ₘ μ), p ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_comp`：ae_ae_of_ae_comp (h : forallᵐ
 z ∂(η ∘ₖ κ) a, p z) : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
-/
lemma ae_ae_of_ae_comp {p : β → Prop} (h : ∀ᵐ ω ∂(κ ∘ₘ μ), p ω) :
    ∀ᵐ ω' ∂μ, ∀ᵐ ω ∂(κ ω'), p ω := by
  rw [comp_eq_comp_const_apply] at h
  exact Kernel.ae_ae_of_ae_comp h
/-
**MeasureTheory.Measure.ae_comp_of_ae_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ae_comp_of_ae_ae {p : β -> Prop} (hp : MeasurableSet {z | p z}) (h : foral
lᵐ y ∂μ, forallᵐ z ∂κ y, p z) : forallᵐ z ∂(κ ∘ₘ μ), p z
参数：hp : MeasurableSet {z | p z}；h : forallᵐ y ∂μ, forallᵐ z ∂κ y, p z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
· 使用引理 `ProbabilityTheory.Kernel.ae_comp_of_ae_ae`：ae_comp_of_ae_ae (hp : Measur
ableSet {z | p z}) (h : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z) : forallᵐ z ∂(η ∘ₖ 
κ) a, p z
-/
lemma ae_comp_of_ae_ae {p : β → Prop} (hp : MeasurableSet {z | p z})
    (h : ∀ᵐ y ∂μ, ∀ᵐ z ∂κ y, p z) : ∀ᵐ z ∂(κ ∘ₘ μ), p z := by
  rw [comp_eq_comp_const_apply]
  exact Kernel.ae_comp_of_ae_ae hp h
/-
**MeasureTheory.Measure.ae_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：ae_comp_iff {p : β -> Prop} (hp : MeasurableSet {z | p z}) : (forallᵐ z ∂(
κ ∘ₘ μ), p z) ↔ forallᵐ y ∂μ, forallᵐ z ∂κ y, p z
参数：hp : MeasurableSet {z | p z}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.ae_ae_of_ae_comp`：ae_ae_of_ae_comp {p : β -> Prop}
 (h : forallᵐ ω ∂(κ ∘ₘ μ), p ω) : forallᵐ ω' ∂μ, forallᵐ ω ∂(κ ω'), p ω
· 使用引理 `MeasureTheory.Measure.ae_comp_of_ae_ae`：ae_comp_of_ae_ae {p : β -> Prop}
 (hp : MeasurableSet {z | p z}) (h : forallᵐ y ∂μ, forallᵐ z ∂κ y, p z) : forall
ᵐ z ∂(κ ∘ₘ μ), p z
-/
lemma ae_comp_iff {p : β → Prop} (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂(κ ∘ₘ μ), p z) ↔ ∀ᵐ y ∂μ, ∀ᵐ z ∂κ y, p z :=
  ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

@[simp]
/-
**MeasureTheory.Measure._root_.ProbabilityTheory.Kernel.comp_const** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ProbabilityTheory.Kernel.comp_const (κ : Kernel β γ) (μ : Measure β) :
    κ ∘ₖ Kernel.const α μ = Kernel.const α (κ ∘ₘ μ) := rfl
/-
**MeasureTheory.Measure.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：map_comp (μ : Measure α) (κ : Kernel α β) {f : β -> γ} (hf : Measurable f)
 : (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ
参数：μ : Measure α；κ : Kernel α β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.map_apply'`：map_apply' (κ : Kernel α β) (hf : M
easurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) : map κ f a s = κ a (f ⁻
¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (μ : Measure α) (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.aemeasurable,
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

@[simp]
/-
**MeasureTheory.Measure.discard_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：discard_comp (μ : Measure α) : Kernel.discard α ∘ₘ μ = μ .univ • Measure.d
irac ()
参数：μ : Measure α。
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
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.discard_apply`：discard_apply (a : α) : discard 
α a = Measure.dirac PUnit.unit
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma discard_comp (μ : Measure α) : Kernel.discard α ∘ₘ μ = μ .univ • Measure.dirac () := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.aemeasurable _), mul_comm]
/-
**MeasureTheory.Measure.copy_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：copy_comp_map {f : α -> β} (hf : AEMeasurable f μ) : Kernel.copy β ∘ₘ (μ.m
ap f) = μ.map (Function.prod f f)
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.copy.eq_1`：∀ (α : Type u_4) [inst : MeasurableS
pace α],   ProbabilityTheory.Kernel.copy α = ProbabilityTheory.Kernel.determinis
tic Function.diag ⋯
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
-/
lemma copy_comp_map {f : α → β} (hf : AEMeasurable f μ) :
    Kernel.copy β ∘ₘ (μ.map f) = μ.map (Function.prod f f) := by
  rw [Kernel.copy, deterministic_comp_eq_map]
  exact (aemeasurable_id.prodMk aemeasurable_id).map_map_of_aemeasurable hf

section CompProd

/-
**MeasureTheory.Measure.compProd_eq_comp_prod** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFin
iteKernel κ] : μ otimesₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ
参数：μ : Measure α；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用引理 `ProbabilityTheory.Kernel.compProd_prodMkLeft_eq_comp`：compProd_prodMkLef
t_eq_comp (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel
 η] : κ otimesₖ (prodMkLeft X η) = (Kernel…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
-/
lemma compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl
/-
**MeasureTheory.Measure.compProd_id_eq_copy_comp** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：compProd_id_eq_copy_comp [SFinite μ] : μ otimesₘ Kernel.id = Kernel.copy α
 ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_id`：compProd_id [SFinite μ] : μ otimesₘ K
ernel.id = μ.map Function.diag
· 使用定理 `ProbabilityTheory.Kernel.copy.eq_1`：∀ (α : Type u_4) [inst : MeasurableS
pace α],   ProbabilityTheory.Kernel.copy α = ProbabilityTheory.Kernel.determinis
tic Function.diag ⋯
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
-/
lemma compProd_id_eq_copy_comp [SFinite μ] : μ ⊗ₘ Kernel.id = Kernel.copy α ∘ₘ μ := by
  rw [compProd_id, Kernel.copy, deterministic_comp_eq_map]
/-
**MeasureTheory.Measure.comp_compProd_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：comp_compProd_comm {η : Kernel (α × β) γ} [SFinite μ] [IsSFiniteKernel η] 
: η ∘ₘ (μ otimesₘ κ) = ((κ otimesₖ η) ∘ₘ μ).snd
参数：α × β。
该定理/引理给出了一组等式。
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
· 使用定理 `MeasureTheory.Measure.snd_apply`：snd_apply {s : Set β} (hs : MeasurableS
et s) : ρ.snd s = ρ (Prod.snd ⁻¹' s)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.compProd_of_not_isSFiniteKernel`：compProd_of_not_i
sSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) : μ ot
imesₘ κ = 0
· 使用定理 `MeasureTheory.Measure.bind_zero_left`：bind_zero_left (f : α -> Measure β
) : bind (0 : Measure α) f = 0
· 使用定理 `ProbabilityTheory.Kernel.compProd_of_not_isSFiniteKernel_left`：compProd_
of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ) (h : ¬ IsSFi
niteKernel κ) : κ otimesₖ η = 0
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用定理 `MeasureTheory.Measure.bind_zero_right`：bind_zero_right (m : Measure α) :
 bind m (0 : α -> Measure β) = 0
· 使用定理 `MeasureTheory.Measure.snd_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β], MeasureTheory.Measure.snd 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_compProd_comm {η : Kernel (α × β) γ} [SFinite μ] [IsSFiniteKernel η] :
    η ∘ₘ (μ ⊗ₘ κ) = ((κ ⊗ₖ η) ∘ₘ μ).snd := by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ,
      Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ, FunLike.coe_zero]
  ext s hs
  rw [Measure.bind_apply hs η.aemeasurable, Measure.snd_apply hs,
    Measure.bind_apply _ (Kernel.aemeasurable _), Measure.lintegral_compProd (η.measurable_coe hs)]
  swap; · exact measurable_snd hs
  congr with a
  rw [Kernel.compProd_apply]
  · rfl
  · exact measurable_snd hs

@[simp]
/-
**MeasureTheory.Measure.prodMkLeft_comp_compProd** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：prodMkLeft_comp_compProd {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ] 
: (η.prodMkLeft α) ∘ₘ μ otimesₘ κ = η ∘ₘ κ ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `ProbabilityTheory.Kernel.prodMkLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (γ : Type u_5)   [inst : Mea
surableSpace γ] (κ : Probabili…
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.comp_deterministic_eq_comap`：comp_deterministic
_eq_comap (κ : Kernel α β) (hg : Measurable g) : κ ∘ₖ deterministic g hg = comap
 κ g hg
-/
lemma prodMkLeft_comp_compProd {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ] :
    (η.prodMkLeft α) ∘ₘ μ ⊗ₘ κ = η ∘ₘ κ ∘ₘ μ := by
  rw [← snd_compProd μ κ, Kernel.prodMkLeft, snd, ← deterministic_comp_eq_map measurable_snd,
    comp_assoc, Kernel.comp_deterministic_eq_comap]
/-
**MeasureTheory.Measure.compProd_deterministic** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：compProd_deterministic [SFinite μ] {f : α -> β} (hf : Measurable f) : μ ot
imesₘ Kernel.deterministic f hf = μ.map (fun a => (a, f a))
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_eq_comp_prod`：compProd_eq_comp_prod (μ : 
Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] : μ otimesₘ κ = (Ker
nel.id ×ₖ κ) ∘ₘ μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `ProbabilityTheory.Kernel.id.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace
 α}, ProbabilityTheory.Kernel.id = ProbabilityTheory.Kernel.deterministic id ⋯
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用引理 `ProbabilityTheory.Kernel.deterministic_prod_deterministic`：deterministic
_prod_deterministic {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurab
le g) : deterministic f hf ×ₖ deterministic g h…
· 使用引理 `MeasureTheory.Measure.deterministic_comp_eq_map`：deterministic_comp_eq_m
ap {f : α -> β} (hf : Measurable f) : Kernel.deterministic f hf ∘ₘ μ = μ.map f
-/
lemma compProd_deterministic [SFinite μ] {f : α → β} (hf : Measurable f) :
    μ ⊗ₘ Kernel.deterministic f hf = μ.map (fun a ↦ (a, f a)) := by
  rw [compProd_eq_comp_prod, Kernel.id, Kernel.deterministic_prod_deterministic,
    deterministic_comp_eq_map]
  rfl

end CompProd

section AddSMul

@[simp]
/-
**MeasureTheory.Measure.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：comp_add : κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.const_add`：const_add (β : Type*) [MeasurableSpa
ce β] (μ ν : Measure α) : const β (μ + ν) = const β μ + const β ν
· 使用引理 `ProbabilityTheory.Kernel.comp_add_right`：comp_add_right (μ κ : Kernel α 
β) (η : Kernel β γ) : η ∘ₖ (μ + κ) = η ∘ₖ μ + η ∘ₖ κ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add : κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [comp_eq_comp_const_apply, Kernel.const_add, Kernel.comp_add_right, _root_.add_apply]
/-
**MeasureTheory.Measure.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：add_comp : (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.comp_add_left`：comp_add_left (μ : Kernel α β) (
κ η : Kernel β γ) : (κ + η) ∘ₖ μ = κ ∘ₖ μ + η ∘ₖ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp : (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [comp_eq_comp_const_apply, Kernel.comp_add_left, _root_.add_apply]

/-- Same as `add_comp` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order to have
a simp-normal form on the left of the equality. -/
@[simp]
/-
**MeasureTheory.Measure.add_comp'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：add_comp' : (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用引理 `MeasureTheory.Measure.add_comp`：add_comp : (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ 
μ

--- 原说明 ---
Same as `add_comp` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order 
to have
a simp-normal form on the left of the equality.
-/
lemma add_comp' : (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by rw [← FunLike.coe_add, add_comp]

@[simp]
/-
**MeasureTheory.Measure.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：comp_smul (a : Real>=0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ)
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
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [bind_apply hs κ.aemeasurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

end AddSMul

section AbsolutelyContinuous

/-
**MeasureTheory.Measure.AbsolutelyContinuous.comp_right** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {mα : MeasurableSpace α} {mγ : MeasurableS
pace γ} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν → ∀ (κ : Pro
babilityTheory.Kernel α γ), (μ.bind ⇑κ).AbsolutelyContinuous (ν.bind ⇑κ)
参数：κ : ProbabilityTheory.Kernel α γ；μ.bind ⇑κ；ν.bind ⇑κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
-/
lemma AbsolutelyContinuous.comp_right (hμν : μ ≪ ν) (κ : Kernel α γ) :
    κ ∘ₘ μ ≪ κ ∘ₘ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  exact hμν.ae_eq hs_zero
/-
**MeasureTheory.Measure.AbsolutelyContinuous.comp_left** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ η : ProbabilityTheory.Kernel α β}   (μ : MeasureTheory.Measure α),   
(∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)) → (μ.bind ⇑κ).AbsolutelyContin
uous (μ.bind ⇑η)
参数：μ : MeasureTheory.Measure α；∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)；μ
.bind ⇑κ；μ.bind ⇑η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma AbsolutelyContinuous.comp_left (μ : Measure α) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero
/-
**MeasureTheory.Measure.AbsolutelyContinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {μ ν : MeasureTheory.Measure α}   {κ η : ProbabilityTheory.Kernel α β}, 
  μ.AbsolutelyContinuous ν →     (∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a
)) → (μ.bind ⇑κ).AbsolutelyContinuous (ν.bind ⇑η)
参数：∀ᵐ (a : α) ∂μ, (κ a).AbsolutelyContinuous (η a)；μ.bind ⇑κ；ν.bind ⇑η。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.comp_left`：∀ {α : Type u_1} {
β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ η : Probabili
tyTheory.Kernel α β}   (μ : MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.comp_right`：∀ {α : Type u_1} 
{γ : Type u_3} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {μ ν : MeasureT
heory.Measure α},   μ.AbsolutelyContinuous …
-/
lemma AbsolutelyContinuous.comp (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν :=
  (AbsolutelyContinuous.comp_left μ hκη).trans (hμν.comp_right η)
/-
**MeasureTheory.Measure.absolutelyContinuous_comp_of_countable** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_comp_of_countable [Countable α] [MeasurableSingletonC
lass α] : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.comp_eq_sum_of_countable`：comp_eq_sum_of_countable
 [Countable α] [MeasurableSingletonClass α] : κ ∘ₘ μ = Measure.sum (fun ω => μ {
ω} • κ ω)
· 使用引理 `MeasureTheory.ae_iff_of_countable`：ae_iff_of_countable [Countable α] {p 
: α -> Prop} : (forallᵐ x ∂μ, p x) ↔ forall x, μ {x} != 0 -> p x
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_sum_right`：absolutelyContinuo
us_sum_right {μs : ι -> Measure α} (i : ι) (hνμ : ν ≪ μs i) : ν ≪ Measure.sum μs
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
-/
lemma absolutelyContinuous_comp_of_countable [Countable α] [MeasurableSingletonClass α] :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  rw [Measure.comp_eq_sum_of_countable, ae_iff_of_countable]
  exact fun ω hμω ↦ Measure.absolutelyContinuous_sum_right ω (Measure.absolutelyContinuous_smul hμω)

end AbsolutelyContinuous

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

section BoolKernel

variable {π : Measure Bool}

@[simp]
/-
**ProbabilityTheory.Kernel.comp_boolKernel** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (κ : ProbabilityTheory.Kernel α β)   (μ ν : MeasureTheory.Measure α),   
κ.comp (ProbabilityTheory.Kernel.boolKernel μ ν) = ProbabilityTheory.Kernel.bool
Kernel (μ.bind ⇑κ) (ν.bind ⇑κ)
参数：κ : ProbabilityTheory.Kernel α β；μ ν : MeasureTheory.Measure α；ProbabilityThe
ory.Kernel.boolKernel μ ν；μ.bind ⇑κ；ν.bind ⇑κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.comp_apply`：comp_apply (η : Kernel β γ) (κ : Ke
rnel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma Kernel.comp_boolKernel (κ : Kernel α β) (μ ν : Measure α) :
    κ ∘ₖ (boolKernel μ ν) = boolKernel (κ ∘ₘ μ) (κ ∘ₘ ν) := by
  ext b : 1
  rw [comp_apply]
  cases b <;> simp
/-
**ProbabilityTheory.boolKernel_comp_measure** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：boolKernel_comp_measure (μ ν : Measure α) (π : Measure Bool) : Kernel.bool
Kernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ
参数：μ ν : Measure α；π : Measure Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用引理 `ProbabilityTheory.Kernel.aemeasurable`：aemeasurable (κ : Kernel α β) {μ 
: Measure α} : AEMeasurable κ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_fintype`：lintegral_fintype [MeasurableSingletonC
lass α] [Fintype α] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x}
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma boolKernel_comp_measure (μ ν : Measure α) (π : Measure Bool) :
    Kernel.boolKernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [lintegral_fintype, mul_comm]
/-
**ProbabilityTheory.absolutelyContinuous_boolKernel_comp_left** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：absolutelyContinuous_boolKernel_comp_left (μ ν : Measure α) (hπ : π {false
} != 0) : μ ≪ Kernel.boolKernel μ ν ∘ₘ π
参数：μ ν : Measure α；hπ : π {false} != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.boolKernel_comp_measure`：boolKernel_comp_measure (μ ν 
: Measure α) (π : Measure Bool) : Kernel.boolKernel μ ν ∘ₘ π = π {true} • ν + π 
{false} • μ
-/
lemma absolutelyContinuous_boolKernel_comp_left (μ ν : Measure α) (hπ : π {false} ≠ 0) :
    μ ≪ Kernel.boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _
/-
**ProbabilityTheory.absolutelyContinuous_boolKernel_comp_right** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：absolutelyContinuous_boolKernel_comp_right (μ ν : Measure α) (hπ : π {true
} != 0) : ν ≪ Kernel.boolKernel μ ν ∘ₘ π
参数：μ ν : Measure α；hπ : π {true} != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.boolKernel_comp_measure`：boolKernel_comp_measure (μ ν 
: Measure α) (π : Measure Bool) : Kernel.boolKernel μ ν ∘ₘ π = π {true} • ν + π 
{false} • μ
-/
lemma absolutelyContinuous_boolKernel_comp_right (μ ν : Measure α) (hπ : π {true} ≠ 0) :
    ν ≪ Kernel.boolKernel μ ν ∘ₘ π :=
  boolKernel_comp_measure _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

end BoolKernel

end ProbabilityTheory

