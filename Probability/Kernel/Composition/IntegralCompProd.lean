/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Bochner integral of a function against the composition and the composition-products of two kernels

We prove properties of the composition and the composition-product of two kernels.

If `κ` is a kernel from `α` to `β` and `η` is a kernel from `β` to `γ`, we can form their
composition `η ∘ₖ κ : Kernel α γ`. We proved in `ProbabilityTheory.Kernel.lintegral_comp` that it
verifies `∫⁻ c, f c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, f c ∂(η b) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

If `κ` is an s-finite kernel from `α` to `β` and `η` is an s-finite kernel from `α × β` to `γ`,
we can form their composition-product `κ ⊗ₖ η : Kernel α (β × γ)`.
We proved in `ProbabilityTheory.Kernel.lintegral_compProd` that it
verifies `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

## Main statements

* `ProbabilityTheory.integral_compProd`: the integral against the composition-product is
  `∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a)`.

* `ProbabilityTheory.integral_comp`: the integral against the composition is
  `∫⁻ z, f z ∂((η ∘ₖ κ) a) = ∫⁻ x, ∫⁻ y, f y ∂(η x) ∂(κ a)`.

## Implementation details

This file is to a large extent a copy of part of `Mathlib/MeasureTheory/Integral/Prod.lean`.
The product of two measures is a particular case of composition-product of kernels and
it turns out that once the measurability of the Lebesgue integral of a kernel is proved,
almost all proofs about integrals against products of measures extend with minimal modifications
to the composition-product of two kernels.

The composition of kernels can also be expressed easily with the composition-product and therefore
the proofs about the composition are only simplified versions of the ones for the
composition-product. However it is necessary to do all the proofs once again because the
composition-product requires s-finiteness while the composition does not.
-/

public section


noncomputable section

open Set Function Real ENNReal MeasureTheory Filter ProbabilityTheory ProbabilityTheory.Kernel
open scoped Topology ENNReal MeasureTheory

variable {α β γ E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [NormedAddCommGroup E] {a : α}

namespace ProbabilityTheory

section compProd

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

/-
**ProbabilityTheory.hasFiniteIntegral_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：hasFiniteIntegral_prodMk_left (a : α) {s : Set (β × γ)} (h2s : (κ otimesₖ 
η) a s != ∞) : HasFiniteIntegral (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ
 a)
参数：a : α；β × γ；h2s : (κ otimesₖ η) a s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.ae_kernel_lt_top`：ae_kernel_lt_top (a : α) (h2s
 : (κ otimesₖ η) a s != ∞) : forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `ProbabilityTheory.Kernel.le_compProd_apply`：le_compProd_apply (κ : Kerne
l α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) (s
 : Set (β × γ)) : ∫⁻ b, η (a, b)…
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem hasFiniteIntegral_prodMk_left (a : α) {s : Set (β × γ)} (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
    HasFiniteIntegral (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  let t := toMeasurable ((κ ⊗ₖ η) a) s
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  calc
    ∫⁻ b, ENNReal.ofReal (η (a, b) (Prod.mk b ⁻¹' s)).toReal ∂κ a
    _ ≤ ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' t) ∂κ a := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_kernel_lt_top a h2s] with b hb
      rw [ofReal_toReal hb.ne]
      exact measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ ≤ (κ ⊗ₖ η) a t := le_compProd_apply _ _ _ _
    _ = (κ ⊗ₖ η) a s := measure_toMeasurable s
    _ < ⊤ := h2s.lt_top
/-
**ProbabilityTheory.integrable_kernel_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：integrable_kernel_prodMk_left (a : α) {s : Set (β × γ)} (hs : MeasurableSe
t s) (h2s : (κ otimesₖ η) a s != ∞) : Integrable (fun b => (η (a, b)).real (Prod
.mk b ⁻¹' s)) (κ a)
参数：a : α；β × γ；hs : MeasurableSet s；h2s : (κ otimesₖ η) a s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `ProbabilityTheory.hasFiniteIntegral_prodMk_left`：hasFiniteIntegral_prodM
k_left (a : α) {s : Set (β × γ)} (h2s : (κ otimesₖ η) a s != ∞) : HasFiniteInteg
ral (fun b => (η (a, b)).real (Prod.m…
-/
theorem integrable_kernel_prodMk_left (a : α) {s : Set (β × γ)} (hs : MeasurableSet s)
    (h2s : (κ ⊗ₖ η) a s ≠ ∞) : Integrable (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  constructor
  · exact (measurable_kernel_prodMk_left' hs a).ennreal_toReal.aestronglyMeasurable
  · exact hasFiniteIntegral_prodMk_left a h2s
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_co
mpProd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd [NormedSpace ℝ E]
    ⦃f : β × γ → E⦄ (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂η (a, x), hf.stronglyMeasurable_mk.integral_kernel_prod_right'', by
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left**
 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left {δ : Type*} [TopologicalSpace δ]
    {f : β × γ → δ} (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    ∀ᵐ x ∂κ a, AEStronglyMeasurable (fun y => f (x, y)) (η (a, x)) := by
  filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with x hx using
    ⟨fun y => hf.mk f (x, y), hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

/-! ### Integrability -/


/-
**ProbabilityTheory.hasFiniteIntegral_compProd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：hasFiniteIntegral_compProd_iff ⦃f : β × γ -> E⦄ (h1f : StronglyMeasurable 
f) : HasFiniteIntegral f ((κ otimesₖ η) a) ↔ (forallᵐ x ∂κ a, HasFiniteIntegral 
(fun y => f (x, y)) (η (a, x))) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η
 (a, x)) (κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Measurable.lintegral_kernel_prod_right''`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measu
rableSpace γ} {η : Probability…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤

--- 原说明 ---
### Integrability
-/
theorem hasFiniteIntegral_compProd_iff ⦃f : β × γ → E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [hasFiniteIntegral_iff_enorm]
  rw [lintegral_compProd _ _ _ h1f.enorm]
  have : ∀ x, ∀ᵐ y ∂η (a, x), 0 ≤ ‖f (x, y)‖ := fun x => Eventually.of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff, and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; finiteness
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_kernel_prod_right''
/-
**ProbabilityTheory.hasFiniteIntegral_compProd_iff'** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory`。
形式化陈述：hasFiniteIntegral_compProd_iff' ⦃f : β × γ -> E⦄ (h1f : AEStronglyMeasurab
le f ((κ otimesₖ η) a)) : HasFiniteIntegral f ((κ otimesₖ η) a) ↔ (forallᵐ x ∂κ 
a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧ HasFiniteIntegral (fun x 
=> ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_congr`：hasFiniteIntegral_congr {f g : α 
-> ε} (h : f =ᵐ[μ] g) : HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `ProbabilityTheory.hasFiniteIntegral_compProd_iff`：hasFiniteIntegral_comp
Prod_iff ⦃f : β × γ -> E⦄ (h1f : StronglyMeasurable f) : HasFiniteIntegral f ((κ
 otimesₖ η) a) ↔ (forallᵐ x ∂κ a, HasF…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_compProd`：ae_ae_of_ae_compProd {p :
 β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a, p bc) : forallᵐ b ∂κ a, forall
ᵐ c ∂η (a, b), p (b, c)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem hasFiniteIntegral_compProd_iff' ⦃f : β × γ → E⦄
    (h1f : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    HasFiniteIntegral f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk,
    hasFiniteIntegral_compProd_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with x hx using
      hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)
/-
**ProbabilityTheory.integrable_compProd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：integrable_compProd_iff ⦃f : β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ 
otimesₖ η) a)) : Integrable f ((κ otimesₖ η) a) ↔ (forallᵐ x ∂κ a, Integrable (f
un y => f (x, y)) (η (a, x))) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) 
(κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.hasFiniteIntegral_compProd_iff'`：hasFiniteIntegral_com
pProd_iff' ⦃f : β × γ -> E⦄ (h1f : AEStronglyMeasurable f ((κ otimesₖ η) a)) : H
asFiniteIntegral f ((κ otimesₖ η) a) ↔ …
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.compProd_mk_left`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} {a : α} {κ : Pro…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd`：∀ {α : Type
 u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ 
: MeasurableSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_compProd_iff ⦃f : β × γ → E⦄ (hf : AEStronglyMeasurable f ((κ ⊗ₖ η) a)) :
    Integrable f ((κ ⊗ₖ η) a) ↔
      (∀ᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x))) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [Integrable, hasFiniteIntegral_compProd_iff' hf, hf.norm.integral_kernel_compProd,
    hf, hf.compProd_mk_left, eventually_and, true_and]
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.ae_of_compProd** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.ae_of_compProd ⦃f : β × γ → E⦄
    (hf : Integrable f ((κ ⊗ₖ η) a)) : ∀ᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x)) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_norm_compProd** 是 M
athlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_compProd ⦃f : β × γ → E⦄
    (hf : Integrable f ((κ ⊗ₖ η) a)) : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_compProd** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_compProd [NormedSpace ℝ E]
    ⦃f : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a)) :
    Integrable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
  Integrable.mono hf.integral_norm_compProd hf.aestronglyMeasurable.integral_kernel_compProd <|
    Eventually.of_forall fun x =>
      (norm_integral_le_integral_norm _).trans_eq <|
        (norm_of_nonneg <|
            integral_nonneg_of_ae <|
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

/-! ### Bochner integral -/


variable [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-
**ProbabilityTheory.Kernel.integral_fn_integral_add** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E] {E' : Type u_5} [inst_4 : NormedAd
dCommGroup E'] [inst_5 : NormedSpace ℝ E']   ⦃f g : β × γ → E⦄ (F : E → E'),   M
easureTheory.Integrable f ((κ.compProd η) a) →     MeasureTheory.Integrable g ((
κ.compProd η) a) →       ∫ (x : β), F (∫ (y : γ), f (x, y) + g (x, y) ∂η (a, x))
 ∂κ a =         ∫ (x : β), F (∫ (y : γ), f (x, y) ∂η (a, x) + ∫ (y : γ), g (x, y
) ∂η (a, x)) ∂κ a
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_compProd`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
   {mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Kernel.integral_fn_integral_add ⦃f g : β × γ → E⦄ (F : E → E')
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) + g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) + ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_add h2f h2g]
/-
**ProbabilityTheory.Kernel.integral_fn_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E] {E' : Type u_5} [inst_4 : NormedAd
dCommGroup E'] [inst_5 : NormedSpace ℝ E']   ⦃f g : β × γ → E⦄ (F : E → E'),   M
easureTheory.Integrable f ((κ.compProd η) a) →     MeasureTheory.Integrable g ((
κ.compProd η) a) →       ∫ (x : β), F (∫ (y : γ), f (x, y) - g (x, y) ∂η (a, x))
 ∂κ a =         ∫ (x : β), F (∫ (y : γ), f (x, y) ∂η (a, x) - ∫ (y : γ), g (x, y
) ∂η (a, x)) ∂κ a
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_compProd`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
   {mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Kernel.integral_fn_integral_sub ⦃f g : β × γ → E⦄ (F : E → E')
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]
/-
**ProbabilityTheory.Kernel.lintegral_fn_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E] ⦃f g : β × γ → E⦄ (F : E → ENNReal
),   MeasureTheory.Integrable f ((κ.compProd η) a) →     MeasureTheory.Integrabl
e g ((κ.compProd η) a) →       ∫⁻ (x : β), F (∫ (y : γ), f (x, y) - g (x, y) ∂η 
(a, x)) ∂κ a =         ∫⁻ (x : β), F (∫ (y : γ), f (x, y) ∂η (a, x) - ∫ (y : γ),
 g (x, y) ∂η (a, x)) ∂κ a
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_compProd`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
   {mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Kernel.lintegral_fn_integral_sub ⦃f g : β × γ → E⦄ (F : E → ℝ≥0∞)
    (hf : Integrable f ((κ ⊗ₖ η) a)) (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫⁻ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]
/-
**ProbabilityTheory.Kernel.integral_integral_add** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E] ⦃f g : β × γ → E⦄,   MeasureTheory
.Integrable f ((κ.compProd η) a) →     MeasureTheory.Integrable g ((κ.compProd η
) a) →       ∫ (x : β), ∫ (y : γ), f (x, y) + g (x, y) ∂η (a, x) ∂κ a =         
∫ (x : β), ∫ (y : γ), f (x, y) ∂η (a, x) ∂κ a + ∫ (x : β), ∫ (y : γ), g (x, y) ∂
η (a, x) ∂κ a
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.integral_fn_integral_add`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Measurab
leSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_compProd`：∀ {α : Type u_1} {β : Type u
_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace
 β}   {mγ : MeasurableSpace γ} […
-/
theorem Kernel.integral_integral_add ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, f (x, y) + g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  (Kernel.integral_fn_integral_add id hf hg).trans <|
    integral_add hf.integral_compProd hg.integral_compProd
/-
**ProbabilityTheory.Kernel.integral_integral_add'** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：integral_integral_add'_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)
) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, ∫ y, (f + g) y ∂η x ∂κ a = ∫ x, ∫ y, f
 y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_add`：∀ {α : Type u_1} {β : Ty
pe u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} […
-/
theorem Kernel.integral_integral_add' ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, (f + g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_add hf hg
/-
**ProbabilityTheory.Kernel.integral_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E] ⦃f g : β × γ → E⦄,   MeasureTheory
.Integrable f ((κ.compProd η) a) →     MeasureTheory.Integrable g ((κ.compProd η
) a) →       ∫ (x : β), ∫ (y : γ), f (x, y) - g (x, y) ∂η (a, x) ∂κ a =         
∫ (x : β), ∫ (y : γ), f (x, y) ∂η (a, x) ∂κ a - ∫ (x : β), ∫ (y : γ), g (x, y) ∂
η (a, x) ∂κ a
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.integral_fn_integral_sub`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Measurab
leSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_compProd`：∀ {α : Type u_1} {β : Type u
_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace
 β}   {mγ : MeasurableSpace γ} […
-/
theorem Kernel.integral_integral_sub ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, f (x, y) - g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  (Kernel.integral_fn_integral_sub id hf hg).trans <|
    integral_sub hf.integral_compProd hg.integral_compProd
/-
**ProbabilityTheory.Kernel.integral_integral_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：integral_integral_sub'_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)
) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, ∫ y, (f - g) y ∂η x ∂κ a = ∫ x, ∫ y, f
 y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_sub`：∀ {α : Type u_1} {β : Ty
pe u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {mγ : MeasurableSpace γ} […
-/
theorem Kernel.integral_integral_sub' ⦃f g : β × γ → E⦄ (hf : Integrable f ((κ ⊗ₖ η) a))
    (hg : Integrable g ((κ ⊗ₖ η) a)) :
    ∫ x, ∫ y, (f - g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_sub hf hg
/-
**ProbabilityTheory.Kernel.continuous_integral_integral** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   [ProbabilityTheory.I
sSFiniteKernel κ] {η : ProbabilityTheory.Kernel (α × β) γ} [ProbabilityTheory.Is
SFiniteKernel η]   [inst_3 : NormedSpace ℝ E], Continuous fun f => ∫ (x : β), ∫ 
(y : γ), ↑↑f (x, y) ∂η (a, x) ∂κ a
参数：α × β；x : β；y : γ；x, y；a, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.integral_compProd`：∀ {α : Type u_1} {β : Type u
_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace
 β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_fn_integral_sub`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Measura
bleSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_compProd`：lintegral_compProd (κ : Ker
nel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) 
{f : β × γ -> Real>=0∞} (hf : Mea…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_ofReal`：continuous_ofReal : Continuous ENNReal.ofReal
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
（共 31 条，此处仅展示前 30 条）
-/
theorem Kernel.continuous_integral_integral :
    Continuous fun f : β × γ →₁[(κ ⊗ₖ η) a] E => ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_compProd.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_compProd) ?_
  simp_rw [← lintegral_fn_integral_sub (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂η (a, x) ∂κ a
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : Lp (α := β × γ) E 1 (((κ ⊗ₖ η) a) : Measure (β × γ))) :
      Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_compProd _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_id
/-
**ProbabilityTheory.integral_compProd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：integral_compProd : forall {f : β × γ -> E} (_ : Integrable f ((κ otimesₖ 
η) a)), ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left'`：measurable_kern
el_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s) (a 
: α) : Measurable fun b => η (a, b) (Prod.mk …
· 使用定理 `ProbabilityTheory.Kernel.ae_kernel_lt_top`：ae_kernel_lt_top (a : α) (h2s
 : (κ otimesₖ η) a s != ∞) : forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `MeasureTheory.integral_add'`：integral_add' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_add'`：integral_integral_add'_
comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ
) a)) : ∫ x, ∫ y, (f + g) y ∂η x ∂κ a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.continuous_integral`：continuous_integral : Continuous fun 
f : α ->₁[μ] G => ∫ a, f a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.continuous_integral_integral`：∀ {α : Type u_1} 
{β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Meas
urableSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 42 条，此处仅展示前 30 条）
-/
theorem integral_compProd :
    ∀ {f : β × γ → E} (_ : Integrable f ((κ ⊗ₖ η) a)),
      ∫ z, f z ∂(κ ⊗ₖ η) a = ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), MeasureTheory.setIntegral_const,
      integral_smul_const, measureReal_def]
    congr 1
    rw [integral_toReal]
    rotate_left
    · exact (Kernel.measurable_kernel_prodMk_left' hs _).aemeasurable
    · exact ae_kernel_lt_top a h2s.ne
    rw [Kernel.compProd_apply hs]
  · intro f g _ i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, Kernel.integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral
  · intro f g hfg _ hf
    convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_compProd hfg] with x hfgx using
        integral_congr_ae (ae_eq_symm hfgx)
/-
**ProbabilityTheory.setIntegral_compProd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：setIntegral_compProd {f : β × γ -> E} {s : Set β} {t : Set γ} (hs : Measur
ableSet s) (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ((κ otimesₖ η) a
)) : ∫ z in s ×ˢ t, f z ∂(κ otimesₖ η) a = ∫ x in s, ∫ y in t, f (x, y) ∂η (a, x
) ∂κ a
参数：hs : MeasurableSet s；ht : MeasurableSet t；hf : IntegrableOn f (s ×ˢ t) ((κ ot
imesₖ η) a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `ProbabilityTheory.Kernel.compProd_restrict`：compProd_restrict {s : Set β
} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) : Kernel.restrict κ 
hs otimesₖ Kernel.restrict η ht …
· 使用定理 `ProbabilityTheory.integral_compProd`：integral_compProd : forall {f : β ×
 γ -> E} (_ : Integrable f ((κ otimesₖ η) a)), ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, 
∫ y, f (x, y) ∂η (a, x) ∂…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.restrict`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {s : Set β}   (κ : 
ProbabilityTheory.Kernel α β) [Probabil…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_compProd {f : β × γ → E} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ((κ ⊗ₖ η) a)) :
    ∫ z in s ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫ x in s, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  -- Porting note: `compProd_restrict` needed some explicit arguments
  rw [← Kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← compProd_restrict hs ht, integral_compProd]
  · simp_rw [Kernel.restrict_apply]
  · rw [compProd_restrict, Kernel.restrict_apply]; exact hf
/-
**ProbabilityTheory.setIntegral_compProd_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory`。
形式化陈述：setIntegral_compProd_univ_right (f : β × γ -> E) {s : Set β} (hs : Measura
bleSet s) (hf : IntegrableOn f (s ×ˢ univ) ((κ otimesₖ η) a)) : ∫ z in s ×ˢ univ
, f z ∂(κ otimesₖ η) a = ∫ x in s, ∫ y, f (x, y) ∂η (a, x) ∂κ a
参数：f : β × γ -> E；hs : MeasurableSet s；hf : IntegrableOn f (s ×ˢ univ) ((κ otime
sₖ η) a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.setIntegral_compProd`：setIntegral_compProd {f : β × γ 
-> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hf 
: IntegrableOn f (s ×ˢ t) ((…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_compProd_univ_right (f : β × γ → E) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ univ) ((κ ⊗ₖ η) a)) :
    ∫ z in s ×ˢ univ, f z ∂(κ ⊗ₖ η) a = ∫ x in s, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd hs MeasurableSet.univ hf, Measure.restrict_univ]
/-
**ProbabilityTheory.setIntegral_compProd_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：setIntegral_compProd_univ_left (f : β × γ -> E) {t : Set γ} (ht : Measurab
leSet t) (hf : IntegrableOn f (univ ×ˢ t) ((κ otimesₖ η) a)) : ∫ z in univ ×ˢ t,
 f z ∂(κ otimesₖ η) a = ∫ x, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a
参数：f : β × γ -> E；ht : MeasurableSet t；hf : IntegrableOn f (univ ×ˢ t) ((κ otime
sₖ η) a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.setIntegral_compProd`：setIntegral_compProd {f : β × γ 
-> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hf 
: IntegrableOn f (s ×ˢ t) ((…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_compProd_univ_left (f : β × γ → E) {t : Set γ} (ht : MeasurableSet t)
    (hf : IntegrableOn f (univ ×ˢ t) ((κ ⊗ₖ η) a)) :
    ∫ z in univ ×ˢ t, f z ∂(κ ⊗ₖ η) a = ∫ x, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd MeasurableSet.univ ht hf, Measure.restrict_univ]

end compProd

section comp

variable {κ : Kernel α β} {η : Kernel β γ}

/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_co
mp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp [NormedSpace ℝ E]
    ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f y ∂η x) (κ a) :=
  ⟨fun x ↦ ∫ y, hf.mk f y ∂η x, hf.stronglyMeasurable_mk.integral_kernel, by
    filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.comp** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp {δ : Type*} [TopologicalSpace δ]
    {f : γ → δ} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    ∀ᵐ x ∂κ a, AEStronglyMeasurable f (η x) := by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x hx using
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hx⟩

/-! ### Integrability with respect to composition -/

/-
**ProbabilityTheory.hasFiniteIntegral_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：hasFiniteIntegral_comp_iff ⦃f : γ -> E⦄ (hf : StronglyMeasurable f) : HasF
initeIntegral f ((η ∘ₖ κ) a) ↔ (forallᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ Has
FiniteIntegral (fun x => ∫ y, ‖f y‖ ∂η x) (κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤

--- 原说明 ---
### Integrability with respect to composition
-/
theorem hasFiniteIntegral_comp_iff ⦃f : γ → E⦄ (hf : StronglyMeasurable f) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (∀ᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) := by
  simp_rw [hasFiniteIntegral_iff_enorm, lintegral_comp _ _ _ hf.enorm]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y ↦ norm_nonneg _)
      hf.norm.aestronglyMeasurable, enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun h ↦ by
    rw [← and_congr_right_iff, and_iff_right_of_imp h]
  rw [this]
  · intro h
    rw [lintegral_congr_ae]
    filter_upwards [h] with x hx
    rw [ofReal_toReal]
    finiteness
  · exact fun h ↦ ae_lt_top hf.enorm.lintegral_kernel h.ne
/-
**ProbabilityTheory.hasFiniteIntegral_comp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：hasFiniteIntegral_comp_iff' ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η 
∘ₖ κ) a)) : HasFiniteIntegral f ((η ∘ₖ κ) a) ↔ (forallᵐ x ∂κ a, HasFiniteIntegra
l f (η x)) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f y‖ ∂η x) (κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_congr`：hasFiniteIntegral_congr {f g : α 
-> ε} (h : f =ᵐ[μ] g) : HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `ProbabilityTheory.hasFiniteIntegral_comp_iff`：hasFiniteIntegral_comp_iff
 ⦃f : γ -> E⦄ (hf : StronglyMeasurable f) : HasFiniteIntegral f ((η ∘ₖ κ) a) ↔ (
forallᵐ x ∂κ a, HasFiniteIntegral …
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.ae_ae_of_ae_comp`：ae_ae_of_ae_comp (h : forallᵐ
 z ∂(η ∘ₖ κ) a, p z) : forallᵐ y ∂κ a, forallᵐ z ∂η y, p z
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem hasFiniteIntegral_comp_iff' ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (∀ᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) := by
  rw [hasFiniteIntegral_congr hf.ae_eq_mk, hasFiniteIntegral_comp_iff hf.stronglyMeasurable_mk]
  refine and_congr (eventually_congr ?_) (hasFiniteIntegral_congr ?_)
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      hasFiniteIntegral_congr hx
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)
/-
**ProbabilityTheory.integrable_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：integrable_comp_iff ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)
) : Integrable f ((η ∘ₖ κ) a) ↔ (forallᵐ y ∂κ a, Integrable f (η y)) ∧ Integrabl
e (fun y => ∫ z, ‖f z‖ ∂η y) (κ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.hasFiniteIntegral_comp_iff'`：hasFiniteIntegral_comp_if
f' ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) : HasFiniteIntegral f
 ((η ∘ₖ κ) a) ↔ (forallᵐ x ∂κ a, Ha…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp`：∀ {α : Type u_1} {β : Type u_2}
 {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : Measur
ableSpace γ} {a : α} {κ : Pro…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_kernel_comp`：∀ {α : Type u_1
} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Me
asurableSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_comp_iff ⦃f : γ → E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    Integrable f ((η ∘ₖ κ) a) ↔
    (∀ᵐ y ∂κ a, Integrable f (η y)) ∧ Integrable (fun y ↦ ∫ z, ‖f z‖ ∂η y) (κ a) := by
  simp only [Integrable, hf, hasFiniteIntegral_comp_iff' hf, true_and, eventually_and, hf.comp,
    hf.norm.integral_kernel_comp]
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.integrable_comp_iff** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.MeasureTheory.Measure.integrable_comp_iff {μ : Measure α} {f : β → E}
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (∀ᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.ae_of_comp** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.ae_of_comp ⦃f : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) :
    ∀ᵐ x ∂κ a, Integrable f (η x) := ((integrable_comp_iff hf.1).1 hf).1
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_norm_comp** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_comp ⦃f : γ → E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x ↦ ∫ y, ‖f y‖ ∂η x) (κ a) :=
  ((integrable_comp_iff hf.1).1 hf).2
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_comp** 是 Mathlib 中的
一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_comp [NormedSpace ℝ E] ⦃f : γ → E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x ↦ ∫ y, f y ∂η x) (κ a) :=
  Integrable.mono hf.integral_norm_comp hf.1.integral_kernel_comp <|
    ae_of_all _ fun _ ↦ (norm_integral_le_integral_norm _).trans_eq
    (norm_of_nonneg <| integral_nonneg_of_ae <| ae_of_all _ fun _ ↦ norm_nonneg _).symm

/-! ### Bochner integral with respect to the composition -/

variable [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace Kernel

/-
**ProbabilityTheory.Kernel.integral_fn_integral_add_comp** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：integral_fn_integral_add_comp ⦃f g : γ -> E⦄ (F : E -> E') (hf : Integrabl
e f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, F (∫ y, f y + g y ∂η x
) ∂κ a = ∫ x, F (∫ y, f y ∂η x + ∫ y, g y ∂η x) ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_fn_integral_add_comp ⦃f g : γ → E⦄ (F : E → E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y + g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x + ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_add h2f h2g]
/-
**ProbabilityTheory.Kernel.integral_fn_integral_sub_comp** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：integral_fn_integral_sub_comp ⦃f g : γ -> E⦄ (F : E -> E') (hf : Integrabl
e f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, F (∫ y, f y - g y ∂η x
) ∂κ a = ∫ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_fn_integral_sub_comp ⦃f g : γ → E⦄ (F : E → E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]
/-
**ProbabilityTheory.Kernel.lintegral_fn_integral_sub_comp** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：lintegral_fn_integral_sub_comp ⦃f g : γ -> E⦄ (F : E -> Real>=0∞) (hf : In
tegrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫⁻ x, F (∫ y, f y - 
g y ∂η x) ∂κ a = ∫⁻ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.ae_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {
mγ : MeasurableSpace γ} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_fn_integral_sub_comp ⦃f g : γ → E⦄ (F : E → ℝ≥0∞)
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫⁻ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫⁻ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]
/-
**ProbabilityTheory.Kernel.integral_integral_add_comp** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：integral_integral_add_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
 (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, ∫ y, f y + g y ∂η x ∂κ a = ∫ x, ∫ y, f 
y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.integral_fn_integral_add_comp`：integral_fn_inte
gral_add_comp ⦃f g : γ -> E⦄ (F : E -> E') (hf : Integrable f ((η ∘ₖ κ) a)) (hg 
: Integrable g ((η ∘ₖ κ) a)) : ∫ x, F (∫ y, …
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_comp`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
  {mγ : MeasurableSpace γ} […
-/
theorem integral_integral_add_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y + g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
  (integral_fn_integral_add_comp id hf hg).trans <| integral_add hf.integral_comp hg.integral_comp
/-
**ProbabilityTheory.Kernel.integral_integral_add'_comp** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   {η : ProbabilityTheo
ry.Kernel β γ} [inst_1 : NormedSpace ℝ E] ⦃f g : γ → E⦄,   MeasureTheory.Integra
ble f ((η.comp κ) a) →     MeasureTheory.Integrable g ((η.comp κ) a) →       ∫ (
x : β), ∫ (y : γ), (f + g) y ∂η x ∂κ a =         ∫ (x : β), ∫ (y : γ), f y ∂η x 
∂κ a + ∫ (x : β), ∫ (y : γ), g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_add_comp`：integral_integral_a
dd_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘
ₖ κ) a)) : ∫ x, ∫ y, f y + g y ∂η x ∂κ a …
-/
theorem integral_integral_add'_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f + g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_add_comp hf hg
/-
**ProbabilityTheory.Kernel.integral_integral_sub_comp** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：integral_integral_sub_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
 (hg : Integrable g ((η ∘ₖ κ) a)) : ∫ x, ∫ y, f y - g y ∂η x ∂κ a = ∫ x, ∫ y, f 
y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.Kernel.integral_fn_integral_sub_comp`：integral_fn_inte
gral_sub_comp ⦃f g : γ -> E⦄ (F : E -> E') (hf : Integrable f ((η ∘ₖ κ) a)) (hg 
: Integrable g ((η ∘ₖ κ) a)) : ∫ x, F (∫ y, …
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_comp`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
  {mγ : MeasurableSpace γ} […
-/
theorem integral_integral_sub_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y - g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
  (integral_fn_integral_sub_comp id hf hg).trans <| integral_sub hf.integral_comp hg.integral_comp
/-
**ProbabilityTheory.Kernel.integral_integral_sub'_comp** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : Measur
ableSpace α} {mβ : MeasurableSpace β}   {mγ : MeasurableSpace γ} [inst : NormedA
ddCommGroup E] {a : α} {κ : ProbabilityTheory.Kernel α β}   {η : ProbabilityTheo
ry.Kernel β γ} [inst_1 : NormedSpace ℝ E] ⦃f g : γ → E⦄,   MeasureTheory.Integra
ble f ((η.comp κ) a) →     MeasureTheory.Integrable g ((η.comp κ) a) →       ∫ (
x : β), ∫ (y : γ), (f - g) y ∂η x ∂κ a =         ∫ (x : β), ∫ (y : γ), f y ∂η x 
∂κ a - ∫ (x : β), ∫ (y : γ), g y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_sub_comp`：integral_integral_s
ub_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘
ₖ κ) a)) : ∫ x, ∫ y, f y - g y ∂η x ∂κ a …
-/
theorem integral_integral_sub'_comp ⦃f g : γ → E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f - g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_sub_comp hf hg
/-
**ProbabilityTheory.Kernel.continuous_integral_integral_comp** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：continuous_integral_integral_comp : Continuous fun f : γ ->₁[(η ∘ₖ κ) a] E
 => ∫ x, ∫ y, f y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.integral_comp`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
  {mγ : MeasurableSpace γ} […
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.lintegral_fn_integral_sub_comp`：lintegral_fn_in
tegral_sub_comp ⦃f g : γ -> E⦄ (F : E -> Real>=0∞) (hf : Integrable f ((η ∘ₖ κ) 
a)) (hg : Integrable g ((η ∘ₖ κ) a)) : ∫⁻ x, …
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `ProbabilityTheory.Kernel.lintegral_comp`：lintegral_comp (η : Kernel β γ)
 (κ : Kernel α β) (a : α) {g : γ -> Real>=0∞} (hg : Measurable g) : ∫⁻ c, g c ∂(
η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_ofReal`：continuous_ofReal : Continuous ENNReal.ofReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
（共 33 条，此处仅展示前 30 条）
-/
theorem continuous_integral_integral_comp :
    Continuous fun f : γ →₁[(η ∘ₖ κ) a] E ↦ ∫ x, ∫ y, f y ∂η x ∂κ a := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  refine tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_comp.aestronglyMeasurable
      (Eventually.of_forall fun h ↦ (L1.integrable_coeFn h).integral_comp) ?_
  simp_rw [← lintegral_fn_integral_sub_comp (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun i ↦ ∫⁻ x, ∫⁻ y, ‖i y - g y‖ₑ ∂η x ∂κ a)
    tendsto_const_nhds ?_ (fun _ ↦ zero_le) ?_
  swap; · exact fun _ ↦ lintegral_mono fun _ ↦ enorm_integral_le_lintegral_enorm _
  have (i : γ →₁[(η ∘ₖ κ) a] E) : Measurable fun z ↦ ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_comp _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  exact (continuous_ofReal.tendsto 0).comp (tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id)
/-
**ProbabilityTheory.Kernel.integral_comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.Kernel`。
形式化陈述：integral_comp : forall {f : γ -> E} (_ : Integrable f ((η ∘ₖ κ) a)), ∫ z, 
f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y, f y ∂η x ∂κ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `ProbabilityTheory.Kernel.ae_lt_top_of_comp_ne_top`：ae_lt_top_of_comp_ne_
top (a : α) (hs : (η ∘ₖ κ) a s != ∞) : forallᵐ b ∂κ a, η b s < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ProbabilityTheory.Kernel.comp_apply'`：comp_apply' (η : Kernel β γ) (κ : 
Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) : (η ∘ₖ κ) a s = ∫⁻ b, η 
b s ∂κ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_add'`：integral_add' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.integral_integral_add'_comp`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} {E : Type u_4} {mα : MeasurableSpace α} {mβ : Measu
rableSpace β}   {mγ : MeasurableSpace γ} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.continuous_integral`：continuous_integral : Continuous fun 
f : α ->₁[μ] G => ∫ a, f a ∂μ
· 使用定理 `ProbabilityTheory.Kernel.continuous_integral_integral_comp`：continuous_i
ntegral_integral_comp : Continuous fun f : γ ->₁[(η ∘ₖ κ) a] E => ∫ x, ∫ y, f y 
∂η x ∂κ a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
（共 41 条，此处仅展示前 30 条）
-/
theorem integral_comp : ∀ {f : γ → E} (_ : Integrable f ((η ∘ₖ κ) a)),
    ∫ z, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y, f y ∂η x ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs ms
    simp_rw [integral_indicator hs, MeasureTheory.setIntegral_const, integral_smul_const,
      measureReal_def]
    congr
    rw [integral_toReal, Kernel.comp_apply' _ _ _ hs]
    · exact (Kernel.measurable_coe _ hs).aemeasurable
    · exact ae_lt_top_of_comp_ne_top a ms.ne
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add'_comp i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral_comp
  · rintro f g hfg - hf
    convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_comp hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)
/-
**ProbabilityTheory.Kernel.setIntegral_comp** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.Kernel`。
形式化陈述：setIntegral_comp {f : γ -> E} {s : Set γ} (hs : MeasurableSet s) (hf : Int
egrableOn f s ((η ∘ₖ κ) a)) : ∫ z in s, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y in s, f y ∂η 
x ∂κ a
参数：hs : MeasurableSet s；hf : IntegrableOn f s ((η ∘ₖ κ) a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.Kernel.restrict_apply`：restrict_apply (κ : Kernel α β)
 (hs : MeasurableSet s) (a : α) : κ.restrict hs a = (κ a).restrict s
· 使用定理 `ProbabilityTheory.Kernel.comp_restrict`：comp_restrict {s : Set γ} (hs : 
MeasurableSet s) : η.restrict hs ∘ₖ κ = (η ∘ₖ κ).restrict hs
· 使用定理 `ProbabilityTheory.Kernel.integral_comp`：integral_comp : forall {f : γ ->
 E} (_ : Integrable f ((η ∘ₖ κ) a)), ∫ z, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y, f y ∂η x ∂
κ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_comp {f : γ → E} {s : Set γ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s ((η ∘ₖ κ) a)) :
    ∫ z in s, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y in s, f y ∂η x ∂κ a := by
  rw [← restrict_apply (η ∘ₖ κ) hs, ← comp_restrict hs, integral_comp]
  · simp_rw [restrict_apply]
  · rwa [comp_restrict, restrict_apply]

end Kernel

end comp

end ProbabilityTheory

namespace MeasureTheory

namespace Measure

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] {a : α} {κ : Kernel α β} {μ : Measure α} {f : β → E}

section Integral

/-
**MeasureTheory.Measure._root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd
** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd [SFinite μ] [IsSFiniteKernel κ]
    {E : Type*} [NormedAddCommGroup E] {f : α → β → E}
    (hf : AEStronglyMeasurable f.uncurry (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (f x) (κ x) := by
  simpa using hf.compProd_mk_left
/-
**MeasureTheory.Measure.integrable_compProd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [Norme
dAddCommGroup E] {f : α × β -> E} (hf : AEStronglyMeasurable f (μ otimesₘ κ)) : 
Integrable f (μ otimesₘ κ) ↔ (forallᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)
) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ
参数：hf : AEStronglyMeasurable f (μ otimesₘ κ)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.integrable_compProd_iff`：integrable_compProd_iff ⦃f : 
β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) : Integrable f ((κ o
timesₖ η) a) ↔ (forallᵐ x ∂κ a,…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
    {f : α × β → E} (hf : AEStronglyMeasurable f (μ ⊗ₘ κ)) :
    Integrable f (μ ⊗ₘ κ) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]
/-
**MeasureTheory.Measure.integral_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCo
mmGroup E] [NormedSpace Real E] {f : α × β -> E} (hf : Integrable f (μ otimesₘ κ
)) : ∫ x, f x ∂(μ otimesₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ
参数：hf : Integrable f (μ otimesₘ κ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.integral_compProd`：integral_compProd : forall {f : β ×
 γ -> E} (_ : Integrable f ((κ otimesₖ η) a)), ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, 
∫ y, f (x, y) ∂η (a, x) ∂…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) :
    ∫ x, f x ∂(μ ⊗ₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd, ProbabilityTheory.integral_compProd hf]
  simp
/-
**MeasureTheory.Measure.setIntegral_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：setIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAd
dCommGroup E] [NormedSpace Real E] {s : Set α} (hs : MeasurableSet s) {t : Set β
} (ht : MeasurableSet t) {f : α × β -> E} (hf : IntegrableOn f (s ×ˢ t) (μ otime
sₘ κ)) : ∫ x in s ×ˢ t, f x ∂(μ otimesₘ κ) = ∫ a in s, ∫ b in t, f (a, b) ∂(κ a)
 ∂μ
参数：hs : MeasurableSet s；ht : MeasurableSet t；hf : IntegrableOn f (s ×ˢ t) (μ oti
mesₘ κ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα
 : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Measure α)   (
κ : ProbabilityTheory.Ker…
· 使用定理 `ProbabilityTheory.setIntegral_compProd`：setIntegral_compProd {f : β × γ 
-> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hf 
: IntegrableOn f (s ×ˢ t) ((…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsSFiniteKernel`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheor
y.Measure β}   [MeasureTheory.SFinite μβ…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.prodMkLeft`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   
{mγ : MeasurableSpace γ} (κ : Probability…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t)
    {f : α × β → E} (hf : IntegrableOn f (s ×ˢ t) (μ ⊗ₘ κ)) :
    ∫ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫ a in s, ∫ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd, ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

end Integral

section Integrable

/-
**MeasureTheory.Measure.integrable_compProd_snd_iff** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：integrable_compProd_snd_iff [SFinite μ] [IsSFiniteKernel κ] (hf : AEStrong
lyMeasurable f (κ ∘ₘ μ)) : Integrable (fun p => f p.2) (μ otimesₘ κ) ↔ Integrabl
e f (κ ∘ₘ μ)
参数：hf : AEStronglyMeasurable f (κ ∘ₘ μ)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma integrable_compProd_snd_iff [SFinite μ] [IsSFiniteKernel κ]
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable (fun p ↦ f p.2) (μ ⊗ₘ κ) ↔ Integrable f (κ ∘ₘ μ) := by
  rw [← Measure.snd_compProd, Measure.snd, integrable_map_measure _ measurable_snd.aemeasurable,
    Function.comp_def]
  rwa [← Measure.snd, Measure.snd_compProd]
/-
**MeasureTheory.Measure.ae_integrable_of_integrable_comp** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：ae_integrable_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) : forallᵐ
 x ∂μ, Integrable f (κ x)
参数：h_int : Integrable f (κ ∘ₘ μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.integrable_comp_iff`：integrable_comp_iff ⦃f : γ -> E⦄ 
(hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) : Integrable f ((η ∘ₖ κ) a) ↔ (forall
ᵐ y ∂κ a, Integrable f (η y…
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
-/
lemma ae_integrable_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    ∀ᵐ x ∂μ, Integrable f (κ x) := by
  rw [Measure.comp_eq_comp_const_apply, integrable_comp_iff h_int.1] at h_int
  exact h_int.1
/-
**MeasureTheory.Measure.integrable_integral_norm_of_integrable_comp** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：integrable_integral_norm_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)
) : Integrable (fun x => ∫ y, ‖f y‖ ∂κ x) μ
参数：h_int : Integrable f (κ ∘ₘ μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.integrable_comp_iff`：integrable_comp_iff ⦃f : γ -> E⦄ 
(hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) : Integrable f ((η ∘ₖ κ) a) ↔ (forall
ᵐ y ∂κ a, Integrable f (η y…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.Measure.comp_eq_comp_const_apply`：comp_eq_comp_const_apply
 : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) ()
-/
lemma integrable_integral_norm_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    Integrable (fun x ↦ ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply, integrable_comp_iff h_int.1] at h_int
  exact h_int.2

end Integrable

end Measure

end MeasureTheory

