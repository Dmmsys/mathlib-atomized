/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integration with respect to the product measure

In this file we prove Fubini's theorem.

## Main results

* `MeasureTheory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
* `MeasureTheory.integral_prod`: Fubini's theorem. It states that for an integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem (see `MeasureTheory.lintegral_prod`). The lemma
  `MeasureTheory.Integrable.integral_prod_right` states that the inner integral of the right-hand
  side is integrable.
* `MeasureTheory.integral_integral_swap_of_hasCompactSupport`: a version of Fubini's theorem for
  continuous functions with compact support, which does not assume that the measures are σ-finite
  contrary to all the usual versions of Fubini.

## Tags

product measure, Fubini's theorem, Fubini-Tonelli theorem
-/

public section

noncomputable section

open scoped Topology ENNReal MeasureTheory

open Set Function Real ENNReal

open MeasureTheory MeasurableSpace MeasureTheory.Measure

open TopologicalSpace

open Filter hiding prod_eq map

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
variable [NormedAddCommGroup E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/

section

variable [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form. -/
/-
**MeasureTheory.StronglyMeasurable.integral_prod_right** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MeasureTheory.StronglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α ->
 β -> E⦄ (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y
, f x y ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.StronglyMeasurable.setToFun_prod_right`：∀ {α : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace
 ℝ E]   [inst_2 : NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.StronglyMeasurable.smul_const`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type u_5}   [inst
_1 : TopologicalSpace 𝕜] [inst_2 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)

--- 原说明 ---
The Bochner integral is measurable. This shows that the integrand of (the right-
hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form.
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂ν := by
  simp only [integral_eq_setToFun]
  apply StronglyMeasurable.setToFun_prod_right _ (fun s hs ↦ ?_) hf
  refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
  exact measurable_measure_prodMk_left hs

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
/-
**MeasureTheory.StronglyMeasurable.integral_prod_right'** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：MeasureTheory.StronglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α ×
 β -> E⦄ (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y)
 ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_prod_right`：MeasureTheory.Stro
nglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α -> β -> E⦄ (hf : StronglyM
easurable (uncurry f)) : StronglyMeasurabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f

--- 原说明 ---
The Bochner integral is measurable. This shows that the integrand of (the right-
hand-side of)
  Fubini's theorem is measurable.
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂ν := by
  rw [← uncurry_curry f] at hf; exact hf.integral_prod_right

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form. -/
/-
**MeasureTheory.StronglyMeasurable.integral_prod_left** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α -> 
β -> E⦄ (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x,
 f x y ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_prod_right'`：MeasureTheory.Str
onglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β -> E⦄ (hf : Strongly
Measurable f) : StronglyMeasurable fun x =>…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
The Bochner integral is measurable. This shows that the integrand of (the right-
hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form.
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable. -/
/-
**MeasureTheory.StronglyMeasurable.integral_prod_left'** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MeasureTheory.StronglyMeasurable.integral_prod_left' [SFinite μ] ⦃f : α × 
β -> E⦄ (hf : StronglyMeasurable f) : StronglyMeasurable fun y => ∫ x, f (x, y) 
∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_prod_right'`：MeasureTheory.Str
onglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β -> E⦄ (hf : Strongly
Measurable f) : StronglyMeasurable fun x =>…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
The Bochner integral is measurable. This shows that the integrand of (the right-
hand-side of)
  the symmetric version of Fubini's theorem is measurable.
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left' [SFinite μ] ⦃f : α × β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun y => ∫ x, f (x, y) ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

end

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

variable [SFinite ν]

/-
**MeasureTheory.Measure.integrable_measure_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：integrable_measure_prodMk_left {s : Set (α × β)} (hs : MeasurableSet s) (h
2s : (μ.prod ν) s != ∞) : Integrable (fun x => ν.real (Prod.mk x ⁻¹' s)) μ
参数：α × β；hs : MeasurableSet s；h2s : (μ.prod ν) s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_measure_lt_top`：ae_measure_lt_top {s : Set (α ×
 β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s != ∞) : forallᵐ x ∂μ, ν (Prod.mk
 x ⁻¹' s) < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem integrable_measure_prodMk_left {s : Set (α × β)} (hs : MeasurableSet s)
    (h2s : (μ.prod ν) s ≠ ∞) : Integrable (fun x => ν.real (Prod.mk x ⁻¹' s)) μ := by
  refine ⟨(measurable_measure_prodMk_left hs).ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  convert! h2s.lt_top using 1
  rw [prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [ae_measure_lt_top hs h2s] with x hx
  rw [lt_top_iff_ne_top] at hx
  simp [ofReal_toReal, hx]

end Measure

end MeasureTheory

open MeasureTheory.Measure

section

variable {X : Type*} [TopologicalSpace X]

/-
**MeasureTheory.AEStronglyMeasurable.prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {X :
 Type u_4} [inst_2 : TopologicalSpace X] [MeasureTheory.SFinite μ]   [MeasureThe
ory.SFinite ν] {f : β × α → X},   MeasureTheory.AEStronglyMeasurable f (ν.prod μ
) → MeasureTheory.AEStronglyMeasurable (fun z => f z.swap) (μ.prod ν)
参数：ν.prod μ；fun z => f z.swap；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
protected theorem MeasureTheory.AEStronglyMeasurable.prod_swap [SFinite μ] [SFinite ν]
    {f : β × α → X} (hf : AEStronglyMeasurable f (ν.prod μ)) :
    AEStronglyMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap
/-
**MeasureTheory.AEStronglyMeasurable.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.comp_fst {γ} [TopologicalSpace γ] {f : 
α -> γ} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun z : α × β =>
 f z.1) (μ.prod ν)
参数：hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_fst {γ} [TopologicalSpace γ] {f : α → γ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
/-
**MeasureTheory.AEStronglyMeasurable.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.comp_snd {γ} [TopologicalSpace γ] {f : 
β -> γ} (hf : AEStronglyMeasurable f ν) : AEStronglyMeasurable (fun z : α × β =>
 f z.2) (μ.prod ν)
参数：hf : AEStronglyMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_snd {γ} [TopologicalSpace γ] {f : β → γ}
    (hf : AEStronglyMeasurable f ν) : AEStronglyMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

/-- The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
/-
**MeasureTheory.AEStronglyMeasurable.integral_prod_right'** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.integral_prod_right' [SFinite ν] [Norme
dSpace Real E] ⦃f : α × β -> E⦄ (hf : AEStronglyMeasurable f (μ.prod ν)) : AEStr
onglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_prod_right'`：MeasureTheory.Str
onglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β -> E⦄ (hf : Strongly
Measurable f) : StronglyMeasurable fun x =>…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ

--- 原说明 ---
The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is 
a.e.-measurable.
-/
theorem MeasureTheory.AEStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace ℝ E]
    ⦃f : α × β → E⦄ (hf : AEStronglyMeasurable f (μ.prod ν)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩
/-
**MeasureTheory.AEStronglyMeasurable.prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.prodMk_left [SFinite ν] {f : α × β -> X
} (hf : AEStronglyMeasurable f (μ.prod ν)) : forallᵐ x ∂μ, AEStronglyMeasurable 
(fun y => f (x, y)) ν
参数：hf : AEStronglyMeasurable f (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem MeasureTheory.AEStronglyMeasurable.prodMk_left [SFinite ν] {f : α × β → X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => f (x, y)) ν := by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨fun y ↦ hf.mk f (x, y),
    hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩
/-
**MeasureTheory.AEStronglyMeasurable.prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.prodMk_right [SFinite μ] [SFinite ν] {f
 : α × β -> X} (hf : AEStronglyMeasurable f (μ.prod ν)) : forallᵐ y ∂ν, AEStrong
lyMeasurable (fun x => f (x, y)) μ
参数：hf : AEStronglyMeasurable f (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk_left`：MeasureTheory.AEStrongly
Measurable.prodMk_left [SFinite ν] {f : α × β -> X} (hf : AEStronglyMeasurable f
 (μ.prod ν)) : forallᵐ x ∂μ, AEStron…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…
-/
theorem MeasureTheory.AEStronglyMeasurable.prodMk_right [SFinite μ] [SFinite ν] {f : α × β → X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x => f (x, y)) μ :=
  hf.prod_swap.prodMk_left
/-
**MeasureTheory.AEStronglyMeasurable.of_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {X :
 Type u_4} [inst_2 : TopologicalSpace X] {f : β → X} [MeasureTheory.SFinite ν], 
  MeasureTheory.AEStronglyMeasurable (fun x => f x.2) (μ.prod ν) → μ ≠ 0 → Measu
reTheory.AEStronglyMeasurable f ν
参数：fun x => f x.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk_left`：MeasureTheory.AEStrongly
Measurable.prodMk_left [SFinite ν] {f : α × β -> X} (hf : AEStronglyMeasurable f
 (μ.prod ν)) : forallᵐ x ∂μ, AEStron…
-/
protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_snd {f : β → X} [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.2) (μ.prod ν)) (hμ : μ ≠ 0) : AEStronglyMeasurable f ν := by
  have := NeZero.mk hμ
  obtain ⟨y, hy⟩ := hf.prodMk_left.exists
  exact hy
/-
**MeasureTheory.AEStronglyMeasurable.of_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {X :
 Type u_4} [inst_2 : TopologicalSpace X] {f : α → X} [MeasureTheory.SFinite μ]  
 [MeasureTheory.SFinite ν],   MeasureTheory.AEStronglyMeasurable (fun x => f x.1
) (μ.prod ν) → ν ≠ 0 → MeasureTheory.AEStronglyMeasurable f μ
参数：fun x => f x.1；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.of_comp_snd`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheo
ry.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…
-/
protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_fst {f : α → X} [SFinite μ] [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.1) (μ.prod ν)) (hν : ν ≠ 0) : AEStronglyMeasurable f μ :=
  hf.prod_swap.of_comp_snd hν
/-
**MeasureTheory.AEStronglyMeasurable.comp_fst_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.comp_fst_iff [SFinite μ] [SFinite ν] {f
 : α -> X} (hν : ν != 0) : AEStronglyMeasurable (f ·.1) (μ.prod ν) ↔ AEStronglyM
easurable f μ
参数：hν : ν != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.of_comp_fst`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheo
ry.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_fst`：MeasureTheory.AEStronglyMea
surable.comp_fst {γ} [TopologicalSpace γ] {f : α -> γ} (hf : AEStronglyMeasurabl
e f μ) : AEStronglyMeasurable (fu…
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_fst_iff [SFinite μ] [SFinite ν] {f : α → X}
    (hν : ν ≠ 0) : AEStronglyMeasurable (f ·.1) (μ.prod ν) ↔ AEStronglyMeasurable f μ :=
  ⟨(.of_comp_fst · hν), .comp_fst⟩
/-
**MeasureTheory.AEStronglyMeasurable.comp_snd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.comp_snd_iff [SFinite ν] {f : β -> X} (
hμ : μ != 0) : AEStronglyMeasurable (f ·.2) (μ.prod ν) ↔ AEStronglyMeasurable f 
ν
参数：hμ : μ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.of_comp_snd`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheo
ry.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`：MeasureTheory.AEStronglyMea
surable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ} (hf : AEStronglyMeasurabl
e f ν) : AEStronglyMeasurable (fu…
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_snd_iff [SFinite ν] {f : β → X}
    (hμ : μ ≠ 0) : AEStronglyMeasurable (f ·.2) (μ.prod ν) ↔ AEStronglyMeasurable f ν :=
  ⟨(.of_comp_snd · hμ), .comp_snd⟩

end

namespace MeasureTheory

variable [SFinite ν]

/-! ### Integrability on a product -/

section

/-
**MeasureTheory.integrable_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_swap_iff [SFinite μ] {f : α × β -> E} : Integrable (f ∘ Prod.sw
ap) (ν.prod μ) ↔ Integrable f (μ.prod ν)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem integrable_swap_iff [SFinite μ] {f : α × β → E} :
    Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν) :=
  measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding
/-
**MeasureTheory.Integrable.swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integra
ble`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] ⦃f : α × β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → Meas
ureTheory.Integrable (f ∘ Prod.swap) (ν.prod μ)
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_swap_iff`：integrable_swap_iff [SFinite μ] {f : 
α × β -> E} : Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν)
-/
theorem Integrable.swap [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (f ∘ Prod.swap) (ν.prod μ) :=
  integrable_swap_iff.2 hf
/-
**MeasureTheory.hasFiniteIntegral_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hasFiniteIntegral_prod_iff ⦃f : α × β -> E⦄ (h1f : StronglyMeasurable f) :
 HasFiniteIntegral f (μ.prod ν) ↔ (forallᵐ x ∂μ, HasFiniteIntegral (fun y => f (
x, y)) ν) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
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
· 使用定理 `Measurable.lintegral_prod_right'`：Measurable.lintegral_prod_right' [SFin
ite ν] : forall {f : α × β -> Real>=0∞}, Measurable f -> Measurable fun x => ∫⁻ 
y, f (x, y) ∂ν
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem hasFiniteIntegral_prod_iff ⦃f : α × β → E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_prod _ h1f.enorm.aemeasurable]
  have (x : _) : ∀ᵐ y ∂ν, 0 ≤ ‖f (x, y)‖ := by filter_upwards with y using norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  -- this fact is probably too specialized to be its own lemma
  have : ∀ {p q r : Prop} (_ : r → p), (r ↔ p ∧ q) ↔ p → (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff, and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; rw [← lt_top_iff_ne_top]; exact hx
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_prod_right'
/-
**MeasureTheory.hasFiniteIntegral_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_prod_iff' ⦃f : α × β -> E⦄ (h1f : AEStronglyMeasurable f
 (μ.prod ν)) : HasFiniteIntegral f (μ.prod ν) ↔ (forallᵐ x ∂μ, HasFiniteIntegral
 (fun y => f (x, y)) ν) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ
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
· 使用定理 `MeasureTheory.hasFiniteIntegral_prod_iff`：hasFiniteIntegral_prod_iff ⦃f 
: α × β -> E⦄ (h1f : StronglyMeasurable f) : HasFiniteIntegral f (μ.prod ν) ↔ (f
orallᵐ x ∂μ, HasFiniteIntegral…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem hasFiniteIntegral_prod_iff' ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk,
    hasFiniteIntegral_prod_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

/-- A binary function is integrable if the function `y ↦ f (x, y)` is integrable for almost every
  `x` and the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable. -/
/-
**MeasureTheory.integrable_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_prod_iff ⦃f : α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod
 ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ x ∂μ, Integrable (fun y => f (x, y)) ν
) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk_left`：MeasureTheory.AEStrongly
Measurable.prodMk_left [SFinite ν] {f : α × β -> X} (hf : AEStronglyMeasurable f
 (μ.prod ν)) : forallᵐ x ∂μ, AEStron…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`：MeasureTheory.A
EStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace Real E] ⦃f : α
 × β -> E⦄ (hf : AEStronglyMeasurable f (μ.pr…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A binary function is integrable if the function `y ↦ f (x, y)` is integrable for
 almost every
  `x` and the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
-/
theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp [Integrable, h1f, hasFiniteIntegral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prodMk_left]

/-- A binary function is integrable if the function `x ↦ f (x, y)` is integrable for almost every
  `y` and the function `y ↦ ∫ ‖f (x, y)‖ dx` is integrable. -/
/-
**MeasureTheory.integrable_prod_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_prod_iff' [SFinite μ] ⦃f : α × β -> E⦄ (h1f : AEStronglyMeasura
ble f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ y ∂ν, Integrable (fun x =
> f (x, y)) μ) ∧ Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasureTheory.integrable_swap_iff`：integrable_swap_iff [SFinite μ] {f : 
α × β -> E} : Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.integrable_prod_iff`：integrable_prod_iff ⦃f : α × β -> E⦄ 
(h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ x
 ∂μ, Integrable (fun y …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…

--- 原说明 ---
A binary function is integrable if the function `x ↦ f (x, y)` is integrable for
 almost every
  `y` and the function `y ↦ ∫ ‖f (x, y)‖ dx` is integrable.
-/
theorem integrable_prod_iff' [SFinite μ] ⦃f : α × β → E⦄
    (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧ Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
  convert! integrable_prod_iff h1f.prod_swap using 1
  rw [funext fun _ => Function.comp_apply.symm, integrable_swap_iff]
/-
**MeasureTheory.Integrable.prod_left_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] ⦃f : α × β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → ∀ᵐ (
y : β) ∂ν, MeasureTheory.Integrable (fun x => f (x, y)) μ
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_prod_iff'`：integrable_prod_iff' [SFinite μ] ⦃f 
: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν
) ↔ (forallᵐ y ∂ν, Integ…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.prod_left_ae [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ :=
  ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1
/-
**MeasureTheory.Integrable.prod_right_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] ⦃f : α × β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → ∀ᵐ (
x : α) ∂μ, MeasureTheory.Integrable (fun y => f (x, y)) ν
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.prod_left_ae`：∀ {α : Type u_1} {β : Type u_2} {
E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Mea
sureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …
-/
theorem Integrable.prod_right_ae [SFinite μ] ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν :=
  hf.swap.prod_left_ae
/-
**MeasureTheory.Integrable.integral_norm_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   ⦃f : α × 
β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → MeasureTheory.Integrable (fun 
x => ∫ (y : β), ‖f (x, y)‖ ∂ν) μ
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_prod_iff`：integrable_prod_iff ⦃f : α × β -> E⦄ 
(h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ x
 ∂μ, Integrable (fun y …
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
-/
theorem Integrable.integral_norm_prod_left ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).2
/-
**MeasureTheory.Integrable.integral_norm_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] ⦃f : α × β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → Meas
ureTheory.Integrable (fun y => ∫ (x : α), ‖f (x, y)‖ ∂μ) ν
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integral_norm_prod_left`：∀ {α : Type u_1} {β : 
Type u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]
   {μ : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …
-/
theorem Integrable.integral_norm_prod_right [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν :=
  hf.swap.integral_norm_prod_left

omit [SFinite ν] in
/-
**MeasureTheory.Integrable.op_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.I
ntegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] {F : Type u_4}   {G : Type u_5} [inst
_3 : NormedAddCommGroup F] [inst_4 : NormedAddCommGroup G] {op : E → F → G},   C
ontinuous (Function.uncurry op) →     (∃ C, ∀ (x : E) (y : F), ‖op x y‖ ≤ C * ‖x
‖ * ‖y‖) →       ∀ {f : α → E} {g : β → F},         MeasureTheory.Integrable f μ
 →           MeasureTheory.Integrable g ν → MeasureTheory.Integrable (fun z => o
p (f z.1) (g z.2)) (μ.prod ν)
参数：Function.uncurry op；∃ C, ∀ (x : E) (y : F), ‖op x y‖ ≤ C * ‖x‖ * ‖y‖；fun z =>
 op (f z.1) (g z.2)；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable₂`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ 
: MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_fst`：MeasureTheory.AEStronglyMea
surable.comp_fst {γ} [TopologicalSpace γ] {f : α -> γ} (hf : AEStronglyMeasurabl
e f μ) : AEStronglyMeasurable (fu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`：MeasureTheory.AEStronglyMea
surable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ} (hf : AEStronglyMeasurabl
e f ν) : AEStronglyMeasurable (fu…
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.lintegral_prod_le`：lintegral_prod_le (f : α × β -> Real>=0
∞) : ∫⁻ z, f z ∂μ.prod ν <= ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.lintegral_mul_const'`：lintegral_mul_const' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem Integrable.op_fst_snd {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {op : E → F → G} (hop : Continuous op.uncurry) (hop_norm : ∃ C, ∀ x y, ‖op x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : α → E} {g : β → F} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z ↦ op (f z.1) (g z.2)) (μ.prod ν) := by
  use hop.comp_aestronglyMeasurable₂ hf.1.comp_fst hg.1.comp_snd
  rcases hop_norm with ⟨C, hC⟩
  calc
    ∫⁻ z, ‖op (f z.1) (g z.2)‖ₑ ∂μ.prod ν ≤ ∫⁻ z, .ofReal C * ‖f z.1‖ₑ * ‖g z.2‖ₑ ∂μ.prod ν := by
      gcongr with z
      simp only [enorm_eq_nnnorm, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
      refine (hC _ _).trans ?_
      gcongr
      apply le_coe_toNNReal
    _ ≤ ∫⁻ x, ∫⁻ y, .ofReal C * ‖f x‖ₑ * ‖g y‖ₑ ∂ν ∂μ := lintegral_prod_le _
    _ ≤ .ofReal C * (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [lintegral_const_mul', lintegral_mul_const', hg.2.ne, mul_assoc]
    _ < ∞ := by apply_rules [ENNReal.mul_lt_top, hf.2, hg.2, ENNReal.ofReal_lt_top]
/-
**MeasureTheory.Integrable.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} [inst_2 : NormedAdd
CommGroup E] {f : α → E},   MeasureTheory.Integrable f μ →     ∀ (ν : MeasureThe
ory.Measure β) [MeasureTheory.IsFiniteMeasure ν],       MeasureTheory.Integrable
 (fun x => f x.1) (μ.prod ν)
参数：ν : MeasureTheory.Measure β；fun x => f x.1；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
-/
lemma Integrable.comp_fst {f : α → E} (hf : Integrable f μ) (ν : Measure β) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ f x.1) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_fst ν
/-
**MeasureTheory.Integrable.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {ν : MeasureTheory.Measure β} [inst_2 : NormedAdd
CommGroup E] [MeasureTheory.SFinite ν] {f : β → E},   MeasureTheory.Integrable f
 ν →     ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],     
  MeasureTheory.Integrable (fun x => f x.2) (μ.prod ν)
参数：μ : MeasureTheory.Measure α；fun x => f x.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
-/
lemma Integrable.comp_snd {f : β → E} (hf : Integrable f ν) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (fun x ↦ f x.2) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_snd μ

omit [SFinite ν] in
@[fun_prop]
/-
**MeasureTheory.Integrable.smul_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] {R : Type u_4}   [inst_3 : NormedRing
 R] [inst_4 : _root_.Module R E] [IsBoundedSMul R E] {f : α → R} {g : β → E},   
MeasureTheory.Integrable f μ →     MeasureTheory.Integrable g ν → MeasureTheory.
Integrable (fun z => f z.1 • g z.2) (μ.prod ν)
参数：fun z => f z.1 • g z.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.op_fst_snd`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measu
reTheory.Measure α} {ν : …
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
-/
theorem Integrable.smul_prod {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    {f : α → R} {g : β → E} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν) :=
  hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg

omit [SFinite ν] in
@[fun_prop]
/-
**MeasureTheory.Integrable.mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {L :
 Type u_4} [inst_2 : NormedRing L] {f : α → L} {g : β → L},   MeasureTheory.Inte
grable f μ →     MeasureTheory.Integrable g ν → MeasureTheory.Integrable (fun z 
=> f z.1 * g z.2) (μ.prod ν)
参数：fun z => f z.1 * g z.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul_prod`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measur
eTheory.Measure α} {ν : …
-/
theorem Integrable.mul_prod {L : Type*} [NormedRing L] {f : α → L} {g : β → L} (hf : Integrable f μ)
    (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) :=
  hf.smul_prod hg
/-
**MeasureTheory.IntegrableOn.swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Integ
rableOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] {f : α × β → E} {s : Set α} {t : Set β},   MeasureTheory.Integr
ableOn f (s ×ˢ t) (μ.prod ν) → MeasureTheory.IntegrableOn (f ∘ Prod.swap) (t ×ˢ 
s) (ν.prod μ)
参数：s ×ˢ t；μ.prod ν；f ∘ Prod.swap；t ×ˢ s；ν.prod μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
-/
theorem IntegrableOn.swap [SFinite μ] {f : α × β → E} {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (f ∘ Prod.swap) (t ×ˢ s) (ν.prod μ) := by
  rw [IntegrableOn, ← Measure.prod_restrict] at hf ⊢
  exact hf.swap
/-
**MeasureTheory.Integrable.of_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   {f : β → 
E}, MeasureTheory.Integrable (fun x => f x.2) (μ.prod ν) → μ ≠ 0 → MeasureTheory
.Integrable f ν
参数：fun x => f x.2；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.of_comp_snd`：∀ {α : Type u_1} {β : Ty
pe u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheo
ry.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Integrable.of_comp_snd {f : β → E} (hf : Integrable (f ·.2) (μ.prod ν)) (hμ : μ ≠ 0) :
    Integrable f ν := by
  rcases hf with ⟨hf_meas, hf_fin⟩
  use hf_meas.of_comp_snd hμ
  have := hf_meas.enorm
  aesop (add simp [HasFiniteIntegral, lintegral_prod, ENNReal.mul_lt_top_iff])
/-
**MeasureTheory.Integrable.of_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.SFinite μ] {f : α → E},   MeasureTheory.Integrable (fun x => f x.1) (μ.pro
d ν) → ν ≠ 0 → MeasureTheory.Integrable f μ
参数：fun x => f x.1；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_comp_snd`：∀ {α : Type u_1} {β : Type u_2} {E
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Meas
ureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …
-/
theorem Integrable.of_comp_fst [SFinite μ] {f : α → E} (hf : Integrable (f ·.1) (μ.prod ν))
    (hν : ν ≠ 0) : Integrable f μ :=
  hf.swap.of_comp_snd hν
/-
**MeasureTheory.Integrable.comp_snd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [MeasureT
heory.IsFiniteMeasure μ] {f : β → E},   μ ≠ 0 → (MeasureTheory.Integrable (fun x
 => f x.2) (μ.prod ν) ↔ MeasureTheory.Integrable f ν)
参数：MeasureTheory.Integrable (fun x => f x.2) (μ.prod ν) ↔ MeasureTheory.Integrab
le f ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_comp_snd`：∀ {α : Type u_1} {β : Type u_2} {E
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Meas
ureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {E : 
Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ν : Measure
Theory.Measure β} [inst…
-/
theorem Integrable.comp_snd_iff [IsFiniteMeasure μ] {f : β → E} (hμ : μ ≠ 0) :
    Integrable (f ·.2) (μ.prod ν) ↔ Integrable f ν :=
  ⟨(.of_comp_snd · hμ), (.comp_snd · μ)⟩

omit [SFinite ν] in
/-
**MeasureTheory.Integrable.comp_fst_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite μ]   [MeasureT
heory.IsFiniteMeasure ν] {f : α → E},   ν ≠ 0 → (MeasureTheory.Integrable (fun x
 => f x.1) (μ.prod ν) ↔ MeasureTheory.Integrable f μ)
参数：MeasureTheory.Integrable (fun x => f x.1) (μ.prod ν) ↔ MeasureTheory.Integrab
le f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_comp_fst`：∀ {α : Type u_1} {β : Type u_2} {E
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Meas
ureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {E : 
Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measure
Theory.Measure α} [inst…
-/
theorem Integrable.comp_fst_iff [SFinite μ] [IsFiniteMeasure ν] {f : α → E} (hν : ν ≠ 0) :
    Integrable (f ·.1) (μ.prod ν) ↔ Integrable f μ :=
  ⟨(.of_comp_fst · hν), (.comp_fst · ν)⟩

end

variable [NormedSpace ℝ E]

/-
**MeasureTheory.Integrable.integral_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [inst_4 :
 NormedSpace ℝ E] ⦃f : α × β → E⦄,   MeasureTheory.Integrable f (μ.prod ν) → Mea
sureTheory.Integrable (fun x => ∫ (y : β), f (x, y) ∂ν) μ
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.integral_norm_prod_left`：∀ {α : Type u_1} {β : 
Type u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]
   {μ : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`：MeasureTheory.A
EStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace Real E] ⦃f : α
 × β -> E⦄ (hf : AEStronglyMeasurable f (μ.pr…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem Integrable.integral_prod_left ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ := by
  apply Integrable.mono hf.integral_norm_prod_left hf.aestronglyMeasurable.integral_prod_right'
  filter_upwards with x
  grw [norm_integral_le_integral_norm]
  exact le_abs_self _
/-
**MeasureTheory.Integrable.integral_prod_right** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   {μ : MeasureTheory.Measure α} {ν : MeasureTheory.
Measure β} [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν]   [inst_4 :
 NormedSpace ℝ E] [MeasureTheory.SFinite μ] ⦃f : α × β → E⦄,   MeasureTheory.Int
egrable f (μ.prod ν) → MeasureTheory.Integrable (fun y => ∫ (x : α), f (x, y) ∂μ
) ν
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …
-/
theorem Integrable.integral_prod_right [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
  hf.swap.integral_prod_left

/-! ### The Bochner integral on a product -/

variable [SFinite μ]

/-
**MeasureTheory.integral_prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod_swap (f : α × β -> E) : ∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂
μ.prod ν
参数：f : α × β -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem integral_prod_swap (f : α × β → E) :
    ∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν :=
  measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _
/-
**MeasureTheory.setIntegral_prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_prod_swap (s : Set α) (t : Set β) (f : α × β -> E) : ∫ (z : β 
× α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν
参数：s : Set α；t : Set β；f : α × β -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.integral_prod_swap`：integral_prod_swap (f : α × β -> E) : 
∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
-/
theorem setIntegral_prod_swap (s : Set α) (t : Set β) (f : α × β → E) :
    ∫ (z : β × α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν := by
  rw [← Measure.prod_restrict, ← Measure.prod_restrict, integral_prod_swap]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/


/-- Integrals commute with addition inside another integral. `F` can be any function. -/
/-
**MeasureTheory.integral_fn_integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_fn_integral_add ⦃f g : α × β -> E⦄ (F : E -> E') (hf : Integrable
 f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫ x, F (∫ y, f (x, y) + g (x, y
) ∂ν) ∂μ) = ∫ x, F ((∫ y, f (x, y) ∂ν) + ∫ y, g (x, y) ∂ν) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.prod_right_ae`：∀ {α : Type u_1} {β : Type u_2} 
{E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Me
asureTheory.Measure α} {ν : …
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

--- 原说明 ---
Integrals commute with addition inside another integral. `F` can be any function
.
-/
theorem integral_fn_integral_add ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) + ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_add h2f h2g]

/-- Integrals commute with subtraction inside another integral.
  `F` can be any measurable function. -/
/-
**MeasureTheory.integral_fn_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_fn_integral_sub ⦃f g : α × β -> E⦄ (F : E -> E') (hf : Integrable
 f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫ x, F (∫ y, f (x, y) - g (x, y
) ∂ν) ∂μ) = ∫ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.prod_right_ae`：∀ {α : Type u_1} {β : Type u_2} 
{E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Me
asureTheory.Measure α} {ν : …
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

--- 原说明 ---
Integrals commute with subtraction inside another integral.
  `F` can be any measurable function.
-/
theorem integral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/-- Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function. -/
/-
**MeasureTheory.lintegral_fn_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_fn_integral_sub ⦃f g : α × β -> E⦄ (F : E -> Real>=0∞) (hf : Int
egrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫⁻ x, F (∫ y, f (x, y) -
 g (x, y) ∂ν) ∂μ) = ∫⁻ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.prod_right_ae`：∀ {α : Type u_1} {β : Type u_2} 
{E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Me
asureTheory.Measure α} {ν : …
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

--- 原说明 ---
Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function.
-/
theorem lintegral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → ℝ≥0∞) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫⁻ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/-- Double integrals commute with addition. -/
/-
**MeasureTheory.integral_integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_integral_add ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) (h
g : Integrable g (μ.prod ν)) : (∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ) = (∫ x, ∫ y
, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_fn_integral_add`：integral_fn_integral_add ⦃f g : 
α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.p
rod ν)) : (∫ x, F (∫ y, f (x…
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …

--- 原说明 ---
Double integrals commute with addition.
-/
theorem integral_integral_add ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_add id hf hg).trans <|
    integral_add hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with addition. This is the version with `(f + g) (x, y)`
  (instead of `f (x, y) + g (x, y)`) in the LHS. -/
/-
**MeasureTheory.integral_integral_add'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_integral_add' ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) (
hg : Integrable g (μ.prod ν)) : (∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f 
(x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_integral_add`：integral_integral_add ⦃f g : α × β 
-> E⦄ (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫ x, ∫ y,
 f (x, y) + g (x, y) ∂ν ∂…

--- 原说明 ---
Double integrals commute with addition. This is the version with `(f + g) (x, y)
`
  (instead of `f (x, y) + g (x, y)`) in the LHS.
-/
theorem integral_integral_add' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_add hf hg

/-- Double integrals commute with subtraction. -/
/-
**MeasureTheory.integral_integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_integral_sub ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) (h
g : Integrable g (μ.prod ν)) : (∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ) = (∫ x, ∫ y
, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_fn_integral_sub`：integral_fn_integral_sub ⦃f g : 
α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.p
rod ν)) : (∫ x, F (∫ y, f (x…
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …

--- 原说明 ---
Double integrals commute with subtraction.
-/
theorem integral_integral_sub ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  (integral_fn_integral_sub id hf hg).trans <|
    integral_sub hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with subtraction. This is the version with `(f - g) (x, y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS. -/
/-
**MeasureTheory.integral_integral_sub'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_integral_sub' ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) (
hg : Integrable g (μ.prod ν)) : (∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f 
(x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_integral_sub`：integral_integral_sub ⦃f g : α × β 
-> E⦄ (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫ x, ∫ y,
 f (x, y) - g (x, y) ∂ν ∂…

--- 原说明 ---
Double integrals commute with subtraction. This is the version with `(f - g) (x,
 y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS.
-/
theorem integral_integral_sub' ⦃f g : α × β → E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_sub hf hg

/-- The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous. -/
/-
**MeasureTheory.continuous_integral_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：continuous_integral_integral : Continuous fun f : α × β ->₁[μ.prod ν] E =>
 ∫ x, ∫ y, f (x, y) ∂ν ∂μ
该定理/引理给出了一组等式。
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
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_fn_integral_sub`：lintegral_fn_integral_sub ⦃f g 
: α × β -> E⦄ (F : E -> Real>=0∞) (hf : Integrable f (μ.prod ν)) (hg : Integrabl
e g (μ.prod ν)) : (∫⁻ x, F (∫…
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
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
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
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous.
-/
theorem continuous_integral_integral :
    Continuous fun f : α × β →₁[μ.prod ν] E => ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_prod_left.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_prod_left) ?_
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : α × β →₁[μ.prod ν] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id

/-- **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in integrable.
  `MeasureTheory.Integrable.integral_prod_right` is useful to show that the inner integral
  of the right-hand side is integrable. -/
/-
**MeasureTheory.integral_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod (f : α × β -> E) (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂
μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
参数：f : α × β -> E；hf : Integrable f (μ.prod ν)。
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
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `MeasureTheory.Measure.ae_measure_lt_top`：ae_measure_lt_top {s : Set (α ×
 β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s != ∞) : forallᵐ x ∂μ, ν (Prod.mk
 x ⁻¹' s) < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.integral_add'`：integral_add' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_integral_add'`：integral_integral_add' ⦃f g : α × 
β -> E⦄ (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν)) : (∫ x, ∫ 
y, (f + g) (x, y) ∂ν ∂μ) =…
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
· 使用定理 `MeasureTheory.continuous_integral_integral`：continuous_integral_integral
 : Continuous fun f : α × β ->₁[μ.prod ν] E => ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in i
ntegrable.
  `MeasureTheory.Integrable.integral_prod_right` is useful to show that the inne
r integral
  of the right-hand side is integrable.
-/
theorem integral_prod (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp only [integral, dif_neg hE]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs h2s.ne)]
    rw [Measure.prod_apply hs]
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf; convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

/-- Symmetric version of **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order. -/
/-
**MeasureTheory.integral_prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod_symm (f : α × β -> E) (hf : Integrable f (μ.prod ν)) : ∫ z, 
f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν
参数：f : α × β -> E；hf : Integrable f (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_swap`：integral_prod_swap (f : α × β -> E) : 
∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …

--- 原说明 ---
Symmetric version of **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order.
-/
theorem integral_prod_symm (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  rw [← integral_prod_swap f]; exact integral_prod _ hf.swap

/-- Reversed version of **Fubini's Theorem**. -/
/-
**MeasureTheory.integral_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_integral {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.prod ν
)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂μ.prod ν
参数：hf : Integrable (uncurry f) (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ

--- 原说明 ---
Reversed version of **Fubini's Theorem**.
-/
theorem integral_integral {f : α → β → E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂μ.prod ν :=
  (integral_prod _ hf).symm

/-- Reversed version of **Fubini's Theorem** (symmetric version). -/
/-
**MeasureTheory.integral_integral_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_integral_symm {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.p
rod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂ν.prod μ
参数：hf : Integrable (uncurry f) (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_symm`：integral_prod_symm (f : α × β -> E) (h
f : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν
· 使用定理 `MeasureTheory.Integrable.swap`：∀ {α : Type u_1} {β : Type u_2} {E : Type
 u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : MeasureTheo
ry.Measure α} {ν : …

--- 原说明 ---
Reversed version of **Fubini's Theorem** (symmetric version).
-/
theorem integral_integral_symm {f : α → β → E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂ν.prod μ :=
  (integral_prod_symm _ hf.swap).symm

/-- Change the order of Bochner integration. -/
/-
**MeasureTheory.integral_integral_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_integral_swap ⦃f : α -> β -> E⦄ (hf : Integrable (uncurry f) (μ.p
rod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_integral`：integral_integral {f : α -> β -> E} (hf
 : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂
μ.prod ν
· 使用定理 `MeasureTheory.integral_prod_symm`：integral_prod_symm (f : α × β -> E) (h
f : Integrable f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν

--- 原说明 ---
Change the order of Bochner integration.
-/
theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  (integral_integral hf).trans (integral_prod_symm _ hf)

/-- Change the order of integration, when one of the integrals is an interval integral. -/
/-
**MeasureTheory.intervalIntegral_integral_swap** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：intervalIntegral_integral_swap {a b : Real} {f : Real -> α -> E} (h_int : 
Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) : ∫ x in a..b,
 ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ
参数：h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `Set.uIoc_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoc a b = Set.Ioc b a
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ

--- 原说明 ---
Change the order of integration, when one of the integrals is an interval integr
al.
-/
lemma intervalIntegral_integral_swap {a b : ℝ} {f : ℝ → α → E}
    (h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ := by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int, integral_neg]

/-- Change the order of integration for interval integrals. -/
/-
**MeasureTheory.intervalIntegral_intervalIntegral_swap** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：intervalIntegral_intervalIntegral_swap {F : Real -> Real -> E} {a b c d : 
Real} (h : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)) : ∫ x in a..b, ∫ y in 
c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y
参数：h : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.intervalIntegral_eq_integral_uIoc`：intervalIntegral_eq_
integral_uIoc (f : Real -> E) (a b : Real) (μ : Measure Real) : ∫ x in a..b, f x
 ∂μ = (if a <= b then 1 else -1 : Real) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.intervalIntegral_integral_swap`：intervalIntegral_integral_
swap {a b : Real} {f : Real -> α -> E} (h_int : Integrable (uncurry f) ((volume.
restrict (Set.uIoc a b)).prod μ)) …
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.integrable_swap_iff`：integrable_swap_iff [SFinite μ] {f : 
α × β -> E} : Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν)
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `intervalIntegral.integral_smul`：∀ {𝕜 : Type u_2} {E : Type u_5} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ}   {μ : MeasureTheory.
Measure ℝ} [inst_2 :…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Change the order of integration for interval integrals.
-/
lemma intervalIntegral_intervalIntegral_swap {F : ℝ → ℝ → E} {a b c d : ℝ}
    (h : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, ← intervalIntegral_integral_swap,
    ← intervalIntegral.integral_smul]
  · simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  · rwa [← integrable_swap_iff, Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]

/-- **Fubini's Theorem** for set integrals. -/
/-
**MeasureTheory.setIntegral_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_prod (f : α × β -> E) {s : Set α} {t : Set β} (hf : Integrable
On f (s ×ˢ t) (μ.prod ν)) : ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f
 (x, y) ∂ν ∂μ
参数：f : α × β -> E；hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…

--- 原说明 ---
**Fubini's Theorem** for set integrals.
-/
theorem setIntegral_prod (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ := by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf
/-
**MeasureTheory.integral_prod_bilin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod_bilin {E F G 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [N
ormedSpace Real E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [N
ormedSpace Real F] [NormedSpace 𝕜 F] [CompleteSpace F] [NormedAddCommGroup G] [N
ormedSpace Real G] [NormedSpace 𝕜 G] [CompleteSpace G] (B : E ->L[𝕜] F ->L[𝕜] G)
 {f : α -> E} {g : β -> F} (hf : Integrable f μ) (hg : Integrable g ν) : ∫ z, B 
(f z.1) (g z.2) ∂μ.prod ν = B (∫ x, f x ∂μ) (∫ y, g y ∂ν)
参数：B : E ->L[𝕜] F ->L[𝕜] G；hf : Integrable f μ；hg : Integrable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Integrable.op_fst_snd`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measu
reTheory.Measure α} {ν : …
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_prod_bilin {E F G 𝕜 : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (B : E →L[𝕜] F →L[𝕜] G) {f : α → E} {g : β → F}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ z, B (f z.1) (g z.2) ∂μ.prod ν = B (∫ x, f x ∂μ) (∫ y, g y ∂ν) := by
  have : Integrable (fun z ↦ B (f z.1) (g z.2)) (μ.prod ν) :=
    hf.op_fst_snd (by fun_prop) ⟨‖B‖, B.le_opNorm₂⟩ hg
  simp_rw [integral_prod _ this, ContinuousLinearMap.integral_comp_comm _ hg]
  change ∫ x, B.flip (∫ y, g y ∂ν) (f x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hf]
  simp
/-
**MeasureTheory.integral_prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : α -> 𝕜) (
g : β -> E) : ∫ z, f z.1 • g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) • ∫ y, g y ∂ν
参数：f : α -> 𝕜；g : β -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Integrable.smul_prod`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measur
eTheory.Measure α} {ν : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem integral_prod_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : α → 𝕜) (g : β → E) :
    ∫ z, f z.1 • g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) • ∫ y, g y ∂ν := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases h : Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_smul, integral_smul_const]
  have H : ¬Integrable f μ ∨ ¬Integrable g ν := by
    contrapose! h
    exact h.1.smul_prod h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]
/-
**MeasureTheory.integral_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_prod_mul {L : Type*} [RCLike L] (f : α -> L) (g : β -> L) : ∫ z, 
f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν
参数：f : α -> L；g : β -> L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_prod_smul`：integral_prod_smul {𝕜 : Type*} [RCLike
 𝕜] [NormedSpace 𝕜 E] (f : α -> 𝕜) (g : β -> E) : ∫ z, f z.1 • g z.2 ∂μ.prod ν =
 (∫ x, f x ∂μ) • ∫ y, …
-/
theorem integral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) :
    ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν :=
  integral_prod_smul f g
/-
**MeasureTheory.setIntegral_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_prod_mul {L : Type*} [RCLike L] (f : α -> L) (g : β -> L) (s :
 Set α) (t : Set β) : ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ
) * ∫ y in t, g y ∂ν
参数：f : α -> L；g : β -> L；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
-/
theorem setIntegral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) (s : Set α)
    (t : Set β) :
    ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν := by
  rw [← Measure.prod_restrict s t]
  apply integral_prod_mul
/-
**MeasureTheory.integral_fun_snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_fun_snd (f : β -> E) : ∫ z, f z.2 ∂μ.prod ν = μ.real univ • ∫ y, 
f y ∂ν
参数：f : β -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.integral_prod_smul`：integral_prod_smul {𝕜 : Type*} [RCLike
 𝕜] [NormedSpace 𝕜 E] (f : α -> 𝕜) (g : β -> E) : ∫ z, f z.1 • g z.2 ∂μ.prod ν =
 (∫ x, f x ∂μ) • ∫ y, …
-/
theorem integral_fun_snd (f : β → E) : ∫ z, f z.2 ∂μ.prod ν = μ.real univ • ∫ y, f y ∂ν := by
  simpa using integral_prod_smul (1 : α → ℝ) f
/-
**MeasureTheory.integral_fun_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_fun_fst (f : α -> E) : ∫ z, f z.1 ∂μ.prod ν = ν.real univ • ∫ x, 
f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_swap`：integral_prod_swap (f : α × β -> E) : 
∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν
· 使用定理 `MeasureTheory.integral_fun_snd`：integral_fun_snd (f : β -> E) : ∫ z, f z
.2 ∂μ.prod ν = μ.real univ • ∫ y, f y ∂ν
-/
theorem integral_fun_fst (f : α → E) : ∫ z, f z.1 ∂μ.prod ν = ν.real univ • ∫ x, f x ∂μ := by
  rw [← integral_prod_swap]
  apply integral_fun_snd

section ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {mG : MeasurableSpace G}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]
  {L : E × F →L[ℝ] G}

/-
**MeasureTheory.integrable_continuousLinearMap_prod'** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：integrable_continuousLinearMap_prod' (hLμ : Integrable (L.comp (.inl Real 
E F)) μ) (hLν : Integrable (L.comp (.inr Real E F)) ν) : Integrable L (μ.prod ν)
参数：hLμ : Integrable (L.comp (.inl Real E F)) μ；hLν : Integrable (L.comp (.inr Re
al E F)) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {E : 
Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ : Measure
Theory.Measure α} [inst…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Integrable.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {E : 
Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ν : Measure
Theory.Measure β} [inst…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma integrable_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl ℝ E F)) μ) (hLν : Integrable (L.comp (.inr ℝ E F)) ν) :
    Integrable L (μ.prod ν) := by
  change Integrable (fun v ↦ L v) (μ.prod ν)
  simp_rw [← L.comp_inl_add_comp_inr]
  exact (hLμ.comp_fst ν).add (hLν.comp_snd μ)
/-
**MeasureTheory.integrable_continuousLinearMap_prod** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：integrable_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrabl
e id ν) : Integrable L (μ.prod ν)
参数：hμ : Integrable id μ；hν : Integrable id ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_continuousLinearMap_prod'`：integrable_continuou
sLinearMap_prod' (hLμ : Integrable (L.comp (.inl Real E F)) μ) (hLν : Integrable
 (L.comp (.inr Real E F)) ν) : Integrabl…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
lemma integrable_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    Integrable L (μ.prod ν) :=
  integrable_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

variable [CompleteSpace G]
/-
**MeasureTheory.integral_continuousLinearMap_prod'** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：integral_continuousLinearMap_prod' (hLμ : Integrable (L.comp (.inl Real E 
F)) μ) (hLν : Integrable (L.comp (.inr Real E F)) ν) : ∫ p, L p ∂(μ.prod ν) = ∫ 
x, L.comp (.inl Real E F) x ∂μ + ∫ y, L.comp (.inr Real E F) y ∂ν
参数：hLμ : Integrable (L.comp (.inl Real E F)) μ；hLν : Integrable (L.comp (.inr Re
al E F)) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.MemLp.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_prod`：integral_prod (f : α × β -> E) (hf : Integr
able f (μ.prod ν)) : ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl ℝ E F)) μ) (hLν : Integrable (L.comp (.inr ℝ E F)) ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl ℝ E F) x ∂μ + ∫ y, L.comp (.inr ℝ E F) y ∂ν := by
  simp_rw [← L.comp_inl_add_comp_inr]
  replace hLμ := ((memLp_one_iff_integrable.mpr hLμ).comp_fst ν).integrable le_rfl
  replace hLν := ((memLp_one_iff_integrable.mpr hLν).comp_snd μ).integrable le_rfl
  rw [integral_add hLμ hLν, integral_prod _ hLμ, integral_prod _ hLν]
  simp
/-
**MeasureTheory.integral_continuousLinearMap_prod** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable 
id ν) : ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl Real E F) x ∂μ + ∫ y, L.comp (.
inr Real E F) y ∂ν
参数：hμ : Integrable id μ；hν : Integrable id ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_continuousLinearMap_prod'`：integral_continuousLin
earMap_prod' (hLμ : Integrable (L.comp (.inl Real E F)) μ) (hLν : Integrable (L.
comp (.inr Real E F)) ν) : ∫ p, L p ∂(…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
-/
lemma integral_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl ℝ E F) x ∂μ + ∫ y, L.comp (.inr ℝ E F) y ∂ν :=
  integral_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

end ContinuousLinearMap

section

variable {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/-- A version of *Fubini theorem* for continuous functions with compact support: one may swap
the order of integration with respect to locally finite measures. One does not assume that the
measures are σ-finite, contrary to the usual Fubini theorem. -/
/-
**MeasureTheory.integral_integral_swap_of_hasCompactSupport** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：integral_integral_swap_of_hasCompactSupport {f : X -> Y -> E} (hf : Contin
uous f.uncurry) (h'f : HasCompactSupport f.uncurry) {μ : Measure X} {ν : Measure
 Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] : ∫ x, (∫ y, f x
 y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν
参数：hf : Continuous f.uncurry；h'f : HasCompactSupport f.uncurry。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`：setIntegr
al_eq_integral_of_forall_compl_eq_zero (h : forall x, x ∉ s -> f x = 0) : ∫ x in
 s, f x ∂μ = ∫ x, f x ∂μ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `HasCompactSupport.stronglyMeasurable_of_prod`：∀ {α : Type u_1} {X : Type
 u_5} {Y : Type u_6} [inst : Zero α] [inst_1 : TopologicalSpace X]   [inst_2 : T
opologicalSpace Y] [inst_3 : Measu…
· 使用引理 `Continuous.bounded_above_of_compact_support`：Continuous.bounded_above_of
_compact_support (hf : Continuous f) (h : HasCompactSupport f) : exists C, foral
l x, ‖f x‖ <= C
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A version of *Fubini theorem* for continuous functions with compact support: one
 may swap
the order of integration with respect to locally finite measures. One does not a
ssume that the
measures are σ-finite, contrary to the usual Fubini theorem.
-/
lemma integral_integral_swap_of_hasCompactSupport
    {f : X → Y → E} (hf : Continuous f.uncurry) (h'f : HasCompactSupport f.uncurry)
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
    contrapose! hy
    have : (x, y) ∈ Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    have : ∀ y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) ∈ Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ p, ‖f.uncurry p‖ ≤ C := hf.bounded_above_of_compact_support h'f
    exact .of_bounded (C := C) (.of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)
    have : ∀ x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) ∈ Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)
    contrapose! hx
    have : (x, y) ∈ Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

end

end MeasureTheory

