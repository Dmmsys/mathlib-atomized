/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Patrick Massot, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# The dominated convergence theorem

This file collects various results related to the Lebesgue dominated convergence theorem
for the Bochner integral.

## Main results
- `MeasureTheory.tendsto_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for the Bochner integral
- `MeasureTheory.hasSum_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for series
- `MeasureTheory.integral_tsum`, `MeasureTheory.integral_tsum_of_summable_integral_norm`:
  the integral and `tsum`s commute, if the norms of the functions form a summable series
- `intervalIntegral.hasSum_integral_of_dominated_convergence`: the Lebesgue dominated convergence
  theorem for parametric interval integrals
- `intervalIntegral.continuous_of_dominated_interval`: continuity of the interval integral
  w.r.t. a parameter
- `intervalIntegral.continuous_primitive` and friends: primitives of interval integrable
  measurable functions are continuous

-/

public section

open MeasureTheory Metric

/-!
## The Lebesgue dominated convergence theorem for the Bochner integral
-/
section DominatedConvergenceTheorem

open Set Filter TopologicalSpace ENNReal
open scoped Topology Interval

namespace MeasureTheory

variable {α E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m : MeasurableSpace α} {μ : Measure α}

/-- **Lebesgue dominated convergence theorem** provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
/-
**MeasureTheory.tendsto_integral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_of_dominated_convergence {F : Nat -> α -> G} {f : α -> G}
 (bound : α -> Real) (F_measurable : forall n, AEStronglyMeasurable (F n) μ) (bo
und_integrable : Integrable bound μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ 
<= bound a) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : T
endsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ)
参数：bound : α -> Real；F_measurable : forall n, AEStronglyMeasurable (F n) μ；bound
_integrable : Integrable bound μ；h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bo
und a；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_of_dominated_convergence`：tendsto_setToFu
n_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {fs : Nat -> α 
-> E} {f : α -> E} (bound : α -> Real) (fs_me…

--- 原说明 ---
**Lebesgue dominated convergence theorem** provides sufficient conditions under 
which almost
  everywhere convergence of a sequence of functions implies the convergence of t
heir integrals.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral
 bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications provi
ng integrability
  is easier.
-/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound F_measurable bound_integrable h_bound h_lim

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
/-
**MeasureTheory.tendsto_integral_filter_of_dominated_convergence** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsC
ountablyGenerated] {F : ι -> α -> G} {f : α -> G} (bound : α -> Real) (hF_meas :
 forallᶠ n in l, AEStronglyMeasurable (F n) μ) (h_bound : forallᶠ n in l, forall
ᵐ a ∂μ, ‖F n a‖ <= bound a) (bound_integrable : Integrable bound μ) (h_lim : for
allᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) : Tendsto (fun n => ∫ a, F n a 
∂μ) l (𝓝 <| ∫ a, f a ∂μ)
参数：bound : α -> Real；hF_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ；h_bo
und : forallᶠ n in l, forallᵐ a ∂μ, ‖F n a‖ <= bound a；bound_integrable : Integr
able bound μ；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…

--- 原说明 ---
Lebesgue dominated convergence theorem for filters with a countable basis
-/
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} {f : α → G} (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
    bound hF_meas h_bound bound_integrable h_lim

/-- Lebesgue dominated convergence theorem for series. -/
/-
**MeasureTheory.hasSum_integral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι -> α -> 
G} {f : α -> G} (bound : ι -> α -> Real) (hF_meas : forall n, AEStronglyMeasurab
le (F n) μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a) (bound_summ
able : forallᵐ a ∂μ, Summable fun n => bound n a) (bound_integrable : Integrable
 (fun a => ∑' n, bound n a) μ) (h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f
 a)) : HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ)
参数：bound : ι -> α -> Real；hF_meas : forall n, AEStronglyMeasurable (F n) μ；h_bou
nd : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a；bound_summable : forallᵐ a ∂μ,
 Summable fun n => bound n a；bound_integrable : Integrable (fun a => ∑' n, bound
 n a) μ；h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.hasSum_setToFun_of_dominated_convergence`：hasSum_setToFun_
of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι} [Countable ι]
 {F : ι -> α -> E} {f : α -> E} (bound : ι -…

--- 原说明 ---
Lebesgue dominated convergence theorem for series.
-/
theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → α → G} {f : α → G}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) := by
  simp only [integral_eq_setToFun]
  exact hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable
    bound_integrable h_lim
/-
**MeasureTheory.integral_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_tsum {ι} [Countable ι] {f : ι -> α -> G} (hf : forall i, AEStrong
lyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞) : ∫ a, ∑' i, f i 
a ∂μ = ∑' i, ∫ a, f i a ∂μ
参数：hf : forall i, AEStronglyMeasurable (f i) μ；hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ
 != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.setToFun_tsum`：setToFun_tsum [CompleteSpace E] (hT : Domin
atedFinMeasAdditive μ T C) {ι} [Countable ι] {f : ι -> α -> E} (hf : forall i, A
EStronglyMeasurab…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_tsum {ι} [Countable ι] {f : ι → α → G} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ ≠ ∞) :
    ∫ a, ∑' i, f i a ∂μ = ∑' i, ∫ a, f i a ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp only [integral_eq_setToFun]
  exact setToFun_tsum _ hf hf'
/-
**MeasureTheory.hasSum_integral_of_summable_integral_norm** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι -> α ->
 E} (hF_int : forall i : ι, Integrable (F i) μ) (hF_sum : Summable fun i => ∫ a,
 ‖F i a‖ ∂μ) : HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ)
参数：hF_int : forall i : ι, Integrable (F i) μ；hF_sum : Summable fun i => ∫ a, ‖F 
i a‖ ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_tsum`：integral_tsum {ι} [Countable ι] {f : ι -> α
 -> G} (hf : forall i, AEStronglyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a : α, ‖f i
 a‖ₑ ∂μ != ∞) : ∫…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `Summable.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommGroup α] [i
nst_1 : LinearOrder α] [IsOrderedAddMonoid α]   [inst_3 : UniformSpace α] [IsUni
fo…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 33 条，此处仅展示前 30 条）
-/
lemma hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ) := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i ↦ (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i ↦ norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs
/-
**MeasureTheory.integral_tsum_of_summable_integral_norm** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι -> α -> E
} (hF_int : forall i : ι, Integrable (F i) μ) (hF_sum : Summable fun i => ∫ a, ‖
F i a‖ ∂μ) : ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ
参数：hF_int : forall i : ι, Integrable (F i) μ；hF_sum : Summable fun i => ∫ a, ‖F 
i a‖ ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `MeasureTheory.hasSum_integral_of_summable_integral_norm`：hasSum_integral
_of_summable_integral_norm {ι} [Countable ι] {F : ι -> α -> E} (hF_int : forall 
i : ι, Integrable (F i) μ) (hF_sum : Summable…
-/
lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

/-- Corollary of the Lebesgue dominated convergence theorem: If a sequence of functions `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwise to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` converge
to the integral of `f`. -/
/-
**MeasureTheory.tendsto_integral_filter_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountably
Generated] {F : ι -> α -> G} [IsFiniteMeasure μ] {f : α -> G} (h_meas : forallᶠ 
n in l, AEStronglyMeasurable (F n) μ) (h_bound : exists C, forallᶠ n in l, (fora
llᵐ ω ∂μ, ‖F n ω‖ <= C)) (h_lim : forallᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f
 ω))) : Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ))
参数：h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ；h_bound : exists C, for
allᶠ n in l, (forallᵐ ω ∂μ, ‖F n ω‖ <= C)；h_lim : forallᵐ ω ∂μ, Tendsto (fun n =
> F n ω) l (𝓝 (f ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_norm_le_const`：tendsto_setToFun
_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ T C) {ι} {l : Filter ι
} [l.IsCountablyGenerated] {F : ι -> α -> E}…

--- 原说明 ---
Corollary of the Lebesgue dominated convergence theorem: If a sequence of functi
ons `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwis
e to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` c
onverge
to the integral of `f`.
-/
theorem tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} [IsFiniteMeasure μ] {f : α → G}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C, ∀ᶠ n in l, (∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C))
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ)) := by
  simp only [integral_eq_setToFun]
  exact tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

end MeasureTheory

section TendstoMono

variable {α E : Type*} [MeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ → Set α}
  {f : α → E}

/-
**_root_.Antitone.tendsto_setIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.Antitone.tendsto_setIntegral (hsm : forall i, MeasurableSet (s i)) 
(h_anti : Antitone s) (hfi : IntegrableOn f (s 0) μ) : Tendsto (fun i => ∫ a in 
s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ))
参数：hsm : forall i, MeasurableSet (s i)；h_anti : Antitone s；hfi : IntegrableOn f 
(s 0) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.tendsto_setIntegral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti zero_le)).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [h_anti zero_le]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

end TendstoMono

/-!
## The Lebesgue dominated convergence theorem for interval integrals
As an application, we show continuity of parametric integrals.
-/
namespace intervalIntegral

section DCT

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ}

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
nonrec theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → ℝ → E} (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ‖F n x‖ ≤ bound x)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc,
    ← ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact tendsto_const_nhds.smul <|
    tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim

/-
**intervalIntegral._root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continu
ousOn** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    {l : Filter ι} [l.IsCountablyGenerated] {F : ι → ℝ → E}
    [IsLocallyFiniteMeasure μ] (hF : ∀ᶠ i in l, ContinuousOn (F i) [[a, b]])
    (h_lim : TendstoUniformlyOn F f l [[a, b]]) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rcases isCompact_uIcc.bddAbove_image (h_lim.continuousOn hF.frequently).norm with ⟨C, hC⟩
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ ↦ C + 1)
  case hF_meas =>
    exact hF.mono fun i hi ↦ hi.mono uIoc_subset_uIcc |>.aestronglyMeasurable measurableSet_uIoc
  case h_bound =>
    have := uniformContinuous_norm.comp_tendstoUniformlyOn h_lim
      |>.eventually_forall_le (show C < C + 1 by simp) (by simpa [upperBounds] using hC)
    exact this.mono fun i hi ↦ .of_forall fun x hx ↦ hi x <| uIoc_subset_uIcc hx
  case bound_integrable =>
    exact intervalIntegrable_const
  case h_lim =>
    exact .of_forall fun x hx ↦ h_lim.tendsto_at <| uIoc_subset_uIcc hx

/-- Lebesgue dominated convergence theorem for parametric interval integrals. -/
nonrec theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → ℝ → E}
    (bound : ι → ℝ → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F n t‖ ≤ bound n t)
    (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → Summable fun n => bound n t)
    (bound_integrable : IntervalIntegrable (fun t => ∑' n, bound n t) μ a b)
    (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc, ←
    ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact
    (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable bound_integrable
          h_lim).const_smul
      _

/-- Interval integrals commute with countable sums, when the supremum norms are summable (a
special case of the dominated convergence theorem). -/
/-
**intervalIntegral.hasSum_intervalIntegral_of_summable_norm** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：hasSum_intervalIntegral_of_summable_norm [Countable ι] {f : ι -> C(Real, E
)} (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ :
 Compacts Real)‖) : HasSum (fun i : ι => ∫ x in a..b, f i x) (∫ x in a..b, ∑' i 
: ι, f i x)
参数：Real, E；hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_
uIcc⟩ : Compacts Real)‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `intervalIntegral.hasSum_integral_of_dominated_convergence`：∀ {E : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f : ℝ → 
E}   {μ : MeasureTheory.Measure ℝ} {ι : Type u_…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `intervalIntegrable_const`：intervalIntegrable_const [IsLocallyFiniteMeasu
re μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `ContinuousMap.summable_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommMonoid β]   [in
st_3 : ContinuousA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Interval integrals commute with countable sums, when the supremum norms are summ
able (a
special case of the dominated convergence theorem).
-/
theorem hasSum_intervalIntegral_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    HasSum (fun i : ι => ∫ x in a..b, f i x) (∫ x in a..b, ∑' i : ι, f i x) := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : ℝ) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x
/-
**intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm** 是 Mathlib 中的一个定理，
位于命名空间 `intervalIntegral`。
形式化陈述：tsum_intervalIntegral_eq_of_summable_norm [Countable ι] {f : ι -> C(Real, 
E)} (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ 
: Compacts Real)‖) : ∑' i : ι, ∫ x in a..b, f i x = ∫ x in a..b, ∑' i : ι, f i x
参数：Real, E；hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_
uIcc⟩ : Compacts Real)‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `intervalIntegral.hasSum_intervalIntegral_of_summable_norm`：hasSum_interv
alIntegral_of_summable_norm [Countable ι] {f : ι -> C(Real, E)} (hf_sum : Summab
le fun i : ι => ‖(f i).restrict (⟨uIcc a b, isC…
-/
theorem tsum_intervalIntegral_eq_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    ∑' i : ι, ∫ x in a..b, f i x = ∫ x in a..b, ∑' i : ι, f i x :=
  (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- Continuity of interval integral with respect to a parameter, at a point within a set.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a function integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(fun x ↦ F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
/-
**intervalIntegral.continuousWithinAt_of_dominated_interval** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：continuousWithinAt_of_dominated_interval {F : X -> Real -> E} {x₀ : X} {bo
und : Real -> Real} {a b : Real} {s : Set X} (hF_meas : forallᶠ x in 𝓝[s] x₀, AE
StronglyMeasurable (F x) (μ.restrict <| Ι a b)) (h_bound : forallᶠ x in 𝓝[s] x₀,
 forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t) (bound_integrable : IntervalInt
egrable bound μ a b) (h_cont : forallᵐ t ∂μ, t in Ι a b -> ContinuousWithinAt (f
un x => F x t) s x₀) : ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀
参数：hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a
 b)；h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound
 t；bound_integrable : IntervalIntegrable bound μ a b；h_cont : forallᵐ t ∂μ, t in
 Ι a b -> ContinuousWithinAt (fun x => F x t) s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {
f : ℝ → E}   {μ : MeasureTheory.Measure ℝ} {ι : Type u_…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated

--- 原说明 ---
Continuity of interval integral with respect to a parameter, at a point within a
 set.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a fun
ction integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(fun 
x ↦ F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`.
-/
theorem continuousWithinAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    {s : Set X} (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousWithinAt (fun x => F x t) s x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(fun x ↦ F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
/-
**intervalIntegral.continuousAt_of_dominated_interval** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：continuousAt_of_dominated_interval {F : X -> Real -> E} {x₀ : X} {bound : 
Real -> Real} {a b : Real} (hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F
 x) (μ.restrict <| Ι a b)) (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ, t in Ι a 
b -> ‖F x t‖ <= bound t) (bound_integrable : IntervalIntegrable bound μ a b) (h_
cont : forallᵐ t ∂μ, t in Ι a b -> ContinuousAt (fun x => F x t) x₀) : Continuou
sAt (fun x => ∫ t in a..b, F x t ∂μ) x₀
参数：hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b)
；h_bound : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t；bou
nd_integrable : IntervalIntegrable bound μ a b；h_cont : forallᵐ t ∂μ, t in Ι a b
 -> ContinuousAt (fun x => F x t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {
f : ℝ → E}   {μ : MeasureTheory.Measure ℝ} {ι : Type u_…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated

--- 原说明 ---
Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(fun x ↦ F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`.
-/
theorem continuousAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousAt (fun x => F x t) x₀) :
    ContinuousAt (fun x => ∫ t in a..b, F x t ∂μ) x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter.
  Given `F : X → ℝ → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `x`.
  If `(fun x ↦ F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
/-
**intervalIntegral.continuous_of_dominated_interval** 是 Mathlib 中的一个定理，位于命名空间 `i
ntervalIntegral`。
形式化陈述：continuous_of_dominated_interval {F : X -> Real -> E} {bound : Real -> Rea
l} {a b : Real} (hF_meas : forall x, AEStronglyMeasurable (F x) <| μ.restrict <|
 Ι a b) (h_bound : forall x, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t) (bo
und_integrable : IntervalIntegrable bound μ a b) (h_cont : forallᵐ t ∂μ, t in Ι 
a b -> Continuous fun x => F x t) : Continuous fun x => ∫ t in a..b, F x t ∂μ
参数：hF_meas : forall x, AEStronglyMeasurable (F x) <| μ.restrict <| Ι a b；h_bound
 : forall x, forallᵐ t ∂μ, t in Ι a b -> ‖F x t‖ <= bound t；bound_integrable : I
ntervalIntegrable bound μ a b；h_cont : forallᵐ t ∂μ, t in Ι a b -> Continuous fu
n x => F x t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `intervalIntegral.continuousAt_of_dominated_interval`：continuousAt_of_dom
inated_interval {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real} {a b : Real
} (hF_meas : forallᶠ x in 𝓝 x₀, AEStrongl…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
Continuity of interval integral with respect to a parameter.
  Given `F : X → ℝ → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `
x`.
  If `(fun x ↦ F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`.
-/
theorem continuous_of_dominated_interval {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) <| μ.restrict <| Ι a b)
    (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → Continuous fun x => F x t) :
    Continuous fun x => ∫ t in a..b, F x t ∂μ :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
        bound_integrable <|
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

end DCT

section ContinuousPrimitive

open scoped Interval

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
  {a b b₀ b₁ b₂ : ℝ} {μ : Measure ℝ} {f : ℝ → E}

set_option backward.isDefEq.respectTransparency.types false in
/-
**intervalIntegral.continuousWithinAt_primitive** 是 Mathlib 中的一个定理，位于命名空间 `inter
valIntegral`。
形式化陈述：continuousWithinAt_primitive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrabl
e f μ (min a b₁) (max a b₂)) : ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ)
 (Icc b₁ b₂) b₀
参数：hb₀ : μ {b₀} = 0；h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `IntervalIntegrable.mono_set`：mono_set (hf : IntervalIntegrable f μ a b) 
(h : [[c, d]] subseteq [[a, b]]) : IntervalIntegrable f μ c d
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `Set.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ 
in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `min_le_of_left_le`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, b 
≤ a → min b c ≤ a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `ContinuousWithinAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {
f g : X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `intervalIntegral.integral_indicator`：∀ {E : Type u_5} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {f : ℝ → E} {μ : MeasureTheory.Measure ℝ}
   {a₁ a₂ a₃ : ℝ}, a₂ ∈ S…
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `IntervalIntegrable.norm`：norm {f : Real -> E} (h : IntervalIntegrable f 
μ a b) : IntervalIntegrable (‖f ·‖) μ a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `intervalIntegral.continuousWithinAt_of_dominated_interval`：continuousWit
hinAt_of_dominated_interval {F : X -> Real -> E} {x₀ : X} {bound : Real -> Real}
 {a b : Real} {s : Set X} (hF_meas : forallᶠ x …
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
（共 66 条，此处仅展示前 30 条）
-/
theorem continuousWithinAt_primitive (hb₀ : μ {b₀} = 0)
    (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) :
    ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ) (Icc b₁ b₂) b₀ := by
  by_cases h₀ : b₀ ∈ Icc b₁ b₂
  · have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
      · exact ⟨min_le_of_left_le <| (min_le_right _ _).trans h₁,
          le_max_of_le_right <| h₂.trans <| le_max_right _ _⟩
    have : ∀ b ∈ Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x ≤ b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff, Measure.restrict_restrict, uIoc, Iic_def,
        Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]
/-
**intervalIntegral.continuousAt_parametric_primitive_of_dominated** 是 Mathlib 中的
一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：continuousAt_parametric_primitive_of_dominated [FirstCountableTopology X] 
{F : X -> Real -> E} (bound : Real -> Real) (a b : Real) {a₀ b₀ : Real} {x₀ : X}
 (hF_meas : forall x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b)) (h_bound
 : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ <= bound t) (bound
_integrable : IntervalIntegrable bound μ a b) (h_cont : forallᵐ t ∂μ.restrict <|
 Ι a b, ContinuousAt (fun x => F x t) x₀) (ha₀ : a₀ in Ioo a b) (hb₀ : b₀ in Ioo
 a b) (hμb₀ : μ {b₀} = 0) 
参数：bound : Real -> Real；a b : Real；hF_meas : forall x, AEStronglyMeasurable (F x
) (μ.restrict <| Ι a b)；h_bound : forallᶠ x in 𝓝 x₀, forallᵐ t ∂μ.restrict <| Ι 
a b, ‖F x t‖ <= bound t；bound_integrable : IntervalIntegrable bound μ a b；h_cont
 : forallᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x => F x t) x₀；ha₀ : a₀ in 
Ioo a b；hb₀ : b₀ in Ioo a b；hμb₀ : μ {b₀} = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.OrdConnected.uIoc_subset`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 : Set α},   s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIoc x y
 ⊆ s
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用引理 `Set.Ioc_subset_uIoc`：Ioc_subset_uIoc : Ioc a b subseteq Ι a b
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `IntervalIntegrable.mono_fun'`：mono_fun' {f : Real -> E} {g : Real -> Rea
l} (hg : IntervalIntegrable g μ a b) (hfm : AEStronglyMeasurable f (μ.restrict (
Ι a b))) (hle : (f…
· 使用定理 `IntervalIntegrable.mono_set_ae`：mono_set_ae (hf : IntervalIntegrable f μ
 a b) (h : Ι c d <=ᵐ[μ] Ι a b) : IntervalIntegrable f μ c d
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_set`：mono_set {s t} (h : s subse
teq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) : AEStronglyMeasurable[m]
 f (μ.restrict s)
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
（共 104 条，此处仅展示前 30 条）
-/
theorem continuousAt_parametric_primitive_of_dominated [FirstCountableTopology X]
    {F : X → ℝ → E} (bound : ℝ → ℝ) (a b : ℝ)
    {a₀ b₀ : ℝ} {x₀ : X} (hF_meas : ∀ x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x ↦ F x t) x₀) (ha₀ : a₀ ∈ Ioo a b)
    (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
    ContinuousAt (fun p : X × ℝ ↦ ∫ t : ℝ in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) := by
  have hsub : ∀ {a₀ b₀}, a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → Ι a₀ b₀ ⊆ Ι a b := fun ha₀ hb₀ ↦
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b ∈ 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x₀ t‖ ≤ bound t := h_bound.self_of_nhds
  have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
    dsimp
    have hiF : ∀ {x a₀ b₀},
        (∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t) → a₀ ∈ Ioo a b → b₀ ∈ Ioo a b →
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ ↦
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub, add_assoc, add_sub_cancel,
      intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x ↦ (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx ↦
            ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
          (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀) <|
          ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t ↦ ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × ℝ ↦ ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ ≤ |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
      have H : ∀ᵐ t : ℝ ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ ≤ 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ ≤ 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

variable [NullSingletonClass μ]
/-
**intervalIntegral.continuousOn_primitive** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：continuousOn_primitive (h_int : IntegrableOn f (Icc a b) μ) : ContinuousOn
 (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b)
参数：h_int : IntegrableOn f (Icc a b) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuousOn_congr`：continuousOn_congr (h' : EqOn g f s) : ContinuousOn 
g s ↔ ContinuousOn f s
· 使用定理 `intervalIntegral.continuousWithinAt_primitive`：continuousWithinAt_primit
ive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) : 
ContinuousWithinAt (fun b => ∫ x in…
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `continuousOn_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalS
pace α] [inst_1 : TopologicalSpace β] (f : α → β), ContinuousOn f ∅
-/
theorem continuousOn_primitive (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b) := by
  by_cases h : a ≤ b
  · have : ∀ x ∈ Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _
/-
**intervalIntegral.continuousOn_primitive_Icc** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：continuousOn_primitive_Icc (h_int : IntegrableOn f (Icc a b) μ) : Continuo
usOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b)
参数：h_int : IntegrableOn f (Icc a b) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ioc`：integral_Icc_eq_integral_Ioc
 : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.continuousOn_primitive`：continuousOn_primitive (h_int :
 IntegrableOn f (Icc a b) μ) : ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (I
cc a b)
-/
theorem continuousOn_primitive_Icc (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b) := by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

/-- Note: this assumes that `f` is `IntervalIntegrable`, in contrast to some other lemmas here. -/
/-
**intervalIntegral.continuousOn_primitive_interval'** 是 Mathlib 中的一个定理，位于命名空间 `i
ntervalIntegral`。
形式化陈述：continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂) (h
a : a in [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x ∂μ) [[b₁, b₂]]
参数：h_int : IntervalIntegrable f μ b₁ b₂；ha : a in [[b₁, b₂]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.continuousWithinAt_primitive`：continuousWithinAt_primit
ive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) : 
ContinuousWithinAt (fun b => ∫ x in…
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b

--- 原说明 ---
Note: this assumes that `f` is `IntervalIntegrable`, in contrast to some other l
emmas here.
-/
theorem continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂)
    (ha : a ∈ [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x ∂μ) [[b₁, b₂]] := fun _ _ ↦ by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1, max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int
/-
**intervalIntegral.continuousOn_primitive_interval** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：continuousOn_primitive_interval (h_int : IntegrableOn f (uIcc a b) μ) : Co
ntinuousOn (fun x => ∫ t in a..x, f t ∂μ) (uIcc a b)
参数：h_int : IntegrableOn f (uIcc a b) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.continuousOn_primitive_interval'`：continuousOn_primitiv
e_interval' (h_int : IntervalIntegrable f μ b₁ b₂) (ha : a in [[b₁, b₂]]) : Cont
inuousOn (fun b => ∫ x in a..b, f x ∂μ)…
· 使用定理 `MeasureTheory.IntegrableOn.intervalIntegrable`：MeasureTheory.IntegrableO
n.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) : IntervalIntegrable f μ a
 b
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
-/
theorem continuousOn_primitive_interval (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in a..x, f t ∂μ) (uIcc a b) :=
  continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc
/-
**intervalIntegral.continuousOn_primitive_interval_left** 是 Mathlib 中的一个定理，位于命名空
间 `intervalIntegral`。
形式化陈述：continuousOn_primitive_interval_left (h_int : IntegrableOn f (uIcc a b) μ)
 : ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (uIcc a b)
参数：h_int : IntegrableOn f (uIcc a b) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `intervalIntegral.continuousOn_primitive_interval`：continuousOn_primitive
_interval (h_int : IntegrableOn f (uIcc a b) μ) : ContinuousOn (fun x => ∫ t in 
a..x, f t ∂μ) (uIcc a b)
-/
theorem continuousOn_primitive_interval_left (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (uIcc a b) := by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg
/-
**intervalIntegral.continuous_primitive** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：continuous_primitive (h_int : forall a b, IntervalIntegrable f μ a b) (a :
 Real) : Continuous fun b => ∫ x in a..b, f x ∂μ
参数：h_int : forall a b, IntervalIntegrable f μ a b；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `intervalIntegral.continuousWithinAt_primitive`：continuousWithinAt_primit
ive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) : 
ContinuousWithinAt (fun b => ∫ x in…
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem continuous_primitive (h_int : ∀ a b, IntervalIntegrable f μ a b) (a : ℝ) :
    Continuous fun b => ∫ x in a..b, f x ∂μ := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : ℝ) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

variable [IsLocallyFiniteMeasure μ] {f : X → ℝ → E}
/-
**intervalIntegral.continuous_parametric_primitive_of_continuous** 是 Mathlib 中的一
个定理，位于命名空间 `intervalIntegral`。
形式化陈述：continuous_parametric_primitive_of_continuous {a₀ : Real} (hf : Continuous
 f.uncurry) : Continuous fun p : X × Real => ∫ t in a₀..p.2, f p.1 t ∂μ
参数：hf : Continuous f.uncurry。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.continuousAt_iff'`：continuousAt_iff' [TopologicalSpace β] {f : β 
-> α} {b : β} : ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, dist (f x) (f
 b) < ε
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsCompact.bddAbove_image`：IsCompact.bddAbove_image [ClosedIciTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddAbove (…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 166 条，此处仅展示前 30 条）
-/
theorem continuous_parametric_primitive_of_continuous
    {a₀ : ℝ} (hf : Continuous f.uncurry) :
    Continuous fun p : X × ℝ ↦ ∫ t in a₀..p.2, f p.1 t ∂μ := by
  -- We will prove continuity at a point `(q, b₀)`.
  rw [continuous_iff_continuousAt]
  rintro ⟨q, b₀⟩
  apply Metric.continuousAt_iff'.2 (fun ε εpos ↦ ?_)
  -- choose `a` and `b` such that `(a, b)` contains both `a₀` and `b₀`. We will use uniform
  -- estimates on a neighborhood of the compact set `{q} × [a, b]`.
  obtain ⟨a, a_lt⟩ := exists_lt (min a₀ b₀)
  obtain ⟨b, lt_b⟩ := exists_gt (max a₀ b₀)
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have : IsCompact ({q} ×ˢ (Icc a b)) := isCompact_singleton.prod isCompact_Icc
  -- let `M` be a bound for `f` on the compact set `{q} × [a, b]`.
  obtain ⟨M, hM⟩ := this.bddAbove_image hf.norm.continuousOn
  -- let `δ` be small enough to satisfy several properties that will show up later.
  obtain ⟨δ, δpos, hδ, h'δ, h''δ⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 1 ∧ Icc (b₀ - δ) (b₀ + δ) ⊆ Icc a b ∧
      (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have B : ∀ᶠ δ in 𝓝 0, Icc (b₀ - δ) (b₀ + δ) ⊆ Icc a b := by
      have I : Tendsto (fun δ ↦ b₀ - δ) (𝓝 0) (𝓝 (b₀ - 0)) := tendsto_const_nhds.sub tendsto_id
      have J : Tendsto (fun δ ↦ b₀ + δ) (𝓝 0) (𝓝 (b₀ + 0)) := tendsto_const_nhds.add tendsto_id
      simp only [sub_zero, add_zero] at I J
      filter_upwards [(tendsto_order.1 I).1 _ a_lt.2, (tendsto_order.1 J).2 _ lt_b.2] with δ hδ h'δ
      exact Icc_subset_Icc hδ.le h'δ.le
    have C : ∀ᶠ δ in 𝓝 0,
        (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
      suffices Tendsto
        (fun δ ↦ (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b))
          (𝓝 0) (𝓝 ((M + 1) * (0 : ℝ≥0∞).toReal + 0 * μ.real (Icc a b))) by
        simp only [toReal_zero, mul_zero, zero_mul, add_zero] at this
        exact (tendsto_order.1 this).2 _ εpos
      apply Tendsto.add (Tendsto.mul tendsto_const_nhds _)
        (Tendsto.mul tendsto_id tendsto_const_nhds)
      exact (tendsto_toReal zero_ne_top).comp (tendsto_measure_Icc _ _)
    rcases (A.and ((B.and C).filter_mono nhdsWithin_le_nhds)).exists with ⟨δ, hδ, h'δ, h''δ⟩
    exact ⟨δ, hδ.1, hδ.2, h'δ, h''δ⟩
  -- By compactness of `[a, b]` and continuity of `f` there, if `p` is close enough to `q`
  -- then `f p x` is `δ`-close to `f q x`, uniformly in `x ∈ [a, b]`.
  -- (Note in particular that this implies a bound `M + δ ≤ M + 1` for `f p x`).
  obtain ⟨v, v_mem, hv⟩ : ∃ v ∈ 𝓝[univ] q, ∀ p ∈ v, ∀ x ∈ Icc a b, dist (f p x) (f q x) < δ :=
    IsCompact.mem_uniformity_of_prod isCompact_Icc hf.continuousOn (mem_univ _)
      (dist_mem_uniformity δpos)
  -- for `p` in this neighborhood and `s` which is `δ`-close to `b₀`, we will show that the
  -- integrals are `ε`-close.
  have : v ×ˢ (Ioo (b₀ - δ) (b₀ + δ)) ∈ 𝓝 (q, b₀) := by
    rw [nhdsWithin_univ] at v_mem
    simp only [prod_mem_nhds_iff, v_mem, true_and]
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [this]
  rintro ⟨p, s⟩ ⟨hp : p ∈ v, hs : s ∈ Ioo (b₀ - δ) (b₀ + δ)⟩
  simp only [dist_eq_norm] at hv ⊢
  have J r u v : IntervalIntegrable (f r) μ u v := (hf.uncurry_left _).intervalIntegrable _ _
  /- we compute the difference between the integrals by splitting the contribution of the change
  from `b₀` to `s` (which gives a contribution controlled by the measure of `(b₀ - δ, b₀ + δ)`,
  small enough thanks to our choice of `δ`) and the change from `q` to `p`, which is small as
  `f p x` and `f q x` are uniformly close by design. -/
  calc
  ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖
    = ‖(∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ)
        + (∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ)‖ := by congr 1; abel
  _ ≤ ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ‖
        + ‖∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖ := norm_add_le _ _
  _ = ‖∫ t in b₀..s, f p t ∂μ‖ + ‖∫ t in a₀..b₀, (f p t - f q t) ∂μ‖ := by
      congr 2
      · rw [integral_interval_sub_left (J _ _ _) (J _ _ _)]
      · rw [integral_sub (J _ _ _) (J _ _ _)]
  _ ≤ ∫ t in Ι b₀ s, ‖f p t‖ ∂μ + ∫ t in Ι a₀ b₀, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact norm_integral_le_integral_norm_uIoc
      · exact norm_integral_le_integral_norm_uIoc
  _ ≤ ∫ t in Icc (b₀ - δ) (b₀ + δ), ‖f p t‖ ∂μ + ∫ t in Icc a b, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact Eventually.of_forall (fun x ↦ norm_nonneg _)
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · apply uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ⟨hs.1.le, hs.2.le⟩ )
        simp [δpos.le]
      · exact Eventually.of_forall (fun x ↦ norm_nonneg _)
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨a_lt.1.le, lt_b.1.le⟩ ⟨a_lt.2.le, lt_b.2.le⟩)
  _ ≤ ∫ t in Icc (b₀ - δ) (b₀ + δ), M + 1 ∂μ + ∫ _t in Icc a b, δ ∂μ := by
      gcongr with x hx x hx
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · calc ‖f p x‖ = ‖f q x + (f p x - f q x)‖ := by congr; abel
        _ ≤ ‖f q x‖ + ‖f p x - f q x‖ := norm_add_le _ _
        _ ≤ M + δ := by
            gcongr
            · apply hM
              change (fun x ↦ ‖Function.uncurry f x‖) (q, x) ∈ _
              apply mem_image_of_mem
              simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
              exact h'δ hx
            · exact le_of_lt (hv _ hp _ (h'δ hx))
        _ ≤ M + 1 := by linarith
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · exact le_of_lt (hv _ hp _ hx)
  _ = (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) := by simp [mul_comm]
  _ < ε := h''δ

@[fun_prop]
/-
**intervalIntegral.continuous_parametric_intervalIntegral_of_continuous** 是 Math
lib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：continuous_parametric_intervalIntegral_of_continuous {a₀ : Real} (hf : Con
tinuous f.uncurry) {s : X -> Real} (hs : Continuous s) : Continuous fun x => ∫ t
 in a₀..s x, f x t ∂μ
参数：hf : Continuous f.uncurry；hs : Continuous s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `intervalIntegral.continuous_parametric_primitive_of_continuous`：continuo
us_parametric_primitive_of_continuous {a₀ : Real} (hf : Continuous f.uncurry) : 
Continuous fun p : X × Real => ∫ t in a₀..p.2, f p.1…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_parametric_intervalIntegral_of_continuous {a₀ : ℝ}
    (hf : Continuous f.uncurry) {s : X → ℝ} (hs : Continuous s) :
    Continuous fun x ↦ ∫ t in a₀..s x, f x t ∂μ :=
  show Continuous ((fun p : X × ℝ ↦ ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x ↦ (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs
/-
**intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'** 是 Mat
hlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：continuous_parametric_intervalIntegral_of_continuous' (hf : Continuous f.u
ncurry) (a₀ b₀ : Real) : Continuous fun x => ∫ t in a₀..b₀, f x t ∂μ
参数：hf : Continuous f.uncurry；a₀ b₀ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`：c
ontinuous_parametric_intervalIntegral_of_continuous {a₀ : Real} (hf : Continuous
 f.uncurry) {s : X -> Real} (hs : Continuous s) : Continuou…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_parametric_intervalIntegral_of_continuous'
    (hf : Continuous f.uncurry) (a₀ b₀ : ℝ) :
    Continuous fun x ↦ ∫ t in a₀..b₀, f x t ∂μ := by fun_prop

end ContinuousPrimitive

end intervalIntegral

namespace MeasureTheory

namespace IntegrableOn

open intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E}

/-
**MeasureTheory.IntegrableOn.continuousWithinAt_Ici_primitive_Ioi** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousWithinAt_Ici_primitive_Ioi {a₀ : Real} (hf : IntegrableOn f (Ioi
 a₀) μ) : ContinuousWithinAt (fun b => ∫ x in Ioi b, f x ∂μ) (Ici a₀) a₀
参数：hf : IntegrableOn f (Ioi a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `Set.indicator_le_indicator_of_subset`：∀ {α : Type u_2} {M : Type u_3} [i
nst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M},   s ⊆ t → 0 ≤ f →
 s.indicator f ≤ t.indicat…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 37 条，此处仅展示前 30 条）
-/
theorem continuousWithinAt_Ici_primitive_Ioi {a₀ : ℝ} (hf : IntegrableOn f (Ioi a₀) μ) :
    ContinuousWithinAt (fun b ↦ ∫ x in Ioi b, f x ∂μ) (Ici a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence ((Ioi a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact (hf.mono_set (Ioi_subset_Ioi ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Ioi_subset_Ioi (by grind)) (fun a ↦ norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Ioi] using! hf.norm
  · refine ae_of_all _ fun x ↦ ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : a₀ < x <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind
/-
**MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousOn_Ici_primitive_Ioi [NullSingletonClass μ] {a₀ : Real} (hf : In
tegrableOn f (Ioi a₀) μ) : ContinuousOn (fun b => ∫ x in Ioi b, f x ∂μ) (Ici a₀)
参数：hf : IntegrableOn f (Ioi a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuous_left_right`：continuousWithinAt_iff_con
tinuous_left_right {a : α} {f : α -> β} : ContinuousWithinAt f s a ↔ ContinuousW
ithinAt f (s inter Iic a) a ∧ Cont…
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_Ioi_sub_Ioi`：integral_Ioi_sub_Ioi (hf : Integr
ableOn f (Ioi a) μ) (hab : a <= b) : ∫ x in Ioi a, f x ∂μ - ∫ x in Ioi b, f x ∂μ
 = ∫ x in a..b, f x ∂μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.continuousWithinAt_primitive`：continuousWithinAt_primit
ive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) : 
ContinuousWithinAt (fun b => ∫ x in…
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ici_inter_Ici`：∀ {α : Type u_1} [inst : SemilatticeSup α] {a b : α},
 Set.Ici a ∩ Set.Ici b = Set.Ici (a ⊔ b)
· 使用定理 `MeasureTheory.IntegrableOn.continuousWithinAt_Ici_primitive_Ioi`：continu
ousWithinAt_Ici_primitive_Ioi {a₀ : Real} (hf : IntegrableOn f (Ioi a₀) μ) : Con
tinuousWithinAt (fun b => ∫ x in Ioi b, f x ∂μ) (Ici …
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
-/
theorem continuousOn_Ici_primitive_Ioi [NullSingletonClass μ] {a₀ : ℝ}
    (hf : IntegrableOn f (Ioi a₀) μ) : ContinuousOn (fun b ↦ ∫ x in Ioi b, f x ∂μ) (Ici a₀) := by
  intro a (ha : a₀ ≤ a)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · rw [Ici_inter_Iic]
    have h_int : IntervalIntegrable f μ a₀ a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 <| hf.mono_set Ioc_subset_Ioi_self
    have h_split : ∀ b ∈ Icc a₀ a, ∫ x in Ioi b, f x ∂μ =
        (∫ x in Ioi a₀, f x ∂μ) - ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [← integral_Ioi_sub_Ioi hf hb.1]
    have h_cwa : ContinuousWithinAt (fun b ↦ ∫ x in a₀..b, f x ∂μ) (Icc a₀ a) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.sub h_cwa).congr h_split (h_split a (right_mem_Icc.2 ha))
  · simpa [ha] using (hf.mono_set (Ioi_subset_Ioi ha)).continuousWithinAt_Ici_primitive_Ioi
/-
**MeasureTheory.IntegrableOn.continuousWithinAt_Iic_primitive_Iio** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousWithinAt_Iic_primitive_Iio {a₀ : Real} (hf : IntegrableOn f (Iio
 a₀) μ) : ContinuousWithinAt (fun b => ∫ x in Iio b, f x ∂μ) (Iic a₀) a₀
参数：hf : IntegrableOn f (Iio a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `Set.indicator_le_indicator_of_subset`：∀ {α : Type u_2} {M : Type u_3} [i
nst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M},   s ⊆ t → 0 ≤ f →
 s.indicator f ≤ t.indicat…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 37 条，此处仅展示前 30 条）
-/
theorem continuousWithinAt_Iic_primitive_Iio {a₀ : ℝ} (hf : IntegrableOn f (Iio a₀) μ) :
    ContinuousWithinAt (fun b ↦ ∫ x in Iio b, f x ∂μ) (Iic a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Iio]
  apply tendsto_integral_filter_of_dominated_convergence ((Iio a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iio]
    exact (hf.mono_set (Iio_subset_Iio ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Iio_subset_Iio (by grind)) (fun a ↦ norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Iio] using! hf.norm
  · refine ae_of_all _ fun x ↦ ?_
    simp only [indicator_apply, mem_Iio]
    by_cases hx : x < a₀ <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind
/-
**MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iio** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousOn_Iic_primitive_Iio [NullSingletonClass μ] {a₀ : Real} (hf : In
tegrableOn f (Iio a₀) μ) : ContinuousOn (fun b => ∫ x in Iio b, f x ∂μ) (Iic a₀)
参数：hf : IntegrableOn f (Iio a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuous_left_right`：continuousWithinAt_iff_con
tinuous_left_right {a : α} {f : α -> β} : ContinuousWithinAt f s a ↔ ContinuousW
ithinAt f (s inter Iic a) a ∧ Cont…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Iic_inter_Iic`：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a 
⊓ b)
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `MeasureTheory.IntegrableOn.continuousWithinAt_Iic_primitive_Iio`：continu
ousWithinAt_Iic_primitive_Iio {a₀ : Real} (hf : IntegrableOn f (Iio a₀) μ) : Con
tinuousWithinAt (fun b => ∫ x in Iio b, f x ∂μ) (Iic …
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `Set.Iic_inter_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ic a ∩ Set.Ici b = Set.Icc b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff_integrableOn_Ico_of_le`：intervalIntegrable_iff_in
tegrableOn_Ico_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_Iio_sub_Iio'`：integral_Iio_sub_Iio' [NullSingl
etonClass μ] (hf : IntegrableOn f (Iio b) μ) (hg : IntegrableOn f (Iio a) μ) : ∫
 x in Iio b, f x ∂μ - ∫ x in…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.continuousWithinAt_primitive`：continuousWithinAt_primit
ive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) : 
ContinuousWithinAt (fun b => ∫ x in…
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `ContinuousWithinAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {
f g : X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 33 条，此处仅展示前 30 条）
-/
theorem continuousOn_Iic_primitive_Iio [NullSingletonClass μ] {a₀ : ℝ}
    (hf : IntegrableOn f (Iio a₀) μ) : ContinuousOn (fun b ↦ ∫ x in Iio b, f x ∂μ) (Iic a₀) := by
  intro a (ha : a ≤ a₀)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · simpa [ha] using (hf.mono_set (Iio_subset_Iio ha)).continuousWithinAt_Iic_primitive_Iio
  · rw [Iic_inter_Ici]
    have h_int : IntervalIntegrable f μ a a₀ :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le ha).2 <| hf.mono_set Ico_subset_Iio_self
    have h_split : ∀ b ∈ Icc a a₀, ∫ x in Iio b, f x ∂μ =
        (∫ x in Iio a₀, f x ∂μ) + ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [integral_symm b a₀, ← integral_Iio_sub_Iio' hf (hf.mono_set (Iio_subset_Iio hb.2))]
    have h_cwa : ContinuousWithinAt (fun b ↦ ∫ x in a₀..b, f x ∂μ) (Icc a a₀) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.add h_cwa).congr h_split (h_split a (left_mem_Icc.2 ha))
/-
**MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ici** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousOn_Ici_primitive_Ici [NullSingletonClass μ] {a₀ : Real} (hf : In
tegrableOn f (Ici a₀) μ) : ContinuousOn (fun b => ∫ x in Ici b, f x ∂μ) (Ici a₀)
参数：hf : IntegrableOn f (Ici a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_Ici_eq_integral_Ioi`：integral_Ici_eq_integral_Ioi
 : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi`：continuousOn_
Ici_primitive_Ioi [NullSingletonClass μ] {a₀ : Real} (hf : IntegrableOn f (Ioi a
₀) μ) : ContinuousOn (fun b => ∫ x in Ioi b, f …
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem continuousOn_Ici_primitive_Ici [NullSingletonClass μ] {a₀ : ℝ}
    (hf : IntegrableOn f (Ici a₀) μ) : ContinuousOn (fun b ↦ ∫ x in Ici b, f x ∂μ) (Ici a₀) := by
  simp_rw [integral_Ici_eq_integral_Ioi]
  exact (hf.mono_set Ioi_subset_Ici_self).continuousOn_Ici_primitive_Ioi
/-
**MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iic** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IntegrableOn`。
形式化陈述：continuousOn_Iic_primitive_Iic [NullSingletonClass μ] {a₀ : Real} (hf : In
tegrableOn f (Iic a₀) μ) : ContinuousOn (fun b => ∫ x in Iic b, f x ∂μ) (Iic a₀)
参数：hf : IntegrableOn f (Iic a₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_Iic_eq_integral_Iio`：integral_Iic_eq_integral_Iio
 : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iio`：continuousOn_
Iic_primitive_Iio [NullSingletonClass μ] {a₀ : Real} (hf : IntegrableOn f (Iio a
₀) μ) : ContinuousOn (fun b => ∫ x in Iio b, f …
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem continuousOn_Iic_primitive_Iic [NullSingletonClass μ] {a₀ : ℝ}
    (hf : IntegrableOn f (Iic a₀) μ) : ContinuousOn (fun b ↦ ∫ x in Iic b, f x ∂μ) (Iic a₀) := by
  simp_rw [integral_Iic_eq_integral_Iio]
  exact (hf.mono_set Iio_subset_Iic_self).continuousOn_Iic_primitive_Iio

end IntegrableOn

end MeasureTheory

end DominatedConvergenceTheorem

