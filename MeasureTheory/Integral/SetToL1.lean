/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Extension of a linear function from indicators to L1

Given `T : Set α → E →L[ℝ] F` with `DominatedFinMeasAdditive μ T C`, we construct an extension
of `T` to integrable simple functions, which are finite sums of indicators of measurable sets
with finite measure, then to integrable functions, which are limits of integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`.
This extension process is used to define the Bochner integral
in the `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` file,
the conditional expectation of an integrable function
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean`,
and the integral with respect to a vector measure
in `Mathlib/MeasureTheory/VectorMeasure/Integral.lean`.

## Main definitions

- `setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `setToFun μ T (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Properties

For most properties of `setToFun`, we provide two lemmas. One version uses hypotheses valid on
all sets, like `T = T'`, and a second version which uses a primed name uses hypotheses on
measurable sets with finite measure, like `∀ s, MeasurableSet s → μ s < ∞ → T s = T' s`.

The lemmas listed here don't show all hypotheses. Refer to the actual lemmas for details.

Linearity:
- `setToFun_zero_left : setToFun μ 0 hT f = 0`
- `setToFun_add_left : setToFun μ (T + T') _ f = setToFun μ T hT f + setToFun μ T' hT' f`
- `setToFun_smul_left : setToFun μ (fun s ↦ c • (T s)) (hT.smul c) f = c • setToFun μ T hT f`
- `setToFun_zero : setToFun μ T hT (0 : α → E) = 0`
- `setToFun_neg : setToFun μ T hT (-f) = - setToFun μ T hT f`

If `f` and `g` are integrable:
- `setToFun_add : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g`
- `setToFun_sub : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g`

If `T` satisfies `∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x`:
- `setToFun_smul : setToFun μ T hT (c • f) = c • setToFun μ T hT f`

Other:
- `setToFun_congr_ae (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g`
- `setToFun_measure_zero (h : μ = 0) : setToFun μ T hT f = 0`

If the space is also an ordered additive group with an order closed topology and `T` is such that
`0 ≤ T s x` for `0 ≤ x`, we also prove order-related properties:
- `setToFun_mono_left (h : ∀ s x, T s x ≤ T' s x) : setToFun μ T hT f ≤ setToFun μ T' hT' f`
- `setToFun_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f`
- `setToFun_mono (hfg : f ≤ᵐ[μ] g) : setToFun μ T hT f ≤ setToFun μ T hT g`
-/

@[expose] public section


noncomputable section

open scoped Topology NNReal

open Set Filter TopologicalSpace ENNReal

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ μ' μ'' : Measure α}

namespace L1

open AEEqFun Lp.simpleFunc Lp

namespace SimpleFunc

/-
**MeasureTheory.L1.SimpleFunc.norm_eq_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.L1.SimpleFunc`。
形式化陈述：norm_eq_sum_mul (f : α ->₁ₛ[μ] G) : ‖f‖ = ∑ x in (toSimpleFunc f).range, μ
.real (toSimpleFunc f ⁻¹' {x}) * ‖x‖
参数：f : α ->₁ₛ[μ] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.simpleFunc.norm_toSimpleFunc`：norm_toSimpleFunc [Fact (
1 <= p)] (f : Lp.simpleFunc E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm (toSimpleFunc
 f) p μ)
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `MeasureTheory.SimpleFunc.map_apply`：map_apply (g : β -> γ) (f : α ->ₛ β)
 (a) : f.map g a = g (f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable`：measure_
preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) {x : E} (hx : 
x != 0) : μ (f ⁻¹' {x}) < ∞
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_eq_sum_mul (f : α →₁ₛ[μ] G) :
    ‖f‖ = ∑ x ∈ (toSimpleFunc f).range, μ.real (toSimpleFunc f ⁻¹' {x}) * ‖x‖ := by
  rw [norm_toSimpleFunc, eLpNorm_one_eq_lintegral_enorm]
  have h_eq := SimpleFunc.map_apply (‖·‖ₑ) (toSimpleFunc f)
  simp_rw [← h_eq, measureReal_def]
  rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.map_lintegral, ENNReal.toReal_sum]
  · congr
    ext1 x
    rw [ENNReal.toReal_mul, mul_comm, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro x _
    by_cases hx0 : x = 0
    · rw [hx0]; simp
    · finiteness [SimpleFunc.measure_preimage_lt_top_of_integrable _ (SimpleFunc.integrable f) hx0]

section SetToL1S

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

/-- Extend `Set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`. -/
/-
**MeasureTheory.L1.SimpleFunc.setToL1S** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
L1.SimpleFunc`。
形式化陈述：setToL1S (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) : F
参数：T : Set α -> E ->L[Real] F；f : α ->₁ₛ[μ] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend `Set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`.
-/
def setToL1S (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (toSimpleFunc f).setToSimpleFunc T
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_eq_setToSimpleFunc** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_eq_setToSimpleFunc (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E)
 : setToL1S T f = (toSimpleFunc f).setToSimpleFunc T
参数：T : Set α -> E ->L[Real] F；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem setToL1S_eq_setToSimpleFunc (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1S T f = (toSimpleFunc f).setToSimpleFunc T :=
  rfl

@[simp]
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_zero_left (f : α ->₁ₛ[μ] E) : setToL1S (0 : Set α -> E ->L[Real] 
F) f = 0
参数：f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_zero`：setToSimpleFunc_zero {m :
 MeasurableSpace α} (f : α ->ₛ F) : setToSimpleFunc (0 : Set α -> F ->L[Real] F'
) f = 0
-/
theorem setToL1S_zero_left (f : α →₁ₛ[μ] E) : setToL1S (0 : Set α → E →L[ℝ] F) f = 0 :=
  SimpleFunc.setToSimpleFunc_zero _
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_zero_left'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_zero_left' {T : Set α -> E ->L[Real] F} (h_zero : forall s, Measu
rableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁ₛ[μ] E) : setToL1S T f = 0
参数：h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_zero'`：setToSimpleFunc_zero' {T
 : Set α -> E ->L[Real] F'} (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T 
s = 0) (f : α ->ₛ E) (hf : Integrabl…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_zero_left' {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) : setToL1S T f = 0 :=
  SimpleFunc.setToSimpleFunc_zero' h_zero _ (SimpleFunc.integrable f)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.L1.SimpleFunc`。
形式化陈述：setToL1S_congr (T : Set α -> E ->L[Real] F) (h_zero : forall s, Measurable
Set s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) {f g : α ->₁ₛ[μ] E} (
h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) : setToL1S T f = setToL1S T g
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_congr (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    setToL1S T f = setToL1S T g :=
  SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) h
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_congr_left (T T' : Set α -> E ->L[Real] F) (h : forall s, Measura
bleSet s -> μ s < ∞ -> T s = T' s) (f : α ->₁ₛ[μ] E) : setToL1S T f = setToL1S T
' f
参数：T T' : Set α -> E ->L[Real] F；h : forall s, MeasurableSet s -> μ s < ∞ -> T s
 = T' s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr_left`：setToSimpleFunc_con
gr_left (T T' : Set α -> E ->L[Real] F) (h : forall s, MeasurableSet s -> μ s < 
∞ -> T s = T' s) (f : α ->ₛ E) (hf : Inte…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_congr_left (T T' : Set α → E →L[ℝ] F)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁ₛ[μ] E) :
    setToL1S T f = setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_congr_left T T' h (simpleFunc.toSimpleFunc f) (SimpleFunc.integrable f)

/-- `setToL1S` does not change if we replace the measure `μ` by `μ'` with `μ ≪ μ'`. The statement
uses two functions `f` and `f'` because they have to belong to different types, but morally these
are the same function (we have `f =ᵐ[μ] f'`). -/
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_congr_measure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_congr_measure {μ' : Measure α} (T : Set α -> E ->L[Real] F) (h_ze
ro : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ
 T) (hμ : μ ≪ μ') (f : α ->₁ₛ[μ] E) (f' : α ->₁ₛ[μ'] E) (h : (f : α -> E) =ᵐ[μ] 
f') : setToL1S T f = setToL1S T f'
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；hμ : μ ≪ μ'；f : α ->₁ₛ[μ] E；f' : α ->₁ₛ[μ'] E
；h : (f : α -> E) =ᵐ[μ] f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…

--- 原说明 ---
`setToL1S` does not change if we replace the measure `μ` by `μ'` with `μ ≪ μ'`. 
The statement
uses two functions `f` and `f'` because they have to belong to different types, 
but morally these
are the same function (we have `f =ᵐ[μ] f'`).
-/
theorem setToL1S_congr_measure {μ' : Measure α} (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (hμ : μ ≪ μ')
    (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E) (h : (f : α → E) =ᵐ[μ] f') :
    setToL1S T f = setToL1S T f' := by
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable f) ?_
  refine (toSimpleFunc_eq_toFun f).trans ?_
  suffices (f' : α → E) =ᵐ[μ] simpleFunc.toSimpleFunc f' from h.trans this
  have goal' : (f' : α → E) =ᵐ[μ'] simpleFunc.toSimpleFunc f' := (toSimpleFunc_eq_toFun f').symm
  exact hμ.ae_eq goal'
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_add_left (T T' : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) : setT
oL1S (T + T') f = setToL1S T f + setToL1S T' f
参数：T T' : Set α -> E ->L[Real] F；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add_left`：setToSimpleFunc_add_l
eft {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] F') {f : α ->ₛ F} : set
ToSimpleFunc (T + T') f = setToSimpleFu…
-/
theorem setToL1S_add_left (T T' : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
    setToL1S (T + T') f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left T T'
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_add_left' (T T' T'' : Set α -> E ->L[Real] F) (h_add : forall s, 
MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁ₛ[μ] E) : setToL1S T
'' f = setToL1S T f + setToL1S T' f
参数：T T' T'' : Set α -> E ->L[Real] F；h_add : forall s, MeasurableSet s -> μ s < 
∞ -> T'' s = T s + T' s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add_left'`：setToSimpleFunc_add_
left' (T T' T'' : Set α -> E ->L[Real] F) (h_add : forall s, MeasurableSet s -> 
μ s < ∞ -> T'' s = T s + T' s) {f : α ->…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_add_left' (T T' T'' : Set α → E →L[ℝ] F)
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1S T'' f = setToL1S T f + setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_add_left' T T' T'' h_add (SimpleFunc.integrable f)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_smul_left (T : Set α -> E ->L[Real] F) (c : Real) (f : α ->₁ₛ[μ] 
E) : setToL1S (fun s => c • T s) f = c • setToL1S T f
参数：T : Set α -> E ->L[Real] F；c : Real；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left`：setToSimpleFunc_smul
_left {m : MeasurableSpace α} (T : Set α -> F ->L[Real] F') (c : Real) (f : α ->
ₛ F) : setToSimpleFunc (fun s => c • T s…
-/
theorem setToL1S_smul_left (T : Set α → E →L[ℝ] F) (c : ℝ) (f : α →₁ₛ[μ] E) :
    setToL1S (fun s => c • T s) f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left T c _
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_smul_left' (T T' : Set α -> E ->L[Real] F) (c : Real) (h_smul : f
orall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s) (f : α ->₁ₛ[μ] E) : setTo
L1S T' f = c • setToL1S T f
参数：T T' : Set α -> E ->L[Real] F；c : Real；h_smul : forall s, MeasurableSet s -> 
μ s < ∞ -> T' s = c • T s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_smul_left'`：setToSimpleFunc_smu
l_left' (T T' : Set α -> E ->L[Real] F') (c : Real) (h_smul : forall s, Measurab
leSet s -> μ s < ∞ -> T' s = c • T s) {f …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_smul_left' (T T' : Set α → E →L[ℝ] F) (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1S T' f = c • setToL1S T f :=
  SimpleFunc.setToSimpleFunc_smul_left' T T' c h_smul (SimpleFunc.integrable f)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：setToL1S_add (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSe
t s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (f g : α ->₁ₛ[μ] E) : s
etToL1S T (f + g) = setToL1S T f + setToL1S T g
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；f g : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_add`：setToSimpleFunc_add (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f g : α ->ₛ E} (hf : Integ
rable f μ) (hg : Integrable g μ) :…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.Lp.simpleFunc.add_toSimpleFunc`：add_toSimpleFunc (f g : Lp
.simpleFunc E p μ) : toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g
-/
theorem setToL1S_add (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1S T (f + g) = setToL1S T f + setToL1S T g := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_add T h_add (SimpleFunc.integrable f)
      (SimpleFunc.integrable g)]
  exact
    SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _)
      (add_toSimpleFunc f g)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：setToL1S_neg {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSe
t s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (f : α ->₁ₛ[μ] E) : set
ToL1S T (-f) = -setToL1S T f
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.simpleFunc.neg_toSimpleFunc`：neg_toSimpleFunc (f : Lp.s
impleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_neg`：setToSimpleFunc_neg (T : S
et α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) {f : α ->ₛ E} (hf : Integra
ble f μ) : setToSimpleFunc T (-f) …
-/
theorem setToL1S_neg {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f : α →₁ₛ[μ] E) : setToL1S T (-f) = -setToL1S T f := by
  simp_rw [setToL1S]
  have : simpleFunc.toSimpleFunc (-f) =ᵐ[μ] ⇑(-simpleFunc.toSimpleFunc f) :=
    neg_toSimpleFunc f
  rw [SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) this]
  exact SimpleFunc.setToSimpleFunc_neg T h_add (SimpleFunc.integrable f)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：setToL1S_sub {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSe
t s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (f g : α ->₁ₛ[μ] E) : s
etToL1S T (f - g) = setToL1S T f - setToL1S T g
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；f g : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_add`：setToL1S_add (T : Set α -> E -
>L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : 
FinMeasAdditive μ T) (f g : α …
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_neg`：setToL1S_neg {T : Set α -> E -
>L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : 
FinMeasAdditive μ T) (f : α ->…
-/
theorem setToL1S_sub {T : Set α → E →L[ℝ] F} (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (f g : α →₁ₛ[μ] E) :
    setToL1S T (f - g) = setToL1S T f - setToL1S T g := by
  rw [sub_eq_add_neg, setToL1S_add T h_zero h_add, setToL1S_neg h_zero h_add, sub_eq_add_neg]
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_smul_real** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_smul_real (T : Set α -> E ->L[Real] F) (h_zero : forall s, Measur
ableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (c : Real) (f : α
 ->₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；c : Real；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_smul_real`：setToSimpleFunc_smul
_real (T : Set α -> E ->L[Real] F) (h_add : FinMeasAdditive μ T) (c : Real) {f :
 α ->ₛ E} (hf : Integrable f μ) : setToS…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.Lp.simpleFunc.smul_toSimpleFunc`：smul_toSimpleFunc (k : 𝕜)
 (f : Lp.simpleFunc E p μ) : toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f)
-/
theorem setToL1S_smul_real (T : Set α → E →L[ℝ] F)
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (c : ℝ)
    (f : α →₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul_real T h_add c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1.SimpleFunc`。
形式化陈述：setToL1S_smul [DistribSMul 𝕜 F] (T : Set α -> E ->L[Real] F) (h_zero : for
all s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (h_s
mul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α ->₁ₛ[μ] 
E) : setToL1S T (c • f) = c • setToL1S T f
参数：T : Set α -> E ->L[Real] F；h_zero : forall s, MeasurableSet s -> μ s = 0 -> T
 s = 0；h_add : FinMeasAdditive μ T；h_smul : forall c : 𝕜, forall s x, T s (c • x
) = c • T s x；c : 𝕜；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_smul`：setToSimpleFunc_smul {E} 
[NormedAddCommGroup E] [SMulZeroClass 𝕜 E] [NormedSpace Real E] [DistribSMul 𝕜 F
] (T : Set α -> E ->L[Real] F) (h_a…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.Lp.simpleFunc.smul_toSimpleFunc`：smul_toSimpleFunc (k : 𝕜)
 (f : Lp.simpleFunc E p μ) : toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f)
-/
theorem setToL1S_smul
    [DistribSMul 𝕜 F] (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α →₁ₛ[μ] E) : setToL1S T (c • f) = c • setToL1S T f := by
  simp_rw [setToL1S]
  rw [← SimpleFunc.setToSimpleFunc_smul T h_add h_smul c (SimpleFunc.integrable f)]
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact smul_toSimpleFunc c f
/-
**MeasureTheory.L1.SimpleFunc.norm_setToL1S_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.L1.SimpleFunc`。
形式化陈述：norm_setToL1S_le (T : Set α -> E ->L[Real] F) {C : Real} (hT_norm : forall
 s, MeasurableSet s -> μ s < ∞ -> ‖T s‖ <= C * μ.real s) (f : α ->₁ₛ[μ] E) : ‖se
tToL1S T f‖ <= C * ‖f‖
参数：T : Set α -> E ->L[Real] F；hT_norm : forall s, MeasurableSet s -> μ s < ∞ -> 
‖T s‖ <= C * μ.real s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S.eq_1`：∀ {α : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [in
st_2 : NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_eq_sum_mul`：norm_eq_sum_mul (f : α ->₁ₛ
[μ] G) : ‖f‖ = ∑ x in (toSimpleFunc f).range, μ.real (toSimpleFunc f ⁻¹' {x}) * 
‖x‖
· 使用定理 `MeasureTheory.SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integra
ble`：norm_setToSimpleFunc_le_sum_mul_norm_of_integrable (T : Set α -> E ->L[Real
] F') {C : Real} (hT_norm : forall s, MeasurableSet s -> μ s < ∞ …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem norm_setToL1S_le (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) (f : α →₁ₛ[μ] E) :
    ‖setToL1S T f‖ ≤ C * ‖f‖ := by
  rw [setToL1S, norm_eq_sum_mul f]
  exact
    SimpleFunc.norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm _
      (SimpleFunc.integrable f)
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_indicatorConst** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_indicatorConst {T : Set α -> E ->L[Real] F} {s : Set α} (h_zero :
 forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) 
(hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) : setToL1S T (simpleFunc.indicato
rConst 1 hs hμs.ne x) = T s x
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；hs : MeasurableSet s；hμs : μ s < ∞；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_eq_setToSimpleFunc`：setToL1S_eq_set
ToSimpleFunc (T : Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) : setToL1S T f = (to
SimpleFunc f).setToSimpleFunc T
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_indicatorConst`：toSimpleFunc_in
dicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : toSim
pleFunc (indicatorConst p hs hμs c) =ᵐ[μ] (Si…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_indicator`：setToSimpleFunc_indi
cator (T : Set α -> F ->L[Real] F') (hT_empty : T ∅ = 0) {m : MeasurableSpace α}
 {s : Set α} (hs : MeasurableSet s) (x :…
-/
theorem setToL1S_indicatorConst {T : Set α → E →L[ℝ] F} {s : Set α}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T)
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  have h_empty : T ∅ = 0 := h_zero _ MeasurableSet.empty measure_empty
  rw [setToL1S_eq_setToSimpleFunc]
  refine Eq.trans ?_ (SimpleFunc.setToSimpleFunc_indicator T h_empty hs x)
  refine SimpleFunc.setToSimpleFunc_congr T h_zero h_add (SimpleFunc.integrable _) ?_
  exact toSimpleFunc_indicatorConst hs hμs.ne x
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.L1.SimpleFunc`。
形式化陈述：setToL1S_const [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F} (h_zero : 
forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (
x : E) : setToL1S T (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_
top μ _) x) = T univ x
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_indicatorConst`：setToL1S_indicatorC
onst {T : Set α -> E ->L[Real] F} {s : Set α} (h_zero : forall s, MeasurableSet 
s -> μ s = 0 -> T s = 0) (h_add : FinMeas…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem setToL1S_const [IsFiniteMeasure μ] {T : Set α → E →L[ℝ] F}
    (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : FinMeasAdditive μ T) (x : E) :
    setToL1S T (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) = T univ x :=
  setToL1S_indicatorConst h_zero h_add MeasurableSet.univ (measure_lt_top _ _) x

section Order

variable {G'' G' : Type*}
  [NormedAddCommGroup G'] [PartialOrder G'] [IsOrderedAddMonoid G'] [NormedSpace ℝ G']
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace ℝ G'']
  {T : Set α → G'' →L[ℝ] G'}

/-
**MeasureTheory.L1.SimpleFunc.setToL1S_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_mono_left {T T' : Set α -> E ->L[Real] G''} (hTT' : forall s x, T
 s x <= T' s x) (f : α ->₁ₛ[μ] E) : setToL1S T f <= setToL1S T' f
参数：hTT' : forall s x, T s x <= T' s x；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left`：setToSimpleFunc_mono
_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] G'') (hTT' : forall s
 x, T s x <= T' s x) (f : α ->ₛ F) : set…
-/
theorem setToL1S_mono_left {T T' : Set α → E →L[ℝ] G''} (hTT' : ∀ s x, T s x ≤ T' s x)
    (f : α →₁ₛ[μ] E) : setToL1S T f ≤ setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.L1.SimpleFunc`。
形式化陈述：setToL1S_mono_left' {T T' : Set α -> E ->L[Real] G''} (hTT' : forall s, Me
asurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->₁ₛ[μ] E) : setTo
L1S T f <= setToL1S T' f
参数：hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x；f : 
α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left'`：setToSimpleFunc_mon
o_left' (T T' : Set α -> E ->L[Real] G'') (hTT' : forall s, MeasurableSet s -> μ
 s < ∞ -> forall x, T s x <= T' s x) (f :…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1S_mono_left' {T T' : Set α → E →L[ℝ] G''}
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1S T f ≤ setToL1S T' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G''] in
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.L1.SimpleFunc`。
形式化陈述：setToL1S_nonneg (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0)
 (h_add : FinMeasAdditive μ T) (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞
 -> forall x, 0 <= x -> 0 <= T s x) {f : α ->₁ₛ[μ] G''} (hf : 0 <= f) : 0 <= set
ToL1S T f
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 
0 <= T s x；hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq`：exists_simpl
eFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 <= f) : exists f' : α ->ₛ G
, 0 <= f' ∧ f =ᵐ[μ] f'
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_nonneg'`：setToSimpleFunc_nonneg
' (T : Set α -> G' ->L[Real] G'') (hT_nonneg : forall s, MeasurableSet s -> μ s 
< ∞ -> forall x, 0 <= x -> 0 <= T s x)…
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
-/
theorem setToL1S_nonneg (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G''}
    (hf : 0 ≤ f) : 0 ≤ setToL1S T f := by
  simp_rw [setToL1S]
  obtain ⟨f', hf', hff'⟩ := exists_simpleFunc_nonneg_ae_eq hf
  replace hff' : simpleFunc.toSimpleFunc f =ᵐ[μ] f' :=
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f).trans hff'
  rw [SimpleFunc.setToSimpleFunc_congr _ h_zero h_add (SimpleFunc.integrable _) hff']
  exact
    SimpleFunc.setToSimpleFunc_nonneg' T hT_nonneg _ hf' ((SimpleFunc.integrable f).congr hff')
/-
**MeasureTheory.L1.SimpleFunc.setToL1S_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1.SimpleFunc`。
形式化陈述：setToL1S_mono (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (
h_add : FinMeasAdditive μ T) (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -
> forall x, 0 <= x -> 0 <= T s x) {f g : α ->₁ₛ[μ] G''} (hfg : f <= g) : setToL1
S T f <= setToL1S T g
参数：h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0；h_add : FinMeasAddit
ive μ T；hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 
0 <= T s x；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_sub`：setToL1S_sub {T : Set α -> E -
>L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : 
FinMeasAdditive μ T) (f g : α …
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_nonneg`：setToL1S_nonneg (h_zero : f
orall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (h
T_nonneg : forall s, MeasurableSe…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `AddSubgroup.toIsOrderedAddMonoid`：∀ {G : Type u_1} [inst : AddCommGroup 
G] [inst_1 : Preorder G] [IsOrderedAddMonoid G] (H : AddSubgroup G),   IsOrdered
AddMonoid ↥H
-/
theorem setToL1S_mono (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
    (h_add : FinMeasAdditive μ T)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G''}
    (hfg : f ≤ g) : setToL1S T f ≤ setToL1S T g := by
  rw [← sub_nonneg] at hfg ⊢
  rw [← setToL1S_sub h_zero h_add]
  exact setToL1S_nonneg h_zero h_add hT_nonneg hfg

end Order

variable [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
variable (α E μ 𝕜)

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`. -/
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM' {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMea
sAdditive μ T C) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) : 
(α ->₁ₛ[μ] E) ->L[𝕜] F
参数：hT : DominatedFinMeasAdditive μ T C；h_smul : forall c : 𝕜, forall s x, T s (c
 • x) = c • T s x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`.
-/
def setToL1SCLM' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁ₛ[μ] E) →L[𝕜] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul T (fun _ => hT.eq_zero_of_measure_zero) hT.1 h_smul⟩
    C fun f => norm_setToL1S_le T hT.2 f

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`. -/
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.L1.SimpleFunc`。
形式化陈述：setToL1SCLM {T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeas
Additive μ T C) : (α ->₁ₛ[μ] E) ->L[Real] F
参数：hT : DominatedFinMeasAdditive μ T C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Extend `Set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`.
-/
def setToL1SCLM {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    (α →₁ₛ[μ] E) →L[ℝ] F :=
  LinearMap.mkContinuous
    ⟨⟨setToL1S T, setToL1S_add T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩,
      setToL1S_smul_real T (fun _ => hT.eq_zero_of_measure_zero) hT.1⟩
    C fun f => norm_setToL1S_le T hT.2 f

variable {α E μ 𝕜}
variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

@[simp]
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L
[Real] F) C) (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT f = 0
参数：hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C；f : α ->₁ₛ[μ] 
E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_zero_left`：setToL1S_zero_left (f : 
α ->₁ₛ[μ] E) : setToL1S (0 : Set α -> E ->L[Real] F) f = 0
-/
theorem setToL1SCLM_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁ₛ[μ] E) : setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left _
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_zero_left' (hT : DominatedFinMeasAdditive μ T C) (h_zero : for
all s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁ₛ[μ] E) : setToL1SCLM α 
E μ hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；h_zero : forall s, MeasurableSet s -> μ s
 < ∞ -> T s = 0；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_zero_left'`：setToL1S_zero_left' {T 
: Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s 
= 0) (f : α ->₁ₛ[μ] E) : setToL1S T f…
-/
theorem setToL1SCLM_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = 0 :=
  setToL1S_zero_left' h_zero f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_congr_left (hT : DominatedFinMeasAdditive μ T C) (hT' : Domina
tedFinMeasAdditive μ T' C') (h : T = T') (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ h
T f = setToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；h 
: T = T'；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_congr_left`：setToL1S_congr_left (T 
T' : Set α -> E ->L[Real] F) (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 
T' s) (f : α ->₁ₛ[μ] E) : setToL1S T …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem setToL1SCLM_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' (fun _ _ _ => by rw [h]) f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_congr_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : Domin
atedFinMeasAdditive μ T' C') (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 
T' s) (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；h 
: forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_congr_left`：setToL1S_congr_left (T 
T' : Set α -> E ->L[Real] F) (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = 
T' s) (f : α ->₁ₛ[μ] E) : setToL1S T …
-/
theorem setToL1SCLM_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α →₁ₛ[μ] E) : setToL1SCLM α E μ hT f = setToL1SCLM α E μ hT' f :=
  setToL1S_congr_left T T' h f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_measure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_congr_measure {μ' : Measure α} (hT : DominatedFinMeasAdditive 
μ T C) (hT' : DominatedFinMeasAdditive μ' T C') (hμ : μ ≪ μ') (f : α ->₁ₛ[μ] E) 
(f' : α ->₁ₛ[μ'] E) (h : (f : α -> E) =ᵐ[μ] f') : setToL1SCLM α E μ hT f = setTo
L1SCLM α E μ' hT' f'
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ' T C'；hμ
 : μ ≪ μ'；f : α ->₁ₛ[μ] E；f' : α ->₁ₛ[μ'] E；h : (f : α -> E) =ᵐ[μ] f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_congr_measure`：setToL1S_congr_measu
re {μ' : Measure α} (T : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableS
et s -> μ s = 0 -> T s = 0) (h_add : Fin…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setToL1SCLM_congr_measure {μ' : Measure α} (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (hμ : μ ≪ μ') (f : α →₁ₛ[μ] E) (f' : α →₁ₛ[μ'] E)
    (h : (f : α → E) =ᵐ[μ] f') : setToL1SCLM α E μ hT f = setToL1SCLM α E μ' hT' f' :=
  setToL1S_congr_measure T (fun _ => hT.eq_zero_of_measure_zero) hT.1 hμ _ _ h
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_add_left (hT : DominatedFinMeasAdditive μ T C) (hT' : Dominate
dFinMeasAdditive μ T' C') (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ (hT.add hT') f =
 setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；f 
: α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_add_left`：setToL1S_add_left (T T' :
 Set α -> E ->L[Real] F) (f : α ->₁ₛ[μ] E) : setToL1S (T + T') f = setToL1S T f 
+ setToL1S T' f
-/
theorem setToL1SCLM_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.add hT') f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left T T' f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_add_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : Dominat
edFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'') (h_add : 
forall s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁ₛ[μ] E) : 
setToL1SCLM α E μ hT'' f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
'' : DominatedFinMeasAdditive μ T'' C''；h_add : forall s, MeasurableSet s -> μ s
 < ∞ -> T'' s = T s + T' s；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_add_left'`：setToL1S_add_left' (T T'
 T'' : Set α -> E ->L[Real] F) (h_add : forall s, MeasurableSet s -> μ s < ∞ -> 
T'' s = T s + T' s) (f : α ->₁ₛ[μ] E…
-/
theorem setToL1SCLM_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT'' f = setToL1SCLM α E μ hT f + setToL1SCLM α E μ hT' f :=
  setToL1S_add_left' T T' T'' h_add f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_smul_left (c : Real) (hT : DominatedFinMeasAdditive μ T C) (f 
: α ->₁ₛ[μ] E) : setToL1SCLM α E μ (hT.smul c) f = c • setToL1SCLM α E μ hT f
参数：c : Real；hT : DominatedFinMeasAdditive μ T C；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_smul_left`：setToL1S_smul_left (T : 
Set α -> E ->L[Real] F) (c : Real) (f : α ->₁ₛ[μ] E) : setToL1S (fun s => c • T 
s) f = c • setToL1S T f
-/
theorem setToL1SCLM_smul_left (c : ℝ) (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ (hT.smul c) f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left T c f
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_smul_left' (c : Real) (hT : DominatedFinMeasAdditive μ T C) (h
T' : DominatedFinMeasAdditive μ T' C') (h_smul : forall s, MeasurableSet s -> μ 
s < ∞ -> T' s = c • T s) (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT' f = c • setTo
L1SCLM α E μ hT f
参数：c : Real；hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ
 T' C'；h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s；f : α ->₁
ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_smul_left'`：setToL1S_smul_left' (T 
T' : Set α -> E ->L[Real] F) (c : Real) (h_smul : forall s, MeasurableSet s -> μ
 s < ∞ -> T' s = c • T s) (f : α ->₁ₛ…
-/
theorem setToL1SCLM_smul_left' (c : ℝ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C')
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT' f = c • setToL1SCLM α E μ hT f :=
  setToL1S_smul_left' T T' c h_smul f
/-
**MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.L1.SimpleFunc`。
形式化陈述：norm_setToL1SCLM_le {T : Set α -> E ->L[Real] F} {C : Real} (hT : Dominate
dFinMeasAdditive μ T C) (hC : 0 <= C) : ‖setToL1SCLM α E μ hT‖ <= C
参数：hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
-/
theorem norm_setToL1SCLM_le {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : ‖setToL1SCLM α E μ hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _
/-
**MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.L1.SimpleFunc`。
形式化陈述：norm_setToL1SCLM_le' {T : Set α -> E ->L[Real] F} {C : Real} (hT : Dominat
edFinMeasAdditive μ T C) : ‖setToL1SCLM α E μ hT‖ <= max C 0
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le'`：mkContinuous_norm_le' (f : E ->ₛₗ[σ₁₂] 
F) {C : Real} (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h‖ <= max C 0
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
-/
theorem norm_setToL1SCLM_le' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1SCLM α E μ hT‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le' _ _
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_const** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_const [IsFiniteMeasure μ] {T : Set α -> E ->L[Real] F} {C : Re
al} (hT : DominatedFinMeasAdditive μ T C) (x : E) : setToL1SCLM α E μ hT (simple
Func.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) = T univ x
参数：hT : DominatedFinMeasAdditive μ T C；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_const`：setToL1S_const [IsFiniteMeas
ure μ] {T : Set α -> E ->L[Real] F} (h_zero : forall s, MeasurableSet s -> μ s =
 0 -> T s = 0) (h_add : FinMeasA…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setToL1SCLM_const [IsFiniteMeasure μ] {T : Set α → E →L[ℝ] F} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1SCLM α E μ hT (simpleFunc.indicatorConst 1 MeasurableSet.univ (measure_ne_top μ _) x) =
      T univ x :=
  setToL1S_const (fun _ => hT.eq_zero_of_measure_zero) hT.1 x

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G''] [NormedSpace ℝ G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [IsOrderedAddMonoid G'] [NormedSpace ℝ G']

/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_mono_left {T T' : Set α -> E ->L[Real] G''} {C C' : Real} (hT 
: DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (hTT'
 : forall s x, T s x <= T' s x) (f : α ->₁ₛ[μ] E) : setToL1SCLM α E μ hT f <= se
tToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s x, T s x <= T' s x；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left`：setToSimpleFunc_mono
_left {m : MeasurableSpace α} (T T' : Set α -> F ->L[Real] G'') (hTT' : forall s
 x, T s x <= T' s x) (f : α ->ₛ F) : set…
-/
theorem setToL1SCLM_mono_left {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f ≤ setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left T T' hTT' _
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_mono_left' {T T' : Set α -> E ->L[Real] G''} {C C' : Real} (hT
 : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (hTT
' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x) (f : α ->
₁ₛ[μ] E) : setToL1SCLM α E μ hT f <= setToL1SCLM α E μ hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x；f : α ->₁
ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_mono_left'`：setToSimpleFunc_mon
o_left' (T T' : Set α -> E ->L[Real] G'') (hTT' : forall s, MeasurableSet s -> μ
 s < ∞ -> forall x, T s x <= T' s x) (f :…
· 使用定理 `MeasureTheory.L1.SimpleFunc.integrable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Me
asure α}   (f : ↥(α →₁ₛ[μ] E…
-/
theorem setToL1SCLM_mono_left' {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁ₛ[μ] E) :
    setToL1SCLM α E μ hT f ≤ setToL1SCLM α E μ hT' f :=
  SimpleFunc.setToSimpleFunc_mono_left' T T' hTT' _ (SimpleFunc.integrable f)

omit [IsOrderedAddMonoid G'] in
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_nonneg {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : Domina
tedFinMeasAdditive μ T C) (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> f
orall x, 0 <= x -> 0 <= T s x) {f : α ->₁ₛ[μ] G'} (hf : 0 <= f) : 0 <= setToL1SC
LM α G' μ hT f
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_nonneg`：setToL1S_nonneg (h_zero : f
orall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (h
T_nonneg : forall s, MeasurableSe…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setToL1SCLM_nonneg {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁ₛ[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1SCLM α G' μ hT f :=
  setToL1S_nonneg (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hf
/-
**MeasureTheory.L1.SimpleFunc.setToL1SCLM_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.L1.SimpleFunc`。
形式化陈述：setToL1SCLM_mono {T : Set α -> G' ->L[Real] G''} {C : Real} (hT : Dominate
dFinMeasAdditive μ T C) (hT_nonneg : forall s, MeasurableSet s -> μ s < ∞ -> for
all x, 0 <= x -> 0 <= T s x) {f g : α ->₁ₛ[μ] G'} (hfg : f <= g) : setToL1SCLM α
 G' μ hT f <= setToL1SCLM α G' μ hT g
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_mono`：setToL1S_mono (h_zero : foral
l s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (hT_no
nneg : forall s, MeasurableSet …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setToL1SCLM_mono {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁ₛ[μ] G'}
    (hfg : f ≤ g) : setToL1SCLM α G' μ hT f ≤ setToL1SCLM α G' μ hT g :=
  setToL1S_mono (fun _ => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg hfg

end Order

end SetToL1S

end SimpleFunc

open L1.SimpleFunc

section SetToL1

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

variable (𝕜) [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F] [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜 F]
  [CompleteSpace F] {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

/-- Extend `Set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
/-
**MeasureTheory.L1.setToL1'** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1' (hT : DominatedFinMeasAdditive μ T C) (h_smul : forall c : 𝕜, for
all s x, T s (c • x) = c • T s x) : (α ->₁[μ] E) ->L[𝕜] F
参数：hT : DominatedFinMeasAdditive μ T C；h_smul : forall c : 𝕜, forall s x, T s (c
 • x) = c • T s x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Extend `Set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`.
-/
def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁[μ] E) →L[𝕜] F :=
  (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜)
/-
**MeasureTheory.L1.setToL1'_eq_setToL1SCLM** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.L1`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} (𝕜 : Type u_6) [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [
inst_3 : NormedSpace ℝ F] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [inst_4 : NormedRing 𝕜] [inst_5 : _root_.Module 𝕜 E] [inst_6 : _root_.Module 𝕜
 F] [inst_7 : IsBoundedSMul 𝕜 E]   [inst_8 : IsBoundedSMul 𝕜 F] [inst_9 : Comple
teSpace F] {T : Set α → E →L[ℝ] F} {C : ℝ}   (hT : MeasureTheory.DominatedFinMea
sAdditive μ T C)   (h_smul : ∀ (c : 𝕜) (s : Set α) (x : E), (T s) (c • x) = c • 
(T s) x) (f : ↥(α →₁ₛ[μ] E)),   (MeasureTheory.L1.setToL1' 𝕜 hT h_smul) ↑f = (Me
asureTheory.L1.SimpleFunc.setToL1SCLM α E μ hT) f
参数：𝕜 : Type u_6；hT : MeasureTheory.DominatedFinMeasAdditive μ T C；h_smul : ∀ (c 
: 𝕜) (s : Set α) (x : E), (T s) (c • x) = c • (T s) x；f : ↥(α →₁ₛ[μ] E)；MeasureT
heory.L1.setToL1' 𝕜 hT h_smul；MeasureTheory.L1.SimpleFunc.setToL1SCLM α E μ hT。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.extend_eq`：extend_eq (h_dense : DenseRange e) (h_e :
 IsUniformInducing e) (x : E) : extend f e (e x) = f x
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.Lp.simpleFunc.isUniformInducing`：isUniformInducing : IsUni
formInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
-/
theorem setToL1'_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul f = setToL1SCLM α E μ hT f := by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  · exact simpleFunc.denseRange one_ne_top

@[simp]
/-
**MeasureTheory.L1.setToL1'_apply_coeToLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.L1`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} (𝕜 : Type u_6) [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [
inst_3 : NormedSpace ℝ F] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [inst_4 : NormedRing 𝕜] [inst_5 : _root_.Module 𝕜 E] [inst_6 : _root_.Module 𝕜
 F] [inst_7 : IsBoundedSMul 𝕜 E]   [inst_8 : IsBoundedSMul 𝕜 F] [inst_9 : Comple
teSpace F] {T : Set α → E →L[ℝ] F} {C : ℝ}   (hT : MeasureTheory.DominatedFinMea
sAdditive μ T C)   (h_smul : ∀ (c : 𝕜) (s : Set α) (x : E), (T s) (c • x) = c • 
(T s) x) (f : ↥(α →₁ₛ[μ] E)),   (MeasureTheory.L1.setToL1' 𝕜 hT h_smul) ((Measur
eTheory.Lp.simpleFunc.coeToLp α E ℝ) f) =     (MeasureTheory.L1.SimpleFunc.setTo
L1SCLM α E μ hT) f
参数：𝕜 : Type u_6；hT : MeasureTheory.DominatedFinMeasAdditive μ T C；h_smul : ∀ (c 
: 𝕜) (s : Set α) (x : E), (T s) (c • x) = c • (T s) x；f : ↥(α →₁ₛ[μ] E)；MeasureT
heory.L1.setToL1' 𝕜 hT h_smul；(MeasureTheory.Lp.simpleFunc.coeToLp α E ℝ) f；Meas
ureTheory.L1.SimpleFunc.setToL1SCLM α E μ hT。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1'_eq_setToL1SCLM`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} (𝕜 : Type u_6) [inst : NormedAddCommGroup E] [inst_1 : NormedSp
ace ℝ E]   [inst_2 : NormedAdd…
-/
theorem setToL1'_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul (coeToLp α E ℝ f) = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM 𝕜 hT h_smul f

variable {𝕜}

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
/-
**MeasureTheory.L1.setToL1** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α ->₁[μ] E) ->L[Real] F
参数：hT : DominatedFinMeasAdditive μ T C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Extend `Set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`.
-/
def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (setToL1SCLM α E μ hT).extend (coeToLp α E ℝ)
/-
**MeasureTheory.L1.setToL1_eq_setToL1SCLM** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.L1`。
形式化陈述：setToL1_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ
] E) : setToL1 hT f = setToL1SCLM α E μ hT f
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1'_eq_setToL1SCLM`：∀ {α : Type u_1} {E : Type u_2
} {F : Type u_3} (𝕜 : Type u_6) [inst : NormedAddCommGroup E] [inst_1 : NormedSp
ace ℝ E]   [inst_2 : NormedAdd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT f = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM ℝ hT (by simp) _

@[simp]
/-
**MeasureTheory.L1.setToL1_apply_coeToLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.L1`。
形式化陈述：setToL1_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ]
 E) : setToL1 hT (coeToLp α E Real f) = setToL1SCLM α E μ hT f
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁ₛ[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
-/
theorem setToL1_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT (coeToLp α E ℝ f) = setToL1SCLM α E μ hT f :=
  setToL1_eq_setToL1SCLM hT f
/-
**MeasureTheory.L1.setToL1_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1_unique (hT : DominatedFinMeasAdditive μ T C) {A : (α ->₁[μ] E) ->L
[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setToL1SCLM α E μ hT f = A f) (f : α ->₁
[μ] E) : setToL1 hT f = A f
参数：hT : DominatedFinMeasAdditive μ T C；α ->₁[μ] E；hA : forall f : α ->₁ₛ[μ] E, s
etToL1SCLM α E μ hT f = A f；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.extend_unique`：extend_unique (h_dense : DenseRange e
) (h_e : IsUniformInducing e) (g : Eₗ ->SL[σ₁₂] F) (H : g.comp e = f) : extend f
 e = g
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.Lp.simpleFunc.isUniformInducing`：isUniformInducing : IsUni
formInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem setToL1_unique (hT : DominatedFinMeasAdditive μ T C) {A : (α →₁[μ] E) →L[ℝ] F}
    (hA : ∀ f : α →₁ₛ[μ] E, setToL1SCLM α E μ hT f = A f) (f : α →₁[μ] E) :
    setToL1 hT f = A f := by
  suffices setToL1 hT = A by rw [this]
  apply ContinuousLinearMap.extend_unique
  · exact (simpleFunc.denseRange one_ne_top)
  · exact simpleFunc.isUniformInducing
  ext f
  rw [hA f]
  rfl
/-
**MeasureTheory.L1.setToL1_eq_setToL1'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L1`。
形式化陈述：setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C) (h_smul : forall
 c : 𝕜, forall s x, T s (c • x) = c • T s x) (f : α ->₁[μ] E) : setToL1 hT f = s
etToL1' 𝕜 hT h_smul f
参数：hT : DominatedFinMeasAdditive μ T C；h_smul : forall c : 𝕜, forall s x, T s (c
 • x) = c • T s x；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用引理 `Dense.induction`：Dense.induction (hs : Dense s) {P : X -> Prop} (mem : f
orall x in s, P x) (isClosed : IsClosed { x | P x }) (x : X) : P x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L1.setToL1_apply_coeToLp`：setToL1_apply_coeToLp (hT : Domi
natedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT (coeToLp α E Real f) 
= setToL1SCLM α E μ hT f
· 使用定理 `MeasureTheory.L1.setToL1'_apply_coeToLp`：∀ {α : Type u_1} {E : Type u_2}
 {F : Type u_3} (𝕜 : Type u_6) [inst : NormedAddCommGroup E] [inst_1 : NormedSpa
ce ℝ E]   [inst_2 : NormedAdd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1' 𝕜 hT h_smul f := by
  have h₁ : Dense (Set.range (coeToLp α E ℝ)) := simpleFunc.denseRange (μ := μ) one_ne_top
  apply Dense.induction (P := fun f : α →₁[μ] E ↦ (setToL1 hT) f = (setToL1' 𝕜 hT h_smul) f) h₁
  · intro f ⟨f', hf⟩
    simp [← hf]
  · exact isClosed_eq (setToL1 hT).continuous (setToL1' 𝕜 hT h_smul).continuous

@[simp]
/-
**MeasureTheory.L1.setToL1_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1
`。
形式化陈述：setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Rea
l] F) C) (f : α ->₁[μ] E) : setToL1 hT f = 0
参数：hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C；f : α ->₁[μ] E
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left`：setToL1SCLM_zero_left
 (hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Real] F) C) (f : α ->₁ₛ[μ]
 E) : setToL1SCLM α E μ hT f = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp) f
/-
**MeasureTheory.L1.setToL1_zero_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C) (h_zero : forall 
s, MeasurableSet s -> μ s < ∞ -> T s = 0) (f : α ->₁[μ] E) : setToL1 hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；h_zero : forall s, MeasurableSet s -> μ s
 < ∞ -> T s = 0；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_zero_left'`：setToL1SCLM_zero_lef
t' (hT : DominatedFinMeasAdditive μ T C) (h_zero : forall s, MeasurableSet s -> 
μ s < ∞ -> T s = 0) (f : α ->₁ₛ[μ] E) : …
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp [setToL1SCLM_zero_left' hT h_zero]) f
/-
**MeasureTheory.L1.setToL1_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：setToL1_congr_left (T T' : Set α -> E ->L[Real] F) {C C' : Real} (hT : Dom
inatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T
') (f : α ->₁[μ] E) : setToL1 hT f = setToL1 hT' f
参数：T T' : Set α -> E ->L[Real] F；hT : DominatedFinMeasAdditive μ T C；hT' : Domin
atedFinMeasAdditive μ T' C'；h : T = T'；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left`：setToL1SCLM_congr_le
ft (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C'
) (h : T = T') (f : α ->₁ₛ[μ] E) : setTo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem setToL1_congr_left (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T')
    (f : α →₁[μ] E) : setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1SCLM_congr_left hT' hT h.symm f
/-
**MeasureTheory.L1.setToL1_congr_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L1`。
形式化陈述：setToL1_congr_left' (T T' : Set α -> E ->L[Real] F) {C C' : Real} (hT : Do
minatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : fora
ll s, MeasurableSet s -> μ s < ∞ -> T s = T' s) (f : α ->₁[μ] E) : setToL1 hT f 
= setToL1 hT' f
参数：T T' : Set α -> E ->L[Real] F；hT : DominatedFinMeasAdditive μ T C；hT' : Domin
atedFinMeasAdditive μ T' C'；h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T'
 s；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_congr_left'`：setToL1SCLM_congr_l
eft' (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' 
C') (h : forall s, MeasurableSet s -> μ s…
-/
theorem setToL1_congr_left' (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact (setToL1SCLM_congr_left' hT hT' h f).symm
/-
**MeasureTheory.L1.setToL1_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`
。
形式化陈述：setToL1_add_left (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFin
MeasAdditive μ T' C') (f : α ->₁[μ] E) : setToL1 (hT.add hT') f = setToL1 hT f +
 setToL1 hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；f 
: α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add`：add (hT : DominatedFinMeasAd
ditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') : DominatedFinMeasAdditiv
e μ (T + T') (C + C')
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left`：setToL1SCLM_add_left (
hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (f
 : α ->₁ₛ[μ] E) : setToL1SCLM α E μ (h…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁[μ] E) :
    setToL1 (hT.add hT') f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique (hT.add hT') (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']
/-
**MeasureTheory.L1.setToL1_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1
`。
形式化陈述：setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFi
nMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'') (h_add : fora
ll s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α ->₁[μ] E) : setTo
L1 hT'' f = setToL1 hT f + setToL1 hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
'' : DominatedFinMeasAdditive μ T'' C''；h_add : forall s, MeasurableSet s -> μ s
 < ∞ -> T'' s = T s + T' s；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_add_left'`：setToL1SCLM_add_left'
 (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') 
(hT'' : DominatedFinMeasAdditive μ T'' …
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁[μ] E) :
    setToL1 hT'' f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique hT'' (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left' hT hT' hT'' h_add]
/-
**MeasureTheory.L1.setToL1_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1
`。
形式化陈述：setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α 
->₁[μ] E) : setToL1 (hT.smul c) f = c • setToL1 hT f
参数：hT : DominatedFinMeasAdditive μ T C；c : Real；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.smul`：smul [SeminormedAddGroup 𝕜]
 [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c 
: 𝕜) : DominatedFinMeasAdditive μ…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left`：setToL1SCLM_smul_left
 (c : Real) (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1SCL
M α E μ (hT.smul c) f = c • setToL1SCLM…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α →₁[μ] E) :
    setToL1 (hT.smul c) f = c • setToL1 hT f := by
  apply setToL1_unique (hT.smul c) (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]
/-
**MeasureTheory.L1.setToL1_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedF
inMeasAdditive μ T' C') (c : Real) (h_smul : forall s, MeasurableSet s -> μ s < 
∞ -> T' s = c • T s) (f : α ->₁[μ] E) : setToL1 hT' f = c • setToL1 hT f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；c 
: Real；h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s；f : α ->₁
[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_unique`：setToL1_unique (hT : DominatedFinMeasAd
ditive μ T C) {A : (α ->₁[μ] E) ->L[Real] F} (hA : forall f : α ->₁ₛ[μ] E, setTo
L1SCLM α E μ hT f = A…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1SCLM_smul_left'`：setToL1SCLM_smul_lef
t' (c : Real) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAddit
ive μ T' C') (h_smul : forall s, Measura…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁[μ] E) :
    setToL1 hT' f = c • setToL1 hT f := by
  apply setToL1_unique hT' (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]
/-
**MeasureTheory.L1.setToL1_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1_smul (hT : DominatedFinMeasAdditive μ T C) (h_smul : forall c : 𝕜,
 forall s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α ->₁[μ] E) : setToL1 hT (c •
 f) = c • setToL1 hT f
参数：hT : DominatedFinMeasAdditive μ T C；h_smul : forall c : 𝕜, forall s x, T s (c
 • x) = c • T s x；c : 𝕜；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1'`：setToL1_eq_setToL1' (hT : Dominate
dFinMeasAdditive μ T C) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T 
s x) (f : α ->₁[μ] E) : se…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem setToL1_smul (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁[μ] E) :
    setToL1 hT (c • f) = c • setToL1 hT f := by
  rw [setToL1_eq_setToL1' hT h_smul, setToL1_eq_setToL1' hT h_smul]
  exact map_smul _ _ _
/-
**MeasureTheory.L1.setToL1_simpleFunc_indicatorConst** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.L1`。
形式化陈述：setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s
 : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) : setToL1 hT (simpleFun
c.indicatorConst 1 hs hμs.ne x) = T s x
参数：hT : DominatedFinMeasAdditive μ T C；hs : MeasurableSet s；hμs : μ s < ∞；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_indicatorConst`：setToL1S_indicatorC
onst {T : Set α -> E ->L[Real] F} {s : Set α} (h_zero : forall s, MeasurableSet 
s -> μ s = 0 -> T s = 0) (h_add : FinMeas…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1 hT (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x
/-
**MeasureTheory.L1.setToL1_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1`。
形式化陈述：setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
 (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) : setToL1 hT (indicatorConstLp 
1 hs hμs x) = T s x
参数：hT : DominatedFinMeasAdditive μ T C；hs : MeasurableSet s；hμs : μ s != ∞；x : E
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.simpleFunc.coe_indicatorConst`：coe_indicatorConst {s : 
Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) : (↑(indicatorConst p hs 
hμs c) : Lp E p μ) = indicatorConstL…
· 使用定理 `MeasureTheory.L1.setToL1_simpleFunc_indicatorConst`：setToL1_simpleFunc_i
ndicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : Measurable
Set s) (hμs : μ s < ∞) (x : E) : setToL1…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToL1 hT (indicatorConstLp 1 hs hμs x) = T s x := by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x
/-
**MeasureTheory.L1.setToL1_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x
 : E) : setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x
) = T univ x
参数：hT : DominatedFinMeasAdditive μ T C；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.L1.setToL1_indicatorConstLp`：setToL1_indicatorConstLp (hT 
: DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hμs : μ s 
!= ∞) (x : E) : setToL1 hT (ind…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem setToL1_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x) = T univ x :=
  setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace ℝ G''] [CompleteSpace G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']

/-
**MeasureTheory.L1.setToL1_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L
1`。
形式化陈述：setToL1_mono_left' [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] 
G''} {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeas
Additive μ T' C') (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s 
x <= T' s x) (f : α ->₁[μ] E) : setToL1 hT f <= setToL1 hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x；f : α ->₁
[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : Meas
urableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheor
y.Measure α} [_i…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_simpleFunc_indicatorConst`：setToL1_simpleFunc_i
ndicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : Measurable
Set s) (hμs : μ s < ∞) (x : E) : setToL1…
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem setToL1_mono_left' [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁[μ] E) :
    setToL1 hT f ≤ setToL1 hT' f := by
  induction f using Lp.induction (hp_ne_top := one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs, setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add, (setToL1 hT').map_add]
    exact add_le_add hf_le hg_le
  | isClosed => exact isClosed_le (setToL1 hT).continuous (setToL1 hT').continuous
/-
**MeasureTheory.L1.setToL1_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1
`。
形式化陈述：setToL1_mono_left [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] G
''} {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasA
dditive μ T' C') (hTT' : forall s x, T s x <= T' s x) (f : α ->₁[μ] E) : setToL1
 hT f <= setToL1 hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s x, T s x <= T' s x；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.L1.setToL1_mono_left'`：setToL1_mono_left' [OrderClosedTopo
logy G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real} (hT : DominatedFinMeas
Additive μ T C) (hT' : Do…
-/
theorem setToL1_mono_left [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToL1 hT f ≤ setToL1 hT' f :=
  setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
/-
**MeasureTheory.L1.setToL1_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1_nonneg [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C 
: Real} (hT : DominatedFinMeasAdditive μ T C) (hT_nonneg : forall s, MeasurableS
et s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α ->₁[μ] G'} (hf : 0 <= 
f) : 0 <= setToL1 hT f
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg`：de
nseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 <= p)] (hp_ne_top : p != ∞)
 : DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `MeasureTheory.L1.SimpleFunc.setToL1S_nonneg`：setToL1S_nonneg (h_zero : f
orall s, MeasurableSet s -> μ s = 0 -> T s = 0) (h_add : FinMeasAdditive μ T) (h
T_nonneg : forall s, MeasurableSe…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem setToL1_nonneg [ClosedIciTopology G''] {T : Set α → G' →L[ℝ] G''} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1 hT f := by
  suffices ∀ f : { g : α →₁[μ] G' // 0 ≤ g }, 0 ≤ setToL1 hT f from
    this (⟨f, hf⟩ : { g : α →₁[μ] G' // 0 ≤ g })
  refine fun g =>
    @isClosed_property { g : α →₁ₛ[μ] G' // 0 ≤ g } { g : α →₁[μ] G' // 0 ≤ g } _ _
      (fun g => 0 ≤ setToL1 hT g)
      (denseRange_coeSimpleFuncNonnegToLpNonneg 1 μ G' one_ne_top) ?_ ?_ g
  · exact (isClosed_Ici (a := 0)).preimage ((setToL1 hT).continuous.comp continuous_induced_dom)
  · intro g
    have : (coeSimpleFuncNonnegToLpNonneg 1 μ G' g : α →₁[μ] G') = (g : α →₁ₛ[μ] G') := rfl
    rw [this, setToL1_eq_setToL1SCLM]
    exact setToL1S_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg g.2
/-
**MeasureTheory.L1.setToL1_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：setToL1_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G'] {T : Set α ->
 G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C) (hT_nonneg :
 forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g : 
α ->₁[μ] G'} (hfg : f <= g) : setToL1 hT f <= setToL1 hT g
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hfg : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousLinearMap.map_sub`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `MeasureTheory.L1.setToL1_nonneg`：setToL1_nonneg [ClosedIciTopology G''] 
{T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
 (hT_nonneg : forall …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
-/
theorem setToL1_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁[μ] G'}
    (hfg : f ≤ g) : setToL1 hT f ≤ setToL1 hT g := by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (setToL1 hT).map_sub]
  exact setToL1_nonneg hT hT_nonneg hfg

end Order

/-
**MeasureTheory.L1.norm_setToL1_le_norm_setToL1SCLM** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.L1`。
形式化陈述：norm_setToL1_le_norm_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) : ‖
setToL1 hT‖ <= ‖setToL1SCLM α E μ hT‖
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.opNorm_extend_le`：opNorm_extend_le (h_dense : DenseR
ange e) (h_e : forall x, ‖x‖ <= N * ‖e x‖) : ‖f.extend e‖ <= N * ‖f‖
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_setToL1_le_norm_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1 hT‖ ≤ ‖setToL1SCLM α E μ hT‖ :=
  calc
    ‖setToL1 hT‖ ≤ (1 : ℝ≥0) * ‖setToL1SCLM α E μ hT‖ := by
      refine
        ContinuousLinearMap.opNorm_extend_le (setToL1SCLM α E μ hT)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq ?_
      rw [NNReal.coe_one, one_mul]
      simp [coeToLp]
    _ = ‖setToL1SCLM α E μ hT‖ := by rw [NNReal.coe_one, one_mul]
/-
**MeasureTheory.L1.norm_setToL1_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.L1`。
形式化陈述：norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= 
C) (f : α ->₁[μ] E) : ‖setToL1 hT f‖ <= C * ‖f‖
参数：hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_norm_setToL1SCLM`：norm_setToL1_le_norm_
setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ <= ‖setToL1SCLM
 α E μ hT‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le`：norm_setToL1SCLM_le {T 
: Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C) (hC :
 0 <= C) : ‖setToL1SCLM α E μ hT‖ <= …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C)
    (f : α →₁[μ] E) : ‖setToL1 hT f‖ ≤ C * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC
/-
**MeasureTheory.L1.norm_setToL1_le_mul_norm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.L1`。
形式化陈述：norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁
[μ] E) : ‖setToL1 hT f‖ <= max C 0 * ‖f‖
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_norm_setToL1SCLM`：norm_setToL1_le_norm_
setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ <= ‖setToL1SCLM
 α E μ hT‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MeasureTheory.L1.SimpleFunc.norm_setToL1SCLM_le'`：norm_setToL1SCLM_le' {
T : Set α -> E ->L[Real] F} {C : Real} (hT : DominatedFinMeasAdditive μ T C) : ‖
setToL1SCLM α E μ hT‖ <= max C 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToL1 hT f‖ ≤ max C 0 * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)
/-
**MeasureTheory.L1.norm_setToL1_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：norm_setToL1_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) : ‖set
ToL1 hT‖ <= C
参数：hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm`：norm_setToL1_le_mul_norm (hT 
: DominatedFinMeasAdditive μ T C) (hC : 0 <= C) (f : α ->₁[μ] E) : ‖setToL1 hT f
‖ <= C * ‖f‖
-/
theorem norm_setToL1_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : ‖setToL1 hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)
/-
**MeasureTheory.L1.norm_setToL1_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`
。
形式化陈述：norm_setToL1_le' (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ <= m
ax C 0
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm'`：norm_setToL1_le_mul_norm' (h
T : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) : ‖setToL1 hT f‖ <= max C 0
 * ‖f‖
-/
theorem norm_setToL1_le' (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)
/-
**MeasureTheory.L1.setToL1_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1
`。
形式化陈述：setToL1_lipschitz (hT : DominatedFinMeasAdditive μ T C) : LipschitzWith (R
eal.toNNReal C) (setToL1 hT)
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.weaken`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWit
h K f → ∀ …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `MeasureTheory.L1.norm_setToL1_le'`：norm_setToL1_le' (hT : DominatedFinMe
asAdditive μ T C) : ‖setToL1 hT‖ <= max C 0
-/
theorem setToL1_lipschitz (hT : DominatedFinMeasAdditive μ T C) :
    LipschitzWith (Real.toNNReal C) (setToL1 hT) :=
  (setToL1 hT).lipschitz.weaken (norm_setToL1_le' hT)

/-- If `fs i → f` in `L1`, then `setToL1 hT (fs i) → setToL1 hT f`. -/
/-
**MeasureTheory.L1.tendsto_setToL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L1`。
形式化陈述：tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) {ι}
 (fs : ι -> α ->₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) : Tendsto (fun
 i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f)
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁[μ] E；fs : ι -> α ->₁[μ] E；hfs :
 Tendsto fs l (𝓝 f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
If `fs i → f` in `L1`, then `setToL1 hT (fs i) → setToL1 hT f`.
-/
theorem tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) {ι}
    (fs : ι → α →₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f) :=
  ((setToL1 hT).continuous.tendsto _).comp hfs

end SetToL1

end L1

section Function

variable {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ} {f g : α → E}
variable (μ T)

open scoped Classical in
/-- Extend `T : Set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
0 if the function is not integrable or if the target space is not complete. -/
/-
**MeasureTheory.setToFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) : F
参数：hT : DominatedFinMeasAdditive μ T C；f : α -> E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Extend `T : Set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E
`). We set it to
0 if the function is not integrable or if the target space is not complete.
-/
def setToFun (hT : DominatedFinMeasAdditive μ T C) (f : α → E) : F :=
  if _hF : CompleteSpace F then
    if hf : Integrable f μ then L1.setToL1 hT (hf.toL1 f) else 0
  else 0

variable {μ T}
/-
**MeasureTheory.setToFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_eq [hF : CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C) (
hf : Integrable f μ) : setToFun μ T hT f = L1.setToL1 hT (hf.toL1 f)
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_eq [hF : CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT f = L1.setToL1 hT (hf.toL1 f) := by
  simp [setToFun, hF, hf]
/-
**MeasureTheory.L1.setToFun_eq_setToL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L1`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {T : Set α → 
E →L[ℝ] F} {C : ℝ} [inst_4 : CompleteSpace F] (hT : MeasureTheory.DominatedFinMe
asAdditive μ T C)   (f : ↥(MeasureTheory.Lp E 1 μ)), MeasureTheory.setToFun μ T 
hT ↑↑f = (MeasureTheory.L1.setToL1 hT) f
参数：hT : MeasureTheory.DominatedFinMeasAdditive μ T C；f : ↥(MeasureTheory.Lp E 1 
μ)；MeasureTheory.L1.setToL1 hT。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.Integrable.toL1_coeFn`：toL1_coeFn (f : α ->₁[μ] β) (hf : I
ntegrable f μ) : hf.toL1 f = f
-/
theorem L1.setToFun_eq_setToL1 [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    setToFun μ T hT f = L1.setToL1 hT f := by
  rw [setToFun_eq hT (L1.integrable_coeFn f), Integrable.toL1_coeFn]
/-
**MeasureTheory.setToFun_undef** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_undef (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ
) : setToFun μ T hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；hf : ¬Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_undef (hT : DominatedFinMeasAdditive μ T C) (hf : ¬Integrable f μ) :
    setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F
  · simp [setToFun, hF, hf]
  · simp [setToFun, hF]
/-
**MeasureTheory.setToFun_non_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：setToFun_non_aestronglyMeasurable (hT : DominatedFinMeasAdditive μ T C) (h
f : ¬AEStronglyMeasurable f μ) : setToFun μ T hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；hf : ¬AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
theorem setToFun_non_aestronglyMeasurable (hT : DominatedFinMeasAdditive μ T C)
    (hf : ¬AEStronglyMeasurable f μ) : setToFun μ T hT f = 0 :=
  setToFun_undef hT (not_and_of_not_left _ hf)
/-
**MeasureTheory.setToFun_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_congr_left (hT : DominatedFinMeasAdditive μ T C) (hT' : Dominated
FinMeasAdditive μ T' C') (h : T = T') (f : α -> E) : setToFun μ T hT f = setToFu
n μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；h 
: T = T'；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_congr_left`：setToL1_congr_left (T T' : Set α ->
 E ->L[Real] F) {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : Domin
atedFinMeasAdditive μ T' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_congr_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T') (f : α → E) :
    setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]
/-
**MeasureTheory.setToFun_congr_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : Dominate
dFinMeasAdditive μ T' C') (h : forall s, MeasurableSet s -> μ s < ∞ -> T s = T' 
s) (f : α -> E) : setToFun μ T hT f = setToFun μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；h 
: forall s, MeasurableSet s -> μ s < ∞ -> T s = T' s；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_congr_left'`：setToL1_congr_left' (T T' : Set α 
-> E ->L[Real] F) {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : Dom
inatedFinMeasAdditive μ T'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_congr_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s)
    (f : α → E) : setToFun μ T hT f = setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_congr_left' T T' hT hT' h]
  · simp_rw [setToFun_undef _ hf]
/-
**MeasureTheory.setToFun_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_add_left (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFi
nMeasAdditive μ T' C') (f : α -> E) : setToFun μ (T + T') (hT.add hT') f = setTo
Fun μ T hT f + setToFun μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；f 
: α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add`：add (hT : DominatedFinMeasAd
ditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') : DominatedFinMeasAdditiv
e μ (T + T') (C + C')
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_add_left`：setToL1_add_left (hT : DominatedFinMe
asAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (f : α ->₁[μ] E) : se
tToL1 (hT.add hT') f = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α → E) :
    setToFun μ (T + T') (hT.add hT') f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left hT hT']
  · simp_rw [setToFun_undef _ hf, add_zero]

/-- `setToFun` applied to the sum `T + T'` of two operators is the sum of the corresponding
`setToFun`. See also `setToFun_add_left'` for a version varying the reference measures. -/
/-
**MeasureTheory.setToFun_add_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedF
inMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'') (h_add : for
all s, MeasurableSet s -> μ s < ∞ -> T'' s = T s + T' s) (f : α -> E) : setToFun
 μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
'' : DominatedFinMeasAdditive μ T'' C''；h_add : forall s, MeasurableSet s -> μ s
 < ∞ -> T'' s = T s + T' s；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_add_left'`：setToL1_add_left' (hT : DominatedFin
MeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFi
nMeasAdditive μ T'' C'')…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
`setToFun` applied to the sum `T + T'` of two operators is the sum of the corres
ponding
`setToFun`. See also `setToFun_add_left'` for a version varying the reference me
asures.
-/
theorem setToFun_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α → E) :
    setToFun μ T'' hT'' f = setToFun μ T hT f + setToFun μ T' hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_add_left' hT hT' hT'' h_add]
  · simp_rw [setToFun_undef _ hf, add_zero]
/-
**MeasureTheory.setToFun_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : Real) (f : α
 -> E) : setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；c : Real；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.smul`：smul [SeminormedAddGroup 𝕜]
 [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c 
: 𝕜) : DominatedFinMeasAdditive μ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_smul_left`：setToL1_smul_left (hT : DominatedFin
MeasAdditive μ T C) (c : Real) (f : α ->₁[μ] E) : setToL1 (hT.smul c) f = c • se
tToL1 hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α → E) :
    setToFun μ (fun s => c • T s) (hT.smul c) f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left hT c]
  · simp_rw [setToFun_undef _ hf, smul_zero]
/-
**MeasureTheory.setToFun_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C) (hT' : Dominated
FinMeasAdditive μ T' C') (c : Real) (h_smul : forall s, MeasurableSet s -> μ s <
 ∞ -> T' s = c • T s) (f : α -> E) : setToFun μ T' hT' f = c • setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；c 
: Real；h_smul : forall s, MeasurableSet s -> μ s < ∞ -> T' s = c • T s；f : α -> 
E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.L1.setToL1_smul_left'`：setToL1_smul_left' (hT : DominatedF
inMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (c : Real) (h_smu
l : forall s, MeasurableS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α → E) :
    setToFun μ T' hT' f = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf, L1.setToL1_smul_left' hT hT' c h_smul]
  · simp_rw [setToFun_undef _ hf, smul_zero]

@[simp]
/-
**MeasureTheory.setToFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 :
 α -> E) = 0
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.Integrable.toL1_zero`：toL1_zero (h : Integrable (0 : α -> 
β) μ) : h.toL1 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_zero (hT : DominatedFinMeasAdditive μ T C) : setToFun μ T hT (0 : α → E) = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (integrable_zero _ _ _), Integrable.toL1_zero, map_zero]

@[simp]
/-
**MeasureTheory.setToFun_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α -> E ->L[Re
al] F) C} : setToFun μ 0 hT f = 0
参数：0 : Set α -> E ->L[Real] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.setToL1_zero_left`：setToL1_zero_left (hT : DominatedFin
MeasAdditive μ (0 : Set α -> E ->L[Real] F) C) (f : α ->₁[μ] E) : setToL1 hT f =
 0
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_zero_left {hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C} :
    setToFun μ 0 hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left hT _
  · exact setToFun_undef hT hf
/-
**MeasureTheory.setToFun_zero_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C) (h_zero : forall
 s, MeasurableSet s -> μ s < ∞ -> T s = 0) : setToFun μ T hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；h_zero : forall s, MeasurableSet s -> μ s
 < ∞ -> T s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.setToL1_zero_left'`：setToL1_zero_left' (hT : DominatedF
inMeasAdditive μ T C) (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0)
 (f : α ->₁[μ] E) : setTo…
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) : setToFun μ T hT f = 0 := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf]; exact L1.setToL1_zero_left' hT h_zero _
  · exact setToFun_undef hT hf
/-
**MeasureTheory.setToFun_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (
hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ 
T hT g
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.Integrable.toL1_add`：toL1_add (f g : α -> β) (hf : Integra
ble f μ) (hg : Integrable g μ) : toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g h
g
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_add (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f + g) = setToFun μ T hT f + setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  rw [setToFun_eq hT (hf.add hg), setToFun_eq hT hf, setToFun_eq hT hg, Integrable.toL1_add,
    (L1.setToL1 hT).map_add]
/-
**MeasureTheory.setToFun_finsetSum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_finsetSum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset 
ι) {f : ι -> α -> E} (hf : forall i in s, Integrable (f i) μ) : setToFun μ T hT 
(∑ i in s, f i) = ∑ i in s, setToFun μ T hT (f i)
参数：hT : DominatedFinMeasAdditive μ T C；s : Finset ι；hf : forall i in s, Integrab
le (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `MeasureTheory.integrable_finsetSum`：integrable_finsetSum {ι} (s : Finset
 ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (fu
n a => ∑ i in s, f i a) …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem setToFun_finsetSum' (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι)
    {f : ι → α → E} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    setToFun μ T hT (∑ i ∈ s, f i) = ∑ i ∈ s, setToFun μ T hT (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [setToFun_zero, Finset.sum_empty]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    rw [setToFun_add hT (hf i (Finset.mem_insert_self i s)) _]
    · rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    · convert! integrable_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi) with x
      simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum' := setToFun_finsetSum'
/-
**MeasureTheory.setToFun_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_finsetSum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι
) {f : ι -> α -> E} (hf : forall i in s, Integrable (f i) μ) : (setToFun μ T hT 
fun a => ∑ i in s, f i a) = ∑ i in s, setToFun μ T hT (f i)
参数：hT : DominatedFinMeasAdditive μ T C；s : Finset ι；hf : forall i in s, Integrab
le (f i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_finsetSum'`：setToFun_finsetSum' (hT : DominatedFi
nMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E} (hf : forall i in s, I
ntegrable (f i) μ) : se…
-/
theorem setToFun_finsetSum (hT : DominatedFinMeasAdditive μ T C) {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (setToFun μ T hT fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, setToFun μ T hT (f i) := by
  convert! setToFun_finsetSum' hT s hf with a; simp

@[deprecated (since := "2026-04-08")] alias setToFun_finset_sum := setToFun_finsetSum
/-
**MeasureTheory.setToFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) : setToFun
 μ T hT (-f) = -setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.toL1_neg`：toL1_neg (f : α -> β) (hf : Integrabl
e f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf
· 使用定理 `ContinuousLinearMap.map_neg`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_neg (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ T hT (-f) = -setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT hf.neg, Integrable.toL1_neg,
      (L1.setToL1 hT).map_neg]
  · rw [setToFun_undef hT hf, setToFun_undef hT, neg_zero]
    rwa [← integrable_neg_iff] at hf
/-
**MeasureTheory.setToFun_neg'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_neg' (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) : setToFu
n μ (-T) hT.neg f = -setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.neg`：neg (hT : DominatedFinMeasAd
ditive μ T C) : DominatedFinMeasAdditive μ (-T) C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.setToFun_smul_left'`：setToFun_smul_left' (hT : DominatedFi
nMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (c : Real) (h_smul
 : forall s, Measurable…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem setToFun_neg' (hT : DominatedFinMeasAdditive μ T C) (f : α → E) :
    setToFun μ (-T) hT.neg f = -setToFun μ T hT f := by
  simpa using setToFun_smul_left' hT hT.neg (-1) (by simp) f
/-
**MeasureTheory.setToFun_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (
hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ 
T hT g
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.setToFun_neg`：setToFun_neg (hT : DominatedFinMeasAdditive 
μ T C) (f : α -> E) : setToFun μ T hT (-f) = -setToFun μ T hT f
-/
theorem setToFun_sub (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ)
    (hg : Integrable g μ) : setToFun μ T hT (f - g) = setToFun μ T hT f - setToFun μ T hT g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, setToFun_add hT hf hg.neg, setToFun_neg hT g]
/-
**MeasureTheory.setToFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [Mod
ule 𝕜 F] [NormSMulClass 𝕜 F] (hT : DominatedFinMeasAdditive μ T C) (h_smul : for
all c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α -> E) : setToFun 
μ T hT (c • f) = c • setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；h_smul : forall c : 𝕜, forall s x, T s (c
 • x) = c • T s x；c : 𝕜；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `MeasureTheory.Integrable.toL1_smul'`：toL1_smul' (f : α -> β) (hf : Integ
rable f μ) (k : 𝕜) : toL1 (k • f) (hf.smul k) = k • toL1 f hf
· 使用定理 `MeasureTheory.L1.setToL1_smul`：setToL1_smul (hT : DominatedFinMeasAdditi
ve μ T C) (h_smul : forall c : 𝕜, forall s x, T s (c • x) = c • T s x) (c : 𝕜) (
f : α ->₁[μ] E) : s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integrable_smul_iff`：integrable_smul_iff [NormedDivisionRi
ng 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -
> β) : Integrable (c • …
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [Module 𝕜 F] [NormSMulClass 𝕜 F]
    (hT : DominatedFinMeasAdditive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
    (f : α → E) : setToFun μ T hT (c • f) = c • setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ
  · rw [setToFun_eq hT hf, setToFun_eq hT (hf.smul c), Integrable.toL1_smul' f hf,
      L1.setToL1_smul hT h_smul c]
  · by_cases hr : c = 0
    · rw [hr]; simp
    · have hf' : ¬Integrable (c • f) μ := by rwa [integrable_smul_iff hr f]
      rw [setToFun_undef hT hf, setToFun_undef hT hf', smul_zero]
/-
**MeasureTheory.setToFun_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) : 
setToFun μ T hT f = setToFun μ T hT g
参数：hT : DominatedFinMeasAdditive μ T C；h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Integrable.toL1_eq_toL1_iff`：toL1_eq_toL1_iff (f g : α -> 
β) (hf : Integrable f μ) (hg : Integrable g μ) : toL1 f hf = toL1 g hg ↔ f =ᵐ[μ]
 g
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_congr_ae (hT : DominatedFinMeasAdditive μ T C) (h : f =ᵐ[μ] g) :
    setToFun μ T hT f = setToFun μ T hT g := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := hfi.congr h
    rw [setToFun_eq hT hfi, setToFun_eq hT hgi, (Integrable.toL1_eq_toL1_iff f g hfi hgi).2 h]
  · have hgi : ¬Integrable g μ := by rw [integrable_congr h] at hfi; exact hfi
    rw [setToFun_undef hT hfi, setToFun_undef hT hgi]
/-
**MeasureTheory.setToFun_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) : 
setToFun μ T hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；h : μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
-/
theorem setToFun_measure_zero (hT : DominatedFinMeasAdditive μ T C) (h : μ = 0) :
    setToFun μ T hT f = 0 := by
  have : f =ᵐ[μ] 0 := by simp [h, EventuallyEq]
  rw [setToFun_congr_ae hT this, setToFun_zero]
/-
**MeasureTheory.setToFun_measure_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setToFun_measure_zero' (hT : DominatedFinMeasAdditive μ T C) (h : forall s
, MeasurableSet s -> μ s < ∞ -> μ s = 0) : setToFun μ T hT f = 0
参数：hT : DominatedFinMeasAdditive μ T C；h : forall s, MeasurableSet s -> μ s < ∞ 
-> μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_zero_left'`：setToFun_zero_left' (hT : DominatedFi
nMeasAdditive μ T C) (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) 
: setToFun μ T hT f = 0
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
-/
theorem setToFun_measure_zero' (hT : DominatedFinMeasAdditive μ T C)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → μ s = 0) : setToFun μ T hT f = 0 :=
  setToFun_zero_left' hT fun s hs hμs => hT.eq_zero_of_measure_zero hs (h s hs hμs)
/-
**MeasureTheory.setToFun_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_toL1 (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) 
: setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
-/
theorem setToFun_toL1 (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    setToFun μ T hT (hf.toL1 f) = setToFun μ T hT f :=
  setToFun_congr_ae hT hf.coeFn_toL1
/-
**MeasureTheory.setToFun_indicator_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setToFun_indicator_const [CompleteSpace F] (hT : DominatedFinMeasAdditive 
μ T C) {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E) : setToFun μ 
T hT (s.indicator fun _ => x) = T s x
参数：hT : DominatedFinMeasAdditive μ T C；hs : MeasurableSet s；hμs : μ s != ∞；x : E
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.L1.setToL1_indicatorConstLp`：setToL1_indicatorConstLp (hT 
: DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hμs : μ s 
!= ∞) (x : E) : setToL1 hT (ind…
-/
theorem setToFun_indicator_const [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToFun μ T hT (s.indicator fun _ => x) = T s x := by
  rw [setToFun_congr_ae hT (@indicatorConstLp_coeFn _ _ _ 1 _ _ _ hs hμs x).symm]
  rw [L1.setToFun_eq_setToL1 hT]
  exact L1.setToL1_indicatorConstLp hT hs hμs x
/-
**MeasureTheory.setToFun_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_const [CompleteSpace F] [IsFiniteMeasure μ] (hT : DominatedFinMea
sAdditive μ T C) (x : E) : (setToFun μ T hT fun _ => x) = T univ x
参数：hT : DominatedFinMeasAdditive μ T C；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_indicator_const`：setToFun_indicator_const [Comple
teSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet
 s) (hμs : μ s != ∞) (x : E)…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem setToFun_const [CompleteSpace F] [IsFiniteMeasure μ]
    (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    (setToFun μ T hT fun _ => x) = T univ x := by
  have : (fun _ : α => x) = Set.indicator univ fun _ => x := (indicator_univ _).symm
  rw [this]
  exact setToFun_indicator_const hT MeasurableSet.univ (measure_ne_top _ _) x
/-
**MeasureTheory.setToFun_simpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_simpleFunc [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C
) (f : SimpleFunc α E) (hf : Integrable f μ) : setToFun μ T hT f = ∑ x in f.rang
e, T (f ⁻¹' {x}) x
参数：hT : DominatedFinMeasAdditive μ T C；f : SimpleFunc α E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.L1.setToL1_eq_setToL1SCLM`：setToL1_eq_setToL1SCLM (hT : Do
minatedFinMeasAdditive μ T C) (f : α ->₁ₛ[μ] E) : setToL1 hT f = setToL1SCLM α E
 μ hT f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_congr`：setToSimpleFunc_congr (T
 : Set α -> E ->L[Real] F) (h_zero : forall s, MeasurableSet s -> μ s = 0 -> T s
 = 0) (h_add : FinMeasAdditive μ T) …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero_of_measure_zero`：eq_zero_
of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α -> β} {C : Real} (
hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
-/
theorem setToFun_simpleFunc [CompleteSpace F] (hT : DominatedFinMeasAdditive μ T C)
    (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = ∑ x ∈ f.range, T (f ⁻¹' {x}) x := by
  have h'f : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  let g := f.toLp h'f
  have A : f =ᵐ[μ] g := h'f.coeFn_toLp.symm
  rw [setToFun_congr_ae hT A, L1.setToFun_eq_setToL1 hT, L1.setToL1_eq_setToL1SCLM]
  apply (SimpleFunc.setToSimpleFunc_congr T (fun s ↦ hT.eq_zero_of_measure_zero) hT.1 hf _).symm
  grw [A, Lp.simpleFunc.toSimpleFunc_eq_toFun]
/-
**MeasureTheory.setToFun_simpleFunc_eq_setToSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：setToFun_simpleFunc_eq_setToSimpleFunc [CompleteSpace F] (hT : DominatedFi
nMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ) : setToFun μ T h
T f = f.setToSimpleFunc T
参数：hT : DominatedFinMeasAdditive μ T C；f : SimpleFunc α E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_simpleFunc`：setToFun_simpleFunc [CompleteSpace F]
 (hT : DominatedFinMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ
) : setToFun μ T hT f =…
-/
theorem setToFun_simpleFunc_eq_setToSimpleFunc [CompleteSpace F]
    (hT : DominatedFinMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ) :
    setToFun μ T hT f = f.setToSimpleFunc T := by
  rw [setToFun_simpleFunc hT f hf]
  rfl

section Order

variable {G' G'' : Type*}
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace ℝ G'']
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']

/-
**MeasureTheory.setToFun_mono_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_mono_left' [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real]
 G''} {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMea
sAdditive μ T' C') (hTT' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s
 x <= T' s x) (f : α -> E) : setToFun μ T hT f <= setToFun μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s, MeasurableSet s -> μ s < ∞ -> forall x, T s x <= T' s x；f : α -> 
E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.setToL1_mono_left'`：setToL1_mono_left' [OrderClosedTopo
logy G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real} (hT : DominatedFinMeas
Additive μ T C) (hT' : Do…
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_mono_left' [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α → E) :
    setToFun μ T hT f ≤ setToFun μ T' hT' f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hf : Integrable f μ
  · simp_rw [setToFun_eq _ hf]; exact L1.setToL1_mono_left' hT hT' hTT' _
  · simp_rw [setToFun_undef _ hf, le_rfl]
/-
**MeasureTheory.setToFun_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_mono_left [OrderClosedTopology G''] {T T' : Set α -> E ->L[Real] 
G''} {C C' : Real} (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeas
Additive μ T' C') (hTT' : forall s x, T s x <= T' s x) (f : α ->₁[μ] E) : setToF
un μ T hT f <= setToFun μ T' hT' f
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ T' C'；hT
T' : forall s x, T s x <= T' s x；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.setToFun_mono_left'`：setToFun_mono_left' [OrderClosedTopol
ogy G''] {T T' : Set α -> E ->L[Real] G''} {C C' : Real} (hT : DominatedFinMeasA
dditive μ T C) (hT' : D…
-/
theorem setToFun_mono_left [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToFun μ T hT f ≤ setToFun μ T' hT' f :=
  setToFun_mono_left' hT hT' (fun s _ _ x => hTT' s x) f
/-
**MeasureTheory.setToFun_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_nonneg [ClosedIciTopology G''] {T : Set α -> G' ->L[Real] G''} {C
 : Real} (hT : DominatedFinMeasAdditive μ T C) (hT_nonneg : forall s, Measurable
Set s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f : α -> G'} (hf : 0 <=ᵐ[μ]
 f) : 0 <= setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.setToL1_nonneg`：setToL1_nonneg [ClosedIciTopology G''] 
{T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C)
 (hT_nonneg : forall …
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setToFun_nonneg [ClosedIciTopology G''] {T : Set α → G' →L[ℝ] G''} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α → G'}
    (hf : 0 ≤ᵐ[μ] f) : 0 ≤ setToFun μ T hT f := by
  by_cases hG'' : CompleteSpace G''; swap
  · simp [setToFun, hG'']
  by_cases hfi : Integrable f μ
  · simp_rw [setToFun_eq _ hfi]
    exact L1.setToL1_nonneg hT hT_nonneg hf
  · simp_rw [setToFun_undef _ hfi, le_rfl]
/-
**MeasureTheory.setToFun_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G'] {T : Set α -
> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C) (hT_nonneg 
: forall s, MeasurableSet s -> μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x) {f g :
 α -> G'} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f <=ᵐ[μ] g) : setTo
Fun μ T hT f <= setToFun μ T hT g
参数：hT : DominatedFinMeasAdditive μ T C；hT_nonneg : forall s, MeasurableSet s -> 
μ s < ∞ -> forall x, 0 <= x -> 0 <= T s x；hf : Integrable f μ；hg : Integrable g 
μ；hfg : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.setToFun_sub`：setToFun_sub (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f - g) = s
etToFun μ T hT f…
· 使用定理 `MeasureTheory.setToFun_nonneg`：setToFun_nonneg [ClosedIciTopology G''] {
T : Set α -> G' ->L[Real] G''} {C : Real} (hT : DominatedFinMeasAdditive μ T C) 
(hT_nonneg : forall…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem setToFun_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α → G'}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    setToFun μ T hT f ≤ setToFun μ T hT g := by
  rw [← sub_nonneg, ← setToFun_sub hT hg hf]
  refine setToFun_nonneg hT hT_nonneg (hfg.mono fun a ha => ?_)
  rw [Pi.sub_apply, Pi.zero_apply, sub_nonneg]
  exact ha

end Order

@[continuity]
/-
**MeasureTheory.continuous_setToFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) : Continuous fun
 f : α ->₁[μ] E => setToFun μ T hT f
参数：hT : DominatedFinMeasAdditive μ T C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :
    Continuous fun f : α →₁[μ] E => setToFun μ T hT f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF, continuous_const]
  simp_rw [L1.setToFun_eq_setToL1 hT]; exact ContinuousLinearMap.continuous _

/-- If `F i → f` in `L1`, then `setToFun μ T hT (F i) → setToFun μ T hT f`. -/
/-
**MeasureTheory.tendsto_setToFun_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α ->
 E) (hf : AEStronglyMeasurable f μ) {fs : ι -> α -> E} {l : Filter ι} (hfsi : fo
rallᶠ i in l, Integrable (fs i) μ) (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖
ₑ ∂μ) l (𝓝 0)) : Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T 
hT f)
参数：hT : DominatedFinMeasAdditive μ T C；f : α -> E；hf : AEStronglyMeasurable f μ；
hfsi : forallᶠ i in l, Integrable (fs i) μ；hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x
 - f x‖ₑ ∂μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.SetToL1.0.MeasureTheory.tendsto_
setToFun_of_L1._abel_1_2`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommG
roup E] {ι : Type u_3} (f : α → E) {fs : ι → α → E} (i : ι),   f = fs i - (fs i 
- f)
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'`：tendsto_Lp_iff_tendsto
_eLpNorm' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι -> Lp E p μ) (f_lim : Lp E 
p μ) : fi.Tendsto f (𝓝 f_lim) ↔ fi.Ten…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `F i → f` in `L1`, then `setToFun μ T hT (F i) → setToFun μ T hT f`.
-/
theorem tendsto_setToFun_of_L1 (hT : DominatedFinMeasAdditive μ T C) {ι} (f : α → E)
    (hf : AEStronglyMeasurable f μ) {fs : ι → α → E} {l : Filter ι}
    (hfsi : ∀ᶠ i in l, Integrable (fs i) μ)
    (hfs : Tendsto (fun i => ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => setToFun μ T hT (fs i)) l (𝓝 <| setToFun μ T hT f) := by
  classical
  rcases eq_or_neBot l with rfl | hl
  · simp
  have hfi : Integrable f μ := by
    obtain ⟨i, hi, h'i⟩ : ∃ i, ∫⁻ x, ‖fs i x - f x‖ₑ ∂μ < 1 ∧ Integrable (fs i) μ :=
      (((tendsto_order.1 hfs).2 _ zero_lt_one).and hfsi).exists
    have : Integrable (fs i - f) μ := ⟨h'i.aestronglyMeasurable.sub hf, hi.trans one_lt_top⟩
    convert h'i.sub this
    abel
  let f_lp := hfi.toL1 f
  let F_lp i := if hFi : Integrable (fs i) μ then hFi.toL1 (fs i) else 0
  have tendsto_L1 : Tendsto F_lp l (𝓝 f_lp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply]
    refine (tendsto_congr' ?_).mp hfs
    filter_upwards [hfsi] with i hi
    refine lintegral_congr_ae ?_
    filter_upwards [hi.coeFn_toL1, hfi.coeFn_toL1] with x hxi hxf
    simp_rw [F_lp, dif_pos hi, hxi, f_lp, hxf]
  suffices Tendsto (fun i => setToFun μ T hT (F_lp i)) l (𝓝 (setToFun μ T hT f)) by
    refine (tendsto_congr' ?_).mp this
    filter_upwards [hfsi] with i hi
    suffices h_ae_eq : F_lp i =ᵐ[μ] fs i from setToFun_congr_ae hT h_ae_eq
    simp_rw [F_lp, dif_pos hi]
    exact hi.coeFn_toL1
  rw [setToFun_congr_ae hT hfi.coeFn_toL1.symm]
  exact ((continuous_setToFun hT).tendsto f_lp).comp tendsto_L1
/-
**MeasureTheory.tendsto_setToFun_approxOn_of_measurable** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T
 C) [MeasurableSpace E] [BorelSpace E] {f : α -> E} {s : Set E} [SeparableSpace 
s] (hfi : Integrable f μ) (hfm : Measurable f) (hs : forallᵐ x ∂μ, f x in closur
e s) {y₀ : E} (h₀ : y₀ in s) (h₀i : Integrable (fun _ => y₀) μ) : Tendsto (fun n
 => setToFun μ T hT (SimpleFunc.approxOn f hfm s y₀ h₀ n)) atTop (𝓝 <| setToFun 
μ T hT f)
参数：hT : DominatedFinMeasAdditive μ T C；hfi : Integrable f μ；hfm : Measurable f；h
s : forallᵐ x ∂μ, f x in closure s；h₀ : y₀ in s；h₀i : Integrable (fun _ => y₀) μ
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_setToFun_of_L1`：tendsto_setToFun_of_L1 (hT : Domin
atedFinMeasAdditive μ T C) {ι} (f : α -> E) (hf : AEStronglyMeasurable f μ) {fs 
: ι -> α -> E} {l : Filter…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn`：integrable_approxOn [Borel
Space E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : Integrable f 
μ) {s : Set E} {y₀ : E} (h₀ : y₀ i…
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_L1_enorm`：tendsto_approxOn_L1_
enorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E} {y₀ 
: E} (h₀ : y₀ in s) [SeparableSpace s] {…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
theorem tendsto_setToFun_approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C)
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set E} [SeparableSpace s]
    (hfi : Integrable f μ) (hfm : Measurable f) (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E}
    (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f hfm s y₀ h₀ n)) atTop
      (𝓝 <| setToFun μ T hT f) :=
  tendsto_setToFun_of_L1 hT _ hfi.aestronglyMeasurable
    (Eventually.of_forall (SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i))
    (SimpleFunc.tendsto_approxOn_L1_enorm hfm _ hs (hfi.sub h₀i).2)
/-
**MeasureTheory.tendsto_setToFun_approxOn_of_measurable_of_range_subset** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_setToFun_approxOn_of_measurable_of_range_subset (hT : DominatedFin
MeasAdditive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α -> E} (fmeas : Mea
surable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s] (hs : range f un
ion {0} subseteq s) : Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f f
meas s 0 (hs <| by simp) n)) atTop (𝓝 <| setToFun μ T hT f)
参数：hT : DominatedFinMeasAdditive μ T C；fmeas : Measurable f；hf : Integrable f μ；
s : Set E；hs : range f union {0} subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_setToFun_approxOn_of_measurable`：tendsto_setToFun_
approxOn_of_measurable (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E]
 [BorelSpace E] {f : α -> E} {s : Set E} [S…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem tendsto_setToFun_approxOn_of_measurable_of_range_subset
    (hT : DominatedFinMeasAdditive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => setToFun μ T hT (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n)) atTop
      (𝓝 <| setToFun μ T hT f) := by
  refine tendsto_setToFun_approxOn_of_measurable hT hf fmeas ?_ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))
/-
**MeasureTheory.setToFun_of_le_map_of_stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：setToFun_of_le_map_of_stronglyMeasurable (hT : DominatedFinMeasAdditive μ 
T C) {β : Type*} {_ : MeasurableSpace β} {μ' : Measure β} {φ : α -> β} {T' : Set
 β -> E ->L[Real] F} (hT' : DominatedFinMeasAdditive μ' T' C') {f : β -> E} (hf 
: Integrable (f ∘ φ) μ) (hfm : StronglyMeasurable f) (hφ : Measurable φ) (hμ' : 
μ' <= μ.map φ) (h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x = T (φ
 ⁻¹' s) x) : setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ)
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ' T' C'；h
f : Integrable (f ∘ φ) μ；hfm : StronglyMeasurable f；hφ : Measurable φ；hμ' : μ' <
= μ.map φ；h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x = T (φ ⁻¹' s
) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.tendsto_setToFun_approxOn_of_measurable_of_range_subset`：t
endsto_setToFun_approxOn_of_measurable_of_range_subset (hT : DominatedFinMeasAdd
itive μ T C) [MeasurableSpace E] [BorelSpace E] {f : α -> E…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_simpleFunc`：setToFun_simpleFunc [CompleteSpace F]
 (hT : DominatedFinMeasAdditive μ T C) (f : SimpleFunc α E) (hf : Integrable f μ
) : setToFun μ T hT f =…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn_range`：integrable_approxOn_
range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [Separa
bleSpace (range f union {0} : Set E)] (h…
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn`：integrable_approxOn [Borel
Space E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : Integrable f 
μ) {s : Set E} {y₀ : E} (h₀ : y₀ i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 52 条，此处仅展示前 30 条）
-/
theorem setToFun_of_le_map_of_stronglyMeasurable
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α → β} {T' : Set β → E →L[ℝ] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β → E} (hf : Integrable (f ∘ φ) μ) (hfm : StronglyMeasurable f) (hφ : Measurable φ)
    (hμ' : μ' ≤ μ.map φ)
    (h : ∀ (s : Set β) (x : E), MeasurableSet s → T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hfi' : Integrable f μ' :=
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hf).mono_measure hμ'
  borelize E
  have : SeparableSpace (range f ∪ {0} : Set E) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_setToFun_approxOn_of_measurable_of_range_subset
      hT' hfm.measurable hfi' _ Subset.rfl) ?_
  convert tendsto_setToFun_approxOn_of_measurable_of_range_subset
    hT (hfm.measurable.comp hφ) hf (range f ∪ {0})
    (union_subset_union_left {0} (range_comp_subset_range φ f)) using 1
  ext i : 1
  rw [setToFun_simpleFunc _ _ (SimpleFunc.integrable_approxOn_range _ hfi' _),
    setToFun_simpleFunc, SimpleFunc.approxOn_comp hfm.measurable hφ]; swap
  · apply SimpleFunc.integrable_approxOn _ hf (by simp) (by simp)
  simp only [union_singleton, SimpleFunc.measurableSet_preimage, h, ← preimage_comp,
    SimpleFunc.coe_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  simp [hy, hT.1.map_empty_eq_zero]
/-
**MeasureTheory.setToFun_of_le_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_of_le_map (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : 
MeasurableSpace β} {μ' : Measure β} {φ : α -> β} {T' : Set β -> E ->L[Real] F} (
hT' : DominatedFinMeasAdditive μ' T' C') {f : β -> E} (hf : Integrable (f ∘ φ) μ
) (hfm : AEStronglyMeasurable f (μ.map φ)) (hφ : Measurable φ) (hμ' : μ' <= μ.ma
p φ) (h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x = T (φ ⁻¹' s) x)
 : setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ)
参数：hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ' T' C'；h
f : Integrable (f ∘ φ) μ；hfm : AEStronglyMeasurable f (μ.map φ)；hφ : Measurable 
φ；hμ' : μ' <= μ.map φ；h : forall (s : Set β) (x : E), MeasurableSet s -> T' s x 
= T (φ ⁻¹' s) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_of_le_map_of_stronglyMeasurable`：setToFun_of_le_m
ap_of_stronglyMeasurable (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : 
MeasurableSpace β} {μ' : Measure β} {φ : α -…
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
theorem setToFun_of_le_map
    (hT : DominatedFinMeasAdditive μ T C) {β : Type*} {_ : MeasurableSpace β}
    {μ' : Measure β} {φ : α → β} {T' : Set β → E →L[ℝ] F} (hT' : DominatedFinMeasAdditive μ' T' C')
    {f : β → E} (hf : Integrable (f ∘ φ) μ) (hfm : AEStronglyMeasurable f (μ.map φ))
    (hφ : Measurable φ) (hμ' : μ' ≤ μ.map φ)
    (h : ∀ (s : Set β) (x : E), MeasurableSet s → T' s x = T (φ ⁻¹' s) x) :
    setToFun μ' T' hT' f = setToFun μ T hT (f ∘ φ) := by
  let g := hfm.mk
  have A : setToFun μ' T' hT' f = setToFun μ' T' hT' g :=
    setToFun_congr_ae _ (ae_mono hμ' hfm.ae_eq_mk)
  have B : setToFun μ T hT (f ∘ φ) = setToFun μ T hT (g ∘ φ) := by
    apply setToFun_congr_ae
    exact ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk
  rw [A, B]
  exact setToFun_of_le_map_of_stronglyMeasurable _ _
    (hf.congr (ae_of_ae_map hφ.aemeasurable hfm.ae_eq_mk)) hfm.stronglyMeasurable_mk hφ hμ' h

/-- Auxiliary lemma for `setToFun_congr_measure`: the function sending `f : α →₁[μ] G` to
`f : α →₁[μ'] G` is continuous when `μ' ≤ c' • μ` for `c' ≠ ∞`. -/
/-
**MeasureTheory.continuous_L1_toL1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_L1_toL1 {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_l
e : μ' <= c' • μ) : Continuous fun f : α ->₁[μ] G => (Integrable.of_measure_le_s
mul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f
参数：c' : Real>=0∞；hc' : c' != ∞；hμ'_le : μ' <= c' • μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Integrable.of_measure_le_smul`：∀ {α : Type u_1} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSp
ace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.nonpos_iff_eq_zero'`：nonpos_iff_eq_zero' : μ <= 0 
↔ μ = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Metric.continuous_iff`：continuous_iff [PseudoMetricSpace β] {f : α -> β}
 : Continuous f ↔ forall b, forall ε > 0, exists δ > 0, forall a, dist a b < δ -
> dist (f a…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MeasureTheory.Lp.dist_def`：dist_def (f g : Lp E p μ) : dist f g = (eLpNo
rm (⇑f - ⇑g) p μ).toReal
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `setToFun_congr_measure`: the function sending `f : α →₁[μ] 
G` to
`f : α →₁[μ'] G` is continuous when `μ' ≤ c' • μ` for `c' ≠ ∞`.
-/
theorem continuous_L1_toL1 {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞) (hμ'_le : μ' ≤ c' • μ) :
    Continuous fun f : α →₁[μ] G =>
      (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f := by
  by_cases hc'0 : c' = 0
  · have hμ'0 : μ' = 0 := by rw [← Measure.nonpos_iff_eq_zero']; refine hμ'_le.trans ?_; simp [hc'0]
    have h_im_zero :
      (fun f : α →₁[μ] G =>
          (Integrable.of_measure_le_smul hc' hμ'_le (L1.integrable_coeFn f)).toL1 f) =
        0 := by
      ext1 f; ext1; simp_rw [hμ'0]; simp only [ae_zero, EventuallyEq, eventually_bot]
    rw [h_im_zero]
    exact continuous_zero
  rw [Metric.continuous_iff]
  intro f ε hε_pos
  use ε / 2 / c'.toReal
  refine ⟨div_pos (half_pos hε_pos) (toReal_pos hc'0 hc'), ?_⟩
  intro g hfg
  rw [Lp.dist_def] at hfg ⊢
  let h_int := fun f' : α →₁[μ] G => (L1.integrable_coeFn f').of_measure_le_smul hc' hμ'_le
  have :
    eLpNorm (⇑(Integrable.toL1 g (h_int g)) - ⇑(Integrable.toL1 f (h_int f))) 1 μ' =
      eLpNorm (⇑g - ⇑f) 1 μ' :=
    eLpNorm_congr_ae ((Integrable.coeFn_toL1 _).sub (Integrable.coeFn_toL1 _))
  rw [this]
  have h_eLpNorm_ne_top : eLpNorm (⇑g - ⇑f) 1 μ ≠ ∞ := by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)]; exact Lp.eLpNorm_ne_top _
  calc
    (eLpNorm (⇑g - ⇑f) 1 μ').toReal ≤ (c' * eLpNorm (⇑g - ⇑f) 1 μ).toReal := by
      refine toReal_mono (ENNReal.mul_ne_top hc' h_eLpNorm_ne_top) ?_
      refine (eLpNorm_mono_measure (⇑g - ⇑f) hμ'_le).trans_eq ?_
      rw [eLpNorm_smul_measure_of_ne_zero hc'0, smul_eq_mul]
      simp
    _ = c'.toReal * (eLpNorm (⇑g - ⇑f) 1 μ).toReal := toReal_mul
    _ ≤ c'.toReal * (ε / 2 / c'.toReal) := by gcongr
    _ = ε / 2 := by
      refine mul_div_cancel₀ (ε / 2) ?_; rw [Ne, toReal_eq_zero_iff]; simp [hc', hc'0]
    _ < ε := half_lt_self hε_pos
/-
**MeasureTheory.setToFun_congr_measure_of_integrable** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc'
 : c' != ∞) (hμ'_le : μ' <= c' • μ) (hT : DominatedFinMeasAdditive μ T C) (hT' :
 DominatedFinMeasAdditive μ' T C') (f : α -> E) (hfμ : Integrable f μ) : setToFu
n μ T hT f = setToFun μ' T hT' f
参数：c' : Real>=0∞；hc' : c' != ∞；hμ'_le : μ' <= c' • μ；hT : DominatedFinMeasAdditi
ve μ T C；hT' : DominatedFinMeasAdditive μ' T C'；f : α -> E；hfμ : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Integrable.of_measure_le_smul`：∀ {α : Type u_1} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSp
ace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.setToFun_indicator_const`：setToFun_indicator_const [Comple
teSpace F] (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet
 s) (hμs : μ s != ∞) (x : E)…
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.continuous_setToFun`：continuous_setToFun (hT : DominatedFi
nMeasAdditive μ T C) : Continuous fun f : α ->₁[μ] E => setToFun μ T hT f
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Integrable.coeFn_toL1`：coeFn_toL1 {f : α -> β} (hf : Integ
rable f μ) : hf.toL1 f =ᵐ[μ] f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.continuous_L1_toL1`：continuous_L1_toL1 {μ' : Measure α} (c
' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <= c' • μ) : Continuous fun f : α ->₁
[μ] G => (Integrable.o…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le_smul`：absolutelyContinu
ous_of_le_smul {μ' : Measure α} {c : Real>=0∞} (hμ'_le : μ' <= c • μ) : μ' ≪ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 35 条，此处仅展示前 30 条）
-/
theorem setToFun_congr_measure_of_integrable {μ' : Measure α} (c' : ℝ≥0∞) (hc' : c' ≠ ∞)
    (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) (hfμ : Integrable f μ) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- integrability for `μ` implies integrability for `μ'`.
  have h_int : ∀ g : α → E, Integrable g μ → Integrable g μ' := fun g hg =>
    Integrable.of_measure_le_smul hc' hμ'_le hg
  -- We use `Integrable.induction`
  apply hfμ.induction (P := fun f => setToFun μ T hT f = setToFun μ' T hT' f)
  · intro c s hs hμs
    have hμ's : μ' s ≠ ∞ := by
      refine ((hμ'_le s).trans_lt ?_).ne
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc'.lt_top hμs
    rw [setToFun_indicator_const hT hs hμs.ne, setToFun_indicator_const hT' hs hμ's]
  · intro f₂ g₂ _ hf₂ hg₂ h_eq_f h_eq_g
    rw [setToFun_add hT hf₂ hg₂, setToFun_add hT' (h_int f₂ hf₂) (h_int g₂ hg₂), h_eq_f, h_eq_g]
  · refine isClosed_eq (continuous_setToFun hT) ?_
    have :
      (fun f : α →₁[μ] E => setToFun μ' T hT' f) = fun f : α →₁[μ] E =>
        setToFun μ' T hT' ((h_int f (L1.integrable_coeFn f)).toL1 f) := by
      ext1 f; exact setToFun_congr_ae hT' (Integrable.coeFn_toL1 _).symm
    rw [this]
    exact (continuous_setToFun hT').comp (continuous_L1_toL1 c' hc' hμ'_le)
  · intro f₂ g₂ hfg _ hf_eq
    have hfg' : f₂ =ᵐ[μ'] g₂ := (Measure.absolutelyContinuous_of_le_smul hμ'_le).ae_eq hfg
    rw [← setToFun_congr_ae hT hfg, hf_eq, setToFun_congr_ae hT' hfg']
/-
**MeasureTheory.setToFun_congr_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setToFun_congr_measure {μ' : Measure α} (c c' : Real>=0∞) (hc : c != ∞) (h
c' : c' != ∞) (hμ_le : μ <= c • μ') (hμ'_le : μ' <= c' • μ) (hT : DominatedFinMe
asAdditive μ T C) (hT' : DominatedFinMeasAdditive μ' T C') (f : α -> E) : setToF
un μ T hT f = setToFun μ' T hT' f
参数：c c' : Real>=0∞；hc : c != ∞；hc' : c' != ∞；hμ_le : μ <= c • μ'；hμ'_le : μ' <= 
c' • μ；hT : DominatedFinMeasAdditive μ T C；hT' : DominatedFinMeasAdditive μ' T C
'；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_integrable`：setToFun_congr_measu
re_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <
= c' • μ) (hT : DominatedFinMeasAdditive…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MeasureTheory.Integrable.of_measure_le_smul`：∀ {α : Type u_1} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSp
ace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_congr_measure {μ' : Measure α} (c c' : ℝ≥0∞) (hc : c ≠ ∞) (hc' : c' ≠ ∞)
    (hμ_le : μ ≤ c • μ') (hμ'_le : μ' ≤ c' • μ) (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ' T C') (f : α → E) :
    setToFun μ T hT f = setToFun μ' T hT' f := by
  by_cases hf : Integrable f μ
  · exact setToFun_congr_measure_of_integrable c' hc' hμ'_le hT hT' f hf
  · -- if `f` is not integrable, both `setToFun` are 0.
    have h_int : ∀ g : α → E, ¬Integrable g μ → ¬Integrable g μ' := fun g =>
      mt fun h => h.of_measure_le_smul hc hμ_le
    simp_rw [setToFun_undef _ hf, setToFun_undef _ (h_int f hf)]
/-
**MeasureTheory.setToFun_congr_measure_of_add_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：setToFun_congr_measure_of_add_right {μ' : Measure α} (hT_add : DominatedFi
nMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C) (f : α -> E) 
(hf : Integrable f (μ + μ')) : setToFun (μ + μ') T hT_add f = setToFun μ T hT f
参数：hT_add : DominatedFinMeasAdditive (μ + μ') T C'；hT : DominatedFinMeasAdditive
 μ T C；f : α -> E；hf : Integrable f (μ + μ')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_integrable`：setToFun_congr_measu
re_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <
= c' • μ) (hT : DominatedFinMeasAdditive…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem setToFun_congr_measure_of_add_right {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  nth_rw 1 [← add_zero μ]
  exact add_le_add le_rfl bot_le
/-
**MeasureTheory.setToFun_congr_measure_of_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：setToFun_congr_measure_of_add_left {μ' : Measure α} (hT_add : DominatedFin
MeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C) (f : α -> E) 
(hf : Integrable f (μ + μ')) : setToFun (μ + μ') T hT_add f = setToFun μ' T hT f
参数：hT_add : DominatedFinMeasAdditive (μ + μ') T C'；hT : DominatedFinMeasAdditive
 μ' T C；f : α -> E；hf : Integrable f (μ + μ')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_integrable`：setToFun_congr_measu
re_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <
= c' • μ) (hT : DominatedFinMeasAdditive…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem setToFun_congr_measure_of_add_left {μ' : Measure α}
    (hT_add : DominatedFinMeasAdditive (μ + μ') T C') (hT : DominatedFinMeasAdditive μ' T C)
    (f : α → E) (hf : Integrable f (μ + μ')) :
    setToFun (μ + μ') T hT_add f = setToFun μ' T hT f := by
  refine setToFun_congr_measure_of_integrable 1 one_ne_top ?_ hT_add hT f hf
  rw [one_smul]
  exact Measure.le_add_left le_rfl
/-
**MeasureTheory.setToFun_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_add_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C
) (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrabl
e f ν) : setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f = setToFun μ T hT
μ f + setToFun ν T' hTν f
参数：hTμ : DominatedFinMeasAdditive μ T C；hTν : DominatedFinMeasAdditive ν T' C'；h
μ : Integrable f μ；hν : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure_right`：add_measure_ri
ght {_ : MeasurableSpace α} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T
 C) (hC : 0 <= C) : DominatedFinMeasAdditive (…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_le`：of_le (hT : DominatedFinMe
asAdditive μ T C) (hC : C <= C') : DominatedFinMeasAdditive μ T C'
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure_left`：add_measure_lef
t {_ : MeasurableSpace α} (μ ν : Measure α) (hT : DominatedFinMeasAdditive ν T C
) (hC : 0 <= C) : DominatedFinMeasAdditive (μ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure`：add_measure {C' : Re
al} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinM
easAdditive ν T' C') : DominatedFinMeasA…
· 使用定理 `MeasureTheory.setToFun_add_left`：setToFun_add_left (hT : DominatedFinMea
sAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (f : α -> E) : setToFu
n μ (T + T') (hT.add …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_add_right`：setToFun_congr_measur
e_of_add_right {μ' : Measure α} (hT_add : DominatedFinMeasAdditive (μ + μ') T C'
) (hT : DominatedFinMeasAdditive μ T C)…
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_add_left`：setToFun_congr_measure
_of_add_left {μ' : Measure α} (hT_add : DominatedFinMeasAdditive (μ + μ') T C') 
(hT : DominatedFinMeasAdditive μ' T C)…
-/
theorem setToFun_add_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun μ T hTμ f + setToFun ν T' hTν f :=
  have hTμ_add : DominatedFinMeasAdditive (μ + ν) T (max C 0) :=
    (hTμ.of_le (le_max_left C 0)).add_measure_right μ ν (le_max_right C 0)
  have hTν_add : DominatedFinMeasAdditive (μ + ν) T' (max C' 0) :=
    (hTν.of_le (le_max_left C' 0)).add_measure_left μ ν (le_max_right C' 0)
  calc
    setToFun (μ + ν) (T + T') (hTμ.add_measure μ ν hTν) f =
      setToFun (μ + ν) T hTμ_add f + setToFun (μ + ν) T' hTν_add f :=
        setToFun_add_left hTμ_add hTν_add f
    _ = setToFun μ T hTμ f + setToFun ν T' hTν f := by
      rw [setToFun_congr_measure_of_add_right hTμ_add hTμ f (hμ.add_measure hν),
        setToFun_congr_measure_of_add_left hTν_add hTν f (hμ.add_measure hν)]
/-
**MeasureTheory.setToFun_sub_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_sub_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C
) (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrabl
e f ν) : setToFun (μ + ν) (T - T') (hTμ.sub_measure μ ν hTν) f = setToFun μ T hT
μ f - setToFun ν T' hTν f
参数：hTμ : DominatedFinMeasAdditive μ T C；hTν : DominatedFinMeasAdditive ν T' C'；h
μ : Integrable f μ；hν : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.sub_measure`：sub_measure {C' : Re
al} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinM
easAdditive ν T' C') : DominatedFinMeasA…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.neg`：neg (hT : DominatedFinMeasAd
ditive μ T C) : DominatedFinMeasAdditive μ (-T) C
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.setToFun_add_measure`：setToFun_add_measure {ν : Measure α}
 (hTμ : DominatedFinMeasAdditive μ T C) (hTν : DominatedFinMeasAdditive ν T' C')
 (hμ : Integrable f μ) (…
· 使用定理 `MeasureTheory.setToFun_neg'`：setToFun_neg' (hT : DominatedFinMeasAdditiv
e μ T C) (f : α -> E) : setToFun μ (-T) hT.neg f = -setToFun μ T hT f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setToFun_sub_measure {ν : Measure α} (hTμ : DominatedFinMeasAdditive μ T C)
    (hTν : DominatedFinMeasAdditive ν T' C') (hμ : Integrable f μ) (hν : Integrable f ν) :
    setToFun (μ + ν) (T - T') (hTμ.sub_measure μ ν hTν) f =
      setToFun μ T hTμ f - setToFun ν T' hTν f := by
  simp [sub_eq_add_neg, setToFun_add_measure hTμ hTν.neg hμ hν, setToFun_neg' hTν]
/-
**MeasureTheory.setToFun_finsetSum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setToFun_finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty) {μ : ι -> 
Measure α} {T : ι -> Set α -> E ->L[Real] F} {C : ι -> Real} (hTs : forall i, Do
minatedFinMeasAdditive (μ i) (T i) (C i)) (hf : forall i in s, Integrable f (μ i
)) : setToFun (∑ i in s, μ i) (∑ i in s, T i) (DominatedFinMeasAdditive.finsetSu
m_measure hs μ T C hTs) f = ∑ i in s, setToFun (μ i) (T i) (hTs i) f
参数：hs : s.Nonempty；hTs : forall i, DominatedFinMeasAdditive (μ i) (T i) (C i)；hf
 : forall i in s, Integrable f (μ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.finsetSum_measure`：finsetSum_meas
ure {ι} {s : Finset ι} (hs : s.Nonempty) (μ : ι -> Measure α) (T : ι -> Set α ->
 β) (C : ι -> Real) (hT : forall i, DominatedF…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure`：add_measure {C' : Re
al} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinM
easAdditive ν T' C') : DominatedFinMeasA…
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `MeasureTheory.setToFun_add_measure`：setToFun_add_measure {ν : Measure α}
 (hTμ : DominatedFinMeasAdditive μ T C) (hTν : DominatedFinMeasAdditive ν T' C')
 (hμ : Integrable f μ) (…
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_finsetSum_measure`：integrable_finsetSum_measure
 [PseudoMetrizableSpace ε] {ι} {m : MeasurableSpace α} {f : α -> ε} {μ : ι -> Me
asure α} {s : Finset ι} : Integr…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
theorem setToFun_finsetSum_measure {ι} {s : Finset ι} (hs : s.Nonempty)
    {μ : ι → Measure α} {T : ι → Set α → E →L[ℝ] F} {C : ι → ℝ}
    (hTs : ∀ i, DominatedFinMeasAdditive (μ i) (T i) (C i))
    (hf : ∀ i ∈ s, Integrable f (μ i)) :
    setToFun (∑ i ∈ s, μ i) (∑ i ∈ s, T i)
      (DominatedFinMeasAdditive.finsetSum_measure hs μ T C hTs) f =
      ∑ i ∈ s, setToFun (μ i) (T i) (hTs i) f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | @cons i s his hs' ih =>
    simpa [his, ih fun j hj => hf j (Finset.mem_cons_of_mem hj)] using!
      setToFun_add_measure (hTs i) (DominatedFinMeasAdditive.finsetSum_measure hs' μ T C hTs)
      (hf i (Finset.mem_cons_self i s))
      (integrable_finsetSum_measure.2 fun j hj => hf j (Finset.mem_cons_of_mem hj))
/-
**MeasureTheory.setToFun_top_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f :
 α -> E) : setToFun (∞ • μ) T hT f = 0
参数：hT : DominatedFinMeasAdditive (∞ • μ) T C；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.setToFun_measure_zero'`：setToFun_measure_zero' (hT : Domin
atedFinMeasAdditive μ T C) (h : forall s, MeasurableSet s -> μ s < ∞ -> μ s = 0)
 : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem setToFun_top_smul_measure (hT : DominatedFinMeasAdditive (∞ • μ) T C) (f : α → E) :
    setToFun (∞ • μ) T hT f = 0 := by
  refine setToFun_measure_zero' hT fun s _ hμs => ?_
  rw [lt_top_iff_ne_top] at hμs
  simp only [true_and, Measure.smul_apply, ENNReal.mul_eq_top,
    top_ne_zero, Ne, not_false_iff, not_or, Classical.not_not, smul_eq_mul] at hμs
  simp only [hμs.right, Measure.smul_apply, mul_zero, smul_eq_mul]
/-
**MeasureTheory.setToFun_congr_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：setToFun_congr_smul_measure (c : Real>=0∞) (hc_ne_top : c != ∞) (hT : Domi
natedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C') (f
 : α -> E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f
参数：c : Real>=0∞；hc_ne_top : c != ∞；hT : DominatedFinMeasAdditive μ T C；hT_smul :
 DominatedFinMeasAdditive (c • μ) T C'；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.eq_zero`：eq_zero {β : Type*} [Nor
medAddCommGroup β] {T : Set α -> β} {C : Real} {_ : MeasurableSpace α} (hT : Dom
inatedFinMeasAdditive (0 : Measure α…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.setToFun_zero_left'`：setToFun_zero_left' (hT : DominatedFi
nMeasAdditive μ T C) (h_zero : forall s, MeasurableSet s -> μ s < ∞ -> T s = 0) 
: setToFun μ T hT f = 0
· 使用定理 `MeasureTheory.setToFun_measure_zero`：setToFun_measure_zero (hT : Dominat
edFinMeasAdditive μ T C) (h : μ = 0) : setToFun μ T hT f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun_congr_measure`：setToFun_congr_measure {μ' : Measu
re α} (c c' : Real>=0∞) (hc : c != ∞) (hc' : c' != ∞) (hμ_le : μ <= c • μ') (hμ'
_le : μ' <= c' • μ) (hT : …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem setToFun_congr_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  by_cases hc0 : c = 0
  · simp [hc0] at hT_smul
    have h : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0 := fun s hs _ => hT_smul.eq_zero hs
    rw [setToFun_zero_left' _ h, setToFun_measure_zero]
    simp [hc0]
  refine setToFun_congr_measure c⁻¹ c ?_ hc_ne_top (le_of_eq ?_) le_rfl hT hT_smul f
  · simp [hc0]
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]
/-
**MeasureTheory.setToFun_congr_smul_measure'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：setToFun_congr_smul_measure' (c : Real>=0) (hT : DominatedFinMeasAdditive 
μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C') (f : α -> E) : setToFun
 μ T hT f = setToFun (c • μ) T hT_smul f
参数：c : Real>=0；hT : DominatedFinMeasAdditive μ T C；hT_smul : DominatedFinMeasAdd
itive (c • μ) T C'；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `MeasureTheory.setToFun_congr_smul_measure`：setToFun_congr_smul_measure (
c : Real>=0∞) (hc_ne_top : c != ∞) (hT : DominatedFinMeasAdditive μ T C) (hT_smu
l : DominatedFinMeasAdditive (c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem setToFun_congr_smul_measure' (c : ℝ≥0)
    (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeasAdditive (c • μ) T C')
    (f : α → E) : setToFun μ T hT f = setToFun (c • μ) T hT_smul f := by
  rw! [ENNReal.smul_def]
  apply setToFun_congr_smul_measure _ (by simp)

/-- `setToFun` applied to the sum `T + T'` of two operators is the sum of the corresponding
`setToFun`. -/
/-
**MeasureTheory.setToFun_add_left''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_add_left'' {hT : DominatedFinMeasAdditive μ T C} {hT' : Dominated
FinMeasAdditive μ' T' C'} {hT'' : DominatedFinMeasAdditive μ'' T'' C''} (h : for
all s, MeasurableSet s -> (μ + μ') s < ∞ -> T'' s = T s + T' s) (hf : Integrable
 f μ) (hf' : Integrable f μ') (hμ : μ'' <= μ + μ') (hC : 0 <= C) (hC' : 0 <= C')
 (hC'' : 0 <= C'') : setToFun μ'' T'' hT'' f = setToFun μ T hT f + setToFun μ' T
' hT' f
参数：h : forall s, MeasurableSet s -> (μ + μ') s < ∞ -> T'' s = T s + T' s；hf : In
tegrable f μ；hf' : Integrable f μ'；hμ : μ'' <= μ + μ'；hC : 0 <= C；hC' : 0 <= C'；
hC'' : 0 <= C''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure_right`：add_measure_ri
ght {_ : MeasurableSpace α} (μ ν : Measure α) (hT : DominatedFinMeasAdditive μ T
 C) (hC : 0 <= C) : DominatedFinMeasAdditive (…
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_add_right`：setToFun_congr_measur
e_of_add_right {μ' : Measure α} (hT_add : DominatedFinMeasAdditive (μ + μ') T C'
) (hT : DominatedFinMeasAdditive μ T C)…
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.add_measure_left`：add_measure_lef
t {_ : MeasurableSpace α} (μ ν : Measure α) (hT : DominatedFinMeasAdditive ν T C
) (hC : 0 <= C) : DominatedFinMeasAdditive (μ…
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_add_left`：setToFun_congr_measure
_of_add_left {μ' : Measure α} (hT_add : DominatedFinMeasAdditive (μ + μ') T C') 
(hT : DominatedFinMeasAdditive μ' T C)…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.of_measure_le`：of_measure_le {μ' 
: Measure α} (h : μ <= μ') (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) :
 DominatedFinMeasAdditive μ' T C
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_integrable`：setToFun_congr_measu
re_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <
= c' • μ) (hT : DominatedFinMeasAdditive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setToFun_add_left'`：setToFun_add_left' (hT : DominatedFinM
easAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFin
MeasAdditive μ T'' C''…

--- 原说明 ---
`setToFun` applied to the sum `T + T'` of two operators is the sum of the corres
ponding
`setToFun`.
-/
theorem setToFun_add_left'' {hT : DominatedFinMeasAdditive μ T C}
    {hT' : DominatedFinMeasAdditive μ' T' C'} {hT'' : DominatedFinMeasAdditive μ'' T'' C''}
    (h : ∀ s, MeasurableSet s → (μ + μ') s < ∞ → T'' s = T s + T' s)
    (hf : Integrable f μ) (hf' : Integrable f μ') (hμ : μ'' ≤ μ + μ')
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hC'' : 0 ≤ C'') :
    setToFun μ'' T'' hT'' f = setToFun μ T hT f + setToFun μ' T' hT' f := by
  have I : DominatedFinMeasAdditive (μ + μ') T C := .add_measure_right _ _ hT hC
  have A : setToFun (μ + μ') T I f = setToFun μ T hT f :=
    setToFun_congr_measure_of_add_right _ _ _ (hf.add_measure hf')
  have I' : DominatedFinMeasAdditive (μ + μ') T' C' := .add_measure_left _ _ hT' hC'
  have A' : setToFun (μ + μ') T' I' f = setToFun μ' T' hT' f :=
    setToFun_congr_measure_of_add_left _ _ _ (hf.add_measure hf')
  have I'' : DominatedFinMeasAdditive (μ + μ') T'' C'' := .of_measure_le hμ hT'' hC''
  have A'' : setToFun (μ + μ') T'' I'' f = setToFun μ'' T'' hT'' f := by
    apply setToFun_congr_measure_of_integrable (c' := 1) (by simp) (by simpa using hμ)
    apply hf.add_measure hf'
  rw [← A, ← A', ← A'']
  apply setToFun_add_left' _ _ _ h
/-
**MeasureTheory.norm_setToFun_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α ->₁
[μ] E) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= C * ‖f‖
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁[μ] E；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm`：norm_setToL1_le_mul_norm (hT 
: DominatedFinMeasAdditive μ T C) (hC : 0 <= C) (f : α ->₁[μ] E) : ‖setToL1 hT f
‖ <= C * ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_setToFun_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E)
    (hC : 0 ≤ C) : ‖setToFun μ T hT f‖ ≤ C * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm hT hC f
/-
**MeasureTheory.norm_setToFun_le_mul_norm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α ->
₁[μ] E) : ‖setToFun μ T hT f‖ <= max C 0 * ‖f‖
参数：hT : DominatedFinMeasAdditive μ T C；f : α ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L1.setToFun_eq_setToL1`：∀ {α : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 
: NormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm'`：norm_setToL1_le_mul_norm' (h
T : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) : ‖setToL1 hT f‖ <= max C 0
 * ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_setToFun_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [L1.setToFun_eq_setToL1]
  exact L1.norm_setToL1_le_mul_norm' hT f
/-
**MeasureTheory.norm_setToFun_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f 
μ) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= C * ‖hf.toL1 f‖
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm`：norm_setToL1_le_mul_norm (hT 
: DominatedFinMeasAdditive μ T C) (hC : 0 <= C) (f : α ->₁[μ] E) : ‖setToL1 hT f
‖ <= C * ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ C * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm hT hC _
/-
**MeasureTheory.norm_setToFun_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f
 μ) : ‖setToFun μ T hT f‖ <= max C 0 * ‖hf.toL1 f‖
参数：hT : DominatedFinMeasAdditive μ T C；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_eq`：setToFun_eq [hF : CompleteSpace F] (hT : Domi
natedFinMeasAdditive μ T C) (hf : Integrable f μ) : setToFun μ T hT f = L1.setTo
L1 hT (hf.toL1 …
· 使用定理 `MeasureTheory.L1.norm_setToL1_le_mul_norm'`：norm_setToL1_le_mul_norm' (h
T : DominatedFinMeasAdditive μ T C) (f : α ->₁[μ] E) : ‖setToL1 hT f‖ <= max C 0
 * ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_setToFun_le' (hT : DominatedFinMeasAdditive μ T C) (hf : Integrable f μ) :
    ‖setToFun μ T hT f‖ ≤ max C 0 * ‖hf.toL1 f‖ := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero]
    positivity
  rw [setToFun_eq hT hf]
  exact L1.norm_setToL1_le_mul_norm' hT _
/-
**MeasureTheory.enorm_setToFun_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：enorm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C) : ‖s
etToFun μ T hT f‖ₑ <= NNReal.mk C hC * ∫⁻ x, ‖f x‖ₑ ∂μ
参数：hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.norm_setToFun_le`：norm_setToFun_le (hT : DominatedFinMeasA
dditive μ T C) (hf : Integrable f μ) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= C * 
‖hf.toL1 f‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Integrable.norm_toL1_eq_lintegral_enorm`：norm_toL1_eq_lint
egral_enorm (f : α -> β) (hf : Integrable f μ) : ‖hf.toL1 f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ)
.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem enorm_setToFun_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ₑ ≤ NNReal.mk C hC * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  by_cases hf : Integrable f μ; swap
  · simp [setToFun_undef _ hf]
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) hf.hasFiniteIntegral.ne)).1
  simp only [toReal_enorm, toReal_mul, coe_toReal, NNReal.coe_mk]
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  apply le_of_eq
  rw [Integrable.norm_toL1_eq_lintegral_enorm]
/-
**MeasureTheory.norm_setToFun_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：norm_setToFun_le_toReal (hT : DominatedFinMeasAdditive μ T C) (hC : 0 <= C
) : ‖setToFun μ T hT f‖ <= NNReal.mk C hC * ENNReal.toReal (∫⁻ a, ENNReal.ofReal
 ‖f a‖ ∂μ)
参数：hT : DominatedFinMeasAdditive μ T C；hC : 0 <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.norm_setToFun_le`：norm_setToFun_le (hT : DominatedFinMeasA
dditive μ T C) (hf : Integrable f μ) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= C * 
‖hf.toL1 f‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.norm_toL1_eq_lintegral_enorm`：norm_toL1_eq_lint
egral_enorm (f : α -> β) (hf : Integrable f μ) : ‖hf.toL1 f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ)
.toReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem norm_setToFun_le_toReal (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    ‖setToFun μ T hT f‖ ≤ NNReal.mk C hC * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  by_cases hF : CompleteSpace F; swap
  · simp only [setToFun, hF, ↓reduceDIte, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  by_cases hf : Integrable f μ; swap
  · simp only [setToFun_undef _ hf, norm_zero, NNReal.coe_mk, ofReal_norm]
    positivity
  apply (norm_setToFun_le hT hf hC).trans
  gcongr
  · simp
  rw [Integrable.norm_toL1_eq_lintegral_enorm]
  simp

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `setToFun`.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
/-
**MeasureTheory.tendsto_setToFun_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ
 T C) {fs : Nat -> α -> E} {f : α -> E} (bound : α -> Real) (fs_measurable : for
all n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ) (h
_bound : forall n, forallᵐ a ∂μ, ‖fs n a‖ <= bound a) (h_lim : forallᵐ a ∂μ, Ten
dsto (fun n => fs n a) atTop (𝓝 (f a))) : Tendsto (fun n => setToFun μ T hT (fs 
n)) atTop (𝓝 <| setToFun μ T hT f)
参数：hT : DominatedFinMeasAdditive μ T C；bound : α -> Real；fs_measurable : forall 
n, AEStronglyMeasurable (fs n) μ；bound_integrable : Integrable bound μ；h_bound :
 forall n, forallᵐ a ∂μ, ‖fs n a‖ <= bound a；h_lim : forallᵐ a ∂μ, Tendsto (fun 
n => fs n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.hasFiniteIntegral_of_dominated_convergence`：hasFiniteInteg
ral_of_dominated_convergence (bound_hasFiniteIntegral : HasFiniteIntegral bound 
μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ …
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.L1.tendsto_setToL1`：tendsto_setToL1 (hT : DominatedFinMeas
Additive μ T C) (f : α ->₁[μ] E) {ι} (fs : ι -> α ->₁[μ] E) {l : Filter ι} (hfs 
: Tendsto fs l (𝓝 f)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `MeasureTheory.tendsto_lintegral_norm_of_dominated_convergence`：tendsto_l
integral_norm_of_dominated_convergence (F_measurable : forall n, AEStronglyMeasu
rable (F n) μ) (bound_hasFiniteIntegral : HasFinite…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.L1.norm_def`：norm_def (f : α ->₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a
‖ₑ ∂μ).toReal
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Lebesgue dominated convergence theorem provides sufficient conditions under whic
h almost
  everywhere convergence of a sequence of functions implies the convergence of t
heir image by
  `setToFun`.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral
 bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications provi
ng integrability
  is easier.
-/
theorem tendsto_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {fs : ℕ → α → E} {f : α → E} (bound : α → ℝ)
    (fs_measurable : ∀ n, AEStronglyMeasurable (fs n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) atTop (𝓝 <| setToFun μ T hT f) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  -- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions.
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ fs_measurable h_lim
  -- all functions we consider are integrable
  have fs_int : ∀ n, Integrable (fs n) μ := fun n =>
    bound_integrable.mono' (fs_measurable n) (h_bound _)
  have f_int : Integrable f μ :=
    ⟨f_measurable,
      hasFiniteIntegral_of_dominated_convergence bound_integrable.hasFiniteIntegral h_bound
        h_lim⟩
  -- it suffices to prove the result for the corresponding L1 functions
  suffices
    Tendsto (fun n => L1.setToL1 hT ((fs_int n).toL1 (fs n))) atTop
      (𝓝 (L1.setToL1 hT (f_int.toL1 f))) by
    convert! this with n
    · exact setToFun_eq hT (fs_int n)
    · exact setToFun_eq hT f_int
  -- the convergence of setToL1 follows from the convergence of the L1 functions
  refine L1.tendsto_setToL1 hT _ _ ?_
  -- up to some rewriting, what we need to prove is `h_lim`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have lintegral_norm_tendsto_zero :
    Tendsto (fun n => ENNReal.toReal <| ∫⁻ a, ENNReal.ofReal ‖fs n a - f a‖ ∂μ) atTop (𝓝 0) :=
    (tendsto_toReal zero_ne_top).comp
      (tendsto_lintegral_norm_of_dominated_convergence fs_measurable
        bound_integrable.hasFiniteIntegral h_bound h_lim)
  convert! lintegral_norm_tendsto_zero with n
  rw [L1.norm_def]
  congr 1
  refine lintegral_congr_ae ?_
  rw [← Integrable.toL1_sub]
  refine ((fs_int n).sub f_int).coeFn_toL1.mono fun x hx => ?_
  dsimp only
  rw [hx, ofReal_norm, Pi.sub_apply]

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
/-
**MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdd
itive μ T C) {ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -> α -> E} {f :
 α -> E} (bound : α -> Real) (hfs_meas : forallᶠ n in l, AEStronglyMeasurable (f
s n) μ) (h_bound : forallᶠ n in l, forallᵐ a ∂μ, ‖fs n a‖ <= bound a) (bound_int
egrable : Integrable bound μ) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => fs n a) l
 (𝓝 (f a))) : Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT 
f)
参数：hT : DominatedFinMeasAdditive μ T C；bound : α -> Real；hfs_meas : forallᶠ n in
 l, AEStronglyMeasurable (fs n) μ；h_bound : forallᶠ n in l, forallᵐ a ∂μ, ‖fs n 
a‖ <= bound a；bound_integrable : Integrable bound μ；h_lim : forallᵐ a ∂μ, Tendst
o (fun n => fs n a) l (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_iff_seq_tendsto`：tendsto_iff_seq_tendsto {f : α -> β} {k 
: Filter α} {l : Filter β} [k.IsCountablyGenerated] : Tendsto f k l ↔ forall x :
 Nat -> α, Tendsto x…
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `MeasureTheory.tendsto_setToFun_of_dominated_convergence`：tendsto_setToFu
n_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {fs : Nat -> α 
-> E} {f : α -> E} (bound : α -> Real) (fs_me…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …

--- 原说明 ---
Lebesgue dominated convergence theorem for filters with a countable basis
-/
theorem tendsto_setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι}
    {l : Filter ι} [l.IsCountablyGenerated] {fs : ι → α → E} {f : α → E} (bound : α → ℝ)
    (hfs_meas : ∀ᶠ n in l, AEStronglyMeasurable (fs n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => fs n a) l (𝓝 (f a))) :
    Tendsto (fun n => setToFun μ T hT (fs n)) l (𝓝 <| setToFun μ T hT f) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl : ∀ s ∈ l, ∃ a, ∀ b ≥ a, x b ∈ s := by rwa [tendsto_atTop'] at xl
  have h :
    { x : ι | (fun n => AEStronglyMeasurable (fs n) μ) x } ∩
        { x : ι | (fun n => ∀ᵐ a ∂μ, ‖fs n a‖ ≤ bound a) x } ∈ l :=
    inter_mem hfs_meas h_bound
  obtain ⟨k, h⟩ := hxl _ h
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_setToFun_of_dominated_convergence hT bound ?_ bound_integrable ?_ ?_
  · exact fun n => (h _ (self_le_add_left _ _)).1
  · exact fun n => (h _ (self_le_add_left _ _)).2
  · filter_upwards [h_lim]
    refine fun a h_lin => @Tendsto.comp _ _ _ (fun n => x (n + k)) (fun n => fs n a) _ _ _ h_lin ?_
    rwa [tendsto_add_atTop_iff_nat]

/-- Lebesgue dominated convergence theorem for series. -/
/-
**MeasureTheory.hasSum_setToFun_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：hasSum_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ 
T C) {ι} [Countable ι] {F : ι -> α -> E} {f : α -> E} (bound : ι -> α -> Real) (
hF_meas : forall n, AEStronglyMeasurable (F n) μ) (h_bound : forall n, forallᵐ a
 ∂μ, ‖F n a‖ <= bound n a) (bound_summable : forallᵐ a ∂μ, Summable fun n => bou
nd n a) (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ) (h_lim : fo
rallᵐ a ∂μ, HasSum (fun n => F n a) (f a)) : HasSum (fun n => setToFun μ T hT (F
 n)) (setToFun μ T hT f)
参数：hT : DominatedFinMeasAdditive μ T C；bound : ι -> α -> Real；hF_meas : forall n
, AEStronglyMeasurable (F n) μ；h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= boun
d n a；bound_summable : forallᵐ a ∂μ, Summable fun n => bound n a；bound_integrabl
e : Integrable (fun a => ∑' n, bound n a) μ；h_lim : forallᵐ a ∂μ, HasSum (fun n 
=> F n a) (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Summable.le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι
} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_
3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setToFun_finsetSum`：setToFun_finsetSum (hT : DominatedFinM
easAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E} (hf : forall i in s, Int
egrable (f i) μ) : (se…
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Finset.aestronglyMeasurable_fun_sum`：∀ {α : Type u_1} {m₀ : MeasurableSp
ace α} {μ : MeasureTheory.Measure α} {M : Type u_5} [inst : AddCommMonoid M]   [
inst_1 : TopologicalSpace…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Lebesgue dominated convergence theorem for series.
-/
theorem hasSum_setToFun_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {F : ι → α → E} {f : α → E}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => setToFun μ T hT (F n)) (setToFun μ T hT f) := by
  have hb_nonneg : ∀ᵐ a ∂μ, ∀ n, 0 ≤ bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : ∀ n, bound n ≤ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using ha_sum.le_tsum _ fun i _ => ha0 i
  have hF_integrable : ∀ n, Integrable (F n) μ := by
    refine fun n => bound_integrable.mono' (hF_meas n) ?_
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← setToFun_finsetSum _ _ fun n _ => hF_integrable n]
  refine tendsto_setToFun_filter_of_dominated_convergence _
      (fun a => ∑' n, bound n a) ?_ ?_ bound_integrable h_lim
  · exact Eventually.of_forall fun s => s.aestronglyMeasurable_fun_sum fun n _ => hF_meas n
  · filter_upwards with s
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n ∈ s, F n a‖ ≤ ∑ n ∈ s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ ≤ ∑' n, bound n a := has.sum_le_tsum _ (fun n _ => ha0 n)
/-
**MeasureTheory.setToFun_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setToFun_tsum [CompleteSpace E] (hT : DominatedFinMeasAdditive μ T C) {ι} 
[Countable ι] {f : ι -> α -> E} (hf : forall i, AEStronglyMeasurable (f i) μ) (h
f' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞) : setToFun μ T hT (fun a => ∑' i, f i a) 
= ∑' i, setToFun μ T hT (f i)
参数：hT : DominatedFinMeasAdditive μ T C；hf : forall i, AEStronglyMeasurable (f i)
 μ；hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_lt_top'`：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `AEMeasurable.tsum`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst 
: MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] 
[Topolo…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable_coe`：tsum_coe_ne_top_iff_summable_c
oe {f : α -> Real>=0} : (∑' a, (f a : Real>=0∞)) != ∞ ↔ Summable fun a => (f a :
 Real)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.hasSum_setToFun_of_dominated_convergence`：hasSum_setToFun_
of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι} [Countable ι]
 {F : ι -> α -> E} {f : α -> E} (bound : ι -…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.tsum`：∀ {X : Type u_4} {E : Type u_5}
 {ι : Type u_6} [inst : MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 
: TopologicalSpace E] [Contin…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
（共 56 条，此处仅展示前 30 条）
-/
theorem setToFun_tsum [CompleteSpace E] (hT : DominatedFinMeasAdditive μ T C)
    {ι} [Countable ι] {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ ≠ ∞) :
    setToFun μ T hT (fun a ↦ ∑' i, f i a) = ∑' i, setToFun μ T hT (f i) := by
  by_cases hF : CompleteSpace F; swap
  · simp [setToFun, hF]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : ∀ᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert!
    (MeasureTheory.hasSum_setToFun_of_dominated_convergence hT (fun i a => ‖f i a‖₊) hf _ hhh ⟨_, _⟩
        _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · fun_prop
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert! this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum

/-- Corollary of the Lebesgue dominated convergence theorem: If a sequence of functions `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwise to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` converge
to the integral of `f`. -/
/-
**MeasureTheory.tendsto_setToFun_filter_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_setToFun_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ 
T C) {ι} {l : Filter ι} [l.IsCountablyGenerated] {F : ι -> α -> E} [IsFiniteMeas
ure μ] {f : α -> E} (h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ) (h_b
ound : exists C, forallᶠ n in l, forallᵐ ω ∂μ, ‖F n ω‖ <= C) (h_lim : forallᵐ ω 
∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) : Tendsto (fun n => setToFun μ T hT (F
 n)) l (𝓝 (setToFun μ T hT f))
参数：hT : DominatedFinMeasAdditive μ T C；h_meas : forallᶠ n in l, AEStronglyMeasur
able (F n) μ；h_bound : exists C, forallᶠ n in l, forallᵐ ω ∂μ, ‖F n ω‖ <= C；h_li
m : forallᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ

--- 原说明 ---
Corollary of the Lebesgue dominated convergence theorem: If a sequence of functi
ons `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwis
e to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` c
onverge
to the integral of `f`.
-/
theorem tendsto_setToFun_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ T C)
    {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → E} [IsFiniteMeasure μ] {f : α → E}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C, ∀ᶠ n in l, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => setToFun μ T hT (F n)) l (𝓝 (setToFun μ T hT f)) := by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α → ℝ := (fun _ => c)
  exact tendsto_setToFun_filter_of_dominated_convergence hT
    C h_meas h_boundc (integrable_const c) h_lim

omit [NormedSpace ℝ E] in
/-
**MeasureTheory._root_.measurableSet_integrable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableSet_integrable {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    MeasurableSet {x | Integrable (f x) μ} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. This version has `f` in curried form. -/
/-
**MeasureTheory.StronglyMeasurable.setToFun_prod_right** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCommGroup F] [inst_3 : Normed
Space ℝ F] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {T : Set α → 
E →L[ℝ] F} {C : ℝ} {β : Type u_7} {mβ : MeasurableSpace β} [MeasureTheory.SFinit
e μ]   (hT : MeasureTheory.DominatedFinMeasAdditive μ T C),   (∀ (s : Set (β × α
)), MeasurableSet s → MeasureTheory.StronglyMeasurable fun x => T (Prod.mk x ⁻¹'
 s)) →     ∀ ⦃f : β → α → E⦄,       MeasureTheory.StronglyMeasurable (Function.u
ncurry f) →         MeasureTheory.StronglyMeasurable fun x => MeasureTheory.setT
oFun μ T hT (f x)
参数：hT : MeasureTheory.DominatedFinMeasAdditive μ T C；∀ (s : Set (β × α)), Measur
ableSet s → MeasureTheory.StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.setToSimpleFunc_eq_sum_of_subset`：setToSimpleFu
nc_eq_sum_of_subset [DecidablePred fun x : F => x != 0] (T : Set α -> F ->L[Real
] F') (hT : T ∅ = 0) {f : α ->ₛ F} {s : Finset …
· 使用定理 `MeasureTheory.FinMeasAdditive.map_empty_eq_zero`：map_empty_eq_zero {β} [
AddCancelMonoid β] {T : Set α -> β} (hT : FinMeasAdditive μ T) : T ∅ = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.stronglyMeasurable_fun_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measu
rableSpace α} {ι : Type…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `StronglyMeasurable.apply_continuousLinearMap`：StronglyMeasurable.apply_c
ontinuousLinearMap {_m : MeasurableSpace α} {φ : α -> F ->L[𝕜] E} (hφ : Strongly
Measurable φ) (v : F) : StronglyMe…
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `measurableSet_integrable`：∀ {α : Type u_1} {E : Type u_2} [inst : Normed
AddCommGroup E] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {β : Typ
e u_7} {mβ : M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
The `setToFun` operation is measurable. This shows that the integrand of (the ri
ght-hand-side
of) Fubini's theorem is measurable. This version has `f` in curried form.
-/
theorem StronglyMeasurable.setToFun_prod_right {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (β × α)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : β → α → E⦄ (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun x => setToFun μ T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  have : SeparableSpace (range (Function.uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (β × α) E :=
    SimpleFunc.approxOn _ hf.measurable (range (Function.uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → β → SimpleFunc α E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : ℕ → β → F := fun n =>
    {x | Integrable (f x) μ}.indicator fun x => (s' n x).setToSimpleFunc T
  have hf' n : StronglyMeasurable (f' n) := by
    refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have : ∀ x, ((s' n x).range.filter fun x => x ≠ 0) ⊆ (s n).range := by
      intro x; refine Finset.Subset.trans (Finset.filter_subset _ _) ?_; intro y
      simp_rw [SimpleFunc.mem_range]; rintro ⟨z, rfl⟩; exact ⟨(x, z), rfl⟩
    simp_rw [SimpleFunc.setToSimpleFunc_eq_sum_of_subset T hT.1.map_empty_eq_zero (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply StronglyMeasurable.apply_continuousLinearMap
    apply h'T
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : β => setToFun μ T hT (f x)) := by
    apply tendsto_pi_nhds.2 fun x ↦ ?_
    by_cases hfx : Integrable (f x) μ
    · have (n : _) : Integrable (s' n x) μ := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [mem_ofPred_eq, hfx, indicator_of_mem, this,
        ← setToFun_simpleFunc_eq_setToSimpleFunc hT, f']
      refine
        tendsto_setToFun_of_dominated_convergence hT (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · refine fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le ?_ ?_ (x, y) n
        · exact hf.measurable
        · simp
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn ?_ ?_ ?_
        · exact hf.measurable.of_uncurry_left
        · simp
        apply subset_closure
        simp [-Function.uncurry_apply_pair]
    · simp [f', hfx, setToFun_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
/-
**MeasureTheory.continuousWithinAt_setToFun_of_dominated** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：continuousWithinAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ 
T C) {fs : X -> α -> E} {x₀ : X} {bound : α -> Real} {s : Set X} (hfs_meas : for
allᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (fs x) μ) (h_bound : forallᶠ x in 𝓝[s] x
₀, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrable : Integrable bound μ) (h
_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => fs x a) s x₀) : ContinuousWit
hinAt (fun x => setToFun μ T hT (fs x)) s x₀
参数：hT : DominatedFinMeasAdditive μ T C；hfs_meas : forallᶠ x in 𝓝[s] x₀, AEStrong
lyMeasurable (fs x) μ；h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖fs x a‖ <= 
bound a；bound_integrable : Integrable bound μ；h_cont : forallᵐ a ∂μ, ContinuousW
ithinAt (fun x => fs x a) s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
-/
theorem continuousWithinAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C)
    {fs : X → α → E} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hfs_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => fs x a) s x₀) :
    ContinuousWithinAt (fun x => setToFun μ T hT (fs x)) s x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›
/-
**MeasureTheory.continuousAt_setToFun_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：continuousAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {
fs : X -> α -> E} {x₀ : X} {bound : α -> Real} (hfs_meas : forallᶠ x in 𝓝 x₀, AE
StronglyMeasurable (fs x) μ) (h_bound : forallᶠ x in 𝓝 x₀, forallᵐ a ∂μ, ‖fs x a
‖ <= bound a) (bound_integrable : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Co
ntinuousAt (fun x => fs x a) x₀) : ContinuousAt (fun x => setToFun μ T hT (fs x)
) x₀
参数：hT : DominatedFinMeasAdditive μ T C；hfs_meas : forallᶠ x in 𝓝 x₀, AEStronglyM
easurable (fs x) μ；h_bound : forallᶠ x in 𝓝 x₀, forallᵐ a ∂μ, ‖fs x a‖ <= bound 
a；bound_integrable : Integrable bound μ；h_cont : forallᵐ a ∂μ, ContinuousAt (fun
 x => fs x a) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
-/
theorem continuousAt_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {x₀ : X} {bound : α → ℝ} (hfs_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => fs x a) x₀) :
    ContinuousAt (fun x => setToFun μ T hT (fs x)) x₀ :=
  tendsto_setToFun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›
/-
**MeasureTheory.continuousOn_setToFun_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：continuousOn_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {
fs : X -> α -> E} {bound : α -> Real} {s : Set X} (hfs_meas : forall x in s, AES
tronglyMeasurable (fs x) μ) (h_bound : forall x in s, forallᵐ a ∂μ, ‖fs x a‖ <= 
bound a) (bound_integrable : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Continu
ousOn (fun x => fs x a) s) : ContinuousOn (fun x => setToFun μ T hT (fs x)) s
参数：hT : DominatedFinMeasAdditive μ T C；hfs_meas : forall x in s, AEStronglyMeasu
rable (fs x) μ；h_bound : forall x in s, forallᵐ a ∂μ, ‖fs x a‖ <= bound a；bound_
integrable : Integrable bound μ；h_cont : forallᵐ a ∂μ, ContinuousOn (fun x => fs
 x a) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.continuousWithinAt_setToFun_of_dominated`：continuousWithin
At_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E
} {x₀ : X} {bound : α -> Real} {s : Set X} (…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem continuousOn_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} {s : Set X} (hfs_meas : ∀ x ∈ s, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => fs x a) s) :
    ContinuousOn (fun x => setToFun μ T hT (fs x)) s := by
  intro x hx
  refine continuousWithinAt_setToFun_of_dominated hT ?_ ?_ bound_integrable ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx using hfs_meas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx using h_bound x hx
  · filter_upwards [h_cont] with a ha using ha x hx
/-
**MeasureTheory.continuous_setToFun_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：continuous_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs
 : X -> α -> E} {bound : α -> Real} (hfs_meas : forall x, AEStronglyMeasurable (
fs x) μ) (h_bound : forall x, forallᵐ a ∂μ, ‖fs x a‖ <= bound a) (bound_integrab
le : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Continuous fun x => fs x a) : C
ontinuous fun x => setToFun μ T hT (fs x)
参数：hT : DominatedFinMeasAdditive μ T C；hfs_meas : forall x, AEStronglyMeasurable
 (fs x) μ；h_bound : forall x, forallᵐ a ∂μ, ‖fs x a‖ <= bound a；bound_integrable
 : Integrable bound μ；h_cont : forallᵐ a ∂μ, Continuous fun x => fs x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MeasureTheory.continuousAt_setToFun_of_dominated`：continuousAt_setToFun_
of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {x₀ : X} {
bound : α -> Real} (hfs_meas : forallᶠ…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem continuous_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X → α → E}
    {bound : α → ℝ} (hfs_meas : ∀ x, AEStronglyMeasurable (fs x) μ)
    (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖fs x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, Continuous fun x => fs x a) : Continuous fun x => setToFun μ T hT (fs x) :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_setToFun_of_dominated hT (Eventually.of_forall hfs_meas)
        (Eventually.of_forall h_bound) ‹_› <|
      h_cont.mono fun _ => Continuous.continuousAt

end Function

end MeasureTheory

