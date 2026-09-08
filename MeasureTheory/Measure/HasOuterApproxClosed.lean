/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Spaces where indicators of closed sets have decreasing approximations by continuous functions

In this file we define a typeclass `HasOuterApproxClosed` for topological spaces in which indicator
functions of closed sets have sequences of bounded continuous functions approximating them from
above. All pseudo-emetrizable spaces have this property, see `instHasOuterApproxClosed`.

In spaces with the `HasOuterApproxClosed` property, finite Borel measures are uniquely characterized
by the integrals of bounded continuous functions. Also weak convergence of finite measures and
convergence in distribution for random variables behave somewhat well in spaces with this property.

## Main definitions

* `HasOuterApproxClosed`: the typeclass for topological spaces in which indicator functions of
  closed sets have sequences of bounded continuous functions approximating them.
* `IsClosed.apprSeq`: a (non-constructive) choice of an approximating sequence to the indicator
  function of a closed set.

## Main results

* `instHasOuterApproxClosed`: Any pseudo-emetrizable space has the property `HasOuterApproxClosed`.
* `tendsto_lintegral_apprSeq`: The integrals of the approximating functions to the indicator of a
  closed set tend to the measure of the set.
* `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`: Two finite measures are equal if the integrals
  of all bounded continuous functions with respect to both agree.

-/

@[expose] public section

open BoundedContinuousFunction MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section auxiliary

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere;
* integration is `MeasureTheory.lintegral`, i.e., the functions and their integrals are
  `ℝ≥0∞`-valued.
-/
/-
**MeasureTheory.tendsto_lintegral_nn_filter_of_le_const** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : Filter ι} [L.IsCo
untablyGenerated] (μ : Measure Ω) [IsFiniteMeasure μ] {fs : ι -> Ω ->ᵇ Real>=0} 
{c : Real>=0} (fs_le_const : forallᶠ i in L, forallᵐ ω : Ω ∂μ, fs i ω <= c) {f :
 Ω -> Real>=0} (fs_lim : forallᵐ ω : Ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (f ω))
) : Tendsto (fun i => ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ))
参数：μ : Measure Ω；fs_le_const : forallᶠ i in L, forallᵐ ω : Ω ∂μ, fs i ω <= c；fs_
lim : forallᵐ ω : Ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (f ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence`：tendsto
_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGene
rated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_const_lt_top`：lintegral_const_lt_top [IsFiniteMe
asure μ] {c : Real>=0∞} (hc : c != ∞) : ∫⁻ _, c ∂μ < ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞

--- 原说明 ---
A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant
 and tend to a
limit, then their integrals against the finite measure tend to the integral of t
he limit.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere;
* integration is `MeasureTheory.lintegral`, i.e., the functions and their integr
als are
  `ℝ≥0∞`-valued.
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    (μ : Measure Ω) [IsFiniteMeasure μ] {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i ↦ fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i ↦ ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ c)
    (Eventually.of_forall fun i ↦ (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] using fs_le_const
  · simpa only [Function.comp_apply, ENNReal.tendsto_coe] using fs_lim

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere.
-/
/-
**MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
 [L.IsCountablyGenerated] (μ : Measure Ω) [IsFiniteMeasure μ] {c : Real>=0} {E :
 Set Ω} (E_mble : MeasurableSet E) (fs : ι -> Ω ->ᵇ Real>=0) (fs_bdd : forallᶠ i
 in L, forallᵐ ω : Ω ∂μ, fs i ω <= c) (fs_lim : forallᵐ ω ∂μ, Tendsto (fun i => 
fs i ω) L (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω))) : Tendsto (fun n => lint
egral μ fun ω => fs n ω) L (𝓝 (μ E))
参数：μ : Measure Ω；E_mble : MeasurableSet E；fs : ι -> Ω ->ᵇ Real>=0；fs_bdd : foral
lᶠ i in L, forallᵐ ω : Ω ∂μ, fs i ω <= c；fs_lim : forallᵐ ω ∂μ, Tendsto (fun i =
> fs i ω) L (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_indicator`：coe_indicator {α} (s : Set α) (f : α -> Real>=0) 
(a : α) : ((s.indicator f a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x
)) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.tendsto_lintegral_nn_filter_of_le_const`：tendsto_lintegral
_nn_filter_of_le_const {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated] (μ : 
Measure Ω) [IsFiniteMeasure μ] {fs : ι -> Ω…

--- 原说明 ---
If bounded continuous functions tend to the indicator of a measurable set and ar
e
uniformly bounded, then their integrals against a finite measure tend to the mea
sure of the set.
This formulation assumes:
* the functions tend to a limit along a countably generated filter;
* the limit is in the almost everywhere sense;
* boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι → Ω →ᵇ ℝ≥0)
    (fs_bdd : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c)
    (fs_lim : ∀ᵐ ω ∂μ, Tendsto (fun i ↦ fs i ω) L (𝓝 (indicator E (fun _ ↦ (1 : ℝ≥0)) ω))) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ fs n ω) L (𝓝 (μ E)) := by
  convert! tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ ω, indicator E (fun _ ↦ (1 : ℝ≥0∞)) ω = ↑(indicator E (fun _ ↦ (1 : ℝ≥0)) ω) :=
    fun ω ↦ by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator E_mble]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
/-
**MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：measure_of_cont_bdd_of_tendsto_indicator (μ : Measure Ω) [IsFiniteMeasure 
μ] {c : Real>=0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : Nat -> Ω ->ᵇ Real>
=0) (fs_bdd : forall n ω, fs n ω <= c) (fs_lim : Tendsto (fun n ω => fs n ω) atT
op (𝓝 (indicator E fun _ => (1 : Real>=0)))) : Tendsto (fun n => lintegral μ fun
 ω => fs n ω) atTop (𝓝 (μ E))
参数：μ : Measure Ω；E_mble : MeasurableSet E；fs : Nat -> Ω ->ᵇ Real>=0；fs_bdd : for
all n ω, fs n ω <= c；fs_lim : Tendsto (fun n ω => fs n ω) atTop (𝓝 (indicator E 
fun _ => (1 : Real>=0)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`：measure_o
f_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι} [L.IsCountably
Generated] (μ : Measure Ω) [IsFiniteMeasure μ] {c :…
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
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If a sequence of bounded continuous functions tends to the indicator of a measur
able set and
the functions are uniformly bounded, then their integrals against a finite measu
re tend to the
measure of the set.

A similar result with more general assumptions is
`MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : ℕ → Ω →ᵇ ℝ≥0) (fs_bdd : ∀ n ω, fs n ω ≤ c)
    (fs_lim : Tendsto (fun n ω ↦ fs n ω) atTop (𝓝 (indicator E fun _ ↦ (1 : ℝ≥0)))) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    ∀ ω, Tendsto (fun n : ℕ ↦ (fs n ω : ℝ≥0)) atTop (𝓝 (indicator E (fun _ ↦ (1 : ℝ≥0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω ↦ fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (Eventually.of_forall fun n ↦ Eventually.of_forall (fs_bdd n)) (Eventually.of_forall fs_lim')

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero. -/
/-
**MeasureTheory.tendsto_lintegral_thickenedIndicator_of_isClosed** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : Measura
bleSpace Ω} [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsF
initeMeasure μ] {F : Set Ω} (F_closed : IsClosed F) {δs : Nat -> Real} (δs_pos :
 forall n, 0 < δs n) (δs_lim : Tendsto δs atTop (𝓝 0)) : Tendsto (fun n => linte
gral μ fun ω => (thickenedIndicator (δs_pos n) F ω : Real>=0∞)) atTop (𝓝 (μ F))
参数：μ : Measure Ω；F_closed : IsClosed F；δs_pos : forall n, 0 < δs n；δs_lim : Tend
sto δs atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator`：measure_of_cont_
bdd_of_tendsto_indicator (μ : Measure Ω) [IsFiniteMeasure μ] {c : Real>=0} {E : 
Set Ω} (E_mble : MeasurableSet E) (fs : Nat …
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `thickenedIndicator_le_one`：thickenedIndicator_le_one {δ : Real} (δ_pos :
 0 < δ) (E : Set α) (x : α) : thickenedIndicator δ_pos E x <= 1
· 使用定理 `thickenedIndicator_tendsto_indicator_closure`：thickenedIndicator_tendsto
_indicator_closure {δseq : Nat -> Real} (δseq_pos : forall n, 0 < δseq n) (δseq_
lim : Tendsto δseq atTop (𝓝 0)) (E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
The integrals of thickened indicators of a closed set against a finite measure t
end to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n ↦ lintegral μ fun ω ↦ (thickenedIndicator (δs_pos n) F ω : ℝ≥0∞)) atTop
      (𝓝 (μ F)) := by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n ↦ thickenedIndicator (δs_pos n) F) fun n ω ↦ thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

/-- A thickened indicator is integrable. -/
/-
**MeasureTheory.integrable_thickenedIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：integrable_thickenedIndicator {Ω : Type*} {mΩ : MeasurableSpace Ω} [Pseudo
EMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (F 
: Set Ω) {δ : Real} (δ_pos : 0 < δ) : Integrable (fun ω => (thickenedIndicator δ
_pos F ω : Real)) μ
参数：F : Set Ω；δ_pos : 0 < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.of_bound`：∀ {α : Type u_1} {E : Type u_5} {mα :
 MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsFini…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `thickenedIndicator_le_one`：thickenedIndicator_le_one {δ : Real} (δ_pos :
 0 < δ) (E : Set α) (x : α) : thickenedIndicator δ_pos E x <= 1

--- 原说明 ---
A thickened indicator is integrable.
-/
lemma integrable_thickenedIndicator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (F : Set Ω)
    {δ : ℝ} (δ_pos : 0 < δ) :
    Integrable (fun ω ↦ (thickenedIndicator δ_pos F ω : ℝ)) μ := by
  refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
  simpa using thickenedIndicator_le_one δ_pos F x

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero. -/
/-
**MeasureTheory.tendsto_integral_thickenedIndicator_of_isClosed** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : Measurab
leSpace Ω} [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFi
niteMeasure μ] {F : Set Ω} (F_closed : IsClosed F) {δs : Nat -> Real} (δs_pos : 
forall (n : Nat), 0 < δs n) (δs_lim : Tendsto δs atTop (𝓝 0)) : Tendsto (fun n :
 Nat => ∫ ω, (thickenedIndicator (δs_pos n) F ω : Real) ∂μ) atTop (𝓝 (μ.real F))
参数：μ : Measure Ω；F_closed : IsClosed F；δs_pos : forall (n : Nat), 0 < δs n；δs_li
m : Tendsto δs atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_lintegral_thickenedIndicator_of_isClosed`：tendsto_
lintegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω} [P
seudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用引理 `MeasureTheory.integrable_thickenedIndicator`：integrable_thickenedIndicat
or {Ω : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace Ω] [OpensMeasurableS
pace Ω] {μ : Measure Ω} [IsFinite…
· 使用定理 `MeasureTheory.Measure.real_def`：∀ {α : Type u_6} {m : MeasurableSpace α}
 (μ : MeasureTheory.Measure α) (s : Set α), μ.real s = (μ s).toReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `thickenedIndicator_apply`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α]
 {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α),   (thickenedIndicator δ_pos E) x =
 (thickenedInd…
· 使用定理 `ENNReal.tendsto_toReal_iff`：tendsto_toReal_iff {ι} {fi : Filter ι} {f : 
ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto 
(fun n => (f n).…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞

--- 原说明 ---
The integrals of thickened indicators of a closed set against a finite measure t
end to the
measure of the closed set if the thickening radii tend to zero.
-/
lemma tendsto_integral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ (n : ℕ), 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (thickenedIndicator (δs_pos n) F ω : ℝ) ∂μ) atTop (𝓝 (μ.real F)) := by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : ℕ → Ω → ℝ := fun n ω ↦ thickenedIndicator (δs_pos n) F ω
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ F_closed δs_pos δs_lim
  have h_eq (n : ℕ) : ∫⁻ ω, thickenedIndicator (δs_pos n) F ω ∂μ
      = ENNReal.ofReal (∫ ω, fs n ω ∂μ) := by
    rw [lintegral_coe_eq_integral]
    exact integrable_thickenedIndicator F (δs_pos _)
  simp_rw [h_eq] at h
  rw [Measure.real_def]
  have h_eq' : (fun n ↦ ∫ ω, fs n ω ∂μ) = fun n ↦ (ENNReal.ofReal (∫ ω, fs n ω ∂μ)).toReal := by
    ext n
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg fun x ↦ by simp [fs]
  rwa [h_eq', ENNReal.tendsto_toReal_iff (by simp) (by finiteness)]

end MeasureTheory -- namespace

end auxiliary -- section

section HasOuterApproxClosed

/-- A type class for topological spaces in which the indicator functions of closed sets can be
approximated pointwise from above by a sequence of bounded continuous functions. -/
/-
**HasOuterApproxClosed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class for topological spaces in which the indicator functions of closed s
ets can be
approximated pointwise from above by a sequence of bounded continuous functions.
-/
class HasOuterApproxClosed (X : Type*) [TopologicalSpace X] : Prop where
  exAppr : ∀ (F : Set X), IsClosed F → ∃ (fseq : ℕ → (X →ᵇ ℝ≥0)),
    (∀ n x, fseq n x ≤ 1) ∧ (∀ n x, x ∈ F → 1 ≤ fseq n x) ∧
    Tendsto (fun n : ℕ ↦ (fun x ↦ fseq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0)))

namespace HasOuterApproxClosed

variable {X : Type*} [TopologicalSpace X] [HasOuterApproxClosed X]
variable {F : Set X} (hF : IsClosed F)

/-- A sequence of continuous functions `X → [0,1]` tending to the indicator of a closed set. -/
/-
**HasOuterApproxClosed._root_.IsClosed.apprSeq** 是 Mathlib 中的一个定义，位于命名空间 `HasOut
erApproxClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of continuous functions `X → [0,1]` tending to the indicator of a clo
sed set.
-/
noncomputable def _root_.IsClosed.apprSeq : ℕ → (X →ᵇ ℝ≥0) :=
  Exists.choose (HasOuterApproxClosed.exAppr F hF)
/-
**HasOuterApproxClosed.apprSeq_apply_le_one** 是 Mathlib 中的一个引理，位于命名空间 `HasOuterA
pproxClosed`。
形式化陈述：apprSeq_apply_le_one (n : Nat) (x : X) : hF.apprSeq n x <= 1
参数：n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasOuterApproxClosed.exAppr`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : HasOuterApproxClosed X] (F : Set X),   IsClosed F →     ∃ fseq,       
(∀ (n : ℕ) (x : X…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma apprSeq_apply_le_one (n : ℕ) (x : X) :
    hF.apprSeq n x ≤ 1 :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x
/-
**HasOuterApproxClosed.apprSeq_apply_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `HasOuterA
pproxClosed`。
形式化陈述：apprSeq_apply_eq_one (n : Nat) {x : X} (hxF : x in F) : hF.apprSeq n x = 1
参数：n : Nat；hxF : x in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `HasOuterApproxClosed.apprSeq_apply_le_one`：apprSeq_apply_le_one (n : Nat
) (x : X) : hF.apprSeq n x <= 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasOuterApproxClosed.exAppr`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : HasOuterApproxClosed X] (F : Set X),   IsClosed F →     ∃ fseq,       
(∀ (n : ℕ) (x : X…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma apprSeq_apply_eq_one (n : ℕ) {x : X} (hxF : x ∈ F) :
    hF.apprSeq n x = 1 :=
  le_antisymm (apprSeq_apply_le_one _ _ _)
    ((Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF)
/-
**HasOuterApproxClosed.tendsto_apprSeq** 是 Mathlib 中的一个引理，位于命名空间 `HasOuterApprox
Closed`。
形式化陈述：tendsto_apprSeq : Tendsto (fun n : Nat => (fun x => hF.apprSeq n x)) atTop
 (𝓝 (indicator F fun _ => (1 : Real>=0)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HasOuterApproxClosed.exAppr`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : HasOuterApproxClosed X] (F : Set X),   IsClosed F →     ∃ fseq,       
(∀ (n : ℕ) (x : X…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma tendsto_apprSeq :
    Tendsto (fun n : ℕ ↦ (fun x ↦ hF.apprSeq n x)) atTop (𝓝 (indicator F fun _ ↦ (1 : ℝ≥0))) :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2
/-
**HasOuterApproxClosed.indicator_le_apprSeq** 是 Mathlib 中的一个引理，位于命名空间 `HasOuterA
pproxClosed`。
形式化陈述：indicator_le_apprSeq (n : Nat) : indicator F (fun _ => 1) <= hF.apprSeq n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `HasOuterApproxClosed.apprSeq_apply_eq_one`：apprSeq_apply_eq_one (n : Nat
) {x : X} (hxF : x in F) : hF.apprSeq n x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma indicator_le_apprSeq (n : ℕ) :
    indicator F (fun _ ↦ 1) ≤ hF.apprSeq n := by
  intro x
  by_cases hxF : x ∈ F
  · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n, le_refl]
  · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/-- The measure of a closed set is at most the integral of any function in a decreasing
approximating sequence to the indicator of the set. -/
/-
**HasOuterApproxClosed.measure_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `HasOuterA
pproxClosed`。
形式化陈述：measure_le_lintegral [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Mea
sure X) (n : Nat) : μ F <= ∫⁻ x, (hF.apprSeq n x : Real>=0∞) ∂μ
参数：μ : Measure X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用引理 `HasOuterApproxClosed.apprSeq_apply_eq_one`：apprSeq_apply_eq_one (n : Nat
) {x : X} (hxF : x in F) : hF.apprSeq n x = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
The measure of a closed set is at most the integral of any function in a decreas
ing
approximating sequence to the indicator of the set.
-/
theorem measure_le_lintegral [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (n : ℕ) :
    μ F ≤ ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂μ := by
  convert_to ∫⁻ x, (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) x ∂μ ≤ ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x ∈ F
    · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n hxF, ENNReal.coe_one, le_refl]
    · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/-- The integrals along a decreasing approximating sequence to the indicator of a closed set
tend to the measure of the closed set. -/
/-
**HasOuterApproxClosed.tendsto_lintegral_apprSeq** 是 Mathlib 中的一个引理，位于命名空间 `HasO
uterApproxClosed`。
形式化陈述：tendsto_lintegral_apprSeq [MeasurableSpace X] [OpensMeasurableSpace X] (μ 
: Measure X) [IsFiniteMeasure μ] : Tendsto (fun n => ∫⁻ x, hF.apprSeq n x ∂μ) at
Top (𝓝 ((μ : Measure X) F))
参数：μ : Measure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator`：measure_of_cont_
bdd_of_tendsto_indicator (μ : Measure Ω) [IsFiniteMeasure μ] {c : Real>=0} {E : 
Set Ω} (E_mble : MeasurableSet E) (fs : Nat …
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用引理 `HasOuterApproxClosed.apprSeq_apply_le_one`：apprSeq_apply_le_one (n : Nat
) (x : X) : hF.apprSeq n x <= 1
· 使用引理 `HasOuterApproxClosed.tendsto_apprSeq`：tendsto_apprSeq : Tendsto (fun n :
 Nat => (fun x => hF.apprSeq n x)) atTop (𝓝 (indicator F fun _ => (1 : Real>=0))
)

--- 原说明 ---
The integrals along a decreasing approximating sequence to the indicator of a cl
osed set
tend to the measure of the closed set.
-/
lemma tendsto_lintegral_apprSeq [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Tendsto (fun n ↦ ∫⁻ x, hF.apprSeq n x ∂μ) atTop (𝓝 ((μ : Measure X) F)) :=
  measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

end HasOuterApproxClosed --namespace

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  refine ⟨fun F hF ↦ ?_⟩
  use fun n ↦ thickenedIndicator (δ := (1 : ℝ) / (n + 1)) Nat.one_div_pos_of_nat F
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact fun n x ↦ thickenedIndicator_le_one Nat.one_div_pos_of_nat F x
  · exact fun n x hxF ↦ one_le_thickenedIndicator_apply X Nat.one_div_pos_of_nat hxF
  · have key := thickenedIndicator_tendsto_indicator_closure
              (δseq := fun (n : ℕ) ↦ (1 : ℝ) / (n + 1))
              (fun _ ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat F
    rw [tendsto_pi_nhds] at *
    intro x
    nth_rw 2 [← IsClosed.closure_eq hF]
    exact key x

namespace MeasureTheory

/-- Two finite measures give equal values to all closed sets if the integrals of all bounded
continuous functions with respect to the two measures agree. -/
/-
**MeasureTheory.measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*} 
[MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [OpensMeasurab
leSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] (h : forall (f : Ω ->ᵇ Real>=0)
, ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) : μ F = ν F
参数：h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν；F_closed : IsClos
ed F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `HasOuterApproxClosed.tendsto_lintegral_apprSeq`：tendsto_lintegral_apprSe
q [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure 
μ] : Tendsto (fun n => ∫⁻ x, hF.appr…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two finite measures give equal values to all closed sets if the integrals of all
 bounded
continuous functions with respect to the two measures agree.
-/
theorem measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) :
    μ F = ν F := by
  have ν_finite : IsFiniteMeasure ν := by
    constructor
    have whole := h 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_const,
      one_mul] at whole
    simp [← whole]
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  have obs_ν := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed ν
  simp_rw [h] at obs_μ
  exact tendsto_nhds_unique obs_μ obs_ν

/-- Two finite Borel measures are equal if the integrals of all non-negative bounded continuous
functions with respect to both agree. -/
/-
**MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：ext_of_forall_lintegral_eq_of_IsFiniteMeasure {Ω : Type*} [MeasurableSpace
 Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : Measure 
Ω} [IsFiniteMeasure μ] (h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x
 ∂ν) : μ = ν
参数：h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeas
ure`：measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*} [
MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω] …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.ext_of_generate_finite`：ext_of_generate_finite (C : Set (S
et α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C) [IsFiniteMeasure μ] (hμν :
 forall s in C, μ s = ν s)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `borel_eq_generateFrom_isClosed`：borel_eq_generateFrom_isClosed [Topologi
calSpace α] : borel α = .generateFrom { s | IsClosed s }
· 使用引理 `isPiSystem_isClosed`：isPiSystem_isClosed [TopologicalSpace α] : IsPiSyst
em ({s : Set α | IsClosed s})
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)

--- 原说明 ---
Two finite Borel measures are equal if the integrals of all non-negative bounded
 continuous
functions with respect to both agree.
-/
theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : ∀ (f : Ω →ᵇ ℝ≥0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F F_closed ↦ key F_closed
  · exact key isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]

/-- Two finite Borel measures are equal if the integrals of all bounded continuous functions with
respect to both agree. -/
/-
**MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：ext_of_forall_integral_eq_of_IsFiniteMeasure {Ω : Type*} [MeasurableSpace 
Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ ν : Measure Ω
} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f : Ω ->ᵇ Real), ∫ x, f x
 ∂μ = ∫ x, f x ∂ν) : μ = ν
参数：h : forall (f : Ω ->ᵇ Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure`：ext_of_fora
ll_lintegral_eq_of_IsFiniteMeasure {Ω : Type*} [MeasurableSpace Ω] [TopologicalS
pace Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] {…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.toReal_lintegral_coe_eq_integral`：toReal_linte
gral_coe_eq_integral [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) (μ : Measure X
) : (∫⁻ x, (f x : Real>=0∞) ∂μ).toReal = ∫ x, (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `BoundedContinuousFunction.map_bounded'`：∀ {α : Type u} {β : Type v} [ins
t : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (self : BoundedContinuo
usFunction α β), ∃ C, ∀ (x y…

--- 原说明 ---
Two finite Borel measures are equal if the integrals of all bounded continuous f
unctions with
respect to both agree.
-/
theorem ext_of_forall_integral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Ω →ᵇ ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ, toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

end MeasureTheory -- namespace

end HasOuterApproxClosed -- section

