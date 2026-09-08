/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Stochastic processes satisfying the Kolmogorov condition

A stochastic process `X : T → Ω → E` on an index space `T` and a measurable space `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-algebra on `E × E`
and the following condition holds:
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`.

This condition is the main assumption of the Kolmogorov-Chentsov theorem, which gives the existence
of a continuous modification of the process.

The measurability condition on pairs ensures that the distance `edist (X s ω) (X t ω)` is
measurable in `ω` for fixed `s, t`. In a space with second-countable topology, the measurability
of pairs can be obtained from measurability of each `X t`.

## Main definitions

* `IsKolmogorovProcess`: property of being a stochastic process that satisfies
  the Kolmogorov condition.
* `IsAEKolmogorovProcess`: a stochastic process satisfies `IsAEKolmogorovProcess` if it is
  a modification of a process satisfying the Kolmogorov condition.

## Main statements

* `IsKolmogorovProcess.mk_of_secondCountableTopology`: in a space with second-countable topology,
  a process is a Kolmogorov process if each `X t` is measurable and the Kolmogorov condition holds.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

/-- A stochastic process `X : T → Ω → E` on an index space `T` and a measurable space `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-algebra on `E × E`
and the following condition holds: `∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`. -/
/-
**ProbabilityTheory.IsKolmogorovProcess** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probability
Theory`。
形式化陈述：{T : Type u_1} →   {Ω : Type u_2} →     {E : Type u_3} →       [PseudoEMet
ricSpace T] →         {mΩ : MeasurableSpace Ω} →           [PseudoEMetricSpace E
] → (T → Ω → E) → MeasureTheory.Measure Ω → ℝ → ℝ → NNReal → Prop
参数：T → Ω → E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stochastic process `X : T → Ω → E` on an index space `T` and a measurable spac
e `Ω`
with measure `P` is said to satisfy the Kolmogorov condition with exponents `p, 
q` and constant `M`
if for all `s, t : T`, the pair `(X s, X t)` is measurable for the Borel sigma-a
lgebra on `E × E`
and the following condition holds: `∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edi
st s t ^ q`.
-/
structure IsKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop where
  measurablePair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω)
  kolmogorovCondition : ∀ s t : T, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q
  p_pos : 0 < p
  q_pos : 0 < q

/-- Property of being a modification of a stochastic process that satisfies the Kolmogorov
condition (`IsKolmogorovProcess`). -/
/-
**ProbabilityTheory.IsAEKolmogorovProcess** 是 Mathlib 中的一个定义，位于命名空间 `Probability
Theory`。
形式化陈述：IsAEKolmogorovProcess (X : T -> Ω -> E) (P : Measure Ω) (p q : Real) (M : 
Real>=0) : Prop
参数：X : T -> Ω -> E；P : Measure Ω；p q : Real；M : Real>=0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Property of being a modification of a stochastic process that satisfies the Kolm
ogorov
condition (`IsKolmogorovProcess`).
-/
def IsAEKolmogorovProcess (X : T → Ω → E) (P : Measure Ω) (p q : ℝ) (M : ℝ≥0) : Prop :=
  ∃ Y, IsKolmogorovProcess Y P p q M ∧ ∀ t, X t =ᵐ[P] Y t
/-
**ProbabilityTheory.IsKolmogorovProcess.IsAEKolmogorovProcess** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsKolmog
orovProcess X P p q M → ProbabilityTheory.IsAEKolmogorovProcess X P p q M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsKolmogorovProcess.IsAEKolmogorovProcess (hX : IsKolmogorovProcess X P p q M) :
    IsAEKolmogorovProcess X P p q M := ⟨X, hX, by simp⟩

namespace IsAEKolmogorovProcess

/-- A process with the property `IsKolmogorovProcess` such that `∀ t, X t =ᵐ[P] h.mk X t`. -/
protected noncomputable
/-
**ProbabilityTheory.IsAEKolmogorovProcess.mk** 是 Mathlib 中的一个定义，位于命名空间 `Probabil
ityTheory.IsAEKolmogorovProcess`。
形式化陈述：mk (X : T -> Ω -> E) (h : IsAEKolmogorovProcess X P p q M) : T -> Ω -> E
参数：X : T -> Ω -> E；h : IsAEKolmogorovProcess X P p q M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
def mk (X : T → Ω → E) (h : IsAEKolmogorovProcess X P p q M) : T → Ω → E :=
  Classical.choose h
/-
**ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：IsKolmogorovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogoro
vProcess (h.mk X) P p q M
参数：h : IsAEKolmogorovProcess X P p q M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsKolmogorovProcess_mk (h : IsAEKolmogorovProcess X P p q M) :
    IsKolmogorovProcess (h.mk X) P p q M := (Classical.choose_spec h).1
/-
**ProbabilityTheory.IsAEKolmogorovProcess.ae_eq_mk** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：ae_eq_mk (h : IsAEKolmogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk 
X t
参数：h : IsAEKolmogorovProcess X P p q M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma ae_eq_mk (h : IsAEKolmogorovProcess X P p q M) : ∀ t, X t =ᵐ[P] h.mk X t :=
  (Classical.choose_spec h).2
/-
**ProbabilityTheory.IsAEKolmogorovProcess.kolmogorovCondition** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：kolmogorovCondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) : ∫⁻ 
ω, edist (X s ω) (X t ω) ^ p ∂P <= M * edist s t ^ q
参数：hX : IsAEKolmogorovProcess X P p q M；s t : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.ae_eq_mk`：ae_eq_mk (h : IsAEKolm
ogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk X t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.kolmogorovCondition`：∀ {T : Type u
_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measurable
Space Ω}   [inst_1 : PseudoEMetricSpace E] {X :…
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
-/
lemma kolmogorovCondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q := by
  convert! hX.IsKolmogorovProcess_mk.kolmogorovCondition s t using 1
  refine lintegral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂
  simp_rw [hω₁, hω₂]
/-
**ProbabilityTheory.IsAEKolmogorovProcess.p_pos** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.IsAEKolmogorovProcess`。
形式化陈述：p_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < p
参数：hX : IsAEKolmogorovProcess X P p q M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.p_pos`：∀ {T : Type u_1} {Ω : Type 
u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}   [in
st_1 : PseudoEMetricSpace E] {X :…
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
-/
lemma p_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < p := hX.IsKolmogorovProcess_mk.p_pos
/-
**ProbabilityTheory.IsAEKolmogorovProcess.q_pos** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.IsAEKolmogorovProcess`。
形式化陈述：q_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < q
参数：hX : IsAEKolmogorovProcess X P p q M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.q_pos`：∀ {T : Type u_1} {Ω : Type 
u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}   [in
st_1 : PseudoEMetricSpace E] {X :…
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
-/
lemma q_pos (hX : IsAEKolmogorovProcess X P p q M) : 0 < q := hX.IsKolmogorovProcess_mk.q_pos
/-
**ProbabilityTheory.IsAEKolmogorovProcess.congr** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.IsAEKolmogorovProcess`。
形式化陈述：congr {Y : T -> Ω -> E} (hX : IsAEKolmogorovProcess X P p q M) (h : forall
 t, X t =ᵐ[P] Y t) : IsAEKolmogorovProcess Y P p q M
参数：hX : IsAEKolmogorovProcess X P p q M；h : forall t, X t =ᵐ[P] Y t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.ae_eq_mk`：ae_eq_mk (h : IsAEKolm
ogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk X t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma congr {Y : T → Ω → E} (hX : IsAEKolmogorovProcess X P p q M)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    IsAEKolmogorovProcess Y P p q M := by
  refine ⟨hX.mk X, hX.IsKolmogorovProcess_mk, fun t ↦ ?_⟩
  filter_upwards [hX.ae_eq_mk t, h t] with ω hX hY using hY.symm.trans hX

end IsAEKolmogorovProcess

section Measurability

/-
**ProbabilityTheory.IsKolmogorovProcess.stronglyMeasurable_edist** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsKolmog
orovProcess X P p q M →     ∀ {s t : T}, MeasureTheory.StronglyMeasurable fun ω 
=> edist (X s ω) (X t ω)
参数：X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Continuous.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α]   [inst
_3 : TopologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.measurablePair`：∀ {T : Type u_1} {
Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpace
 Ω}   [inst_1 : PseudoEMetricSpace E] {X :…
-/
lemma IsKolmogorovProcess.stronglyMeasurable_edist
    (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    StronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) := by
  borelize (E × E)
  exact continuous_edist.stronglyMeasurable.comp_measurable (hX.measurablePair s t)
/-
**ProbabilityTheory.IsAEKolmogorovProcess.aestronglyMeasurable_edist** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsAEKolm
ogorovProcess X P p q M →     ∀ {s t : T}, MeasureTheory.AEStronglyMeasurable (f
un ω => edist (X s ω) (X t ω)) P
参数：fun ω => edist (X s ω) (X t ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.stronglyMeasurable_edist`：∀ {T : T
ype u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measu
rableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.ae_eq_mk`：ae_eq_mk (h : IsAEKolm
ogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk X t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsAEKolmogorovProcess.aestronglyMeasurable_edist
    (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEStronglyMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := by
  refine ⟨(fun ω ↦ edist (hX.mk X s ω) (hX.mk X t ω)),
    hX.IsKolmogorovProcess_mk.stronglyMeasurable_edist, ?_⟩
  filter_upwards [hX.ae_eq_mk s, hX.ae_eq_mk t] with ω hω₁ hω₂ using by simp [hω₁, hω₂]
/-
**ProbabilityTheory.IsKolmogorovProcess.measurable_edist** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsKolmog
orovProcess X P p q M → ∀ {s t : T}, Measurable fun ω => edist (X s ω) (X t ω)
参数：X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.stronglyMeasurable_edist`：∀ {T : T
ype u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measu
rableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
-/
lemma IsKolmogorovProcess.measurable_edist (hX : IsKolmogorovProcess X P p q M) {s t : T} :
    Measurable (fun ω ↦ edist (X s ω) (X t ω)) := hX.stronglyMeasurable_edist.measurable
/-
**ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable_edist** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsAEKolm
ogorovProcess X P p q M → ∀ {s t : T}, AEMeasurable (fun ω => edist (X s ω) (X t
 ω)) P
参数：fun ω => edist (X s ω) (X t ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ProbabilityTheory.IsAEKolmogorovProcess.aestronglyMeasurable_edist`：∀ {T
 : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : M
easurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
-/
lemma IsAEKolmogorovProcess.aemeasurable_edist (hX : IsAEKolmogorovProcess X P p q M) {s t : T} :
    AEMeasurable (fun ω ↦ edist (X s ω) (X t ω)) P := hX.aestronglyMeasurable_edist.aemeasurable

variable [MeasurableSpace E] [BorelSpace E]
/-
**ProbabilityTheory.IsKolmogorovProcess.measurable** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst_2 : MeasurableSpace E
] [BorelSpace E],   ProbabilityTheory.IsKolmogorovProcess X P p q M → ∀ (s : T),
 Measurable (X s)
参数：s : T；X s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `prod_le_borel_prod`：prod_le_borel_prod : Prod.instMeasurableSpace <= bor
el (α × β)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.measurablePair`：∀ {T : Type u_1} {
Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpace
 Ω}   [inst_1 : PseudoEMetricSpace E] {X :…
-/
lemma IsKolmogorovProcess.measurable (hX : IsKolmogorovProcess X P p q M) (s : T) :
    Measurable (X s) :=
  (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hX.measurablePair s s)
/-
**ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst_2 : MeasurableSpace E
] [BorelSpace E],   ProbabilityTheory.IsAEKolmogorovProcess X P p q M → ∀ (s : T
), AEMeasurable (X s) P
参数：s : T；X s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.measurable`：∀ {T : Type u_1} {Ω : 
Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω} 
  [inst_1 : PseudoEMetricSpace E] {p q…
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.IsKolmogorovProcess_mk`：IsKolmog
orovProcess_mk (h : IsAEKolmogorovProcess X P p q M) : IsKolmogorovProcess (h.mk
 X) P p q M
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.ae_eq_mk`：ae_eq_mk (h : IsAEKolm
ogorovProcess X P p q M) : forall t, X t =ᵐ[P] h.mk X t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma IsAEKolmogorovProcess.aemeasurable (hX : IsAEKolmogorovProcess X P p q M) (s : T) :
    AEMeasurable (X s) P := by
  refine ⟨hX.mk X s, hX.IsKolmogorovProcess_mk.measurable s, ?_⟩
  filter_upwards [hX.ae_eq_mk s] with ω hω using hω
/-
**ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E}   [inst_2 : MeasurableSpace E
] [BorelSpace E] [SecondCountableTopology E],   (∀ (s : T), Measurable (X s)) → 
    (∀ (s t : T), ∫⁻ (ω : Ω), edist (X s ω) (X t ω) ^ p ∂P ≤ ↑M * edist s t ^ q)
 →       0 < p → 0 < q → ProbabilityTheory.IsKolmogorovProcess X P p q M
参数：∀ (s : T), Measurable (X s)；∀ (s t : T), ∫⁻ (ω : Ω), edist (X s ω) (X t ω) ^ 
p ∂P ≤ ↑M * edist s t ^ q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
-/
lemma IsKolmogorovProcess.mk_of_secondCountableTopology [SecondCountableTopology E]
    (h_meas : ∀ s, Measurable (X s))
    (h_kol : ∀ s t : T, ∫⁻ ω, (edist (X s ω) (X t ω)) ^ p ∂P ≤ M * edist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M where
  measurablePair s t := by
    suffices Measurable (fun ω ↦ (X s ω, X t ω)) by
      rwa [Prod.borelSpace.measurable_eq] at this
    fun_prop
  kolmogorovCondition := h_kol
  p_pos := hp
  q_pos := hq

end Measurability

section ZeroDist

/-
**ProbabilityTheory.IsAEKolmogorovProcess.edist_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsAEKolm
ogorovProcess X P p q M →     ∀ {s t : T}, edist s t = 0 → ∀ᵐ (ω : Ω) ∂P, edist 
(X s ω) (X t ω) = 0
参数：ω : Ω；X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable_edist`：∀ {T : Type 
u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measurabl
eSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.kolmogorovCondition`：kolmogorovC
ondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) : ∫⁻ ω, edist (X s ω) 
(X t ω) ^ p ∂P <= M * edist s t ^ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.q_pos`：q_pos (hX : IsAEKolmogoro
vProcess X P p q M) : 0 < q
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.p_pos`：p_pos (hX : IsAEKolmogoro
vProcess X P p q M) : 0 < p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma IsAEKolmogorovProcess.edist_eq_zero (hX : IsAEKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω ↦ edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p), ← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ ≤ M * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp [h, hX.q_pos]
/-
**ProbabilityTheory.IsKolmogorovProcess.edist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNR
eal} {P : MeasureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsKolmog
orovProcess X P p q M →     ∀ {s t : T}, edist s t = 0 → ∀ᵐ (ω : Ω) ∂P, edist (X
 s ω) (X t ω) = 0
参数：ω : Ω；X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsAEKolmogorovProcess.edist_eq_zero`：∀ {T : Type u_1} 
{Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : MeasurableSpac
e Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.IsAEKolmogorovProcess`：∀ {T : Type
 u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measurab
leSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
-/
lemma IsKolmogorovProcess.edist_eq_zero (hX : IsKolmogorovProcess X P p q M)
    {s t : T} (h : edist s t = 0) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero h
/-
**ProbabilityTheory.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsAEKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {P : Mea
sureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsAEKolmogorovProcess
 X P p q 0 → ∀ (s t : T), ∀ᵐ (ω : Ω) ∂P, edist (X s ω) (X t ω) = 0
参数：s t : T；ω : Ω；X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `ProbabilityTheory.IsAEKolmogorovProcess.aemeasurable_edist`：∀ {T : Type 
u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measurabl
eSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.kolmogorovCondition`：kolmogorovC
ondition (hX : IsAEKolmogorovProcess X P p q M) (s t : T) : ∫⁻ ω, edist (X s ω) 
(X t ω) ^ p ∂P <= M * edist s t ^ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ProbabilityTheory.IsAEKolmogorovProcess.p_pos`：p_pos (hX : IsAEKolmogoro
vProcess X P p q M) : 0 < p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsAEKolmogorovProcess X P p q 0)
    (s t : T) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 := by
  suffices (fun ω ↦ edist (X s ω) (X t ω) ^ p) =ᵐ[P] 0 by
    filter_upwards [this] with ω hω
    simpa [hX.p_pos, not_lt_of_gt hX.p_pos] using hω
  rw [← lintegral_eq_zero_iff' (hX.aemeasurable_edist.pow_const p), ← nonpos_iff_eq_zero]
  calc ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
  _ ≤ 0 * edist s t ^ q := hX.kolmogorovCondition s t
  _ = 0 := by simp
/-
**ProbabilityTheory.IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.IsKolmogorovProcess`。
形式化陈述：∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace 
T] {mΩ : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {P : Mea
sureTheory.Measure Ω} {X : T → Ω → E},   ProbabilityTheory.IsKolmogorovProcess X
 P p q 0 → ∀ (s t : T), ∀ᵐ (ω : Ω) ∂P, edist (X s ω) (X t ω) = 0
参数：s t : T；ω : Ω；X s ω；X t ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero`：
∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ
 : MeasurableSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
· 使用定理 `ProbabilityTheory.IsKolmogorovProcess.IsAEKolmogorovProcess`：∀ {T : Type
 u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T] {mΩ : Measurab
leSpace Ω}   [inst_1 : PseudoEMetricSpace E] {p q…
-/
lemma IsKolmogorovProcess.edist_eq_zero_of_const_eq_zero (hX : IsKolmogorovProcess X P p q 0)
    (s t : T) :
    ∀ᵐ ω ∂P, edist (X s ω) (X t ω) = 0 :=
  hX.IsAEKolmogorovProcess.edist_eq_zero_of_const_eq_zero s t

end ZeroDist

end ProbabilityTheory

