/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Results about indicator functions, their integrals, and measures

This file has a few measure-theoretic or integration-related results on indicator functions.

## Implementation notes

This file exists to avoid importing `Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
in `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`.

## TODO

The result `MeasureTheory.tendsto_measure_of_tendsto_indicator` here could be proved without
integration, if we had convergence of measures results for countably generated filters. Ideally,
the present file would then become unnecessary: lemmas such as
`MeasureTheory.tendsto_measure_of_ae_tendsto_indicator` would not need integration so could be
moved out of `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`, and the lemmas in this file could
be moved to, e.g., `Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`.
-/

public section

namespace MeasureTheory

section TendstoIndicator

open Set Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to the indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then
the measures of `Aᵢ` tend to the measure of `A`. -/
/-
**MeasureTheory.tendsto_measure_of_ae_tendsto_indicator** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_measure_of_ae_tendsto_indicator {μ : Measure α} (A_mble : Measurab
leSet A) (As_mble : forall i, MeasurableSet (As i)) {B : Set α} (B_mble : Measur
ableSet B) (B_finmeas : μ B != ∞) (As_le_B : forallᶠ i in L, As i subseteq B) (h
_lim : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A) : Tendsto (fun i => μ (
As i)) L (𝓝 (μ A))
参数：A_mble : MeasurableSet A；As_mble : forall i, MeasurableSet (As i)；B_mble : Me
asurableSet B；B_finmeas : μ B != ∞；As_le_B : forallᶠ i in L, As i subseteq B；h_l
im : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence`：tendsto
_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGene
rated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `ENNReal.instT5Space`：T5Space ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal

--- 原说明 ---
If the indicators of measurable sets `Aᵢ` tend pointwise almost everywhere to th
e indicator
of a measurable set `A` and we eventually have `Aᵢ ⊆ B` for some set `B` of fini
te measure, then
the measures of `Aᵢ` tend to the measure of `A`.
-/
lemma tendsto_measure_of_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble,
           ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (1 : α → ℝ≥0∞))
          (Eventually.of_forall ?_) ?_ ?_ ?_
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    exact Eventually.of_forall fun x ↦ by grw [hi]
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas
  · simpa only [Pi.one_def, tendsto_indicator_const_apply_iff_eventually] using h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ Aᵢ` tend to
the measure `μ A`. -/
/-
**MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure** 是 M
athlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure {μ : Measure α}
 [IsFiniteMeasure μ] (A_mble : MeasurableSet A) (As_mble : forall i, MeasurableS
et (As i)) (h_lim : forallᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A) : Tendsto 
(fun i => μ (As i)) L (𝓝 (μ A))
参数：A_mble : MeasurableSet A；As_mble : forall i, MeasurableSet (As i)；h_lim : for
allᵐ x ∂μ, forallᶠ i in L, x in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.tendsto_measure_of_ae_tendsto_indicator`：tendsto_measure_o
f_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A) (As_mble : for
all i, MeasurableSet (As i)) {B : Set α} (B…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend point
wise
almost everywhere to the indicator of a measurable set `A`, then the measures `μ
 Aᵢ` tend to
the measure `μ A`.
-/
lemma tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    {μ : Measure α} [IsFiniteMeasure μ] (A_mble : MeasurableSet A)
    (As_mble : ∀ i, MeasurableSet (As i)) (h_lim : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_ae_tendsto_indicator L A_mble As_mble MeasurableSet.univ
    (by finiteness) (Eventually.of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a set `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the measures of `Aᵢ`
tend to the measure of `A`. -/
/-
**MeasureTheory.tendsto_measure_of_tendsto_indicator** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：tendsto_measure_of_tendsto_indicator {μ : Measure α} (As_mble : forall i, 
MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B) (B_finmeas : μ B !=
 ∞) (As_le_B : forallᶠ i in L, As i subseteq B) (h_lim : forall x, forallᶠ i in 
L, x in As i ↔ x in A) : Tendsto (fun i => μ (As i)) L (𝓝 (μ A))
参数：As_mble : forall i, MeasurableSet (As i)；B_mble : MeasurableSet B；B_finmeas :
 μ B != ∞；As_le_B : forallᶠ i in L, As i subseteq B；h_lim : forall x, forallᶠ i 
in L, x in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.tendsto_measure_of_ae_tendsto_indicator`：tendsto_measure_o
f_ae_tendsto_indicator {μ : Measure α} (A_mble : MeasurableSet A) (As_mble : for
all i, MeasurableSet (As i)) {B : Set α} (B…
· 使用引理 `measurableSet_of_tendsto_indicator`：measurableSet_of_tendsto_indicator [
NeBot L] (As_mble : forall i, MeasurableSet (As i)) (h_lim : forall x, forallᶠ i
 in L, x in As i ↔ x in …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If the indicators of measurable sets `Aᵢ` tend pointwise to the indicator of a s
et `A`
and we eventually have `Aᵢ ⊆ B` for some set `B` of finite measure, then the mea
sures of `Aᵢ`
tend to the measure of `A`.
-/
lemma tendsto_measure_of_tendsto_indicator {μ : Measure α}
    (As_mble : ∀ i, MeasurableSet (As i)) {B : Set α} (B_mble : MeasurableSet B)
    (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ x, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator L ?_ As_mble B_mble B_finmeas As_le_B
        (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend pointwise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`. -/
/-
**MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure (μ : Measure α) [I
sFiniteMeasure μ] (As_mble : forall i, MeasurableSet (As i)) (h_lim : forall x, 
forallᶠ i in L, x in As i ↔ x in A) : Tendsto (fun i => μ (As i)) L (𝓝 (μ A))
参数：μ : Measure α；As_mble : forall i, MeasurableSet (As i)；h_lim : forall x, fora
llᶠ i in L, x in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
`：tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure {μ : Measure α} [Is
FiniteMeasure μ] (A_mble : MeasurableSet A) (As_mble : forall …
· 使用引理 `measurableSet_of_tendsto_indicator`：measurableSet_of_tendsto_indicator [
NeBot L] (As_mble : forall i, MeasurableSet (As i)) (h_lim : forall x, forallᶠ i
 in L, x in As i ↔ x in …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If `μ` is a finite measure and the indicators of measurable sets `Aᵢ` tend point
wise to
the indicator of a set `A`, then the measures `μ Aᵢ` tend to the measure `μ A`.
-/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
    (μ : Measure α) [IsFiniteMeasure μ] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ x, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  rcases L.eq_or_neBot with rfl | _
  · exact tendsto_bot
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure L ?_ As_mble (ae_of_all μ h_lim)
  exact measurableSet_of_tendsto_indicator L As_mble h_lim

end TendstoIndicator -- section

end MeasureTheory

