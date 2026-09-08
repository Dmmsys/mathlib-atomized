/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

This file is about Lebesgue integrals. See the file `AEEqOfIntegral` for Bochner integrals.

## Main statements

The results listed below apply to two functions `f, g`, under the hypothesis that
for all measurable sets `s` with finite measure, `∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEMeasurable.ae_eq_of_forall_setLIntegral_eq`: for functions which are `AEMeasurable` and
  have finite integral.

-/

public section


open Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

/-
**MeasureTheory.ae_const_le_iff_forall_lt_measure_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpa
ce β] [OrderTopology β] [FirstCountableTopology β] (f : α -> β) (c : β) : (foral
lᵐ x ∂μ, c <= f x) ↔ forall b < c, μ {x | f x <= b} = 0
参数：f : α -> β；c : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 := by
  simp_rw [eventually_const_le_iff_forall_lt_eventually_const_lt, ae_iff, not_lt]
/-
**MeasureTheory.ae_le_const_iff_forall_gt_measure_zero** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_le_const_iff_forall_gt_measure_zero {β} [LinearOrder β] [TopologicalSpa
ce β] [OrderTopology β] [FirstCountableTopology β] {μ : Measure α} (f : α -> β) 
(c : β) : (forallᵐ x ∂μ, f x <= c) ↔ forall b, c < b -> μ {x | b <= f x} = 0
参数：f : α -> β；c : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_const_le_iff_forall_lt_measure_zero`：ae_const_le_iff_fo
rall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β] [OrderTopology β] 
[FirstCountableTopology β] (f : α -> β) (c…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
lemma ae_le_const_iff_forall_gt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] {μ : Measure α} (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, f x ≤ c) ↔ ∀ b, c < b → μ {x | b ≤ f x} = 0 :=
  ae_const_le_iff_forall_lt_measure_zero (β := βᵒᵈ) _ _
/-
**MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α ->
 Real>=0∞} (hf : Measurable f) (h : forall s, MeasurableSet s -> μ s < ∞ -> (∫⁻ 
x in s, f x ∂μ) <= ∫⁻ x in s, g x ∂μ) : f <=ᵐ[μ] g
参数：hf : Measurable f；h : forall s, MeasurableSet s -> μ s < ∞ -> (∫⁻ x in s, f x
 ∂μ) <= ∫⁻ x in s, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀`：ae_le_of_
forall_setLIntegral_le_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (h : forall s, MeasurableSet s…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  have A : ∀ (ε N : ℝ≥0) (p : ℕ), 0 < ε →
      μ ({x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p) = 0 := by
    intro ε N p εpos
    let s := {x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p
    have s_lt_top : μ s < ∞ :=
      (measure_mono (Set.inter_subset_right)).trans_lt (measure_spanningSets_lt_top μ p)
    have A : (∫⁻ x in s, g x ∂μ) + ε * μ s ≤ (∫⁻ x in s, g x ∂μ) + 0 :=
      calc
        (∫⁻ x in s, g x ∂μ) + ε * μ s = (∫⁻ x in s, g x ∂μ) + ∫⁻ _ in s, ε ∂μ := by
          simp only [lintegral_const, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]
        _ = ∫⁻ x in s, g x + ε ∂μ := (lintegral_add_right _ measurable_const).symm
        _ ≤ ∫⁻ x in s, f x ∂μ :=
          setLIntegral_mono_ae hf.restrict <| ae_of_all _ fun x hx => hx.1.1
        _ ≤ (∫⁻ x in s, g x ∂μ) + 0 := by
          rw [add_zero, ← Measure.restrict_toMeasurable s_lt_top.ne]
          refine h _ (measurableSet_toMeasurable ..) ?_
          rwa [measure_toMeasurable]
    have B : (∫⁻ x in s, g x ∂μ) ≠ ∞ :=
      (setLIntegral_lt_top_of_le_nnreal s_lt_top.ne ⟨N, fun _ h ↦ h.1.2⟩).ne
    have : (ε : ℝ≥0∞) * μ s ≤ 0 := ENNReal.le_of_add_le_add_left B A
    simpa only [ENNReal.coe_eq_zero, nonpos_iff_eq_zero, mul_eq_zero, εpos.ne', false_or]
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ≥0)
  let s := fun n : ℕ => {x | g x + u n ≤ f x ∧ g x ≤ (n : ℝ≥0)} ∩ spanningSets μ n
  have μs : ∀ n, μ (s n) = 0 := fun n => A _ _ _ (u_pos n)
  have B : {x | f x ≤ g x}ᶜ ⊆ ⋃ n, s n := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred, not_le] at hx
    have L1 : ∀ᶠ n in atTop, g x + u n ≤ f x := by
      have : Tendsto (fun n => g x + u n) atTop (𝓝 (g x + (0 : ℝ≥0))) :=
        tendsto_const_nhds.add (ENNReal.tendsto_coe.2 u_lim)
      simp only [ENNReal.coe_zero, add_zero] at this
      exact this.eventually_le_const hx
    have L2 : ∀ᶠ n : ℕ in (atTop : Filter ℕ), g x ≤ (n : ℝ≥0) :=
      have : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ∞) := by
        simp only [ENNReal.coe_natCast]
        exact ENNReal.tendsto_nat_nhds_top
      this.eventually_const_le (hx.trans_le le_top)
    apply Set.mem_iUnion.2
    exact ((L1.and L2).and (eventually_mem_spanningSets μ x)).exists
  refine le_antisymm ?_ bot_le
  calc
    μ {x : α | (fun x : α => f x ≤ g x) x}ᶜ ≤ μ (⋃ n, s n) := measure_mono B
    _ ≤ ∑' n, μ (s n) := measure_iUnion_le _
    _ = 0 := by simp only [μs, tsum_zero]
/-
**MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α ->
 Real>=0∞} (hf : Measurable f) (h : forall s, MeasurableSet s -> μ s < ∞ -> (∫⁻ 
x in s, f x ∂μ) <= ∫⁻ x in s, g x ∂μ) : f <=ᵐ[μ] g
参数：hf : Measurable f；h : forall s, MeasurableSet s -> μ s < ∞ -> (∫⁻ x in s, f x
 ∂μ) <= ∫⁻ x in s, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀`：ae_le_of_
forall_setLIntegral_le_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (h : forall s, MeasurableSet s…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ) : f ≤ᵐ[μ] g :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf.aemeasurable h
/-
**MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α ->
 Real>=0∞} (hf : Measurable f) (hg : Measurable g) (h : forall s, MeasurableSet 
s -> μ s < ∞ -> ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g
参数：hf : Measurable f；hg : Measurable g；h : forall s, MeasurableSet s -> μ s < ∞ 
-> ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀`：ae_eq_of_
forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf fun s hs h's => le_of_eq (h s hs h's)
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hg fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymm
/-
**MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α ->
 Real>=0∞} (hf : Measurable f) (hg : Measurable g) (h : forall s, MeasurableSet 
s -> μ s < ∞ -> ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g
参数：hf : Measurable f；hg : Measurable g；h : forall s, MeasurableSet s -> μ s < ∞ 
-> ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀`：ae_eq_of_
forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.aemeasurable hg.aemeasurable h
/-
**MeasureTheory.AEMeasurable.ae_eq_of_forall_setLIntegral_eq** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 g : α → ENNReal},   AEMeasurable f μ →     AEMeasurable g μ →       ∫⁻ (x : α),
 f x ∂μ ≠ ⊤ →         ∫⁻ (x : α), g x ∂μ ≠ ⊤ →           (∀ ⦃s : Set α⦄, Measura
bleSet s → μ s < ⊤ → ∫⁻ (x : α) in s, f x ∂μ = ∫⁻ (x : α) in s, g x ∂μ) → f =ᵐ[μ
] g
参数：x : α；x : α；∀ ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → ∫⁻ (x : α) in s, f x ∂
μ = ∫⁻ (x : α) in s, g x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.aefinStronglyMeasurable_of_aemeasurable`：ENNReal.aefinStronglyMe
asurable_of_aemeasurable (hf : ∫⁻ x, f x ∂μ != ∞) (hf_meas : AEMeasurable f μ) :
 AEFinStronglyMeasurable f μ
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀`：ae_eq_of_
forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : f…
· 使用定理 `MeasureTheory.instSigmaFiniteRestrictUnionSet`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {s t : Set α}   [MeasureTheory.Si
gmaFinite (μ.restrict s)] [MeasureT…
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.measurableSet`：∀ {α : Type u_1} {β
 : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace β]   {f : α → β} [inst_1 : Ze…
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl`：ae_eq_zero_compl
 (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem AEMeasurable.ae_eq_of_forall_setLIntegral_eq {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (hgi : ∫⁻ x, g x ∂μ ≠ ∞)
    (hfg : ∀ ⦃s⦄, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  have hf' : AEFinStronglyMeasurable f μ :=
    ENNReal.aefinStronglyMeasurable_of_aemeasurable hfi hf
  have hg' : AEFinStronglyMeasurable g μ :=
    ENNReal.aefinStronglyMeasurable_of_aemeasurable hgi hg
  let s := hf'.sigmaFiniteSet
  let t := hg'.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict (s ∪ t)] g by
    refine ae_of_ae_restrict_of_ae_restrict_compl _ this ?_
    simp only [Set.compl_union]
    have h1 : f =ᵐ[μ.restrict sᶜ] 0 := hf'.ae_eq_zero_compl
    have h2 : g =ᵐ[μ.restrict tᶜ] 0 := hg'.ae_eq_zero_compl
    rw [ae_restrict_iff' (hf'.measurableSet.compl.inter hg'.measurableSet.compl)]
    rw [EventuallyEq, ae_restrict_iff' hf'.measurableSet.compl] at h1
    rw [EventuallyEq, ae_restrict_iff' hg'.measurableSet.compl] at h2
    filter_upwards [h1, h2] with x h1 h2 hx
    rw [h1 (Set.inter_subset_left hx), h2 (Set.inter_subset_right hx)]
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.restrict hg.restrict
    fun u hu huμ ↦ ?_
  rw [Measure.restrict_restrict hu]
  rw [Measure.restrict_apply hu] at huμ
  exact hfg (hu.inter (hf'.measurableSet.union hg'.measurableSet)) huμ

section PiSystem

variable {s : Set (Set α)} {f g : α → ℝ≥0∞}

/-
**MeasureTheory.lintegral_eq_lintegral_of_isPiSystem** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：lintegral_eq_lintegral_of_isPiSystem (h_eq : m0 = MeasurableSpace.generate
From s) (h_inter : IsPiSystem s) (basic : forall t in s, ∫⁻ x in t, f x ∂μ = ∫⁻ 
x in t, g x ∂μ) (h_univ : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) (hf_int : ∫⁻ x, f x ∂μ !=
 ∞) : forall t (_ : MeasurableSet t), ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ
参数：h_eq : m0 = MeasurableSpace.generateFrom s；h_inter : IsPiSystem s；basic : for
all t in s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ；h_univ : ∫⁻ x, f x ∂μ = ∫⁻ x, 
g x ∂μ；hf_int : ∫⁻ x, f x ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setLIntegral_compl`：setLIntegral_compl {f : α -> Real>=0∞}
 {s : Set α} (hsm : MeasurableSet s) (hfs : ∫⁻ x in s, f x ∂μ != ∞) : ∫⁻ x in sᶜ
, f x ∂μ = ∫⁻ x, f x ∂…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_iUnion`：lintegral_iUnion [Countable β] {s : β ->
 Set α} (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (f 
: α -> Real>=0∞) : ∫…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lintegral_eq_lintegral_of_isPiSystem
    (h_eq : m0 = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s)
    (basic : ∀ t ∈ s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ)
    (h_univ : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) (hf_int : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ t (_ : MeasurableSet t), ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ := by
  refine MeasurableSpace.induction_on_inter h_eq h_inter ?_ basic ?_ ?_
  · simp
  · intro t ht h_eq
    rw [setLIntegral_compl ht, setLIntegral_compl ht, h_eq, h_univ]
    · refine ne_of_lt ?_
      calc ∫⁻ x in t, g x ∂μ
      _ ≤ ∫⁻ x, g x ∂μ := setLIntegral_le_lintegral t _
      _ < ∞ := by rw [← h_univ]; exact hf_int.lt_top
    · refine ne_of_lt ?_
      calc ∫⁻ x in t, f x ∂μ
      _ ≤ ∫⁻ x, f x ∂μ := setLIntegral_le_lintegral t _
      _ < ∞ := hf_int.lt_top
  · intro t htd htm h
    simp_rw [lintegral_iUnion htm htd, h]
/-
**MeasureTheory.lintegral_eq_lintegral_of_isPiSystem_of_univ_mem** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_eq_lintegral_of_isPiSystem_of_univ_mem (h_eq : m0 = MeasurableSp
ace.generateFrom s) (h_inter : IsPiSystem s) (h_univ : Set.univ in s) (basic : f
orall t in s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ) (hf_int : ∫⁻ x, f x ∂μ != ∞
) {t : Set α} (ht : MeasurableSet t) : ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ
参数：h_eq : m0 = MeasurableSpace.generateFrom s；h_inter : IsPiSystem s；h_univ : Se
t.univ in s；basic : forall t in s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ；hf_int 
: ∫⁻ x, f x ∂μ != ∞；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_eq_lintegral_of_isPiSystem`：lintegral_eq_lintegr
al_of_isPiSystem (h_eq : m0 = MeasurableSpace.generateFrom s) (h_inter : IsPiSys
tem s) (basic : forall t in s, ∫⁻ x in t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
-/
lemma lintegral_eq_lintegral_of_isPiSystem_of_univ_mem
    (h_eq : m0 = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s) (h_univ : Set.univ ∈ s)
    (basic : ∀ t ∈ s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ)
    (hf_int : ∫⁻ x, f x ∂μ ≠ ∞) {t : Set α} (ht : MeasurableSet t) :
    ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ := by
  refine lintegral_eq_lintegral_of_isPiSystem h_eq h_inter basic ?_ hf_int t ht
  rw [← setLIntegral_univ, ← setLIntegral_univ g]
  exact basic _ h_univ

/-- If two a.e.-measurable functions `α × β → ℝ≥0∞` with finite integrals have the same integral
on every rectangle, then they are almost everywhere equal. -/
/-
**MeasureTheory.ae_eq_of_setLIntegral_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：ae_eq_of_setLIntegral_prod_eq {β : Type*} {mβ : MeasurableSpace β} {μ : Me
asure (α × β)} {f g : α × β -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasura
ble g μ) (hf_int : ∫⁻ x, f x ∂μ != ∞) (h : forall ⦃s : Set α⦄ (_ : MeasurableSet
 s) ⦃t : Set β⦄ (_ : MeasurableSet t), ∫⁻ x in s ×ˢ t, f x ∂μ = ∫⁻ x in s ×ˢ t, 
g x ∂μ) : f =ᵐ[μ] g
参数：α × β；hf : AEMeasurable f μ；hg : AEMeasurable g μ；hf_int : ∫⁻ x, f x ∂μ != ∞；
h : forall ⦃s : Set α⦄ (_ : MeasurableSet s) ⦃t : Set β⦄ (_ : MeasurableSet t), 
∫⁻ x in s ×ˢ t, f x ∂μ = ∫⁻ x in s ×ˢ t, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.AEMeasurable.ae_eq_of_forall_setLIntegral_eq`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → ENNReal},
   AEMeasurable f μ →     AEMeasurable g μ →    …
· 使用引理 `MeasureTheory.lintegral_eq_lintegral_of_isPiSystem_of_univ_mem`：lintegra
l_eq_lintegral_of_isPiSystem_of_univ_mem (h_eq : m0 = MeasurableSpace.generateFr
om s) (h_inter : IsPiSystem s) (h_univ : Set.univ in…
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })

--- 原说明 ---
If two a.e.-measurable functions `α × β → ℝ≥0∞` with finite integrals have the s
ame integral
on every rectangle, then they are almost everywhere equal.
-/
lemma ae_eq_of_setLIntegral_prod_eq {β : Type*} {mβ : MeasurableSpace β}
    {μ : Measure (α × β)} {f g : α × β → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hf_int : ∫⁻ x, f x ∂μ ≠ ∞)
    (h : ∀ ⦃s : Set α⦄ (_ : MeasurableSet s) ⦃t : Set β⦄ (_ : MeasurableSet t),
      ∫⁻ x in s ×ˢ t, f x ∂μ = ∫⁻ x in s ×ˢ t, g x ∂μ) :
    f =ᵐ[μ] g := by
  have hg_int : ∫⁻ x, g x ∂μ ≠ ∞ := by
    rwa [← setLIntegral_univ, ← Set.univ_prod_univ, ← h .univ .univ, Set.univ_prod_univ,
      setLIntegral_univ]
  refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hf_int hg_int fun s hs _ ↦ ?_
  refine lintegral_eq_lintegral_of_isPiSystem_of_univ_mem generateFrom_prod.symm isPiSystem_prod
    ?_ ?_ hf_int hs
  · exact ⟨Set.univ, .univ, Set.univ, .univ, Set.univ_prod_univ⟩
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact h hs ht

end PiSystem

section WithDensity

variable {m : MeasurableSpace α} {μ : Measure α}

/-
**MeasureTheory.withDensity_eq_iff_of_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：withDensity_eq_iff_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (h
f : AEMeasurable f μ) (hg : AEMeasurable g μ) : μ.withDensity f = μ.withDensity 
g ↔ f =ᵐ[μ] g
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀`：ae_eq_of_
forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ] {f g : α -> Real>=0∞} (hf
 : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
-/
theorem withDensity_eq_iff_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf hg fun s hs _ ↦ ?_
    rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩
/-
**MeasureTheory.withDensity_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：withDensity_eq_iff {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEM
easurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ.withDensity f = μ.withDensity g ↔ f
 =ᵐ[μ] g
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ；hfi : ∫⁻ x, f x ∂μ != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEMeasurable.ae_eq_of_forall_setLIntegral_eq`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → ENNReal},
   AEMeasurable f μ →     AEMeasurable g μ →    …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
-/
theorem withDensity_eq_iff {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hfi ?_ fun s hs _ ↦ ?_
    · rwa [← setLIntegral_univ, ← withDensity_apply g MeasurableSet.univ, ← hfg,
        withDensity_apply f MeasurableSet.univ, setLIntegral_univ]
    · rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

end WithDensity

end MeasureTheory

