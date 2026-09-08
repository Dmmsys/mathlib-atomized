/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-!
# Pointwise convergence of infinite sums in `Lᵖ`

If a series in `Lᵖ` is converging in norm, then the series also converges pointwise
almost everywhere.
-/

public section

open Finset Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {X E : Type*} {_ : MeasurableSpace X} {μ : Measure X} [NormedAddCommGroup E]

/-- If a series of functions has summable `L^p` norms for some `1 ≤ p`, then the norms are ae
pointwise summable. -/
/-
**MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：summable_norm_of_tsum_eLpNorm_ne_top {ι : Type*} [Countable ι] {p : Real>=
0∞} (hp : 1 <= p) {f : ι -> X -> E} (hf : forall n, AEStronglyMeasurable (f n) μ
) (h'f : ∑' n, eLpNorm (f n) p μ != ∞) : forallᵐ a ∂μ, Summable (fun n => ‖f n a
‖)
参数：hp : 1 <= p；hf : forall n, AEStronglyMeasurable (f n) μ；h'f : ∑' n, eLpNorm (
f n) p μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `MeasureTheory.ae_le_eLpNormEssSup`：ae_le_eLpNormEssSup {f : α -> ε} : fo
rallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
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
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
If a series of functions has summable `L^p` norms for some `1 ≤ p`, then the nor
ms are ae
pointwise summable.
-/
theorem summable_norm_of_tsum_eLpNorm_ne_top {ι : Type*} [Countable ι]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → X → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h'f : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
  suffices H : ∀ᵐ a ∂μ, ∑' n, ‖f n a‖ₑ < ∞ by
    filter_upwards [H] with x hx using tsum_enorm_ne_top_iff_summable_norm.1 hx.ne
  -- the result is straightforward in `L^∞`.
  rcases eq_top_or_lt_top p with rfl | h'p
  · have : ∀ᵐ x ∂μ, ∀ n, ‖f n x‖ₑ ≤ eLpNorm (f n) ∞ μ := ae_all_iff.2 (fun n ↦ ae_le_eLpNormEssSup)
    filter_upwards [this] with x hx
    apply lt_of_le_of_lt ?_ h'f.lt_top
    gcongr with i
    exact hx i
  /- Let us now consider `p < ∞`. In a measurable set `s` of finite measure, the `L^1` norm is
  controlled by a multiple of the `L^p` norm, so the `L^1` norms are summable, i.e.,
  `∫ x ∈ s, ∑ ‖f n x‖ₑ ∂μ < ∞`. This forces the sum to be finite ae. -/
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
      ∀ᵐ x ∂μ, x ∈ s → ∑' n, ‖f n x‖ₑ < ∞ := by
    rw [← ae_restrict_iff' hs]
    apply ae_lt_top' (AEMeasurable.tsum (fun i ↦ (hf i).restrict.enorm))
    rw [lintegral_tsum (fun i ↦ (hf i).restrict.enorm)]
    apply ne_of_lt
    have : ∑' n, eLpNorm (f n) p (μ.restrict s) *
        (μ.restrict s) Set.univ ^ (1 / ENNReal.toReal 1 - 1 / p.toReal) < ∞ := by
      rw [ENNReal.tsum_mul_right]
      apply ENNReal.mul_lt_top ?_ ?_
      · apply lt_of_le_of_lt ?_ h'f.lt_top
        gcongr
        exact Measure.restrict_le_self
      · simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, ENNReal.toReal_one,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, one_div]
        apply ENNReal.rpow_lt_top_of_nonneg _ h's
        simp only [sub_nonneg]
        apply inv_le_one_of_one_le₀
        rw [← ENNReal.ofReal_le_iff_le_toReal h'p.ne]
        simpa
    apply lt_of_le_of_lt ?_ this
    gcongr with i
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hf i).restrict
  /- We wish now to reduce to finite measure sets to apply the above. The function `f n` in `L^p`
  has a sigma-finite support, that we denote by `s n`. -/
  have B n : ∃ s, MeasurableSet s ∧ (f n =ᵐ[μ.restrict sᶜ] 0) ∧ SigmaFinite (μ.restrict s) := by
    apply AEFinStronglyMeasurable.exists_set_sigmaFinite
    have : MemLp (f n) p μ := by
      simpa [MemLp, hf] using lt_of_le_of_lt (ENNReal.le_tsum n) h'f.lt_top
    exact this.aefinStronglyMeasurable (zero_lt_one.trans_le hp).ne' h'p.ne
  choose! s s_meas hs h's using B
  /- Covering `s n` by countably many sets of finite measure, we deduce using the above that
  the series of norms is ae finite on `s n`. -/
  have C : ∀ᵐ x ∂μ, ∀ n, x ∈ s n → ∑' n, ‖f n x‖ₑ < ∞ := by
    apply ae_all_iff.2 (fun n ↦ ?_)
    have : ∀ᵐ x ∂μ, ∀ i, x ∈ s n ∩ spanningSets (μ.restrict (s n)) i → ∑' n, ‖f n x‖ₑ < ∞ := by
      apply ae_all_iff.2 (fun i ↦ ?_)
      apply A _ ((s_meas n).inter (measurableSet_spanningSets _ _))
      rw [Set.inter_comm, ← Measure.restrict_apply' (s_meas n)]
      exact (measure_spanningSets_lt_top _ _).ne
    filter_upwards [this] with x hx h'x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ spanningSets (μ.restrict (s n)) i := ⟨_, mem_spanningSetsIndex _ _⟩
    exact hx i ⟨h'x, hi⟩
  /- Finally, we get the result in `⋃ n, s n`. Outside of this set, all the functions are ae
  zero, so the result is trivial there. -/
  have D : ∀ᵐ x ∂μ, ∀ n, x ∉ s n → f n x = 0 :=
    ae_all_iff.2 (fun n ↦ (ae_restrict_iff' (s_meas n).compl).1 (hs n))
  filter_upwards [C, D] with x hx h'x
  by_cases! h : ∃ n, x ∈ s n
  · rcases h with ⟨n, hn⟩
    exact hx n hn
  · have E n : f n x = 0 := h'x n (h n)
    simp [E]

namespace Lp

/-
**MeasureTheory.Lp.hasSum_coeFn_tsum_nat** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasSum_coeFn_tsum_nat {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [CompleteSpace E] {f : ℕ → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ∀ᵐ a ∂μ, HasSum (fun n ↦ f n a) (⇑(∑' n, f n) a) := by
  have A : ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top hp.out (fun n ↦ Lp.aestronglyMeasurable (f n))
    simpa [enorm_def] using hf
  have B : ∀ᵐ x ∂μ, ∀ n, ⇑(∑ i ∈ range n, f i) x = ∑ i ∈ range n, f i x := by
    rw [ae_all_iff]
    exact fun i ↦ coeFn_fun_finsetSum _ _
  obtain ⟨ns, hns, nslim⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun i ↦ (∑ j ∈ range (ns i), f j : Lp E p μ) x) atTop (𝓝 ((∑' n, f n) x)) := by
    have : Tendsto (fun i ↦ (∑ j ∈ range i, f j)) atTop (𝓝 (∑' n, f n)) :=
      Summable.tendsto_sum_tsum_nat (Summable.of_enorm hf)
    exact (tendstoInMeasure_of_tendsto_Lp this).exists_seq_tendsto_ae
  filter_upwards [A, B, nslim] with x S h'x h''x
  apply hasSum_of_subseq_of_summable S (tendsto_finset_range.comp hns.tendsto_atTop)
  simpa only [h'x, Function.comp] using h''x

/-- If a series is converging in `L^p`, then it also converges pointwise almost everywhere. -/
/-
**MeasureTheory.Lp.hasSum_coeFn_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：hasSum_coeFn_tsum {p : Real>=0∞} [hp : Fact (1 <= p)] {ι : Type*} [Countab
le ι] [CompleteSpace E] {f : ι -> Lp E p μ} (hf : ∑' n, ‖f n‖ₑ != ∞) : forallᵐ a
 ∂μ, HasSum (fun n => f n a) (⇑(∑' n, f n) a)
参数：1 <= p；hf : ∑' n, ‖f n‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.coeFn_fun_finsetSum`：coeFn_fun_finsetSum {ι : Type*} (s
 : Finset ι) (f : ι -> Lp E p μ) : ⇑(∑ i in s, f i) =ᵐ[μ] fun x => ∑ i in s, f i
 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum.0.MeasureThe
ory.Lp.hasSum_coeFn_tsum_nat`：∀ {X : Type u_1} {E : Type u_2} {x : MeasurableSpa
ce X} {μ : MeasureTheory.Measure X} [inst : NormedAddCommGroup E]   {p : ENNReal
} [hp : Fa…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…

--- 原说明 ---
If a series is converging in `L^p`, then it also converges pointwise almost ever
ywhere.
-/
theorem hasSum_coeFn_tsum {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {ι : Type*} [Countable ι]
    [CompleteSpace E] {f : ι → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ∀ᵐ a ∂μ, HasSum (fun n ↦ f n a) (⇑(∑' n, f n) a) := by
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    filter_upwards [coeFn_fun_finsetSum univ f] with x hx
    rw [tsum_fintype, hx]
    exact hasSum_fintype _
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := ι)
    have : ∀ᵐ a ∂μ, HasSum (fun n ↦ f (e n) a) (⇑(∑' n, f (e n)) a) := by
      apply Lp.hasSum_coeFn_tsum_nat
      convert hf
      exact e.tsum_eq (fun i ↦ ‖f i‖ₑ)
    filter_upwards [this] with x hx
    rw [e.tsum_eq] at hx
    exact e.hasSum_iff.1 hx
/-
**MeasureTheory.Lp.coeFn_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_tsum {ι : Type*} [Countable ι] {p : Real>=0∞} [hp : Fact (1 <= p)] [
CompleteSpace E] {f : ι -> Lp E p μ} (hf : ∑' n, ‖f n‖ₑ != ∞) : ⇑(∑' n, f n) =ᵐ[
μ] fun x => ∑' n, f n x
参数：1 <= p；hf : ∑' n, ‖f n‖ₑ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.hasSum_coeFn_tsum`：hasSum_coeFn_tsum {p : Real>=0∞} [hp
 : Fact (1 <= p)] {ι : Type*} [Countable ι] [CompleteSpace E] {f : ι -> Lp E p μ
} (hf : ∑' n, ‖f n‖ₑ != …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem coeFn_tsum {ι : Type*} [Countable ι] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [CompleteSpace E] {f : ι → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ⇑(∑' n, f n) =ᵐ[μ] fun x ↦ ∑' n, f n x := by
  filter_upwards [Lp.hasSum_coeFn_tsum hf] with x hx using hx.tsum_eq.symm

end Lp

end MeasureTheory

