/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform tightness

This file contains the definitions for uniform tightness for a family of Lp functions.
It is used as a hypothesis to the version of Vitali's convergence theorem for Lp spaces
that works also for spaces of infinite measure. This version of Vitali's theorem
is also proved later in the file.

## Main definitions

* `MeasureTheory.UnifTight`:
  A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
  exists some measurable set `s` with finite measure such that the Lp-norm of
  `f i` restricted to `sᶜ` is smaller than `ε` for all `i`.

## Main results

* `MeasureTheory.unifTight_finite`: a finite sequence of Lp functions is uniformly
  tight.
* `MeasureTheory.tendsto_Lp_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable and uniformly tight converges in Lp if it converges almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable,
  uniformly tight and converges in measure.

## Tags

uniformly integrable, uniformly tight, Vitali convergence theorem
-/

@[expose] public section

namespace MeasureTheory

open Set Filter Topology MeasureTheory NNReal ENNReal

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

section UnifTight

/- This follows closely the `UnifIntegrable` section
from `Mathlib/MeasureTheory/Function/UniformIntegrable.lean`. -/

variable {f g : ι → α → β} {p : ℝ≥0∞}

/-- A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
exists some measurable set `s` with finite measure such that the Lp-norm of
`f i` restricted to `sᶜ` is smaller than `ε` for all `i`. -/
/-
**MeasureTheory.UnifTight** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：UnifTight {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Me
asure α) : Prop
参数：f : ι -> α -> β；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, ther
e
exists some measurable set `s` with finite measure such that the Lp-norm of
`f i` restricted to `sᶜ` is smaller than `ε` for all `i`.
-/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε
/-
**MeasureTheory.unifTight_iff_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifTight_iff_ennreal {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>
=0∞) (μ : Measure α) : UnifTight f p μ ↔ forall ⦃ε : Real>=0∞⦄, 0 < ε -> exists 
s : Set α, μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε
参数：f : ι -> α -> β；p : Real>=0∞；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
theorem unifTight_iff_ennreal {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε := by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp only [zero_lt_top, le_top, implies_true, and_true, true_implies]
  use ∅; simpa only [measure_empty] using zero_ne_top
/-
**MeasureTheory.unifTight_iff_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifTight_iff_real {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞
) (μ : Measure α) : UnifTight f p μ ↔ forall ⦃ε : Real⦄, 0 < ε -> exists s : Set
 α, μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= .ofReal ε
参数：f : ι -> α -> β；p : Real>=0∞；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem unifTight_iff_real {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ .ofReal ε := by
  refine ⟨fun hut rε hrε ↦ hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε ↦ ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))

namespace UnifTight

/-
**MeasureTheory.UnifTight.eventually_cofinite_indicator** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.UnifTight`。
形式化陈述：eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : 
ε != 0) : forallᶠ s in μ.cofinite.smallSets, forall i, eLpNorm (s.indicator (f i
)) p μ <= ε
参数：hf : UnifTight f p μ；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ENNReal.toNNReal_ne_zero`：toNNReal_ne_zero : a.toNNReal != 0 ↔ a != 0 ∧ 
a != ∞
· 使用定理 `Filter.eventually_smallSets'`：eventually_smallSets' {p : Set α -> Prop} 
(hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) : (forallᶠ s in l.smallSets, p s
) ↔ exists s in l,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_mono`：eLpNorm_mono {f : α -> F} {g : α -> G} (h : 
forall x, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `norm_indicator_le_of_subset`：norm_indicator_le_of_subset (h : s subseteq
 t) (f : α -> E) (a : α) : ‖indicator s f a‖ <= ‖indicator t f a‖
· 使用定理 `MeasureTheory.Measure.compl_mem_cofinite`：compl_mem_cofinite : sᶜ in μ.c
ofinite ↔ μ s < ∞
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
-/
theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ s in μ.cofinite.smallSets, ∀ i, eLpNorm (s.indicator (f i)) p μ ≤ ε := by
  by_cases hε_top : ε = ∞
  · subst hε_top; simp
  rcases hf (pos_iff_ne_zero.2 (toNNReal_ne_zero.mpr ⟨hε,hε_top⟩)) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i ↦ (coe_toNNReal hε_top) ▸ hfs i⟩
  · intro s t hst ht i
    exact (eLpNorm_mono <| norm_indicator_le_of_subset hst _).trans (ht i)
  · rwa [Measure.compl_mem_cofinite, lt_top_iff_ne_top]
/-
**MeasureTheory.UnifTight.exists_measurableSet_indicator** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.UnifTight`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UnifTight f p μ →     ∀ {ε : ENNReal},       ε ≠ 0 → ∃
 s, MeasurableSet s ∧ μ s < ⊤ ∧ ∀ (i : ι), MeasureTheory.eLpNorm (sᶜ.indicator (
f i)) p μ ≤ ε
参数：i : ι；sᶜ.indicator (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists_measurable_mem_of_smallSets`：∀ {α : Type u_1} [
inst : MeasurableSpace α] {f : Filter α} [f.IsMeasurablyGenerated] {p : Set α → 
Prop},   (∀ᶠ (s : Set α) in f.smallSets, p…
· 使用定理 `MeasureTheory.Measure.cofinite.instIsMeasurablyGenerated`：∀ {α : Type u_
1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ.cofinite.IsMeasurab
lyGenerated
· 使用定理 `MeasureTheory.UnifTight.eventually_cofinite_indicator`：eventually_cofini
te_indicator (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0) : forallᶠ s in 
μ.cofinite.smallSets, forall i, eLpNorm (s.…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩
/-
**MeasureTheory.UnifTight.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.UnifTight
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifTight f p μ →     MeasureTheory.UnifTight g p μ 
→       (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ) →         (∀ (i 
: ι), MeasureTheory.AEStronglyMeasurable (g i) μ) → MeasureTheory.UnifTight (f +
 g) p μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (g i) μ；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_Lp_half`：exists_Lp_half (p : Real>=0∞) {δ : Real>=0
∞} (hδ : δ != 0) : exists η : Real>=0∞, 0 < η ∧ forall (f g : α -> ε), AEStrongl
yMeasurable f μ ->…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Filter.Eventually.exists_measurable_mem_of_smallSets`：∀ {α : Type u_1} [
inst : MeasurableSpace α] {f : Filter α} [f.IsMeasurablyGenerated] {p : Set α → 
Prop},   (∀ᶠ (s : Set α) in f.smallSets, p…
· 使用定理 `MeasureTheory.Measure.cofinite.instIsMeasurablyGenerated`：∀ {α : Type u_
1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ.cofinite.IsMeasurab
lyGenerated
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `MeasureTheory.UnifTight.eventually_cofinite_indicator`：eventually_cofini
te_indicator (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0) : forallᶠ s in 
μ.cofinite.smallSets, forall i, eLpNorm (s.…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.indicator_add'`：∀ {α : Type u_1} {M : Type u_4} [inst : AddZeroClass
 M] (s : Set α) (f g : α → M),   s.indicator (f + g) = s.indicator f + s.indicat
or g
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := fun ε hε ↦ by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by simp), fun i ↦ ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top le_top).le
  obtain ⟨s, hμs, hsm, hfs, hgs⟩ :
      ∃ s ∈ μ.cofinite, MeasurableSet s ∧
        (∀ i, eLpNorm (s.indicator (f i)) p μ ≤ η) ∧
        (∀ i, eLpNorm (s.indicator (g i)) p μ ≤ η) :=
    ((hf.eventually_cofinite_indicator hη_pos.ne').and
      (hg.eventually_cofinite_indicator hη_pos.ne')).exists_measurable_mem_of_smallSets
  refine ⟨sᶜ, ne_of_lt hμs, fun i ↦ ?_⟩
  have η_cast : ↑η.toNNReal = η := coe_toNNReal hη_top
  calc
    eLpNorm (indicator sᶜᶜ (f i + g i)) p μ
      = eLpNorm (indicator s (f i) + indicator s (g i)) p μ := by rw [compl_compl, indicator_add']
    _ ≤ ε := le_of_lt <|
      hη _ _ ((hf_meas i).indicator hsm) ((hg_meas i).indicator hsm)
        (η_cast ▸ hfs i) (η_cast ▸ hgs i)
/-
**MeasureTheory.UnifTight.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.UnifTight
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f : ι → α → β} {p : 
ENNReal},   MeasureTheory.UnifTight f p μ → MeasureTheory.UnifTight (-f) p μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_neg'`：∀ {α : Type u_1} {G : Type u_6} [inst : AddGroup G] 
(s : Set α) (f : α → G), s.indicator (-f) = -s.indicator f
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
-/
protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf
/-
**MeasureTheory.UnifTight.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.UnifTight
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifTight f p μ →     MeasureTheory.UnifTight g p μ 
→       (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ) →         (∀ (i 
: ι), MeasureTheory.AEStronglyMeasurable (g i) μ) → MeasureTheory.UnifTight (f -
 g) p μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (g i) μ；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.UnifTight.add`：∀ {α : Type u_1} {β : Type u_2} {ι : Type u
_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddCom
mGroup β] {f g : …
· 使用定理 `MeasureTheory.UnifTight.neg`：∀ {α : Type u_1} {β : Type u_2} {ι : Type u
_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddCom
mGroup β] {f : ι …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg
/-
**MeasureTheory.UnifTight.aeeq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.UnifTigh
t`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] {f g : ι → α → β} {p 
: ENNReal},   MeasureTheory.UnifTight f p μ → (∀ (n : ι), f n =ᵐ[μ] g n) → Measu
reTheory.UnifTight g p μ
参数：∀ (n : ι), f n =ᵐ[μ] g n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem aeeq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, hx]

end UnifTight

/-- If two functions agree a.e., then one is tight iff the other is tight. -/
/-
**MeasureTheory.unifTight_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifTight_congr_ae {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n) : Uni
fTight f p μ ↔ UnifTight g p μ
参数：hfg : forall n, f n =ᵐ[μ] g n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.UnifTight.aeeq`：∀ {α : Type u_1} {β : Type u_2} {ι : Type 
u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup β] {f g : …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If two functions agree a.e., then one is tight iff the other is tight.
-/
theorem unifTight_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight f p μ ↔ UnifTight g p μ :=
  ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

/-- A constant sequence is tight. -/
/-
**MeasureTheory.unifTight_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifTight_const {g : α -> β} (hp_ne_top : p != ∞) (hg : MemLp g p μ) : Uni
fTight (fun _ : ι => g) p μ
参数：hp_ne_top : p != ∞；hg : MemLp g p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {β : Type u
_7}   [inst : NormedAddCommGroup β],   p ≠ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A constant sequence is tight.
-/
theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_eLpNorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

/-- A single function is tight. -/
/-
**MeasureTheory.unifTight_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：unifTight_of_subsingleton [Subsingleton ι] (hp_top : p != ∞) {f : ι -> α -
> β} (hf : forall i, MemLp (f i) p μ) : UnifTight f p μ
参数：hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {β : Type u
_7}   [inst : NormedAddCommGroup β],   p ≠ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A single function is tight.
-/
theorem unifTight_of_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by simp, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
  case neg => exact ⟨∅, (by simp), fun i => False.elim <| hι <| Nonempty.intro i⟩
  obtain ⟨i⟩ := hι
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert! hfε.le

/-- This lemma is less general than `MeasureTheory.unifTight_finite` which applies to
all sequences indexed by a finite type. -/
/-
**MeasureTheory.unifTight_fin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is less general than `MeasureTheory.unifTight_finite` which applies t
o
all sequences indexed by a finite type.
-/
private theorem unifTight_fin (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction n with
  | zero => exact fun {f} hf ↦ unifTight_of_subsingleton hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    by_cases hε_top : ε = ∞
    · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
    let g : Fin n → α → β := fun k => f k.castSucc
    have hgLp : ∀ i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨S, hμS, hFε⟩ := h hgLp hε
    obtain ⟨s, _, hμs, hfε⟩ :=
      (hfLp (Fin.last n)).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
    refine ⟨s ∪ S, (by finiteness), fun i => ?_⟩
    by_cases! hi : i.val < n
    · rw [show f i = g ⟨i.val, hi⟩ from rfl, compl_union, ← indicator_indicator]
      apply (eLpNorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm i.is_le hi)
      rw [compl_union, inter_comm, ← indicator_indicator]
      exact (eLpNorm_indicator_le _).trans hfε.le

/-- A finite sequence of Lp functions is uniformly tight. -/
/-
**MeasureTheory.unifTight_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：unifTight_finite [Finite ι] (hp_top : p != ∞) {f : ι -> α -> β} (hf : fora
ll i, MemLp (f i) p μ) : UnifTight f p μ
参数：hp_top : p != ∞；hf : forall i, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `_private.Mathlib.MeasureTheory.Function.UnifTight.0.MeasureTheory.unifTi
ght_fin`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} [inst : NormedAddCommGroup β]   {p : ENNReal},   p ≠ ⊤…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x

--- 原说明 ---
A finite sequence of Lp functions is uniformly tight.
-/
theorem unifTight_finite [Finite ι] (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n → α → β := f ∘ hn.some.symm
  have hg : ∀ i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  simpa only [g, Function.comp_apply, Equiv.symm_apply_apply] using hfε (hn.some i)

end UnifTight

section VitaliConvergence

variable {μ : Measure α} {p : ℝ≥0∞} {f : ℕ → α → β} {g : α → β}

/-! Both directions and an iff version of Vitali's convergence theorem on measure spaces
of not necessarily finite volume. See `Thm III.6.15` of Dunford & Schwartz, Part I (1958). -/

/- We start with the reverse direction. We only need to show that uniform tightness follows
from convergence in Lp. Mathlib already has the analogous `unifIntegrable_of_tendsto_Lp`
and `tendstoInMeasure_of_tendsto_eLpNorm`. -/

/-- Intermediate lemma for `unifTight_of_tendsto_Lp`. -/
/-
**MeasureTheory.unifTight_of_tendsto_Lp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate lemma for `unifTight_of_tendsto_Lp`.
-/
private theorem unifTight_of_tendsto_Lp_zero (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n ↦ eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifTight f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ENNReal.coe_pos])
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨s, hμs, fun n => ?_⟩
  by_cases! hn : n < N
  · exact hFε ⟨n, hn⟩
  · exact (eLpNorm_indicator_le _).trans (hNε n hn)

/-- Convergence in Lp implies uniform tightness. -/
/-
**MeasureTheory.unifTight_of_tendsto_Lp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convergence in Lp implies uniform tightness.
-/
private theorem unifTight_of_tendsto_Lp (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifTight f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg

set_option linter.style.whitespace false in -- manual alignment is not recognised
/- Next we deal with the forward direction. The `MemLp` and `TendstoInMeasure` hypotheses
are unwrapped and strengthened (by known lemmas) to also have the `StronglyMeasurable`
and a.e. convergence hypotheses. The bulk of the proof is done under these stronger hypotheses. -/

/-- Bulk of the proof under strengthened hypotheses. Invoked from `tendsto_Lp_of_tendsto_ae`. -/
/-
**MeasureTheory.tendsto_Lp_of_tendsto_ae_of_meas** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bulk of the proof under strengthened hypotheses. Invoked from `tendsto_Lp_of_ten
dsto_ae`.
-/
private theorem tendsto_Lp_of_tendsto_ae_of_meas (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε ≠ ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (ofNat_ne_top)
  -- use tightness to divide the domain into interior and exterior
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := MemLp.exists_eLpNorm_indicator_compl_lt hp' hg' hε'.ne'
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut.exists_measurableSet_indicator hε'.ne'
  have hmE := hmEf.union hmEg
  have hfmE := (measure_union_le Ef Eg).trans_lt (add_lt_top.mpr ⟨hμEf, hμEg⟩)
  set E : Set α := Ef ∪ Eg
  -- use uniform integrability to get control on the limit over E
  have hgE' := MemLp.restrict E hg'
  have huiE := hui.restrict E
  have hfgE : (∀ᵐ x ∂(μ.restrict E), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :=
    ae_restrict_of_ae hfg
  -- `tendsto_Lp_of_tendsto_ae_of_meas` needs to
  -- synthesize an argument `[IsFiniteMeasure (μ.restrict E)]`.
  -- It is enough to have in the context a term of `Fact (μ E < ∞)`, which is our `ffmE` below,
  -- which is automatically fed into `Restrict.isFiniteInstance`.
  have ffmE := Fact.mk hfmE
  have hInner := tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' hf hg hgE' huiE hfgE
  rw [ENNReal.tendsto_atTop_zero] at hInner
  -- get a sufficiently large N for given ε, and consider any n ≥ N
  obtain ⟨N, hfngε⟩ := hInner (ε / 3) hε'
  use N; intro n hn
  -- get interior estimates
  have hmfngE : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE).aestronglyMeasurable
  have hfngEε := calc
    eLpNorm (E.indicator (f n - g)) p μ
      = eLpNorm (f n - g) p (μ.restrict E) := eLpNorm_indicator_eq_eLpNorm_restrict hmE
    _ ≤ ε / 3                              := hfngε n hn
  -- get exterior estimates
  have hmgEc : AEStronglyMeasurable _ μ := (hg.indicator hmE.compl).aestronglyMeasurable
  have hgEcε := calc
    eLpNorm (Eᶜ.indicator g) p μ
      ≤ eLpNorm (Efᶜ.indicator (Egᶜ.indicator g)) p μ := by
        unfold E; rw [compl_union, ← indicator_indicator]
    _ ≤ eLpNorm (Egᶜ.indicator g) p μ := eLpNorm_indicator_le _
    _ ≤ ε / 3 := hgε.le
  have hmfnEc : AEStronglyMeasurable _ μ := ((hf n).indicator hmE.compl).aestronglyMeasurable
  have hfnEcε : eLpNorm (Eᶜ.indicator (f n)) p μ ≤ ε / 3 := calc
    eLpNorm (Eᶜ.indicator (f n)) p μ
      ≤ eLpNorm (Egᶜ.indicator (Efᶜ.indicator (f n))) p μ := by
        unfold E; rw [compl_union, inter_comm, ← indicator_indicator]
    _ ≤ eLpNorm (Efᶜ.indicator (f n)) p μ := eLpNorm_indicator_le _
    _ ≤ ε / 3 := hfε n
  have hmfngEc : AEStronglyMeasurable _ μ :=
    (((hf n).sub hg).indicator hmE.compl).aestronglyMeasurable
  have hfngEcε := calc
    eLpNorm (Eᶜ.indicator (f n - g)) p μ
      = eLpNorm (Eᶜ.indicator (f n) - Eᶜ.indicator g) p μ := by
        rw [(Eᶜ.indicator_sub' _ _)]
    _ ≤ eLpNorm (Eᶜ.indicator (f n)) p μ + eLpNorm (Eᶜ.indicator g) p μ := by
        apply eLpNorm_sub_le (by assumption) (by assumption) hp
    _ ≤ ε / 3 + ε / 3 := add_le_add hfnEcε hgEcε
  -- finally, combine interior and exterior estimates
  calc
    eLpNorm (f n - g) p μ
      = eLpNorm (Eᶜ.indicator (f n - g) + E.indicator (f n - g)) p μ := by
        congr; exact (E.indicator_compl_add_self _).symm
    _ ≤ eLpNorm (indicator Eᶜ (f n - g)) p μ + eLpNorm (indicator E (f n - g)) p μ := by
        apply eLpNorm_add_le (by assumption) (by assumption) hp
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hfngEcε hfngEε
    _ = ε := by simp only [ENNReal.add_thirds]

/-- Lemma used in `tendsto_Lp_of_tendsto_ae`. -/
/-
**MeasureTheory.ae_tendsto_ae_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lemma used in `tendsto_Lp_of_tendsto_ae`.
-/
private theorem ae_tendsto_ae_congr {f f' : ℕ → α → β} {g g' : α → β}
    (hff' : ∀ (n : ℕ), f n =ᵐ[μ] f' n) (hgg' : g =ᵐ[μ] g')
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)) := by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx

/-- Forward direction of Vitali's convergence theorem, with a.e. instead of `InMeasure`
convergence -/
/-
**MeasureTheory.tendsto_Lp_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：tendsto_Lp_of_tendsto_ae (hp : 1 <= p) (hp' : p != ∞) {f : Nat -> α -> β} 
{g : α -> β} (haef : forall n, AEStronglyMeasurable (f n) μ) (hg' : MemLp g p μ)
 (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ) (hfg : forallᵐ x ∂μ, Tends
to (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => eLpNorm (f n - g) p μ) 
atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；haef : forall n, AEStronglyMeasurable (f n) μ；hg' : 
MemLp g p μ；hui : UnifIntegrable f p μ；hut : UnifTight f p μ；hfg : forallᵐ x ∂μ,
 Tendsto (fun n => f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.UnifIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {ι :
 Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup β] {f g : …
· 使用定理 `MeasureTheory.UnifTight.aeeq`：∀ {α : Type u_1} {β : Type u_2} {ι : Type 
u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup β] {f g : …
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `_private.Mathlib.MeasureTheory.Function.UnifTight.0.MeasureTheory.ae_ten
dsto_ae_congr`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst : N
ormedAddCommGroup β] {μ : MeasureTheory.Measure α}   {f f' : ℕ → α → β} {g …
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.MeasureTheory.Function.UnifTight.0.MeasureTheory.tendst
o_Lp_of_tendsto_ae_of_meas`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} [inst : NormedAddCommGroup β] {μ : MeasureTheory.Measure α}   {p : ENNReal},
   1 ≤ p…

--- 原说明 ---
Forward direction of Vitali's convergence theorem, with a.e. instead of `InMeasu
re`
convergence
-/
theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.aeeq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_mk
  have hgg' := hg'.aestronglyMeasurable.ae_eq_mk (μ := μ)
  have hg'' := hg'.ae_eq hgg'
  have haefg' := ae_tendsto_ae_congr hff' hgg' hfg
  set f' := fun n => (haef n).mk (μ := μ)
  set g' := hg'.aestronglyMeasurable.mk (μ := μ)
  have haefg (n : ℕ) : f n - g =ᵐ[μ] f' n - g' := (hff' n).sub hgg'
  have hsnfg (n : ℕ) := eLpNorm_congr_ae (p := p) (haefg n)
  apply Filter.Tendsto.congr (fun n => (hsnfg n).symm)
  exact tendsto_Lp_of_tendsto_ae_of_meas hp hp' hf hg hg'' hui' hut' haefg'

/-- Forward direction of Vitali's convergence theorem:
if `f` is a sequence of uniformly integrable, uniformly tight functions that converge in
measure to some function `g` in a finite measure space, then `f` converge in Lp to `g`. -/
/-
**MeasureTheory.tendsto_Lp_of_tendstoInMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：tendsto_Lp_of_tendstoInMeasure (hp : 1 <= p) (hp' : p != ∞) (hf : forall n
, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ) 
(hut : UnifTight f p μ) (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n =>
 eLpNorm (f n - g) p μ) atTop (𝓝 0)
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, AEStronglyMeasurable (f n) μ；hg : Mem
Lp g p μ；hui : UnifIntegrable f p μ；hut : UnifTight f p μ；hfg : TendstoInMeasure
 μ f atTop g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_subseq_tendsto`：tendsto_of_subseq_tendsto {ι : Type*} 
{x : ι -> α} {f : Filter α} {l : Filter ι} [l.IsCountablyGenerated] (hxy : foral
l ns : Nat -> ι, Tends…
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`：∀ {α : Type u_1} {
E : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Pseu
doEMetricSpace E]   {f : ℕ → α → E} {g : α…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `MeasureTheory.tendsto_Lp_of_tendsto_ae`：tendsto_Lp_of_tendsto_ae (hp : 1
 <= p) (hp' : p != ∞) {f : Nat -> α -> β} {g : α -> β} (haef : forall n, AEStron
glyMeasurable (f n) μ) (hg' …

--- 原说明 ---
Forward direction of Vitali's convergence theorem:
if `f` is a sequence of uniformly integrable, uniformly tight functions that con
verge in
measure to some function `g` in a finite measure space, then `f` converge in Lp 
to `g`.
-/
theorem tendsto_Lp_of_tendstoInMeasure (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩ := hui hε
        ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      (fun ε hε => -- `UnifTight` on a subsequence
        let ⟨s, hμs, hfε⟩ := hut hε
        ⟨s, hμs, fun i => hfε _⟩)
      hms'⟩

/-- **Vitali's convergence theorem** (non-finite measure version).

A sequence of functions `f` converges to `g` in Lp
if and only if it is uniformly integrable, uniformly tight and converges to `g` in measure. -/
/-
**MeasureTheory.tendstoInMeasure_iff_tendsto_Lp** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendstoInMeasure_iff_tendsto_Lp (hp : 1 <= p) (hp' : p != ∞) (hf : forall 
n, MemLp (f n) p μ) (hg : MemLp g p μ) : TendstoInMeasure μ f atTop g ∧ UnifInte
grable f p μ ∧ UnifTight f p μ ↔ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop 
(𝓝 0) where mp h
参数：hp : 1 <= p；hp' : p != ∞；hf : forall n, MemLp (f n) p μ；hg : MemLp g p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_Lp_of_tendstoInMeasure`：tendsto_Lp_of_tendstoInMea
sure (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, AEStronglyMeasurable (f n) μ) 
(hg : MemLp g p μ) (hui : UnifInte…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`：tendstoInMeasure_of_t
endsto_eLpNorm [NormedAddCommGroup E] {l : Filter ι} (hp_ne_zero : p != 0) (hf :
 forall n, AEStronglyMeasurable (f n) μ…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.unifIntegrable_of_tendsto_Lp`：unifIntegrable_of_tendsto_Lp
 (hp : 1 <= p) (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ) (hg : MemLp g p μ
) (hfg : Tendsto (fun n => eLpNo…
· 使用定理 `_private.Mathlib.MeasureTheory.Function.UnifTight.0.MeasureTheory.unifTi
ght_of_tendsto_Lp`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [inst
 : NormedAddCommGroup β] {μ : MeasureTheory.Measure α}   {p : ENNReal} {f : ℕ →…

--- 原说明 ---
**Vitali's convergence theorem** (non-finite measure version).

A sequence of functions `f` converges to `g` in Lp
if and only if it is uniformly integrable, uniformly tight and converges to `g` 
in measure.
-/
theorem tendstoInMeasure_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) where
  mp h := tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1
  mpr h := ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTight_of_tendsto_Lp hp' hf hg h⟩

end VitaliConvergence
end MeasureTheory

