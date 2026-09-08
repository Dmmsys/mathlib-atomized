/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Lp seminorm with respect to trimmed measure

In this file we prove basic properties of the Lp-seminorm of a function
with respect to the restriction of a measure to a sub-σ-algebra.
-/

public section

namespace MeasureTheory

open Filter
open scoped ENNReal

variable {α E ε : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup E] [TopologicalSpace ε] [ContinuousENorm ε]

/-
**MeasureTheory.eLpNorm'_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {m m0 : MeasurableSpace α} {q : ℝ} {μ : Me
asureTheory.Measure α}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε
] (hm : m ≤ m0) {f : α → ε},   MeasureTheory.StronglyMeasurable f → MeasureTheor
y.eLpNorm' f q (μ.trim hm) = MeasureTheory.eLpNorm' f q μ
参数：hm : m ≤ m0；μ.trim hm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.lintegral_trim`：lintegral_trim {μ : Measure α} (hm : m <= 
m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : ∫⁻ a, f a ∂μ.trim hm = ∫⁻ a, f 
a ∂μ
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
-/
theorem eLpNorm'_trim (hm : m ≤ m0) {f : α → ε} (hf : StronglyMeasurable[m] f) :
    eLpNorm' f q (μ.trim hm) = eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  congr 1
  exact lintegral_trim hm (by fun_prop)
/-
**MeasureTheory.limsup_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：limsup_trim (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : li
msup f (ae (μ.trim hm)) = limsup f (ae μ)
参数：hm : m <= m0；hf : Measurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem limsup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    limsup f (ae (μ.trim hm)) = limsup f (ae μ) := by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : ℝ≥0∞ | ∀ᵐ n ∂μ.trim hm, f n ≤ a } = { a : ℝ≥0∞ | ∀ᵐ n ∂μ, f n ≤ a } by
    rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : μ { x | ¬f x ≤ a } = μ.trim hm { x | ¬f x ≤ a } by
    simp_rw [Set.mem_ofPred_eq, ae_iff, h_meas_eq]
  refine (trim_measurableSet_eq hm ?_).symm
  exact (measurableSet_le hf measurable_const).compl
/-
**MeasureTheory.essSup_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：essSup_trim (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) : es
sSup f (μ.trim hm) = essSup f μ
参数：hm : m <= m0；hf : Measurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.limsup_trim`：limsup_trim (hm : m <= m0) {f : α -> Real>=0∞
} (hf : Measurable[m] f) : limsup f (ae (μ.trim hm)) = limsup f (ae μ)
-/
theorem essSup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    essSup f (μ.trim hm) = essSup f μ := by
  simp_rw [essSup]
  exact limsup_trim hm hf
/-
**MeasureTheory.eLpNormEssSup_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_trim (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m]
 f) : eLpNormEssSup f (μ.trim hm) = eLpNormEssSup f μ
参数：hm : m <= m0；hf : StronglyMeasurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.essSup_trim`：essSup_trim (hm : m <= m0) {f : α -> Real>=0∞
} (hf : Measurable[m] f) : essSup f (μ.trim hm) = essSup f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
-/
theorem eLpNormEssSup_trim (hm : m ≤ m0) {f : α → ε} (hf : StronglyMeasurable[m] f) :
    eLpNormEssSup f (μ.trim hm) = eLpNormEssSup f μ :=
  essSup_trim _ (@StronglyMeasurable.enorm _ m _ _ _ _ hf)
/-
**MeasureTheory.eLpNorm_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_trim (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f) : 
eLpNorm f p (μ.trim hm) = eLpNorm f p μ
参数：hm : m <= m0；hf : StronglyMeasurable[m] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_trim`：eLpNormEssSup_trim (hm : m <= m0) {f :
 α -> ε} (hf : StronglyMeasurable[m] f) : eLpNormEssSup f (μ.trim hm) = eLpNormE
ssSup f μ
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_trim`：∀ {α : Type u_1} {ε : Type u_3} {m m0 : Mea
surableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [inst : TopologicalSpace
 ε] [inst_1 : Con…
-/
theorem eLpNorm_trim (hm : m ≤ m0) {f : α → ε} (hf : StronglyMeasurable[m] f) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, eLpNorm_exponent_top] using eLpNormEssSup_trim hm hf
  simpa only [eLpNorm_eq_eLpNorm' h0 h_top] using eLpNorm'_trim hm hf
/-
**MeasureTheory.eLpNorm_trim_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_trim_ae (hm : m <= m0) {f : α -> ε} (hf : AEStronglyMeasurable[m] 
f (μ.trim hm)) : eLpNorm f p (μ.trim hm) = eLpNorm f p μ
参数：hm : m <= m0；hf : AEStronglyMeasurable[m] f (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.ae_eq_of_ae_eq_trim`：ae_eq_of_ae_eq_trim {E} {hm : m <= m0
} {f₁ f₂ : α -> E} (h12 : f₁ =ᵐ[μ.trim hm] f₂) : f₁ =ᵐ[μ] f₂
· 使用定理 `MeasureTheory.eLpNorm_trim`：eLpNorm_trim (hm : m <= m0) {f : α -> ε} (hf
 : StronglyMeasurable[m] f) : eLpNorm f p (μ.trim hm) = eLpNorm f p μ
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
theorem eLpNorm_trim_ae (hm : m ≤ m0) {f : α → ε} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  rw [eLpNorm_congr_ae hf.ae_eq_mk, eLpNorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact eLpNorm_trim hm hf.stronglyMeasurable_mk
/-
**MeasureTheory.memLp_of_memLp_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_of_memLp_trim (hm : m <= m0) {f : α -> ε} (hf : MemLp f p (μ.trim hm
)) : MemLp f p μ
参数：hm : m <= m0；hf : MemLp f p (μ.trim hm)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aestronglyMeasurable_of_aestronglyMeasurable_trim`：∀ {β : Type u_2} [ins
t : TopologicalSpace β] {α : Type u_5} {m m0 : MeasurableSpace α} {μ : MeasureTh
eory.Measure α}   (hm : m ≤ m0) {f : α …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_trim_ae`：eLpNorm_trim_ae (hm : m <= m0) {f : α -> 
ε} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) : eLpNorm f p (μ.trim hm) = eLpN
orm f p μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem memLp_of_memLp_trim (hm : m ≤ m0) {f : α → ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (eLpNorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

end MeasureTheory

