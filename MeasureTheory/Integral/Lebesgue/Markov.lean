/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Markov's inequality

The classical form of Markov's inequality states that for a nonnegative random variable `X` and
real number `ε > 0`, `P(X ≥ ε) ≤ E(X) / ε`. Multiplying both sides by the measure of the space gives
the measure-theoretic form:
```
μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε
```
This file proves a few variants of the inequality and other lemmas that depend on it.
-/

public section

namespace MeasureTheory

open Set Filter ENNReal Topology

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
/-
**MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：lintegral_add_mul_meas_add_le_le_lintegral {f g : α -> Real>=0∞} (hle : f 
<=ᵐ[μ] g) (hg : AEMeasurable g μ) (ε : Real>=0∞) : ∫⁻ a, f a ∂μ + ε * μ { x | f 
x + ε <= g x } <= ∫⁻ a, g a ∂μ
参数：hle : f <=ᵐ[μ] g；hg : AEMeasurable g μ；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_indicator₀`：lintegral_indicator₀ {s : Set α} (hs
 : NullMeasurableSet s μ) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a 
in s, f a ∂μ
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `Measurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   [MeasurableAdd M
], Measura…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.NullMeasurable.measurable'`：∀ {α : Type u_2} {β : Type u_3
} [m : MeasurableSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureT
heory.Measure α}, MeasureTheor…
· 使用定理 `Measurable.nullMeasurable`：∀ {α : Type u_2} {β : Type u_3} [m : Measurab
leSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α
}, Measurable f…
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A version of **Markov's inequality** for two functions. It doesn't follow from t
he standard
Markov's inequality because we only assume measurability of `g`, not `f`.
-/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε ≤ g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε ≤ g x } := by
      rw [hφ_eq]
    _ ≤ ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε ≤ g x } := by
      gcongr
      exact hφ_le _
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm, lintegral_indicator₀, setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
/-
**MeasureTheory.mul_meas_ge_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：mul_meas_ge_le_lintegral {f : α -> Real>=0∞} (hf : Measurable f) (ε : Real
>=0∞) : ε * μ { x | ε <= f x } <= ∫⁻ a, f a ∂μ
参数：hf : Measurable f；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mul_meas_ge_le_lintegral₀`：mul_meas_ge_le_lintegral₀ {f : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= f x } <
= ∫⁻ a, f a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
**Markov's inequality** also known as **Chebyshev's first inequality**.
-/
theorem mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le) hf ε

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`AEMeasurable`, see `mul_meas_ge_le_lintegral₀`. -/
/-
**MeasureTheory.mul_meas_ge_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：mul_meas_ge_le_lintegral {f : α -> Real>=0∞} (hf : Measurable f) (ε : Real
>=0∞) : ε * μ { x | ε <= f x } <= ∫⁻ a, f a ∂μ
参数：hf : Measurable f；ε : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mul_meas_ge_le_lintegral₀`：mul_meas_ge_le_lintegral₀ {f : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= f x } <
= ∫⁻ a, f a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
**Markov's inequality** also known as **Chebyshev's first inequality**. For a ve
rsion assuming
`AEMeasurable`, see `mul_meas_ge_le_lintegral₀`.
-/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.aemeasurable ε
/-
**MeasureTheory.meas_le_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma meas_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : ∀ x ∈ s, 1 ≤ f x) : μ s ≤ ∫⁻ a, f a ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs
/-
**MeasureTheory.lintegral_le_meas** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_le_meas {s : Set α} {f : α -> Real>=0∞} (hf : forall a, f a <= 1
) (h'f : forall a in sᶜ, f a = 0) : ∫⁻ a, f a ∂μ <= μ s
参数：hf : forall a, f a <= 1；h'f : forall a in sᶜ, f a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_indicator_one_le`：lintegral_indicator_one_le (s 
: Set α) : ∫⁻ a, s.indicator 1 a ∂μ <= μ s
-/
lemma lintegral_le_meas {s : Set α} {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) (h'f : ∀ a ∈ sᶜ, f a = 0) :
    ∫⁻ a, f a ∂μ ≤ μ s := by
  apply (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x ∈ s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx
/-
**MeasureTheory.setLIntegral_le_meas** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_le_meas {s t : Set α} (hs : MeasurableSet s) {f : α -> Real>=
0∞} (hf : forall a in s, a in t -> f a <= 1) (hf' : forall a in s, a ∉ t -> f a 
= 0) : ∫⁻ a in s, f a ∂μ <= μ t
参数：hs : MeasurableSet s；hf : forall a in s, a in t -> f a <= 1；hf' : forall a in
 s, a ∉ t -> f a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用引理 `MeasureTheory.lintegral_le_meas`：lintegral_le_meas {s : Set α} {f : α ->
 Real>=0∞} (hf : forall a, f a <= 1) (h'f : forall a in sᶜ, f a = 0) : ∫⁻ a, f a
 ∂μ <= μ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma setLIntegral_le_meas {s t : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, a ∈ t → f a ≤ 1)
    (hf' : ∀ a ∈ s, a ∉ t → f a = 0) : ∫⁻ a in s, f a ∂μ ≤ μ t := by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a ↦ ?_) (by simp_all)
  by_cases has : a ∈ s <;> [by_cases hat : a ∈ t; skip] <;> simp [*]
/-
**MeasureTheory.lintegral_eq_top_of_measure_eq_top_ne_zero** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：lintegral_eq_top_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} (hf : AEMea
surable f μ) (hμf : μ {x | f x = ∞} != 0) : ∫⁻ x, f x ∂μ = ∞
参数：hf : AEMeasurable f μ；hμf : μ {x | f x = ∞} != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.mul_meas_ge_le_lintegral₀`：mul_meas_ge_le_lintegral₀ {f : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= f x } <
= ∫⁻ a, f a ∂μ
-/
theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} ≠ 0) : ∫⁻ x, f x ∂μ = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [hμf]
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞
/-
**MeasureTheory.setLIntegral_eq_top_of_measure_eq_top_ne_zero** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_eq_top_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} {s : Set
 α} (hf : AEMeasurable f (μ.restrict s)) (hμf : μ ({x in s | f x = ∞}) != 0) : ∫
⁻ x in s, f x ∂μ = ∞
参数：hf : AEMeasurable f (μ.restrict s)；hμf : μ ({x in s | f x = ∞}) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_eq_top_of_measure_eq_top_ne_zero`：lintegral_eq_t
op_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hμf : 
μ {x | f x = ∞} != 0) : ∫⁻ x, f x ∂μ = ∞
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_inter_eq_sep`：ofPred_inter_eq_sep (p : α -> Prop) (s : Set α)
 : {a | p a} inter s = {a in s | p a}
· 使用定理 `MeasureTheory.Measure.le_restrict_apply`：le_restrict_apply (s t : Set α)
 : μ (t inter s) <= μ.restrict s t
-/
theorem setLIntegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : μ ({x ∈ s | f x = ∞}) ≠ 0) :
    ∫⁻ x in s, f x ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero hf <|
    mt (eq_bot_mono <| by rw [← ofPred_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf
/-
**MeasureTheory.measure_eq_top_of_lintegral_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：measure_eq_top_of_lintegral_ne_top {f : α -> Real>=0∞} (hf : AEMeasurable 
f μ) (hμf : ∫⁻ x, f x ∂μ != ∞) : μ {x | f x = ∞} = 0
参数：hf : AEMeasurable f μ；hμf : ∫⁻ x, f x ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `MeasureTheory.lintegral_eq_top_of_measure_eq_top_ne_zero`：lintegral_eq_t
op_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hμf : 
μ {x | f x = ∞} != 0) : ∫⁻ x, f x ∂μ = ∞
-/
theorem measure_eq_top_of_lintegral_ne_top {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) : μ {x | f x = ∞} = 0 :=
  of_not_not fun h => hμf <| lintegral_eq_top_of_measure_eq_top_ne_zero hf h
/-
**MeasureTheory.measure_eq_top_of_setLIntegral_ne_top** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：measure_eq_top_of_setLIntegral_ne_top {f : α -> Real>=0∞} {s : Set α} (hf 
: AEMeasurable f (μ.restrict s)) (hμf : ∫⁻ x in s, f x ∂μ != ∞) : μ ({x in s | f
 x = ∞}) = 0
参数：hf : AEMeasurable f (μ.restrict s)；hμf : ∫⁻ x in s, f x ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `MeasureTheory.setLIntegral_eq_top_of_measure_eq_top_ne_zero`：setLIntegra
l_eq_top_of_measure_eq_top_ne_zero {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasu
rable f (μ.restrict s)) (hμf : μ ({x in s | f x =…
-/
theorem measure_eq_top_of_setLIntegral_ne_top {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    μ ({x ∈ s | f x = ∞}) = 0 :=
  of_not_not fun h => hμf <| setLIntegral_eq_top_of_measure_eq_top_ne_zero hf h

/-- **Markov's inequality**, also known as **Chebyshev's first inequality**. -/
/-
**MeasureTheory.meas_ge_le_lintegral_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：meas_ge_le_lintegral_div {f : α -> Real>=0∞} (hf : AEMeasurable f μ) {ε : 
Real>=0∞} (hε : ε != 0) (hε' : ε != ∞) : μ { x | ε <= f x } <= (∫⁻ a, f a ∂μ) / 
ε
参数：hf : AEMeasurable f μ；hε : ε != 0；hε' : ε != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.mul_meas_ge_le_lintegral₀`：mul_meas_ge_le_lintegral₀ {f : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= f x } <
= ∫⁻ a, f a ∂μ

--- 原说明 ---
**Markov's inequality**, also known as **Chebyshev's first inequality**.
-/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <| by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε
/-
**MeasureTheory.ae_eq_of_ae_le_of_lintegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：ae_eq_of_ae_le_of_lintegral_le {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (h
f : ∫⁻ x, f x ∂μ != ∞) (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ <= ∫⁻ x, f x 
∂μ) : f =ᵐ[μ] g
参数：hfg : f <=ᵐ[μ] g；hf : ∫⁻ x, f x ∂μ != ∞；hg : AEMeasurable g μ；hgf : ∫⁻ x, g x
 ∂μ <= ∫⁻ x, f x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral`：lintegral_add_
mul_meas_add_le_le_lintegral {f g : α -> Real>=0∞} (hle : f <=ᵐ[μ] g) (hg : AEMe
asurable g μ) (ε : Real>=0∞) : ∫⁻ a, f a ∂μ + …
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `AddLECancellable.add_le_iff_nonpos_right`：∀ {α : Type u_1} [inst : LE α]
 [inst_1 : AddZeroClass α] [AddLeftMono α] {a b : α},   AddLECancellable a → (a 
+ b ≤ a ↔ b ≤ 0)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
（共 42 条，此处仅展示前 30 条）
-/
theorem ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g := by
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + (n : ℝ≥0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : ℝ≥0∞)⁻¹ ≤ g x } ≤ ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : ℕ => f x + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)
/-
**MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α -> Real>=0∞} (
hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] g) (h : exists
ᵐ x ∂μ, f x != g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ
参数：hg : AEMeasurable g μ；hfi : ∫⁻ x, f x ∂μ != ∞；h_le : f <=ᵐ[μ] g；h : existsᵐ x
 ∂μ, f x != g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_eq_of_ae_le_of_lintegral_le`：ae_eq_of_ae_le_of_lintegra
l_le {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞) (hg : AEM
easurable g μ) (hgf : ∫⁻ x, g x ∂μ…
-/
theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h
/-
**MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_on** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α -> Real>=0∞} (hg : AEM
easurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] g) {s : Set α} (hμs : 
μ s != 0) (h : forallᵐ x ∂μ, x in s -> f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ
参数：hg : AEMeasurable g μ；hfi : ∫⁻ x, f x ∂μ != ∞；h_le : f <=ᵐ[μ] g；hμs : μ s != 
0；h : forallᵐ x ∂μ, x in s -> f x < g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt`：linteg
ral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α -> Real>=0∞} (hg : AEMeasu
rable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] …
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.frequently_ae_mem_iff`：frequently_ae_mem_iff {s : Set α} :
 (existsᵐ a ∂μ, a in s) ↔ μ s != 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) {s : Set α} (hμs : μ s ≠ 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
  lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le <|
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne
/-
**MeasureTheory.lintegral_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_strict_mono {f g : α -> Real>=0∞} (hμ : μ != 0) (hg : AEMeasurab
le g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) (h : forallᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ <
 ∫⁻ x, g x ∂μ
参数：hμ : μ != 0；hg : AEMeasurable g μ；hfi : ∫⁻ x, f x ∂μ != ∞；h : forallᵐ x ∂μ, f
 x < g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_on`：lintegral_stri
ct_mono_of_ae_le_of_ae_lt_on {f g : α -> Real>=0∞} (hg : AEMeasurable g μ) (hfi 
: ∫⁻ x, f x ∂μ != ∞) (h_le : f <=ᵐ[μ] g) {s : …
· 使用定理 `MeasureTheory.ae_le_of_ae_lt`：ae_le_of_ae_lt {β : Type*} [Preorder β] {f
 g : α -> β} (h : forallᵐ x ∂μ, f x < g x) : f <=ᵐ[μ] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  rw [Ne, ← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h
/-
**MeasureTheory.setLIntegral_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLIntegral_strict_mono {f g : α -> Real>=0∞} {s : Set α} (hsm : Measurab
leSet s) (hs : μ s != 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ != ∞) (h :
 forallᵐ x ∂μ, x in s -> f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ
参数：hsm : MeasurableSet s；hs : μ s != 0；hg : Measurable g；hfi : ∫⁻ x in s, f x ∂μ
 != ∞；h : forallᵐ x ∂μ, x in s -> f x < g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_strict_mono`：lintegral_strict_mono {f g : α -> R
eal>=0∞} (hμ : μ != 0) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) (h : fo
rallᵐ x ∂μ, f x < g x) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setLIntegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)
/-
**MeasureTheory.ae_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ
 != ∞) : forallᵐ x ∂μ, f x < ∞
参数：hf : AEMeasurable f μ；h2f : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_eq_top_of_lintegral_ne_top`：measure_eq_top_of_lint
egral_ne_top {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ != 
∞) : μ {x | f x = ∞} = 0
-/
theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f
/-
**MeasureTheory.ae_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ != ∞
) : forallᵐ x ∂μ, f x < ∞
参数：hf : Measurable f；h2f : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_lt_top'`：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem ae_lt_top {f : α → ℝ≥0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  ae_lt_top' hf.aemeasurable h2f

end MeasureTheory

