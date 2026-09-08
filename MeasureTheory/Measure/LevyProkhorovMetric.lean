/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The Lévy-Prokhorov distance on spaces of finite measures and probability measures

## Main definitions

* `MeasureTheory.levyProkhorovEDist`: The Lévy-Prokhorov edistance between two measures.
* `MeasureTheory.levyProkhorovDist`: The Lévy-Prokhorov distance between two finite measures.

## Main results

* `LevyProkhorov.instPseudoMetricSpaceFiniteMeasure`: The Lévy-Prokhorov distance is a
  pseudometric on the space of finite measures.
* `LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure`: The Lévy-Prokhorov distance is a
  pseudometric on the space of probability measures.
* `LevyProkhorov.le_convergenceInDistribution`: The topology of the Lévy-Prokhorov metric on
  probability measures is always at least as fine as the topology of convergence in distribution.
* `LevyProkhorov.eq_convergenceInDistribution`: The topology of the Lévy-Prokhorov metric on
  probability measures on a separable space coincides with the topology of convergence in
  distribution, and in particular convergence in distribution is then pseudometrizable.

## Tags

finite measure, probability measure, weak convergence, convergence in distribution, metrizability
-/

@[expose] public section

open Topology Metric Filter Set ENNReal NNReal

namespace MeasureTheory

open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Levy_Prokhorov

/-! ### Lévy-Prokhorov metric -/

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω]

/-- The Lévy-Prokhorov edistance between measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
/-
**MeasureTheory.levyProkhorovEDist** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：levyProkhorovEDist (μ ν : Measure Ω) : Real>=0∞
参数：μ ν : Measure Ω。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lévy-Prokhorov edistance between measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`.
-/
noncomputable def levyProkhorovEDist (μ ν : Measure Ω) : ℝ≥0∞ :=
  sInf {ε | ∀ B, MeasurableSet B →
            μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε}

/- This result is not placed in earlier more generic files, since it is rather specialized;
it mixes measure and metric in a very particular way. -/
/-
**MeasureTheory.meas_le_of_le_of_forall_le_meas_thickening_add** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory`。
形式化陈述：meas_le_of_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : Real>=0∞} (μ ν : M
easure Ω) (h_le : ε₁ <= ε₂) {B : Set Ω} (hε₁ : μ B <= ν (thickening ε₁.toReal B)
 + ε₁) : μ B <= ν (thickening ε₂.toReal B) + ε₂
参数：μ ν : Measure Ω；h_le : ε₁ <= ε₂；hε₁ : μ B <= ν (thickening ε₁.toReal B) + ε₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Metric.thickening_mono`：thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) 
(E : Set α) : thickening δ₁ E subseteq thickening δ₂ E
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal

--- 原说明 ---
This result is not placed in earlier more generic files, since it is rather spec
ialized;
it mixes measure and metric in a very particular way.
-/
lemma meas_le_of_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : ℝ≥0∞} (μ ν : Measure Ω)
    (h_le : ε₁ ≤ ε₂) {B : Set Ω} (hε₁ : μ B ≤ ν (thickening ε₁.toReal B) + ε₁) :
    μ B ≤ ν (thickening ε₂.toReal B) + ε₂ := by
  by_cases ε_top : ε₂ = ∞
  · simp only [ε_top, toReal_top,
                add_top, le_top]
  apply hε₁.trans (add_le_add ?_ h_le)
  exact measure_mono (μ := ν) (thickening_mono (toReal_mono ε_top h_le) B)
/-
**MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory`。
形式化陈述：left_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : Real>=0∞} 
(h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) : μ B <=
 ν (thickening c.toReal B) + c
参数：h : levyProkhorovEDist μ ν < c；B_mble : MeasurableSet B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sInf_lt_iff`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
 {b : α}, sInf s < b ↔ ∃ a ∈ s, a < b
· 使用引理 `MeasureTheory.meas_le_of_le_of_forall_le_meas_thickening_add`：meas_le_of
_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : Real>=0∞} (μ ν : Measure Ω) (h_le 
: ε₁ <= ε₂) {B : Set Ω} (hε₁ : μ B <= ν (thickenin…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma left_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) :
    μ B ≤ ν (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact meas_le_of_le_of_forall_le_meas_thickening_add μ ν lt_c.le (hc' B B_mble).1
/-
**MeasureTheory.right_measure_le_of_levyProkhorovEDist_lt** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：right_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : Real>=0∞}
 (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) : ν B <
= μ (thickening c.toReal B) + c
参数：h : levyProkhorovEDist μ ν < c；B_mble : MeasurableSet B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sInf_lt_iff`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
 {b : α}, sInf s < b ↔ ∃ a ∈ s, a < b
· 使用引理 `MeasureTheory.meas_le_of_le_of_forall_le_meas_thickening_add`：meas_le_of
_le_of_forall_le_meas_thickening_add {ε₁ ε₂ : Real>=0∞} (μ ν : Measure Ω) (h_le 
: ε₁ <= ε₂) {B : Set Ω} (hε₁ : μ B <= ν (thickenin…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma right_measure_le_of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : ℝ≥0∞}
    (h : levyProkhorovEDist μ ν < c) {B : Set Ω} (B_mble : MeasurableSet B) :
    ν B ≤ μ (thickening c.toReal B) + c := by
  obtain ⟨c', ⟨hc', lt_c⟩⟩ := sInf_lt_iff.mp h
  exact meas_le_of_le_of_forall_le_meas_thickening_add ν μ lt_c.le (hc' B B_mble).2

/-- A general sufficient condition for bounding `levyProkhorovEDist` from above. -/
/-
**MeasureTheory.levyProkhorovEDist_le_of_forall_add_pos_le** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory`。
形式化陈述：levyProkhorovEDist_le_of_forall_add_pos_le (μ ν : Measure Ω) (δ : Real>=0∞
) (h : forall ε B, 0 < ε -> ε < ∞ -> MeasurableSet B -> μ B <= ν (thickening (δ 
+ ε).toReal B) + δ + ε ∧ ν B <= μ (thickening (δ + ε).toReal B) + δ + ε) : levyP
rokhorovEDist μ ν <= δ
参数：μ ν : Measure Ω；δ : Real>=0∞；h : forall ε B, 0 < ε -> ε < ∞ -> MeasurableSet 
B -> μ B <= ν (thickening (δ + ε).toReal B) + δ + ε ∧ ν B <= μ (thickening (δ + 
ε).toReal B) + δ + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤

--- 原说明 ---
A general sufficient condition for bounding `levyProkhorovEDist` from above.
-/
lemma levyProkhorovEDist_le_of_forall_add_pos_le (μ ν : Measure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, 0 < ε → ε < ∞ → MeasurableSet B →
      μ B ≤ ν (thickening (δ + ε).toReal B) + δ + ε ∧
      ν B ≤ μ (thickening (δ + ε).toReal B) + δ + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  by_cases ε_top : ε = ∞
  · simp only [ε_top, add_top, le_top]
  apply sInf_le
  intro B B_mble
  simpa only [add_assoc] using h ε B (by positivity) coe_lt_top B_mble

/-- A simple general sufficient condition for bounding `levyProkhorovEDist` from above. -/
/-
**MeasureTheory.levyProkhorovEDist_le_of_forall** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：levyProkhorovEDist_le_of_forall (μ ν : Measure Ω) (δ : Real>=0∞) (h : fora
ll ε B, δ < ε -> ε < ∞ -> MeasurableSet B -> μ B <= ν (thickening ε.toReal B) + 
ε ∧ ν B <= μ (thickening ε.toReal B) + ε) : levyProkhorovEDist μ ν <= δ
参数：μ ν : Measure Ω；δ : Real>=0∞；h : forall ε B, δ < ε -> ε < ∞ -> MeasurableSet 
B -> μ B <= ν (thickening ε.toReal B) + ε ∧ ν B <= μ (thickening ε.toReal B) + ε
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.levyProkhorovEDist_le_of_forall_add_pos_le`：levyProkhorovE
Dist_le_of_forall_add_pos_le (μ ν : Measure Ω) (δ : Real>=0∞) (h : forall ε B, 0
 < ε -> ε < ∞ -> MeasurableSet B -> μ B <= ν (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A simple general sufficient condition for bounding `levyProkhorovEDist` from abo
ve.
-/
lemma levyProkhorovEDist_le_of_forall (μ ν : Measure Ω) (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B →
        μ B ≤ ν (thickening ε.toReal B) + ε ∧ ν B ≤ μ (thickening ε.toReal B) + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  by_cases δ_top : δ = ∞
  · simp only [δ_top, le_top]
  apply levyProkhorovEDist_le_of_forall_add_pos_le
  intro x B x_pos x_lt_top B_mble
  simpa only [← add_assoc] using h (δ + x) B (ENNReal.lt_add_right δ_top x_pos.ne.symm)
    (by simp only [add_lt_top, Ne.lt_top δ_top, x_lt_top, and_self]) B_mble
/-
**MeasureTheory.levyProkhorovEDist_le_max_measure_univ** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：levyProkhorovEDist_le_max_measure_univ (μ ν : Measure Ω) : levyProkhorovED
ist μ ν <= max (μ univ) (ν univ)
参数：μ ν : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma levyProkhorovEDist_le_max_measure_univ (μ ν : Measure Ω) :
    levyProkhorovEDist μ ν ≤ max (μ univ) (ν univ) := by
  refine sInf_le fun B _ ↦ ⟨?_, ?_⟩ <;> apply le_add_left <;> simp [measure_mono]
/-
**MeasureTheory.levyProkhorovEDist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoEMetricSpace Ω
] (μ ν : MeasureTheory.Measure Ω)   [MeasureTheory.IsFiniteMeasure μ] [MeasureTh
eory.IsFiniteMeasure ν], MeasureTheory.levyProkhorovEDist μ ν < ⊤
参数：μ ν : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.levyProkhorovEDist_le_max_measure_univ`：levyProkhorovEDist
_le_max_measure_univ (μ ν : Measure Ω) : levyProkhorovEDist μ ν <= max (μ univ) 
(ν univ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma levyProkhorovEDist_lt_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν < ∞ :=
  (levyProkhorovEDist_le_max_measure_univ μ ν).trans_lt <| by simp [measure_lt_top]
/-
**MeasureTheory.levyProkhorovEDist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoEMetricSpace Ω
] (μ ν : MeasureTheory.Measure Ω)   [MeasureTheory.IsFiniteMeasure μ] [MeasureTh
eory.IsFiniteMeasure ν], MeasureTheory.levyProkhorovEDist μ ν ≠ ⊤
参数：μ ν : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.levyProkhorovEDist_lt_top`：∀ {Ω : Type u_1} [inst : Measur
ableSpace Ω] [inst_1 : PseudoEMetricSpace Ω] (μ ν : MeasureTheory.Measure Ω)   [
MeasureTheory.IsFiniteMeasure…
-/
@[simp] lemma levyProkhorovEDist_ne_top (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    levyProkhorovEDist μ ν ≠ ∞ := (levyProkhorovEDist_lt_top μ ν).ne
/-
**MeasureTheory.levyProkhorovEDist_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoEMetricSpace Ω
] (μ : MeasureTheory.Measure Ω),   MeasureTheory.levyProkhorovEDist μ μ = 0
参数：μ : MeasureTheory.Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `csInf_Ioo`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a b
 : α} [DenselyOrdered α], b < a → sInf (Set.Ioo b a) = b
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
@[simp] lemma levyProkhorovEDist_self (μ : Measure Ω) : levyProkhorovEDist μ μ = 0 := by
  rw [← nonpos_iff_eq_zero, ← csInf_Ioo zero_lt_top]
  refine sInf_le_sInf fun ε ⟨hε₀, hε_top⟩ B _ ↦ and_self_iff.2 ?_
  refine le_add_right <| measure_mono <| self_subset_thickening ?_ _
  exact ENNReal.toReal_pos hε₀.ne' hε_top.ne
/-
**MeasureTheory.levyProkhorovEDist_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：levyProkhorovEDist_comm (μ ν : Measure Ω) : levyProkhorovEDist μ ν = levyP
rokhorovEDist ν μ
参数：μ ν : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma levyProkhorovEDist_comm (μ ν : Measure Ω) :
    levyProkhorovEDist μ ν = levyProkhorovEDist ν μ := by
  simp only [levyProkhorovEDist, and_comm]
/-
**MeasureTheory.levyProkhorovEDist_triangle** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：levyProkhorovEDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω) :
 levyProkhorovEDist μ κ <= levyProkhorovEDist μ ν + levyProkhorovEDist ν κ
参数：μ ν κ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用引理 `MeasureTheory.levyProkhorovEDist_le_of_forall_add_pos_le`：levyProkhorovE
Dist_le_of_forall_add_pos_le (μ ν : Measure Ω) (δ : Real>=0∞) (h : forall ε B, 0
 < ε -> ε < ∞ -> MeasurableSet B -> μ B <= ν (…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `ENNReal.Finiteness.add_ne_top`：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b 
≠ ⊤
· 使用定理 `ENNReal.div_ne_top`：div_ne_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y != ∞
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt`：left_measure_le_
of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : Real>=0∞} (h : levyProkhorovEDis
t μ ν < c) {B : Set Ω} (B_mble : MeasurableS…
（共 42 条，此处仅展示前 30 条）
-/
lemma levyProkhorovEDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω) :
    levyProkhorovEDist μ κ ≤ levyProkhorovEDist μ ν + levyProkhorovEDist ν κ := by
  by_cases LPμν_finite : levyProkhorovEDist μ ν = ∞
  · simp [LPμν_finite]
  by_cases LPνκ_finite : levyProkhorovEDist ν κ = ∞
  · simp [LPνκ_finite]
  apply levyProkhorovEDist_le_of_forall_add_pos_le
  intro ε B ε_pos ε_lt_top B_mble
  have half_ε_pos : 0 < ε / 2 := ENNReal.div_pos ε_pos.ne' ofNat_ne_top
  let r := levyProkhorovEDist μ ν + ε / 2
  let s := levyProkhorovEDist ν κ + ε / 2
  have lt_r : levyProkhorovEDist μ ν < r := lt_add_right LPμν_finite half_ε_pos.ne'
  have lt_s : levyProkhorovEDist ν κ < s := lt_add_right LPνκ_finite half_ε_pos.ne'
  have hs_add_r : s + r = levyProkhorovEDist μ ν + levyProkhorovEDist ν κ + ε := by
    simp_rw [s, r, add_assoc, add_comm (ε / 2), add_assoc, ENNReal.add_halves, ← add_assoc,
      add_comm (levyProkhorovEDist μ ν)]
  have hs_add_r' : s.toReal + r.toReal
      = (levyProkhorovEDist μ ν + levyProkhorovEDist ν κ + ε).toReal := by
    rw [← hs_add_r, ← ENNReal.toReal_add]
    · finiteness
    · finiteness
  rw [← hs_add_r', add_assoc, ← hs_add_r, add_assoc _ _ ε, ← hs_add_r]
  refine ⟨?_, ?_⟩
  · calc μ B ≤ ν (thickening r.toReal B) + r :=
      left_measure_le_of_levyProkhorovEDist_lt lt_r B_mble
    _ ≤ κ (thickening s.toReal (thickening r.toReal B)) + s + r := by
      grw [left_measure_le_of_levyProkhorovEDist_lt lt_s isOpen_thickening.measurableSet]
    _ = κ (thickening s.toReal (thickening r.toReal B)) + (s + r) := add_assoc _ _ _
    _ ≤ κ (thickening (s.toReal + r.toReal) B) + (s + r) := by grw [thickening_thickening_subset]
  · calc κ B ≤ ν (thickening s.toReal B) + s :=
      right_measure_le_of_levyProkhorovEDist_lt lt_s B_mble
    _ ≤ μ (thickening r.toReal (thickening s.toReal B)) + r + s := by
      grw [right_measure_le_of_levyProkhorovEDist_lt lt_r isOpen_thickening.measurableSet]
    _ = μ (thickening r.toReal (thickening s.toReal B)) + (s + r) := by rw [add_assoc, add_comm r]
    _ ≤ μ (thickening (r.toReal + s.toReal) B) + (s + r) := by grw [thickening_thickening_subset]
    _ = μ (thickening (s.toReal + r.toReal) B) + (s + r) := by rw [add_comm r.toReal]

/-- The Lévy-Prokhorov distance between finite measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`. -/
/-
**MeasureTheory.levyProkhorovDist** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：levyProkhorovDist (μ ν : Measure Ω) : Real
参数：μ ν : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lévy-Prokhorov distance between finite measures:
`d(μ,ν) = inf {r ≥ 0 | ∀ B, μ B ≤ ν Bᵣ + r ∧ ν B ≤ μ Bᵣ + r}`.
-/
noncomputable def levyProkhorovDist (μ ν : Measure Ω) : ℝ :=
  (levyProkhorovEDist μ ν).toReal
/-
**MeasureTheory.levyProkhorovDist_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：levyProkhorovDist_self (μ : Measure Ω) : levyProkhorovDist μ μ = 0
参数：μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.levyProkhorovEDist_self`：∀ {Ω : Type u_1} [inst : Measurab
leSpace Ω] [inst_1 : PseudoEMetricSpace Ω] (μ : MeasureTheory.Measure Ω),   Meas
ureTheory.levyProkhorovEDis…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma levyProkhorovDist_self (μ : Measure Ω) :
    levyProkhorovDist μ μ = 0 := by
  simp only [levyProkhorovDist, levyProkhorovEDist_self, toReal_zero]
/-
**MeasureTheory.levyProkhorovDist_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：levyProkhorovDist_comm (μ ν : Measure Ω) : levyProkhorovDist μ ν = levyPro
khorovDist ν μ
参数：μ ν : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.levyProkhorovEDist_comm`：levyProkhorovEDist_comm (μ ν : Me
asure Ω) : levyProkhorovEDist μ ν = levyProkhorovEDist ν μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma levyProkhorovDist_comm (μ ν : Measure Ω) :
    levyProkhorovDist μ ν = levyProkhorovDist ν μ := by
  simp only [levyProkhorovDist, levyProkhorovEDist_comm]
/-
**MeasureTheory.levyProkhorovDist_triangle** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：levyProkhorovDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω) [I
sFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] : levyProkhorovDist μ 
κ <= levyProkhorovDist μ ν + levyProkhorovDist ν κ
参数：μ ν κ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.levyProkhorovEDist_lt_top`：∀ {Ω : Type u_1} [inst : Measur
ableSpace Ω] [inst_1 : PseudoEMetricSpace Ω] (μ ν : MeasureTheory.Measure Ω)   [
MeasureTheory.IsFiniteMeasure…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用引理 `MeasureTheory.levyProkhorovEDist_triangle`：levyProkhorovEDist_triangle [
OpensMeasurableSpace Ω] (μ ν κ : Measure Ω) : levyProkhorovEDist μ κ <= levyProk
horovEDist μ ν + levyProkhorovE…
-/
lemma levyProkhorovDist_triangle [OpensMeasurableSpace Ω] (μ ν κ : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    levyProkhorovDist μ κ ≤ levyProkhorovDist μ ν + levyProkhorovDist ν κ := by
  have dμν_finite := (levyProkhorovEDist_lt_top μ ν).ne
  have dνκ_finite := (levyProkhorovEDist_lt_top ν κ).ne
  convert! ENNReal.toReal_mono ?_ <| levyProkhorovEDist_triangle μ ν κ
  · simp only [levyProkhorovDist, ENNReal.toReal_add dμν_finite dνκ_finite]
  · exact ENNReal.add_ne_top.mpr ⟨dμν_finite, dνκ_finite⟩

variable [OpensMeasurableSpace Ω]
/-
**MeasureTheory.measure_le_measure_closure_of_levyProkhorovEDist_eq_zero** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_le_measure_closure_of_levyProkhorovEDist_eq_zero {μ ν : Measure Ω}
 (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_mble : MeasurableSet s) (h_fi
nite : exists δ > 0, ν (thickening δ s) != ∞) : μ s <= ν (closure s)
参数：hLP : levyProkhorovEDist μ ν = 0；s_mble : MeasurableSet s；h_finite : exists δ
 > 0, ν (thickening δ s) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用引理 `ENNReal.continuousAt_toReal`：continuousAt_toReal (hx : x != ∞) : Continu
ousAt ENNReal.toReal x
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_measure_thickening`：tendsto_measure_thickening {μ : Measure α} {
s : Set α} (hs : exists R > 0, μ (thickening R s) != ∞) : Tendsto (fun r => μ (t
hickening r s)) …
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
（共 32 条，此处仅展示前 30 条）
-/
lemma measure_le_measure_closure_of_levyProkhorovEDist_eq_zero {μ ν : Measure Ω}
    (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_mble : MeasurableSet s)
    (h_finite : ∃ δ > 0, ν (thickening δ s) ≠ ∞) :
    μ s ≤ ν (closure s) := by
  have key : Tendsto (fun ε ↦ ν (thickening ε.toReal s)) (𝓝[>] (0 : ℝ≥0∞)) (𝓝 (ν (closure s))) := by
    have aux : Tendsto ENNReal.toReal (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (s := Ioi 0) ENNReal.toReal
      · exact tendsto_nhdsWithin_of_tendsto_nhds (continuousAt_toReal zero_ne_top).tendsto
      · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
        exact toReal_pos hx.1.ne' <| ne_top_of_lt hx.2
    exact (tendsto_measure_thickening h_finite).comp aux
  have obs := Tendsto.add key (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  simp only [id_eq, add_zero] at obs
  apply ge_of_tendsto (b := μ s) obs
  filter_upwards [self_mem_nhdsWithin] with ε ε_pos
  exact left_measure_le_of_levyProkhorovEDist_lt (B_mble := s_mble) (hLP ▸ ε_pos)

/-- Two measures at vanishing Lévy-Prokhorov distance from each other assign the same values to all
closed sets. -/
/-
**MeasureTheory.measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed** 是
 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed {μ ν : Measur
e Ω} (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_closed : IsClosed s) (hμs
 : exists δ > 0, μ (thickening δ s) != ∞) (hνs : exists δ > 0, ν (thickening δ s
) != ∞) : μ s = ν s
参数：hLP : levyProkhorovEDist μ ν = 0；s_closed : IsClosed s；hμs : exists δ > 0, μ 
(thickening δ s) != ∞；hνs : exists δ > 0, ν (thickening δ s) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.measure_le_measure_closure_of_levyProkhorovEDist_eq_zero`：
measure_le_measure_closure_of_levyProkhorovEDist_eq_zero {μ ν : Measure Ω} (hLP 
: levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_mble : Measurab…
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `MeasureTheory.levyProkhorovEDist_comm`：levyProkhorovEDist_comm (μ ν : Me
asure Ω) : levyProkhorovEDist μ ν = levyProkhorovEDist ν μ

--- 原说明 ---
Two measures at vanishing Lévy-Prokhorov distance from each other assign the sam
e values to all
closed sets.
-/
lemma measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed {μ ν : Measure Ω}
    (hLP : levyProkhorovEDist μ ν = 0) {s : Set Ω} (s_closed : IsClosed s)
    (hμs : ∃ δ > 0, μ (thickening δ s) ≠ ∞) (hνs : ∃ δ > 0, ν (thickening δ s) ≠ ∞) :
    μ s = ν s := by
  apply le_antisymm
  · exact measure_le_measure_closure_of_levyProkhorovEDist_eq_zero
      hLP s_closed.measurableSet hνs |>.trans <|
      le_of_eq (congr_arg _ s_closed.closure_eq)
  · exact measure_le_measure_closure_of_levyProkhorovEDist_eq_zero
      (levyProkhorovEDist_comm μ ν ▸ hLP) s_closed.measurableSet hμs |>.trans <|
      le_of_eq (congr_arg _ s_closed.closure_eq)

/-- A simple sufficient condition for bounding `levyProkhorovEDist` between probability measures
from above. The condition involves only one of two natural bounds, the other bound is for free. -/
/-
**MeasureTheory.levyProkhorovEDist_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：levyProkhorovEDist_le_of_forall_le (μ ν : Measure Ω) [IsProbabilityMeasure
 μ] [IsProbabilityMeasure ν] (δ : Real>=0∞) (h : forall ε B, δ < ε -> ε < ∞ -> M
easurableSet B -> μ B <= ν (thickening ε.toReal B) + ε) : levyProkhorovEDist μ ν
 <= δ
参数：μ ν : Measure Ω；δ : Real>=0∞；h : forall ε B, δ < ε -> ε < ∞ -> MeasurableSet 
B -> μ B <= ν (thickening ε.toReal B) + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.levyProkhorovEDist_le_of_forall`：levyProkhorovEDist_le_of_
forall (μ ν : Measure Ω) (δ : Real>=0∞) (h : forall ε B, δ < ε -> ε < ∞ -> Measu
rableSet B -> μ B <= ν (thickening …
· 使用引理 `Metric.subset_compl_thickening_compl_thickening_self`：subset_compl_thick
ening_compl_thickening_self (δ : Real) (E : Set α) : E subseteq (thickening δ (t
hickening δ E)ᶜ)ᶜ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.prob_compl_eq_one_sub`：prob_compl_eq_one_sub (hs : Measura
bleSet s) : μ sᶜ = 1 - μ s
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ENNReal.add_sub_cancel_left`：∀ {a b : ENNReal}, a ≠ ⊤ → a + b - a = b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A simple sufficient condition for bounding `levyProkhorovEDist` between probabil
ity measures
from above. The condition involves only one of two natural bounds, the other bou
nd is for free.
-/
lemma levyProkhorovEDist_le_of_forall_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (δ : ℝ≥0∞)
    (h : ∀ ε B, δ < ε → ε < ∞ → MeasurableSet B → μ B ≤ ν (thickening ε.toReal B) + ε) :
    levyProkhorovEDist μ ν ≤ δ := by
  apply levyProkhorovEDist_le_of_forall μ ν δ
  intro ε B ε_gt ε_lt_top B_mble
  refine ⟨h ε B ε_gt ε_lt_top B_mble, ?_⟩
  have B_subset := subset_compl_thickening_compl_thickening_self ε.toReal B
  apply (measure_mono (μ := ν) B_subset).trans
  rw [prob_compl_eq_one_sub isOpen_thickening.measurableSet]
  have Tc_mble := (isOpen_thickening (δ := ε.toReal) (E := B)).isClosed_compl.measurableSet
  specialize h ε (thickening ε.toReal B)ᶜ ε_gt ε_lt_top Tc_mble
  rw [prob_compl_eq_one_sub isOpen_thickening.measurableSet] at h
  have almost := add_le_add (c := μ (thickening ε.toReal B)) h rfl.le
  rw [tsub_add_cancel_of_le prob_le_one, add_assoc] at almost
  apply (tsub_le_tsub_right almost _).trans
  rw [ENNReal.add_sub_cancel_left (measure_ne_top ν _), add_comm ε]

/-- A simple sufficient condition for bounding `levyProkhorovDist` between probability measures
from above. The condition involves only one of two natural bounds, the other bound is for free. -/
/-
**MeasureTheory.levyProkhorovDist_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：levyProkhorovDist_le_of_forall_le (μ ν : Measure Ω) [IsProbabilityMeasure 
μ] [IsProbabilityMeasure ν] {δ : Real} (δ_nn : 0 <= δ) (h : forall ε B, δ < ε ->
 MeasurableSet B -> μ B <= ν (thickening ε B) + ENNReal.ofReal ε) : levyProkhoro
vDist μ ν <= δ
参数：μ ν : Measure Ω；δ_nn : 0 <= δ；h : forall ε B, δ < ε -> MeasurableSet B -> μ B
 <= ν (thickening ε B) + ENNReal.ofReal ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用引理 `MeasureTheory.levyProkhorovEDist_le_of_forall_le`：levyProkhorovEDist_le_
of_forall_le (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 (δ : Real>=0∞) (h : forall ε B, δ < ε…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_toReal_eq_iff`：ofReal_toReal_eq_iff : ENNReal.ofReal a.to
Real = a ↔ a != ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a

--- 原说明 ---
A simple sufficient condition for bounding `levyProkhorovDist` between probabili
ty measures
from above. The condition involves only one of two natural bounds, the other bou
nd is for free.
-/
lemma levyProkhorovDist_le_of_forall_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ} (δ_nn : 0 ≤ δ)
    (h : ∀ ε B, δ < ε → MeasurableSet B → μ B ≤ ν (thickening ε B) + ENNReal.ofReal ε) :
    levyProkhorovDist μ ν ≤ δ := by
  apply toReal_le_of_le_ofReal δ_nn
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B ε_gt ε_lt_top B_mble
  have ε_gt' : δ < ε.toReal := by
    refine (ofReal_lt_ofReal_iff ?_).mp ?_
    · exact ENNReal.toReal_pos ε_gt.bot_lt.ne' ε_lt_top.ne
    · simpa [ofReal_toReal_eq_iff.mpr ε_lt_top.ne] using ε_gt
  convert! h ε.toReal B ε_gt' B_mble
  exact (ENNReal.ofReal_toReal ε_lt_top.ne).symm

/-! ### Equipping measures with the Lévy-Prokhorov metric -/

/-- A type synonym, to be used for `Measure α`, `FiniteMeasure α`, or `ProbabilityMeasure α`,
when they are to be equipped with the Lévy-Prokhorov distance. -/
/-
**MeasureTheory.LevyProkhorov** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
形式化陈述：LevyProkhorov (α : Type*) where /-- Turn a measure into the corresponding 
element of the space of measures equipped with the Lévy-Prokhorov metric. -/ ofM
easure :: /-- Turn an element of the space of measure equipped with the Lévy-Pro
khorov metric into the corresponding measure. -/ toMeasure : α  open Lean.Pretty
Printer.Delaborator in /-- This prevents `ofMeasure x` being printed as `{ toMea
sure
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym, to be used for `Measure α`, `FiniteMeasure α`, or `ProbabilityMe
asure α`,
when they are to be equipped with the Lévy-Prokhorov distance. -/
-/
structure LevyProkhorov (α : Type*) where
  /-- Turn a measure into the corresponding element of the space of measures equipped with the
  Lévy-Prokhorov metric. -/
  ofMeasure ::
  /-- Turn an element of the space of measure equipped with the Lévy-Prokhorov metric into the
  corresponding measure. -/
  toMeasure : α

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `ofMeasure x` being printed as `{ toMeasure := x }` by `delabStructureInstance`.
-/
@[app_delab LevyProkhorov.ofMeasure]
meta def LevyProkhorov.delabOfMeasure : Delab := delabApp

namespace LevyProkhorov

/-
**MeasureTheory.LevyProkhorov.toMeasure_injective** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.LevyProkhorov`。
形式化陈述：toMeasure_injective {α : Type*} : (toMeasure : LevyProkhorov α -> α).Injec
tive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toMeasure_injective {α : Type*} : (toMeasure : LevyProkhorov α → α).Injective :=
  fun ⟨μ⟩ ⟨ν⟩ => by congr!

/-- `LevyProkhorov.toMeasure` as an equiv. -/
@[simps]
/-
**MeasureTheory.LevyProkhorov.toMeasureEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.LevyProkhorov`。
形式化陈述：toMeasureEquiv {α : Type*} : LevyProkhorov α ≃ α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LevyProkhorov.toMeasure` as an equiv.
-/
def toMeasureEquiv {α : Type*} : LevyProkhorov α ≃ α where
  toFun := toMeasure
  invFun := ofMeasure

/-- The Lévy-Prokhorov distance `levyProkhorovEDist` makes `Measure Ω` a pseudoemetric
space. The instance is recorded on the type synonym `LevyProkhorov (Measure Ω) := Measure Ω`. -/
/-
**MeasureTheory.LevyProkhorov.instPseudoEMetricSpaceMeasure** 是 Mathlib 中的一个实例，位
于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：instPseudoEMetricSpaceMeasure : PseudoEMetricSpace (LevyProkhorov (Measure
 Ω)) where edist μ ν
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lévy-Prokhorov distance `levyProkhorovEDist` makes `Measure Ω` a pseudoemetr
ic
space. The instance is recorded on the type synonym `LevyProkhorov (Measure Ω) :
= Measure Ω`.
-/
noncomputable instance instPseudoEMetricSpaceMeasure :
    PseudoEMetricSpace (LevyProkhorov (Measure Ω)) where
  edist μ ν := levyProkhorovEDist μ.toMeasure ν.toMeasure
  edist_self _ := levyProkhorovEDist_self _
  edist_comm _ _ := levyProkhorovEDist_comm ..
  edist_triangle _ _ _ := levyProkhorovEDist_triangle ..

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `FiniteMeasure Ω` a pseudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (FiniteMeasure Ω) := FiniteMeasure Ω`. -/
/-
**MeasureTheory.LevyProkhorov.instPseudoMetricSpaceFiniteMeasure** 是 Mathlib 中的一
个实例，位于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：instPseudoMetricSpaceFiniteMeasure : PseudoMetricSpace (LevyProkhorov (Fin
iteMeasure Ω)) where edist μ ν
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lévy-Prokhorov distance `levyProkhorovDist` makes `FiniteMeasure Ω` a pseudo
metric
space. The instance is recorded on the type synonym
`LevyProkhorov (FiniteMeasure Ω) := FiniteMeasure Ω`.
-/
noncomputable instance instPseudoMetricSpaceFiniteMeasure :
    PseudoMetricSpace (LevyProkhorov (FiniteMeasure Ω)) where
  edist μ ν := levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
  dist μ ν := levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
  dist_self _ := levyProkhorovDist_self _
  dist_comm _ _ := levyProkhorovDist_comm ..
  dist_triangle _ _ _ := levyProkhorovDist_triangle ..
  edist_dist μ ν := by simp [levyProkhorovDist, levyProkhorovEDist_ne_top]

/-- The Lévy-Prokhorov distance `levyProkhorovDist` makes `ProbabilityMeasure Ω` a pseudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this pseudometric to give the topology of convergence in distribution, one must
furthermore assume that `Ω` is separable. -/
/-
**MeasureTheory.LevyProkhorov.instPseudoMetricSpaceProbabilityMeasure** 是 Mathli
b 中的一个实例，位于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：instPseudoMetricSpaceProbabilityMeasure : PseudoMetricSpace (LevyProkhorov
 (ProbabilityMeasure Ω))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lévy-Prokhorov distance `levyProkhorovDist` makes `ProbabilityMeasure Ω` a p
seudometric
space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this pseudometric to give the topology of convergence in distribution,
 one must
furthermore assume that `Ω` is separable.
-/
noncomputable instance instPseudoMetricSpaceProbabilityMeasure :
    PseudoMetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) :=
  .induced (LevyProkhorov.ofMeasure ·.toMeasure.toFiniteMeasure) inferInstance
/-
**MeasureTheory.LevyProkhorov.edist_measure_def** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.LevyProkhorov`。
形式化陈述：edist_measure_def (μ ν : LevyProkhorov (Measure Ω)) : edist μ ν = levyProk
horovEDist μ.toMeasure ν.toMeasure
参数：μ ν : LevyProkhorov (Measure Ω)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_measure_def (μ ν : LevyProkhorov (Measure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure ν.toMeasure := rfl
/-
**MeasureTheory.LevyProkhorov.edist_finiteMeasure_def** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.LevyProkhorov`。
形式化陈述：edist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) : edist μ 
ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
参数：μ ν : LevyProkhorov (FiniteMeasure Ω)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl
/-
**MeasureTheory.LevyProkhorov.dist_finiteMeasure_def** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.LevyProkhorov`。
形式化陈述：dist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) : dist μ ν 
= levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
参数：μ ν : LevyProkhorov (FiniteMeasure Ω)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_finiteMeasure_def (μ ν : LevyProkhorov (FiniteMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl
/-
**MeasureTheory.LevyProkhorov.edist_probabilityMeasure_def** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：edist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) 
: edist μ ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
参数：μ ν : LevyProkhorov (ProbabilityMeasure Ω)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    edist μ ν = levyProkhorovEDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl
/-
**MeasureTheory.LevyProkhorov.dist_probabilityMeasure_def** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：dist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
 dist μ ν = levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure
参数：μ ν : LevyProkhorov (ProbabilityMeasure Ω)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_probabilityMeasure_def (μ ν : LevyProkhorov (ProbabilityMeasure Ω)) :
    dist μ ν = levyProkhorovDist μ.toMeasure.toMeasure ν.toMeasure.toMeasure := rfl

/-- If `Ω` is a Borel space, then the Lévy-Prokhorov distance `levyProkhorovDist` makes
`ProbabilityMeasure Ω` into a metric space. The instance is recorded on the type synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this metric to give the topology of convergence in distribution, one must
furthermore assume that `Ω` is separable. -/
/-
**MeasureTheory.LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure**
 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：levyProkhorovDist_metricSpace_probabilityMeasure [BorelSpace Ω] : MetricSp
ace (LevyProkhorov (ProbabilityMeasure Ω)) where eq_of_dist_eq_zero {μ ν} h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Ω` is a Borel space, then the Lévy-Prokhorov distance `levyProkhorovDist` ma
kes
`ProbabilityMeasure Ω` into a metric space. The instance is recorded on the type
 synonym
`LevyProkhorov (ProbabilityMeasure Ω) := ProbabilityMeasure Ω`.

Note: For this metric to give the topology of convergence in distribution, one m
ust
furthermore assume that `Ω` is separable.
-/
noncomputable instance levyProkhorovDist_metricSpace_probabilityMeasure [BorelSpace Ω] :
    MetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) where
  eq_of_dist_eq_zero {μ ν} h := by
    apply toMeasure_injective
    apply ProbabilityMeasure.toMeasure_injective
    refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun A hA ↦ ?_) (by simp)
    · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]
    refine measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed ?_ hA ?_ ?_
    · simpa [dist_probabilityMeasure_def, levyProkhorovDist, toReal_eq_zero_iff] using h
    · exact ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩
    · exact ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩

end LevyProkhorov
end Levy_Prokhorov --section

section Levy_Prokhorov_is_finer

/-! ### The Lévy-Prokhorov topology is at least as fine as convergence in distribution -/

open BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω]

variable [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- A version of the layer cake formula for bounded continuous functions which have finite integral:
`∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt`. -/
/-
**MeasureTheory.BoundedContinuousFunction.integral_eq_integral_meas_le_of_hasFin
iteIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.BoundedContinuousFunction`。
形式化陈述：∀ {α : Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] 
[OpensMeasurableSpace α]   (f : BoundedContinuousFunction α ℝ) (μ : MeasureTheor
y.Measure α),   0 ≤ᵐ[μ] ⇑f →     MeasureTheory.HasFiniteIntegral (⇑f) μ → ∫ (ω :
 α), f ω ∂μ = ∫ (t : ℝ) in Set.Ioc 0 ‖f‖, μ.real {a | t ≤ f a}
参数：f : BoundedContinuousFunction α ℝ；μ : MeasureTheory.Measure α；⇑f；ω : α；t : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le`：∀ {α : Type u
_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℝ} {M : ℝ}
,   MeasureTheory.Integrable f μ →     0 ≤ᵐ[μ] …
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `BoundedContinuousFunction.apply_le_norm`：apply_le_norm (f : α ->ᵇ Real) 
(x : α) : f x <= ‖f‖

--- 原说明 ---
A version of the layer cake formula for bounded continuous functions which have 
finite integral:
`∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt`.
-/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le_of_hasFiniteIntegral
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) (f_nn : 0 ≤ᵐ[μ] f) (hf : HasFiniteIntegral f μ) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, μ.real {a : α | t ≤ f a} := by
  rw [Integrable.integral_eq_integral_Ioc_meas_le (M := ‖f‖) ?_ f_nn ?_]
  · exact ⟨f.continuous.measurable.aestronglyMeasurable, hf⟩
  · exact Eventually.of_forall (fun x ↦ BoundedContinuousFunction.apply_le_norm f x)

/-- A version of the layer cake formula for bounded continuous functions and finite measures:
`∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt`. -/
/-
**MeasureTheory.BoundedContinuousFunction.integral_eq_integral_meas_le** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.BoundedContinuousFunction`。
形式化陈述：∀ {α : Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] 
[OpensMeasurableSpace α]   (f : BoundedContinuousFunction α ℝ) (μ : MeasureTheor
y.Measure α) [MeasureTheory.IsFiniteMeasure μ],   0 ≤ᵐ[μ] ⇑f → ∫ (ω : α), f ω ∂μ
 = ∫ (t : ℝ) in Set.Ioc 0 ‖f‖, μ.real {a | t ≤ f a}
参数：f : BoundedContinuousFunction α ℝ；μ : MeasureTheory.Measure α；ω : α；t : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.BoundedContinuousFunction.integral_eq_integral_meas_le_of_
hasFiniteIntegral`：∀ {α : Type u_2} [inst : MeasurableSpace α] [inst_1 : Topolog
icalSpace α] [OpensMeasurableSpace α]   (f : BoundedContinuousFunction α ℝ) (μ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ

--- 原说明 ---
A version of the layer cake formula for bounded continuous functions and finite 
measures:
`∫ f dμ = ∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt`.
-/
lemma BoundedContinuousFunction.integral_eq_integral_meas_le
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (f : α →ᵇ ℝ) (μ : Measure α) [IsFiniteMeasure μ] (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 ‖f‖, μ.real {a : α | t ≤ f a} :=
  integral_eq_integral_meas_le_of_hasFiniteIntegral _ _ f_nn (f.integrable μ).2

/-- Assuming `levyProkhorovEDist μ ν < ε`, we can bound `∫ f ∂μ` in terms of
`∫ t in (0, ‖f‖], ν (thickening ε {x | f(x) ≥ t}) dt` and `‖f‖`. -/
/-
**MeasureTheory.BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.BoundedContinuousFunction`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω]
 [OpensMeasurableSpace Ω]   (μ ν : MeasureTheory.Measure Ω) [MeasureTheory.IsFin
iteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] {ε : ℝ},   0 < ε →     MeasureTh
eory.levyProkhorovEDist μ ν < ENNReal.ofReal ε →       ∀ (f : BoundedContinuousF
unction Ω ℝ),         0 ≤ᵐ[μ] ⇑f →           ∫ (ω : Ω), f ω ∂μ ≤ (∫ (t : ℝ) in S
et.Ioc 0 ‖f‖, ν.real (Metric.thickening ε {a | t ≤ f a})) + ε * ‖f‖
参数：μ ν : MeasureTheory.Measure Ω；f : BoundedContinuousFunction Ω ℝ；ω : Ω；∫ (t : 
ℝ) in Set.Ioc 0 ‖f‖, ν.real (Metric.thickening ε {a | t ≤ f a})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.BoundedContinuousFunction.integral_eq_integral_meas_le`：∀ 
{α : Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [OpensMe
asurableSpace α]   (f : BoundedContinuousFunction α ℝ) (μ …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用引理 `MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt`：left_measure_le_
of_levyProkhorovEDist_lt {μ ν : Measure Ω} {c : Real>=0∞} (h : levyProkhorovEDis
t μ ν < c) {B : Set Ω} (B_mble : MeasurableS…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Measure.integrableOn_of_bounded`：∀ {α : Type u_1} {E : Typ
e u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ :
 MeasureTheory.Measure α} {f : α → …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `measure_Ioc_lt_top`：measure_Ioc_lt_top : μ (Ioc a b) < ∞
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
Assuming `levyProkhorovEDist μ ν < ε`, we can bound `∫ f ∂μ` in terms of
`∫ t in (0, ‖f‖], ν (thickening ε {x | f(x) ≥ t}) dt` and `‖f‖`.
-/
lemma BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (ε_pos : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) (f : Ω →ᵇ ℝ) (f_nn : 0 ≤ᵐ[μ] f) :
    ∫ ω, f ω ∂μ
      ≤ (∫ t in Ioc 0 ‖f‖, ν.real (thickening ε {a | t ≤ f a})) + ε * ‖f‖ := by
  rw [BoundedContinuousFunction.integral_eq_integral_meas_le f μ f_nn]
  have key : (fun (t : ℝ) ↦ μ.real {a | t ≤ f a})
              ≤ (fun (t : ℝ) ↦ ν.real (thickening ε {a | t ≤ f a}) + ε) := by
    intro t
    simp only [measureReal_def]
    convert!
      ENNReal.toReal_mono ?_ <|
        left_measure_le_of_levyProkhorovEDist_lt hμν (B := {a | t ≤ f a})
          (f.continuous.measurable measurableSet_Ici)
    · rw [ENNReal.toReal_add (measure_ne_top ν _) ofReal_ne_top, ENNReal.toReal_ofReal ε_pos.le]
    · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, ofReal_ne_top⟩
  have intble₁ : IntegrableOn (fun t ↦ μ.real {a | t ≤ f a}) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := μ.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (subset_univ _)
  have intble₂ : IntegrableOn (fun t ↦ ν.real (thickening ε {a | t ≤ f a})) (Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := ν.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono <| thickening_subset_of_subset ε (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact ENNReal.toReal_mono (by finiteness) <| measure_mono (subset_univ _)
  apply le_trans (setIntegral_mono (s := Ioc 0 ‖f‖) ?_ ?_ key)
  · rw [integral_add]
    · simp [(mul_comm _ ε).le]
    · exact intble₂
    · exact integrable_const ε
  · exact intble₁
  · exact intble₂.add <| integrable_const ε

/-- A monotone decreasing convergence lemma for integrals of measures of thickenings:
`∫ t in (0, ‖f‖], μ (thickening ε {x | f(x) ≥ t}) dt` tends to
`∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt` as `ε → 0`. -/
/-
**MeasureTheory.tendsto_integral_meas_thickening_le** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：tendsto_integral_meas_thickening_le (f : Ω ->ᵇ Real) {A : Set Real} (A_fin
meas : volume A != ∞) (μ : ProbabilityMeasure Ω) : Tendsto (fun ε => ∫ t in A, (
Measure.real μ (thickening ε {a | t <= f a}))) (𝓝[>] (0 : Real)) (𝓝 (∫ t in A, (
Measure.real μ {a | t <= f a})))
参数：f : Ω ->ᵇ Real；A_finmeas : volume A != ∞；μ : ProbabilityMeasure Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ENNReal.measurable_toNNReal`：measurable_toNNReal : Measurable ENNReal.to
NNReal
· 使用定理 `Antitone.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Topological
Space α] {mα : MeasurableSpace α} [BorelSpace α]   [inst_2 : TopologicalSpace β]
 {mβ : Me…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Metric.thickening_subset_of_subset`：thickening_subset_of_subset (δ : Rea
l) {E₁ E₂ : Set α} (h : E₁ subseteq E₂) : thickening δ E₁ subseteq thickening δ 
E₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A monotone decreasing convergence lemma for integrals of measures of thickenings
:
`∫ t in (0, ‖f‖], μ (thickening ε {x | f(x) ≥ t}) dt` tends to
`∫ t in (0, ‖f‖], μ {x | f(x) ≥ t} dt` as `ε → 0`.
-/
lemma tendsto_integral_meas_thickening_le (f : Ω →ᵇ ℝ)
    {A : Set ℝ} (A_finmeas : volume A ≠ ∞) (μ : ProbabilityMeasure Ω) :
    Tendsto (fun ε ↦ ∫ t in A, (Measure.real μ (thickening ε {a | t ≤ f a}))) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in A, (Measure.real μ {a | t ≤ f a}))) := by
  apply tendsto_integral_filter_of_dominated_convergence (G := ℝ) (μ := volume.restrict A)
        (F := fun ε t ↦ (μ (thickening ε {a | t ≤ f a}))) (f := fun t ↦ (μ {a | t ≤ f a})) 1
  · apply Eventually.of_forall fun n ↦ Measurable.aestronglyMeasurable ?_
    simp only [measurable_coe_nnreal_real_iff]
    apply measurable_toNNReal.comp <| Antitone.measurable (fun s t hst ↦ ?_)
    exact measure_mono <| thickening_subset_of_subset _ <| fun ω h ↦ hst.trans h
  · apply Eventually.of_forall (fun i ↦ ?_)
    apply Eventually.of_forall (fun t ↦ ?_)
    simp only [Real.norm_eq_abs, NNReal.abs_eq, Pi.one_apply]
    exact ENNReal.toReal_mono one_ne_top prob_le_one
  · have aux : IsFiniteMeasure (volume.restrict A) := ⟨by simp [lt_top_iff_ne_top, A_finmeas]⟩
    apply integrable_const
  · apply Eventually.of_forall (fun t ↦ ?_)
    simp only [NNReal.tendsto_coe]
    apply (ENNReal.tendsto_toNNReal _).comp
    · apply tendsto_measure_thickening_of_isClosed ?_ ?_
      · exact ⟨1, ⟨Real.zero_lt_one, measure_ne_top _ _⟩⟩
      · exact isClosed_le continuous_const f.continuous
    · finiteness

/-- The identity map `LevyProkhorov (ProbabilityMeasure Ω) → ProbabilityMeasure Ω` is continuous. -/
/-
**MeasureTheory.LevyProkhorov.continuous_toMeasure_probabilityMeasure** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω]
 [inst_2 : OpensMeasurableSpace Ω],   Continuous MeasureTheory.LevyProkhorov.toM
easure
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeqContinuous.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] [SequentialSpace X]   {f : X → Y}, S
eqContinuous f…
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`：te
ndsto_iff_forall_integral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Probabil
ityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (𝓝…
· 使用引理 `BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_
integral`：tendsto_integral_of_forall_limsup_integral_le_integral {ι : Type*} {L 
: Filter ι} {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measur…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 184 条，此处仅展示前 30 条）

--- 原说明 ---
The identity map `LevyProkhorov (ProbabilityMeasure Ω) → ProbabilityMeasure Ω` i
s continuous.
-/
lemma LevyProkhorov.continuous_toMeasure_probabilityMeasure :
    Continuous (toMeasure (α := ProbabilityMeasure Ω)) := by
  refine SeqContinuous.continuous ?_
  intro μs ν hμs
  set P := ν.toMeasure -- more palatable notation
  set Ps := LevyProkhorov.toMeasure ∘ μs -- more palatable notation
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine fun f ↦ tendsto_integral_of_forall_limsup_integral_le_integral ?_ f
  intro f f_nn
  by_cases f_zero : ‖f‖ = 0
  · simp only [norm_eq_zero] at f_zero
    simp [f_zero, limsup_const]
  have norm_f_pos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (fun a => f_zero a.symm)
  apply _root_.le_of_forall_pos_le_add
  intro δ δ_pos
  apply limsup_le_of_le ?_
  · obtain ⟨εs, _, εs_pos, εs_lim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
    have ε_of_room := Tendsto.add (tendsto_iff_dist_tendsto_zero.mp hμs) εs_lim
    have ε_of_room' : Tendsto (fun n ↦ dist (μs n) ν + εs n) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa using ε_of_room, Eventually.of_forall fun n ↦ ?_⟩
      · rw [mem_Ioi]
        linarith [εs_pos n, dist_nonneg (x := μs n) (y := ν)]
    rw [add_zero] at ε_of_room
    have key := (tendsto_integral_meas_thickening_le f (A := Ioc 0 ‖f‖) (by simp) P).comp ε_of_room'
    have aux : ∀ (z : ℝ), Iio (z + δ / 2) ∈ 𝓝 z := fun z ↦ Iio_mem_nhds (by linarith)
    filter_upwards [key (aux _), ε_of_room <| Iio_mem_nhds <| half_pos <|
                      mul_pos (inv_pos.mpr norm_f_pos) δ_pos]
      with n hn hn'
    simp only [mem_preimage, Function.comp_def, mem_Iio] at *
    specialize εs_pos n
    have bound := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt
                    (Ps n) P (ε := dist (μs n) ν + εs n) ?_ ?_ f ?_
    · grw [bound, hn, BoundedContinuousFunction.integral_eq_integral_meas_le _ _ <| .of_forall f_nn,
        add_assoc, mul_comm]
      gcongr
      calc
        δ / 2 + ‖f‖ * (dist (μs n) ν + εs n)
        _ ≤ δ / 2 + ‖f‖ * (‖f‖⁻¹ * δ / 2) := by gcongr
        _ = δ := by field
    · positivity
    · rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_zero (levyProkhorovEDist _ _)]
      apply ENNReal.add_lt_add_of_le_of_lt (levyProkhorovEDist_ne_top _ _)
            (le_of_eq ?_) (ofReal_pos.mpr εs_pos)
      rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist,
        ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
      rfl
    · exact Eventually.of_forall f_nn
  · simp only [IsCoboundedUnder, IsCobounded, eventually_map, eventually_atTop,
               forall_exists_index]
    refine ⟨0, fun a i hia ↦ le_trans (integral_nonneg f_nn) (hia i le_rfl)⟩

/-- The topology of the Lévy-Prokhorov metric is at least as fine as the topology of convergence in
distribution. -/
/-
**MeasureTheory.LevyProkhorov.le_convergenceInDistribution** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω]
 [inst_2 : OpensMeasurableSpace Ω],   TopologicalSpace.coinduced MeasureTheory.L
evyProkhorov.toMeasure inferInstance ≤ inferInstance
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.coinduced_le`：Continuous.coinduced_le (h : Continuous[t, t'] 
f) : t.coinduced f <= t'
· 使用定理 `MeasureTheory.LevyProkhorov.continuous_toMeasure_probabilityMeasure`：∀ {
Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω] [inst_2 
: OpensMeasurableSpace Ω],   Continuous MeasureTheory.Lev…

--- 原说明 ---
The topology of the Lévy-Prokhorov metric is at least as fine as the topology of
 convergence in
distribution.
-/
theorem LevyProkhorov.le_convergenceInDistribution :
    TopologicalSpace.coinduced (LevyProkhorov.toMeasure (α := ProbabilityMeasure Ω)) inferInstance
      ≤ (inferInstance : TopologicalSpace (ProbabilityMeasure Ω)) :=
  LevyProkhorov.continuous_toMeasure_probabilityMeasure.coinduced_le

end Levy_Prokhorov_is_finer

section Levy_Prokhorov_metrizes_convergence_in_distribution

/-! ### On separable spaces the Lévy-Prokhorov distance metrizes convergence in distribution -/

open TopologicalSpace

variable {Ω : Type*} [PseudoMetricSpace Ω]
variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-
**MeasureTheory.ProbabilityMeasure.toMeasure_add_pos_gt_mem_nhds** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.ProbabilityMeasure`。
形式化陈述：∀ {Ω : Type u_1} [inst : PseudoMetricSpace Ω] [inst_1 : MeasurableSpace Ω]
 [inst_2 : OpensMeasurableSpace Ω]   (P : MeasureTheory.ProbabilityMeasure Ω) {G
 : Set Ω},   IsOpen G → ∀ {ε : ENNReal}, 0 < ε → {Q | ↑P G < ↑Q G + ε} ∈ nhds P
参数：P : MeasureTheory.ProbabilityMeasure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.ProbabilityMeasure.instIsProbabilityMeasureToMeasure`：∀ {Ω
 : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.ProbabilityMeasure Ω)
,   MeasureTheory.IsProbabilityMeasure ↑μ
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`：∀ {Ω
 : Type u_1} {ι : Type u_2} {L : Filter ι} [inst : MeasurableSpace Ω] [inst_1 : 
TopologicalSpace Ω]   [inst_2 : OpensMeasurableSpace Ω] …
· 使用定理 `instHasOuterApproxClosedOfPseudoMetrizableSpace`：∀ (X : Type u_1) [inst 
: TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], HasOuterApprox
Closed X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.gt_mem_sets_of_limsInf_gt`：gt_mem_sets_of_limsInf_gt : f.IsBounde
d (· >= ·) -> b < f.limsInf -> forallᶠ a in f, b < a
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
（共 32 条，此处仅展示前 30 条）
-/
lemma ProbabilityMeasure.toMeasure_add_pos_gt_mem_nhds (P : ProbabilityMeasure Ω)
    {G : Set Ω} (G_open : IsOpen G) {ε : ℝ≥0∞} (ε_pos : 0 < ε) :
    {Q | P.toMeasure G < Q.toMeasure G + ε} ∈ 𝓝 P := by
  by_cases! easy : P.toMeasure G < ε
  · exact Eventually.of_forall (fun _ ↦ lt_of_lt_of_le easy le_add_self)
  by_cases ε_top : ε = ∞
  · simp [ε_top, measure_lt_top]
  have aux : P.toMeasure G - ε < liminf (fun Q ↦ Q.toMeasure G) (𝓝 P) := by
    apply lt_of_lt_of_le (ENNReal.sub_lt_self (by finiteness) _ _)
        <| ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id G_open
    · exact (lt_of_lt_of_le ε_pos easy).ne.symm
    · exact ε_pos.ne.symm
  filter_upwards [gt_mem_sets_of_limsInf_gt (α := ℝ≥0∞) isBounded_ge_of_bot
      (show P.toMeasure G - ε < limsInf ((𝓝 P).map (fun Q ↦ Q.toMeasure G)) from aux)] with Q hQ
  simp only [preimage_ofPred_eq, mem_ofPred_eq] at hQ
  convert! ENNReal.add_lt_add_right ε_top hQ
  exact (tsub_add_cancel_of_le easy).symm

variable [SeparableSpace Ω]

variable (Ω) in
/-- In a separable pseudometric space, for any ε > 0 there exists a countable collection of
disjoint Borel measurable subsets of diameter at most ε that cover the whole space. -/
/-
**MeasureTheory.SeparableSpace.exists_measurable_partition_diam_le** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.SeparableSpace`。
形式化陈述：∀ (Ω : Type u_1) [inst : PseudoMetricSpace Ω] [inst_1 : MeasurableSpace Ω]
 [OpensMeasurableSpace Ω]   [TopologicalSpace.SeparableSpace Ω] {ε : ℝ},   0 < ε
 →     ∃ As,       (∀ (n : ℕ), MeasurableSet (As n)) ∧         (∀ (n : ℕ), Borno
logy.IsBounded (As n)) ∧           (∀ (n : ℕ), Metric.diam (As n) ≤ ε) ∧ ⋃ n, As
 n = Set.univ ∧ Pairwise fun n m => Disjoint (As n) (As m)
参数：Ω : Type u_1；∀ (n : ℕ), MeasurableSet (As n)；∀ (n : ℕ), Bornology.IsBounded (
As n)；∀ (n : ℕ), Metric.diam (As n) ≤ ε；As n；As m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Bornology.isBounded_empty`：isBounded_empty : IsBounded (∅ : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.diam_empty`：diam_empty : diam (∅ : Set α) = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `disjoint_of_subsingleton`：disjoint_of_subsingleton [Subsingleton α] : Di
sjoint a b
· 使用定理 `TopologicalSpace.exists_dense_seq`：exists_dense_seq [SeparableSpace α] [
Nonempty α] : exists u : Nat -> α, DenseRange u
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
In a separable pseudometric space, for any ε > 0 there exists a countable collec
tion of
disjoint Borel measurable subsets of diameter at most ε that cover the whole spa
ce.
-/
lemma SeparableSpace.exists_measurable_partition_diam_le {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (As : ℕ → Set Ω), (∀ n, MeasurableSet (As n)) ∧ (∀ n, Bornology.IsBounded (As n)) ∧
        (∀ n, diam (As n) ≤ ε) ∧ (⋃ n, As n = univ) ∧
        (Pairwise (fun (n m : ℕ) ↦ Disjoint (As n) (As m))) := by
  cases isEmpty_or_nonempty Ω
  · refine ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ ↦ Bornology.isBounded_empty, ?_, ?_,
            fun _ _ _ ↦ disjoint_of_subsingleton⟩
    · intro n
      simpa only [diam_empty] using ε_pos.le
    · subsingleton
  obtain ⟨xs, xs_dense⟩ := exists_dense_seq Ω
  have half_ε_pos : 0 < ε / 2 := half_pos ε_pos
  set Bs := fun n ↦ Metric.ball (xs n) (ε / 2)
  set As := disjointed Bs
  refine ⟨As, ?_, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.disjointed (fun n ↦ measurableSet_ball)
  · exact fun n ↦ Bornology.IsBounded.subset isBounded_ball <| disjointed_subset Bs n
  · intro n
    apply (diam_mono (disjointed_subset Bs n) isBounded_ball).trans
    convert! diam_ball half_ε_pos.le
    ring
  · have aux : ⋃ n, Bs n = univ := by
      convert! DenseRange.iUnion_uniformity_ball xs_dense <| Metric.dist_mem_uniformity half_ε_pos
      exact (ball_eq_ball' _ _).symm
    simpa only [← aux] using iUnion_disjointed
  · exact disjoint_disjointed Bs

namespace LevyProkhorov

/-
**MeasureTheory.LevyProkhorov.continuous_ofMeasure_probabilityMeasure** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：continuous_ofMeasure_probabilityMeasure : Continuous (ofMeasure (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Metric.continuousAt_iff'`：continuousAt_iff' [TopologicalSpace β] {f : β 
-> α} {b : β} : ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, dist (f x) (f
 b) < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 131 条，此处仅展示前 30 条）
-/
lemma continuous_ofMeasure_probabilityMeasure :
    Continuous (ofMeasure (α := ProbabilityMeasure Ω)) := by
  -- We check continuity of `id : ProbabilityMeasure Ω → LevyProkhorov (ProbabilityMeasure Ω)` at
  -- each point `P : ProbabilityMeasure Ω`.
  rw [continuous_iff_continuousAt]
  intro P
  -- To check continuity, fix `ε > 0`. To leave some wiggle room, be ready to use `ε/3 > 0` instead.
  rw [continuousAt_iff']
  intro ε ε_pos
  have third_ε_pos : 0 < ε / 3 := by linarith
  have third_ε_pos' : 0 < ENNReal.ofReal (ε / 3) := ofReal_pos.mpr third_ε_pos
  -- First use separability to choose a countable partition of `Ω` into measurable
  -- subsets `Es n ⊆ Ω` of small diameter, `diam (Es n) < ε/3`.
  obtain ⟨Es, Es_mble, Es_bdd, Es_diam, Es_cover, Es_disjoint⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le Ω third_ε_pos
  -- Instead of the whole space `Ω = ⋃ n ∈ ℕ, Es n`, focus on a large but finite
  -- union `⋃ n < N, Es n`, chosen in such a way that the complement has small `P`-mass,
  -- `P (⋃ n < N, Es n)ᶜ < ε/3`.
  obtain ⟨N, hN⟩ : ∃ N, P.toMeasure (⋃ j ∈ Iio N, Es j)ᶜ < ENNReal.ofReal (ε / 3) := by
    have exhaust := @tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint Ω _ P.toMeasure _
                    Es (fun n ↦ (Es_mble n).nullMeasurableSet) Es_disjoint
    simp only [tendsto_atTop_nhds, Function.comp_apply] at exhaust
    obtain ⟨N, hN⟩ := exhaust (Iio (ENNReal.ofReal (ε / 3))) third_ε_pos' isOpen_Iio
    refine ⟨N, ?_⟩
    have rewr : ⋃ i, ⋃ (_ : N ≤ i), Es i = (⋃ i, ⋃ (_ : i < N), Es i)ᶜ := by
      simpa only [mem_Iio, compl_Iio, mem_Ici] using
        (biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ Es_cover Es_disjoint (Iio N)).symm
    simpa only [mem_Iio, ← rewr, gt_iff_lt] using hN N le_rfl
  -- With the finite `N` fixed above, consider the finite collection of open sets of the form
  -- `Gs J = thickening (ε/3) (⋃ j ∈ J, Es j)`, where `J ⊆ {0, 1, ..., N-1}`.
  have Js_finite : Set.Finite {J | J ⊆ Iio N} := Finite.finite_subsets <| finite_Iio N
  set Gs := (fun (J : Set ℕ) ↦ thickening (ε / 3) (⋃ j ∈ J, Es j)) '' {J | J ⊆ Iio N}
  have Gs_open : ∀ (J : Set ℕ), IsOpen (thickening (ε / 3) (⋃ j ∈ J, Es j)) :=
    fun J ↦ isOpen_thickening
  -- Any open set `G ⊆ Ω` determines a neighborhood of `P` consisting of those `Q` that
  -- satisfy `P G < Q G + ε/3`.
  have mem_nhds_P (G : Set Ω) (G_open : IsOpen G) :
      {Q | P.toMeasure G < Q.toMeasure G + ENNReal.ofReal (ε/3)} ∈ 𝓝 P :=
    P.toMeasure_add_pos_gt_mem_nhds G_open third_ε_pos'
  -- Assume that `Q` is in the neighborhood of `P` such that for each `J ⊆ {0, 1, ..., N-1}`
  -- we have `P (Gs J) < Q (Gs J) + ε/3`.
  filter_upwards [(Finset.iInter_mem_sets Js_finite.toFinset).mpr <|
                    fun J _ ↦ mem_nhds_P _ (Gs_open J)] with Q hQ
  simp only [Finite.mem_toFinset, mem_ofPred_eq, thickening_iUnion, mem_iInter] at hQ
  -- Note that in order to show that the Lévy-Prokhorov distance between `P` and `Q` is small
  -- (`≤ 2*ε/3`), it suffices to show that for arbitrary subsets `B ⊆ Ω`, the measure `P B` is
  -- bounded above up to a small error by the `Q`-measure of a small thickening of `B`.
  apply lt_of_le_of_lt ?_ (show 2 * (ε / 3) < ε by linarith)
  rw [dist_comm, dist_probabilityMeasure_def]
  -- Fix an arbitrary set `B ⊆ Ω`, and an arbitrary `δ > 2*ε/3` to gain some room for error
  -- and for thickening.
  apply levyProkhorovDist_le_of_forall_le _ _ (by linarith) (fun δ B δ_gt _ ↦ ?_)
  -- Let `JB ⊆ {0, 1, ..., N-1}` consist of those indices `j` such that `B` intersects `Es j`.
  -- Then the open set `Gs JB` approximates `B` rather well:
  -- except for what happens in the small complement `(⋃ n < N, Es n)ᶜ`, the set `B` is
  -- contained in `Gs JB`, and conversely `Gs JB` only contains points within `δ` from `B`.
  set JB := {i | (B ∩ Es i).Nonempty ∧ i ∈ Iio N}
  have B_subset : B ⊆ (⋃ i ∈ JB, thickening (ε / 3) (Es i)) ∪ (⋃ j ∈ Iio N, Es j)ᶜ := by
    suffices B ⊆ (⋃ i ∈ JB, thickening (ε / 3) (Es i)) ∪ (⋃ j ∈ Ici N, Es j) by
      refine this.trans <| union_subset_union le_rfl ?_
      intro ω hω
      simp only [mem_Ici, mem_iUnion, exists_prop] at hω
      obtain ⟨i, i_large, ω_in_Esi⟩ := hω
      by_contra con
      simp only [mem_Iio, compl_iUnion, mem_iInter, mem_compl_iff, not_forall, not_not,
                  exists_prop] at con
      obtain ⟨j, j_small, ω_in_Esj⟩ := con
      exact disjoint_left.mp (Es_disjoint (show j ≠ i by lia)) ω_in_Esj ω_in_Esi
    intro ω ω_in_B
    obtain ⟨i, hi⟩ := show ∃ n, ω ∈ Es n by simp only [← mem_iUnion, Es_cover, mem_univ]
    simp only [mem_Ici, mem_union, mem_iUnion, exists_prop]
    by_cases i_small : i ∈ Iio N
    · refine Or.inl ⟨i, ?_, self_subset_thickening third_ε_pos _ hi⟩
      simp only [mem_Iio, mem_ofPred_eq, JB]
      exact ⟨Set.nonempty_of_mem <| mem_inter ω_in_B hi, i_small⟩
    · exact Or.inr ⟨i, by simpa only [mem_Iio, not_lt] using i_small, hi⟩
  have subset_thickB : ⋃ i ∈ JB, thickening (ε / 3) (Es i) ⊆ thickening δ B := by
    intro ω ω_in_U
    simp only [mem_iUnion, exists_prop] at ω_in_U
    obtain ⟨k, ⟨B_intersects, _⟩, ω_in_thEk⟩ := ω_in_U
    rw [mem_thickening_iff] at ω_in_thEk ⊢
    obtain ⟨w, w_in_Ek, w_near⟩ := ω_in_thEk
    obtain ⟨z, ⟨z_in_B, z_in_Ek⟩⟩ := B_intersects
    refine ⟨z, z_in_B, lt_of_le_of_lt (dist_triangle ω w z) ?_⟩
    apply lt_of_le_of_lt (add_le_add w_near.le <|
            (dist_le_diam_of_mem (Es_bdd k) w_in_Ek z_in_Ek).trans <| Es_diam k)
    linarith
  -- We use the resulting upper bound `P B ≤ P (Gs JB) + P (small complement)`.
  apply (measure_mono B_subset).trans ((measure_union_le _ _).trans ?_)
  -- From the choice of `Q` in a suitable neighborhood, we have `P (Gs JB) < Q (Gs JB) + ε/3`.
  specialize hQ _ (show JB ⊆ Iio N from fun _ h ↦ h.2)
  -- Now it remains to add the pieces and use the above estimates.
  apply (add_le_add hQ.le hN.le).trans
  rw [add_assoc, ← ENNReal.ofReal_add third_ε_pos.le third_ε_pos.le, ← two_mul]
  apply add_le_add (measure_mono subset_thickB) (ofReal_le_ofReal _)
  exact δ_gt.le

/-- The topology of the Lévy-Prokhorov metric on probability measures on a separable space
coincides with the topology of convergence in distribution. -/
/-
**MeasureTheory.LevyProkhorov.eq_convergenceInDistribution** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：eq_convergenceInDistribution : (inferInstance : TopologicalSpace (Probabil
ityMeasure Ω)) = TopologicalSpace.coinduced LevyProkhorov.toMeasure inferInstanc
e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `MeasureTheory.LevyProkhorov.le_convergenceInDistribution`：∀ {Ω : Type u_
1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω] [inst_2 : OpensMeas
urableSpace Ω],   TopologicalSpace.coinduced M…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用引理 `MeasureTheory.LevyProkhorov.continuous_ofMeasure_probabilityMeasure`：con
tinuous_ofMeasure_probabilityMeasure : Continuous (ofMeasure (α

--- 原说明 ---
The topology of the Lévy-Prokhorov metric on probability measures on a separable
 space
coincides with the topology of convergence in distribution.
-/
theorem eq_convergenceInDistribution :
    (inferInstance : TopologicalSpace (ProbabilityMeasure Ω))
      = TopologicalSpace.coinduced LevyProkhorov.toMeasure inferInstance :=
  le_convergenceInDistribution.antisymm' fun s hs ↦ by
    simpa using! hs.preimage continuous_ofMeasure_probabilityMeasure

/-- The identity map is a homeomorphism from `ProbabilityMeasure Ω` with the topology of
convergence in distribution to `ProbabilityMeasure Ω` with the Lévy-Prokhorov (pseudo)metric. -/
/-
**MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph** 是 Mathlib 中的一个定义，位于
命名空间 `MeasureTheory.LevyProkhorov`。
形式化陈述：probabilityMeasureHomeomorph : ProbabilityMeasure Ω ≃ₜ LevyProkhorov (Prob
abilityMeasure Ω) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.LevyProkhorov.continuous_ofMeasure_probabilityMeasure`：con
tinuous_ofMeasure_probabilityMeasure : Continuous (ofMeasure (α
· 使用定理 `MeasureTheory.LevyProkhorov.continuous_toMeasure_probabilityMeasure`：∀ {
Ω : Type u_1} [inst : MeasurableSpace Ω] [inst_1 : PseudoMetricSpace Ω] [inst_2 
: OpensMeasurableSpace Ω],   Continuous MeasureTheory.Lev…

--- 原说明 ---
The identity map is a homeomorphism from `ProbabilityMeasure Ω` with the topolog
y of
convergence in distribution to `ProbabilityMeasure Ω` with the Lévy-Prokhorov (p
seudo)metric.
-/
noncomputable def probabilityMeasureHomeomorph :
    ProbabilityMeasure Ω ≃ₜ LevyProkhorov (ProbabilityMeasure Ω) where
  toFun := LevyProkhorov.ofMeasure
  invFun := LevyProkhorov.toMeasure
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := LevyProkhorov.continuous_ofMeasure_probabilityMeasure
  continuous_invFun := LevyProkhorov.continuous_toMeasure_probabilityMeasure

end LevyProkhorov

/-- The topology of convergence in distribution on a separable space is pseudo-metrizable. -/
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology of convergence in distribution on a separable space is pseudo-metri
zable.
-/
instance (X : Type*) [TopologicalSpace X] [PseudoMetrizableSpace X] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] :
    PseudoMetrizableSpace (ProbabilityMeasure X) :=
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  (LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)).isInducing.pseudoMetrizableSpace

/-- The topology of convergence in distribution on a separable Borel space is metrizable. -/
/-
**MeasureTheory.instMetrizableSpaceProbabilityMeasure** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory`。
形式化陈述：instMetrizableSpaceProbabilityMeasure (X : Type*) [TopologicalSpace X] [Ps
eudoMetrizableSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] : M
etrizableSpace (ProbabilityMeasure X)
参数：X : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.metrizableSpace`：∀ {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [TopologicalSpace.Metr
izableSpace Y] {f : X → Y}…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
The topology of convergence in distribution on a separable Borel space is metriz
able.
-/
instance instMetrizableSpaceProbabilityMeasure (X : Type*) [TopologicalSpace X]
    [PseudoMetrizableSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] :
    MetrizableSpace (ProbabilityMeasure X) := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact LevyProkhorov.probabilityMeasureHomeomorph.isEmbedding.metrizableSpace

end Levy_Prokhorov_metrizes_convergence_in_distribution

end MeasureTheory -- namespace

