/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
/-!
# Equivalence of variation definitions for signed measures

For a `SignedMeasure`, two definitions of variation are available:
* the supremum-based `VectorMeasure.variation`,
* the Hahn–Jordan-based `SignedMeasure.totalVariation`.

In this file the two notions are shown to coincide.

## Main results

* `MeasureTheory.SignedMeasure.totalVariation_eq_variation`: `μ.totalVariation = μ.variation`.

-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory.SignedMeasure

variable {X : Type*} {mX : MeasurableSpace X} (μ : SignedMeasure X)

/-- The pointwise bound `‖s i‖ ≤ s.totalVariation.real i` for any signed measure. -/
/-
**MeasureTheory.SignedMeasure.norm_le_totalVariation** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SignedMeasure`。
形式化陈述：norm_le_totalVariation (s : SignedMeasure X) (i : Set X) : ‖s i‖ <= s.tota
lVariation.real i
参数：s : SignedMeasure X；i : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.apply_eq_posPart_real_sub_negPart_real`：appl
y_eq_posPart_real_sub_negPart_real (s : SignedMeasure α) {i : Set α} (hi : Measu
rableSet i) : s i = s.toJordanDecomposition.posPart.real…
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.JordanDecomposition.posPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.posPart
· 使用定理 `MeasureTheory.JordanDecomposition.negPart_finite`：∀ {α : Type u_2} [inst
 : MeasurableSpace α] (self : MeasureTheory.JordanDecomposition α),   MeasureThe
ory.IsFiniteMeasure self.negPart
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0

--- 原说明 ---
The pointwise bound `‖s i‖ ≤ s.totalVariation.real i` for any signed measure.
-/
theorem norm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ ≤ s.totalVariation.real i := by
  by_cases hi : MeasurableSet i
  · rw [s.apply_eq_posPart_real_sub_negPart_real hi, totalVariation, measureReal_add_apply]
    grind [measureReal_nonneg, Real.norm_eq_abs]
  · simp [hi]

/-- The pointwise bound `‖s i‖ₑ ≤ s.totalVariation i` for any signed measure. -/
/-
**MeasureTheory.SignedMeasure.enorm_le_totalVariation** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SignedMeasure`。
形式化陈述：enorm_le_totalVariation (s : SignedMeasure X) (i : Set X) : ‖s i‖ₑ <= s.to
talVariation i
参数：s : SignedMeasure X；i : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `MeasureTheory.SignedMeasure.norm_le_totalVariation`：norm_le_totalVariati
on (s : SignedMeasure X) (i : Set X) : ‖s i‖ <= s.totalVariation.real i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.SignedMeasure.instIsFiniteMeasureTotalVariation`：∀ {α : Ty
pe u_1} [inst : MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   Measur
eTheory.IsFiniteMeasure s.totalVariation

--- 原说明 ---
The pointwise bound `‖s i‖ₑ ≤ s.totalVariation i` for any signed measure.
-/
theorem enorm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ₑ ≤ s.totalVariation i := calc
  _ = ENNReal.ofReal ‖s i‖ := (ofReal_norm _).symm
  _ ≤ ENNReal.ofReal (s.totalVariation.real i) :=
    ENNReal.ofReal_le_ofReal (s.norm_le_totalVariation i)
  _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
/-
**MeasureTheory.SignedMeasure.toMeasureOfZeroLE_apply_eq_enorm** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma toMeasureOfZeroLE_apply_eq_enorm {i j : Set X} (him : MeasurableSet i) (hi : 0 ≤[i] μ)
    (hjm : MeasurableSet j) : μ.toMeasureOfZeroLE i him hi j = ‖μ (i ∩ j)‖ₑ := by
  have : 0 ≤ μ (i ∩ j) :=
    μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset ‹_› Set.inter_subset_left ‹_›)
  rw [Real.enorm_of_nonneg this, μ.toMeasureOfZeroLE_apply hi him hjm, ENNReal.ofReal_eq_coe_nnreal]
/-
**MeasureTheory.SignedMeasure.toMeasureOfLEZero_apply_eq_enorm** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma toMeasureOfLEZero_apply_eq_enorm {i j : Set X} (him : MeasurableSet i)
    (hi : μ ≤[i] 0) (hjm : MeasurableSet j) :
    μ.toMeasureOfLEZero i him hi j = ‖μ (i ∩ j)‖ₑ := by
  have : μ (i ∩ j) ≤ 0 :=
    μ.nonpos_of_restrict_le_zero (μ.restrict_le_zero_subset ‹_› Set.inter_subset_left ‹_›)
  rw [← enorm_neg, Real.enorm_of_nonneg (neg_nonneg.mpr this), μ.toMeasureOfLEZero_apply hi him hjm,
    ENNReal.ofReal_eq_coe_nnreal]

/-- The Hahn–Jordan-based `totalVariation` agrees with the supremum-based `variation`. -/
/-
**MeasureTheory.SignedMeasure.totalVariation_eq_variation** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：totalVariation_eq_variation (μ : SignedMeasure X) : μ.totalVariation = μ.v
ariation
参数：μ : SignedMeasure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.SignedMeasure.toJordanDecomposition_spec`：toJordanDecompos
ition_spec (s : SignedMeasure α) : exists (i : Set α) (hi₁ : MeasurableSet i) (h
i₂ : 0 <=[i] s) (hi₃ : s <=[iᶜ] 0), s.toJord…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SignedMeasure.totalVariation.eq_1`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] (s : MeasureTheory.SignedMeasure α),   s.totalVariation = s
.toJordanDecomposition.posPart + s.to…
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure.0.M
easureTheory.SignedMeasure.toMeasureOfZeroLE_apply_eq_enorm`：∀ {X : Type u_1} {m
X : MeasurableSpace X} (μ : MeasureTheory.SignedMeasure X) {i j : Set X} (him : 
MeasurableSet i)   (hi : MeasureTheory.Ve…
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure.0.M
easureTheory.SignedMeasure.toMeasureOfLEZero_apply_eq_enorm`：∀ {X : Type u_1} {m
X : MeasurableSpace X} (μ : MeasureTheory.SignedMeasure X) {i j : Set X} (him : 
MeasurableSet i)   (hi : MeasureTheory.Ve…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `MeasureTheory.SignedMeasure.enorm_le_totalVariation`：enorm_le_totalVaria
tion (s : SignedMeasure X) (i : Set X) : ‖s i‖ₑ <= s.totalVariation i

--- 原说明 ---
The Hahn–Jordan-based `totalVariation` agrees with the supremum-based `variation
`.
-/
theorem totalVariation_eq_variation (μ : SignedMeasure X) : μ.totalVariation = μ.variation := by
  ext r hr
  apply le_antisymm
  · obtain ⟨s, hs, hpos, hneg, hposPart, hnegPart⟩ := μ.toJordanDecomposition_spec
    calc μ.totalVariation r
      _ = ‖μ (s ∩ r)‖ₑ + ‖μ (sᶜ ∩ r)‖ₑ := by
          rw [totalVariation, Measure.add_apply, hposPart, hnegPart,
            μ.toMeasureOfZeroLE_apply_eq_enorm hs hpos hr,
            μ.toMeasureOfLEZero_apply_eq_enorm hs.compl hneg hr]
      _ ≤ μ.variation (s ∩ r) + μ.variation (sᶜ ∩ r) :=
          add_le_add (μ.enorm_measure_le_variation _) (μ.enorm_measure_le_variation _)
      _ = μ.variation ((s ∩ r) ∪ (sᶜ ∩ r)) :=
        (measure_union (by grind) (hs.compl.inter hr)).symm
      _ = μ.variation r := by congr; grind
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    exact fun s _ ↦ enorm_le_totalVariation μ s

end MeasureTheory.SignedMeasure

