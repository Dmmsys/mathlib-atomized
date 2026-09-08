/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!

We introduce the typeclass `IsZeroOneMeasure` for measures that only take the values `0` and `1`.

## Main definitions

* `IsZeroOneMeasure`: a measure is a zero-one measure if it only takes the values `0`
  or `1`.

## Main statements

* `exists_eq_dirac`: in a standard Borel space, a zero-one measure that is not the zero measure is
  a Dirac measure.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- A measure is a zero-one measure if it only takes the values `0` or `1`. -/
/-
**MeasureTheory.IsZeroOneMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {mα : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is a zero-one measure if it only takes the values `0` or `1`.
-/
class IsZeroOneMeasure (μ : Measure α) : Prop where
  zero_one₀ : ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1
/-
**MeasureTheory.Measure.zero_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ : MeasureTheory.Measure α) [M
easureTheory.IsZeroOneMeasure μ] (s : Set α),   μ s = 0 ∨ μ s = 1
参数：μ : MeasureTheory.Measure α；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsZeroOneMeasure.zero_one₀`：∀ {α : Type u_1} {mα : Measura
bleSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsZeroOneMeasure
 μ]   ⦃s : Set α⦄, MeasurableS…
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Measure.zero_one (μ : Measure α) [IsZeroOneMeasure μ] :
    ∀ s, μ s = 0 ∨ μ s = 1 := by
  intro s
  by_cases hs : MeasurableSet s
  · exact IsZeroOneMeasure.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact IsZeroOneMeasure.zero_one₀ mt

variable {μ : Measure α} [IsZeroOneMeasure μ]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroOrProbabilityMeasure μ where
  measure_univ := μ.zero_one univ

namespace IsZeroOneMeasure

/-
**MeasureTheory.IsZeroOneMeasure.exists_measure_eq_one_iff_measure_univ_eq_one**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.IsZeroOneMeasure`。
形式化陈述：exists_measure_eq_one_iff_measure_univ_eq_one : (exists s, μ s = 1) ↔ μ un
iv = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.zero_one`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZeroOneMeasure μ] (s : Set α), 
  μ s = 0 ∨ μ s = 1
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
lemma exists_measure_eq_one_iff_measure_univ_eq_one : (∃ s, μ s = 1) ↔ μ univ = 1 := by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
    · have := measure_mono (μ := μ) <| subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩
/-
**MeasureTheory.IsZeroOneMeasure.measure_univ** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.IsZeroOneMeasure`。
形式化陈述：measure_univ {s : Set α} (hμs : μ s = 1) : μ univ = 1
参数：hμs : μ s = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.IsZeroOneMeasure.exists_measure_eq_one_iff_measure_univ_eq
_one`：exists_measure_eq_one_iff_measure_univ_eq_one : (exists s, μ s = 1) ↔ μ un
iv = 1
-/
lemma measure_univ {s : Set α} (hμs : μ s = 1) : μ univ = 1 :=
  (exists_measure_eq_one_iff_measure_univ_eq_one).mp ⟨s, hμs⟩
/-
**MeasureTheory.IsZeroOneMeasure.measure_inter_eq_one** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.IsZeroOneMeasure`。
形式化陈述：measure_inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : Measurable
Set t) (hμs : μ s = 1) (hμt : μ t = 1) : μ (s inter t) = 1
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμs : μ s = 1；hμt : μ t = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.zero_one`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZeroOneMeasure μ] (s : Set α), 
  μ s = 0 ∨ μ s = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasure`：∀ {α : Type u_1} {mα : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsZeroOneMeasure μ]
,   MeasureTheory.IsZeroOrProbabil…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MeasureTheory.IsZeroOneMeasure.measure_univ`：measure_univ {s : Set α} (h
μs : μ s = 1) : μ univ = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
lemma measure_inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s = 1) (hμt : μ t = 1) : μ (s ∩ t) = 1 := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  rcases μ.zero_one s with (_ | hμs)
    <;> rcases μ.zero_one t with (_ | hμt)
    <;> rcases μ.zero_one (s ∩ t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s ∩ t)ᶜ ≤ 0 by
    rw [measure_compl (hs.inter ht) (by simp), measure_univ ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ ∪ tᶜ) := by simp [compl_inter]
  _ ≤ μ sᶜ + μ tᶜ := measure_union_le _ _
  _ ≤ 0 := by
    rw [measure_compl hs (by simp), measure_univ hμs, hμs, tsub_self,
      measure_compl ht (by simp), measure_univ hμt, hμt, tsub_self]
    simp
/-
**MeasureTheory.IsZeroOneMeasure.measure_inter_eq_prod** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.IsZeroOneMeasure`。
形式化陈述：measure_inter_eq_prod {s t : Set α} (hs : MeasurableSet s) (ht : Measurabl
eSet t) : μ (s inter t) = μ s * μ t
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.zero_one`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZeroOneMeasure μ] (s : Set α), 
  μ s = 0 ∨ μ s = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.IsZeroOneMeasure.measure_inter_eq_one`：measure_inter_eq_on
e {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s = 1) (h
μt : μ t = 1) : μ (s inter t) = 1
-/
lemma measure_inter_eq_prod {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∩ t) = μ s * μ t := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s ∩ t)
  all_goals try simp_all [measure_inter_eq_one]

/-- In a standard Borel space, a zero-one measure that is not the zero measure is a Dirac
measure. -/
/-
**MeasureTheory.IsZeroOneMeasure.exists_eq_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsZeroOneMeasure`。
形式化陈述：exists_eq_dirac [StandardBorelSpace α] [NeZero μ] : exists x₀, μ = Measure
.dirac x₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.measure_univ`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : MeasureTheory.I
sZeroOrProbabilityMeasure μ], μ Set.univ = …
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasure`：∀ {α : Type u_1} {mα : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsZeroOneMeasure μ]
,   MeasureTheory.IsZeroOrProbabil…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_seq_separating`：exists_seq_separating (α : Type*) {p : Set α -> P
rop} {s₀} (hp : p s₀) (t : Set α) [HasCountableSeparatingOn α p t] : exists S : 
Nat -> Set …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `MeasurableSpace.separatesPoints_of_measurableSingletonClass`：∀ {α : Type
 u_1} [inst : MeasurableSpace α] [MeasurableSingletonClass α], MeasurableSpace.S
eparatesPoints α
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.prob_compl_eq_zero_iff`：prob_compl_eq_zero_iff (hs : Measu
rableSet s) : μ sᶜ = 0 ↔ μ s = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `MeasureTheory.Measure.zero_one`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZeroOneMeasure μ] (s : Set α), 
  μ s = 0 ∨ μ s = 1
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
In a standard Borel space, a zero-one measure that is not the zero measure is a 
Dirac
measure.
-/
theorem exists_eq_dirac [StandardBorelSpace α] [NeZero μ] : ∃ x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n ↦ ?_
    simp only [dite_eq_ite, B]
    split_ifs
    · exact hAm n
    · exact (hAm n).compl
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    split_ifs with h
    · simp_all
    · rw [compl_compl]
      rcases μ.zero_one (A n) with (h₀ | h₁)
      · exact h₀
      · simp_all
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨neBn.some, neBn.some_mem, fun y hy ↦ ?_⟩
    refine hAsep y (by trivial) neBn.some (by trivial) fun n ↦ ?_
    have hsome := neBn.some_mem
    simp only [dite_eq_ite, mem_iInter, B] at hsome hy
    specialize hsome n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using! hsome
      · contradiction
    · intro h
      split_ifs at hsome with hμAn
      · simpa [hμAn] using! hy
      · contradiction
  use x₀
  ext s hs
  by_cases h : x₀ ∈ s
  · simp [h]
    have : μ {x₀} ≤ μ s := measure_mono (μ := μ) (by grind)
    rw [← hx₀, hBn] at this
    simp_all
  · simp [h]
    have : μ s ≤ μ {x₀}ᶜ := measure_mono (μ := μ) (by grind)
    rw [← hx₀, measure_compl mBn (by simp), MeasureTheory.measure_univ, hBn] at this
    simp_all

end IsZeroOneMeasure

end MeasureTheory

