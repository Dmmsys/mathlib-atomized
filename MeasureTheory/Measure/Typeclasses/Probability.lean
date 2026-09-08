/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.UnitInterval

/-!
# Classes for probability measures

We introduce the following typeclasses for measures:

* `IsZeroOrProbabilityMeasure μ`: `μ univ = 0 ∨ μ univ = 1`;
* `IsProbabilityMeasure μ`: `μ univ = 1`.
-/

public section

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsZeroOrProbabilityMeasure

/-- A measure `μ` is zero or a probability measure if `μ univ = 0` or `μ univ = 1`. This class
of measures appears naturally when conditioning on events, and many results which are true for
probability measures hold more generally over this class. -/
/-
**MeasureTheory.IsZeroOrProbabilityMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureT
heory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is zero or a probability measure if `μ univ = 0` or `μ univ = 1`. 
This class
of measures appears naturally when conditioning on events, and many results whic
h are true for
probability measures hold more generally over this class.
-/
class IsZeroOrProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 0 ∨ μ univ = 1
/-
**MeasureTheory.isZeroOrProbabilityMeasure_iff** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0
 ∨ μ univ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.measure_univ`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : MeasureTheory.I
sZeroOrProbabilityMeasure μ], μ Set.univ = …
-/
lemma isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1 :=
  ⟨fun _ ↦ IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩
/-
**MeasureTheory.prob_le_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ
 s <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.measure_univ`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : MeasureTheory.I
sZeroOrProbabilityMeasure μ], μ Set.univ = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ s ≤ 1 := by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

@[simp]
/-
**MeasureTheory.measureReal_le_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set
 α} : μ.real s <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
-/
lemma measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} :
    μ.real s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]
/-
**MeasureTheory.one_le_prob_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：one_le_prob_iff {μ : Measure α} [IsZeroOrProbabilityMeasure μ] : 1 <= μ s 
↔ μ s = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem one_le_prob_iff {μ : Measure α} [IsZeroOrProbabilityMeasure μ] : 1 ≤ μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsZeroOrProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsZeroOrProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨prob_le_one.trans_lt one_lt_top⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroOrProbabilityMeasure (0 : Measure α) :=
  ⟨Or.inl rfl⟩

end IsZeroOrProbabilityMeasure

section IsProbabilityMeasure

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
/-
**MeasureTheory.IsProbabilityMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`
。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is called a probability measure if `μ univ = 1`.
-/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1

export MeasureTheory.IsProbabilityMeasure (measure_univ)

attribute [simp] IsProbabilityMeasure.measure_univ
/-
**MeasureTheory.isProbabilityMeasure_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
lemma isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1 :=
  ⟨fun _ ↦ measure_univ, IsProbabilityMeasure.mk⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsZeroOrProbabilityMeasure μ :=
  ⟨Or.inr measure_univ⟩
/-
**MeasureTheory.nonempty_of_isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：nonempty_of_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ] 
: Nonempty α
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem nonempty_of_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α := by
  by_contra! maybe_empty
  have : μ Set.univ = 0 := by
    rw [Set.univ_eq_empty_iff.mpr maybe_empty, measure_empty]
  simp at this
/-
**MeasureTheory.IsProbabilityMeasure.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.IsProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [M
easureTheory.IsProbabilityMeasure μ], μ ≠ 0
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem IsProbabilityMeasure.ne_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ ≠ 0 :=
  mt measure_univ_eq_zero.2 <| by simp [measure_univ]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsProbabilityMeasure.neZero (μ : Measure α) [IsProbabilityMeasure μ] :
    NeZero μ := ⟨IsProbabilityMeasure.ne_zero μ⟩
/-
**MeasureTheory.IsProbabilityMeasure.ae_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.IsProbabilityMeasure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [M
easureTheory.IsProbabilityMeasure μ],   (MeasureTheory.ae μ).NeBot
参数：MeasureTheory.ae μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
-/
theorem IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot (ae μ) := inferInstance
/-
**MeasureTheory.prob_add_prob_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s +
 μ sᶜ = 1
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_add_measure_compl`：measure_add_measure_compl (h : 
MeasurableSet s) : μ s + μ sᶜ = μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
theorem prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s + μ sᶜ = 1 :=
  (measure_add_measure_compl h).trans measure_univ
/-
**MeasureTheory.probReal_add_probReal_compl** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：probReal_add_probReal_compl [IsProbabilityMeasure μ] (h : MeasurableSet s)
 : μ.real s + μ.real sᶜ = 1
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.prob_add_prob_compl`：prob_add_prob_compl [IsProbabilityMea
sure μ] (h : MeasurableSet s) : μ s + μ sᶜ = 1
-/
lemma probReal_add_probReal_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = 1 := by
  simpa [Measure.real, ENNReal.toReal_add] using congr($(prob_add_prob_compl (μ := μ) h).toReal)
/-
**MeasureTheory.isProbabilityMeasureSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y`。
形式化陈述：isProbabilityMeasureSMul [IsFiniteMeasure μ] [NeZero μ] : IsProbabilityMea
sure ((μ univ)⁻¹ • μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
instance isProbabilityMeasureSMul [IsFiniteMeasure μ] [NeZero μ] :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩
/-
**MeasureTheory.isProbabilityMeasure_dite** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry`。
形式化陈述：isProbabilityMeasure_dite {p : Prop} [Decidable p] {μ : p -> Measure α} {ν
 : ¬ p -> Measure α} [forall h, IsProbabilityMeasure (μ h)] [forall h, IsProbabi
lityMeasure (ν h)] : IsProbabilityMeasure (dite p μ ν)
参数：μ h；ν h。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
instance isProbabilityMeasure_dite {p : Prop} [Decidable p] {μ : p → Measure α}
    {ν : ¬ p → Measure α} [∀ h, IsProbabilityMeasure (μ h)] [∀ h, IsProbabilityMeasure (ν h)] :
    IsProbabilityMeasure (dite p μ ν) := by split <;> infer_instance
/-
**MeasureTheory.isProbabilityMeasure_ite** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y`。
形式化陈述：isProbabilityMeasure_ite {p : Prop} [Decidable p] {μ ν : Measure α} [IsPro
babilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (ite p μ ν)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
instance isProbabilityMeasure_ite {p : Prop} [Decidable p] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ite p μ ν) := by split <;> infer_instance

open unitInterval in
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : I} :
    IsProbabilityMeasure (toNNReal p • μ + toNNReal (σ p) • ν) where
  measure_univ := by simp [← ENNReal.coe_add]

variable [IsProbabilityMeasure μ] {p : α → Prop} {f : β → α}
/-
**MeasureTheory.probReal_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [M
easureTheory.IsProbabilityMeasure μ],   μ.real Set.univ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma probReal_univ : μ.real univ = 1 := by simp [Measure.real]
/-
**MeasureTheory.isProbabilityMeasure_iff_real** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：isProbabilityMeasure_iff_real {μ : Measure α} : IsProbabilityMeasure μ ↔ μ
.real univ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
-/
lemma isProbabilityMeasure_iff_real {μ : Measure α} :
    IsProbabilityMeasure μ ↔ μ.real univ = 1 := by
  refine ⟨fun h ↦ probReal_univ, fun h ↦ ⟨(ENNReal.toReal_eq_one_iff (μ univ)).mp h⟩⟩
/-
**MeasureTheory.Measure.isProbabilityMeasure_map** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsProbabilityMeasure μ]
 {f : α → β},   AEMeasurable f μ → MeasureTheory.IsProbabilityMeasure (MeasureTh
eory.Measure.map f μ)
参数：MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Measure.isProbabilityMeasure_map {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (map f μ) :=
  ⟨by simp [map_apply_of_aemeasurable, hf]⟩
/-
**MeasureTheory.Measure.isProbabilityMeasure_of_map** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] {μ : MeasureTheory.Measure α}   (f : α → β) [MeasureTheory.IsProbabili
tyMeasure (MeasureTheory.Measure.map f μ)], MeasureTheory.IsProbabilityMeasure μ
参数：f : α → β；MeasureTheory.Measure.map f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.of_map_ne_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {f : α → β}   {μ : MeasureTheory.Measure 
α}, MeasureTheory…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
theorem Measure.isProbabilityMeasure_of_map {μ : Measure α} (f : α → β)
    [IsProbabilityMeasure (μ.map f)] : IsProbabilityMeasure μ where
  measure_univ := by
    have hf : AEMeasurable f μ := AEMeasurable.of_map_ne_zero (IsProbabilityMeasure.ne_zero _)
    rw [← Set.preimage_univ (f := f), ← map_apply_of_aemeasurable hf .univ]
    exact IsProbabilityMeasure.measure_univ
/-
**MeasureTheory.Measure.isProbabilityMeasure_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m0 : MeasurableSpace α} [inst : Measurabl
eSpace β] {μ : MeasureTheory.Measure α}   {f : α → β},   AEMeasurable f μ →     
(MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map f μ) ↔ MeasureThe
ory.IsProbabilityMeasure μ)
参数：MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map f μ) ↔ MeasureT
heory.IsProbabilityMeasure μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_of_map`：∀ {α : Type u_1} {β :
 Type u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheor
y.Measure α}   (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
-/
theorem Measure.isProbabilityMeasure_map_iff {μ : Measure α} {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) ↔ IsProbabilityMeasure μ :=
  ⟨fun _ ↦ isProbabilityMeasure_of_map f, fun _ ↦ isProbabilityMeasure_map hf⟩
/-
**MeasureTheory.IsProbabilityMeasure_comap_equiv** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory`。
形式化陈述：IsProbabilityMeasure_comap_equiv (f : β ≃ᵐ α) : IsProbabilityMeasure (μ.co
map f)
参数：f : β ≃ᵐ α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.map_symm`：map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map 
e.symm = μ.comap e
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
-/
instance IsProbabilityMeasure_comap_equiv (f : β ≃ᵐ α) : IsProbabilityMeasure (μ.comap f) := by
  rw [← MeasurableEquiv.map_symm]; exact isProbabilityMeasure_map f.symm.measurable.aemeasurable

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
/-
**MeasureTheory.prob_compl_eq_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.prob_compl_eq_one_sub₀`：prob_compl_eq_one_sub₀ (h : NullMe
asurableSet s μ) : μ sᶜ = 1 - μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
Note that this is not quite as useful as it looks because the measure takes valu
es in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather th
an the
better-behaved subtraction of `ℝ`.
-/
lemma prob_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ sᶜ = 1 - μ s := by
  rw [measure_compl₀ h (measure_ne_top _ _), measure_univ]

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
/-
**MeasureTheory.prob_compl_eq_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.prob_compl_eq_one_sub₀`：prob_compl_eq_one_sub₀ (h : NullMe
asurableSet s μ) : μ sᶜ = 1 - μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
Note that this is not quite as useful as it looks because the measure takes valu
es in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather th
an the
better-behaved subtraction of `ℝ`.
-/
theorem prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s :=
  prob_compl_eq_one_sub₀ hs.nullMeasurableSet
/-
**MeasureTheory.prob_compl_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma prob_compl_eq_zero_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 0 ↔ μ s = 1 := by
  rw [prob_compl_eq_one_sub₀ hs, tsub_eq_zero_iff_le, one_le_prob_iff]
/-
**MeasureTheory.prob_compl_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1 := by
  simp [hs]
/-
**MeasureTheory.prob_compl_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma prob_compl_eq_one_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 1 ↔ μ s = 0 := by
  rw [← prob_compl_eq_zero_iff₀ hs.compl, compl_compl]
/-
**MeasureTheory.prob_compl_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0 := by
  simp [hs]
/-
**MeasureTheory.mem_ae_iff_prob_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s in ae μ ↔ μ s = 1
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用引理 `MeasureTheory.prob_compl_eq_zero_iff`：prob_compl_eq_zero_iff (hs : Measu
rableSet s) : μ sᶜ = 0 ↔ μ s = 1
-/
lemma mem_ae_iff_prob_eq_one₀ (hs : NullMeasurableSet s μ) : s ∈ ae μ ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff₀ hs
/-
**MeasureTheory.mem_ae_iff_prob_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s in ae μ ↔ μ s = 1
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用引理 `MeasureTheory.prob_compl_eq_zero_iff`：prob_compl_eq_zero_iff (hs : Measu
rableSet s) : μ sᶜ = 0 ↔ μ s = 1
-/
lemma mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s ∈ ae μ ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff hs
/-
**MeasureTheory.ae_iff_prob_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_iff_prob_eq_one (hp : Measurable p) : (forallᵐ a ∂μ, p a) ↔ μ {a | p a}
 = 1
参数：hp : Measurable p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.mem_ae_iff_prob_eq_one`：mem_ae_iff_prob_eq_one (hs : Measu
rableSet s) : s in ae μ ↔ μ s = 1
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma ae_iff_prob_eq_one (hp : Measurable p) : (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_prob_eq_one hp.setOf
/-
**MeasureTheory.isProbabilityMeasure_comap** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：isProbabilityMeasure_comap (hf : Injective f) (hf' : forallᵐ a ∂μ, a in ra
nge f) (hf'' : forall s, MeasurableSet s -> MeasurableSet (f '' s)) : IsProbabil
ityMeasure (μ.comap f) where measure_univ
参数：hf : Injective f；hf' : forallᵐ a ∂μ, a in range f；hf'' : forall s, Measurable
Set s -> MeasurableSet (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.mem_ae_iff_prob_eq_one`：mem_ae_iff_prob_eq_one (hs : Measu
rableSet s) : s in ae μ ↔ μ s = 1
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma isProbabilityMeasure_comap (hf : Injective f) (hf' : ∀ᵐ a ∂μ, a ∈ range f)
    (hf'' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) :
    IsProbabilityMeasure (μ.comap f) where
  measure_univ := by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ,
      ← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa
/-
**MeasureTheory._root_.MeasurableEmbedding.isProbabilityMeasure_comap** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.MeasurableEmbedding.isProbabilityMeasure_comap (hf : MeasurableEmbedding f)
    (hf' : ∀ᵐ a ∂μ, a ∈ range f) : IsProbabilityMeasure (μ.comap f) :=
  isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'
/-
**MeasureTheory.isProbabilityMeasure_map_up** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory`。
形式化陈述：isProbabilityMeasure_map_up : IsProbabilityMeasure (μ.map ULift.up)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `measurable_up`：measurable_up : Measurable (ULift.up : α -> ULift α)
-/
instance isProbabilityMeasure_map_up :
    IsProbabilityMeasure (μ.map ULift.up) := isProbabilityMeasure_map measurable_up.aemeasurable
/-
**MeasureTheory.isProbabilityMeasure_comap_down** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory`。
形式化陈述：isProbabilityMeasure_comap_down : IsProbabilityMeasure (μ.comap ULift.down
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.isProbabilityMeasure_comap`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isProbabilityMeasure_comap_down : IsProbabilityMeasure (μ.comap ULift.down) :=
  MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap <| ae_of_all _ <| by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]
/-
**MeasureTheory.Measure.eq_of_le_of_isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} 
[MeasureTheory.IsProbabilityMeasure μ]   [MeasureTheory.IsProbabilityMeasure ν],
 μ ≤ ν → μ = ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_of_le_of_measure_univ_eq`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeas
ure μ],   μ ≤ ν → μ Set.univ = ν Set.un…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Measure.eq_of_le_of_isProbabilityMeasure {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≤ ν) : μ = ν :=
  eq_of_le_of_measure_univ_eq hμν (by simp)

end IsProbabilityMeasure

section IsZeroOrProbabilityMeasure

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/-
**MeasureTheory.isZeroOrProbabilityMeasureSMul** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory`。
形式化陈述：isZeroOrProbabilityMeasureSMul : IsZeroOrProbabilityMeasure ((μ univ)⁻¹ • 
μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfNatMeasure`：∀ {α : Type u_
1} {m0 : MeasurableSpace α}, MeasureTheory.IsZeroOrProbabilityMeasure 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
-/
instance isZeroOrProbabilityMeasureSMul :
    IsZeroOrProbabilityMeasure ((μ univ)⁻¹ • μ) := by
  rcases eq_zero_or_neZero μ with rfl | h
  · simp; infer_instance
  rcases eq_top_or_lt_top (μ univ) with h | h
  · simp [h]; infer_instance
  have : IsFiniteMeasure μ := ⟨h⟩
  infer_instance

variable [IsZeroOrProbabilityMeasure μ] {p : α → Prop} {f : β → α}

variable (μ) in
/-
**MeasureTheory.eq_zero_or_isProbabilityMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：eq_zero_or_isProbabilityMeasure : μ = 0 ∨ IsProbabilityMeasure μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.measure_univ`：∀ {α : Type u_1} 
{m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : MeasureTheory.I
sZeroOrProbabilityMeasure μ], μ Set.univ = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
-/
lemma eq_zero_or_isProbabilityMeasure : μ = 0 ∨ IsProbabilityMeasure μ := by
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · apply Or.inl (measure_univ_eq_zero.mp h)
  · exact Or.inr ⟨h⟩
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : α → β} : IsZeroOrProbabilityMeasure (map f μ) := by
  by_cases hf : AEMeasurable f μ
  · simpa [isZeroOrProbabilityMeasure_iff, hf] using IsZeroOrProbabilityMeasure.measure_univ
  · simp [isZeroOrProbabilityMeasure_iff, hf]
/-
**MeasureTheory.prob_compl_lt_one_sub_of_lt_prob** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：prob_compl_lt_one_sub_of_lt_prob {p : Real>=0∞} (hμs : p < μ s) (s_mble : 
MeasurableSet s) : μ sᶜ < 1 - p
参数：hμs : p < μ s；s_mble : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.prob_compl_eq_one_sub`：prob_compl_eq_one_sub (hs : Measura
bleSet s) : μ sᶜ = 1 - μ s
· 使用定理 `ENNReal.sub_lt_of_sub_lt`：sub_lt_of_sub_lt (h₂ : c <= a) (h₃ : a != ∞ ∨ 
b != ∞) (h₁ : a - b < c) : a - c < b
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ENNReal.sub_sub_cancel`：sub_sub_cancel (h : a != ∞) (h2 : b <= a) : a - 
(a - b) = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma prob_compl_lt_one_sub_of_lt_prob {p : ℝ≥0∞} (hμs : p < μ s) (s_mble : MeasurableSet s) :
    μ sᶜ < 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp at hμs
  · rw [prob_compl_eq_one_sub s_mble]
    apply ENNReal.sub_lt_of_sub_lt prob_le_one (Or.inl one_ne_top)
    convert! hμs
    exact ENNReal.sub_sub_cancel one_ne_top (lt_of_lt_of_le hμs prob_le_one).le
/-
**MeasureTheory.prob_compl_le_one_sub_of_le_prob** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：prob_compl_le_one_sub_of_le_prob {p : Real>=0∞} (hμs : p <= μ s) (s_mble :
 MeasurableSet s) : μ sᶜ <= 1 - p
参数：hμs : p <= μ s；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.prob_compl_eq_one_sub`：prob_compl_eq_one_sub (hs : Measura
bleSet s) : μ sᶜ = 1 - μ s
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
-/
lemma prob_compl_le_one_sub_of_le_prob {p : ℝ≥0∞} (hμs : p ≤ μ s) (s_mble : MeasurableSet s) :
    μ sᶜ ≤ 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  · simpa [prob_compl_eq_one_sub s_mble] using tsub_le_tsub_left hμs 1

@[simp]
/-
**MeasureTheory.inv_measure_univ_smul_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：inv_measure_univ_smul_eq_self : (μ univ)⁻¹ • μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma inv_measure_univ_smul_eq_self : (μ univ)⁻¹ • μ = μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

end IsZeroOrProbabilityMeasure

end MeasureTheory

