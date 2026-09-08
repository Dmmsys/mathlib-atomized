/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measures as real-valued functions

Given a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.
In this file, we develop a basic API around this notion.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of
the form `≠ ∞`.

There are certainly many missing lemmas. The missing ones should be added as they are needed.

There are no lemmas on infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. They should probably be added in the long
run.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal NNReal Function symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}

/-
**MeasureTheory.measureReal_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measureReal_eq_zero_iff (h : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.real.eq_1`：∀ {α : Type u_6} {m : MeasurableSpace α
} (μ : MeasureTheory.Measure α) (s : Set α), μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
-/
theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h
/-
**MeasureTheory.measureReal_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measureReal_ne_zero_iff (h : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measureReal_ne_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s ≠ 0 ↔ μ s ≠ 0 := by
  simp [measureReal_eq_zero_iff, h]
/-
**MeasureTheory.measureReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α}, MeasureTheory.Measure.real 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem measureReal_zero : (0 : Measure α).real = 0 := rfl
/-
**MeasureTheory.measureReal_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0 := rfl
/-
**MeasureTheory.measureReal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
: Set α}, 0 ≤ μ.real s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg
/-
**MeasureTheory.measureReal_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ.
real ∅ = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]

@[simp]
/-
**MeasureTheory.measureReal_univ_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
  ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (by finiteness)
/-
**MeasureTheory.measureReal_univ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ 
!= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measureReal_univ_pos`：measureReal_univ_pos [IsFiniteMeasur
e μ] [NeZero μ] : 0 < μ.real Set.univ
-/
theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
  measureReal_univ_pos.ne'

@[simp]
/-
**MeasureTheory.ofReal_measureReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ofReal_measureReal (h : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_measureReal (h : μ s ≠ ∞ := by finiteness) : ENNReal.ofReal (μ.real s) = μ s := by
  simp [measureReal_def, h]
/-
**MeasureTheory.nonempty_of_measureReal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：nonempty_of_measureReal_ne_zero (h : μ.real s != 0) : s.Nonempty
参数：h : μ.real s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ measureReal_empty
/-
**MeasureTheory.measureReal_ennreal_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
: Set α} (c : ENNReal),   (c • μ).real s = c.toReal * μ.real s
参数：c : ENNReal；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem measureReal_ennreal_smul_apply (c : ℝ≥0∞) :
    (c • μ).real s = c.toReal * μ.real s := by
  simp [Measure.real]
/-
**MeasureTheory.measureReal_nnreal_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
: Set α} (c : NNReal),   (c • μ).real s = ↑c * μ.real s
参数：c : NNReal；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem measureReal_nnreal_smul_apply (c : ℝ≥0) :
    (c • μ).real s = c * μ.real s := by
  simp [measureReal_def]
/-
**MeasureTheory.map_measureReal_apply_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：map_measureReal_apply_of_aemeasurable [MeasurableSpace β] {f : α -> β} (hf
 : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.r
eal (f ⁻¹' s)
参数：hf : AEMeasurable f μ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_measureReal_apply_of_aemeasurable [MeasurableSpace β] {f : α → β}
    (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).real s = μ.real (f ⁻¹' s) := by
  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]
/-
**MeasureTheory.map_measureReal_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_measureReal_apply [MeasurableSpace β] {f : α -> β} (hf : Measurable f)
 {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.map_measureReal_apply_of_aemeasurable`：map_measureReal_app
ly_of_aemeasurable [MeasurableSpace β] {f : α -> β} (hf : AEMeasurable f μ) {s :
 Set β} (hs : MeasurableSet s) : (μ.map f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) :=
  map_measureReal_apply_of_aemeasurable hf.aemeasurable hs
/-
**MeasureTheory.measureReal_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s₁
 s₂ : Set α},   s₁ ⊆ s₂ → autoParam (μ s₂ ≠ ⊤) MeasureTheory.measureReal_mono._a
uto_1 → μ.real s₁ ≤ μ.real s₂
参数：μ s₂ ≠ ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ ≤ μ.real s₂ :=
  ENNReal.toReal_mono h₂ (measure_mono h)
/-
**MeasureTheory.measureReal_eq_measureReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t 
: Set β} (h₁ : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β}
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : ν t ≠ ∞ := by finiteness) :
    μ.real s = ν.real t ↔ μ s = ν t := by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]
/-
**MeasureTheory.measureReal_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_restrict_apply (ht : MeasurableSet t) : (μ.restrict s).real t 
= μ.real (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]
/-
**MeasureTheory.measureReal_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_restrict_apply (ht : MeasurableSet t) : (μ.restrict s).real t 
= μ.real (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply (ht : MeasurableSet t) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply ht]
/-
**MeasureTheory.measureReal_restrict_apply_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measureReal_restrict_apply_univ (s : Set α) : (μ.restrict s).real univ = μ
.real s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply_univ (s : Set α) : (μ.restrict s).real univ = μ.real s := by
  simp

@[simp]
/-
**MeasureTheory.measureReal_restrict_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_restrict_apply' (hs : MeasurableSet s) : (μ.restrict s).real t
 = μ.real (t inter s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply' (hs : MeasurableSet s) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply' hs]
/-
**MeasureTheory.measureReal_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_restrict_apply (ht : MeasurableSet t) : (μ.restrict s).real t 
= μ.real (t inter s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  simp only [restrict_apply₀' hs]

@[simp]
/-
**MeasureTheory.measureReal_restrict_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measureReal_restrict_apply_self (s : Set α) : (μ.restrict s).real s = μ.re
al s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_self`：restrict_apply_self (s : Set 
α) : (μ.restrict s) s = μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_restrict_apply_self (s : Set α) : (μ.restrict s).real s = μ.real s := by
  simp [measureReal_def]
/-
**MeasureTheory.measureReal_mono_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_mono_null (h : s₁ subseteq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s
₂ != ∞
参数：h : s₁ subseteq s₂；h₂ : μ.real s₂ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]
/-
**MeasureTheory.measureReal_le_measureReal_union_left** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：measureReal_le_measureReal_union_left (h : μ t != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_mono`：∀ {α : Type u_1} {x : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {s₁ s₂ : Set α},   s₁ ⊆ s₂ → autoParam (μ s₂ ≠ ⊤)
 MeasureTheory.measu…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_union_lt_top`：measure_union_lt_top (hs : μ s < ∞) 
(ht : μ t < ∞) : μ (s union t) < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real (s ∪ t) := by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne
/-
**MeasureTheory.measureReal_le_measureReal_union_right** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：measureReal_le_measureReal_union_right (h : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `MeasureTheory.measureReal_le_measureReal_union_left`：measureReal_le_meas
ureReal_union_left (h : μ t != ∞
-/
theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
    μ.real t ≤ μ.real (s ∪ t) := by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h
/-
**MeasureTheory.measureReal_union_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ union s₂) <= μ.real s₁ +
 μ.real s₂
参数：s₁ s₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
  rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
    simp only [Measure.real, ← ENNReal.toReal_add A B]
    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)
/-
**MeasureTheory.measureReal_biUnion_finset_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measureReal_biUnion_finset_le (s : Finset β) (f : β -> Set α) : μ.real (⋃ 
b in s, f b) <= ∑ p in s, μ.real (f p)
参数：s : Finset β；f : β -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measureReal_union_le`：measureReal_union_le (s₁ s₂ : Set α)
 : μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :
    μ.real (⋃ b ∈ s, f b) ≤ ∑ p ∈ s, μ.real (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx IH =>
    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)
/-
**MeasureTheory.measureReal_iUnion_fintype_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measureReal_iUnion_fintype_le [Fintype β] (f : β -> Set α) : μ.real (⋃ b, 
f b) <= ∑ p, μ.real (f p)
参数：f : β -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measureReal_biUnion_finset_le`：measureReal_biUnion_finset_
le (s : Finset β) (f : β -> Set α) : μ.real (⋃ b in s, f b) <= ∑ p in s, μ.real 
(f p)
-/
theorem measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :
    μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by
  convert! measureReal_biUnion_finset_le Finset.univ f
  simp
/-
**MeasureTheory.measureReal_iUnion_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_iUnion_fintype [Fintype β] {f : β -> Set α} (hn : Pairwise (Di
sjoint on f)) (h : forall i, MeasurableSet (f i)) (h' : forall i, μ (f i) != ∞
参数：hn : Pairwise (Disjoint on f)；h : forall i, MeasurableSet (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))
    (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :
    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,
    ENNReal.toReal_sum (fun i _hi ↦ h' i)]
/-
**MeasureTheory.measureReal_union_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) : μ.real 
(s₁ union s₂) = 0
参数：h₁ : μ.real s₁ = 0；h₂ : μ.real s₂ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measureReal_union_le`：measureReal_union_le (s₁ s₂ : Set α)
 : μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
-/
theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
    μ.real (s₁ ∪ s₂) = 0 :=
  le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]
/-
**MeasureTheory.measureReal_union_null_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_union_null_iff (h₁ : μ s₁ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_mono_null`：measureReal_mono_null (h : s₁ subse
teq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ != ∞
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `MeasureTheory.measure_union_ne_top`：measure_union_ne_top (hs : μ s != ∞)
 (ht : μ t != ∞) : μ (s union t) != ∞
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `MeasureTheory.measureReal_union_null`：measureReal_union_null (h₁ : μ.rea
l s₁ = 0) (h₂ : μ.real s₂ = 0) : μ.real (s₁ union s₂) = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measureReal_union_null_iff
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 :=
  ⟨fun h ↦ ⟨measureReal_mono_null subset_union_left h (by finiteness),
      measureReal_mono_null subset_union_right h (by finiteness)⟩,
  fun h ↦ measureReal_union_null h.1 h.2⟩

/-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/
/-
**MeasureTheory.measureReal_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t
参数：H : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`.
-/
theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
  simp [Measure.real, measure_congr H]
/-
**MeasureTheory.measureReal_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_inter_add_sdiff (ht : MeasurableSet t) (h : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
-/
theorem measureReal_inter_add_sdiff₀ (ht : NullMeasurableSet t μ)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add, measure_inter_add_sdiff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff₀ := measureReal_inter_add_sdiff₀
/-
**MeasureTheory.measureReal_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_union_add_inter (ht : MeasurableSet t) (h₁ : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union_add_inter₀`：measureReal_union_add_inter₀
 (ht : NullMeasurableSet t μ) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_union_add_inter₀ (ht : NullMeasurableSet t μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  have : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_sdiff₀ ht this, Set.union_inter_cancel_right, union_sdiff_right,
    ← measureReal_inter_add_sdiff₀ ht h₁]
  ac_rfl
/-
**MeasureTheory.measureReal_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_union_add_inter (ht : MeasurableSet t) (h₁ : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union_add_inter₀`：measureReal_union_add_inter₀
 (ht : NullMeasurableSet t μ) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  rw [union_comm, inter_comm, measureReal_union_add_inter₀ hs h₂ h₁, add_comm]
/-
**MeasureTheory.measureReal_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) (h₁ : μ s₁ 
!= ∞
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union₀`：measureReal_union₀ (ht : NullMeasurabl
eSet t μ) (hd : AEDisjoint μ s t) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  simp only [Measure.real]
  rw [measure_union₀ ht hd, ENNReal.toReal_add h₁ h₂]
/-
**MeasureTheory.measureReal_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) (h₁ : μ s₁ 
!= ∞
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union₀`：measureReal_union₀ (ht : NullMeasurabl
eSet t μ) (hd : AEDisjoint μ s t) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  rw [union_comm, measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]
/-
**MeasureTheory.measureReal_add_measureReal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s
) : μ.real s + μ.real sᶜ = μ.real univ
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_add_measureReal_compl₀`：measureReal_add_measur
eReal_compl₀ [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) : μ.real s + μ.rea
l sᶜ = μ.real univ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  rw [← measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]
/-
**MeasureTheory.measureReal_add_measureReal_compl** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s
) : μ.real s + μ.real sᶜ = μ.real univ
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_add_measureReal_compl₀`：measureReal_add_measur
eReal_compl₀ [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) : μ.real s + μ.rea
l sᶜ = μ.real univ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = μ.real univ :=
  measureReal_add_measureReal_compl₀ h.nullMeasurableSet
/-
**MeasureTheory.measureReal_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) (h₁ : μ s₁ 
!= ∞
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union₀`：measureReal_union₀ (ht : NullMeasurabl
eSet t μ) (hd : AEDisjoint μ s t) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂
/-
**MeasureTheory.measureReal_union'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) (h₁ : μ s₁
 != ∞
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union₀'`：measureReal_union₀' (hs : NullMeasura
bleSet s μ) (hd : AEDisjoint μ s t) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂
/-
**MeasureTheory.measureReal_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_inter_add_sdiff (ht : MeasurableSet t) (h : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
-/
theorem measureReal_inter_add_sdiff (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_inter_add_sdiff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff := measureReal_inter_add_sdiff
/-
**MeasureTheory.measureReal_sdiff_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_sdiff_add_inter (ht : MeasurableSet t) (h : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.measureReal_inter_add_sdiff`：measureReal_inter_add_sdiff (
ht : MeasurableSet t) (h : μ s != ∞
-/
theorem measureReal_sdiff_add_inter (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
  (add_comm _ _).trans (measureReal_inter_add_sdiff ht h)

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_add_inter := measureReal_sdiff_add_inter
/-
**MeasureTheory.measureReal_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measureReal_union_add_inter (ht : MeasurableSet t) (h₁ : μ s != ∞
参数：ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union_add_inter₀`：measureReal_union_add_inter₀
 (ht : NullMeasurableSet t μ) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_union_add_inter (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀ ht.nullMeasurableSet h₁ h₂
/-
**MeasureTheory.measureReal_union_add_inter'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measureReal_union_add_inter' (hs : MeasurableSet s) (h₁ : μ s != ∞
参数：hs : MeasurableSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_union_add_inter₀'`：measureReal_union_add_inter
₀' (hs : NullMeasurableSet s μ) (h₁ : μ s != ∞
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_union_add_inter' (hs : MeasurableSet s)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀' hs.nullMeasurableSet h₁ h₂
/-
**MeasureTheory.measureReal_symmDiff_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t) (h₁ 
: μ s != ∞
参数：hs : MeasurableSet s；ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `MeasureTheory.measure_symmDiff_eq`：measure_symmDiff_eq (hs : NullMeasura
bleSet s μ) (ht : NullMeasurableSet t μ) : μ (s ∆ t) = μ (s \ t) + μ (t \ s)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  · exact measure_ne_top_of_subset sdiff_subset h₁
  · exact measure_ne_top_of_subset sdiff_subset h₂
/-
**MeasureTheory.measureReal_symmDiff_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：measureReal_symmDiff_le (u : Set α) (h₁ : μ s != ∞
参数：u : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_symmDiff_eq_top`：measure_symmDiff_eq_top (hs : μ s
 != ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measureReal_mono`：∀ {α : Type u_1} {x : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {s₁ s₂ : Set α},   s₁ ⊆ s₂ → autoParam (μ s₂ ≠ ⊤)
 MeasureTheory.measu…
· 使用定理 `symmDiff_triangle`：symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c
· 使用定理 `MeasureTheory.measure_union_ne_top`：measure_union_ne_top (hs : μ s != ∞)
 (ht : μ t != ∞) : μ (s union t) != ∞
· 使用定理 `MeasureTheory.measure_symmDiff_ne_top`：measure_symmDiff_ne_top (hs : μ s
 != ∞) (ht : μ t != ∞) : μ (s ∆ t) != ∞
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MeasureTheory.measureReal_union_le`：measureReal_union_le (s₁ s₂ : Set α)
 : μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
-/
lemma measureReal_symmDiff_le (u : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ u) ≤ μ.real (s ∆ t) + μ.real (t ∆ u) := by
  rcases eq_top_or_lt_top (μ u) with hu | hu
  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_trans (measureReal_mono (symmDiff_triangle s t u)
        (measure_union_ne_top (by finiteness) (by finiteness)))
      (measureReal_union_le (s ∆ t) (t ∆ u))
/-
**MeasureTheory.measureReal_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseD
isjoint (↑s) f) (hm : forall b in s, MeasurableSet (f b)) (h : forall b in s, μ 
(f b) != ∞
参数：hd : PairwiseDisjoint (↑s) f；hm : forall b in s, MeasurableSet (f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_biUnion_finset₀`：measureReal_biUnion_finset₀ {
s : Finset ι} {f : ι -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm 
: forall b in s, NullMeasurable…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ)
    (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) := by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]
/-
**MeasureTheory.measureReal_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measureReal_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseD
isjoint (↑s) f) (hm : forall b in s, MeasurableSet (f b)) (h : forall b in s, μ 
(f b) != ∞
参数：hd : PairwiseDisjoint (↑s) f；hm : forall b in s, MeasurableSet (f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measureReal_biUnion_finset₀`：measureReal_biUnion_finset₀ {
s : Finset ι} {f : ι -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm 
: forall b in s, NullMeasurable…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) :=
  measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
/-
**MeasureTheory.sum_measureReal_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：sum_measureReal_preimage_singleton (s : Finset β) {f : α -> β} (hf : foral
l y in s, MeasurableSet (f ⁻¹' {y})) (h : forall a in s, μ (f ⁻¹' {a}) != ∞
参数：s : Finset β；hf : forall y in s, MeasurableSet (f ⁻¹' {y})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sum_measure_preimage_singleton`：sum_measure_preimage_singl
eton (s : Finset β) {f : α -> β} (hf : forall y in s, MeasurableSet (f ⁻¹' {y}))
 : (∑ b in s, μ (f ⁻¹' {b})) = μ (…
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` is a `Finset`, then the measure of its preimage can be found as the sum o
f measures
of the fibers `f ⁻¹' {y}`.
-/
theorem sum_measureReal_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) (h : ∀ a ∈ s, μ (f ⁻¹' {a}) ≠ ∞ := by finiteness) :
    (∑ b ∈ s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' s) := by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

/-- If `s` is a `Finset`, then the sums of the real measures of the singletons in the set is the
real measure of the set. -/
/-
**MeasureTheory.sum_measureReal_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asurableSingletonClass α]   [MeasureTheory.SigmaFinite μ] (s : Finset α), ∑ b ∈ 
s, μ.real {b} = μ.real ↑s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `MeasureTheory.measure_singleton_lt_top`：measure_singleton_lt_top [SigmaF
inite μ] : μ {a} < ∞
· 使用定理 `MeasureTheory.sum_measure_singleton`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} {s : Finset α} [MeasurableSingletonClass α],
   ∑ x ∈ s, μ {x} = μ ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` is a `Finset`, then the sums of the real measures of the singletons in th
e set is the
real measure of the set.
-/
@[simp] theorem sum_measureReal_singleton [MeasurableSingletonClass α] [SigmaFinite μ]
    (s : Finset α) :
    (∑ b ∈ s, μ.real {b}) = μ.real s := by
  simp [measureReal_def, ← ENNReal.toReal_sum (fun _ _ ↦ ne_of_lt measure_singleton_lt_top)]
/-
**MeasureTheory.measureReal_sdiff_null'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measureReal_sdiff_null' (h : μ.real (s₁ inter s₂) = 0) (h' : μ s₁ != ∞
参数：h : μ.real (s₁ inter s₂) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff_null'`：measure_sdiff_null' (h : μ (s₁ inter 
s₂) = 0) : μ (s₁ \ s₂) = μ s₁
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem measureReal_sdiff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  simp only [measureReal_def]
  rw [measure_sdiff_null']
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null' := measureReal_sdiff_null'
/-
**MeasureTheory.measureReal_sdiff_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measureReal_sdiff_null (h : μ.real s₂ = 0) (h' : μ s₂ != ∞
参数：h : μ.real s₂ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff_eq_top`：measure_sdiff_eq_top (hs : μ s = ∞) 
(ht : μ t != ∞) : μ (s \ t) = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measureReal_sdiff_null'`：measureReal_sdiff_null' (h : μ.re
al (s₁ inter s₂) = 0) (h' : μ s₁ != ∞
· 使用定理 `MeasureTheory.measureReal_mono_null`：measureReal_mono_null (h : s₁ subse
teq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ != ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem measureReal_sdiff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  rcases eq_top_or_lt_top (μ s₁) with H | H
  · simp [measureReal_def, H, measure_sdiff_eq_top H h']
  · exact measureReal_sdiff_null' (measureReal_mono_null inter_subset_right h h') H.ne

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null := measureReal_sdiff_null
/-
**MeasureTheory.measureReal_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_add_sdiff (hs : MeasurableSet s) (h₁ : μ s != ∞
参数：hs : MeasurableSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_union'`：measureReal_union' (hd : Disjoint s₁ s
₂) (h : MeasurableSet s₁) (h₁ : μ s₁ != ∞
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
-/
theorem measureReal_add_sdiff (hs : MeasurableSet s)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real s + μ.real (t \ s) = μ.real (s ∪ t) := by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset sdiff_subset h₂), union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measureReal_add_diff := measureReal_add_sdiff
/-
**MeasureTheory.measureReal_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_sdiff' (hm : MeasurableSet t) (h₁ : μ s != ∞
参数：hm : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_add_sdiff`：measureReal_add_sdiff (hs : Measura
bleSet s) (h₁ : μ s != ∞
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
theorem measureReal_sdiff' (hm : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s \ t) = μ.real (s ∪ t) - μ.real t := by
  rw [union_comm, ← measureReal_add_sdiff hm h₂ h₁]
  ring

@[deprecated (since := "2026-06-03")] alias measureReal_diff' := measureReal_sdiff'
/-
**MeasureTheory.measureReal_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_sdiff (h : s₂ subseteq s₁) (h₂ : MeasurableSet s₂) (h₁ : μ s₁ 
!= ∞
参数：h : s₂ subseteq s₁；h₂ : MeasurableSet s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_sdiff'`：measureReal_sdiff' (hm : MeasurableSet
 t) (h₁ : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
-/
theorem measureReal_sdiff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂) (h₁ : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
  rw [measureReal_sdiff' h₂ h₁ (measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measureReal_diff := measureReal_sdiff
/-
**MeasureTheory.le_measureReal_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_measureReal_sdiff (h : μ s₂ != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.measureReal_le_measureReal_union_right`：measureReal_le_mea
sureReal_union_right (h : μ s != ∞
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `MeasureTheory.measureReal_union_le`：measureReal_union_le (s₁ s₂ : Set α)
 : μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
-/
theorem le_measureReal_sdiff (h : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ - μ.real s₂ ≤ μ.real (s₁ \ s₂) := by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ ∪ s₁ \ s₂) := congr_arg μ.real union_sdiff_self.symm
    _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_measureReal_diff := le_measureReal_sdiff
/-
**MeasureTheory.measureReal_sdiff_lt_of_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measureReal_sdiff_lt_of_lt_add (hs : MeasurableSet s) (hst : s subseteq t)
 (ε : Real) (h : μ.real t < μ.real s + ε) (ht' : μ t != ∞
参数：hs : MeasurableSet s；hst : s subseteq t；ε : Real；h : μ.real t < μ.real s + ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_sdiff`：measureReal_sdiff (h : s₂ subseteq s₁) 
(h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 33 条，此处仅展示前 30 条）
-/
theorem measureReal_sdiff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (h : μ.real t < μ.real s + ε) (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) < ε := by
  rw [measureReal_sdiff hst hs ht']; linarith

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_lt_of_lt_add := measureReal_sdiff_lt_of_lt_add
/-
**MeasureTheory.measureReal_sdiff_le_iff_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measureReal_sdiff_le_iff_le_add (hs : MeasurableSet s) (hst : s subseteq t
) (ε : Real) (ht' : μ t != ∞
参数：hs : MeasurableSet s；hst : s subseteq t；ε : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_sdiff`：measureReal_sdiff (h : s₂ subseteq s₁) 
(h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measureReal_sdiff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) ≤ ε ↔ μ.real t ≤ μ.real s + ε := by
  rw [measureReal_sdiff hst hs ht', tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_le_iff_le_add := measureReal_sdiff_le_iff_le_add
/-
**MeasureTheory.measureReal_eq_measureReal_of_null_sdiff** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：measureReal_eq_measureReal_of_null_sdiff (hst : s subseteq t) (h_nulldiff 
: μ.real (t \ s) = 0) (h : μ (t \ s) != ∞
参数：hst : s subseteq t；h_nulldiff : μ.real (t \ s) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_measure_of_null_sdiff`：measure_eq_measure_of_nu
ll_sdiff {s t : Set α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0) : μ s 
= μ t
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_eq_measureReal_of_null_sdiff (hst : s ⊆ t)
    (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) ≠ ∞ := by finiteness) :
    μ.real s = μ.real t := by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_sdiff hst h_nulldiff]

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_of_null_diff := measureReal_eq_measureReal_of_null_sdiff
/-
**MeasureTheory.measureReal_eq_measureReal_of_between_null_sdiff** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_eq_measureReal_of_between_null_sdiff (h12 : s₁ subseteq s₂) (h
23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) != ∞
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nulldiff : μ.real (s₃ \ s₁) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_eq_measure_of_between_null_sdiff`：measure_eq_measu
re_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂) (h23 : s₂ sub
seteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem measureReal_eq_measureReal_of_between_null_sdiff
    (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_sdiff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]
/-
**MeasureTheory.measureReal_eq_measureReal_smaller_of_between_null_sdiff** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_eq_measureReal_smaller_of_between_null_sdiff (h12 : s₁ subsete
q s₂) (h23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s
₁) != ∞
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nulldiff : μ.real (s₃ \ s₁) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.measureReal_eq_measureReal_of_between_null_sdiff`：measureR
eal_eq_measureReal_of_between_null_sdiff (h12 : s₁ subseteq s₂) (h23 : s₂ subset
eq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (…
-/
theorem measureReal_eq_measureReal_smaller_of_between_null_sdiff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ :=
  (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').1

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_smaller_of_between_null_diff :=
  measureReal_eq_measureReal_smaller_of_between_null_sdiff
/-
**MeasureTheory.measureReal_eq_measureReal_larger_of_between_null_sdiff** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_eq_measureReal_larger_of_between_null_sdiff (h12 : s₁ subseteq
 s₂) (h23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁
) != ∞
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nulldiff : μ.real (s₃ \ s₁) = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.measureReal_eq_measureReal_of_between_null_sdiff`：measureR
eal_eq_measureReal_of_between_null_sdiff (h12 : s₁ subseteq s₂) (h23 : s₂ subset
eq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (…
-/
theorem measureReal_eq_measureReal_larger_of_between_null_sdiff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₂ = μ.real s₃ :=
  (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').2

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_larger_of_between_null_diff :=
  measureReal_eq_measureReal_larger_of_between_null_sdiff
/-
**MeasureTheory.measureReal_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) : μ.real sᶜ =
 μ.real univ - μ.real s
参数：h₁ : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `MeasureTheory.measureReal_sdiff`：measureReal_sdiff (h : s₂ subseteq s₁) 
(h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  rw [compl_eq_univ_sdiff]
  exact measureReal_sdiff (subset_univ s) h₁
/-
**MeasureTheory.measureReal_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) : μ.real sᶜ =
 μ.real univ - μ.real s
参数：h₁ : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `MeasureTheory.measureReal_sdiff`：measureReal_sdiff (h : s₂ subseteq s₁) 
(h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem measureReal_compl₀ [IsFiniteMeasure μ] (h₁ : NullMeasurableSet s μ) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  linarith [measureReal_add_measureReal_compl₀ h₁]
/-
**MeasureTheory.measureReal_union_congr_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measureReal_union_congr_of_subset (hs : s₁ subseteq s₂) (hsμ : μ.real s₂ <
= μ.real s₁) (ht : t₁ subseteq t₂) (htμ : μ.real t₂ <= μ.real t₁) (h₁ : μ s₂ != 
∞
参数：hs : s₁ subseteq s₂；hsμ : μ.real s₂ <= μ.real s₁；ht : t₁ subseteq t₂；htμ : μ.
real t₂ <= μ.real t₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_union_congr_of_subset`：measure_union_congr_of_subs
et {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁) (ht : t₁ subseteq 
t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
-/
theorem measureReal_union_congr_of_subset (hs : s₁ ⊆ s₂)
    (hsμ : μ.real s₂ ≤ μ.real s₁) (ht : t₁ ⊆ t₂) (htμ : μ.real t₂ ≤ μ.real t₁)
    (h₁ : μ s₂ ≠ ∞ := by finiteness) (h₂ : μ t₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ t₁) = μ.real (s₂ ∪ t₂) := by
  simp only [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ
/-
**MeasureTheory.sum_measureReal_le_measureReal_univ** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t 
: ι -> Set α} (h : forall i in s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint
 (↑s) t) : (∑ i in s, μ.real (t i)) <= μ.real univ
参数：h : forall i in s, MeasurableSet (t i)；H : Set.PairwiseDisjoint (↑s) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.sum_measure_le_measure_univ`：sum_measure_le_measure_univ {
s : Finset ι} {t : ι -> Set α} (h : forall i in s, NullMeasurableSet (t i) μ) (H
 : Set.Pairwise s (AEDisjoint μ…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
-/
theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i ∈ s, μ.real (t i)) ≤ μ.real univ := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (by finiteness)]
  apply ENNReal.toReal_mono (by finiteness)
  exact sum_measure_le_measure_univ (fun i mi ↦ (h i mi).nullMeasurableSet) H.aedisjoint
/-
**MeasureTheory.measureReal_add_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_add_apply {μ₁ μ₂ : Measure α} (h₁ : μ₁ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_add_apply {μ₁ μ₂ : Measure α} (h₁ : μ₁ s ≠ ∞ := by finiteness)
    (h₂ : μ₂ s ≠ ∞ := by finiteness) :
    (μ₁ + μ₂).real s = μ₁.real s + μ₂.real s := by
  simp only [measureReal_def, add_apply, ENNReal.toReal_add h₁ h₂]

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty. -/
/-
**MeasureTheory.exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal [IsFiniteMeas
ure μ] {s : Finset ι} {t : ι -> Set α} (h : forall i in s, MeasurableSet (t i)) 
(H : μ.real univ < ∑ i in s, μ.real (t i)) : exists i in s, exists j in s, exist
s _h : i != j, (t i inter t j).Nonempty
参数：h : forall i in s, MeasurableSet (t i)；H : μ.real univ < ∑ i in s, μ.real (t 
i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`：exis
ts_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Me
asure α) {s : Finset ι} {t : ι -> Set α} (h : forall i i…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …

--- 原说明 ---
Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j`
 is not empty.
-/
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal [IsFiniteMeasure μ]
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ.real univ < ∑ i ∈ s, μ.real (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i mi ↦ (h i mi).nullMeasurableSet)
  simp only [Measure.real] at H
  apply (ENNReal.toReal_lt_toReal (by finiteness) _).1
  · convert! H
    rw [ENNReal.toReal_sum (by finiteness)]
  · exact (ENNReal.sum_lt_top.mpr (fun i hi ↦ measure_lt_top ..)).ne

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `t` is measurable. -/
/-
**MeasureTheory.nonempty_inter_of_measureReal_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：nonempty_inter_of_measureReal_lt_add (ht : MeasurableSet t) (h's : s subse
teq u) (h't : t subseteq u) (h : μ.real u < μ.real s + μ.real t) (hu : μ u != ∞
参数：ht : MeasurableSet t；h's : s subseteq u；h't : t subseteq u；h : μ.real u < μ.r
eal s + μ.real t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_inter_of_measure_lt_add`：nonempty_inter_of_measur
e_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α} (ht : Measurabl
eSet t) (h's : s subseteq u) (h't : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal

--- 原说明 ---
If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `t` is measurable.
-/
theorem nonempty_inter_of_measureReal_lt_add
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `s` is measurable. -/
/-
**MeasureTheory.nonempty_inter_of_measureReal_lt_add'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：nonempty_inter_of_measureReal_lt_add' (hs : MeasurableSet s) (h's : s subs
eteq u) (h't : t subseteq u) (h : μ.real u < μ.real s + μ.real t) (hu : μ u != ∞
参数：hs : MeasurableSet s；h's : s subseteq u；h't : t subseteq u；h : μ.real u < μ.r
eal s + μ.real t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.nonempty_inter_of_measureReal_lt_add`：nonempty_inter_of_me
asureReal_lt_add (ht : MeasurableSet t) (h's : s subseteq u) (h't : t subseteq u
) (h : μ.real u < μ.real s + μ.real t) (…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `s` is measurable.
-/
theorem nonempty_inter_of_measureReal_lt_add'
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add hs h't h's h hu

variable [IsProbabilityMeasure μ]
/-
**MeasureTheory.probReal_compl_eq_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：probReal_compl_eq_one_sub (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real 
s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.probReal_compl_eq_one_sub₀`：probReal_compl_eq_one_sub₀ (h 
: NullMeasurableSet s μ) : μ.real sᶜ = 1 - μ.real s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma probReal_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ.real sᶜ = 1 - μ.real s := by
  rw [measureReal_compl₀ h, probReal_univ]
/-
**MeasureTheory.probReal_compl_eq_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：probReal_compl_eq_one_sub (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real 
s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.probReal_compl_eq_one_sub₀`：probReal_compl_eq_one_sub₀ (h 
: NullMeasurableSet s μ) : μ.real sᶜ = 1 - μ.real s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma probReal_compl_eq_one_sub (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real s :=
  probReal_compl_eq_one_sub₀ hs.nullMeasurableSet

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
@[positivity MeasureTheory.Measure.real _ _]
meta def evalMeasureReal : PositivityExt where eval {_ _} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

