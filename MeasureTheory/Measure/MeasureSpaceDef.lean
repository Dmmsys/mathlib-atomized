/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Induced
public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Measure spaces

This file defines measure spaces, the almost-everywhere filter and `AEMeasurable` functions.
See `MeasureTheory.MeasureSpace` for their properties and for extended documentation.

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the sum of the measures of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, an outer measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

See the documentation of `MeasureTheory.MeasureSpace` for ways to construct measures and proving
that two measures are equal.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

This file does not import `MeasureTheory.MeasurableSpace.Basic`, but only `MeasurableSpace.Defs`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/

@[expose] public section

assert_not_exists Module.Basis

noncomputable section

open Set Function MeasurableSpace Topology Filter ENNReal NNReal

open Filter hiding map

variable {α β γ δ : Type*} {ι : Sort*}

namespace MeasureTheory

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

The measure of a set `s`, denoted `μ s`, is an extended nonnegative real. The real-valued version
is written `μ.real s`.
-/
/-
**MeasureTheory.Measure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：(α : Type u_6) → [MeasurableSpace α] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the ca
nonical
extension of the restricted measure.

The measure of a set `s`, denoted `μ s`, is an extended nonnegative real. The re
al-valued version
is written `μ.real s`.
-/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim ≤ toOuterMeasure

/-- Notation for `Measure` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measure[" mα "] " α:arg => @Measure α mα

/-
**MeasureTheory.Measure.toOuterMeasure_injective** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α], Function.Injective MeasureThe
ory.Measure.toOuterMeasure
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measure.toOuterMeasure_injective [MeasurableSpace α] :
    Injective (toOuterMeasure : Measure α → OuterMeasure α)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
/-
**MeasureTheory.Measure.instFunLike** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：{α : Type u_1} → [inst : MeasurableSpace α] → FunLike (MeasureTheory.Measu
re α) (Set α) ENNReal
参数：MeasureTheory.Measure α；Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Measure.instFunLike [MeasurableSpace α] : FunLike (Measure α) (Set α) ℝ≥0∞ where
  coe μ := μ.toOuterMeasure
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective <| DFunLike.coe_injective h
/-
**MeasureTheory.Measure.instOuterMeasureClass** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α], MeasureTheory.OuterMeasureCla
ss (MeasureTheory.Measure α) α
参数：MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `MeasureTheory.OuterMeasure.iUnion_nat`：∀ {α : Type u_2} (self : MeasureT
heory.OuterMeasure α) (s : ℕ → Set α),   Pairwise (Function.onFun Disjoint s) → 
self.measureOf (⋃ i, s i) ≤…
-/
instance Measure.instOuterMeasureClass [MeasurableSpace α] : OuterMeasureClass (Measure α) α where
  measure_empty m := measure_empty (μ := m.toOuterMeasure)
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

/-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`.
The API is developed in `Mathlib/MeasureTheory/Measure/Real.lean`. -/
/-
**MeasureTheory.Measure.real** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{α : Type u_6} → {m : MeasurableSpace α} → MeasureTheory.Measure α → Set α
 → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real-valued version of a measure. Maps infinite measure sets to zero. Use as
 `μ.real s`.
The API is developed in `Mathlib/MeasureTheory/Measure/Real.lean`.
-/
protected def Measure.real {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) : ℝ :=
  (μ s).toReal
/-
**MeasureTheory.measureReal_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measureReal_def {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : S
et α) : μ.real s = (μ s).toReal
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measureReal_def {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.real s = (μ s).toReal := rfl

alias Measure.real_def := measureReal_def

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

namespace Measure

/-
**MeasureTheory.Measure.trimmed** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：trimmed (μ : Measure α) : μ.toOuterMeasure.trim = μ.toOuterMeasure
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.trim_le`：∀ {α : Type u_6} [inst : MeasurableSpace 
α] (self : MeasureTheory.Measure α), self.trim ≤ self.toOuterMeasure
· 使用定理 `MeasureTheory.OuterMeasure.le_trim`：le_trim : m <= m.trim
-/
theorem trimmed (μ : Measure α) : μ.toOuterMeasure.trim = μ.toOuterMeasure :=
  le_antisymm μ.trim_le μ.1.le_trim

/-! ### General facts about measures -/

/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
/-
**MeasureTheory.Measure.ofMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：ofMeasurable (m : forall s : Set α, MeasurableSet s -> Real>=0∞) (m0 : m ∅
 MeasurableSet.empty = 0) (mU : forall ⦃f : Nat -> Set α⦄ (h : forall i, Measura
bleSet (f i)), Pairwise (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUnion h)
 = ∑' i, m (f i) (h i)) : Measure α
参数：m : forall s : Set α, MeasurableSet s -> Real>=0∞；m0 : m ∅ MeasurableSet.empt
y = 0；mU : forall ⦃f : Nat -> Set α⦄ (h : forall i, MeasurableSet (f i)), Pairwi
se (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i
)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
Obtain a measure by giving a countably additive function that sends `∅` to `0`.
-/
def ofMeasurable (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  { toOuterMeasure := inducedOuterMeasure m _ m0
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU (MeasurableSet.iUnion hf), mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs ↦ by
      rw [OuterMeasure.trim_eq _ hs, inducedOuterMeasure_eq m0 mU hs] }
/-
**MeasureTheory.Measure.ofMeasurable_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：ofMeasurable_apply {m : forall s : Set α, MeasurableSet s -> Real>=0∞} {m0
 : m ∅ MeasurableSet.empty = 0} {mU : forall ⦃f : Nat -> Set α⦄ (h : forall i, M
easurableSet (f i)), Pairwise (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUn
ion h) = ∑' i, m (f i) (h i)} (s : Set α) (hs : MeasurableSet s) : ofMeasurable 
m m0 mU s = m s hs
参数：h : forall i, MeasurableSet (f i)；Disjoint on f；⋃ i, f i；MeasurableSet.iUnion
 h；f i；h i；s : Set α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq`：inducedOuterMeasure_eq {s : Set α}
 (hs : MeasurableSet s) : inducedOuterMeasure m MeasurableSet.empty m0 s = m s h
s
-/
theorem ofMeasurable_apply {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
    {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  inducedOuterMeasure_eq m0 mU hs

@[ext]
/-
**MeasureTheory.Measure.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：ext (h : forall s, MeasurableSet s -> μ₁ s = μ₂ s) : μ₁ = μ₂
参数：h : forall s, MeasurableSet s -> μ₁ s = μ₂ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
· 使用定理 `MeasureTheory.OuterMeasure.trim_congr`：trim_congr {m₁ m₂ : OuterMeasure 
α} (H : forall {s : Set α}, MeasurableSet s -> m₁ s = m₂ s) : m₁.trim = m₂.trim
-/
theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  toOuterMeasure_injective <| by
  rw [← trimmed, OuterMeasure.trim_congr (h _), trimmed]
/-
**MeasureTheory.Measure.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ext_iff' : μ₁ = μ₂ ↔ forall s, μ₁ s = μ₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
-/
theorem ext_iff' : μ₁ = μ₂ ↔ ∀ s, μ₁ s = μ₂ s :=
  ⟨by rintro rfl s; rfl, fun h ↦ Measure.ext (fun s _ ↦ h s)⟩
/-
**MeasureTheory.Measure.outerMeasure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：outerMeasure_le_iff {m : OuterMeasure α} : m <= μ.1 ↔ forall s, Measurable
Set s -> m s <= μ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
· 使用定理 `MeasureTheory.OuterMeasure.le_trim_iff`：le_trim_iff {m₁ m₂ : OuterMeasur
e α} : m₁ <= m₂.trim ↔ forall s, MeasurableSet s -> m₁ s <= m₂ s
-/
theorem outerMeasure_le_iff {m : OuterMeasure α} : m ≤ μ.1 ↔ ∀ s, MeasurableSet s → m s ≤ μ s := by
  simpa only [μ.trimmed] using! OuterMeasure.le_trim_iff (m₂ := μ.1)
/-
**MeasureTheory.Measure.mono_null** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：mono_null ⦃s t : Set α⦄ (h : s subseteq t) (ht : μ t = 0) : μ s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma mono_null ⦃s t : Set α⦄ (h : s ⊆ t) (ht : μ t = 0) : μ s = 0 := measure_mono_null h ht

end Measure

/-
**MeasureTheory.Measure.coe_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α),
 ⇑μ.toOuterMeasure = ⇑μ
参数：μ : MeasureTheory.Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Measure.coe_toOuterMeasure (μ : Measure α) : ⇑μ.toOuterMeasure = μ := rfl
/-
**MeasureTheory.Measure.toOuterMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α) 
(s : Set α), μ.toOuterMeasure s = μ s
参数：μ : MeasureTheory.Measure α；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measure.toOuterMeasure_apply (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s :=
  rfl
/-
**MeasureTheory.measure_eq_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
· 使用定理 `MeasureTheory.Measure.coe_toOuterMeasure`：∀ {α : Type u_1} [inst : Measu
rableSpace α] (μ : MeasureTheory.Measure α), ⇑μ.toOuterMeasure = ⇑μ
-/
theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by
  rw [μ.trimmed, μ.coe_toOuterMeasure]
/-
**MeasureTheory.measure_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (_ : s subseteq t) (_ : Measurab
leSet t), μ t
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_trim`：measure_eq_trim (s : Set α) : μ s = μ.toO
uterMeasure.trim s
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_iInf`：trim_eq_iInf (s : Set α) : m.tr
im s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
· 使用定理 `MeasureTheory.Measure.coe_toOuterMeasure`：∀ {α : Type u_1} [inst : Measu
rableSpace α] (μ : MeasureTheory.Measure α), ⇑μ.toOuterMeasure = ⇑μ
-/
theorem measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (_ : s ⊆ t) (_ : MeasurableSet t), μ t := by
  rw [measure_eq_trim, OuterMeasure.trim_eq_iInf, μ.coe_toOuterMeasure]

/-- A variant of `measure_eq_iInf` which has a single `iInf`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
/-
**MeasureTheory.measure_eq_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_iInf' (μ : Measure α) (s : Set α) : μ s = ⨅ t : { t // s subset
eq t ∧ MeasurableSet t }, μ t
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `measure_eq_iInf` which has a single `iInf`. This is useful when ap
plying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`.
-/
theorem measure_eq_iInf' (μ : Measure α) (s : Set α) :
    μ s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, μ t := by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]
/-
**MeasureTheory.measure_eq_inducedOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_eq_inducedOuterMeasure : μ s = inducedOuterMeasure (fun s _ => μ s
) MeasurableSet.empty μ.empty s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_eq_trim`：measure_eq_trim (s : Set α) : μ s = μ.toO
uterMeasure.trim s
-/
theorem measure_eq_inducedOuterMeasure :
    μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty s :=
  measure_eq_trim _
/-
**MeasureTheory.toOuterMeasure_eq_inducedOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：toOuterMeasure_eq_inducedOuterMeasure : μ.toOuterMeasure = inducedOuterMea
sure (fun s _ => μ s) MeasurableSet.empty μ.empty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.trimmed`：trimmed (μ : Measure α) : μ.toOuterMeasur
e.trim = μ.toOuterMeasure
-/
theorem toOuterMeasure_eq_inducedOuterMeasure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty :=
  μ.trimmed.symm
/-
**MeasureTheory.measure_eq_extend** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_extend (hs : MeasurableSet s) : μ s = extend (fun t (_ht : Meas
urableSet t) => μ t) s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.extend_eq`：extend_eq {s : α} (h : P s) : extend m s = m s 
h
-/
theorem measure_eq_extend (hs : MeasurableSet s) :
    μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s := by
  rw [extend_eq]
  exact hs
/-
**MeasureTheory.nonempty_of_measure_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：nonempty_of_measure_ne_zero (h : μ s != 0) : s.Nonempty
参数：h : μ s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ measure_empty
/-
**MeasureTheory.measure_mono_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_mono_top (h : s₁ subseteq s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞
参数：h : s₁ subseteq s₂；h₁ : μ s₁ = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
  top_unique <| h₁ ▸ measure_mono h

@[simp, mono]
/-
**MeasureTheory.measure_le_measure_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_le_measure_union_left : μ s <= μ (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem measure_le_measure_union_left : μ s ≤ μ (s ∪ t) := μ.mono subset_union_left

@[simp, mono]
/-
**MeasureTheory.measure_le_measure_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_le_measure_union_right : μ t <= μ (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem measure_le_measure_union_right : μ t ≤ μ (s ∪ t) := μ.mono subset_union_right

/-- For every set there exists a measurable superset of the same measure. -/
/-
**MeasureTheory.exists_measurable_superset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：exists_measurable_superset (μ : Measure α) (s : Set α) : exists t, s subse
teq t ∧ MeasurableSet t ∧ μ t = μ s
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim`：exists_me
asurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exists t, s subsete
q t ∧ MeasurableSet t ∧ m t = m.trim s

--- 原说明 ---
For every set there exists a measurable superset of the same measure.
-/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [← measure_eq_trim] using! μ.toOuterMeasure.exists_measurable_superset_eq_trim s

/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
/-
**MeasureTheory.exists_measurable_superset_forall_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：exists_measurable_superset_forall_eq [Countable ι] (μ : ι -> Measure α) (s
 : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ forall i, μ i t = μ i s
参数：μ : ι -> Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_forall_eq_trim`：ex
ists_measurable_superset_forall_eq_trim {ι} [Countable ι] (μ : ι -> OuterMeasure
 α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t…

--- 原说明 ---
For every set `s` and a countable collection of measures `μ i` there exists a me
asurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t
`.
-/
theorem exists_measurable_superset_forall_eq [Countable ι] (μ : ι → Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = μ i s := by
  simpa only [← measure_eq_trim] using!
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s
/-
**MeasureTheory.exists_measurable_superset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：exists_measurable_superset (μ : Measure α) (s : Set α) : exists t, s subse
teq t ∧ MeasurableSet t ∧ μ t = μ s
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim`：exists_me
asurable_superset_eq_trim (m : OuterMeasure α) (s : Set α) : exists t, s subsete
q t ∧ MeasurableSet t ∧ m t = m.trim s
-/
theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [Bool.forall_bool.trans and_comm] using!
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s
/-
**MeasureTheory.exists_measurable_superset_of_null** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_measurable_superset_of_null (h : μ s = 0) : exists t, s subseteq t 
∧ MeasurableSet t ∧ μ t = 0
参数：h : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
-/
theorem exists_measurable_superset_of_null (h : μ s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s
/-
**MeasureTheory.exists_measurable_superset_iff_measure_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measurable_superset_iff_measure_eq_zero : (exists t, s subseteq t ∧
 MeasurableSet t ∧ μ t = 0) ↔ μ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
-/
theorem exists_measurable_superset_iff_measure_eq_zero :
    (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩
/-
**MeasureTheory.measure_biUnion_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_biUnion_lt_top {s : Set β} {f : β -> Set α} (hs : s.Finite) (hfin 
: forall i in s, μ (f i) < ∞) : μ (⋃ i in s, f i) < ∞
参数：hs : s.Finite；hfin : forall i in s, μ (f i) < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_biUnion_finset_le`：measure_biUnion_finset_le (I : 
Finset ι) (s : ι -> Set α) : μ (⋃ i in I, s i) <= ∑ i in I, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem measure_biUnion_lt_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) < ∞) : μ (⋃ i ∈ s, f i) < ∞ := by
  convert! (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · simpa only [ENNReal.sum_lt_top, Finite.mem_toFinset]

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**MeasureTheory.measure_biUnion_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_biUnion_ne_top {s : Set β} {f : β -> Set α} (hs : s.Finite) (hfin 
: forall i in s, μ (f i) != ∞) : μ (⋃ i in s, f i) != ∞
参数：hs : s.Finite；hfin : forall i in s, μ (f i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem measure_biUnion_ne_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) ≠ ∞) : μ (⋃ i ∈ s, f i) ≠ ∞ :=
  (measure_biUnion_lt_top hs (fun i hi ↦ Ne.lt_top (hfin i hi ·))).ne
/-
**MeasureTheory.measure_union_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s union t) < ∞
参数：hs : μ s < ∞；ht : μ t < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
  (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]
/-
**MeasureTheory.measure_union_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_union_lt_top_iff : μ (s union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `MeasureTheory.measure_union_lt_top`：measure_union_lt_top (hs : μ s < ∞) 
(ht : μ t < ∞) : μ (s union t) < ∞
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**MeasureTheory.measure_union_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union_ne_top (hs : μ s != ∞) (ht : μ t != ∞) : μ (s union t) != ∞
参数：hs : μ s != ∞；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_union_lt_top`：measure_union_lt_top (hs : μ s < ∞) 
(ht : μ t < ∞) : μ (s union t) < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).ne

open scoped symmDiff in
@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
/-
**MeasureTheory.measure_symmDiff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_symmDiff_ne_top (hs : μ s != ∞) (ht : μ t != ∞) : μ (s ∆ t) != ∞
参数：hs : μ s != ∞；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.measure_union_ne_top`：measure_union_ne_top (hs : μ s != ∞)
 (ht : μ t != ∞) : μ (s union t) != ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.symmDiff_subset_union`：symmDiff_subset_union : s ∆ t subseteq s unio
n t
-/
theorem measure_symmDiff_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∆ t) ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) <| measure_mono symmDiff_subset_union

@[simp]
/-
**MeasureTheory.measure_union_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_union_eq_top_iff : μ (s union t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measure_union_eq_top_iff : μ (s ∪ t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
  not_iff_not.1 <| by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]
/-
**MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：exists_measure_pos_of_not_measure_iUnion_null [Countable ι] {s : ι -> Set 
α} (hs : μ (⋃ n, s n) != 0) : exists n, 0 < μ (s n)
参数：hs : μ (⋃ n, s n) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.measure_iUnion_null`：∀ {α : Type u_1} {F : Type u_3} [inst
 : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {ι
 : Sort u_4} [Countable…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem exists_measure_pos_of_not_measure_iUnion_null [Countable ι] {s : ι → Set α}
    (hs : μ (⋃ n, s n) ≠ 0) : ∃ n, 0 < μ (s n) := by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)
/-
**MeasureTheory.measure_lt_top_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_lt_top_of_subset (hst : t subseteq s) (hs : μ s != ∞) : μ t < ∞
参数：hst : t subseteq s；hs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem measure_lt_top_of_subset (hst : t ⊆ s) (hs : μ s ≠ ∞) : μ t < ∞ :=
  lt_of_le_of_lt (μ.mono hst) hs.lt_top
/-
**MeasureTheory.measure_ne_top_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_ne_top_of_subset (h : t subseteq s) (ht : μ s != ∞) : μ t != ∞
参数：h : t subseteq s；ht : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top_of_subset`：measure_lt_top_of_subset (hst : 
t subseteq s) (hs : μ s != ∞) : μ t < ∞
-/
theorem measure_ne_top_of_subset (h : t ⊆ s) (ht : μ s ≠ ∞) : μ t ≠ ∞ :=
  (measure_lt_top_of_subset h ht).ne

@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**MeasureTheory.measure_inter_ne_top_of_left_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：measure_inter_ne_top_of_left_ne_top (hs_finite : μ s != ∞) : μ (s inter t)
 != ∞
参数：hs_finite : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem measure_inter_ne_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) ≠ ∞ :=
  measure_ne_top_of_subset inter_subset_left hs_finite
/-
**MeasureTheory.measure_inter_lt_top_of_left_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：measure_inter_lt_top_of_left_ne_top (hs_finite : μ s != ∞) : μ (s inter t)
 < ∞
参数：hs_finite : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.measure_inter_ne_top_of_left_ne_top`：measure_inter_ne_top_
of_left_ne_top (hs_finite : μ s != ∞) : μ (s inter t) != ∞
-/
theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) < ∞ := by
  finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**MeasureTheory.measure_inter_ne_top_of_right_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：measure_inter_ne_top_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t
) != ∞
参数：ht_finite : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem measure_inter_ne_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) ≠ ∞ :=
  measure_ne_top_of_subset inter_subset_right ht_finite
/-
**MeasureTheory.measure_inter_lt_top_of_right_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：measure_inter_lt_top_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t
) < ∞
参数：ht_finite : μ t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.measure_inter_ne_top_of_right_ne_top`：measure_inter_ne_top
_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t) != ∞
-/
theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) < ∞ := by
  finiteness
/-
**MeasureTheory.measure_inter_null_of_null_right** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ
 (S inter T) = 0
参数：S : Set α；h : μ T = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_right h
/-
**MeasureTheory.measure_inter_null_of_null_left** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ 
(S inter T) = 0
参数：T : Set α；h : μ S = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_left h

/-! ### The almost everywhere filter -/
section ae

/-- Given a predicate on `β` and `Set α` where both `α` and `β` are measurable spaces, if the
predicate holds for almost every `x : β` and
- `∅ : Set α`
- a family of sets generating the σ-algebra of `α`

Moreover, if for almost every `x : β`, the predicate is closed under complements and countable
disjoint unions, then the predicate holds for almost every `x : β` and all measurable sets of `α`.

This is an AE version of `MeasurableSpace.induction_on_inter` where the condition is dependent
on a measurable space `β`. -/
/-
**MeasureTheory._root_.MeasurableSpace.ae_induction_on_inter** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate on `β` and `Set α` where both `α` and `β` are measurable space
s, if the
predicate holds for almost every `x : β` and
- `∅ : Set α`
- a family of sets generating the σ-algebra of `α`

Moreover, if for almost every `x : β`, the predicate is closed under complements
 and countable
disjoint unions, then the predicate holds for almost every `x : β` and all measu
rable sets of `α`.

This is an AE version of `MeasurableSpace.induction_on_inter` where the conditio
n is dependent
on a measurable space `β`.
-/
theorem _root_.MeasurableSpace.ae_induction_on_inter
    {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {C : β → Set α → Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s) (h_empty : ∀ᵐ x ∂μ, C x ∅) (h_basic : ∀ᵐ x ∂μ, ∀ t ∈ s, C x t)
    (h_compl : ∀ᵐ x ∂μ, ∀ t, MeasurableSet t → C x t → C x tᶜ)
    (h_union : ∀ᵐ x ∂μ, ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C x (f i)) → C x (⋃ i, f i)) :
    ∀ᵐ x ∂μ, ∀ ⦃t⦄, MeasurableSet t → C x t := by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter (C := fun t _ ↦ C x t)
      h_eq h_inter hx_empty hx_basic hx_compl hx_union

end ae

open scoped Classical in
/-- A measurable set `t ⊇ s` such that `μ t = μ s`. It even satisfies `μ (t ∩ u) = μ (s ∩ u)` for
any measurable set `u` if `μ s ≠ ∞`, see `measure_toMeasurable_inter`.
This property holds without the assumption `μ s ≠ ∞` when the space is s-finite (for example
σ-finite); see `measure_toMeasurable_inter_of_sFinite`.
If `s` is a null measurable set, then
we also have `t =ᵐ[μ] s`, see `NullMeasurableSet.toMeasurable_ae_eq`.
This notion is sometimes called a "measurable hull" in the literature. -/
irreducible_def toMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ t, t ⊇ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s then h.choose else
    if h' : ∃ t, t ⊇ s ∧ MeasurableSet t ∧
      ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then h'.choose
    else (exists_measurable_superset μ s).choose

/-
**MeasureTheory.subset_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：subset_toMeasurable (μ : Measure α) (s : Set α) : s subseteq toMeasurable 
μ s
参数：μ : Measure α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.toMeasurable_def`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (μ : MeasureTheory.Measure α) (s : Set α),   MeasureTheory.toMeasurable μ s 
=     if h : ∃ t ⊇ s…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem subset_toMeasurable (μ : Measure α) (s : Set α) : s ⊆ toMeasurable μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]
/-
**MeasureTheory.ae_le_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_toMeasurable : s <=ᵐ[μ] toMeasurable μ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
theorem ae_le_toMeasurable : s ≤ᵐ[μ] toMeasurable μ s :=
  LE.le.eventuallyLE (subset_toMeasurable _ _)

@[simp]
/-
**MeasureTheory.measurableSet_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurableSet_toMeasurable (μ : Measure α) (s : Set α) : MeasurableSet (to
Measurable μ s)
参数：μ : Measure α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.toMeasurable_def`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (μ : MeasureTheory.Measure α) (s : Set α),   MeasureTheory.toMeasurable μ s 
=     if h : ∃ t ⊇ s…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem measurableSet_toMeasurable (μ : Measure α) (s : Set α) :
    MeasurableSet (toMeasurable μ s) := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]

@[simp]
/-
**MeasureTheory.measure_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset`：exists_measurable_superset (μ 
: Measure α) (s : Set α) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.toMeasurable_def`：∀ {α : Type u_6} [inst : MeasurableSpace
 α] (μ : MeasureTheory.Measure α) (s : Set α),   MeasureTheory.toMeasurable μ s 
=     if h : ∃ t ⊇ s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2

/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
/-
**MeasureTheory.MeasureSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：Type u_6 → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure space is a measurable space equipped with a
  measure, referred to as `volume`.
-/
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α

export MeasureSpace (volume)

/-- `volume` is the canonical measure on `α`. -/
add_decl_doc volume

section MeasureSpace

/-- `∀ᵐ a, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "∀ᵐ "(...)", "r:(scoped P =>
  Filter.Eventually P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

/-- `∃ᵐ a, p a` means that `p` holds frequently, i.e. on a set of positive measure,
w.r.t. the volume measure.

This is notation for `Filter.Frequently P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "∃ᵐ "(...)", "r:(scoped P =>
  Filter.Frequently P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

/-- The tactic `exact volume`, to be used in optional (`autoParam`) arguments. -/
macro "volume_tac" : tactic =>
  `(tactic| exact MeasureTheory.MeasureSpace.volume)

end MeasureSpace

end

end MeasureTheory

section

open MeasureTheory

/-!
### Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `AEMeasurable f μ`. It's properties are discussed in
`MeasureTheory.MeasureSpace`.
-/


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ ν : Measure α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function.

A similar notion is `MeasureTheory.NullMeasurable`. That notion is equivalent to `AEMeasurable` if
the σ-algebra on the codomain is countably generated, but weaker in general. -/
@[fun_prop]
/-
**AEMeasurable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AEMeasurable {_m : MeasurableSpace α} (f : α -> β) (μ : Measure α
参数：f : α -> β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A function is almost everywhere measurable if it coincides almost everywhere wit
h a measurable
function.

A similar notion is `MeasureTheory.NullMeasurable`. That notion is equivalent to
 `AEMeasurable` if
the σ-algebra on the codomain is countably generated, but weaker in general.
-/
def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g

/-- A function is `m`-`AEMeasurable` with respect to a measure `μ` if it coincides almost everywhere
with a `m`-measurable function. -/
scoped[MeasureTheory] notation "AEMeasurable[" m "]" => @AEMeasurable _ _ _ m

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEMeasurable ..])
  (by fun_prop (disch := measurability))

@[fun_prop]
/-
**Measurable.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ
参数：h : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩

namespace AEMeasurable

@[fun_prop]
/-
**AEMeasurable.of_discrete** 是 Mathlib 中的一个引理，位于命名空间 `AEMeasurable`。
形式化陈述：of_discrete [DiscreteMeasurableSpace α] : AEMeasurable f μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
-/
lemma of_discrete [DiscreteMeasurableSpace α] : AEMeasurable f μ :=
  Measurable.of_discrete.aemeasurable

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
/-
**AEMeasurable.mk** 是 Mathlib 中的一个定义，位于命名空间 `AEMeasurable`。
形式化陈述：mk (f : α -> β) (h : AEMeasurable f μ) : α -> β
参数：f : α -> β；h : AEMeasurable f μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Given an almost everywhere measurable function `f`, associate to it a measurable
 function
that coincides with it almost everywhere. `f` is explicit in the definition to m
ake sure that
it shows in pretty-printing.
-/
def mk (f : α → β) (h : AEMeasurable f μ) : α → β :=
  Classical.choose h

@[fun_prop]
/-
**AEMeasurable.measurable_mk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f)
参数：h : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.choose_spec h).1
/-
**AEMeasurable.ae_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
参数：h : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.choose_spec h).2
/-
**AEMeasurable.congr** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ
参数：hf : AEMeasurable f μ；h : f =ᵐ[μ] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

end AEMeasurable

/-
**aemeasurable_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ
参数：h : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ :=
  ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩

@[simp, fun_prop]
/-
**aemeasurable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_const {b : β} : AEMeasurable (fun _a : α => b) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem aemeasurable_const {b : β} : AEMeasurable (fun _a : α => b) μ :=
  measurable_const.aemeasurable

@[fun_prop]
/-
**aemeasurable_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_id : AEMeasurable id μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem aemeasurable_id : AEMeasurable id μ :=
  measurable_id.aemeasurable

@[fun_prop]
/-
**aemeasurable_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_id' : AEMeasurable (fun x => x) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.aemeasurable
/-
**Measurable.comp_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α -> δ} {g : δ -> β}
 (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ
参数：hg : Measurable g；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : Measurable g)
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

@[fun_prop]
/-
**Measurable.comp_aemeasurable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.comp_aemeasurable' [MeasurableSpace δ] {f : α -> δ} {g : δ -> β
} (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) 
μ
参数：hg : Measurable g；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
-/
theorem Measurable.comp_aemeasurable' [MeasurableSpace δ] {f : α → δ} {g : δ → β}
    (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ g (f x)) μ :=
  Measurable.comp_aemeasurable hg hf

variable {δ : Type*} {X : δ → Type*} {mX : ∀ a, MeasurableSpace (X a)}
/-
**AEMeasurable.eval** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {δ 
: Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → MeasurableSpace (X a)} {g : α →
 (a : δ) → X a},   AEMeasurable g μ → ∀ (a : δ), AEMeasurable (fun x => g x a) μ
参数：a : δ；X a；a : δ；a : δ；fun x => g x a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.eval`：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : 
Measurable g) : Measurable fun x => g x a
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
protected theorem AEMeasurable.eval {g : α → Π a, X a} (hg : AEMeasurable g μ) (a : δ) :
    AEMeasurable (fun x ↦ g x a) μ := by
  use fun x ↦ hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h ↦ congrFun h _

variable [Countable δ]
/-
**aemeasurable_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_pi_iff {g : α -> Π a, X a} : AEMeasurable g μ ↔ forall a, AEM
easurable (fun x => g x a) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.eval`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure
Theory.Measure α} {δ : Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → Measurable
Space (…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem aemeasurable_pi_iff {g : α → Π a, X a} :
    AEMeasurable g μ ↔ ∀ a, AEMeasurable (fun x ↦ g x a) μ := by
  constructor
  · exact AEMeasurable.eval
  · intro h
    use fun x a ↦ (h a).mk _ x, measurable_pi_lambda _ fun a ↦ (h a).measurable_mk
    exact (eventually_countable_forall.mpr fun a ↦ (h a).ae_eq_mk).mono fun _ h ↦ funext h

@[fun_prop]
/-
**aemeasurable_pi_lambda** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf : forall a, AEMeasurable (f
un c => f c a) μ) : AEMeasurable f μ
参数：f : α -> Π a, X a；hf : forall a, AEMeasurable (fun c => f c a) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_pi_iff`：aemeasurable_pi_iff {g : α -> Π a, X a} : AEMeasura
ble g μ ↔ forall a, AEMeasurable (fun x => g x a) μ
-/
theorem aemeasurable_pi_lambda (f : α → Π a, X a) (hf : ∀ a, AEMeasurable (fun c ↦ f c a) μ) :
    AEMeasurable f μ :=
  aemeasurable_pi_iff.mpr hf

end

