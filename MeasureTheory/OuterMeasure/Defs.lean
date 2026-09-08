/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real

/-!
# Definitions of an outer measure and the corresponding `FunLike` class

In this file we define `MeasureTheory.OuterMeasure α`
to be the type of outer measures on `α`.

An outer measure is a function `μ : Set α → ℝ≥0∞`,
from the powerset of a type to the extended nonnegative real numbers
that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union
   is at most the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

We also define a typeclass `MeasureTheory.OuterMeasureClass`.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/

public section

assert_not_exists Module.Basis IsTopologicalRing UniformSpace

open scoped ENNReal

variable {α : Type*}

namespace MeasureTheory

open scoped Function -- required for scoped `on` notation

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
/-
**MeasureTheory.OuterMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An outer measure is a countably subadditive monotone function that sends `∅` to 
`0`.
-/
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)

attribute [gcongr] OuterMeasure.mono

/-- A mixin class saying that elements `μ : F` are outer measures on `α`.

This typeclass is used to unify some API for outer measures and measures. -/
/-
**MeasureTheory.OuterMeasureClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：(F : Type u_2) → (α : outParam (Type u_3)) → [FunLike F (Set α) ENNReal] →
 Prop
参数：Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin class saying that elements `μ : F` are outer measures on `α`.

This typeclass is used to unify some API for outer measures and measures.
-/
class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) ℝ≥0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)

attribute [gcongr] OuterMeasureClass.measure_mono

namespace OuterMeasure

/-
**MeasureTheory.OuterMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.OuterMeas
ure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (OuterMeasure α) (Set α) ℝ≥0∞ where
  coe m := m.measureOf
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
/-
**MeasureTheory.OuterMeasure.measureOf_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：∀ {α : Type u_1} (m : MeasureTheory.OuterMeasure α), m.measureOf = ⇑m
参数：m : MeasureTheory.OuterMeasure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m := rfl
/-
**MeasureTheory.OuterMeasure.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Out
erMeasure`。
形式化陈述：∀ {α : Type u_1} (m : Set α → ENNReal) (h₁ : m ∅ = 0) (h₂ : ∀ {s₁ s₂ : Set
 α}, s₁ ⊆ s₂ → m s₁ ≤ m s₂)   (h₃ : ∀ (s : ℕ → Set α), Pairwise (Function.onFun 
Disjoint s) → m (⋃ i, s i) ≤ ∑' (i : ℕ), m (s i)),   ⇑{ measureOf := m, empty :=
 h₁, mono := h₂, iUnion_nat := h₃ } = m
参数：m : Set α → ENNReal；h₁ : m ∅ = 0；h₂ : ∀ {s₁ s₂ : Set α}, s₁ ⊆ s₂ → m s₁ ≤ m s
₂；h₃ : ∀ (s : ℕ → Set α), Pairwise (Function.onFun Disjoint s) → m (⋃ i, s i) ≤ 
∑' (i : ℕ), m (s i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (m : Set α → ℝ≥0∞) (h₁ h₂ h₃) : OuterMeasure.mk m h₁ h₂ h₃ = m := rfl
/-
**MeasureTheory.OuterMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.OuterMeas
ure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OuterMeasureClass (OuterMeasure α) α where
  measure_empty f := f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

end OuterMeasure

end MeasureTheory

