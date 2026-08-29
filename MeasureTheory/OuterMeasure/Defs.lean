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

/--
Definition of `OuterMeasure` / `OuterMeasure` 的定义

English:
structure OuterMeasure
  parameters: (α : Type*)
  axioms and operations (4):
    - measureOf : Set α -> Real>=0∞
    - empty : measureOf ∅ = 0
    - mono : forall {s₁ s₂}, s₁ subseteq s₂ -> measureOf s₁ <= measureOf s₂
    - iUnion_nat : forall s : Nat -> Set α, Pairwise (Disjoint on s) -> measureOf (⋃ i, s i) <= ∑' i, measureOf (s i)

中文:
结构 OuterMeasure
  参数: (α : 类型)
  公理与运算 (4 个):
    - measureOf : Set α -> 实数>=0∞
    - empty : measureOf ∅ = 0
    - mono : 对任意 {s₁ s₂}, s₁ subseteq s₂ -> measureOf s₁ <= measureOf s₂
    - iUnion_nat : 对任意 s : 自然数 -> Set α, Pairwise (Disjoint on s) -> measureOf (⋃ i, s i) <= ∑' i, measureOf (s i)
-/
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α -> Real>=0∞
  protected empty : measureOf ∅ = 0
  protected mono : forall {s₁ s₂}, s₁ subseteq s₂ -> measureOf s₁ <= measureOf s₂
  protected iUnion_nat : forall s : Nat -> Set α, Pairwise (Disjoint on s) ->
    measureOf (⋃ i, s i) <= ∑' i, measureOf (s i)

attribute [gcongr] OuterMeasure.mono

/--
Definition of `OuterMeasureClass` / `OuterMeasureClass` 的定义

English:
class OuterMeasureClass
  parameters: (F : Type*) (α : outParam Type*) [FunLike F (Set α) Real>=0∞]
  axioms and operations (3):
    - measure_empty((f : F)) : f ∅ = 0
    - measure_mono((f : F) {s t}) : s subseteq t -> f s <= f t
    - measure_iUnion_nat_le((f : F) (s : Nat -> Set α)) : Pairwise (Disjoint on s) -> f (⋃ i, s i) <= ∑' i, f (s i)

中文:
类 OuterMeasureClass
  参数: (F : 类型) (α : outParam 类型) [FunLike F (Set α) 实数>=0∞]
  公理与运算 (3 个):
    - measure_empty((f : F)) : f ∅ = 0
    - measure_mono((f : F) {s t}) : s subseteq t -> f s <= f t
    - measure_iUnion_nat_le((f : F) (s : 自然数 -> Set α)) : Pairwise (Disjoint on s) -> f (⋃ i, s i) <= ∑' i, f (s i)
-/
class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) Real>=0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s subseteq t -> f s <= f t
  protected measure_iUnion_nat_le (f : F) (s : Nat -> Set α) : Pairwise (Disjoint on s) ->
    f (⋃ i, s i) <= ∑' i, f (s i)

attribute [gcongr] OuterMeasureClass.measure_mono

namespace OuterMeasure

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (OuterMeasure α) (Set α) Real>=0∞
  body: m.measureOf
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

中文:
实例 :
  签名: FunLike (OuterMeasure α) (Set α) 实数>=0∞
  定义体: m.measureOf
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

Depends on / 依赖: m.measureOf, measureOf
-/
instance : FunLike (OuterMeasure α) (Set α) Real>=0∞ where
  coe m := m.measureOf
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/--
theorem `measureOf_eq_coe` / 定理 `measureOf_eq_coe`

English:
theorem measureOf_eq_coe
  given: (m : OuterMeasure α)
  statement: m.measureOf = m
  proof: rfl

中文:
定理 measureOf_eq_coe
  条件: (m : OuterMeasure α)
  结论: m.measureOf = m
  证明: rfl
-/
@[simp] theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m := rfl
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (m : Set α -> Real>=0∞) (h₁ h₂ h₃)
  statement: OuterMeasure.mk m h₁ h₂ h₃ = m
  proof: rfl

中文:
定理 coe_mk
  条件: (m : Set α -> 实数>=0∞) (h₁ h₂ h₃)
  结论: OuterMeasure.mk m h₁ h₂ h₃ = m
  证明: rfl
-/
@[simp] theorem coe_mk (m : Set α -> Real>=0∞) (h₁ h₂ h₃) : OuterMeasure.mk m h₁ h₂ h₃ = m := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OuterMeasureClass (OuterMeasure α) α
  body: f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

中文:
实例 :
  签名: OuterMeasureClass (OuterMeasure α) α
  定义体: f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

Depends on / 依赖: f.empty
-/
instance : OuterMeasureClass (OuterMeasure α) α where
  measure_empty f := f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

end OuterMeasure

end MeasureTheory
