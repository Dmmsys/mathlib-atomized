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

/--
Definition of `Measure` / `Measure` 的定义

English:
structure Measure
  parameters: (α : Type*) [MeasurableSpace α]
  extends: OuterMeasure α
  axioms and operations (2):
    - m_iUnion(⦃f) : Nat -> Set α⦄ : (forall i, MeasurableSet (f i)) -> Pairwise (Disjoint on f) -> toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
    - trim_le : toOuterMeasure.trim <= toOuterMeasure

中文:
结构 测度
  参数: (α : 类型) [可测空间 α]
  继承: 外测度 α
  公理与运算 (2 个):
    - m_iUnion(⦃f) : 自然数 -> 集合 α⦄ : (对任意 i, 可测集 (f i)) -> 两两 (Disjoint on f) -> toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
    - trim_le : toOuterMeasure.trim <= toOuterMeasure
-/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : Nat -> Set α⦄ : (forall i, MeasurableSet (f i)) -> Pairwise (Disjoint on f) ->
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim <= toOuterMeasure

/-- Notation for `Measure` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measure[" mα "] " α:arg => @Measure α mα

/--
theorem `Measure.toOuterMeasure_injective` / 定理 `Measure.toOuterMeasure_injective`

English:
theorem Measure.toOuterMeasure_injective
  given: [MeasurableSpace α]

中文:
定理 测度.toOuterMeasure_injective
  条件: [可测空间 α]
-/
theorem Measure.toOuterMeasure_injective [MeasurableSpace α] :
    Injective (toOuterMeasure : Measure α -> OuterMeasure α)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/--
Instance `Measure.instFunLike` / 实例 `Measure.instFunLike`

English:
instance Measure.instFunLike
  signature: [MeasurableSpace α]
  body: μ.toOuterMeasure
coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective DFunLike.coe_injective h

中文:
实例 测度.instFunLike
  签名: [可测空间 α]
  定义体: μ.toOuterMeasure
coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective DFunLike.coe_injective h

Depends on / 依赖: toOuterMeasure
-/
instance Measure.instFunLike [MeasurableSpace α] : FunLike (Measure α) (Set α) Real>=0∞ where
  coe μ := μ.toOuterMeasure
coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective DFunLike.coe_injective h


/--
Instance `Measure.instOuterMeasureClass` / 实例 `Measure.instOuterMeasureClass`

English:
instance Measure.instOuterMeasureClass
  signature: [MeasurableSpace α]
  body: measure_empty (μ := m.toOuterMeasure)
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

中文:
实例 测度.instOuterMeasureClass
  签名: [可测空间 α]
  定义体: measure_empty (μ := m.toOuterMeasure)
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

Depends on / 依赖: m.toOuterMeasure, measure_empty, toOuterMeasure
-/
instance Measure.instOuterMeasureClass [MeasurableSpace α] : OuterMeasureClass (Measure α) α where
  measure_empty m := measure_empty (μ := m.toOuterMeasure)
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

/--
Definition of `Measure.real` / `Measure.real` 的定义

English:
definition Measure.real
  signature: {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α)
  body: (μ s).toReal

中文:
定义 测度.real
  签名: {α : 类型} {m : 可测空间 α} (μ : 测度 α) (s : 集合 α)
  定义体: (μ s).toReal
-/
protected def Measure.real {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) : Real :=
  (μ s).toReal

/--
theorem `measureReal_def` / 定理 `measureReal_def`

English:
theorem measureReal_def
  given: {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α)
  proof: rfl

alias Measure.real_def := measureReal_def

中文:
定理 measure实数_def
  条件: {α : 类型} {m : 可测空间 α} (μ : 测度 α) (s : 集合 α)
  证明: rfl

alias Measure.real_def := measureReal_def
-/
theorem measureReal_def {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.real s = (μ s).toReal := rfl

alias Measure.real_def := measureReal_def

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

namespace Measure

/--
theorem `trimmed` / 定理 `trimmed`

English:
theorem trimmed
  given: (μ : Measure α)
  statement: μ.toOuterMeasure.trim = μ.toOuterMeasure
  proof: le_antisymm μ.trim_le μ.1.le_trim

中文:
定理 trimmed
  条件: (μ : 测度 α)
  结论: μ.toOuterMeasure.trim = μ.toOuterMeasure
  证明: le_antisymm μ.trim_le μ.1.le_trim

Depends on / 依赖: le_antisymm, le_trim, trim_le
-/
theorem trimmed (μ : Measure α) : μ.toOuterMeasure.trim = μ.toOuterMeasure :=
  le_antisymm μ.trim_le μ.1.le_trim

/-! ### General facts about measures -/

/--
Definition of `ofMeasurable` / `ofMeasurable` 的定义

English:
definition ofMeasurable
  signature: (m : forall s : Set α, MeasurableSet s -> Real>=0∞) (m0 : m ∅ MeasurableSet.empty = 0)
  body: { toOuterMeasure := inducedOuterMeasure m _ m0
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU (MeasurableSet.iUnion hf)]; rw [mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs => by
      rw [OuterMeasure.trim_eq _ hs]; rw [inducedOuterMeasure_eq m0 mU hs] }

中文:
定义 ofMeasurable
  签名: (m : 对任意 s : 集合 α, 可测集 s -> 实数>=0∞) (m0 : m ∅ 可测集.empty = 0)
  定义体: { toOuterMeasure := inducedOuterMeasure m _ m0
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU (MeasurableSet.iUnion hf)]; rw [mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs => by
      rw [OuterMeasure.trim_eq _ hs]; rw [inducedOuterMeasure_eq m0 mU hs] }

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, OuterMeasure, OuterMeasure.trim_eq, iUnion, inducedOuterMeasure, inducedOuterMeasure_eq, le_inducedOuterMeasure, m_iUnion, toOuterMeasure, trim_eq, trim_le
-/
def ofMeasurable (m : forall s : Set α, MeasurableSet s -> Real>=0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      forall ⦃f : Nat -> Set α⦄ (h : forall i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  { toOuterMeasure := inducedOuterMeasure m _ m0
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU (MeasurableSet.iUnion hf)]; rw [mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs => by
      rw [OuterMeasure.trim_eq _ hs]; rw [inducedOuterMeasure_eq m0 mU hs] }

/--
theorem `ofMeasurable_apply` / 定理 `ofMeasurable_apply`

English:
theorem ofMeasurable_apply
  statement: {m : forall s : Set α, MeasurableSet s -> Real>=0∞}
  proof: inducedOuterMeasure_eq m0 mU hs

@[ext]

中文:
定理 ofMeasurable_apply
  结论: {m : 对任意 s : 集合 α, 可测集 s -> 实数>=0∞}
  证明: inducedOuterMeasure_eq m0 mU hs

@[ext]

Depends on / 依赖: inducedOuterMeasure_eq
-/
theorem ofMeasurable_apply {m : forall s : Set α, MeasurableSet s -> Real>=0∞}
    {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      forall ⦃f : Nat -> Set α⦄ (h : forall i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) -> m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  inducedOuterMeasure_eq m0 mU hs

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall s, MeasurableSet s -> μ₁ s = μ₂ s)
  statement: μ₁ = μ₂
  proof: toOuterMeasure_injective by
  rw [← trimmed]; rw [OuterMeasure.trim_congr (h _)]; rw [trimmed]

中文:
定理 ext
  条件: (h : 对任意 s, 可测集 s -> μ₁ s = μ₂ s)
  结论: μ₁ = μ₂
  证明: toOuterMeasure_injective by
  rw [← trimmed]; rw [OuterMeasure.trim_congr (h _)]; rw [trimmed]

Depends on / 依赖: OuterMeasure, OuterMeasure.trim_congr, toOuterMeasure_injective, trim_congr, trimmed
-/
theorem ext (h : forall s, MeasurableSet s -> μ₁ s = μ₂ s) : μ₁ = μ₂ :=
toOuterMeasure_injective by
  rw [← trimmed]; rw [OuterMeasure.trim_congr (h _)]; rw [trimmed]

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  statement: μ₁ = μ₂ ↔ forall s, μ₁ s = μ₂ s
  proof: ⟨by rintro rfl s; rfl, fun h => Measure.ext (fun s _ => h s)⟩

中文:
定理 ext_iff'
  结论: μ₁ = μ₂ ↔ 对任意 s, μ₁ s = μ₂ s
  证明: ⟨by rintro rfl s; rfl, fun h => Measure.ext (fun s _ => h s)⟩

Depends on / 依赖: Measure, Measure.ext
-/
theorem ext_iff' : μ₁ = μ₂ ↔ forall s, μ₁ s = μ₂ s :=
  ⟨by rintro rfl s; rfl, fun h => Measure.ext (fun s _ => h s)⟩

/--
theorem `outerMeasure_le_iff` / 定理 `outerMeasure_le_iff`

English:
theorem outerMeasure_le_iff
  given: {m : OuterMeasure α}
  statement: m <= μ.1 ↔ forall s, MeasurableSet s -> m s <= μ s
  proof: by
  simpa only [μ.trimmed] using! OuterMeasure.le_trim_iff (m₂ := μ.1)

中文:
定理 outerMeasure_le_iff
  条件: {m : 外测度 α}
  结论: m <= μ.1 ↔ 对任意 s, 可测集 s -> m s <= μ s
  证明: by
  simpa only [μ.trimmed] using! OuterMeasure.le_trim_iff (m₂ := μ.1)

Depends on / 依赖: OuterMeasure, OuterMeasure.le_trim_iff, le_trim_iff, trimmed
-/
theorem outerMeasure_le_iff {m : OuterMeasure α} : m <= μ.1 ↔ forall s, MeasurableSet s -> m s <= μ s := by
  simpa only [μ.trimmed] using! OuterMeasure.le_trim_iff (m₂ := μ.1)

/--
lemma `mono_null` / 引理 `mono_null`

English:
lemma mono_null
  given: ⦃s t
  statement: Set α⦄ (h : s subseteq t) (ht : μ t = 0) : μ s = 0
  proof: measure_mono_null h ht

中文:
引理 mono_null
  条件: ⦃s t
  结论: 集合 α⦄ (h : s subseteq t) (ht : μ t = 0) : μ s = 0
  证明: measure_mono_null h ht

Depends on / 依赖: measure_mono_null
-/
lemma mono_null ⦃s t : Set α⦄ (h : s subseteq t) (ht : μ t = 0) : μ s = 0 := measure_mono_null h ht

end Measure

/--
theorem `Measure.coe_toOuterMeasure` / 定理 `Measure.coe_toOuterMeasure`

English:
theorem Measure.coe_toOuterMeasure
  given: (μ : Measure α)
  statement: ⇑μ.toOuterMeasure = μ
  proof: rfl

中文:
定理 测度.coe_toOuterMeasure
  条件: (μ : 测度 α)
  结论: ⇑μ.toOuterMeasure = μ
  证明: rfl
-/
@[simp] theorem Measure.coe_toOuterMeasure (μ : Measure α) : ⇑μ.toOuterMeasure = μ := rfl

/--
theorem `Measure.toOuterMeasure_apply` / 定理 `Measure.toOuterMeasure_apply`

English:
theorem Measure.toOuterMeasure_apply
  given: (μ : Measure α) (s : Set α)
  proof: rfl

中文:
定理 测度.toOuterMeasure_apply
  条件: (μ : 测度 α) (s : 集合 α)
  证明: rfl
-/
theorem Measure.toOuterMeasure_apply (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s :=
  rfl

/--
theorem `measure_eq_trim` / 定理 `measure_eq_trim`

English:
theorem measure_eq_trim
  given: (s : Set α)
  statement: μ s = μ.toOuterMeasure.trim s
  proof: by
  rw [μ.trimmed]; rw [μ.coe_toOuterMeasure]

中文:
定理 measure_eq_trim
  条件: (s : 集合 α)
  结论: μ s = μ.toOuterMeasure.trim s
  证明: by
  rw [μ.trimmed]; rw [μ.coe_toOuterMeasure]

Depends on / 依赖: coe_toOuterMeasure, trimmed
-/
theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by
  rw [μ.trimmed]; rw [μ.coe_toOuterMeasure]

/--
theorem `measure_eq_iInf` / 定理 `measure_eq_iInf`

English:
theorem measure_eq_iInf
  given: (s : Set α)
  statement: μ s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), μ t
  proof: by
  rw [measure_eq_trim]; rw [OuterMeasure.trim_eq_iInf]; rw [μ.coe_toOuterMeasure]

中文:
定理 measure_eq_iInf
  条件: (s : 集合 α)
  结论: μ s = ⨅ (t) (_ : s subseteq t) (_ : 可测集 t), μ t
  证明: by
  rw [measure_eq_trim]; rw [OuterMeasure.trim_eq_iInf]; rw [μ.coe_toOuterMeasure]

Depends on / 依赖: OuterMeasure, OuterMeasure.trim_eq_iInf, coe_toOuterMeasure, measure_eq_trim, trim_eq_iInf
-/
theorem measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), μ t := by
  rw [measure_eq_trim]; rw [OuterMeasure.trim_eq_iInf]; rw [μ.coe_toOuterMeasure]

/--
theorem `measure_eq_iInf'` / 定理 `measure_eq_iInf'`

English:
theorem measure_eq_iInf'
  given: (μ : Measure α) (s : Set α)
  proof: by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]

中文:
定理 measure_eq_iInf'
  条件: (μ : 测度 α) (s : 集合 α)
  证明: by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]

Depends on / 依赖: iInf_and, iInf_subtype, measure_eq_iInf, simp_rw
-/
theorem measure_eq_iInf' (μ : Measure α) (s : Set α) :
    μ s = ⨅ t : { t // s subseteq t ∧ MeasurableSet t }, μ t := by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]

/--
theorem `measure_eq_inducedOuterMeasure` / 定理 `measure_eq_inducedOuterMeasure`

English:
theorem measure_eq_inducedOuterMeasure
  proof: measure_eq_trim _

中文:
定理 measure_eq_inducedOuterMeasure
  证明: measure_eq_trim _

Depends on / 依赖: measure_eq_trim
-/
theorem measure_eq_inducedOuterMeasure :
    μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty s :=
  measure_eq_trim _

/--
theorem `toOuterMeasure_eq_inducedOuterMeasure` / 定理 `toOuterMeasure_eq_inducedOuterMeasure`

English:
theorem toOuterMeasure_eq_inducedOuterMeasure
  proof: μ.trimmed.symm

中文:
定理 toOuterMeasure_eq_inducedOuterMeasure
  证明: μ.trimmed.symm

Depends on / 依赖: trimmed, trimmed.symm
-/
theorem toOuterMeasure_eq_inducedOuterMeasure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty :=
  μ.trimmed.symm

/--
theorem `measure_eq_extend` / 定理 `measure_eq_extend`

English:
theorem measure_eq_extend
  given: (hs : MeasurableSet s)
  proof: by
  rw [extend_eq]
  exact hs

中文:
定理 measure_eq_extend
  条件: (hs : 可测集 s)
  证明: by
  rw [extend_eq]
  exact hs

Depends on / 依赖: extend_eq
-/
theorem measure_eq_extend (hs : MeasurableSet s) :
    μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s := by
  rw [extend_eq]
  exact hs

/--
theorem `nonempty_of_measure_ne_zero` / 定理 `nonempty_of_measure_ne_zero`

English:
theorem nonempty_of_measure_ne_zero
  given: (h : μ s != 0)
  statement: s.Nonempty
  proof: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measure_empty

中文:
定理 nonempty_of_measure_ne_zero
  条件: (h : μ s != 0)
  结论: s.非空
  证明: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measure_empty

Depends on / 依赖: measure_empty, nonempty_iff_ne_empty
-/
theorem nonempty_of_measure_ne_zero (h : μ s != 0) : s.Nonempty :=
nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measure_empty

/--
theorem `measure_mono_top` / 定理 `measure_mono_top`

English:
theorem measure_mono_top
  given: (h : s₁ subseteq s₂) (h₁ : μ s₁ = ∞)
  statement: μ s₂ = ∞
  proof: top_unique h₁ ▸ measure_mono h

@[simp, mono]

中文:
定理 measure_mono_top
  条件: (h : s₁ subseteq s₂) (h₁ : μ s₁ = ∞)
  结论: μ s₂ = ∞
  证明: top_unique h₁ ▸ measure_mono h

@[simp, mono]

Depends on / 依赖: measure_mono, top_unique
-/
theorem measure_mono_top (h : s₁ subseteq s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
top_unique h₁ ▸ measure_mono h

@[simp, mono]
/--
theorem `measure_le_measure_union_left` / 定理 `measure_le_measure_union_left`

English:
theorem measure_le_measure_union_left
  statement: μ s <= μ (s union t)
  proof: μ.mono subset_union_left

@[simp, mono]

中文:
定理 measure_le_measure_union_left
  结论: μ s <= μ (s union t)
  证明: μ.mono subset_union_left

@[simp, mono]

Depends on / 依赖: subset_union_left
-/
theorem measure_le_measure_union_left : μ s <= μ (s union t) := μ.mono subset_union_left

@[simp, mono]
/--
theorem `measure_le_measure_union_right` / 定理 `measure_le_measure_union_right`

English:
theorem measure_le_measure_union_right
  statement: μ t <= μ (s union t)
  proof: μ.mono subset_union_right

中文:
定理 measure_le_measure_union_right
  结论: μ t <= μ (s union t)
  证明: μ.mono subset_union_right

Depends on / 依赖: subset_union_right
-/
theorem measure_le_measure_union_right : μ t <= μ (s union t) := μ.mono subset_union_right

/--
theorem `exists_measurable_superset` / 定理 `exists_measurable_superset`

English:
theorem exists_measurable_superset
  given: (μ : Measure α) (s : Set α)
  proof: by
  simpa only [← measure_eq_trim] using! μ.toOuterMeasure.exists_measurable_superset_eq_trim s

中文:
定理 存在_measurable_superset
  条件: (μ : 测度 α) (s : 集合 α)
  证明: by
  simpa only [← measure_eq_trim] using! μ.toOuterMeasure.exists_measurable_superset_eq_trim s

Depends on / 依赖: exists_measurable_superset_eq_trim, measure_eq_trim, toOuterMeasure, toOuterMeasure.exists_measurable_superset_eq_trim
-/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) :
    exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [← measure_eq_trim] using! μ.toOuterMeasure.exists_measurable_superset_eq_trim s

/--
theorem `exists_measurable_superset_forall_eq` / 定理 `exists_measurable_superset_forall_eq`

English:
theorem exists_measurable_superset_forall_eq
  given: [Countable ι] (μ : ι -> Measure α) (s : Set α)
  proof: by
  simpa only [← measure_eq_trim] using!
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s

中文:
定理 存在_measurable_superset_对任意_eq
  条件: [可数 ι] (μ : ι -> 测度 α) (s : 集合 α)
  证明: by
  simpa only [← measure_eq_trim] using!
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s

Depends on / 依赖: OuterMeasure, OuterMeasure.exists_measurable_superset_forall_eq_trim, exists_measurable_superset_forall_eq_trim, measure_eq_trim, toOuterMeasure
-/
theorem exists_measurable_superset_forall_eq [Countable ι] (μ : ι -> Measure α) (s : Set α) :
    exists t, s subseteq t ∧ MeasurableSet t ∧ forall i, μ i t = μ i s := by
  simpa only [← measure_eq_trim] using!
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s

/--
theorem `exists_measurable_superset₂` / 定理 `exists_measurable_superset₂`

English:
theorem exists_measurable_superset₂
  given: (μ ν : Measure α) (s : Set α)
  proof: by
  simpa only [Bool.forall_bool.trans and_comm] using!
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s

中文:
定理 存在_measurable_superset₂
  条件: (μ ν : 测度 α) (s : 集合 α)
  证明: by
  simpa only [Bool.forall_bool.trans and_comm] using!
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s

Depends on / 依赖: Bool.forall_bool.trans, and_comm, exists_measurable_superset_forall_eq, forall_bool
-/
theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [Bool.forall_bool.trans and_comm] using!
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s

/--
theorem `exists_measurable_superset_of_null` / 定理 `exists_measurable_superset_of_null`

English:
theorem exists_measurable_superset_of_null
  given: (h : μ s = 0)
  statement: exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
  proof: h ▸ exists_measurable_superset μ s

中文:
定理 存在_measurable_superset_of_null
  条件: (h : μ s = 0)
  结论: 存在 t, s subseteq t ∧ 可测集 t ∧ μ t = 0
  证明: h ▸ exists_measurable_superset μ s

Depends on / 依赖: exists_measurable_superset
-/
theorem exists_measurable_superset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s

/--
theorem `exists_measurable_superset_iff_measure_eq_zero` / 定理 `exists_measurable_superset_iff_measure_eq_zero`

English:
theorem exists_measurable_superset_iff_measure_eq_zero
  proof: ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

中文:
定理 存在_measurable_superset_iff_measure_eq_zero
  证明: ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

Depends on / 依赖: exists_measurable_superset_of_null, measure_mono_null
-/
theorem exists_measurable_superset_iff_measure_eq_zero :
    (exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

/--
theorem `measure_biUnion_lt_top` / 定理 `measure_biUnion_lt_top`

English:
theorem measure_biUnion_lt_top
  statement: {s : Set β} {f : β -> Set α} (hs : s.Finite)
  proof: by
  convert! (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · simpa only [ENNReal.sum_lt_top, Finite.mem_toFinset]

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 measure_biUnion_lt_top
  结论: {s : 集合 β} {f : β -> 集合 α} (hs : s.有限)
  证明: by
  convert! (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · simpa only [ENNReal.sum_lt_top, Finite.mem_toFinset]

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: ENNReal, ENNReal.sum_lt_top, Finite, Finite.mem_toFinset, convert, hs.toFinset, measure_biUnion_finset_le, mem_toFinset, sum_lt_top, toFinset, trans_lt
-/
theorem measure_biUnion_lt_top {s : Set β} {f : β -> Set α} (hs : s.Finite)
    (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i in s, f i) < ∞ := by
  convert! (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · simpa only [ENNReal.sum_lt_top, Finite.mem_toFinset]

@[aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `measure_biUnion_ne_top` / 定理 `measure_biUnion_ne_top`

English:
theorem measure_biUnion_ne_top
  statement: {s : Set β} {f : β -> Set α} (hs : s.Finite)
  proof: (measure_biUnion_lt_top hs (fun i hi => Ne.lt_top (hfin i hi ·))).ne

中文:
定理 measure_biUnion_ne_top
  结论: {s : 集合 β} {f : β -> 集合 α} (hs : s.有限)
  证明: (measure_biUnion_lt_top hs (fun i hi => Ne.lt_top (hfin i hi ·))).ne

Depends on / 依赖: Ne.lt_top, lt_top, measure_biUnion_lt_top
-/
theorem measure_biUnion_ne_top {s : Set β} {f : β -> Set α} (hs : s.Finite)
    (hfin : forall i in s, μ (f i) != ∞) : μ (⋃ i in s, f i) != ∞ :=
  (measure_biUnion_lt_top hs (fun i hi => Ne.lt_top (hfin i hi ·))).ne

/--
theorem `measure_union_lt_top` / 定理 `measure_union_lt_top`

English:
theorem measure_union_lt_top
  given: (hs : μ s < ∞) (ht : μ t < ∞)
  statement: μ (s union t) < ∞
  proof: (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]

中文:
定理 measure_union_lt_top
  条件: (hs : μ s < ∞) (ht : μ t < ∞)
  结论: μ (s union t) < ∞
  证明: (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.add_lt_top.mpr, add_lt_top, measure_union_le, trans_lt
-/
theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s union t) < ∞ :=
  (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]
/--
theorem `measure_union_lt_top_iff` / 定理 `measure_union_lt_top_iff`

English:
theorem measure_union_lt_top_iff
  statement: μ (s union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 measure_union_lt_top_iff
  结论: μ (s union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: Set.subset_union_left, Set.subset_union_right, measure_mono, measure_union_lt_top, subset_union_left, subset_union_right, trans_lt
-/
theorem measure_union_lt_top_iff : μ (s union t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h

@[aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `measure_union_ne_top` / 定理 `measure_union_ne_top`

English:
theorem measure_union_ne_top
  given: (hs : μ s != ∞) (ht : μ t != ∞)
  statement: μ (s union t) != ∞
  proof: (measure_union_lt_top hs.lt_top ht.lt_top).ne

中文:
定理 measure_union_ne_top
  条件: (hs : μ s != ∞) (ht : μ t != ∞)
  结论: μ (s union t) != ∞
  证明: (measure_union_lt_top hs.lt_top ht.lt_top).ne

Depends on / 依赖: hs.lt_top, ht.lt_top, lt_top, measure_union_lt_top
-/
theorem measure_union_ne_top (hs : μ s != ∞) (ht : μ t != ∞) : μ (s union t) != ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).ne

open scoped symmDiff in
@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
/--
theorem `measure_symmDiff_ne_top` / 定理 `measure_symmDiff_ne_top`

English:
theorem measure_symmDiff_ne_top
  given: (hs : μ s != ∞) (ht : μ t != ∞)
  statement: μ (s ∆ t) != ∞
  proof: ne_top_of_le_ne_top (by finiteness) measure_mono symmDiff_subset_union

@[simp]

中文:
定理 measure_symmDiff_ne_top
  条件: (hs : μ s != ∞) (ht : μ t != ∞)
  结论: μ (s ∆ t) != ∞
  证明: ne_top_of_le_ne_top (by finiteness) measure_mono symmDiff_subset_union

@[simp]

Depends on / 依赖: finiteness, measure_mono, ne_top_of_le_ne_top, symmDiff_subset_union
-/
theorem measure_symmDiff_ne_top (hs : μ s != ∞) (ht : μ t != ∞) : μ (s ∆ t) != ∞ :=
ne_top_of_le_ne_top (by finiteness) measure_mono symmDiff_subset_union

@[simp]
/--
theorem `measure_union_eq_top_iff` / 定理 `measure_union_eq_top_iff`

English:
theorem measure_union_eq_top_iff
  statement: μ (s union t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞
  proof: not_iff_not.1 by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]

中文:
定理 measure_union_eq_top_iff
  结论: μ (s union t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞
  证明: not_iff_not.1 by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]

Depends on / 依赖: Ne.eq_def, eq_def, lt_top_iff_ne_top, measure_union_lt_top_iff, not_iff_not, not_or
-/
theorem measure_union_eq_top_iff : μ (s union t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
not_iff_not.1 by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]

/--
theorem `exists_measure_pos_of_not_measure_iUnion_null` / 定理 `exists_measure_pos_of_not_measure_iUnion_null`

English:
theorem exists_measure_pos_of_not_measure_iUnion_null
  statement: [Countable ι] {s : ι -> Set α}
  proof: by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)

中文:
定理 存在_measure_pos_of_not_measure_iUnion_null
  结论: [可数 ι] {s : ι -> 集合 α}
  证明: by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)

Depends on / 依赖: contrapose, measure_iUnion_null, nonpos_iff_eq_zero
-/
theorem exists_measure_pos_of_not_measure_iUnion_null [Countable ι] {s : ι -> Set α}
    (hs : μ (⋃ n, s n) != 0) : exists n, 0 < μ (s n) := by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)

/--
theorem `measure_lt_top_of_subset` / 定理 `measure_lt_top_of_subset`

English:
theorem measure_lt_top_of_subset
  given: (hst : t subseteq s) (hs : μ s != ∞)
  statement: μ t < ∞
  proof: lt_of_le_of_lt (μ.mono hst) hs.lt_top

中文:
定理 measure_lt_top_of_subset
  条件: (hst : t subseteq s) (hs : μ s != ∞)
  结论: μ t < ∞
  证明: lt_of_le_of_lt (μ.mono hst) hs.lt_top

Depends on / 依赖: hs.lt_top, lt_of_le_of_lt, lt_top
-/
theorem measure_lt_top_of_subset (hst : t subseteq s) (hs : μ s != ∞) : μ t < ∞ :=
  lt_of_le_of_lt (μ.mono hst) hs.lt_top

/--
theorem `measure_ne_top_of_subset` / 定理 `measure_ne_top_of_subset`

English:
theorem measure_ne_top_of_subset
  given: (h : t subseteq s) (ht : μ s != ∞)
  statement: μ t != ∞
  proof: (measure_lt_top_of_subset h ht).ne

@[aesop (rule_sets := [finiteness]) unsafe apply]

中文:
定理 measure_ne_top_of_subset
  条件: (h : t subseteq s) (ht : μ s != ∞)
  结论: μ t != ∞
  证明: (measure_lt_top_of_subset h ht).ne

@[aesop (rule_sets := [finiteness]) unsafe apply]

Depends on / 依赖: measure_lt_top_of_subset
-/
theorem measure_ne_top_of_subset (h : t subseteq s) (ht : μ s != ∞) : μ t != ∞ :=
  (measure_lt_top_of_subset h ht).ne

@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
theorem `measure_inter_ne_top_of_left_ne_top` / 定理 `measure_inter_ne_top_of_left_ne_top`

English:
theorem measure_inter_ne_top_of_left_ne_top
  given: (hs_finite : μ s != ∞)
  statement: μ (s inter t) != ∞
  proof: measure_ne_top_of_subset inter_subset_left hs_finite

中文:
定理 measure_inter_ne_top_of_left_ne_top
  条件: (hs_finite : μ s != ∞)
  结论: μ (s inter t) != ∞
  证明: measure_ne_top_of_subset inter_subset_left hs_finite

Depends on / 依赖: hs_finite, inter_subset_left, measure_ne_top_of_subset
-/
theorem measure_inter_ne_top_of_left_ne_top (hs_finite : μ s != ∞) : μ (s inter t) != ∞ :=
  measure_ne_top_of_subset inter_subset_left hs_finite

/--
theorem `measure_inter_lt_top_of_left_ne_top` / 定理 `measure_inter_lt_top_of_left_ne_top`

English:
theorem measure_inter_lt_top_of_left_ne_top
  given: (hs_finite : μ s != ∞)
  statement: μ (s inter t) < ∞
  proof: by
  finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]

中文:
定理 measure_inter_lt_top_of_left_ne_top
  条件: (hs_finite : μ s != ∞)
  结论: μ (s inter t) < ∞
  证明: by
  finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]

Depends on / 依赖: finiteness
-/
theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s != ∞) : μ (s inter t) < ∞ := by
  finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
theorem `measure_inter_ne_top_of_right_ne_top` / 定理 `measure_inter_ne_top_of_right_ne_top`

English:
theorem measure_inter_ne_top_of_right_ne_top
  given: (ht_finite : μ t != ∞)
  statement: μ (s inter t) != ∞
  proof: measure_ne_top_of_subset inter_subset_right ht_finite

中文:
定理 measure_inter_ne_top_of_right_ne_top
  条件: (ht_finite : μ t != ∞)
  结论: μ (s inter t) != ∞
  证明: measure_ne_top_of_subset inter_subset_right ht_finite

Depends on / 依赖: ht_finite, inter_subset_right, measure_ne_top_of_subset
-/
theorem measure_inter_ne_top_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t) != ∞ :=
  measure_ne_top_of_subset inter_subset_right ht_finite

/--
theorem `measure_inter_lt_top_of_right_ne_top` / 定理 `measure_inter_lt_top_of_right_ne_top`

English:
theorem measure_inter_lt_top_of_right_ne_top
  given: (ht_finite : μ t != ∞)
  statement: μ (s inter t) < ∞
  proof: by
  finiteness

中文:
定理 measure_inter_lt_top_of_right_ne_top
  条件: (ht_finite : μ t != ∞)
  结论: μ (s inter t) < ∞
  证明: by
  finiteness

Depends on / 依赖: finiteness
-/
theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t) < ∞ := by
  finiteness

/--
theorem `measure_inter_null_of_null_right` / 定理 `measure_inter_null_of_null_right`

English:
theorem measure_inter_null_of_null_right
  given: (S : Set α) {T : Set α} (h : μ T = 0)
  statement: μ (S inter T) = 0
  proof: measure_mono_null inter_subset_right h

中文:
定理 measure_inter_null_of_null_right
  条件: (S : 集合 α) {T : 集合 α} (h : μ T = 0)
  结论: μ (S inter T) = 0
  证明: measure_mono_null inter_subset_right h

Depends on / 依赖: inter_subset_right, measure_mono_null
-/
theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0 :=
  measure_mono_null inter_subset_right h

/--
theorem `measure_inter_null_of_null_left` / 定理 `measure_inter_null_of_null_left`

English:
theorem measure_inter_null_of_null_left
  given: {S : Set α} (T : Set α) (h : μ S = 0)
  statement: μ (S inter T) = 0
  proof: measure_mono_null inter_subset_left h

中文:
定理 measure_inter_null_of_null_left
  条件: {S : 集合 α} (T : 集合 α) (h : μ S = 0)
  结论: μ (S inter T) = 0
  证明: measure_mono_null inter_subset_left h

Depends on / 依赖: inter_subset_left, measure_mono_null
-/
theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S inter T) = 0 :=
  measure_mono_null inter_subset_left h

/-! ### The almost everywhere filter -/
section ae

/--
theorem `_root_.MeasurableSpace.ae_induction_on_inter` / 定理 `_root_.MeasurableSpace.ae_induction_on_inter`

English:
theorem _root_.MeasurableSpace.ae_induction_on_inter
  proof: by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter (C := fun t _ => C x t)
      h_eq h_inter hx_empty hx_basic hx_compl hx_union

中文:
定理 _root_.可测空间.ae_induction_on_inter
  证明: by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter (C := fun t _ => C x t)
      h_eq h_inter hx_empty hx_basic hx_compl hx_union

Depends on / 依赖: MeasurableSpace, MeasurableSpace.induction_on_inter, filter_upwards, h_basic, h_compl, h_empty, h_eq, h_inter, h_union, hx_basic, hx_compl, hx_empty, hx_union, induction_on_inter
-/
theorem _root_.MeasurableSpace.ae_induction_on_inter
    {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {C : β -> Set α -> Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s) (h_empty : forallᵐ x ∂μ, C x ∅) (h_basic : forallᵐ x ∂μ, forall t in s, C x t)
    (h_compl : forallᵐ x ∂μ, forall t, MeasurableSet t -> C x t -> C x tᶜ)
    (h_union : forallᵐ x ∂μ, forall f : Nat -> Set α,
        Pairwise (Disjoint on f) -> (forall i, MeasurableSet (f i)) -> (forall i, C x (f i)) -> C x (⋃ i, f i)) :
    forallᵐ x ∂μ, forall ⦃t⦄, MeasurableSet t -> C x t := by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter (C := fun t _ => C x t)
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
  if h : exists t, t ⊇ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s then h.choose else
    if h' : exists t, t ⊇ s ∧ MeasurableSet t ∧
      forall u, MeasurableSet u -> μ (t inter u) = μ (s inter u) then h'.choose
    else (exists_measurable_superset μ s).choose

/--
theorem `subset_toMeasurable` / 定理 `subset_toMeasurable`

English:
theorem subset_toMeasurable
  given: (μ : Measure α) (s : Set α)
  statement: s subseteq toMeasurable μ s
  proof: by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]

中文:
定理 subset_toMeasurable
  条件: (μ : 测度 α) (s : 集合 α)
  结论: s subseteq toMeasurable μ s
  证明: by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]

Depends on / 依赖: choose_spec, exacts, exists_measurable_superset, hs.choose_spec, s.choose_spec, split_ifs, toMeasurable_def
-/
theorem subset_toMeasurable (μ : Measure α) (s : Set α) : s subseteq toMeasurable μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]

/--
theorem `ae_le_toMeasurable` / 定理 `ae_le_toMeasurable`

English:
theorem ae_le_toMeasurable
  statement: s <=ᵐ[μ] toMeasurable μ s
  proof: LE.le.eventuallyLE (subset_toMeasurable _ _)

@[simp]

中文:
定理 ae_le_toMeasurable
  结论: s <=ᵐ[μ] toMeasurable μ s
  证明: LE.le.eventuallyLE (subset_toMeasurable _ _)

@[simp]

Depends on / 依赖: LE.le.eventuallyLE, eventuallyLE, subset_toMeasurable
-/
theorem ae_le_toMeasurable : s <=ᵐ[μ] toMeasurable μ s :=
  LE.le.eventuallyLE (subset_toMeasurable _ _)

@[simp]
/--
theorem `measurableSet_toMeasurable` / 定理 `measurableSet_toMeasurable`

English:
theorem measurableSet_toMeasurable
  given: (μ : Measure α) (s : Set α)
  proof: by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]

@[simp]

中文:
定理 measurableSet_toMeasurable
  条件: (μ : 测度 α) (s : 集合 α)
  证明: by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]

@[simp]

Depends on / 依赖: choose_spec, exacts, exists_measurable_superset, hs.choose_spec, s.choose_spec, split_ifs, toMeasurable_def
-/
theorem measurableSet_toMeasurable (μ : Measure α) (s : Set α) :
    MeasurableSet (toMeasurable μ s) := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]

@[simp]
/--
theorem `measure_toMeasurable` / 定理 `measure_toMeasurable`

English:
theorem measure_toMeasurable
  given: (s : Set α)
  statement: μ (toMeasurable μ s) = μ s
  proof: by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2

中文:
定理 measure_toMeasurable
  条件: (s : 集合 α)
  结论: μ (toMeasurable μ s) = μ s
  证明: by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, choose_spec, exists_measurable_superset, hs.choose_spec, inter_univ, measure_congr, s.choose_spec, split_ifs, toMeasurable_def
-/
theorem measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2

/--
Definition of `MeasureSpace` / `MeasureSpace` 的定义

English:
class MeasureSpace
  parameters: (α : Type*)
  extends: MeasurableSpace α
  axioms and operations (1):
    - volume : Measure α

中文:
类 测度空间
  参数: (α : 类型)
  继承: 可测空间 α
  公理与运算 (1 个):
    - volume : 测度 α
-/
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α

export MeasureSpace (volume)

/-- `volume` is the canonical measure on `α`. -/
add_decl_doc volume

section MeasureSpace

/-- `∀ᵐ a, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "forallᵐ "(...)", "r:(scoped P =>
Filter.Eventually P MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

/-- `∃ᵐ a, p a` means that `p` holds frequently, i.e. on a set of positive measure,
w.r.t. the volume measure.

This is notation for `Filter.Frequently P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "existsᵐ "(...)", "r:(scoped P =>
Filter.Frequently P MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

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


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α -> β} {μ ν : Measure α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function.

A similar notion is `MeasureTheory.NullMeasurable`. That notion is equivalent to `AEMeasurable` if
the σ-algebra on the codomain is countably generated, but weaker in general. -/
@[fun_prop]
/--
Definition of `AEMeasurable` / `AEMeasurable` 的定义

English:
definition AEMeasurable
  signature: {_m : MeasurableSpace α} (f : α -> β) (μ : Measure α := by volume_tac)
  body: exists g : α -> β, Measurable g ∧ f =ᵐ[μ] g

中文:
定义 几乎处处可测
  签名: {_m : 可测空间 α} (f : α -> β) (μ : 测度 α := by volume_tac)
  定义体: exists g : α -> β, Measurable g ∧ f =ᵐ[μ] g

Depends on / 依赖: Measurable, volume_tac
-/
def AEMeasurable {_m : MeasurableSpace α} (f : α -> β) (μ : Measure α := by volume_tac) : Prop :=
  exists g : α -> β, Measurable g ∧ f =ᵐ[μ] g

/-- A function is `m`-`AEMeasurable` with respect to a measure `μ` if it coincides almost everywhere
with a `m`-measurable function. -/
scoped[MeasureTheory] notation "AEMeasurable[" m "]" => @AEMeasurable _ _ _ m

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEMeasurable ..])
  (by fun_prop (disch := measurability))

@[fun_prop]
/--
theorem `Measurable.aemeasurable` / 定理 `Measurable.aemeasurable`

English:
theorem Measurable.aemeasurable
  given: (h : Measurable f)
  statement: AEMeasurable f μ
  proof: ⟨f, h, ae_eq_refl f⟩

中文:
定理 可测.aemeasurable
  条件: (h : 可测 f)
  结论: 几乎处处可测 f μ
  证明: ⟨f, h, ae_eq_refl f⟩

Depends on / 依赖: ae_eq_refl
-/
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩

namespace AEMeasurable

@[fun_prop]
/--
lemma `of_discrete` / 引理 `of_discrete`

English:
lemma of_discrete
  given: [DiscreteMeasurableSpace α]
  statement: AEMeasurable f μ
  proof: Measurable.of_discrete.aemeasurable

中文:
引理 of_discrete
  条件: [DiscreteMeasurable空间 α]
  结论: 几乎处处可测 f μ
  证明: Measurable.of_discrete.aemeasurable

Depends on / 依赖: Measurable, Measurable.of_discrete.aemeasurable, aemeasurable, of_discrete
-/
lemma of_discrete [DiscreteMeasurableSpace α] : AEMeasurable f μ :=
  Measurable.of_discrete.aemeasurable

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : α -> β) (h : AEMeasurable f μ)
  body: Classical.choose h

@[fun_prop]

中文:
定义 mk
  签名: (f : α -> β) (h : 几乎处处可测 f μ)
  定义体: Classical.choose h

@[fun_prop]

Depends on / 依赖: Classical, Classical.choose
-/
def mk (f : α -> β) (h : AEMeasurable f μ) : α -> β :=
  Classical.choose h

@[fun_prop]
/--
theorem `measurable_mk` / 定理 `measurable_mk`

English:
theorem measurable_mk
  given: (h : AEMeasurable f μ)
  statement: Measurable (h.mk f)
  proof: (Classical.choose_spec h).1

中文:
定理 measurable_mk
  条件: (h : 几乎处处可测 f μ)
  结论: 可测 (h.mk f)
  证明: (Classical.choose_spec h).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.choose_spec h).1

/--
theorem `ae_eq_mk` / 定理 `ae_eq_mk`

English:
theorem ae_eq_mk
  given: (h : AEMeasurable f μ)
  statement: f =ᵐ[μ] h.mk f
  proof: (Classical.choose_spec h).2

中文:
定理 ae_eq_mk
  条件: (h : 几乎处处可测 f μ)
  结论: f =ᵐ[μ] h.mk f
  证明: (Classical.choose_spec h).2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.choose_spec h).2

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g)
  statement: AEMeasurable g μ
  proof: ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

中文:
定理 congr
  条件: (hf : 几乎处处可测 f μ) (h : f =ᵐ[μ] g)
  结论: 几乎处处可测 g μ
  证明: ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

Depends on / 依赖: ae_eq_mk, h.symm.trans, hf.ae_eq_mk, hf.measurable_mk, hf.mk, measurable_mk
-/
theorem congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

end AEMeasurable

/--
theorem `aemeasurable_congr` / 定理 `aemeasurable_congr`

English:
theorem aemeasurable_congr
  given: (h : f =ᵐ[μ] g)
  statement: AEMeasurable f μ ↔ AEMeasurable g μ
  proof: ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩

@[simp, fun_prop]

中文:
定理 aemeasurable_congr
  条件: (h : f =ᵐ[μ] g)
  结论: 几乎处处可测 f μ ↔ 几乎处处可测 g μ
  证明: ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩

@[simp, fun_prop]

Depends on / 依赖: AEMeasurable, AEMeasurable.congr, h.symm
-/
theorem aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ :=
  ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩

@[simp, fun_prop]
/--
theorem `aemeasurable_const` / 定理 `aemeasurable_const`

English:
theorem aemeasurable_const
  given: {b : β}
  statement: AEMeasurable (fun _a : α => b) μ
  proof: measurable_const.aemeasurable

@[fun_prop]

中文:
定理 aemeasurable_const
  条件: {b : β}
  结论: 几乎处处可测 (fun _a : α => b) μ
  证明: measurable_const.aemeasurable

@[fun_prop]

Depends on / 依赖: aemeasurable, measurable_const, measurable_const.aemeasurable
-/
theorem aemeasurable_const {b : β} : AEMeasurable (fun _a : α => b) μ :=
  measurable_const.aemeasurable

@[fun_prop]
/--
theorem `aemeasurable_id` / 定理 `aemeasurable_id`

English:
theorem aemeasurable_id
  statement: AEMeasurable id μ
  proof: measurable_id.aemeasurable

@[fun_prop]

中文:
定理 aemeasurable_id
  结论: 几乎处处可测 id μ
  证明: measurable_id.aemeasurable

@[fun_prop]

Depends on / 依赖: aemeasurable, measurable_id, measurable_id.aemeasurable
-/
theorem aemeasurable_id : AEMeasurable id μ :=
  measurable_id.aemeasurable

@[fun_prop]
/--
theorem `aemeasurable_id'` / 定理 `aemeasurable_id'`

English:
theorem aemeasurable_id'
  statement: AEMeasurable (fun x => x) μ
  proof: measurable_id.aemeasurable

中文:
定理 aemeasurable_id'
  结论: 几乎处处可测 (fun x => x) μ
  证明: measurable_id.aemeasurable

Depends on / 依赖: aemeasurable, measurable_id, measurable_id.aemeasurable
-/
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.aemeasurable

/--
theorem `Measurable.comp_aemeasurable` / 定理 `Measurable.comp_aemeasurable`

English:
theorem Measurable.comp_aemeasurable
  statement: [MeasurableSpace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g)
  proof: ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

@[fun_prop]

中文:
定理 可测.comp_aemeasurable
  结论: [可测空间 δ] {f : α -> δ} {g : δ -> β} (hg : 可测 g)
  证明: ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

@[fun_prop]

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, ae_eq_mk, fun_comp, hf.ae_eq_mk, hf.measurable_mk, hf.mk, hg.comp, measurable_mk
-/
theorem Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g)
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

@[fun_prop]
/--
theorem `Measurable.comp_aemeasurable'` / 定理 `Measurable.comp_aemeasurable'`

English:
theorem Measurable.comp_aemeasurable'
  statement: [MeasurableSpace δ] {f : α -> δ} {g : δ -> β}
  proof: Measurable.comp_aemeasurable hg hf

中文:
定理 可测.comp_aemeasurable'
  结论: [可测空间 δ] {f : α -> δ} {g : δ -> β}
  证明: Measurable.comp_aemeasurable hg hf

Depends on / 依赖: Measurable, Measurable.comp_aemeasurable, comp_aemeasurable
-/
theorem Measurable.comp_aemeasurable' [MeasurableSpace δ] {f : α -> δ} {g : δ -> β}
    (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) μ :=
  Measurable.comp_aemeasurable hg hf

variable {δ : Type*} {X : δ -> Type*} {mX : forall a, MeasurableSpace (X a)}

/--
theorem `AEMeasurable.eval` / 定理 `AEMeasurable.eval`

English:
theorem AEMeasurable.eval
  given: {g : α -> Π a, X a} (hg : AEMeasurable g μ) (a : δ)
  proof: by
  use fun x => hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h => congrFun h _

中文:
定理 几乎处处可测.eval
  条件: {g : α -> Π a, X a} (hg : 几乎处处可测 g μ) (a : δ)
  证明: by
  use fun x => hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h => congrFun h _
-/
protected theorem AEMeasurable.eval {g : α -> Π a, X a} (hg : AEMeasurable g μ) (a : δ) :
    AEMeasurable (fun x => g x a) μ := by
  use fun x => hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h => congrFun h _

variable [Countable δ]

/--
theorem `aemeasurable_pi_iff` / 定理 `aemeasurable_pi_iff`

English:
theorem aemeasurable_pi_iff
  given: {g : α -> Π a, X a}
  proof: by
  constructor
  · exact AEMeasurable.eval
  · intro h
    use fun x a => (h a).mk _ x, measurable_pi_lambda _ fun a => (h a).measurable_mk
    exact (eventually_countable_forall.mpr fun a => (h a).ae_eq_mk).mono fun _ h => funext h

@[fun_prop]

中文:
定理 aemeasurable_pi_iff
  条件: {g : α -> Π a, X a}
  证明: by
  constructor
  · exact AEMeasurable.eval
  · intro h
    use fun x a => (h a).mk _ x, measurable_pi_lambda _ fun a => (h a).measurable_mk
    exact (eventually_countable_forall.mpr fun a => (h a).ae_eq_mk).mono fun _ h => funext h

@[fun_prop]

Depends on / 依赖: AEMeasurable, AEMeasurable.eval, ae_eq_mk, eventually_countable_forall, eventually_countable_forall.mpr, measurable_mk, measurable_pi_lambda
-/
theorem aemeasurable_pi_iff {g : α -> Π a, X a} :
    AEMeasurable g μ ↔ forall a, AEMeasurable (fun x => g x a) μ := by
  constructor
  · exact AEMeasurable.eval
  · intro h
    use fun x a => (h a).mk _ x, measurable_pi_lambda _ fun a => (h a).measurable_mk
    exact (eventually_countable_forall.mpr fun a => (h a).ae_eq_mk).mono fun _ h => funext h

@[fun_prop]
/--
theorem `aemeasurable_pi_lambda` / 定理 `aemeasurable_pi_lambda`

English:
theorem aemeasurable_pi_lambda
  given: (f : α -> Π a, X a) (hf : forall a, AEMeasurable (fun c => f c a) μ)
  proof: aemeasurable_pi_iff.mpr hf

中文:
定理 aemeasurable_pi_lambda
  条件: (f : α -> Π a, X a) (hf : 对任意 a, 几乎处处可测 (fun c => f c a) μ)
  证明: aemeasurable_pi_iff.mpr hf

Depends on / 依赖: aemeasurable_pi_iff, aemeasurable_pi_iff.mpr
-/
theorem aemeasurable_pi_lambda (f : α -> Π a, X a) (hf : forall a, AEMeasurable (fun c => f c a) μ) :
    AEMeasurable f μ :=
  aemeasurable_pi_iff.mpr hf

end
