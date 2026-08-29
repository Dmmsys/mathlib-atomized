/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
public import Mathlib.MeasureTheory.Measure.AEDisjoint

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : Set α` is called *null measurable* (`MeasureTheory.NullMeasurableSet`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `MeasureTheory.toMeasurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `MeasurableSpace` instance on
`MeasureTheory.NullMeasurableSpace α μ`. We also say that `f : α → β` is
`MeasureTheory.NullMeasurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`MeasureTheory.NullMeasurableSpace α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `MeasurableSpace α` σ-algebra (or the σ-algebra is
complete w.r.t. measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `MeasureTheory.Measure.completion μ` to be the same measure
interpreted as a measure on `MeasureTheory.NullMeasurableSpace α μ` and prove that this is a
complete measure.

## Implementation notes

We define `MeasureTheory.NullMeasurableSet` as `@MeasurableSet (NullMeasurableSpace α μ) _` so
that theorems about `MeasurableSet`s like `MeasurableSet.union` can be applied to
`NullMeasurableSet`s. However, these lemmas output terms of the same form
`@MeasurableSet (NullMeasurableSpace α μ) _ _`. While this is definitionally equal to the
expected output `NullMeasurableSet s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `MeasureTheory.NullMeasurableSet` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/

@[expose] public section

open Filter Set Encodable
open scoped ENNReal

variable {ι α β γ : Type*}

namespace MeasureTheory

/-- A type tag for `α` with `MeasurableSet` given by `NullMeasurableSet`. -/
@[nolint unusedArguments]
/--
Definition of `NullMeasurableSpace` / `NullMeasurableSpace` 的定义

English:
definition NullMeasurableSpace
  signature: (α : Type*) [MeasurableSpace α]
  body: α

中文:
定义 NullMeasurableSpace
  签名: (α : 类型) [可测空间 α]
  定义体: α

Depends on / 依赖: volume_tac
-/
def NullMeasurableSpace (α : Type*) [MeasurableSpace α]
    (_μ : Measure α := by volume_tac) : Type _ :=
  α

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

/--
Instance `NullMeasurableSpace.instInhabited` / 实例 `NullMeasurableSpace.instInhabited`

English:
instance NullMeasurableSpace.instInhabited
  signature: [h : Inhabited α]
  body: h

中文:
实例 NullMeasurableSpace.instInhabited
  签名: [h : 可居 α]
  定义体: h
-/
instance NullMeasurableSpace.instInhabited [h : Inhabited α] :
    Inhabited (NullMeasurableSpace α μ) :=
  h

/--
Instance `NullMeasurableSpace.instSubsingleton` / 实例 `NullMeasurableSpace.instSubsingleton`

English:
instance NullMeasurableSpace.instSubsingleton
  signature: [h : Subsingleton α]
  body: h

中文:
实例 NullMeasurableSpace.instSubsingleton
  签名: [h : 子单例 α]
  定义体: h
-/
instance NullMeasurableSpace.instSubsingleton [h : Subsingleton α] :
    Subsingleton (NullMeasurableSpace α μ) :=
  h

/--
Instance `NullMeasurableSpace.instMeasurableSpace` / 实例 `NullMeasurableSpace.instMeasurableSpace`

English:
instance NullMeasurableSpace.instMeasurableSpace
  signature: : MeasurableSpace (NullMeasurableSpace α μ)
  body: fast_instance% @eventuallyMeasurableSpace α inferInstance (ae μ) _

中文:
实例 NullMeasurableSpace.instMeasurableSpace
  签名: : 可测空间 (NullMeasurableSpace α μ)
  定义体: fast_instance% @eventuallyMeasurableSpace α inferInstance (ae μ) _

Depends on / 依赖: eventuallyMeasurableSpace, fast_instance
-/
instance NullMeasurableSpace.instMeasurableSpace : MeasurableSpace (NullMeasurableSpace α μ) :=
  fast_instance% @eventuallyMeasurableSpace α inferInstance (ae μ) _

/--
Definition of `NullMeasurableSet` / `NullMeasurableSet` 的定义

English:
definition NullMeasurableSet
  signature: [MeasurableSpace α] (s : Set α)
  body: @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp, aesop unsafe (rule_sets := [Measurable])]

中文:
定义 NullMeasurableSet
  签名: [可测空间 α] (s : 集合 α)
  定义体: @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp, aesop unsafe (rule_sets := [Measurable])]

Depends on / 依赖: MeasurableSet, NullMeasurableSpace, volume_tac
-/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by volume_tac) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s

@[simp, aesop unsafe (rule_sets := [Measurable])]
/--
theorem `_root_.MeasurableSet.nullMeasurableSet` / 定理 `_root_.MeasurableSet.nullMeasurableSet`

English:
theorem _root_.MeasurableSet.nullMeasurableSet
  given: (h : MeasurableSet s)
  statement: NullMeasurableSet s μ
  proof: h.eventuallyMeasurableSet

中文:
定理 _root_.可测集.nullMeasurableSet
  条件: (h : 可测集 s)
  结论: NullMeasurableSet s μ
  证明: h.eventuallyMeasurableSet

Depends on / 依赖: eventuallyMeasurableSet, h.eventuallyMeasurableSet
-/
theorem _root_.MeasurableSet.nullMeasurableSet (h : MeasurableSet s) : NullMeasurableSet s μ :=
  h.eventuallyMeasurableSet

/--
theorem `_root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet` / 定理 `_root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet`

English:
theorem _root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet
  given: (s : Set α)
  proof: Iff.rfl

中文:
定理 _root_.测度论.nullMeasurableSet_iff_eventuallyMeasurableSet
  条件: (s : 集合 α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem _root_.MeasureTheory.nullMeasurableSet_iff_eventuallyMeasurableSet (s : Set α) :
    NullMeasurableSet s μ ↔ EventuallyMeasurableSet m0 (ae μ) s :=
  Iff.rfl

/--
theorem `nullMeasurableSet_empty` / 定理 `nullMeasurableSet_empty`

English:
theorem nullMeasurableSet_empty
  statement: NullMeasurableSet ∅ μ
  proof: MeasurableSet.empty

中文:
定理 nullMeasurableSet_empty
  结论: NullMeasurableSet ∅ μ
  证明: MeasurableSet.empty

Depends on / 依赖: MeasurableSet, MeasurableSet.empty
-/
theorem nullMeasurableSet_empty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty

/--
theorem `nullMeasurableSet_univ` / 定理 `nullMeasurableSet_univ`

English:
theorem nullMeasurableSet_univ
  statement: NullMeasurableSet univ μ
  proof: MeasurableSet.univ

中文:
定理 nullMeasurableSet_univ
  结论: NullMeasurableSet univ μ
  证明: MeasurableSet.univ

Depends on / 依赖: MeasurableSet, MeasurableSet.univ
-/
theorem nullMeasurableSet_univ : NullMeasurableSet univ μ :=
  MeasurableSet.univ

namespace NullMeasurableSet

/--
theorem `of_null` / 定理 `of_null`

English:
theorem of_null
  given: (h : μ s = 0)
  statement: NullMeasurableSet s μ
  proof: ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

中文:
定理 of_null
  条件: (h : μ s = 0)
  结论: NullMeasurableSet s μ
  证明: ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, ae_eq_empty
-/
theorem of_null (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

/--
theorem `compl` / 定理 `compl`

English:
theorem compl
  given: (h : NullMeasurableSet s μ)
  statement: NullMeasurableSet sᶜ μ
  proof: MeasurableSet.compl h

中文:
定理 compl
  条件: (h : NullMeasurableSet s μ)
  结论: NullMeasurableSet sᶜ μ
  证明: MeasurableSet.compl h

Depends on / 依赖: MeasurableSet, MeasurableSet.compl
-/
theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet sᶜ μ :=
  MeasurableSet.compl h

/--
theorem `of_compl` / 定理 `of_compl`

English:
theorem of_compl
  given: (h : NullMeasurableSet sᶜ μ)
  statement: NullMeasurableSet s μ
  proof: MeasurableSet.of_compl h

@[simp]

中文:
定理 of_compl
  条件: (h : NullMeasurableSet sᶜ μ)
  结论: NullMeasurableSet s μ
  证明: MeasurableSet.of_compl h

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.of_compl, of_compl
-/
theorem of_compl (h : NullMeasurableSet sᶜ μ) : NullMeasurableSet s μ :=
  MeasurableSet.of_compl h

@[simp]
/--
theorem `compl_iff` / 定理 `compl_iff`

English:
theorem compl_iff
  statement: NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ
  proof: MeasurableSet.compl_iff

@[nontriviality]

中文:
定理 compl_iff
  结论: NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ
  证明: MeasurableSet.compl_iff

@[nontriviality]

Depends on / 依赖: MeasurableSet, MeasurableSet.compl_iff, compl_iff
-/
theorem compl_iff : NullMeasurableSet sᶜ μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff

@[nontriviality]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton α]
  statement: NullMeasurableSet s μ
  proof: Subsingleton.measurableSet

中文:
定理 of_subsingleton
  条件: [子单例 α]
  结论: NullMeasurableSet s μ
  证明: Subsingleton.measurableSet

Depends on / 依赖: Subsingleton, Subsingleton.measurableSet, measurableSet
-/
theorem of_subsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurableSet

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t)
  statement: NullMeasurableSet t μ
  proof: by
  rw [nullMeasurableSet_iff_eventuallyMeasurableSet]
  exact EventuallyMeasurableSet.congr hs h.symm

@[measurability]

中文:
定理 congr
  条件: (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t)
  结论: NullMeasurableSet t μ
  证明: by
  rw [nullMeasurableSet_iff_eventuallyMeasurableSet]
  exact EventuallyMeasurableSet.congr hs h.symm

@[measurability]
-/
protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ := by
  rw [nullMeasurableSet_iff_eventuallyMeasurableSet]
  exact EventuallyMeasurableSet.congr hs h.symm

@[measurability]
/--
theorem `iUnion` / 定理 `iUnion`

English:
theorem iUnion
  statement: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  proof: MeasurableSet.iUnion h

中文:
定理 iUnion
  结论: {ι : 类型层*} [可数 ι] {s : ι -> 集合 α}
  证明: MeasurableSet.iUnion h

Depends on / 依赖: Finite, Finite.to_isCoatomic, OrderTop, PartialOrder, to_isCoatomic
-/
protected theorem iUnion {ι : Sort*} [Countable ι] {s : ι -> Set α}
    (h : forall i, NullMeasurableSet (s i) μ) : NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.iUnion h

/--
theorem `biUnion` / 定理 `biUnion`

English:
theorem biUnion
  statement: {f : ι -> Set α} {s : Set ι} (hs : s.Countable)
  proof: MeasurableSet.biUnion hs h

中文:
定理 biUnion
  结论: {f : ι -> 集合 α} {s : 集合 ι} (hs : s.可数)
  证明: MeasurableSet.biUnion hs h

Depends on / 依赖: Finite, Finite.to_isAtomic, OrderBot, PartialOrder, to_isAtomic
-/
protected theorem biUnion {f : ι -> Set α} {s : Set ι} (hs : s.Countable)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b in s, f b) μ :=
  MeasurableSet.biUnion hs h

/--
theorem `sUnion` / 定理 `sUnion`

English:
theorem sUnion
  given: {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, NullMeasurableSet t μ)
  proof: by
  rw [sUnion_eq_biUnion]
  exact MeasurableSet.biUnion hs h

@[measurability]

中文:
定理 集合并集
  条件: {s : 集合 (集合 α)} (hs : s.可数) (h : 对任意 t in s, NullMeasurableSet t μ)
  证明: by
  rw [sUnion_eq_biUnion]
  exact MeasurableSet.biUnion hs h

@[measurability]
-/
protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀ s) μ := by
  rw [sUnion_eq_biUnion]
  exact MeasurableSet.biUnion hs h

@[measurability]
/--
theorem `iInter` / 定理 `iInter`

English:
theorem iInter
  statement: {ι : Sort*} [Countable ι] {f : ι -> Set α}
  proof: MeasurableSet.iInter h

中文:
定理 i整数er
  结论: {ι : 类型层*} [可数 ι] {f : ι -> 集合 α}
  证明: MeasurableSet.iInter h
-/
protected theorem iInter {ι : Sort*} [Countable ι] {f : ι -> Set α}
    (h : forall i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.iInter h

/--
theorem `biInter` / 定理 `biInter`

English:
theorem biInter
  statement: {f : β -> Set α} {s : Set β} (hs : s.Countable)
  proof: MeasurableSet.biInter hs h

中文:
定理 bi整数er
  结论: {f : β -> 集合 α} {s : 集合 β} (hs : s.可数)
  证明: MeasurableSet.biInter hs h
-/
protected theorem biInter {f : β -> Set α} {s : Set β} (hs : s.Countable)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b in s, f b) μ :=
  MeasurableSet.biInter hs h

/--
theorem `sInter` / 定理 `sInter`

English:
theorem sInter
  given: {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, NullMeasurableSet t μ)
  proof: MeasurableSet.sInter hs h

@[simp]

中文:
定理 集合交集
  条件: {s : 集合 (集合 α)} (hs : s.可数) (h : 对任意 t in s, NullMeasurableSet t μ)
  证明: MeasurableSet.sInter hs h

@[simp]
-/
protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.sInter hs h

@[simp]
/--
theorem `union` / 定理 `union`

English:
theorem union
  given: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: MeasurableSet.union hs ht

中文:
定理 union
  条件: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: MeasurableSet.union hs ht
-/
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s union t) μ :=
  MeasurableSet.union hs ht

/--
theorem `union_null` / 定理 `union_null`

English:
theorem union_null
  given: (hs : NullMeasurableSet s μ) (ht : μ t = 0)
  proof: hs.union (of_null ht)

@[simp]

中文:
定理 union_null
  条件: (hs : NullMeasurableSet s μ) (ht : μ t = 0)
  证明: hs.union (of_null ht)

@[simp]
-/
protected theorem union_null (hs : NullMeasurableSet s μ) (ht : μ t = 0) :
    NullMeasurableSet (s union t) μ :=
  hs.union (of_null ht)

@[simp]
/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: MeasurableSet.inter hs ht

@[simp]

中文:
定理 inter
  条件: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: MeasurableSet.inter hs ht

@[simp]
-/
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s inter t) μ :=
  MeasurableSet.inter hs ht

@[simp]
/--
theorem `diff` / 定理 `diff`

English:
theorem diff
  given: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: MeasurableSet.diff hs ht

@[simp]

中文:
定理 diff
  条件: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: MeasurableSet.diff hs ht

@[simp]
-/
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s \ t) μ :=
  MeasurableSet.diff hs ht

@[simp]
/--
theorem `symmDiff` / 定理 `symmDiff`

English:
theorem symmDiff
  statement: {s₁ s₂ : Set α} (h₁ : NullMeasurableSet s₁ μ)
  proof: (h₁.diff h₂).union (h₂.diff h₁)

@[simp]

中文:
定理 symmDiff
  结论: {s₁ s₂ : 集合 α} (h₁ : NullMeasurableSet s₁ μ)
  证明: (h₁.diff h₂).union (h₂.diff h₁)

@[simp]

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.toOrderBot, OrderBot, toOrderBot
-/
protected theorem symmDiff {s₁ s₂ : Set α} (h₁ : NullMeasurableSet s₁ μ)
    (h₂ : NullMeasurableSet s₂ μ) : NullMeasurableSet (symmDiff s₁ s₂) μ :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
/--
theorem `disjointed` / 定理 `disjointed`

English:
theorem disjointed
  given: {f : Nat -> Set α} (h : forall i, NullMeasurableSet (f i) μ) (n)
  proof: MeasurableSet.disjointed h n

中文:
定理 disjointed
  条件: {f : 自然数 -> 集合 α} (h : 对任意 i, NullMeasurableSet (f i) μ) (n)
  证明: MeasurableSet.disjointed h n
-/
protected theorem disjointed {f : Nat -> Set α} (h : forall i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (p : Prop)
  statement: NullMeasurableSet { _a : α | p } μ
  proof: MeasurableSet.const p

中文:
定理 const
  条件: (p : 命题)
  结论: NullMeasurableSet { _a : α | p } μ
  证明: MeasurableSet.const p
-/
protected theorem const (p : Prop) : NullMeasurableSet { _a : α | p } μ :=
  MeasurableSet.const p

/--
Instance `instMeasurableSingletonClass` / 实例 `instMeasurableSingletonClass`

English:
instance instMeasurableSingletonClass
  signature: [MeasurableSingletonClass α]
  body: eventuallyMeasurableSingleton (m := m0)

中文:
实例 instMeasurableSingletonClass
  签名: [MeasurableSingleton类 α]
  定义体: eventuallyMeasurableSingleton (m := m0)

Depends on / 依赖: eventuallyMeasurableSingleton
-/
instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  eventuallyMeasurableSingleton (m := m0)

/--
theorem `insert` / 定理 `insert`

English:
theorem insert
  statement: [MeasurableSingletonClass (NullMeasurableSpace α μ)]
  proof: MeasurableSet.insert hs a

中文:
定理 insert
  结论: [MeasurableSingleton类 (NullMeasurableSpace α μ)]
  证明: MeasurableSet.insert hs a
-/
protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)]
    (hs : NullMeasurableSet s μ) (a : α) : NullMeasurableSet (insert a s) μ :=
  MeasurableSet.insert hs a

/--
theorem `exists_measurable_superset_ae_eq` / 定理 `exists_measurable_superset_ae_eq`

English:
theorem exists_measurable_superset_ae_eq
  given: (h : NullMeasurableSet s μ)
  proof: by
  rcases h with ⟨t, htm, hst⟩
  refine ⟨t union toMeasurable μ (s \ t), ?_, htm.union (measurableSet_toMeasurable _ _), ?_⟩
  · exact sdiff_subset_iff.1 (subset_toMeasurable _ _)
  · have : toMeasurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using

中文:
定理 存在_measurable_superset_ae_eq
  条件: (h : NullMeasurableSet s μ)
  证明: by
  rcases h with ⟨t, htm, hst⟩
  refine ⟨t union toMeasurable μ (s \ t), ?_, htm.union (measurableSet_toMeasurable _ _), ?_⟩
  · exact sdiff_subset_iff.1 (subset_toMeasurable _ _)
  · have : toMeasurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using

Depends on / 依赖: ae_le_set, hst.le, hst.symm.union, htm.union, measurableSet_toMeasurable, sdiff_subset_iff, subset_toMeasurable, toMeasurable, union_empty
-/
theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    exists t ⊇ s, MeasurableSet t ∧ t =ᵐ[μ] s := by
  rcases h with ⟨t, htm, hst⟩
  refine ⟨t union toMeasurable μ (s \ t), ?_, htm.union (measurableSet_toMeasurable _ _), ?_⟩
  · exact sdiff_subset_iff.1 (subset_toMeasurable _ _)
  · have : toMeasurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using hst.symm.union this

/--
theorem `toMeasurable_ae_eq` / 定理 `toMeasurable_ae_eq`

English:
theorem toMeasurable_ae_eq
  given: (h : NullMeasurableSet s μ)
  statement: toMeasurable μ s =ᵐ[μ] s
  proof: by
  rw [toMeasurable_def]; rw [dif_pos]
  exact (exists_measurable_superset_ae_eq h).choose_spec.2.2

中文:
定理 toMeasurable_ae_eq
  条件: (h : NullMeasurableSet s μ)
  结论: toMeasurable μ s =ᵐ[μ] s
  证明: by
  rw [toMeasurable_def]; rw [dif_pos]
  exact (exists_measurable_superset_ae_eq h).choose_spec.2.2

Depends on / 依赖: choose_spec, dif_pos, exists_measurable_superset_ae_eq, toMeasurable_def
-/
theorem toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s := by
  rw [toMeasurable_def]; rw [dif_pos]
  exact (exists_measurable_superset_ae_eq h).choose_spec.2.2

/--
theorem `compl_toMeasurable_compl_ae_eq` / 定理 `compl_toMeasurable_compl_ae_eq`

English:
theorem compl_toMeasurable_compl_ae_eq
  given: (h : NullMeasurableSet s μ)
  statement: (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] s
  proof: Iff.mpr ae_eq_set_compl toMeasurable_ae_eq h.compl

中文:
定理 compl_toMeasurable_compl_ae_eq
  条件: (h : NullMeasurableSet s μ)
  结论: (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] s
  证明: Iff.mpr ae_eq_set_compl toMeasurable_ae_eq h.compl

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra, Iff.mpr, ae_eq_set_compl, h.compl, toGeneralizedCoheytingAlgebra, toMeasurable_ae_eq
-/
theorem compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : (toMeasurable μ sᶜ)ᶜ =ᵐ[μ] s :=
Iff.mpr ae_eq_set_compl toMeasurable_ae_eq h.compl

/--
theorem `exists_measurable_subset_ae_eq` / 定理 `exists_measurable_subset_ae_eq`

English:
theorem exists_measurable_subset_ae_eq
  given: (h : NullMeasurableSet s μ)
  proof: ⟨(toMeasurable μ sᶜ)ᶜ, compl_subset_comm.2 subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, compl_toMeasurable_compl_ae_eq h⟩

中文:
定理 存在_measurable_subset_ae_eq
  条件: (h : NullMeasurableSet s μ)
  证明: ⟨(toMeasurable μ sᶜ)ᶜ, compl_subset_comm.2 subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, compl_toMeasurable_compl_ae_eq h⟩

Depends on / 依赖: compl_subset_comm, compl_toMeasurable_compl_ae_eq, measurableSet_toMeasurable, subset_toMeasurable, toMeasurable
-/
theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    exists t subseteq s, MeasurableSet t ∧ t =ᵐ[μ] s :=
⟨(toMeasurable μ sᶜ)ᶜ, compl_subset_comm.2 subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, compl_toMeasurable_compl_ae_eq h⟩

end NullMeasurableSet

open NullMeasurableSet

open scoped Function -- required for scoped `on` notation

/--
theorem `exists_subordinate_pairwise_disjoint` / 定理 `exists_subordinate_pairwise_disjoint`

English:
theorem exists_subordinate_pairwise_disjoint
  statement: [Countable ι] {s : ι -> Set α}
  proof: by
  choose t ht_sub htm ht_eq using fun i => exists_measurable_subset_ae_eq (h i)
  rcases exists_null_pairwise_disjoint_sdiff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => sdiff_subset.trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (sdiff_null_ae_eq_self (hu₀ i)).symm

中文:
定理 存在_subordinate_pairwise_disjoint
  结论: [可数 ι] {s : ι -> 集合 α}
  证明: by
  choose t ht_sub htm ht_eq using fun i => exists_measurable_subset_ae_eq (h i)
  rcases exists_null_pairwise_disjoint_sdiff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => sdiff_subset.trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (sdiff_null_ae_eq_self (hu₀ i)).symm

Depends on / 依赖: exists_measurable_subset_ae_eq, exists_null_pairwise_disjoint_sdiff, h.mono, ht_eq, ht_sub, hud.mono, sdiff_null_ae_eq_self, sdiff_subset, sdiff_subset.trans, sdiff_subset_sdiff_left, symm.trans
-/
theorem exists_subordinate_pairwise_disjoint [Countable ι] {s : ι -> Set α}
    (h : forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) :
    exists t : ι -> Set α,
      (forall i, t i subseteq s i) ∧
        (forall i, s i =ᵐ[μ] t i) ∧ (forall i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) := by
  choose t ht_sub htm ht_eq using fun i => exists_measurable_subset_ae_eq (h i)
  rcases exists_null_pairwise_disjoint_sdiff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => sdiff_subset.trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (sdiff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diff (hum i),
      hud.mono fun i j h =>
        h.mono (sdiff_subset_sdiff_left (ht_sub i)) (sdiff_subset_sdiff_left (ht_sub j))⟩

/--
theorem `measure_iUnion` / 定理 `measure_iUnion`

English:
theorem measure_iUnion
  statement: {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι -> Set α}
  proof: by
  rw [measure_eq_extend (MeasurableSet.iUnion h)]; rw [extend_iUnion MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_iUnion

中文:
定理 measure_iUnion
  结论: {m0 : 可测空间 α} {μ : 测度 α} [可数 ι] {f : ι -> 集合 α}
  证明: by
  rw [measure_eq_extend (MeasurableSet.iUnion h)]; rw [extend_iUnion MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_iUnion

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.iUnion, extend_iUnion, iUnion, m_iUnion, measure_eq_extend
-/
theorem measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι -> Set α}
    (hn : Pairwise (Disjoint on f)) (h : forall i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rw [measure_eq_extend (MeasurableSet.iUnion h)]; rw [extend_iUnion MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_iUnion

/--
theorem `measure_iUnion₀` / 定理 `measure_iUnion₀`

English:
theorem measure_iUnion₀
  statement: [Countable ι] {f : ι -> Set α} (hd : Pairwise (AEDisjoint μ on f))
  proof: by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := measure_iUnion htd htm
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm

中文:
定理 measure_iUnion₀
  结论: [可数 ι] {f : ι -> 集合 α} (hd : 两两 (AEDisjoint μ on f))
  证明: by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := measure_iUnion htd htm
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm

Depends on / 依赖: _ht_sub, countable_iUnion, exists_subordinate_pairwise_disjoint, ht_eq, measure_congr, measure_iUnion, tsum_congr
-/
theorem measure_iUnion₀ [Countable ι] {f : ι -> Set α} (hd : Pairwise (AEDisjoint μ on f))
    (h : forall i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, _ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := measure_iUnion htd htm
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm

/--
theorem `measure_union₀_aux` / 定理 `measure_union₀_aux`

English:
theorem measure_union₀_aux
  statement: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: by
  rw [union_eq_iUnion]; rw [measure_iUnion₀]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [pairwise_on_bool.mpr hd, fun b => Bool.casesOn b ht hs]

中文:
定理 measure_union₀_aux
  结论: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: by
  rw [union_eq_iUnion]; rw [measure_iUnion₀]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [pairwise_on_bool.mpr hd, fun b => Bool.casesOn b ht hs]

Depends on / 依赖: Bool.casesOn, Fintype, Fintype.sum_bool, casesOn, exacts, pairwise_on_bool, pairwise_on_bool.mpr, sum_bool, tsum_fintype, union_eq_iUnion
-/
theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t := by
  rw [union_eq_iUnion]; rw [measure_iUnion₀]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [pairwise_on_bool.mpr hd, fun b => Bool.casesOn b ht hs]

/--
theorem `measure_inter_add_sdiff₀` / 定理 `measure_inter_add_sdiff₀`

English:
theorem measure_inter_add_sdiff₀
  given: (s : Set α) (ht : NullMeasurableSet t μ)
  proof: by
  refine le_antisymm ?_ (measure_le_inter_add_sdiff _ _ _)
  rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
  replace hs'm : NullMeasurableSet s' μ := hs'm.nullMeasurableSet
  calc
    μ (s inter t) + μ (s \ t) <= μ (s' inter t) + μ (s' \ t) := by gcongr
    _ = μ (s' inter t un

中文:
定理 measure_inter_add_sdiff₀
  条件: (s : 集合 α) (ht : NullMeasurableSet t μ)
  证明: by
  refine le_antisymm ?_ (measure_le_inter_add_sdiff _ _ _)
  rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
  replace hs'm : NullMeasurableSet s' μ := hs'm.nullMeasurableSet
  calc
    μ (s inter t) + μ (s \ t) <= μ (s' inter t) + μ (s' \ t) := by gcongr
    _ = μ (s' inter t un

Depends on / 依赖: NullMeasurableSet, aedisjoint, congr_arg, disjoint_inf_sdiff, exists_measurable_superset, inter_union_sdiff, le_antisymm, m.diff, m.inter, m.nullMeasurableSet, measure_le_inter_add_sdiff, nullMeasurableSet, replace
-/
theorem measure_inter_add_sdiff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s inter t) + μ (s \ t) = μ s := by
  refine le_antisymm ?_ (measure_le_inter_add_sdiff _ _ _)
  rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
  replace hs'm : NullMeasurableSet s' μ := hs'm.nullMeasurableSet
  calc
    μ (s inter t) + μ (s \ t) <= μ (s' inter t) + μ (s' \ t) := by gcongr
    _ = μ (s' inter t union s' \ t) :=
      (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
          (@disjoint_inf_sdiff _ s' t _).aedisjoint).symm
    _ = μ s' := congr_arg μ (inter_union_sdiff _ _)
    _ = μ s := hs'

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff₀ := measure_inter_add_sdiff₀

/--
theorem `measure_sdiff_symm` / 定理 `measure_sdiff_symm`

English:
theorem measure_sdiff_symm
  statement: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: by
  rw [← ENNReal.add_right_inj hfin]; rw [measure_inter_add_sdiff₀ _ ht]; rw [inter_comm]; rw [measure_inter_add_sdiff₀ _ hs]; rw [h]

@[deprecated (since := "2026-06-03")] alias measure_diff_symm := measure_sdiff_symm

中文:
定理 measure_sdiff_symm
  结论: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: by
  rw [← ENNReal.add_right_inj hfin]; rw [measure_inter_add_sdiff₀ _ ht]; rw [inter_comm]; rw [measure_inter_add_sdiff₀ _ hs]; rw [h]

@[deprecated (since := "2026-06-03")] alias measure_diff_symm := measure_sdiff_symm

Depends on / 依赖: ENNReal, ENNReal.add_right_inj, add_right_inj, inter_comm
-/
theorem measure_sdiff_symm (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (h : μ s = μ t) (hfin : μ (s inter t) != ∞) : μ (s \ t) = μ (t \ s) := by
  rw [← ENNReal.add_right_inj hfin]; rw [measure_inter_add_sdiff₀ _ ht]; rw [inter_comm]; rw [measure_inter_add_sdiff₀ _ hs]; rw [h]

@[deprecated (since := "2026-06-03")] alias measure_diff_symm := measure_sdiff_symm

/--
theorem `measure_union_add_inter₀` / 定理 `measure_union_add_inter₀`

English:
theorem measure_union_add_inter₀
  given: (s : Set α) (ht : NullMeasurableSet t μ)
  proof: by
  rw [← measure_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

中文:
定理 measure_union_add_inter₀
  条件: (s : 集合 α) (ht : NullMeasurableSet t μ)
  证明: by
  rw [← measure_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

Depends on / 依赖: add_assoc, add_comm, add_right_comm, union_inter_cancel_right, union_sdiff_right
-/
theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s union t) + μ (s inter t) = μ s + μ t := by
  rw [← measure_inter_add_sdiff₀ (s union t) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff₀ s ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

/--
theorem `measure_union_add_inter₀'` / 定理 `measure_union_add_inter₀'`

English:
theorem measure_union_add_inter₀'
  given: (hs : NullMeasurableSet s μ) (t : Set α)
  proof: by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter₀ t hs]; rw [add_comm]

中文:
定理 measure_union_add_inter₀'
  条件: (hs : NullMeasurableSet s μ) (t : 集合 α)
  证明: by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter₀ t hs]; rw [add_comm]

Depends on / 依赖: add_comm, inter_comm, union_comm
-/
theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) :
    μ (s union t) + μ (s inter t) = μ s + μ t := by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter₀ t hs]; rw [add_comm]

/--
theorem `measure_union₀` / 定理 `measure_union₀`

English:
theorem measure_union₀
  given: (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
  proof: by rw [← measure_union_add_inter₀ s ht, hd, add_zero]

中文:
定理 measure_union₀
  条件: (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
  证明: by rw [← measure_union_add_inter₀ s ht, hd, add_zero]

Depends on / 依赖: add_zero
-/
theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t) :
    μ (s union t) = μ s + μ t := by rw [← measure_union_add_inter₀ s ht, hd, add_zero]

/--
theorem `measure_union₀'` / 定理 `measure_union₀'`

English:
theorem measure_union₀'
  given: (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
  proof: by rw [union_comm, measure_union₀ hs (AEDisjoint.symm hd), add_comm]

中文:
定理 measure_union₀'
  条件: (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
  证明: by rw [union_comm, measure_union₀ hs (AEDisjoint.symm hd), add_comm]

Depends on / 依赖: AEDisjoint, AEDisjoint.symm, add_comm, union_comm
-/
theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t) :
    μ (s union t) = μ s + μ t := by rw [union_comm, measure_union₀ hs (AEDisjoint.symm hd), add_comm]

/--
theorem `measure_add_measure_compl₀` / 定理 `measure_add_measure_compl₀`

English:
theorem measure_add_measure_compl₀
  given: {s : Set α} (hs : NullMeasurableSet s μ)
  proof: by rw [← measure_union₀' hs aedisjoint_compl_right, union_compl_self]

中文:
定理 measure_add_measure_compl₀
  条件: {s : 集合 α} (hs : NullMeasurableSet s μ)
  证明: by rw [← measure_union₀' hs aedisjoint_compl_right, union_compl_self]

Depends on / 依赖: aedisjoint_compl_right, union_compl_self
-/
theorem measure_add_measure_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    μ s + μ sᶜ = μ univ := by rw [← measure_union₀' hs aedisjoint_compl_right, union_compl_self]

/--
lemma `measure_of_measure_compl_eq_zero` / 引理 `measure_of_measure_compl_eq_zero`

English:
lemma measure_of_measure_compl_eq_zero
  given: (hs : μ sᶜ = 0)
  statement: μ s = μ Set.univ
  proof: by
simpa [hs] using measure_add_measure_compl₀ .of_compl .of_null hs

中文:
引理 measure_of_measure_compl_eq_zero
  条件: (hs : μ sᶜ = 0)
  结论: μ s = μ 集合.univ
  证明: by
simpa [hs] using measure_add_measure_compl₀ .of_compl .of_null hs

Depends on / 依赖: of_compl, of_null
-/
lemma measure_of_measure_compl_eq_zero (hs : μ sᶜ = 0) : μ s = μ Set.univ := by
simpa [hs] using measure_add_measure_compl₀ .of_compl .of_null hs

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

/--
theorem `nullMeasurableSet_singleton` / 定理 `nullMeasurableSet_singleton`

English:
theorem nullMeasurableSet_singleton
  given: (x : α)
  statement: NullMeasurableSet {x} μ
  proof: @measurableSet_singleton _ _ _ _

@[simp]

中文:
定理 nullMeasurableSet_singleton
  条件: (x : α)
  结论: NullMeasurableSet {x} μ
  证明: @measurableSet_singleton _ _ _ _

@[simp]

Depends on / 依赖: measurableSet_singleton
-/
theorem nullMeasurableSet_singleton (x : α) : NullMeasurableSet {x} μ :=
  @measurableSet_singleton _ _ _ _

@[simp]
/--
theorem `nullMeasurableSet_insert` / 定理 `nullMeasurableSet_insert`

English:
theorem nullMeasurableSet_insert
  given: {a : α} {s : Set α}
  proof: measurableSet_insert

中文:
定理 nullMeasurableSet_insert
  条件: {a : α} {s : 集合 α}
  证明: measurableSet_insert

Depends on / 依赖: measurableSet_insert
-/
theorem nullMeasurableSet_insert {a : α} {s : Set α} :
    NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurableSet_insert

/--
theorem `nullMeasurableSet_eq` / 定理 `nullMeasurableSet_eq`

English:
theorem nullMeasurableSet_eq
  given: {a : α}
  statement: NullMeasurableSet { x | x = a } μ
  proof: nullMeasurableSet_singleton a

中文:
定理 nullMeasurableSet_eq
  条件: {a : α}
  结论: NullMeasurableSet { x | x = a } μ
  证明: nullMeasurableSet_singleton a

Depends on / 依赖: nullMeasurableSet_singleton
-/
theorem nullMeasurableSet_eq {a : α} : NullMeasurableSet { x | x = a } μ :=
  nullMeasurableSet_singleton a

/--
theorem `_root_.Set.Finite.nullMeasurableSet` / 定理 `_root_.Set.Finite.nullMeasurableSet`

English:
theorem _root_.Set.Finite.nullMeasurableSet
  given: (hs : s.Finite)
  statement: NullMeasurableSet s μ
  proof: Finite.measurableSet hs

中文:
定理 _root_.集合.有限.nullMeasurableSet
  条件: (hs : s.有限)
  结论: NullMeasurableSet s μ
  证明: Finite.measurableSet hs
-/
protected theorem _root_.Set.Finite.nullMeasurableSet (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurableSet hs

/--
theorem `_root_.Finset.nullMeasurableSet` / 定理 `_root_.Finset.nullMeasurableSet`

English:
theorem _root_.Finset.nullMeasurableSet
  given: (s : Finset α)
  statement: NullMeasurableSet (↑s) μ
  proof: by
  apply Finset.measurableSet

中文:
定理 _root_.有限集.nullMeasurableSet
  条件: (s : 有限集 α)
  结论: NullMeasurableSet (↑s) μ
  证明: by
  apply Finset.measurableSet
-/
protected theorem _root_.Finset.nullMeasurableSet (s : Finset α) : NullMeasurableSet (↑s) μ := by
  apply Finset.measurableSet

end MeasurableSingletonClass

/--
theorem `_root_.Set.Finite.nullMeasurableSet_biUnion` / 定理 `_root_.Set.Finite.nullMeasurableSet_biUnion`

English:
theorem _root_.Set.Finite.nullMeasurableSet_biUnion
  statement: {f : ι -> Set α} {s : Set ι} (hs : s.Finite)
  proof: Finite.measurableSet_biUnion hs h

中文:
定理 _root_.集合.有限.nullMeasurableSet_biUnion
  结论: {f : ι -> 集合 α} {s : 集合 ι} (hs : s.有限)
  证明: Finite.measurableSet_biUnion hs h

Depends on / 依赖: Finite, Finite.measurableSet_biUnion, measurableSet_biUnion
-/
theorem _root_.Set.Finite.nullMeasurableSet_biUnion {f : ι -> Set α} {s : Set ι} (hs : s.Finite)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b in s, f b) μ :=
  Finite.measurableSet_biUnion hs h

/--
theorem `_root_.Finset.nullMeasurableSet_biUnion` / 定理 `_root_.Finset.nullMeasurableSet_biUnion`

English:
theorem _root_.Finset.nullMeasurableSet_biUnion
  statement: {f : ι -> Set α} (s : Finset ι)
  proof: Finset.measurableSet_biUnion s h

中文:
定理 _root_.有限集.nullMeasurableSet_biUnion
  结论: {f : ι -> 集合 α} (s : 有限集 ι)
  证明: Finset.measurableSet_biUnion s h

Depends on / 依赖: Finset, Finset.measurableSet_biUnion, measurableSet_biUnion
-/
theorem _root_.Finset.nullMeasurableSet_biUnion {f : ι -> Set α} (s : Finset ι)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b in s, f b) μ :=
  Finset.measurableSet_biUnion s h

/--
theorem `_root_.Set.Finite.nullMeasurableSet_sUnion` / 定理 `_root_.Set.Finite.nullMeasurableSet_sUnion`

English:
theorem _root_.Set.Finite.nullMeasurableSet_sUnion
  statement: {s : Set (Set α)} (hs : s.Finite)
  proof: Finite.measurableSet_sUnion hs h

中文:
定理 _root_.集合.有限.nullMeasurableSet_sUnion
  结论: {s : 集合 (集合 α)} (hs : s.有限)
  证明: Finite.measurableSet_sUnion hs h

Depends on / 依赖: Finite, Finite.measurableSet_sUnion, measurableSet_sUnion
-/
theorem _root_.Set.Finite.nullMeasurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : forall t in s, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀ s) μ :=
  Finite.measurableSet_sUnion hs h

/--
theorem `_root_.Set.Finite.nullMeasurableSet_biInter` / 定理 `_root_.Set.Finite.nullMeasurableSet_biInter`

English:
theorem _root_.Set.Finite.nullMeasurableSet_biInter
  statement: {f : ι -> Set α} {s : Set ι} (hs : s.Finite)
  proof: Finite.measurableSet_biInter hs h

中文:
定理 _root_.集合.有限.nullMeasurableSet_bi整数er
  结论: {f : ι -> 集合 α} {s : 集合 ι} (hs : s.有限)
  证明: Finite.measurableSet_biInter hs h

Depends on / 依赖: Finite, Finite.measurableSet_biInter, measurableSet_biInter
-/
theorem _root_.Set.Finite.nullMeasurableSet_biInter {f : ι -> Set α} {s : Set ι} (hs : s.Finite)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b in s, f b) μ :=
  Finite.measurableSet_biInter hs h

/--
theorem `_root_.Finset.nullMeasurableSet_biInter` / 定理 `_root_.Finset.nullMeasurableSet_biInter`

English:
theorem _root_.Finset.nullMeasurableSet_biInter
  statement: {f : ι -> Set α} (s : Finset ι)
  proof: s.finite_toSet.nullMeasurableSet_biInter h

中文:
定理 _root_.有限集.nullMeasurableSet_bi整数er
  结论: {f : ι -> 集合 α} (s : 有限集 ι)
  证明: s.finite_toSet.nullMeasurableSet_biInter h

Depends on / 依赖: finite_toSet, nullMeasurableSet_biInter, s.finite_toSet.nullMeasurableSet_biInter
-/
theorem _root_.Finset.nullMeasurableSet_biInter {f : ι -> Set α} (s : Finset ι)
    (h : forall b in s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b in s, f b) μ :=
  s.finite_toSet.nullMeasurableSet_biInter h

/--
theorem `_root_.Set.Finite.nullMeasurableSet_sInter` / 定理 `_root_.Set.Finite.nullMeasurableSet_sInter`

English:
theorem _root_.Set.Finite.nullMeasurableSet_sInter
  statement: {s : Set (Set α)} (hs : s.Finite)
  proof: NullMeasurableSet.sInter (Finite.countable hs) h

中文:
定理 _root_.集合.有限.nullMeasurableSet_s整数er
  结论: {s : 集合 (集合 α)} (hs : s.有限)
  证明: NullMeasurableSet.sInter (Finite.countable hs) h

Depends on / 依赖: Finite, Finite.countable, NullMeasurableSet, NullMeasurableSet.sInter, countable, sInter
-/
theorem _root_.Set.Finite.nullMeasurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : forall t in s, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter (Finite.countable hs) h

/--
theorem `nullMeasurableSet_toMeasurable` / 定理 `nullMeasurableSet_toMeasurable`

English:
theorem nullMeasurableSet_toMeasurable
  statement: NullMeasurableSet (toMeasurable μ s) μ
  proof: (measurableSet_toMeasurable _ _).nullMeasurableSet

中文:
定理 nullMeasurableSet_toMeasurable
  结论: NullMeasurableSet (toMeasurable μ s) μ
  证明: (measurableSet_toMeasurable _ _).nullMeasurableSet

Depends on / 依赖: measurableSet_toMeasurable, nullMeasurableSet
-/
theorem nullMeasurableSet_toMeasurable : NullMeasurableSet (toMeasurable μ s) μ :=
  (measurableSet_toMeasurable _ _).nullMeasurableSet

variable [MeasurableSingletonClass α] {mβ : MeasurableSpace β} [MeasurableSingletonClass β]

/--
lemma `measure_preimage_fst_singleton_eq_tsum` / 引理 `measure_preimage_fst_singleton_eq_tsum`

English:
lemma measure_preimage_fst_singleton_eq_tsum
  given: [Countable β] (μ : Measure (α × β)) (x : α)
  proof: by
  rw [← measure_iUnion (by simp [Pairwise]) fun _ => .singleton _, iUnion_singleton_eq_range,
    preimage_fst_singleton_eq_range]

中文:
引理 measure_preimage_fst_singleton_eq_tsum
  条件: [可数 β] (μ : 测度 (α × β)) (x : α)
  证明: by
  rw [← measure_iUnion (by simp [Pairwise]) fun _ => .singleton _, iUnion_singleton_eq_range,
    preimage_fst_singleton_eq_range]

Depends on / 依赖: Pairwise, iUnion_singleton_eq_range, measure_iUnion, preimage_fst_singleton_eq_range, singleton
-/
lemma measure_preimage_fst_singleton_eq_tsum [Countable β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑' y, μ {(x, y)} := by
  rw [← measure_iUnion (by simp [Pairwise]) fun _ => .singleton _, iUnion_singleton_eq_range,
    preimage_fst_singleton_eq_range]

/--
lemma `measure_preimage_snd_singleton_eq_tsum` / 引理 `measure_preimage_snd_singleton_eq_tsum`

English:
lemma measure_preimage_snd_singleton_eq_tsum
  given: [Countable α] (μ : Measure (α × β)) (y : β)
  proof: by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this]; rw [measure_iUnion] <;> simp [Pairwise]

中文:
引理 measure_preimage_snd_singleton_eq_tsum
  条件: [可数 α] (μ : 测度 (α × β)) (y : β)
  证明: by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this]; rw [measure_iUnion] <;> simp [Pairwise]

Depends on / 依赖: Pairwise, Prod.ext_iff, Prod.snd, eq_comm, ext_iff, measure_iUnion
-/
lemma measure_preimage_snd_singleton_eq_tsum [Countable α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑' x, μ {(x, y)} := by
  have : Prod.snd ⁻¹' {y} = ⋃ x : α, {(x, y)} := by ext y; simp [Prod.ext_iff, eq_comm]
  rw [this]; rw [measure_iUnion] <;> simp [Pairwise]

/--
lemma `measure_preimage_fst_singleton_eq_sum` / 引理 `measure_preimage_fst_singleton_eq_sum`

English:
lemma measure_preimage_fst_singleton_eq_sum
  given: [Fintype β] (μ : Measure (α × β)) (x : α)
  proof: by
  rw [measure_preimage_fst_singleton_eq_tsum μ x]; rw [tsum_fintype]

中文:
引理 measure_preimage_fst_singleton_eq_sum
  条件: [有限类型 β] (μ : 测度 (α × β)) (x : α)
  证明: by
  rw [measure_preimage_fst_singleton_eq_tsum μ x]; rw [tsum_fintype]

Depends on / 依赖: measure_preimage_fst_singleton_eq_tsum, tsum_fintype
-/
lemma measure_preimage_fst_singleton_eq_sum [Fintype β] (μ : Measure (α × β)) (x : α) :
    μ (Prod.fst ⁻¹' {x}) = ∑ y, μ {(x, y)} := by
  rw [measure_preimage_fst_singleton_eq_tsum μ x]; rw [tsum_fintype]

/--
lemma `measure_preimage_snd_singleton_eq_sum` / 引理 `measure_preimage_snd_singleton_eq_sum`

English:
lemma measure_preimage_snd_singleton_eq_sum
  given: [Fintype α] (μ : Measure (α × β)) (y : β)
  proof: by
  rw [measure_preimage_snd_singleton_eq_tsum μ y]; rw [tsum_fintype]

中文:
引理 measure_preimage_snd_singleton_eq_sum
  条件: [有限类型 α] (μ : 测度 (α × β)) (y : β)
  证明: by
  rw [measure_preimage_snd_singleton_eq_tsum μ y]; rw [tsum_fintype]

Depends on / 依赖: measure_preimage_snd_singleton_eq_tsum, tsum_fintype
-/
lemma measure_preimage_snd_singleton_eq_sum [Fintype α] (μ : Measure (α × β)) (y : β) :
    μ (Prod.snd ⁻¹' {y}) = ∑ x, μ {(x, y)} := by
  rw [measure_preimage_snd_singleton_eq_tsum μ y]; rw [tsum_fintype]

end

section NullMeasurable

variable [m : MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α -> β} {μ : Measure α}

/--
Definition of `NullMeasurable` / `NullMeasurable` 的定义

English:
definition NullMeasurable
  signature: (f : α -> β) (μ : Measure α := by volume_tac)
  body: forall ⦃s : Set β⦄, MeasurableSet s -> NullMeasurableSet (f ⁻¹' s) μ

中文:
定义 NullMeasurable
  签名: (f : α -> β) (μ : 测度 α := by volume_tac)
  定义体: forall ⦃s : Set β⦄, MeasurableSet s -> NullMeasurableSet (f ⁻¹' s) μ

Depends on / 依赖: MeasurableSet, NullMeasurableSet, volume_tac
-/
def NullMeasurable (f : α -> β) (μ : Measure α := by volume_tac) : Prop :=
  forall ⦃s : Set β⦄, MeasurableSet s -> NullMeasurableSet (f ⁻¹' s) μ

/--
theorem `_root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable` / 定理 `_root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable`

English:
theorem _root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable
  given: (f : α -> β)
  proof: by rfl

中文:
定理 _root_.测度论.nullMeasurable_iff_eventuallyMeasurable
  条件: (f : α -> β)
  证明: by rfl
-/
theorem _root_.MeasureTheory.nullMeasurable_iff_eventuallyMeasurable (f : α -> β) :
    NullMeasurable f μ ↔ EventuallyMeasurable m (ae μ) f := by rfl

/--
theorem `_root_.Measurable.nullMeasurable` / 定理 `_root_.Measurable.nullMeasurable`

English:
theorem _root_.Measurable.nullMeasurable
  given: (h : Measurable f)
  statement: NullMeasurable f μ
  proof: h.eventuallyMeasurable

中文:
定理 _root_.可测.nullMeasurable
  条件: (h : 可测 f)
  结论: NullMeasurable f μ
  证明: h.eventuallyMeasurable
-/
protected theorem _root_.Measurable.nullMeasurable (h : Measurable f) : NullMeasurable f μ :=
  h.eventuallyMeasurable

/--
theorem `NullMeasurable.measurable'` / 定理 `NullMeasurable.measurable'`

English:
theorem NullMeasurable.measurable'
  given: (h : NullMeasurable f μ)
  proof: h

中文:
定理 NullMeasurable.measurable'
  条件: (h : NullMeasurable f μ)
  证明: h
-/
protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) :
    @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h

/--
theorem `Measurable.comp_nullMeasurable` / 定理 `Measurable.comp_nullMeasurable`

English:
theorem Measurable.comp_nullMeasurable
  given: {g : β -> γ} (hg : Measurable g) (hf : NullMeasurable f μ)
  proof: by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact hg.comp_eventuallyMeasurable hf

中文:
定理 可测.comp_nullMeasurable
  条件: {g : β -> γ} (hg : 可测 g) (hf : NullMeasurable f μ)
  证明: by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact hg.comp_eventuallyMeasurable hf

Depends on / 依赖: comp_eventuallyMeasurable, hg.comp_eventuallyMeasurable, nullMeasurable_iff_eventuallyMeasurable
-/
theorem Measurable.comp_nullMeasurable {g : β -> γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ := by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact hg.comp_eventuallyMeasurable hf

/--
theorem `NullMeasurable.congr` / 定理 `NullMeasurable.congr`

English:
theorem NullMeasurable.congr
  given: {g : α -> β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g)
  proof: by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact EventuallyMeasurable.congr hf hg.symm

中文:
定理 NullMeasurable.congr
  条件: {g : α -> β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g)
  证明: by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact EventuallyMeasurable.congr hf hg.symm

Depends on / 依赖: EventuallyMeasurable, EventuallyMeasurable.congr, hg.symm, nullMeasurable_iff_eventuallyMeasurable
-/
theorem NullMeasurable.congr {g : α -> β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) :
    NullMeasurable g μ := by
  rw [nullMeasurable_iff_eventuallyMeasurable]
  exact EventuallyMeasurable.congr hf hg.symm

end NullMeasurable

section IsComplete

/--
Definition of `Measure.IsComplete` / `Measure.IsComplete` 的定义

English:
class Measure.IsComplete
  parameters: {_ : MeasurableSpace α} (μ : Measure α)
  axioms and operations (1):
    - out' : forall s, μ s = 0 -> MeasurableSet s

中文:
类 测度.是完备
  参数: {_ : 可测空间 α} (μ : 测度 α)
  公理与运算 (1 个):
    - out' : 对任意 s, μ s = 0 -> 可测集 s
-/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : forall s, μ s = 0 -> MeasurableSet s

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

/--
theorem `Measure.isComplete_iff` / 定理 `Measure.isComplete_iff`

English:
theorem Measure.isComplete_iff
  statement: μ.IsComplete ↔ forall s, μ s = 0 -> MeasurableSet s
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 测度.isComplete_iff
  结论: μ.是完备 ↔ 对任意 s, μ s = 0 -> 可测集 s
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem Measure.isComplete_iff : μ.IsComplete ↔ forall s, μ s = 0 -> MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `Measure.IsComplete.out` / 定理 `Measure.IsComplete.out`

English:
theorem Measure.IsComplete.out
  given: (h : μ.IsComplete)
  statement: forall s, μ s = 0 -> MeasurableSet s
  proof: h.1

中文:
定理 测度.是完备.out
  条件: (h : μ.是完备)
  结论: 对任意 s, μ s = 0 -> 可测集 s
  证明: h.1
-/
theorem Measure.IsComplete.out (h : μ.IsComplete) : forall s, μ s = 0 -> MeasurableSet s :=
  h.1

/--
theorem `measurableSet_of_null` / 定理 `measurableSet_of_null`

English:
theorem measurableSet_of_null
  given: [μ.IsComplete] (hs : μ s = 0)
  statement: MeasurableSet s
  proof: MeasureTheory.Measure.IsComplete.out' s hs

中文:
定理 measurableSet_of_null
  条件: [μ.是完备] (hs : μ s = 0)
  结论: 可测集 s
  证明: MeasureTheory.Measure.IsComplete.out' s hs

Depends on / 依赖: IsComplete, Measure, MeasureTheory, MeasureTheory.Measure.IsComplete.out
-/
theorem measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs

/--
theorem `NullMeasurableSet.measurable_of_complete` / 定理 `NullMeasurableSet.measurable_of_complete`

English:
theorem NullMeasurableSet.measurable_of_complete
  given: (hs : NullMeasurableSet s μ) [μ.IsComplete]
  proof: sdiff_sdiff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diff
      (measurableSet_of_null (ae_le_set.1 <|
        EventuallyEq.le (NullMeasurableSet.toMeasurable_ae_eq hs)))

中文:
定理 NullMeasurableSet.measurable_of_complete
  条件: (hs : NullMeasurableSet s μ) [μ.是完备]
  证明: sdiff_sdiff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diff
      (measurableSet_of_null (ae_le_set.1 <|
        EventuallyEq.le (NullMeasurableSet.toMeasurable_ae_eq hs)))

Depends on / 依赖: EventuallyEq, EventuallyEq.le, NullMeasurableSet, NullMeasurableSet.toMeasurable_ae_eq, ae_le_set, measurableSet_of_null, measurableSet_toMeasurable, sdiff_sdiff_cancel_left, subset_toMeasurable, toMeasurable_ae_eq
-/
theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] :
    MeasurableSet s :=
  sdiff_sdiff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diff
      (measurableSet_of_null (ae_le_set.1 <|
        EventuallyEq.le (NullMeasurableSet.toMeasurable_ae_eq hs)))

/--
theorem `NullMeasurable.measurable_of_complete` / 定理 `NullMeasurable.measurable_of_complete`

English:
theorem NullMeasurable.measurable_of_complete
  statement: [μ.IsComplete] {_m1 : MeasurableSpace β} {f : α -> β}
  proof: fun _s hs => (hf hs).measurable_of_complete

中文:
定理 NullMeasurable.measurable_of_complete
  结论: [μ.是完备] {_m1 : 可测空间 β} {f : α -> β}
  证明: fun _s hs => (hf hs).measurable_of_complete

Depends on / 依赖: measurable_of_complete
-/
theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {_m1 : MeasurableSpace β} {f : α -> β}
    (hf : NullMeasurable f μ) : Measurable f := fun _s hs => (hf hs).measurable_of_complete

/--
theorem `_root_.Measurable.congr_ae` / 定理 `_root_.Measurable.congr_ae`

English:
theorem _root_.Measurable.congr_ae
  statement: {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  proof: NullMeasurable.measurable_of_complete (NullMeasurable.congr hf.nullMeasurable hfg)

中文:
定理 _root_.可测.congr_ae
  结论: {α β} [可测空间 α] [可测空间 β] {μ : 测度 α}
  证明: NullMeasurable.measurable_of_complete (NullMeasurable.congr hf.nullMeasurable hfg)

Depends on / 依赖: NullMeasurable, NullMeasurable.congr, NullMeasurable.measurable_of_complete, hf.nullMeasurable, measurable_of_complete, nullMeasurable
-/
theorem _root_.Measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [_hμ : μ.IsComplete] {f g : α -> β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  NullMeasurable.measurable_of_complete (NullMeasurable.congr hf.nullMeasurable hfg)

namespace Measure

/--
Definition of `completion` / `completion` 的定义

English:
definition completion
  signature: {_ : MeasurableSpace α} (μ : Measure α)
  body: μ.toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint) hs
  trim_le := by
    nth_rewrite 2 [← μ.trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ fun _ => MeasurableSet.nullMeasurableSet

中文:
定义 completion
  签名: {_ : 可测空间 α} (μ : 测度 α)
  定义体: μ.toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint) hs
  trim_le := by
    nth_rewrite 2 [← μ.trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ fun _ => MeasurableSet.nullMeasurableSet

Depends on / 依赖: toOuterMeasure
-/
def completion {_ : MeasurableSpace α} (μ : Measure α) :
    MeasureTheory.Measure (NullMeasurableSpace α μ) where
  toOuterMeasure := μ.toOuterMeasure
  m_iUnion _ hs hd := measure_iUnion₀ (hd.mono fun _ _ h => h.aedisjoint) hs
  trim_le := by
    nth_rewrite 2 [← μ.trimmed]
    exact OuterMeasure.trim_anti_measurableSpace _ fun _ => MeasurableSet.nullMeasurableSet

/--
Instance `completion.isComplete` / 实例 `completion.isComplete`

English:
instance completion.isComplete
  signature: {_m : MeasurableSpace α} (μ : Measure α)
  body: ⟨fun _z hz => NullMeasurableSet.of_null hz⟩

@[simp]

中文:
实例 completion.isComplete
  签名: {_m : 可测空间 α} (μ : 测度 α)
  定义体: ⟨fun _z hz => NullMeasurableSet.of_null hz⟩

@[simp]

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.of_null, of_null
-/
instance completion.isComplete {_m : MeasurableSpace α} (μ : Measure α) : μ.completion.IsComplete :=
  ⟨fun _z hz => NullMeasurableSet.of_null hz⟩

@[simp]
/--
theorem `coe_completion` / 定理 `coe_completion`

English:
theorem coe_completion
  given: {_ : MeasurableSpace α} (μ : Measure α)
  statement: ⇑μ.completion = μ
  proof: rfl

中文:
定理 coe_completion
  条件: {_ : 可测空间 α} (μ : 测度 α)
  结论: ⇑μ.completion = μ
  证明: rfl
-/
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.completion = μ :=
  rfl

/--
theorem `completion_apply` / 定理 `completion_apply`

English:
theorem completion_apply
  given: {_ : MeasurableSpace α} (μ : Measure α) (s : Set α)
  proof: rfl

@[simp]

中文:
定理 completion_apply
  条件: {_ : 可测空间 α} (μ : 测度 α) (s : 集合 α)
  证明: rfl

@[simp]
-/
theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.completion s = μ s :=
  rfl

@[simp]
/--
theorem `ae_completion` / 定理 `ae_completion`

English:
theorem ae_completion
  given: {_ : MeasurableSpace α} (μ : Measure α)
  statement: ae μ.completion = ae μ
  proof: rfl

中文:
定理 ae_completion
  条件: {_ : 可测空间 α} (μ : 测度 α)
  结论: ae μ.completion = ae μ
  证明: rfl
-/
theorem ae_completion {_ : MeasurableSpace α} (μ : Measure α) : ae μ.completion = ae μ := rfl

end Measure

end IsComplete

end MeasureTheory
