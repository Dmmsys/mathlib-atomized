/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.Measurability

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/

@[expose] public section

assert_not_exists Covariant MonoidWithZero

open Set Encodable Function Equiv

variable {α β γ δ δ' : Type*} {ι : Sort*} {s t u : Set α}

/--
Definition of `MeasurableSpace` / `MeasurableSpace` 的定义

English:
structure MeasurableSpace
  parameters: (α : Type*)
  axioms and operations (4):
    - MeasurableSet' : Set α -> Prop
    - measurableSet_empty : MeasurableSet' ∅
    - measurableSet_compl : forall s, MeasurableSet' s -> MeasurableSet' sᶜ
    - measurableSet_iUnion : forall f : Nat -> Set α, (forall i, MeasurableSet' (f i)) -> MeasurableSet' (⋃ i, f i)

中文:
结构 可测空间
  参数: (α : 类型)
  公理与运算 (4 个):
    - MeasurableSet' : 集合 α -> 命题
    - measurableSet_empty : 可测集' ∅
    - measurableSet_compl : 对任意 s, 可测集' s -> 可测集' sᶜ
    - measurableSet_iUnion : 对任意 f : 自然数 -> 集合 α, (对任意 i, 可测集' (f i)) -> 可测集' (⋃ i, f i)
-/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α -> Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : forall s, MeasurableSet' s -> MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : forall f : Nat -> Set α, (forall i, MeasurableSet' (f i)) -> MeasurableSet' (⋃ i, f i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : MeasurableSpace α] : MeasurableSpace αᵒᵈ
  body: h

中文:
实例 [h
  签名: : 可测空间 α] : 可测空间 αᵒᵈ
  定义体: h
-/
instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h

/--
Definition of `MeasurableSet` / `MeasurableSet` 的定义

English:
definition MeasurableSet
  signature: [MeasurableSpace α] (s : Set α)
  body: ‹MeasurableSpace α›.MeasurableSet' s

中文:
定义 可测集
  签名: [可测空间 α] (s : 集合 α)
  定义体: ‹MeasurableSpace α›.MeasurableSet' s

Depends on / 依赖: MeasurableSet, MeasurableSpace
-/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s

/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/
scoped[MeasureTheory] notation "MeasurableSet[" m "]" => @MeasurableSet _ m

open MeasureTheory

section

open scoped symmDiff

@[simp, measurability]
/--
theorem `MeasurableSet.empty` / 定理 `MeasurableSet.empty`

English:
theorem MeasurableSet.empty
  given: [MeasurableSpace α]
  statement: MeasurableSet (∅ : Set α)
  proof: MeasurableSpace.measurableSet_empty _

中文:
定理 可测集.empty
  条件: [可测空间 α]
  结论: 可测集 (∅ : 集合 α)
  证明: MeasurableSpace.measurableSet_empty _

Depends on / 依赖: MeasurableSpace, MeasurableSpace.measurableSet_empty, measurableSet_empty
-/
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  MeasurableSpace.measurableSet_empty _

variable {m : MeasurableSpace α}

@[measurability]
/--
theorem `MeasurableSet.compl` / 定理 `MeasurableSet.compl`

English:
theorem MeasurableSet.compl
  statement: MeasurableSet s -> MeasurableSet sᶜ
  proof: MeasurableSpace.measurableSet_compl _ s

中文:
定理 可测集.compl
  结论: 可测集 s -> 可测集 sᶜ
  证明: MeasurableSpace.measurableSet_compl _ s
-/
protected theorem MeasurableSet.compl : MeasurableSet s -> MeasurableSet sᶜ :=
  MeasurableSpace.measurableSet_compl _ s

/--
theorem `MeasurableSet.of_compl` / 定理 `MeasurableSet.of_compl`

English:
theorem MeasurableSet.of_compl
  given: (h : MeasurableSet sᶜ)
  statement: MeasurableSet s
  proof: compl_compl s ▸ h.compl

@[simp]

中文:
定理 可测集.of_compl
  条件: (h : 可测集 sᶜ)
  结论: 可测集 s
  证明: compl_compl s ▸ h.compl

@[simp]
-/
protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
/--
theorem `MeasurableSet.compl_iff` / 定理 `MeasurableSet.compl_iff`

English:
theorem MeasurableSet.compl_iff
  statement: MeasurableSet sᶜ ↔ MeasurableSet s
  proof: ⟨.of_compl, .compl⟩

@[simp, measurability]

中文:
定理 可测集.compl_iff
  结论: 可测集 sᶜ ↔ 可测集 s
  证明: ⟨.of_compl, .compl⟩

@[simp, measurability]

Depends on / 依赖: of_compl
-/
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩

@[simp, measurability]
/--
theorem `MeasurableSet.univ` / 定理 `MeasurableSet.univ`

English:
theorem MeasurableSet.univ
  statement: MeasurableSet (univ : Set α)
  proof: .of_compl by simp

@[nontriviality, measurability]

中文:
定理 可测集.univ
  结论: 可测集 (univ : 集合 α)
  证明: .of_compl by simp

@[nontriviality, measurability]
-/
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
.of_compl by simp

@[nontriviality, measurability]
/--
theorem `Subsingleton.measurableSet` / 定理 `Subsingleton.measurableSet`

English:
theorem Subsingleton.measurableSet
  given: [Subsingleton α] {s : Set α}
  statement: MeasurableSet s
  proof: Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

中文:
定理 子单例.measurableSet
  条件: [子单例 α] {s : 集合 α}
  结论: 可测集 s
  证明: Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.univ, Subsingleton, Subsingleton.set_cases, set_cases
-/
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

/--
theorem `MeasurableSet.congr` / 定理 `MeasurableSet.congr`

English:
theorem MeasurableSet.congr
  given: {s t : Set α} (hs : MeasurableSet s) (h : s = t)
  statement: MeasurableSet t
  proof: by
  rwa [← h]

@[measurability]

中文:
定理 可测集.congr
  条件: {s t : 集合 α} (hs : 可测集 s) (h : s = t)
  结论: 可测集 t
  证明: by
  rwa [← h]

@[measurability]
-/
theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

@[measurability]
/--
theorem `MeasurableSet.iUnion` / 定理 `MeasurableSet.iUnion`

English:
theorem MeasurableSet.iUnion
  given: [Countable ι] ⦃f
  statement: ι -> Set α⦄
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _

中文:
定理 可测集.iUnion
  条件: [可数 ι] ⦃f
  结论: ι -> 集合 α⦄
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _
-/
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι -> Set α⦄
    (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _

/--
theorem `MeasurableSet.biUnion` / 定理 `MeasurableSet.biUnion`

English:
theorem MeasurableSet.biUnion
  statement: {f : β -> Set α} {s : Set β} (hs : s.Countable)
  proof: by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)

中文:
定理 可测集.biUnion
  结论: {f : β -> 集合 α} {s : 集合 β} (hs : s.可数)
  证明: by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)
-/
protected theorem MeasurableSet.biUnion {f : β -> Set α} {s : Set β} (hs : s.Countable)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b in s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)

/--
theorem `Set.Finite.measurableSet_biUnion` / 定理 `Set.Finite.measurableSet_biUnion`

English:
theorem Set.Finite.measurableSet_biUnion
  statement: {f : β -> Set α} {s : Set β} (hs : s.Finite)
  proof: .biUnion hs.countable h

中文:
定理 集合.有限.measurableSet_biUnion
  结论: {f : β -> 集合 α} {s : 集合 β} (hs : s.有限)
  证明: .biUnion hs.countable h

Depends on / 依赖: biUnion, countable, hs.countable
-/
theorem Set.Finite.measurableSet_biUnion {f : β -> Set α} {s : Set β} (hs : s.Finite)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b in s, f b) :=
  .biUnion hs.countable h

/--
theorem `Finset.measurableSet_biUnion` / 定理 `Finset.measurableSet_biUnion`

English:
theorem Finset.measurableSet_biUnion
  statement: {f : β -> Set α} (s : Finset β)
  proof: s.finite_toSet.measurableSet_biUnion h

中文:
定理 有限集.measurableSet_biUnion
  结论: {f : β -> 集合 α} (s : 有限集 β)
  证明: s.finite_toSet.measurableSet_biUnion h

Depends on / 依赖: finite_toSet, measurableSet_biUnion, s.finite_toSet.measurableSet_biUnion
-/
theorem Finset.measurableSet_biUnion {f : β -> Set α} (s : Finset β)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b in s, f b) :=
  s.finite_toSet.measurableSet_biUnion h

/--
theorem `MeasurableSet.sUnion` / 定理 `MeasurableSet.sUnion`

English:
theorem MeasurableSet.sUnion
  statement: {s : Set (Set α)} (hs : s.Countable)
  proof: by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h

中文:
定理 可测集.集合并集
  结论: {s : 集合 (集合 α)} (hs : s.可数)
  证明: by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h
-/
protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : forall t in s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h

/--
theorem `Set.Finite.measurableSet_sUnion` / 定理 `Set.Finite.measurableSet_sUnion`

English:
theorem Set.Finite.measurableSet_sUnion
  statement: {s : Set (Set α)} (hs : s.Finite)
  proof: MeasurableSet.sUnion hs.countable h

@[measurability]

中文:
定理 集合.有限.measurableSet_sUnion
  结论: {s : 集合 (集合 α)} (hs : s.有限)
  证明: MeasurableSet.sUnion hs.countable h

@[measurability]

Depends on / 依赖: MeasurableSet, MeasurableSet.sUnion, countable, hs.countable, sUnion
-/
theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : forall t in s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h

@[measurability]
/--
theorem `MeasurableSet.iInter` / 定理 `MeasurableSet.iInter`

English:
theorem MeasurableSet.iInter
  given: [Countable ι] {f : ι -> Set α} (h : forall b, MeasurableSet (f b))
  proof: .of_compl by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

中文:
定理 可测集.i整数er
  条件: [可数 ι] {f : ι -> 集合 α} (h : 对任意 b, 可测集 (f b))
  证明: .of_compl by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

Depends on / 依赖: compl_iInter, iUnion, of_compl
-/
theorem MeasurableSet.iInter [Countable ι] {f : ι -> Set α} (h : forall b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
.of_compl by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

/--
theorem `MeasurableSet.biInter` / 定理 `MeasurableSet.biInter`

English:
theorem MeasurableSet.biInter
  statement: {f : β -> Set α} {s : Set β} (hs : s.Countable)
  proof: .of_compl by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

中文:
定理 可测集.bi整数er
  结论: {f : β -> 集合 α} {s : 集合 β} (hs : s.可数)
  证明: .of_compl by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

Depends on / 依赖: biUnion, of_compl
-/
theorem MeasurableSet.biInter {f : β -> Set α} {s : Set β} (hs : s.Countable)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b) :=
.of_compl by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

/--
theorem `Set.Finite.measurableSet_biInter` / 定理 `Set.Finite.measurableSet_biInter`

English:
theorem Set.Finite.measurableSet_biInter
  statement: {f : β -> Set α} {s : Set β} (hs : s.Finite)
  proof: .biInter hs.countable h

中文:
定理 集合.有限.measurableSet_bi整数er
  结论: {f : β -> 集合 α} {s : 集合 β} (hs : s.有限)
  证明: .biInter hs.countable h

Depends on / 依赖: biInter, countable, hs.countable
-/
theorem Set.Finite.measurableSet_biInter {f : β -> Set α} {s : Set β} (hs : s.Finite)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b) :=
  .biInter hs.countable h

/--
theorem `Finset.measurableSet_biInter` / 定理 `Finset.measurableSet_biInter`

English:
theorem Finset.measurableSet_biInter
  statement: {f : β -> Set α} (s : Finset β)
  proof: s.finite_toSet.measurableSet_biInter h

中文:
定理 有限集.measurableSet_bi整数er
  结论: {f : β -> 集合 α} (s : 有限集 β)
  证明: s.finite_toSet.measurableSet_biInter h

Depends on / 依赖: finite_toSet, measurableSet_biInter, s.finite_toSet.measurableSet_biInter
-/
theorem Finset.measurableSet_biInter {f : β -> Set α} (s : Finset β)
    (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b) :=
  s.finite_toSet.measurableSet_biInter h

/--
theorem `MeasurableSet.sInter` / 定理 `MeasurableSet.sInter`

English:
theorem MeasurableSet.sInter
  given: {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, MeasurableSet t)
  proof: by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

中文:
定理 可测集.集合交集
  条件: {s : 集合 (集合 α)} (hs : s.可数) (h : 对任意 t in s, 可测集 t)
  证明: by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

Depends on / 依赖: MeasurableSet, MeasurableSet.biInter, biInter, sInter_eq_biInter
-/
theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

/--
theorem `Set.Finite.measurableSet_sInter` / 定理 `Set.Finite.measurableSet_sInter`

English:
theorem Set.Finite.measurableSet_sInter
  statement: {s : Set (Set α)} (hs : s.Finite)
  proof: MeasurableSet.sInter hs.countable h

@[simp, measurability]

中文:
定理 集合.有限.measurableSet_s整数er
  结论: {s : 集合 (集合 α)} (hs : s.有限)
  证明: MeasurableSet.sInter hs.countable h

@[simp, measurability]

Depends on / 依赖: MeasurableSet, MeasurableSet.sInter, countable, hs.countable, sInter
-/
theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : forall t in s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h

@[simp, measurability]
/--
theorem `MeasurableSet.union` / 定理 `MeasurableSet.union`

English:
theorem MeasurableSet.union
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]

中文:
定理 可测集.union
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
-/
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ union s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
/--
theorem `MeasurableSet.inter` / 定理 `MeasurableSet.inter`

English:
theorem MeasurableSet.inter
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]

中文:
定理 可测集.inter
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
-/
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ inter s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
/--
theorem `MeasurableSet.diff` / 定理 `MeasurableSet.diff`

English:
theorem MeasurableSet.diff
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: h₁.inter h₂.compl

@[simp, measurability]

中文:
定理 可测集.diff
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: h₁.inter h₂.compl

@[simp, measurability]
-/
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp, measurability]
/--
lemma `MeasurableSet.himp` / 引理 `MeasurableSet.himp`

English:
lemma MeasurableSet.himp
  given: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
  proof: by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]

中文:
引理 可测集.himp
  条件: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁) (h₂ : 可测集 s₂)
  证明: by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
-/
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
/--
theorem `MeasurableSet.symmDiff` / 定理 `MeasurableSet.symmDiff`

English:
theorem MeasurableSet.symmDiff
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]

中文:
定理 可测集.symmDiff
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
-/
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
/--
lemma `MeasurableSet.bihimp` / 引理 `MeasurableSet.bihimp`

English:
lemma MeasurableSet.bihimp
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]

中文:
引理 可测集.bihimp
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
-/
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
/--
theorem `MeasurableSet.ite` / 定理 `MeasurableSet.ite`

English:
theorem MeasurableSet.ite
  statement: {t s₁ s₂ : Set α} (ht : MeasurableSet t)
  proof: (h₁.inter ht).union (h₂.diff ht)

中文:
定理 可测集.ite
  结论: {t s₁ s₂ : 集合 α} (ht : 可测集 t)
  证明: (h₁.inter ht).union (h₂.diff ht)
-/
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

open scoped Classical in
/--
theorem `MeasurableSet.ite'` / 定理 `MeasurableSet.ite'`

English:
theorem MeasurableSet.ite'
  statement: {s t : Set α} {p : Prop} (hs : p -> MeasurableSet s)
  proof: by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]

中文:
定理 可测集.ite'
  结论: {s t : 集合 α} {p : 命题} (hs : p -> 可测集 s)
  证明: by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]

Depends on / 依赖: exacts, split_ifs
-/
theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p -> MeasurableSet s)
    (ht : ¬p -> MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]
/--
theorem `MeasurableSet.cond` / 定理 `MeasurableSet.cond`

English:
theorem MeasurableSet.cond
  statement: {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
  proof: by
  cases i
  exacts [h₂, h₁]

中文:
定理 可测集.cond
  结论: {s₁ s₂ : 集合 α} (h₁ : 可测集 s₁)
  证明: by
  cases i
  exacts [h₂, h₁]
-/
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts [h₂, h₁]

/--
theorem `MeasurableSet.const` / 定理 `MeasurableSet.const`

English:
theorem MeasurableSet.const
  given: (p : Prop)
  statement: MeasurableSet { _a : α | p }
  proof: by
  by_cases p <;> simp [*]

中文:
定理 可测集.const
  条件: (p : 命题)
  结论: 可测集 { _a : α | p }
  证明: by
  by_cases p <;> simp [*]
-/
protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]

/--
lemma `MeasurableSet.imp` / 引理 `MeasurableSet.imp`

English:
lemma MeasurableSet.imp
  statement: {p q : α -> Prop}
  proof: by
  have h_eq : {x | p x -> q x} = {x | p x}ᶜ union {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht

中文:
引理 可测集.imp
  结论: {p q : α -> 命题}
  证明: by
  have h_eq : {x | p x -> q x} = {x | p x}ᶜ union {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht
-/
protected lemma MeasurableSet.imp {p q : α -> Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x -> q x} := by
  have h_eq : {x | p x -> q x} = {x | p x}ᶜ union {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht

/--
lemma `MeasurableSet.iff` / 引理 `MeasurableSet.iff`

English:
lemma MeasurableSet.iff
  statement: {p q : α -> Prop}
  proof: by
  have h_eq : {x | p x ↔ q x} = {x | p x -> q x} inter {x | q x -> p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)

中文:
引理 可测集.iff
  结论: {p q : α -> 命题}
  证明: by
  have h_eq : {x | p x ↔ q x} = {x | p x -> q x} inter {x | q x -> p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)
-/
protected lemma MeasurableSet.iff {p q : α -> Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ↔ q x} := by
  have h_eq : {x | p x ↔ q x} = {x | p x -> q x} inter {x | q x -> p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)

/--
theorem `nonempty_measurable_superset` / 定理 `nonempty_measurable_superset`

English:
theorem nonempty_measurable_superset
  given: (s : Set α)
  statement: Nonempty { t // s subseteq t ∧ MeasurableSet t }
  proof: ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

中文:
定理 nonempty_measurable_superset
  条件: (s : 集合 α)
  结论: 非空 { t // s subseteq t ∧ 可测集 t }
  证明: ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, subset_univ
-/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s subseteq t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end

/--
theorem `MeasurableSpace.measurableSet_injective` / 定理 `MeasurableSpace.measurableSet_injective`

English:
theorem MeasurableSpace.measurableSet_injective
  statement: Injective (@MeasurableSet α)

中文:
定理 可测空间.measurableSet_injective
  结论: 单射 (@可测集 α)
-/
theorem MeasurableSpace.measurableSet_injective : Injective (@MeasurableSet α)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _ => by congr

@[ext]
/--
theorem `MeasurableSpace.ext` / 定理 `MeasurableSpace.ext`

English:
theorem MeasurableSpace.ext
  statement: {m₁ m₂ : MeasurableSpace α}
  proof: measurableSet_injective funext fun s => propext (h s)

中文:
定理 可测空间.ext
  结论: {m₁ m₂ : 可测空间 α}
  证明: measurableSet_injective funext fun s => propext (h s)

Depends on / 依赖: measurableSet_injective, propext
-/
theorem MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α}
    (h : forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂ :=
measurableSet_injective funext fun s => propext (h s)

/--
Definition of `MeasurableSingletonClass` / `MeasurableSingletonClass` 的定义

English:
class MeasurableSingletonClass
  parameters: (α : Type*) [MeasurableSpace α]
  axioms and operations (1):
    - measurableSet_singleton : forall x, MeasurableSet ({x} : Set α)

中文:
类 MeasurableSingleton类
  参数: (α : 类型) [可测空间 α]
  公理与运算 (1 个):
    - measurableSet_singleton : 对任意 x, 可测集 ({x} : 集合 α)
-/
class MeasurableSingletonClass (α : Type*) [MeasurableSpace α] : Prop where
  /-- A singleton is a measurable set. -/
  measurableSet_singleton : forall x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurableSet_singleton)

@[simp]
/--
lemma `MeasurableSet.singleton` / 引理 `MeasurableSet.singleton`

English:
lemma MeasurableSet.singleton
  given: [MeasurableSpace α] [MeasurableSingletonClass α] (a : α)
  proof: measurableSet_singleton a

中文:
引理 可测集.singleton
  条件: [可测空间 α] [MeasurableSingleton类 α] (a : α)
  证明: measurableSet_singleton a

Depends on / 依赖: measurableSet_singleton
-/
lemma MeasurableSet.singleton [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} :=
  measurableSet_singleton a

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/--
theorem `measurableSet_eq` / 定理 `measurableSet_eq`

English:
theorem measurableSet_eq
  given: {a : α}
  statement: MeasurableSet { x | x = a }
  proof: .singleton a

@[measurability]

中文:
定理 measurableSet_eq
  条件: {a : α}
  结论: 可测集 { x | x = a }
  证明: .singleton a

@[measurability]

Depends on / 依赖: singleton
-/
theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } := .singleton a

@[measurability]
/--
theorem `MeasurableSet.insert` / 定理 `MeasurableSet.insert`

English:
theorem MeasurableSet.insert
  given: {s : Set α} (hs : MeasurableSet s) (a : α)
  proof: .union (.singleton a) hs

@[simp]

中文:
定理 可测集.insert
  条件: {s : 集合 α} (hs : 可测集 s) (a : α)
  证明: .union (.singleton a) hs

@[simp]
-/
protected theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  .union (.singleton a) hs

@[simp]
/--
theorem `measurableSet_insert` / 定理 `measurableSet_insert`

English:
theorem measurableSet_insert
  given: {a : α} {s : Set α}
  proof: by
  classical
  exact ⟨fun h =>
    if ha : a in s then by rwa [← insert_eq_of_mem ha]
    else insert_sdiff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩

中文:
定理 measurableSet_insert
  条件: {a : α} {s : 集合 α}
  证明: by
  classical
  exact ⟨fun h =>
    if ha : a in s then by rwa [← insert_eq_of_mem ha]
    else insert_sdiff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩

Depends on / 依赖: classical, h.diff, h.insert, insert, insert_eq_of_mem, insert_sdiff_self_of_notMem, singleton
-/
theorem measurableSet_insert {a : α} {s : Set α} :
    MeasurableSet (insert a s) ↔ MeasurableSet s := by
  classical
  exact ⟨fun h =>
    if ha : a in s then by rwa [← insert_eq_of_mem ha]
    else insert_sdiff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩

/--
theorem `Set.Subsingleton.measurableSet` / 定理 `Set.Subsingleton.measurableSet`

English:
theorem Set.Subsingleton.measurableSet
  given: {s : Set α} (hs : s.Subsingleton)
  statement: MeasurableSet s
  proof: hs.induction_on .empty .singleton

中文:
定理 集合.子单例.measurableSet
  条件: {s : 集合 α} (hs : s.子单例)
  结论: 可测集 s
  证明: hs.induction_on .empty .singleton

Depends on / 依赖: hs.induction_on, induction_on, singleton
-/
theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on .empty .singleton

/--
theorem `Set.Finite.measurableSet` / 定理 `Set.Finite.measurableSet`

English:
theorem Set.Finite.measurableSet
  given: {s : Set α} (hs : s.Finite)
  statement: MeasurableSet s
  proof: Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]

中文:
定理 集合.有限.measurableSet
  条件: {s : 集合 α} (hs : s.有限)
  结论: 可测集 s
  证明: Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]

Depends on / 依赖: Finite, Finite.induction_on, hsm.insert, induction_on, insert
-/
theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]
/--
theorem `Finset.measurableSet` / 定理 `Finset.measurableSet`

English:
theorem Finset.measurableSet
  given: (s : Finset α)
  statement: MeasurableSet (↑s : Set α)
  proof: s.finite_toSet.measurableSet

中文:
定理 有限集.measurableSet
  条件: (s : 有限集 α)
  结论: 可测集 (↑s : 集合 α)
  证明: s.finite_toSet.measurableSet
-/
protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.measurableSet

/--
theorem `Set.Countable.measurableSet` / 定理 `Set.Countable.measurableSet`

English:
theorem Set.Countable.measurableSet
  given: {s : Set α} (hs : s.Countable)
  statement: MeasurableSet s
  proof: by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

中文:
定理 集合.可数.measurableSet
  条件: {s : 集合 α} (hs : s.可数)
  结论: 可测集 s
  证明: by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

Depends on / 依赖: biUnion, biUnion_of_singleton, singleton
-/
theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

end MeasurableSingletonClass

namespace MeasurableSpace

/-- Copy of a `MeasurableSpace` with a new `MeasurableSet` equal to the old one. Useful to fix
definitional equalities. -/
@[instance_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (m : MeasurableSpace α) (p : Set α -> Prop) (h : forall s, p s ↔ MeasurableSet[m] s)
  body: p
  measurableSet_empty := by simpa only [h] using! m.measurableSet_empty
  measurableSet_compl := by simpa only [h] using! m.measurableSet_compl
  measurableSet_iUnion := by simpa only [h] using! m.measurableSet_iUnion

中文:
定义 copy
  签名: (m : 可测空间 α) (p : 集合 α -> 命题) (h : 对任意 s, p s ↔ 可测集[m] s)
  定义体: p
  measurableSet_empty := by simpa only [h] using! m.measurableSet_empty
  measurableSet_compl := by simpa only [h] using! m.measurableSet_compl
  measurableSet_iUnion := by simpa only [h] using! m.measurableSet_iUnion
-/
protected def copy (m : MeasurableSpace α) (p : Set α -> Prop) (h : forall s, p s ↔ MeasurableSet[m] s) :
    MeasurableSpace α where
  MeasurableSet' := p
  measurableSet_empty := by simpa only [h] using! m.measurableSet_empty
  measurableSet_compl := by simpa only [h] using! m.measurableSet_compl
  measurableSet_iUnion := by simpa only [h] using! m.measurableSet_iUnion

/--
lemma `measurableSet_copy` / 引理 `measurableSet_copy`

English:
lemma measurableSet_copy
  statement: {m : MeasurableSpace α} {p : Set α -> Prop}
  proof: Iff.rfl

中文:
引理 measurableSet_copy
  结论: {m : 可测空间 α} {p : 集合 α -> 命题}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma measurableSet_copy {m : MeasurableSpace α} {p : Set α -> Prop}
    (h : forall s, p s ↔ MeasurableSet[m] s) {s} : MeasurableSet[.copy m p h] s ↔ p s :=
  Iff.rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: {m : MeasurableSpace α} {p : Set α -> Prop} (h : forall s, p s ↔ MeasurableSet[m] s)
  proof: ext h

中文:
引理 copy_eq
  条件: {m : 可测空间 α} {p : 集合 α -> 命题} (h : 对任意 s, p s ↔ 可测集[m] s)
  证明: ext h
-/
lemma copy_eq {m : MeasurableSpace α} {p : Set α -> Prop} (h : forall s, p s ↔ MeasurableSet[m] s) :
    m.copy p h = m :=
  ext h

section CompleteLattice

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (MeasurableSpace α)
  body: forall s, MeasurableSet[m₁] s -> MeasurableSet[m₂] s

中文:
实例 :
  签名: LE (可测空间 α)
  定义体: forall s, MeasurableSet[m₁] s -> MeasurableSet[m₂] s

Depends on / 依赖: MeasurableSet
-/
instance : LE (MeasurableSpace α) where le m₁ m₂ := forall s, MeasurableSet[m₁] s -> MeasurableSet[m₂] s

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {α} {a b : MeasurableSpace α}
  statement: a <= b ↔ a.MeasurableSet' <= b.MeasurableSet'
  proof: Iff.rfl

中文:
定理 le_def
  条件: {α} {a b : 可测空间 α}
  结论: a <= b ↔ a.可测集' <= b.可测集'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {α} {a b : MeasurableSpace α} : a <= b ↔ a.MeasurableSet' <= b.MeasurableSet' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (MeasurableSpace α)
  body: { PartialOrder.lift (@MeasurableSet α) measurableSet_injective with
    le := LE.le
    lt := fun m₁ m₂ => m₁ <= m₂ ∧ ¬m₂ <= m₁ }

中文:
实例 :
  签名: 偏序 (可测空间 α)
  定义体: { PartialOrder.lift (@MeasurableSet α) measurableSet_injective with
    le := LE.le
    lt := fun m₁ m₂ => m₁ <= m₂ ∧ ¬m₂ <= m₁ }

Depends on / 依赖: LE.le, MeasurableSet, PartialOrder, PartialOrder.lift, measurableSet_injective
-/
instance : PartialOrder (MeasurableSpace α) :=
  { PartialOrder.lift (@MeasurableSet α) measurableSet_injective with
    le := LE.le
    lt := fun m₁ m₂ => m₁ <= m₂ ∧ ¬m₂ <= m₁ }

/--
Inductive type `GenerateMeasurable` / 归纳类型 `GenerateMeasurable`

English:
inductive GenerateMeasurable
  parameters: (s : Set (Set α))
  constructors (4):
    - protected: basic : forall u in s, GenerateMeasurable s u
    - protected: empty : GenerateMeasurable s ∅
    - protected: compl : forall t, GenerateMeasurable s t -> GenerateMeasurable s tᶜ
    - protected: iUnion : forall f : Nat -> Set α, (forall n, GenerateMeasurable s (f n)) -> GenerateMeasurable s (⋃ i, f i)

中文:
归纳类型 GenerateMeasurable
  参数: (s : 集合 (集合 α))
  构造子 (4 个):
    - protected: basic : 对任意 u in s, GenerateMeasurable s u
    - protected: empty : GenerateMeasurable s ∅
    - protected: compl : 对任意 t, GenerateMeasurable s t -> GenerateMeasurable s tᶜ
    - protected: iUnion : 对任意 f : 自然数 -> 集合 α, (对任意 n, GenerateMeasurable s (f n)) -> GenerateMeasurable s (⋃ i, f i)
-/
inductive GenerateMeasurable (s : Set (Set α)) : Set α -> Prop
  | protected basic : forall u in s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : forall t, GenerateMeasurable s t -> GenerateMeasurable s tᶜ
  | protected iUnion : forall f : Nat -> Set α, (forall n, GenerateMeasurable s (f n)) ->
      GenerateMeasurable s (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
@[instance_reducible]
/--
Definition of `generateFrom` / `generateFrom` 的定义

English:
definition generateFrom
  signature: (s : Set (Set α))
  body: GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

中文:
定义 generateFrom
  签名: (s : 集合 (集合 α))
  定义体: GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

Depends on / 依赖: GenerateMeasurable
-/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

/--
theorem `measurableSet_generateFrom` / 定理 `measurableSet_generateFrom`

English:
theorem measurableSet_generateFrom
  given: {s : Set (Set α)} {t : Set α} (ht : t in s)
  proof: .basic t ht

@[elab_as_elim]

中文:
定理 measurableSet_generateFrom
  条件: {s : 集合 (集合 α)} {t : 集合 α} (ht : t in s)
  证明: .basic t ht

@[elab_as_elim]
-/
theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t in s) :
    MeasurableSet[generateFrom s] t :=
  .basic t ht

@[elab_as_elim]
/--
theorem `generateFrom_induction` / 定理 `generateFrom_induction`

English:
theorem generateFrom_induction
  statement: (C : Set (Set α))
  proof: by
  induction hs
  exacts [hC _ ‹_› _, empty, compl _ ‹_› ‹_›, iUnion ‹_› ‹_› ‹_›]

中文:
定理 generateFrom_induction
  结论: (C : 集合 (集合 α))
  证明: by
  induction hs
  exacts [hC _ ‹_› _, empty, compl _ ‹_› ‹_›, iUnion ‹_› ‹_› ‹_›]

Depends on / 依赖: exacts, iUnion
-/
theorem generateFrom_induction (C : Set (Set α))
    (p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop) (hC : forall t in C, forall ht, p t ht)
    (empty : p ∅ (measurableSet_empty _)) (compl : forall t ht, p t ht -> p tᶜ ht.compl)
    (iUnion : forall (s : Nat -> Set α) (hs : forall n, MeasurableSet[generateFrom C] (s n)),
      (forall n, p (s n) (hs n)) -> p (⋃ i, s i) (.iUnion hs)) (s : Set α)
    (hs : MeasurableSet[generateFrom C] s) : p s hs := by
  induction hs
  exacts [hC _ ‹_› _, empty, compl _ ‹_› ‹_›, iUnion ‹_› ‹_› ‹_›]

/--
theorem `generateFrom_le` / 定理 `generateFrom_le`

English:
theorem generateFrom_le
  statement: {s : Set (Set α)} {m : MeasurableSpace α}
  proof: fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf

中文:
定理 generateFrom_le
  结论: {s : 集合 (集合 α)} {m : 可测空间 α}
  证明: fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf

Depends on / 依赖: GenerateMeasurable, ht.recOn, iUnion
-/
theorem generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α}
    (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m :=
  fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf

/--
theorem `generateFrom_le_iff` / 定理 `generateFrom_le_iff`

English:
theorem generateFrom_le_iff
  given: {s : Set (Set α)} (m : MeasurableSpace α)
  proof: Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h

@[simp]

中文:
定理 generateFrom_le_iff
  条件: {s : 集合 (集合 α)} (m : 可测空间 α)
  证明: Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h

@[simp]

Depends on / 依赖: Iff.intro, generateFrom_le, measurableSet_generateFrom
-/
theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s <= m ↔ s subseteq { t | MeasurableSet[m] t } :=
  Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h

@[simp]
/--
theorem `generateFrom_measurableSet` / 定理 `generateFrom_measurableSet`

English:
theorem generateFrom_measurableSet
  given: [MeasurableSpace α]
  proof: le_antisymm (generateFrom_le fun _ => id) fun _ h => measurableSet_generateFrom h

中文:
定理 generateFrom_measurableSet
  条件: [可测空间 α]
  证明: le_antisymm (generateFrom_le fun _ => id) fun _ h => measurableSet_generateFrom h

Depends on / 依赖: generateFrom_le, le_antisymm, measurableSet_generateFrom
-/
theorem generateFrom_measurableSet [MeasurableSpace α] :
    generateFrom {s : Set α | MeasurableSet s} = ‹_› :=
  le_antisymm (generateFrom_le fun _ => id) fun _ h => measurableSet_generateFrom h

/--
theorem `forall_generateFrom_mem_iff_mem_iff` / 定理 `forall_generateFrom_mem_iff_mem_iff`

English:
theorem forall_generateFrom_mem_iff_mem_iff
  given: {S : Set (Set α)} {x y : α}
  proof: by
  refine ⟨fun H s hs => H s (.basic s hs), fun H s => ?_⟩
  apply generateFrom_induction
  · exact fun s hs _ => H s hs
  · rfl
  · exact fun _ _ => Iff.not
  · intro f _ hf
    simp only [mem_iUnion, hf]

中文:
定理 对任意_generateFrom_mem_iff_mem_iff
  条件: {S : 集合 (集合 α)} {x y : α}
  证明: by
  refine ⟨fun H s hs => H s (.basic s hs), fun H s => ?_⟩
  apply generateFrom_induction
  · exact fun s hs _ => H s hs
  · rfl
  · exact fun _ _ => Iff.not
  · intro f _ hf
    simp only [mem_iUnion, hf]

Depends on / 依赖: Iff.not, generateFrom_induction, mem_iUnion
-/
theorem forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} :
    (forall s, MeasurableSet[generateFrom S] s -> (x in s ↔ y in s)) ↔ (forall s in S, x in s ↔ y in s) := by
  refine ⟨fun H s hs => H s (.basic s hs), fun H s => ?_⟩
  apply generateFrom_induction
  · exact fun s hs _ => H s hs
  · rfl
  · exact fun _ _ => Iff.not
  · intro f _ hf
    simp only [mem_iUnion, hf]

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
@[instance_reducible]
/--
Definition of `mkOfClosure` / `mkOfClosure` 的定义

English:
definition mkOfClosure
  signature: (g : Set (Set α)) (hg : { t | MeasurableSet[generateFrom g] t } = g)
  body: (generateFrom g).copy (· in g) Set.ext_iff.1 hg.symm

中文:
定义 mkOfClosure
  签名: (g : 集合 (集合 α)) (hg : { t | 可测集[generateFrom g] t } = g)
  定义体: (generateFrom g).copy (· in g) Set.ext_iff.1 hg.symm
-/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | MeasurableSet[generateFrom g] t } = g) :
    MeasurableSpace α :=
(generateFrom g).copy (· in g) Set.ext_iff.1 hg.symm

/--
theorem `mkOfClosure_sets` / 定理 `mkOfClosure_sets`

English:
theorem mkOfClosure_sets
  given: {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom s] t } = s}
  proof: copy_eq _

中文:
定理 mkOfClosure_sets
  条件: {s : 集合 (集合 α)} {hs : { t | 可测集[generateFrom s] t } = s}
  证明: copy_eq _

Depends on / 依赖: copy_eq
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  copy_eq _

/--
Definition of `giGenerateFrom` / `giGenerateFrom` 的定义

English:
definition giGenerateFrom
  signature: : GaloisInsertion (@generateFrom α) fun m => { t | MeasurableSet[m] t } where
  body: generateFrom_le_iff
  le_l_u _ _ h := measurableSet_generateFrom h
choice g hg := MeasurableSpace.mkOfClosure g le_antisymm hg (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets

中文:
定义 giGenerateFrom
  签名: : Galois嵌入 (@generateFrom α) fun m => { t | 可测集[m] t } where
  定义体: generateFrom_le_iff
  le_l_u _ _ h := measurableSet_generateFrom h
choice g hg := MeasurableSpace.mkOfClosure g le_antisymm hg (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets

Depends on / 依赖: generateFrom_le_iff
-/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | MeasurableSet[m] t } where
  gc _ := generateFrom_le_iff
  le_l_u _ _ h := measurableSet_generateFrom h
choice g hg := MeasurableSpace.mkOfClosure g le_antisymm hg (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (MeasurableSpace α)
  body: giGenerateFrom.liftCompleteLattice

中文:
实例 :
  签名: 完备格 (可测空间 α)
  定义体: giGenerateFrom.liftCompleteLattice

Depends on / 依赖: giGenerateFrom, giGenerateFrom.liftCompleteLattice, liftCompleteLattice
-/
instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MeasurableSpace α)
  body: ⟨⊤⟩

@[gcongr, mono]

中文:
实例 :
  签名: 可居 (可测空间 α)
  定义体: ⟨⊤⟩

@[gcongr, mono]
-/
instance : Inhabited (MeasurableSpace α) := ⟨⊤⟩

@[gcongr, mono]
/--
theorem `generateFrom_mono` / 定理 `generateFrom_mono`

English:
theorem generateFrom_mono
  given: {s t : Set (Set α)} (h : s subseteq t)
  statement: generateFrom s <= generateFrom t
  proof: giGenerateFrom.gc.monotone_l h

中文:
定理 generateFrom_mono
  条件: {s t : 集合 (集合 α)} (h : s subseteq t)
  结论: generateFrom s <= generateFrom t
  证明: giGenerateFrom.gc.monotone_l h

Depends on / 依赖: giGenerateFrom, giGenerateFrom.gc.monotone_l, monotone_l
-/
theorem generateFrom_mono {s t : Set (Set α)} (h : s subseteq t) : generateFrom s <= generateFrom t :=
  giGenerateFrom.gc.monotone_l h

/--
theorem `generateFrom_sup_generateFrom` / 定理 `generateFrom_sup_generateFrom`

English:
theorem generateFrom_sup_generateFrom
  given: {s t : Set (Set α)}
  proof: (@giGenerateFrom α).gc.l_sup.symm

中文:
定理 generateFrom_sup_generateFrom
  条件: {s t : 集合 (集合 α)}
  证明: (@giGenerateFrom α).gc.l_sup.symm

Depends on / 依赖: gc.l_sup.symm, giGenerateFrom, l_sup
-/
theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s union t) :=
  (@giGenerateFrom α).gc.l_sup.symm

/--
lemma `iSup_generateFrom` / 引理 `iSup_generateFrom`

English:
lemma iSup_generateFrom
  given: (s : ι -> Set (Set α))
  proof: (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]

中文:
引理 iSup_generateFrom
  条件: (s : ι -> 集合 (集合 α))
  证明: (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.giGenerateFrom, gc.l_iSup.symm, giGenerateFrom, l_iSup
-/
lemma iSup_generateFrom (s : ι -> Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]
/--
lemma `generateFrom_empty` / 引理 `generateFrom_empty`

English:
lemma generateFrom_empty
  statement: generateFrom (∅ : Set (Set α)) = ⊥
  proof: le_bot_iff.mp (generateFrom_le (by simp))

中文:
引理 generateFrom_empty
  结论: generateFrom (∅ : 集合 (集合 α)) = ⊥
  证明: le_bot_iff.mp (generateFrom_le (by simp))

Depends on / 依赖: generateFrom_le, le_bot_iff, le_bot_iff.mp
-/
lemma generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥ :=
  le_bot_iff.mp (generateFrom_le (by simp))

/--
theorem `generateFrom_singleton_empty` / 定理 `generateFrom_singleton_empty`

English:
theorem generateFrom_singleton_empty
  statement: generateFrom {∅} = (⊥ : MeasurableSpace α)
  proof: bot_unique generateFrom_le by simp [@MeasurableSet.empty α ⊥]

中文:
定理 generateFrom_singleton_empty
  结论: generateFrom {∅} = (⊥ : 可测空间 α)
  证明: bot_unique generateFrom_le by simp [@MeasurableSet.empty α ⊥]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, bot_unique, generateFrom_le
-/
theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) :=
bot_unique generateFrom_le by simp [@MeasurableSet.empty α ⊥]

/--
theorem `generateFrom_singleton_univ` / 定理 `generateFrom_singleton_univ`

English:
theorem generateFrom_singleton_univ
  statement: generateFrom {Set.univ} = (⊥ : MeasurableSpace α)
  proof: bot_unique generateFrom_le by simp

@[simp]

中文:
定理 generateFrom_singleton_univ
  结论: generateFrom {集合.univ} = (⊥ : 可测空间 α)
  证明: bot_unique generateFrom_le by simp

@[simp]

Depends on / 依赖: bot_unique, generateFrom_le
-/
theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpace α) :=
bot_unique generateFrom_le by simp

@[simp]
/--
theorem `generateFrom_insert_univ` / 定理 `generateFrom_insert_univ`

English:
theorem generateFrom_insert_univ
  given: (S : Set (Set α))
  proof: by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_univ]; rw [bot_sup_eq]

@[simp]

中文:
定理 generateFrom_insert_univ
  条件: (S : 集合 (集合 α))
  证明: by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_univ]; rw [bot_sup_eq]

@[simp]

Depends on / 依赖: bot_sup_eq, generateFrom_singleton_univ, generateFrom_sup_generateFrom, insert_eq
-/
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S := by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_univ]; rw [bot_sup_eq]

@[simp]
/--
theorem `generateFrom_insert_empty` / 定理 `generateFrom_insert_empty`

English:
theorem generateFrom_insert_empty
  given: (S : Set (Set α))
  proof: by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_empty]; rw [bot_sup_eq]

中文:
定理 generateFrom_insert_empty
  条件: (S : 集合 (集合 α))
  证明: by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_empty]; rw [bot_sup_eq]

Depends on / 依赖: bot_sup_eq, generateFrom_singleton_empty, generateFrom_sup_generateFrom, insert_eq
-/
theorem generateFrom_insert_empty (S : Set (Set α)) :
    generateFrom (insert ∅ S) = generateFrom S := by
  rw [insert_eq]; rw [← generateFrom_sup_generateFrom]; rw [generateFrom_singleton_empty]; rw [bot_sup_eq]

/--
theorem `measurableSet_bot_iff` / 定理 `measurableSet_bot_iff`

English:
theorem measurableSet_bot_iff
  given: {s : Set α}
  statement: MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ
  proof: let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp +contextual [or_imp]
      measurableSet_iUnion := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

中文:
定理 measurableSet_bot_iff
  条件: {s : 集合 α}
  结论: 可测集[⊥] s ↔ s = ∅ ∨ s = univ
  证明: let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp +contextual [or_imp]
      measurableSet_iUnion := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, MeasurableSet, MeasurableSet.univ, MeasurableSpace, Or.inl, bot_unique, contextual, forall_mem_range, hs.elim, measurableSet_compl, measurableSet_empty, measurableSet_iUnion, or_imp, s.symm, sUnion_mem_empty_univ
-/
theorem measurableSet_bot_iff {s : Set α} : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp +contextual [or_imp]
      measurableSet_iUnion := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

/--
theorem `measurableSet_top` / 定理 `measurableSet_top`

English:
theorem measurableSet_top
  given: {s : Set α}
  statement: MeasurableSet[⊤] s
  proof: trivial

@[simp]

中文:
定理 measurableSet_top
  条件: {s : 集合 α}
  结论: 可测集[⊤] s
  证明: trivial

@[simp]
-/
@[simp, measurability] theorem measurableSet_top {s : Set α} : MeasurableSet[⊤] s := trivial

@[simp]
-- The `m₁` parameter gets filled in by typeclass instance synthesis (for some reason...)
-- so we have to order it *after* `m₂`. Otherwise `simp` can't apply this lemma.
/--
theorem `measurableSet_inf` / 定理 `measurableSet_inf`

English:
theorem measurableSet_inf
  given: {m₂ m₁ : MeasurableSpace α} {s : Set α}
  proof: Iff.rfl

@[simp]

中文:
定理 measurableSet_inf
  条件: {m₂ m₁ : 可测空间 α} {s : 集合 α}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem measurableSet_inf {m₂ m₁ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ MeasurableSet[m₂] s :=
  Iff.rfl

@[simp]
/--
theorem `measurableSet_sInf` / 定理 `measurableSet_sInf`

English:
theorem measurableSet_sInf
  given: {ms : Set (MeasurableSpace α)} {s : Set α}
  proof: show s in ⋂₀ _ ↔ _ by simp

中文:
定理 measurableSet_sInf
  条件: {ms : 集合 (可测空间 α)} {s : 集合 α}
  证明: show s in ⋂₀ _ ↔ _ by simp
-/
theorem measurableSet_sInf {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sInf ms] s ↔ forall m in ms, MeasurableSet[m] s :=
  show s in ⋂₀ _ ↔ _ by simp

/--
theorem `measurableSet_iInf` / 定理 `measurableSet_iInf`

English:
theorem measurableSet_iInf
  given: {ι} {m : ι -> MeasurableSpace α} {s : Set α}
  proof: by
  rw [iInf]; rw [measurableSet_sInf]; rw [forall_mem_range]

中文:
定理 measurableSet_iInf
  条件: {ι} {m : ι -> 可测空间 α} {s : 集合 α}
  证明: by
  rw [iInf]; rw [measurableSet_sInf]; rw [forall_mem_range]

Depends on / 依赖: forall_mem_range, measurableSet_sInf
-/
theorem measurableSet_iInf {ι} {m : ι -> MeasurableSpace α} {s : Set α} :
    MeasurableSet[iInf m] s ↔ forall i, MeasurableSet[m i] s := by
  rw [iInf]; rw [measurableSet_sInf]; rw [forall_mem_range]

/--
theorem `measurableSet_sup` / 定理 `measurableSet_sup`

English:
theorem measurableSet_sup
  given: {m₁ m₂ : MeasurableSpace α} {s : Set α}
  proof: Iff.rfl

中文:
定理 measurableSet_sup
  条件: {m₁ m₂ : 可测空间 α} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊔ m₂] s ↔
      GenerateMeasurable {s | MeasurableSet[m₁] s ∨ MeasurableSet[m₂] s} s :=
  Iff.rfl

/--
theorem `measurableSet_sSup` / 定理 `measurableSet_sSup`

English:
theorem measurableSet_sSup
  given: {ms : Set (MeasurableSpace α)} {s : Set α}
  proof: by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← ofPred_exists]

中文:
定理 measurableSet_sSup
  条件: {ms : 集合 (可测空间 α)} {s : 集合 α}
  证明: by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← ofPred_exists]

Depends on / 依赖: GenerateMeasurable, ofPred_exists
-/
theorem measurableSet_sSup {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sSup ms] s ↔
      GenerateMeasurable { s : Set α | exists m in ms, MeasurableSet[m] s } s := by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← ofPred_exists]

/--
theorem `measurableSet_iSup` / 定理 `measurableSet_iSup`

English:
theorem measurableSet_iSup
  given: {ι} {m : ι -> MeasurableSpace α} {s : Set α}
  proof: by
  unfold iSup
  simp only [measurableSet_sSup, exists_range_iff]

中文:
定理 measurableSet_iSup
  条件: {ι} {m : ι -> 可测空间 α} {s : 集合 α}
  证明: by
  unfold iSup
  simp only [measurableSet_sSup, exists_range_iff]

Depends on / 依赖: exists_range_iff, measurableSet_sSup
-/
theorem measurableSet_iSup {ι} {m : ι -> MeasurableSpace α} {s : Set α} :
    MeasurableSet[iSup m] s ↔ GenerateMeasurable { s : Set α | exists i, MeasurableSet[m i] s } s := by
  unfold iSup
  simp only [measurableSet_sSup, exists_range_iff]

/--
theorem `measurableSpace_iSup_eq` / 定理 `measurableSpace_iSup_eq`

English:
theorem measurableSpace_iSup_eq
  given: (m : ι -> MeasurableSpace α)
  proof: by
  ext s
  rw [measurableSet_iSup]
  rfl

中文:
定理 measurableSpace_iSup_eq
  条件: (m : ι -> 可测空间 α)
  证明: by
  ext s
  rw [measurableSet_iSup]
  rfl

Depends on / 依赖: measurableSet_iSup
-/
theorem measurableSpace_iSup_eq (m : ι -> MeasurableSpace α) :
    ⨆ n, m n = generateFrom { s | exists n, MeasurableSet[m n] s } := by
  ext s
  rw [measurableSet_iSup]
  rfl

/--
theorem `generateFrom_iUnion_measurableSet` / 定理 `generateFrom_iUnion_measurableSet`

English:
theorem generateFrom_iUnion_measurableSet
  given: (m : ι -> MeasurableSpace α)
  proof: (@giGenerateFrom α).l_iSup_u m

中文:
定理 generateFrom_iUnion_measurableSet
  条件: (m : ι -> 可测空间 α)
  证明: (@giGenerateFrom α).l_iSup_u m

Depends on / 依赖: giGenerateFrom, l_iSup_u
-/
theorem generateFrom_iUnion_measurableSet (m : ι -> MeasurableSpace α) :
    generateFrom (⋃ n, { t | MeasurableSet[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_iSup_u m

end CompleteLattice

end MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop, wikidata Q516776]
/--
Definition of `Measurable` / `Measurable` 的定义

English:
definition Measurable
  signature: [MeasurableSpace α] [MeasurableSpace β] (f : α -> β)
  body: forall ⦃t : Set β⦄, MeasurableSet t -> MeasurableSet (f ⁻¹' t)

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

中文:
定义 可测
  签名: [可测空间 α] [可测空间 β] (f : α -> β)
  定义体: forall ⦃t : Set β⦄, MeasurableSet t -> MeasurableSet (f ⁻¹' t)

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

Depends on / 依赖: MeasurableSet
-/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) : Prop :=
  forall ⦃t : Set β⦄, MeasurableSet t -> MeasurableSet (f ⁻¹' t)

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

namespace MeasureTheory

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measurable[" m "]" => @Measurable _ _ m _
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.
-/
scoped notation "Measurable[" mα ", " mβ "]" => @Measurable _ _ mα mβ

end MeasureTheory

section MeasurableFunctions

/--
theorem `measurable_id` / 定理 `measurable_id`

English:
theorem measurable_id
  given: {_ : MeasurableSpace α}
  statement: Measurable (@id α)
  proof: fun _ => id

@[fun_prop]

中文:
定理 measurable_id
  条件: {_ : 可测空间 α}
  结论: 可测 (@id α)
  证明: fun _ => id

@[fun_prop]
-/
theorem measurable_id {_ : MeasurableSpace α} : Measurable (@id α) := fun _ => id

@[fun_prop]
/--
theorem `measurable_id'` / 定理 `measurable_id'`

English:
theorem measurable_id'
  given: {_ : MeasurableSpace α}
  statement: Measurable fun a : α => a
  proof: measurable_id

中文:
定理 measurable_id'
  条件: {_ : 可测空间 α}
  结论: 可测 fun a : α => a
  证明: measurable_id

Depends on / 依赖: measurable_id
-/
theorem measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a := measurable_id

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
@[to_fun]
/--
theorem `Measurable.comp` / 定理 `Measurable.comp`

English:
theorem Measurable.comp
  statement: {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  proof: fun _ h => hf (hg h)

中文:
定理 可测.comp
  结论: {_ : 可测空间 α} {_ : 可测空间 β}
  证明: fun _ h => hf (hg h)
-/
protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β -> γ} {f : α -> β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)

attribute [fun_prop] Measurable.fun_comp

@[deprecated (since := "2026-01-23")] alias Measurable.comp' := Measurable.fun_comp

@[simp, fun_prop]
/--
theorem `measurable_const` / 定理 `measurable_const`

English:
theorem measurable_const
  given: {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α}
  proof: fun s _ => .const (a in s)

@[fun_prop]

中文:
定理 measurable_const
  条件: {_ : 可测空间 α} {_ : 可测空间 β} {a : α}
  证明: fun s _ => .const (a in s)

@[fun_prop]
-/
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a in s)

@[fun_prop]
/--
theorem `Measurable.le` / 定理 `Measurable.le`

English:
theorem Measurable.le
  statement: {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m <= m0)
  proof: fun _ hs => hm _ (hf hs)

中文:
定理 可测.le
  结论: {α} {m m0 : 可测空间 α} {_ : 可测空间 β} (hm : m <= m0)
  证明: fun _ hs => hm _ (hf hs)
-/
theorem Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m <= m0)
    {f : α -> β} (hf : Measurable[m] f) : Measurable[m0] f := fun _ hs => hm _ (hf hs)

end MeasurableFunctions

/--
Definition of `DiscreteMeasurableSpace` / `DiscreteMeasurableSpace` 的定义

English:
class DiscreteMeasurableSpace
  parameters: (α : Type*) [MeasurableSpace α]
  axioms and operations (1):
    - forall_measurableSet : forall s : Set α, MeasurableSet s

中文:
类 DiscreteMeasurable空间
  参数: (α : 类型) [可测空间 α]
  公理与运算 (1 个):
    - forall_measurableSet : 对任意 s : 集合 α, 可测集 s
-/
class DiscreteMeasurableSpace (α : Type*) [MeasurableSpace α] : Prop where
  /-- Do not use this. Use `MeasurableSet.of_discrete` instead. -/
  forall_measurableSet : forall s : Set α, MeasurableSet s

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @DiscreteMeasurableSpace α ⊤
  body: @DiscreteMeasurableSpace.mk _ (_) fun _ => MeasurableSpace.measurableSet_top

中文:
实例 :
  签名: @DiscreteMeasurable空间 α ⊤
  定义体: @DiscreteMeasurableSpace.mk _ (_) fun _ => MeasurableSpace.measurableSet_top

Depends on / 依赖: DiscreteMeasurableSpace, DiscreteMeasurableSpace.mk, MeasurableSpace, MeasurableSpace.measurableSet_top, measurableSet_top
-/
instance : @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk _ (_) fun _ => MeasurableSpace.measurableSet_top

-- See note [lower instance priority]
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteMeasurableSpace
variable [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α] {s : Set α} {f : α -> β}

/--
lemma `MeasurableSet.of_discrete` / 引理 `MeasurableSet.of_discrete`

English:
lemma MeasurableSet.of_discrete
  statement: MeasurableSet s
  proof: DiscreteMeasurableSpace.forall_measurableSet _

中文:
引理 可测集.of_discrete
  结论: 可测集 s
  证明: DiscreteMeasurableSpace.forall_measurableSet _
-/
@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _

/--
lemma `Measurable.of_discrete` / 引理 `Measurable.of_discrete`

English:
lemma Measurable.of_discrete
  statement: Measurable f
  proof: fun _ _ => .of_discrete

中文:
引理 可测.of_discrete
  结论: 可测 f
  证明: fun _ _ => .of_discrete
-/
@[fun_prop] lemma Measurable.of_discrete : Measurable f := fun _ _ => .of_discrete

/-- Warning: Creates a typeclass loop with `MeasurableSingletonClass.toDiscreteMeasurableSpace`.
To be monitored. -/
-- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableSingletonClass :
    MeasurableSingletonClass α where
  measurableSet_singleton _ := .of_discrete

end DiscreteMeasurableSpace
