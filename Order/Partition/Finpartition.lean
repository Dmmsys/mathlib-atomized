/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.SupIndep

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : Finset α` which does not contain `⊥` and whose supremum is `a`.

Finpartitions of a finset are at the heart of Szemerédi's regularity lemma. They are also studied
purely order theoretically in Sperner theory.

## Constructions

We provide many ways to build finpartitions:
* `Finpartition.ofErase`: Builds a finpartition by erasing `⊥` for you.
* `Finpartition.ofSubset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `Finpartition.empty`: The empty finpartition of `⊥`.
* `Finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `Finpartition.discrete`: The discrete finpartition of `s : Finset α` made of singletons.
* `Finpartition.toSubtype`: Turns a finpartition of a type to one of a subtype.
* `Finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `Finpartition.extend`: Extends a finpartition of `a` to a finpartition of `a ⊔ b` by adding `b`
  as a new part.
* `Finpartition.extendOfLE`: Extends a finpartition of `a` to a finpartition of `b` when `a ≤ b`,
  by adding `b \ a` as a new part (if nonempty).
* `Finpartition.restrict`: Restricts a finpartition of `a` to `b` where `b ≤ a` by intersecting
  each part with `b`.
* `Finpartition.ofPairwiseDisjoint`: Builds a finpartition from a finset `parts` of pairwise
  disjoint elements.
* `Finpartition.combine`: Combines a family of partitions of pairwise disjoint elements into a
  partition of their sup.
* `Finpartition.ofExistsUnique`: Builds a finpartition from a collection of parts such that each
  element is in exactly one part.
* `Finpartition.ofSetoid`: With `Fintype α`, constructs the finpartition of `univ : Finset α`
  induced by the equivalence classes of `s : Setoid α`.
* `Finpartition.atomise`: Makes a finpartition of `s : Finset α` by breaking `s` along all finsets
  in `F : Finset (Finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`Finpartition.indiscrete` and `Finpartition.bind` together form the monadic structure of
`Finpartition`.

## Implementation notes

Forbidding `⊥` as a part follows mathematical tradition and is a pragmatic choice concerning
operations on `Finpartition`. Not caring about `⊥` being a part or not breaks extensionality (it's
not because the parts of `P` and the parts of `Q` have the same elements that `P = Q`). Enforcing
`⊥` to be a part makes `Finpartition.bind` uglier and doesn't rid us of the need of
`Finpartition.ofErase`.

## TODO

The order is the wrong way around to make `Finpartition a` a graded order. Is it bad to depart from
the literature and turn the order around?

The specialisation to `Finset α` could be generalised to atomistic orders.
-/

@[expose] public section


open Finset Function

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext]
/--
Definition of `Finpartition` / `Finpartition` 的定义

English:
structure Finpartition
  parameters: [Lattice α] [OrderBot α] (a : α)
  axioms and operations (4):
    - parts : Finset α
    - supIndep : parts.SupIndep id
    - sup_parts : parts.sup id = a
    - bot_notMem : ⊥ ∉ parts

中文:
结构 有限分拆
  参数: [格 α] [有底序 α] (a : α)
  公理与运算 (4 个):
    - parts : 有限集 α
    - supIndep : parts.SupIndep id
    - sup_parts : parts.上确界 id = a
    - bot_notMem : ⊥ ∉ parts
-/
structure Finpartition [Lattice α] [OrderBot α] (a : α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset α
  /-- The partition is supremum-independent -/
  protected supIndep : parts.SupIndep id
  /-- The supremum of the partition is `a` -/
  sup_parts : parts.sup id = a
  /-- No element of the partition is bottom -/
  bot_notMem : ⊥ ∉ parts
  deriving DecidableEq

namespace Finpartition

section Lattice

variable [Lattice α] [OrderBot α]

/-- A `Finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps]
/--
Definition of `ofErase` / `ofErase` 的定义

English:
definition ofErase
  signature: [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupIndep id)
  body: parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  sup_parts := (sup_erase_bot _).trans sup_parts
  bot_notMem := notMem_erase _ _

中文:
定义 ofErase
  签名: [DecidableEq α] {a : α} (parts : 有限集 α) (sup_indep : parts.SupIndep id)
  定义体: parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  sup_parts := (sup_erase_bot _).trans sup_parts
  bot_notMem := notMem_erase _ _

Depends on / 依赖: parts.erase
-/
def ofErase [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupIndep id)
    (sup_parts : parts.sup id = a) : Finpartition a where
  parts := parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  sup_parts := (sup_erase_bot _).trans sup_parts
  bot_notMem := notMem_erase _ _

/-- A `Finpartition` constructor from a bigger existing finpartition. -/
@[simps]
/--
Definition of `ofSubset` / `ofSubset` 的定义

English:
definition ofSubset
  signature: {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts subseteq P.parts)
  body: { parts := parts
    supIndep := P.supIndep.subset subset
    sup_parts := sup_parts
    bot_notMem := fun h => P.bot_notMem (subset h) }

中文:
定义 ofSubset
  签名: {a b : α} (P : 有限分拆 a) {parts : 有限集 α} (subset : parts subseteq P.parts)
  定义体: { parts := parts
    supIndep := P.supIndep.subset subset
    sup_parts := sup_parts
    bot_notMem := fun h => P.bot_notMem (subset h) }

Depends on / 依赖: P.bot_notMem, P.supIndep.subset, bot_notMem, subset, supIndep, sup_parts
-/
def ofSubset {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts subseteq P.parts)
    (sup_parts : parts.sup id = b) : Finpartition b :=
  { parts := parts
    supIndep := P.supIndep.subset subset
    sup_parts := sup_parts
    bot_notMem := fun h => P.bot_notMem (subset h) }

/--
lemma `sum_ofSubset_eq_sum` / 引理 `sum_ofSubset_eq_sum`

English:
lemma sum_ofSubset_eq_sum
  statement: {a b : α} (P : Finpartition a) {parts : Finset α}
  proof: Finset.sum_subset subset hf

中文:
引理 sum_ofSubset_eq_sum
  结论: {a b : α} (P : 有限分拆 a) {parts : 有限集 α}
  证明: Finset.sum_subset subset hf

Depends on / 依赖: Finset, Finset.sum_subset, subset, sum_subset
-/
lemma sum_ofSubset_eq_sum {a b : α} (P : Finpartition a) {parts : Finset α}
    (subset : parts subseteq P.parts) (sup_parts : parts.sup id = b)
    {X : Type*} [AddCommMonoid X] (f : α -> X) (hf : forall p in P.parts, p ∉ parts -> f p = 0) :
    ∑ p in (P.ofSubset subset sup_parts).parts, f p = ∑ p in P.parts, f p :=
  Finset.sum_subset subset hf

/-- Changes the type of a finpartition to an equal one. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {a b : α} (P : Finpartition a) (h : a = b)
  body: P.parts
  supIndep := P.supIndep
  sup_parts := h ▸ P.sup_parts
  bot_notMem := P.bot_notMem

中文:
定义 copy
  签名: {a b : α} (P : 有限分拆 a) (h : a = b)
  定义体: P.parts
  supIndep := P.supIndep
  sup_parts := h ▸ P.sup_parts
  bot_notMem := P.bot_notMem

Depends on / 依赖: P.parts
-/
def copy {a b : α} (P : Finpartition a) (h : a = b) : Finpartition b where
  parts := P.parts
  supIndep := P.supIndep
  sup_parts := h ▸ P.sup_parts
  bot_notMem := P.bot_notMem

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β : Type*} [Lattice β] [OrderBot β] {a : α} (e : α ≃o β) (P : Finpartition a)
  body: P.parts.map e
  supIndep u hu _ hb hbu _ hx hxu := by
    rw [← map_symm_subset] at hu
    simp only [mem_map_equiv] at hb
    have := P.supIndep hu hb (by simp [hbu]) (map_rel e.symm hx) ?_
    · rw [← e.symm.map_bot] at this
      exact e.symm.map_rel_iff.mp this
    · convert! e.symm.map_rel_iff.mpr hxu
      rw [map_finset_sup]; rw [sup_map]
      rfl
  sup_parts := by simp [← P.sup_parts]
  bot_notMem := by
    rw [mem_map_equiv]
    convert! P.bot_notMem
    exact e.symm.map_bot

@[simp]

中文:
定义 map
  签名: {β : 类型} [格 β] [有底序 β] {a : α} (e : α ≃o β) (P : 有限分拆 a)
  定义体: P.parts.map e
  supIndep u hu _ hb hbu _ hx hxu := by
    rw [← map_symm_subset] at hu
    simp only [mem_map_equiv] at hb
    have := P.supIndep hu hb (by simp [hbu]) (map_rel e.symm hx) ?_
    · rw [← e.symm.map_bot] at this
      exact e.symm.map_rel_iff.mp this
    · convert! e.symm.map_rel_iff.mpr hxu
      rw [map_finset_sup]; rw [sup_map]
      rfl
  sup_parts := by simp [← P.sup_parts]
  bot_notMem := by
    rw [mem_map_equiv]
    convert! P.bot_notMem
    exact e.symm.map_bot

@[simp]

Depends on / 依赖: P.parts.map
-/
def map {β : Type*} [Lattice β] [OrderBot β] {a : α} (e : α ≃o β) (P : Finpartition a) :
    Finpartition (e a) where
  parts := P.parts.map e
  supIndep u hu _ hb hbu _ hx hxu := by
    rw [← map_symm_subset] at hu
    simp only [mem_map_equiv] at hb
    have := P.supIndep hu hb (by simp [hbu]) (map_rel e.symm hx) ?_
    · rw [← e.symm.map_bot] at this
      exact e.symm.map_rel_iff.mp this
    · convert! e.symm.map_rel_iff.mpr hxu
      rw [map_finset_sup]; rw [sup_map]
      rfl
  sup_parts := by simp [← P.sup_parts]
  bot_notMem := by
    rw [mem_map_equiv]
    convert! P.bot_notMem
    exact e.symm.map_bot

@[simp]
/--
theorem `parts_map` / 定理 `parts_map`

English:
theorem parts_map
  given: {β : Type*} [Lattice β] [OrderBot β] {a : α} {e : α ≃o β} {P : Finpartition a}
  proof: rfl

中文:
定理 parts_map
  条件: {β : 类型} [格 β] [有底序 β] {a : α} {e : α ≃o β} {P : 有限分拆 a}
  证明: rfl
-/
theorem parts_map {β : Type*} [Lattice β] [OrderBot β] {a : α} {e : α ≃o β} {P : Finpartition a} :
    (P.map e).parts = P.parts.map e := rfl

variable (α)

/-- The empty finpartition. -/
@[simps]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Finpartition (⊥ : α) where
  body: ∅
  supIndep := supIndep_empty _
  sup_parts := Finset.sup_empty
  bot_notMem := notMem_empty ⊥

中文:
定义 empty
  签名: : 有限分拆 (⊥ : α) where
  定义体: ∅
  supIndep := supIndep_empty _
  sup_parts := Finset.sup_empty
  bot_notMem := notMem_empty ⊥
-/
protected def empty : Finpartition (⊥ : α) where
  parts := ∅
  supIndep := supIndep_empty _
  sup_parts := Finset.sup_empty
  bot_notMem := notMem_empty ⊥

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Finpartition (⊥ : α))
  body: ⟨Finpartition.empty α⟩

@[simp]

中文:
实例 :
  签名: 可居 (有限分拆 (⊥ : α))
  定义体: ⟨Finpartition.empty α⟩

@[simp]

Depends on / 依赖: Finpartition, Finpartition.empty
-/
instance : Inhabited (Finpartition (⊥ : α)) :=
  ⟨Finpartition.empty α⟩

@[simp]
/--
theorem `default_eq_empty` / 定理 `default_eq_empty`

English:
theorem default_eq_empty
  statement: (default : Finpartition (⊥ : α)) = Finpartition.empty α
  proof: rfl

中文:
定理 default_eq_empty
  结论: (default : 有限分拆 (⊥ : α)) = 有限分拆.empty α
  证明: rfl
-/
theorem default_eq_empty : (default : Finpartition (⊥ : α)) = Finpartition.empty α :=
  rfl

variable {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps]
/--
Definition of `indiscrete` / `indiscrete` 的定义

English:
definition indiscrete
  signature: (ha : a != ⊥)
  body: {a}
  supIndep := supIndep_singleton _ _
  sup_parts := Finset.sup_singleton
  bot_notMem h := ha (mem_singleton.1 h).symm

中文:
定义 indiscrete
  签名: (ha : a != ⊥)
  定义体: {a}
  supIndep := supIndep_singleton _ _
  sup_parts := Finset.sup_singleton
  bot_notMem h := ha (mem_singleton.1 h).symm
-/
def indiscrete (ha : a != ⊥) : Finpartition a where
  parts := {a}
  supIndep := supIndep_singleton _ _
  sup_parts := Finset.sup_singleton
  bot_notMem h := ha (mem_singleton.1 h).symm

variable (P : Finpartition a)

/--
theorem `le` / 定理 `le`

English:
theorem le
  given: {b : α} (hb : b in P.parts)
  statement: b <= a
  proof: (le_sup hb).trans P.sup_parts.le

中文:
定理 le
  条件: {b : α} (hb : b in P.parts)
  结论: b <= a
  证明: (le_sup hb).trans P.sup_parts.le
-/
protected theorem le {b : α} (hb : b in P.parts) : b <= a :=
  (le_sup hb).trans P.sup_parts.le

/--
theorem `ne_bot` / 定理 `ne_bot`

English:
theorem ne_bot
  given: {b : α} (hb : b in P.parts)
  statement: b != ⊥
  proof: by
  intro h
  refine P.bot_notMem (?_)
  rw [h] at hb
  exact hb

中文:
定理 ne_bot
  条件: {b : α} (hb : b in P.parts)
  结论: b != ⊥
  证明: by
  intro h
  refine P.bot_notMem (?_)
  rw [h] at hb
  exact hb

Depends on / 依赖: P.bot_notMem, bot_notMem
-/
theorem ne_bot {b : α} (hb : b in P.parts) : b != ⊥ := by
  intro h
  refine P.bot_notMem (?_)
  rw [h] at hb
  exact hb

/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  statement: (P.parts : Set α).PairwiseDisjoint id
  proof: P.supIndep.pairwiseDisjoint

中文:
定理 disjoint
  结论: (P.parts : 集合 α).PairwiseDisjoint id
  证明: P.supIndep.pairwiseDisjoint
-/
protected theorem disjoint : (P.parts : Set α).PairwiseDisjoint id :=
  P.supIndep.pairwiseDisjoint

section Apply

variable {β : Type*} {f : α -> β}

/--
theorem `sup_parts_apply` / 定理 `sup_parts_apply`

English:
theorem sup_parts_apply
  statement: [SemilatticeSup β] [OrderBot β] (hf : forall x y, f (x ⊔ y) = f x ⊔ f y)
  proof: (apply_sup_eq_sup_comp f hf hbot).symm.trans (congrArg f P.sup_parts)

中文:
定理 sup_parts_apply
  结论: [SemilatticeSup β] [有底序 β] (hf : 对任意 x y, f (x ⊔ y) = f x ⊔ f y)
  证明: (apply_sup_eq_sup_comp f hf hbot).symm.trans (congrArg f P.sup_parts)

Depends on / 依赖: P.sup_parts, apply_sup_eq_sup_comp, sup_parts, symm.trans
-/
theorem sup_parts_apply [SemilatticeSup β] [OrderBot β] (hf : forall x y, f (x ⊔ y) = f x ⊔ f y)
    (hbot : f ⊥ = ⊥) : P.parts.sup f = f a :=
  (apply_sup_eq_sup_comp f hf hbot).symm.trans (congrArg f P.sup_parts)

/--
theorem `pairwiseDisjoint_apply` / 定理 `pairwiseDisjoint_apply`

English:
theorem pairwiseDisjoint_apply
  statement: [SemilatticeInf β] [OrderBot β] (hf : forall x y, f (x ⊓ y) = f x ⊓ f y)
  proof: by
  intro _ hx _ hy hxy
  have := (P.disjoint hx hy hxy).eq_bot
  simp_all [disjoint_iff, ← hf]

中文:
定理 pairwiseDisjoint_apply
  结论: [SemilatticeInf β] [有底序 β] (hf : 对任意 x y, f (x ⊓ y) = f x ⊓ f y)
  证明: by
  intro _ hx _ hy hxy
  have := (P.disjoint hx hy hxy).eq_bot
  simp_all [disjoint_iff, ← hf]

Depends on / 依赖: P.disjoint, disjoint, disjoint_iff, eq_bot
-/
theorem pairwiseDisjoint_apply [SemilatticeInf β] [OrderBot β] (hf : forall x y, f (x ⊓ y) = f x ⊓ f y)
    (hbot : f ⊥ = ⊥) : (P.parts : Set α).PairwiseDisjoint f := by
  intro _ hx _ hy hxy
  have := (P.disjoint hx hy hxy).eq_bot
  simp_all [disjoint_iff, ← hf]

end Apply

variable {P}

@[simp]
/--
theorem `parts_eq_empty_iff` / 定理 `parts_eq_empty_iff`

English:
theorem parts_eq_empty_iff
  statement: P.parts = ∅ ↔ a = ⊥
  proof: by
  simp_rw [← P.sup_parts]
  refine ⟨fun h => ?_, fun h => eq_empty_iff_forall_notMem.2 fun b hb => P.bot_notMem ?_⟩
  · rw [h]
    exact Finset.sup_empty
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]

@[simp]

中文:
定理 parts_eq_empty_iff
  结论: P.parts = ∅ ↔ a = ⊥
  证明: by
  simp_rw [← P.sup_parts]
  refine ⟨fun h => ?_, fun h => eq_empty_iff_forall_notMem.2 fun b hb => P.bot_notMem ?_⟩
  · rw [h]
    exact Finset.sup_empty
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]

@[simp]

Depends on / 依赖: Finset, Finset.sup_empty, P.bot_notMem, P.sup_parts, bot_notMem, eq_empty_iff_forall_notMem, h.le, le_bot_iff, le_sup, simp_rw, sup_empty, sup_parts
-/
theorem parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ := by
  simp_rw [← P.sup_parts]
  refine ⟨fun h => ?_, fun h => eq_empty_iff_forall_notMem.2 fun b hb => P.bot_notMem ?_⟩
  · rw [h]
    exact Finset.sup_empty
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]

@[simp]
/--
theorem `parts_nonempty_iff` / 定理 `parts_nonempty_iff`

English:
theorem parts_nonempty_iff
  statement: P.parts.Nonempty ↔ a != ⊥
  proof: by
  contrapose!; exact parts_eq_empty_iff

中文:
定理 parts_nonempty_iff
  结论: P.parts.非空 ↔ a != ⊥
  证明: by
  contrapose!; exact parts_eq_empty_iff

Depends on / 依赖: contrapose, parts_eq_empty_iff
-/
theorem parts_nonempty_iff : P.parts.Nonempty ↔ a != ⊥ := by
  contrapose!; exact parts_eq_empty_iff

/--
theorem `parts_nonempty` / 定理 `parts_nonempty`

English:
theorem parts_nonempty
  given: (P : Finpartition a) (ha : a != ⊥)
  statement: P.parts.Nonempty
  proof: parts_nonempty_iff.2 ha

中文:
定理 parts_nonempty
  条件: (P : 有限分拆 a) (ha : a != ⊥)
  结论: P.parts.非空
  证明: parts_nonempty_iff.2 ha

Depends on / 依赖: parts_nonempty_iff
-/
theorem parts_nonempty (P : Finpartition a) (ha : a != ⊥) : P.parts.Nonempty :=
  parts_nonempty_iff.2 ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Finpartition (⊥ : α))
  body: { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P => by
      ext a
      exact iff_of_false (fun h => P.ne_bot h <| le_bot_iff.1 <| P.le h) (notMem_empty a) }

中文:
实例 :
  签名: 唯一 (有限分拆 (⊥ : α))
  定义体: { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P => by
      ext a
      exact iff_of_false (fun h => P.ne_bot h <| le_bot_iff.1 <| P.le h) (notMem_empty a) }

Depends on / 依赖: Finpartition, Inhabited, P.le, P.ne_bot, iff_of_false, le_bot_iff, ne_bot, notMem_empty
-/
instance : Unique (Finpartition (⊥ : α)) :=
  { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P => by
      ext a
      exact iff_of_false (fun h => P.ne_bot h <| le_bot_iff.1 <| P.le h) (notMem_empty a) }

/--
Instance `instNonempty` / 实例 `instNonempty`

English:
instance instNonempty
  signature: : Nonempty (Finpartition a)
  body: by
  by_cases h : a = ⊥
  · rw [h]; exact ⟨Finpartition.empty α⟩
  · exact ⟨Finpartition.indiscrete h⟩

中文:
实例 instNonempty
  签名: : 非空 (有限分拆 a)
  定义体: by
  by_cases h : a = ⊥
  · rw [h]; exact ⟨Finpartition.empty α⟩
  · exact ⟨Finpartition.indiscrete h⟩

Depends on / 依赖: Finpartition, Finpartition.empty, Finpartition.indiscrete, indiscrete
-/
instance instNonempty : Nonempty (Finpartition a) := by
  by_cases h : a = ⊥
  · rw [h]; exact ⟨Finpartition.empty α⟩
  · exact ⟨Finpartition.indiscrete h⟩

-- See note [reducible non-instances]
/--
Definition of `_root_.IsAtom.uniqueFinpartition` / `_root_.IsAtom.uniqueFinpartition` 的定义

English:
abbreviation _root_.IsAtom.uniqueFinpartition
  signature: (ha : IsAtom a)
  body: indiscrete ha.1
  uniq P := by
    have h : forall b in P.parts, b = a := fun _ hb =>
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    refine Iff.trans ⟨h b, ?_⟩ mem_singleton.symm
    rintro rfl
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    simp_rw [← h c hc]
    exact hc

中文:
缩写 _root_.IsAtom.uniqueFinpartition
  签名: (ha : IsAtom a)
  定义体: indiscrete ha.1
  uniq P := by
    have h : forall b in P.parts, b = a := fun _ hb =>
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    refine Iff.trans ⟨h b, ?_⟩ mem_singleton.symm
    rintro rfl
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    simp_rw [← h c hc]
    exact hc

Depends on / 依赖: indiscrete
-/
abbrev _root_.IsAtom.uniqueFinpartition (ha : IsAtom a) : Unique (Finpartition a) where
  default := indiscrete ha.1
  uniq P := by
    have h : forall b in P.parts, b = a := fun _ hb =>
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    refine Iff.trans ⟨h b, ?_⟩ mem_singleton.symm
    rintro rfl
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    simp_rw [← h c hc]
    exact hc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: α] [DecidableEq α] (a
  body: @Fintype.ofSurjective { p : Finset α // p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p } (Finpartition a) _
    (Subtype.fintype _) (fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) fun ⟨_, y, z, w⟩ =>
    ⟨⟨_, y, z, w⟩, rfl⟩

中文:
实例 [有限类型
  签名: α] [DecidableEq α] (a
  定义体: @Fintype.ofSurjective { p : Finset α // p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p } (Finpartition a) _
    (Subtype.fintype _) (fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) fun ⟨_, y, z, w⟩ =>
    ⟨⟨_, y, z, w⟩, rfl⟩

Depends on / 依赖: Finpartition, Finset, Fintype, Fintype.ofSurjective, Subtype, Subtype.fintype, SupIndep, fintype, ofSurjective, p.SupIndep, p.sup
-/
instance [Fintype α] [DecidableEq α] (a : α) : Fintype (Finpartition a) :=
  @Fintype.ofSurjective { p : Finset α // p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p } (Finpartition a) _
    (Subtype.fintype _) (fun i => ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) fun ⟨_, y, z, w⟩ =>
    ⟨⟨_, y, z, w⟩, rfl⟩

/-! ### Refinement order -/


section Order

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Finpartition a)
  body: ⟨fun P Q => forall ⦃b⦄, b in P.parts -> exists c in Q.parts, b <= c⟩

中文:
实例 :
  签名: LE (有限分拆 a)
  定义体: ⟨fun P Q => forall ⦃b⦄, b in P.parts -> exists c in Q.parts, b <= c⟩

Depends on / 依赖: P.parts, Q.parts
-/
instance : LE (Finpartition a) :=
  ⟨fun P Q => forall ⦃b⦄, b in P.parts -> exists c in Q.parts, b <= c⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Finpartition a)
  body: { (inferInstance : LE (Finpartition a)) with
    le_refl := fun _ b hb => ⟨b, hb, le_rfl⟩
    le_trans := fun _ Q R hPQ hQR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hcd⟩ := hQR hc
      exact ⟨d, hd, hbc.trans hcd⟩
    le_antisymm := fun P Q hPQ hQP => by
      ext b
      refine ⟨fun hb => ?_, fun hb => ?_⟩
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        obtain ⟨d, hd, hcd⟩ := hQP hc
        rwa [hbc.antisymm]
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        rwa [hbc.antisymm]
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }

中文:
实例 :
  签名: 偏序 (有限分拆 a)
  定义体: { (inferInstance : LE (Finpartition a)) with
    le_refl := fun _ b hb => ⟨b, hb, le_rfl⟩
    le_trans := fun _ Q R hPQ hQR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hcd⟩ := hQR hc
      exact ⟨d, hd, hbc.trans hcd⟩
    le_antisymm := fun P Q hPQ hQP => by
      ext b
      refine ⟨fun hb => ?_, fun hb => ?_⟩
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        obtain ⟨d, hd, hcd⟩ := hQP hc
        rwa [hbc.antisymm]
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        rwa [hbc.antisymm]
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }

Depends on / 依赖: Finpartition, P.disjoint.eq_of_le, P.ne_bot, antisymm, disjoint, eq_of_le, hbc.antisymm, hbc.trans, le_antisymm, le_refl, le_rfl, le_trans, ne_bot
-/
instance : PartialOrder (Finpartition a) :=
  { (inferInstance : LE (Finpartition a)) with
    le_refl := fun _ b hb => ⟨b, hb, le_rfl⟩
    le_trans := fun _ Q R hPQ hQR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hcd⟩ := hQR hc
      exact ⟨d, hd, hbc.trans hcd⟩
    le_antisymm := fun P Q hPQ hQP => by
      ext b
      refine ⟨fun hb => ?_, fun hb => ?_⟩
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        obtain ⟨d, hd, hcd⟩ := hQP hc
        rwa [hbc.antisymm]
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        rwa [hbc.antisymm]
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Decidable
  signature: (a = ⊥)] : OrderTop (Finpartition a) where
  body: if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    · intro x hx
      simpa [h, P.ne_bot hx] using P.le hx
    · exact fun b hb => ⟨a, mem_singleton_self _, P.le hb⟩

中文:
实例 [可判定
  签名: (a = ⊥)] : 有顶序 (有限分拆 a) where
  定义体: if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    · intro x hx
      simpa [h, P.ne_bot hx] using P.le hx
    · exact fun b hb => ⟨a, mem_singleton_self _, P.le hb⟩

Depends on / 依赖: Finpartition, Finpartition.empty, ha.symm, indiscrete
-/
instance [Decidable (a = ⊥)] : OrderTop (Finpartition a) where
  top := if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    · intro x hx
      simpa [h, P.ne_bot hx] using P.le hx
    · exact fun b hb => ⟨a, mem_singleton_self _, P.le hb⟩

/--
theorem `parts_top_subset` / 定理 `parts_top_subset`

English:
theorem parts_top_subset
  given: (a : α) [Decidable (a = ⊥)]
  statement: (⊤ : Finpartition a).parts subseteq {a}
  proof: by
  intro b hb
  have hb : b in Finpartition.parts (dite _ _ _) := hb
  split_ifs at hb
  · simp only [copy_parts, empty_parts, notMem_empty] at hb
  · exact hb

中文:
定理 parts_top_subset
  条件: (a : α) [可判定 (a = ⊥)]
  结论: (⊤ : 有限分拆 a).parts subseteq {a}
  证明: by
  intro b hb
  have hb : b in Finpartition.parts (dite _ _ _) := hb
  split_ifs at hb
  · simp only [copy_parts, empty_parts, notMem_empty] at hb
  · exact hb

Depends on / 依赖: Finpartition, Finpartition.parts, I.IsMaximal, I.IsPrime, IsMaximal, IsPrime, KrullDimLE, Ring.KrullDimLE, copy_parts, empty_parts, notMem_empty, split_ifs
-/
theorem parts_top_subset (a : α) [Decidable (a = ⊥)] : (⊤ : Finpartition a).parts subseteq {a} := by
  intro b hb
  have hb : b in Finpartition.parts (dite _ _ _) := hb
  split_ifs at hb
  · simp only [copy_parts, empty_parts, notMem_empty] at hb
  · exact hb

/--
theorem `parts_top_subsingleton` / 定理 `parts_top_subsingleton`

English:
theorem parts_top_subsingleton
  given: (a : α) [Decidable (a = ⊥)]
  proof: Set.subsingleton_of_subset_singleton fun _ hb => mem_singleton.1 parts_top_subset _ hb

中文:
定理 parts_top_subsingleton
  条件: (a : α) [可判定 (a = ⊥)]
  证明: Set.subsingleton_of_subset_singleton fun _ hb => mem_singleton.1 parts_top_subset _ hb

Depends on / 依赖: Set.subsingleton_of_subset_singleton, mem_singleton, parts_top_subset, subsingleton_of_subset_singleton
-/
theorem parts_top_subsingleton (a : α) [Decidable (a = ⊥)] :
    ((⊤ : Finpartition a).parts : Set α).Subsingleton :=
Set.subsingleton_of_subset_singleton fun _ hb => mem_singleton.1 parts_top_subset _ hb

-- TODO: this instance takes double-exponential time to generate all partitions, find a faster way
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] {s
  body: s.powerset.powerset.image
    fun ps => if h : ps.sup id = s ∧ ⊥ ∉ ps ∧ ps.SupIndep id then ⟨ps, h.2.2, h.1, h.2.1⟩ else ⊤
  complete P := by
    refine mem_image.mpr ⟨P.parts, ?_, ?_⟩
    · rw [mem_powerset]; intro p hp; rw [mem_powerset]; exact P.le hp
    · simp [P.supIndep, P.sup_parts, P.bot_notMem, -bot_eq_empty]

中文:
实例 [DecidableEq
  签名: α] {s
  定义体: s.powerset.powerset.image
    fun ps => if h : ps.sup id = s ∧ ⊥ ∉ ps ∧ ps.SupIndep id then ⟨ps, h.2.2, h.1, h.2.1⟩ else ⊤
  complete P := by
    refine mem_image.mpr ⟨P.parts, ?_, ?_⟩
    · rw [mem_powerset]; intro p hp; rw [mem_powerset]; exact P.le hp
    · simp [P.supIndep, P.sup_parts, P.bot_notMem, -bot_eq_empty]

Depends on / 依赖: powerset, s.powerset.powerset.image
-/
instance [DecidableEq α] {s : Finset α} : Fintype (Finpartition s) where
  elems := s.powerset.powerset.image
    fun ps => if h : ps.sup id = s ∧ ⊥ ∉ ps ∧ ps.SupIndep id then ⟨ps, h.2.2, h.1, h.2.1⟩ else ⊤
  complete P := by
    refine mem_image.mpr ⟨P.parts, ?_, ?_⟩
    · rw [mem_powerset]; intro p hp; rw [mem_powerset]; exact P.le hp
    · simp [P.supIndep, P.sup_parts, P.bot_notMem, -bot_eq_empty]

/--
theorem `exists_le_of_le` / 定理 `exists_le_of_le`

English:
theorem exists_le_of_le
  given: {a b : α} {P Q : Finpartition a} (h : P <= Q) (hb : b in Q.parts)
  proof: by
  classical
  by_contra H
  refine Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) ?_)
  have : forall p in P.parts, exists q in Q.parts.erase b, p <= q := by grind [h _]
  have : P.parts.sup id <= (Q.parts.erase b).sup id := by grind [Finset.le_sup, Finset.sup_le_iff]
  grw [← P.sup_parts, this]
  exact Q.supIndep (erase_subset _ _) hb (notMem_erase _ _)

中文:
定理 存在_le_of_le
  条件: {a b : α} {P Q : 有限分拆 a} (h : P <= Q) (hb : b in Q.parts)
  证明: by
  classical
  by_contra H
  refine Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) ?_)
  have : forall p in P.parts, exists q in Q.parts.erase b, p <= q := by grind [h _]
  have : P.parts.sup id <= (Q.parts.erase b).sup id := by grind [Finset.le_sup, Finset.sup_le_iff]
  grw [← P.sup_parts, this]
  exact Q.supIndep (erase_subset _ _) hb (notMem_erase _ _)

Depends on / 依赖: Disjoint, Disjoint.mono_right, Finset, Finset.le_sup, Finset.sup_le_iff, P.parts, P.parts.sup, P.sup_parts, Q.le, Q.ne_bot, Q.parts.erase, Q.supIndep, classical, disjoint_self, erase_subset, le_sup, mono_right, ne_bot, notMem_erase, supIndep
-/
theorem exists_le_of_le {a b : α} {P Q : Finpartition a} (h : P <= Q) (hb : b in Q.parts) :
    exists c in P.parts, c <= b := by
  classical
  by_contra H
  refine Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) ?_)
  have : forall p in P.parts, exists q in Q.parts.erase b, p <= q := by grind [h _]
  have : P.parts.sup id <= (Q.parts.erase b).sup id := by grind [Finset.le_sup, Finset.sup_le_iff]
  grw [← P.sup_parts, this]
  exact Q.supIndep (erase_subset _ _) hb (notMem_erase _ _)

/--
theorem `card_mono` / 定理 `card_mono`

English:
theorem card_mono
  given: {a : α} {P Q : Finpartition a} (h : P <= Q)
  statement: #Q.parts <= #P.parts
  proof: by
  have : forall b in Q.parts, exists c in P.parts, c <= b := fun b => exists_le_of_le h
  choose f hP hf using this
  rw [← card_attach]
  refine card_le_card_of_injOn (fun b => f _ b.2) (fun b _ => hP _ b.2) fun b _ c _ h => ?_
  exact
    Subtype.coe_injective
      (Q.disjoint.elim b.2 c.2 fun H =>
P.ne_bot (hP _ b.2) disjoint_self.1 H.mono (hf _ b.2) h.le.trans hf _ c.2)

中文:
定理 card_mono
  条件: {a : α} {P Q : 有限分拆 a} (h : P <= Q)
  结论: #Q.parts <= #P.parts
  证明: by
  have : forall b in Q.parts, exists c in P.parts, c <= b := fun b => exists_le_of_le h
  choose f hP hf using this
  rw [← card_attach]
  refine card_le_card_of_injOn (fun b => f _ b.2) (fun b _ => hP _ b.2) fun b _ c _ h => ?_
  exact
    Subtype.coe_injective
      (Q.disjoint.elim b.2 c.2 fun H =>
P.ne_bot (hP _ b.2) disjoint_self.1 H.mono (hf _ b.2) h.le.trans hf _ c.2)

Depends on / 依赖: H.mono, P.ne_bot, P.parts, Q.disjoint.elim, Q.parts, Subtype, Subtype.coe_injective, card_attach, card_le_card_of_injOn, coe_injective, disjoint, disjoint_self, exists_le_of_le, h.le.trans, ne_bot
-/
theorem card_mono {a : α} {P Q : Finpartition a} (h : P <= Q) : #Q.parts <= #P.parts := by
  have : forall b in Q.parts, exists c in P.parts, c <= b := fun b => exists_le_of_le h
  choose f hP hf using this
  rw [← card_attach]
  refine card_le_card_of_injOn (fun b => f _ b.2) (fun b _ => hP _ b.2) fun b _ c _ h => ?_
  exact
    Subtype.coe_injective
      (Q.disjoint.elim b.2 c.2 fun H =>
P.ne_bot (hP _ b.2) disjoint_self.1 H.mono (hf _ b.2) h.le.trans hf _ c.2)

end Order

section ToSubtype

variable {s : α} (P : Finpartition s) {Pr : α -> Prop}
  (Prsup : forall ⦃s t : α⦄, Pr s -> Pr t -> Pr (s ⊔ t)) (Prinf : forall ⦃s t : α⦄, Pr s -> Pr t -> Pr (s ⊓ t))
  (Prbot : Pr (⊥ : α)) (hs : Pr s) (hP : forall p in P.parts, Pr p)

/--
Definition of `toSubtype` / `toSubtype` 的定义

English:
definition toSubtype
  signature: :
  body: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    Finpartition (⟨s, hs⟩ : Subtype Pr) :=
  letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
  letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
  { parts := preimage P.parts Subtype.val Subtype.val_injective.injOn
    supIndep t ht i hi hi' := by
      classical
      have : (fun (i : Subtype Pr) => (id i).val) = id ∘ Subtype.val := rfl
      rw [disjoint_subtype_iff Prinf Prbot]; rw [sup_coe]; rw [this]; rw [← sup_image t Subtype.val id]
      · apply P.supIndep
        · simpa [image_subset_iff_subset_preimage] using ht
        · simpa using hi
        · simpa [i.property] using hi'
      exact Prsup
    sup_parts := by
      simpa [Finset.sup_preimage_val_id Prsup Prbot hP] using P.sup_parts
    bot_notMem := by simpa [mem_preimage, Subtype.coe_bot Prbot] using P.bot_notMem }

@[simp]

中文:
定义 toSubtype
  签名: :
  定义体: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    Finpartition (⟨s, hs⟩ : Subtype Pr) :=
  letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
  letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
  { parts := preimage P.parts Subtype.val Subtype.val_injective.injOn
    supIndep t ht i hi hi' := by
      classical
      have : (fun (i : Subtype Pr) => (id i).val) = id ∘ Subtype.val := rfl
      rw [disjoint_subtype_iff Prinf Prbot]; rw [sup_coe]; rw [this]; rw [← sup_image t Subtype.val id]
      · apply P.supIndep
        · simpa [image_subset_iff_subset_preimage] using ht
        · simpa using hi
        · simpa [i.property] using hi'
      exact Prsup
    sup_parts := by
      simpa [Finset.sup_preimage_val_id Prsup Prbot hP] using P.sup_parts
    bot_notMem := by simpa [mem_preimage, Subtype.coe_bot Prbot] using P.bot_notMem }

@[simp]

Depends on / 依赖: Subtype, Subtype.lattice, lattice
-/
noncomputable def toSubtype :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    Finpartition (⟨s, hs⟩ : Subtype Pr) :=
  letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
  letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
  { parts := preimage P.parts Subtype.val Subtype.val_injective.injOn
    supIndep t ht i hi hi' := by
      classical
      have : (fun (i : Subtype Pr) => (id i).val) = id ∘ Subtype.val := rfl
      rw [disjoint_subtype_iff Prinf Prbot]; rw [sup_coe]; rw [this]; rw [← sup_image t Subtype.val id]
      · apply P.supIndep
        · simpa [image_subset_iff_subset_preimage] using ht
        · simpa using hi
        · simpa [i.property] using hi'
      exact Prsup
    sup_parts := by
      simpa [Finset.sup_preimage_val_id Prsup Prbot hP] using P.sup_parts
    bot_notMem := by simpa [mem_preimage, Subtype.coe_bot Prbot] using P.bot_notMem }

@[simp]
/--
lemma `mem_toSubtype_iff` / 引理 `mem_toSubtype_iff`

English:
lemma mem_toSubtype_iff
  given: (p : Subtype Pr)
  proof: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    p in (toSubtype P Prsup Prinf Prbot hs hP).parts ↔ p.val in P.parts := by simp [toSubtype]

中文:
引理 mem_toSubtype_iff
  条件: (p : 子类型 Pr)
  证明: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    p in (toSubtype P Prsup Prinf Prbot hs hP).parts ↔ p.val in P.parts := by simp [toSubtype]

Depends on / 依赖: Subtype, Subtype.lattice, lattice, zero_le_one
-/
lemma mem_toSubtype_iff (p : Subtype Pr) :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    p in (toSubtype P Prsup Prinf Prbot hs hP).parts ↔ p.val in P.parts := by simp [toSubtype]

/--
lemma `sum_eq_sum_finpartition_subtype` / 引理 `sum_eq_sum_finpartition_subtype`

English:
lemma sum_eq_sum_finpartition_subtype
  given: {X : Type*} [AddCommMonoid X] (f : α -> X)
  proof: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    ∑ p in P.parts, f p = ∑ p in (Finpartition.toSubtype P Prsup Prinf Prbot hs hP).parts, f p := by
  apply Finset.sum_bij (fun p hpP => ⟨p, hP p hpP⟩) <;> simp

中文:
引理 sum_eq_sum_finpartition_subtype
  条件: {X : 类型} [加法交换幺半群 X] (f : α -> X)
  证明: Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    ∑ p in P.parts, f p = ∑ p in (Finpartition.toSubtype P Prsup Prinf Prbot hs hP).parts, f p := by
  apply Finset.sum_bij (fun p hpP => ⟨p, hP p hpP⟩) <;> simp

Depends on / 依赖: Subtype, Subtype.lattice, lattice
-/
lemma sum_eq_sum_finpartition_subtype {X : Type*} [AddCommMonoid X] (f : α -> X) :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    ∑ p in P.parts, f p = ∑ p in (Finpartition.toSubtype P Prsup Prinf Prbot hs hP).parts, f p := by
  apply Finset.sum_bij (fun p hpP => ⟨p, hP p hpP⟩) <;> simp

end ToSubtype

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] [DecidableEq α] {a b c : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Finpartition a)
  body: ⟨fun P Q =>
    ofErase ((P.parts ×ˢ Q.parts).image fun bc => bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        simp only [mem_image, and_imp, forall_exists_index, id, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        · refine Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ ?_)
          intro t
          simp [t] at h
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
      (by
        rw [sup_image]; rw [id_comp]; rw [sup_product_left]
        trans P.parts.sup id ⊓ Q.parts.sup id
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          rfl
        · rw [P.sup_parts, Q.sup_parts, inf_idem])⟩

@[simp]

中文:
实例 :
  签名: 最小值 (有限分拆 a)
  定义体: ⟨fun P Q =>
    ofErase ((P.parts ×ˢ Q.parts).image fun bc => bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        simp only [mem_image, and_imp, forall_exists_index, id, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        · refine Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ ?_)
          intro t
          simp [t] at h
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
      (by
        rw [sup_image]; rw [id_comp]; rw [sup_product_left]
        trans P.parts.sup id ⊓ Q.parts.sup id
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          rfl
        · rw [P.sup_parts, Q.sup_parts, inf_idem])⟩

@[simp]

Depends on / 依赖: Disjoint, Disjoint.mono, Finset, Finset.disjoint_sup_right, P.disjoint, P.parts, Prod.exists, Q.disjoint, Q.parts, and_imp, disjoint, disjoint_sup_right, eq_or_ne, forall_exists_index, inf_le_left, inf_le_right, mem_erase, mem_image, mem_product, ofErase
-/
instance : Min (Finpartition a) :=
  ⟨fun P Q =>
    ofErase ((P.parts ×ˢ Q.parts).image fun bc => bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        simp only [mem_image, and_imp, forall_exists_index, id, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        · refine Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ ?_)
          intro t
          simp [t] at h
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
      (by
        rw [sup_image]; rw [id_comp]; rw [sup_product_left]
        trans P.parts.sup id ⊓ Q.parts.sup id
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          rfl
        · rw [P.sup_parts, Q.sup_parts, inf_idem])⟩

@[simp]
/--
theorem `parts_inf` / 定理 `parts_inf`

English:
theorem parts_inf
  given: (P Q : Finpartition a)
  proof: rfl

中文:
定理 parts_inf
  条件: (P Q : 有限分拆 a)
  证明: rfl
-/
theorem parts_inf (P Q : Finpartition a) :
    (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).image fun bc : α × α => bc.1 ⊓ bc.2).erase ⊥ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (Finpartition a)
  body: { inf := Min.min
    inf_le_left := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.1, hc.1, inf_le_left⟩
    inf_le_right := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.2, hc.2, inf_le_right⟩
    le_inf := fun P Q R hPQ hPR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hbd⟩ := hPR hb
      have h := _root_.le_inf hbc hbd
      refine
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

中文:
实例 :
  签名: SemilatticeInf (有限分拆 a)
  定义体: { inf := Min.min
    inf_le_left := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.1, hc.1, inf_le_left⟩
    inf_le_right := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.2, hc.2, inf_le_right⟩
    le_inf := fun P Q R hPQ hPR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hbd⟩ := hPR hb
      have h := _root_.le_inf hbc hbd
      refine
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

Depends on / 依赖: Min.min, _root_, _root_.le_inf, inf_le_left, inf_le_right, le_inf, mem_erase_of_ne_of_mem, mem_image, mem_of_mem_erase, mem_product, ne_bot_of_le_ne_bot
-/
instance : SemilatticeInf (Finpartition a) :=
  { inf := Min.min
    inf_le_left := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.1, hc.1, inf_le_left⟩
    inf_le_right := fun P Q b hb => by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.2, hc.2, inf_le_right⟩
    le_inf := fun P Q R hPQ hPR b hb => by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hbd⟩ := hPR hb
      have h := _root_.le_inf hbc hbd
      refine
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (P : Finpartition a) (hb : b <= a)
  body: (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [sup_erase_bot, sup_image, Function.id_comp, (sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this]; rw [inf_eq_right.mpr hb]
  bot_notMem := notMem_erase _ _

中文:
定义 restrict
  签名: (P : 有限分拆 a) (hb : b <= a)
  定义体: (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [sup_erase_bot, sup_image, Function.id_comp, (sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this]; rw [inf_eq_right.mpr hb]
  bot_notMem := notMem_erase _ _

Depends on / 依赖: P.parts.image
-/
def restrict (P : Finpartition a) (hb : b <= a) : Finpartition b where
  parts := (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [sup_erase_bot, sup_image, Function.id_comp, (sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this]; rw [inf_eq_right.mpr hb]
  bot_notMem := notMem_erase _ _

/--
lemma `sum_restrict` / 引理 `sum_restrict`

English:
lemma sum_restrict
  statement: (P : Finpartition a) (hb : b <= a) {M : Type*} [AddCommMonoid M]
  proof: by
  have hinj : forall x in P.parts.filter (· ⊓ b != ⊥), forall y in P.parts.filter (· ⊓ b != ⊥),
      x ⊓ b = y ⊓ b -> x = y := fun x hx y hy hxy => by
    by_contra hne
    simp only [Finset.mem_filter] at hx hy
    have : Disjoint (x ⊓ b) (y ⊓ b) := (P.disjoint hx.1 hy.1 hne).mono inf_le_left inf_le_left
    grind
  have heq : (P.parts.image (· ⊓ b)).erase ⊥ = (P.parts.filter (· ⊓ b != ⊥)).image (· ⊓ b) := by
    grind
  have hz : ∑ x in P.parts.filter (¬ · ⊓ b != ⊥), f (x ⊓ b) = 0 := Finset.sum_eq_zero fun x hx => by
    simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hx
    rw [hx.2]; rw [hf]
  simp only [restrict, heq, ← Finset.sum_filter_add_sum_filter_not P.parts (· ⊓ b != ⊥), hz,
    Finset.sum_image hinj, add_zero]

中文:
引理 sum_restrict
  结论: (P : 有限分拆 a) (hb : b <= a) {M : 类型} [加法交换幺半群 M]
  证明: by
  have hinj : forall x in P.parts.filter (· ⊓ b != ⊥), forall y in P.parts.filter (· ⊓ b != ⊥),
      x ⊓ b = y ⊓ b -> x = y := fun x hx y hy hxy => by
    by_contra hne
    simp only [Finset.mem_filter] at hx hy
    have : Disjoint (x ⊓ b) (y ⊓ b) := (P.disjoint hx.1 hy.1 hne).mono inf_le_left inf_le_left
    grind
  have heq : (P.parts.image (· ⊓ b)).erase ⊥ = (P.parts.filter (· ⊓ b != ⊥)).image (· ⊓ b) := by
    grind
  have hz : ∑ x in P.parts.filter (¬ · ⊓ b != ⊥), f (x ⊓ b) = 0 := Finset.sum_eq_zero fun x hx => by
    simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hx
    rw [hx.2]; rw [hf]
  simp only [restrict, heq, ← Finset.sum_filter_add_sum_filter_not P.parts (· ⊓ b != ⊥), hz,
    Finset.sum_image hinj, add_zero]

Depends on / 依赖: Disjoint, Finset, Finset.mem_filter, Finset.sum_eq_zero, P.disjoint, P.parts.filter, P.parts.image, disjoint, filter, inf_le_left, mem_filter, sum_eq_zero
-/
lemma sum_restrict (P : Finpartition a) (hb : b <= a) {M : Type*} [AddCommMonoid M]
    (f : α -> M) (hf : f ⊥ = 0) :
    ∑ p in (P.restrict hb).parts, f p = ∑ q in P.parts, f (q ⊓ b) := by
  have hinj : forall x in P.parts.filter (· ⊓ b != ⊥), forall y in P.parts.filter (· ⊓ b != ⊥),
      x ⊓ b = y ⊓ b -> x = y := fun x hx y hy hxy => by
    by_contra hne
    simp only [Finset.mem_filter] at hx hy
    have : Disjoint (x ⊓ b) (y ⊓ b) := (P.disjoint hx.1 hy.1 hne).mono inf_le_left inf_le_left
    grind
  have heq : (P.parts.image (· ⊓ b)).erase ⊥ = (P.parts.filter (· ⊓ b != ⊥)).image (· ⊓ b) := by
    grind
  have hz : ∑ x in P.parts.filter (¬ · ⊓ b != ⊥), f (x ⊓ b) = 0 := Finset.sum_eq_zero fun x hx => by
    simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hx
    rw [hx.2]; rw [hf]
  simp only [restrict, heq, ← Finset.sum_filter_add_sum_filter_not P.parts (· ⊓ b != ⊥), hz,
    Finset.sum_image hinj, add_zero]

/-- A `Finpartition` constructor of `parts.sup id` from a finset `parts` of pairwise disjoint
elements. Any `⊥` elements in `parts` are erased. -/
@[simps]
/--
Definition of `ofPairwiseDisjoint` / `ofPairwiseDisjoint` 的定义

English:
definition ofPairwiseDisjoint
  signature: (parts : Finset α) (hdisjoint : (parts : Set α).PairwiseDisjoint id)
  body: parts.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hdisjoint (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot parts
  bot_notMem := Finset.notMem_erase _ _

中文:
定义 ofPairwiseDisjoint
  签名: (parts : 有限集 α) (hdisjoint : (parts : 集合 α).PairwiseDisjoint id)
  定义体: parts.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hdisjoint (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot parts
  bot_notMem := Finset.notMem_erase _ _

Depends on / 依赖: parts.erase
-/
def ofPairwiseDisjoint (parts : Finset α) (hdisjoint : (parts : Set α).PairwiseDisjoint id) :
    Finpartition (parts.sup id) where
  parts := parts.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hdisjoint (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot parts
  bot_notMem := Finset.notMem_erase _ _

/--
lemma `sum_ofPairwiseDisjoint_eq_sum` / 引理 `sum_ofPairwiseDisjoint_eq_sum`

English:
lemma sum_ofPairwiseDisjoint_eq_sum
  statement: {parts : Finset α}
  proof: by
  by_cases hbot : ⊥ in parts
  · simp only [Finpartition.ofPairwiseDisjoint]
    rw [← erase_union_eq ⊥ parts hbot]; rw [union_comm]; rw [sum_union_eq_right]
    · simp
    grind
  · simp_all

中文:
引理 sum_ofPairwiseDisjoint_eq_sum
  结论: {parts : 有限集 α}
  证明: by
  by_cases hbot : ⊥ in parts
  · simp only [Finpartition.ofPairwiseDisjoint]
    rw [← erase_union_eq ⊥ parts hbot]; rw [union_comm]; rw [sum_union_eq_right]
    · simp
    grind
  · simp_all

Depends on / 依赖: Finpartition, Finpartition.ofPairwiseDisjoint, erase_union_eq, ofPairwiseDisjoint, sum_union_eq_right, union_comm
-/
lemma sum_ofPairwiseDisjoint_eq_sum {parts : Finset α}
    (hdisjoint : (parts : Set α).PairwiseDisjoint id)
    {X : Type*} [AddCommMonoid X] {f : α -> X} (hf : f ⊥ = 0) :
    ∑ p in (ofPairwiseDisjoint parts hdisjoint).parts, f p = ∑ p in parts, f p := by
  by_cases hbot : ⊥ in parts
  · simp only [Finpartition.ofPairwiseDisjoint]
    rw [← erase_union_eq ⊥ parts hbot]; rw [union_comm]; rw [sum_union_eq_right]
    · simp
    grind
  · simp_all

end DistribLattice

section IsModularLattice

variable [Lattice α] [OrderBot α] [IsModularLattice α] [DecidableEq α] {a b c : α}

/-- Combine a family of partitions of pairwise disjoint elements into a partition of their sup. -/
@[simps]
/--
Definition of `combine` / `combine` 的定义

English:
definition combine
  signature: {ι : Type*} {I : Finset ι} {a : ι -> α} (P : forall i, Finpartition (a i))
  body: I.biUnion fun i => (P i).parts
  supIndep :=
    .biUnion (by simpa only [sup_parts]) (fun i _ => (P i).supIndep)
  sup_parts := by
    rw [sup_biUnion]
    exact sup_congr rfl fun i _ => (P i).sup_parts
  bot_notMem := by
    rw [mem_biUnion]; push Not; exact fun i _ => (P i).bot_notMem

中文:
定义 combine
  签名: {ι : 类型} {I : 有限集 ι} {a : ι -> α} (P : 对任意 i, 有限分拆 (a i))
  定义体: I.biUnion fun i => (P i).parts
  supIndep :=
    .biUnion (by simpa only [sup_parts]) (fun i _ => (P i).supIndep)
  sup_parts := by
    rw [sup_biUnion]
    exact sup_congr rfl fun i _ => (P i).sup_parts
  bot_notMem := by
    rw [mem_biUnion]; push Not; exact fun i _ => (P i).bot_notMem

Depends on / 依赖: I.biUnion, biUnion
-/
def combine {ι : Type*} {I : Finset ι} {a : ι -> α} (P : forall i, Finpartition (a i))
    (ha : I.SupIndep a) : Finpartition (I.sup a) where
  parts := I.biUnion fun i => (P i).parts
  supIndep :=
    .biUnion (by simpa only [sup_parts]) (fun i _ => (P i).supIndep)
  sup_parts := by
    rw [sup_biUnion]
    exact sup_congr rfl fun i _ => (P i).sup_parts
  bot_notMem := by
    rw [mem_biUnion]; push Not; exact fun i _ => (P i).bot_notMem

/--
lemma `sum_combine` / 引理 `sum_combine`

English:
lemma sum_combine
  statement: {ι : Type*} {I : Finset ι} {s : ι -> α} (P : forall i, Finpartition (s i))
  proof: by
  simp_rw [combine]
  refine Finset.sum_biUnion fun i hi j hj hij => ?_
  rw [Function.onFun]; rw [Finset.disjoint_left]
  intro p hpi hpj
  have hp_disj : Disjoint p p := (ha.pairwiseDisjoint hi hj hij).mono ((P i).le hpi) ((P j).le hpj)
  exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)

中文:
引理 sum_combine
  结论: {ι : 类型} {I : 有限集 ι} {s : ι -> α} (P : 对任意 i, 有限分拆 (s i))
  证明: by
  simp_rw [combine]
  refine Finset.sum_biUnion fun i hi j hj hij => ?_
  rw [Function.onFun]; rw [Finset.disjoint_left]
  intro p hpi hpj
  have hp_disj : Disjoint p p := (ha.pairwiseDisjoint hi hj hij).mono ((P i).le hpi) ((P j).le hpj)
  exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)

Depends on / 依赖: Disjoint, Finset, Finset.disjoint_left, Finset.sum_biUnion, Function, Function.onFun, combine, disjoint_left, disjoint_self, disjoint_self.mp, ha.pairwiseDisjoint, hp_disj, ne_bot, pairwiseDisjoint, simp_rw, sum_biUnion
-/
lemma sum_combine {ι : Type*} {I : Finset ι} {s : ι -> α} (P : forall i, Finpartition (s i))
    (ha : I.SupIndep s) {M : Type*} [AddCommMonoid M] (f : α -> M) :
    ∑ p in (Finpartition.combine P ha).parts, f p = ∑ i in I, ∑ p in (P i).parts, f p := by
  simp_rw [combine]
  refine Finset.sum_biUnion fun i hi j hj hij => ?_
  rw [Function.onFun]; rw [Finset.disjoint_left]
  intro p hpi hpj
  have hp_disj : Disjoint p p := (ha.pairwiseDisjoint hi hj hij).mono ((P i).le hpi) ((P j).le hpj)
  exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)

section Bind

variable {P : Finpartition a} {Q : forall i in P.parts, Finpartition i}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps! parts]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (P : Finpartition a) (Q : forall i in P.parts, Finpartition i)
  body: (combine (fun i : P.parts => Q i.1 i.2) P.supIndep.attach).copy by
    rw [Finset.sup_attach (f := fun x => x)]; rw [← Function.id_def]; rw [P.sup_parts]

中文:
定义 bind
  签名: (P : 有限分拆 a) (Q : 对任意 i in P.parts, 有限分拆 i)
  定义体: (combine (fun i : P.parts => Q i.1 i.2) P.supIndep.attach).copy by
    rw [Finset.sup_attach (f := fun x => x)]; rw [← Function.id_def]; rw [P.sup_parts]

Depends on / 依赖: Finset, Finset.sup_attach, Function, Function.id_def, P.parts, P.supIndep.attach, P.sup_parts, attach, combine, id_def, supIndep, sup_attach, sup_parts
-/
def bind (P : Finpartition a) (Q : forall i in P.parts, Finpartition i) : Finpartition a :=
(combine (fun i : P.parts => Q i.1 i.2) P.supIndep.attach).copy by
    rw [Finset.sup_attach (f := fun x => x)]; rw [← Function.id_def]; rw [P.sup_parts]

/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  statement: b in (P.bind Q).parts ↔ exists A hA, b in (Q A hA).parts
  proof: by
  rw [bind_parts]; rw [mem_biUnion]
  constructor
  · rintro ⟨⟨A, hA⟩, -, h⟩
    exact ⟨A, hA, h⟩
  · rintro ⟨A, hA, h⟩
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩

中文:
定理 mem_bind
  结论: b in (P.bind Q).parts ↔ 存在 A hA, b in (Q A hA).parts
  证明: by
  rw [bind_parts]; rw [mem_biUnion]
  constructor
  · rintro ⟨⟨A, hA⟩, -, h⟩
    exact ⟨A, hA, h⟩
  · rintro ⟨A, hA, h⟩
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩

Depends on / 依赖: bind_parts, mem_attach, mem_biUnion
-/
theorem mem_bind : b in (P.bind Q).parts ↔ exists A hA, b in (Q A hA).parts := by
  rw [bind_parts]; rw [mem_biUnion]
  constructor
  · rintro ⟨⟨A, hA⟩, -, h⟩
    exact ⟨A, hA, h⟩
  · rintro ⟨A, hA, h⟩
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩

/--
theorem `card_bind` / 定理 `card_bind`

English:
theorem card_bind
  given: (Q : forall i in P.parts, Finpartition i)
  proof: by
  apply card_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun]; rw [Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne]; rw [Subtype.mk_eq_mk] at hbc
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
(le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans (P.disjoint hb hc hbc).le_bot)

中文:
定理 card_bind
  条件: (Q : 对任意 i in P.parts, 有限分拆 i)
  证明: by
  apply card_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun]; rw [Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne]; rw [Subtype.mk_eq_mk] at hbc
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
(le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans (P.disjoint hb hc hbc).le_bot)

Depends on / 依赖: Finset, Finset.disjoint_left, Function, Function.onFun, P.disjoint, Subtype, Subtype.mk_eq_mk, card_biUnion, disjoint, disjoint_left, eq_bot_iff, le_bot, le_inf, mk_eq_mk, ne_bot
-/
theorem card_bind (Q : forall i in P.parts, Finpartition i) :
    #(P.bind Q).parts = ∑ A in P.parts.attach, #(Q _ A.2).parts := by
  apply card_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun]; rw [Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne]; rw [Subtype.mk_eq_mk] at hbc
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
(le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans (P.disjoint hb hc hbc).le_bot)

end Bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps]
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (P : Finpartition a) (hb : b != ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c)
  body: insert b P.parts
  supIndep := by
    refine P.supIndep.insert ?_
    rwa [sup_parts, disjoint_comm]
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm]
  bot_notMem h := (mem_insert.1 h).elim hb.symm P.bot_notMem

中文:
定义 extend
  签名: (P : 有限分拆 a) (hb : b != ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c)
  定义体: insert b P.parts
  supIndep := by
    refine P.supIndep.insert ?_
    rwa [sup_parts, disjoint_comm]
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm]
  bot_notMem h := (mem_insert.1 h).elim hb.symm P.bot_notMem

Depends on / 依赖: P.parts, insert
-/
def extend (P : Finpartition a) (hb : b != ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c) :
    Finpartition c where
  parts := insert b P.parts
  supIndep := by
    refine P.supIndep.insert ?_
    rwa [sup_parts, disjoint_comm]
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm]
  bot_notMem h := (mem_insert.1 h).elim hb.symm P.bot_notMem

/--
theorem `card_extend` / 定理 `card_extend`

English:
theorem card_extend
  statement: (P : Finpartition a) (b c : α) {hb : b != ⊥} {hab : Disjoint a b}
  proof: card_insert_of_notMem fun h => hb hab.symm.eq_bot_of_le P.le h

中文:
定理 card_extend
  结论: (P : 有限分拆 a) (b c : α) {hb : b != ⊥} {hab : Disjoint a b}
  证明: card_insert_of_notMem fun h => hb hab.symm.eq_bot_of_le P.le h

Depends on / 依赖: P.le, card_insert_of_notMem, eq_bot_of_le, hab.symm.eq_bot_of_le
-/
theorem card_extend (P : Finpartition a) (b c : α) {hb : b != ⊥} {hab : Disjoint a b}
    {hc : a ⊔ b = c} : #(P.extend hb hab hc).parts = #P.parts + 1 :=
card_insert_of_notMem fun h => hb hab.symm.eq_bot_of_le P.le h

end IsModularLattice

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableEq α] {a b c : α} (P : Finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
@[simps!]
/--
Definition of `avoid` / `avoid` 的定义

English:
definition avoid
  signature: (b : α)
  body: ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun _ => sdiff_le).supIndep
    (by rw [sup_image, id_comp, Finset.sup_sdiff_right, ← Function.id_def, P.sup_parts])

@[simp]

中文:
定义 avoid
  签名: (b : α)
  定义体: ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun _ => sdiff_le).supIndep
    (by rw [sup_image, id_comp, Finset.sup_sdiff_right, ← Function.id_def, P.sup_parts])

@[simp]

Depends on / 依赖: Finset, Finset.sup_sdiff_right, Function, Function.id_def, P.disjoint.image_finset_of_le, P.parts.image, P.sup_parts, disjoint, id_comp, id_def, image_finset_of_le, ofErase, sdiff_le, supIndep, sup_image, sup_parts, sup_sdiff_right
-/
def avoid (b : α) : Finpartition (a \ b) :=
  ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun _ => sdiff_le).supIndep
    (by rw [sup_image, id_comp, Finset.sup_sdiff_right, ← Function.id_def, P.sup_parts])

@[simp]
/--
theorem `mem_avoid` / 定理 `mem_avoid`

English:
theorem mem_avoid
  statement: c in (P.avoid b).parts ↔ exists d in P.parts, ¬d <= b ∧ d \ b = c
  proof: by
  simp only [avoid, ofErase, mem_erase, Ne, mem_image, ← exists_and_left,
    @and_left_comm (c != ⊥)]
refine exists_congr fun d => and_congr_right' and_congr_left ?_
  rintro rfl
  rw [sdiff_eq_bot_iff]

中文:
定理 mem_avoid
  结论: c in (P.avoid b).parts ↔ 存在 d in P.parts, ¬d <= b ∧ d \ b = c
  证明: by
  simp only [avoid, ofErase, mem_erase, Ne, mem_image, ← exists_and_left,
    @and_left_comm (c != ⊥)]
refine exists_congr fun d => and_congr_right' and_congr_left ?_
  rintro rfl
  rw [sdiff_eq_bot_iff]

Depends on / 依赖: and_congr_left, and_congr_right, and_left_comm, exists_and_left, exists_congr, mem_erase, mem_image, ofErase, sdiff_eq_bot_iff
-/
theorem mem_avoid : c in (P.avoid b).parts ↔ exists d in P.parts, ¬d <= b ∧ d \ b = c := by
  simp only [avoid, ofErase, mem_erase, Ne, mem_image, ← exists_and_left,
    @and_left_comm (c != ⊥)]
refine exists_congr fun d => and_congr_right' and_congr_left ?_
  rintro rfl
  rw [sdiff_eq_bot_iff]

/--
Definition of `extendOfLE` / `extendOfLE` 的定义

English:
definition extendOfLE
  signature: (hab : a <= b)
  body: if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

中文:
定义 extendOfLE
  签名: (hab : a <= b)
  定义体: if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

Depends on / 依赖: P.extend, disjoint_sdiff_self_right, extend, le_antisymm, sdiff_eq_bot_iff, sdiff_eq_bot_iff.mp, sup_sdiff_cancel_right
-/
def extendOfLE (hab : a <= b) : Finpartition b :=
  if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

/--
lemma `parts_extendOfLE_of_eq` / 引理 `parts_extendOfLE_of_eq`

English:
lemma parts_extendOfLE_of_eq
  given: (hab : a = b)
  statement: (P.extendOfLE hab.le).parts = P.parts
  proof: by
  subst hab; simp [extendOfLE]

中文:
引理 parts_extendOfLE_of_eq
  条件: (hab : a = b)
  结论: (P.extendOfLE hab.le).parts = P.parts
  证明: by
  subst hab; simp [extendOfLE]

Depends on / 依赖: extendOfLE
-/
lemma parts_extendOfLE_of_eq (hab : a = b) : (P.extendOfLE hab.le).parts = P.parts := by
  subst hab; simp [extendOfLE]

/--
lemma `parts_extendOfLE_of_lt` / 引理 `parts_extendOfLE_of_lt`

English:
lemma parts_extendOfLE_of_lt
  given: (hab : a < b)
  proof: by
  simp [extendOfLE, sdiff_eq_bot_iff.not.mpr (not_le_of_gt hab)]

中文:
引理 parts_extendOfLE_of_lt
  条件: (hab : a < b)
  证明: by
  simp [extendOfLE, sdiff_eq_bot_iff.not.mpr (not_le_of_gt hab)]

Depends on / 依赖: extendOfLE, not_le_of_gt, sdiff_eq_bot_iff, sdiff_eq_bot_iff.not.mpr
-/
lemma parts_extendOfLE_of_lt (hab : a < b) :
    (P.extendOfLE (le_of_lt hab)).parts = insert (b \ a) P.parts := by
  simp [extendOfLE, sdiff_eq_bot_iff.not.mpr (not_le_of_gt hab)]

/--
lemma `parts_subset_extendOfLE` / 引理 `parts_subset_extendOfLE`

English:
lemma parts_subset_extendOfLE
  given: (hab : a <= b)
  statement: P.parts subseteq (P.extendOfLE hab).parts
  proof: by
  unfold extendOfLE
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _

中文:
引理 parts_subset_extendOfLE
  条件: (hab : a <= b)
  结论: P.parts subseteq (P.extendOfLE hab).parts
  证明: by
  unfold extendOfLE
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _

Depends on / 依赖: Finset, Finset.subset_insert, extendOfLE, le_antisymm, sdiff_eq_bot_iff, sdiff_eq_bot_iff.mp, split_ifs, subset_insert
-/
lemma parts_subset_extendOfLE (hab : a <= b) : P.parts subseteq (P.extendOfLE hab).parts := by
  unfold extendOfLE
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _

/--
lemma `mem_parts_or_eq_sdiff_of_mem_extendOfLE` / 引理 `mem_parts_or_eq_sdiff_of_mem_extendOfLE`

English:
lemma mem_parts_or_eq_sdiff_of_mem_extendOfLE
  statement: (hab : a <= b) {p : α}
  proof: by
  by_cases h : a < b
  · simp_all [parts_extendOfLE_of_lt _ h, mem_insert, Or.comm]
  · left
    simpa [parts_extendOfLE_of_eq _ (LE.le.eq_of_not_lt hab h)] using hp

中文:
引理 mem_parts_or_eq_sdiff_of_mem_extendOfLE
  结论: (hab : a <= b) {p : α}
  证明: by
  by_cases h : a < b
  · simp_all [parts_extendOfLE_of_lt _ h, mem_insert, Or.comm]
  · left
    simpa [parts_extendOfLE_of_eq _ (LE.le.eq_of_not_lt hab h)] using hp

Depends on / 依赖: LE.le.eq_of_not_lt, Or.comm, eq_of_not_lt, mem_insert, parts_extendOfLE_of_eq, parts_extendOfLE_of_lt
-/
lemma mem_parts_or_eq_sdiff_of_mem_extendOfLE (hab : a <= b) {p : α}
    (hp : p in (P.extendOfLE hab).parts) : p in P.parts ∨ p = b \ a := by
  by_cases h : a < b
  · simp_all [parts_extendOfLE_of_lt _ h, mem_insert, Or.comm]
  · left
    simpa [parts_extendOfLE_of_eq _ (LE.le.eq_of_not_lt hab h)] using hp

end GeneralizedBooleanAlgebra

end Finpartition

/-! ### Finite partitions of finsets -/


namespace Finpartition

variable [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

/--
lemma `subset` / 引理 `subset`

English:
lemma subset
  given: {a : Finset α} (ha : a in P.parts)
  statement: a subseteq s
  proof: P.le ha

中文:
引理 subset
  条件: {a : 有限集 α} (ha : a in P.parts)
  结论: a subseteq s
  证明: P.le ha

Depends on / 依赖: P.le
-/
lemma subset {a : Finset α} (ha : a in P.parts) : a subseteq s := P.le ha

/--
theorem `nonempty_of_mem_parts` / 定理 `nonempty_of_mem_parts`

English:
theorem nonempty_of_mem_parts
  given: {a : Finset α} (ha : a in P.parts)
  statement: a.Nonempty
  proof: nonempty_iff_ne_empty.2 P.ne_bot ha

@[simp]

中文:
定理 nonempty_of_mem_parts
  条件: {a : 有限集 α} (ha : a in P.parts)
  结论: a.非空
  证明: nonempty_iff_ne_empty.2 P.ne_bot ha

@[simp]

Depends on / 依赖: P.ne_bot, ne_bot, nonempty_iff_ne_empty
-/
theorem nonempty_of_mem_parts {a : Finset α} (ha : a in P.parts) : a.Nonempty :=
nonempty_iff_ne_empty.2 P.ne_bot ha

@[simp]
/--
theorem `empty_notMem_parts` / 定理 `empty_notMem_parts`

English:
theorem empty_notMem_parts
  statement: ∅ ∉ P.parts
  proof: P.bot_notMem

中文:
定理 empty_notMem_parts
  结论: ∅ ∉ P.parts
  证明: P.bot_notMem

Depends on / 依赖: P.bot_notMem, bot_notMem
-/
theorem empty_notMem_parts : ∅ ∉ P.parts := P.bot_notMem

/--
theorem `ne_empty` / 定理 `ne_empty`

English:
theorem ne_empty
  given: (h : t in P.parts)
  statement: t != ∅
  proof: P.ne_bot h

中文:
定理 ne_empty
  条件: (h : t in P.parts)
  结论: t != ∅
  证明: P.ne_bot h

Depends on / 依赖: P.ne_bot, ne_bot
-/
theorem ne_empty (h : t in P.parts) : t != ∅ := P.ne_bot h

/--
lemma `eq_of_mem_parts` / 引理 `eq_of_mem_parts`

English:
lemma eq_of_mem_parts
  given: (ht : t in P.parts) (hu : u in P.parts) (hat : a in t) (hau : a in u)
  statement: t = u
  proof: P.disjoint.elim ht hu not_disjoint_iff.2 ⟨a, hat, hau⟩

中文:
引理 eq_of_mem_parts
  条件: (ht : t in P.parts) (hu : u in P.parts) (hat : a in t) (hau : a in u)
  结论: t = u
  证明: P.disjoint.elim ht hu not_disjoint_iff.2 ⟨a, hat, hau⟩

Depends on / 依赖: P.disjoint.elim, disjoint, not_disjoint_iff
-/
lemma eq_of_mem_parts (ht : t in P.parts) (hu : u in P.parts) (hat : a in t) (hau : a in u) : t = u :=
P.disjoint.elim ht hu not_disjoint_iff.2 ⟨a, hat, hau⟩

/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  given: (ha : a in s)
  statement: exists t in P.parts, a in t
  proof: by
  simp_rw [← P.sup_parts] at ha
  exact mem_sup.1 ha

中文:
定理 存在_mem
  条件: (ha : a in s)
  结论: 存在 t in P.parts, a in t
  证明: by
  simp_rw [← P.sup_parts] at ha
  exact mem_sup.1 ha

Depends on / 依赖: P.sup_parts, mem_sup, simp_rw, sup_parts
-/
theorem exists_mem (ha : a in s) : exists t in P.parts, a in t := by
  simp_rw [← P.sup_parts] at ha
  exact mem_sup.1 ha

/--
theorem `biUnion_parts` / 定理 `biUnion_parts`

English:
theorem biUnion_parts
  statement: P.parts.biUnion id = s
  proof: (sup_eq_biUnion _ _).symm.trans P.sup_parts

中文:
定理 biUnion_parts
  结论: P.parts.biUnion id = s
  证明: (sup_eq_biUnion _ _).symm.trans P.sup_parts

Depends on / 依赖: P.sup_parts, sup_eq_biUnion, sup_parts, symm.trans
-/
theorem biUnion_parts : P.parts.biUnion id = s :=
  (sup_eq_biUnion _ _).symm.trans P.sup_parts

/--
theorem `existsUnique_mem` / 定理 `existsUnique_mem`

English:
theorem existsUnique_mem
  given: (ha : a in s)
  statement: exists! t, t in P.parts ∧ a in t
  proof: by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine ⟨t, ⟨ht, ht'⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  exact P.eq_of_mem_parts hu ht hu' ht'

中文:
定理 存在Unique_mem
  条件: (ha : a in s)
  结论: 存在! t, t in P.parts ∧ a in t
  证明: by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine ⟨t, ⟨ht, ht'⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  exact P.eq_of_mem_parts hu ht hu' ht'

Depends on / 依赖: P.eq_of_mem_parts, P.exists_mem, eq_of_mem_parts, exists_mem
-/
theorem existsUnique_mem (ha : a in s) : exists! t, t in P.parts ∧ a in t := by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine ⟨t, ⟨ht, ht'⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  exact P.eq_of_mem_parts hu ht hu' ht'

/--
Construct a `Finpartition s` from a finset of finsets `parts` such that each element of `s` is in
exactly one member of `parts`. This provides a converse to `Finpartition.subset`,
`Finpartition.not_empty_mem_parts` and `Finpartition.existsUnique_mem`.
-/
@[simps]
/--
Definition of `ofExistsUnique` / `ofExistsUnique` 的定义

English:
definition ofExistsUnique
  signature: (parts : Finset (Finset α)) (h : forall p in parts, p subseteq s)
  body: parts
  supIndep := by
    simp only [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    rw [Function.onFun]; rw [Finset.disjoint_left]
    intro x hx hx'
    exact hab ((h' x (h _ ha hx)).unique ⟨ha, hx⟩ ⟨hb, hx'⟩)
  sup_parts := by
    ext i
    simp only [mem_sup, id_eq]
    constructor
    · rintro ⟨j, hj, hj'⟩
      exact h j hj hj'
    · rintro hi
      exact (h' i hi).exists
  bot_notMem := h''

中文:
定义 ofExistsUnique
  签名: (parts : 有限集 (有限集 α)) (h : 对任意 p in parts, p subseteq s)
  定义体: parts
  supIndep := by
    simp only [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    rw [Function.onFun]; rw [Finset.disjoint_left]
    intro x hx hx'
    exact hab ((h' x (h _ ha hx)).unique ⟨ha, hx⟩ ⟨hb, hx'⟩)
  sup_parts := by
    ext i
    simp only [mem_sup, id_eq]
    constructor
    · rintro ⟨j, hj, hj'⟩
      exact h j hj hj'
    · rintro hi
      exact (h' i hi).exists
  bot_notMem := h''
-/
def ofExistsUnique (parts : Finset (Finset α)) (h : forall p in parts, p subseteq s)
    (h' : forall a in s, exists! t in parts, a in t) (h'' : ∅ ∉ parts) :
    Finpartition s where
  parts := parts
  supIndep := by
    simp only [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    rw [Function.onFun]; rw [Finset.disjoint_left]
    intro x hx hx'
    exact hab ((h' x (h _ ha hx)).unique ⟨ha, hx⟩ ⟨hb, hx'⟩)
  sup_parts := by
    ext i
    simp only [mem_sup, id_eq]
    constructor
    · rintro ⟨j, hj, hj'⟩
      exact h j hj hj'
    · rintro hi
      exact (h' i hi).exists
  bot_notMem := h''

/--
Definition of `part` / `part` 的定义

English:
definition part
  signature: (a : α)
  body: if ha : a in s then choose (hp := P.existsUnique_mem ha) else ∅

@[simp]

中文:
定义 part
  签名: (a : α)
  定义体: if ha : a in s then choose (hp := P.existsUnique_mem ha) else ∅

@[simp]

Depends on / 依赖: P.existsUnique_mem, existsUnique_mem
-/
def part (a : α) : Finset α := if ha : a in s then choose (hp := P.existsUnique_mem ha) else ∅

@[simp]
/--
lemma `part_mem` / 引理 `part_mem`

English:
lemma part_mem
  statement: P.part a in P.parts ↔ a in s
  proof: by
  by_cases ha : a in s <;> simp [part, ha, choose_mem]

@[simp]

中文:
引理 part_mem
  结论: P.part a in P.parts ↔ a in s
  证明: by
  by_cases ha : a in s <;> simp [part, ha, choose_mem]

@[simp]

Depends on / 依赖: choose_mem
-/
lemma part_mem : P.part a in P.parts ↔ a in s := by
  by_cases ha : a in s <;> simp [part, ha, choose_mem]

@[simp]
/--
lemma `part_eq_empty` / 引理 `part_eq_empty`

English:
lemma part_eq_empty
  statement: P.part a = ∅ ↔ a ∉ s
  proof: ⟨fun h has => P.ne_empty (P.part_mem.2 has) h, fun h => by simp [part, h]⟩

@[simp]

中文:
引理 part_eq_empty
  结论: P.part a = ∅ ↔ a ∉ s
  证明: ⟨fun h has => P.ne_empty (P.part_mem.2 has) h, fun h => by simp [part, h]⟩

@[simp]

Depends on / 依赖: P.ne_empty, P.part_mem, ne_empty, part_mem
-/
lemma part_eq_empty : P.part a = ∅ ↔ a ∉ s :=
  ⟨fun h has => P.ne_empty (P.part_mem.2 has) h, fun h => by simp [part, h]⟩

@[simp]
/--
lemma `part_nonempty` / 引理 `part_nonempty`

English:
lemma part_nonempty
  statement: (P.part a).Nonempty ↔ a in s
  proof: by
  contrapose!; exact part_eq_empty P

@[simp]

中文:
引理 part_nonempty
  结论: (P.part a).非空 ↔ a in s
  证明: by
  contrapose!; exact part_eq_empty P

@[simp]

Depends on / 依赖: contrapose, part_eq_empty
-/
lemma part_nonempty : (P.part a).Nonempty ↔ a in s := by
  contrapose!; exact part_eq_empty P

@[simp]
/--
lemma `part_subset` / 引理 `part_subset`

English:
lemma part_subset
  given: (a : α)
  statement: P.part a subseteq s
  proof: by
  by_cases ha : a in s
· exact P.le P.part_mem.2 ha
  · simp [P.part_eq_empty.2 ha]

@[simp]

中文:
引理 part_subset
  条件: (a : α)
  结论: P.part a subseteq s
  证明: by
  by_cases ha : a in s
· exact P.le P.part_mem.2 ha
  · simp [P.part_eq_empty.2 ha]

@[simp]

Depends on / 依赖: P.le, P.part_eq_empty, P.part_mem, part_eq_empty, part_mem
-/
lemma part_subset (a : α) : P.part a subseteq s := by
  by_cases ha : a in s
· exact P.le P.part_mem.2 ha
  · simp [P.part_eq_empty.2 ha]

@[simp]
/--
lemma `mem_part_self` / 引理 `mem_part_self`

English:
lemma mem_part_self
  statement: a in P.part a ↔ a in s
  proof: by
  by_cases ha : a in s
  · simp [part, ha, choose_property (p := fun s => a in s) P.parts (P.existsUnique_mem ha)]
  · simp [P.part_eq_empty.2, ha]

alias ⟨_, mem_part⟩ := mem_part_self

中文:
引理 mem_part_self
  结论: a in P.part a ↔ a in s
  证明: by
  by_cases ha : a in s
  · simp [part, ha, choose_property (p := fun s => a in s) P.parts (P.existsUnique_mem ha)]
  · simp [P.part_eq_empty.2, ha]

alias ⟨_, mem_part⟩ := mem_part_self

Depends on / 依赖: P.existsUnique_mem, P.part_eq_empty, P.parts, choose_property, existsUnique_mem, part_eq_empty
-/
lemma mem_part_self : a in P.part a ↔ a in s := by
  by_cases ha : a in s
  · simp [part, ha, choose_property (p := fun s => a in s) P.parts (P.existsUnique_mem ha)]
  · simp [P.part_eq_empty.2, ha]

alias ⟨_, mem_part⟩ := mem_part_self

/--
lemma `part_eq_iff_mem` / 引理 `part_eq_iff_mem`

English:
lemma part_eq_iff_mem
  given: (ht : t in P.parts)
  statement: P.part a = t ↔ a in t
  proof: by
  constructor
  · rintro rfl
    simp_all
  · intro hat
    apply P.eq_of_mem_parts (a := a) <;> simp [*, P.le ht hat]

中文:
引理 part_eq_iff_mem
  条件: (ht : t in P.parts)
  结论: P.part a = t ↔ a in t
  证明: by
  constructor
  · rintro rfl
    simp_all
  · intro hat
    apply P.eq_of_mem_parts (a := a) <;> simp [*, P.le ht hat]

Depends on / 依赖: P.eq_of_mem_parts, P.le, eq_of_mem_parts
-/
lemma part_eq_iff_mem (ht : t in P.parts) : P.part a = t ↔ a in t := by
  constructor
  · rintro rfl
    simp_all
  · intro hat
    apply P.eq_of_mem_parts (a := a) <;> simp [*, P.le ht hat]

/--
lemma `part_eq_of_mem` / 引理 `part_eq_of_mem`

English:
lemma part_eq_of_mem
  given: (ht : t in P.parts) (hat : a in t)
  statement: P.part a = t
  proof: (P.part_eq_iff_mem ht).2 hat

中文:
引理 part_eq_of_mem
  条件: (ht : t in P.parts) (hat : a in t)
  结论: P.part a = t
  证明: (P.part_eq_iff_mem ht).2 hat

Depends on / 依赖: P.part_eq_iff_mem, part_eq_iff_mem
-/
lemma part_eq_of_mem (ht : t in P.parts) (hat : a in t) : P.part a = t :=
  (P.part_eq_iff_mem ht).2 hat

/--
lemma `mem_part_iff_part_eq_part` / 引理 `mem_part_iff_part_eq_part`

English:
lemma mem_part_iff_part_eq_part
  given: {b : α} (ha : a in s) (hb : b in s)
  proof: ⟨fun c => (P.part_eq_of_mem (P.part_mem.2 hb) c), fun c => c ▸ P.mem_part ha⟩

中文:
引理 mem_part_iff_part_eq_part
  条件: {b : α} (ha : a in s) (hb : b in s)
  证明: ⟨fun c => (P.part_eq_of_mem (P.part_mem.2 hb) c), fun c => c ▸ P.mem_part ha⟩

Depends on / 依赖: P.mem_part, P.part_eq_of_mem, P.part_mem, mem_part, part_eq_of_mem, part_mem
-/
lemma mem_part_iff_part_eq_part {b : α} (ha : a in s) (hb : b in s) :
    a in P.part b ↔ P.part a = P.part b :=
  ⟨fun c => (P.part_eq_of_mem (P.part_mem.2 hb) c), fun c => c ▸ P.mem_part ha⟩

/--
theorem `part_surjOn` / 定理 `part_surjOn`

English:
theorem part_surjOn
  statement: Set.SurjOn P.part s P.parts
  proof: fun p hp => by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
  have hx' := mem_of_subset (P.le hp) hx
  use x, hx', (P.existsUnique_mem hx').unique ⟨P.part_mem.2 hx', P.mem_part hx'⟩ ⟨hp, hx⟩

中文:
定理 part_surjOn
  结论: 集合.满射限制 P.part s P.parts
  证明: fun p hp => by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
  have hx' := mem_of_subset (P.le hp) hx
  use x, hx', (P.existsUnique_mem hx').unique ⟨P.part_mem.2 hx', P.mem_part hx'⟩ ⟨hp, hx⟩

Depends on / 依赖: P.existsUnique_mem, P.le, P.mem_part, P.nonempty_of_mem_parts, P.part_mem, existsUnique_mem, mem_of_subset, mem_part, nonempty_of_mem_parts, part_mem, unique
-/
theorem part_surjOn : Set.SurjOn P.part s P.parts := fun p hp => by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
  have hx' := mem_of_subset (P.le hp) hx
  use x, hx', (P.existsUnique_mem hx').unique ⟨P.part_mem.2 hx', P.mem_part hx'⟩ ⟨hp, hx⟩

/--
theorem `exists_subset_part_bijOn` / 定理 `exists_subset_part_bijOn`

English:
theorem exists_subset_part_bijOn
  statement: exists r subseteq s, Set.BijOn P.part r P.parts
  proof: by
  obtain ⟨r, hrs, hr⟩ := P.part_surjOn.exists_bijOn_subset
  lift r to Finset α using s.finite_toSet.subset hrs
  exact ⟨r, mod_cast hrs, hr⟩

中文:
定理 存在_subset_part_bijOn
  结论: 存在 r subseteq s, 集合.双射限制 P.part r P.parts
  证明: by
  obtain ⟨r, hrs, hr⟩ := P.part_surjOn.exists_bijOn_subset
  lift r to Finset α using s.finite_toSet.subset hrs
  exact ⟨r, mod_cast hrs, hr⟩

Depends on / 依赖: Finset, P.part_surjOn.exists_bijOn_subset, exists_bijOn_subset, finite_toSet, mod_cast, part_surjOn, s.finite_toSet.subset, subset
-/
theorem exists_subset_part_bijOn : exists r subseteq s, Set.BijOn P.part r P.parts := by
  obtain ⟨r, hrs, hr⟩ := P.part_surjOn.exists_bijOn_subset
  lift r to Finset α using s.finite_toSet.subset hrs
  exact ⟨r, mod_cast hrs, hr⟩

/--
theorem `mem_part_iff_exists` / 定理 `mem_part_iff_exists`

English:
theorem mem_part_iff_exists
  given: {b}
  statement: a in P.part b ↔ exists p in P.parts, a in p ∧ b in p
  proof: by
  constructor
  · intro h
    have : b in s := P.part_nonempty.1 ⟨a, h⟩
    refine ⟨_, ?_, h, ?_⟩ <;> simp [this]
  · rintro ⟨p, hp, hap, hbp⟩
    obtain rfl : P.part b = p := P.part_eq_of_mem hp hbp
    exact hap

中文:
定理 mem_part_iff_存在
  条件: {b}
  结论: a in P.part b ↔ 存在 p in P.parts, a in p ∧ b in p
  证明: by
  constructor
  · intro h
    have : b in s := P.part_nonempty.1 ⟨a, h⟩
    refine ⟨_, ?_, h, ?_⟩ <;> simp [this]
  · rintro ⟨p, hp, hap, hbp⟩
    obtain rfl : P.part b = p := P.part_eq_of_mem hp hbp
    exact hap

Depends on / 依赖: P.part, P.part_eq_of_mem, P.part_nonempty, part_eq_of_mem, part_nonempty
-/
theorem mem_part_iff_exists {b} : a in P.part b ↔ exists p in P.parts, a in p ∧ b in p := by
  constructor
  · intro h
    have : b in s := P.part_nonempty.1 ⟨a, h⟩
    refine ⟨_, ?_, h, ?_⟩ <;> simp [this]
  · rintro ⟨p, hp, hap, hbp⟩
    obtain rfl : P.part b = p := P.part_eq_of_mem hp hbp
    exact hap

/--
Definition of `equivSigmaParts` / `equivSigmaParts` 的定义

English:
definition equivSigmaParts
  signature: : s ≃ Σ t : P.parts, t.1 where
  body: ⟨⟨P.part x.1, P.part_mem.2 x.2⟩, ⟨x, P.mem_part x.2⟩⟩
  invFun x := ⟨x.2, mem_of_subset (P.le x.1.2) x.2.2⟩
  left_inv x := by simp
  right_inv x := by
    ext e
    · obtain ⟨⟨p, mp⟩, ⟨f, mf⟩⟩ := x
      dsimp only at mf ⊢
      rw [P.part_eq_of_mem mp mf]
    · simp

中文:
定义 equivSigmaParts
  签名: : s ≃ Σ t : P.parts, t.1 where
  定义体: ⟨⟨P.part x.1, P.part_mem.2 x.2⟩, ⟨x, P.mem_part x.2⟩⟩
  invFun x := ⟨x.2, mem_of_subset (P.le x.1.2) x.2.2⟩
  left_inv x := by simp
  right_inv x := by
    ext e
    · obtain ⟨⟨p, mp⟩, ⟨f, mf⟩⟩ := x
      dsimp only at mf ⊢
      rw [P.part_eq_of_mem mp mf]
    · simp

Depends on / 依赖: P.mem_part, P.part, P.part_mem, mem_part, part_mem
-/
def equivSigmaParts : s ≃ Σ t : P.parts, t.1 where
  toFun x := ⟨⟨P.part x.1, P.part_mem.2 x.2⟩, ⟨x, P.mem_part x.2⟩⟩
  invFun x := ⟨x.2, mem_of_subset (P.le x.1.2) x.2.2⟩
  left_inv x := by simp
  right_inv x := by
    ext e
    · obtain ⟨⟨p, mp⟩, ⟨f, mf⟩⟩ := x
      dsimp only at mf ⊢
      rw [P.part_eq_of_mem mp mf]
    · simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_enumeration` / 引理 `exists_enumeration`

English:
lemma exists_enumeration
  statement: exists f : s ≃ Σ t : P.parts, Fin #t.1,
  proof: by
  use P.equivSigmaParts.trans ((Equiv.refl _).sigmaCongr (fun t => t.1.equivFin))
  simp [equivSigmaParts, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]

中文:
引理 存在_enumeration
  结论: 存在 f : s ≃ Σ t : P.parts, 有限集 #t.1,
  证明: by
  use P.equivSigmaParts.trans ((Equiv.refl _).sigmaCongr (fun t => t.1.equivFin))
  simp [equivSigmaParts, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]

Depends on / 依赖: Equiv.refl, Equiv.sigmaCongr, Equiv.sigmaCongrLeft, P.equivSigmaParts.trans, equivFin, equivSigmaParts, sigmaCongr, sigmaCongrLeft
-/
lemma exists_enumeration : exists f : s ≃ Σ t : P.parts, Fin #t.1,
    forall a b : s, P.part a = P.part b ↔ (f a).1 = (f b).1 := by
  use P.equivSigmaParts.trans ((Equiv.refl _).sigmaCongr (fun t => t.1.equivFin))
  simp [equivSigmaParts, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]

/--
theorem `sum_card_parts` / 定理 `sum_card_parts`

English:
theorem sum_card_parts
  statement: ∑ i in P.parts, #i = #s
  proof: by
  convert! congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  rfl

中文:
定理 sum_card_parts
  结论: ∑ i in P.parts, #i = #s
  证明: by
  convert! congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  rfl

Depends on / 依赖: Finset, Finset.card, P.biUnion_parts, P.supIndep.pairwiseDisjoint, biUnion_parts, card_biUnion, congr_arg, convert, pairwiseDisjoint, supIndep
-/
theorem sum_card_parts : ∑ i in P.parts, #i = #s := by
  convert! congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  rfl

/-- `⊥` is the partition in singletons, aka discrete partition. -/
instance (s : Finset α) : Bot (Finpartition s) :=
  ⟨{ parts := s.map ⟨singleton, singleton_injective⟩
supIndep := Set.PairwiseDisjoint.supIndep by
        rw [Finset.coe_map]
        exact Finset.pairwiseDisjoint_range_singleton.subset (Set.image_subset_range _ _)
      sup_parts := by rw [sup_map, id_comp, Embedding.coeFn_mk, Finset.sup_singleton_eq_self]
      bot_notMem := by simp }⟩

@[simp]
/--
theorem `parts_bot` / 定理 `parts_bot`

English:
theorem parts_bot
  given: (s : Finset α)
  proof: rfl

中文:
定理 parts_bot
  条件: (s : 有限集 α)
  证明: rfl
-/
theorem parts_bot (s : Finset α) :
    (⊥ : Finpartition s).parts = s.map ⟨singleton, singleton_injective⟩ :=
  rfl

/--
theorem `card_bot` / 定理 `card_bot`

English:
theorem card_bot
  given: (s : Finset α)
  statement: #(⊥ : Finpartition s).parts = #s
  proof: Finset.card_map _

中文:
定理 card_bot
  条件: (s : 有限集 α)
  结论: #(⊥ : 有限分拆 s).parts = #s
  证明: Finset.card_map _

Depends on / 依赖: Finset, Finset.card_map, card_map
-/
theorem card_bot (s : Finset α) : #(⊥ : Finpartition s).parts = #s := Finset.card_map _

/--
theorem `mem_bot_iff` / 定理 `mem_bot_iff`

English:
theorem mem_bot_iff
  statement: t in (⊥ : Finpartition s).parts ↔ exists a in s, {a} = t
  proof: mem_map

中文:
定理 mem_bot_iff
  结论: t in (⊥ : 有限分拆 s).parts ↔ 存在 a in s, {a} = t
  证明: mem_map

Depends on / 依赖: mem_map
-/
theorem mem_bot_iff : t in (⊥ : Finpartition s).parts ↔ exists a in s, {a} = t :=
  mem_map

instance (s : Finset α) : OrderBot (Finpartition s) :=
  { (inferInstance : Bot (Finpartition s)) with
    bot_le := fun P t ht => by
      rw [mem_bot_iff] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨t, ht, hat⟩ := P.exists_mem ha
      exact ⟨t, ht, singleton_subset_iff.2 hat⟩ }

/--
theorem `card_parts_le_card` / 定理 `card_parts_le_card`

English:
theorem card_parts_le_card
  statement: #P.parts <= #s
  proof: by
  rw [← card_bot s]
  exact card_mono bot_le

中文:
定理 card_parts_le_card
  结论: #P.parts <= #s
  证明: by
  rw [← card_bot s]
  exact card_mono bot_le

Depends on / 依赖: bot_le, card_bot, card_mono
-/
theorem card_parts_le_card : #P.parts <= #s := by
  rw [← card_bot s]
  exact card_mono bot_le

/--
lemma `card_mod_card_parts_le` / 引理 `card_mod_card_parts_le`

English:
lemma card_mod_card_parts_le
  statement: #s % #P.parts <= #P.parts
  proof: by
  obtain h | h := (#P.parts).eq_zero_or_pos
  · rw [h]
    rw [Finset.card_eq_zero]; rw [parts_eq_empty_iff]; rw [bot_eq_empty]; rw [← Finset.card_eq_zero] at h
    rw [h]
  · exact (Nat.mod_lt _ h).le

中文:
引理 card_mod_card_parts_le
  结论: #s % #P.parts <= #P.parts
  证明: by
  obtain h | h := (#P.parts).eq_zero_or_pos
  · rw [h]
    rw [Finset.card_eq_zero]; rw [parts_eq_empty_iff]; rw [bot_eq_empty]; rw [← Finset.card_eq_zero] at h
    rw [h]
  · exact (Nat.mod_lt _ h).le

Depends on / 依赖: Finset, Finset.card_eq_zero, Nat.mod_lt, P.parts, bot_eq_empty, card_eq_zero, eq_zero_or_pos, mod_lt, parts_eq_empty_iff
-/
lemma card_mod_card_parts_le : #s % #P.parts <= #P.parts := by
  obtain h | h := (#P.parts).eq_zero_or_pos
  · rw [h]
    rw [Finset.card_eq_zero]; rw [parts_eq_empty_iff]; rw [bot_eq_empty]; rw [← Finset.card_eq_zero] at h
    rw [h]
  · exact (Nat.mod_lt _ h).le

section SetSetoid

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps -isSimp]
/--
Definition of `ofSetSetoid` / `ofSetSetoid` 的定义

English:
definition ofSetSetoid
  signature: (s : Setoid α) (x : Finset α) [DecidableRel s.r]
  body: x.image fun a => {b in x | s.r a b}
  supIndep := by
    suffices forall (a b c d : α), s a d -> s b d -> (s a c ↔ s b c) by
      simp only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise, coe_image,
        Set.mem_image, mem_coe, ne_eq, onFun, id_eq, disjoint_iff_ne, forall_mem_not_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, filter_inj',
        not_forall, @not_imp_comm (_ ↔ _), Decidable.not_not]
      intro _ _ _ _ _ _ _ _ ha _ hb
      exact ⟨(s.trans' hb <| s.trans' (s.symm' ha) ·), (s.trans' ha <| s.trans' (s.symm' hb) ·)⟩
    simp +contextual [← Quotient.eq]
  sup_parts := by
    ext a
    simp_rw [sup_image, id_comp, mem_sup, mem_filter]
    refine ⟨(·.choose_spec.2.1), fun _ => by use a⟩
  bot_notMem := by
    suffices forall x₁ in x, exists x₂ in x, s x₁ x₂ by simpa [filter_eq_empty_iff]
    intro x _
    use x

中文:
定义 ofSetSetoid
  签名: (s : 集合等价关系 α) (x : 有限集 α) [DecidableRel s.r]
  定义体: x.image fun a => {b in x | s.r a b}
  supIndep := by
    suffices forall (a b c d : α), s a d -> s b d -> (s a c ↔ s b c) by
      simp only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise, coe_image,
        Set.mem_image, mem_coe, ne_eq, onFun, id_eq, disjoint_iff_ne, forall_mem_not_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, filter_inj',
        not_forall, @not_imp_comm (_ ↔ _), Decidable.not_not]
      intro _ _ _ _ _ _ _ _ ha _ hb
      exact ⟨(s.trans' hb <| s.trans' (s.symm' ha) ·), (s.trans' ha <| s.trans' (s.symm' hb) ·)⟩
    simp +contextual [← Quotient.eq]
  sup_parts := by
    ext a
    simp_rw [sup_image, id_comp, mem_sup, mem_filter]
    refine ⟨(·.choose_spec.2.1), fun _ => by use a⟩
  bot_notMem := by
    suffices forall x₁ in x, exists x₂ in x, s x₁ x₂ by simpa [filter_eq_empty_iff]
    intro x _
    use x

Depends on / 依赖: x.image
-/
def ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartition x where
  parts := x.image fun a => {b in x | s.r a b}
  supIndep := by
    suffices forall (a b c d : α), s a d -> s b d -> (s a c ↔ s b c) by
      simp only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise, coe_image,
        Set.mem_image, mem_coe, ne_eq, onFun, id_eq, disjoint_iff_ne, forall_mem_not_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, filter_inj',
        not_forall, @not_imp_comm (_ ↔ _), Decidable.not_not]
      intro _ _ _ _ _ _ _ _ ha _ hb
      exact ⟨(s.trans' hb <| s.trans' (s.symm' ha) ·), (s.trans' ha <| s.trans' (s.symm' hb) ·)⟩
    simp +contextual [← Quotient.eq]
  sup_parts := by
    ext a
    simp_rw [sup_image, id_comp, mem_sup, mem_filter]
    refine ⟨(·.choose_spec.2.1), fun _ => by use a⟩
  bot_notMem := by
    suffices forall x₁ in x, exists x₂ in x, s x₁ x₂ by simpa [filter_eq_empty_iff]
    intro x _
    use x

/--
theorem `mem_part_ofSetSetoid_iff_rel` / 定理 `mem_part_ofSetSetoid_iff_rel`

English:
theorem mem_part_ofSetSetoid_iff_rel
  given: {s : Setoid α} (x : Finset α) [DecidableRel s.r] {b : α}
  proof: by
  suffices (exists a₁ in x, (b in x ∧ s a₁ b) ∧ a in x ∧ s a₁ a) ↔ a in x ∧ b in x ∧ s a b by
    simpa [mem_part_iff_exists, ofSetSetoid_parts]
  exact ⟨
    fun ⟨c, _, ⟨hb, hcb⟩, ⟨ha, hca⟩⟩ => ⟨ha, hb, s.trans' (s.symm' hca) hcb⟩,
    fun h => ⟨a, ⟨h.1, ⟨⟨h.2.1, h.2.2⟩, ⟨h.1, s.refl _⟩⟩⟩⟩
  ⟩

中文:
定理 mem_part_ofSetSetoid_iff_rel
  条件: {s : 集合等价关系 α} (x : 有限集 α) [DecidableRel s.r] {b : α}
  证明: by
  suffices (exists a₁ in x, (b in x ∧ s a₁ b) ∧ a in x ∧ s a₁ a) ↔ a in x ∧ b in x ∧ s a b by
    simpa [mem_part_iff_exists, ofSetSetoid_parts]
  exact ⟨
    fun ⟨c, _, ⟨hb, hcb⟩, ⟨ha, hca⟩⟩ => ⟨ha, hb, s.trans' (s.symm' hca) hcb⟩,
    fun h => ⟨a, ⟨h.1, ⟨⟨h.2.1, h.2.2⟩, ⟨h.1, s.refl _⟩⟩⟩⟩
  ⟩

Depends on / 依赖: mem_part_iff_exists, ofSetSetoid_parts, s.refl, s.symm, s.trans
-/
theorem mem_part_ofSetSetoid_iff_rel {s : Setoid α} (x : Finset α) [DecidableRel s.r] {b : α} :
    b in (ofSetSetoid s x).part a ↔ a in x ∧ b in x ∧ s a b := by
  suffices (exists a₁ in x, (b in x ∧ s a₁ b) ∧ a in x ∧ s a₁ a) ↔ a in x ∧ b in x ∧ s a b by
    simpa [mem_part_iff_exists, ofSetSetoid_parts]
  exact ⟨
    fun ⟨c, _, ⟨hb, hcb⟩, ⟨ha, hca⟩⟩ => ⟨ha, hb, s.trans' (s.symm' hca) hcb⟩,
    fun h => ⟨a, ⟨h.1, ⟨⟨h.2.1, h.2.2⟩, ⟨h.1, s.refl _⟩⟩⟩⟩
  ⟩

end SetSetoid

section Setoid

variable [Fintype α]

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps! -isSimp]
/--
Definition of `ofSetoid` / `ofSetoid` 的定义

English:
definition ofSetoid
  signature: (s : Setoid α) [DecidableRel s.r]
  body: ofSetSetoid s univ

中文:
定义 ofSetoid
  签名: (s : 集合等价关系 α) [DecidableRel s.r]
  定义体: ofSetSetoid s univ

Depends on / 依赖: ofSetSetoid
-/
def ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α) :=
  ofSetSetoid s univ

/--
theorem `mem_part_ofSetoid_iff_rel` / 定理 `mem_part_ofSetoid_iff_rel`

English:
theorem mem_part_ofSetoid_iff_rel
  given: {s : Setoid α} [DecidableRel s.r] {b : α}
  proof: by
  suffices b in (ofSetSetoid s univ).part a ↔ a in univ ∧ b in univ ∧ s a b by simpa
  exact mem_part_ofSetSetoid_iff_rel univ

中文:
定理 mem_part_ofSetoid_iff_rel
  条件: {s : 集合等价关系 α} [DecidableRel s.r] {b : α}
  证明: by
  suffices b in (ofSetSetoid s univ).part a ↔ a in univ ∧ b in univ ∧ s a b by simpa
  exact mem_part_ofSetSetoid_iff_rel univ

Depends on / 依赖: mem_part_ofSetSetoid_iff_rel, ofSetSetoid
-/
theorem mem_part_ofSetoid_iff_rel {s : Setoid α} [DecidableRel s.r] {b : α} :
    b in (ofSetoid s).part a ↔ s a b := by
  suffices b in (ofSetSetoid s univ).part a ↔ a in univ ∧ b in univ ∧ s a b by simpa
  exact mem_part_ofSetSetoid_iff_rel univ

end Setoid

section Atomise

/--
Definition of `atomise` / `atomise` 的定义

English:
definition atomise
  signature: (s : Finset α) (F : Finset (Finset α))
  body: ofErase (F.powerset.image fun Q => {i in s | forall t in F, t in Q ↔ i in t})
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h =>
      disjoint_left.mpr fun z hz1 hz2 =>
        h (by
            rw [mem_coe]; rw [mem_image] at hx hy
            obtain ⟨Q, hQ, rfl⟩ := hx
            obtain ⟨R, hR, rfl⟩ := hy
            suffices h' : Q = R by
              subst h'
              exact of_eq_true (eq_self {i in s | forall t in F, t in Q ↔ i in t})
            rw [id]; rw [mem_filter] at hz1 hz2
            rw [mem_powerset] at hQ hR
            ext i
            refine ⟨fun hi => ?_, fun hi => ?_⟩
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
    (by
      refine (Finset.sup_le fun t ht => ?_).antisymm fun a ha => ?_
      · rw [mem_image] at ht
        obtain ⟨A, _, rfl⟩ := ht
        exact s.filter_subset _
      · rw [mem_sup]
        refine
          ⟨{i in s | forall t in F, t in {u in F | a in u} ↔ i in t},
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht => ?_⟩⟩
        rw [mem_filter]
        exact and_iff_right ht)

中文:
定义 atomise
  签名: (s : 有限集 α) (F : 有限集 (有限集 α))
  定义体: ofErase (F.powerset.image fun Q => {i in s | forall t in F, t in Q ↔ i in t})
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h =>
      disjoint_left.mpr fun z hz1 hz2 =>
        h (by
            rw [mem_coe]; rw [mem_image] at hx hy
            obtain ⟨Q, hQ, rfl⟩ := hx
            obtain ⟨R, hR, rfl⟩ := hy
            suffices h' : Q = R by
              subst h'
              exact of_eq_true (eq_self {i in s | forall t in F, t in Q ↔ i in t})
            rw [id]; rw [mem_filter] at hz1 hz2
            rw [mem_powerset] at hQ hR
            ext i
            refine ⟨fun hi => ?_, fun hi => ?_⟩
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
    (by
      refine (Finset.sup_le fun t ht => ?_).antisymm fun a ha => ?_
      · rw [mem_image] at ht
        obtain ⟨A, _, rfl⟩ := ht
        exact s.filter_subset _
      · rw [mem_sup]
        refine
          ⟨{i in s | forall t in F, t in {u in F | a in u} ↔ i in t},
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht => ?_⟩⟩
        rw [mem_filter]
        exact and_iff_right ht)

Depends on / 依赖: F.powerset.image, PairwiseDisjoint, Set.PairwiseDisjoint.supIndep, disjoint_left, disjoint_left.mpr, eq_self, mem_coe, mem_filter, mem_image, mem_powerset, ofErase, of_eq_true, powerset, supIndep
-/
def atomise (s : Finset α) (F : Finset (Finset α)) : Finpartition s :=
  ofErase (F.powerset.image fun Q => {i in s | forall t in F, t in Q ↔ i in t})
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h =>
      disjoint_left.mpr fun z hz1 hz2 =>
        h (by
            rw [mem_coe]; rw [mem_image] at hx hy
            obtain ⟨Q, hQ, rfl⟩ := hx
            obtain ⟨R, hR, rfl⟩ := hy
            suffices h' : Q = R by
              subst h'
              exact of_eq_true (eq_self {i in s | forall t in F, t in Q ↔ i in t})
            rw [id]; rw [mem_filter] at hz1 hz2
            rw [mem_powerset] at hQ hR
            ext i
            refine ⟨fun hi => ?_, fun hi => ?_⟩
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
    (by
      refine (Finset.sup_le fun t ht => ?_).antisymm fun a ha => ?_
      · rw [mem_image] at ht
        obtain ⟨A, _, rfl⟩ := ht
        exact s.filter_subset _
      · rw [mem_sup]
        refine
          ⟨{i in s | forall t in F, t in {u in F | a in u} ↔ i in t},
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht => ?_⟩⟩
        rw [mem_filter]
        exact and_iff_right ht)

variable {F : Finset (Finset α)}

/--
theorem `mem_atomise` / 定理 `mem_atomise`

English:
theorem mem_atomise
  proof: by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_powerset]

中文:
定理 mem_atomise
  证明: by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_powerset]

Depends on / 依赖: atomise, bot_eq_empty, mem_erase, mem_image, mem_powerset, nonempty_iff_ne_empty, ofErase
-/
theorem mem_atomise :
    t in (atomise s F).parts ↔
      t.Nonempty ∧ exists Q subseteq F, {i in s | forall u in F, u in Q ↔ i in u} = t := by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_powerset]

/--
theorem `atomise_empty` / 定理 `atomise_empty`

English:
theorem atomise_empty
  given: (hs : s.Nonempty)
  statement: (atomise s ∅).parts = {s}
  proof: by
  simp only [atomise, powerset_empty, image_singleton, notMem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_true]
  exact erase_eq_of_notMem (notMem_singleton.2 hs.ne_empty.symm)

中文:
定理 atomise_empty
  条件: (hs : s.非空)
  结论: (atomise s ∅).parts = {s}
  证明: by
  simp only [atomise, powerset_empty, image_singleton, notMem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_true]
  exact erase_eq_of_notMem (notMem_singleton.2 hs.ne_empty.symm)

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, atomise, erase_eq_of_notMem, filter_true, forall_iff, hs.ne_empty.symm, image_singleton, imp_true_iff, ne_empty, notMem_empty, notMem_singleton, powerset_empty
-/
theorem atomise_empty (hs : s.Nonempty) : (atomise s ∅).parts = {s} := by
  simp only [atomise, powerset_empty, image_singleton, notMem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_true]
  exact erase_eq_of_notMem (notMem_singleton.2 hs.ne_empty.symm)

/--
theorem `card_atomise_le` / 定理 `card_atomise_le`

English:
theorem card_atomise_le
  statement: #(atomise s F).parts <= 2 ^ #F
  proof: (card_le_card <| erase_subset _ _).trans Finset.card_image_le.trans (card_powerset _).le

中文:
定理 card_atomise_le
  结论: #(atomise s F).parts <= 2 ^ #F
  证明: (card_le_card <| erase_subset _ _).trans Finset.card_image_le.trans (card_powerset _).le

Depends on / 依赖: Finset, Finset.card_image_le.trans, card_image_le, card_le_card, card_powerset, erase_subset
-/
theorem card_atomise_le : #(atomise s F).parts <= 2 ^ #F :=
(card_le_card <| erase_subset _ _).trans Finset.card_image_le.trans (card_powerset _).le

/--
theorem `biUnion_filter_atomise` / 定理 `biUnion_filter_atomise`

English:
theorem biUnion_filter_atomise
  given: (ht : t in F) (hts : t subseteq s)
  proof: by
  ext a
  refine mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ => (mem_filter.1 hu).2.1 ha, fun ha => ?_⟩
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  refine ⟨u, mem_filter.2 ⟨hu, fun b hb => ?_, _, hau⟩, hau⟩
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  rw [mem_filter] at hau hb
  rwa [← hb.2 _ ht, hau.2 _ ht]

中文:
定理 biUnion_filter_atomise
  条件: (ht : t in F) (hts : t subseteq s)
  证明: by
  ext a
  refine mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ => (mem_filter.1 hu).2.1 ha, fun ha => ?_⟩
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  refine ⟨u, mem_filter.2 ⟨hu, fun b hb => ?_, _, hau⟩, hau⟩
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  rw [mem_filter] at hau hb
  rwa [← hb.2 _ ht, hau.2 _ ht]

Depends on / 依赖: atomise, exists_mem, mem_atomise, mem_biUnion, mem_biUnion.trans, mem_filter
-/
theorem biUnion_filter_atomise (ht : t in F) (hts : t subseteq s) :
    {u in (atomise s F).parts | u subseteq t ∧ u.Nonempty}.biUnion id = t := by
  ext a
  refine mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ => (mem_filter.1 hu).2.1 ha, fun ha => ?_⟩
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  refine ⟨u, mem_filter.2 ⟨hu, fun b hb => ?_, _, hau⟩, hau⟩
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  rw [mem_filter] at hau hb
  rwa [← hb.2 _ ht, hau.2 _ ht]

/--
theorem `card_filter_atomise_le_two_pow` / 定理 `card_filter_atomise_le_two_pow`

English:
theorem card_filter_atomise_le_two_pow
  given: (ht : t in F)
  proof: by
  suffices h :
    {u in (atomise s F).parts | u subseteq t ∧ u.Nonempty} subseteq
      (F.erase t).powerset.image fun P => {i in s | forall x in F, x in insert t P ↔ i in x} by
    refine (card_le_card h).trans (card_image_le.trans ?_)
    rw [card_powerset]; rw [card_erase_of_mem ht]
  rw [subset_iff]
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp, and_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  refine ⟨P.erase t, erase_subset_erase _ PQ, ?_⟩
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]

中文:
定理 card_filter_atomise_le_two_pow
  条件: (ht : t in F)
  证明: by
  suffices h :
    {u in (atomise s F).parts | u subseteq t ∧ u.Nonempty} subseteq
      (F.erase t).powerset.image fun P => {i in s | forall x in F, x in insert t P ↔ i in x} by
    refine (card_le_card h).trans (card_image_le.trans ?_)
    rw [card_powerset]; rw [card_erase_of_mem ht]
  rw [subset_iff]
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp, and_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  refine ⟨P.erase t, erase_subset_erase _ PQ, ?_⟩
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]

Depends on / 依赖: F.erase, Finset, Finset.Nonempty, Nonempty, P.erase, and_imp, atomise, card_erase_of_mem, card_image_le, card_image_le.trans, card_le_card, card_powerset, erase_subset_era, exists_imp, insert, mem_atomise, mem_filter, mem_image, mem_powerset, powerset
-/
theorem card_filter_atomise_le_two_pow (ht : t in F) :
    #{u in (atomise s F).parts | u subseteq t ∧ u.Nonempty} <= 2 ^ (#F - 1) := by
  suffices h :
    {u in (atomise s F).parts | u subseteq t ∧ u.Nonempty} subseteq
      (F.erase t).powerset.image fun P => {i in s | forall x in F, x in insert t P ↔ i in x} by
    refine (card_le_card h).trans (card_image_le.trans ?_)
    rw [card_powerset]; rw [card_erase_of_mem ht]
  rw [subset_iff]
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp, and_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  refine ⟨P.erase t, erase_subset_erase _ PQ, ?_⟩
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]

end Atomise

end Finpartition
