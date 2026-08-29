/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Set.SymmDiff

/-!
# Basic lemmas on finite sets

This file contains lemmas on the interaction of various definitions on the `Finset` type.

For an explanation of `Finset` design decisions, please see `Mathlib/Data/Finset/Defs.lean`.

## Main declarations

### Main definitions

* `Finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Equivalences between finsets

* The `Mathlib/Logic/Equiv/Defs.lean` file describes a general type of equivalence, so look in there
  for any lemmas. There is some API for rewriting sums and products from `s` to `t` given that
  `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-! #### union -/

@[simp]
/--
theorem `disjUnion_eq_union` / 定理 `disjUnion_eq_union`

English:
theorem disjUnion_eq_union
  given: (s t h)
  statement: @disjUnion α s t h = s union t
  proof: by grind

@[simp]

中文:
定理 disjUnion_eq_union
  条件: (s t h)
  结论: @disjUnion α s t h = s union t
  证明: by grind

@[simp]
-/
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s union t := by grind

@[simp]
/--
theorem `disjoint_union_left` / 定理 `disjoint_union_left`

English:
theorem disjoint_union_left
  statement: Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
  proof: by
  simp only [disjoint_left, mem_union, or_imp, forall_and]

@[simp]

中文:
定理 disjoint_union_left
  结论: Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
  证明: by
  simp only [disjoint_left, mem_union, or_imp, forall_and]

@[simp]

Depends on / 依赖: disjoint_left, forall_and, mem_union, or_imp
-/
theorem disjoint_union_left : Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_union, or_imp, forall_and]

@[simp]
/--
theorem `disjoint_union_right` / 定理 `disjoint_union_right`

English:
theorem disjoint_union_right
  statement: Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u
  proof: by
  simp only [disjoint_right, mem_union, or_imp, forall_and]

中文:
定理 disjoint_union_right
  结论: Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u
  证明: by
  simp only [disjoint_right, mem_union, or_imp, forall_and]

Depends on / 依赖: disjoint_right, forall_and, mem_union, or_imp
-/
theorem disjoint_union_right : Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]


/--
theorem `not_disjoint_iff_nonempty_inter` / 定理 `not_disjoint_iff_nonempty_inter`

English:
theorem not_disjoint_iff_nonempty_inter
  statement: ¬Disjoint s t ↔ (s inter t).Nonempty
  proof: not_disjoint_iff.trans by simp [Finset.Nonempty]

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

中文:
定理 not_disjoint_iff_nonempty_inter
  结论: ¬Disjoint s t ↔ (s inter t).非空
  证明: not_disjoint_iff.trans by simp [Finset.Nonempty]

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, not_disjoint_iff, not_disjoint_iff.trans
-/
theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s inter t).Nonempty :=
not_disjoint_iff.trans by simp [Finset.Nonempty]

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

/--
theorem `disjoint_or_nonempty_inter` / 定理 `disjoint_or_nonempty_inter`

English:
theorem disjoint_or_nonempty_inter
  given: (s t : Finset α)
  statement: Disjoint s t ∨ (s inter t).Nonempty
  proof: by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _

omit [DecidableEq α] in

中文:
定理 disjoint_or_nonempty_inter
  条件: (s t : 有限集 α)
  结论: Disjoint s t ∨ (s inter t).非空
  证明: by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _

omit [DecidableEq α] in

Depends on / 依赖: not_disjoint_iff_nonempty_inter
-/
theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s inter t).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _

omit [DecidableEq α] in
/--
theorem `disjoint_of_subset_iff_left_eq_empty` / 定理 `disjoint_of_subset_iff_left_eq_empty`

English:
theorem disjoint_of_subset_iff_left_eq_empty
  given: (h : s subseteq t)
  proof: disjoint_of_le_iff_left_eq_bot h

中文:
定理 disjoint_of_subset_iff_left_eq_empty
  条件: (h : s subseteq t)
  证明: disjoint_of_le_iff_left_eq_bot h

Depends on / 依赖: disjoint_of_le_iff_left_eq_bot
-/
theorem disjoint_of_subset_iff_left_eq_empty (h : s subseteq t) :
    Disjoint s t ↔ s = ∅ :=
  disjoint_of_le_iff_left_eq_bot h

/--
lemma `pairwiseDisjoint_iff` / 引理 `pairwiseDisjoint_iff`

English:
lemma pairwiseDisjoint_iff
  given: {ι : Type*} {s : Set ι} {f : ι -> Finset α}
  proof: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

中文:
引理 pairwiseDisjoint_iff
  条件: {ι : 类型} {s : 集合 ι} {f : ι -> 有限集 α}
  证明: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

Depends on / 依赖: Pairwise, PairwiseDisjoint, Set.Pairwise, Set.PairwiseDisjoint, not_disjoint_iff_nonempty_inter, not_imp_comm
-/
lemma pairwiseDisjoint_iff {ι : Type*} {s : Set ι} {f : ι -> Finset α} :
    s.PairwiseDisjoint f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f i inter f j).Nonempty -> i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

end Lattice

/--
Instance `isDirected_le` / 实例 `isDirected_le`

English:
instance isDirected_le
  signature: : IsDirectedOrder (Finset α)
  body: by classical infer_instance

中文:
实例 isDirected_le
  签名: : IsDirectedOrder (有限集 α)
  定义体: by classical infer_instance

Depends on / 依赖: classical, infer_instance
-/
instance isDirected_le : IsDirectedOrder (Finset α) := by classical infer_instance
/--
Instance `isDirected_subset` / 实例 `isDirected_subset`

English:
instance isDirected_subset
  signature: : IsDirected (Finset α) (· subseteq ·)
  body: isDirected_le

中文:
实例 isDirected_subset
  签名: : 是Directed (有限集 α) (· subseteq ·)
  定义体: isDirected_le

Depends on / 依赖: NeZero, NeZero.ne, isDirected_le, n.natAbs_ne_zero.mpr, natAbs_ne_zero
-/
instance isDirected_subset : IsDirected (Finset α) (· subseteq ·) := isDirected_le

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

@[simp]
/--
theorem `erase_empty` / 定理 `erase_empty`

English:
theorem erase_empty
  given: (a : α)
  statement: erase ∅ a = ∅
  proof: rfl

中文:
定理 erase_empty
  条件: (a : α)
  结论: erase ∅ a = ∅
  证明: rfl

Depends on / 依赖: Nat.le_refl, NeZero, NeZero.ne, add_le_add, le_refl, one_le_iff_ne_zero, one_le_iff_ne_zero.mpr
-/
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl

/--
lemma `Nontrivial.erase_nonempty` / 引理 `Nontrivial.erase_nonempty`

English:
lemma Nontrivial.erase_nonempty
  given: (hs : s.Nontrivial)
  statement: (s.erase a).Nonempty
  proof: (hs.exists_ne a).imp by simp_all

中文:
引理 非平凡.erase_nonempty
  条件: (hs : s.非平凡)
  结论: (s.erase a).非空
  证明: (hs.exists_ne a).imp by simp_all
-/
protected lemma Nontrivial.erase_nonempty (hs : s.Nontrivial) : (s.erase a).Nonempty :=
(hs.exists_ne a).imp by simp_all

/--
lemma `erase_nonempty` / 引理 `erase_nonempty`

English:
lemma erase_nonempty
  given: (ha : a in s)
  statement: (s.erase a).Nonempty ↔ s.Nontrivial
  proof: by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ in _)]
  refine ⟨?_, fun hs => hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]

中文:
引理 erase_nonempty
  条件: (ha : a in s)
  结论: (s.erase a).非空 ↔ s.非平凡
  证明: by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ in _)]
  refine ⟨?_, fun hs => hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
-/
@[simp] lemma erase_nonempty (ha : a in s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ in _)]
  refine ⟨?_, fun hs => hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
/--
theorem `erase_singleton` / 定理 `erase_singleton`

English:
theorem erase_singleton
  given: (a : α)
  statement: ({a} : Finset α).erase a = ∅
  proof: by grind

@[simp]

中文:
定理 erase_singleton
  条件: (a : α)
  结论: ({a} : 有限集 α).erase a = ∅
  证明: by grind

@[simp]

Depends on / 依赖: AtLeastTwo, NeZero, n.AtLeastTwo, toNeZero
-/
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by grind

@[simp]
/--
theorem `erase_insert_eq_erase` / 定理 `erase_insert_eq_erase`

English:
theorem erase_insert_eq_erase
  given: (s : Finset α) (a : α)
  statement: (insert a s).erase a = s.erase a
  proof: by grind

中文:
定理 erase_insert_eq_erase
  条件: (s : 有限集 α) (a : α)
  结论: (insert a s).erase a = s.erase a
  证明: by grind
-/
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a := by grind

/--
theorem `erase_insert` / 定理 `erase_insert`

English:
theorem erase_insert
  given: {a : α} {s : Finset α} (h : a ∉ s)
  statement: (insert a s).erase a = s
  proof: by grind

中文:
定理 erase_insert
  条件: {a : α} {s : 有限集 α} (h : a ∉ s)
  结论: (insert a s).erase a = s
  证明: by grind

Depends on / 依赖: Nat.div_lt_self, Nat.log, Nat.logTR, decreasing_by, decreasing_trivial, div_lt_self, numbers, performs
-/
theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).erase a = s := by grind

/--
theorem `erase_insert_of_ne` / 定理 `erase_insert_of_ne`

English:
theorem erase_insert_of_ne
  given: {a b : α} {s : Finset α} (h : a != b)
  proof: by grind

中文:
定理 erase_insert_of_ne
  条件: {a b : α} {s : 有限集 α} (h : a != b)
  证明: by grind
-/
theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a != b) :
    (insert a s).erase b = insert a (s.erase b) := by grind

/--
theorem `erase_cons_of_ne` / 定理 `erase_cons_of_ne`

English:
theorem erase_cons_of_ne
  given: {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a != b)
  proof: by grind

中文:
定理 erase_cons_of_ne
  条件: {a b : α} {s : 有限集 α} (ha : a ∉ s) (hb : a != b)
  证明: by grind
-/
theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a != b) :
(s.cons a ha).erase b = (s.erase b).cons a fun h => ha erase_subset _ _ h := by grind

/--
theorem `insert_erase` / 定理 `insert_erase`

English:
theorem insert_erase
  given: (h : a in s)
  statement: insert a (s.erase a) = s
  proof: by grind

中文:
定理 insert_erase
  条件: (h : a in s)
  结论: insert a (s.erase a) = s
  证明: by grind
-/
@[simp] theorem insert_erase (h : a in s) : insert a (s.erase a) = s := by grind

/--
lemma `erase_eq_iff_eq_insert` / 引理 `erase_eq_iff_eq_insert`

English:
lemma erase_eq_iff_eq_insert
  given: (hs : a in s) (ht : a ∉ t)
  statement: s.erase a = t ↔ s = insert a t
  proof: by
  aesop

中文:
引理 erase_eq_iff_eq_insert
  条件: (hs : a in s) (ht : a ∉ t)
  结论: s.erase a = t ↔ s = insert a t
  证明: by
  aesop
-/
lemma erase_eq_iff_eq_insert (hs : a in s) (ht : a ∉ t) : s.erase a = t ↔ s = insert a t := by
  aesop

/--
lemma `insert_erase_invOn` / 引理 `insert_erase_invOn`

English:
lemma insert_erase_invOn
  proof: ⟨fun _s => insert_erase, fun _s => erase_insert⟩

中文:
引理 insert_erase_invOn
  证明: ⟨fun _s => insert_erase, fun _s => erase_insert⟩

Depends on / 依赖: erase_insert, insert_erase
-/
lemma insert_erase_invOn :
    Set.InvOn (insert a) (fun s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s} :=
  ⟨fun _s => insert_erase, fun _s => erase_insert⟩

/--
theorem `erase_ssubset` / 定理 `erase_ssubset`

English:
theorem erase_ssubset
  given: {a : α} {s : Finset α} (h : a in s)
  statement: s.erase a ⊂ s
  proof: by grind

中文:
定理 erase_ssubset
  条件: {a : α} {s : 有限集 α} (h : a in s)
  结论: s.erase a ⊂ s
  证明: by grind
-/
theorem erase_ssubset {a : α} {s : Finset α} (h : a in s) : s.erase a ⊂ s := by grind

/--
theorem `erase_union_eq` / 定理 `erase_union_eq`

English:
theorem erase_union_eq
  given: (a : α) (s : Finset α) (h : a in s)
  statement: (erase s a) union {a} = s
  proof: by grind

中文:
定理 erase_union_eq
  条件: (a : α) (s : 有限集 α) (h : a in s)
  结论: (erase s a) union {a} = s
  证明: by grind
-/
theorem erase_union_eq (a : α) (s : Finset α) (h : a in s) : (erase s a) union {a} = s := by grind

/--
theorem `ssubset_iff_exists_subset_erase` / 定理 `ssubset_iff_exists_subset_erase`

English:
theorem ssubset_iff_exists_subset_erase
  given: {s t : Finset α}
  statement: s ⊂ t ↔ exists a in t, s subseteq t.erase a
  proof: by
  grind

中文:
定理 ssubset_iff_存在_subset_erase
  条件: {s t : 有限集 α}
  结论: s ⊂ t ↔ 存在 a in t, s subseteq t.erase a
  证明: by
  grind
-/
theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ exists a in t, s subseteq t.erase a := by
  grind

/--
theorem `erase_ssubset_insert` / 定理 `erase_ssubset_insert`

English:
theorem erase_ssubset_insert
  given: (s : Finset α) (a : α)
  statement: s.erase a ⊂ insert a s
  proof: ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, by grw [← subset_insert]⟩

中文:
定理 erase_ssubset_insert
  条件: (s : 有限集 α) (a : α)
  结论: s.erase a ⊂ insert a s
  证明: ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, by grw [← subset_insert]⟩

Depends on / 依赖: mem_insert_self, ssubset_iff_exists_subset_erase, subset_insert
-/
theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, by grw [← subset_insert]⟩

/--
theorem `erase_cons` / 定理 `erase_cons`

English:
theorem erase_cons
  given: {s : Finset α} {a : α} (h : a ∉ s)
  statement: (s.cons a h).erase a = s
  proof: by grind

中文:
定理 erase_cons
  条件: {s : 有限集 α} {a : α} (h : a ∉ s)
  结论: (s.cons a h).erase a = s
  证明: by grind
-/
theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by grind

/--
theorem `subset_insert_iff` / 定理 `subset_insert_iff`

English:
theorem subset_insert_iff
  given: {a : α} {s t : Finset α}
  statement: s subseteq insert a t ↔ s.erase a subseteq t
  proof: by grind

中文:
定理 subset_insert_iff
  条件: {a : α} {s t : 有限集 α}
  结论: s subseteq insert a t ↔ s.erase a subseteq t
  证明: by grind
-/
theorem subset_insert_iff {a : α} {s t : Finset α} : s subseteq insert a t ↔ s.erase a subseteq t := by grind

/--
theorem `erase_insert_subset` / 定理 `erase_insert_subset`

English:
theorem erase_insert_subset
  given: (a : α) (s : Finset α)
  statement: (insert a s).erase a subseteq s
  proof: subset_insert_iff.1 Subset.rfl

中文:
定理 erase_insert_subset
  条件: (a : α) (s : 有限集 α)
  结论: (insert a s).erase a subseteq s
  证明: subset_insert_iff.1 Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, subset_insert_iff
-/
theorem erase_insert_subset (a : α) (s : Finset α) : (insert a s).erase a subseteq s :=
  subset_insert_iff.1 Subset.rfl

/--
theorem `insert_erase_subset` / 定理 `insert_erase_subset`

English:
theorem insert_erase_subset
  given: (a : α) (s : Finset α)
  statement: s subseteq insert a (s.erase a)
  proof: subset_insert_iff.2 Subset.rfl

中文:
定理 insert_erase_subset
  条件: (a : α) (s : 有限集 α)
  结论: s subseteq insert a (s.erase a)
  证明: subset_insert_iff.2 Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, subset_insert_iff
-/
theorem insert_erase_subset (a : α) (s : Finset α) : s subseteq insert a (s.erase a) :=
  subset_insert_iff.2 Subset.rfl

/--
theorem `subset_insert_iff_of_notMem` / 定理 `subset_insert_iff_of_notMem`

English:
theorem subset_insert_iff_of_notMem
  given: (h : a ∉ s)
  statement: s subseteq insert a t ↔ s subseteq t
  proof: by
  rw [subset_insert_iff]; rw [erase_eq_of_notMem h]

中文:
定理 subset_insert_iff_of_notMem
  条件: (h : a ∉ s)
  结论: s subseteq insert a t ↔ s subseteq t
  证明: by
  rw [subset_insert_iff]; rw [erase_eq_of_notMem h]

Depends on / 依赖: erase_eq_of_notMem, subset_insert_iff
-/
theorem subset_insert_iff_of_notMem (h : a ∉ s) : s subseteq insert a t ↔ s subseteq t := by
  rw [subset_insert_iff]; rw [erase_eq_of_notMem h]

/--
theorem `erase_subset_iff_of_mem` / 定理 `erase_subset_iff_of_mem`

English:
theorem erase_subset_iff_of_mem
  given: (h : a in t)
  statement: s.erase a subseteq t ↔ s subseteq t
  proof: by
  rw [← subset_insert_iff]; rw [insert_eq_of_mem h]

中文:
定理 erase_subset_iff_of_mem
  条件: (h : a in t)
  结论: s.erase a subseteq t ↔ s subseteq t
  证明: by
  rw [← subset_insert_iff]; rw [insert_eq_of_mem h]

Depends on / 依赖: insert_eq_of_mem, subset_insert_iff
-/
theorem erase_subset_iff_of_mem (h : a in t) : s.erase a subseteq t ↔ s subseteq t := by
  rw [← subset_insert_iff]; rw [insert_eq_of_mem h]

/--
theorem `erase_injOn'` / 定理 `erase_injOn'`

English:
theorem erase_injOn'
  given: (a : α)
  statement: { s : Finset α | a in s }.InjOn fun s => s.erase a
  proof: fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

中文:
定理 erase_injOn'
  条件: (a : α)
  结论: { s : 有限集 α | a in s }.单射限制 fun s => s.erase a
  证明: fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

Depends on / 依赖: insert_erase, s.erase
-/
theorem erase_injOn' (a : α) : { s : Finset α | a in s }.InjOn fun s => s.erase a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]

end Erase

/--
lemma `Nontrivial.exists_cons_eq` / 引理 `Nontrivial.exists_cons_eq`

English:
lemma Nontrivial.exists_cons_eq
  given: {s : Finset α} (hs : s.Nontrivial)
  proof: by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b in s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;> simp [insert_erase ha, *]

中文:
引理 非平凡.存在_cons_eq
  条件: {s : 有限集 α} (hs : s.非平凡)
  证明: by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b in s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;> simp [insert_erase ha, *]

Depends on / 依赖: classical, hab.symm, insert_erase, mem_erase, s.erase
-/
lemma Nontrivial.exists_cons_eq {s : Finset α} (hs : s.Nontrivial) :
    exists t a ha b hb hab, (cons b t hb).cons a (mem_cons.not.2 <| not_or_intro hab ha) = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b in s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;> simp [insert_erase ha, *]

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/--
lemma `erase_sdiff_erase` / 引理 `erase_sdiff_erase`

English:
lemma erase_sdiff_erase
  given: (hab : a != b) (hb : b in s)
  statement: s.erase a \ s.erase b = {b}
  proof: by
  ext; aesop

中文:
引理 erase_sdiff_erase
  条件: (hab : a != b) (hb : b in s)
  结论: s.erase a \ s.erase b = {b}
  证明: by
  ext; aesop
-/
lemma erase_sdiff_erase (hab : a != b) (hb : b in s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

-- TODO: Do we want to delete this lemma and `Finset.disjUnion_singleton`,
-- or instead add `Finset.union_singleton`/`Finset.singleton_union`?
/--
theorem `sdiff_singleton_eq_erase` / 定理 `sdiff_singleton_eq_erase`

English:
theorem sdiff_singleton_eq_erase
  given: (a : α) (s : Finset α)
  statement: s \ {a} = s.erase a
  proof: by grind

中文:
定理 sdiff_singleton_eq_erase
  条件: (a : α) (s : 有限集 α)
  结论: s \ {a} = s.erase a
  证明: by grind
-/
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ {a} = s.erase a := by grind

-- This lemma matches `Finset.insert_eq` in functionality.
/--
theorem `erase_eq` / 定理 `erase_eq`

English:
theorem erase_eq
  given: (s : Finset α) (a : α)
  statement: s.erase a = s \ {a}
  proof: (sdiff_singleton_eq_erase _ _).symm

中文:
定理 erase_eq
  条件: (s : 有限集 α) (a : α)
  结论: s.erase a = s \ {a}
  证明: (sdiff_singleton_eq_erase _ _).symm

Depends on / 依赖: sdiff_singleton_eq_erase
-/
theorem erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm

/--
theorem `disjoint_erase_comm` / 定理 `disjoint_erase_comm`

English:
theorem disjoint_erase_comm
  statement: Disjoint (s.erase a) t ↔ Disjoint s (t.erase a)
  proof: by
  simp_rw [erase_eq, disjoint_sdiff_comm]

中文:
定理 disjoint_erase_comm
  结论: Disjoint (s.erase a) t ↔ Disjoint s (t.erase a)
  证明: by
  simp_rw [erase_eq, disjoint_sdiff_comm]

Depends on / 依赖: disjoint_sdiff_comm, erase_eq, simp_rw
-/
theorem disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]

/--
lemma `disjoint_insert_erase` / 引理 `disjoint_insert_erase`

English:
lemma disjoint_insert_erase
  given: (ha : a ∉ t)
  statement: Disjoint (s.erase a) (insert a t) ↔ Disjoint s t
  proof: by
  rw [disjoint_erase_comm]; rw [erase_insert ha]

中文:
引理 disjoint_insert_erase
  条件: (ha : a ∉ t)
  结论: Disjoint (s.erase a) (insert a t) ↔ Disjoint s t
  证明: by
  rw [disjoint_erase_comm]; rw [erase_insert ha]

Depends on / 依赖: disjoint_erase_comm, erase_insert
-/
lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm]; rw [erase_insert ha]

/--
lemma `disjoint_erase_insert` / 引理 `disjoint_erase_insert`

English:
lemma disjoint_erase_insert
  given: (ha : a ∉ s)
  statement: Disjoint (insert a s) (t.erase a) ↔ Disjoint s t
  proof: by
  rw [← disjoint_erase_comm]; rw [erase_insert ha]

中文:
引理 disjoint_erase_insert
  条件: (ha : a ∉ s)
  结论: Disjoint (insert a s) (t.erase a) ↔ Disjoint s t
  证明: by
  rw [← disjoint_erase_comm]; rw [erase_insert ha]

Depends on / 依赖: disjoint_erase_comm, erase_insert
-/
lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm]; rw [erase_insert ha]

/--
theorem `disjoint_of_erase_left` / 定理 `disjoint_of_erase_left`

English:
theorem disjoint_of_erase_left
  given: (ha : a ∉ t) (hst : Disjoint (s.erase a) t)
  statement: Disjoint s t
  proof: by
  rw [← erase_insert ha]; rw [← disjoint_erase_comm]; rw [disjoint_insert_right]
  exact ⟨notMem_erase _ _, hst⟩

中文:
定理 disjoint_of_erase_left
  条件: (ha : a ∉ t) (hst : Disjoint (s.erase a) t)
  结论: Disjoint s t
  证明: by
  rw [← erase_insert ha]; rw [← disjoint_erase_comm]; rw [disjoint_insert_right]
  exact ⟨notMem_erase _ _, hst⟩

Depends on / 依赖: disjoint_erase_comm, disjoint_insert_right, erase_insert, notMem_erase
-/
theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjoint s t := by
  rw [← erase_insert ha]; rw [← disjoint_erase_comm]; rw [disjoint_insert_right]
  exact ⟨notMem_erase _ _, hst⟩

/--
theorem `disjoint_of_erase_right` / 定理 `disjoint_of_erase_right`

English:
theorem disjoint_of_erase_right
  given: (ha : a ∉ s) (hst : Disjoint s (t.erase a))
  statement: Disjoint s t
  proof: by
  rw [← erase_insert ha]; rw [disjoint_erase_comm]; rw [disjoint_insert_left]
  exact ⟨notMem_erase _ _, hst⟩

中文:
定理 disjoint_of_erase_right
  条件: (ha : a ∉ s) (hst : Disjoint s (t.erase a))
  结论: Disjoint s t
  证明: by
  rw [← erase_insert ha]; rw [disjoint_erase_comm]; rw [disjoint_insert_left]
  exact ⟨notMem_erase _ _, hst⟩

Depends on / 依赖: disjoint_erase_comm, disjoint_insert_left, erase_insert, notMem_erase
-/
theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disjoint s t := by
  rw [← erase_insert ha]; rw [disjoint_erase_comm]; rw [disjoint_insert_left]
  exact ⟨notMem_erase _ _, hst⟩

/--
theorem `inter_erase` / 定理 `inter_erase`

English:
theorem inter_erase
  given: (a : α) (s t : Finset α)
  statement: s inter t.erase a = (s inter t).erase a
  proof: by grind

@[simp]

中文:
定理 inter_erase
  条件: (a : α) (s t : 有限集 α)
  结论: s inter t.erase a = (s inter t).erase a
  证明: by grind

@[simp]
-/
theorem inter_erase (a : α) (s t : Finset α) : s inter t.erase a = (s inter t).erase a := by grind

@[simp]
/--
theorem `erase_inter` / 定理 `erase_inter`

English:
theorem erase_inter
  given: (a : α) (s t : Finset α)
  statement: s.erase a inter t = (s inter t).erase a
  proof: by grind

中文:
定理 erase_inter
  条件: (a : α) (s t : 有限集 α)
  结论: s.erase a inter t = (s inter t).erase a
  证明: by grind
-/
theorem erase_inter (a : α) (s t : Finset α) : s.erase a inter t = (s inter t).erase a := by grind

/--
theorem `erase_sdiff_comm` / 定理 `erase_sdiff_comm`

English:
theorem erase_sdiff_comm
  given: (s t : Finset α) (a : α)
  statement: s.erase a \ t = (s \ t).erase a
  proof: by grind

中文:
定理 erase_sdiff_comm
  条件: (s t : 有限集 α) (a : α)
  结论: s.erase a \ t = (s \ t).erase a
  证明: by grind
-/
theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by grind

/--
theorem `erase_inter_comm` / 定理 `erase_inter_comm`

English:
theorem erase_inter_comm
  given: (s t : Finset α) (a : α)
  statement: s.erase a inter t = s inter t.erase a
  proof: by grind

中文:
定理 erase_inter_comm
  条件: (s t : 有限集 α) (a : α)
  结论: s.erase a inter t = s inter t.erase a
  证明: by grind
-/
theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a inter t = s inter t.erase a := by grind

/--
theorem `erase_union_distrib` / 定理 `erase_union_distrib`

English:
theorem erase_union_distrib
  given: (s t : Finset α) (a : α)
  statement: (s union t).erase a = s.erase a union t.erase a
  proof: by
  grind

中文:
定理 erase_union_distrib
  条件: (s t : 有限集 α) (a : α)
  结论: (s union t).erase a = s.erase a union t.erase a
  证明: by
  grind
-/
theorem erase_union_distrib (s t : Finset α) (a : α) : (s union t).erase a = s.erase a union t.erase a := by
  grind

/--
theorem `insert_inter_distrib` / 定理 `insert_inter_distrib`

English:
theorem insert_inter_distrib
  given: (s t : Finset α) (a : α)
  proof: by grind

中文:
定理 insert_inter_distrib
  条件: (s t : 有限集 α) (a : α)
  证明: by grind
-/
theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s inter t) = insert a s inter insert a t := by grind

/--
theorem `erase_sdiff_distrib` / 定理 `erase_sdiff_distrib`

English:
theorem erase_sdiff_distrib
  given: (s t : Finset α) (a : α)
  statement: (s \ t).erase a = s.erase a \ t.erase a
  proof: by
  grind

中文:
定理 erase_sdiff_distrib
  条件: (s t : 有限集 α) (a : α)
  结论: (s \ t).erase a = s.erase a \ t.erase a
  证明: by
  grind
-/
theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a := by
  grind

/--
theorem `erase_union_of_mem` / 定理 `erase_union_of_mem`

English:
theorem erase_union_of_mem
  given: (ha : a in t) (s : Finset α)
  statement: s.erase a union t = s union t
  proof: by
  grind

中文:
定理 erase_union_of_mem
  条件: (ha : a in t) (s : 有限集 α)
  结论: s.erase a union t = s union t
  证明: by
  grind
-/
theorem erase_union_of_mem (ha : a in t) (s : Finset α) : s.erase a union t = s union t := by
  grind

/--
theorem `union_erase_of_mem` / 定理 `union_erase_of_mem`

English:
theorem union_erase_of_mem
  given: (ha : a in s) (t : Finset α)
  statement: s union t.erase a = s union t
  proof: by
  grind

中文:
定理 union_erase_of_mem
  条件: (ha : a in s) (t : 有限集 α)
  结论: s union t.erase a = s union t
  证明: by
  grind
-/
theorem union_erase_of_mem (ha : a in s) (t : Finset α) : s union t.erase a = s union t := by
  grind

/--
theorem `sdiff_union_erase_cancel` / 定理 `sdiff_union_erase_cancel`

English:
theorem sdiff_union_erase_cancel
  given: (hts : t subseteq s) (ha : a in t)
  statement: s \ t union t.erase a = s.erase a
  proof: by
  grind

中文:
定理 sdiff_union_erase_cancel
  条件: (hts : t subseteq s) (ha : a in t)
  结论: s \ t union t.erase a = s.erase a
  证明: by
  grind
-/
theorem sdiff_union_erase_cancel (hts : t subseteq s) (ha : a in t) : s \ t union t.erase a = s.erase a := by
  grind

/--
theorem `sdiff_insert` / 定理 `sdiff_insert`

English:
theorem sdiff_insert
  given: (s t : Finset α) (x : α)
  statement: s \ insert x t = (s \ t).erase x
  proof: by
  grind

中文:
定理 sdiff_insert
  条件: (s t : 有限集 α) (x : α)
  结论: s \ insert x t = (s \ t).erase x
  证明: by
  grind
-/
theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  grind

/--
theorem `sdiff_insert_insert_of_mem_of_notMem` / 定理 `sdiff_insert_insert_of_mem_of_notMem`

English:
theorem sdiff_insert_insert_of_mem_of_notMem
  given: {s t : Finset α} {x : α} (hxs : x in s) (hxt : x ∉ t)
  proof: by
  grind

中文:
定理 sdiff_insert_insert_of_mem_of_notMem
  条件: {s t : 有限集 α} {x : α} (hxs : x in s) (hxt : x ∉ t)
  证明: by
  grind
-/
theorem sdiff_insert_insert_of_mem_of_notMem {s t : Finset α} {x : α} (hxs : x in s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  grind

/--
theorem `sdiff_erase` / 定理 `sdiff_erase`

English:
theorem sdiff_erase
  given: (h : a in s)
  statement: s \ t.erase a = insert a (s \ t)
  proof: by
  grind

中文:
定理 sdiff_erase
  条件: (h : a in s)
  结论: s \ t.erase a = insert a (s \ t)
  证明: by
  grind
-/
theorem sdiff_erase (h : a in s) : s \ t.erase a = insert a (s \ t) := by
  grind

/--
theorem `sdiff_erase_self` / 定理 `sdiff_erase_self`

English:
theorem sdiff_erase_self
  given: (ha : a in s)
  statement: s \ s.erase a = {a}
  proof: by
  grind

中文:
定理 sdiff_erase_self
  条件: (ha : a in s)
  结论: s \ s.erase a = {a}
  证明: by
  grind
-/
theorem sdiff_erase_self (ha : a in s) : s \ s.erase a = {a} := by
  grind

/--
theorem `erase_eq_empty_iff` / 定理 `erase_eq_empty_iff`

English:
theorem erase_eq_empty_iff
  given: (s : Finset α) (a : α)
  statement: s.erase a = ∅ ↔ s = ∅ ∨ s = {a}
  proof: by
  rw [← sdiff_singleton_eq_erase]; rw [sdiff_eq_empty_iff_subset]; rw [subset_singleton_iff]

中文:
定理 erase_eq_empty_iff
  条件: (s : 有限集 α) (a : α)
  结论: s.erase a = ∅ ↔ s = ∅ ∨ s = {a}
  证明: by
  rw [← sdiff_singleton_eq_erase]; rw [sdiff_eq_empty_iff_subset]; rw [subset_singleton_iff]

Depends on / 依赖: sdiff_eq_empty_iff_subset, sdiff_singleton_eq_erase, subset_singleton_iff
-/
theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase]; rw [sdiff_eq_empty_iff_subset]; rw [subset_singleton_iff]

--TODO@Yaël: Kill lemmas duplicate with `BooleanAlgebra`
/--
theorem `sdiff_disjoint` / 定理 `sdiff_disjoint`

English:
theorem sdiff_disjoint
  statement: Disjoint (t \ s) s
  proof: disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2

中文:
定理 sdiff_disjoint
  结论: Disjoint (t \ s) s
  证明: disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2

Depends on / 依赖: disjoint_left, mem_sdiff
-/
theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2

/--
theorem `disjoint_sdiff` / 定理 `disjoint_sdiff`

English:
theorem disjoint_sdiff
  statement: Disjoint s (t \ s)
  proof: sdiff_disjoint.symm

中文:
定理 disjoint_sdiff
  结论: Disjoint s (t \ s)
  证明: sdiff_disjoint.symm

Depends on / 依赖: sdiff_disjoint, sdiff_disjoint.symm
-/
theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm

/--
theorem `disjoint_sdiff_inter` / 定理 `disjoint_sdiff_inter`

English:
theorem disjoint_sdiff_inter
  given: (s t : Finset α)
  statement: Disjoint (s \ t) (s inter t)
  proof: disjoint_of_subset_right inter_subset_right sdiff_disjoint

中文:
定理 disjoint_sdiff_inter
  条件: (s t : 有限集 α)
  结论: Disjoint (s \ t) (s inter t)
  证明: disjoint_of_subset_right inter_subset_right sdiff_disjoint

Depends on / 依赖: disjoint_of_subset_right, inter_subset_right, sdiff_disjoint
-/
theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s inter t) :=
  disjoint_of_subset_right inter_subset_right sdiff_disjoint

end Sdiff

/-! ### attach -/

@[simp]
/--
theorem `attach_empty` / 定理 `attach_empty`

English:
theorem attach_empty
  statement: (∅ : Finset α).attach = ∅
  proof: rfl

@[simp]

中文:
定理 attach_empty
  结论: (∅ : 有限集 α).attach = ∅
  证明: rfl

@[simp]
-/
theorem attach_empty : (∅ : Finset α).attach = ∅ :=
  rfl

@[simp]
/--
theorem `attach_nonempty_iff` / 定理 `attach_nonempty_iff`

English:
theorem attach_nonempty_iff
  given: {s : Finset α}
  statement: s.attach.Nonempty ↔ s.Nonempty
  proof: by
  simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]

中文:
定理 attach_nonempty_iff
  条件: {s : 有限集 α}
  结论: s.attach.非空 ↔ s.非空
  证明: by
  simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty
-/
theorem attach_nonempty_iff {s : Finset α} : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]
/--
theorem `attach_eq_empty_iff` / 定理 `attach_eq_empty_iff`

English:
theorem attach_eq_empty_iff
  given: {s : Finset α}
  statement: s.attach = ∅ ↔ s = ∅
  proof: by
  simp [eq_empty_iff_forall_notMem]

中文:
定理 attach_eq_empty_iff
  条件: {s : 有限集 α}
  结论: s.attach = ∅ ↔ s = ∅
  证明: by
  simp [eq_empty_iff_forall_notMem]

Depends on / 依赖: eq_empty_iff_forall_notMem
-/
theorem attach_eq_empty_iff {s : Finset α} : s.attach = ∅ ↔ s = ∅ := by
  simp [eq_empty_iff_forall_notMem]

/-! ### filter -/

section Filter
variable (p q : α -> Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

/--
theorem `filter_singleton` / 定理 `filter_singleton`

English:
theorem filter_singleton
  given: (a : α)
  statement: filter p {a} = if p a then {a} else ∅
  proof: by grind

中文:
定理 filter_singleton
  条件: (a : α)
  结论: filter p {a} = if p a then {a} else ∅
  证明: by grind
-/
theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅ := by grind

/--
theorem `filter_cons_of_pos` / 定理 `filter_cons_of_pos`

English:
theorem filter_cons_of_pos
  given: (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a)
  proof: eq_of_veq s.val.filter_cons_of_pos hp

中文:
定理 filter_cons_of_pos
  条件: (a : α) (s : 有限集 α) (ha : a ∉ s) (hp : p a)
  证明: eq_of_veq s.val.filter_cons_of_pos hp

Depends on / 依赖: eq_of_veq, filter_cons_of_pos, s.val.filter_cons_of_pos
-/
theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    (s.cons a ha).filter p = (s.filter p).cons a ((mem_of_mem_filter _).mt ha) :=
eq_of_veq s.val.filter_cons_of_pos hp

/--
theorem `filter_cons_of_neg` / 定理 `filter_cons_of_neg`

English:
theorem filter_cons_of_neg
  given: (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a)
  proof: eq_of_veq s.val.filter_cons_of_neg hp

中文:
定理 filter_cons_of_neg
  条件: (a : α) (s : 有限集 α) (ha : a ∉ s) (hp : ¬p a)
  证明: eq_of_veq s.val.filter_cons_of_neg hp

Depends on / 依赖: eq_of_veq, filter_cons_of_neg, s.val.filter_cons_of_neg
-/
theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    (s.cons a ha).filter p = s.filter p :=
eq_of_veq s.val.filter_cons_of_neg hp

/--
theorem `disjoint_filter` / 定理 `disjoint_filter`

English:
theorem disjoint_filter
  given: {s : Finset α} {p q : α -> Prop} [DecidablePred p] [DecidablePred q]
  proof: by
  constructor <;> simp +contextual [disjoint_left]

中文:
定理 disjoint_filter
  条件: {s : 有限集 α} {p q : α -> 命题} [DecidablePred p] [DecidablePred q]
  证明: by
  constructor <;> simp +contextual [disjoint_left]

Depends on / 依赖: contextual, disjoint_left
-/
theorem disjoint_filter {s : Finset α} {p q : α -> Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filter p) (s.filter q) ↔ forall x in s, p x -> ¬q x := by
  constructor <;> simp +contextual [disjoint_left]

/--
theorem `disjoint_filter_filter'` / 定理 `disjoint_filter_filter'`

English:
theorem disjoint_filter_filter'
  statement: (s t : Finset α)
  proof: by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a

中文:
定理 disjoint_filter_filter'
  结论: (s t : 有限集 α)
  证明: by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a

Depends on / 依赖: Pi.disjoint_iff, disjoint_iff, disjoint_left, mem_filter, simp_rw
-/
theorem disjoint_filter_filter' (s t : Finset α)
    {p q : α -> Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) :
    Disjoint (s.filter p) (t.filter q) := by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a

/--
theorem `disjoint_filter_filter_not` / 定理 `disjoint_filter_filter_not`

English:
theorem disjoint_filter_filter_not
  statement: (s t : Finset α) (p : α -> Prop)
  proof: s.disjoint_filter_filter' t disjoint_compl_right

中文:
定理 disjoint_filter_filter_not
  结论: (s t : 有限集 α) (p : α -> 命题)
  证明: s.disjoint_filter_filter' t disjoint_compl_right

Depends on / 依赖: disjoint_compl_right, disjoint_filter_filter, s.disjoint_filter_filter
-/
theorem disjoint_filter_filter_not (s t : Finset α) (p : α -> Prop)
    [DecidablePred p] [forall x, Decidable (¬p x)] :
    Disjoint (s.filter p) (t.filter fun a => ¬p a) :=
  s.disjoint_filter_filter' t disjoint_compl_right

/--
theorem `filter_disjUnion` / 定理 `filter_disjUnion`

English:
theorem filter_disjUnion
  given: (s : Finset α) (t : Finset α) (h : Disjoint s t)
  proof: eq_of_veq Multiset.filter_add _ _ _

中文:
定理 filter_disjUnion
  条件: (s : 有限集 α) (t : 有限集 α) (h : Disjoint s t)
  证明: eq_of_veq Multiset.filter_add _ _ _

Depends on / 依赖: Multiset, Multiset.filter_add, eq_of_veq, filter_add
-/
theorem filter_disjUnion (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    (s.disjUnion t h).filter p = (s.filter p).disjUnion (t.filter p) (disjoint_filter_filter h) :=
eq_of_veq Multiset.filter_add _ _ _

/--
theorem `filter_cons` / 定理 `filter_cons`

English:
theorem filter_cons
  given: {a : α} (s : Finset α) (ha : a ∉ s)
  proof: by grind

@[simp]

中文:
定理 filter_cons
  条件: {a : α} (s : 有限集 α) (ha : a ∉ s)
  证明: by grind

@[simp]
-/
theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).filter p =
      if p a then (s.filter p).cons a ((mem_of_mem_filter _).mt ha) else s.filter p := by grind

@[simp]
/--
theorem `disjoint_disjUnion_left` / 定理 `disjoint_disjUnion_left`

English:
theorem disjoint_disjUnion_left
  given: {s t u : Finset α} (h : Disjoint s t)
  proof: by
  simp only [disjoint_left, mem_disjUnion, or_imp, forall_and]

@[simp]

中文:
定理 disjoint_disjUnion_left
  条件: {s t u : 有限集 α} (h : Disjoint s t)
  证明: by
  simp only [disjoint_left, mem_disjUnion, or_imp, forall_and]

@[simp]

Depends on / 依赖: disjoint_left, forall_and, mem_disjUnion, or_imp
-/
theorem disjoint_disjUnion_left {s t u : Finset α} (h : Disjoint s t) :
    Disjoint (s.disjUnion t h) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_disjUnion, or_imp, forall_and]

@[simp]
/--
theorem `disjoint_disjUnion_right` / 定理 `disjoint_disjUnion_right`

English:
theorem disjoint_disjUnion_right
  given: {s t u : Finset α} (h : Disjoint t u)
  proof: by
  simp only [disjoint_right, mem_disjUnion, or_imp, forall_and]

中文:
定理 disjoint_disjUnion_right
  条件: {s t u : 有限集 α} (h : Disjoint t u)
  证明: by
  simp only [disjoint_right, mem_disjUnion, or_imp, forall_and]

Depends on / 依赖: disjoint_right, forall_and, mem_disjUnion, or_imp
-/
theorem disjoint_disjUnion_right {s t u : Finset α} (h : Disjoint t u) :
    Disjoint s (t.disjUnion u h) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_disjUnion, or_imp, forall_and]

section
variable [DecidableEq α]

/--
theorem `filter_union` / 定理 `filter_union`

English:
theorem filter_union
  given: (s₁ s₂ : Finset α)
  statement: (s₁ union s₂).filter p = s₁.filter p union s₂.filter p
  proof: by
  grind

中文:
定理 filter_union
  条件: (s₁ s₂ : 有限集 α)
  结论: (s₁ union s₂).filter p = s₁.filter p union s₂.filter p
  证明: by
  grind
-/
theorem filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).filter p = s₁.filter p union s₂.filter p := by
  grind

/--
theorem `filter_union_right` / 定理 `filter_union_right`

English:
theorem filter_union_right
  given: (s : Finset α)
  proof: by grind

中文:
定理 filter_union_right
  条件: (s : 有限集 α)
  证明: by grind
-/
theorem filter_union_right (s : Finset α) :
    s.filter p union s.filter q = s.filter fun x => p x ∨ q x := by grind

/--
theorem `filter_mem_eq_inter` / 定理 `filter_mem_eq_inter`

English:
theorem filter_mem_eq_inter
  given: {s t : Finset α} [forall i, Decidable (i in t)]
  proof: by grind

中文:
定理 filter_mem_eq_inter
  条件: {s t : 有限集 α} [对任意 i, 可判定 (i in t)]
  证明: by grind
-/
theorem filter_mem_eq_inter {s t : Finset α} [forall i, Decidable (i in t)] :
    (s.filter fun i => i in t) = s inter t := by grind

/--
theorem `filter_notMem_eq_sdiff` / 定理 `filter_notMem_eq_sdiff`

English:
theorem filter_notMem_eq_sdiff
  given: {s t : Finset α} [forall i, Decidable (i ∉ t)]
  proof: by grind

中文:
定理 filter_notMem_eq_sdiff
  条件: {s t : 有限集 α} [对任意 i, 可判定 (i ∉ t)]
  证明: by grind
-/
theorem filter_notMem_eq_sdiff {s t : Finset α} [forall i, Decidable (i ∉ t)] :
    (s.filter fun i => i ∉ t) = s \ t := by grind

/--
theorem `filter_inter_distrib` / 定理 `filter_inter_distrib`

English:
theorem filter_inter_distrib
  given: (s t : Finset α)
  statement: (s inter t).filter p = s.filter p inter t.filter p
  proof: by
  grind

中文:
定理 filter_inter_distrib
  条件: (s t : 有限集 α)
  结论: (s inter t).filter p = s.filter p inter t.filter p
  证明: by
  grind
-/
theorem filter_inter_distrib (s t : Finset α) : (s inter t).filter p = s.filter p inter t.filter p := by
  grind

/--
theorem `filter_inter` / 定理 `filter_inter`

English:
theorem filter_inter
  given: (s t : Finset α)
  statement: s.filter p inter t = (s inter t).filter p
  proof: by grind

中文:
定理 filter_inter
  条件: (s t : 有限集 α)
  结论: s.filter p inter t = (s inter t).filter p
  证明: by grind
-/
theorem filter_inter (s t : Finset α) : s.filter p inter t = (s inter t).filter p := by grind

/--
theorem `inter_filter` / 定理 `inter_filter`

English:
theorem inter_filter
  given: (s t : Finset α)
  statement: s inter t.filter p = (s inter t).filter p
  proof: by grind

中文:
定理 inter_filter
  条件: (s t : 有限集 α)
  结论: s inter t.filter p = (s inter t).filter p
  证明: by grind
-/
theorem inter_filter (s t : Finset α) : s inter t.filter p = (s inter t).filter p := by grind

/--
theorem `filter_insert` / 定理 `filter_insert`

English:
theorem filter_insert
  given: (a : α) (s : Finset α)
  proof: by grind

中文:
定理 filter_insert
  条件: (a : α) (s : 有限集 α)
  证明: by grind
-/
theorem filter_insert (a : α) (s : Finset α) :
    (insert a s).filter p = if p a then insert a (s.filter p) else s.filter p := by grind

/--
theorem `filter_erase` / 定理 `filter_erase`

English:
theorem filter_erase
  given: (a : α) (s : Finset α)
  statement: (s.erase a).filter p = (s.filter p).erase a
  proof: by
  grind

中文:
定理 filter_erase
  条件: (a : α) (s : 有限集 α)
  结论: (s.erase a).filter p = (s.filter p).erase a
  证明: by
  grind
-/
theorem filter_erase (a : α) (s : Finset α) : (s.erase a).filter p = (s.filter p).erase a := by
  grind

/--
theorem `filter_or` / 定理 `filter_or`

English:
theorem filter_or
  given: (s : Finset α)
  statement: (s.filter fun a => p a ∨ q a) = s.filter p union s.filter q
  proof: by
  grind

中文:
定理 filter_or
  条件: (s : 有限集 α)
  结论: (s.filter fun a => p a ∨ q a) = s.filter p union s.filter q
  证明: by
  grind
-/
theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p union s.filter q := by
  grind

/--
theorem `filter_and` / 定理 `filter_and`

English:
theorem filter_and
  given: (s : Finset α)
  statement: (s.filter fun a => p a ∧ q a) = s.filter p inter s.filter q
  proof: by
  grind

中文:
定理 filter_and
  条件: (s : 有限集 α)
  结论: (s.filter fun a => p a ∧ q a) = s.filter p inter s.filter q
  证明: by
  grind
-/
theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p inter s.filter q := by
  grind

/--
theorem `filter_not` / 定理 `filter_not`

English:
theorem filter_not
  given: (s : Finset α)
  statement: (s.filter fun a => ¬p a) = s \ s.filter p
  proof: by
  grind

中文:
定理 filter_not
  条件: (s : 有限集 α)
  结论: (s.filter fun a => ¬p a) = s \ s.filter p
  证明: by
  grind
-/
theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p := by
  grind

/--
lemma `filter_and_not` / 引理 `filter_and_not`

English:
lemma filter_and_not
  given: (s : Finset α) (p q : α -> Prop) [DecidablePred p] [DecidablePred q]
  proof: by grind

中文:
引理 filter_and_not
  条件: (s : 有限集 α) (p q : α -> 命题) [DecidablePred p] [DecidablePred q]
  证明: by grind
-/
lemma filter_and_not (s : Finset α) (p q : α -> Prop) [DecidablePred p] [DecidablePred q] :
    s.filter (fun a => p a ∧ ¬ q a) = s.filter p \ s.filter q := by grind

/--
theorem `sdiff_eq_filter` / 定理 `sdiff_eq_filter`

English:
theorem sdiff_eq_filter
  given: (s₁ s₂ : Finset α)
  statement: s₁ \ s₂ = s₁.filter (· ∉ s₂)
  proof: by grind

中文:
定理 sdiff_eq_filter
  条件: (s₁ s₂ : 有限集 α)
  结论: s₁ \ s₂ = s₁.filter (· ∉ s₂)
  证明: by grind
-/
theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁.filter (· ∉ s₂) := by grind

/--
theorem `subset_union_elim` / 定理 `subset_union_elim`

English:
theorem subset_union_elim
  given: {s : Finset α} {t₁ t₂ : Set α} (h : ↑s subseteq t₁ union t₂)
  proof: by
  classical
    refine ⟨s.filter (· in t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · grind
    · grind
    · intro x
      simp only [coe_filter, Set.mem_ofPred_eq, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

中文:
定理 subset_union_elim
  条件: {s : 有限集 α} {t₁ t₂ : 集合 α} (h : ↑s subseteq t₁ union t₂)
  证明: by
  classical
    refine ⟨s.filter (· in t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · grind
    · grind
    · intro x
      simp only [coe_filter, Set.mem_ofPred_eq, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

Depends on / 依赖: Or.resolve_left, Set.mem_ofPred_eq, and_imp, classical, coe_filter, filter, mem_ofPred_eq, resolve_left, s.filter
-/
theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s subseteq t₁ union t₂) :
    exists s₁ s₂ : Finset α, s₁ union s₂ = s ∧ ↑s₁ subseteq t₁ ∧ ↑s₂ subseteq t₂ \ t₁ := by
  classical
    refine ⟨s.filter (· in t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · grind
    · grind
    · intro x
      simp only [coe_filter, Set.mem_ofPred_eq, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

-- This is not a good simp lemma, as it would prevent `Finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter (Eq b)`.
/--
theorem `filter_eq` / 定理 `filter_eq`

English:
theorem filter_eq
  given: [DecidableEq β] (s : Finset β) (b : β)
  proof: by grind

中文:
定理 filter_eq
  条件: [DecidableEq β] (s : 有限集 β) (b : β)
  证明: by grind
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) :
    s.filter (Eq b) = ite (b in s) {b} ∅ := by grind

/--
theorem `filter_eq'` / 定理 `filter_eq'`

English:
theorem filter_eq'
  given: [DecidableEq β] (s : Finset β) (b : β)
  proof: by grind

中文:
定理 filter_eq'
  条件: [DecidableEq β] (s : 有限集 β) (b : β)
  证明: by grind
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b in s) {b} ∅ := by grind

/--
theorem `filter_ne` / 定理 `filter_ne`

English:
theorem filter_ne
  given: [DecidableEq β] (s : Finset β) (b : β)
  proof: by grind

中文:
定理 filter_ne
  条件: [DecidableEq β] (s : 有限集 β) (b : β)
  证明: by grind
-/
theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b != a) = s.erase b := by grind

/--
theorem `filter_ne'` / 定理 `filter_ne'`

English:
theorem filter_ne'
  given: [DecidableEq β] (s : Finset β) (b : β)
  statement: (s.filter fun a => a != b) = s.erase b
  proof: (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]).trans (s.filter_ne b)

中文:
定理 filter_ne'
  条件: [DecidableEq β] (s : 有限集 β) (b : β)
  结论: (s.filter fun a => a != b) = s.erase b
  证明: (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]).trans (s.filter_ne b)

Depends on / 依赖: filter_congr, filter_ne, ne_comm, s.filter_ne, simp_rw
-/
theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a != b) = s.erase b :=
  (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]).trans (s.filter_ne b)

/--
theorem `filter_union_filter_of_codisjoint` / 定理 `filter_union_filter_of_codisjoint`

English:
theorem filter_union_filter_of_codisjoint
  given: (s : Finset α) (h : Codisjoint p q)
  proof: (filter_or _ _ _).symm.trans filter_true_of_mem fun x _ => h.top_le x trivial

中文:
定理 filter_union_filter_of_codisjoint
  条件: (s : 有限集 α) (h : Codisjoint p q)
  证明: (filter_or _ _ _).symm.trans filter_true_of_mem fun x _ => h.top_le x trivial

Depends on / 依赖: filter_or, filter_true_of_mem, h.top_le, symm.trans, top_le
-/
theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filter p union s.filter q = s :=
(filter_or _ _ _).symm.trans filter_true_of_mem fun x _ => h.top_le x trivial

/--
theorem `filter_union_filter_not_eq` / 定理 `filter_union_filter_not_eq`

English:
theorem filter_union_filter_not_eq
  given: [forall x, Decidable (¬p x)] (s : Finset α)
  proof: filter_union_filter_of_codisjoint _ _ _ @codisjoint_hnot_right _ _ p

中文:
定理 filter_union_filter_not_eq
  条件: [对任意 x, 可判定 (¬p x)] (s : 有限集 α)
  证明: filter_union_filter_of_codisjoint _ _ _ @codisjoint_hnot_right _ _ p

Depends on / 依赖: codisjoint_hnot_right, filter_union_filter_of_codisjoint
-/
theorem filter_union_filter_not_eq [forall x, Decidable (¬p x)] (s : Finset α) :
    (s.filter p union s.filter fun a => ¬p a) = s :=
filter_union_filter_of_codisjoint _ _ _ @codisjoint_hnot_right _ _ p

end

end Filter

/-! ### range -/


section Range

open Nat

variable {n m l : Nat}

@[simp]
/--
theorem `range_filter_eq` / 定理 `range_filter_eq`

English:
theorem range_filter_eq
  given: {n m : Nat}
  statement: (range n).filter (· = m) = if m < n then {m} else ∅
  proof: by grind

@[simp]

中文:
定理 range_filter_eq
  条件: {n m : 自然数}
  结论: (range n).filter (· = m) = if m < n then {m} else ∅
  证明: by grind

@[simp]
-/
theorem range_filter_eq {n m : Nat} : (range n).filter (· = m) = if m < n then {m} else ∅ := by grind

@[simp]
/--
theorem `range_inter_range` / 定理 `range_inter_range`

English:
theorem range_inter_range
  given: (m n : Nat)
  statement: range m inter range n = range (min m n)
  proof: by ext; simp

@[simp]

中文:
定理 range_inter_range
  条件: (m n : 自然数)
  结论: range m inter range n = range (最小值 m n)
  证明: by ext; simp

@[simp]
-/
theorem range_inter_range (m n : Nat) : range m inter range n = range (min m n) := by ext; simp

@[simp]
/--
theorem `range_union_range` / 定理 `range_union_range`

English:
theorem range_union_range
  given: (m n : Nat)
  statement: range m union range n = range (max m n)
  proof: by ext; simp

中文:
定理 range_union_range
  条件: (m n : 自然数)
  结论: range m union range n = range (最大值 m n)
  证明: by ext; simp
-/
theorem range_union_range (m n : Nat) : range m union range n = range (max m n) := by ext; simp

end Range

end Finset

/-! ### dedup on list and multiset -/

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

@[simp]
/--
theorem `toFinset_add` / 定理 `toFinset_add`

English:
theorem toFinset_add
  given: (s t : Multiset α)
  statement: (s + t).toFinset = s.toFinset union t.toFinset
  proof: Finset.ext by simp

@[simp]

中文:
定理 toFinset_add
  条件: (s t : Multiset α)
  结论: (s + t).toFinset = s.toFinset union t.toFinset
  证明: Finset.ext by simp

@[simp]

Depends on / 依赖: Finset, Finset.ext
-/
theorem toFinset_add (s t : Multiset α) : (s + t).toFinset = s.toFinset union t.toFinset :=
Finset.ext by simp

@[simp]
/--
theorem `toFinset_inter` / 定理 `toFinset_inter`

English:
theorem toFinset_inter
  given: (s t : Multiset α)
  statement: (s inter t).toFinset = s.toFinset inter t.toFinset
  proof: Finset.ext by simp

@[simp]

中文:
定理 toFinset_inter
  条件: (s t : Multiset α)
  结论: (s inter t).toFinset = s.toFinset inter t.toFinset
  证明: Finset.ext by simp

@[simp]

Depends on / 依赖: Finset, Finset.ext
-/
theorem toFinset_inter (s t : Multiset α) : (s inter t).toFinset = s.toFinset inter t.toFinset :=
Finset.ext by simp

@[simp]
/--
theorem `toFinset_union` / 定理 `toFinset_union`

English:
theorem toFinset_union
  given: (s t : Multiset α)
  statement: (s union t).toFinset = s.toFinset union t.toFinset
  proof: by
  ext; simp

@[simp]

中文:
定理 toFinset_union
  条件: (s t : Multiset α)
  结论: (s union t).toFinset = s.toFinset union t.toFinset
  证明: by
  ext; simp

@[simp]
-/
theorem toFinset_union (s t : Multiset α) : (s union t).toFinset = s.toFinset union t.toFinset := by
  ext; simp

@[simp]
/--
theorem `toFinset_eq_empty` / 定理 `toFinset_eq_empty`

English:
theorem toFinset_eq_empty
  given: {m : Multiset α}
  statement: m.toFinset = ∅ ↔ m = 0
  proof: Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]

中文:
定理 toFinset_eq_empty
  条件: {m : Multiset α}
  结论: m.toFinset = ∅ ↔ m = 0
  证明: Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]

Depends on / 依赖: Finset, Finset.val_inj.symm.trans, Multiset, Multiset.dedup_eq_zero, dedup_eq_zero, val_inj
-/
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]
/--
theorem `toFinset_nonempty` / 定理 `toFinset_nonempty`

English:
theorem toFinset_nonempty
  statement: s.toFinset.Nonempty ↔ s != 0
  proof: by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty

@[simp]

中文:
定理 toFinset_nonempty
  结论: s.toFinset.非空 ↔ s != 0
  证明: by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty

@[simp]

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, nonempty_iff_ne_empty, toFinset_eq_empty
-/
theorem toFinset_nonempty : s.toFinset.Nonempty ↔ s != 0 := by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty

@[simp]
/--
theorem `toFinset_filter` / 定理 `toFinset_filter`

English:
theorem toFinset_filter
  given: (s : Multiset α) (p : α -> Prop) [DecidablePred p]
  proof: by
  ext; simp

中文:
定理 toFinset_filter
  条件: (s : Multiset α) (p : α -> 命题) [DecidablePred p]
  证明: by
  ext; simp
-/
theorem toFinset_filter (s : Multiset α) (p : α -> Prop) [DecidablePred p] :
    (s.filter p).toFinset = s.toFinset.filter p := by
  ext; simp

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α} {f : α -> β}
  {s : Finset α} {t : Set β} {t' : Finset β}

@[simp]
/--
theorem `toFinset_union` / 定理 `toFinset_union`

English:
theorem toFinset_union
  given: (l l' : List α)
  statement: (l union l').toFinset = l.toFinset union l'.toFinset
  proof: by
  ext
  simp

@[simp]

中文:
定理 toFinset_union
  条件: (l l' : 列表 α)
  结论: (l union l').toFinset = l.toFinset union l'.toFinset
  证明: by
  ext
  simp

@[simp]
-/
theorem toFinset_union (l l' : List α) : (l union l').toFinset = l.toFinset union l'.toFinset := by
  ext
  simp

@[simp]
/--
theorem `toFinset_inter` / 定理 `toFinset_inter`

English:
theorem toFinset_inter
  given: (l l' : List α)
  statement: (l inter l').toFinset = l.toFinset inter l'.toFinset
  proof: by
  ext
  simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty_iff

@[simp]

中文:
定理 toFinset_inter
  条件: (l l' : 列表 α)
  结论: (l inter l').toFinset = l.toFinset inter l'.toFinset
  证明: by
  ext
  simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty_iff

@[simp]
-/
theorem toFinset_inter (l l' : List α) : (l inter l').toFinset = l.toFinset inter l'.toFinset := by
  ext
  simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.toFinset_nonempty_of_ne⟩ := toFinset_nonempty_iff

@[simp]
/--
theorem `toFinset_filter` / 定理 `toFinset_filter`

English:
theorem toFinset_filter
  given: (s : List α) (p : α -> Bool)
  proof: by
  ext; simp [List.mem_filter]

中文:
定理 toFinset_filter
  条件: (s : 列表 α) (p : α -> 布尔值)
  证明: by
  ext; simp [List.mem_filter]

Depends on / 依赖: List.mem_filter, mem_filter
-/
theorem toFinset_filter (s : List α) (p : α -> Bool) :
    (s.filter p).toFinset = s.toFinset.filter (p ·) := by
  ext; simp [List.mem_filter]

/--
theorem `filter_toFinset` / 定理 `filter_toFinset`

English:
theorem filter_toFinset
  given: (s : List α) (p : α -> Prop) [DecidablePred p]
  proof: by simp

中文:
定理 filter_toFinset
  条件: (s : 列表 α) (p : α -> 命题) [DecidablePred p]
  证明: by simp
-/
theorem filter_toFinset (s : List α) (p : α -> Prop) [DecidablePred p] :
    s.toFinset.filter p = (s.filter p).toFinset := by simp

end List

namespace Finset

section ToList

@[simp]
/--
theorem `toList_eq_nil` / 定理 `toList_eq_nil`

English:
theorem toList_eq_nil
  given: {s : Finset α}
  statement: s.toList = [] ↔ s = ∅
  proof: Multiset.toList_eq_nil.trans val_eq_zero

中文:
定理 toList_eq_nil
  条件: {s : 有限集 α}
  结论: s.toList = [] ↔ s = ∅
  证明: Multiset.toList_eq_nil.trans val_eq_zero

Depends on / 依赖: Multiset, Multiset.toList_eq_nil.trans, toList_eq_nil, val_eq_zero
-/
theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  Multiset.toList_eq_nil.trans val_eq_zero

/--
theorem `empty_toList` / 定理 `empty_toList`

English:
theorem empty_toList
  given: {s : Finset α}
  statement: s.toList.isEmpty ↔ s = ∅
  proof: by simp

@[simp]

中文:
定理 empty_toList
  条件: {s : 有限集 α}
  结论: s.toList.isEmpty ↔ s = ∅
  证明: by simp

@[simp]
-/
theorem empty_toList {s : Finset α} : s.toList.isEmpty ↔ s = ∅ := by simp

@[simp]
/--
theorem `toList_empty` / 定理 `toList_empty`

English:
theorem toList_empty
  statement: (∅ : Finset α).toList = []
  proof: toList_eq_nil.mpr rfl

中文:
定理 toList_empty
  结论: (∅ : 有限集 α).toList = []
  证明: toList_eq_nil.mpr rfl

Depends on / 依赖: toList_eq_nil, toList_eq_nil.mpr
-/
theorem toList_empty : (∅ : Finset α).toList = [] :=
  toList_eq_nil.mpr rfl

/--
theorem `Nonempty.toList_ne_nil` / 定理 `Nonempty.toList_ne_nil`

English:
theorem Nonempty.toList_ne_nil
  given: {s : Finset α} (hs : s.Nonempty)
  statement: s.toList != []
  proof: mt toList_eq_nil.mp hs.ne_empty

中文:
定理 非空.toList_ne_nil
  条件: {s : 有限集 α} (hs : s.非空)
  结论: s.toList != []
  证明: mt toList_eq_nil.mp hs.ne_empty

Depends on / 依赖: hs.ne_empty, ne_empty, toList_eq_nil, toList_eq_nil.mp
-/
theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList != [] :=
  mt toList_eq_nil.mp hs.ne_empty

/--
theorem `Nonempty.not_empty_toList` / 定理 `Nonempty.not_empty_toList`

English:
theorem Nonempty.not_empty_toList
  given: {s : Finset α} (hs : s.Nonempty)
  statement: ¬s.toList.isEmpty
  proof: mt empty_toList.mp hs.ne_empty

中文:
定理 非空.not_empty_toList
  条件: {s : 有限集 α} (hs : s.非空)
  结论: ¬s.toList.isEmpty
  证明: mt empty_toList.mp hs.ne_empty

Depends on / 依赖: empty_toList, empty_toList.mp, hs.ne_empty, ne_empty
-/
theorem Nonempty.not_empty_toList {s : Finset α} (hs : s.Nonempty) : ¬s.toList.isEmpty :=
  mt empty_toList.mp hs.ne_empty

end ToList

/-! ### choose -/


section Choose

variable (p : α -> Prop) [DecidablePred p] (l : Finset α)

/--
Definition of `chooseX` / `chooseX` 的定义

English:
definition chooseX
  signature: (hp : exists! a, a in l ∧ p a)
  body: l.val.chooseX p hp

中文:
定义 chooseX
  签名: (hp : 存在! a, a in l ∧ p a)
  定义体: l.val.chooseX p hp

Depends on / 依赖: chooseX, l.val.chooseX
-/
def chooseX (hp : exists! a, a in l ∧ p a) : { a // a in l ∧ p a } :=
  l.val.chooseX p hp

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: (hp : exists! a, a in l ∧ p a)
  body: l.chooseX p hp

中文:
定义 choose
  签名: (hp : 存在! a, a in l ∧ p a)
  定义体: l.chooseX p hp

Depends on / 依赖: chooseX, l.chooseX
-/
def choose (hp : exists! a, a in l ∧ p a) : α :=
  l.chooseX p hp

/--
theorem `choose_spec` / 定理 `choose_spec`

English:
theorem choose_spec
  given: (hp : exists! a, a in l ∧ p a)
  statement: l.choose p hp in l ∧ p (l.choose p hp)
  proof: (l.chooseX p hp).property

中文:
定理 choose_spec
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: l.choose p hp in l ∧ p (l.choose p hp)
  证明: (l.chooseX p hp).property

Depends on / 依赖: chooseX, l.chooseX, property
-/
theorem choose_spec (hp : exists! a, a in l ∧ p a) : l.choose p hp in l ∧ p (l.choose p hp) :=
  (l.chooseX p hp).property

/--
theorem `choose_mem` / 定理 `choose_mem`

English:
theorem choose_mem
  given: (hp : exists! a, a in l ∧ p a)
  statement: l.choose p hp in l
  proof: (choose_spec _ _ _).1

grind_pattern choose_mem => l.choose p hp

中文:
定理 choose_mem
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: l.choose p hp in l
  证明: (choose_spec _ _ _).1

grind_pattern choose_mem => l.choose p hp

Depends on / 依赖: choose_spec
-/
theorem choose_mem (hp : exists! a, a in l ∧ p a) : l.choose p hp in l :=
  (choose_spec _ _ _).1

grind_pattern choose_mem => l.choose p hp

/--
theorem `choose_property` / 定理 `choose_property`

English:
theorem choose_property
  given: (hp : exists! a, a in l ∧ p a)
  statement: p (l.choose p hp)
  proof: (choose_spec _ _ _).2

grind_pattern choose_property => l.choose p hp

中文:
定理 choose_property
  条件: (hp : 存在! a, a in l ∧ p a)
  结论: p (l.choose p hp)
  证明: (choose_spec _ _ _).2

grind_pattern choose_property => l.choose p hp

Depends on / 依赖: choose_spec
-/
theorem choose_property (hp : exists! a, a in l ∧ p a) : p (l.choose p hp) :=
  (choose_spec _ _ _).2

grind_pattern choose_property => l.choose p hp

/--
theorem `choose_eq_iff` / 定理 `choose_eq_iff`

English:
theorem choose_eq_iff
  given: (hp : exists! a, a in l ∧ p a) {a : α}
  statement: choose p l hp = a ↔ a in l ∧ p a
  proof: l.val.choose_eq_iff _ hp

中文:
定理 choose_eq_iff
  条件: (hp : 存在! a, a in l ∧ p a) {a : α}
  结论: choose p l hp = a ↔ a in l ∧ p a
  证明: l.val.choose_eq_iff _ hp

Depends on / 依赖: choose_eq_iff, l.val.choose_eq_iff
-/
theorem choose_eq_iff (hp : exists! a, a in l ∧ p a) {a : α} : choose p l hp = a ↔ a in l ∧ p a :=
  l.val.choose_eq_iff _ hp

end Choose

end Finset

namespace Equiv
variable [DecidableEq α] {s t : Finset α}

open Finset

/--
Definition of `Finset.union` / `Finset.union` 的定义

English:
definition Finset.union
  signature: (s t : Finset α) (h : Disjoint s t)
  body: .symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_union _ _)

@[simp]

中文:
定义 有限集.union
  签名: (s t : 有限集 α) (h : Disjoint s t)
  定义体: .symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_union _ _)

@[simp]

Depends on / 依赖: Equiv.Set.union, Equiv.setCongr, coe_union, disjoint_coe, disjoint_coe.mpr, setCongr
-/
def Finset.union (s t : Finset α) (h : Disjoint s t) :
    s oplus t ≃ (s union t : Finset α) :=
.symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_union _ _)

@[simp]
/--
theorem `Finset.union_inl` / 定理 `Finset.union_inl`

English:
theorem Finset.union_inl
  given: (h : Disjoint s t) (x : s)
  proof: rfl

@[simp]

中文:
定理 有限集.union_inl
  条件: (h : Disjoint s t) (x : s)
  证明: rfl

@[simp]
-/
theorem Finset.union_inl (h : Disjoint s t) (x : s) :
Equiv.Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr Or.inl x.2⟩ :=
  rfl

@[simp]
/--
theorem `Finset.union_inr` / 定理 `Finset.union_inr`

English:
theorem Finset.union_inr
  given: (h : Disjoint s t) (y : t)
  proof: rfl

@[simp]

中文:
定理 有限集.union_inr
  条件: (h : Disjoint s t) (y : t)
  证明: rfl

@[simp]
-/
theorem Finset.union_inr (h : Disjoint s t) (y : t) :
Equiv.Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr Or.inr y.2⟩ :=
  rfl

@[simp]
/--
theorem `Finset.union_symm_left` / 定理 `Finset.union_symm_left`

English:
theorem Finset.union_symm_left
  statement: (h : Disjoint s t) {i : α} (hi : i in s)
  proof: by
  simp [Equiv.symm_apply_eq]

@[simp]

中文:
定理 有限集.union_symm_left
  结论: (h : Disjoint s t) {i : α} (hi : i in s)
  证明: by
  simp [Equiv.symm_apply_eq]

@[simp]

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem Finset.union_symm_left (h : Disjoint s t) {i : α} (hi : i in s)
    (hi' : i in s union t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
/--
theorem `Finset.union_symm_right` / 定理 `Finset.union_symm_right`

English:
theorem Finset.union_symm_right
  statement: (h : Disjoint s t) {i : α} (hi : i in t)
  proof: by
  simp [Equiv.symm_apply_eq]

中文:
定理 有限集.union_symm_right
  结论: (h : Disjoint s t) {i : α} (hi : i in t)
  证明: by
  simp [Equiv.symm_apply_eq]

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem Finset.union_symm_right (h : Disjoint s t) {i : α} (hi : i in t)
    (hi' : i in s union t) : (Equiv.Finset.union s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/--
Definition of `Finset.disjUnionEquiv` / `Finset.disjUnionEquiv` 的定义

English:
definition Finset.disjUnionEquiv
  signature: (s t : Finset α) (h : Disjoint s t)
  body: .symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_disjUnion h)

@[simp]

中文:
定义 有限集.disjUnionEquiv
  签名: (s t : 有限集 α) (h : Disjoint s t)
  定义体: .symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_disjUnion h)

@[simp]

Depends on / 依赖: Equiv.Set.union, Equiv.setCongr, coe_disjUnion, disjoint_coe, disjoint_coe.mpr, setCongr
-/
def Finset.disjUnionEquiv (s t : Finset α) (h : Disjoint s t) :
    s oplus t ≃ s.disjUnion t h :=
.symm .trans (Equiv.Set.union (disjoint_coe.mpr h)) Equiv.setCongr (coe_disjUnion h)

@[simp]
/--
theorem `Finset.disjUnionEquiv_inl` / 定理 `Finset.disjUnionEquiv_inl`

English:
theorem Finset.disjUnionEquiv_inl
  given: (h : Disjoint s t) (x : s)
  proof: rfl

@[simp]

中文:
定理 有限集.disjUnionEquiv_inl
  条件: (h : Disjoint s t) (x : s)
  证明: rfl

@[simp]
-/
theorem Finset.disjUnionEquiv_inl (h : Disjoint s t) (x : s) :
Equiv.Finset.disjUnionEquiv s t h (Sum.inl x) = ⟨x, Finset.mem_disjUnion.mpr Or.inl x.2⟩ :=
  rfl

@[simp]
/--
theorem `Finset.disjUnionEquiv_inr` / 定理 `Finset.disjUnionEquiv_inr`

English:
theorem Finset.disjUnionEquiv_inr
  given: (h : Disjoint s t) (y : t)
  proof: rfl

@[simp]

中文:
定理 有限集.disjUnionEquiv_inr
  条件: (h : Disjoint s t) (y : t)
  证明: rfl

@[simp]
-/
theorem Finset.disjUnionEquiv_inr (h : Disjoint s t) (y : t) :
Equiv.Finset.disjUnionEquiv s t h (Sum.inr y) = ⟨y, Finset.mem_disjUnion.mpr Or.inr y.2⟩ :=
  rfl

@[simp]
/--
theorem `Finset.disjUnionEquiv_symm_left` / 定理 `Finset.disjUnionEquiv_symm_left`

English:
theorem Finset.disjUnionEquiv_symm_left
  statement: (h : Disjoint s t) {i : α} (hi : i in s)
  proof: by
  simp [Equiv.symm_apply_eq]

@[simp]

中文:
定理 有限集.disjUnionEquiv_symm_left
  结论: (h : Disjoint s t) {i : α} (hi : i in s)
  证明: by
  simp [Equiv.symm_apply_eq]

@[simp]

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem Finset.disjUnionEquiv_symm_left (h : Disjoint s t) {i : α} (hi : i in s)
    (hi' : i in s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inl ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

@[simp]
/--
theorem `Finset.disjUnionEquiv_symm_right` / 定理 `Finset.disjUnionEquiv_symm_right`

English:
theorem Finset.disjUnionEquiv_symm_right
  statement: (h : Disjoint s t) {i : α} (hi : i in t)
  proof: by
  simp [Equiv.symm_apply_eq]

中文:
定理 有限集.disjUnionEquiv_symm_right
  结论: (h : Disjoint s t) {i : α} (hi : i in t)
  证明: by
  simp [Equiv.symm_apply_eq]

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem Finset.disjUnionEquiv_symm_right (h : Disjoint s t) {i : α} (hi : i in t)
    (hi' : i in s.disjUnion t h) :
    (Equiv.Finset.disjUnionEquiv s t h).symm ⟨i, hi'⟩ = Sum.inr ⟨i, hi⟩ := by
  simp [Equiv.symm_apply_eq]

/--
Definition of `piFinsetUnion` / `piFinsetUnion` 的定义

English:
definition piFinsetUnion
  signature: {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι} (h : Disjoint s t)
  body: let e := Equiv.Finset.union s t h
.symm.trans (.piCongrLeft (fun i : ↥(s union t) => α i) e) sumPiEquivProdPi (fun b => α (e b))

中文:
定义 piFinsetUnion
  签名: {ι} [DecidableEq ι] (α : ι -> 类型) {s t : 有限集 ι} (h : Disjoint s t)
  定义体: let e := Equiv.Finset.union s t h
.symm.trans (.piCongrLeft (fun i : ↥(s union t) => α i) e) sumPiEquivProdPi (fun b => α (e b))

Depends on / 依赖: Equiv.Finset.union, Finset, piCongrLeft, sumPiEquivProdPi, symm.trans
-/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((forall i : s, α i) × forall i : t, α i) ≃ forall i : (s union t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
.symm.trans (.piCongrLeft (fun i : ↥(s union t) => α i) e) sumPiEquivProdPi (fun b => α (e b))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `piFinsetUnion_left` / 引理 `piFinsetUnion_left`

English:
lemma piFinsetUnion_left
  statement: {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
  proof: by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_left h hi hi']
  rfl

中文:
引理 piFinsetUnion_left
  结论: {ι} [DecidableEq ι] (α : ι -> 类型) {s t : 有限集 ι}
  证明: by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_left h hi hi']
  rfl

Depends on / 依赖: Finset, Finset.union_symm_left, coe_fn_symm_mk, piCongrLeft, piFinsetUnion, simp_rw, sumPiEquivProdPi, trans_apply, union_symm_left
-/
lemma piFinsetUnion_left {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i in s) (hi' : i in s union t) :
    piFinsetUnion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_left h hi hi']
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `piFinsetUnion_right` / 引理 `piFinsetUnion_right`

English:
lemma piFinsetUnion_right
  statement: {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
  proof: by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_right h hi hi']
  rfl

中文:
引理 piFinsetUnion_right
  结论: {ι} [DecidableEq ι] (α : ι -> 类型) {s t : 有限集 ι}
  证明: by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_right h hi hi']
  rfl

Depends on / 依赖: Finset, Finset.union_symm_right, coe_fn_symm_mk, piCongrLeft, piFinsetUnion, simp_rw, sumPiEquivProdPi, trans_apply, union_symm_right
-/
lemma piFinsetUnion_right {ι} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
    (h : Disjoint s t) {f g} {i : ι} (hi : i in t) (hi' : i in s union t) :
    Equiv.piFinsetUnion α h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
  simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
  rw! [Finset.union_symm_right h hi hi']
  rfl

/--
Definition of `_root_.Finset.equivToSet` / `_root_.Finset.equivToSet` 的定义

English:
definition _root_.Finset.equivToSet
  signature: (s : Finset α)
  body: ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

中文:
定义 _root_.有限集.equivToSet
  签名: (s : 有限集 α)
  定义体: ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

Depends on / 依赖: mem_coe
-/
def _root_.Finset.equivToSet (s : Finset α) : s ≃ (s : Set α) where
  toFun a := ⟨a.1, mem_coe.2 a.2⟩
  invFun a := ⟨a.1, mem_coe.1 a.2⟩

end Equiv

namespace Multiset

variable [DecidableEq α]

@[simp]
/--
lemma `toFinset_replicate` / 引理 `toFinset_replicate`

English:
lemma toFinset_replicate
  given: (n : Nat) (a : α)
  proof: by
  ext x
  simp only [mem_toFinset, mem_replicate]
  split_ifs with hn <;> simp [hn]

中文:
引理 toFinset_replicate
  条件: (n : 自然数) (a : α)
  证明: by
  ext x
  simp only [mem_toFinset, mem_replicate]
  split_ifs with hn <;> simp [hn]

Depends on / 依赖: mem_replicate, mem_toFinset, split_ifs
-/
lemma toFinset_replicate (n : Nat) (a : α) :
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by
  ext x
  simp only [mem_toFinset, mem_replicate]
  split_ifs with hn <;> simp [hn]

end Multiset

namespace Finset

variable {α : Type*}

/--
theorem `mem_union_of_disjoint` / 定理 `mem_union_of_disjoint`

English:
theorem mem_union_of_disjoint
  statement: [DecidableEq α]
  proof: by
  rw [Finset.mem_union]; rw [Xor]
  have := disjoint_left.1 h
  tauto

@[simp]

中文:
定理 mem_union_of_disjoint
  结论: [DecidableEq α]
  证明: by
  rw [Finset.mem_union]; rw [Xor]
  have := disjoint_left.1 h
  tauto

@[simp]

Depends on / 依赖: Finset, Finset.mem_union, disjoint_left, mem_union
-/
theorem mem_union_of_disjoint [DecidableEq α]
    {s t : Finset α} (h : Disjoint s t) {x : α} :
    x in s union t ↔ Xor (x in s) (x in t) := by
  rw [Finset.mem_union]; rw [Xor]
  have := disjoint_left.1 h
  tauto

@[simp]
/--
theorem `univ_finset_of_isEmpty` / 定理 `univ_finset_of_isEmpty`

English:
theorem univ_finset_of_isEmpty
  given: [h : IsEmpty α]
  statement: (Set.univ : Set (Finset α)) = {∅}
  proof: subset_antisymm (fun S hS => by simp [Finset.eq_empty_of_isEmpty S]) (by simp)

中文:
定理 univ_finset_of_isEmpty
  条件: [h : 是空 α]
  结论: (集合.univ : 集合 (有限集 α)) = {∅}
  证明: subset_antisymm (fun S hS => by simp [Finset.eq_empty_of_isEmpty S]) (by simp)

Depends on / 依赖: Finset, Finset.eq_empty_of_isEmpty, eq_empty_of_isEmpty, subset_antisymm
-/
theorem univ_finset_of_isEmpty [h : IsEmpty α] : (Set.univ : Set (Finset α)) = {∅} :=
  subset_antisymm (fun S hS => by simp [Finset.eq_empty_of_isEmpty S]) (by simp)

/--
theorem `isEmpty_of_forall_eq_empty` / 定理 `isEmpty_of_forall_eq_empty`

English:
theorem isEmpty_of_forall_eq_empty
  given: (H : forall s : Finset α, s = ∅)
  statement: IsEmpty α
  proof: isEmpty_iff.mpr fun a => by specialize H {a}; aesop

@[simp]

中文:
定理 isEmpty_of_对任意_eq_empty
  条件: (H : 对任意 s : 有限集 α, s = ∅)
  结论: 是空 α
  证明: isEmpty_iff.mpr fun a => by specialize H {a}; aesop

@[simp]

Depends on / 依赖: isEmpty_iff, isEmpty_iff.mpr, specialize
-/
theorem isEmpty_of_forall_eq_empty (H : forall s : Finset α, s = ∅) : IsEmpty α :=
  isEmpty_iff.mpr fun a => by specialize H {a}; aesop

@[simp]
/--
theorem `univ_finset_eq_singleton_empty_iff` / 定理 `univ_finset_eq_singleton_empty_iff`

English:
theorem univ_finset_eq_singleton_empty_iff
  statement: @Set.univ (Finset α) = {∅} ↔ IsEmpty α
  proof: ⟨fun h => isEmpty_of_forall_eq_empty fun s => Set.mem_singleton_iff.mp
    (Set.ext_iff.mp h s |>.mp (Set.mem_univ s)), fun _ => by simp⟩

中文:
定理 univ_finset_eq_singleton_empty_iff
  结论: @集合.univ (有限集 α) = {∅} ↔ 是空 α
  证明: ⟨fun h => isEmpty_of_forall_eq_empty fun s => Set.mem_singleton_iff.mp
    (Set.ext_iff.mp h s |>.mp (Set.mem_univ s)), fun _ => by simp⟩

Depends on / 依赖: Set.ext_iff.mp, Set.mem_singleton_iff.mp, Set.mem_univ, ext_iff, isEmpty_of_forall_eq_empty, mem_singleton_iff, mem_univ
-/
theorem univ_finset_eq_singleton_empty_iff : @Set.univ (Finset α) = {∅} ↔ IsEmpty α :=
  ⟨fun h => isEmpty_of_forall_eq_empty fun s => Set.mem_singleton_iff.mp
    (Set.ext_iff.mp h s |>.mp (Set.mem_univ s)), fun _ => by simp⟩

end Finset
