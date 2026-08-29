/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Aesop
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Tactic.Simproc.ExistsAndEq

/-!
# Lemmas about insertion, singleton, and pairs

This file provides extra lemmas about `insert`, `singleton`, and `pair`.

## Tags

insert, singleton

-/

@[expose] public section

assert_not_exists HeytingAlgebra

/-! ### Set coercion to a type -/

open Function

namespace Set

variable {α β : Type*} {s t : Set α} {a b : α}


/--
theorem `insert_def` / 定理 `insert_def`

English:
theorem insert_def
  given: (x : α) (s : Set α)
  statement: insert x s = { y | y = x ∨ y in s }
  proof: rfl

@[simp]

中文:
定理 insert_def
  条件: (x : α) (s : 集合 α)
  结论: insert x s = { y | y = x ∨ y in s }
  证明: rfl

@[simp]
-/
theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y in s } :=
  rfl

@[simp]
/--
theorem `subset_insert` / 定理 `subset_insert`

English:
theorem subset_insert
  given: (x : α) (s : Set α)
  statement: s subseteq insert x s
  proof: fun _ => Or.inr

中文:
定理 subset_insert
  条件: (x : α) (s : 集合 α)
  结论: s subseteq insert x s
  证明: fun _ => Or.inr

Depends on / 依赖: Or.inr
-/
theorem subset_insert (x : α) (s : Set α) : s subseteq insert x s := fun _ => Or.inr

-- This is a fairly aggressive pattern; it might be safer to use
-- `s ⊆ insert x s` or `_ ⊆ insert x s` instead.
-- Currently Cslib relies on this.
-- See `MathlibTest/grind/set.lean` for a test case illustrating the reasoning
-- that Cslib is relying on.
grind_pattern subset_insert => insert x s

/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  given: (x : α) (s : Set α)
  statement: x in insert x s
  proof: Or.inl rfl

中文:
定理 mem_insert
  条件: (x : α) (s : 集合 α)
  结论: x in insert x s
  证明: Or.inl rfl

Depends on / 依赖: Or.inl
-/
theorem mem_insert (x : α) (s : Set α) : x in insert x s :=
  Or.inl rfl

/--
theorem `mem_insert_of_mem` / 定理 `mem_insert_of_mem`

English:
theorem mem_insert_of_mem
  given: {x : α} {s : Set α} (y : α)
  statement: x in s -> x in insert y s
  proof: Or.inr

中文:
定理 mem_insert_of_mem
  条件: {x : α} {s : 集合 α} (y : α)
  结论: x in s -> x in insert y s
  证明: Or.inr

Depends on / 依赖: Or.inr
-/
theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x in s -> x in insert y s :=
  Or.inr

/--
theorem `eq_or_mem_of_mem_insert` / 定理 `eq_or_mem_of_mem_insert`

English:
theorem eq_or_mem_of_mem_insert
  given: {x a : α} {s : Set α}
  statement: x in insert a s -> x = a ∨ x in s
  proof: id

中文:
定理 eq_or_mem_of_mem_insert
  条件: {x a : α} {s : 集合 α}
  结论: x in insert a s -> x = a ∨ x in s
  证明: id
-/
theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x in insert a s -> x = a ∨ x in s :=
  id

/--
theorem `mem_of_mem_insert_of_ne` / 定理 `mem_of_mem_insert_of_ne`

English:
theorem mem_of_mem_insert_of_ne
  statement: b in insert a s -> b != a -> b in s
  proof: Or.resolve_left

中文:
定理 mem_of_mem_insert_of_ne
  结论: b in insert a s -> b != a -> b in s
  证明: Or.resolve_left

Depends on / 依赖: Or.resolve_left, resolve_left
-/
theorem mem_of_mem_insert_of_ne : b in insert a s -> b != a -> b in s :=
  Or.resolve_left

/--
theorem `eq_of_mem_insert_of_notMem` / 定理 `eq_of_mem_insert_of_notMem`

English:
theorem eq_of_mem_insert_of_notMem
  statement: b in insert a s -> b ∉ s -> b = a
  proof: Or.resolve_right

@[simp, grind =, push]

中文:
定理 eq_of_mem_insert_of_notMem
  结论: b in insert a s -> b ∉ s -> b = a
  证明: Or.resolve_right

@[simp, grind =, push]

Depends on / 依赖: Or.resolve_right, resolve_right
-/
theorem eq_of_mem_insert_of_notMem : b in insert a s -> b ∉ s -> b = a :=
  Or.resolve_right

@[simp, grind =, push]
/--
theorem `mem_insert_iff` / 定理 `mem_insert_iff`

English:
theorem mem_insert_iff
  given: {x a : α} {s : Set α}
  statement: x in insert a s ↔ x = a ∨ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_insert_iff
  条件: {x a : α} {s : 集合 α}
  结论: x in insert a s ↔ x = a ∨ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_insert_iff {x a : α} {s : Set α} : x in insert a s ↔ x = a ∨ x in s :=
  Iff.rfl

@[simp]
/--
theorem `insert_eq_of_mem` / 定理 `insert_eq_of_mem`

English:
theorem insert_eq_of_mem
  given: {a : α} {s : Set α} (h : a in s)
  statement: insert a s = s
  proof: by grind

中文:
定理 insert_eq_of_mem
  条件: {a : α} {s : 集合 α} (h : a in s)
  结论: insert a s = s
  证明: by grind
-/
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a in s) : insert a s = s := by grind

/--
theorem `ne_insert_of_notMem` / 定理 `ne_insert_of_notMem`

English:
theorem ne_insert_of_notMem
  given: {s : Set α} (t : Set α) {a : α}
  statement: a ∉ s -> s != insert a t
  proof: by grind

@[simp]

中文:
定理 ne_insert_of_notMem
  条件: {s : 集合 α} (t : 集合 α) {a : α}
  结论: a ∉ s -> s != insert a t
  证明: by grind

@[simp]
-/
theorem ne_insert_of_notMem {s : Set α} (t : Set α) {a : α} : a ∉ s -> s != insert a t := by grind

@[simp]
/--
theorem `insert_eq_self` / 定理 `insert_eq_self`

English:
theorem insert_eq_self
  statement: insert a s = s ↔ a in s
  proof: by grind

中文:
定理 insert_eq_self
  结论: insert a s = s ↔ a in s
  证明: by grind

Depends on / 依赖: CommRing
-/
theorem insert_eq_self : insert a s = s ↔ a in s := by grind

/--
theorem `insert_ne_self` / 定理 `insert_ne_self`

English:
theorem insert_ne_self
  statement: insert a s != s ↔ a ∉ s
  proof: by grind

中文:
定理 insert_ne_self
  结论: insert a s != s ↔ a ∉ s
  证明: by grind
-/
theorem insert_ne_self : insert a s != s ↔ a ∉ s := by grind

/--
theorem `insert_subset_iff` / 定理 `insert_subset_iff`

English:
theorem insert_subset_iff
  statement: insert a s subseteq t ↔ a in t ∧ s subseteq t
  proof: by grind

中文:
定理 insert_subset_iff
  结论: insert a s subseteq t ↔ a in t ∧ s subseteq t
  证明: by grind
-/
theorem insert_subset_iff : insert a s subseteq t ↔ a in t ∧ s subseteq t := by grind

/--
theorem `insert_subset` / 定理 `insert_subset`

English:
theorem insert_subset
  given: (ha : a in t) (hs : s subseteq t)
  statement: insert a s subseteq t
  proof: by grind

@[gcongr]

中文:
定理 insert_subset
  条件: (ha : a in t) (hs : s subseteq t)
  结论: insert a s subseteq t
  证明: by grind

@[gcongr]
-/
theorem insert_subset (ha : a in t) (hs : s subseteq t) : insert a s subseteq t := by grind

@[gcongr]
/--
theorem `insert_subset_insert` / 定理 `insert_subset_insert`

English:
theorem insert_subset_insert
  given: (h : s subseteq t)
  statement: insert a s subseteq insert a t
  proof: by grind

中文:
定理 insert_subset_insert
  条件: (h : s subseteq t)
  结论: insert a s subseteq insert a t
  证明: by grind
-/
theorem insert_subset_insert (h : s subseteq t) : insert a s subseteq insert a t := by grind

/--
theorem `insert_subset_insert_iff` / 定理 `insert_subset_insert_iff`

English:
theorem insert_subset_insert_iff
  given: (ha : a ∉ s)
  statement: insert a s subseteq insert a t ↔ s subseteq t
  proof: by grind

中文:
定理 insert_subset_insert_iff
  条件: (ha : a ∉ s)
  结论: insert a s subseteq insert a t ↔ s subseteq t
  证明: by grind
-/
@[simp] theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s subseteq insert a t ↔ s subseteq t := by grind

/--
theorem `subset_insert_iff_of_notMem` / 定理 `subset_insert_iff_of_notMem`

English:
theorem subset_insert_iff_of_notMem
  given: (ha : a ∉ s)
  statement: s subseteq insert a t ↔ s subseteq t
  proof: by grind

中文:
定理 subset_insert_iff_of_notMem
  条件: (ha : a ∉ s)
  结论: s subseteq insert a t ↔ s subseteq t
  证明: by grind
-/
theorem subset_insert_iff_of_notMem (ha : a ∉ s) : s subseteq insert a t ↔ s subseteq t := by grind

/--
theorem `ssubset_iff_insert` / 定理 `ssubset_iff_insert`

English:
theorem ssubset_iff_insert
  given: {s t : Set α}
  statement: s ⊂ t ↔ exists a ∉ s, insert a s subseteq t
  proof: by grind

中文:
定理 ssubset_iff_insert
  条件: {s t : 集合 α}
  结论: s ⊂ t ↔ 存在 a ∉ s, insert a s subseteq t
  证明: by grind
-/
theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ exists a ∉ s, insert a s subseteq t := by grind

/--
theorem `_root_.LE.le.ssubset_of_mem_notMem` / 定理 `_root_.LE.le.ssubset_of_mem_notMem`

English:
theorem _root_.LE.le.ssubset_of_mem_notMem
  given: (hst : s subseteq t) (hat : a in t) (has : a ∉ s)
  proof: by grind

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.ssubset_of_mem_notMem := LE.le.ssubset_of_mem_notMem

中文:
定理 _root_.LE.le.ssubset_of_mem_notMem
  条件: (hst : s subseteq t) (hat : a in t) (has : a ∉ s)
  证明: by grind

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.ssubset_of_mem_notMem := LE.le.ssubset_of_mem_notMem
-/
theorem _root_.LE.le.ssubset_of_mem_notMem (hst : s subseteq t) (hat : a in t) (has : a ∉ s) :
    s ⊂ t := by grind

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.ssubset_of_mem_notMem := LE.le.ssubset_of_mem_notMem

/--
theorem `ssubset_insert` / 定理 `ssubset_insert`

English:
theorem ssubset_insert
  given: {s : Set α} {a : α} (h : a ∉ s)
  statement: s ⊂ insert a s
  proof: by grind

中文:
定理 ssubset_insert
  条件: {s : 集合 α} {a : α} (h : a ∉ s)
  结论: s ⊂ insert a s
  证明: by grind
-/
theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s := by grind

/--
theorem `insert_comm` / 定理 `insert_comm`

English:
theorem insert_comm
  given: (a b : α) (s : Set α)
  statement: insert a (insert b s) = insert b (insert a s)
  proof: by
  grind

中文:
定理 insert_comm
  条件: (a b : α) (s : 集合 α)
  结论: insert a (insert b s) = insert b (insert a s)
  证明: by
  grind
-/
theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) := by
  grind

/--
theorem `insert_idem` / 定理 `insert_idem`

English:
theorem insert_idem
  given: (a : α) (s : Set α)
  statement: insert a (insert a s) = insert a s
  proof: by grind

中文:
定理 insert_idem
  条件: (a : α) (s : 集合 α)
  结论: insert a (insert a s) = insert a s
  证明: by grind
-/
theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s := by grind

/--
theorem `insert_union` / 定理 `insert_union`

English:
theorem insert_union
  statement: insert a s union t = insert a (s union t)
  proof: by grind

@[simp]

中文:
定理 insert_union
  结论: insert a s union t = insert a (s union t)
  证明: by grind

@[simp]
-/
theorem insert_union : insert a s union t = insert a (s union t) := by grind

@[simp]
/--
theorem `union_insert` / 定理 `union_insert`

English:
theorem union_insert
  statement: s union insert a t = insert a (s union t)
  proof: by grind

@[simp]

中文:
定理 union_insert
  结论: s union insert a t = insert a (s union t)
  证明: by grind

@[simp]
-/
theorem union_insert : s union insert a t = insert a (s union t) := by grind

@[simp]
/--
theorem `insert_nonempty` / 定理 `insert_nonempty`

English:
theorem insert_nonempty
  given: (a : α) (s : Set α)
  statement: (insert a s).Nonempty
  proof: ⟨a, mem_insert a s⟩

中文:
定理 insert_nonempty
  条件: (a : α) (s : 集合 α)
  结论: (insert a s).非空
  证明: ⟨a, mem_insert a s⟩

Depends on / 依赖: mem_insert
-/
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

/--
theorem `insert_inter_distrib` / 定理 `insert_inter_distrib`

English:
theorem insert_inter_distrib
  given: (a : α) (s t : Set α)
  proof: by grind

中文:
定理 insert_inter_distrib
  条件: (a : α) (s t : 集合 α)
  证明: by grind
-/
theorem insert_inter_distrib (a : α) (s t : Set α) :
    insert a (s inter t) = insert a s inter insert a t := by grind

/--
theorem `insert_union_distrib` / 定理 `insert_union_distrib`

English:
theorem insert_union_distrib
  given: (a : α) (s t : Set α)
  proof: by grind

中文:
定理 insert_union_distrib
  条件: (a : α) (s t : 集合 α)
  证明: by grind
-/
theorem insert_union_distrib (a : α) (s t : Set α) :
    insert a (s union t) = insert a s union insert a t := by grind

-- useful in proofs by induction
/--
theorem `forall_of_forall_insert` / 定理 `forall_of_forall_insert`

English:
theorem forall_of_forall_insert
  statement: {P : α -> Prop} {a : α} {s : Set α} (H : forall x, x in insert a s -> P x)
  proof: by grind

中文:
定理 对任意_of_对任意_insert
  结论: {P : α -> 命题} {a : α} {s : 集合 α} (H : 对任意 x, x in insert a s -> P x)
  证明: by grind
-/
theorem forall_of_forall_insert {P : α -> Prop} {a : α} {s : Set α} (H : forall x, x in insert a s -> P x)
    (x) (h : x in s) : P x := by grind

/--
theorem `forall_insert_of_forall` / 定理 `forall_insert_of_forall`

English:
theorem forall_insert_of_forall
  statement: {P : α -> Prop} {a : α} {s : Set α} (H : forall x, x in s -> P x) (ha : P a)
  proof: by grind

中文:
定理 对任意_insert_of_对任意
  结论: {P : α -> 命题} {a : α} {s : 集合 α} (H : 对任意 x, x in s -> P x) (ha : P a)
  证明: by grind
-/
theorem forall_insert_of_forall {P : α -> Prop} {a : α} {s : Set α} (H : forall x, x in s -> P x) (ha : P a)
    (x) (h : x in insert a s) : P x := by grind

/--
theorem `exists_mem_insert` / 定理 `exists_mem_insert`

English:
theorem exists_mem_insert
  given: {P : α -> Prop} {a : α} {s : Set α}
  proof: by grind

中文:
定理 存在_mem_insert
  条件: {P : α -> 命题} {a : α} {s : 集合 α}
  证明: by grind
-/
theorem exists_mem_insert {P : α -> Prop} {a : α} {s : Set α} :
    (exists x in insert a s, P x) ↔ (P a ∨ exists x in s, P x) := by grind

/--
theorem `forall_mem_insert` / 定理 `forall_mem_insert`

English:
theorem forall_mem_insert
  given: {P : α -> Prop} {a : α} {s : Set α}
  proof: by grind

中文:
定理 对任意_mem_insert
  条件: {P : α -> 命题} {a : α} {s : 集合 α}
  证明: by grind
-/
theorem forall_mem_insert {P : α -> Prop} {a : α} {s : Set α} :
    (forall x in insert a s, P x) ↔ P a ∧ forall x in s, P x := by grind

/--
Definition of `subtypeInsertEquivOption` / `subtypeInsertEquivOption` 的定义

English:
definition subtypeInsertEquivOption
  body: if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

中文:
定义 subtypeInsertEquivOption
  定义体: if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind
-/
def subtypeInsertEquivOption
    [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
    { i // i in insert x t } ≃ Option { i // i in t } where
  toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulSingleton α (Set α)
  body: ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩

中文:
实例 :
  签名: LawfulSingleton α (集合 α)
  定义体: ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩

Depends on / 依赖: Iff.rfl, Set.ext, mem_empty_iff_false, mem_insert_iff, or_false
-/
instance : LawfulSingleton α (Set α) :=
  ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩

/--
theorem `singleton_def` / 定理 `singleton_def`

English:
theorem singleton_def
  given: (a : α)
  statement: ({a} : Set α) = insert a ∅
  proof: (insert_empty_eq a).symm

@[simp, grind =, push]

中文:
定理 singleton_def
  条件: (a : α)
  结论: ({a} : 集合 α) = insert a ∅
  证明: (insert_empty_eq a).symm

@[simp, grind =, push]

Depends on / 依赖: insert_empty_eq
-/
theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_empty_eq a).symm

@[simp, grind =, push]
/--
theorem `mem_singleton_iff` / 定理 `mem_singleton_iff`

English:
theorem mem_singleton_iff
  given: {a b : α}
  statement: a in ({b} : Set α) ↔ a = b
  proof: Iff.rfl

中文:
定理 mem_singleton_iff
  条件: {a b : α}
  结论: a in ({b} : 集合 α) ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_singleton_iff {a b : α} : a in ({b} : Set α) ↔ a = b :=
  Iff.rfl

/--
theorem `notMem_singleton_iff` / 定理 `notMem_singleton_iff`

English:
theorem notMem_singleton_iff
  given: {a b : α}
  statement: a ∉ ({b} : Set α) ↔ a != b
  proof: Iff.rfl

@[simp]

中文:
定理 notMem_singleton_iff
  条件: {a b : α}
  结论: a ∉ ({b} : 集合 α) ↔ a != b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem notMem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a != b :=
  Iff.rfl

@[simp]
/--
theorem `ofPred_eq_eq_singleton` / 定理 `ofPred_eq_eq_singleton`

English:
theorem ofPred_eq_eq_singleton
  given: {a : α}
  statement: { n | n = a } = {a}
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton := ofPred_eq_eq_singleton

@[simp]

中文:
定理 ofPred_eq_eq_singleton
  条件: {a : α}
  结论: { n | n = a } = {a}
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton := ofPred_eq_eq_singleton

@[simp]
-/
theorem ofPred_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton := ofPred_eq_eq_singleton

@[simp]
/--
theorem `ofPred_eq_eq_singleton'` / 定理 `ofPred_eq_eq_singleton'`

English:
theorem ofPred_eq_eq_singleton'
  given: {a : α}
  statement: { x | a = x } = {a}
  proof: ext fun _ => eq_comm

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton' := ofPred_eq_eq_singleton'

中文:
定理 ofPred_eq_eq_singleton'
  条件: {a : α}
  结论: { x | a = x } = {a}
  证明: ext fun _ => eq_comm

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton' := ofPred_eq_eq_singleton'

Depends on / 依赖: eq_comm
-/
theorem ofPred_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton' := ofPred_eq_eq_singleton'

-- TODO: again, annotation needed
-- Not `@[simp]` since `mem_singleton_iff` proves it.
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: (a : α)
  statement: a in ({a} : Set α)
  proof: @rfl _ _

中文:
定理 mem_singleton
  条件: (a : α)
  结论: a in ({a} : 集合 α)
  证明: @rfl _ _
-/
theorem mem_singleton (a : α) : a in ({a} : Set α) :=
  @rfl _ _

/--
theorem `eq_of_mem_singleton` / 定理 `eq_of_mem_singleton`

English:
theorem eq_of_mem_singleton
  given: {x y : α} (h : x in ({y} : Set α))
  statement: x = y
  proof: h

@[simp]

中文:
定理 eq_of_mem_singleton
  条件: {x y : α} (h : x in ({y} : 集合 α))
  结论: x = y
  证明: h

@[simp]
-/
theorem eq_of_mem_singleton {x y : α} (h : x in ({y} : Set α)) : x = y :=
  h

@[simp]
/--
theorem `singleton_eq_singleton_iff` / 定理 `singleton_eq_singleton_iff`

English:
theorem singleton_eq_singleton_iff
  given: {x y : α}
  statement: {x} = ({y} : Set α) ↔ x = y
  proof: Set.ext_iff.trans eq_iff_eq_cancel_left

中文:
定理 singleton_eq_singleton_iff
  条件: {x y : α}
  结论: {x} = ({y} : 集合 α) ↔ x = y
  证明: Set.ext_iff.trans eq_iff_eq_cancel_left

Depends on / 依赖: Set.ext_iff.trans, eq_iff_eq_cancel_left, ext_iff
-/
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  Set.ext_iff.trans eq_iff_eq_cancel_left

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Injective (singleton : α -> Set α)
  proof: fun _ _ =>
  singleton_eq_singleton_iff.mp

中文:
定理 singleton_injective
  结论: 单射 (singleton : α -> 集合 α)
  证明: fun _ _ =>
  singleton_eq_singleton_iff.mp
-/
theorem singleton_injective : Injective (singleton : α -> Set α) := fun _ _ =>
  singleton_eq_singleton_iff.mp

/--
theorem `mem_singleton_of_eq` / 定理 `mem_singleton_of_eq`

English:
theorem mem_singleton_of_eq
  given: {x y : α} (H : x = y)
  statement: x in ({y} : Set α)
  proof: H

中文:
定理 mem_singleton_of_eq
  条件: {x y : α} (H : x = y)
  结论: x in ({y} : 集合 α)
  证明: H
-/
theorem mem_singleton_of_eq {x y : α} (H : x = y) : x in ({y} : Set α) :=
  H

/--
theorem `insert_eq` / 定理 `insert_eq`

English:
theorem insert_eq
  given: (x : α) (s : Set α)
  statement: insert x s = ({x} : Set α) union s
  proof: rfl

@[simp]

中文:
定理 insert_eq
  条件: (x : α) (s : 集合 α)
  结论: insert x s = ({x} : 集合 α) union s
  证明: rfl

@[simp]
-/
theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) union s :=
  rfl

@[simp]
/--
theorem `singleton_nonempty` / 定理 `singleton_nonempty`

English:
theorem singleton_nonempty
  given: (a : α)
  statement: ({a} : Set α).Nonempty
  proof: ⟨a, rfl⟩

@[simp]

中文:
定理 singleton_nonempty
  条件: (a : α)
  结论: ({a} : 集合 α).非空
  证明: ⟨a, rfl⟩

@[simp]
-/
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩

@[simp]
/--
theorem `singleton_ne_empty` / 定理 `singleton_ne_empty`

English:
theorem singleton_ne_empty
  given: (a : α)
  statement: ({a} : Set α) != ∅
  proof: (singleton_nonempty _).ne_empty

@[simp]

中文:
定理 singleton_ne_empty
  条件: (a : α)
  结论: ({a} : 集合 α) != ∅
  证明: (singleton_nonempty _).ne_empty

@[simp]

Depends on / 依赖: ContMDiffVectorBundle, ContMDiffVectorBundle.of_le, h.out, ne_empty, of_le, singleton_nonempty
-/
theorem singleton_ne_empty (a : α) : ({a} : Set α) != ∅ :=
  (singleton_nonempty _).ne_empty

@[simp]
/--
theorem `empty_ne_singleton` / 定理 `empty_ne_singleton`

English:
theorem empty_ne_singleton
  given: (a : α)
  statement: ∅ != ({a} : Set α)
  proof: (singleton_ne_empty a).symm

中文:
定理 empty_ne_singleton
  条件: (a : α)
  结论: ∅ != ({a} : 集合 α)
  证明: (singleton_ne_empty a).symm

Depends on / 依赖: ContMDiffVectorBundle, ContMDiffVectorBundle.of_le, le_top, of_le, singleton_ne_empty
-/
theorem empty_ne_singleton (a : α) : ∅ != ({a} : Set α) :=
  (singleton_ne_empty a).symm

/--
theorem `empty_ssubset_singleton` / 定理 `empty_ssubset_singleton`

English:
theorem empty_ssubset_singleton
  statement: (∅ : Set α) ⊂ {a}
  proof: (singleton_nonempty _).empty_ssubset

@[simp, grind =]

中文:
定理 empty_ssubset_singleton
  结论: (∅ : 集合 α) ⊂ {a}
  证明: (singleton_nonempty _).empty_ssubset

@[simp, grind =]

Depends on / 依赖: empty_ssubset, singleton_nonempty
-/
theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, grind =]
/--
theorem `singleton_subset_iff` / 定理 `singleton_subset_iff`

English:
theorem singleton_subset_iff
  given: {a : α} {s : Set α}
  statement: {a} subseteq s ↔ a in s
  proof: forall_eq

@[gcongr]

中文:
定理 singleton_subset_iff
  条件: {a : α} {s : 集合 α}
  结论: {a} subseteq s ↔ a in s
  证明: forall_eq

@[gcongr]

Depends on / 依赖: forall_eq
-/
theorem singleton_subset_iff {a : α} {s : Set α} : {a} subseteq s ↔ a in s :=
  forall_eq

@[gcongr]
/--
theorem `singleton_subset_singleton` / 定理 `singleton_subset_singleton`

English:
theorem singleton_subset_singleton
  statement: ({a} : Set α) subseteq {b} ↔ a = b
  proof: by simp

中文:
定理 singleton_subset_singleton
  结论: ({a} : 集合 α) subseteq {b} ↔ a = b
  证明: by simp
-/
theorem singleton_subset_singleton : ({a} : Set α) subseteq {b} ↔ a = b := by simp

/--
theorem `set_compr_eq_eq_singleton` / 定理 `set_compr_eq_eq_singleton`

English:
theorem set_compr_eq_eq_singleton
  given: {a : α}
  statement: { b | b = a } = {a}
  proof: rfl

@[simp]

中文:
定理 set_compr_eq_eq_singleton
  条件: {a : α}
  结论: { b | b = a } = {a}
  证明: rfl

@[simp]
-/
theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl

@[simp]
/--
theorem `singleton_union` / 定理 `singleton_union`

English:
theorem singleton_union
  statement: {a} union s = insert a s
  proof: rfl

@[simp]

中文:
定理 singleton_union
  结论: {a} union s = insert a s
  证明: rfl

@[simp]
-/
theorem singleton_union : {a} union s = insert a s :=
  rfl

@[simp]
/--
theorem `union_singleton` / 定理 `union_singleton`

English:
theorem union_singleton
  statement: s union {a} = insert a s
  proof: union_comm _ _

@[simp]

中文:
定理 union_singleton
  结论: s union {a} = insert a s
  证明: union_comm _ _

@[simp]

Depends on / 依赖: union_comm
-/
theorem union_singleton : s union {a} = insert a s :=
  union_comm _ _

@[simp]
/--
theorem `singleton_inter_nonempty` / 定理 `singleton_inter_nonempty`

English:
theorem singleton_inter_nonempty
  statement: ({a} inter s).Nonempty ↔ a in s
  proof: by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]

中文:
定理 singleton_inter_nonempty
  结论: ({a} inter s).非空 ↔ a in s
  证明: by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]

Depends on / 依赖: Nonempty, Set.Nonempty, exists_eq_left, mem_inter_iff, mem_singleton_iff
-/
theorem singleton_inter_nonempty : ({a} inter s).Nonempty ↔ a in s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]
/--
theorem `inter_singleton_nonempty` / 定理 `inter_singleton_nonempty`

English:
theorem inter_singleton_nonempty
  statement: (s inter {a}).Nonempty ↔ a in s
  proof: by
  rw [inter_comm]; rw [singleton_inter_nonempty]

@[simp]

中文:
定理 inter_singleton_nonempty
  结论: (s inter {a}).非空 ↔ a in s
  证明: by
  rw [inter_comm]; rw [singleton_inter_nonempty]

@[simp]

Depends on / 依赖: inter_comm, singleton_inter_nonempty
-/
theorem inter_singleton_nonempty : (s inter {a}).Nonempty ↔ a in s := by
  rw [inter_comm]; rw [singleton_inter_nonempty]

@[simp]
/--
theorem `singleton_inter_eq_empty` / 定理 `singleton_inter_eq_empty`

English:
theorem singleton_inter_eq_empty
  statement: {a} inter s = ∅ ↔ a ∉ s
  proof: not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp]

中文:
定理 singleton_inter_eq_empty
  结论: {a} inter s = ∅ ↔ a ∉ s
  证明: not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp]

Depends on / 依赖: not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.symm.trans, singleton_inter_nonempty, singleton_inter_nonempty.not
-/
theorem singleton_inter_eq_empty : {a} inter s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp]
/--
theorem `inter_singleton_eq_empty` / 定理 `inter_singleton_eq_empty`

English:
theorem inter_singleton_eq_empty
  statement: s inter {a} = ∅ ↔ a ∉ s
  proof: by
  rw [inter_comm]; rw [singleton_inter_eq_empty]

@[simp] alias ⟨_, singleton_inter_of_notMem⟩ := singleton_inter_eq_empty
@[simp] alias ⟨_, inter_singleton_of_notMem⟩ := inter_singleton_eq_empty

中文:
定理 inter_singleton_eq_empty
  结论: s inter {a} = ∅ ↔ a ∉ s
  证明: by
  rw [inter_comm]; rw [singleton_inter_eq_empty]

@[simp] alias ⟨_, singleton_inter_of_notMem⟩ := singleton_inter_eq_empty
@[simp] alias ⟨_, inter_singleton_of_notMem⟩ := inter_singleton_eq_empty

Depends on / 依赖: inter_comm, singleton_inter_eq_empty
-/
theorem inter_singleton_eq_empty : s inter {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm]; rw [singleton_inter_eq_empty]

@[simp] alias ⟨_, singleton_inter_of_notMem⟩ := singleton_inter_eq_empty
@[simp] alias ⟨_, inter_singleton_of_notMem⟩ := inter_singleton_eq_empty

/--
lemma `singleton_inter_of_mem` / 引理 `singleton_inter_of_mem`

English:
lemma singleton_inter_of_mem
  given: (ha : a in s)
  statement: {a} inter s = {a}
  proof: by simpa

中文:
引理 singleton_inter_of_mem
  条件: (ha : a in s)
  结论: {a} inter s = {a}
  证明: by simpa
-/
@[simp] lemma singleton_inter_of_mem (ha : a in s) : {a} inter s = {a} := by simpa
/--
lemma `inter_singleton_of_mem` / 引理 `inter_singleton_of_mem`

English:
lemma inter_singleton_of_mem
  given: (ha : a in s)
  statement: s inter {a} = {a}
  proof: by simpa

中文:
引理 inter_singleton_of_mem
  条件: (ha : a in s)
  结论: s inter {a} = {a}
  证明: by simpa
-/
@[simp] lemma inter_singleton_of_mem (ha : a in s) : s inter {a} = {a} := by simpa

/--
theorem `notMem_singleton_empty` / 定理 `notMem_singleton_empty`

English:
theorem notMem_singleton_empty
  given: {s : Set α}
  statement: s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty
  proof: nonempty_iff_ne_empty.symm

中文:
定理 notMem_singleton_empty
  条件: {s : 集合 α}
  结论: s ∉ ({∅} : 集合 (集合 α)) ↔ s.非空
  证明: nonempty_iff_ne_empty.symm

Depends on / 依赖: nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
theorem notMem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm

/--
Instance `uniqueSingleton` / 实例 `uniqueSingleton`

English:
instance uniqueSingleton
  signature: (a : α)
  body: ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.ext h⟩

中文:
实例 uniqueSingleton
  签名: (a : α)
  定义体: ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.ext h⟩

Depends on / 依赖: Subtype, Subtype.ext, mem_singleton
-/
instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.ext h⟩

/--
theorem `eq_singleton_iff_unique_mem` / 定理 `eq_singleton_iff_unique_mem`

English:
theorem eq_singleton_iff_unique_mem
  statement: s = {a} ↔ a in s ∧ forall x in s, x = a
  proof: Subset.antisymm_iff.trans and_comm.trans and_congr_left' singleton_subset_iff

中文:
定理 eq_singleton_iff_unique_mem
  结论: s = {a} ↔ a in s ∧ 对任意 x in s, x = a
  证明: Subset.antisymm_iff.trans and_comm.trans and_congr_left' singleton_subset_iff

Depends on / 依赖: Subset, Subset.antisymm_iff.trans, and_comm, and_comm.trans, and_congr_left, antisymm_iff, singleton_subset_iff
-/
theorem eq_singleton_iff_unique_mem : s = {a} ↔ a in s ∧ forall x in s, x = a :=
Subset.antisymm_iff.trans and_comm.trans and_congr_left' singleton_subset_iff

/--
theorem `eq_singleton_iff_nonempty_unique_mem` / 定理 `eq_singleton_iff_nonempty_unique_mem`

English:
theorem eq_singleton_iff_nonempty_unique_mem
  statement: s = {a} ↔ s.Nonempty ∧ forall x in s, x = a
  proof: eq_singleton_iff_unique_mem.trans
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

中文:
定理 eq_singleton_iff_nonempty_unique_mem
  结论: s = {a} ↔ s.非空 ∧ 对任意 x in s, x = a
  证明: eq_singleton_iff_unique_mem.trans
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

Depends on / 依赖: and_congr_left, eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem.trans
-/
theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ forall x in s, x = a :=
eq_singleton_iff_unique_mem.trans
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

/--
theorem `singleton_iff_unique_mem` / 定理 `singleton_iff_unique_mem`

English:
theorem singleton_iff_unique_mem
  statement: (exists a, s = {a}) ↔ exists! a, a in s
  proof: ⟨fun ⟨a, h⟩ => ⟨a, by grind⟩, fun ⟨a, h⟩ => ⟨a, by grind⟩⟩

中文:
定理 singleton_iff_unique_mem
  结论: (存在 a, s = {a}) ↔ 存在! a, a in s
  证明: ⟨fun ⟨a, h⟩ => ⟨a, by grind⟩, fun ⟨a, h⟩ => ⟨a, by grind⟩⟩
-/
theorem singleton_iff_unique_mem : (exists a, s = {a}) ↔ exists! a, a in s :=
  ⟨fun ⟨a, h⟩ => ⟨a, by grind⟩, fun ⟨a, h⟩ => ⟨a, by grind⟩⟩

/--
theorem `ofPred_mem_list_eq_replicate` / 定理 `ofPred_mem_list_eq_replicate`

English:
theorem ofPred_mem_list_eq_replicate
  given: {l : List α} {a : α}
  proof: by
  simpa +contextual [Set.ext_iff, iff_iff_implies_and_implies, forall_and, List.eq_replicate_iff,
    List.length_pos_iff_exists_mem] using ⟨fun _ _ => ⟨_, ‹_›⟩, fun x hx h => h _ hx ▸ hx⟩

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_replicate := ofPred_mem_list_eq_replicate

中文:
定理 ofPred_mem_list_eq_replicate
  条件: {l : 列表 α} {a : α}
  证明: by
  simpa +contextual [Set.ext_iff, iff_iff_implies_and_implies, forall_and, List.eq_replicate_iff,
    List.length_pos_iff_exists_mem] using ⟨fun _ _ => ⟨_, ‹_›⟩, fun x hx h => h _ hx ▸ hx⟩

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_replicate := ofPred_mem_list_eq_replicate

Depends on / 依赖: List.eq_replicate_iff, List.length_pos_iff_exists_mem, Set.ext_iff, contextual, eq_replicate_iff, ext_iff, forall_and, iff_iff_implies_and_implies, length_pos_iff_exists_mem
-/
theorem ofPred_mem_list_eq_replicate {l : List α} {a : α} :
    { x | x in l } = {a} ↔ exists n > 0, l = List.replicate n a := by
  simpa +contextual [Set.ext_iff, iff_iff_implies_and_implies, forall_and, List.eq_replicate_iff,
    List.length_pos_iff_exists_mem] using ⟨fun _ _ => ⟨_, ‹_›⟩, fun x hx h => h _ hx ▸ hx⟩

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_replicate := ofPred_mem_list_eq_replicate

/--
theorem `ofPred_mem_list_eq_singleton_of_nodup` / 定理 `ofPred_mem_list_eq_singleton_of_nodup`

English:
theorem ofPred_mem_list_eq_singleton_of_nodup
  given: {l : List α} (H : l.Nodup) {a : α}
  proof: by
  constructor
  · rw [ofPred_mem_list_eq_replicate]
    rintro ⟨n, hn, rfl⟩
    simp only [List.nodup_replicate] at H
    simp [show n = 1 by lia]
  · rintro rfl
    simp

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_singleton_of_nodup := ofPred_mem_list_eq_singleton_of_nodup

中文:
定理 ofPred_mem_list_eq_singleton_of_nodup
  条件: {l : 列表 α} (H : l.Nodup) {a : α}
  证明: by
  constructor
  · rw [ofPred_mem_list_eq_replicate]
    rintro ⟨n, hn, rfl⟩
    simp only [List.nodup_replicate] at H
    simp [show n = 1 by lia]
  · rintro rfl
    simp

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_singleton_of_nodup := ofPred_mem_list_eq_singleton_of_nodup

Depends on / 依赖: List.nodup_replicate, nodup_replicate, ofPred_mem_list_eq_replicate
-/
theorem ofPred_mem_list_eq_singleton_of_nodup {l : List α} (H : l.Nodup) {a : α} :
    { x | x in l } = {a} ↔ l = [a] := by
  constructor
  · rw [ofPred_mem_list_eq_replicate]
    rintro ⟨n, hn, rfl⟩
    simp only [List.nodup_replicate] at H
    simp [show n = 1 by lia]
  · rintro rfl
    simp

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_singleton_of_nodup := ofPred_mem_list_eq_singleton_of_nodup

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
/--
theorem `default_coe_singleton` / 定理 `default_coe_singleton`

English:
theorem default_coe_singleton
  given: (x : α)
  statement: (default : ({x} : Set α)) = ⟨x, rfl⟩
  proof: rfl

@[simp]

中文:
定理 default_coe_singleton
  条件: (x : α)
  结论: (default : ({x} : 集合 α)) = ⟨x, rfl⟩
  证明: rfl

@[simp]
-/
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl

@[simp]
/--
theorem `subset_singleton_iff` / 定理 `subset_singleton_iff`

English:
theorem subset_singleton_iff
  given: {α : Type*} {s : Set α} {x : α}
  statement: s subseteq {x} ↔ forall y in s, y = x
  proof: Iff.rfl

中文:
定理 subset_singleton_iff
  条件: {α : 类型} {s : 集合 α} {x : α}
  结论: s subseteq {x} ↔ 对任意 y in s, y = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s subseteq {x} ↔ forall y in s, y = x :=
  Iff.rfl

/--
theorem `subset_singleton_iff_eq` / 定理 `subset_singleton_iff_eq`

English:
theorem subset_singleton_iff_eq
  given: {s : Set α} {x : α}
  statement: s subseteq {x} ↔ s = ∅ ∨ s = {x}
  proof: by grind

中文:
定理 subset_singleton_iff_eq
  条件: {s : 集合 α} {x : α}
  结论: s subseteq {x} ↔ s = ∅ ∨ s = {x}
  证明: by grind
-/
theorem subset_singleton_iff_eq {s : Set α} {x : α} : s subseteq {x} ↔ s = ∅ ∨ s = {x} := by grind

/--
theorem `Nonempty.subset_singleton_iff` / 定理 `Nonempty.subset_singleton_iff`

English:
theorem Nonempty.subset_singleton_iff
  given: (h : s.Nonempty)
  statement: s subseteq {a} ↔ s = {a}
  proof: subset_singleton_iff_eq.trans or_iff_right h.ne_empty

中文:
定理 非空.subset_singleton_iff
  条件: (h : s.非空)
  结论: s subseteq {a} ↔ s = {a}
  证明: subset_singleton_iff_eq.trans or_iff_right h.ne_empty

Depends on / 依赖: h.ne_empty, ne_empty, or_iff_right, subset_singleton_iff_eq, subset_singleton_iff_eq.trans
-/
theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s subseteq {a} ↔ s = {a} :=
subset_singleton_iff_eq.trans or_iff_right h.ne_empty

/--
theorem `ssubset_singleton_iff` / 定理 `ssubset_singleton_iff`

English:
theorem ssubset_singleton_iff
  given: {s : Set α} {x : α}
  statement: s ⊂ {x} ↔ s = ∅
  proof: by
  rw [ssubset_iff_subset_ne]; rw [subset_singleton_iff_eq]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [and_iff_left_iff_imp]
  exact fun h => h ▸ empty_ne_singleton _

中文:
定理 ssubset_singleton_iff
  条件: {s : 集合 α} {x : α}
  结论: s ⊂ {x} ↔ s = ∅
  证明: by
  rw [ssubset_iff_subset_ne]; rw [subset_singleton_iff_eq]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [and_iff_left_iff_imp]
  exact fun h => h ▸ empty_ne_singleton _

Depends on / 依赖: and_iff_left_iff_imp, and_not_self_iff, empty_ne_singleton, or_and_right, or_false, ssubset_iff_subset_ne, subset_singleton_iff_eq
-/
theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne]; rw [subset_singleton_iff_eq]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [and_iff_left_iff_imp]
  exact fun h => h ▸ empty_ne_singleton _

/--
theorem `eq_empty_of_ssubset_singleton` / 定理 `eq_empty_of_ssubset_singleton`

English:
theorem eq_empty_of_ssubset_singleton
  given: {s : Set α} {x : α} (hs : s ⊂ {x})
  statement: s = ∅
  proof: ssubset_singleton_iff.1 hs

中文:
定理 eq_empty_of_ssubset_singleton
  条件: {s : 集合 α} {x : α} (hs : s ⊂ {x})
  结论: s = ∅
  证明: ssubset_singleton_iff.1 hs

Depends on / 依赖: ssubset_singleton_iff
-/
theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/--
theorem `eq_of_nonempty_of_subsingleton` / 定理 `eq_of_nonempty_of_subsingleton`

English:
theorem eq_of_nonempty_of_subsingleton
  statement: {α} [Subsingleton α] (s t : Set α) [Nonempty s]
  proof: Nonempty.of_subtype.eq_univ.trans Nonempty.of_subtype.eq_univ.symm

中文:
定理 eq_of_nonempty_of_subsingleton
  结论: {α} [子单例 α] (s t : 集合 α) [非空 s]
  证明: Nonempty.of_subtype.eq_univ.trans Nonempty.of_subtype.eq_univ.symm

Depends on / 依赖: Nonempty, Nonempty.of_subtype.eq_univ.symm, Nonempty.of_subtype.eq_univ.trans, eq_univ, of_subtype
-/
theorem eq_of_nonempty_of_subsingleton {α} [Subsingleton α] (s t : Set α) [Nonempty s]
    [Nonempty t] : s = t :=
  Nonempty.of_subtype.eq_univ.trans Nonempty.of_subtype.eq_univ.symm

/--
theorem `eq_of_nonempty_of_subsingleton'` / 定理 `eq_of_nonempty_of_subsingleton'`

English:
theorem eq_of_nonempty_of_subsingleton'
  statement: {α} [Subsingleton α] {s : Set α} (t : Set α)
  proof: have := hs.to_subtype; eq_of_nonempty_of_subsingleton s t

中文:
定理 eq_of_nonempty_of_subsingleton'
  结论: {α} [子单例 α] {s : 集合 α} (t : 集合 α)
  证明: have := hs.to_subtype; eq_of_nonempty_of_subsingleton s t

Depends on / 依赖: eq_of_nonempty_of_subsingleton, hs.to_subtype, to_subtype
-/
theorem eq_of_nonempty_of_subsingleton' {α} [Subsingleton α] {s : Set α} (t : Set α)
    (hs : s.Nonempty) [Nonempty t] : s = t :=
  have := hs.to_subtype; eq_of_nonempty_of_subsingleton s t

/--
theorem `Nonempty.eq_zero` / 定理 `Nonempty.eq_zero`

English:
theorem Nonempty.eq_zero
  given: [Subsingleton α] [Zero α] {s : Set α} (h : s.Nonempty)
  proof: eq_of_nonempty_of_subsingleton' {0} h

中文:
定理 非空.eq_zero
  条件: [子单例 α] [零 α] {s : 集合 α} (h : s.非空)
  证明: eq_of_nonempty_of_subsingleton' {0} h

Depends on / 依赖: eq_of_nonempty_of_subsingleton
-/
theorem Nonempty.eq_zero [Subsingleton α] [Zero α] {s : Set α} (h : s.Nonempty) :
    s = {0} := eq_of_nonempty_of_subsingleton' {0} h

/--
theorem `Nonempty.eq_one` / 定理 `Nonempty.eq_one`

English:
theorem Nonempty.eq_one
  given: [Subsingleton α] [One α] {s : Set α} (h : s.Nonempty)
  proof: eq_of_nonempty_of_subsingleton' {1} h

中文:
定理 非空.eq_one
  条件: [子单例 α] [幺 α] {s : 集合 α} (h : s.非空)
  证明: eq_of_nonempty_of_subsingleton' {1} h

Depends on / 依赖: eq_of_nonempty_of_subsingleton
-/
theorem Nonempty.eq_one [Subsingleton α] [One α] {s : Set α} (h : s.Nonempty) :
    s = {1} := eq_of_nonempty_of_subsingleton' {1} h

/-! ### Disjointness -/

@[simp default + 1]
/--
lemma `disjoint_singleton_left` / 引理 `disjoint_singleton_left`

English:
lemma disjoint_singleton_left
  statement: Disjoint {a} s ↔ a ∉ s
  proof: by simp [Set.disjoint_iff, subset_def]

@[simp]

中文:
引理 disjoint_singleton_left
  结论: Disjoint {a} s ↔ a ∉ s
  证明: by simp [Set.disjoint_iff, subset_def]

@[simp]

Depends on / 依赖: Set.disjoint_iff, disjoint_iff, subset_def
-/
lemma disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by simp [Set.disjoint_iff, subset_def]

@[simp]
/--
lemma `disjoint_singleton_right` / 引理 `disjoint_singleton_right`

English:
lemma disjoint_singleton_right
  statement: Disjoint s {a} ↔ a ∉ s
  proof: disjoint_comm.trans disjoint_singleton_left

中文:
引理 disjoint_singleton_right
  结论: Disjoint s {a} ↔ a ∉ s
  证明: disjoint_comm.trans disjoint_singleton_left

Depends on / 依赖: disjoint_comm, disjoint_comm.trans, disjoint_singleton_left
-/
lemma disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

/--
lemma `disjoint_singleton` / 引理 `disjoint_singleton`

English:
lemma disjoint_singleton
  statement: Disjoint ({a} : Set α) {b} ↔ a != b
  proof: by
  simp

@[simp]

中文:
引理 disjoint_singleton
  结论: Disjoint ({a} : 集合 α) {b} ↔ a != b
  证明: by
  simp

@[simp]
-/
lemma disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a != b := by
  simp

@[simp]
/--
theorem `disjoint_insert_left` / 定理 `disjoint_insert_left`

English:
theorem disjoint_insert_left
  statement: Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
  proof: by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]

中文:
定理 disjoint_insert_left
  结论: Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
  证明: by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]

Depends on / 依赖: Set.disjoint_left, Set.mem_insert_iff, disjoint_left, forall_eq_or_imp, mem_insert_iff
-/
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]
/--
theorem `disjoint_insert_right` / 定理 `disjoint_insert_right`

English:
theorem disjoint_insert_right
  statement: Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
  proof: by
  rw [disjoint_comm]; rw [disjoint_insert_left]; rw [disjoint_comm]

中文:
定理 disjoint_insert_right
  结论: Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
  证明: by
  rw [disjoint_comm]; rw [disjoint_insert_left]; rw [disjoint_comm]

Depends on / 依赖: disjoint_comm, disjoint_insert_left
-/
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm]; rw [disjoint_insert_left]; rw [disjoint_comm]

/--
theorem `insert_inj` / 定理 `insert_inj`

English:
theorem insert_inj
  given: (ha : a ∉ s)
  statement: insert a s = insert b s ↔ a = b
  proof: ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩

@[simp]

中文:
定理 insert_inj
  条件: (ha : a ∉ s)
  结论: insert a s = insert b s ↔ a = b
  证明: ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩

@[simp]

Depends on / 依赖: congr_arg, eq_of_mem_insert_of_notMem, insert, mem_insert
-/
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩

@[simp]
/--
theorem `insert_sdiff_eq_singleton` / 定理 `insert_sdiff_eq_singleton`

English:
theorem insert_sdiff_eq_singleton
  given: {a : α} {s : Set α} (h : a ∉ s)
  statement: insert a s \ s = {a}
  proof: by grind

@[deprecated (since := "2026-06-03")] alias insert_diff_eq_singleton := insert_sdiff_eq_singleton

中文:
定理 insert_sdiff_eq_singleton
  条件: {a : α} {s : 集合 α} (h : a ∉ s)
  结论: insert a s \ s = {a}
  证明: by grind

@[deprecated (since := "2026-06-03")] alias insert_diff_eq_singleton := insert_sdiff_eq_singleton
-/
theorem insert_sdiff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by grind

@[deprecated (since := "2026-06-03")] alias insert_diff_eq_singleton := insert_sdiff_eq_singleton

/--
theorem `inter_insert_of_mem` / 定理 `inter_insert_of_mem`

English:
theorem inter_insert_of_mem
  given: (h : a in s)
  statement: s inter insert a t = insert a (s inter t)
  proof: by grind

中文:
定理 inter_insert_of_mem
  条件: (h : a in s)
  结论: s inter insert a t = insert a (s inter t)
  证明: by grind
-/
theorem inter_insert_of_mem (h : a in s) : s inter insert a t = insert a (s inter t) := by grind

/--
theorem `insert_inter_of_mem` / 定理 `insert_inter_of_mem`

English:
theorem insert_inter_of_mem
  given: (h : a in t)
  statement: insert a s inter t = insert a (s inter t)
  proof: by grind

中文:
定理 insert_inter_of_mem
  条件: (h : a in t)
  结论: insert a s inter t = insert a (s inter t)
  证明: by grind
-/
theorem insert_inter_of_mem (h : a in t) : insert a s inter t = insert a (s inter t) := by grind

/--
theorem `inter_insert_of_notMem` / 定理 `inter_insert_of_notMem`

English:
theorem inter_insert_of_notMem
  given: (h : a ∉ s)
  statement: s inter insert a t = s inter t
  proof: by grind

中文:
定理 inter_insert_of_notMem
  条件: (h : a ∉ s)
  结论: s inter insert a t = s inter t
  证明: by grind
-/
theorem inter_insert_of_notMem (h : a ∉ s) : s inter insert a t = s inter t := by grind

/--
theorem `insert_inter_of_notMem` / 定理 `insert_inter_of_notMem`

English:
theorem insert_inter_of_notMem
  given: (h : a ∉ t)
  statement: insert a s inter t = s inter t
  proof: by grind

中文:
定理 insert_inter_of_notMem
  条件: (h : a ∉ t)
  结论: insert a s inter t = s inter t
  证明: by grind
-/
theorem insert_inter_of_notMem (h : a ∉ t) : insert a s inter t = s inter t := by grind


/--
theorem `pair_eq_singleton` / 定理 `pair_eq_singleton`

English:
theorem pair_eq_singleton
  given: (a : α)
  statement: ({a, a} : Set α) = {a}
  proof: union_self _

中文:
定理 pair_eq_singleton
  条件: (a : α)
  结论: ({a, a} : 集合 α) = {a}
  证明: union_self _

Depends on / 依赖: union_self
-/
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

/--
theorem `pair_comm` / 定理 `pair_comm`

English:
theorem pair_comm
  given: (a b : α)
  statement: ({a, b} : Set α) = {b, a}
  proof: union_comm _ _

中文:
定理 pair_comm
  条件: (a b : α)
  结论: ({a, b} : 集合 α) = {b, a}
  证明: union_comm _ _

Depends on / 依赖: union_comm
-/
theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

/--
theorem `pair_eq_pair_iff` / 定理 `pair_eq_pair_iff`

English:
theorem pair_eq_pair_iff
  given: {x y z w : α}
  proof: by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

中文:
定理 pair_eq_pair_iff
  条件: {x y z w : α}
  证明: by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

Depends on / 依赖: insert_subset_iff, subset_antisymm_iff
-/
theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop

/--
theorem `pair_subset_iff` / 定理 `pair_subset_iff`

English:
theorem pair_subset_iff
  statement: {a, b} subseteq s ↔ a in s ∧ b in s
  proof: by grind

中文:
定理 pair_subset_iff
  结论: {a, b} subseteq s ↔ a in s ∧ b in s
  证明: by grind
-/
theorem pair_subset_iff : {a, b} subseteq s ↔ a in s ∧ b in s := by grind

/--
theorem `pair_subset` / 定理 `pair_subset`

English:
theorem pair_subset
  given: (ha : a in s) (hb : b in s)
  statement: {a, b} subseteq s
  proof: pair_subset_iff.2 ⟨ha,hb⟩

中文:
定理 pair_subset
  条件: (ha : a in s) (hb : b in s)
  结论: {a, b} subseteq s
  证明: pair_subset_iff.2 ⟨ha,hb⟩

Depends on / 依赖: pair_subset_iff
-/
theorem pair_subset (ha : a in s) (hb : b in s) : {a, b} subseteq s :=
  pair_subset_iff.2 ⟨ha,hb⟩

/--
theorem `subset_pair_iff` / 定理 `subset_pair_iff`

English:
theorem subset_pair_iff
  statement: s subseteq {a, b} ↔ forall x in s, x = a ∨ x = b
  proof: by grind

中文:
定理 subset_pair_iff
  结论: s subseteq {a, b} ↔ 对任意 x in s, x = a ∨ x = b
  证明: by grind
-/
theorem subset_pair_iff : s subseteq {a, b} ↔ forall x in s, x = a ∨ x = b := by grind

/--
theorem `subset_pair_iff_eq` / 定理 `subset_pair_iff_eq`

English:
theorem subset_pair_iff_eq
  given: {x y : α}
  statement: s subseteq {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  proof: by grind
  mpr := by grind

中文:
定理 subset_pair_iff_eq
  条件: {x y : α}
  结论: s subseteq {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  证明: by grind
  mpr := by grind
-/
theorem subset_pair_iff_eq {x y : α} : s subseteq {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  mp := by grind
  mpr := by grind

/--
theorem `Nonempty.subset_pair_iff_eq` / 定理 `Nonempty.subset_pair_iff_eq`

English:
theorem Nonempty.subset_pair_iff_eq
  given: (hs : s.Nonempty)
  proof: by
  rw [Set.subset_pair_iff_eq]; rw [or_iff_right]; exact hs.ne_empty

中文:
定理 非空.subset_pair_iff_eq
  条件: (hs : s.非空)
  证明: by
  rw [Set.subset_pair_iff_eq]; rw [or_iff_right]; exact hs.ne_empty

Depends on / 依赖: Set.subset_pair_iff_eq, hs.ne_empty, ne_empty, or_iff_right, subset_pair_iff_eq
-/
theorem Nonempty.subset_pair_iff_eq (hs : s.Nonempty) :
    s subseteq {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  rw [Set.subset_pair_iff_eq]; rw [or_iff_right]; exact hs.ne_empty

/--
theorem `range_ite_const` / 定理 `range_ite_const`

English:
theorem range_ite_const
  statement: {p : α -> Prop} [DecidablePred p] {x y : β}
  proof: by
  grind

中文:
定理 range_ite_const
  结论: {p : α -> 命题} [DecidablePred p] {x y : β}
  证明: by
  grind
-/
theorem range_ite_const {p : α -> Prop} [DecidablePred p] {x y : β}
    (hp : exists a, p a) (hn : exists a, ¬ p a) :
    Set.range (fun a => if p a then x else y) = {x, y} := by
  grind

/-! ### Powerset -/

/--
theorem `powerset_singleton` / 定理 `powerset_singleton`

English:
theorem powerset_singleton
  given: (x : α)
  statement: 𝒫 {x} = {∅, {x}}
  proof: by grind

中文:
定理 powerset_singleton
  条件: (x : α)
  结论: 𝒫 {x} = {∅, {x}}
  证明: by grind
-/
theorem powerset_singleton (x : α) : 𝒫 {x} = {∅, {x}} := by grind

section
variable {α β : Type*} {a : α} {b : β}

/--
lemma `preimage_fst_singleton_eq_range` / 引理 `preimage_fst_singleton_eq_range`

English:
lemma preimage_fst_singleton_eq_range
  statement: (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·)
  proof: by
  grind

中文:
引理 preimage_fst_singleton_eq_range
  结论: (积类型.fst ⁻¹' {a} : 集合 (α × β)) = range (a, ·)
  证明: by
  grind
-/
lemma preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·) := by
  grind

/--
lemma `preimage_snd_singleton_eq_range` / 引理 `preimage_snd_singleton_eq_range`

English:
lemma preimage_snd_singleton_eq_range
  statement: (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b)
  proof: by
  grind

中文:
引理 preimage_snd_singleton_eq_range
  结论: (积类型.snd ⁻¹' {b} : 集合 (α × β)) = range (·, b)
  证明: by
  grind
-/
lemma preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b) := by
  grind

end

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

/-! ### Decidability instances for sets -/

variable (s t : Set α) (a b : α)

/--
Instance `decidableSingleton` / 实例 `decidableSingleton`

English:
instance decidableSingleton
  signature: [Decidable (a = b)]
  body: inferInstanceAs (Decidable (a = b))

中文:
实例 decidableSingleton
  签名: [可判定 (a = b)]
  定义体: inferInstanceAs (Decidable (a = b))

Depends on / 依赖: Decidable
-/
instance decidableSingleton [Decidable (a = b)] : Decidable (a in ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

end Set

open Set

/--
theorem `Prop.compl_singleton` / 定理 `Prop.compl_singleton`

English:
theorem Prop.compl_singleton
  given: (p : Prop)
  statement: ({p}ᶜ : Set Prop) = {¬p}
  proof: ext fun q => by simpa [@Iff.comm q] using not_iff

中文:
定理 命题.compl_singleton
  条件: (p : 命题)
  结论: ({p}ᶜ : 集合 命题) = {¬p}
  证明: ext fun q => by simpa [@Iff.comm q] using not_iff
-/
@[simp] theorem Prop.compl_singleton (p : Prop) : ({p}ᶜ : Set Prop) = {¬p} :=
  ext fun q => by simpa [@Iff.comm q] using not_iff
