/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Lemmas about the lattice structure of finite sets

This file contains many results on the lattice structure of `Finset α`, in particular the
interaction between union, intersection, empty set and inserting elements.

## Tags

finite sets, finset

-/

public section

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

/--
theorem `disjoint_iff_inter_eq_empty` / 定理 `disjoint_iff_inter_eq_empty`

English:
theorem disjoint_iff_inter_eq_empty
  statement: Disjoint s t ↔ s inter t = ∅
  proof: disjoint_iff

中文:
定理 disjoint_iff_inter_eq_empty
  结论: Disjoint s t ↔ s inter t = ∅
  证明: disjoint_iff

Depends on / 依赖: disjoint_iff
-/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s inter t = ∅ :=
  disjoint_iff

/-! #### union -/

@[simp]
/--
theorem `union_empty` / 定理 `union_empty`

English:
theorem union_empty
  given: (s : Finset α)
  statement: s union ∅ = s
  proof: ext fun x => mem_union.trans by simp

@[simp]

中文:
定理 union_empty
  条件: (s : Finset α)
  结论: s union ∅ = s
  证明: ext fun x => mem_union.trans by simp

@[simp]

Depends on / 依赖: mem_union, mem_union.trans
-/
theorem union_empty (s : Finset α) : s union ∅ = s :=
ext fun x => mem_union.trans by simp

@[simp]
/--
theorem `empty_union` / 定理 `empty_union`

English:
theorem empty_union
  given: (s : Finset α)
  statement: ∅ union s = s
  proof: ext fun x => mem_union.trans by simp

@[aesop unsafe apply (rule_sets := [finsetNonempty])]

中文:
定理 empty_union
  条件: (s : Finset α)
  结论: ∅ union s = s
  证明: ext fun x => mem_union.trans by simp

@[aesop unsafe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: mem_union, mem_union.trans
-/
theorem empty_union (s : Finset α) : ∅ union s = s :=
ext fun x => mem_union.trans by simp

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.inl` / 定理 `Nonempty.inl`

English:
theorem Nonempty.inl
  given: {s t : Finset α} (h : s.Nonempty)
  statement: (s union t).Nonempty
  proof: h.mono subset_union_left

@[aesop unsafe apply (rule_sets := [finsetNonempty])]

中文:
定理 Nonempty.inl
  条件: {s t : Finset α} (h : s.Nonempty)
  结论: (s union t).Nonempty
  证明: h.mono subset_union_left

@[aesop unsafe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: h.mono, subset_union_left
-/
theorem Nonempty.inl {s t : Finset α} (h : s.Nonempty) : (s union t).Nonempty :=
  h.mono subset_union_left

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.inr` / 定理 `Nonempty.inr`

English:
theorem Nonempty.inr
  given: {s t : Finset α} (h : t.Nonempty)
  statement: (s union t).Nonempty
  proof: h.mono subset_union_right

中文:
定理 Nonempty.inr
  条件: {s t : Finset α} (h : t.Nonempty)
  结论: (s union t).Nonempty
  证明: h.mono subset_union_right

Depends on / 依赖: h.mono, subset_union_right
-/
theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s union t).Nonempty :=
  h.mono subset_union_right

/--
theorem `insert_eq` / 定理 `insert_eq`

English:
theorem insert_eq
  given: (a : α) (s : Finset α)
  statement: insert a s = {a} union s
  proof: rfl

@[simp, grind =]

中文:
定理 insert_eq
  条件: (a : α) (s : Finset α)
  结论: insert a s = {a} union s
  证明: rfl

@[simp, grind =]
-/
theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} union s :=
  rfl

@[simp, grind =]
/--
lemma `singleton_union` / 引理 `singleton_union`

English:
lemma singleton_union
  given: (x : α) (s : Finset α)
  statement: {x} union s = insert x s
  proof: rfl

中文:
引理 singleton_union
  条件: (x : α) (s : Finset α)
  结论: {x} union s = insert x s
  证明: rfl
-/
lemma singleton_union (x : α) (s : Finset α) : {x} union s = insert x s :=
  rfl

/- We lower the simp-priority of `union_singleton` to ensure that `{x} ∪ {y}`
simplifies to `{x, y}` and not `{y, x}`. -/

@[simp 900, grind =]
/--
lemma `union_singleton` / 引理 `union_singleton`

English:
lemma union_singleton
  given: (x : α) (s : Finset α)
  statement: s union {x} = insert x s
  proof: by
  rw [Finset.union_comm]; rw [singleton_union]

@[simp, grind =]

中文:
引理 union_singleton
  条件: (x : α) (s : Finset α)
  结论: s union {x} = insert x s
  证明: by
  rw [Finset.union_comm]; rw [singleton_union]

@[simp, grind =]

Depends on / 依赖: Finset, Finset.union_comm, singleton_union, union_comm
-/
lemma union_singleton (x : α) (s : Finset α) : s union {x} = insert x s := by
  rw [Finset.union_comm]; rw [singleton_union]

@[simp, grind =]
/--
theorem `insert_union` / 定理 `insert_union`

English:
theorem insert_union
  given: (a : α) (s t : Finset α)
  statement: insert a s union t = insert a (s union t)
  proof: by
  simp only [insert_eq, union_assoc]

@[simp, grind =]

中文:
定理 insert_union
  条件: (a : α) (s t : Finset α)
  结论: insert a s union t = insert a (s union t)
  证明: by
  simp only [insert_eq, union_assoc]

@[simp, grind =]

Depends on / 依赖: insert_eq, union_assoc
-/
theorem insert_union (a : α) (s t : Finset α) : insert a s union t = insert a (s union t) := by
  simp only [insert_eq, union_assoc]

@[simp, grind =]
/--
theorem `union_insert` / 定理 `union_insert`

English:
theorem union_insert
  given: (a : α) (s t : Finset α)
  statement: s union insert a t = insert a (s union t)
  proof: by
  simp only [insert_eq, union_left_comm]

中文:
定理 union_insert
  条件: (a : α) (s t : Finset α)
  结论: s union insert a t = insert a (s union t)
  证明: by
  simp only [insert_eq, union_left_comm]

Depends on / 依赖: insert_eq, union_left_comm
-/
theorem union_insert (a : α) (s t : Finset α) : s union insert a t = insert a (s union t) := by
  simp only [insert_eq, union_left_comm]

/--
theorem `insert_union_distrib` / 定理 `insert_union_distrib`

English:
theorem insert_union_distrib
  given: (a : α) (s t : Finset α)
  proof: by
  simp only [insert_union, union_insert, insert_idem]

中文:
定理 insert_union_distrib
  条件: (a : α) (s t : Finset α)
  证明: by
  simp only [insert_union, union_insert, insert_idem]

Depends on / 依赖: insert_idem, insert_union, union_insert
-/
theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s union t) = insert a s union insert a t := by
  simp only [insert_union, union_insert, insert_idem]

/--
theorem `induction_on_union` / 定理 `induction_on_union`

English:
theorem induction_on_union
  statement: (P : Finset α -> Finset α -> Prop) (symm : forall {a b}, P a b -> P b a)
  proof: by
  intro a b
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

中文:
定理 induction_on_union
  结论: (P : Finset α -> Finset α -> 命题) (symm : 对任意 {a b}, P a b -> P b a)
  证明: by
  intro a b
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

Depends on / 依赖: Finset, Finset.induction_on, Finset.insert_eq, empty_right, induction_on, insert_eq, singletons, union_of
-/
theorem induction_on_union (P : Finset α -> Finset α -> Prop) (symm : forall {a b}, P a b -> P b a)
    (empty_right : forall {a}, P a ∅) (singletons : forall {a b}, P {a} {b})
    (union_of : forall {a b c}, P a c -> P b c -> P (a union b) c) : forall a b, P a b := by
  intro a b
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

/-! #### inter -/

@[simp]
/--
theorem `inter_empty` / 定理 `inter_empty`

English:
theorem inter_empty
  given: (s : Finset α)
  statement: s inter ∅ = ∅
  proof: ext fun _ => mem_inter.trans by simp

@[simp]

中文:
定理 inter_empty
  条件: (s : Finset α)
  结论: s inter ∅ = ∅
  证明: ext fun _ => mem_inter.trans by simp

@[simp]

Depends on / 依赖: mem_inter, mem_inter.trans
-/
theorem inter_empty (s : Finset α) : s inter ∅ = ∅ :=
ext fun _ => mem_inter.trans by simp

@[simp]
/--
theorem `empty_inter` / 定理 `empty_inter`

English:
theorem empty_inter
  given: (s : Finset α)
  statement: ∅ inter s = ∅
  proof: ext fun _ => mem_inter.trans by simp

@[simp]

中文:
定理 empty_inter
  条件: (s : Finset α)
  结论: ∅ inter s = ∅
  证明: ext fun _ => mem_inter.trans by simp

@[simp]

Depends on / 依赖: mem_inter, mem_inter.trans
-/
theorem empty_inter (s : Finset α) : ∅ inter s = ∅ :=
ext fun _ => mem_inter.trans by simp

@[simp]
/--
theorem `insert_inter_of_mem` / 定理 `insert_inter_of_mem`

English:
theorem insert_inter_of_mem
  given: {s₁ s₂ : Finset α} {a : α} (h : a in s₂)
  proof: ext fun x => by
have : x = a ∨ x in s₂ ↔ x in s₂ := or_iff_right_of_imp by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]

@[simp]

中文:
定理 insert_inter_of_mem
  条件: {s₁ s₂ : Finset α} {a : α} (h : a in s₂)
  证明: ext fun x => by
have : x = a ∨ x in s₂ ↔ x in s₂ := or_iff_right_of_imp by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]

@[simp]

Depends on / 依赖: mem_insert, mem_inter, or_and_left, or_iff_right_of_imp
-/
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a in s₂) :
    insert a s₁ inter s₂ = insert a (s₁ inter s₂) :=
  ext fun x => by
have : x = a ∨ x in s₂ ↔ x in s₂ := or_iff_right_of_imp by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]

@[simp]
/--
theorem `inter_insert_of_mem` / 定理 `inter_insert_of_mem`

English:
theorem inter_insert_of_mem
  given: {s₁ s₂ : Finset α} {a : α} (h : a in s₁)
  proof: by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]

中文:
定理 inter_insert_of_mem
  条件: {s₁ s₂ : Finset α} {a : α} (h : a in s₁)
  证明: by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]

Depends on / 依赖: insert_inter_of_mem, inter_comm
-/
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a in s₁) :
    s₁ inter insert a s₂ = insert a (s₁ inter s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]
/--
theorem `insert_inter_of_notMem` / 定理 `insert_inter_of_notMem`

English:
theorem insert_inter_of_notMem
  given: {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂)
  proof: ext fun x => by
    have : ¬(x = a ∧ x in s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or]

@[simp]

中文:
定理 insert_inter_of_notMem
  条件: {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂)
  证明: ext fun x => by
    have : ¬(x = a ∧ x in s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or]

@[simp]

Depends on / 依赖: false_or, mem_insert, mem_inter, or_and_right
-/
theorem insert_inter_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ inter s₂ = s₁ inter s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x in s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or]

@[simp]
/--
theorem `inter_insert_of_notMem` / 定理 `inter_insert_of_notMem`

English:
theorem inter_insert_of_notMem
  given: {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁)
  proof: by rw [inter_comm, insert_inter_of_notMem h, inter_comm]

@[grind =]

中文:
定理 inter_insert_of_notMem
  条件: {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁)
  证明: by rw [inter_comm, insert_inter_of_notMem h, inter_comm]

@[grind =]

Depends on / 依赖: insert_inter_of_notMem, inter_comm
-/
theorem inter_insert_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ inter insert a s₂ = s₁ inter s₂ := by rw [inter_comm, insert_inter_of_notMem h, inter_comm]

@[grind =]
/--
theorem `inter_insert` / 定理 `inter_insert`

English:
theorem inter_insert
  given: {s₁ s₂ : Finset α} {a : α}
  proof: by
  split_ifs <;> simp [*]

@[grind =]

中文:
定理 inter_insert
  条件: {s₁ s₂ : Finset α} {a : α}
  证明: by
  split_ifs <;> simp [*]

@[grind =]

Depends on / 依赖: split_ifs
-/
theorem inter_insert {s₁ s₂ : Finset α} {a : α} :
    insert a s₁ inter s₂ = if a in s₂ then insert a (s₁ inter s₂) else s₁ inter s₂ := by
  split_ifs <;> simp [*]

@[grind =]
/--
theorem `insert_inter` / 定理 `insert_inter`

English:
theorem insert_inter
  given: {s₁ s₂ : Finset α} {a : α}
  proof: by
  split_ifs <;> simp [*]

@[simp]

中文:
定理 insert_inter
  条件: {s₁ s₂ : Finset α} {a : α}
  证明: by
  split_ifs <;> simp [*]

@[simp]

Depends on / 依赖: split_ifs
-/
theorem insert_inter {s₁ s₂ : Finset α} {a : α} :
    s₁ inter insert a s₂ = if a in s₁ then insert a (s₁ inter s₂) else s₁ inter s₂ := by
  split_ifs <;> simp [*]

@[simp]
/--
theorem `singleton_inter_of_mem` / 定理 `singleton_inter_of_mem`

English:
theorem singleton_inter_of_mem
  given: {a : α} {s : Finset α} (H : a in s)
  statement: {a} inter s = {a}
  proof: show insert a ∅ inter s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]

@[simp]

中文:
定理 singleton_inter_of_mem
  条件: {a : α} {s : Finset α} (H : a in s)
  结论: {a} inter s = {a}
  证明: show insert a ∅ inter s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]

@[simp]

Depends on / 依赖: empty_inter, insert, insert_inter_of_mem
-/
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a in s) : {a} inter s = {a} :=
  show insert a ∅ inter s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]

@[simp]
/--
theorem `singleton_inter_of_notMem` / 定理 `singleton_inter_of_notMem`

English:
theorem singleton_inter_of_notMem
  given: {a : α} {s : Finset α} (H : a ∉ s)
  statement: {a} inter s = ∅
  proof: eq_empty_of_forall_notMem by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[grind =]

中文:
定理 singleton_inter_of_notMem
  条件: {a : α} {s : Finset α} (H : a ∉ s)
  结论: {a} inter s = ∅
  证明: eq_empty_of_forall_notMem by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[grind =]

Depends on / 依赖: eq_empty_of_forall_notMem, mem_inter, mem_singleton
-/
theorem singleton_inter_of_notMem {a : α} {s : Finset α} (H : a ∉ s) : {a} inter s = ∅ :=
eq_empty_of_forall_notMem by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[grind =]
/--
lemma `singleton_inter` / 引理 `singleton_inter`

English:
lemma singleton_inter
  given: {a : α} {s : Finset α}
  proof: by
  split_ifs with h <;> simp [h]

@[simp]

中文:
引理 singleton_inter
  条件: {a : α} {s : Finset α}
  证明: by
  split_ifs with h <;> simp [h]

@[simp]

Depends on / 依赖: split_ifs
-/
lemma singleton_inter {a : α} {s : Finset α} :
    {a} inter s = if a in s then {a} else ∅ := by
  split_ifs with h <;> simp [h]

@[simp]
/--
theorem `inter_singleton_of_mem` / 定理 `inter_singleton_of_mem`

English:
theorem inter_singleton_of_mem
  given: {a : α} {s : Finset α} (h : a in s)
  statement: s inter {a} = {a}
  proof: by
  rw [inter_comm]; rw [singleton_inter_of_mem h]

@[simp]

中文:
定理 inter_singleton_of_mem
  条件: {a : α} {s : Finset α} (h : a in s)
  结论: s inter {a} = {a}
  证明: by
  rw [inter_comm]; rw [singleton_inter_of_mem h]

@[simp]

Depends on / 依赖: inter_comm, singleton_inter_of_mem
-/
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a in s) : s inter {a} = {a} := by
  rw [inter_comm]; rw [singleton_inter_of_mem h]

@[simp]
/--
theorem `inter_singleton_of_notMem` / 定理 `inter_singleton_of_notMem`

English:
theorem inter_singleton_of_notMem
  given: {a : α} {s : Finset α} (h : a ∉ s)
  statement: s inter {a} = ∅
  proof: by
  rw [inter_comm]; rw [singleton_inter_of_notMem h]

中文:
定理 inter_singleton_of_notMem
  条件: {a : α} {s : Finset α} (h : a ∉ s)
  结论: s inter {a} = ∅
  证明: by
  rw [inter_comm]; rw [singleton_inter_of_notMem h]

Depends on / 依赖: inter_comm, singleton_inter_of_notMem
-/
theorem inter_singleton_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : s inter {a} = ∅ := by
  rw [inter_comm]; rw [singleton_inter_of_notMem h]

/--
lemma `inter_singleton` / 引理 `inter_singleton`

English:
lemma inter_singleton
  given: {a : α} {s : Finset α}
  proof: by
  split_ifs with h <;> simp [h]

中文:
引理 inter_singleton
  条件: {a : α} {s : Finset α}
  证明: by
  split_ifs with h <;> simp [h]

Depends on / 依赖: split_ifs
-/
lemma inter_singleton {a : α} {s : Finset α} :
    s inter {a} = if a in s then {a} else ∅ := by
  split_ifs with h <;> simp [h]

/--
lemma `union_eq_empty` / 引理 `union_eq_empty`

English:
lemma union_eq_empty
  statement: s union t = ∅ ↔ s = ∅ ∧ t = ∅
  proof: sup_eq_bot_iff

中文:
引理 union_eq_empty
  结论: s union t = ∅ ↔ s = ∅ ∧ t = ∅
  证明: sup_eq_bot_iff
-/
@[simp] lemma union_eq_empty : s union t = ∅ ↔ s = ∅ ∧ t = ∅ := sup_eq_bot_iff
/--
lemma `union_nonempty` / 引理 `union_nonempty`

English:
lemma union_nonempty
  statement: (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty
  proof: mod_cast Set.union_nonempty (α := α) (s := s) (t := t)

中文:
引理 union_nonempty
  结论: (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty
  证明: mod_cast Set.union_nonempty (α := α) (s := s) (t := t)
-/
@[simp] lemma union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  mod_cast Set.union_nonempty (α := α) (s := s) (t := t)

/--
theorem `insert_union_comm` / 定理 `insert_union_comm`

English:
theorem insert_union_comm
  given: (s t : Finset α) (a : α)
  statement: insert a s union t = s union insert a t
  proof: by
  rw [insert_union]; rw [union_insert]

中文:
定理 insert_union_comm
  条件: (s t : Finset α) (a : α)
  结论: insert a s union t = s union insert a t
  证明: by
  rw [insert_union]; rw [union_insert]

Depends on / 依赖: insert_union, union_insert
-/
theorem insert_union_comm (s t : Finset α) (a : α) : insert a s union t = s union insert a t := by
  rw [insert_union]; rw [union_insert]

end Lattice

end Finset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
/--
theorem `toFinset_append` / 定理 `toFinset_append`

English:
theorem toFinset_append
  statement: toFinset (l ++ l') = l.toFinset union l'.toFinset
  proof: by
  induction l with
  | nil => simp
  | cons hd tl hl => simp [hl]

中文:
定理 toFinset_append
  结论: toFinset (l ++ l') = l.toFinset union l'.toFinset
  证明: by
  induction l with
  | nil => simp
  | cons hd tl hl => simp [hl]
-/
theorem toFinset_append : toFinset (l ++ l') = l.toFinset union l'.toFinset := by
  induction l with
  | nil => simp
  | cons hd tl hl => simp [hl]

end List
