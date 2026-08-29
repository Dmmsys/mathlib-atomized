/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Util.Delaborators

/-!
# Constructing finite sets by adding one element

This file contains the definitions of `{a} : Finset α`, `insert a s : Finset α` and `Finset.cons`,
all ways to construct a `Finset` by adding one element.

## Main declarations

* `Finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `Finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `Finset α`,
  then it holds for the finset obtained by inserting a new element.
* `Finset.instSingletonFinset`: Denoted by `{a}`; the finset consisting of one element.
* `insert` and `Finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*}

namespace Finset

/-! ### Subset and strict subset relations -/

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### singleton -/


section Singleton

variable {s : Finset α} {a b : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton α (Finset α)
  body: ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]

中文:
实例 :
  签名: 单例 α (有限集 α)
  定义体: ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]

Depends on / 依赖: nodup_singleton
-/
instance : Singleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
/--
theorem `singleton_val` / 定理 `singleton_val`

English:
theorem singleton_val
  given: (a : α)
  statement: ({a} : Finset α).1 = {a}
  proof: rfl

@[simp, grind =]

中文:
定理 singleton_val
  条件: (a : α)
  结论: ({a} : 有限集 α).1 = {a}
  证明: rfl

@[simp, grind =]
-/
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl

@[simp, grind =]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: {a b : α}
  statement: b in ({a} : Finset α) ↔ b = a
  proof: Multiset.mem_singleton

中文:
定理 mem_singleton
  条件: {a b : α}
  结论: b in ({a} : 有限集 α) ↔ b = a
  证明: Multiset.mem_singleton

Depends on / 依赖: Multiset, Multiset.mem_singleton, mem_singleton
-/
theorem mem_singleton {a b : α} : b in ({a} : Finset α) ↔ b = a :=
  Multiset.mem_singleton

/--
theorem `eq_of_mem_singleton` / 定理 `eq_of_mem_singleton`

English:
theorem eq_of_mem_singleton
  given: {x y : α} (h : x in ({y} : Finset α))
  statement: x = y
  proof: mem_singleton.1 h

中文:
定理 eq_of_mem_singleton
  条件: {x y : α} (h : x in ({y} : 有限集 α))
  结论: x = y
  证明: mem_singleton.1 h

Depends on / 依赖: mem_singleton
-/
theorem eq_of_mem_singleton {x y : α} (h : x in ({y} : Finset α)) : x = y :=
  mem_singleton.1 h

/--
theorem `notMem_singleton` / 定理 `notMem_singleton`

English:
theorem notMem_singleton
  given: {a b : α}
  statement: a ∉ ({b} : Finset α) ↔ a != b
  proof: not_congr mem_singleton

中文:
定理 notMem_singleton
  条件: {a b : α}
  结论: a ∉ ({b} : 有限集 α) ↔ a != b
  证明: not_congr mem_singleton

Depends on / 依赖: mem_singleton, not_congr
-/
theorem notMem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a != b :=
  not_congr mem_singleton

/--
theorem `mem_singleton_self` / 定理 `mem_singleton_self`

English:
theorem mem_singleton_self
  given: (a : α)
  statement: a in ({a} : Finset α)
  proof: mem_singleton.mpr rfl

@[simp]

中文:
定理 mem_singleton_self
  条件: (a : α)
  结论: a in ({a} : 有限集 α)
  证明: mem_singleton.mpr rfl

@[simp]

Depends on / 依赖: mem_singleton, mem_singleton.mpr
-/
theorem mem_singleton_self (a : α) : a in ({a} : Finset α) :=
  mem_singleton.mpr rfl

@[simp]
/--
theorem `val_eq_singleton_iff` / 定理 `val_eq_singleton_iff`

English:
theorem val_eq_singleton_iff
  given: {a : α} {s : Finset α}
  statement: s.val = {a} ↔ s = {a}
  proof: by
  rw [← val_inj]
  rfl

中文:
定理 val_eq_singleton_iff
  条件: {a : α} {s : 有限集 α}
  结论: s.val = {a} ↔ s = {a}
  证明: by
  rw [← val_inj]
  rfl

Depends on / 依赖: val_inj
-/
theorem val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a} := by
  rw [← val_inj]
  rfl

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Injective (singleton : α -> Finset α)
  proof: fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp]

中文:
定理 singleton_injective
  结论: 单射 (singleton : α -> 有限集 α)
  证明: fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp]
-/
theorem singleton_injective : Injective (singleton : α -> Finset α) := fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  statement: ({a} : Finset α) = {b} ↔ a = b
  proof: singleton_injective.eq_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 singleton_inj
  结论: ({a} : 有限集 α) = {b} ↔ a = b
  证明: singleton_injective.eq_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `singleton_nonempty` / 定理 `singleton_nonempty`

English:
theorem singleton_nonempty
  given: (a : α)
  statement: ({a} : Finset α).Nonempty
  proof: ⟨a, mem_singleton_self a⟩

@[simp]

中文:
定理 singleton_nonempty
  条件: (a : α)
  结论: ({a} : 有限集 α).非空
  证明: ⟨a, mem_singleton_self a⟩

@[simp]

Depends on / 依赖: mem_singleton_self
-/
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩

@[simp]
/--
theorem `singleton_ne_empty` / 定理 `singleton_ne_empty`

English:
theorem singleton_ne_empty
  given: (a : α)
  statement: ({a} : Finset α) != ∅
  proof: (singleton_nonempty a).ne_empty

@[simp]

中文:
定理 singleton_ne_empty
  条件: (a : α)
  结论: ({a} : 有限集 α) != ∅
  证明: (singleton_nonempty a).ne_empty

@[simp]

Depends on / 依赖: ne_empty, singleton_nonempty
-/
theorem singleton_ne_empty (a : α) : ({a} : Finset α) != ∅ :=
  (singleton_nonempty a).ne_empty

@[simp]
/--
theorem `empty_ne_singleton` / 定理 `empty_ne_singleton`

English:
theorem empty_ne_singleton
  given: (a : α)
  statement: ∅ != ({a} : Finset α)
  proof: (singleton_ne_empty a).symm

中文:
定理 empty_ne_singleton
  条件: (a : α)
  结论: ∅ != ({a} : 有限集 α)
  证明: (singleton_ne_empty a).symm

Depends on / 依赖: singleton_ne_empty
-/
theorem empty_ne_singleton (a : α) : ∅ != ({a} : Finset α) :=
  (singleton_ne_empty a).symm

/--
theorem `empty_ssubset_singleton` / 定理 `empty_ssubset_singleton`

English:
theorem empty_ssubset_singleton
  statement: (∅ : Finset α) ⊂ {a}
  proof: (singleton_nonempty _).empty_ssubset

@[simp, norm_cast]

中文:
定理 empty_ssubset_singleton
  结论: (∅ : 有限集 α) ⊂ {a}
  证明: (singleton_nonempty _).empty_ssubset

@[simp, norm_cast]

Depends on / 依赖: empty_ssubset, singleton_nonempty
-/
theorem empty_ssubset_singleton : (∅ : Finset α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, norm_cast]
/--
theorem `coe_singleton` / 定理 `coe_singleton`

English:
theorem coe_singleton
  given: (a : α)
  statement: (({a} : Finset α) : Set α) = {a}
  proof: by grind

@[simp, norm_cast]

中文:
定理 coe_singleton
  条件: (a : α)
  结论: (({a} : 有限集 α) : 集合 α) = {a}
  证明: by grind

@[simp, norm_cast]
-/
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} := by grind

@[simp, norm_cast]
/--
theorem `coe_eq_singleton` / 定理 `coe_eq_singleton`

English:
theorem coe_eq_singleton
  given: {s : Finset α} {a : α}
  statement: (s : Set α) = {a} ↔ s = {a}
  proof: by grind

@[norm_cast]

中文:
定理 coe_eq_singleton
  条件: {s : 有限集 α} {a : α}
  结论: (s : 集合 α) = {a} ↔ s = {a}
  证明: by grind

@[norm_cast]
-/
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by grind

@[norm_cast]
/--
lemma `coe_subset_singleton` / 引理 `coe_subset_singleton`

English:
lemma coe_subset_singleton
  statement: (s : Set α) subseteq {a} ↔ s subseteq {a}
  proof: by grind

@[norm_cast]

中文:
引理 coe_subset_singleton
  结论: (s : 集合 α) subseteq {a} ↔ s subseteq {a}
  证明: by grind

@[norm_cast]
-/
lemma coe_subset_singleton : (s : Set α) subseteq {a} ↔ s subseteq {a} := by grind

@[norm_cast]
/--
lemma `singleton_subset_coe` / 引理 `singleton_subset_coe`

English:
lemma singleton_subset_coe
  statement: {a} subseteq (s : Set α) ↔ {a} subseteq s
  proof: by grind

中文:
引理 singleton_subset_coe
  结论: {a} subseteq (s : 集合 α) ↔ {a} subseteq s
  证明: by grind
-/
lemma singleton_subset_coe : {a} subseteq (s : Set α) ↔ {a} subseteq s := by grind

/--
theorem `eq_singleton_iff_unique_mem` / 定理 `eq_singleton_iff_unique_mem`

English:
theorem eq_singleton_iff_unique_mem
  given: {s : Finset α} {a : α}
  statement: s = {a} ↔ a in s ∧ forall x in s, x = a
  proof: by
  grind

中文:
定理 eq_singleton_iff_unique_mem
  条件: {s : 有限集 α} {a : α}
  结论: s = {a} ↔ a in s ∧ 对任意 x in s, x = a
  证明: by
  grind
-/
theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a := by
  grind

/--
theorem `eq_singleton_iff_nonempty_unique_mem` / 定理 `eq_singleton_iff_nonempty_unique_mem`

English:
theorem eq_singleton_iff_nonempty_unique_mem
  given: {s : Finset α} {a : α}
  proof: by
  grind [singleton_nonempty]

中文:
定理 eq_singleton_iff_nonempty_unique_mem
  条件: {s : 有限集 α} {a : α}
  证明: by
  grind [singleton_nonempty]

Depends on / 依赖: singleton_nonempty
-/
theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ forall x in s, x = a := by
  grind [singleton_nonempty]

/--
theorem `nonempty_iff_eq_singleton_default` / 定理 `nonempty_iff_eq_singleton_default`

English:
theorem nonempty_iff_eq_singleton_default
  given: [Unique α] {s : Finset α}
  proof: by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default

中文:
定理 nonempty_iff_eq_singleton_default
  条件: [唯一 α] {s : 有限集 α}
  证明: by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default

Depends on / 依赖: eq_iff_true_of_subsingleton, eq_singleton_iff_nonempty_unique_mem
-/
theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} :
    s.Nonempty ↔ s = {default} := by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default

/--
theorem `singleton_iff_unique_mem` / 定理 `singleton_iff_unique_mem`

English:
theorem singleton_iff_unique_mem
  given: (s : Finset α)
  statement: (exists a, s = {a}) ↔ exists! a, a in s
  proof: by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]

中文:
定理 singleton_iff_unique_mem
  条件: (s : 有限集 α)
  结论: (存在 a, s = {a}) ↔ 存在! a, a in s
  证明: by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]

Depends on / 依赖: ExistsUnique, eq_singleton_iff_unique_mem
-/
theorem singleton_iff_unique_mem (s : Finset α) : (exists a, s = {a}) ↔ exists! a, a in s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]

/--
theorem `singleton_subset_set_iff` / 定理 `singleton_subset_set_iff`

English:
theorem singleton_subset_set_iff
  given: {s : Set α} {a : α}
  statement: ↑({a} : Finset α) subseteq s ↔ a in s
  proof: by
  grind

@[simp, grind =]

中文:
定理 singleton_subset_set_iff
  条件: {s : 集合 α} {a : α}
  结论: ↑({a} : 有限集 α) subseteq s ↔ a in s
  证明: by
  grind

@[simp, grind =]
-/
theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) subseteq s ↔ a in s := by
  grind

@[simp, grind =]
/--
theorem `singleton_subset_iff` / 定理 `singleton_subset_iff`

English:
theorem singleton_subset_iff
  given: {s : Finset α} {a : α}
  statement: {a} subseteq s ↔ a in s
  proof: singleton_subset_set_iff

@[simp]

中文:
定理 singleton_subset_iff
  条件: {s : 有限集 α} {a : α}
  结论: {a} subseteq s ↔ a in s
  证明: singleton_subset_set_iff

@[simp]

Depends on / 依赖: singleton_subset_set_iff
-/
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} subseteq s ↔ a in s :=
  singleton_subset_set_iff

@[simp]
/--
theorem `subset_singleton_iff` / 定理 `subset_singleton_iff`

English:
theorem subset_singleton_iff
  given: {s : Finset α} {a : α}
  statement: s subseteq {a} ↔ s = ∅ ∨ s = {a}
  proof: by
  grind

中文:
定理 subset_singleton_iff
  条件: {s : 有限集 α} {a : α}
  结论: s subseteq {a} ↔ s = ∅ ∨ s = {a}
  证明: by
  grind
-/
theorem subset_singleton_iff {s : Finset α} {a : α} : s subseteq {a} ↔ s = ∅ ∨ s = {a} := by
  grind

/--
theorem `singleton_subset_singleton` / 定理 `singleton_subset_singleton`

English:
theorem singleton_subset_singleton
  statement: ({a} : Finset α) subseteq {b} ↔ a = b
  proof: by simp

中文:
定理 singleton_subset_singleton
  结论: ({a} : 有限集 α) subseteq {b} ↔ a = b
  证明: by simp
-/
theorem singleton_subset_singleton : ({a} : Finset α) subseteq {b} ↔ a = b := by simp

/--
theorem `Nonempty.subset_singleton_iff` / 定理 `Nonempty.subset_singleton_iff`

English:
theorem Nonempty.subset_singleton_iff
  given: {s : Finset α} {a : α} (h : s.Nonempty)
  proof: subset_singleton_iff.trans or_iff_right h.ne_empty

中文:
定理 非空.subset_singleton_iff
  条件: {s : 有限集 α} {a : α} (h : s.非空)
  证明: subset_singleton_iff.trans or_iff_right h.ne_empty
-/
protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) :
    s subseteq {a} ↔ s = {a} :=
subset_singleton_iff.trans or_iff_right h.ne_empty

/--
theorem `subset_singleton_iff'` / 定理 `subset_singleton_iff'`

English:
theorem subset_singleton_iff'
  given: {s : Finset α} {a : α}
  statement: s subseteq {a} ↔ forall b in s, b = a
  proof: forall₂_congr fun _ _ => mem_singleton

@[simp]

中文:
定理 subset_singleton_iff'
  条件: {s : 有限集 α} {a : α}
  结论: s subseteq {a} ↔ 对任意 b in s, b = a
  证明: forall₂_congr fun _ _ => mem_singleton

@[simp]

Depends on / 依赖: mem_singleton
-/
theorem subset_singleton_iff' {s : Finset α} {a : α} : s subseteq {a} ↔ forall b in s, b = a :=
  forall₂_congr fun _ _ => mem_singleton

@[simp]
/--
theorem `ssubset_singleton_iff` / 定理 `ssubset_singleton_iff`

English:
theorem ssubset_singleton_iff
  given: {s : Finset α} {a : α}
  statement: s ⊂ {a} ↔ s = ∅
  proof: by grind

中文:
定理 ssubset_singleton_iff
  条件: {s : 有限集 α} {a : α}
  结论: s ⊂ {a} ↔ s = ∅
  证明: by grind
-/
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by grind

/--
theorem `eq_empty_of_ssubset_singleton` / 定理 `eq_empty_of_ssubset_singleton`

English:
theorem eq_empty_of_ssubset_singleton
  given: {s : Finset α} {x : α} (hs : s ⊂ {x})
  statement: s = ∅
  proof: ssubset_singleton_iff.1 hs

中文:
定理 eq_empty_of_ssubset_singleton
  条件: {s : 有限集 α} {x : α} (hs : s ⊂ {x})
  结论: s = ∅
  证明: ssubset_singleton_iff.1 hs

Depends on / 依赖: ssubset_singleton_iff
-/
theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/--
Definition of `Nontrivial` / `Nontrivial` 的定义

English:
abbreviation Nontrivial
  signature: (s : Finset α)
  body: (s : Set α).Nontrivial

@[grind =]

中文:
缩写 非平凡
  签名: (s : 有限集 α)
  定义体: (s : Set α).Nontrivial

@[grind =]
-/
protected abbrev Nontrivial (s : Finset α) : Prop := (s : Set α).Nontrivial

@[grind =]
/--
theorem `nontrivial_def` / 定理 `nontrivial_def`

English:
theorem nontrivial_def
  given: {s : Finset α}
  statement: s.Nontrivial ↔ exists a, a in s ∧ exists b, b in s ∧ a != b
  proof: Iff.rfl

nonrec lemma Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty := hs.nonempty

@[simp]

中文:
定理 nontrivial_def
  条件: {s : 有限集 α}
  结论: s.非平凡 ↔ 存在 a, a in s ∧ 存在 b, b in s ∧ a != b
  证明: Iff.rfl

nonrec lemma Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty := hs.nonempty

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem nontrivial_def {s : Finset α} : s.Nontrivial ↔ exists a, a in s ∧ exists b, b in s ∧ a != b := Iff.rfl

nonrec lemma Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty := hs.nonempty

@[simp]
/--
theorem `not_nontrivial_empty` / 定理 `not_nontrivial_empty`

English:
theorem not_nontrivial_empty
  statement: ¬(∅ : Finset α).Nontrivial
  proof: by simp [Finset.Nontrivial]

@[simp]

中文:
定理 not_nontrivial_empty
  结论: ¬(∅ : 有限集 α).非平凡
  证明: by simp [Finset.Nontrivial]

@[simp]

Depends on / 依赖: Finset, Finset.Nontrivial, Nontrivial
-/
theorem not_nontrivial_empty : ¬(∅ : Finset α).Nontrivial := by simp [Finset.Nontrivial]

@[simp]
/--
theorem `not_nontrivial_singleton` / 定理 `not_nontrivial_singleton`

English:
theorem not_nontrivial_singleton
  statement: ¬({a} : Finset α).Nontrivial
  proof: by simp [Finset.Nontrivial]

中文:
定理 not_nontrivial_singleton
  结论: ¬({a} : 有限集 α).非平凡
  证明: by simp [Finset.Nontrivial]

Depends on / 依赖: Finset, Finset.Nontrivial, Nontrivial
-/
theorem not_nontrivial_singleton : ¬({a} : Finset α).Nontrivial := by simp [Finset.Nontrivial]

/--
theorem `Nontrivial.ne_singleton` / 定理 `Nontrivial.ne_singleton`

English:
theorem Nontrivial.ne_singleton
  given: (hs : s.Nontrivial)
  statement: s != {a}
  proof: by
  rintro rfl; exact not_nontrivial_singleton hs

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : exists b in s, b != a := hs.exists_ne _

中文:
定理 非平凡.ne_singleton
  条件: (hs : s.非平凡)
  结论: s != {a}
  证明: by
  rintro rfl; exact not_nontrivial_singleton hs

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : exists b in s, b != a := hs.exists_ne _

Depends on / 依赖: not_nontrivial_singleton
-/
theorem Nontrivial.ne_singleton (hs : s.Nontrivial) : s != {a} := by
  rintro rfl; exact not_nontrivial_singleton hs

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : exists b in s, b != a := hs.exists_ne _

/--
theorem `eq_singleton_or_nontrivial` / 定理 `eq_singleton_or_nontrivial`

English:
theorem eq_singleton_or_nontrivial
  given: (ha : a in s)
  statement: s = {a} ∨ s.Nontrivial
  proof: by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha

中文:
定理 eq_singleton_or_nontrivial
  条件: (ha : a in s)
  结论: s = {a} ∨ s.非平凡
  证明: by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha

Depends on / 依赖: Set.eq_singleton_or_nontrivial, coe_eq_singleton, eq_singleton_or_nontrivial
-/
theorem eq_singleton_or_nontrivial (ha : a in s) : s = {a} ∨ s.Nontrivial := by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha

/--
theorem `nontrivial_iff_ne_singleton` / 定理 `nontrivial_iff_ne_singleton`

English:
theorem nontrivial_iff_ne_singleton
  given: (ha : a in s)
  statement: s.Nontrivial ↔ s != {a}
  proof: ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

中文:
定理 nontrivial_iff_ne_singleton
  条件: (ha : a in s)
  结论: s.非平凡 ↔ s != {a}
  证明: ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

Depends on / 依赖: Nontrivial, Nontrivial.ne_singleton, eq_singleton_or_nontrivial, ne_singleton, resolve_left
-/
theorem nontrivial_iff_ne_singleton (ha : a in s) : s.Nontrivial ↔ s != {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

/--
theorem `Nonempty.exists_eq_singleton_or_nontrivial` / 定理 `Nonempty.exists_eq_singleton_or_nontrivial`

English:
theorem Nonempty.exists_eq_singleton_or_nontrivial
  statement: s.Nonempty -> (exists a, s = {a}) ∨ s.Nontrivial
  proof: fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a

中文:
定理 非空.存在_eq_singleton_or_nontrivial
  结论: s.非空 -> (存在 a, s = {a}) ∨ s.非平凡
  证明: fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a

Depends on / 依赖: Exists, Exists.intro, eq_singleton_or_nontrivial, imp_left
-/
theorem Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty -> (exists a, s = {a}) ∨ s.Nontrivial :=
fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a

/--
lemma `nontrivial_coe` / 引理 `nontrivial_coe`

English:
lemma nontrivial_coe
  statement: (s : Set α).Nontrivial ↔ s.Nontrivial
  proof: .rfl

alias ⟨Nontrivial.of_coe, Nontrivial.coe⟩ := nontrivial_coe

中文:
引理 nontrivial_coe
  结论: (s : 集合 α).非平凡 ↔ s.非平凡
  证明: .rfl

alias ⟨Nontrivial.of_coe, Nontrivial.coe⟩ := nontrivial_coe
-/
@[simp, norm_cast] lemma nontrivial_coe : (s : Set α).Nontrivial ↔ s.Nontrivial := .rfl

alias ⟨Nontrivial.of_coe, Nontrivial.coe⟩ := nontrivial_coe

/--
lemma `Nontrivial.not_subset_singleton` / 引理 `Nontrivial.not_subset_singleton`

English:
lemma Nontrivial.not_subset_singleton
  given: (hs : s.Nontrivial)
  statement: ¬s subseteq {a}
  proof: mod_cast hs.coe.not_subset_singleton

中文:
引理 非平凡.not_subset_singleton
  条件: (hs : s.非平凡)
  结论: ¬s subseteq {a}
  证明: mod_cast hs.coe.not_subset_singleton

Depends on / 依赖: hs.coe.not_subset_singleton, mod_cast, not_subset_singleton
-/
lemma Nontrivial.not_subset_singleton (hs : s.Nontrivial) : ¬s subseteq {a} :=
  mod_cast hs.coe.not_subset_singleton

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nonempty α]
  body: ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

中文:
实例 instNontrivial
  签名: [非空 α]
  定义体: ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

Depends on / 依赖: Nonempty, singleton_ne_empty
-/
instance instNontrivial [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Finset α) where
  body: ∅
  uniq _ := eq_empty_of_forall_notMem isEmptyElim

中文:
实例 [是空
  签名: α] : 唯一 (有限集 α) where
  定义体: ∅
  uniq _ := eq_empty_of_forall_notMem isEmptyElim
-/
instance [IsEmpty α] : Unique (Finset α) where
  default := ∅
  uniq _ := eq_empty_of_forall_notMem isEmptyElim

instance (i : α) : Unique ({i} : Finset α) where
  default := ⟨i, mem_singleton_self i⟩
uniq j := Subtype.ext mem_singleton.mp j.2

@[simp]
/--
lemma `default_singleton` / 引理 `default_singleton`

English:
lemma default_singleton
  given: (i : α)
  statement: ((default : ({i} : Finset α)) : α) = i
  proof: rfl

中文:
引理 default_singleton
  条件: (i : α)
  结论: ((default : ({i} : 有限集 α)) : α) = i
  证明: rfl
-/
lemma default_singleton (i : α) : ((default : ({i} : Finset α)) : α) = i := rfl

/--
Instance `Nontrivial.instDecidablePred` / 实例 `Nontrivial.instDecidablePred`

English:
instance Nontrivial.instDecidablePred
  signature: : DecidablePred (Finset.Nontrivial (α := α))
  body: fun s =>
  /-
  We don't use `Finset.one_lt_card_iff_nontrivial`
  because `Finset.card` is defined in a different file.
  -/
  Quotient.recOnSubsingleton (motive := fun (s : Multiset α) =>
      (h : s.Nodup) -> Decidable (Finset.Nontrivial ⟨s, h⟩))
    s.val (fun l h => match l with
      | [] => 

中文:
实例 非平凡.instDecidablePred
  签名: : DecidablePred (有限集.非平凡 (α := α))
  定义体: fun s =>
  /-
  We don't use `Finset.one_lt_card_iff_nontrivial`
  because `Finset.card` is defined in a different file.
  -/
  Quotient.recOnSubsingleton (motive := fun (s : Multiset α) =>
      (h : s.Nodup) -> Decidable (Finset.Nontrivial ⟨s, h⟩))
    s.val (fun l h => match l with
      | [] => 
-/
instance Nontrivial.instDecidablePred : DecidablePred (Finset.Nontrivial (α := α)) := fun s =>
  /-
  We don't use `Finset.one_lt_card_iff_nontrivial`
  because `Finset.card` is defined in a different file.
  -/
  Quotient.recOnSubsingleton (motive := fun (s : Multiset α) =>
      (h : s.Nodup) -> Decidable (Finset.Nontrivial ⟨s, h⟩))
    s.val (fun l h => match l with
      | [] => isFalse (by simp)
      | [_] => isFalse (by simp [SetLike.coe])
      | a :: b :: _ => isTrue ⟨a, by simp, b, by simp,
        List.ne_of_not_mem_cons (List.nodup_cons.mp h).left⟩) s.nodup

end Singleton

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (s : Finset α) (h : a ∉ s)
  body: ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp, grind =]

中文:
定义 cons
  签名: (a : α) (s : 有限集 α) (h : a ∉ s)
  定义体: ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp, grind =]

Depends on / 依赖: nodup_cons
-/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp, grind =]
/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: {h}
  statement: b in s.cons a h ↔ b = a ∨ b in s
  proof: Multiset.mem_cons

中文:
定理 mem_cons
  条件: {h}
  结论: b in s.cons a h ↔ b = a ∨ b in s
  证明: Multiset.mem_cons

Depends on / 依赖: Multiset, Multiset.mem_cons, mem_cons
-/
theorem mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s :=
  Multiset.mem_cons

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a in s)
  statement: a in cons b s hb
  proof: Multiset.mem_cons_of_mem ha

中文:
定理 mem_cons_of_mem
  条件: {a b : α} {s : 有限集 α} {hb : b ∉ s} (ha : a in s)
  结论: a in cons b s hb
  证明: Multiset.mem_cons_of_mem ha

Depends on / 依赖: Multiset, Multiset.mem_cons_of_mem, mem_cons_of_mem
-/
theorem mem_cons_of_mem {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a in s) : a in cons b s hb :=
  Multiset.mem_cons_of_mem ha

/--
theorem `mem_cons_self` / 定理 `mem_cons_self`

English:
theorem mem_cons_self
  given: (a : α) (s : Finset α) {h}
  statement: a in cons a s h
  proof: Multiset.mem_cons_self _ _

@[simp]

中文:
定理 mem_cons_self
  条件: (a : α) (s : 有限集 α) {h}
  结论: a in cons a s h
  证明: Multiset.mem_cons_self _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_cons_self, mem_cons_self
-/
theorem mem_cons_self (a : α) (s : Finset α) {h} : a in cons a s h :=
  Multiset.mem_cons_self _ _

@[simp]
/--
theorem `cons_val` / 定理 `cons_val`

English:
theorem cons_val
  given: (h : a ∉ s)
  statement: (cons a s h).1 = a ::ₘ s.1
  proof: rfl

中文:
定理 cons_val
  条件: (h : a ∉ s)
  结论: (cons a s h).1 = a ::ₘ s.1
  证明: rfl
-/
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl

/--
theorem `eq_of_mem_cons_of_notMem` / 定理 `eq_of_mem_cons_of_notMem`

English:
theorem eq_of_mem_cons_of_notMem
  given: (has : a ∉ s) (h : b in cons a s has) (hb : b ∉ s)
  statement: b = a
  proof: (mem_cons.1 h).resolve_right hb

中文:
定理 eq_of_mem_cons_of_notMem
  条件: (has : a ∉ s) (h : b in cons a s has) (hb : b ∉ s)
  结论: b = a
  证明: (mem_cons.1 h).resolve_right hb

Depends on / 依赖: mem_cons, resolve_right
-/
theorem eq_of_mem_cons_of_notMem (has : a ∉ s) (h : b in cons a s has) (hb : b ∉ s) : b = a :=
  (mem_cons.1 h).resolve_right hb

/--
theorem `mem_of_mem_cons_of_ne` / 定理 `mem_of_mem_cons_of_ne`

English:
theorem mem_of_mem_cons_of_ne
  statement: {s : Finset α} {a : α} {has} {i : α}
  proof: (mem_cons.1 hi).resolve_left hia

中文:
定理 mem_of_mem_cons_of_ne
  结论: {s : 有限集 α} {a : α} {has} {i : α}
  证明: (mem_cons.1 hi).resolve_left hia

Depends on / 依赖: mem_cons, resolve_left
-/
theorem mem_of_mem_cons_of_ne {s : Finset α} {a : α} {has} {i : α}
    (hi : i in cons a s has) (hia : i != a) : i in s :=
  (mem_cons.1 hi).resolve_left hia

/--
theorem `forall_mem_cons` / 定理 `forall_mem_cons`

English:
theorem forall_mem_cons
  given: (h : a ∉ s) (p : α -> Prop)
  proof: by
  grind

中文:
定理 对任意_mem_cons
  条件: (h : a ∉ s) (p : α -> 命题)
  证明: by
  grind
-/
theorem forall_mem_cons (h : a ∉ s) (p : α -> Prop) :
    (forall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x := by
  grind

/--
theorem `forall_of_forall_cons` / 定理 `forall_of_forall_cons`

English:
theorem forall_of_forall_cons
  statement: {p : α -> Prop} {h : a ∉ s} (H : forall x, x in cons a s h -> p x) (x)
  proof: H _ mem_cons.2 Or.inr h

@[simp]

中文:
定理 对任意_of_对任意_cons
  结论: {p : α -> 命题} {h : a ∉ s} (H : 对任意 x, x in cons a s h -> p x) (x)
  证明: H _ mem_cons.2 Or.inr h

@[simp]

Depends on / 依赖: Or.inr, mem_cons
-/
theorem forall_of_forall_cons {p : α -> Prop} {h : a ∉ s} (H : forall x, x in cons a s h -> p x) (x)
    (h : x in s) : p x :=
H _ mem_cons.2 Or.inr h

@[simp]
/--
theorem `mk_cons` / 定理 `mk_cons`

English:
theorem mk_cons
  given: {s : Multiset α} (h : (a ::ₘ s).Nodup)
  proof: rfl

@[simp]

中文:
定理 mk_cons
  条件: {s : Multiset α} (h : (a ::ₘ s).Nodup)
  证明: rfl

@[simp]
-/
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl

@[simp]
/--
theorem `cons_empty` / 定理 `cons_empty`

English:
theorem cons_empty
  given: (a : α)
  statement: cons a ∅ (notMem_empty _) = {a}
  proof: rfl

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 cons_empty
  条件: (a : α)
  结论: cons a ∅ (notMem_empty _) = {a}
  证明: rfl

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem cons_empty (a : α) : cons a ∅ (notMem_empty _) = {a} := rfl

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `cons_nonempty` / 定理 `cons_nonempty`

English:
theorem cons_nonempty
  given: (h : a ∉ s)
  statement: (cons a s h).Nonempty
  proof: ⟨a, mem_cons.2 Or.inl rfl⟩

中文:
定理 cons_nonempty
  条件: (h : a ∉ s)
  结论: (cons a s h).非空
  证明: ⟨a, mem_cons.2 Or.inl rfl⟩

Depends on / 依赖: Or.inl, mem_cons
-/
theorem cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty :=
⟨a, mem_cons.2 Or.inl rfl⟩

/--
theorem `cons_ne_empty` / 定理 `cons_ne_empty`

English:
theorem cons_ne_empty
  given: (h : a ∉ s)
  statement: cons a s h != ∅
  proof: (cons_nonempty _).ne_empty

中文:
定理 cons_ne_empty
  条件: (h : a ∉ s)
  结论: cons a s h != ∅
  证明: (cons_nonempty _).ne_empty
-/
@[simp] theorem cons_ne_empty (h : a ∉ s) : cons a s h != ∅ := (cons_nonempty _).ne_empty

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `nonempty_mk` / 定理 `nonempty_mk`

English:
theorem nonempty_mk
  given: {m : Multiset α} {hm}
  statement: (⟨m, hm⟩ : Finset α).Nonempty ↔ m != 0
  proof: by
  induction m using Multiset.induction_on <;> simp

@[simp]

中文:
定理 nonempty_mk
  条件: {m : Multiset α} {hm}
  结论: (⟨m, hm⟩ : 有限集 α).非空 ↔ m != 0
  证明: by
  induction m using Multiset.induction_on <;> simp

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m != 0 := by
  induction m using Multiset.induction_on <;> simp

@[simp]
/--
theorem `coe_cons` / 定理 `coe_cons`

English:
theorem coe_cons
  given: {a s h}
  statement: (@cons α a s h : Set α) = insert a (s : Set α)
  proof: by
  ext
  simp

中文:
定理 coe_cons
  条件: {a s h}
  结论: (@cons α a s h : 集合 α) = insert a (s : 集合 α)
  证明: by
  ext
  simp
-/
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α) := by
  ext
  simp

/--
theorem `subset_cons` / 定理 `subset_cons`

English:
theorem subset_cons
  given: (h : a ∉ s)
  statement: s subseteq s.cons a h
  proof: Multiset.subset_cons _ _

中文:
定理 subset_cons
  条件: (h : a ∉ s)
  结论: s subseteq s.cons a h
  证明: Multiset.subset_cons _ _

Depends on / 依赖: Multiset, Multiset.subset_cons, subset_cons
-/
theorem subset_cons (h : a ∉ s) : s subseteq s.cons a h :=
  Multiset.subset_cons _ _

/--
theorem `ssubset_cons` / 定理 `ssubset_cons`

English:
theorem ssubset_cons
  given: (h : a ∉ s)
  statement: s ⊂ s.cons a h
  proof: Multiset.ssubset_cons h

中文:
定理 ssubset_cons
  条件: (h : a ∉ s)
  结论: s ⊂ s.cons a h
  证明: Multiset.ssubset_cons h

Depends on / 依赖: Multiset, Multiset.ssubset_cons, ssubset_cons
-/
theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  Multiset.ssubset_cons h

/--
theorem `cons_subset` / 定理 `cons_subset`

English:
theorem cons_subset
  given: {h : a ∉ s}
  statement: s.cons a h subseteq t ↔ a in t ∧ s subseteq t
  proof: Multiset.cons_subset

@[simp]

中文:
定理 cons_subset
  条件: {h : a ∉ s}
  结论: s.cons a h subseteq t ↔ a in t ∧ s subseteq t
  证明: Multiset.cons_subset

@[simp]

Depends on / 依赖: Multiset, Multiset.cons_subset, cons_subset
-/
theorem cons_subset {h : a ∉ s} : s.cons a h subseteq t ↔ a in t ∧ s subseteq t :=
  Multiset.cons_subset

@[simp]
/--
theorem `cons_subset_cons` / 定理 `cons_subset_cons`

English:
theorem cons_subset_cons
  given: {hs ht}
  statement: s.cons a hs subseteq t.cons a ht ↔ s subseteq t
  proof: by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

中文:
定理 cons_subset_cons
  条件: {hs ht}
  结论: s.cons a hs subseteq t.cons a ht ↔ s subseteq t
  证明: by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

Depends on / 依赖: Set.insert_subset_insert_iff, coe_cons, coe_subset, insert_subset_insert_iff
-/
theorem cons_subset_cons {hs ht} : s.cons a hs subseteq t.cons a ht ↔ s subseteq t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

/--
theorem `ssubset_iff_exists_cons_subset` / 定理 `ssubset_iff_exists_cons_subset`

English:
theorem ssubset_iff_exists_cons_subset
  statement: s ⊂ t ↔ exists (a : _) (h : a ∉ s), s.cons a h subseteq t
  proof: by
  grind

中文:
定理 ssubset_iff_存在_cons_subset
  结论: s ⊂ t ↔ 存在 (a : _) (h : a ∉ s), s.cons a h subseteq t
  证明: by
  grind
-/
theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ exists (a : _) (h : a ∉ s), s.cons a h subseteq t := by
  grind

/--
theorem `cons_swap` / 定理 `cons_swap`

English:
theorem cons_swap
  given: (hb : b ∉ s) (ha : a ∉ s.cons b hb)
  proof: eq_of_veq Multiset.cons_swap a b s.val

中文:
定理 cons_swap
  条件: (hb : b ∉ s) (ha : a ∉ s.cons b hb)
  证明: eq_of_veq Multiset.cons_swap a b s.val

Depends on / 依赖: Multiset, Multiset.cons_swap, cons_swap, eq_of_veq, s.val
-/
theorem cons_swap (hb : b ∉ s) (ha : a ∉ s.cons b hb) :
    (s.cons b hb).cons a ha = (s.cons a fun h => ha (mem_cons.mpr (.inr h))).cons b fun h =>
      ha (mem_cons.mpr (.inl ((mem_cons.mp h).elim symm (fun h => False.elim (hb h))))) :=
eq_of_veq Multiset.cons_swap a b s.val

/-- Split the added element of cons off a Pi type. -/
@[simps!]
/--
Definition of `consPiProd` / `consPiProd` 的定义

English:
definition consPiProd
  signature: (f : α -> Type*) (has : a ∉ s) (x : Π i in cons a s has, f i)
  body: (x a (mem_cons_self a s), fun i hi => x i (mem_cons_of_mem hi))

中文:
定义 consPiProd
  签名: (f : α -> 类型) (has : a ∉ s) (x : Π i in cons a s has, f i)
  定义体: (x a (mem_cons_self a s), fun i hi => x i (mem_cons_of_mem hi))

Depends on / 依赖: mem_cons_of_mem, mem_cons_self
-/
def consPiProd (f : α -> Type*) (has : a ∉ s) (x : Π i in cons a s has, f i) : f a × Π i in s, f i :=
  (x a (mem_cons_self a s), fun i hi => x i (mem_cons_of_mem hi))

/--
Definition of `prodPiCons` / `prodPiCons` 的定义

English:
definition prodPiCons
  signature: [DecidableEq α] (f : α -> Type*) {a : α} (has : a ∉ s) (x : f a × Π i in s, f i)
  body: fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_cons_of_ne hi h)

中文:
定义 prodPiCons
  签名: [DecidableEq α] (f : α -> 类型) {a : α} (has : a ∉ s) (x : f a × Π i in s, f i)
  定义体: fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_cons_of_ne hi h)

Depends on / 依赖: h.symm, mem_of_mem_cons_of_ne
-/
def prodPiCons [DecidableEq α] (f : α -> Type*) {a : α} (has : a ∉ s) (x : f a × Π i in s, f i) :
    (Π i in cons a s has, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_cons_of_ne hi h)

/--
Definition of `consPiProdEquiv` / `consPiProdEquiv` 的定义

English:
definition consPiProdEquiv
  signature: [DecidableEq α] {s : Finset α} (f : α -> Type*) {a : α} (has : a ∉ s)
  body: consPiProd f has
  invFun := prodPiCons f has
  left_inv _ := by grind [prodPiCons, consPiProd]
  right_inv _ := by
    -- I'm surprised `grind` needs this `ext` step: it is just `Prod.ext` and `funext`.
    ext _ hi <;> grind [prodPiCons, consPiProd]

中文:
定义 consPiProdEquiv
  签名: [DecidableEq α] {s : 有限集 α} (f : α -> 类型) {a : α} (has : a ∉ s)
  定义体: consPiProd f has
  invFun := prodPiCons f has
  left_inv _ := by grind [prodPiCons, consPiProd]
  right_inv _ := by
    -- I'm surprised `grind` needs this `ext` step: it is just `Prod.ext` and `funext`.
    ext _ hi <;> grind [prodPiCons, consPiProd]

Depends on / 依赖: consPiProd
-/
def consPiProdEquiv [DecidableEq α] {s : Finset α} (f : α -> Type*) {a : α} (has : a ∉ s) :
    (Π i in cons a s has, f i) ≃ f a × Π i in s, f i where
  toFun := consPiProd f has
  invFun := prodPiCons f has
  left_inv _ := by grind [prodPiCons, consPiProd]
  right_inv _ := by
    -- I'm surprised `grind` needs this `ext` step: it is just `Prod.ext` and `funext`.
    ext _ hi <;> grind [prodPiCons, consPiProd]

end Cons

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t : Finset α} {a b : α} {f : α -> β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert α (Finset α)
  body: ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

中文:
实例 :
  签名: Insert α (有限集 α)
  定义体: ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

Depends on / 依赖: ndinsert
-/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

/--
theorem `insert_def` / 定理 `insert_def`

English:
theorem insert_def
  given: (a : α) (s : Finset α)
  statement: insert a s = ⟨_, s.2.ndinsert a⟩
  proof: rfl

@[simp]

中文:
定理 insert_def
  条件: (a : α) (s : 有限集 α)
  结论: insert a s = ⟨_, s.2.ndinsert a⟩
  证明: rfl

@[simp]
-/
theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl

@[simp]
/--
theorem `insert_val` / 定理 `insert_val`

English:
theorem insert_val
  given: (a : α) (s : Finset α)
  statement: (insert a s).1 = ndinsert a s.1
  proof: rfl

中文:
定理 insert_val
  条件: (a : α) (s : 有限集 α)
  结论: (insert a s).1 = ndinsert a s.1
  证明: rfl
-/
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl

/--
theorem `insert_val'` / 定理 `insert_val'`

English:
theorem insert_val'
  given: (a : α) (s : Finset α)
  statement: (insert a s).1 = dedup (a ::ₘ s.1)
  proof: by
  rw [dedup_cons]; rw [dedup_eq_self]; rfl

中文:
定理 insert_val'
  条件: (a : α) (s : 有限集 α)
  结论: (insert a s).1 = dedup (a ::ₘ s.1)
  证明: by
  rw [dedup_cons]; rw [dedup_eq_self]; rfl

Depends on / 依赖: dedup_cons, dedup_eq_self
-/
theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons]; rw [dedup_eq_self]; rfl

/--
theorem `insert_val_of_notMem` / 定理 `insert_val_of_notMem`

English:
theorem insert_val_of_notMem
  given: {a : α} {s : Finset α} (h : a ∉ s)
  statement: (insert a s).1 = a ::ₘ s.1
  proof: by
  rw [insert_val]; rw [ndinsert_of_notMem h]

@[simp, grind =]

中文:
定理 insert_val_of_notMem
  条件: {a : α} {s : 有限集 α} (h : a ∉ s)
  结论: (insert a s).1 = a ::ₘ s.1
  证明: by
  rw [insert_val]; rw [ndinsert_of_notMem h]

@[simp, grind =]

Depends on / 依赖: insert_val, ndinsert_of_notMem
-/
theorem insert_val_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val]; rw [ndinsert_of_notMem h]

@[simp, grind =]
/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  statement: a in insert b s ↔ a = b ∨ a in s
  proof: mem_ndinsert

中文:
定理 mem_insert
  结论: a in insert b s ↔ a = b ∨ a in s
  证明: mem_ndinsert

Depends on / 依赖: mem_ndinsert
-/
theorem mem_insert : a in insert b s ↔ a = b ∨ a in s :=
  mem_ndinsert

/--
theorem `mem_insert_self` / 定理 `mem_insert_self`

English:
theorem mem_insert_self
  given: (a : α) (s : Finset α)
  statement: a in insert a s
  proof: mem_ndinsert_self a s.1

中文:
定理 mem_insert_self
  条件: (a : α) (s : 有限集 α)
  结论: a in insert a s
  证明: mem_ndinsert_self a s.1

Depends on / 依赖: mem_ndinsert_self
-/
theorem mem_insert_self (a : α) (s : Finset α) : a in insert a s :=
  mem_ndinsert_self a s.1

/--
theorem `mem_insert_of_mem` / 定理 `mem_insert_of_mem`

English:
theorem mem_insert_of_mem
  given: (h : a in s)
  statement: a in insert b s
  proof: mem_ndinsert_of_mem h

中文:
定理 mem_insert_of_mem
  条件: (h : a in s)
  结论: a in insert b s
  证明: mem_ndinsert_of_mem h

Depends on / 依赖: mem_ndinsert_of_mem
-/
theorem mem_insert_of_mem (h : a in s) : a in insert b s :=
  mem_ndinsert_of_mem h

/--
theorem `mem_of_mem_insert_of_ne` / 定理 `mem_of_mem_insert_of_ne`

English:
theorem mem_of_mem_insert_of_ne
  given: (h : b in insert a s)
  statement: b != a -> b in s
  proof: (mem_insert.1 h).resolve_left

中文:
定理 mem_of_mem_insert_of_ne
  条件: (h : b in insert a s)
  结论: b != a -> b in s
  证明: (mem_insert.1 h).resolve_left

Depends on / 依赖: mem_insert, resolve_left
-/
theorem mem_of_mem_insert_of_ne (h : b in insert a s) : b != a -> b in s :=
  (mem_insert.1 h).resolve_left

/--
theorem `eq_of_mem_insert_of_notMem` / 定理 `eq_of_mem_insert_of_notMem`

English:
theorem eq_of_mem_insert_of_notMem
  given: (ha : b in insert a s) (hb : b ∉ s)
  statement: b = a
  proof: (mem_insert.1 ha).resolve_right hb

中文:
定理 eq_of_mem_insert_of_notMem
  条件: (ha : b in insert a s) (hb : b ∉ s)
  结论: b = a
  证明: (mem_insert.1 ha).resolve_right hb

Depends on / 依赖: mem_insert, resolve_right
-/
theorem eq_of_mem_insert_of_notMem (ha : b in insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb

/--
lemma `insert_empty` / 引理 `insert_empty`

English:
lemma insert_empty
  statement: insert a (∅ : Finset α) = {a}
  proof: rfl

@[simp, grind =]

中文:
引理 insert_empty
  结论: insert a (∅ : 有限集 α) = {a}
  证明: rfl

@[simp, grind =]
-/
@[simp] lemma insert_empty : insert a (∅ : Finset α) = {a} := rfl

@[simp, grind =]
/--
theorem `cons_eq_insert` / 定理 `cons_eq_insert`

English:
theorem cons_eq_insert
  given: (a s h)
  statement: @cons α a s h = insert a s
  proof: ext fun a => by simp

@[simp, norm_cast]

中文:
定理 cons_eq_insert
  条件: (a s h)
  结论: @cons α a s h = insert a s
  证明: ext fun a => by simp

@[simp, norm_cast]
-/
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp

@[simp, norm_cast]
/--
theorem `coe_insert` / 定理 `coe_insert`

English:
theorem coe_insert
  given: (a : α) (s : Finset α)
  statement: ↑(insert a s) = (insert a s : Set α)
  proof: by grind

中文:
定理 coe_insert
  条件: (a : α) (s : 有限集 α)
  结论: ↑(insert a s) = (insert a s : 集合 α)
  证明: by grind
-/
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) := by grind

/--
theorem `mem_insert_coe` / 定理 `mem_insert_coe`

English:
theorem mem_insert_coe
  given: {s : Finset α} {x y : α}
  statement: x in insert y s ↔ x in insert y (s : Set α)
  proof: by
  simp

中文:
定理 mem_insert_coe
  条件: {s : 有限集 α} {x y : α}
  结论: x in insert y s ↔ x in insert y (s : 集合 α)
  证明: by
  simp
-/
theorem mem_insert_coe {s : Finset α} {x y : α} : x in insert y s ↔ x in insert y (s : Set α) := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulSingleton α (Finset α)
  body: ⟨fun a => by simp⟩

@[simp, grind =]

中文:
实例 :
  签名: LawfulSingleton α (有限集 α)
  定义体: ⟨fun a => by simp⟩

@[simp, grind =]
-/
instance : LawfulSingleton α (Finset α) :=
  ⟨fun a => by simp⟩

@[simp, grind =]
/--
theorem `insert_eq_of_mem` / 定理 `insert_eq_of_mem`

English:
theorem insert_eq_of_mem
  given: (h : a in s)
  statement: insert a s = s
  proof: eq_of_veq ndinsert_of_mem h

@[simp]

中文:
定理 insert_eq_of_mem
  条件: (h : a in s)
  结论: insert a s = s
  证明: eq_of_veq ndinsert_of_mem h

@[simp]

Depends on / 依赖: eq_of_veq, ndinsert_of_mem
-/
theorem insert_eq_of_mem (h : a in s) : insert a s = s :=
eq_of_veq ndinsert_of_mem h

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
-/
theorem insert_eq_self : insert a s = s ↔ a in s := by grind

/--
theorem `insert_ne_self` / 定理 `insert_ne_self`

English:
theorem insert_ne_self
  statement: insert a s != s ↔ a ∉ s
  proof: insert_eq_self.not

中文:
定理 insert_ne_self
  结论: insert a s != s ↔ a ∉ s
  证明: insert_eq_self.not

Depends on / 依赖: insert_eq_self, insert_eq_self.not
-/
theorem insert_ne_self : insert a s != s ↔ a ∉ s :=
  insert_eq_self.not

/--
theorem `pair_eq_singleton` / 定理 `pair_eq_singleton`

English:
theorem pair_eq_singleton
  given: (a : α)
  statement: ({a, a} : Finset α) = {a}
  proof: insert_eq_of_mem mem_singleton_self _

中文:
定理 pair_eq_singleton
  条件: (a : α)
  结论: ({a, a} : 有限集 α) = {a}
  证明: insert_eq_of_mem mem_singleton_self _

Depends on / 依赖: insert_eq_of_mem, mem_singleton_self
-/
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
insert_eq_of_mem mem_singleton_self _

/--
theorem `insert_comm` / 定理 `insert_comm`

English:
theorem insert_comm
  given: (a b : α) (s : Finset α)
  statement: insert a (insert b s) = insert b (insert a s)
  proof: by
  grind

@[norm_cast]

中文:
定理 insert_comm
  条件: (a b : α) (s : 有限集 α)
  结论: insert a (insert b s) = insert b (insert a s)
  证明: by
  grind

@[norm_cast]
-/
theorem insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) := by
  grind

@[norm_cast]
/--
theorem `coe_pair` / 定理 `coe_pair`

English:
theorem coe_pair
  given: {a b : α}
  statement: (({a, b} : Finset α) : Set α) = {a, b}
  proof: by grind

@[simp, norm_cast]

中文:
定理 coe_pair
  条件: {a b : α}
  结论: (({a, b} : 有限集 α) : 集合 α) = {a, b}
  证明: by grind

@[simp, norm_cast]
-/
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} := by grind

@[simp, norm_cast]
/--
theorem `coe_eq_pair` / 定理 `coe_eq_pair`

English:
theorem coe_eq_pair
  given: {s : Finset α} {a b : α}
  statement: (s : Set α) = {a, b} ↔ s = {a, b}
  proof: by
  rw [← coe_pair]; rw [coe_inj]

中文:
定理 coe_eq_pair
  条件: {s : 有限集 α} {a b : α}
  结论: (s : 集合 α) = {a, b} ↔ s = {a, b}
  证明: by
  rw [← coe_pair]; rw [coe_inj]

Depends on / 依赖: coe_inj, coe_pair
-/
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair]; rw [coe_inj]

/--
theorem `pair_comm` / 定理 `pair_comm`

English:
theorem pair_comm
  given: (a b : α)
  statement: ({a, b} : Finset α) = {b, a}
  proof: insert_comm a b ∅

中文:
定理 pair_comm
  条件: (a b : α)
  结论: ({a, b} : 有限集 α) = {b, a}
  证明: insert_comm a b ∅

Depends on / 依赖: insert_comm
-/
theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  insert_comm a b ∅

/--
theorem `insert_idem` / 定理 `insert_idem`

English:
theorem insert_idem
  given: (a : α) (s : Finset α)
  statement: insert a (insert a s) = insert a s
  proof: by grind

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 insert_idem
  条件: (a : α) (s : 有限集 α)
  结论: insert a (insert a s) = insert a s
  证明: by grind

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s := by grind

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `insert_nonempty` / 定理 `insert_nonempty`

English:
theorem insert_nonempty
  given: (a : α) (s : Finset α)
  statement: (insert a s).Nonempty
  proof: ⟨a, mem_insert_self a s⟩

@[simp]

中文:
定理 insert_nonempty
  条件: (a : α) (s : 有限集 α)
  结论: (insert a s).非空
  证明: ⟨a, mem_insert_self a s⟩

@[simp]

Depends on / 依赖: mem_insert_self
-/
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩

@[simp]
/--
theorem `insert_ne_empty` / 定理 `insert_ne_empty`

English:
theorem insert_ne_empty
  given: (a : α) (s : Finset α)
  statement: insert a s != ∅
  proof: (insert_nonempty a s).ne_empty

中文:
定理 insert_ne_empty
  条件: (a : α) (s : 有限集 α)
  结论: insert a s != ∅
  证明: (insert_nonempty a s).ne_empty

Depends on / 依赖: insert_nonempty, ne_empty
-/
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s != ∅ :=
  (insert_nonempty a s).ne_empty

instance (i : α) (s : Finset α) : Nonempty ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

/--
theorem `ne_insert_of_notMem` / 定理 `ne_insert_of_notMem`

English:
theorem ne_insert_of_notMem
  given: (s t : Finset α) {a : α} (h : a ∉ s)
  statement: s != insert a t
  proof: by
  contrapose h
  simp [h]

中文:
定理 ne_insert_of_notMem
  条件: (s t : 有限集 α) {a : α} (h : a ∉ s)
  结论: s != insert a t
  证明: by
  contrapose h
  simp [h]

Depends on / 依赖: contrapose
-/
theorem ne_insert_of_notMem (s t : Finset α) {a : α} (h : a ∉ s) : s != insert a t := by
  contrapose h
  simp [h]

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
  proof: insert_subset_iff.mpr ⟨ha,hs⟩

中文:
定理 insert_subset
  条件: (ha : a in t) (hs : s subseteq t)
  结论: insert a s subseteq t
  证明: insert_subset_iff.mpr ⟨ha,hs⟩

Depends on / 依赖: insert_subset_iff, insert_subset_iff.mpr
-/
theorem insert_subset (ha : a in t) (hs : s subseteq t) : insert a s subseteq t :=
  insert_subset_iff.mpr ⟨ha,hs⟩

/--
theorem `subset_insert` / 定理 `subset_insert`

English:
theorem subset_insert
  given: (a : α) (s : Finset α)
  statement: s subseteq insert a s
  proof: fun _b => mem_insert_of_mem

@[gcongr, simp]

中文:
定理 subset_insert
  条件: (a : α) (s : 有限集 α)
  结论: s subseteq insert a s
  证明: fun _b => mem_insert_of_mem

@[gcongr, simp]
-/
@[simp] theorem subset_insert (a : α) (s : Finset α) : s subseteq insert a s := fun _b => mem_insert_of_mem

@[gcongr, simp]
/--
theorem `insert_subset_insert` / 定理 `insert_subset_insert`

English:
theorem insert_subset_insert
  given: (a : α) {s t : Finset α} (h : s subseteq t)
  statement: insert a s subseteq insert a t
  proof: by
  grind

中文:
定理 insert_subset_insert
  条件: (a : α) {s t : 有限集 α} (h : s subseteq t)
  结论: insert a s subseteq insert a t
  证明: by
  grind
-/
theorem insert_subset_insert (a : α) {s t : Finset α} (h : s subseteq t) : insert a s subseteq insert a t := by
  grind

/--
lemma `insert_subset_insert_iff` / 引理 `insert_subset_insert_iff`

English:
lemma insert_subset_insert_iff
  given: (ha : a ∉ s)
  statement: insert a s subseteq insert a t ↔ s subseteq t
  proof: by
  simp_rw [← coe_subset]; simp [ha]

中文:
引理 insert_subset_insert_iff
  条件: (ha : a ∉ s)
  结论: insert a s subseteq insert a t ↔ s subseteq t
  证明: by
  simp_rw [← coe_subset]; simp [ha]
-/
@[simp] lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s subseteq insert a t ↔ s subseteq t := by
  simp_rw [← coe_subset]; simp [ha]

/--
theorem `insert_inj` / 定理 `insert_inj`

English:
theorem insert_inj
  given: (ha : a ∉ s)
  statement: insert a s = insert b s ↔ a = b
  proof: ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert_self _ _) ha, congr_arg (insert · s)⟩

中文:
定理 insert_inj
  条件: (ha : a ∉ s)
  结论: insert a s = insert b s ↔ a = b
  证明: ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert_self _ _) ha, congr_arg (insert · s)⟩

Depends on / 依赖: congr_arg, eq_of_mem_insert_of_notMem, insert, mem_insert_self
-/
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert_self _ _) ha, congr_arg (insert · s)⟩

/--
theorem `insert_inj_on` / 定理 `insert_inj_on`

English:
theorem insert_inj_on
  given: (s : Finset α)
  statement: Set.InjOn (fun a => insert a s) sᶜ
  proof: fun _ h _ _ =>
  (insert_inj h).1

中文:
定理 insert_inj_on
  条件: (s : 有限集 α)
  结论: 集合.单射限制 (fun a => insert a s) sᶜ
  证明: fun _ h _ _ =>
  (insert_inj h).1
-/
theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ := fun _ h _ _ =>
  (insert_inj h).1

/--
theorem `ssubset_iff` / 定理 `ssubset_iff`

English:
theorem ssubset_iff
  statement: s ⊂ t ↔ exists a ∉ s, insert a s subseteq t
  proof: mod_cast @Set.ssubset_iff_insert α s t

中文:
定理 ssubset_iff
  结论: s ⊂ t ↔ 存在 a ∉ s, insert a s subseteq t
  证明: mod_cast @Set.ssubset_iff_insert α s t

Depends on / 依赖: Set.ssubset_iff_insert, mod_cast, ssubset_iff_insert
-/
theorem ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subseteq t := mod_cast @Set.ssubset_iff_insert α s t

/--
theorem `ssubset_insert` / 定理 `ssubset_insert`

English:
theorem ssubset_insert
  given: (h : a ∉ s)
  statement: s ⊂ insert a s
  proof: ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_elim]

中文:
定理 ssubset_insert
  条件: (h : a ∉ s)
  结论: s ⊂ insert a s
  证明: ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_elim]

Depends on / 依赖: Subset, Subset.rfl, ssubset_iff, ssubset_iff.mpr
-/
theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_elim]
/--
theorem `cons_induction` / 定理 `cons_induction`

English:
theorem cons_induction
  statement: {α : Type*} {motive : Finset α -> Prop} (empty : motive ∅)

中文:
定理 cons_induction
  结论: {α : 类型} {motive : 有限集 α -> 命题} (empty : motive ∅)
-/
theorem cons_induction {α : Type*} {motive : Finset α -> Prop} (empty : motive ∅)
    (cons : forall (a : α) (s : Finset α) (h : a ∉ s), motive s -> motive (cons a s h)) : forall s, motive s
  | ⟨s, nd⟩ => by
    induction s using Multiset.induction with
    | empty => exact empty
    | cons a s IH =>
      rw [mk_cons nd]
      exact cons a _ _ (IH _)

@[elab_as_elim]
/--
theorem `cons_induction_on` / 定理 `cons_induction_on`

English:
theorem cons_induction_on
  statement: {α : Type*} {motive : Finset α -> Prop} (s : Finset α) (empty : motive ∅)
  proof: cons_induction empty cons s

@[elab_as_elim]

中文:
定理 cons_induction_on
  结论: {α : 类型} {motive : 有限集 α -> 命题} (s : 有限集 α) (empty : motive ∅)
  证明: cons_induction empty cons s

@[elab_as_elim]

Depends on / 依赖: cons_induction
-/
theorem cons_induction_on {α : Type*} {motive : Finset α -> Prop} (s : Finset α) (empty : motive ∅)
    (cons : forall (a : α) (s : Finset α) (h : a ∉ s), motive s -> motive (cons a s h)) : motive s :=
  cons_induction empty cons s

@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {α : Type*} {motive : Finset α -> Prop} [DecidableEq α]
  proof: cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert a s ha

中文:
定理 induction
  结论: {α : 类型} {motive : 有限集 α -> 命题} [DecidableEq α]
  证明: cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert a s ha
-/
protected theorem induction {α : Type*} {motive : Finset α -> Prop} [DecidableEq α]
    (empty : motive ∅)
    (insert : forall (a : α) (s : Finset α), a ∉ s -> motive s -> motive (insert a s)) : forall s, motive s :=
  cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert a s ha

/-- To prove a proposition about an arbitrary `Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α`,
then it holds for the `Finset` obtained by inserting a new element.
-/
@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {α : Type*} {motive : Finset α -> Prop} [DecidableEq α] (s : Finset α)
  proof: Finset.induction empty insert s

中文:
定理 induction_on
  结论: {α : 类型} {motive : 有限集 α -> 命题} [DecidableEq α] (s : 有限集 α)
  证明: Finset.induction empty insert s
-/
protected theorem induction_on {α : Type*} {motive : Finset α -> Prop} [DecidableEq α] (s : Finset α)
    (empty : motive ∅)
    (insert : forall (a : α) (s : Finset α), a ∉ s -> motive s -> motive (insert a s)) : motive s :=
  Finset.induction empty insert s

/-- To prove a proposition about `S : Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α ⊆ S`,
then it holds for the `Finset` obtained by inserting a new element of `S`.
-/
@[elab_as_elim]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {α : Type*} {motive : Finset α -> Prop} [DecidableEq α] (S : Finset α)
  proof: @Finset.induction_on α (fun T => T subseteq S -> motive T) _ S (fun _ => empty)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      insert a s hS sS has (hqs sS))
    (Finset.Subset.refl S)

中文:
定理 induction_on'
  结论: {α : 类型} {motive : 有限集 α -> 命题} [DecidableEq α] (S : 有限集 α)
  证明: @Finset.induction_on α (fun T => T subseteq S -> motive T) _ S (fun _ => empty)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      insert a s hS sS has (hqs sS))
    (Finset.Subset.refl S)

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.induction_on, Finset.insert_subset_iff, Subset, induction_on, insert, insert_subset_iff, motive, subseteq
-/
theorem induction_on' {α : Type*} {motive : Finset α -> Prop} [DecidableEq α] (S : Finset α)
    (empty : motive ∅)
    (insert : forall (a s), a in S -> s subseteq S -> a ∉ s -> motive s -> motive (insert a s)) : motive S :=
  @Finset.induction_on α (fun T => T subseteq S -> motive T) _ S (fun _ => empty)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      insert a s hS sS has (hqs sS))
    (Finset.Subset.refl S)

/-- To prove a proposition about a nonempty `s : Finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds for the `Finset`
obtained by inserting an element in `t`. -/
@[elab_as_elim]
/--
theorem `Nonempty.cons_induction` / 定理 `Nonempty.cons_induction`

English:
theorem Nonempty.cons_induction
  statement: {α : Type*} {motive : forall s : Finset α, s.Nonempty -> Prop}
  proof: by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)

中文:
定理 非空.cons_induction
  结论: {α : 类型} {motive : 对任意 s : 有限集 α, s.非空 -> 命题}
  证明: by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction, eq_empty_or_nonempty, not_nonempty_empty, singleton, t.eq_empty_or_nonempty
-/
theorem Nonempty.cons_induction {α : Type*} {motive : forall s : Finset α, s.Nonempty -> Prop}
    (singleton : forall a, motive {a} (singleton_nonempty _))
    (cons : forall a s (h : a ∉ s) (hs), motive s hs -> motive (Finset.cons a s h) (cons_nonempty h))
    {s : Finset α} (hs : s.Nonempty) : motive s hs := by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)

-- We use a fresh `α` here to exclude the unneeded `DecidableEq α` instance from the section.
/--
lemma `Nonempty.exists_cons_eq` / 引理 `Nonempty.exists_cons_eq`

English:
lemma Nonempty.exists_cons_eq
  given: {α} {s : Finset α} (hs : s.Nonempty)
  statement: exists t a ha, cons a t ha = s
  proof: hs.cons_induction (fun a => ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ => ⟨_, _, _, rfl⟩

中文:
引理 非空.存在_cons_eq
  条件: {α} {s : 有限集 α} (hs : s.非空)
  结论: 存在 t a ha, cons a t ha = s
  证明: hs.cons_induction (fun a => ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ => ⟨_, _, _, rfl⟩

Depends on / 依赖: cons_empty, cons_induction, hs.cons_induction
-/
lemma Nonempty.exists_cons_eq {α} {s : Finset α} (hs : s.Nonempty) : exists t a ha, cons a t ha = s :=
  hs.cons_induction (fun a => ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ => ⟨_, _, _, rfl⟩

/--
Definition of `subtypeInsertEquivOption` / `subtypeInsertEquivOption` 的定义

English:
definition subtypeInsertEquivOption
  signature: {t : Finset α} {x : α} (h : x ∉ t)
  body: if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

中文:
定义 subtypeInsertEquivOption
  签名: {t : 有限集 α} {x : α} (h : x ∉ t)
  定义体: if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

Depends on / 依赖: mem_insert, mem_insert.mp, resolve_left
-/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i in insert x t } ≃ Option { i // i in t } where
  toFun y := if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

/-- Split the added element of insert off a Pi type. -/
@[simps!]
/--
Definition of `insertPiProd` / `insertPiProd` 的定义

English:
definition insertPiProd
  signature: (f : α -> Type*) (x : Π i in insert a s, f i)
  body: (x a (mem_insert_self a s), fun i hi => x i (mem_insert_of_mem hi))

中文:
定义 insertPiProd
  签名: (f : α -> 类型) (x : Π i in insert a s, f i)
  定义体: (x a (mem_insert_self a s), fun i hi => x i (mem_insert_of_mem hi))

Depends on / 依赖: mem_insert_of_mem, mem_insert_self
-/
def insertPiProd (f : α -> Type*) (x : Π i in insert a s, f i) : f a × Π i in s, f i :=
  (x a (mem_insert_self a s), fun i hi => x i (mem_insert_of_mem hi))

/--
Definition of `prodPiInsert` / `prodPiInsert` 的定义

English:
definition prodPiInsert
  signature: (f : α -> Type*) {a : α} (x : f a × Π i in s, f i)
  body: fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_insert_of_ne hi h)

中文:
定义 prodPiInsert
  签名: (f : α -> 类型) {a : α} (x : f a × Π i in s, f i)
  定义体: fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_insert_of_ne hi h)

Depends on / 依赖: h.symm, mem_of_mem_insert_of_ne
-/
def prodPiInsert (f : α -> Type*) {a : α} (x : f a × Π i in s, f i) : (Π i in insert a s, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_insert_of_ne hi h)

/--
Definition of `insertPiProdEquiv` / `insertPiProdEquiv` 的定义

English:
definition insertPiProdEquiv
  signature: {s : Finset α} (f : α -> Type*) {a : α} (has : a ∉ s)
  body: insertPiProd f
  invFun := prodPiInsert f
  left_inv _ := by grind [prodPiInsert, insertPiProd]
  right_inv _ := by ext _ hi <;> grind [prodPiInsert, insertPiProd]

中文:
定义 insertPiProdEquiv
  签名: {s : 有限集 α} (f : α -> 类型) {a : α} (has : a ∉ s)
  定义体: insertPiProd f
  invFun := prodPiInsert f
  left_inv _ := by grind [prodPiInsert, insertPiProd]
  right_inv _ := by ext _ hi <;> grind [prodPiInsert, insertPiProd]

Depends on / 依赖: insertPiProd
-/
def insertPiProdEquiv {s : Finset α} (f : α -> Type*) {a : α} (has : a ∉ s) :
    (Π i in insert a s, f i) ≃ f a × Π i in s, f i where
  toFun := insertPiProd f
  invFun := prodPiInsert f
  left_inv _ := by grind [prodPiInsert, insertPiProd]
  right_inv _ := by ext _ hi <;> grind [prodPiInsert, insertPiProd]

-- useful rules for calculations with quantifiers
/--
theorem `exists_mem_insert` / 定理 `exists_mem_insert`

English:
theorem exists_mem_insert
  given: (a : α) (s : Finset α) (p : α -> Prop)
  proof: by grind

中文:
定理 存在_mem_insert
  条件: (a : α) (s : 有限集 α) (p : α -> 命题)
  证明: by grind
-/
theorem exists_mem_insert (a : α) (s : Finset α) (p : α -> Prop) :
    (exists x, x in insert a s ∧ p x) ↔ p a ∨ exists x, x in s ∧ p x := by grind

/--
theorem `forall_mem_insert` / 定理 `forall_mem_insert`

English:
theorem forall_mem_insert
  given: (a : α) (s : Finset α) (p : α -> Prop)
  proof: by grind

中文:
定理 对任意_mem_insert
  条件: (a : α) (s : 有限集 α) (p : α -> 命题)
  证明: by grind
-/
theorem forall_mem_insert (a : α) (s : Finset α) (p : α -> Prop) :
    (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x := by grind

/--
theorem `forall_of_forall_insert` / 定理 `forall_of_forall_insert`

English:
theorem forall_of_forall_insert
  statement: {p : α -> Prop} {a : α} {s : Finset α}
  proof: H _ mem_insert_of_mem h

中文:
定理 对任意_of_对任意_insert
  结论: {p : α -> 命题} {a : α} {s : 有限集 α}
  证明: H _ mem_insert_of_mem h

Depends on / 依赖: mem_insert_of_mem
-/
theorem forall_of_forall_insert {p : α -> Prop} {a : α} {s : Finset α}
    (H : forall x, x in insert a s -> p x) (x) (h : x in s) : p x :=
H _ mem_insert_of_mem h

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
/--
theorem `toFinset_zero` / 定理 `toFinset_zero`

English:
theorem toFinset_zero
  statement: toFinset (0 : Multiset α) = ∅
  proof: rfl

@[simp]

中文:
定理 toFinset_zero
  结论: toFinset (0 : Multiset α) = ∅
  证明: rfl

@[simp]
-/
theorem toFinset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl

@[simp]
/--
theorem `toFinset_cons` / 定理 `toFinset_cons`

English:
theorem toFinset_cons
  given: (a : α) (s : Multiset α)
  statement: toFinset (a ::ₘ s) = insert a (toFinset s)
  proof: Finset.eq_of_veq dedup_cons

@[simp]

中文:
定理 toFinset_cons
  条件: (a : α) (s : Multiset α)
  结论: toFinset (a ::ₘ s) = insert a (toFinset s)
  证明: Finset.eq_of_veq dedup_cons

@[simp]

Depends on / 依赖: Finset, Finset.eq_of_veq, dedup_cons, eq_of_veq
-/
theorem toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons

@[simp]
/--
theorem `toFinset_singleton` / 定理 `toFinset_singleton`

English:
theorem toFinset_singleton
  given: (a : α)
  statement: toFinset ({a} : Multiset α) = {a}
  proof: by
  rw [← cons_zero]; rw [toFinset_cons]; rw [toFinset_zero]; rw [LawfulSingleton.insert_empty_eq]

中文:
定理 toFinset_singleton
  条件: (a : α)
  结论: toFinset ({a} : Multiset α) = {a}
  证明: by
  rw [← cons_zero]; rw [toFinset_cons]; rw [toFinset_zero]; rw [LawfulSingleton.insert_empty_eq]

Depends on / 依赖: LawfulSingleton, LawfulSingleton.insert_empty_eq, cons_zero, insert_empty_eq, toFinset_cons, toFinset_zero
-/
theorem toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [← cons_zero]; rw [toFinset_cons]; rw [toFinset_zero]; rw [LawfulSingleton.insert_empty_eq]

end Multiset

namespace List

variable [DecidableEq α] {l : List α} {a : α}

@[simp]
/--
theorem `toFinset_nil` / 定理 `toFinset_nil`

English:
theorem toFinset_nil
  statement: toFinset (@nil α) = ∅
  proof: rfl

@[simp]

中文:
定理 toFinset_nil
  结论: toFinset (@nil α) = ∅
  证明: rfl

@[simp]
-/
theorem toFinset_nil : toFinset (@nil α) = ∅ :=
  rfl

@[simp]
/--
theorem `toFinset_cons` / 定理 `toFinset_cons`

English:
theorem toFinset_cons
  statement: toFinset (a :: l) = insert a (toFinset l)
  proof: Finset.eq_of_veq by by_cases h : a in l <;> simp [h]

中文:
定理 toFinset_cons
  结论: toFinset (a :: l) = insert a (toFinset l)
  证明: Finset.eq_of_veq by by_cases h : a in l <;> simp [h]

Depends on / 依赖: Finset, Finset.eq_of_veq, eq_of_veq
-/
theorem toFinset_cons : toFinset (a :: l) = insert a (toFinset l) :=
Finset.eq_of_veq by by_cases h : a in l <;> simp [h]

/--
theorem `toFinset_replicate_of_ne_zero` / 定理 `toFinset_replicate_of_ne_zero`

English:
theorem toFinset_replicate_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  proof: by
  ext x
  simp [hn, List.mem_replicate]

@[simp]

中文:
定理 toFinset_replicate_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  ext x
  simp [hn, List.mem_replicate]

@[simp]

Depends on / 依赖: List.mem_replicate, mem_replicate
-/
theorem toFinset_replicate_of_ne_zero {n : Nat} (hn : n != 0) :
    (List.replicate n a).toFinset = {a} := by
  ext x
  simp [hn, List.mem_replicate]

@[simp]
/--
theorem `toFinset_eq_empty_iff` / 定理 `toFinset_eq_empty_iff`

English:
theorem toFinset_eq_empty_iff
  given: (l : List α)
  statement: l.toFinset = ∅ ↔ l = nil
  proof: by
  cases l <;> simp

@[simp]

中文:
定理 toFinset_eq_empty_iff
  条件: (l : 列表 α)
  结论: l.toFinset = ∅ ↔ l = nil
  证明: by
  cases l <;> simp

@[simp]
-/
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp

@[simp]
/--
theorem `toFinset_nonempty_iff` / 定理 `toFinset_nonempty_iff`

English:
theorem toFinset_nonempty_iff
  given: (l : List α)
  statement: l.toFinset.Nonempty ↔ l != []
  proof: by
  simp [Finset.nonempty_iff_ne_empty]

中文:
定理 toFinset_nonempty_iff
  条件: (l : 列表 α)
  结论: l.toFinset.非空 ↔ l != []
  证明: by
  simp [Finset.nonempty_iff_ne_empty]

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, nonempty_iff_ne_empty
-/
theorem toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l != [] := by
  simp [Finset.nonempty_iff_ne_empty]

end List

namespace Finset

section ToList

@[simp]
/--
theorem `toList_eq_singleton_iff` / 定理 `toList_eq_singleton_iff`

English:
theorem toList_eq_singleton_iff
  given: {a : α} {s : Finset α}
  statement: s.toList = [a] ↔ s = {a}
  proof: by
  rw [toList]; rw [Multiset.toList_eq_singleton_iff]; rw [val_eq_singleton_iff]

@[simp]

中文:
定理 toList_eq_singleton_iff
  条件: {a : α} {s : 有限集 α}
  结论: s.toList = [a] ↔ s = {a}
  证明: by
  rw [toList]; rw [Multiset.toList_eq_singleton_iff]; rw [val_eq_singleton_iff]

@[simp]

Depends on / 依赖: Multiset, Multiset.toList_eq_singleton_iff, toList, toList_eq_singleton_iff, val_eq_singleton_iff
-/
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [toList]; rw [Multiset.toList_eq_singleton_iff]; rw [val_eq_singleton_iff]

@[simp]
/--
theorem `toList_singleton` / 定理 `toList_singleton`

English:
theorem toList_singleton
  statement: forall a, ({a} : Finset α).toList = [a]
  proof: Multiset.toList_singleton

中文:
定理 toList_singleton
  结论: 对任意 a, ({a} : 有限集 α).toList = [a]
  证明: Multiset.toList_singleton

Depends on / 依赖: Multiset, Multiset.toList_singleton, toList_singleton
-/
theorem toList_singleton : forall a, ({a} : Finset α).toList = [a] :=
  Multiset.toList_singleton

open scoped List in
/--
theorem `toList_cons` / 定理 `toList_cons`

English:
theorem toList_cons
  given: {a : α} {s : Finset α} (h : a ∉ s)
  statement: (cons a s h).toList ~ a :: s.toList
  proof: (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]

中文:
定理 toList_cons
  条件: {a : α} {s : 有限集 α} (h : a ∉ s)
  结论: (cons a s h).toList ~ a :: s.toList
  证明: (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]

Depends on / 依赖: Finset, Finset.mem_cons, Finset.mem_toList, List.mem_cons, List.perm_ext_iff_of_nodup, mem_cons, mem_toList, nodup_toList, perm_ext_iff_of_nodup
-/
theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]

open scoped List in
/--
theorem `toList_insert` / 定理 `toList_insert`

English:
theorem toList_insert
  given: [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s)
  proof: cons_eq_insert _ _ h ▸ toList_cons _

中文:
定理 toList_insert
  条件: [DecidableEq α] {a : α} {s : 有限集 α} (h : a ∉ s)
  证明: cons_eq_insert _ _ h ▸ toList_cons _

Depends on / 依赖: cons_eq_insert, toList_cons
-/
theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _

end ToList

section Pairwise

variable {s : Finset α}

/--
theorem `pairwise_cons'` / 定理 `pairwise_cons'`

English:
theorem pairwise_cons'
  given: {a : α} (ha : a ∉ s) (r : β -> β -> Prop) (f : α -> β)
  proof: by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert]
  grind

中文:
定理 pairwise_cons'
  条件: {a : α} (ha : a ∉ s) (r : β -> β -> 命题) (f : α -> β)
  证明: by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert]
  grind

Depends on / 依赖: Finset, Finset.coe_cons, Set.pairwise_insert, coe_cons, pairwise_insert, pairwise_subtype_iff_pairwise_finset
-/
theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β -> β -> Prop) (f : α -> β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
    Pairwise (r on fun a : s => f a) ∧ forall b in s, r (f a) (f b) ∧ r (f b) (f a) := by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert]
  grind

/--
theorem `pairwise_cons` / 定理 `pairwise_cons`

English:
theorem pairwise_cons
  given: {a : α} (ha : a ∉ s) (r : α -> α -> Prop)
  proof: pairwise_cons' ha r id

中文:
定理 pairwise_cons
  条件: {a : α} (ha : a ∉ s) (r : α -> α -> 命题)
  证明: pairwise_cons' ha r id

Depends on / 依赖: pairwise_cons
-/
theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α -> α -> Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔
      Pairwise (r on fun a : s => a) ∧ forall b in s, r a b ∧ r b a :=
  pairwise_cons' ha r id

end Pairwise

end Finset
