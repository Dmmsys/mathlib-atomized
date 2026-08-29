/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.SymmDiff

/-!
# Symmetric difference of finite sets

This file concerns the symmetric difference operator `s Δ t` on finite sets.

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

/-! ### Symmetric difference -/

section SymmDiff

open scoped symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

/--
theorem `mem_symmDiff` / 定理 `mem_symmDiff`

English:
theorem mem_symmDiff
  statement: a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s
  proof: by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]

中文:
定理 mem_symmDiff
  结论: a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s
  证明: by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]

Depends on / 依赖: mem_sdiff, mem_union, simp_rw, sup_eq_union, symmDiff
-/
theorem mem_symmDiff : a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]

/--
theorem `symmDiff_def` / 定理 `symmDiff_def`

English:
theorem symmDiff_def
  given: (s t : Finset α)
  statement: s ∆ t = s \ t union t \ s
  proof: rfl

@[simp, norm_cast]

中文:
定理 symmDiff_def
  条件: (s t : 有限集 α)
  结论: s ∆ t = s \ t union t \ s
  证明: rfl

@[simp, norm_cast]
-/
protected theorem symmDiff_def (s t : Finset α) : s ∆ t = s \ t union t \ s := rfl

@[simp, norm_cast]
/--
theorem `coe_symmDiff` / 定理 `coe_symmDiff`

English:
theorem coe_symmDiff
  statement: (↑(s ∆ t) : Set α) = (s : Set α) ∆ t
  proof: Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]

中文:
定理 coe_symmDiff
  结论: (↑(s ∆ t) : 集合 α) = (s : 集合 α) ∆ t
  证明: Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]

Depends on / 依赖: Set.ext, Set.mem_symmDiff, mem_symmDiff
-/
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]

/--
lemma `symmDiff_eq_empty` / 引理 `symmDiff_eq_empty`

English:
lemma symmDiff_eq_empty
  statement: s ∆ t = ∅ ↔ s = t
  proof: symmDiff_eq_bot

中文:
引理 symmDiff_eq_empty
  结论: s ∆ t = ∅ ↔ s = t
  证明: symmDiff_eq_bot
-/
@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
/--
lemma `symmDiff_nonempty` / 引理 `symmDiff_nonempty`

English:
lemma symmDiff_nonempty
  statement: (s ∆ t).Nonempty ↔ s != t
  proof: nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

中文:
引理 symmDiff_nonempty
  结论: (s ∆ t).非空 ↔ s != t
  证明: nonempty_iff_ne_empty.trans symmDiff_eq_empty.not
-/
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s != t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

/--
theorem `image_symmDiff` / 定理 `image_symmDiff`

English:
theorem image_symmDiff
  given: [DecidableEq β] {f : α -> β} (s t : Finset α) (hf : Injective f)
  proof: mod_cast Set.image_symmDiff hf s t

中文:
定理 image_symmDiff
  条件: [DecidableEq β] {f : α -> β} (s t : 有限集 α) (hf : 单射 f)
  证明: mod_cast Set.image_symmDiff hf s t

Depends on / 依赖: Set.image_symmDiff, image_symmDiff, mod_cast
-/
theorem image_symmDiff [DecidableEq β] {f : α -> β} (s t : Finset α) (hf : Injective f) :
    (s ∆ t).image f = s.image f ∆ t.image f :=
  mod_cast Set.image_symmDiff hf s t

/--
lemma `symmDiff_subset_sdiff` / 引理 `symmDiff_subset_sdiff`

English:
lemma symmDiff_subset_sdiff
  statement: s \ t subseteq s ∆ t
  proof: subset_union_left

中文:
引理 symmDiff_subset_sdiff
  结论: s \ t subseteq s ∆ t
  证明: subset_union_left

Depends on / 依赖: subset_union_left
-/
lemma symmDiff_subset_sdiff : s \ t subseteq s ∆ t := subset_union_left

/--
lemma `symmDiff_subset_sdiff'` / 引理 `symmDiff_subset_sdiff'`

English:
lemma symmDiff_subset_sdiff'
  statement: t \ s subseteq s ∆ t
  proof: subset_union_right

中文:
引理 symmDiff_subset_sdiff'
  结论: t \ s subseteq s ∆ t
  证明: subset_union_right

Depends on / 依赖: subset_union_right
-/
lemma symmDiff_subset_sdiff' : t \ s subseteq s ∆ t := subset_union_right

/--
lemma `symmDiff_subset_union` / 引理 `symmDiff_subset_union`

English:
lemma symmDiff_subset_union
  statement: s ∆ t subseteq s union t
  proof: symmDiff_le_sup (α := Finset α)

中文:
引理 symmDiff_subset_union
  结论: s ∆ t subseteq s union t
  证明: symmDiff_le_sup (α := Finset α)

Depends on / 依赖: Finset, symmDiff_le_sup
-/
lemma symmDiff_subset_union : s ∆ t subseteq s union t := symmDiff_le_sup (α := Finset α)

/--
lemma `symmDiff_eq_union_iff` / 引理 `symmDiff_eq_union_iff`

English:
lemma symmDiff_eq_union_iff
  given: (s t : Finset α)
  statement: s ∆ t = s union t ↔ Disjoint s t
  proof: symmDiff_eq_sup s t

中文:
引理 symmDiff_eq_union_iff
  条件: (s t : 有限集 α)
  结论: s ∆ t = s union t ↔ Disjoint s t
  证明: symmDiff_eq_sup s t

Depends on / 依赖: symmDiff_eq_sup
-/
lemma symmDiff_eq_union_iff (s t : Finset α) : s ∆ t = s union t ↔ Disjoint s t := symmDiff_eq_sup s t

/--
lemma `symmDiff_eq_union` / 引理 `symmDiff_eq_union`

English:
lemma symmDiff_eq_union
  given: (h : Disjoint s t)
  statement: s ∆ t = s union t
  proof: Disjoint.symmDiff_eq_sup h

中文:
引理 symmDiff_eq_union
  条件: (h : Disjoint s t)
  结论: s ∆ t = s union t
  证明: Disjoint.symmDiff_eq_sup h

Depends on / 依赖: Disjoint, Disjoint.symmDiff_eq_sup, symmDiff_eq_sup
-/
lemma symmDiff_eq_union (h : Disjoint s t) : s ∆ t = s union t := Disjoint.symmDiff_eq_sup h

end SymmDiff

end Finset
