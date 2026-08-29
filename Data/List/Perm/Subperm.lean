/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Basic
public import Batteries.Tactic.Trans
public import Mathlib.Data.List.Perm.Basic

/-!
# List Sub-permutations

This file develops theory about the `List.Subperm` relation.

## Notation

The notation `<+~` is used for sub-permutations.
-/

public section

open Nat

namespace List
variable {α : Type*} {l l₁ l₂ : List α} {a : α}

open Perm

section Subperm

attribute [trans] Subperm.trans

end Subperm

/--
lemma `subperm_iff_count` / 引理 `subperm_iff_count`

English:
lemma subperm_iff_count
  given: [DecidableEq α]
  statement: l₁ <+~ l₂ ↔ forall a, count a l₁ <= count a l₂
  proof: subperm_ext_iff.trans forall_congr' fun a => by
    by_cases ha : a in l₁ <;> simp [ha, count_eq_zero_of_not_mem]

中文:
引理 subperm_iff_count
  条件: [DecidableEq α]
  结论: l₁ <+~ l₂ ↔ 对任意 a, count a l₁ <= count a l₂
  证明: subperm_ext_iff.trans forall_congr' fun a => by
    by_cases ha : a in l₁ <;> simp [ha, count_eq_zero_of_not_mem]

Depends on / 依赖: count_eq_zero_of_not_mem, forall_congr, subperm_ext_iff, subperm_ext_iff.trans
-/
lemma subperm_iff_count [DecidableEq α] : l₁ <+~ l₂ ↔ forall a, count a l₁ <= count a l₂ :=
subperm_ext_iff.trans forall_congr' fun a => by
    by_cases ha : a in l₁ <;> simp [ha, count_eq_zero_of_not_mem]

/--
lemma `subperm_iff` / 引理 `subperm_iff`

English:
lemma subperm_iff
  statement: l₁ <+~ l₂ ↔ exists l, l ~ l₂ ∧ l₁ <+ l
  proof: by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ => h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩

中文:
引理 subperm_iff
  结论: l₁ <+~ l₂ ↔ 存在 l, l ~ l₂ ∧ l₁ <+ l
  证明: by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ => h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩

Depends on / 依赖: append_right, exists_perm_append, prefix_append, sublist, subperm, subperm.trans
-/
lemma subperm_iff : l₁ <+~ l₂ ↔ exists l, l ~ l₂ ∧ l₁ <+ l := by
  refine ⟨?_, fun ⟨l, h₁, h₂⟩ => h₂.subperm.trans h₁.subperm⟩
  rintro ⟨l, h₁, h₂⟩
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩

/--
lemma `subperm_singleton_iff` / 引理 `subperm_singleton_iff`

English:
lemma subperm_singleton_iff
  statement: l <+~ [a] ↔ l = [] ∨ l = [a]
  proof: by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]

中文:
引理 subperm_singleton_iff
  结论: l <+~ [a] ↔ l = [] ∨ l = [a]
  证明: by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]
-/
@[simp] lemma subperm_singleton_iff : l <+~ [a] ↔ l = [] ∨ l = [a] := by
  constructor
  · rw [subperm_iff]
    rintro ⟨s, hla, h⟩
    rwa [perm_singleton.mp hla, sublist_singleton] at h
  · rintro (rfl | rfl)
    exacts [nil_subperm, Subperm.refl _]

/--
lemma `subperm_cons_self` / 引理 `subperm_cons_self`

English:
lemma subperm_cons_self
  statement: l <+~ a :: l
  proof: ⟨l, Perm.refl _, sublist_cons_self _ _⟩

protected alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons

中文:
引理 subperm_cons_self
  结论: l <+~ a :: l
  证明: ⟨l, Perm.refl _, sublist_cons_self _ _⟩

protected alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons

Depends on / 依赖: Perm.refl, sublist_cons_self
-/
lemma subperm_cons_self : l <+~ a :: l := ⟨l, Perm.refl _, sublist_cons_self _ _⟩

protected alias ⟨subperm.of_cons, subperm.cons⟩ := subperm_cons

/--
theorem `Subperm.append` / 定理 `Subperm.append`

English:
theorem Subperm.append
  given: {l₁ l₂ r₁ r₂ : List α}

中文:
定理 Subperm.append
  条件: {l₁ l₂ r₁ r₂ : List α}
-/
theorem Subperm.append {l₁ l₂ r₁ r₂ : List α} :
    l₁ <+~ l₂ -> r₁ <+~ r₂ -> (l₁ ++ r₁) <+~ (l₂ ++ r₂)
  | ⟨l, hl_perm, hl_sub⟩, ⟨r, hr_perm, hr_sub⟩ =>
    ⟨l ++ r, hl_perm.append hr_perm, hl_sub.append hr_sub⟩

/--
theorem `map_subperm_map_iff` / 定理 `map_subperm_map_iff`

English:
theorem map_subperm_map_iff
  given: {α β} {l₁ l₂ : List α} {f : α -> β} (hf : Function.Injective f)
  proof: by
    obtain ⟨l, hl_perm, hl_sub⟩ := a
    exact ⟨l.map f, hl_perm.map f, hl_sub.map f⟩
  mp a := by
    obtain ⟨w, ⟨perm, sublist⟩⟩ := a
    obtain ⟨x, ⟨sublistₓ, mapₓ⟩⟩ := sublist_map_iff.mp sublist
    use x
    constructor
    · rw [mapₓ] at perm
      exact (map_perm_map_iff hf).mp perm
    · 

中文:
定理 map_subperm_map_iff
  条件: {α β} {l₁ l₂ : List α} {f : α -> β} (hf : Function.Injective f)
  证明: by
    obtain ⟨l, hl_perm, hl_sub⟩ := a
    exact ⟨l.map f, hl_perm.map f, hl_sub.map f⟩
  mp a := by
    obtain ⟨w, ⟨perm, sublist⟩⟩ := a
    obtain ⟨x, ⟨sublistₓ, mapₓ⟩⟩ := sublist_map_iff.mp sublist
    use x
    constructor
    · rw [mapₓ] at perm
      exact (map_perm_map_iff hf).mp perm
    · 

Depends on / 依赖: hl_perm, hl_perm.map, hl_sub, hl_sub.map, l.map, map_perm_map_iff, sublist, sublist_map_iff, sublist_map_iff.mp
-/
theorem map_subperm_map_iff {α β} {l₁ l₂ : List α} {f : α -> β} (hf : Function.Injective f) :
    (l₁.map f) <+~ (l₂.map f) ↔ l₁ <+~ l₂ where
  mpr a := by
    obtain ⟨l, hl_perm, hl_sub⟩ := a
    exact ⟨l.map f, hl_perm.map f, hl_sub.map f⟩
  mp a := by
    obtain ⟨w, ⟨perm, sublist⟩⟩ := a
    obtain ⟨x, ⟨sublistₓ, mapₓ⟩⟩ := sublist_map_iff.mp sublist
    use x
    constructor
    · rw [mapₓ] at perm
      exact (map_perm_map_iff hf).mp perm
    · exact sublistₓ

alias ⟨_, Subperm.map⟩ := map_subperm_map_iff

/--
theorem `Nodup.subperm` / 定理 `Nodup.subperm`

English:
theorem Nodup.subperm
  given: (d : Nodup l₁) (H : l₁ subseteq l₂)
  statement: l₁ <+~ l₂
  proof: subperm_of_subset d H

中文:
定理 Nodup.subperm
  条件: (d : Nodup l₁) (H : l₁ subseteq l₂)
  结论: l₁ <+~ l₂
  证明: subperm_of_subset d H
-/
protected theorem Nodup.subperm (d : Nodup l₁) (H : l₁ subseteq l₂) : l₁ <+~ l₂ :=
  subperm_of_subset d H

end List
