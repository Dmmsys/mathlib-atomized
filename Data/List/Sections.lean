/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Forall2
/-!
# List sections

This file proves some stuff about `List.sections` (definition in `Data.List.Defs`). A section of a
list of lists `[l₁, ..., lₙ]` is a list whose `i`-th element comes from the `i`-th list.
-/

public section


open Nat Function

namespace List

variable {α β : Type*}

/--
theorem `mem_sections` / 定理 `mem_sections`

English:
theorem mem_sections
  given: {L : List (List α)} {f}
  statement: f in sections L ↔ Forall₂ (· in ·) f L
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact Forall₂.nil
    simp only [sections, mem_flatMap, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and]
  · induction h with
    | nil => simp only [sections, mem_singleton]
    | @cons a l f L al fL fs =>
      simp only [sections, mem_flatMap, mem_map]
      exact ⟨f, fs, a, al, rfl⟩

中文:
定理 mem_sections
  条件: {L : 列表 (列表 α)} {f}
  结论: f in sections L ↔ Forall₂ (· in ·) f L
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact Forall₂.nil
    simp only [sections, mem_flatMap, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and]
  · induction h with
    | nil => simp only [sections, mem_singleton]
    | @cons a l f L al fL fs =>
      simp only [sections, mem_flatMap, mem_map]
      exact ⟨f, fs, a, al, rfl⟩

Depends on / 依赖: generalizing, mem_flatMap, mem_map, mem_singleton, sections, true_and
-/
theorem mem_sections {L : List (List α)} {f} : f in sections L ↔ Forall₂ (· in ·) f L := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact Forall₂.nil
    simp only [sections, mem_flatMap, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and]
  · induction h with
    | nil => simp only [sections, mem_singleton]
    | @cons a l f L al fL fs =>
      simp only [sections, mem_flatMap, mem_map]
      exact ⟨f, fs, a, al, rfl⟩

/--
theorem `mem_sections_length` / 定理 `mem_sections_length`

English:
theorem mem_sections_length
  given: {L : List (List α)} {f} (h : f in sections L)
  statement: length f = length L
  proof: (mem_sections.1 h).length_eq

中文:
定理 mem_sections_length
  条件: {L : 列表 (列表 α)} {f} (h : f in sections L)
  结论: length f = length L
  证明: (mem_sections.1 h).length_eq

Depends on / 依赖: length_eq, mem_sections
-/
theorem mem_sections_length {L : List (List α)} {f} (h : f in sections L) : length f = length L :=
  (mem_sections.1 h).length_eq

open scoped Relator in
/--
theorem `rel_sections` / 定理 `rel_sections`

English:
theorem rel_sections
  given: {r : α -> β -> Prop}

中文:
定理 rel_sections
  条件: {r : α -> β -> 命题}
-/
theorem rel_sections {r : α -> β -> Prop} :
    (Forall₂ (Forall₂ r) ⇒ Forall₂ (Forall₂ r)) sections sections
  | _, _, Forall₂.nil => Forall₂.cons Forall₂.nil Forall₂.nil
  | _, _, Forall₂.cons h₀ h₁ =>
    rel_flatMap (rel_sections h₁) fun _ _ hl => rel_map (fun _ _ ha => Forall₂.cons ha hl) h₀

end List
