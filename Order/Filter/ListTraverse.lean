/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Control.Traversable.Instances
public import Mathlib.Order.Filter.Map
/-!
# Properties of `Traversable.traverse` on `List`s and `Filter`s

In this file we prove basic properties (monotonicity, membership)
for `Traversable.traverse f l`, where `f : β → Filter α` and `l : List β`.
-/

public section

open Set List

namespace Filter

universe u

variable {α β γ : Type u} {f : β -> Filter α} {s : γ -> Set α}

/--
theorem `sequence_mono` / 定理 `sequence_mono`

English:
theorem sequence_mono
  statement: forall as bs : List (Filter α), Forall₂ (· <= ·) as bs -> sequence as <= sequence bs

中文:
定理 sequence_mono
  结论: 对任意 as bs : List (Filter α), Forall₂ (· <= ·) as bs -> sequence as <= sequence bs
-/
theorem sequence_mono : forall as bs : List (Filter α), Forall₂ (· <= ·) as bs -> sequence as <= sequence bs
  | [], [], Forall₂.nil => le_rfl
  | _::as, _::bs, Forall₂.cons h hs => seq_mono (map_mono h) (sequence_mono as bs hs)

/--
theorem `mem_traverse` / 定理 `mem_traverse`

English:
theorem mem_traverse

中文:
定理 mem_traverse
-/
theorem mem_traverse :
    forall (fs : List β) (us : List γ),
      Forall₂ (fun b c => s c in f b) fs us -> traverse s us in traverse f fs
| [], [], Forall₂.nil => mem_pure.2 mem_singleton _
  | _::fs, _::us, Forall₂.cons h hs => seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)

-- TODO: add a `Filter.HasBasis` statement
/--
theorem `mem_traverse_iff` / 定理 `mem_traverse_iff`

English:
theorem mem_traverse_iff
  given: (fs : List β) (t : Set (List α))
  proof: by
  constructor
  · induction fs generalizing t with
    | nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    | cons b fs ih =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩

中文:
定理 mem_traverse_iff
  条件: (fs : List β) (t : Set (List α))
  证明: by
  constructor
  · induction fs generalizing t with
    | nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    | cons b fs ih =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩

Depends on / 依赖: Set.pure_def, Set.seq_mono, exists_eq_left, generalizing, imp_self, mem_map_iff_exists_image, mem_of_superset, mem_pure, mem_seq_iff, mem_traverse, pure_def, seq_mono, sequence, singleton_subset_iff, traverse_nil
-/
theorem mem_traverse_iff (fs : List β) (t : Set (List α)) :
    t in traverse f fs ↔
      exists us : List (Set α), Forall₂ (fun b (s : Set α) => s in f b) fs us ∧ sequence us subseteq t := by
  constructor
  · induction fs generalizing t with
    | nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    | cons b fs ih =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩
      rcases ih v hv with ⟨us, hus, hu⟩
      exact ⟨w::us, Forall₂.cons hw hus, (Set.seq_mono hwu hu).trans ht⟩
  · rintro ⟨us, hus, hs⟩
    exact mem_of_superset (mem_traverse _ _ hus) hs

end Filter
