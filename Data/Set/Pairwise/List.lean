/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Translating pairwise relations on sets to lists

On a list with no duplicates, the condition of `Set.Pairwise` and `List.Pairwise` are equivalent.
-/

public section


variable {α : Type*} {r : α -> α -> Prop}

namespace List

variable {l : List α}

/--
theorem `Nodup.pairwise_of_set_pairwise` / 定理 `Nodup.pairwise_of_set_pairwise`

English:
theorem Nodup.pairwise_of_set_pairwise
  statement: {l : List α} {r : α -> α -> Prop} (hl : l.Nodup)
  proof: hl.pairwise_of_forall_ne h

@[simp]

中文:
定理 Nodup.pairwise_of_set_pairwise
  结论: {l : List α} {r : α -> α -> 命题} (hl : l.Nodup)
  证明: hl.pairwise_of_forall_ne h

@[simp]

Depends on / 依赖: hl.pairwise_of_forall_ne, pairwise_of_forall_ne
-/
theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α -> α -> Prop} (hl : l.Nodup)
    (h : {x | x in l}.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h

@[simp]
/--
theorem `Nodup.pairwise_coe` / 定理 `Nodup.pairwise_coe`

English:
theorem Nodup.pairwise_coe
  given: [Std.Symm r] (hl : l.Nodup)
  proof: by
  induction l with | nil => simp | cons a l ih => ?_
  rw [List.nodup_cons] at hl
  have : forall b in l, ¬a = b -> r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.ofPred_or, Set.pairwise_insert_of_symm, ih hl.2, and_comm, forall₂_congr this]

中文:
定理 Nodup.pairwise_coe
  条件: [Std.Symm r] (hl : l.Nodup)
  证明: by
  induction l with | nil => simp | cons a l ih => ?_
  rw [List.nodup_cons] at hl
  have : forall b in l, ¬a = b -> r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.ofPred_or, Set.pairwise_insert_of_symm, ih hl.2, and_comm, forall₂_congr this]

Depends on / 依赖: List.nodup_cons, Set.ofPred_or, Set.pairwise_insert_of_symm, and_comm, imp_iff_right, ne_of_mem_of_not_mem, nodup_cons, ofPred_or, pairwise_insert_of_symm
-/
theorem Nodup.pairwise_coe [Std.Symm r] (hl : l.Nodup) :
    { a | a in l }.Pairwise r ↔ l.Pairwise r := by
  induction l with | nil => simp | cons a l ih => ?_
  rw [List.nodup_cons] at hl
  have : forall b in l, ¬a = b -> r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.ofPred_or, Set.pairwise_insert_of_symm, ih hl.2, and_comm, forall₂_congr this]

end List
