/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Perm
public import Mathlib.Tactic.Common
public import Batteries.Data.List.Lemmas

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively.
-/

public section

assert_not_exists Monoid Set.range

open Nat

variable {α β : Type*}

namespace List

@[simp]
/--
theorem `countP_lt_length_iff` / 定理 `countP_lt_length_iff`

English:
theorem countP_lt_length_iff
  given: {l : List α} {p : α -> Bool}
  proof: by
  simp [Nat.lt_iff_le_and_ne, countP_le_length]

中文:
定理 countP_lt_length_iff
  条件: {l : List α} {p : α -> 布尔}
  证明: by
  simp [Nat.lt_iff_le_and_ne, countP_le_length]

Depends on / 依赖: Nat.lt_iff_le_and_ne, countP_le_length, lt_iff_le_and_ne
-/
theorem countP_lt_length_iff {l : List α} {p : α -> Bool} :
    l.countP p < l.length ↔ exists a in l, p a = false := by
  simp [Nat.lt_iff_le_and_ne, countP_le_length]

variable [BEq α] [LawfulBEq α] {l l₁ l₂ : List α}

@[simp]
/--
theorem `count_lt_length_iff` / 定理 `count_lt_length_iff`

English:
theorem count_lt_length_iff
  given: {a : α}
  statement: l.count a < l.length ↔ exists b in l, b != a
  proof: by simp [count]

中文:
定理 count_lt_length_iff
  条件: {a : α}
  结论: l.count a < l.length ↔ 存在 b in l, b != a
  证明: by simp [count]
-/
theorem count_lt_length_iff {a : α} : l.count a < l.length ↔ exists b in l, b != a := by simp [count]

/--
lemma `countP_erase` / 引理 `countP_erase`

English:
lemma countP_erase
  given: (p : α -> Bool) (l : List α) (a : α)
  proof: by
  grind [countP_eq_length_filter]

中文:
引理 countP_erase
  条件: (p : α -> 布尔) (l : List α) (a : α)
  证明: by
  grind [countP_eq_length_filter]

Depends on / 依赖: countP_eq_length_filter
-/
lemma countP_erase (p : α -> Bool) (l : List α) (a : α) :
    countP p (l.erase a) = countP p l - if a in l ∧ p a then 1 else 0 := by
  grind [countP_eq_length_filter]

/--
lemma `count_diff` / 引理 `count_diff`

English:
lemma count_diff
  given: (a : α) (l₁ : List α)

中文:
引理 count_diff
  条件: (a : α) (l₁ : List α)
-/
lemma count_diff (a : α) (l₁ : List α) :
    forall l₂, count a (l₁.diff l₂) = count a l₁ - count a l₂
  | [] => rfl
  | b :: l₂ => by
    simp only [diff_cons, count_diff, count_erase, beq_iff_eq, Nat.sub_right_comm, count_cons,
      Nat.sub_add_eq]

/--
lemma `countP_diff` / 引理 `countP_diff`

English:
lemma countP_diff
  given: (hl : l₂ <+~ l₁) (p : α -> Bool)
  proof: by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [← countP_append]
  exact ((subperm_append_diff_self_of_count_le <| subperm_ext_iff.1 hl).symm.trans
    perm_append_comm).countP_eq _

@[simp]

中文:
引理 countP_diff
  条件: (hl : l₂ <+~ l₁) (p : α -> 布尔)
  证明: by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [← countP_append]
  exact ((subperm_append_diff_self_of_count_le <| subperm_ext_iff.1 hl).symm.trans
    perm_append_comm).countP_eq _

@[simp]

Depends on / 依赖: Nat.sub_eq_of_eq_add, countP_append, countP_eq, perm_append_comm, sub_eq_of_eq_add, subperm_append_diff_self_of_count_le, subperm_ext_iff, symm.trans
-/
lemma countP_diff (hl : l₂ <+~ l₁) (p : α -> Bool) :
    countP p (l₁.diff l₂) = countP p l₁ - countP p l₂ := by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [← countP_append]
  exact ((subperm_append_diff_self_of_count_le <| subperm_ext_iff.1 hl).symm.trans
    perm_append_comm).countP_eq _

@[simp]
/--
theorem `count_map_of_injective` / 定理 `count_map_of_injective`

English:
theorem count_map_of_injective
  statement: [BEq β] [LawfulBEq β] (l : List α) (f : α -> β)
  proof: by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]

中文:
定理 count_map_of_injective
  结论: [BEq β] [LawfulBEq β] (l : List α) (f : α -> β)
  证明: by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]

Depends on / 依赖: Function, Function.comp, beq_eq, countP_map, hf.beq_eq
-/
theorem count_map_of_injective [BEq β] [LawfulBEq β] (l : List α) (f : α -> β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map]
  unfold Function.comp
  simp only [hf.beq_eq]

end List
