/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison
-/
module

public import Mathlib.Data.List.Chain

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'`
and defines `List.finRange`.
`finRange n` is the list of elements of `Fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

@[expose] public section

universe u

open Nat

namespace List

variable {α : Type u}

/--
theorem `getElem_range'_1` / 定理 `getElem_range'_1`

English:
theorem getElem_range'_1
  given: {n m} (i) (H : i < (range' n m).length)
  proof: by simp

中文:
定理 getElem_range'_1
  条件: {n m} (i) (H : i < (range' n m).length)
  证明: by simp
-/
theorem getElem_range'_1 {n m} (i) (H : i < (range' n m).length) :
    (range' n m)[i] = n + i := by simp

/--
theorem `isChain_range` / 定理 `isChain_range`

English:
theorem isChain_range
  given: (r : Nat -> Nat -> Prop) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn]; rw [forall_lt_succ_right]

中文:
定理 isChain_range
  条件: (r : 自然数 -> 自然数 -> 命题) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn]; rw [forall_lt_succ_right]

Depends on / 依赖: IsChain, IsChain.singleton, Nat.add_lt_add_iff_right, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt, add_lt_add_iff_right, add_one_sub_one, and_true, append_assoc, cons_append, forall_lt_succ_right, isChain_append_cons_cons, lt_sub_iff_add_lt, nil_append, range_succ, singleton, succ_eq_add_one
-/
theorem isChain_range (r : Nat -> Nat -> Prop) (n : Nat) :
    IsChain r (range n) ↔ forall m < n - 1, r m m.succ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn]; rw [forall_lt_succ_right]

/--
theorem `isChain_range_succ` / 定理 `isChain_range_succ`

English:
theorem isChain_range_succ
  given: (r : Nat -> Nat -> Prop) (n : Nat)
  proof: by
  rw [isChain_range]; rw [succ_eq_add_one]; rw [Nat.add_one_sub_one]

中文:
定理 isChain_range_succ
  条件: (r : 自然数 -> 自然数 -> 命题) (n : 自然数)
  证明: by
  rw [isChain_range]; rw [succ_eq_add_one]; rw [Nat.add_one_sub_one]

Depends on / 依赖: Nat.add_one_sub_one, add_one_sub_one, isChain_range, succ_eq_add_one
-/
theorem isChain_range_succ (r : Nat -> Nat -> Prop) (n : Nat) :
    IsChain r (range n.succ) ↔ forall m < n, r m m.succ := by
  rw [isChain_range]; rw [succ_eq_add_one]; rw [Nat.add_one_sub_one]

/--
theorem `isChain_cons_range_succ` / 定理 `isChain_cons_range_succ`

English:
theorem isChain_cons_range_succ
  given: (r : Nat -> Nat -> Prop) (n a : Nat)
  proof: by
  rw [range_succ_eq_map]; rw [isChain_cons_cons]; rw [and_congr_right_iff]; rw [← isChain_range_succ]; rw [range_succ_eq_map]
  exact fun _ => Iff.rfl

中文:
定理 isChain_cons_range_succ
  条件: (r : 自然数 -> 自然数 -> 命题) (n a : 自然数)
  证明: by
  rw [range_succ_eq_map]; rw [isChain_cons_cons]; rw [and_congr_right_iff]; rw [← isChain_range_succ]; rw [range_succ_eq_map]
  exact fun _ => Iff.rfl

Depends on / 依赖: Iff.rfl, and_congr_right_iff, isChain_cons_cons, isChain_range_succ, range_succ_eq_map
-/
theorem isChain_cons_range_succ (r : Nat -> Nat -> Prop) (n a : Nat) :
    IsChain r (a :: range n.succ) ↔ r a 0 ∧ forall m < n, r m m.succ := by
  rw [range_succ_eq_map]; rw [isChain_cons_cons]; rw [and_congr_right_iff]; rw [← isChain_range_succ]; rw [range_succ_eq_map]
  exact fun _ => Iff.rfl

section Ranges

/--
Definition of `ranges` / `ranges` 的定义

English:
definition ranges
  signature: : List Nat -> List (List Nat)

中文:
定义 ranges
  签名: : 列表 自然数 -> 列表 (列表 自然数)
-/
def ranges : List Nat -> List (List Nat)
  | [] => nil
  | a::l => range a::(ranges l).map (map (a + ·))

/--
theorem `ranges_disjoint` / 定理 `ranges_disjoint`

English:
theorem ranges_disjoint
  given: (l : List Nat)
  proof: by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

中文:
定理 ranges_disjoint
  条件: (l : 列表 自然数)
  证明: by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

Depends on / 依赖: Nat.add_left_cancel, Pairwise, Pairwise.imp, Pairwise.nil, add_left_cancel, disjoint_map, mem_map, mem_map.mp, mem_range, pairwise_cons, pairwise_map, ranges
-/
theorem ranges_disjoint (l : List Nat) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

/--
theorem `ranges_length` / 定理 `ranges_length`

English:
theorem ranges_length
  given: (l : List Nat)
  proof: by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [ranges, map_cons, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

中文:
定理 ranges_length
  条件: (l : 列表 自然数)
  证明: by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [ranges, map_cons, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, cons.injEq, conv_rhs, length_map, length_range, map_congr_left, map_cons, map_map, map_nil, ranges, true_and
-/
theorem ranges_length (l : List Nat) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [ranges, map_cons, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

end Ranges

end List
