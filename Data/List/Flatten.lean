/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
module

public import Mathlib.Tactic.GCongr.Core

/-!
# Join of a list of lists

This file proves basic properties of `List.flatten`, which concatenates a list of lists. It is
defined in `Init.Prelude`.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α β : Type*}

namespace List

@[gcongr]
/--
theorem `Sublist.flatten` / 定理 `Sublist.flatten`

English:
theorem Sublist.flatten
  given: {l₁ l₂ : List (List α)} (h : l₁ <+ l₂)
  proof: by
  induction h with grind

@[gcongr]

中文:
定理 子表.flatten
  条件: {l₁ l₂ : 列表 (列表 α)} (h : l₁ <+ l₂)
  证明: by
  induction h with grind

@[gcongr]
-/
protected theorem Sublist.flatten {l₁ l₂ : List (List α)} (h : l₁ <+ l₂) :
    l₁.flatten <+ l₂.flatten := by
  induction h with grind

@[gcongr]
/--
theorem `Sublist.flatMap` / 定理 `Sublist.flatMap`

English:
theorem Sublist.flatMap
  given: {l₁ l₂ : List α} (h : l₁ <+ l₂) (f : α -> List β)
  proof: (h.map f).flatten

中文:
定理 子表.flatMap
  条件: {l₁ l₂ : 列表 α} (h : l₁ <+ l₂) (f : α -> 列表 β)
  证明: (h.map f).flatten
-/
protected theorem Sublist.flatMap {l₁ l₂ : List α} (h : l₁ <+ l₂) (f : α -> List β) :
    l₁.flatMap f <+ l₂.flatMap f :=
  (h.map f).flatten

/--
theorem `Sublist.flatMap_right` / 定理 `Sublist.flatMap_right`

English:
theorem Sublist.flatMap_right
  given: (l : List α) {f g : α -> List β} (h : forall a in l, f a <+ g a)
  proof: by
  induction l with grind

中文:
定理 子表.flatMap_right
  条件: (l : 列表 α) {f g : α -> 列表 β} (h : 对任意 a in l, f a <+ g a)
  证明: by
  induction l with grind
-/
protected theorem Sublist.flatMap_right (l : List α) {f g : α -> List β} (h : forall a in l, f a <+ g a) :
    l.flatMap f <+ l.flatMap g := by
  induction l with grind

/--
theorem `drop_take_succ_eq_cons_getElem` / 定理 `drop_take_succ_eq_cons_getElem`

English:
theorem drop_take_succ_eq_cons_getElem
  given: (L : List α) (i : Nat) (h : i < L.length)
  proof: by
  induction L generalizing i with grind

中文:
定理 drop_take_succ_eq_cons_getElem
  条件: (L : 列表 α) (i : 自然数) (h : i < L.length)
  证明: by
  induction L generalizing i with grind

Depends on / 依赖: generalizing
-/
theorem drop_take_succ_eq_cons_getElem (L : List α) (i : Nat) (h : i < L.length) :
    (L.take (i + 1)).drop i = [L[i]] := by
  induction L generalizing i with grind

/--
theorem `append_flatten_map_append` / 定理 `append_flatten_map_append`

English:
theorem append_flatten_map_append
  given: (L : List (List α)) (x : List α)
  proof: by
  induction L with grind

中文:
定理 append_flatten_map_append
  条件: (L : 列表 (列表 α)) (x : 列表 α)
  证明: by
  induction L with grind
-/
theorem append_flatten_map_append (L : List (List α)) (x : List α) :
    x ++ (L.map (· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x := by
  induction L with grind

/--
theorem `head_head_eq_head_flatten` / 定理 `head_head_eq_head_flatten`

English:
theorem head_head_eq_head_flatten
  given: {l : List (List α)} (hl : l != []) (hl' : l.head hl != [])
  proof: by
  cases l with grind

中文:
定理 head_head_eq_head_flatten
  条件: {l : 列表 (列表 α)} (hl : l != []) (hl' : l.head hl != [])
  证明: by
  cases l with grind
-/
theorem head_head_eq_head_flatten {l : List (List α)} (hl : l != []) (hl' : l.head hl != []) :
    (l.head hl).head hl' = l.flatten.head (flatten_ne_nil_iff.2 ⟨_, head_mem hl, hl'⟩) := by
  cases l with grind

/--
theorem `head_flatten_eq_head_head` / 定理 `head_flatten_eq_head_head`

English:
theorem head_flatten_eq_head_head
  statement: {l : List (List α)} (hl : l.flatten != [])
  proof: (head_head_eq_head_flatten ..).symm

中文:
定理 head_flatten_eq_head_head
  结论: {l : 列表 (列表 α)} (hl : l.flatten != [])
  证明: (head_head_eq_head_flatten ..).symm

Depends on / 依赖: head_head_eq_head_flatten
-/
theorem head_flatten_eq_head_head {l : List (List α)} (hl : l.flatten != [])
    (hl' : l.head (by grind) != []) : l.flatten.head hl = (l.head (by grind)).head hl' :=
  (head_head_eq_head_flatten ..).symm

/--
theorem `getLast_getLast_eq_getLast_flatten` / 定理 `getLast_getLast_eq_getLast_flatten`

English:
theorem getLast_getLast_eq_getLast_flatten
  statement: {l : List (List α)}
  proof: by
  cases eq_nil_or_concat l with grind

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_getLast_ne_nil := getLast_getLast_eq_getLast_flatten

中文:
定理 getLast_getLast_eq_getLast_flatten
  结论: {l : 列表 (列表 α)}
  证明: by
  cases eq_nil_or_concat l with grind

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_getLast_ne_nil := getLast_getLast_eq_getLast_flatten

Depends on / 依赖: eq_nil_or_concat
-/
theorem getLast_getLast_eq_getLast_flatten {l : List (List α)}
    (hl : l != []) (hl' : l.getLast hl != []) :
    (l.getLast hl).getLast hl' =
      l.flatten.getLast (flatten_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩) := by
  cases eq_nil_or_concat l with grind

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_getLast_ne_nil := getLast_getLast_eq_getLast_flatten

/--
theorem `getLast_flatten_eq_getLast_getLast` / 定理 `getLast_flatten_eq_getLast_getLast`

English:
theorem getLast_flatten_eq_getLast_getLast
  statement: {l : List (List α)}
  proof: (getLast_getLast_eq_getLast_flatten ..).symm

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_flatten_ne_nil := getLast_flatten_eq_getLast_getLast

中文:
定理 getLast_flatten_eq_getLast_getLast
  结论: {l : 列表 (列表 α)}
  证明: (getLast_getLast_eq_getLast_flatten ..).symm

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_flatten_ne_nil := getLast_flatten_eq_getLast_getLast

Depends on / 依赖: getLast_getLast_eq_getLast_flatten
-/
theorem getLast_flatten_eq_getLast_getLast {l : List (List α)}
    (hl : l.flatten != []) (hl' : l.getLast (by grind) != []) :
    l.flatten.getLast hl = (l.getLast (by grind)).getLast hl' :=
  (getLast_getLast_eq_getLast_flatten ..).symm

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_flatten_ne_nil := getLast_flatten_eq_getLast_getLast

end List
