/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Cast.Basic

/-!
# Cardinality of a finite set and subtraction

This file contains results on the cardinality of a `Finset` and subtraction, by casting the
cardinality as element of an `AddGroupWithOne`.

## Main results

* `Finset.cast_card_erase_of_mem`: erasing an element of a finset decrements the cardinality
  (avoiding `ℕ` subtraction).
* `Finset.cast_card_inter`, `Finset.cast_card_union`: inclusion/exclusion principle.
* `Finset.cast_card_sdiff`: cardinality of `t \ s` is the difference of cardinalities if `s ⊆ t`.
-/

public section

assert_not_exists MonoidWithZero IsOrderedMonoid

open Nat

namespace Finset

variable {α R : Type*} {s t : Finset α} {a b : α}
variable [DecidableEq α] [AddGroupWithOne R]

-- @[simp] -- removed because LHS is not in simp normal form
/--
theorem `cast_card_erase_of_mem` / 定理 `cast_card_erase_of_mem`

English:
theorem cast_card_erase_of_mem
  given: (hs : a in s)
  statement: (#(s.erase a) : R) = #s - 1
  proof: by
  rw [← card_erase_add_one hs]; rw [cast_add]; rw [cast_one]; rw [eq_sub_iff_add_eq]

中文:
定理 cast_card_erase_of_mem
  条件: (hs : a in s)
  结论: (#(s.erase a) : R) = #s - 1
  证明: by
  rw [← card_erase_add_one hs]; rw [cast_add]; rw [cast_one]; rw [eq_sub_iff_add_eq]

Depends on / 依赖: card_erase_add_one, cast_add, cast_one, eq_sub_iff_add_eq
-/
theorem cast_card_erase_of_mem (hs : a in s) : (#(s.erase a) : R) = #s - 1 := by
  rw [← card_erase_add_one hs]; rw [cast_add]; rw [cast_one]; rw [eq_sub_iff_add_eq]

/--
lemma `cast_card_inter` / 引理 `cast_card_inter`

English:
lemma cast_card_inter
  statement: (#(s inter t) : R) = #s + #t - #(s union t)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_inter_add_card_union]; rw [cast_add]

中文:
引理 cast_card_inter
  结论: (#(s inter t) : R) = #s + #t - #(s union t)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_inter_add_card_union]; rw [cast_add]

Depends on / 依赖: card_inter_add_card_union, cast_add, eq_sub_iff_add_eq
-/
lemma cast_card_inter : (#(s inter t) : R) = #s + #t - #(s union t) := by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_inter_add_card_union]; rw [cast_add]

/--
lemma `cast_card_union` / 引理 `cast_card_union`

English:
lemma cast_card_union
  statement: (#(s union t) : R) = #s + #t - #(s inter t)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_union_add_card_inter]; rw [cast_add]

中文:
引理 cast_card_union
  结论: (#(s union t) : R) = #s + #t - #(s inter t)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_union_add_card_inter]; rw [cast_add]

Depends on / 依赖: card_union_add_card_inter, cast_add, eq_sub_iff_add_eq
-/
lemma cast_card_union : (#(s union t) : R) = #s + #t - #(s inter t) := by
  rw [eq_sub_iff_add_eq]; rw [← cast_add]; rw [card_union_add_card_inter]; rw [cast_add]

/--
lemma `cast_card_sdiff` / 引理 `cast_card_sdiff`

English:
lemma cast_card_sdiff
  given: (h : s subseteq t)
  statement: (#(t \ s) : R) = #t - #s
  proof: by
  rw [card_sdiff_of_subset h]; rw [Nat.cast_sub (card_mono h)]

中文:
引理 cast_card_sdiff
  条件: (h : s subseteq t)
  结论: (#(t \ s) : R) = #t - #s
  证明: by
  rw [card_sdiff_of_subset h]; rw [Nat.cast_sub (card_mono h)]

Depends on / 依赖: Nat.cast_sub, card_mono, card_sdiff_of_subset, cast_sub
-/
lemma cast_card_sdiff (h : s subseteq t) : (#(t \ s) : R) = #t - #s := by
  rw [card_sdiff_of_subset h]; rw [Nat.cast_sub (card_mono h)]

end Finset
