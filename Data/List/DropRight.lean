/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.List.Basic

/-!

# Dropping or taking from lists on the right

Taking or removing element from the tail end of a list

## Main definitions

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `rdropWhile p`: remove all the elements from the tail of a list until it finds the first element
  for which `p : α → Bool` returns false. This element and everything before is returned.
- `rtakeWhile p`: Returns the longest terminal segment of a list for which `p : α → Bool` returns
  true.

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`List.reverse`, followed by another `List.reverse`, so they are not the most performant.
The other two rely on `List.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/

@[expose] public section

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α : Type*} (p : α -> Bool) (l : List α) (n : Nat)

namespace List

/--
Definition of `rdrop` / `rdrop` 的定义

English:
definition rdrop
  signature: : List α
  body: l.take (l.length - n)

@[simp]

中文:
定义 rdrop
  签名: : 列表 α
  定义体: l.take (l.length - n)

@[simp]

Depends on / 依赖: l.length, l.take, length
-/
def rdrop : List α :=
  l.take (l.length - n)

@[simp]
/--
theorem `rdrop_nil` / 定理 `rdrop_nil`

English:
theorem rdrop_nil
  statement: rdrop ([] : List α) n = []
  proof: by simp [rdrop]

@[simp]

中文:
定理 rdrop_nil
  结论: rdrop ([] : 列表 α) n = []
  证明: by simp [rdrop]

@[simp]
-/
theorem rdrop_nil : rdrop ([] : List α) n = [] := by simp [rdrop]

@[simp]
/--
theorem `rdrop_zero` / 定理 `rdrop_zero`

English:
theorem rdrop_zero
  statement: rdrop l 0 = l
  proof: by simp [rdrop]

中文:
定理 rdrop_zero
  结论: rdrop l 0 = l
  证明: by simp [rdrop]
-/
theorem rdrop_zero : rdrop l 0 = l := by simp [rdrop]

/--
theorem `rdrop_eq_reverse_drop_reverse` / 定理 `rdrop_eq_reverse_drop_reverse`

English:
theorem rdrop_eq_reverse_drop_reverse
  statement: l.rdrop n = reverse (l.reverse.drop n)
  proof: by
  rw [rdrop]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · simp [take_length_add_append]
    · simp [take_append, IH]

@[simp]

中文:
定理 rdrop_eq_reverse_drop_reverse
  结论: l.rdrop n = reverse (l.reverse.drop n)
  证明: by
  rw [rdrop]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · simp [take_length_add_append]
    · simp [take_append, IH]

@[simp]

Depends on / 依赖: List.reverseRecOn, append_singleton, generalizing, reverseRecOn, take_append, take_length_add_append
-/
theorem rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) := by
  rw [rdrop]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · simp [take_length_add_append]
    · simp [take_append, IH]

@[simp]
/--
theorem `rdrop_concat_succ` / 定理 `rdrop_concat_succ`

English:
theorem rdrop_concat_succ
  given: (x : α)
  statement: rdrop (l ++ [x]) (n + 1) = rdrop l n
  proof: by
  simp [rdrop_eq_reverse_drop_reverse]

中文:
定理 rdrop_concat_succ
  条件: (x : α)
  结论: rdrop (l ++ [x]) (n + 1) = rdrop l n
  证明: by
  simp [rdrop_eq_reverse_drop_reverse]

Depends on / 依赖: rdrop_eq_reverse_drop_reverse
-/
theorem rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n := by
  simp [rdrop_eq_reverse_drop_reverse]

/--
Definition of `rtake` / `rtake` 的定义

English:
definition rtake
  signature: : List α
  body: l.drop (l.length - n)

@[simp]

中文:
定义 rtake
  签名: : 列表 α
  定义体: l.drop (l.length - n)

@[simp]

Depends on / 依赖: l.drop, l.length, length
-/
def rtake : List α :=
  l.drop (l.length - n)

@[simp]
/--
theorem `rtake_nil` / 定理 `rtake_nil`

English:
theorem rtake_nil
  statement: rtake ([] : List α) n = []
  proof: by simp [rtake]

@[simp]

中文:
定理 rtake_nil
  结论: rtake ([] : 列表 α) n = []
  证明: by simp [rtake]

@[simp]
-/
theorem rtake_nil : rtake ([] : List α) n = [] := by simp [rtake]

@[simp]
/--
theorem `rtake_zero` / 定理 `rtake_zero`

English:
theorem rtake_zero
  statement: rtake l 0 = []
  proof: by simp [rtake]

中文:
定理 rtake_zero
  结论: rtake l 0 = []
  证明: by simp [rtake]
-/
theorem rtake_zero : rtake l 0 = [] := by simp [rtake]

/--
theorem `rtake_eq_reverse_take_reverse` / 定理 `rtake_eq_reverse_take_reverse`

English:
theorem rtake_eq_reverse_take_reverse
  statement: l.rtake n = reverse (l.reverse.take n)
  proof: by
  rw [rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact drop_length
    · simp [drop_append, IH]

@[simp]

中文:
定理 rtake_eq_reverse_take_reverse
  结论: l.rtake n = reverse (l.reverse.take n)
  证明: by
  rw [rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact drop_length
    · simp [drop_append, IH]

@[simp]

Depends on / 依赖: List.reverseRecOn, append_singleton, drop_append, drop_length, generalizing, reverseRecOn
-/
theorem rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) := by
  rw [rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact drop_length
    · simp [drop_append, IH]

@[simp]
/--
theorem `rtake_concat_succ` / 定理 `rtake_concat_succ`

English:
theorem rtake_concat_succ
  given: (x : α)
  statement: rtake (l ++ [x]) (n + 1) = rtake l n ++ [x]
  proof: by
  simp [rtake_eq_reverse_take_reverse]

中文:
定理 rtake_concat_succ
  条件: (x : α)
  结论: rtake (l ++ [x]) (n + 1) = rtake l n ++ [x]
  证明: by
  simp [rtake_eq_reverse_take_reverse]

Depends on / 依赖: rtake_eq_reverse_take_reverse
-/
theorem rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]

/--
Definition of `rdropWhile` / `rdropWhile` 的定义

English:
definition rdropWhile
  signature: : List α
  body: reverse (l.reverse.dropWhile p)

@[simp]

中文:
定义 rdropWhile
  签名: : 列表 α
  定义体: reverse (l.reverse.dropWhile p)

@[simp]

Depends on / 依赖: dropWhile, l.reverse.dropWhile, reverse
-/
def rdropWhile : List α :=
  reverse (l.reverse.dropWhile p)

@[simp]
/--
theorem `rdropWhile_nil` / 定理 `rdropWhile_nil`

English:
theorem rdropWhile_nil
  statement: rdropWhile p ([] : List α) = []
  proof: by simp [rdropWhile]

中文:
定理 rdropWhile_nil
  结论: rdropWhile p ([] : 列表 α) = []
  证明: by simp [rdropWhile]

Depends on / 依赖: rdropWhile
-/
theorem rdropWhile_nil : rdropWhile p ([] : List α) = [] := by simp [rdropWhile]

/--
theorem `rdropWhile_concat` / 定理 `rdropWhile_concat`

English:
theorem rdropWhile_concat
  given: (x : α)
  proof: by
  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]

中文:
定理 rdropWhile_concat
  条件: (x : α)
  证明: by
  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]

Depends on / 依赖: dropWhile, rdropWhile, reverse_append, reverse_singleton, singleton_append, split_ifs
-/
theorem rdropWhile_concat (x : α) :
    rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x] := by
  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]
/--
theorem `rdropWhile_concat_pos` / 定理 `rdropWhile_concat_pos`

English:
theorem rdropWhile_concat_pos
  given: (x : α) (h : p x)
  statement: rdropWhile p (l ++ [x]) = rdropWhile p l
  proof: by
  rw [rdropWhile_concat]; rw [if_pos h]

@[simp]

中文:
定理 rdropWhile_concat_pos
  条件: (x : α) (h : p x)
  结论: rdropWhile p (l ++ [x]) = rdropWhile p l
  证明: by
  rw [rdropWhile_concat]; rw [if_pos h]

@[simp]

Depends on / 依赖: if_pos, rdropWhile_concat
-/
theorem rdropWhile_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropWhile p l := by
  rw [rdropWhile_concat]; rw [if_pos h]

@[simp]
/--
theorem `rdropWhile_concat_neg` / 定理 `rdropWhile_concat_neg`

English:
theorem rdropWhile_concat_neg
  given: (x : α) (h : ¬p x)
  statement: rdropWhile p (l ++ [x]) = l ++ [x]
  proof: by
  rw [rdropWhile_concat]; rw [if_neg h]

中文:
定理 rdropWhile_concat_neg
  条件: (x : α) (h : ¬p x)
  结论: rdropWhile p (l ++ [x]) = l ++ [x]
  证明: by
  rw [rdropWhile_concat]; rw [if_neg h]

Depends on / 依赖: if_neg, rdropWhile_concat
-/
theorem rdropWhile_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdropWhile_concat]; rw [if_neg h]

/--
theorem `rdropWhile_singleton` / 定理 `rdropWhile_singleton`

English:
theorem rdropWhile_singleton
  given: (x : α)
  statement: rdropWhile p [x] = if p x then [] else [x]
  proof: by
  rw [← nil_append [x], rdropWhile_concat, rdropWhile_nil]

中文:
定理 rdropWhile_singleton
  条件: (x : α)
  结论: rdropWhile p [x] = if p x then [] else [x]
  证明: by
  rw [← nil_append [x], rdropWhile_concat, rdropWhile_nil]

Depends on / 依赖: nil_append, rdropWhile_concat, rdropWhile_nil
-/
theorem rdropWhile_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdropWhile_concat, rdropWhile_nil]

/--
theorem `rdropWhile_last_not` / 定理 `rdropWhile_last_not`

English:
theorem rdropWhile_last_not
  given: (hl : l.rdropWhile p != [])
  statement: ¬p ((rdropWhile p l).getLast hl)
  proof: by
  simp_rw [rdropWhile]
  rw [getLast_reverse]; rw [head_dropWhile_not p]
  simp

中文:
定理 rdropWhile_last_not
  条件: (hl : l.rdropWhile p != [])
  结论: ¬p ((rdropWhile p l).getLast hl)
  证明: by
  simp_rw [rdropWhile]
  rw [getLast_reverse]; rw [head_dropWhile_not p]
  simp

Depends on / 依赖: getLast_reverse, head_dropWhile_not, rdropWhile, simp_rw
-/
theorem rdropWhile_last_not (hl : l.rdropWhile p != []) : ¬p ((rdropWhile p l).getLast hl) := by
  simp_rw [rdropWhile]
  rw [getLast_reverse]; rw [head_dropWhile_not p]
  simp

/--
theorem `rdropWhile_prefix` / 定理 `rdropWhile_prefix`

English:
theorem rdropWhile_prefix
  statement: l.rdropWhile p <+: l
  proof: by
  rw [← reverse_suffix]; rw [rdropWhile]; rw [reverse_reverse]
  exact dropWhile_suffix _

中文:
定理 rdropWhile_prefix
  结论: l.rdropWhile p <+: l
  证明: by
  rw [← reverse_suffix]; rw [rdropWhile]; rw [reverse_reverse]
  exact dropWhile_suffix _

Depends on / 依赖: dropWhile_suffix, rdropWhile, reverse_reverse, reverse_suffix
-/
theorem rdropWhile_prefix : l.rdropWhile p <+: l := by
  rw [← reverse_suffix]; rw [rdropWhile]; rw [reverse_reverse]
  exact dropWhile_suffix _

variable {p} {l}

@[simp]
/--
theorem `rdropWhile_eq_nil_iff` / 定理 `rdropWhile_eq_nil_iff`

English:
theorem rdropWhile_eq_nil_iff
  statement: rdropWhile p l = [] ↔ forall x in l, p x
  proof: by simp [rdropWhile]

@[simp]

中文:
定理 rdropWhile_eq_nil_iff
  结论: rdropWhile p l = [] ↔ 对任意 x in l, p x
  证明: by simp [rdropWhile]

@[simp]

Depends on / 依赖: rdropWhile
-/
theorem rdropWhile_eq_nil_iff : rdropWhile p l = [] ↔ forall x in l, p x := by simp [rdropWhile]

@[simp]
/--
theorem `rdropWhile_eq_self_iff` / 定理 `rdropWhile_eq_self_iff`

English:
theorem rdropWhile_eq_self_iff
  statement: rdropWhile p l = l ↔ forall hl : l != [], ¬p (l.getLast hl)
  proof: by
  simp [rdropWhile, reverse_eq_iff, getLast_eq_getElem, Nat.pos_iff_ne_zero]

中文:
定理 rdropWhile_eq_self_iff
  结论: rdropWhile p l = l ↔ 对任意 hl : l != [], ¬p (l.getLast hl)
  证明: by
  simp [rdropWhile, reverse_eq_iff, getLast_eq_getElem, Nat.pos_iff_ne_zero]

Depends on / 依赖: Nat.pos_iff_ne_zero, getLast_eq_getElem, pos_iff_ne_zero, rdropWhile, reverse_eq_iff
-/
theorem rdropWhile_eq_self_iff : rdropWhile p l = l ↔ forall hl : l != [], ¬p (l.getLast hl) := by
  simp [rdropWhile, reverse_eq_iff, getLast_eq_getElem, Nat.pos_iff_ne_zero]

variable (p) (l)

/--
theorem `dropWhile_idempotent` / 定理 `dropWhile_idempotent`

English:
theorem dropWhile_idempotent
  statement: dropWhile p (dropWhile p l) = dropWhile p l
  proof: by
  simp only [dropWhile_eq_self_iff]
  exact fun h => dropWhile_get_zero_not p l h

中文:
定理 dropWhile_idempotent
  结论: dropWhile p (dropWhile p l) = dropWhile p l
  证明: by
  simp only [dropWhile_eq_self_iff]
  exact fun h => dropWhile_get_zero_not p l h

Depends on / 依赖: dropWhile_eq_self_iff, dropWhile_get_zero_not
-/
theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l := by
  simp only [dropWhile_eq_self_iff]
  exact fun h => dropWhile_get_zero_not p l h

/--
theorem `rdropWhile_idempotent` / 定理 `rdropWhile_idempotent`

English:
theorem rdropWhile_idempotent
  statement: rdropWhile p (rdropWhile p l) = rdropWhile p l
  proof: rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)

中文:
定理 rdropWhile_idempotent
  结论: rdropWhile p (rdropWhile p l) = rdropWhile p l
  证明: rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)

Depends on / 依赖: rdropWhile_eq_self_iff, rdropWhile_eq_self_iff.mpr, rdropWhile_last_not
-/
theorem rdropWhile_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l :=
  rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)

/--
theorem `rdropWhile_reverse` / 定理 `rdropWhile_reverse`

English:
theorem rdropWhile_reverse
  statement: l.reverse.rdropWhile p = (l.dropWhile p).reverse
  proof: by
  simp_rw [rdropWhile, reverse_reverse]

中文:
定理 rdropWhile_reverse
  结论: l.reverse.rdropWhile p = (l.dropWhile p).reverse
  证明: by
  simp_rw [rdropWhile, reverse_reverse]

Depends on / 依赖: rdropWhile, reverse_reverse, simp_rw
-/
theorem rdropWhile_reverse : l.reverse.rdropWhile p = (l.dropWhile p).reverse := by
  simp_rw [rdropWhile, reverse_reverse]

/--
Definition of `rtakeWhile` / `rtakeWhile` 的定义

English:
definition rtakeWhile
  signature: : List α
  body: reverse (l.reverse.takeWhile p)

@[simp]

中文:
定义 rtakeWhile
  签名: : 列表 α
  定义体: reverse (l.reverse.takeWhile p)

@[simp]

Depends on / 依赖: l.reverse.takeWhile, reverse, takeWhile
-/
def rtakeWhile : List α :=
  reverse (l.reverse.takeWhile p)

@[simp]
/--
theorem `rtakeWhile_nil` / 定理 `rtakeWhile_nil`

English:
theorem rtakeWhile_nil
  statement: rtakeWhile p ([] : List α) = []
  proof: by simp [rtakeWhile]

中文:
定理 rtakeWhile_nil
  结论: rtakeWhile p ([] : 列表 α) = []
  证明: by simp [rtakeWhile]

Depends on / 依赖: rtakeWhile
-/
theorem rtakeWhile_nil : rtakeWhile p ([] : List α) = [] := by simp [rtakeWhile]

/--
theorem `rtakeWhile_concat` / 定理 `rtakeWhile_concat`

English:
theorem rtakeWhile_concat
  given: (x : α)
  proof: by
  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]

中文:
定理 rtakeWhile_concat
  条件: (x : α)
  证明: by
  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]

Depends on / 依赖: reverse_append, reverse_singleton, rtakeWhile, singleton_append, split_ifs, takeWhile
-/
theorem rtakeWhile_concat (x : α) :
    rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else [] := by
  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]

@[simp]
/--
theorem `rtakeWhile_concat_pos` / 定理 `rtakeWhile_concat_pos`

English:
theorem rtakeWhile_concat_pos
  given: (x : α) (h : p x)
  proof: by rw [rtakeWhile_concat, if_pos h]

@[simp]

中文:
定理 rtakeWhile_concat_pos
  条件: (x : α) (h : p x)
  证明: by rw [rtakeWhile_concat, if_pos h]

@[simp]

Depends on / 依赖: if_pos, rtakeWhile_concat
-/
theorem rtakeWhile_concat_pos (x : α) (h : p x) :
    rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x] := by rw [rtakeWhile_concat, if_pos h]

@[simp]
/--
theorem `rtakeWhile_concat_neg` / 定理 `rtakeWhile_concat_neg`

English:
theorem rtakeWhile_concat_neg
  given: (x : α) (h : ¬p x)
  statement: rtakeWhile p (l ++ [x]) = []
  proof: by
  rw [rtakeWhile_concat]; rw [if_neg h]

中文:
定理 rtakeWhile_concat_neg
  条件: (x : α) (h : ¬p x)
  结论: rtakeWhile p (l ++ [x]) = []
  证明: by
  rw [rtakeWhile_concat]; rw [if_neg h]

Depends on / 依赖: if_neg, rtakeWhile_concat
-/
theorem rtakeWhile_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = [] := by
  rw [rtakeWhile_concat]; rw [if_neg h]

/--
theorem `rtakeWhile_suffix` / 定理 `rtakeWhile_suffix`

English:
theorem rtakeWhile_suffix
  statement: l.rtakeWhile p <:+ l
  proof: by
  rw [← reverse_prefix]; rw [rtakeWhile]; rw [reverse_reverse]
  exact takeWhile_prefix _

中文:
定理 rtakeWhile_suffix
  结论: l.rtakeWhile p <:+ l
  证明: by
  rw [← reverse_prefix]; rw [rtakeWhile]; rw [reverse_reverse]
  exact takeWhile_prefix _

Depends on / 依赖: reverse_prefix, reverse_reverse, rtakeWhile, takeWhile_prefix
-/
theorem rtakeWhile_suffix : l.rtakeWhile p <:+ l := by
  rw [← reverse_prefix]; rw [rtakeWhile]; rw [reverse_reverse]
  exact takeWhile_prefix _

variable {p} {l}

@[simp]
/--
theorem `rtakeWhile_eq_self_iff` / 定理 `rtakeWhile_eq_self_iff`

English:
theorem rtakeWhile_eq_self_iff
  statement: rtakeWhile p l = l ↔ forall x in l, p x
  proof: by
  simp [rtakeWhile, reverse_eq_iff]

@[simp]

中文:
定理 rtakeWhile_eq_self_iff
  结论: rtakeWhile p l = l ↔ 对任意 x in l, p x
  证明: by
  simp [rtakeWhile, reverse_eq_iff]

@[simp]

Depends on / 依赖: reverse_eq_iff, rtakeWhile
-/
theorem rtakeWhile_eq_self_iff : rtakeWhile p l = l ↔ forall x in l, p x := by
  simp [rtakeWhile, reverse_eq_iff]

@[simp]
/--
theorem `rtakeWhile_eq_nil_iff` / 定理 `rtakeWhile_eq_nil_iff`

English:
theorem rtakeWhile_eq_nil_iff
  statement: rtakeWhile p l = [] ↔ forall hl : l != [], ¬p (l.getLast hl)
  proof: by
  induction l using List.reverseRecOn <;> simp [rtakeWhile]

中文:
定理 rtakeWhile_eq_nil_iff
  结论: rtakeWhile p l = [] ↔ 对任意 hl : l != [], ¬p (l.getLast hl)
  证明: by
  induction l using List.reverseRecOn <;> simp [rtakeWhile]

Depends on / 依赖: List.reverseRecOn, reverseRecOn, rtakeWhile
-/
theorem rtakeWhile_eq_nil_iff : rtakeWhile p l = [] ↔ forall hl : l != [], ¬p (l.getLast hl) := by
  induction l using List.reverseRecOn <;> simp [rtakeWhile]

/--
theorem `mem_rtakeWhile_imp` / 定理 `mem_rtakeWhile_imp`

English:
theorem mem_rtakeWhile_imp
  given: {x : α} (hx : x in rtakeWhile p l)
  statement: p x
  proof: by
  rw [rtakeWhile]; rw [mem_reverse] at hx
  exact mem_takeWhile_imp hx

中文:
定理 mem_rtakeWhile_imp
  条件: {x : α} (hx : x in rtakeWhile p l)
  结论: p x
  证明: by
  rw [rtakeWhile]; rw [mem_reverse] at hx
  exact mem_takeWhile_imp hx

Depends on / 依赖: mem_reverse, mem_takeWhile_imp, rtakeWhile
-/
theorem mem_rtakeWhile_imp {x : α} (hx : x in rtakeWhile p l) : p x := by
  rw [rtakeWhile]; rw [mem_reverse] at hx
  exact mem_takeWhile_imp hx

/--
theorem `rtakeWhile_idempotent` / 定理 `rtakeWhile_idempotent`

English:
theorem rtakeWhile_idempotent
  given: (p : α -> Bool) (l : List α)
  proof: rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp

中文:
定理 rtakeWhile_idempotent
  条件: (p : α -> 布尔值) (l : 列表 α)
  证明: rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp

Depends on / 依赖: mem_rtakeWhile_imp, rtakeWhile_eq_self_iff, rtakeWhile_eq_self_iff.mpr
-/
theorem rtakeWhile_idempotent (p : α -> Bool) (l : List α) :
    rtakeWhile p (rtakeWhile p l) = rtakeWhile p l :=
  rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp

/--
theorem `rtakeWhile_reverse` / 定理 `rtakeWhile_reverse`

English:
theorem rtakeWhile_reverse
  statement: l.reverse.rtakeWhile p = (l.takeWhile p).reverse
  proof: by
  simp_rw [rtakeWhile, reverse_reverse]

@[simp]

中文:
定理 rtakeWhile_reverse
  结论: l.reverse.rtakeWhile p = (l.takeWhile p).reverse
  证明: by
  simp_rw [rtakeWhile, reverse_reverse]

@[simp]

Depends on / 依赖: reverse_reverse, rtakeWhile, simp_rw
-/
theorem rtakeWhile_reverse : l.reverse.rtakeWhile p = (l.takeWhile p).reverse := by
  simp_rw [rtakeWhile, reverse_reverse]

@[simp]
/--
theorem `rdropWhile_append_rtakeWhile` / 定理 `rdropWhile_append_rtakeWhile`

English:
theorem rdropWhile_append_rtakeWhile
  proof: by
  simp only [rdropWhile, rtakeWhile]
  rw [← List.reverse_append]; rw [takeWhile_append_dropWhile]; rw [reverse_reverse]

中文:
定理 rdropWhile_append_rtakeWhile
  证明: by
  simp only [rdropWhile, rtakeWhile]
  rw [← List.reverse_append]; rw [takeWhile_append_dropWhile]; rw [reverse_reverse]

Depends on / 依赖: List.reverse_append, rdropWhile, reverse_append, reverse_reverse, rtakeWhile, takeWhile_append_dropWhile
-/
theorem rdropWhile_append_rtakeWhile :
    l.rdropWhile p ++ l.rtakeWhile p = l := by
  simp only [rdropWhile, rtakeWhile]
  rw [← List.reverse_append]; rw [takeWhile_append_dropWhile]; rw [reverse_reverse]

/--
lemma `rdrop_add` / 引理 `rdrop_add`

English:
lemma rdrop_add
  given: (i j : Nat)
  statement: (l.rdrop i).rdrop j = l.rdrop (i + j)
  proof: by
  simp_rw [rdrop_eq_reverse_drop_reverse, reverse_reverse, drop_drop]

@[simp]

中文:
引理 rdrop_add
  条件: (i j : 自然数)
  结论: (l.rdrop i).rdrop j = l.rdrop (i + j)
  证明: by
  simp_rw [rdrop_eq_reverse_drop_reverse, reverse_reverse, drop_drop]

@[simp]

Depends on / 依赖: drop_drop, rdrop_eq_reverse_drop_reverse, reverse_reverse, simp_rw
-/
lemma rdrop_add (i j : Nat) : (l.rdrop i).rdrop j = l.rdrop (i + j) := by
  simp_rw [rdrop_eq_reverse_drop_reverse, reverse_reverse, drop_drop]

@[simp]
/--
lemma `rdrop_append_length` / 引理 `rdrop_append_length`

English:
lemma rdrop_append_length
  given: {l₁ l₂ : List α}
  proof: by
  rw [rdrop_eq_reverse_drop_reverse]; rw [← length_reverse]; rw [reverse_append]; rw [drop_left]; rw [reverse_reverse]

中文:
引理 rdrop_append_length
  条件: {l₁ l₂ : 列表 α}
  证明: by
  rw [rdrop_eq_reverse_drop_reverse]; rw [← length_reverse]; rw [reverse_append]; rw [drop_left]; rw [reverse_reverse]

Depends on / 依赖: drop_left, length_reverse, rdrop_eq_reverse_drop_reverse, reverse_append, reverse_reverse
-/
lemma rdrop_append_length {l₁ l₂ : List α} :
    List.rdrop (l₁ ++ l₂) (List.length l₂) = l₁ := by
  rw [rdrop_eq_reverse_drop_reverse]; rw [← length_reverse]; rw [reverse_append]; rw [drop_left]; rw [reverse_reverse]

/--
lemma `rdrop_append_of_le_length` / 引理 `rdrop_append_of_le_length`

English:
lemma rdrop_append_of_le_length
  given: {l₁ l₂ : List α} (k : Nat)
  proof: by
  intro hk
  rw [← length_reverse] at hk
  rw [rdrop_eq_reverse_drop_reverse]; rw [reverse_append]; rw [drop_append_of_le_length hk]; rw [reverse_append]; rw [reverse_reverse]; rw [← rdrop_eq_reverse_drop_reverse]

@[simp]

中文:
引理 rdrop_append_of_le_length
  条件: {l₁ l₂ : 列表 α} (k : 自然数)
  证明: by
  intro hk
  rw [← length_reverse] at hk
  rw [rdrop_eq_reverse_drop_reverse]; rw [reverse_append]; rw [drop_append_of_le_length hk]; rw [reverse_append]; rw [reverse_reverse]; rw [← rdrop_eq_reverse_drop_reverse]

@[simp]

Depends on / 依赖: drop_append_of_le_length, length_reverse, rdrop_eq_reverse_drop_reverse, reverse_append, reverse_reverse
-/
lemma rdrop_append_of_le_length {l₁ l₂ : List α} (k : Nat) :
    k <= length l₂ -> List.rdrop (l₁ ++ l₂) k = l₁ ++ List.rdrop l₂ k := by
  intro hk
  rw [← length_reverse] at hk
  rw [rdrop_eq_reverse_drop_reverse]; rw [reverse_append]; rw [drop_append_of_le_length hk]; rw [reverse_append]; rw [reverse_reverse]; rw [← rdrop_eq_reverse_drop_reverse]

@[simp]
/--
lemma `rdrop_append_length_add` / 引理 `rdrop_append_length_add`

English:
lemma rdrop_append_length_add
  given: {l₁ l₂ : List α} (k : Nat)
  proof: by
  rw [← rdrop_add]; rw [rdrop_append_length]

中文:
引理 rdrop_append_length_add
  条件: {l₁ l₂ : 列表 α} (k : 自然数)
  证明: by
  rw [← rdrop_add]; rw [rdrop_append_length]

Depends on / 依赖: rdrop_add, rdrop_append_length
-/
lemma rdrop_append_length_add {l₁ l₂ : List α} (k : Nat) :
    List.rdrop (l₁ ++ l₂) (length l₂ + k) = List.rdrop l₁ k := by
  rw [← rdrop_add]; rw [rdrop_append_length]

end List
