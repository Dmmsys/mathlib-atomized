/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Chain

/-!
# List of Booleans

In this file we prove lemmas about the number of `false`s and `true`s in a list of Booleans. First
we prove that the number of `false`s plus the number of `true` equals the length of the list. Then
we prove that in a list with alternating `true`s and `false`s, the number of `true`s differs from
the number of `false`s by at most one. We provide several versions of these statements.
-/

public section


namespace List

@[simp]
/--
theorem `count_not_add_count` / 定理 `count_not_add_count`

English:
theorem count_not_add_count
  given: (l : List Bool) (b : Bool)
  statement: count (!b) l + count b l = length l
  proof: by
  have := length_eq_countP_add_countP (l := l) (· == !b)
  aesop (add simp this)

grind_pattern count_not_add_count => count (!b) l

@[simp]

中文:
定理 count_not_add_count
  条件: (l : List 布尔) (b : 布尔)
  结论: count (!b) l + count b l = length l
  证明: by
  have := length_eq_countP_add_countP (l := l) (· == !b)
  aesop (add simp this)

grind_pattern count_not_add_count => count (!b) l

@[simp]

Depends on / 依赖: length_eq_countP_add_countP
-/
theorem count_not_add_count (l : List Bool) (b : Bool) : count (!b) l + count b l = length l := by
  have := length_eq_countP_add_countP (l := l) (· == !b)
  aesop (add simp this)

grind_pattern count_not_add_count => count (!b) l

@[simp]
/--
theorem `count_add_count_not` / 定理 `count_add_count_not`

English:
theorem count_add_count_not
  given: (l : List Bool) (b : Bool)
  statement: count b l + count (!b) l = length l
  proof: by
  grind

@[simp]

中文:
定理 count_add_count_not
  条件: (l : List 布尔) (b : 布尔)
  结论: count b l + count (!b) l = length l
  证明: by
  grind

@[simp]
-/
theorem count_add_count_not (l : List Bool) (b : Bool) : count b l + count (!b) l = length l := by
  grind

@[simp]
/--
theorem `count_false_add_count_true` / 定理 `count_false_add_count_true`

English:
theorem count_false_add_count_true
  given: (l : List Bool)
  statement: count false l + count true l = length l
  proof: count_not_add_count l true

grind_pattern count_false_add_count_true => count false l
grind_pattern count_false_add_count_true => count true l

@[simp]

中文:
定理 count_false_add_count_true
  条件: (l : List 布尔)
  结论: count false l + count true l = length l
  证明: count_not_add_count l true

grind_pattern count_false_add_count_true => count false l
grind_pattern count_false_add_count_true => count true l

@[simp]

Depends on / 依赖: count_not_add_count
-/
theorem count_false_add_count_true (l : List Bool) : count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true => count false l
grind_pattern count_false_add_count_true => count true l

@[simp]
/--
theorem `count_true_add_count_false` / 定理 `count_true_add_count_false`

English:
theorem count_true_add_count_false
  given: (l : List Bool)
  statement: count true l + count false l = length l
  proof: count_not_add_count l false

中文:
定理 count_true_add_count_false
  条件: (l : List 布尔)
  结论: count true l + count false l = length l
  证明: count_not_add_count l false

Depends on / 依赖: count_not_add_count
-/
theorem count_true_add_count_false (l : List Bool) : count true l + count false l = length l :=
  count_not_add_count l false

/--
theorem `IsChain.count_not_cons` / 定理 `IsChain.count_not_cons`

English:
theorem IsChain.count_not_cons

中文:
定理 IsChain.count_not_cons
-/
theorem IsChain.count_not_cons :
    forall {b : Bool} {l : List Bool}, IsChain (· != ·) (b :: l) ->
    count (!b) l = count b l + length l % 2
  | _, [], _h => rfl
  | b, x :: l, h => by
    grind [h.of_cons.count_not_cons]

namespace IsChain

variable {l : List Bool}

/--
theorem `count_not_eq_count` / 定理 `count_not_eq_count`

English:
theorem count_not_eq_count
  given: (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : Bool)
  proof: by
  rcases l with - | ⟨x, l⟩
  · rfl
  grind [count_cons_of_ne x.not_ne_self.symm, hl.count_not_cons]

中文:
定理 count_not_eq_count
  条件: (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : 布尔)
  证明: by
  rcases l with - | ⟨x, l⟩
  · rfl
  grind [count_cons_of_ne x.not_ne_self.symm, hl.count_not_cons]

Depends on / 依赖: count_cons_of_ne, count_not_cons, hl.count_not_cons, not_ne_self, x.not_ne_self.symm
-/
theorem count_not_eq_count (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : Bool) :
    count (!b) l = count b l := by
  rcases l with - | ⟨x, l⟩
  · rfl
  grind [count_cons_of_ne x.not_ne_self.symm, hl.count_not_cons]

/--
theorem `count_false_eq_count_true` / 定理 `count_false_eq_count_true`

English:
theorem count_false_eq_count_true
  given: (hl : IsChain (· != ·) l) (h2 : Even (length l))
  proof: hl.count_not_eq_count h2 true

中文:
定理 count_false_eq_count_true
  条件: (hl : IsChain (· != ·) l) (h2 : Even (length l))
  证明: hl.count_not_eq_count h2 true

Depends on / 依赖: count_not_eq_count, hl.count_not_eq_count
-/
theorem count_false_eq_count_true (hl : IsChain (· != ·) l) (h2 : Even (length l)) :
    count false l = count true l :=
  hl.count_not_eq_count h2 true

/--
theorem `count_not_le_count_add_one` / 定理 `count_not_le_count_add_one`

English:
theorem count_not_le_count_add_one
  given: (hl : IsChain (· != ·) l) (b : Bool)
  proof: by
  cases l
  · exact zero_le
  grind [hl.count_not_cons]

中文:
定理 count_not_le_count_add_one
  条件: (hl : IsChain (· != ·) l) (b : 布尔)
  证明: by
  cases l
  · exact zero_le
  grind [hl.count_not_cons]

Depends on / 依赖: count_not_cons, hl.count_not_cons, zero_le
-/
theorem count_not_le_count_add_one (hl : IsChain (· != ·) l) (b : Bool) :
    count (!b) l <= count b l + 1 := by
  cases l
  · exact zero_le
  grind [hl.count_not_cons]

/--
theorem `count_false_le_count_true_add_one` / 定理 `count_false_le_count_true_add_one`

English:
theorem count_false_le_count_true_add_one
  given: (hl : IsChain (· != ·) l)
  proof: hl.count_not_le_count_add_one true

中文:
定理 count_false_le_count_true_add_one
  条件: (hl : IsChain (· != ·) l)
  证明: hl.count_not_le_count_add_one true

Depends on / 依赖: count_not_le_count_add_one, hl.count_not_le_count_add_one
-/
theorem count_false_le_count_true_add_one (hl : IsChain (· != ·) l) :
    count false l <= count true l + 1 :=
  hl.count_not_le_count_add_one true

/--
theorem `count_true_le_count_false_add_one` / 定理 `count_true_le_count_false_add_one`

English:
theorem count_true_le_count_false_add_one
  given: (hl : IsChain (· != ·) l)
  proof: hl.count_not_le_count_add_one false

中文:
定理 count_true_le_count_false_add_one
  条件: (hl : IsChain (· != ·) l)
  证明: hl.count_not_le_count_add_one false

Depends on / 依赖: count_not_le_count_add_one, hl.count_not_le_count_add_one
-/
theorem count_true_le_count_false_add_one (hl : IsChain (· != ·) l) :
    count true l <= count false l + 1 :=
  hl.count_not_le_count_add_one false

/--
theorem `two_mul_count_bool_of_even` / 定理 `two_mul_count_bool_of_even`

English:
theorem two_mul_count_bool_of_even
  given: (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : Bool)
  proof: by
  rw [← count_not_add_count l b]; rw [hl.count_not_eq_count h2]; rw [two_mul]

中文:
定理 two_mul_count_bool_of_even
  条件: (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : 布尔)
  证明: by
  rw [← count_not_add_count l b]; rw [hl.count_not_eq_count h2]; rw [two_mul]

Depends on / 依赖: count_not_add_count, count_not_eq_count, hl.count_not_eq_count, two_mul
-/
theorem two_mul_count_bool_of_even (hl : IsChain (· != ·) l) (h2 : Even (length l)) (b : Bool) :
    2 * count b l = length l := by
  rw [← count_not_add_count l b]; rw [hl.count_not_eq_count h2]; rw [two_mul]

/--
theorem `two_mul_count_bool_eq_ite` / 定理 `two_mul_count_bool_eq_ite`

English:
theorem two_mul_count_bool_eq_ite
  given: (hl : IsChain (· != ·) l) (b : Bool)
  proof: by
  by_cases h2 : Even (length l)
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
  · rcases l with - | ⟨x, l⟩
    · exact (h2 .zero).elim
    grind [hl.tail.two_mul_count_bool_of_even]

中文:
定理 two_mul_count_bool_eq_ite
  条件: (hl : IsChain (· != ·) l) (b : 布尔)
  证明: by
  by_cases h2 : Even (length l)
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
  · rcases l with - | ⟨x, l⟩
    · exact (h2 .zero).elim
    grind [hl.tail.two_mul_count_bool_of_even]

Depends on / 依赖: hl.tail.two_mul_count_bool_of_even, hl.two_mul_count_bool_of_even, if_pos, length, two_mul_count_bool_of_even
-/
theorem two_mul_count_bool_eq_ite (hl : IsChain (· != ·) l) (b : Bool) :
    2 * count b l =
      if Even (length l) then length l else
      if Option.some b == l.head? then length l + 1 else length l - 1 := by
  by_cases h2 : Even (length l)
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
  · rcases l with - | ⟨x, l⟩
    · exact (h2 .zero).elim
    grind [hl.tail.two_mul_count_bool_of_even]

/--
theorem `length_sub_one_le_two_mul_count_bool` / 定理 `length_sub_one_le_two_mul_count_bool`

English:
theorem length_sub_one_le_two_mul_count_bool
  given: (hl : IsChain (· != ·) l) (b : Bool)
  proof: by
  grind [hl.two_mul_count_bool_eq_ite]

中文:
定理 length_sub_one_le_two_mul_count_bool
  条件: (hl : IsChain (· != ·) l) (b : 布尔)
  证明: by
  grind [hl.two_mul_count_bool_eq_ite]

Depends on / 依赖: hl.two_mul_count_bool_eq_ite, two_mul_count_bool_eq_ite
-/
theorem length_sub_one_le_two_mul_count_bool (hl : IsChain (· != ·) l) (b : Bool) :
    length l - 1 <= 2 * count b l := by
  grind [hl.two_mul_count_bool_eq_ite]

/--
theorem `length_div_two_le_count_bool` / 定理 `length_div_two_le_count_bool`

English:
theorem length_div_two_le_count_bool
  given: (hl : IsChain (· != ·) l) (b : Bool)
  proof: by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos]; rw [← tsub_le_iff_right]
  exact length_sub_one_le_two_mul_count_bool hl b

中文:
定理 length_div_two_le_count_bool
  条件: (hl : IsChain (· != ·) l) (b : 布尔)
  证明: by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos]; rw [← tsub_le_iff_right]
  exact length_sub_one_le_two_mul_count_bool hl b

Depends on / 依赖: Nat.div_le_iff_le_mul_add_pred, div_le_iff_le_mul_add_pred, length_sub_one_le_two_mul_count_bool, tsub_le_iff_right, two_pos
-/
theorem length_div_two_le_count_bool (hl : IsChain (· != ·) l) (b : Bool) :
    length l / 2 <= count b l := by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos]; rw [← tsub_le_iff_right]
  exact length_sub_one_le_two_mul_count_bool hl b

/--
theorem `two_mul_count_bool_le_length_add_one` / 定理 `two_mul_count_bool_le_length_add_one`

English:
theorem two_mul_count_bool_le_length_add_one
  given: (hl : IsChain (· != ·) l) (b : Bool)
  proof: by
  grind [hl.two_mul_count_bool_eq_ite]

中文:
定理 two_mul_count_bool_le_length_add_one
  条件: (hl : IsChain (· != ·) l) (b : 布尔)
  证明: by
  grind [hl.two_mul_count_bool_eq_ite]

Depends on / 依赖: hl.two_mul_count_bool_eq_ite, two_mul_count_bool_eq_ite
-/
theorem two_mul_count_bool_le_length_add_one (hl : IsChain (· != ·) l) (b : Bool) :
    2 * count b l <= length l + 1 := by
  grind [hl.two_mul_count_bool_eq_ite]

end IsChain

end List
