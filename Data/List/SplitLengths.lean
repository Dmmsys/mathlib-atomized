/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.MinMax

/-!
# Splitting a list to chunks of specified lengths

This file defines splitting a list to chunks of given lengths, and some proofs about that.
-/

@[expose] public section

variable {α : Type*} (l : List α) (sz : List Nat)

namespace List

/--
Definition of `splitLengths` / `splitLengths` 的定义

English:
definition splitLengths
  signature: : List Nat -> List α -> List (List α)
  body: x.splitAt n
    x0 :: ns.splitLengths x1

@[simp]

中文:
定义 splitLengths
  签名: : 列表 自然数 -> 列表 α -> 列表 (列表 α)
  定义体: x.splitAt n
    x0 :: ns.splitLengths x1

@[simp]

Depends on / 依赖: splitAt, x.splitAt
-/
def splitLengths : List Nat -> List α -> List (List α)
  | [], _ => []
  | n::ns, x =>
    let (x0, x1) := x.splitAt n
    x0 :: ns.splitLengths x1

@[simp]
/--
theorem `length_splitLengths` / 定理 `length_splitLengths`

English:
theorem length_splitLengths
  statement: (sz.splitLengths l).length = sz.length
  proof: by
  induction sz generalizing l <;> simp [splitLengths, *]

@[simp]

中文:
定理 length_splitLengths
  结论: (sz.splitLengths l).length = sz.length
  证明: by
  induction sz generalizing l <;> simp [splitLengths, *]

@[simp]

Depends on / 依赖: generalizing, splitLengths
-/
theorem length_splitLengths : (sz.splitLengths l).length = sz.length := by
  induction sz generalizing l <;> simp [splitLengths, *]

@[simp]
/--
lemma `splitLengths_nil` / 引理 `splitLengths_nil`

English:
lemma splitLengths_nil
  statement: [].splitLengths l = []
  proof: rfl

@[simp]

中文:
引理 splitLengths_nil
  结论: [].splitLengths l = []
  证明: rfl

@[simp]
-/
lemma splitLengths_nil : [].splitLengths l = [] := rfl

@[simp]
/--
lemma `splitLengths_cons` / 引理 `splitLengths_cons`

English:
lemma splitLengths_cons
  given: (n : Nat)
  proof: by
  simp [splitLengths]

中文:
引理 splitLengths_cons
  条件: (n : 自然数)
  证明: by
  simp [splitLengths]

Depends on / 依赖: splitLengths
-/
lemma splitLengths_cons (n : Nat) :
    (n :: sz).splitLengths l = l.take n :: sz.splitLengths (l.drop n) := by
  simp [splitLengths]

/--
theorem `take_splitLength` / 定理 `take_splitLength`

English:
theorem take_splitLength
  given: (i : Nat)
  statement: (sz.splitLengths l).take i = (sz.take i).splitLengths l
  proof: by
  induction i generalizing sz l
  case zero => simp
  case succ i hi =>
    cases sz
    · simp
    · simp only [splitLengths_cons, take_succ_cons, hi]

中文:
定理 take_splitLength
  条件: (i : 自然数)
  结论: (sz.splitLengths l).take i = (sz.take i).splitLengths l
  证明: by
  induction i generalizing sz l
  case zero => simp
  case succ i hi =>
    cases sz
    · simp
    · simp only [splitLengths_cons, take_succ_cons, hi]

Depends on / 依赖: generalizing, splitLengths_cons, take_succ_cons
-/
theorem take_splitLength (i : Nat) : (sz.splitLengths l).take i = (sz.take i).splitLengths l := by
  induction i generalizing sz l
  case zero => simp
  case succ i hi =>
    cases sz
    · simp
    · simp only [splitLengths_cons, take_succ_cons, hi]

/--
theorem `length_splitLengths_getElem_le` / 定理 `length_splitLengths_getElem_le`

English:
theorem length_splitLengths_getElem_le
  given: {i : Nat} {hi : i < (sz.splitLengths l).length}
  proof: by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths_cons]
    cases i
    · simp
    · simp only [getElem_cons_succ, tail_ih]

中文:
定理 length_splitLengths_getElem_le
  条件: {i : 自然数} {hi : i < (sz.splitLengths l).length}
  证明: by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths_cons]
    cases i
    · simp
    · simp only [getElem_cons_succ, tail_ih]

Depends on / 依赖: generalizing, getElem_cons_succ, splitLengths_cons, tail_ih
-/
theorem length_splitLengths_getElem_le {i : Nat} {hi : i < (sz.splitLengths l).length} :
    (sz.splitLengths l)[i].length <= sz[i]'(by simpa using hi) := by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths_cons]
    cases i
    · simp
    · simp only [getElem_cons_succ, tail_ih]

/--
theorem `flatten_splitLengths` / 定理 `flatten_splitLengths`

English:
theorem flatten_splitLengths
  given: (h : l.length <= sz.sum)
  statement: (sz.splitLengths l).flatten = l
  proof: by
  induction sz generalizing l
  · simp_all
  case cons head tail ih =>
    simp only [splitLengths_cons, flatten_cons]
    rw [ih]; rw [take_append_drop]
    simpa [add_comm] using h

中文:
定理 flatten_splitLengths
  条件: (h : l.length <= sz.求和)
  结论: (sz.splitLengths l).flatten = l
  证明: by
  induction sz generalizing l
  · simp_all
  case cons head tail ih =>
    simp only [splitLengths_cons, flatten_cons]
    rw [ih]; rw [take_append_drop]
    simpa [add_comm] using h

Depends on / 依赖: add_comm, flatten_cons, generalizing, splitLengths_cons, take_append_drop
-/
theorem flatten_splitLengths (h : l.length <= sz.sum) : (sz.splitLengths l).flatten = l := by
  induction sz generalizing l
  · simp_all
  case cons head tail ih =>
    simp only [splitLengths_cons, flatten_cons]
    rw [ih]; rw [take_append_drop]
    simpa [add_comm] using h

/--
theorem `map_splitLengths_length` / 定理 `map_splitLengths_length`

English:
theorem map_splitLengths_length
  given: (h : sz.sum <= l.length)
  proof: by
  induction sz generalizing l
  · simp
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths_cons, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]

中文:
定理 map_splitLengths_length
  条件: (h : sz.求和 <= l.length)
  证明: by
  induction sz generalizing l
  · simp
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths_cons, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]

Depends on / 依赖: Nat.le_of_add_right_le, Nat.le_sub_of_add_le, cons.injEq, generalizing, le_of_add_right_le, le_sub_of_add_le, length_take, map_cons, min_eq_left_iff, splitLengths_cons, sum_cons
-/
theorem map_splitLengths_length (h : sz.sum <= l.length) :
    (sz.splitLengths l).map length = sz := by
  induction sz generalizing l
  · simp
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths_cons, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]

/--
theorem `length_splitLengths_getElem_eq` / 定理 `length_splitLengths_getElem_eq`

English:
theorem length_splitLengths_getElem_eq
  statement: {i : Nat} (hi : i < sz.length)
  proof: by
  rw [List.getElem_take' (hj := i.lt_add_one)]
  simp only [take_splitLength]
  conv_rhs =>
    rw [List.getElem_take' (hj := i.lt_add_one)]
    simp +singlePass only [← map_splitLengths_length l _ h]
    rw [getElem_map]

中文:
定理 length_splitLengths_getElem_eq
  结论: {i : 自然数} (hi : i < sz.length)
  证明: by
  rw [List.getElem_take' (hj := i.lt_add_one)]
  simp only [take_splitLength]
  conv_rhs =>
    rw [List.getElem_take' (hj := i.lt_add_one)]
    simp +singlePass only [← map_splitLengths_length l _ h]
    rw [getElem_map]

Depends on / 依赖: List.getElem_take, conv_rhs, getElem_map, getElem_take, i.lt_add_one, lt_add_one, map_splitLengths_length, singlePass, take_splitLength
-/
theorem length_splitLengths_getElem_eq {i : Nat} (hi : i < sz.length)
    (h : (sz.take (i + 1)).sum <= l.length) :
    ((sz.splitLengths l)[i]'(by simpa)).length = sz[i] := by
  rw [List.getElem_take' (hj := i.lt_add_one)]
  simp only [take_splitLength]
  conv_rhs =>
    rw [List.getElem_take' (hj := i.lt_add_one)]
    simp +singlePass only [← map_splitLengths_length l _ h]
    rw [getElem_map]

/--
theorem `splitLengths_length_getElem` / 定理 `splitLengths_length_getElem`

English:
theorem splitLengths_length_getElem
  statement: {α : Type*} (l : List α) (sz : List Nat)
  proof: by
  have := map_splitLengths_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

中文:
定理 splitLengths_length_getElem
  结论: {α : 类型} (l : 列表 α) (sz : 列表 自然数)
  证明: by
  have := map_splitLengths_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

Depends on / 依赖: List.getElem_map, List.length, getElem_map, length, map_splitLengths_length
-/
theorem splitLengths_length_getElem {α : Type*} (l : List α) (sz : List Nat)
    (h : sz.sum <= l.length) (i : Nat) (hi : i < (sz.splitLengths l).length) :
    (sz.splitLengths l)[i].length = sz[i]'(by simpa using hi) := by
  have := map_splitLengths_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

/--
theorem `length_mem_splitLengths` / 定理 `length_mem_splitLengths`

English:
theorem length_mem_splitLengths
  statement: {α : Type*} (l : List α) (sz : List Nat) (b : Nat)
  proof: by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  have := length_splitLengths_getElem_le l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  lia

中文:
定理 length_mem_splitLengths
  结论: {α : 类型} (l : 列表 α) (sz : 列表 自然数) (b : 自然数)
  证明: by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  have := length_splitLengths_getElem_le l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  lia

Depends on / 依赖: List.forall_mem_iff_forall_getElem, forall_mem_iff_forall_getElem, getElem_mem, length_splitLengths_getElem_le
-/
theorem length_mem_splitLengths {α : Type*} (l : List α) (sz : List Nat) (b : Nat)
    (h : forall n in sz, n <= b) : forall l₂ in sz.splitLengths l, l₂.length <= b := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  have := length_splitLengths_getElem_le l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  lia

end List
