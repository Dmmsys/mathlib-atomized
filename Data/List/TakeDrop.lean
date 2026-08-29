/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Logic.Function.Iterate

/-!
# `Take` and `Drop` lemmas for lists

This file provides lemmas about `List.take` and `List.drop` and related functions.
-/

public section

assert_not_exists GroupWithZero
assert_not_exists Lattice
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Ring
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}


/--
theorem `take_one_drop_eq_of_lt_length` / 定理 `take_one_drop_eq_of_lt_length`

English:
theorem take_one_drop_eq_of_lt_length
  given: {l : List α} {n : Nat} (h : n < l.length)
  proof: by
  rw [drop_eq_getElem_cons h]; rw [take]; rw [take]
  simp

中文:
定理 take_one_drop_eq_of_lt_length
  条件: {l : List α} {n : 自然数} (h : n < l.length)
  证明: by
  rw [drop_eq_getElem_cons h]; rw [take]; rw [take]
  simp

Depends on / 依赖: drop_eq_getElem_cons
-/
theorem take_one_drop_eq_of_lt_length {l : List α} {n : Nat} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h]; rw [take]; rw [take]
  simp

/--
lemma `take_eq_self_iff` / 引理 `take_eq_self_iff`

English:
lemma take_eq_self_iff
  given: (x : List α) {n : Nat}
  statement: x.take n = x ↔ x.length <= n
  proof: ⟨by grind, take_of_length_le⟩

中文:
引理 take_eq_self_iff
  条件: (x : List α) {n : 自然数}
  结论: x.take n = x ↔ x.length <= n
  证明: ⟨by grind, take_of_length_le⟩
-/
@[simp] lemma take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length <= n :=
  ⟨by grind, take_of_length_le⟩

/--
lemma `take_self_eq_iff` / 引理 `take_self_eq_iff`

English:
lemma take_self_eq_iff
  given: (x : List α) {n : Nat}
  statement: x = x.take n ↔ x.length <= n
  proof: by
  rw [Eq.comm]; rw [take_eq_self_iff]

中文:
引理 take_self_eq_iff
  条件: (x : List α) {n : 自然数}
  结论: x = x.take n ↔ x.length <= n
  证明: by
  rw [Eq.comm]; rw [take_eq_self_iff]
-/
@[simp] lemma take_self_eq_iff (x : List α) {n : Nat} : x = x.take n ↔ x.length <= n := by
  rw [Eq.comm]; rw [take_eq_self_iff]

/--
lemma `take_eq_left_iff` / 引理 `take_eq_left_iff`

English:
lemma take_eq_left_iff
  given: {x y : List α} {n : Nat}
  proof: by
  simp [take_append, Nat.sub_eq_zero_iff_le, Or.comm]

中文:
引理 take_eq_left_iff
  条件: {x y : List α} {n : 自然数}
  证明: by
  simp [take_append, Nat.sub_eq_zero_iff_le, Or.comm]
-/
@[simp] lemma take_eq_left_iff {x y : List α} {n : Nat} :
    (x ++ y).take n = x.take n ↔ y = [] ∨ n <= x.length := by
  simp [take_append, Nat.sub_eq_zero_iff_le, Or.comm]

/--
lemma `left_eq_take_iff` / 引理 `left_eq_take_iff`

English:
lemma left_eq_take_iff
  given: {x y : List α} {n : Nat}
  proof: by
  rw [Eq.comm]; apply take_eq_left_iff

中文:
引理 left_eq_take_iff
  条件: {x y : List α} {n : 自然数}
  证明: by
  rw [Eq.comm]; apply take_eq_left_iff
-/
@[simp] lemma left_eq_take_iff {x y : List α} {n : Nat} :
    x.take n = (x ++ y).take n ↔ y = [] ∨ n <= x.length := by
  rw [Eq.comm]; apply take_eq_left_iff

/--
lemma `drop_take_append_drop` / 引理 `drop_take_append_drop`

English:
lemma drop_take_append_drop
  given: (x : List α) (m n : Nat)
  proof: by rw [← drop_drop, take_append_drop]

中文:
引理 drop_take_append_drop
  条件: (x : List α) (m n : 自然数)
  证明: by rw [← drop_drop, take_append_drop]
-/
@[simp] lemma drop_take_append_drop (x : List α) (m n : Nat) :
    (x.drop m).take n ++ x.drop (m + n) = x.drop m := by rw [← drop_drop, take_append_drop]

/--
lemma `drop_take_append_drop'` / 引理 `drop_take_append_drop'`

English:
lemma drop_take_append_drop'
  given: (x : List α) (m n : Nat)
  proof: by rw [Nat.add_comm, drop_take_append_drop]

中文:
引理 drop_take_append_drop'
  条件: (x : List α) (m n : 自然数)
  证明: by rw [Nat.add_comm, drop_take_append_drop]
-/
@[simp] lemma drop_take_append_drop' (x : List α) (m n : Nat) :
    (x.drop m).take n ++ x.drop (n + m) = x.drop m := by rw [Nat.add_comm, drop_take_append_drop]

/--
lemma `take_concat_get'` / 引理 `take_concat_get'`

English:
lemma take_concat_get'
  given: (l : List α) (i : Nat) (h : i < l.length)
  proof: by simp

中文:
引理 take_concat_get'
  条件: (l : List α) (i : 自然数) (h : i < l.length)
  证明: by simp
-/
lemma take_concat_get' (l : List α) (i : Nat) (h : i < l.length) :
    l.take i ++ [l[i]] = l.take (i + 1) := by simp

/--
theorem `cons_getElem_drop_succ` / 定理 `cons_getElem_drop_succ`

English:
theorem cons_getElem_drop_succ
  given: {l : List α} {n : Nat} {h : n < l.length}
  proof: (drop_eq_getElem_cons h).symm

中文:
定理 cons_getElem_drop_succ
  条件: {l : List α} {n : 自然数} {h : n < l.length}
  证明: (drop_eq_getElem_cons h).symm

Depends on / 依赖: drop_eq_getElem_cons
-/
theorem cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} :
    l[n] :: l.drop (n + 1) = l.drop n :=
  (drop_eq_getElem_cons h).symm

/--
theorem `cons_get_drop_succ` / 定理 `cons_get_drop_succ`

English:
theorem cons_get_drop_succ
  given: {l : List α} {n}
  proof: (drop_eq_getElem_cons n.2).symm

中文:
定理 cons_get_drop_succ
  条件: {l : List α} {n}
  证明: (drop_eq_getElem_cons n.2).symm

Depends on / 依赖: drop_eq_getElem_cons
-/
theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 :=
  (drop_eq_getElem_cons n.2).symm

/--
lemma `drop_length_sub_one` / 引理 `drop_length_sub_one`

English:
lemma drop_length_sub_one
  given: {l : List α} (h : l != [])
  statement: l.drop (l.length - 1) = [l.getLast h]
  proof: by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    rw [length_cons]; rw [Nat.add_one_sub_one]; rw [List.drop_length_cons hl a]
    simp [getLast_cons, hl]

中文:
引理 drop_length_sub_one
  条件: {l : List α} (h : l != [])
  结论: l.drop (l.length - 1) = [l.getLast h]
  证明: by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    rw [length_cons]; rw [Nat.add_one_sub_one]; rw [List.drop_length_cons hl a]
    simp [getLast_cons, hl]

Depends on / 依赖: List.drop_length_cons, Nat.add_one_sub_one, add_one_sub_one, drop_length_cons, getLast_cons, length_cons
-/
lemma drop_length_sub_one {l : List α} (h : l != []) : l.drop (l.length - 1) = [l.getLast h] := by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    rw [length_cons]; rw [Nat.add_one_sub_one]; rw [List.drop_length_cons hl a]
    simp [getLast_cons, hl]

/--
theorem `tail_iterate` / 定理 `tail_iterate`

English:
theorem tail_iterate
  given: (l : List α) (n : Nat)
  statement: (List.tail^[n]) l = l.drop n
  proof: by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [*]

中文:
定理 tail_iterate
  条件: (l : List α) (n : 自然数)
  结论: (List.tail^[n]) l = l.drop n
  证明: by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem tail_iterate (l : List α) (n : Nat) : (List.tail^[n]) l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [*]

section TailDropLast

variable (l : List α) (n : Nat)

/--
theorem `tail_take_eq_take_tail` / 定理 `tail_take_eq_take_tail`

English:
theorem tail_take_eq_take_tail
  statement: (l.take n).tail = l.tail.take (n - 1)
  proof: by
  ext
  grind

中文:
定理 tail_take_eq_take_tail
  结论: (l.take n).tail = l.tail.take (n - 1)
  证明: by
  ext
  grind
-/
theorem tail_take_eq_take_tail : (l.take n).tail = l.tail.take (n - 1) := by
  ext
  grind

/--
theorem `dropLast_take_eq_take_dropLast` / 定理 `dropLast_take_eq_take_dropLast`

English:
theorem dropLast_take_eq_take_dropLast
  statement: (l.take n).dropLast = l.dropLast.take (n - 1)
  proof: by
  ext
  grind

中文:
定理 dropLast_take_eq_take_dropLast
  结论: (l.take n).dropLast = l.dropLast.take (n - 1)
  证明: by
  ext
  grind
-/
theorem dropLast_take_eq_take_dropLast : (l.take n).dropLast = l.dropLast.take (n - 1) := by
  ext
  grind

/--
theorem `tail_drop_eq_drop_tail` / 定理 `tail_drop_eq_drop_tail`

English:
theorem tail_drop_eq_drop_tail
  statement: (l.drop n).tail = l.tail.drop n
  proof: by
  ext
  grind

中文:
定理 tail_drop_eq_drop_tail
  结论: (l.drop n).tail = l.tail.drop n
  证明: by
  ext
  grind
-/
theorem tail_drop_eq_drop_tail : (l.drop n).tail = l.tail.drop n := by
  ext
  grind

/--
theorem `dropLast_drop_eq_drop_dropLast` / 定理 `dropLast_drop_eq_drop_dropLast`

English:
theorem dropLast_drop_eq_drop_dropLast
  statement: (l.drop n).dropLast = l.dropLast.drop n
  proof: by
  ext
  grind

中文:
定理 dropLast_drop_eq_drop_dropLast
  结论: (l.drop n).dropLast = l.dropLast.drop n
  证明: by
  ext
  grind
-/
theorem dropLast_drop_eq_drop_dropLast : (l.drop n).dropLast = l.dropLast.drop n := by
  ext
  grind

end TailDropLast

section TakeI

variable [Inhabited α]

@[simp]
/--
theorem `takeI_length` / 定理 `takeI_length`

English:
theorem takeI_length
  statement: forall n l, length (@takeI α _ n l) = n

中文:
定理 takeI_length
  结论: 对任意 n l, length (@takeI α _ n l) = n
-/
theorem takeI_length : forall n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)

@[simp]
/--
theorem `takeI_nil` / 定理 `takeI_nil`

English:
theorem takeI_nil
  statement: forall n, takeI n (@nil α) = replicate n default

中文:
定理 takeI_nil
  结论: 对任意 n, takeI n (@nil α) = replicate n default
-/
theorem takeI_nil : forall n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)

/--
theorem `takeI_eq_take` / 定理 `takeI_eq_take`

English:
theorem takeI_eq_take
  statement: forall {n} {l : List α}, n <= length l -> takeI n l = take n l

中文:
定理 takeI_eq_take
  结论: 对任意 {n} {l : List α}, n <= length l -> takeI n l = take n l
-/
theorem takeI_eq_take : forall {n} {l : List α}, n <= length l -> takeI n l = take n l
  | 0, _, _ => rfl
| _ + 1, _ :: _, h => congr_arg (cons _) takeI_eq_take le_of_succ_le_succ h

@[simp]
/--
theorem `takeI_left` / 定理 `takeI_left`

English:
theorem takeI_left
  given: (l₁ l₂ : List α)
  statement: takeI (length l₁) (l₁ ++ l₂) = l₁
  proof: (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans take_left

中文:
定理 takeI_left
  条件: (l₁ l₂ : List α)
  结论: takeI (length l₁) (l₁ ++ l₂) = l₁
  证明: (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans take_left

Depends on / 依赖: Nat.le_add_right, le_add_right, length_append, takeI_eq_take, take_left
-/
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans take_left

/--
theorem `takeI_left'` / 定理 `takeI_left'`

English:
theorem takeI_left'
  given: {l₁ l₂ : List α} {n} (h : length l₁ = n)
  statement: takeI n (l₁ ++ l₂) = l₁
  proof: by
  rw [← h]; apply takeI_left

中文:
定理 takeI_left'
  条件: {l₁ l₂ : List α} {n} (h : length l₁ = n)
  结论: takeI n (l₁ ++ l₂) = l₁
  证明: by
  rw [← h]; apply takeI_left

Depends on / 依赖: takeI_left
-/
theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left

end TakeI

/- The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
/--
theorem `takeD_length` / 定理 `takeD_length`

English:
theorem takeD_length
  statement: forall n l a, length (@takeD α n l a) = n

中文:
定理 takeD_length
  结论: 对任意 n l a, length (@takeD α n l a) = n
-/
theorem takeD_length : forall n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- `takeD_nil` is already in batteries

/--
theorem `takeD_eq_take` / 定理 `takeD_eq_take`

English:
theorem takeD_eq_take
  statement: forall {n} {l : List α} a, n <= length l -> takeD n l a = take n l

中文:
定理 takeD_eq_take
  结论: 对任意 {n} {l : List α} a, n <= length l -> takeD n l a = take n l
-/
theorem takeD_eq_take : forall {n} {l : List α} a, n <= length l -> takeD n l a = take n l
  | 0, _, _, _ => rfl
| _ + 1, _ :: _, a, h => congr_arg (cons _) takeD_eq_take a le_of_succ_le_succ h

@[simp]
/--
theorem `takeD_left` / 定理 `takeD_left`

English:
theorem takeD_left
  given: (l₁ l₂ : List α) (a : α)
  statement: takeD (length l₁) (l₁ ++ l₂) a = l₁
  proof: (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans take_left

中文:
定理 takeD_left
  条件: (l₁ l₂ : List α) (a : α)
  结论: takeD (length l₁) (l₁ ++ l₂) a = l₁
  证明: (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans take_left

Depends on / 依赖: Nat.le_add_right, le_add_right, length_append, takeD_eq_take, take_left
-/
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans take_left

/--
theorem `takeD_left'` / 定理 `takeD_left'`

English:
theorem takeD_left'
  given: {l₁ l₂ : List α} {n} {a} (h : length l₁ = n)
  statement: takeD n (l₁ ++ l₂) a = l₁
  proof: by
  rw [← h]; apply takeD_left

中文:
定理 takeD_left'
  条件: {l₁ l₂ : List α} {n} {a} (h : length l₁ = n)
  结论: takeD n (l₁ ++ l₂) a = l₁
  证明: by
  rw [← h]; apply takeD_left

Depends on / 依赖: takeD_left
-/
theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ := by
  rw [← h]; apply takeD_left

end TakeD

/-! ### filter -/

section Filter

variable (p)

variable (p : α -> Bool)

/--
theorem `span.loop_eq_take_drop` / 定理 `span.loop_eq_take_drop`

English:
theorem span.loop_eq_take_drop

中文:
定理 span.loop_eq_take_drop
-/
private theorem span.loop_eq_take_drop :
    forall l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
/--
theorem `span_eq_takeWhile_dropWhile` / 定理 `span_eq_takeWhile_dropWhile`

English:
theorem span_eq_takeWhile_dropWhile
  given: (l : List α)
  statement: span p l = (takeWhile p l, dropWhile p l)
  proof: by
  simpa using! span.loop_eq_take_drop p l []

中文:
定理 span_eq_takeWhile_dropWhile
  条件: (l : List α)
  结论: span p l = (takeWhile p l, dropWhile p l)
  证明: by
  simpa using! span.loop_eq_take_drop p l []

Depends on / 依赖: loop_eq_take_drop, span.loop_eq_take_drop
-/
theorem span_eq_takeWhile_dropWhile (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using! span.loop_eq_take_drop p l []

end Filter


/--
theorem `dropSlice_eq` / 定理 `dropSlice_eq`

English:
theorem dropSlice_eq
  given: (xs : List α) (n m : Nat)
  statement: dropSlice n m xs = xs.take n ++ xs.drop (n + m)
  proof: by
  induction n generalizing xs with cases xs with grind [dropSlice]

@[simp, grind =]

中文:
定理 dropSlice_eq
  条件: (xs : List α) (n m : 自然数)
  结论: dropSlice n m xs = xs.take n ++ xs.drop (n + m)
  证明: by
  induction n generalizing xs with cases xs with grind [dropSlice]

@[simp, grind =]

Depends on / 依赖: dropSlice, generalizing
-/
theorem dropSlice_eq (xs : List α) (n m : Nat) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs with cases xs with grind [dropSlice]

@[simp, grind =]
/--
theorem `length_dropSlice` / 定理 `length_dropSlice`

English:
theorem length_dropSlice
  given: (i j : Nat) (xs : List α)
  proof: by
  induction xs generalizing i j with cases i with grind [dropSlice]

中文:
定理 length_dropSlice
  条件: (i j : 自然数) (xs : List α)
  证明: by
  induction xs generalizing i j with cases i with grind [dropSlice]

Depends on / 依赖: dropSlice, generalizing
-/
theorem length_dropSlice (i j : Nat) (xs : List α) :
    (dropSlice i j xs).length = xs.length - min j (xs.length - i) := by
  induction xs generalizing i j with cases i with grind [dropSlice]

/--
theorem `length_dropSlice_lt` / 定理 `length_dropSlice_lt`

English:
theorem length_dropSlice_lt
  given: (i j : Nat) (hj : 0 < j) (xs : List α) (hi : i < xs.length)
  proof: by grind

中文:
定理 length_dropSlice_lt
  条件: (i j : 自然数) (hj : 0 < j) (xs : List α) (hi : i < xs.length)
  证明: by grind
-/
theorem length_dropSlice_lt (i j : Nat) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    (dropSlice i j xs).length < xs.length := by grind

end List
