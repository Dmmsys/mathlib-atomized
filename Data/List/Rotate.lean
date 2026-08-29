/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yakov Pechersky
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Quot

/-!
# List rotation

This file proves basic results about `List.rotate`, the list rotation.

## Main declarations

* `List.IsRotated l₁ l₂`: States that `l₁` is a rotated version of `l₂`.
* `List.cyclicPermutations l`: The list of all cyclic permutants of `l`, up to the length of `l`.

## Tags

rotated, rotation, permutation, cycle
-/

@[expose] public section


universe u

variable {α : Type u}

open Nat Function

namespace List

@[simp]
/--
theorem `rotate_mod` / 定理 `rotate_mod`

English:
theorem rotate_mod
  given: (l : List α) (n : Nat)
  statement: l.rotate (n % l.length) = l.rotate n
  proof: by simp [rotate]

@[simp]

中文:
定理 rotate_mod
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate (n % l.length) = l.rotate n
  证明: by simp [rotate]

@[simp]

Depends on / 依赖: rotate
-/
theorem rotate_mod (l : List α) (n : Nat) : l.rotate (n % l.length) = l.rotate n := by simp [rotate]

@[simp]
/--
theorem `rotate_nil` / 定理 `rotate_nil`

English:
theorem rotate_nil
  given: (n : Nat)
  statement: ([] : List α).rotate n = []
  proof: by simp [rotate]

@[simp]

中文:
定理 rotate_nil
  条件: (n : 自然数)
  结论: ([] : 列表 α).rotate n = []
  证明: by simp [rotate]

@[simp]

Depends on / 依赖: rotate
-/
theorem rotate_nil (n : Nat) : ([] : List α).rotate n = [] := by simp [rotate]

@[simp]
/--
theorem `rotate_zero` / 定理 `rotate_zero`

English:
theorem rotate_zero
  given: (l : List α)
  statement: l.rotate 0 = l
  proof: by simp [rotate]

中文:
定理 rotate_zero
  条件: (l : 列表 α)
  结论: l.rotate 0 = l
  证明: by simp [rotate]

Depends on / 依赖: rotate
-/
theorem rotate_zero (l : List α) : l.rotate 0 = l := by simp [rotate]

/--
theorem `rotate'_nil` / 定理 `rotate'_nil`

English:
theorem rotate'_nil
  given: (n : Nat)
  statement: ([] : List α).rotate' n = []
  proof: by simp

@[simp]

中文:
定理 rotate'_nil
  条件: (n : 自然数)
  结论: ([] : 列表 α).rotate' n = []
  证明: by simp

@[simp]
-/
theorem rotate'_nil (n : Nat) : ([] : List α).rotate' n = [] := by simp

@[simp]
/--
theorem `rotate'_zero` / 定理 `rotate'_zero`

English:
theorem rotate'_zero
  given: (l : List α)
  statement: l.rotate' 0 = l
  proof: by cases l <;> rfl

中文:
定理 rotate'_zero
  条件: (l : 列表 α)
  结论: l.rotate' 0 = l
  证明: by cases l <;> rfl
-/
theorem rotate'_zero (l : List α) : l.rotate' 0 = l := by cases l <;> rfl

/--
theorem `rotate'_cons_succ` / 定理 `rotate'_cons_succ`

English:
theorem rotate'_cons_succ
  given: (l : List α) (a : α) (n : Nat)
  proof: by simp [rotate']

@[simp]

中文:
定理 rotate'_cons_succ
  条件: (l : 列表 α) (a : α) (n : 自然数)
  证明: by simp [rotate']

@[simp]
-/
theorem rotate'_cons_succ (l : List α) (a : α) (n : Nat) :
    (a :: l : List α).rotate' n.succ = (l ++ [a]).rotate' n := by simp [rotate']

@[simp]
/--
theorem `length_rotate'` / 定理 `length_rotate'`

English:
theorem length_rotate'
  statement: forall (l : List α) (n : Nat), (l.rotate' n).length = l.length

中文:
定理 length_rotate'
  结论: 对任意 (l : 列表 α) (n : 自然数), (l.rotate' n).length = l.length
-/
theorem length_rotate' : forall (l : List α) (n : Nat), (l.rotate' n).length = l.length
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | a :: l, n + 1 => by rw [List.rotate', length_rotate' (l ++ [a]) n]; simp

/--
theorem `rotate'_eq_drop_append_take` / 定理 `rotate'_eq_drop_append_take`

English:
theorem rotate'_eq_drop_append_take
  proof: le_of_succ_le_succ h
    have hnl' : n <= (l ++ [a]).length := by
      rw [length_append]; rw [length_cons]; rw [List.length]; exact le_of_succ_le h
    rw [rotate'_cons_succ]; rw [rotate'_eq_drop_append_take hnl']; rw [drop]; rw [take]; rw [drop_append_of_le_length hnl]; rw [take_append_of_le_leng

中文:
定理 rotate'_eq_drop_append_take
  证明: le_of_succ_le_succ h
    have hnl' : n <= (l ++ [a]).length := by
      rw [length_append]; rw [length_cons]; rw [List.length]; exact le_of_succ_le h
    rw [rotate'_cons_succ]; rw [rotate'_eq_drop_append_take hnl']; rw [drop]; rw [take]; rw [drop_append_of_le_length hnl]; rw [take_append_of_le_leng
-/
theorem rotate'_eq_drop_append_take :
    forall {l : List α} {n : Nat}, n <= l.length -> l.rotate' n = l.drop n ++ l.take n
  | [], n, h => by simp
  | l, 0, h => by simp
  | a :: l, n + 1, h => by
    have hnl : n <= l.length := le_of_succ_le_succ h
    have hnl' : n <= (l ++ [a]).length := by
      rw [length_append]; rw [length_cons]; rw [List.length]; exact le_of_succ_le h
    rw [rotate'_cons_succ]; rw [rotate'_eq_drop_append_take hnl']; rw [drop]; rw [take]; rw [drop_append_of_le_length hnl]; rw [take_append_of_le_length hnl]; simp

@[simp]
/--
theorem `rotate'_rotate'` / 定理 `rotate'_rotate'`

English:
theorem rotate'_rotate'
  statement: forall (l : List α) (n m : Nat), (l.rotate' n).rotate' m = l.rotate' (n + m)

中文:
定理 rotate'_rotate'
  结论: 对任意 (l : 列表 α) (n m : 自然数), (l.rotate' n).rotate' m = l.rotate' (n + m)
-/
theorem rotate'_rotate' : forall (l : List α) (n m : Nat), (l.rotate' n).rotate' m = l.rotate' (n + m)
  | a :: l, 0, m => by simp
  | [], n, m => by simp
  | a :: l, n + 1, m => by
    rw [rotate'_cons_succ]; rw [rotate'_rotate' _ n]; rw [Nat.add_right_comm]; rw [← rotate'_cons_succ]; rw [Nat.succ_eq_add_one]

@[simp]
/--
theorem `rotate'_length` / 定理 `rotate'_length`

English:
theorem rotate'_length
  given: (l : List α)
  statement: rotate' l l.length = l
  proof: by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]

中文:
定理 rotate'_length
  条件: (l : 列表 α)
  结论: rotate' l l.length = l
  证明: by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]
-/
theorem rotate'_length (l : List α) : rotate' l l.length = l := by
  rw [rotate'_eq_drop_append_take le_rfl]; simp

@[simp]
/--
theorem `rotate'_length_mul` / 定理 `rotate'_length_mul`

English:
theorem rotate'_length_mul
  given: (l : List α)
  statement: forall n : Nat, l.rotate' (l.length * n) = l
  proof: by
        simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

@[simp]

中文:
定理 rotate'_length_mul
  条件: (l : 列表 α)
  结论: 对任意 n : 自然数, l.rotate' (l.length * n) = l
  证明: by
        simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

@[simp]
-/
theorem rotate'_length_mul (l : List α) : forall n : Nat, l.rotate' (l.length * n) = l
  | 0 => by simp
  | n + 1 =>
    calc
      l.rotate' (l.length * (n + 1)) =
          (l.rotate' (l.length * n)).rotate' (l.rotate' (l.length * n)).length := by
        simp [-rotate'_length, Nat.mul_succ, rotate'_rotate']
      _ = l := by rw [rotate'_length, rotate'_length_mul l n]

@[simp]
/--
theorem `rotate'_mod` / 定理 `rotate'_mod`

English:
theorem rotate'_mod
  given: (l : List α) (n : Nat)
  statement: l.rotate' (n % l.length) = l.rotate' n
  proof: calc l.rotate' (n % l.length)
    _ = (l.rotate' (n % l.length)).rotate'
        ((l.rotate' (n % l.length)).length * (n / l.length)) := by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]

中文:
定理 rotate'_mod
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate' (n % l.length) = l.rotate' n
  证明: calc l.rotate' (n % l.length)
    _ = (l.rotate' (n % l.length)).rotate'
        ((l.rotate' (n % l.length)).length * (n / l.length)) := by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]
-/
theorem rotate'_mod (l : List α) (n : Nat) : l.rotate' (n % l.length) = l.rotate' n :=
  calc l.rotate' (n % l.length)
    _ = (l.rotate' (n % l.length)).rotate'
        ((l.rotate' (n % l.length)).length * (n / l.length)) := by rw [rotate'_length_mul]
    _ = l.rotate' n := by rw [rotate'_rotate', length_rotate', Nat.mod_add_div]

/--
theorem `rotate_eq_rotate'` / 定理 `rotate_eq_rotate'`

English:
theorem rotate_eq_rotate'
  given: (l : List α) (n : Nat)
  statement: l.rotate n = l.rotate' n
  proof: if h : l.length = 0 then by simp_all [length_eq_zero_iff]
  else by
    rw [← rotate'_mod]; rw [rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))]
    simp [rotate]

中文:
定理 rotate_eq_rotate'
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate n = l.rotate' n
  证明: if h : l.length = 0 then by simp_all [length_eq_zero_iff]
  else by
    rw [← rotate'_mod]; rw [rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))]
    simp [rotate]

Depends on / 依赖: Nat.mod_lt, Nat.pos_of_ne_zero, _eq_drop_append_take, _mod, l.length, le_of_lt, length, length_eq_zero_iff, mod_lt, pos_of_ne_zero, rotate
-/
theorem rotate_eq_rotate' (l : List α) (n : Nat) : l.rotate n = l.rotate' n :=
  if h : l.length = 0 then by simp_all [length_eq_zero_iff]
  else by
    rw [← rotate'_mod]; rw [rotate'_eq_drop_append_take (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))]
    simp [rotate]

/--
theorem `rotate_cons_succ` / 定理 `rotate_cons_succ`

English:
theorem rotate_cons_succ
  given: (l : List α) (a : α) (n : Nat)
  proof: by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_cons_succ]

@[simp]

中文:
定理 rotate_cons_succ
  条件: (l : 列表 α) (a : α) (n : 自然数)
  证明: by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_cons_succ]

@[simp]
-/
@[simp] theorem rotate_cons_succ (l : List α) (a : α) (n : Nat) :
    (a :: l : List α).rotate (n + 1) = (l ++ [a]).rotate n := by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_cons_succ]

@[simp]
/--
theorem `mem_rotate` / 定理 `mem_rotate`

English:
theorem mem_rotate
  statement: forall {l : List α} {a : α} {n : Nat}, a in l.rotate n ↔ a in l

中文:
定理 mem_rotate
  结论: 对任意 {l : 列表 α} {a : α} {n : 自然数}, a in l.rotate n ↔ a in l
-/
theorem mem_rotate : forall {l : List α} {a : α} {n : Nat}, a in l.rotate n ↔ a in l
  | [], _, n => by simp
  | a :: l, _, 0 => by simp
  | a :: l, _, n + 1 => by simp [rotate_cons_succ, mem_rotate, or_comm]

@[simp]
/--
theorem `length_rotate` / 定理 `length_rotate`

English:
theorem length_rotate
  given: (l : List α) (n : Nat)
  statement: (l.rotate n).length = l.length
  proof: by
  rw [rotate_eq_rotate']; rw [length_rotate']

@[simp]

中文:
定理 length_rotate
  条件: (l : 列表 α) (n : 自然数)
  结论: (l.rotate n).length = l.length
  证明: by
  rw [rotate_eq_rotate']; rw [length_rotate']

@[simp]

Depends on / 依赖: length_rotate, rotate_eq_rotate
-/
theorem length_rotate (l : List α) (n : Nat) : (l.rotate n).length = l.length := by
  rw [rotate_eq_rotate']; rw [length_rotate']

@[simp]
/--
theorem `rotate_replicate` / 定理 `rotate_replicate`

English:
theorem rotate_replicate
  given: (a : α) (n : Nat) (k : Nat)
  statement: (replicate n a).rotate k = replicate n a
  proof: eq_replicate_iff.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
eq_of_mem_replicate mem_rotate.1 hb⟩

中文:
定理 rotate_replicate
  条件: (a : α) (n : 自然数) (k : 自然数)
  结论: (replicate n a).rotate k = replicate n a
  证明: eq_replicate_iff.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
eq_of_mem_replicate mem_rotate.1 hb⟩

Depends on / 依赖: eq_of_mem_replicate, eq_replicate_iff, length_replicate, length_rotate, mem_rotate
-/
theorem rotate_replicate (a : α) (n : Nat) (k : Nat) : (replicate n a).rotate k = replicate n a :=
  eq_replicate_iff.2 ⟨by rw [length_rotate, length_replicate], fun b hb =>
eq_of_mem_replicate mem_rotate.1 hb⟩

/--
theorem `rotate_eq_drop_append_take` / 定理 `rotate_eq_drop_append_take`

English:
theorem rotate_eq_drop_append_take
  given: {l : List α} {n : Nat}
  proof: by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take

中文:
定理 rotate_eq_drop_append_take
  条件: {l : 列表 α} {n : 自然数}
  证明: by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take

Depends on / 依赖: _eq_drop_append_take, rotate, rotate_eq_rotate
-/
theorem rotate_eq_drop_append_take {l : List α} {n : Nat} :
    n <= l.length -> l.rotate n = l.drop n ++ l.take n := by
  rw [rotate_eq_rotate']; exact rotate'_eq_drop_append_take

/--
theorem `rotate_eq_drop_append_take_mod` / 定理 `rotate_eq_drop_append_take_mod`

English:
theorem rotate_eq_drop_append_take_mod
  given: {l : List α} {n : Nat}
  proof: by
  rcases l.length.zero_le.eq_or_lt with hl | hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le]; rw [rotate_mod]

@[simp]

中文:
定理 rotate_eq_drop_append_take_mod
  条件: {l : 列表 α} {n : 自然数}
  证明: by
  rcases l.length.zero_le.eq_or_lt with hl | hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le]; rw [rotate_mod]

@[simp]

Depends on / 依赖: eq_nil_of_length_eq_zero, eq_or_lt, hl.symm, l.length.zero_le.eq_or_lt, length, mod_lt, n.mod_lt, rotate_eq_drop_append_take, rotate_mod, zero_le
-/
theorem rotate_eq_drop_append_take_mod {l : List α} {n : Nat} :
    l.rotate n = l.drop (n % l.length) ++ l.take (n % l.length) := by
  rcases l.length.zero_le.eq_or_lt with hl | hl
  · simp [eq_nil_of_length_eq_zero hl.symm]
  rw [← rotate_eq_drop_append_take (n.mod_lt hl).le]; rw [rotate_mod]

@[simp]
/--
theorem `rotate_append_length_eq` / 定理 `rotate_append_length_eq`

English:
theorem rotate_append_length_eq
  given: (l l' : List α)
  statement: (l ++ l').rotate l.length = l' ++ l
  proof: by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp_all [rotate']

@[simp]

中文:
定理 rotate_append_length_eq
  条件: (l l' : 列表 α)
  结论: (l ++ l').rotate l.length = l' ++ l
  证明: by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp_all [rotate']

@[simp]

Depends on / 依赖: generalizing, rotate, rotate_eq_rotate
-/
theorem rotate_append_length_eq (l l' : List α) : (l ++ l').rotate l.length = l' ++ l := by
  rw [rotate_eq_rotate']
  induction l generalizing l'
  · simp
  · simp_all [rotate']

@[simp]
/--
theorem `rotate_rotate` / 定理 `rotate_rotate`

English:
theorem rotate_rotate
  given: (l : List α) (n m : Nat)
  statement: (l.rotate n).rotate m = l.rotate (n + m)
  proof: by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_rotate']

@[simp]

中文:
定理 rotate_rotate
  条件: (l : 列表 α) (n m : 自然数)
  结论: (l.rotate n).rotate m = l.rotate (n + m)
  证明: by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_rotate']

@[simp]

Depends on / 依赖: _rotate, rotate, rotate_eq_rotate
-/
theorem rotate_rotate (l : List α) (n m : Nat) : (l.rotate n).rotate m = l.rotate (n + m) := by
  rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate_eq_rotate']; rw [rotate'_rotate']

@[simp]
/--
theorem `rotate_length` / 定理 `rotate_length`

English:
theorem rotate_length
  given: (l : List α)
  statement: rotate l l.length = l
  proof: by
  rw [rotate_eq_rotate']; rw [rotate'_length]

@[simp]

中文:
定理 rotate_length
  条件: (l : 列表 α)
  结论: rotate l l.length = l
  证明: by
  rw [rotate_eq_rotate']; rw [rotate'_length]

@[simp]

Depends on / 依赖: _length, rotate, rotate_eq_rotate
-/
theorem rotate_length (l : List α) : rotate l l.length = l := by
  rw [rotate_eq_rotate']; rw [rotate'_length]

@[simp]
/--
theorem `rotate_length_mul` / 定理 `rotate_length_mul`

English:
theorem rotate_length_mul
  given: (l : List α) (n : Nat)
  statement: l.rotate (l.length * n) = l
  proof: by
  rw [rotate_eq_rotate']; rw [rotate'_length_mul]

中文:
定理 rotate_length_mul
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate (l.length * n) = l
  证明: by
  rw [rotate_eq_rotate']; rw [rotate'_length_mul]

Depends on / 依赖: _length_mul, rotate, rotate_eq_rotate
-/
theorem rotate_length_mul (l : List α) (n : Nat) : l.rotate (l.length * n) = l := by
  rw [rotate_eq_rotate']; rw [rotate'_length_mul]

/--
theorem `rotate_perm` / 定理 `rotate_perm`

English:
theorem rotate_perm
  given: (l : List α) (n : Nat)
  statement: l.rotate n ~ l
  proof: by
  rw [rotate_eq_rotate']
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]

中文:
定理 rotate_perm
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate n ~ l
  证明: by
  rw [rotate_eq_rotate']
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]

Depends on / 依赖: _cons_succ, generalizing, perm_append_singleton, rotate, rotate_eq_rotate
-/
theorem rotate_perm (l : List α) (n : Nat) : l.rotate n ~ l := by
  rw [rotate_eq_rotate']
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate'_cons_succ]
      exact (hn _).trans (perm_append_singleton _ _)

@[simp]
/--
theorem `nodup_rotate` / 定理 `nodup_rotate`

English:
theorem nodup_rotate
  given: {l : List α} {n : Nat}
  statement: Nodup (l.rotate n) ↔ Nodup l
  proof: (rotate_perm l n).nodup_iff

@[simp]

中文:
定理 nodup_rotate
  条件: {l : 列表 α} {n : 自然数}
  结论: Nodup (l.rotate n) ↔ Nodup l
  证明: (rotate_perm l n).nodup_iff

@[simp]

Depends on / 依赖: nodup_iff, rotate_perm
-/
theorem nodup_rotate {l : List α} {n : Nat} : Nodup (l.rotate n) ↔ Nodup l :=
  (rotate_perm l n).nodup_iff

@[simp]
/--
theorem `rotate_eq_nil_iff` / 定理 `rotate_eq_nil_iff`

English:
theorem rotate_eq_nil_iff
  given: {l : List α} {n : Nat}
  statement: l.rotate n = [] ↔ l = []
  proof: by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [rotate_cons_succ, hn]

中文:
定理 rotate_eq_nil_iff
  条件: {l : 列表 α} {n : 自然数}
  结论: l.rotate n = [] ↔ l = []
  证明: by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [rotate_cons_succ, hn]

Depends on / 依赖: generalizing, rotate_cons_succ
-/
theorem rotate_eq_nil_iff {l : List α} {n : Nat} : l.rotate n = [] ↔ l = [] := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [rotate_cons_succ, hn]

/--
theorem `nil_eq_rotate_iff` / 定理 `nil_eq_rotate_iff`

English:
theorem nil_eq_rotate_iff
  given: {l : List α} {n : Nat}
  statement: [] = l.rotate n ↔ [] = l
  proof: by
  rw [eq_comm]; rw [rotate_eq_nil_iff]; rw [eq_comm]

@[simp]

中文:
定理 nil_eq_rotate_iff
  条件: {l : 列表 α} {n : 自然数}
  结论: [] = l.rotate n ↔ [] = l
  证明: by
  rw [eq_comm]; rw [rotate_eq_nil_iff]; rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, rotate_eq_nil_iff
-/
theorem nil_eq_rotate_iff {l : List α} {n : Nat} : [] = l.rotate n ↔ [] = l := by
  rw [eq_comm]; rw [rotate_eq_nil_iff]; rw [eq_comm]

@[simp]
/--
theorem `rotate_singleton` / 定理 `rotate_singleton`

English:
theorem rotate_singleton
  given: (x : α) (n : Nat)
  statement: [x].rotate n = [x]
  proof: rotate_replicate x 1 n

中文:
定理 rotate_singleton
  条件: (x : α) (n : 自然数)
  结论: [x].rotate n = [x]
  证明: rotate_replicate x 1 n

Depends on / 依赖: rotate_replicate
-/
theorem rotate_singleton (x : α) (n : Nat) : [x].rotate n = [x] :=
  rotate_replicate x 1 n

/--
theorem `zipWith_rotate_distrib` / 定理 `zipWith_rotate_distrib`

English:
theorem zipWith_rotate_distrib
  statement: {β γ : Type*} (f : α -> β -> γ) (l : List α) (l' : List β) (n : Nat)
  proof: by
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [h]; rw [zipWith_append]; rw [← drop_zipWith]; rw [←
    take_zipWith]; rw [List.length_zipWith]; rw [h]; rw [min_self]
  rw [length_drop]; rw [length_drop]; rw [h]

中文:
定理 zipWith_rotate_distrib
  结论: {β γ : 类型} (f : α -> β -> γ) (l : 列表 α) (l' : 列表 β) (n : 自然数)
  证明: by
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [h]; rw [zipWith_append]; rw [← drop_zipWith]; rw [←
    take_zipWith]; rw [List.length_zipWith]; rw [h]; rw [min_self]
  rw [length_drop]; rw [length_drop]; rw [h]

Depends on / 依赖: List.length_zipWith, drop_zipWith, length_drop, length_zipWith, min_self, rotate_eq_drop_append_take_mod, take_zipWith, zipWith_append
-/
theorem zipWith_rotate_distrib {β γ : Type*} (f : α -> β -> γ) (l : List α) (l' : List β) (n : Nat)
    (h : l.length = l'.length) :
    (zipWith f l l').rotate n = zipWith f (l.rotate n) (l'.rotate n) := by
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod]; rw [h]; rw [zipWith_append]; rw [← drop_zipWith]; rw [←
    take_zipWith]; rw [List.length_zipWith]; rw [h]; rw [min_self]
  rw [length_drop]; rw [length_drop]; rw [h]

/--
theorem `zipWith_rotate_one` / 定理 `zipWith_rotate_one`

English:
theorem zipWith_rotate_one
  given: {β : Type*} (f : α -> α -> β) (x y : α) (l : List α)
  proof: by
  simp

中文:
定理 zipWith_rotate_one
  条件: {β : 类型} (f : α -> α -> β) (x y : α) (l : 列表 α)
  证明: by
  simp
-/
theorem zipWith_rotate_one {β : Type*} (f : α -> α -> β) (x y : α) (l : List α) :
    zipWith f (x :: y :: l) ((x :: y :: l).rotate 1) = f x y :: zipWith f (y :: l) (l ++ [x]) := by
  simp

/--
theorem `getElem?_rotate` / 定理 `getElem?_rotate`

English:
theorem getElem?_rotate
  given: {l : List α} {n m : Nat} (hml : m < l.length)
  proof: by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_ge m (l.drop (n % l.length)).length with hm | hm
  · rw [getElem?_append_left hm, getElem?_drop, ← add_mod_mod]
    rw [length_drop]; rw [Nat.lt_sub_iff_add_lt] at hm
    rw [mod_eq_of_lt hm]; rw [Nat.add_comm]
  · have hlt : n % length l < len

中文:
定理 getElem?_rotate
  条件: {l : 列表 α} {n m : 自然数} (hml : m < l.length)
  证明: by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_ge m (l.drop (n % l.length)).length with hm | hm
  · rw [getElem?_append_left hm, getElem?_drop, ← add_mod_mod]
    rw [length_drop]; rw [Nat.lt_sub_iff_add_lt] at hm
    rw [mod_eq_of_lt hm]; rw [Nat.add_comm]
  · have hlt : n % length l < len
-/
theorem getElem?_rotate {l : List α} {n m : Nat} (hml : m < l.length) :
    (l.rotate n)[m]? = l[(m + n) % l.length]? := by
  rw [rotate_eq_drop_append_take_mod]
  rcases lt_or_ge m (l.drop (n % l.length)).length with hm | hm
  · rw [getElem?_append_left hm, getElem?_drop, ← add_mod_mod]
    rw [length_drop]; rw [Nat.lt_sub_iff_add_lt] at hm
    rw [mod_eq_of_lt hm]; rw [Nat.add_comm]
  · have hlt : n % length l < length l := mod_lt _ (m.zero_le.trans_lt hml)
    rw [getElem?_append_right hm]; rw [getElem?_take_of_lt]; rw [length_drop]
    · congr 1
      rw [length_drop] at hm
      have hm' := Nat.sub_le_iff_le_add'.1 hm
      have : n % length l + m - length l < length l := by
        rw [Nat.sub_lt_iff_lt_add hm']
        exact Nat.add_lt_add hlt hml
      conv_rhs => rw [Nat.add_comm m, ← mod_add_mod, mod_eq_sub_mod hm', mod_eq_of_lt this]
      lia
    · rwa [Nat.sub_lt_iff_lt_add' hm, length_drop, Nat.sub_add_cancel hlt.le]

@[simp]
/--
theorem `getElem_rotate` / 定理 `getElem_rotate`

English:
theorem getElem_rotate
  given: (l : List α) (n : Nat) (k : Nat) (h : k < (l.rotate n).length)
  proof: by
  rw [← Option.some_inj]; rw [← getElem?_eq_getElem]; rw [← getElem?_eq_getElem]; rw [getElem?_rotate]
  exact h.trans_eq (length_rotate _ _)

中文:
定理 getElem_rotate
  条件: (l : 列表 α) (n : 自然数) (k : 自然数) (h : k < (l.rotate n).length)
  证明: by
  rw [← Option.some_inj]; rw [← getElem?_eq_getElem]; rw [← getElem?_eq_getElem]; rw [getElem?_rotate]
  exact h.trans_eq (length_rotate _ _)

Depends on / 依赖: Option.some_inj, _eq_getElem, _rotate, getElem, h.trans_eq, length_rotate, some_inj, trans_eq
-/
theorem getElem_rotate (l : List α) (n : Nat) (k : Nat) (h : k < (l.rotate n).length) :
    (l.rotate n)[k] =
      l[(k + n) % l.length]'(mod_lt _ (length_rotate l n ▸ k.zero_le.trans_lt h)) := by
  rw [← Option.some_inj]; rw [← getElem?_eq_getElem]; rw [← getElem?_eq_getElem]; rw [getElem?_rotate]
  exact h.trans_eq (length_rotate _ _)

/--
theorem `get_rotate` / 定理 `get_rotate`

English:
theorem get_rotate
  given: (l : List α) (n : Nat) (k : Fin (l.rotate n).length)
  proof: by
  simp [getElem_rotate]

@[simp]

中文:
定理 get_rotate
  条件: (l : 列表 α) (n : 自然数) (k : 有限集 (l.rotate n).length)
  证明: by
  simp [getElem_rotate]

@[simp]

Depends on / 依赖: getElem_rotate
-/
theorem get_rotate (l : List α) (n : Nat) (k : Fin (l.rotate n).length) :
    (l.rotate n).get k = l.get ⟨(k + n) % l.length, mod_lt _ (length_rotate l n ▸ k.pos)⟩ := by
  simp [getElem_rotate]

@[simp]
/--
theorem `head?_rotate` / 定理 `head?_rotate`

English:
theorem head?_rotate
  given: {l : List α} {n : Nat} (h : n < l.length)
  statement: head? (l.rotate n) = l[n]?
  proof: by
  rw [head?_eq_getElem?]; rw [getElem?_rotate (n.zero_le.trans_lt h)]; rw [Nat.zero_add]; rw [Nat.mod_eq_of_lt h]

中文:
定理 head?_rotate
  条件: {l : 列表 α} {n : 自然数} (h : n < l.length)
  结论: head? (l.rotate n) = l[n]?
  证明: by
  rw [head?_eq_getElem?]; rw [getElem?_rotate (n.zero_le.trans_lt h)]; rw [Nat.zero_add]; rw [Nat.mod_eq_of_lt h]
-/
theorem head?_rotate {l : List α} {n : Nat} (h : n < l.length) : head? (l.rotate n) = l[n]? := by
  rw [head?_eq_getElem?]; rw [getElem?_rotate (n.zero_le.trans_lt h)]; rw [Nat.zero_add]; rw [Nat.mod_eq_of_lt h]

/--
theorem `get_rotate_one` / 定理 `get_rotate_one`

English:
theorem get_rotate_one
  given: (l : List α) (k : Fin (l.rotate 1).length)
  proof: get_rotate l 1 k

中文:
定理 get_rotate_one
  条件: (l : 列表 α) (k : 有限集 (l.rotate 1).length)
  证明: get_rotate l 1 k

Depends on / 依赖: get_rotate
-/
theorem get_rotate_one (l : List α) (k : Fin (l.rotate 1).length) :
    (l.rotate 1).get k = l.get ⟨(k + 1) % l.length, mod_lt _ (length_rotate l 1 ▸ k.pos)⟩ :=
  get_rotate l 1 k

-- Allow `l[a]'b` to have a line break between `[a]'` and `b`.
set_option linter.style.whitespace false in
/--
theorem `getElem_eq_getElem_rotate` / 定理 `getElem_eq_getElem_rotate`

English:
theorem getElem_eq_getElem_rotate
  given: (l : List α) (n : Nat) (k : Nat) (hk : k < l.length)
  proof: by
  rw [getElem_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod]; rw [Nat.add_right_comm]; rw [Nat.sub_add_cancel]; rw [add_mod_left]; rw [mod_eq_of_lt]
  exacts [hk, (mod_lt _ (k.zero_le.trans_lt hk)).le]

中文:
定理 getElem_eq_getElem_rotate
  条件: (l : 列表 α) (n : 自然数) (k : 自然数) (hk : k < l.length)
  证明: by
  rw [getElem_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod]; rw [Nat.add_right_comm]; rw [Nat.sub_add_cancel]; rw [add_mod_left]; rw [mod_eq_of_lt]
  exacts [hk, (mod_lt _ (k.zero_le.trans_lt hk)).le]

Depends on / 依赖: Fin.eq_of_val_eq, Nat.add_right_comm, Nat.sub_add_cancel, add_mod_left, add_mod_mod, add_right_comm, congr_arg, eq_of_val_eq, exacts, getElem_rotate, k.zero_le.trans_lt, l.get, mod_add_mod, mod_eq_of_lt, mod_lt, sub_add_cancel, trans_lt, zero_le
-/
theorem getElem_eq_getElem_rotate (l : List α) (n : Nat) (k : Nat) (hk : k < l.length) :
    l[k] = ((l.rotate n)[(l.length - n % l.length + k) % l.length]'
      ((Nat.mod_lt _ (k.zero_le.trans_lt hk)).trans_eq (length_rotate _ _).symm)) := by
  rw [getElem_rotate]
  refine congr_arg l.get (Fin.eq_of_val_eq ?_)
  simp only [mod_add_mod]
  rw [← add_mod_mod]; rw [Nat.add_right_comm]; rw [Nat.sub_add_cancel]; rw [add_mod_left]; rw [mod_eq_of_lt]
  exacts [hk, (mod_lt _ (k.zero_le.trans_lt hk)).le]

/--
theorem `get_eq_get_rotate` / 定理 `get_eq_get_rotate`

English:
theorem get_eq_get_rotate
  given: (l : List α) (n : Nat) (k : Fin l.length)
  proof: by
  simpa using getElem_eq_getElem_rotate _ _ _ _

中文:
定理 get_eq_get_rotate
  条件: (l : 列表 α) (n : 自然数) (k : 有限集 l.length)
  证明: by
  simpa using getElem_eq_getElem_rotate _ _ _ _

Depends on / 依赖: getElem_eq_getElem_rotate
-/
theorem get_eq_get_rotate (l : List α) (n : Nat) (k : Fin l.length) :
    l.get k = (l.rotate n).get ⟨(l.length - n % l.length + k) % l.length,
      (Nat.mod_lt _ (k.1.zero_le.trans_lt k.2)).trans_eq (length_rotate _ _).symm⟩ := by
  simpa using getElem_eq_getElem_rotate _ _ _ _

/--
theorem `rotate_eq_self_iff_eq_replicate` / 定理 `rotate_eq_self_iff_eq_replicate`

English:
theorem rotate_eq_self_iff_eq_replicate
  given: [hα : Nonempty α]

中文:
定理 rotate_eq_self_iff_eq_replicate
  条件: [hα : 非空 α]
-/
theorem rotate_eq_self_iff_eq_replicate [hα : Nonempty α] :
    forall {l : List α}, (forall n, l.rotate n = l) ↔ exists a, l = replicate l.length a
  | [] => by simp
  | a :: l => ⟨fun h => ⟨a, ext_getElem length_replicate.symm fun n h₁ h₂ => by
      rw [getElem_replicate]; rw [← Option.some_inj]; rw [← getElem?_eq_getElem]; rw [← head?_rotate h₁]; rw [h]; rw [head?_cons]⟩,
    fun ⟨b, hb⟩ n => by rw [hb, rotate_replicate]⟩

/--
theorem `rotate_one_eq_self_iff_eq_replicate` / 定理 `rotate_one_eq_self_iff_eq_replicate`

English:
theorem rotate_one_eq_self_iff_eq_replicate
  given: [Nonempty α] {l : List α}
  proof: ⟨fun h =>
    rotate_eq_self_iff_eq_replicate.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_replicate.mpr h 1⟩

中文:
定理 rotate_one_eq_self_iff_eq_replicate
  条件: [非空 α] {l : 列表 α}
  证明: ⟨fun h =>
    rotate_eq_self_iff_eq_replicate.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_replicate.mpr h 1⟩

Depends on / 依赖: Nat.rec, Nat.succ_eq_add_one, l.rotate_rotate, l.rotate_zero, rotate_eq_self_iff_eq_replicate, rotate_eq_self_iff_eq_replicate.mp, rotate_eq_self_iff_eq_replicate.mpr, rotate_rotate, rotate_zero, succ_eq_add_one
-/
theorem rotate_one_eq_self_iff_eq_replicate [Nonempty α] {l : List α} :
    l.rotate 1 = l ↔ exists a : α, l = List.replicate l.length a :=
  ⟨fun h =>
    rotate_eq_self_iff_eq_replicate.mp fun n =>
      Nat.rec l.rotate_zero (fun n hn => by rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn]) n,
    fun h => rotate_eq_self_iff_eq_replicate.mpr h 1⟩

/--
theorem `rotate_injective` / 定理 `rotate_injective`

English:
theorem rotate_injective
  given: (n : Nat)
  statement: Function.Injective fun l : List α => l.rotate n
  proof: by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h (by simp_all)
  rw [← take_append_drop _

中文:
定理 rotate_injective
  条件: (n : 自然数)
  结论: 函数.单射 fun l : 列表 α => l.rotate n
  证明: by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h (by simp_all)
  rw [← take_append_drop _

Depends on / 依赖: append_inj, h.symm, l.length, l.length_rotate, l.rotate, length, length_rotate, rotate, rotate_eq_drop_append_take_mod, symm.trans, take_append_drop
-/
theorem rotate_injective (n : Nat) : Function.Injective fun l : List α => l.rotate n := by
  rintro l l' (h : l.rotate n = l'.rotate n)
  have hle : l.length = l'.length := (l.length_rotate n).symm.trans (h.symm ▸ l'.length_rotate n)
  rw [rotate_eq_drop_append_take_mod]; rw [rotate_eq_drop_append_take_mod] at h
  obtain ⟨hd, ht⟩ := append_inj h (by simp_all)
  rw [← take_append_drop _ l]; rw [ht]; rw [hd]; rw [take_append_drop]

@[simp]
/--
theorem `rotate_eq_rotate` / 定理 `rotate_eq_rotate`

English:
theorem rotate_eq_rotate
  given: {l l' : List α} {n : Nat}
  statement: l.rotate n = l'.rotate n ↔ l = l'
  proof: (rotate_injective n).eq_iff

中文:
定理 rotate_eq_rotate
  条件: {l l' : 列表 α} {n : 自然数}
  结论: l.rotate n = l'.rotate n ↔ l = l'
  证明: (rotate_injective n).eq_iff

Depends on / 依赖: eq_iff, rotate_injective
-/
theorem rotate_eq_rotate {l l' : List α} {n : Nat} : l.rotate n = l'.rotate n ↔ l = l' :=
  (rotate_injective n).eq_iff

/--
theorem `rotate_eq_iff` / 定理 `rotate_eq_iff`

English:
theorem rotate_eq_iff
  given: {l l' : List α} {n : Nat}
  proof: by
  rw [← @rotate_eq_rotate _ l _ n]; rw [rotate_rotate]; rw [← rotate_mod l']; rw [add_mod]
  rcases l'.length.zero_le.eq_or_lt with hl | hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil]
  · rcases (Nat.zero_le (n % l'.length)).eq_or_lt with hn | hn
    · simp [← hn]
    · rw [mod_eq_of_lt

中文:
定理 rotate_eq_iff
  条件: {l l' : 列表 α} {n : 自然数}
  证明: by
  rw [← @rotate_eq_rotate _ l _ n]; rw [rotate_rotate]; rw [← rotate_mod l']; rw [add_mod]
  rcases l'.length.zero_le.eq_or_lt with hl | hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil]
  · rcases (Nat.zero_le (n % l'.length)).eq_or_lt with hn | hn
    · simp [← hn]
    · rw [mod_eq_of_lt

Depends on / 依赖: Nat.mod_lt, Nat.sub_add_cancel, Nat.sub_lt, Nat.zero_le, add_mod, eq_nil_of_length_eq_zero, eq_or_lt, hl.symm, length, length.zero_le.eq_or_lt, mod_eq_of_lt, mod_lt, mod_self, rotate_eq_rotate, rotate_mod, rotate_nil, rotate_rotate, rotate_zero, sub_add_cancel, sub_lt
-/
theorem rotate_eq_iff {l l' : List α} {n : Nat} :
    l.rotate n = l' ↔ l = l'.rotate (l'.length - n % l'.length) := by
  rw [← @rotate_eq_rotate _ l _ n]; rw [rotate_rotate]; rw [← rotate_mod l']; rw [add_mod]
  rcases l'.length.zero_le.eq_or_lt with hl | hl
  · rw [eq_nil_of_length_eq_zero hl.symm, rotate_nil]
  · rcases (Nat.zero_le (n % l'.length)).eq_or_lt with hn | hn
    · simp [← hn]
    · rw [mod_eq_of_lt (Nat.sub_lt hl hn), Nat.sub_add_cancel, mod_self, rotate_zero]
      exact (Nat.mod_lt _ hl).le

@[simp]
/--
theorem `rotate_eq_singleton_iff` / 定理 `rotate_eq_singleton_iff`

English:
theorem rotate_eq_singleton_iff
  given: {l : List α} {n : Nat} {x : α}
  statement: l.rotate n = [x] ↔ l = [x]
  proof: by
  rw [rotate_eq_iff]; rw [rotate_singleton]

@[simp]

中文:
定理 rotate_eq_singleton_iff
  条件: {l : 列表 α} {n : 自然数} {x : α}
  结论: l.rotate n = [x] ↔ l = [x]
  证明: by
  rw [rotate_eq_iff]; rw [rotate_singleton]

@[simp]

Depends on / 依赖: rotate_eq_iff, rotate_singleton
-/
theorem rotate_eq_singleton_iff {l : List α} {n : Nat} {x : α} : l.rotate n = [x] ↔ l = [x] := by
  rw [rotate_eq_iff]; rw [rotate_singleton]

@[simp]
/--
theorem `singleton_eq_rotate_iff` / 定理 `singleton_eq_rotate_iff`

English:
theorem singleton_eq_rotate_iff
  given: {l : List α} {n : Nat} {x : α}
  statement: [x] = l.rotate n ↔ [x] = l
  proof: by
  rw [eq_comm]; rw [rotate_eq_singleton_iff]; rw [eq_comm]

中文:
定理 singleton_eq_rotate_iff
  条件: {l : 列表 α} {n : 自然数} {x : α}
  结论: [x] = l.rotate n ↔ [x] = l
  证明: by
  rw [eq_comm]; rw [rotate_eq_singleton_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, rotate_eq_singleton_iff
-/
theorem singleton_eq_rotate_iff {l : List α} {n : Nat} {x : α} : [x] = l.rotate n ↔ [x] = l := by
  rw [eq_comm]; rw [rotate_eq_singleton_iff]; rw [eq_comm]

/--
theorem `reverse_rotate` / 定理 `reverse_rotate`

English:
theorem reverse_rotate
  given: (l : List α) (n : Nat)
  proof: by
  rw [← length_reverse]; rw [← rotate_eq_iff]
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate_cons_succ, ← rotate_rotate, hn]
      simp

中文:
定理 reverse_rotate
  条件: (l : 列表 α) (n : 自然数)
  证明: by
  rw [← length_reverse]; rw [← rotate_eq_iff]
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate_cons_succ, ← rotate_rotate, hn]
      simp

Depends on / 依赖: generalizing, length_reverse, rotate_cons_succ, rotate_eq_iff, rotate_rotate
-/
theorem reverse_rotate (l : List α) (n : Nat) :
    (l.rotate n).reverse = l.reverse.rotate (l.length - n % l.length) := by
  rw [← length_reverse]; rw [← rotate_eq_iff]
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · rw [rotate_cons_succ, ← rotate_rotate, hn]
      simp

/--
theorem `rotate_reverse` / 定理 `rotate_reverse`

English:
theorem rotate_reverse
  given: (l : List α) (n : Nat)
  proof: by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse]
  let k := n % l.reverse.length
  rcases hk' : k with - | k'
  · simp_all! [k, length_reverse, ← rotate_rotate]
  · rcases l with - | ⟨x,

中文:
定理 rotate_reverse
  条件: (l : 列表 α) (n : 自然数)
  证明: by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse]
  let k := n % l.reverse.length
  rcases hk' : k with - | k'
  · simp_all! [k, length_reverse, ← rotate_rotate]
  · rcases l with - | ⟨x,

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.sub_add_cancel, Nat.sub_le, Nat.sub_lt, l.reverse.length, length, length_reverse, length_rotate, mod_eq_of_lt, reverse, reverse_reverse, reverse_rotate, rotate_eq_iff, rotate_length, rotate_rotate, simp_rw, sub_add_cancel, sub_le, sub_lt
-/
theorem rotate_reverse (l : List α) (n : Nat) :
    l.reverse.rotate n = (l.rotate (l.length - n % l.length)).reverse := by
  rw [← reverse_reverse l]
  simp_rw [reverse_rotate, reverse_reverse, rotate_eq_iff, rotate_rotate, length_rotate,
    length_reverse]
  rw [← length_reverse]
  let k := n % l.reverse.length
  rcases hk' : k with - | k'
  · simp_all! [k, length_reverse, ← rotate_rotate]
  · rcases l with - | ⟨x, l⟩
    · simp
    · rw [Nat.mod_eq_of_lt, Nat.sub_add_cancel, rotate_length]
      · exact Nat.sub_le _ _
      · exact Nat.sub_lt (by simp) (by simp_all! [k])

@[simp]
/--
theorem `map_rotate` / 定理 `map_rotate`

English:
theorem map_rotate
  given: {β : Type*} (f : α -> β) (l : List α) (n : Nat)
  proof: by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [hn]

中文:
定理 map_rotate
  条件: {β : 类型} (f : α -> β) (l : 列表 α) (n : 自然数)
  证明: by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [hn]

Depends on / 依赖: generalizing
-/
theorem map_rotate {β : Type*} (f : α -> β) (l : List α) (n : Nat) :
    map f (l.rotate n) = (map f l).rotate n := by
  induction n generalizing l with
  | zero => simp
  | succ n hn =>
    rcases l with - | ⟨hd, tl⟩
    · simp
    · simp [hn]

/--
theorem `Nodup.rotate_congr` / 定理 `Nodup.rotate_congr`

English:
theorem Nodup.rotate_congr
  statement: {l : List α} (hl : l.Nodup) (hn : l != []) (i j : Nat)
  proof: by
  rw [← rotate_mod l i]; rw [← rotate_mod l j] at h
  simpa only [head?_rotate, mod_lt, length_pos_of_ne_nil hn, getElem?_eq_getElem, Option.some_inj,
    hl.getElem_inj_iff, Fin.ext_iff] using congr_arg head? h

中文:
定理 Nodup.rotate_congr
  结论: {l : 列表 α} (hl : l.Nodup) (hn : l != []) (i j : 自然数)
  证明: by
  rw [← rotate_mod l i]; rw [← rotate_mod l j] at h
  simpa only [head?_rotate, mod_lt, length_pos_of_ne_nil hn, getElem?_eq_getElem, Option.some_inj,
    hl.getElem_inj_iff, Fin.ext_iff] using congr_arg head? h

Depends on / 依赖: Fin.ext_iff, Option.some_inj, _eq_getElem, _rotate, congr_arg, ext_iff, getElem, getElem_inj_iff, hl.getElem_inj_iff, length_pos_of_ne_nil, mod_lt, rotate_mod, some_inj
-/
theorem Nodup.rotate_congr {l : List α} (hl : l.Nodup) (hn : l != []) (i j : Nat)
    (h : l.rotate i = l.rotate j) : i % l.length = j % l.length := by
  rw [← rotate_mod l i]; rw [← rotate_mod l j] at h
  simpa only [head?_rotate, mod_lt, length_pos_of_ne_nil hn, getElem?_eq_getElem, Option.some_inj,
    hl.getElem_inj_iff, Fin.ext_iff] using congr_arg head? h

/--
theorem `Nodup.rotate_congr_iff` / 定理 `Nodup.rotate_congr_iff`

English:
theorem Nodup.rotate_congr_iff
  given: {l : List α} (hl : l.Nodup) {i j : Nat}
  proof: by
  rcases eq_or_ne l [] with rfl | hn
  · simp
  · simp only [hn, or_false]
    refine ⟨hl.rotate_congr hn _ _, fun h => ?_⟩
    rw [← rotate_mod]; rw [h]; rw [rotate_mod]

中文:
定理 Nodup.rotate_congr_iff
  条件: {l : 列表 α} (hl : l.Nodup) {i j : 自然数}
  证明: by
  rcases eq_or_ne l [] with rfl | hn
  · simp
  · simp only [hn, or_false]
    refine ⟨hl.rotate_congr hn _ _, fun h => ?_⟩
    rw [← rotate_mod]; rw [h]; rw [rotate_mod]

Depends on / 依赖: eq_or_ne, hl.rotate_congr, or_false, rotate_congr, rotate_mod
-/
theorem Nodup.rotate_congr_iff {l : List α} (hl : l.Nodup) {i j : Nat} :
    l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = [] := by
  rcases eq_or_ne l [] with rfl | hn
  · simp
  · simp only [hn, or_false]
    refine ⟨hl.rotate_congr hn _ _, fun h => ?_⟩
    rw [← rotate_mod]; rw [h]; rw [rotate_mod]

/--
theorem `Nodup.rotate_eq_self_iff` / 定理 `Nodup.rotate_eq_self_iff`

English:
theorem Nodup.rotate_eq_self_iff
  given: {l : List α} (hl : l.Nodup) {n : Nat}
  proof: by
  rw [← zero_mod]; rw [← hl.rotate_congr_iff]; rw [rotate_zero]

中文:
定理 Nodup.rotate_eq_self_iff
  条件: {l : 列表 α} (hl : l.Nodup) {n : 自然数}
  证明: by
  rw [← zero_mod]; rw [← hl.rotate_congr_iff]; rw [rotate_zero]

Depends on / 依赖: hl.rotate_congr_iff, rotate_congr_iff, rotate_zero, zero_mod
-/
theorem Nodup.rotate_eq_self_iff {l : List α} (hl : l.Nodup) {n : Nat} :
    l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := by
  rw [← zero_mod]; rw [← hl.rotate_congr_iff]; rw [rotate_zero]

section IsRotated

variable (l l' : List α)

/--
Definition of `IsRotated` / `IsRotated` 的定义

English:
definition IsRotated
  signature: : Prop
  body: exists n, l.rotate n = l'

@[inherit_doc List.IsRotated]

中文:
定义 IsRotated
  签名: : 命题
  定义体: exists n, l.rotate n = l'

@[inherit_doc List.IsRotated]

Depends on / 依赖: l.rotate, rotate
-/
def IsRotated : Prop :=
  exists n, l.rotate n = l'

@[inherit_doc List.IsRotated]
-- This matches the precedence of the infix `~` for `List.Perm`, and of other relation infixes
infixr:50 " ~r " => IsRotated

variable {l l'} {a : α}

@[refl]
/--
theorem `IsRotated.refl` / 定理 `IsRotated.refl`

English:
theorem IsRotated.refl
  given: (l : List α)
  statement: l ~r l
  proof: ⟨0, by simp⟩

@[symm]

中文:
定理 IsRotated.refl
  条件: (l : 列表 α)
  结论: l ~r l
  证明: ⟨0, by simp⟩

@[symm]
-/
theorem IsRotated.refl (l : List α) : l ~r l :=
  ⟨0, by simp⟩

@[symm]
/--
theorem `IsRotated.symm` / 定理 `IsRotated.symm`

English:
theorem IsRotated.symm
  given: (h : l ~r l')
  statement: l' ~r l
  proof: by
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate]; rw [Nat.add_sub_cancel']; rw [rotate_length_mul]
    exact Nat.le_mul_of_pos_left _ (by simp)

中文:
定理 IsRotated.symm
  条件: (h : l ~r l')
  结论: l' ~r l
  证明: by
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate]; rw [Nat.add_sub_cancel']; rw [rotate_length_mul]
    exact Nat.le_mul_of_pos_left _ (by simp)

Depends on / 依赖: Nat.add_sub_cancel, Nat.le_mul_of_pos_left, add_sub_cancel, le_mul_of_pos_left, length, rotate_length_mul, rotate_rotate
-/
theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · exists 0
  · use (hd :: tl).length * n - n
    rw [rotate_rotate]; rw [Nat.add_sub_cancel']; rw [rotate_length_mul]
    exact Nat.le_mul_of_pos_left _ (by simp)

/--
theorem `isRotated_comm` / 定理 `isRotated_comm`

English:
theorem isRotated_comm
  statement: l ~r l' ↔ l' ~r l
  proof: ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]

中文:
定理 isRotated_comm
  结论: l ~r l' ↔ l' ~r l
  证明: ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]

Depends on / 依赖: IsRotated, IsRotated.symm
-/
theorem isRotated_comm : l ~r l' ↔ l' ~r l :=
  ⟨IsRotated.symm, IsRotated.symm⟩

@[simp]
/--
theorem `IsRotated.forall` / 定理 `IsRotated.forall`

English:
theorem IsRotated.forall
  given: (l : List α) (n : Nat)
  statement: l.rotate n ~r l
  proof: IsRotated.symm ⟨n, rfl⟩

@[trans]

中文:
定理 IsRotated.对任意
  条件: (l : 列表 α) (n : 自然数)
  结论: l.rotate n ~r l
  证明: IsRotated.symm ⟨n, rfl⟩

@[trans]
-/
protected theorem IsRotated.forall (l : List α) (n : Nat) : l.rotate n ~r l :=
  IsRotated.symm ⟨n, rfl⟩

@[trans]
/--
theorem `IsRotated.trans` / 定理 `IsRotated.trans`

English:
theorem IsRotated.trans
  statement: forall {l l' l'' : List α}, l ~r l' -> l' ~r l'' -> l ~r l''

中文:
定理 IsRotated.trans
  结论: 对任意 {l l' l'' : 列表 α}, l ~r l' -> l' ~r l'' -> l ~r l''
-/
theorem IsRotated.trans : forall {l l' l'' : List α}, l ~r l' -> l' ~r l'' -> l ~r l''
  | _, _, _, ⟨n, rfl⟩, ⟨m, rfl⟩ => ⟨n + m, by rw [rotate_rotate]⟩

/--
theorem `IsRotated.eqv` / 定理 `IsRotated.eqv`

English:
theorem IsRotated.eqv
  statement: Equivalence (@IsRotated α)
  proof: Equivalence.mk IsRotated.refl IsRotated.symm IsRotated.trans

中文:
定理 IsRotated.eqv
  结论: 等价 (@IsRotated α)
  证明: Equivalence.mk IsRotated.refl IsRotated.symm IsRotated.trans

Depends on / 依赖: Equivalence, Equivalence.mk, IsRotated, IsRotated.refl, IsRotated.symm, IsRotated.trans
-/
theorem IsRotated.eqv : Equivalence (@IsRotated α) :=
  Equivalence.mk IsRotated.refl IsRotated.symm IsRotated.trans

/-- The relation `List.IsRotated l l'` forms a `Setoid` of cycles. -/
@[instance_reducible]
/--
Definition of `IsRotated.setoid` / `IsRotated.setoid` 的定义

English:
definition IsRotated.setoid
  signature: (α : Type*)
  body: IsRotated
  iseqv := IsRotated.eqv

中文:
定义 IsRotated.setoid
  签名: (α : 类型)
  定义体: IsRotated
  iseqv := IsRotated.eqv

Depends on / 依赖: IsRotated
-/
def IsRotated.setoid (α : Type*) : Setoid (List α) where
  r := IsRotated
  iseqv := IsRotated.eqv

/--
theorem `IsRotated.perm` / 定理 `IsRotated.perm`

English:
theorem IsRotated.perm
  given: (h : l ~r l')
  statement: l ~ l'
  proof: Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

中文:
定理 IsRotated.perm
  条件: (h : l ~r l')
  结论: l ~ l'
  证明: Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

Depends on / 依赖: Exists, Exists.elim, rotate_perm
-/
theorem IsRotated.perm (h : l ~r l') : l ~ l' :=
  Exists.elim h fun _ hl => hl ▸ (rotate_perm _ _).symm

/--
theorem `IsRotated.nodup_iff` / 定理 `IsRotated.nodup_iff`

English:
theorem IsRotated.nodup_iff
  given: (h : l ~r l')
  statement: Nodup l ↔ Nodup l'
  proof: h.perm.nodup_iff

中文:
定理 IsRotated.nodup_iff
  条件: (h : l ~r l')
  结论: Nodup l ↔ Nodup l'
  证明: h.perm.nodup_iff

Depends on / 依赖: h.perm.nodup_iff, nodup_iff
-/
theorem IsRotated.nodup_iff (h : l ~r l') : Nodup l ↔ Nodup l' :=
  h.perm.nodup_iff

/--
theorem `IsRotated.mem_iff` / 定理 `IsRotated.mem_iff`

English:
theorem IsRotated.mem_iff
  given: (h : l ~r l') {a : α}
  statement: a in l ↔ a in l'
  proof: h.perm.mem_iff

@[simp]

中文:
定理 IsRotated.mem_iff
  条件: (h : l ~r l') {a : α}
  结论: a in l ↔ a in l'
  证明: h.perm.mem_iff

@[simp]

Depends on / 依赖: h.perm.mem_iff, mem_iff
-/
theorem IsRotated.mem_iff (h : l ~r l') {a : α} : a in l ↔ a in l' :=
  h.perm.mem_iff

@[simp]
/--
theorem `isRotated_nil_iff` / 定理 `isRotated_nil_iff`

English:
theorem isRotated_nil_iff
  statement: l ~r [] ↔ l = []
  proof: ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]

中文:
定理 isRotated_nil_iff
  结论: l ~r [] ↔ l = []
  证明: ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
-/
theorem isRotated_nil_iff : l ~r [] ↔ l = [] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
/--
theorem `isRotated_nil_iff'` / 定理 `isRotated_nil_iff'`

English:
theorem isRotated_nil_iff'
  statement: [] ~r l ↔ [] = l
  proof: by
  rw [isRotated_comm]; rw [isRotated_nil_iff]; rw [eq_comm]

@[simp]

中文:
定理 isRotated_nil_iff'
  结论: [] ~r l ↔ [] = l
  证明: by
  rw [isRotated_comm]; rw [isRotated_nil_iff]; rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, isRotated_comm, isRotated_nil_iff
-/
theorem isRotated_nil_iff' : [] ~r l ↔ [] = l := by
  rw [isRotated_comm]; rw [isRotated_nil_iff]; rw [eq_comm]

@[simp]
/--
theorem `isRotated_singleton_iff` / 定理 `isRotated_singleton_iff`

English:
theorem isRotated_singleton_iff
  given: {x : α}
  statement: l ~r [x] ↔ l = [x]
  proof: ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]

中文:
定理 isRotated_singleton_iff
  条件: {x : α}
  结论: l ~r [x] ↔ l = [x]
  证明: ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
-/
theorem isRotated_singleton_iff {x : α} : l ~r [x] ↔ l = [x] :=
  ⟨fun ⟨n, hn⟩ => by simpa using hn, fun h => h ▸ by rfl⟩

@[simp]
/--
theorem `isRotated_singleton_iff'` / 定理 `isRotated_singleton_iff'`

English:
theorem isRotated_singleton_iff'
  given: {x : α}
  statement: [x] ~r l ↔ [x] = l
  proof: by
  rw [isRotated_comm]; rw [isRotated_singleton_iff]; rw [eq_comm]

中文:
定理 isRotated_singleton_iff'
  条件: {x : α}
  结论: [x] ~r l ↔ [x] = l
  证明: by
  rw [isRotated_comm]; rw [isRotated_singleton_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, isRotated_comm, isRotated_singleton_iff
-/
theorem isRotated_singleton_iff' {x : α} : [x] ~r l ↔ [x] = l := by
  rw [isRotated_comm]; rw [isRotated_singleton_iff]; rw [eq_comm]

/--
theorem `isRotated_concat` / 定理 `isRotated_concat`

English:
theorem isRotated_concat
  given: (hd : α) (tl : List α)
  statement: (tl ++ [hd]) ~r (hd :: tl)
  proof: IsRotated.symm ⟨1, by simp⟩

中文:
定理 isRotated_concat
  条件: (hd : α) (tl : 列表 α)
  结论: (tl ++ [hd]) ~r (hd :: tl)
  证明: IsRotated.symm ⟨1, by simp⟩

Depends on / 依赖: IsRotated, IsRotated.symm
-/
theorem isRotated_concat (hd : α) (tl : List α) : (tl ++ [hd]) ~r (hd :: tl) :=
  IsRotated.symm ⟨1, by simp⟩

/--
theorem `isRotated_append` / 定理 `isRotated_append`

English:
theorem isRotated_append
  statement: (l ++ l') ~r (l' ++ l)
  proof: ⟨l.length, by simp⟩

中文:
定理 isRotated_append
  结论: (l ++ l') ~r (l' ++ l)
  证明: ⟨l.length, by simp⟩

Depends on / 依赖: l.length, length
-/
theorem isRotated_append : (l ++ l') ~r (l' ++ l) :=
  ⟨l.length, by simp⟩

/--
theorem `IsRotated.reverse` / 定理 `IsRotated.reverse`

English:
theorem IsRotated.reverse
  given: (h : l ~r l')
  statement: l.reverse ~r l'.reverse
  proof: by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩

中文:
定理 IsRotated.reverse
  条件: (h : l ~r l')
  结论: l.reverse ~r l'.reverse
  证明: by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩

Depends on / 依赖: reverse_rotate
-/
theorem IsRotated.reverse (h : l ~r l') : l.reverse ~r l'.reverse := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨_, (reverse_rotate _ _).symm⟩

/--
theorem `isRotated_reverse_comm_iff` / 定理 `isRotated_reverse_comm_iff`

English:
theorem isRotated_reverse_comm_iff
  statement: l.reverse ~r l' ↔ l ~r l'.reverse
  proof: by
  constructor <;>
    · intro h
      simpa using h.reverse

@[simp]

中文:
定理 isRotated_reverse_comm_iff
  结论: l.reverse ~r l' ↔ l ~r l'.reverse
  证明: by
  constructor <;>
    · intro h
      simpa using h.reverse

@[simp]

Depends on / 依赖: h.reverse, reverse
-/
theorem isRotated_reverse_comm_iff : l.reverse ~r l' ↔ l ~r l'.reverse := by
  constructor <;>
    · intro h
      simpa using h.reverse

@[simp]
/--
theorem `isRotated_reverse_iff` / 定理 `isRotated_reverse_iff`

English:
theorem isRotated_reverse_iff
  statement: l.reverse ~r l'.reverse ↔ l ~r l'
  proof: by
  simp [isRotated_reverse_comm_iff]

中文:
定理 isRotated_reverse_iff
  结论: l.reverse ~r l'.reverse ↔ l ~r l'
  证明: by
  simp [isRotated_reverse_comm_iff]

Depends on / 依赖: isRotated_reverse_comm_iff
-/
theorem isRotated_reverse_iff : l.reverse ~r l'.reverse ↔ l ~r l' := by
  simp [isRotated_reverse_comm_iff]

/--
theorem `isRotated_iff_mod` / 定理 `isRotated_iff_mod`

English:
theorem isRotated_iff_mod
  statement: l ~r l' ↔ exists n <= l.length, l.rotate n = l'
  proof: by
  refine ⟨fun h => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · simp
  · refine ⟨n % (hd :: tl).length, ?_, rotate_mod _ _⟩
    refine (Nat.mod_lt _ ?_).le
    simp

中文:
定理 isRotated_iff_mod
  结论: l ~r l' ↔ 存在 n <= l.length, l.rotate n = l'
  证明: by
  refine ⟨fun h => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · simp
  · refine ⟨n % (hd :: tl).length, ?_, rotate_mod _ _⟩
    refine (Nat.mod_lt _ ?_).le
    simp

Depends on / 依赖: Nat.mod_lt, length, mod_lt, rotate_mod
-/
theorem isRotated_iff_mod : l ~r l' ↔ exists n <= l.length, l.rotate n = l' := by
  refine ⟨fun h => ?_, fun ⟨n, _, h⟩ => ⟨n, h⟩⟩
  obtain ⟨n, rfl⟩ := h
  rcases l with - | ⟨hd, tl⟩
  · simp
  · refine ⟨n % (hd :: tl).length, ?_, rotate_mod _ _⟩
    refine (Nat.mod_lt _ ?_).le
    simp

/--
theorem `isRotated_iff_mem_map_range` / 定理 `isRotated_iff_mem_map_range`

English:
theorem isRotated_iff_mem_map_range
  statement: l ~r l' ↔ l' in (List.range (l.length + 1)).map l.rotate
  proof: by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩

中文:
定理 isRotated_iff_mem_map_range
  结论: l ~r l' ↔ l' in (列表.range (l.length + 1)).map l.rotate
  证明: by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩

Depends on / 依赖: Nat.le_of_lt_succ, Nat.lt_succ_of_le, isRotated_iff_mod, le_of_lt_succ, lt_succ_of_le, mem_map, mem_range, simp_rw
-/
theorem isRotated_iff_mem_map_range : l ~r l' ↔ l' in (List.range (l.length + 1)).map l.rotate := by
  simp_rw [mem_map, mem_range, isRotated_iff_mod]
  exact
    ⟨fun ⟨n, hn, h⟩ => ⟨n, Nat.lt_succ_of_le hn, h⟩,
      fun ⟨n, hn, h⟩ => ⟨n, Nat.le_of_lt_succ hn, h⟩⟩

/--
theorem `IsRotated.map` / 定理 `IsRotated.map`

English:
theorem IsRotated.map
  given: {β : Type*} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α -> β)
  proof: by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

中文:
定理 IsRotated.map
  条件: {β : 类型} {l₁ l₂ : 列表 α} (h : l₁ ~r l₂) (f : α -> β)
  证明: by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

Depends on / 依赖: map_rotate
-/
theorem IsRotated.map {β : Type*} {l₁ l₂ : List α} (h : l₁ ~r l₂) (f : α -> β) :
    map f l₁ ~r map f l₂ := by
  obtain ⟨n, rfl⟩ := h
  rw [map_rotate]
  use n

/--
lemma `IsRotated.cons_append_singleton` / 引理 `IsRotated.cons_append_singleton`

English:
lemma IsRotated.cons_append_singleton
  statement: a :: l ~r l ++ [a]
  proof: by
  simpa using isRotated_append (l := [a])

中文:
引理 IsRotated.cons_append_singleton
  结论: a :: l ~r l ++ [a]
  证明: by
  simpa using isRotated_append (l := [a])

Depends on / 依赖: isRotated_append
-/
lemma IsRotated.cons_append_singleton : a :: l ~r l ++ [a] := by
  simpa using isRotated_append (l := [a])

/--
theorem `IsRotated.cons_getLast_dropLast` / 定理 `IsRotated.cons_getLast_dropLast`

English:
theorem IsRotated.cons_getLast_dropLast
  proof: by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp only [getLast_append, dropLast_concat]
    apply IsRotated.symm
    apply isRotated_concat

中文:
定理 IsRotated.cons_getLast_dropLast
  证明: by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp only [getLast_append, dropLast_concat]
    apply IsRotated.symm
    apply isRotated_concat

Depends on / 依赖: IsRotated, IsRotated.symm, List.reverseRecOn, append_singleton, dropLast_concat, getLast_append, isRotated_concat, reverseRecOn
-/
theorem IsRotated.cons_getLast_dropLast
    (L : List α) (hL : L != []) : L.getLast hL :: L.dropLast ~r L := by
  induction L using List.reverseRecOn with
  | nil => simp at hL
  | append_singleton a L _ =>
    simp only [getLast_append, dropLast_concat]
    apply IsRotated.symm
    apply isRotated_concat

/--
theorem `IsRotated.dropLast_tail` / 定理 `IsRotated.dropLast_tail`

English:
theorem IsRotated.dropLast_tail
  statement: {α}
  proof: match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by
    simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons] at hL'
    simp [hL', IsRotated.cons_getLast_dropLast]

中文:
定理 IsRotated.dropLast_tail
  结论: {α}
  证明: match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by
    simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons] at hL'
    simp [hL', IsRotated.cons_getLast_dropLast]

Depends on / 依赖: IsRotated, IsRotated.cons_getLast_dropLast, cons_getLast_dropLast, getLast_cons, head_cons, ne_eq, not_false_eq_true, reduceCtorEq
-/
theorem IsRotated.dropLast_tail {α}
    {L : List α} (hL : L != []) (hL' : L.head hL = L.getLast hL) : L.dropLast ~r L.tail :=
  match L with
  | [] => by simp
  | [_] => by simp
  | a :: b :: L => by
    simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons] at hL'
    simp [hL', IsRotated.cons_getLast_dropLast]

/--
Definition of `cyclicPermutations` / `cyclicPermutations` 的定义

English:
definition cyclicPermutations
  signature: : List α -> List (List α)

中文:
定义 cyclicPermutations
  签名: : 列表 α -> 列表 (列表 α)
-/
def cyclicPermutations : List α -> List (List α)
  | [] => [[]]
  | l@(_ :: _) => dropLast (zipWith (· ++ ·) (tails l) (inits l))

@[simp]
/--
theorem `cyclicPermutations_nil` / 定理 `cyclicPermutations_nil`

English:
theorem cyclicPermutations_nil
  statement: cyclicPermutations ([] : List α) = [[]]
  proof: rfl

中文:
定理 cyclicPermutations_nil
  结论: cyclicPermutations ([] : 列表 α) = [[]]
  证明: rfl
-/
theorem cyclicPermutations_nil : cyclicPermutations ([] : List α) = [[]] :=
  rfl

/--
theorem `cyclicPermutations_cons` / 定理 `cyclicPermutations_cons`

English:
theorem cyclicPermutations_cons
  given: (x : α) (l : List α)
  proof: rfl

中文:
定理 cyclicPermutations_cons
  条件: (x : α) (l : 列表 α)
  证明: rfl
-/
theorem cyclicPermutations_cons (x : α) (l : List α) :
    cyclicPermutations (x :: l) = dropLast (zipWith (· ++ ·) (tails (x :: l)) (inits (x :: l))) :=
  rfl

/--
theorem `cyclicPermutations_of_ne_nil` / 定理 `cyclicPermutations_of_ne_nil`

English:
theorem cyclicPermutations_of_ne_nil
  given: (l : List α) (h : l != [])
  proof: by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclicPermutations_cons _ _

中文:
定理 cyclicPermutations_of_ne_nil
  条件: (l : 列表 α) (h : l != [])
  证明: by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclicPermutations_cons _ _

Depends on / 依赖: cyclicPermutations_cons, exists_cons_of_ne_nil
-/
theorem cyclicPermutations_of_ne_nil (l : List α) (h : l != []) :
    cyclicPermutations l = dropLast (zipWith (· ++ ·) (tails l) (inits l)) := by
  obtain ⟨hd, tl, rfl⟩ := exists_cons_of_ne_nil h
  exact cyclicPermutations_cons _ _

/--
theorem `length_cyclicPermutations_cons` / 定理 `length_cyclicPermutations_cons`

English:
theorem length_cyclicPermutations_cons
  given: (x : α) (l : List α)
  proof: by simp [cyclicPermutations_cons]

@[simp]

中文:
定理 length_cyclicPermutations_cons
  条件: (x : α) (l : 列表 α)
  证明: by simp [cyclicPermutations_cons]

@[simp]

Depends on / 依赖: cyclicPermutations_cons
-/
theorem length_cyclicPermutations_cons (x : α) (l : List α) :
    length (cyclicPermutations (x :: l)) = length l + 1 := by simp [cyclicPermutations_cons]

@[simp]
/--
theorem `length_cyclicPermutations_of_ne_nil` / 定理 `length_cyclicPermutations_of_ne_nil`

English:
theorem length_cyclicPermutations_of_ne_nil
  given: (l : List α) (h : l != [])
  proof: by simp [cyclicPermutations_of_ne_nil _ h]

@[simp]

中文:
定理 length_cyclicPermutations_of_ne_nil
  条件: (l : 列表 α) (h : l != [])
  证明: by simp [cyclicPermutations_of_ne_nil _ h]

@[simp]

Depends on / 依赖: cyclicPermutations_of_ne_nil
-/
theorem length_cyclicPermutations_of_ne_nil (l : List α) (h : l != []) :
    length (cyclicPermutations l) = length l := by simp [cyclicPermutations_of_ne_nil _ h]

@[simp]
/--
theorem `cyclicPermutations_ne_nil` / 定理 `cyclicPermutations_ne_nil`

English:
theorem cyclicPermutations_ne_nil
  statement: forall l : List α, cyclicPermutations l != []

中文:
定理 cyclicPermutations_ne_nil
  结论: 对任意 l : 列表 α, cyclicPermutations l != []
-/
theorem cyclicPermutations_ne_nil : forall l : List α, cyclicPermutations l != []
  | a::l, h => by simpa using congr_arg length h

@[simp]
/--
theorem `getElem_cyclicPermutations` / 定理 `getElem_cyclicPermutations`

English:
theorem getElem_cyclicPermutations
  given: (l : List α) (n : Nat) (h : n < length (cyclicPermutations l))
  proof: by
  cases l with
  | nil => simp
  | cons a l =>
    simp only [cyclicPermutations_cons, getElem_dropLast, getElem_zipWith, getElem_tails,
      getElem_inits]
    rw [rotate_eq_drop_append_take (by simpa using h.le)]

中文:
定理 getElem_cyclicPermutations
  条件: (l : 列表 α) (n : 自然数) (h : n < length (cyclicPermutations l))
  证明: by
  cases l with
  | nil => simp
  | cons a l =>
    simp only [cyclicPermutations_cons, getElem_dropLast, getElem_zipWith, getElem_tails,
      getElem_inits]
    rw [rotate_eq_drop_append_take (by simpa using h.le)]

Depends on / 依赖: cyclicPermutations_cons, getElem_dropLast, getElem_inits, getElem_tails, getElem_zipWith, h.le, rotate_eq_drop_append_take
-/
theorem getElem_cyclicPermutations (l : List α) (n : Nat) (h : n < length (cyclicPermutations l)) :
    (cyclicPermutations l)[n] = l.rotate n := by
  cases l with
  | nil => simp
  | cons a l =>
    simp only [cyclicPermutations_cons, getElem_dropLast, getElem_zipWith, getElem_tails,
      getElem_inits]
    rw [rotate_eq_drop_append_take (by simpa using h.le)]

/--
theorem `get_cyclicPermutations` / 定理 `get_cyclicPermutations`

English:
theorem get_cyclicPermutations
  given: (l : List α) (n : Fin (length (cyclicPermutations l)))
  proof: by
  simp

@[simp]

中文:
定理 get_cyclicPermutations
  条件: (l : 列表 α) (n : 有限集 (length (cyclicPermutations l)))
  证明: by
  simp

@[simp]
-/
theorem get_cyclicPermutations (l : List α) (n : Fin (length (cyclicPermutations l))) :
    (cyclicPermutations l).get n = l.rotate n := by
  simp

@[simp]
/--
theorem `head_cyclicPermutations` / 定理 `head_cyclicPermutations`

English:
theorem head_cyclicPermutations
  given: (l : List α)
  proof: by
  have h : 0 < length (cyclicPermutations l) := length_pos_of_ne_nil (cyclicPermutations_ne_nil _)
  rw [← get_mk_zero h]; rw [get_cyclicPermutations]; rw [Fin.val_mk]; rw [rotate_zero]

@[simp]

中文:
定理 head_cyclicPermutations
  条件: (l : 列表 α)
  证明: by
  have h : 0 < length (cyclicPermutations l) := length_pos_of_ne_nil (cyclicPermutations_ne_nil _)
  rw [← get_mk_zero h]; rw [get_cyclicPermutations]; rw [Fin.val_mk]; rw [rotate_zero]

@[simp]

Depends on / 依赖: Fin.val_mk, cyclicPermutations, cyclicPermutations_ne_nil, get_cyclicPermutations, get_mk_zero, length, length_pos_of_ne_nil, rotate_zero, val_mk
-/
theorem head_cyclicPermutations (l : List α) :
    (cyclicPermutations l).head (cyclicPermutations_ne_nil l) = l := by
  have h : 0 < length (cyclicPermutations l) := length_pos_of_ne_nil (cyclicPermutations_ne_nil _)
  rw [← get_mk_zero h]; rw [get_cyclicPermutations]; rw [Fin.val_mk]; rw [rotate_zero]

@[simp]
/--
theorem `head?_cyclicPermutations` / 定理 `head?_cyclicPermutations`

English:
theorem head?_cyclicPermutations
  given: (l : List α)
  statement: (cyclicPermutations l).head? = l
  proof: by
  rw [head?_eq_some_head (cyclicPermutations_ne_nil l)]; rw [head_cyclicPermutations]

中文:
定理 head?_cyclicPermutations
  条件: (l : 列表 α)
  结论: (cyclicPermutations l).head? = l
  证明: by
  rw [head?_eq_some_head (cyclicPermutations_ne_nil l)]; rw [head_cyclicPermutations]
-/
theorem head?_cyclicPermutations (l : List α) : (cyclicPermutations l).head? = l := by
  rw [head?_eq_some_head (cyclicPermutations_ne_nil l)]; rw [head_cyclicPermutations]

/--
theorem `cyclicPermutations_injective` / 定理 `cyclicPermutations_injective`

English:
theorem cyclicPermutations_injective
  statement: Function.Injective (@cyclicPermutations α)
  proof: fun l l' h => by
  simpa using congr_arg head? h

@[simp]

中文:
定理 cyclicPermutations_injective
  结论: 函数.单射 (@cyclicPermutations α)
  证明: fun l l' h => by
  simpa using congr_arg head? h

@[simp]

Depends on / 依赖: congr_arg
-/
theorem cyclicPermutations_injective : Function.Injective (@cyclicPermutations α) := fun l l' h => by
  simpa using congr_arg head? h

@[simp]
/--
theorem `cyclicPermutations_inj` / 定理 `cyclicPermutations_inj`

English:
theorem cyclicPermutations_inj
  given: {l l' : List α}
  proof: cyclicPermutations_injective.eq_iff

中文:
定理 cyclicPermutations_inj
  条件: {l l' : 列表 α}
  证明: cyclicPermutations_injective.eq_iff

Depends on / 依赖: cyclicPermutations_injective, cyclicPermutations_injective.eq_iff, eq_iff
-/
theorem cyclicPermutations_inj {l l' : List α} :
    cyclicPermutations l = cyclicPermutations l' ↔ l = l' :=
  cyclicPermutations_injective.eq_iff

/--
theorem `length_mem_cyclicPermutations` / 定理 `length_mem_cyclicPermutations`

English:
theorem length_mem_cyclicPermutations
  given: (l : List α) (h : l' in cyclicPermutations l)
  proof: by
  obtain ⟨k, hk, rfl⟩ := get_of_mem h
  simp

中文:
定理 length_mem_cyclicPermutations
  条件: (l : 列表 α) (h : l' in cyclicPermutations l)
  证明: by
  obtain ⟨k, hk, rfl⟩ := get_of_mem h
  simp

Depends on / 依赖: get_of_mem
-/
theorem length_mem_cyclicPermutations (l : List α) (h : l' in cyclicPermutations l) :
    length l' = length l := by
  obtain ⟨k, hk, rfl⟩ := get_of_mem h
  simp

/--
theorem `mem_cyclicPermutations_self` / 定理 `mem_cyclicPermutations_self`

English:
theorem mem_cyclicPermutations_self
  given: (l : List α)
  statement: l in cyclicPermutations l
  proof: by
  simpa using head_mem (cyclicPermutations_ne_nil l)

@[simp]

中文:
定理 mem_cyclicPermutations_self
  条件: (l : 列表 α)
  结论: l in cyclicPermutations l
  证明: by
  simpa using head_mem (cyclicPermutations_ne_nil l)

@[simp]

Depends on / 依赖: cyclicPermutations_ne_nil, head_mem
-/
theorem mem_cyclicPermutations_self (l : List α) : l in cyclicPermutations l := by
  simpa using head_mem (cyclicPermutations_ne_nil l)

@[simp]
/--
theorem `cyclicPermutations_rotate` / 定理 `cyclicPermutations_rotate`

English:
theorem cyclicPermutations_rotate
  given: (l : List α) (k : Nat)
  proof: by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine ext_get this fun n hn hn' => ?_
  rw [get_rotate]; rw [get_cyclicPermutations]; rw [rotate_rotate]; rw [← rotate_m

中文:
定理 cyclicPermutations_rotate
  条件: (l : 列表 α) (k : 自然数)
  证明: by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine ext_get this fun n hn hn' => ?_
  rw [get_rotate]; rw [get_cyclicPermutations]; rw [rotate_rotate]; rw [← rotate_m

Depends on / 依赖: Nat.add_comm, add_comm, cyclicPermutations, cyclicPermutations.length, ext_get, get_cyclicPermutations, get_rotate, l.cyclicPermutations.rotate, l.rotate, length, length_cyclicPermutations_of_ne_nil, rotate, rotate_mod, rotate_rotate
-/
theorem cyclicPermutations_rotate (l : List α) (k : Nat) :
    (l.rotate k).cyclicPermutations = l.cyclicPermutations.rotate k := by
  have : (l.rotate k).cyclicPermutations.length = length (l.cyclicPermutations.rotate k) := by
    cases l
    · simp
    · rw [length_cyclicPermutations_of_ne_nil] <;> simp
  refine ext_get this fun n hn hn' => ?_
  rw [get_rotate]; rw [get_cyclicPermutations]; rw [rotate_rotate]; rw [← rotate_mod]; rw [Nat.add_comm]
  cases l <;> simp

@[simp]
/--
theorem `mem_cyclicPermutations_iff` / 定理 `mem_cyclicPermutations_iff`

English:
theorem mem_cyclicPermutations_iff
  statement: l in cyclicPermutations l' ↔ l ~r l'
  proof: by
  constructor
  · simp_rw [mem_iff_get, get_cyclicPermutations]
    rintro ⟨k, rfl⟩
    exact .forall _ _
  · rintro ⟨k, rfl⟩
    rw [cyclicPermutations_rotate]; rw [mem_rotate]
    apply mem_cyclicPermutations_self

@[simp]

中文:
定理 mem_cyclicPermutations_iff
  结论: l in cyclicPermutations l' ↔ l ~r l'
  证明: by
  constructor
  · simp_rw [mem_iff_get, get_cyclicPermutations]
    rintro ⟨k, rfl⟩
    exact .forall _ _
  · rintro ⟨k, rfl⟩
    rw [cyclicPermutations_rotate]; rw [mem_rotate]
    apply mem_cyclicPermutations_self

@[simp]

Depends on / 依赖: cyclicPermutations_rotate, get_cyclicPermutations, mem_cyclicPermutations_self, mem_iff_get, mem_rotate, simp_rw
-/
theorem mem_cyclicPermutations_iff : l in cyclicPermutations l' ↔ l ~r l' := by
  constructor
  · simp_rw [mem_iff_get, get_cyclicPermutations]
    rintro ⟨k, rfl⟩
    exact .forall _ _
  · rintro ⟨k, rfl⟩
    rw [cyclicPermutations_rotate]; rw [mem_rotate]
    apply mem_cyclicPermutations_self

@[simp]
/--
theorem `cyclicPermutations_eq_nil_iff` / 定理 `cyclicPermutations_eq_nil_iff`

English:
theorem cyclicPermutations_eq_nil_iff
  given: {l : List α}
  statement: cyclicPermutations l = [[]] ↔ l = []
  proof: cyclicPermutations_injective.eq_iff' rfl

@[simp]

中文:
定理 cyclicPermutations_eq_nil_iff
  条件: {l : 列表 α}
  结论: cyclicPermutations l = [[]] ↔ l = []
  证明: cyclicPermutations_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: cyclicPermutations_injective, cyclicPermutations_injective.eq_iff, eq_iff
-/
theorem cyclicPermutations_eq_nil_iff {l : List α} : cyclicPermutations l = [[]] ↔ l = [] :=
  cyclicPermutations_injective.eq_iff' rfl

@[simp]
/--
theorem `cyclicPermutations_eq_singleton_iff` / 定理 `cyclicPermutations_eq_singleton_iff`

English:
theorem cyclicPermutations_eq_singleton_iff
  given: {l : List α} {x : α}
  proof: cyclicPermutations_injective.eq_iff' rfl

中文:
定理 cyclicPermutations_eq_singleton_iff
  条件: {l : 列表 α} {x : α}
  证明: cyclicPermutations_injective.eq_iff' rfl

Depends on / 依赖: cyclicPermutations_injective, cyclicPermutations_injective.eq_iff, eq_iff
-/
theorem cyclicPermutations_eq_singleton_iff {l : List α} {x : α} :
    cyclicPermutations l = [[x]] ↔ l = [x] :=
  cyclicPermutations_injective.eq_iff' rfl

/--
theorem `Nodup.cyclicPermutations` / 定理 `Nodup.cyclicPermutations`

English:
theorem Nodup.cyclicPermutations
  given: {l : List α} (hn : Nodup l)
  proof: by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [length_cyclicPermutations_of_ne_nil l hl] at hi hj
    simpa [hn.rotate_congr_iff, mod_eq_of_lt, *] using h

中文:
定理 Nodup.cyclicPermutations
  条件: {l : 列表 α} (hn : Nodup l)
  证明: by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [length_cyclicPermutations_of_ne_nil l hl] at hi hj
    simpa [hn.rotate_congr_iff, mod_eq_of_lt, *] using h
-/
protected theorem Nodup.cyclicPermutations {l : List α} (hn : Nodup l) :
    Nodup (cyclicPermutations l) := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [length_cyclicPermutations_of_ne_nil l hl] at hi hj
    simpa [hn.rotate_congr_iff, mod_eq_of_lt, *] using h

/--
theorem `IsRotated.cyclicPermutations` / 定理 `IsRotated.cyclicPermutations`

English:
theorem IsRotated.cyclicPermutations
  given: {l l' : List α} (h : l ~r l')
  proof: by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

@[simp]

中文:
定理 IsRotated.cyclicPermutations
  条件: {l l' : 列表 α} (h : l ~r l')
  证明: by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

@[simp]
-/
protected theorem IsRotated.cyclicPermutations {l l' : List α} (h : l ~r l') :
    l.cyclicPermutations ~r l'.cyclicPermutations := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by simp⟩

@[simp]
/--
theorem `isRotated_cyclicPermutations_iff` / 定理 `isRotated_cyclicPermutations_iff`

English:
theorem isRotated_cyclicPermutations_iff
  given: {l l' : List α}
  proof: by
  simp only [IsRotated, ← cyclicPermutations_rotate, cyclicPermutations_inj]

中文:
定理 isRotated_cyclicPermutations_iff
  条件: {l l' : 列表 α}
  证明: by
  simp only [IsRotated, ← cyclicPermutations_rotate, cyclicPermutations_inj]

Depends on / 依赖: IsRotated, cyclicPermutations_inj, cyclicPermutations_rotate
-/
theorem isRotated_cyclicPermutations_iff {l l' : List α} :
    l.cyclicPermutations ~r l'.cyclicPermutations ↔ l ~r l' := by
  simp only [IsRotated, ← cyclicPermutations_rotate, cyclicPermutations_inj]

section Decidable

variable [DecidableEq α]

/--
Instance `isRotatedDecidable` / 实例 `isRotatedDecidable`

English:
instance isRotatedDecidable
  signature: (l l' : List α)
  body: decidable_of_iff' _ isRotated_iff_mem_map_range

中文:
实例 isRotatedDecidable
  签名: (l l' : 列表 α)
  定义体: decidable_of_iff' _ isRotated_iff_mem_map_range

Depends on / 依赖: decidable_of_iff, isRotated_iff_mem_map_range
-/
instance isRotatedDecidable (l l' : List α) : Decidable (l ~r l') :=
  decidable_of_iff' _ isRotated_iff_mem_map_range

instance {l l' : List α} : Decidable (IsRotated.setoid α l l') :=
  List.isRotatedDecidable _ _

end Decidable

end IsRotated

end List
