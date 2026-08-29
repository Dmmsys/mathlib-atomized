/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Defs

/-!
# iterate

Proves various lemmas about `List.iterate`.
-/

public section

variable {α : Type*}

namespace List

@[simp]
/--
theorem `length_iterate` / 定理 `length_iterate`

English:
theorem length_iterate
  given: (f : α -> α) (a : α) (n : Nat)
  statement: length (iterate f a n) = n
  proof: by
  induction n generalizing a <;> simp [*]

@[simp]

中文:
定理 length_iterate
  条件: (f : α -> α) (a : α) (n : 自然数)
  结论: length (iterate f a n) = n
  证明: by
  induction n generalizing a <;> simp [*]

@[simp]

Depends on / 依赖: generalizing
-/
theorem length_iterate (f : α -> α) (a : α) (n : Nat) : length (iterate f a n) = n := by
  induction n generalizing a <;> simp [*]

@[simp]
/--
theorem `iterate_eq_nil` / 定理 `iterate_eq_nil`

English:
theorem iterate_eq_nil
  given: {f : α -> α} {a : α} {n : Nat}
  statement: iterate f a n = [] ↔ n = 0
  proof: by
  rw [← length_eq_zero_iff]; rw [length_iterate]

中文:
定理 iterate_eq_nil
  条件: {f : α -> α} {a : α} {n : 自然数}
  结论: iterate f a n = [] ↔ n = 0
  证明: by
  rw [← length_eq_zero_iff]; rw [length_iterate]

Depends on / 依赖: length_eq_zero_iff, length_iterate
-/
theorem iterate_eq_nil {f : α -> α} {a : α} {n : Nat} : iterate f a n = [] ↔ n = 0 := by
  rw [← length_eq_zero_iff]; rw [length_iterate]

/--
theorem `getElem?_iterate` / 定理 `getElem?_iterate`

English:
theorem getElem?_iterate
  given: (f : α -> α) (a : α)

中文:
定理 getElem?_iterate
  条件: (f : α -> α) (a : α)
-/
theorem getElem?_iterate (f : α -> α) (a : α) :
    forall (n i : Nat), i < n -> (iterate f a n)[i]? = f^[i] a
  | n + 1, 0, _ => by simp
  | n + 1, i + 1, h => by simp [getElem?_iterate f (f a) n i (by simpa using h)]

@[simp]
/--
theorem `getElem_iterate` / 定理 `getElem_iterate`

English:
theorem getElem_iterate
  given: (f : α -> α) (a : α) (n : Nat) (i : Nat) (h : i < (iterate f a n).length)
  proof: (getElem_eq_iff _).2 getElem?_iterate _ _ _ _ by rwa [length_iterate] at h

@[simp]

中文:
定理 getElem_iterate
  条件: (f : α -> α) (a : α) (n : 自然数) (i : 自然数) (h : i < (iterate f a n).length)
  证明: (getElem_eq_iff _).2 getElem?_iterate _ _ _ _ by rwa [length_iterate] at h

@[simp]

Depends on / 依赖: _iterate, getElem, getElem_eq_iff, length_iterate
-/
theorem getElem_iterate (f : α -> α) (a : α) (n : Nat) (i : Nat) (h : i < (iterate f a n).length) :
    (iterate f a n)[i] = f^[i] a :=
(getElem_eq_iff _).2 getElem?_iterate _ _ _ _ by rwa [length_iterate] at h

@[simp]
/--
theorem `mem_iterate` / 定理 `mem_iterate`

English:
theorem mem_iterate
  given: {f : α -> α} {a : α} {n : Nat} {b : α}
  proof: by
  simp [List.mem_iff_get, Fin.exists_iff, eq_comm (b := b)]

@[simp]

中文:
定理 mem_iterate
  条件: {f : α -> α} {a : α} {n : 自然数} {b : α}
  证明: by
  simp [List.mem_iff_get, Fin.exists_iff, eq_comm (b := b)]

@[simp]

Depends on / 依赖: Fin.exists_iff, List.mem_iff_get, eq_comm, exists_iff, mem_iff_get
-/
theorem mem_iterate {f : α -> α} {a : α} {n : Nat} {b : α} :
    b in iterate f a n ↔ exists m < n, b = f^[m] a := by
  simp [List.mem_iff_get, Fin.exists_iff, eq_comm (b := b)]

@[simp]
/--
theorem `range_map_iterate` / 定理 `range_map_iterate`

English:
theorem range_map_iterate
  given: (n : Nat) (f : α -> α) (a : α)
  proof: by
  apply List.ext_getElem <;> simp

中文:
定理 range_map_iterate
  条件: (n : 自然数) (f : α -> α) (a : α)
  证明: by
  apply List.ext_getElem <;> simp

Depends on / 依赖: List.ext_getElem, ext_getElem
-/
theorem range_map_iterate (n : Nat) (f : α -> α) (a : α) :
    (List.range n).map (f^[·] a) = List.iterate f a n := by
  apply List.ext_getElem <;> simp

/--
theorem `iterate_add` / 定理 `iterate_add`

English:
theorem iterate_add
  given: (f : α -> α) (a : α) (m n : Nat)
  proof: by
  induction m generalizing a with
  | zero => simp
  | succ n ih => rw [iterate, add_right_comm, iterate, ih, Nat.iterate, cons_append]

中文:
定理 iterate_add
  条件: (f : α -> α) (a : α) (m n : 自然数)
  证明: by
  induction m generalizing a with
  | zero => simp
  | succ n ih => rw [iterate, add_right_comm, iterate, ih, Nat.iterate, cons_append]

Depends on / 依赖: Nat.iterate, add_right_comm, cons_append, generalizing, iterate
-/
theorem iterate_add (f : α -> α) (a : α) (m n : Nat) :
    iterate f a (m + n) = iterate f a m ++ iterate f (f^[m] a) n := by
  induction m generalizing a with
  | zero => simp
  | succ n ih => rw [iterate, add_right_comm, iterate, ih, Nat.iterate, cons_append]

/--
theorem `take_iterate` / 定理 `take_iterate`

English:
theorem take_iterate
  given: (f : α -> α) (a : α) (m n : Nat)
  proof: by
  rw [← range_map_iterate]; rw [← range_map_iterate]; rw [← map_take]; rw [take_range]

中文:
定理 take_iterate
  条件: (f : α -> α) (a : α) (m n : 自然数)
  证明: by
  rw [← range_map_iterate]; rw [← range_map_iterate]; rw [← map_take]; rw [take_range]

Depends on / 依赖: map_take, range_map_iterate, take_range
-/
theorem take_iterate (f : α -> α) (a : α) (m n : Nat) :
    take m (iterate f a n) = iterate f a (min m n) := by
  rw [← range_map_iterate]; rw [← range_map_iterate]; rw [← map_take]; rw [take_range]

end List
