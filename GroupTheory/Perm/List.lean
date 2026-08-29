/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.Support

/-!
# Permutations from a list

A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `List.formPerm` is implemented as a product of `Equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `List.formPerm` definition is meant to primarily be used with `Nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `List.formPerm` to produce a
nontrivial permutation that is noncyclic.
-/

@[expose] public section


namespace List

variable {α β : Type*}

section FormPerm

variable [DecidableEq α] (l : List α)

open Equiv Equiv.Perm

/--
Definition of `formPerm` / `formPerm` 的定义

English:
definition formPerm
  signature: : Equiv.Perm α
  body: (zipWith Equiv.swap l l.tail).prod

@[simp]

中文:
定义 formPerm
  签名: : Equiv.Perm α
  定义体: (zipWith Equiv.swap l l.tail).prod

@[simp]

Depends on / 依赖: Equiv.swap, l.tail, zipWith
-/
def formPerm : Equiv.Perm α :=
  (zipWith Equiv.swap l l.tail).prod

@[simp]
/--
theorem `formPerm_nil` / 定理 `formPerm_nil`

English:
theorem formPerm_nil
  statement: formPerm ([] : List α) = 1
  proof: rfl

@[simp]

中文:
定理 formPerm_nil
  结论: formPerm ([] : List α) = 1
  证明: rfl

@[simp]
-/
theorem formPerm_nil : formPerm ([] : List α) = 1 :=
  rfl

@[simp]
/--
theorem `formPerm_singleton` / 定理 `formPerm_singleton`

English:
theorem formPerm_singleton
  given: (x : α)
  statement: formPerm [x] = 1
  proof: rfl

@[simp]

中文:
定理 formPerm_singleton
  条件: (x : α)
  结论: formPerm [x] = 1
  证明: rfl

@[simp]
-/
theorem formPerm_singleton (x : α) : formPerm [x] = 1 :=
  rfl

@[simp]
/--
theorem `formPerm_cons_cons` / 定理 `formPerm_cons_cons`

English:
theorem formPerm_cons_cons
  given: (x y : α) (l : List α)
  proof: rfl

中文:
定理 formPerm_cons_cons
  条件: (x y : α) (l : List α)
  证明: rfl
-/
theorem formPerm_cons_cons (x y : α) (l : List α) :
    formPerm (x :: y :: l) = Equiv.swap x y * formPerm (y :: l) :=
  rfl

/--
theorem `formPerm_pair` / 定理 `formPerm_pair`

English:
theorem formPerm_pair
  given: (x y : α)
  statement: formPerm [x, y] = Equiv.swap x y
  proof: rfl

中文:
定理 formPerm_pair
  条件: (x y : α)
  结论: formPerm [x, y] = Equiv.swap x y
  证明: rfl
-/
theorem formPerm_pair (x y : α) : formPerm [x, y] = Equiv.swap x y :=
  rfl

/--
theorem `mem_or_mem_of_zipWith_swap_prod_ne` / 定理 `mem_or_mem_of_zipWith_swap_prod_ne`

English:
theorem mem_or_mem_of_zipWith_swap_prod_ne
  statement: forall {l l' : List α} {x : α},

中文:
定理 mem_or_mem_of_zipWith_swap_prod_ne
  结论: 对任意 {l l' : List α} {x : α},
-/
theorem mem_or_mem_of_zipWith_swap_prod_ne : forall {l l' : List α} {x : α},
    (zipWith Equiv.swap l l').prod x != x -> x in l ∨ x in l'
  | [], _, _ => by simp
  | _, [], _ => by simp
  | a::l, b::l', x => fun hx =>
    if h : (zipWith Equiv.swap l l').prod x = x then
      (eq_or_eq_of_swap_apply_ne_self (a := a) (b := b) (x := x) (by simpa [h] using hx)).imp
        (by rintro rfl; exact .head _) (by rintro rfl; exact .head _)
    else
     (mem_or_mem_of_zipWith_swap_prod_ne h).imp (.tail _) (.tail _)

/--
theorem `zipWith_swap_prod_support'` / 定理 `zipWith_swap_prod_support'`

English:
theorem zipWith_swap_prod_support'
  given: (l l' : List α)
  proof: fun _ h => by
  simpa using mem_or_mem_of_zipWith_swap_prod_ne h

中文:
定理 zipWith_swap_prod_support'
  条件: (l l' : List α)
  证明: fun _ h => by
  simpa using mem_or_mem_of_zipWith_swap_prod_ne h

Depends on / 依赖: mem_or_mem_of_zipWith_swap_prod_ne
-/
theorem zipWith_swap_prod_support' (l l' : List α) :
    { x | (zipWith Equiv.swap l l').prod x != x } <= l.toFinset ⊔ l'.toFinset := fun _ h => by
  simpa using mem_or_mem_of_zipWith_swap_prod_ne h

/--
theorem `zipWith_swap_prod_support` / 定理 `zipWith_swap_prod_support`

English:
theorem zipWith_swap_prod_support
  given: [Fintype α] (l l' : List α)
  proof: by
  intro x hx
  have hx' : x in { x | (zipWith Equiv.swap l l').prod x != x } := by simpa using hx
  simpa using zipWith_swap_prod_support' _ _ hx'

中文:
定理 zipWith_swap_prod_support
  条件: [Fintype α] (l l' : List α)
  证明: by
  intro x hx
  have hx' : x in { x | (zipWith Equiv.swap l l').prod x != x } := by simpa using hx
  simpa using zipWith_swap_prod_support' _ _ hx'

Depends on / 依赖: Equiv.swap, zipWith, zipWith_swap_prod_support
-/
theorem zipWith_swap_prod_support [Fintype α] (l l' : List α) :
    (zipWith Equiv.swap l l').prod.support <= l.toFinset ⊔ l'.toFinset := by
  intro x hx
  have hx' : x in { x | (zipWith Equiv.swap l l').prod x != x } := by simpa using hx
  simpa using zipWith_swap_prod_support' _ _ hx'

/--
theorem `support_formPerm_le'` / 定理 `support_formPerm_le'`

English:
theorem support_formPerm_le'
  statement: { x | formPerm l x != x } <= l.toFinset
  proof: by
  refine (zipWith_swap_prod_support' l l.tail).trans ?_
  simpa [Finset.subset_iff] using! tail_subset l

中文:
定理 support_formPerm_le'
  结论: { x | formPerm l x != x } <= l.toFinset
  证明: by
  refine (zipWith_swap_prod_support' l l.tail).trans ?_
  simpa [Finset.subset_iff] using! tail_subset l

Depends on / 依赖: Finset, Finset.subset_iff, l.tail, subset_iff, tail_subset, zipWith_swap_prod_support
-/
theorem support_formPerm_le' : { x | formPerm l x != x } <= l.toFinset := by
  refine (zipWith_swap_prod_support' l l.tail).trans ?_
  simpa [Finset.subset_iff] using! tail_subset l

/--
theorem `support_formPerm_le` / 定理 `support_formPerm_le`

English:
theorem support_formPerm_le
  given: [Fintype α]
  statement: support (formPerm l) <= l.toFinset
  proof: by
  intro x hx
  have hx' : x in { x | formPerm l x != x } := by simpa using hx
  simpa using support_formPerm_le' _ hx'

中文:
定理 support_formPerm_le
  条件: [Fintype α]
  结论: support (formPerm l) <= l.toFinset
  证明: by
  intro x hx
  have hx' : x in { x | formPerm l x != x } := by simpa using hx
  simpa using support_formPerm_le' _ hx'

Depends on / 依赖: formPerm, support_formPerm_le
-/
theorem support_formPerm_le [Fintype α] : support (formPerm l) <= l.toFinset := by
  intro x hx
  have hx' : x in { x | formPerm l x != x } := by simpa using hx
  simpa using support_formPerm_le' _ hx'

variable {l} {x : α}

/--
theorem `mem_of_formPerm_apply_ne` / 定理 `mem_of_formPerm_apply_ne`

English:
theorem mem_of_formPerm_apply_ne
  given: (h : l.formPerm x != x)
  statement: x in l
  proof: by
  simpa [or_iff_left_of_imp mem_of_mem_tail] using mem_or_mem_of_zipWith_swap_prod_ne h

中文:
定理 mem_of_formPerm_apply_ne
  条件: (h : l.formPerm x != x)
  结论: x in l
  证明: by
  simpa [or_iff_left_of_imp mem_of_mem_tail] using mem_or_mem_of_zipWith_swap_prod_ne h

Depends on / 依赖: mem_of_mem_tail, mem_or_mem_of_zipWith_swap_prod_ne, or_iff_left_of_imp
-/
theorem mem_of_formPerm_apply_ne (h : l.formPerm x != x) : x in l := by
  simpa [or_iff_left_of_imp mem_of_mem_tail] using mem_or_mem_of_zipWith_swap_prod_ne h

/--
theorem `formPerm_apply_of_notMem` / 定理 `formPerm_apply_of_notMem`

English:
theorem formPerm_apply_of_notMem
  given: (h : x ∉ l)
  statement: formPerm l x = x
  proof: not_imp_comm.1 mem_of_formPerm_apply_ne h

中文:
定理 formPerm_apply_of_notMem
  条件: (h : x ∉ l)
  结论: formPerm l x = x
  证明: not_imp_comm.1 mem_of_formPerm_apply_ne h

Depends on / 依赖: mem_of_formPerm_apply_ne, not_imp_comm
-/
theorem formPerm_apply_of_notMem (h : x ∉ l) : formPerm l x = x :=
  not_imp_comm.1 mem_of_formPerm_apply_ne h

/--
theorem `formPerm_apply_mem_of_mem` / 定理 `formPerm_apply_mem_of_mem`

English:
theorem formPerm_apply_mem_of_mem
  given: (h : x in l)
  statement: formPerm l x in l
  proof: by
  rcases l with - | ⟨y, l⟩
  · simp at h
  induction l generalizing x y with
  | nil => simpa using h
  | cons z l IH =>
    by_cases hx : x in z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      split_ifs
      · simp
      · simp
      · simp [*]
    · replace h : x = y := Or.

中文:
定理 formPerm_apply_mem_of_mem
  条件: (h : x in l)
  结论: formPerm l x in l
  证明: by
  rcases l with - | ⟨y, l⟩
  · simp at h
  induction l generalizing x y with
  | nil => simpa using h
  | cons z l IH =>
    by_cases hx : x in z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      split_ifs
      · simp
      · simp
      · simp [*]
    · replace h : x = y := Or.

Depends on / 依赖: Or.resolve_right, formPerm_apply_of_notMem, formPerm_cons_cons, generalizing, mem_cons, mul_apply, replace, resolve_right, split_ifs, swap_apply_def
-/
theorem formPerm_apply_mem_of_mem (h : x in l) : formPerm l x in l := by
  rcases l with - | ⟨y, l⟩
  · simp at h
  induction l generalizing x y with
  | nil => simpa using h
  | cons z l IH =>
    by_cases hx : x in z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      split_ifs
      · simp
      · simp
      · simp [*]
    · replace h : x = y := Or.resolve_right (mem_cons.1 h) hx
      simp [formPerm_apply_of_notMem hx, ← h]

/--
theorem `mem_of_formPerm_apply_mem` / 定理 `mem_of_formPerm_apply_mem`

English:
theorem mem_of_formPerm_apply_mem
  given: (h : l.formPerm x in l)
  statement: x in l
  proof: by
  contrapose h
  rwa [formPerm_apply_of_notMem h]

@[simp]

中文:
定理 mem_of_formPerm_apply_mem
  条件: (h : l.formPerm x in l)
  结论: x in l
  证明: by
  contrapose h
  rwa [formPerm_apply_of_notMem h]

@[simp]

Depends on / 依赖: contrapose, formPerm_apply_of_notMem
-/
theorem mem_of_formPerm_apply_mem (h : l.formPerm x in l) : x in l := by
  contrapose h
  rwa [formPerm_apply_of_notMem h]

@[simp]
/--
theorem `formPerm_mem_iff_mem` / 定理 `formPerm_mem_iff_mem`

English:
theorem formPerm_mem_iff_mem
  statement: l.formPerm x in l ↔ x in l
  proof: ⟨l.mem_of_formPerm_apply_mem, l.formPerm_apply_mem_of_mem⟩

@[simp]

中文:
定理 formPerm_mem_iff_mem
  结论: l.formPerm x in l ↔ x in l
  证明: ⟨l.mem_of_formPerm_apply_mem, l.formPerm_apply_mem_of_mem⟩

@[simp]

Depends on / 依赖: formPerm_apply_mem_of_mem, l.formPerm_apply_mem_of_mem, l.mem_of_formPerm_apply_mem, mem_of_formPerm_apply_mem
-/
theorem formPerm_mem_iff_mem : l.formPerm x in l ↔ x in l :=
  ⟨l.mem_of_formPerm_apply_mem, l.formPerm_apply_mem_of_mem⟩

@[simp]
/--
theorem `formPerm_cons_concat_apply_last` / 定理 `formPerm_cons_concat_apply_last`

English:
theorem formPerm_cons_concat_apply_last
  given: (x y : α) (xs : List α)
  proof: by
  induction xs generalizing x y with
  | nil => simp
  | cons z xs IH => simp [IH]

@[simp]

中文:
定理 formPerm_cons_concat_apply_last
  条件: (x y : α) (xs : List α)
  证明: by
  induction xs generalizing x y with
  | nil => simp
  | cons z xs IH => simp [IH]

@[simp]

Depends on / 依赖: generalizing
-/
theorem formPerm_cons_concat_apply_last (x y : α) (xs : List α) :
    formPerm (x :: (xs ++ [y])) y = x := by
  induction xs generalizing x y with
  | nil => simp
  | cons z xs IH => simp [IH]

@[simp]
/--
theorem `formPerm_apply_getLast` / 定理 `formPerm_apply_getLast`

English:
theorem formPerm_apply_getLast
  given: (x : α) (xs : List α)
  proof: by
  induction xs using List.reverseRecOn generalizing x <;> simp

@[simp]

中文:
定理 formPerm_apply_getLast
  条件: (x : α) (xs : List α)
  证明: by
  induction xs using List.reverseRecOn generalizing x <;> simp

@[simp]

Depends on / 依赖: List.reverseRecOn, generalizing, reverseRecOn
-/
theorem formPerm_apply_getLast (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x := by
  induction xs using List.reverseRecOn generalizing x <;> simp

@[simp]
/--
theorem `formPerm_apply_getElem_length` / 定理 `formPerm_apply_getElem_length`

English:
theorem formPerm_apply_getElem_length
  given: (x : α) (xs : List α)
  proof: by
  rw [getElem_cons_length rfl]; rw [formPerm_apply_getLast]

中文:
定理 formPerm_apply_getElem_length
  条件: (x : α) (xs : List α)
  证明: by
  rw [getElem_cons_length rfl]; rw [formPerm_apply_getLast]

Depends on / 依赖: formPerm_apply_getLast, getElem_cons_length
-/
theorem formPerm_apply_getElem_length (x : α) (xs : List α) :
    formPerm (x :: xs) (x :: xs)[xs.length] = x := by
  rw [getElem_cons_length rfl]; rw [formPerm_apply_getLast]

/--
theorem `formPerm_apply_head` / 定理 `formPerm_apply_head`

English:
theorem formPerm_apply_head
  given: (x y : α) (xs : List α) (h : Nodup (x :: y :: xs))
  proof: by simp [formPerm_apply_of_notMem h.notMem]

中文:
定理 formPerm_apply_head
  条件: (x y : α) (xs : List α) (h : Nodup (x :: y :: xs))
  证明: by simp [formPerm_apply_of_notMem h.notMem]

Depends on / 依赖: formPerm_apply_of_notMem, h.notMem, notMem
-/
theorem formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) :
    formPerm (x :: y :: xs) x = y := by simp [formPerm_apply_of_notMem h.notMem]

/--
theorem `formPerm_apply_getElem_zero` / 定理 `formPerm_apply_getElem_zero`

English:
theorem formPerm_apply_getElem_zero
  given: (l : List α) (h : Nodup l) (hl : 1 < l.length)
  proof: by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
  · simp at hl
  · rw [getElem_cons_zero, formPerm_apply_head _ _ _ h, getElem_cons_succ, getElem_cons_zero]

中文:
定理 formPerm_apply_getElem_zero
  条件: (l : List α) (h : Nodup l) (hl : 1 < l.length)
  证明: by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
  · simp at hl
  · rw [getElem_cons_zero, formPerm_apply_head _ _ _ h, getElem_cons_succ, getElem_cons_zero]

Depends on / 依赖: formPerm_apply_head, getElem_cons_succ, getElem_cons_zero
-/
theorem formPerm_apply_getElem_zero (l : List α) (h : Nodup l) (hl : 1 < l.length) :
    formPerm l l[0] = l[1] := by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
  · simp at hl
  · rw [getElem_cons_zero, formPerm_apply_head _ _ _ h, getElem_cons_succ, getElem_cons_zero]

variable (l)

/--
theorem `formPerm_eq_head_iff_eq_getLast` / 定理 `formPerm_eq_head_iff_eq_getLast`

English:
theorem formPerm_eq_head_iff_eq_getLast
  given: (x y : α)
  proof: Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff

中文:
定理 formPerm_eq_head_iff_eq_getLast
  条件: (x y : α)
  证明: Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff

Depends on / 依赖: Iff.trans, eq_iff, formPerm, formPerm_apply_getLast, injective, injective.eq_iff
-/
theorem formPerm_eq_head_iff_eq_getLast (x y : α) :
    formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _) :=
  Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff

/--
theorem `formPerm_apply_lt_getElem` / 定理 `formPerm_apply_lt_getElem`

English:
theorem formPerm_apply_lt_getElem
  given: (xs : List α) (h : Nodup xs) (n : Nat) (hn : n + 1 < xs.length)
  proof: by
  induction n generalizing xs with
  | zero => simpa using formPerm_apply_getElem_zero _ h _
  | succ n IH =>
    rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
    · rw [formPerm_singleton, getElem_singleton, getElem_singleton, one_apply]
    · specialize IH (y :: l) h.of_cons _
      · s

中文:
定理 formPerm_apply_lt_getElem
  条件: (xs : List α) (h : Nodup xs) (n : 自然数) (hn : n + 1 < xs.length)
  证明: by
  induction n generalizing xs with
  | zero => simpa using formPerm_apply_getElem_zero _ h _
  | succ n IH =>
    rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
    · rw [formPerm_singleton, getElem_singleton, getElem_singleton, one_apply]
    · specialize IH (y :: l) h.of_cons _
      · s

Depends on / 依赖: Function, Function.comp, Nat.succ_lt_succ_iff, coe_mul, formPerm_apply_getElem_zero, formPerm_cons_cons, formPerm_singleton, generalizing, getElem_cons_succ, getElem_singleton, h.of_cons, of_cons, one_apply, specialize, succ_lt_succ_iff, swap_apply_eq_iff, swap_apply_of_ne_of_ne
-/
theorem formPerm_apply_lt_getElem (xs : List α) (h : Nodup xs) (n : Nat) (hn : n + 1 < xs.length) :
    formPerm xs xs[n] = xs[n + 1] := by
  induction n generalizing xs with
  | zero => simpa using formPerm_apply_getElem_zero _ h _
  | succ n IH =>
    rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
    · rw [formPerm_singleton, getElem_singleton, getElem_singleton, one_apply]
    · specialize IH (y :: l) h.of_cons _
      · simpa [Nat.succ_lt_succ_iff] using hn
      simp only [swap_apply_eq_iff, coe_mul, formPerm_cons_cons, Function.comp]
      simp only [getElem_cons_succ] at *
      rw [← IH]; rw [swap_apply_of_ne_of_ne] <;>
      · intro hx
        rw [← hx]; rw [IH] at h
        simp [getElem_mem] at h

/--
theorem `formPerm_apply_getElem` / 定理 `formPerm_apply_getElem`

English:
theorem formPerm_apply_getElem
  given: (xs : List α) (w : Nodup xs) (i : Nat) (h : i < xs.length)
  proof: by
  rcases xs with - | ⟨x, xs⟩
  · simp at h
  · have : i <= xs.length := by
      refine Nat.le_of_lt_succ ?_
      simpa using h
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · rw [formPerm_apply_lt_getElem (x :: xs) w _ (Nat.succ_lt_succ hn')]
      congr
      rw [Nat.mod_eq_of_lt]; 

中文:
定理 formPerm_apply_getElem
  条件: (xs : List α) (w : Nodup xs) (i : 自然数) (h : i < xs.length)
  证明: by
  rcases xs with - | ⟨x, xs⟩
  · simp at h
  · have : i <= xs.length := by
      refine Nat.le_of_lt_succ ?_
      simpa using h
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · rw [formPerm_apply_lt_getElem (x :: xs) w _ (Nat.succ_lt_succ hn')]
      congr
      rw [Nat.mod_eq_of_lt]; 

Depends on / 依赖: Nat.le_of_lt_succ, Nat.mod_eq_of_lt, Nat.succ_eq_add_one, Nat.succ_lt_succ, eq_or_lt, formPerm_apply_lt_getElem, le_of_lt_succ, length, mod_eq_of_lt, succ_eq_add_one, succ_lt_succ, this.eq_or_lt, xs.length
-/
theorem formPerm_apply_getElem (xs : List α) (w : Nodup xs) (i : Nat) (h : i < xs.length) :
    formPerm xs xs[i] =
      xs[(i + 1) % xs.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  rcases xs with - | ⟨x, xs⟩
  · simp at h
  · have : i <= xs.length := by
      refine Nat.le_of_lt_succ ?_
      simpa using h
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · rw [formPerm_apply_lt_getElem (x :: xs) w _ (Nat.succ_lt_succ hn')]
      congr
      rw [Nat.mod_eq_of_lt]; simpa [Nat.succ_eq_add_one]

/--
theorem `support_formPerm_of_nodup'` / 定理 `support_formPerm_of_nodup'`

English:
theorem support_formPerm_of_nodup'
  given: (l : List α) (h : Nodup l) (h' : forall x : α, l != [x])
  proof: by
  apply _root_.le_antisymm
  · exact support_formPerm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_toFinset] at hx
    obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
    rw [Set.mem_ofPred_eq]; rw [formPerm_apply_getElem _ h]
    intro H
    rw [nodup_iff_injective_get]; rw [Function.Injecti

中文:
定理 support_formPerm_of_nodup'
  条件: (l : List α) (h : Nodup l) (h' : 对任意 x : α, l != [x])
  证明: by
  apply _root_.le_antisymm
  · exact support_formPerm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_toFinset] at hx
    obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
    rw [Set.mem_ofPred_eq]; rw [formPerm_apply_getElem _ h]
    intro H
    rw [nodup_iff_injective_get]; rw [Function.Injecti

Depends on / 依赖: Fin.mk.inj_iff.mp, Finset, Finset.mem_coe, Function, Function.Injective, Injective, Nat.mod_self, Nat.succ_le_of_lt, Set.mem_ofPred_eq, _root_, _root_.le_antisymm, eq_or_lt, formPerm_apply_getElem, getElem_of_mem, inj_iff, le_antisymm, length_eq_one_iff, mem_coe, mem_ofPred_eq, mem_toFinset
-/
theorem support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : forall x : α, l != [x]) :
    { x | formPerm l x != x } = l.toFinset := by
  apply _root_.le_antisymm
  · exact support_formPerm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_toFinset] at hx
    obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
    rw [Set.mem_ofPred_eq]; rw [formPerm_apply_getElem _ h]
    intro H
    rw [nodup_iff_injective_get]; rw [Function.Injective] at h
    specialize h H
    rcases (Nat.succ_le_of_lt hn).eq_or_lt with hn' | hn'
    · simp only [← hn', Nat.mod_self] at h
      refine not_exists.mpr h' ?_
      rw [← length_eq_one_iff]; rw [← hn']; rw [(Fin.mk.inj_iff.mp h).symm]
    · simp [Nat.mod_eq_of_lt hn'] at h

/--
theorem `support_formPerm_of_nodup` / 定理 `support_formPerm_of_nodup`

English:
theorem support_formPerm_of_nodup
  given: [Fintype α] (l : List α) (h : Nodup l) (h' : forall x : α, l != [x])
  proof: by
  rw [← Finset.coe_inj]
  convert! support_formPerm_of_nodup' _ h h'
  simp [Set.ext_iff]

中文:
定理 support_formPerm_of_nodup
  条件: [Fintype α] (l : List α) (h : Nodup l) (h' : 对任意 x : α, l != [x])
  证明: by
  rw [← Finset.coe_inj]
  convert! support_formPerm_of_nodup' _ h h'
  simp [Set.ext_iff]

Depends on / 依赖: Finset, Finset.coe_inj, Set.ext_iff, coe_inj, convert, ext_iff, support_formPerm_of_nodup
-/
theorem support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : forall x : α, l != [x]) :
    support (formPerm l) = l.toFinset := by
  rw [← Finset.coe_inj]
  convert! support_formPerm_of_nodup' _ h h'
  simp [Set.ext_iff]

/--
theorem `formPerm_rotate_one` / 定理 `formPerm_rotate_one`

English:
theorem formPerm_rotate_one
  given: (l : List α) (h : Nodup l)
  statement: formPerm (l.rotate 1) = formPerm l
  proof: by
  have h' : Nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x in l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    rw [formPerm_apply_getElem _ h']; rw [getElem_rotate l]; rw [getElem_rotate l]; rw [formPerm_apply_getElem _ h]
    simp
  · rw [formPerm_apply_of_notMem hx,

中文:
定理 formPerm_rotate_one
  条件: (l : List α) (h : Nodup l)
  结论: formPerm (l.rotate 1) = formPerm l
  证明: by
  have h' : Nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x in l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    rw [formPerm_apply_getElem _ h']; rw [getElem_rotate l]; rw [getElem_rotate l]; rw [formPerm_apply_getElem _ h]
    simp
  · rw [formPerm_apply_of_notMem hx,

Depends on / 依赖: formPerm_apply_getElem, formPerm_apply_of_notMem, getElem_of_mem, getElem_rotate, l.rotate, rotate
-/
theorem formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = formPerm l := by
  have h' : Nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x in l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    rw [formPerm_apply_getElem _ h']; rw [getElem_rotate l]; rw [getElem_rotate l]; rw [formPerm_apply_getElem _ h]
    simp
  · rw [formPerm_apply_of_notMem hx, formPerm_apply_of_notMem]
    simpa using hx

/--
theorem `formPerm_rotate` / 定理 `formPerm_rotate`

English:
theorem formPerm_rotate
  given: (l : List α) (h : Nodup l) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [← rotate_rotate]; rw [formPerm_rotate_one]; rw [hn]
    rwa [IsRotated.nodup_iff]
    exact IsRotated.forall l n

中文:
定理 formPerm_rotate
  条件: (l : List α) (h : Nodup l) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [← rotate_rotate]; rw [formPerm_rotate_one]; rw [hn]
    rwa [IsRotated.nodup_iff]
    exact IsRotated.forall l n

Depends on / 依赖: IsRotated, IsRotated.forall, IsRotated.nodup_iff, formPerm_rotate_one, nodup_iff, rotate_rotate
-/
theorem formPerm_rotate (l : List α) (h : Nodup l) (n : Nat) :
    formPerm (l.rotate n) = formPerm l := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [← rotate_rotate]; rw [formPerm_rotate_one]; rw [hn]
    rwa [IsRotated.nodup_iff]
    exact IsRotated.forall l n

/--
theorem `formPerm_eq_of_isRotated` / 定理 `formPerm_eq_of_isRotated`

English:
theorem formPerm_eq_of_isRotated
  given: {l l' : List α} (hd : Nodup l) (h : l ~r l')
  proof: by
  obtain ⟨n, rfl⟩ := h
  exact (formPerm_rotate l hd n).symm

中文:
定理 formPerm_eq_of_isRotated
  条件: {l l' : List α} (hd : Nodup l) (h : l ~r l')
  证明: by
  obtain ⟨n, rfl⟩ := h
  exact (formPerm_rotate l hd n).symm

Depends on / 依赖: formPerm_rotate
-/
theorem formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') :
    formPerm l = formPerm l' := by
  obtain ⟨n, rfl⟩ := h
  exact (formPerm_rotate l hd n).symm

/--
theorem `formPerm_append_pair` / 定理 `formPerm_append_pair`

English:
theorem formPerm_append_pair
  statement: forall (l : List α) (a b : α),

中文:
定理 formPerm_append_pair
  结论: 对任意 (l : List α) (a b : α),
-/
theorem formPerm_append_pair : forall (l : List α) (a b : α),
    formPerm (l ++ [a, b]) = formPerm (l ++ [a]) * Equiv.swap a b
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x::y::l, a, b => by
    simpa [mul_assoc] using formPerm_append_pair (y::l) a b

/--
theorem `formPerm_reverse` / 定理 `formPerm_reverse`

English:
theorem formPerm_reverse
  statement: forall l : List α, formPerm l.reverse = (formPerm l)⁻¹

中文:
定理 formPerm_reverse
  结论: 对任意 l : List α, formPerm l.reverse = (formPerm l)⁻¹
-/
theorem formPerm_reverse : forall l : List α, formPerm l.reverse = (formPerm l)⁻¹
  | [] => rfl
  | [_] => rfl
  | a::b::l => by
    simp [formPerm_append_pair, Equiv.swap_comm, ← formPerm_reverse (b::l)]

/--
theorem `formPerm_pow_apply_getElem` / 定理 `formPerm_pow_apply_getElem`

English:
theorem formPerm_pow_apply_getElem
  given: (l : List α) (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length)
  proof: by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt h]
  | succ n hn =>
    simp [pow_succ', mul_apply, hn, formPerm_apply_getElem _ w,
      ← Nat.add_assoc]

中文:
定理 formPerm_pow_apply_getElem
  条件: (l : List α) (w : Nodup l) (n : 自然数) (i : 自然数) (h : i < l.length)
  证明: by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt h]
  | succ n hn =>
    simp [pow_succ', mul_apply, hn, formPerm_apply_getElem _ w,
      ← Nat.add_assoc]

Depends on / 依赖: Nat.add_assoc, Nat.mod_eq_of_lt, add_assoc, formPerm_apply_getElem, mod_eq_of_lt, mul_apply, pow_succ
-/
theorem formPerm_pow_apply_getElem (l : List α) (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length) :
    (formPerm l ^ n) l[i] =
      l[(i + n) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt h]
  | succ n hn =>
    simp [pow_succ', mul_apply, hn, formPerm_apply_getElem _ w,
      ← Nat.add_assoc]

/--
theorem `formPerm_pow_apply_head` / 定理 `formPerm_pow_apply_head`

English:
theorem formPerm_pow_apply_head
  given: (x : α) (l : List α) (h : Nodup (x :: l)) (n : Nat)
  proof: by
  convert! formPerm_pow_apply_getElem _ h n 0 (Nat.succ_pos _)
  simp

中文:
定理 formPerm_pow_apply_head
  条件: (x : α) (l : List α) (h : Nodup (x :: l)) (n : 自然数)
  证明: by
  convert! formPerm_pow_apply_getElem _ h n 0 (Nat.succ_pos _)
  simp

Depends on / 依赖: Nat.succ_pos, convert, formPerm_pow_apply_getElem, succ_pos
-/
theorem formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : Nat) :
    (formPerm (x :: l) ^ n) x =
      (x :: l)[(n % (x :: l).length)]'(Nat.mod_lt _ (Nat.zero_lt_succ _)) := by
  convert! formPerm_pow_apply_getElem _ h n 0 (Nat.succ_pos _)
  simp

/--
theorem `formPerm_ext_iff` / 定理 `formPerm_ext_iff`

English:
theorem formPerm_ext_iff
  statement: {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
  proof: by
  refine ⟨fun h => ?_, fun hr => formPerm_eq_of_isRotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' in x :: y :: l := by
    have : x' in { z | formPerm (x :: y :: l) z != z } := by
      rw [Set.mem_ofPred_eq]; rw [h x']; rw [formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, n

中文:
定理 formPerm_ext_iff
  结论: {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
  证明: by
  refine ⟨fun h => ?_, fun hr => formPerm_eq_of_isRotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' in x :: y :: l := by
    have : x' in { z | formPerm (x :: y :: l) z != z } := by
      rw [Set.mem_ofPred_eq]; rw [h x']; rw [formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, n

Depends on / 依赖: Equiv.Perm.ext_iff, Set.mem_ofPred_eq, dedup_eq_self, dedup_eq_self.m, ext_iff, formPerm, formPerm_apply_head, formPerm_eq_of_isRotated, get_of_mem, left.left.symm, length, mem_cons, mem_ofPred_eq, nodup_cons, support_formPerm_le
-/
theorem formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
    (hd' : Nodup (x' :: y' :: l')) :
    formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') := by
  refine ⟨fun h => ?_, fun hr => formPerm_eq_of_isRotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' in x :: y :: l := by
    have : x' in { z | formPerm (x :: y :: l) z != z } := by
      rw [Set.mem_ofPred_eq]; rw [h x']; rw [formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, nodup_cons] at hd'
      push Not at hd'
      exact hd'.left.left.symm
    simpa using support_formPerm_le' _ this
  obtain ⟨⟨n, hn⟩, hx'⟩ := get_of_mem hx
  have hl : (x :: y :: l).length = (x' :: y' :: l').length := by
    rw [← dedup_eq_self.mpr hd]; rw [← dedup_eq_self.mpr hd']; rw [← card_toFinset]; rw [← card_toFinset]
    refine congr_arg Finset.card ?_
    rw [← Finset.coe_inj]; rw [← support_formPerm_of_nodup' _ hd (by simp)]; rw [←
      support_formPerm_of_nodup' _ hd' (by simp)]
    simp only [h]
  use n
  apply List.ext_getElem
  · rw [length_rotate, hl]
  · intro k hk hk'
    rw [getElem_rotate]
    induction k with
    | zero =>
      refine Eq.trans ?_ hx'
      congr
      simpa using hn
    | succ k IH =>
      conv => congr <;> · arg 2; (rw [← Nat.mod_eq_of_lt hk'])
      rw [← formPerm_apply_getElem _ hd' k (k.lt_succ_self.trans hk')]; rw [← IH (k.lt_succ_self.trans hk)]; rw [← h]; rw [formPerm_apply_getElem _ hd]
      congr 1
      rw [hl]; rw [Nat.mod_eq_of_lt hk']; rw [add_right_comm]
      apply Nat.add_mod

/--
theorem `formPerm_apply_mem_eq_self_iff` / 定理 `formPerm_apply_mem_eq_self_iff`

English:
theorem formPerm_apply_mem_eq_self_iff
  given: (hl : Nodup l) (x : α) (hx : x in l)
  proof: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [formPerm_apply_getElem _ hl k hk]; rw [hl.getElem_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_ge
  · rw [hn] at hk
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with hk' | hk'
    · simp [← hk', eq_comm]
    · sim

中文:
定理 formPerm_apply_mem_eq_self_iff
  条件: (hl : Nodup l) (x : α) (hx : x in l)
  证明: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [formPerm_apply_getElem _ hl k hk]; rw [hl.getElem_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_ge
  · rw [hn] at hk
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with hk' | hk'
    · simp [← hk', eq_comm]
    · sim

Depends on / 依赖: Nat.le_of_lt_succ, Nat.mod_eq_of_lt, Nat.succ_lt_succ, Nat.succ_lt_succ_iff, absurd, eq_comm, eq_or_lt, formPerm_apply_getElem, getElem_inj_iff, getElem_of_mem, hk.trans_le, hl.getElem_inj_iff, hn.le, k.zero_le, k.zero_le.trans_lt, l.length, le_of_lt_succ, length, mod_eq_of_lt, ne.symm
-/
theorem formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x in l) :
    formPerm l x = x ↔ length l <= 1 := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [formPerm_apply_getElem _ hl k hk]; rw [hl.getElem_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_ge
  · rw [hn] at hk
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with hk' | hk'
    · simp [← hk', eq_comm]
    · simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.succ_lt_succ_iff] using
        (k.zero_le.trans_lt hk').ne.symm

/--
theorem `formPerm_apply_mem_ne_self_iff` / 定理 `formPerm_apply_mem_ne_self_iff`

English:
theorem formPerm_apply_mem_ne_self_iff
  given: (hl : Nodup l) (x : α) (hx : x in l)
  proof: by
  rw [Ne]; rw [formPerm_apply_mem_eq_self_iff _ hl x hx]; rw [not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩

中文:
定理 formPerm_apply_mem_ne_self_iff
  条件: (hl : Nodup l) (x : α) (hx : x in l)
  证明: by
  rw [Ne]; rw [formPerm_apply_mem_eq_self_iff _ hl x hx]; rw [not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩

Depends on / 依赖: Nat.lt_of_succ_le, Nat.succ_le_of_lt, formPerm_apply_mem_eq_self_iff, lt_of_succ_le, not_le, succ_le_of_lt
-/
theorem formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x in l) :
    formPerm l x != x ↔ 2 <= l.length := by
  rw [Ne]; rw [formPerm_apply_mem_eq_self_iff _ hl x hx]; rw [not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩

/--
theorem `formPerm_eq_one_iff` / 定理 `formPerm_eq_one_iff`

English:
theorem formPerm_eq_one_iff
  given: (hl : Nodup l)
  statement: formPerm l = 1 ↔ l.length <= 1
  proof: by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd mem_cons_self]
    constructor
    · simp +contextual
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd mem_cons_self,
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, le

中文:
定理 formPerm_eq_one_iff
  条件: (hl : Nodup l)
  结论: formPerm l = 1 ↔ l.length <= 1
  证明: by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd mem_cons_self]
    constructor
    · simp +contextual
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd mem_cons_self,
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, le

Depends on / 依赖: add_le_iff_nonpos_left, contextual, formPerm_apply_mem_eq_self_iff, length, length_eq_zero_iff, mem_cons_self, nonpos_iff_eq_zero
-/
theorem formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length <= 1 := by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd mem_cons_self]
    constructor
    · simp +contextual
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd mem_cons_self,
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero_iff] at h
      simp [h]

/--
theorem `formPerm_eq_formPerm_iff` / 定理 `formPerm_eq_formPerm_iff`

English:
theorem formPerm_eq_formPerm_iff
  given: {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup)
  proof: by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length <= 1 ↔ l' = nil ∨ l'.length <= 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length <= 1 ↔ [x] ~r l' ∨ l'.le

中文:
定理 formPerm_eq_formPerm_iff
  条件: {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup)
  证明: by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length <= 1 ↔ l' = nil ∨ l'.length <= 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length <= 1 ↔ [x] ~r l' ∨ l'.le

Depends on / 依赖: Or.inr, eq_comm, formPer, formPerm_eq_one_iff, h.perm.length_eq, le_rfl, length, length_eq, length_eq_zero_iff
-/
theorem formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length <= 1 ∧ l'.length <= 1 := by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length <= 1 ↔ l' = nil ∨ l'.length <= 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length <= 1 ↔ [x] ~r l' ∨ l'.length <= 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff, le_rfl]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (h | h)
    · simp [← h.perm.length_eq]
    · exact h
  · rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [-formPerm_cons_cons, formPerm_ext_iff hl hl']

/--
theorem `form_perm_zpow_apply_mem_imp_mem` / 定理 `form_perm_zpow_apply_mem_imp_mem`

English:
theorem form_perm_zpow_apply_mem_imp_mem
  given: (l : List α) (x : α) (hx : x in l) (n : Int)
  proof: by
  by_cases h : (l.formPerm ^ n) x = x
  · simpa [h] using hx
  · have h : x in { x | (l.formPerm ^ n) x != x } := h
    rw [← set_support_apply_mem] at h
    replace h := set_support_zpow_subset _ _ h
    simpa using support_formPerm_le' _ h

中文:
定理 form_perm_zpow_apply_mem_imp_mem
  条件: (l : List α) (x : α) (hx : x in l) (n : 整数)
  证明: by
  by_cases h : (l.formPerm ^ n) x = x
  · simpa [h] using hx
  · have h : x in { x | (l.formPerm ^ n) x != x } := h
    rw [← set_support_apply_mem] at h
    replace h := set_support_zpow_subset _ _ h
    simpa using support_formPerm_le' _ h

Depends on / 依赖: formPerm, l.formPerm, replace, set_support_apply_mem, set_support_zpow_subset, support_formPerm_le
-/
theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x in l) (n : Int) :
    (formPerm l ^ n) x in l := by
  by_cases h : (l.formPerm ^ n) x = x
  · simpa [h] using hx
  · have h : x in { x | (l.formPerm ^ n) x != x } := h
    rw [← set_support_apply_mem] at h
    replace h := set_support_zpow_subset _ _ h
    simpa using support_formPerm_le' _ h

/--
theorem `formPerm_pow_length_eq_one_of_nodup` / 定理 `formPerm_pow_length_eq_one_of_nodup`

English:
theorem formPerm_pow_length_eq_one_of_nodup
  given: (hl : Nodup l)
  statement: formPerm l ^ length l = 1
  proof: by
  ext x
  by_cases hx : x in l
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    simp [formPerm_pow_apply_getElem _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.formPerm ^ l.length) x != x } := by
      intro H
      refine hx ?_
      replace H := set_support_zpow_subset l.formPerm l.length H

中文:
定理 formPerm_pow_length_eq_one_of_nodup
  条件: (hl : Nodup l)
  结论: formPerm l ^ length l = 1
  证明: by
  ext x
  by_cases hx : x in l
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    simp [formPerm_pow_apply_getElem _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.formPerm ^ l.length) x != x } := by
      intro H
      refine hx ?_
      replace H := set_support_zpow_subset l.formPerm l.length H

Depends on / 依赖: Nat.mod_eq_of_lt, formPerm, formPerm_pow_apply_getElem, getElem_of_mem, l.formPerm, l.length, length, mod_eq_of_lt, replace, set_support_zpow_subset, support_formPerm_le
-/
theorem formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l = 1 := by
  ext x
  by_cases hx : x in l
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    simp [formPerm_pow_apply_getElem _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.formPerm ^ l.length) x != x } := by
      intro H
      refine hx ?_
      replace H := set_support_zpow_subset l.formPerm l.length H
      simpa using support_formPerm_le' _ H
    simpa using this

end FormPerm

end List
