/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.List
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fin.Basic

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `IsRotated`.

Based on this, we define the quotient of lists by the rotation relation, called `Cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.

-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace List

variable {α : Type*} [DecidableEq α]

/--
Definition of `nextOr` / `nextOr` 的定义

English:
definition nextOr
  signature: : forall (_ : List α) (_ _ : α), α

中文:
定义 nextOr
  签名: : 对任意 (_ : 列表 α) (_ _ : α), α
-/
def nextOr : forall (_ : List α) (_ _ : α), α
  | [], _, default => default
  | [_], _, default => default
  -- Handles the not-found and the wraparound case
  | y :: z :: xs, x, default => if x = y then z else nextOr (z :: xs) x default

@[simp]
/--
theorem `nextOr_nil` / 定理 `nextOr_nil`

English:
theorem nextOr_nil
  given: (x d : α)
  statement: nextOr [] x d = d
  proof: rfl

@[simp]

中文:
定理 nextOr_nil
  条件: (x d : α)
  结论: nextOr [] x d = d
  证明: rfl

@[simp]
-/
theorem nextOr_nil (x d : α) : nextOr [] x d = d :=
  rfl

@[simp]
/--
theorem `nextOr_singleton` / 定理 `nextOr_singleton`

English:
theorem nextOr_singleton
  given: (x y d : α)
  statement: nextOr [y] x d = d
  proof: rfl

@[simp]

中文:
定理 nextOr_singleton
  条件: (x y d : α)
  结论: nextOr [y] x d = d
  证明: rfl

@[simp]
-/
theorem nextOr_singleton (x y d : α) : nextOr [y] x d = d :=
  rfl

@[simp]
/--
theorem `nextOr_self_cons_cons` / 定理 `nextOr_self_cons_cons`

English:
theorem nextOr_self_cons_cons
  given: (xs : List α) (x y d : α)
  statement: nextOr (x :: y :: xs) x d = y
  proof: if_pos rfl

中文:
定理 nextOr_self_cons_cons
  条件: (xs : 列表 α) (x y d : α)
  结论: nextOr (x :: y :: xs) x d = y
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem nextOr_self_cons_cons (xs : List α) (x y d : α) : nextOr (x :: y :: xs) x d = y :=
  if_pos rfl

/--
theorem `nextOr_cons_of_ne` / 定理 `nextOr_cons_of_ne`

English:
theorem nextOr_cons_of_ne
  given: (xs : List α) (y x d : α) (h : x != y)
  proof: by
  rcases xs with - | ⟨z, zs⟩
  · rfl
  · exact if_neg h

中文:
定理 nextOr_cons_of_ne
  条件: (xs : 列表 α) (y x d : α) (h : x != y)
  证明: by
  rcases xs with - | ⟨z, zs⟩
  · rfl
  · exact if_neg h

Depends on / 依赖: if_neg
-/
theorem nextOr_cons_of_ne (xs : List α) (y x d : α) (h : x != y) :
    nextOr (y :: xs) x d = nextOr xs x d := by
  rcases xs with - | ⟨z, zs⟩
  · rfl
  · exact if_neg h

/--
theorem `nextOr_eq_nextOr_of_mem_dropLast` / 定理 `nextOr_eq_nextOr_of_mem_dropLast`

English:
theorem nextOr_eq_nextOr_of_mem_dropLast
  given: (xs : List α) (x d d' : α) (x_mem : x in xs.dropLast)
  proof: by
  induction xs with
  | nil => cases x_mem
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at x_mem
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    simpa [h] using x_mem

中文:
定理 nextOr_eq_nextOr_of_mem_dropLast
  条件: (xs : 列表 α) (x d d' : α) (x_mem : x in xs.dropLast)
  证明: by
  induction xs with
  | nil => cases x_mem
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at x_mem
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    simpa [h] using x_mem

Depends on / 依赖: nextOr, nextOr_self_cons_cons, x_mem
-/
theorem nextOr_eq_nextOr_of_mem_dropLast (xs : List α) (x d d' : α) (x_mem : x in xs.dropLast) :
    nextOr xs x d = nextOr xs x d' := by
  induction xs with
  | nil => cases x_mem
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at x_mem
  by_cases h : x = y
  · rw [h, nextOr_self_cons_cons, nextOr_self_cons_cons]
  · rw [nextOr, nextOr, IH]
    simpa [h] using x_mem

/--
theorem `mem_of_nextOr_ne` / 定理 `mem_of_nextOr_ne`

English:
theorem mem_of_nextOr_ne
  given: {xs : List α} {x d : α} (h : nextOr xs x d != d)
  statement: x in xs
  proof: by
  induction xs with
  | nil => simp at h
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at h
  · by_cases hx : x = y
    · simp [hx]
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h

中文:
定理 mem_of_nextOr_ne
  条件: {xs : 列表 α} {x d : α} (h : nextOr xs x d != d)
  结论: x in xs
  证明: by
  induction xs with
  | nil => simp at h
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at h
  · by_cases hx : x = y
    · simp [hx]
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h

Depends on / 依赖: nextOr_cons_of_ne
-/
theorem mem_of_nextOr_ne {xs : List α} {x d : α} (h : nextOr xs x d != d) : x in xs := by
  induction xs with
  | nil => simp at h
  | cons y ys IH => ?_
  rcases ys with - | ⟨z, zs⟩
  · simp at h
  · by_cases hx : x = y
    · simp [hx]
    · rw [nextOr_cons_of_ne _ _ _ _ hx] at h
      simpa [hx] using IH h

/--
theorem `nextOr_concat` / 定理 `nextOr_concat`

English:
theorem nextOr_concat
  given: {xs : List α} {x : α} (d : α) (h : x ∉ xs)
  statement: nextOr (xs ++ [x]) x d = d
  proof: by
  induction xs with
  | nil => simp
  | cons z zs IH =>
    obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    rw [cons_append]; rw [nextOr_cons_of_ne _ _ _ _ hz]; rw [IH hzs]

中文:
定理 nextOr_concat
  条件: {xs : 列表 α} {x : α} (d : α) (h : x ∉ xs)
  结论: nextOr (xs ++ [x]) x d = d
  证明: by
  induction xs with
  | nil => simp
  | cons z zs IH =>
    obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    rw [cons_append]; rw [nextOr_cons_of_ne _ _ _ _ hz]; rw [IH hzs]

Depends on / 依赖: cons_append, mem_cons, nextOr_cons_of_ne, not_or, not_or.mp
-/
theorem nextOr_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : nextOr (xs ++ [x]) x d = d := by
  induction xs with
  | nil => simp
  | cons z zs IH =>
    obtain ⟨hz, hzs⟩ := not_or.mp (mt mem_cons.2 h)
    rw [cons_append]; rw [nextOr_cons_of_ne _ _ _ _ hz]; rw [IH hzs]

/--
theorem `nextOr_mem` / 定理 `nextOr_mem`

English:
theorem nextOr_mem
  given: {xs : List α} {x d : α} (hd : d in xs)
  statement: nextOr xs x d in xs
  proof: by
  revert hd
  suffices forall xs' : List α, (forall x in xs, x in xs') -> d in xs' -> nextOr xs x d in xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction xs with
  | nil => exact hd
  | cons y ys ih => ?_
  rcases ys with - | ⟨z, zs⟩
  · exact hd
  rw [nextOr]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ mem_cons_self)
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

中文:
定理 nextOr_mem
  条件: {xs : 列表 α} {x d : α} (hd : d in xs)
  结论: nextOr xs x d in xs
  证明: by
  revert hd
  suffices forall xs' : List α, (forall x in xs, x in xs') -> d in xs' -> nextOr xs x d in xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction xs with
  | nil => exact hd
  | cons y ys ih => ?_
  rcases ys with - | ⟨z, zs⟩
  · exact hd
  rw [nextOr]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ mem_cons_self)
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

Depends on / 依赖: mem_cons_of_mem, mem_cons_self, nextOr, revert, split_ifs
-/
theorem nextOr_mem {xs : List α} {x d : α} (hd : d in xs) : nextOr xs x d in xs := by
  revert hd
  suffices forall xs' : List α, (forall x in xs, x in xs') -> d in xs' -> nextOr xs x d in xs' by
    exact this xs fun _ => id
  intro xs' hxs' hd
  induction xs with
  | nil => exact hd
  | cons y ys ih => ?_
  rcases ys with - | ⟨z, zs⟩
  · exact hd
  rw [nextOr]
  split_ifs with h
  · exact hxs' _ (mem_cons_of_mem _ mem_cons_self)
  · exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

/--
Definition of `next` / `next` 的定义

English:
definition next
  signature: (l : List α) (x : α) (h : x in l)
  body: nextOr l x (l.get ⟨0, length_pos_of_mem h⟩)

中文:
定义 next
  签名: (l : 列表 α) (x : α) (h : x in l)
  定义体: nextOr l x (l.get ⟨0, length_pos_of_mem h⟩)

Depends on / 依赖: l.get, length_pos_of_mem, nextOr
-/
def next (l : List α) (x : α) (h : x in l) : α :=
  nextOr l x (l.get ⟨0, length_pos_of_mem h⟩)

/--
Definition of `prev` / `prev` 的定义

English:
definition prev
  signature: : forall l : List α, forall x in l, α

中文:
定义 prev
  签名: : 对任意 l : 列表 α, 对任意 x in l, α
-/
def prev : forall l : List α, forall x in l, α
  | [], _, h => by simp at h
  | [y], _, _ => y
  | y :: z :: xs, x, h =>
    if hx : x = y then getLast (z :: xs) (cons_ne_nil _ _)
    else if x = z then y else prev (z :: xs) x (by simpa [hx] using h)

variable (l : List α) (x : α)

@[simp]
/--
theorem `next_singleton` / 定理 `next_singleton`

English:
theorem next_singleton
  given: (x y : α) (h : x in [y])
  statement: next [y] x h = y
  proof: rfl

@[simp]

中文:
定理 next_singleton
  条件: (x y : α) (h : x in [y])
  结论: next [y] x h = y
  证明: rfl

@[simp]
-/
theorem next_singleton (x y : α) (h : x in [y]) : next [y] x h = y :=
  rfl

@[simp]
/--
theorem `prev_singleton` / 定理 `prev_singleton`

English:
theorem prev_singleton
  given: (x y : α) (h : x in [y])
  statement: prev [y] x h = y
  proof: rfl

中文:
定理 prev_singleton
  条件: (x y : α) (h : x in [y])
  结论: prev [y] x h = y
  证明: rfl
-/
theorem prev_singleton (x y : α) (h : x in [y]) : prev [y] x h = y :=
  rfl

/--
theorem `next_cons_cons_eq'` / 定理 `next_cons_cons_eq'`

English:
theorem next_cons_cons_eq'
  given: (y z : α) (h : x in y :: z :: l) (hx : x = y)
  proof: by rw [next, nextOr, if_pos hx]

@[simp]

中文:
定理 next_cons_cons_eq'
  条件: (y z : α) (h : x in y :: z :: l) (hx : x = y)
  证明: by rw [next, nextOr, if_pos hx]

@[simp]

Depends on / 依赖: if_pos, nextOr
-/
theorem next_cons_cons_eq' (y z : α) (h : x in y :: z :: l) (hx : x = y) :
    next (y :: z :: l) x h = z := by rw [next, nextOr, if_pos hx]

@[simp]
/--
theorem `next_cons_cons_eq` / 定理 `next_cons_cons_eq`

English:
theorem next_cons_cons_eq
  given: (z : α) (h : x in x :: z :: l)
  statement: next (x :: z :: l) x h = z
  proof: next_cons_cons_eq' l x x z h rfl

中文:
定理 next_cons_cons_eq
  条件: (z : α) (h : x in x :: z :: l)
  结论: next (x :: z :: l) x h = z
  证明: next_cons_cons_eq' l x x z h rfl

Depends on / 依赖: next_cons_cons_eq
-/
theorem next_cons_cons_eq (z : α) (h : x in x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl

/--
theorem `next_cons_eq_next_of_mem_dropLast` / 定理 `next_cons_eq_next_of_mem_dropLast`

English:
theorem next_cons_eq_next_of_mem_dropLast
  given: (h : x in l.dropLast) (y : α) (hy : x != y)
  proof: by
  rwa [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_dropLast]

中文:
定理 next_cons_eq_next_of_mem_dropLast
  条件: (h : x in l.dropLast) (y : α) (hy : x != y)
  证明: by
  rwa [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_dropLast]

Depends on / 依赖: nextOr_cons_of_ne, nextOr_eq_nextOr_of_mem_dropLast
-/
theorem next_cons_eq_next_of_mem_dropLast (h : x in l.dropLast) (y : α) (hy : x != y) :
    next (y :: l) x (mem_cons_of_mem _ <| mem_of_mem_dropLast h) =
      next l x (mem_of_mem_dropLast h) := by
  rwa [next, next, nextOr_cons_of_ne _ _ _ _ hy, nextOr_eq_nextOr_of_mem_dropLast]

/--
theorem `next_cons_concat` / 定理 `next_cons_concat`

English:
theorem next_cons_concat
  statement: (y : α) (hy : x != y) (hx : x ∉ l)
  proof: by
  rw [next]; rw [nextOr_concat]
  · simp
  · simp [hy, hx]

中文:
定理 next_cons_concat
  结论: (y : α) (hy : x != y) (hx : x ∉ l)
  证明: by
  rw [next]; rw [nextOr_concat]
  · simp
  · simp [hy, hx]

Depends on / 依赖: mem_append_right, mem_singleton_self
-/
theorem next_cons_concat (y : α) (hy : x != y) (hx : x ∉ l)
    (h : x in y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next]; rw [nextOr_concat]
  · simp
  · simp [hy, hx]

/--
theorem `next_getLast_cons` / 定理 `next_getLast_cons`

English:
theorem next_getLast_cons
  statement: (h : x in l) (y : α) (h : x in y :: l) (hy : x != y)
  proof: by
  rw [next]; rw [get]; rw [← dropLast_append_getLast (cons_ne_nil y l)]; rw [hx]; rw [nextOr_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := getElem_of_mem H
  · grind
  suffices k + 1 = l.length by simp [this] at hk
  rcases l with - | ⟨hd, tl⟩
  · simp at hk
  · rw [nodup_iff_injective_get] at hl
    rw [length]; rw [Nat.succ_inj]
exact Fin.val_eq_of_eq @hl ⟨k, Nat.lt_of_succ_lt by simpa using hk⟩
      ⟨tl.length, by simp⟩ (by grind)

中文:
定理 next_getLast_cons
  结论: (h : x in l) (y : α) (h : x in y :: l) (hy : x != y)
  证明: by
  rw [next]; rw [get]; rw [← dropLast_append_getLast (cons_ne_nil y l)]; rw [hx]; rw [nextOr_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := getElem_of_mem H
  · grind
  suffices k + 1 = l.length by simp [this] at hk
  rcases l with - | ⟨hd, tl⟩
  · simp at hk
  · rw [nodup_iff_injective_get] at hl
    rw [length]; rw [Nat.succ_inj]
exact Fin.val_eq_of_eq @hl ⟨k, Nat.lt_of_succ_lt by simpa using hk⟩
      ⟨tl.length, by simp⟩ (by grind)

Depends on / 依赖: Fin.val_eq_of_eq, Nat.lt_of_succ_lt, Nat.succ_inj, cons_ne_nil, dropLast_append_getLast, getElem_of_mem, l.length, length, lt_of_succ_lt, nextOr_concat, nodup_iff_injective_get, succ_inj, tl.length, val_eq_of_eq
-/
theorem next_getLast_cons (h : x in l) (y : α) (h : x in y :: l) (hy : x != y)
    (hx : x = getLast (y :: l) (cons_ne_nil _ _)) (hl : Nodup l) : next (y :: l) x h = y := by
  rw [next]; rw [get]; rw [← dropLast_append_getLast (cons_ne_nil y l)]; rw [hx]; rw [nextOr_concat]
  subst hx
  intro H
  obtain ⟨_ | k, hk, hk'⟩ := getElem_of_mem H
  · grind
  suffices k + 1 = l.length by simp [this] at hk
  rcases l with - | ⟨hd, tl⟩
  · simp at hk
  · rw [nodup_iff_injective_get] at hl
    rw [length]; rw [Nat.succ_inj]
exact Fin.val_eq_of_eq @hl ⟨k, Nat.lt_of_succ_lt by simpa using hk⟩
      ⟨tl.length, by simp⟩ (by grind)

/--
theorem `prev_getLast_cons'` / 定理 `prev_getLast_cons'`

English:
theorem prev_getLast_cons'
  given: (y : α) (hxy : x in y :: l) (hx : x = y)
  proof: by cases l <;> simp [prev, hx]

@[simp]

中文:
定理 prev_getLast_cons'
  条件: (y : α) (hxy : x in y :: l) (hx : x = y)
  证明: by cases l <;> simp [prev, hx]

@[simp]
-/
theorem prev_getLast_cons' (y : α) (hxy : x in y :: l) (hx : x = y) :
    prev (y :: l) x hxy = getLast (y :: l) (cons_ne_nil _ _) := by cases l <;> simp [prev, hx]

@[simp]
/--
theorem `prev_getLast_cons` / 定理 `prev_getLast_cons`

English:
theorem prev_getLast_cons
  given: (h : x in x :: l)
  proof: prev_getLast_cons' l x x h rfl

中文:
定理 prev_getLast_cons
  条件: (h : x in x :: l)
  证明: prev_getLast_cons' l x x h rfl

Depends on / 依赖: prev_getLast_cons
-/
theorem prev_getLast_cons (h : x in x :: l) :
    prev (x :: l) x h = getLast (x :: l) (cons_ne_nil _ _) :=
  prev_getLast_cons' l x x h rfl

/--
theorem `prev_head_eq_getLast` / 定理 `prev_head_eq_getLast`

English:
theorem prev_head_eq_getLast
  given: (hl : l != [])
  statement: l.prev (l.head hl) (head_mem hl) = l.getLast hl
  proof: by
  cases l with
  | nil => contradiction
  | cons head tail => apply prev_getLast_cons

中文:
定理 prev_head_eq_getLast
  条件: (hl : l != [])
  结论: l.prev (l.head hl) (head_mem hl) = l.getLast hl
  证明: by
  cases l with
  | nil => contradiction
  | cons head tail => apply prev_getLast_cons

Depends on / 依赖: prev_getLast_cons
-/
theorem prev_head_eq_getLast (hl : l != []) : l.prev (l.head hl) (head_mem hl) = l.getLast hl := by
  cases l with
  | nil => contradiction
  | cons head tail => apply prev_getLast_cons

/--
theorem `prev_cons_cons_eq'` / 定理 `prev_cons_cons_eq'`

English:
theorem prev_cons_cons_eq'
  given: (y z : α) (h : x in y :: z :: l) (hx : x = y)
  proof: by rw [prev, dif_pos hx]

中文:
定理 prev_cons_cons_eq'
  条件: (y z : α) (h : x in y :: z :: l) (hx : x = y)
  证明: by rw [prev, dif_pos hx]

Depends on / 依赖: dif_pos
-/
theorem prev_cons_cons_eq' (y z : α) (h : x in y :: z :: l) (hx : x = y) :
    prev (y :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) := by rw [prev, dif_pos hx]

/--
theorem `prev_cons_cons_eq` / 定理 `prev_cons_cons_eq`

English:
theorem prev_cons_cons_eq
  given: (z : α) (h : x in x :: z :: l)
  proof: prev_cons_cons_eq' l x x z h rfl

中文:
定理 prev_cons_cons_eq
  条件: (z : α) (h : x in x :: z :: l)
  证明: prev_cons_cons_eq' l x x z h rfl

Depends on / 依赖: prev_cons_cons_eq
-/
theorem prev_cons_cons_eq (z : α) (h : x in x :: z :: l) :
    prev (x :: z :: l) x h = getLast (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl

/--
theorem `prev_cons_cons_of_ne'` / 定理 `prev_cons_cons_of_ne'`

English:
theorem prev_cons_cons_of_ne'
  given: (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x = z)
  proof: by
  cases l
  · simp [prev, hz]
  · rw [prev, dif_neg hy, if_pos hz]

中文:
定理 prev_cons_cons_of_ne'
  条件: (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x = z)
  证明: by
  cases l
  · simp [prev, hz]
  · rw [prev, dif_neg hy, if_pos hz]

Depends on / 依赖: dif_neg, if_pos
-/
theorem prev_cons_cons_of_ne' (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x = z) :
    prev (y :: z :: l) x h = y := by
  cases l
  · simp [prev, hz]
  · rw [prev, dif_neg hy, if_pos hz]

/--
theorem `prev_cons_cons_of_ne` / 定理 `prev_cons_cons_of_ne`

English:
theorem prev_cons_cons_of_ne
  given: (y : α) (h : x in y :: x :: l) (hy : x != y)
  proof: prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

中文:
定理 prev_cons_cons_of_ne
  条件: (y : α) (h : x in y :: x :: l) (hy : x != y)
  证明: prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

Depends on / 依赖: prev_cons_cons_of_ne
-/
theorem prev_cons_cons_of_ne (y : α) (h : x in y :: x :: l) (hy : x != y) :
    prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

/--
theorem `prev_ne_cons_cons` / 定理 `prev_ne_cons_cons`

English:
theorem prev_ne_cons_cons
  given: (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x != z)
  proof: by
  cases l
  · simp [hy, hz] at h
  · rw [prev, dif_neg hy, if_neg hz]

中文:
定理 prev_ne_cons_cons
  条件: (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x != z)
  证明: by
  cases l
  · simp [hy, hz] at h
  · rw [prev, dif_neg hy, if_neg hz]

Depends on / 依赖: dif_neg, if_neg
-/
theorem prev_ne_cons_cons (y z : α) (h : x in y :: z :: l) (hy : x != y) (hz : x != z) :
    prev (y :: z :: l) x h = prev (z :: l) x (by simpa [hy] using h) := by
  cases l
  · simp [hy, hz] at h
  · rw [prev, dif_neg hy, if_neg hz]

/--
theorem `next_mem` / 定理 `next_mem`

English:
theorem next_mem
  given: (h : x in l)
  statement: l.next x h in l
  proof: nextOr_mem (get_mem _ _)

中文:
定理 next_mem
  条件: (h : x in l)
  结论: l.next x h in l
  证明: nextOr_mem (get_mem _ _)

Depends on / 依赖: get_mem, nextOr_mem
-/
theorem next_mem (h : x in l) : l.next x h in l :=
  nextOr_mem (get_mem _ _)

/--
theorem `prev_mem` / 定理 `prev_mem`

English:
theorem prev_mem
  given: (h : x in l)
  statement: l.prev x h in l
  proof: by
  rcases l with - | ⟨hd, tl⟩
  · simp at h
  induction tl generalizing hd with
  | nil => simp
  | cons hd' tl hl =>
    by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (getLast_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self
      · exact mem_cons_of_mem _ (hl _ _)

中文:
定理 prev_mem
  条件: (h : x in l)
  结论: l.prev x h in l
  证明: by
  rcases l with - | ⟨hd, tl⟩
  · simp at h
  induction tl generalizing hd with
  | nil => simp
  | cons hd' tl hl =>
    by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (getLast_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self
      · exact mem_cons_of_mem _ (hl _ _)

Depends on / 依赖: dif_neg, generalizing, getLast_mem, mem_cons_of_mem, mem_cons_self, prev_cons_cons_eq, split_ifs
-/
theorem prev_mem (h : x in l) : l.prev x h in l := by
  rcases l with - | ⟨hd, tl⟩
  · simp at h
  induction tl generalizing hd with
  | nil => simp
  | cons hd' tl hl =>
    by_cases hx : x = hd
    · simp only [hx, prev_cons_cons_eq]
      exact mem_cons_of_mem _ (getLast_mem _)
    · rw [prev, dif_neg hx]
      split_ifs with hm
      · exact mem_cons_self
      · exact mem_cons_of_mem _ (hl _ _)

/--
theorem `nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast` / 定理 `nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast`

English:
theorem nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast
  statement: {l : List α} {a : α} (ha : a in l.dropLast)
  proof: by
  match l with
  | nil => simp at ha
  | [head] => simp at ha
  | x :: y :: tail =>
    rw [getElem?_cons_succ]; rw [nextOr]
    split_ifs with hx
    · grind
    rw [idxOf_cons_ne _ <| Ne.symm hx]; rw [nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
    grind

中文:
定理 nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast
  结论: {l : 列表 α} {a : α} (ha : a in l.dropLast)
  证明: by
  match l with
  | nil => simp at ha
  | [head] => simp at ha
  | x :: y :: tail =>
    rw [getElem?_cons_succ]; rw [nextOr]
    split_ifs with hx
    · grind
    rw [idxOf_cons_ne _ <| Ne.symm hx]; rw [nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
    grind

Depends on / 依赖: Ne.symm, _cons_succ, _idxOf_succ_of_mem_dropLast, getElem, idxOf_cons_ne, nextOr, nextOr_eq_getElem, split_ifs
-/
theorem nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast)
    (d : α) : l.nextOr a d = l[l.idxOf a + 1]? := by
  match l with
  | nil => simp at ha
  | [head] => simp at ha
  | x :: y :: tail =>
    rw [getElem?_cons_succ]; rw [nextOr]
    split_ifs with hx
    · grind
    rw [idxOf_cons_ne _ <| Ne.symm hx]; rw [nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
    grind

/--
theorem `nextOr_eq_getElem_idxOf_succ_of_mem_dropLast` / 定理 `nextOr_eq_getElem_idxOf_succ_of_mem_dropLast`

English:
theorem nextOr_eq_getElem_idxOf_succ_of_mem_dropLast
  statement: {l : List α} {a : α} (ha : a in l.dropLast)
  proof: Option.some_injective _ nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast ha d ▸ getElem?_pos ..

中文:
定理 nextOr_eq_getElem_idxOf_succ_of_mem_dropLast
  结论: {l : 列表 α} {a : α} (ha : a in l.dropLast)
  证明: Option.some_injective _ nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast ha d ▸ getElem?_pos ..

Depends on / 依赖: Option.some_injective, _idxOf_succ_of_mem_dropLast, _pos, getElem, nextOr_eq_getElem, some_injective
-/
theorem nextOr_eq_getElem_idxOf_succ_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast)
    (d : α) : l.nextOr a d = l[l.idxOf a + 1]'(succ_idxOf_lt_length_of_mem_dropLast ha) :=
Option.some_injective _ nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast ha d ▸ getElem?_pos ..

/--
theorem `nextOr_infix_of_mem_dropLast` / 定理 `nextOr_infix_of_mem_dropLast`

English:
theorem nextOr_infix_of_mem_dropLast
  given: {l : List α} {a : α} (ha : a in l.dropLast) (d : α)
  proof: by
  refine infix_iff_getElem?.mpr ⟨l.idxOf a, ?_, fun i hi => ?_⟩
  · have ⟨_, _⟩ := l.dropLast_prefix
    grind
  by_cases hi₁ : i = 1
  · grind [next, nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
  · grind [getElem?_idxOf, mem_of_mem_dropLast]

中文:
定理 nextOr_infix_of_mem_dropLast
  条件: {l : 列表 α} {a : α} (ha : a in l.dropLast) (d : α)
  证明: by
  refine infix_iff_getElem?.mpr ⟨l.idxOf a, ?_, fun i hi => ?_⟩
  · have ⟨_, _⟩ := l.dropLast_prefix
    grind
  by_cases hi₁ : i = 1
  · grind [next, nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
  · grind [getElem?_idxOf, mem_of_mem_dropLast]

Depends on / 依赖: _idxOf, _idxOf_succ_of_mem_dropLast, dropLast_prefix, getElem, infix_iff_getElem, l.dropLast_prefix, l.idxOf, mem_of_mem_dropLast, nextOr_eq_getElem
-/
theorem nextOr_infix_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast) (d : α) :
    [a, l.nextOr a d] <:+: l := by
  refine infix_iff_getElem?.mpr ⟨l.idxOf a, ?_, fun i hi => ?_⟩
  · have ⟨_, _⟩ := l.dropLast_prefix
    grind
  by_cases hi₁ : i = 1
  · grind [next, nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast]
  · grind [getElem?_idxOf, mem_of_mem_dropLast]

/--
theorem `nextOr_getLast_of_notMem_dropLast` / 定理 `nextOr_getLast_of_notMem_dropLast`

English:
theorem nextOr_getLast_of_notMem_dropLast
  statement: {l : List α} (hl : l != []) (h : l.getLast hl ∉ l.dropLast)
  proof: by
  match l with
  | nil | [_] => simp
  | x :: y :: tail =>
    unfold nextOr
    split_ifs with h'
    · grind
    apply nextOr_getLast_of_notMem_dropLast
    grind

中文:
定理 nextOr_getLast_of_notMem_dropLast
  结论: {l : 列表 α} (hl : l != []) (h : l.getLast hl ∉ l.dropLast)
  证明: by
  match l with
  | nil | [_] => simp
  | x :: y :: tail =>
    unfold nextOr
    split_ifs with h'
    · grind
    apply nextOr_getLast_of_notMem_dropLast
    grind

Depends on / 依赖: nextOr, nextOr_getLast_of_notMem_dropLast, split_ifs
-/
theorem nextOr_getLast_of_notMem_dropLast {l : List α} (hl : l != []) (h : l.getLast hl ∉ l.dropLast)
    (d : α) : l.nextOr (l.getLast hl) d = d := by
  match l with
  | nil | [_] => simp
  | x :: y :: tail =>
    unfold nextOr
    split_ifs with h'
    · grind
    apply nextOr_getLast_of_notMem_dropLast
    grind

/--
theorem `next_getLast_eq_head_of_notMem_dropLast` / 定理 `next_getLast_eq_head_of_notMem_dropLast`

English:
theorem next_getLast_eq_head_of_notMem_dropLast
  statement: {l : List α} (hl : l != [])
  proof: .trans by grind nextOr_getLast_of_notMem_dropLast hl h _

中文:
定理 next_getLast_eq_head_of_notMem_dropLast
  结论: {l : 列表 α} (hl : l != [])
  证明: .trans by grind nextOr_getLast_of_notMem_dropLast hl h _

Depends on / 依赖: nextOr_getLast_of_notMem_dropLast
-/
theorem next_getLast_eq_head_of_notMem_dropLast {l : List α} (hl : l != [])
    (h : l.getLast hl ∉ l.dropLast) : l.next (l.getLast hl) (getLast_mem hl) = l.head hl :=
.trans by grind nextOr_getLast_of_notMem_dropLast hl h _

/--
theorem `next_eq_getElem` / 定理 `next_eq_getElem`

English:
theorem next_eq_getElem
  given: {l : List α} {a : α} (ha : a in l)
  proof: by
  have hl := ne_nil_of_mem ha
  by_cases ha' : a in l.dropLast
  · simp [next, nextOr_eq_getElem_idxOf_succ_of_mem_dropLast ha',
Nat.mod_eq_of_lt succ_idxOf_lt_length_of_mem_dropLast ha']
  grind [dropLast_append_getLast, next_getLast_eq_head_of_notMem_dropLast, Nat.mod_self]

中文:
定理 next_eq_getElem
  条件: {l : 列表 α} {a : α} (ha : a in l)
  证明: by
  have hl := ne_nil_of_mem ha
  by_cases ha' : a in l.dropLast
  · simp [next, nextOr_eq_getElem_idxOf_succ_of_mem_dropLast ha',
Nat.mod_eq_of_lt succ_idxOf_lt_length_of_mem_dropLast ha']
  grind [dropLast_append_getLast, next_getLast_eq_head_of_notMem_dropLast, Nat.mod_self]

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.mod_self, dropLast, dropLast_append_getLast, l.dropLast, mod_eq_of_lt, mod_self, ne_nil_of_mem, nextOr_eq_getElem_idxOf_succ_of_mem_dropLast, next_getLast_eq_head_of_notMem_dropLast, succ_idxOf_lt_length_of_mem_dropLast
-/
theorem next_eq_getElem {l : List α} {a : α} (ha : a in l) :
    l.next a ha = l[(l.idxOf a + 1) % l.length]'(Nat.mod_lt _ <| by grind) := by
  have hl := ne_nil_of_mem ha
  by_cases ha' : a in l.dropLast
  · simp [next, nextOr_eq_getElem_idxOf_succ_of_mem_dropLast ha',
Nat.mod_eq_of_lt succ_idxOf_lt_length_of_mem_dropLast ha']
  grind [dropLast_append_getLast, next_getLast_eq_head_of_notMem_dropLast, Nat.mod_self]

/--
theorem `next_getElem` / 定理 `next_getElem`

English:
theorem next_getElem
  given: (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length)
  proof: by
  grind [next_eq_getElem]

中文:
定理 next_getElem
  条件: (l : 列表 α) (h : Nodup l) (i : 自然数) (hi : i < l.length)
  证明: by
  grind [next_eq_getElem]

Depends on / 依赖: next_eq_getElem
-/
theorem next_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    l.next l[i] (get_mem ..) = l[(i + 1) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt hi)) := by
  grind [next_eq_getElem]

/--
theorem `prev_eq_getElem?_idxOf_pred_of_ne_head` / 定理 `prev_eq_getElem?_idxOf_pred_of_ne_head`

English:
theorem prev_eq_getElem?_idxOf_pred_of_ne_head
  statement: {l : List α} {a : α} (ha : a in l)
  proof: by
  match l with
  | nil | [_] => grind
  | x :: y :: tail =>
    have ih := (y :: tail).prev_eq_getElem?_idxOf_pred_of_ne_head (a := a)
    grind [prev]

中文:
定理 prev_eq_getElem?_idxOf_pred_of_ne_head
  结论: {l : 列表 α} {a : α} (ha : a in l)
  证明: by
  match l with
  | nil | [_] => grind
  | x :: y :: tail =>
    have ih := (y :: tail).prev_eq_getElem?_idxOf_pred_of_ne_head (a := a)
    grind [prev]

Depends on / 依赖: _idxOf_pred_of_ne_head, prev_eq_getElem
-/
theorem prev_eq_getElem?_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a in l)
    (ha₀ : a != l.head (ne_nil_of_mem ha)) : l.prev a ha = l[l.idxOf a - 1]? := by
  match l with
  | nil | [_] => grind
  | x :: y :: tail =>
    have ih := (y :: tail).prev_eq_getElem?_idxOf_pred_of_ne_head (a := a)
    grind [prev]

/--
theorem `prev_eq_getElem_idxOf_pred_of_ne_head` / 定理 `prev_eq_getElem_idxOf_pred_of_ne_head`

English:
theorem prev_eq_getElem_idxOf_pred_of_ne_head
  statement: {l : List α} {a : α} (ha : a in l)
  proof: Option.some_injective _ prev_eq_getElem?_idxOf_pred_of_ne_head ha ha₀ ▸ getElem?_pos ..

中文:
定理 prev_eq_getElem_idxOf_pred_of_ne_head
  结论: {l : 列表 α} {a : α} (ha : a in l)
  证明: Option.some_injective _ prev_eq_getElem?_idxOf_pred_of_ne_head ha ha₀ ▸ getElem?_pos ..

Depends on / 依赖: Option.some_injective, _idxOf_pred_of_ne_head, _pos, getElem, prev_eq_getElem, some_injective
-/
theorem prev_eq_getElem_idxOf_pred_of_ne_head {l : List α} {a : α} (ha : a in l)
    (ha₀ : a != l.head (ne_nil_of_mem ha)) :
    l.prev a ha = l[l.idxOf a - 1]'(by grind [idxOf_lt_length_of_mem]) :=
Option.some_injective _ prev_eq_getElem?_idxOf_pred_of_ne_head ha ha₀ ▸ getElem?_pos ..

/--
theorem `prev_infix_of_mem_tail` / 定理 `prev_infix_of_mem_tail`

English:
theorem prev_infix_of_mem_tail
  statement: {l : List α} {a : α} (ha : a in l)
  proof: by
have := cons_head_tail (ne_nil_of_mem ha) ▸ idxOf_cons_ne _ Ne.symm ha₀
  refine infix_iff_getElem?.mpr ⟨l.idxOf a - 1, by grind, fun i hi => ?_⟩
  by_cases hi₁ : i = 1
  · subst hi₁
    grind
  grind [prev_eq_getElem?_idxOf_pred_of_ne_head]

中文:
定理 prev_infix_of_mem_tail
  结论: {l : 列表 α} {a : α} (ha : a in l)
  证明: by
have := cons_head_tail (ne_nil_of_mem ha) ▸ idxOf_cons_ne _ Ne.symm ha₀
  refine infix_iff_getElem?.mpr ⟨l.idxOf a - 1, by grind, fun i hi => ?_⟩
  by_cases hi₁ : i = 1
  · subst hi₁
    grind
  grind [prev_eq_getElem?_idxOf_pred_of_ne_head]

Depends on / 依赖: Ne.symm, _idxOf_pred_of_ne_head, cons_head_tail, idxOf_cons_ne, infix_iff_getElem, l.idxOf, ne_nil_of_mem, prev_eq_getElem
-/
theorem prev_infix_of_mem_tail {l : List α} {a : α} (ha : a in l)
    (ha₀ : a != l.head (ne_nil_of_mem ha)) : [l.prev a ha, a] <:+: l := by
have := cons_head_tail (ne_nil_of_mem ha) ▸ idxOf_cons_ne _ Ne.symm ha₀
  refine infix_iff_getElem?.mpr ⟨l.idxOf a - 1, by grind, fun i hi => ?_⟩
  by_cases hi₁ : i = 1
  · subst hi₁
    grind
  grind [prev_eq_getElem?_idxOf_pred_of_ne_head]

/--
theorem `prev_eq_getElem` / 定理 `prev_eq_getElem`

English:
theorem prev_eq_getElem
  given: {l : List α} {a : α} (ha : a in l)
  proof: by
  cases l with | nil => grind | cons head tail =>
  by_cases ha₀ : a = head
  · subst ha₀
    simp
    grind
  rw [prev_eq_getElem_idxOf_pred_of_ne_head ha ha₀]
  congr
  rw [← Nat.add_sub_assoc]; rw [Nat.sub_add_comm]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt]
  all_goals grind

中文:
定理 prev_eq_getElem
  条件: {l : 列表 α} {a : α} (ha : a in l)
  证明: by
  cases l with | nil => grind | cons head tail =>
  by_cases ha₀ : a = head
  · subst ha₀
    simp
    grind
  rw [prev_eq_getElem_idxOf_pred_of_ne_head ha ha₀]
  congr
  rw [← Nat.add_sub_assoc]; rw [Nat.sub_add_comm]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt]
  all_goals grind
-/
theorem prev_eq_getElem {l : List α} {a : α} (ha : a in l) :
    l.prev a ha = l[(l.idxOf a + (l.length - 1)) % l.length]'(Nat.mod_lt _ <| by grind) := by
  cases l with | nil => grind | cons head tail =>
  by_cases ha₀ : a = head
  · subst ha₀
    simp
    grind
  rw [prev_eq_getElem_idxOf_pred_of_ne_head ha ha₀]
  congr
  rw [← Nat.add_sub_assoc]; rw [Nat.sub_add_comm]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt]
  all_goals grind

/--
theorem `prev_getElem` / 定理 `prev_getElem`

English:
theorem prev_getElem
  given: (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length)
  proof: by
  grind [prev_eq_getElem]

@[simp]

中文:
定理 prev_getElem
  条件: (l : 列表 α) (h : Nodup l) (i : 自然数) (hi : i < l.length)
  证明: by
  grind [prev_eq_getElem]

@[simp]

Depends on / 依赖: prev_eq_getElem
-/
theorem prev_getElem (l : List α) (h : Nodup l) (i : Nat) (hi : i < l.length) :
    l.prev l[i] (get_mem ..) = l[(i + (l.length - 1)) % l.length]'(Nat.mod_lt _ (by lia)) := by
  grind [prev_eq_getElem]

@[simp]
/--
theorem `next_getLast_eq_head` / 定理 `next_getLast_eq_head`

English:
theorem next_getLast_eq_head
  given: (l : List α) (h : l != []) (hn : l.Nodup)
  proof: by
  have h1 : l.length - 1 + 1 = l.length := by grind [length_pos_iff]
  simp [getLast_eq_getElem h, head_eq_getElem h, next_getElem l hn (l.length - 1) (by grind), h1]

中文:
定理 next_getLast_eq_head
  条件: (l : 列表 α) (h : l != []) (hn : l.Nodup)
  证明: by
  have h1 : l.length - 1 + 1 = l.length := by grind [length_pos_iff]
  simp [getLast_eq_getElem h, head_eq_getElem h, next_getElem l hn (l.length - 1) (by grind), h1]

Depends on / 依赖: getLast_eq_getElem, head_eq_getElem, l.length, length, length_pos_iff, next_getElem
-/
theorem next_getLast_eq_head (l : List α) (h : l != []) (hn : l.Nodup) :
    l.next (l.getLast h) (getLast_mem h) = l.head h := by
  have h1 : l.length - 1 + 1 = l.length := by grind [length_pos_iff]
  simp [getLast_eq_getElem h, head_eq_getElem h, next_getElem l hn (l.length - 1) (by grind), h1]

/--
theorem `pmap_next_eq_rotate_one` / 定理 `pmap_next_eq_rotate_one`

English:
theorem pmap_next_eq_rotate_one
  given: (h : Nodup l)
  statement: (l.pmap l.next fun _ h => h) = l.rotate 1
  proof: by
  apply List.ext_getElem
  · simp
  · intros
    rw [getElem_pmap]; rw [getElem_rotate]; rw [next_getElem _ h]

中文:
定理 pmap_next_eq_rotate_one
  条件: (h : Nodup l)
  结论: (l.pmap l.next fun _ h => h) = l.rotate 1
  证明: by
  apply List.ext_getElem
  · simp
  · intros
    rw [getElem_pmap]; rw [getElem_rotate]; rw [next_getElem _ h]

Depends on / 依赖: List.ext_getElem, ext_getElem, getElem_pmap, getElem_rotate, intros, next_getElem
-/
theorem pmap_next_eq_rotate_one (h : Nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 := by
  apply List.ext_getElem
  · simp
  · intros
    rw [getElem_pmap]; rw [getElem_rotate]; rw [next_getElem _ h]

/--
theorem `pmap_prev_eq_rotate_length_sub_one` / 定理 `pmap_prev_eq_rotate_length_sub_one`

English:
theorem pmap_prev_eq_rotate_length_sub_one
  given: (h : Nodup l)
  proof: by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    rw [getElem_rotate]; rw [getElem_pmap]; rw [prev_getElem _ h]

中文:
定理 pmap_prev_eq_rotate_length_sub_one
  条件: (h : Nodup l)
  证明: by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    rw [getElem_rotate]; rw [getElem_pmap]; rw [prev_getElem _ h]

Depends on / 依赖: List.ext_getElem, ext_getElem, getElem_pmap, getElem_rotate, prev_getElem
-/
theorem pmap_prev_eq_rotate_length_sub_one (h : Nodup l) :
    (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    rw [getElem_rotate]; rw [getElem_pmap]; rw [prev_getElem _ h]

/--
theorem `prev_next` / 定理 `prev_next`

English:
theorem prev_next
  given: (l : List α) (h : Nodup l) (x : α) (hx : x in l)
  proof: by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [add_comm 1]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, this]

中文:
定理 prev_next
  条件: (l : 列表 α) (h : Nodup l) (x : α) (hx : x in l)
  证明: by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [add_comm 1]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, this]

Depends on / 依赖: Nat.add_mod_right, Nat.mod_add_mod, Nat.mod_eq_of_lt, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, add_assoc, add_comm, add_mod_right, getElem_of_mem, length, length_cons, mod_add_mod, mod_eq_of_lt, next_getElem, prev_getElem, sub_zero, succ_sub_succ_eq_sub
-/
theorem prev_next (l : List α) (h : Nodup l) (x : α) (hx : x in l) :
    prev l (next l x hx) (next_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + 1 + length tl) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [add_comm 1]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp only [length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, this]

/--
theorem `next_prev` / 定理 `next_prev`

English:
theorem next_prev
  given: (l : List α) (h : Nodup l) (x : α) (hx : x in l)
  proof: by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp [this]

中文:
定理 next_prev
  条件: (l : 列表 α) (h : Nodup l) (x : α) (hx : x in l)
  证明: by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp [this]

Depends on / 依赖: Nat.add_mod_right, Nat.mod_add_mod, Nat.mod_eq_of_lt, add_assoc, add_mod_right, getElem_of_mem, length, length_cons, mod_add_mod, mod_eq_of_lt, next_getElem, prev_getElem
-/
theorem next_prev (l : List α) (h : Nodup l) (x : α) (hx : x in l) :
    next l (prev l x hx) (prev_mem _ _ _) = x := by
  obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
  simp only [next_getElem, prev_getElem, h, Nat.mod_add_mod]
  rcases l with - | ⟨hd, tl⟩
  · simp at hn
  · have : (n + length tl + 1) % (length tl + 1) = n := by
      rw [length_cons] at hn
      rw [add_assoc]; rw [Nat.add_mod_right]; rw [Nat.mod_eq_of_lt hn]
    simp [this]

/--
theorem `prev_reverse_eq_next` / 定理 `prev_reverse_eq_next`

English:
theorem prev_reverse_eq_next
  given: (l : List α) (h : Nodup l) (x : α) (hx : x in l)
  proof: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length := by lia
  rw [← getElem_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [getElem_eq_getElem_reverse (l := l), pmap_next_eq_rotate_one _ h]
  rw [← getElem_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (Nat.sub_lt lpos Nat.succ_pos'),
      Nat.sub_sub_self (Nat.succ_le_of_lt lpos)]
    rw [getElem_eq_getElem_reverse]
    · simp [Nat.sub_sub_self (Nat.le_sub_one_of_lt hk)]
  · simpa

中文:
定理 prev_reverse_eq_next
  条件: (l : 列表 α) (h : Nodup l) (x : α) (hx : x in l)
  证明: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length := by lia
  rw [← getElem_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [getElem_eq_getElem_reverse (l := l), pmap_next_eq_rotate_one _ h]
  rw [← getElem_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (Nat.sub_lt lpos Nat.succ_pos'),
      Nat.sub_sub_self (Nat.succ_le_of_lt lpos)]
    rw [getElem_eq_getElem_reverse]
    · simp [Nat.sub_sub_self (Nat.le_sub_one_of_lt hk)]
  · simpa

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.sub_lt, Nat.sub_sub_self, Nat.succ_pos, getElem_eq_getElem_reverse, getElem_of_mem, getElem_pmap, k.zero_le.trans_lt, l.length, l.next, l.reverse.prev, length, length_reverse, mod_eq_of_lt, nodup_reverse, nodup_reverse.mpr, pmap_next_eq_rotate_one, pmap_prev_eq_rotate_length_sub_one, reverse, rotate_reverse
-/
theorem prev_reverse_eq_next (l : List α) (h : Nodup l) (x : α) (hx : x in l) :
    prev l.reverse x (mem_reverse.mpr hx) = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  have lpos : 0 < l.length := k.zero_le.trans_lt hk
  have key : l.length - 1 - k < l.length := by lia
  rw [← getElem_pmap l.next (fun _ h => h) (by simpa using hk)]
  simp_rw [getElem_eq_getElem_reverse (l := l), pmap_next_eq_rotate_one _ h]
  rw [← getElem_pmap l.reverse.prev fun _ h => h]
  · simp_rw [pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), rotate_reverse,
      length_reverse, Nat.mod_eq_of_lt (Nat.sub_lt lpos Nat.succ_pos'),
      Nat.sub_sub_self (Nat.succ_le_of_lt lpos)]
    rw [getElem_eq_getElem_reverse]
    · simp [Nat.sub_sub_self (Nat.le_sub_one_of_lt hk)]
  · simpa

/--
theorem `next_reverse_eq_prev` / 定理 `next_reverse_eq_prev`

English:
theorem next_reverse_eq_prev
  given: (l : List α) (h : Nodup l) (x : α) (hx : x in l)
  proof: by
  convert! (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm

中文:
定理 next_reverse_eq_prev
  条件: (l : 列表 α) (h : Nodup l) (x : α) (hx : x in l)
  证明: by
  convert! (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm

Depends on / 依赖: convert, l.reverse, mem_reverse, mem_reverse.mpr, nodup_reverse, nodup_reverse.mpr, prev_reverse_eq_next, reverse, reverse_reverse
-/
theorem next_reverse_eq_prev (l : List α) (h : Nodup l) (x : α) (hx : x in l) :
    next l.reverse x (mem_reverse.mpr hx) = prev l x hx := by
  convert! (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm
  exact (reverse_reverse l).symm

/--
theorem `isRotated_next_eq` / 定理 `isRotated_next_eq`

English:
theorem isRotated_next_eq
  given: {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l)
  proof: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_getElem _ hn]
  simp_rw [getElem_eq_getElem_rotate _ n k]
  rw [next_getElem _ (h.nodup_iff.mp hn)]; rw [getElem_eq_getElem_rotate _ n]
  simp [add_assoc]

中文:
定理 isRotated_next_eq
  条件: {l l' : 列表 α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l)
  证明: by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_getElem _ hn]
  simp_rw [getElem_eq_getElem_rotate _ n k]
  rw [next_getElem _ (h.nodup_iff.mp hn)]; rw [getElem_eq_getElem_rotate _ n]
  simp [add_assoc]

Depends on / 依赖: add_assoc, getElem_eq_getElem_rotate, getElem_of_mem, h.nodup_iff.mp, next_getElem, nodup_iff, simp_rw
-/
theorem isRotated_next_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l) :
    l.next x hx = l'.next x (h.mem_iff.mp hx) := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  obtain ⟨n, rfl⟩ := id h
  rw [next_getElem _ hn]
  simp_rw [getElem_eq_getElem_rotate _ n k]
  rw [next_getElem _ (h.nodup_iff.mp hn)]; rw [getElem_eq_getElem_rotate _ n]
  simp [add_assoc]

/--
theorem `isRotated_prev_eq` / 定理 `isRotated_prev_eq`

English:
theorem isRotated_prev_eq
  given: {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l)
  proof: by
  rw [← next_reverse_eq_prev _ hn]; rw [← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _

中文:
定理 isRotated_prev_eq
  条件: {l l' : 列表 α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l)
  证明: by
  rw [← next_reverse_eq_prev _ hn]; rw [← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _

Depends on / 依赖: h.nodup_iff.mp, h.reverse, isRotated_next_eq, next_reverse_eq_prev, nodup_iff, nodup_reverse, nodup_reverse.mpr, reverse
-/
theorem isRotated_prev_eq {l l' : List α} (h : l ~r l') (hn : Nodup l) {x : α} (hx : x in l) :
    l.prev x hx = l'.prev x (h.mem_iff.mp hx) := by
  rw [← next_reverse_eq_prev _ hn]; rw [← next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
  exact isRotated_next_eq h.reverse (nodup_reverse.mpr hn) _

end List

open List

/--
Definition of `Cycle` / `Cycle` 的定义

English:
definition Cycle
  signature: (α : Type*)
  body: Quotient (IsRotated.setoid α)

中文:
定义 环
  签名: (α : 类型)
  定义体: Quotient (IsRotated.setoid α)

Depends on / 依赖: IsRotated, IsRotated.setoid, Quotient, setoid
-/
def Cycle (α : Type*) : Type _ :=
  Quotient (IsRotated.setoid α)

namespace Cycle

variable {α : Type*}

/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: : List α -> Cycle α
  body: Quot.mk _

中文:
定义 ofList
  签名: : 列表 α -> 环 α
  定义体: Quot.mk _
-/
@[coe] def ofList : List α -> Cycle α :=
  Quot.mk _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (List α) (Cycle α)
  body: ⟨ofList⟩

@[simp]

中文:
实例 :
  签名: Coe (列表 α) (环 α)
  定义体: ⟨ofList⟩

@[simp]

Depends on / 依赖: ofList
-/
instance : Coe (List α) (Cycle α) :=
  ⟨ofList⟩

@[simp]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {l₁ l₂ : List α}
  statement: (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂
  proof: @Quotient.eq _ (IsRotated.setoid _) _ _

@[simp]

中文:
定理 coe_eq_coe
  条件: {l₁ l₂ : 列表 α}
  结论: (l₁ : 环 α) = (l₂ : 环 α) ↔ l₁ ~r l₂
  证明: @Quotient.eq _ (IsRotated.setoid _) _ _

@[simp]

Depends on / 依赖: IsRotated, IsRotated.setoid, Quotient, Quotient.eq, setoid
-/
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : Cycle α) ↔ l₁ ~r l₂ :=
  @Quotient.eq _ (IsRotated.setoid _) _ _

@[simp]
/--
theorem `mk_eq_coe` / 定理 `mk_eq_coe`

English:
theorem mk_eq_coe
  given: (l : List α)
  statement: Quot.mk _ l = (l : Cycle α)
  proof: rfl

@[simp]

中文:
定理 mk_eq_coe
  条件: (l : 列表 α)
  结论: 商.mk _ l = (l : 环 α)
  证明: rfl

@[simp]
-/
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl

@[simp]
/--
theorem `mk''_eq_coe` / 定理 `mk''_eq_coe`

English:
theorem mk''_eq_coe
  given: (l : List α)
  statement: Quotient.mk'' l = (l : Cycle α)
  proof: rfl

中文:
定理 mk''_eq_coe
  条件: (l : 列表 α)
  结论: 商.mk'' l = (l : 环 α)
  证明: rfl
-/
theorem mk''_eq_coe (l : List α) : Quotient.mk'' l = (l : Cycle α) :=
  rfl

/--
theorem `coe_cons_eq_coe_append` / 定理 `coe_cons_eq_coe_append`

English:
theorem coe_cons_eq_coe_append
  given: (l : List α) (a : α)
  proof: Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩

中文:
定理 coe_cons_eq_coe_append
  条件: (l : 列表 α) (a : α)
  证明: Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩

Depends on / 依赖: Quot.sound, rotate_cons_succ, rotate_zero
-/
theorem coe_cons_eq_coe_append (l : List α) (a : α) :
    (↑(a :: l) : Cycle α) = (↑(l ++ [a]) : Cycle α) :=
  Quot.sound ⟨1, by rw [rotate_cons_succ, rotate_zero]⟩

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Cycle α
  body: ([] : List α)

@[simp]

中文:
定义 nil
  签名: : 环 α
  定义体: ([] : List α)

@[simp]
-/
def nil : Cycle α :=
  ([] : List α)

@[simp]
/--
theorem `coe_nil` / 定理 `coe_nil`

English:
theorem coe_nil
  statement: ↑([] : List α) = @nil α
  proof: rfl

@[simp]

中文:
定理 coe_nil
  结论: ↑([] : 列表 α) = @nil α
  证明: rfl

@[simp]
-/
theorem coe_nil : ↑([] : List α) = @nil α :=
  rfl

@[simp]
/--
theorem `coe_eq_nil` / 定理 `coe_eq_nil`

English:
theorem coe_eq_nil
  given: (l : List α)
  statement: (l : Cycle α) = nil ↔ l = []
  proof: coe_eq_coe.trans isRotated_nil_iff

中文:
定理 coe_eq_nil
  条件: (l : 列表 α)
  结论: (l : 环 α) = nil ↔ l = []
  证明: coe_eq_coe.trans isRotated_nil_iff

Depends on / 依赖: coe_eq_coe, coe_eq_coe.trans, isRotated_nil_iff
-/
theorem coe_eq_nil (l : List α) : (l : Cycle α) = nil ↔ l = [] :=
  coe_eq_coe.trans isRotated_nil_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Cycle α)
  body: ⟨nil⟩

@[simp]

中文:
实例 :
  签名: EmptyCollection (环 α)
  定义体: ⟨nil⟩

@[simp]
-/
instance : EmptyCollection (Cycle α) :=
  ⟨nil⟩

@[simp]
/--
theorem `empty_eq` / 定理 `empty_eq`

English:
theorem empty_eq
  statement: ∅ = @nil α
  proof: rfl

中文:
定理 empty_eq
  结论: ∅ = @nil α
  证明: rfl
-/
theorem empty_eq : ∅ = @nil α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Cycle α)
  body: ⟨nil⟩

中文:
实例 :
  签名: 可居 (环 α)
  定义体: ⟨nil⟩
-/
instance : Inhabited (Cycle α) :=
  ⟨nil⟩

/-- An induction principle for `Cycle`. Use as `induction s`. -/
@[elab_as_elim, induction_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : Cycle α -> Prop} (s : Cycle α) (nil : motive nil)
  proof: Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp only [mk''_eq_coe, coe_nil]
    assumption'

中文:
定理 induction_on
  结论: {motive : 环 α -> 命题} (s : 环 α) (nil : motive nil)
  证明: Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp only [mk''_eq_coe, coe_nil]
    assumption'

Depends on / 依赖: List.recOn, Quotient, Quotient.inductionOn, _eq_coe, coe_nil, inductionOn
-/
theorem induction_on {motive : Cycle α -> Prop} (s : Cycle α) (nil : motive nil)
    (cons : forall (a) (l : List α), motive ↑l -> motive ↑(a :: l)) : motive s :=
  Quotient.inductionOn' s fun l => by
    refine List.recOn l ?_ ?_ <;> simp only [mk''_eq_coe, coe_nil]
    assumption'

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : Cycle α) (a : α)
  body: Quot.liftOn s (fun l => a in l) fun _ _ e => propext e.mem_iff

中文:
定义 Mem
  签名: (s : 环 α) (a : α)
  定义体: Quot.liftOn s (fun l => a in l) fun _ _ e => propext e.mem_iff

Depends on / 依赖: Quot.liftOn, e.mem_iff, liftOn, mem_iff, propext
-/
def Mem (s : Cycle α) (a : α) : Prop :=
Quot.liftOn s (fun l => a in l) fun _ _ e => propext e.mem_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Cycle α)
  body: ⟨Mem⟩

@[simp]

中文:
实例 :
  签名: Membership α (环 α)
  定义体: ⟨Mem⟩

@[simp]
-/
instance : Membership α (Cycle α) :=
  ⟨Mem⟩

@[simp]
/--
theorem `mem_coe_iff` / 定理 `mem_coe_iff`

English:
theorem mem_coe_iff
  given: {a : α} {l : List α}
  statement: a in (↑l : Cycle α) ↔ a in l
  proof: Iff.rfl

@[simp]

中文:
定理 mem_coe_iff
  条件: {a : α} {l : 列表 α}
  结论: a in (↑l : 环 α) ↔ a in l
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe_iff {a : α} {l : List α} : a in (↑l : Cycle α) ↔ a in l :=
  Iff.rfl

@[simp]
/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  given: (a : α)
  statement: a ∉ nil
  proof: List.not_mem_nil

中文:
定理 notMem_nil
  条件: (a : α)
  结论: a ∉ nil
  证明: List.not_mem_nil

Depends on / 依赖: List.not_mem_nil, not_mem_nil
-/
theorem notMem_nil (a : α) : a ∉ nil :=
  List.not_mem_nil

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Cycle α)
  body: fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (环 α)
  定义体: fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''
-/
instance [DecidableEq α] : DecidableEq (Cycle α) := fun s₁ s₂ =>
  Quotient.recOnSubsingleton₂' s₁ s₂ fun _ _ => decidable_of_iff' _ Quotient.eq''

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (x
  body: Quotient.recOnSubsingleton' s fun l => show Decidable (x in l) from inferInstance

中文:
实例 [DecidableEq
  签名: α] (x
  定义体: Quotient.recOnSubsingleton' s fun l => show Decidable (x in l) from inferInstance

Depends on / 依赖: Decidable, Quotient, Quotient.recOnSubsingleton, recOnSubsingleton
-/
instance [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x in s) :=
  Quotient.recOnSubsingleton' s fun l => show Decidable (x in l) from inferInstance

/-- Reverse a `s : Cycle α` by reversing the underlying `List`. -/
nonrec def reverse (s : Cycle α) : Cycle α :=
  Quot.map reverse (fun _ _ => IsRotated.reverse) s

@[simp]
/--
theorem `reverse_coe` / 定理 `reverse_coe`

English:
theorem reverse_coe
  given: (l : List α)
  statement: (l : Cycle α).reverse = l.reverse
  proof: rfl

@[simp]

中文:
定理 reverse_coe
  条件: (l : 列表 α)
  结论: (l : 环 α).reverse = l.reverse
  证明: rfl

@[simp]
-/
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl

@[simp]
/--
theorem `mem_reverse_iff` / 定理 `mem_reverse_iff`

English:
theorem mem_reverse_iff
  given: {a : α} {s : Cycle α}
  statement: a in s.reverse ↔ a in s
  proof: Quot.inductionOn s fun _ => mem_reverse

@[simp]

中文:
定理 mem_reverse_iff
  条件: {a : α} {s : 环 α}
  结论: a in s.reverse ↔ a in s
  证明: Quot.inductionOn s fun _ => mem_reverse

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn, mem_reverse
-/
theorem mem_reverse_iff {a : α} {s : Cycle α} : a in s.reverse ↔ a in s :=
  Quot.inductionOn s fun _ => mem_reverse

@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  given: (s : Cycle α)
  statement: s.reverse.reverse = s
  proof: Quot.inductionOn s fun _ => by simp

@[simp]

中文:
定理 reverse_reverse
  条件: (s : 环 α)
  结论: s.reverse.reverse = s
  证明: Quot.inductionOn s fun _ => by simp

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.inductionOn s fun _ => by simp

@[simp]
/--
theorem `reverse_nil` / 定理 `reverse_nil`

English:
theorem reverse_nil
  statement: nil.reverse = @nil α
  proof: rfl

中文:
定理 reverse_nil
  结论: nil.reverse = @nil α
  证明: rfl
-/
theorem reverse_nil : nil.reverse = @nil α :=
  rfl

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (s : Cycle α)
  body: Quot.liftOn s List.length fun _ _ e => e.perm.length_eq

@[simp]

中文:
定义 length
  签名: (s : 环 α)
  定义体: Quot.liftOn s List.length fun _ _ e => e.perm.length_eq

@[simp]

Depends on / 依赖: List.length, Quot.liftOn, e.perm.length_eq, length, length_eq, liftOn
-/
def length (s : Cycle α) : Nat :=
  Quot.liftOn s List.length fun _ _ e => e.perm.length_eq

@[simp]
/--
theorem `length_coe` / 定理 `length_coe`

English:
theorem length_coe
  given: (l : List α)
  statement: length (l : Cycle α) = l.length
  proof: rfl

@[simp]

中文:
定理 length_coe
  条件: (l : 列表 α)
  结论: length (l : 环 α) = l.length
  证明: rfl

@[simp]
-/
theorem length_coe (l : List α) : length (l : Cycle α) = l.length :=
  rfl

@[simp]
/--
theorem `length_nil` / 定理 `length_nil`

English:
theorem length_nil
  statement: length (@nil α) = 0
  proof: rfl

@[simp]

中文:
定理 length_nil
  结论: length (@nil α) = 0
  证明: rfl

@[simp]
-/
theorem length_nil : length (@nil α) = 0 :=
  rfl

@[simp]
/--
theorem `length_reverse` / 定理 `length_reverse`

English:
theorem length_reverse
  given: (s : Cycle α)
  statement: s.reverse.length = s.length
  proof: Quot.inductionOn s fun _ => List.length_reverse

中文:
定理 length_reverse
  条件: (s : 环 α)
  结论: s.reverse.length = s.length
  证明: Quot.inductionOn s fun _ => List.length_reverse

Depends on / 依赖: List.length_reverse, Quot.inductionOn, inductionOn, length_reverse
-/
theorem length_reverse (s : Cycle α) : s.reverse.length = s.length :=
  Quot.inductionOn s fun _ => List.length_reverse

/--
Definition of `Subsingleton` / `Subsingleton` 的定义

English:
definition Subsingleton
  signature: (s : Cycle α)
  body: s.length <= 1

中文:
定义 子单例
  签名: (s : 环 α)
  定义体: s.length <= 1

Depends on / 依赖: length, s.length
-/
def Subsingleton (s : Cycle α) : Prop :=
  s.length <= 1

/--
theorem `subsingleton_nil` / 定理 `subsingleton_nil`

English:
theorem subsingleton_nil
  statement: Subsingleton (@nil α)
  proof: Nat.zero_le _

中文:
定理 subsingleton_nil
  结论: 子单例 (@nil α)
  证明: Nat.zero_le _

Depends on / 依赖: Nat.zero_le, zero_le
-/
theorem subsingleton_nil : Subsingleton (@nil α) := Nat.zero_le _

/--
theorem `length_subsingleton_iff` / 定理 `length_subsingleton_iff`

English:
theorem length_subsingleton_iff
  given: {s : Cycle α}
  statement: Subsingleton s ↔ length s <= 1
  proof: Iff.rfl

@[simp]

中文:
定理 length_subsingleton_iff
  条件: {s : 环 α}
  结论: 子单例 s ↔ length s <= 1
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s <= 1 :=
  Iff.rfl

@[simp]
/--
theorem `subsingleton_reverse_iff` / 定理 `subsingleton_reverse_iff`

English:
theorem subsingleton_reverse_iff
  given: {s : Cycle α}
  statement: s.reverse.Subsingleton ↔ s.Subsingleton
  proof: by
  simp [length_subsingleton_iff]

中文:
定理 subsingleton_reverse_iff
  条件: {s : 环 α}
  结论: s.reverse.子单例 ↔ s.子单例
  证明: by
  simp [length_subsingleton_iff]

Depends on / 依赖: length_subsingleton_iff
-/
theorem subsingleton_reverse_iff {s : Cycle α} : s.reverse.Subsingleton ↔ s.Subsingleton := by
  simp [length_subsingleton_iff]

/--
theorem `Subsingleton.congr` / 定理 `Subsingleton.congr`

English:
theorem Subsingleton.congr
  given: {s : Cycle α} (h : Subsingleton s)
  proof: by
  induction s using Quot.inductionOn with | _ l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero_iff, length_eq_one_iff, Nat.not_lt_zero, false_or] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp

中文:
定理 子单例.congr
  条件: {s : 环 α} (h : 子单例 s)
  证明: by
  induction s using Quot.inductionOn with | _ l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero_iff, length_eq_one_iff, Nat.not_lt_zero, false_or] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp

Depends on / 依赖: Nat.lt_add_one_iff, Nat.not_lt_zero, Quot.inductionOn, false_or, inductionOn, le_iff_lt_or_eq, length_coe, length_eq_one_iff, length_eq_zero_iff, length_subsingleton_iff, lt_add_one_iff, mk_eq_coe, not_lt_zero
-/
theorem Subsingleton.congr {s : Cycle α} (h : Subsingleton s) :
    forall ⦃x⦄ (_hx : x in s) ⦃y⦄ (_hy : y in s), x = y := by
  induction s using Quot.inductionOn with | _ l
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eq, Nat.lt_add_one_iff,
    length_eq_zero_iff, length_eq_one_iff, Nat.not_lt_zero, false_or] at h
  rcases h with (rfl | ⟨z, rfl⟩) <;> simp

/--
Definition of `Nontrivial` / `Nontrivial` 的定义

English:
definition Nontrivial
  signature: (s : Cycle α)
  body: exists x y : α, x != y ∧ x in s ∧ y in s

@[simp]

中文:
定义 非平凡
  签名: (s : 环 α)
  定义体: exists x y : α, x != y ∧ x in s ∧ y in s

@[simp]
-/
def Nontrivial (s : Cycle α) : Prop :=
  exists x y : α, x != y ∧ x in s ∧ y in s

@[simp]
/--
theorem `nontrivial_coe_nodup_iff` / 定理 `nontrivial_coe_nodup_iff`

English:
theorem nontrivial_coe_nodup_iff
  given: {l : List α} (hl : l.Nodup)
  proof: by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons, mem_coe_iff, List.length, Ne, Nat.succ_le_succ_iff,
      Nat.zero_le, iff_true]
    refine ⟨hd, hd', ?_, by simp⟩
    simp only [not_or, mem_cons, nodup_cons] at hl
    exact hl.left.left

@[simp]

中文:
定理 nontrivial_coe_nodup_iff
  条件: {l : 列表 α} (hl : l.Nodup)
  证明: by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons, mem_coe_iff, List.length, Ne, Nat.succ_le_succ_iff,
      Nat.zero_le, iff_true]
    refine ⟨hd, hd', ?_, by simp⟩
    simp only [not_or, mem_cons, nodup_cons] at hl
    exact hl.left.left

@[simp]

Depends on / 依赖: List.length, Nat.succ_le_succ_iff, Nat.zero_le, Nontrivial, hl.left.left, iff_true, length, mem_coe_iff, mem_cons, nodup_cons, not_or, succ_le_succ_iff, zero_le
-/
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.Nodup) :
    Nontrivial (l : Cycle α) ↔ 2 <= l.length := by
  rw [Nontrivial]
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp
  · simp
  · simp only [mem_cons, mem_coe_iff, List.length, Ne, Nat.succ_le_succ_iff,
      Nat.zero_le, iff_true]
    refine ⟨hd, hd', ?_, by simp⟩
    simp only [not_or, mem_cons, nodup_cons] at hl
    exact hl.left.left

@[simp]
/--
theorem `nontrivial_reverse_iff` / 定理 `nontrivial_reverse_iff`

English:
theorem nontrivial_reverse_iff
  given: {s : Cycle α}
  statement: s.reverse.Nontrivial ↔ s.Nontrivial
  proof: by
  simp [Nontrivial]

中文:
定理 nontrivial_reverse_iff
  条件: {s : 环 α}
  结论: s.reverse.非平凡 ↔ s.非平凡
  证明: by
  simp [Nontrivial]

Depends on / 依赖: Nontrivial
-/
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.Nontrivial ↔ s.Nontrivial := by
  simp [Nontrivial]

/--
theorem `length_nontrivial` / 定理 `length_nontrivial`

English:
theorem length_nontrivial
  given: {s : Cycle α} (h : Nontrivial s)
  statement: 2 <= length s
  proof: by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction s using Quot.inductionOn with | _ l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simp [hx, hy] at hxy
  · simp [Nat.succ_le_succ_iff]

中文:
定理 length_nontrivial
  条件: {s : 环 α} (h : 非平凡 s)
  结论: 2 <= length s
  证明: by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction s using Quot.inductionOn with | _ l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simp [hx, hy] at hxy
  · simp [Nat.succ_le_succ_iff]

Depends on / 依赖: Nat.succ_le_succ_iff, Quot.inductionOn, inductionOn, mem_coe_iff, mem_singleton, mk_eq_coe, succ_le_succ_iff
-/
theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 <= length s := by
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  induction s using Quot.inductionOn with | _ l
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
  · simp at hx
  · simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy
    simp [hx, hy] at hxy
  · simp [Nat.succ_le_succ_iff]

/-- The `s : Cycle α` contains no duplicates. -/
nonrec def Nodup (s : Cycle α) : Prop :=
Quot.liftOn s Nodup fun _l₁ _l₂ e => propext e.nodup_iff

@[simp]
nonrec theorem nodup_nil : Nodup (@nil α) :=
  nodup_nil

@[simp]
/--
theorem `nodup_coe_iff` / 定理 `nodup_coe_iff`

English:
theorem nodup_coe_iff
  given: {l : List α}
  statement: Nodup (l : Cycle α) ↔ l.Nodup
  proof: Iff.rfl

@[simp]

中文:
定理 nodup_coe_iff
  条件: {l : 列表 α}
  结论: Nodup (l : 环 α) ↔ l.Nodup
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ l.Nodup :=
  Iff.rfl

@[simp]
/--
theorem `nodup_reverse_iff` / 定理 `nodup_reverse_iff`

English:
theorem nodup_reverse_iff
  given: {s : Cycle α}
  statement: s.reverse.Nodup ↔ s.Nodup
  proof: Quot.inductionOn s fun _ => nodup_reverse

中文:
定理 nodup_reverse_iff
  条件: {s : 环 α}
  结论: s.reverse.Nodup ↔ s.Nodup
  证明: Quot.inductionOn s fun _ => nodup_reverse

Depends on / 依赖: Quot.inductionOn, inductionOn, nodup_reverse
-/
theorem nodup_reverse_iff {s : Cycle α} : s.reverse.Nodup ↔ s.Nodup :=
  Quot.inductionOn s fun _ => nodup_reverse

/--
theorem `Subsingleton.nodup` / 定理 `Subsingleton.nodup`

English:
theorem Subsingleton.nodup
  given: {s : Cycle α} (h : Subsingleton s)
  statement: Nodup s
  proof: by
  induction s using Quot.inductionOn with | _ l
  obtain - | ⟨hd, tl⟩ := l
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero_iff, Nat.succ_le_succ_iff] using h
    simp [this]

中文:
定理 子单例.nodup
  条件: {s : 环 α} (h : 子单例 s)
  结论: Nodup s
  证明: by
  induction s using Quot.inductionOn with | _ l
  obtain - | ⟨hd, tl⟩ := l
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero_iff, Nat.succ_le_succ_iff] using h
    simp [this]

Depends on / 依赖: Nat.succ_le_succ_iff, Quot.inductionOn, Subsingleton, inductionOn, length_eq_zero_iff, succ_le_succ_iff
-/
theorem Subsingleton.nodup {s : Cycle α} (h : Subsingleton s) : Nodup s := by
  induction s using Quot.inductionOn with | _ l
  obtain - | ⟨hd, tl⟩ := l
  · simp
  · have : tl = [] := by simpa [Subsingleton, length_eq_zero_iff, Nat.succ_le_succ_iff] using h
    simp [this]

/--
theorem `Nodup.nontrivial_iff` / 定理 `Nodup.nontrivial_iff`

English:
theorem Nodup.nontrivial_iff
  given: {s : Cycle α} (h : Nodup s)
  statement: Nontrivial s ↔ ¬Subsingleton s
  proof: by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]

中文:
定理 Nodup.nontrivial_iff
  条件: {s : 环 α} (h : Nodup s)
  结论: 非平凡 s ↔ ¬子单例 s
  证明: by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]

Depends on / 依赖: Nat.succ_le_iff, Quotient, Quotient.inductionOn, _eq_coe, inductionOn, length_subsingleton_iff, nodup_coe_iff, succ_le_iff
-/
theorem Nodup.nontrivial_iff {s : Cycle α} (h : Nodup s) : Nontrivial s ↔ ¬Subsingleton s := by
  rw [length_subsingleton_iff]
  induction s using Quotient.inductionOn'
  simp only [mk''_eq_coe, nodup_coe_iff] at h
  simp [h, Nat.succ_le_iff]

/--
Definition of `toMultiset` / `toMultiset` 的定义

English:
definition toMultiset
  signature: (s : Cycle α)
  body: Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm

@[simp]

中文:
定义 toMultiset
  签名: (s : 环 α)
  定义体: Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm

@[simp]

Depends on / 依赖: Multiset, Multiset.coe_eq_coe.mpr, Quotient, Quotient.liftOn, coe_eq_coe, h.perm, liftOn
-/
def toMultiset (s : Cycle α) : Multiset α :=
  Quotient.liftOn' s (↑) fun _ _ h => Multiset.coe_eq_coe.mpr h.perm

@[simp]
/--
theorem `coe_toMultiset` / 定理 `coe_toMultiset`

English:
theorem coe_toMultiset
  given: (l : List α)
  statement: (l : Cycle α).toMultiset = l
  proof: rfl

@[simp]

中文:
定理 coe_toMultiset
  条件: (l : 列表 α)
  结论: (l : 环 α).toMultiset = l
  证明: rfl

@[simp]
-/
theorem coe_toMultiset (l : List α) : (l : Cycle α).toMultiset = l :=
  rfl

@[simp]
/--
theorem `nil_toMultiset` / 定理 `nil_toMultiset`

English:
theorem nil_toMultiset
  statement: nil.toMultiset = (0 : Multiset α)
  proof: rfl

@[simp]

中文:
定理 nil_toMultiset
  结论: nil.toMultiset = (0 : Multiset α)
  证明: rfl

@[simp]

Depends on / 依赖: insert_nonempty, to_subtype
-/
theorem nil_toMultiset : nil.toMultiset = (0 : Multiset α) :=
  rfl

@[simp]
/--
theorem `card_toMultiset` / 定理 `card_toMultiset`

English:
theorem card_toMultiset
  given: (s : Cycle α)
  statement: Multiset.card s.toMultiset = s.length
  proof: Quotient.inductionOn' s (by simp)

@[simp]

中文:
定理 card_toMultiset
  条件: (s : 环 α)
  结论: Multiset.card s.toMultiset = s.length
  证明: Quotient.inductionOn' s (by simp)

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem card_toMultiset (s : Cycle α) : Multiset.card s.toMultiset = s.length :=
  Quotient.inductionOn' s (by simp)

@[simp]
/--
theorem `toMultiset_eq_nil` / 定理 `toMultiset_eq_nil`

English:
theorem toMultiset_eq_nil
  given: {s : Cycle α}
  statement: s.toMultiset = 0 ↔ s = Cycle.nil
  proof: Quotient.inductionOn' s (by simp)

中文:
定理 toMultiset_eq_nil
  条件: {s : 环 α}
  结论: s.toMultiset = 0 ↔ s = 环.nil
  证明: Quotient.inductionOn' s (by simp)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem toMultiset_eq_nil {s : Cycle α} : s.toMultiset = 0 ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β : Type*} (f : α -> β)
  body: Quotient.map' (List.map f) fun _ _ h => h.map _

@[simp]

中文:
定义 map
  签名: {β : 类型} (f : α -> β)
  定义体: Quotient.map' (List.map f) fun _ _ h => h.map _

@[simp]

Depends on / 依赖: List.map, Quotient, Quotient.map, h.map
-/
def map {β : Type*} (f : α -> β) : Cycle α -> Cycle β :=
  Quotient.map' (List.map f) fun _ _ h => h.map _

@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  given: {β : Type*} (f : α -> β)
  statement: map f nil = nil
  proof: rfl

@[simp]

中文:
定理 map_nil
  条件: {β : 类型} (f : α -> β)
  结论: map f nil = nil
  证明: rfl

@[simp]
-/
theorem map_nil {β : Type*} (f : α -> β) : map f nil = nil :=
  rfl

@[simp]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: {β : Type*} (f : α -> β) (l : List α)
  statement: map f ↑l = List.map f l
  proof: rfl

@[simp]

中文:
定理 map_coe
  条件: {β : 类型} (f : α -> β) (l : 列表 α)
  结论: map f ↑l = 列表.map f l
  证明: rfl

@[simp]
-/
theorem map_coe {β : Type*} (f : α -> β) (l : List α) : map f ↑l = List.map f l :=
  rfl

@[simp]
/--
theorem `map_eq_nil` / 定理 `map_eq_nil`

English:
theorem map_eq_nil
  given: {β : Type*} (f : α -> β) (s : Cycle α)
  statement: map f s = nil ↔ s = nil
  proof: Quotient.inductionOn' s (by simp)

@[simp]

中文:
定理 map_eq_nil
  条件: {β : 类型} (f : α -> β) (s : 环 α)
  结论: map f s = nil ↔ s = nil
  证明: Quotient.inductionOn' s (by simp)

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem map_eq_nil {β : Type*} (f : α -> β) (s : Cycle α) : map f s = nil ↔ s = nil :=
  Quotient.inductionOn' s (by simp)

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {β : Type*} {f : α -> β} {b : β} {s : Cycle α}
  proof: Quotient.inductionOn' s (by simp)

中文:
定理 mem_map
  条件: {β : 类型} {f : α -> β} {b : β} {s : 环 α}
  证明: Quotient.inductionOn' s (by simp)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem mem_map {β : Type*} {f : α -> β} {b : β} {s : Cycle α} :
    b in s.map f ↔ exists a, a in s ∧ f a = b :=
  Quotient.inductionOn' s (by simp)

/--
Definition of `lists` / `lists` 的定义

English:
definition lists
  signature: (s : Cycle α)
  body: Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm

@[simp]

中文:
定义 lists
  签名: (s : 环 α)
  定义体: Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm

@[simp]

Depends on / 依赖: Multiset, Quotient, Quotient.liftOn, cyclicPermutations, h.cyclicPermutations.perm, l.cyclicPermutations, liftOn
-/
def lists (s : Cycle α) : Multiset (List α) :=
  Quotient.liftOn' s (fun l => (l.cyclicPermutations : Multiset (List α))) fun l₁ l₂ h => by
    simpa using h.cyclicPermutations.perm

@[simp]
/--
theorem `lists_coe` / 定理 `lists_coe`

English:
theorem lists_coe
  given: (l : List α)
  statement: lists (l : Cycle α) = ↑l.cyclicPermutations
  proof: rfl

中文:
定理 lists_coe
  条件: (l : 列表 α)
  结论: lists (l : 环 α) = ↑l.cyclicPermutations
  证明: rfl
-/
theorem lists_coe (l : List α) : lists (l : Cycle α) = ↑l.cyclicPermutations :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_lists_iff_coe_eq` / 定理 `mem_lists_iff_coe_eq`

English:
theorem mem_lists_iff_coe_eq
  given: {s : Cycle α} {l : List α}
  statement: l in s.lists ↔ (l : Cycle α) = s
  proof: Quotient.inductionOn' s fun l => by
    rw [lists]; rw [Quotient.liftOn'_mk'']
    simp

@[simp]

中文:
定理 mem_lists_iff_coe_eq
  条件: {s : 环 α} {l : 列表 α}
  结论: l in s.lists ↔ (l : 环 α) = s
  证明: Quotient.inductionOn' s fun l => by
    rw [lists]; rw [Quotient.liftOn'_mk'']
    simp

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.liftOn, inductionOn, liftOn
-/
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l in s.lists ↔ (l : Cycle α) = s :=
  Quotient.inductionOn' s fun l => by
    rw [lists]; rw [Quotient.liftOn'_mk'']
    simp

@[simp]
/--
theorem `lists_nil` / 定理 `lists_nil`

English:
theorem lists_nil
  statement: lists (@nil α) = {([] : List α)}
  proof: by
  rw [nil]; rw [lists_coe]; rw [cyclicPermutations_nil]; rw [Multiset.coe_singleton]

中文:
定理 lists_nil
  结论: lists (@nil α) = {([] : 列表 α)}
  证明: by
  rw [nil]; rw [lists_coe]; rw [cyclicPermutations_nil]; rw [Multiset.coe_singleton]

Depends on / 依赖: Multiset, Multiset.coe_singleton, coe_singleton, cyclicPermutations_nil, lists_coe
-/
theorem lists_nil : lists (@nil α) = {([] : List α)} := by
  rw [nil]; rw [lists_coe]; rw [cyclicPermutations_nil]; rw [Multiset.coe_singleton]

section Decidable

variable [DecidableEq α]

/--
Definition of `decidableNontrivialCoe` / `decidableNontrivialCoe` 的定义

English:
definition decidableNontrivialCoe
  signature: : forall l : List α, Decidable (Nontrivial (l : Cycle α))

中文:
定义 decidableNontrivialCoe
  签名: : 对任意 l : 列表 α, 可判定 (非平凡 (l : 环 α))
-/
def decidableNontrivialCoe : forall l : List α, Decidable (Nontrivial (l : Cycle α))
  | [] => isFalse (by simp [Nontrivial])
  | [x] => isFalse (by simp [Nontrivial])
  | x :: y :: l =>
    if h : x = y then
      @decidable_of_iff' _ (Nontrivial (x :: l : Cycle α)) (by simp [h, Nontrivial])
        (decidableNontrivialCoe (x :: l))
    else isTrue ⟨x, y, h, by simp, by simp⟩

instance {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingleton s decidableNontrivialCoe

instance {s : Cycle α} : Decidable (Nodup s) :=
  Quot.recOnSubsingleton s List.nodupDecidable

/--
Instance `fintypeNodupCycle` / 实例 `fintypeNodupCycle`

English:
instance fintypeNodupCycle
  signature: [Fintype α]
  body: Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction s using Quotient.inductionOn' with | _ hs
    exact ⟨⟨_, hs⟩, by simp⟩

中文:
实例 fintypeNodupCycle
  签名: [有限类型 α]
  定义体: Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction s using Quotient.inductionOn' with | _ hs
    exact ⟨⟨_, hs⟩, by simp⟩

Depends on / 依赖: Fintype, Fintype.ofSurjective, Quotient, Quotient.inductionOn, inductionOn, l.Nodup, l.prop, l.val, ofSurjective
-/
instance fintypeNodupCycle [Fintype α] : Fintype { s : Cycle α // s.Nodup } :=
  Fintype.ofSurjective (fun l : { l : List α // l.Nodup } => ⟨l.val, by simpa using l.prop⟩)
    fun ⟨s, hs⟩ => by
    induction s using Quotient.inductionOn' with | _ hs
    exact ⟨⟨_, hs⟩, by simp⟩

/--
Instance `fintypeNodupNontrivialCycle` / 实例 `fintypeNodupNontrivialCycle`

English:
instance fintypeNodupNontrivialCycle
  signature: [Fintype α]
  body: Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)

中文:
实例 fintypeNodupNontrivialCycle
  签名: [有限类型 α]
  定义体: Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)

Depends on / 依赖: Cycle.Nontrivial, Embedding, Finset, Finset.univ, Fintype, Fintype.subtype, Function, Function.Embedding.subtype, Nontrivial, filter, s.Nodup, subtype
-/
instance fintypeNodupNontrivialCycle [Fintype α] :
    Fintype { s : Cycle α // s.Nodup ∧ s.Nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.Nodup }).map (Function.Embedding.subtype _)).filter
      Cycle.Nontrivial)
    (by simp)

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (s : Cycle α)
  body: s.toMultiset.toFinset

@[simp]

中文:
定义 toFinset
  签名: (s : 环 α)
  定义体: s.toMultiset.toFinset

@[simp]

Depends on / 依赖: s.toMultiset.toFinset, toFinset, toMultiset
-/
def toFinset (s : Cycle α) : Finset α :=
  s.toMultiset.toFinset

@[simp]
/--
theorem `toFinset_toMultiset` / 定理 `toFinset_toMultiset`

English:
theorem toFinset_toMultiset
  given: (s : Cycle α)
  statement: s.toMultiset.toFinset = s.toFinset
  proof: rfl

@[simp]

中文:
定理 toFinset_toMultiset
  条件: (s : 环 α)
  结论: s.toMultiset.toFinset = s.toFinset
  证明: rfl

@[simp]
-/
theorem toFinset_toMultiset (s : Cycle α) : s.toMultiset.toFinset = s.toFinset :=
  rfl

@[simp]
/--
theorem `coe_toFinset` / 定理 `coe_toFinset`

English:
theorem coe_toFinset
  given: (l : List α)
  statement: (l : Cycle α).toFinset = l.toFinset
  proof: rfl

@[simp]

中文:
定理 coe_toFinset
  条件: (l : 列表 α)
  结论: (l : 环 α).toFinset = l.toFinset
  证明: rfl

@[simp]
-/
theorem coe_toFinset (l : List α) : (l : Cycle α).toFinset = l.toFinset :=
  rfl

@[simp]
/--
theorem `nil_toFinset` / 定理 `nil_toFinset`

English:
theorem nil_toFinset
  statement: (@nil α).toFinset = ∅
  proof: rfl

@[simp]

中文:
定理 nil_toFinset
  结论: (@nil α).toFinset = ∅
  证明: rfl

@[simp]
-/
theorem nil_toFinset : (@nil α).toFinset = ∅ :=
  rfl

@[simp]
/--
theorem `toFinset_eq_nil` / 定理 `toFinset_eq_nil`

English:
theorem toFinset_eq_nil
  given: {s : Cycle α}
  statement: s.toFinset = ∅ ↔ s = Cycle.nil
  proof: Quotient.inductionOn' s (by simp)

中文:
定理 toFinset_eq_nil
  条件: {s : 环 α}
  结论: s.toFinset = ∅ ↔ s = 环.nil
  证明: Quotient.inductionOn' s (by simp)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem toFinset_eq_nil {s : Cycle α} : s.toFinset = ∅ ↔ s = Cycle.nil :=
  Quotient.inductionOn' s (by simp)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the next element after `x ∈ s`. -/
nonrec def next : forall (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x in s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => forall (_hs : Cycle.Nodup s) (x : α) (_hx : x in s), α) s
  (fun l _hn x hx => next l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_next_eq h h₁ _)

/-- Given a `s : Cycle α` such that `Nodup s`, retrieve the previous element before `x ∈ s`. -/
nonrec def prev : forall (s : Cycle α) (_hs : Nodup s) (x : α) (_hx : x in s), α := fun s =>
  Quot.hrecOn (motive := fun (s : Cycle α) => forall (_hs : Cycle.Nodup s) (x : α) (_hx : x in s), α) s
  (fun l _hn x hx => prev l x hx) fun l₁ l₂ h =>
    Function.hfunext (propext h.nodup_iff) fun h₁ h₂ _he =>
      Function.hfunext rfl fun x y hxy =>
        Function.hfunext (propext (by rw [eq_of_heq hxy]; simpa [eq_of_heq hxy] using h.mem_iff))
  fun hm hm' he' => heq_of_eq
    (by rw [heq_iff_eq] at hxy; subst x; simpa using isRotated_prev_eq h h₁ _)

-- `simp` cannot infer the proofs: see `prev_reverse_eq_next'` for `@[simp]` lemma.
nonrec theorem prev_reverse_eq_next (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  Quotient.inductionOn' s prev_reverse_eq_next

@[simp]
nonrec theorem prev_reverse_eq_next' (s : Cycle α) (hs : Nodup s.reverse) (x : α)
    (hx : x in s.reverse) :
    s.reverse.prev hs x hx = s.next (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) :=
  prev_reverse_eq_next s (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx)

-- `simp` cannot infer the proofs: see `next_reverse_eq_prev'` for `@[simp]` lemma.
/--
theorem `next_reverse_eq_prev` / 定理 `next_reverse_eq_prev`

English:
theorem next_reverse_eq_prev
  given: (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s)
  proof: by
  simp [← prev_reverse_eq_next]

@[simp]

中文:
定理 next_reverse_eq_prev
  条件: (s : 环 α) (hs : Nodup s) (x : α) (hx : x in s)
  证明: by
  simp [← prev_reverse_eq_next]

@[simp]

Depends on / 依赖: prev_reverse_eq_next
-/
theorem next_reverse_eq_prev (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) :
    s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx := by
  simp [← prev_reverse_eq_next]

@[simp]
/--
theorem `next_reverse_eq_prev'` / 定理 `next_reverse_eq_prev'`

English:
theorem next_reverse_eq_prev'
  given: (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x in s.reverse)
  proof: by
  simp [← prev_reverse_eq_next]

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : s.next hs x hx in s := by
  induction s using Quot.inductionOn
  apply next_mem; assumption

中文:
定理 next_reverse_eq_prev'
  条件: (s : 环 α) (hs : Nodup s.reverse) (x : α) (hx : x in s.reverse)
  证明: by
  simp [← prev_reverse_eq_next]

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : s.next hs x hx in s := by
  induction s using Quot.inductionOn
  apply next_mem; assumption

Depends on / 依赖: prev_reverse_eq_next
-/
theorem next_reverse_eq_prev' (s : Cycle α) (hs : Nodup s.reverse) (x : α) (hx : x in s.reverse) :
    s.reverse.next hs x hx = s.prev (nodup_reverse_iff.mp hs) x (mem_reverse_iff.mp hx) := by
  simp [← prev_reverse_eq_next]

@[simp]
nonrec theorem next_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : s.next hs x hx in s := by
  induction s using Quot.inductionOn
  apply next_mem; assumption

/--
theorem `prev_mem` / 定理 `prev_mem`

English:
theorem prev_mem
  given: (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s)
  statement: s.prev hs x hx in s
  proof: by
  rw [← next_reverse_eq_prev]; rw [← mem_reverse_iff]
  apply next_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev

中文:
定理 prev_mem
  条件: (s : 环 α) (hs : Nodup s) (x : α) (hx : x in s)
  结论: s.prev hs x hx in s
  证明: by
  rw [← next_reverse_eq_prev]; rw [← mem_reverse_iff]
  apply next_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev

Depends on / 依赖: mem_reverse_iff, next_mem, next_reverse_eq_prev
-/
theorem prev_mem (s : Cycle α) (hs : Nodup s) (x : α) (hx : x in s) : s.prev hs x hx in s := by
  rw [← next_reverse_eq_prev]; rw [← mem_reverse_iff]
  apply next_mem

@[simp]
nonrec theorem prev_next (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  Quotient.inductionOn' s prev_next

@[simp]
nonrec theorem next_prev (s : Cycle α) : forall (hs : Nodup s) (x : α) (hx : x in s),
    s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  Quotient.inductionOn' s next_prev

end Decidable

/-- We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representable types. For example, the cycle `(2 1 4 3)` will be shown
as `c[2, 1, 4, 3]`. Two equal cycles may be printed differently if their internal representation
is different.
-/
unsafe instance [Repr α] : Repr (Cycle α) :=
  ⟨fun s _ => "c[" ++ Std.Format.joinSep (s.map repr).lists.unquot.head! ", " ++ "]"⟩

/-- `chain R s` means that `R` holds between adjacent elements of `s`.

`chain R ([a, b, c] : Cycle α) ↔ R a b ∧ R b c ∧ R c a` -/
nonrec def Chain (r : α -> α -> Prop) (c : Cycle α) : Prop :=
  Quotient.liftOn' c
    (fun l =>
      match l with
      | [] => True
      | a :: m => IsChain r (a :: m ++ [a]))
    fun a b hab =>
propext by
      rcases a with - | ⟨a, l⟩ <;> rcases b with - | ⟨b, m⟩
      · rfl
      · have := isRotated_nil_iff'.1 hab
        contradiction
      · have := isRotated_nil_iff.1 hab
        contradiction
      · dsimp only
        obtain ⟨n, hn⟩ := hab
        induction n generalizing a b l m with
        | zero =>
          simp only [rotate_zero, cons.injEq] at hn
          rw [hn.1]; rw [hn.2]
        | succ d hd =>
          rcases l with - | ⟨c, s⟩
          · simp only [rotate_cons_succ, nil_append, rotate_singleton, cons.injEq] at hn
            rw [hn.1]; rw [hn.2]
          · rw [Nat.add_comm, ← rotate_rotate, rotate_cons_succ, rotate_zero, cons_append] at hn
            rw [← hd c _ _ _ hn]
            simp [and_comm]

@[simp]
/--
theorem `Chain.nil` / 定理 `Chain.nil`

English:
theorem Chain.nil
  given: (r : α -> α -> Prop)
  statement: Cycle.Chain r (@nil α)
  proof: by trivial

@[simp]

中文:
定理 链.nil
  条件: (r : α -> α -> 命题)
  结论: 环.链 r (@nil α)
  证明: by trivial

@[simp]
-/
theorem Chain.nil (r : α -> α -> Prop) : Cycle.Chain r (@nil α) := by trivial

@[simp]
/--
theorem `chain_coe_cons` / 定理 `chain_coe_cons`

English:
theorem chain_coe_cons
  given: (r : α -> α -> Prop) (a : α) (l : List α)
  proof: Iff.rfl

中文:
定理 chain_coe_cons
  条件: (r : α -> α -> 命题) (a : α) (l : 列表 α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem chain_coe_cons (r : α -> α -> Prop) (a : α) (l : List α) :
    Chain r (a :: l) ↔ List.IsChain r (a :: (l ++ [a])) :=
  Iff.rfl

/--
theorem `chain_singleton` / 定理 `chain_singleton`

English:
theorem chain_singleton
  given: (r : α -> α -> Prop) (a : α)
  statement: Chain r [a] ↔ r a a
  proof: by
  rw [chain_coe_cons]; rw [nil_append]; rw [List.isChain_pair]

中文:
定理 chain_singleton
  条件: (r : α -> α -> 命题) (a : α)
  结论: 链 r [a] ↔ r a a
  证明: by
  rw [chain_coe_cons]; rw [nil_append]; rw [List.isChain_pair]

Depends on / 依赖: List.isChain_pair, chain_coe_cons, isChain_pair, nil_append
-/
theorem chain_singleton (r : α -> α -> Prop) (a : α) : Chain r [a] ↔ r a a := by
  rw [chain_coe_cons]; rw [nil_append]; rw [List.isChain_pair]

/--
theorem `chain_ne_nil` / 定理 `chain_ne_nil`

English:
theorem chain_ne_nil
  given: (r : α -> α -> Prop) {l : List α}
  proof: l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [getLast_append_singleton])

中文:
定理 chain_ne_nil
  条件: (r : α -> α -> 命题) {l : 列表 α}
  证明: l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [getLast_append_singleton])

Depends on / 依赖: chain_coe_cons, coe_cons_eq_coe_append, getLast_append_singleton, hm.irrefl.elim, irrefl, l.reverseRecOn, reverseRecOn
-/
theorem chain_ne_nil (r : α -> α -> Prop) {l : List α} :
    forall hl : l != [], Chain r l ↔ List.IsChain r (getLast l hl :: l) :=
  l.reverseRecOn (fun hm => hm.irrefl.elim) (by
    intro m a _H _
    rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [getLast_append_singleton])

/--
theorem `chain_map` / 定理 `chain_map`

English:
theorem chain_map
  given: {β : Type*} {r : α -> α -> Prop} (f : β -> α) {s : Cycle β}
  proof: Quotient.inductionOn s fun l => by
    rcases l with - | ⟨a, l⟩
    · rfl
    · simp [← concat_eq_append, ← map_concat, List.isChain_cons_map f]

中文:
定理 chain_map
  条件: {β : 类型} {r : α -> α -> 命题} (f : β -> α) {s : 环 β}
  证明: Quotient.inductionOn s fun l => by
    rcases l with - | ⟨a, l⟩
    · rfl
    · simp [← concat_eq_append, ← map_concat, List.isChain_cons_map f]

Depends on / 依赖: List.isChain_cons_map, Quotient, Quotient.inductionOn, concat_eq_append, inductionOn, isChain_cons_map, map_concat
-/
theorem chain_map {β : Type*} {r : α -> α -> Prop} (f : β -> α) {s : Cycle β} :
    Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s :=
  Quotient.inductionOn s fun l => by
    rcases l with - | ⟨a, l⟩
    · rfl
    · simp [← concat_eq_append, ← map_concat, List.isChain_cons_map f]

/--
theorem `chain_range_succ` / 定理 `chain_range_succ`

English:
theorem chain_range_succ
  given: (r : Nat -> Nat -> Prop) (n : Nat)
  proof: by
  rw [range_succ]; rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [← range_succ]; rw [isChain_cons_range_succ]

中文:
定理 chain_range_succ
  条件: (r : 自然数 -> 自然数 -> 命题) (n : 自然数)
  证明: by
  rw [range_succ]; rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [← range_succ]; rw [isChain_cons_range_succ]

Depends on / 依赖: chain_coe_cons, coe_cons_eq_coe_append, isChain_cons_range_succ, range_succ
-/
theorem chain_range_succ (r : Nat -> Nat -> Prop) (n : Nat) :
    Chain r (List.range n.succ) ↔ r n 0 ∧ forall m < n, r m m.succ := by
  rw [range_succ]; rw [← coe_cons_eq_coe_append]; rw [chain_coe_cons]; rw [← range_succ]; rw [isChain_cons_range_succ]

variable {r : α -> α -> Prop} {s : Cycle α}

/--
theorem `Chain.imp` / 定理 `Chain.imp`

English:
theorem Chain.imp
  given: {r₁ r₂ : α -> α -> Prop} (H : forall a b, r₁ a b -> r₂ a b) (p : Chain r₁ s)
  proof: by
  induction s
  · trivial
  · rw [chain_coe_cons] at p ⊢
    exact p.imp H

中文:
定理 链.imp
  条件: {r₁ r₂ : α -> α -> 命题} (H : 对任意 a b, r₁ a b -> r₂ a b) (p : 链 r₁ s)
  证明: by
  induction s
  · trivial
  · rw [chain_coe_cons] at p ⊢
    exact p.imp H

Depends on / 依赖: chain_coe_cons, p.imp
-/
theorem Chain.imp {r₁ r₂ : α -> α -> Prop} (H : forall a b, r₁ a b -> r₂ a b) (p : Chain r₁ s) :
    Chain r₂ s := by
  induction s
  · trivial
  · rw [chain_coe_cons] at p ⊢
    exact p.imp H

/--
theorem `chain_mono` / 定理 `chain_mono`

English:
theorem chain_mono
  statement: Monotone (Chain : (α -> α -> Prop) -> Cycle α -> Prop)
  proof: fun _a _b hab _s =>
  Chain.imp hab

中文:
定理 chain_mono
  结论: 递增 (链 : (α -> α -> 命题) -> 环 α -> 命题)
  证明: fun _a _b hab _s =>
  Chain.imp hab
-/
theorem chain_mono : Monotone (Chain : (α -> α -> Prop) -> Cycle α -> Prop) := fun _a _b hab _s =>
  Chain.imp hab

/--
theorem `chain_of_pairwise` / 定理 `chain_of_pairwise`

English:
theorem chain_of_pairwise
  statement: (forall a in s, forall b in s, r a b) -> Chain r s
  proof: by
  induction s with
  | nil => exact fun _ => Cycle.Chain.nil r
  | cons a l => ?_
  intro hs
  have Ha : a in (a :: l : Cycle α) := by simp
  have Hl : forall {b} (_hb : b in l), b in (a :: l : Cycle α) := @fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply Pairwise.isChain
  rw [pairwise_cons]
  exact
    ⟨fun b hb => by grind,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => by grind⟩⟩

中文:
定理 chain_of_pairwise
  结论: (对任意 a in s, 对任意 b in s, r a b) -> 链 r s
  证明: by
  induction s with
  | nil => exact fun _ => Cycle.Chain.nil r
  | cons a l => ?_
  intro hs
  have Ha : a in (a :: l : Cycle α) := by simp
  have Hl : forall {b} (_hb : b in l), b in (a :: l : Cycle α) := @fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply Pairwise.isChain
  rw [pairwise_cons]
  exact
    ⟨fun b hb => by grind,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => by grind⟩⟩

Depends on / 依赖: Cycle.Chain.nil, Cycle.chain_coe_cons, Pairwise, Pairwise.isChain, chain_coe_cons, isChain, pairwise_append, pairwise_cons, pairwise_of_forall_mem_list, pairwise_singleton
-/
theorem chain_of_pairwise : (forall a in s, forall b in s, r a b) -> Chain r s := by
  induction s with
  | nil => exact fun _ => Cycle.Chain.nil r
  | cons a l => ?_
  intro hs
  have Ha : a in (a :: l : Cycle α) := by simp
  have Hl : forall {b} (_hb : b in l), b in (a :: l : Cycle α) := @fun b hb => by simp [hb]
  rw [Cycle.chain_coe_cons]
  apply Pairwise.isChain
  rw [pairwise_cons]
  exact
    ⟨fun b hb => by grind,
      pairwise_append.2
        ⟨pairwise_of_forall_mem_list fun b hb c hc => hs b (Hl hb) c (Hl hc),
          pairwise_singleton r a, fun b hb c hc => by grind⟩⟩

/--
theorem `chain_iff_pairwise` / 定理 `chain_iff_pairwise`

English:
theorem chain_iff_pairwise
  given: [IsTrans α r]
  statement: Chain r s ↔ forall a in s, forall b in s, r a b
  proof: ⟨by
    induction s with
    | nil => exact fun _ b hb => (notMem_nil _ hb).elim
    | cons a l => ?_
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons]; rw [List.isChain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩

中文:
定理 chain_iff_pairwise
  条件: [是Trans α r]
  结论: 链 r s ↔ 对任意 a in s, 对任意 b in s, r a b
  证明: ⟨by
    induction s with
    | nil => exact fun _ b hb => (notMem_nil _ hb).elim
    | cons a l => ?_
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons]; rw [List.isChain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩

Depends on / 依赖: Cycle.chain_coe_cons, IsEmpty, IsEmpty.forall_iff, List.isChain_iff_pairwise, List.not_mem_nil, Or.inl, Or.inr, Pairwise, Pairwise.nil, chain_coe_cons, forall_eq, forall_iff, imp_true_iff, isChain_iff_pairwise, mem_append, mem_coe_iff, mem_cons, mem_singleton, notMem_nil, not_mem_nil
-/
theorem chain_iff_pairwise [IsTrans α r] : Chain r s ↔ forall a in s, forall b in s, r a b :=
  ⟨by
    induction s with
    | nil => exact fun _ b hb => (notMem_nil _ hb).elim
    | cons a l => ?_
    intro hs b hb c hc
    rw [Cycle.chain_coe_cons]; rw [List.isChain_iff_pairwise] at hs
    simp only [pairwise_append, pairwise_cons, mem_append, mem_singleton, List.not_mem_nil,
      IsEmpty.forall_iff, imp_true_iff, Pairwise.nil, forall_eq, true_and] at hs
    simp only [mem_coe_iff, mem_cons] at hb hc
    rcases hb with (rfl | hb) <;> rcases hc with (rfl | hc)
    · exact hs.1 c (Or.inr rfl)
    · exact hs.1 c (Or.inl hc)
    · exact hs.2.2 b hb
    · exact _root_.trans (hs.2.2 b hb) (hs.1 c (Or.inl hc)), Cycle.chain_of_pairwise⟩

/--
theorem `Chain.eq_nil_of_irrefl` / 定理 `Chain.eq_nil_of_irrefl`

English:
theorem Chain.eq_nil_of_irrefl
  given: [IsTrans α r] [Std.Irrefl r] (h : Chain r s)
  statement: s = Cycle.nil
  proof: by
  induction s with
  | nil => rfl
  | cons a l h =>
    have ha : a in a :: l := mem_cons_self
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim

中文:
定理 链.eq_nil_of_irrefl
  条件: [是Trans α r] [Std.Irrefl r] (h : 链 r s)
  结论: s = 环.nil
  证明: by
  induction s with
  | nil => rfl
  | cons a l h =>
    have ha : a in a :: l := mem_cons_self
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim

Depends on / 依赖: chain_iff_pairwise, irrefl_of, mem_cons_self
-/
theorem Chain.eq_nil_of_irrefl [IsTrans α r] [Std.Irrefl r] (h : Chain r s) : s = Cycle.nil := by
  induction s with
  | nil => rfl
  | cons a l h =>
    have ha : a in a :: l := mem_cons_self
    exact (irrefl_of r a <| chain_iff_pairwise.1 h a ha a ha).elim

/--
theorem `Chain.eq_nil_of_well_founded` / 定理 `Chain.eq_nil_of_well_founded`

English:
theorem Chain.eq_nil_of_well_founded
  given: [IsWellFounded α r] (h : Chain r s)
  statement: s = Cycle.nil
  proof: Chain.eq_nil_of_irrefl h.imp fun _ _ => Relation.TransGen.single

中文:
定理 链.eq_nil_of_well_founded
  条件: [是良基 α r] (h : 链 r s)
  结论: s = 环.nil
  证明: Chain.eq_nil_of_irrefl h.imp fun _ _ => Relation.TransGen.single

Depends on / 依赖: Chain.eq_nil_of_irrefl, Relation, Relation.TransGen.single, TransGen, eq_nil_of_irrefl, h.imp, single
-/
theorem Chain.eq_nil_of_well_founded [IsWellFounded α r] (h : Chain r s) : s = Cycle.nil :=
Chain.eq_nil_of_irrefl h.imp fun _ _ => Relation.TransGen.single

/--
theorem `forall_eq_of_chain` / 定理 `forall_eq_of_chain`

English:
theorem forall_eq_of_chain
  statement: [IsTrans α r] [Std.Antisymm r] (hs : Chain r s) {a b : α} (ha : a in s)
  proof: by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)

中文:
定理 对任意_eq_of_chain
  结论: [是Trans α r] [Std.反对称 r] (hs : 链 r s) {a b : α} (ha : a in s)
  证明: by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)

Depends on / 依赖: antisymm, chain_iff_pairwise
-/
theorem forall_eq_of_chain [IsTrans α r] [Std.Antisymm r] (hs : Chain r s) {a b : α} (ha : a in s)
    (hb : b in s) : a = b := by
  rw [chain_iff_pairwise] at hs
  exact antisymm (hs a ha b hb) (hs b hb a ha)

end Cycle
