/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common

/-!
# Map₂ Lemmas

This file contains additional lemmas about a number of list functions related to combining zipping
Lists together. In particular, we include lemmas about:

* `map₂Left'`
* `map₂Right'`
* `zipWith`
* `zipLeft'`
* `zipRight'`

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

/-! ### map₂Left' -/

section Map₂Left'

-- The definitional equalities for `map₂Left'` can already be used by the
-- simplifier because `map₂Left'` is marked `@[simp]`.
@[simp]
/--
theorem `map₂Left'_nil_right` / 定理 `map₂Left'_nil_right`

English:
theorem map₂Left'_nil_right
  given: (f : α -> Option β -> γ) (as)
  proof: by cases as <;> rfl

中文:
定理 map₂Left'_nil_right
  条件: (f : α -> Option β -> γ) (as)
  证明: by cases as <;> rfl
-/
theorem map₂Left'_nil_right (f : α -> Option β -> γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl

end Map₂Left'

/-! ### map₂Right' -/

section Map₂Right'

variable (f : Option α -> β -> γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `map₂Right'_nil_left` / 定理 `map₂Right'_nil_left`

English:
theorem map₂Right'_nil_left
  statement: map₂Right' f [] bs = (bs.map (f none), [])
  proof: by cases bs <;> rfl

@[simp]

中文:
定理 map₂Right'_nil_left
  结论: map₂Right' f [] bs = (bs.map (f none), [])
  证明: by cases bs <;> rfl

@[simp]
-/
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl

@[simp]
/--
theorem `map₂Right'_nil_right` / 定理 `map₂Right'_nil_right`

English:
theorem map₂Right'_nil_right
  statement: map₂Right' f as [] = ([], as)
  proof: rfl

@[simp]

中文:
定理 map₂Right'_nil_right
  结论: map₂Right' f as [] = ([], as)
  证明: rfl

@[simp]
-/
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl

@[simp]
/--
theorem `map₂Right'_nil_cons` / 定理 `map₂Right'_nil_cons`

English:
theorem map₂Right'_nil_cons
  statement: map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), [])
  proof: rfl

@[simp]

中文:
定理 map₂Right'_nil_cons
  结论: map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), [])
  证明: rfl

@[simp]
-/
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl

@[simp]
/--
theorem `map₂Right'_cons_cons` / 定理 `map₂Right'_cons_cons`

English:
theorem map₂Right'_cons_cons
  proof: map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl

中文:
定理 map₂Right'_cons_cons
  证明: map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl
-/
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let r := map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl

end Map₂Right'


/--
theorem `nil_zipWith` / 定理 `nil_zipWith`

English:
theorem nil_zipWith
  given: (f : α -> β -> γ) (l : List β)
  statement: zipWith f [] l = []
  proof: by cases l <;> rfl

中文:
定理 nil_zipWith
  条件: (f : α -> β -> γ) (l : List β)
  结论: zipWith f [] l = []
  证明: by cases l <;> rfl
-/
theorem nil_zipWith (f : α -> β -> γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl

/--
theorem `zipWith_nil` / 定理 `zipWith_nil`

English:
theorem zipWith_nil
  given: (f : α -> β -> γ) (l : List α)
  statement: zipWith f l [] = []
  proof: by cases l <;> rfl

@[simp]

中文:
定理 zipWith_nil
  条件: (f : α -> β -> γ) (l : List α)
  结论: zipWith f l [] = []
  证明: by cases l <;> rfl

@[simp]
-/
theorem zipWith_nil (f : α -> β -> γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl

@[simp]
/--
theorem `zipWith_flip` / 定理 `zipWith_flip`

English:
theorem zipWith_flip
  given: (f : α -> β -> γ)
  statement: forall as bs, zipWith (flip f) bs as = zipWith f as bs

中文:
定理 zipWith_flip
  条件: (f : α -> β -> γ)
  结论: 对任意 as bs, zipWith (flip f) bs as = zipWith f as bs
-/
theorem zipWith_flip (f : α -> β -> γ) : forall as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp! [zipWith_flip]
    rfl


/-! ### zipLeft' -/

section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `zipLeft'_nil_right` / 定理 `zipLeft'_nil_right`

English:
theorem zipLeft'_nil_right
  statement: zipLeft' as ([] : List β) = (as.map fun a => (a, none), [])
  proof: by
  cases as <;> rfl

@[simp]

中文:
定理 zipLeft'_nil_right
  结论: zipLeft' as ([] : List β) = (as.map fun a => (a, none), [])
  证明: by
  cases as <;> rfl

@[simp]
-/
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl

@[simp]
/--
theorem `zipLeft'_nil_left` / 定理 `zipLeft'_nil_left`

English:
theorem zipLeft'_nil_left
  statement: zipLeft' ([] : List α) bs = ([], bs)
  proof: rfl

@[simp]

中文:
定理 zipLeft'_nil_left
  结论: zipLeft' ([] : List α) bs = ([], bs)
  证明: rfl

@[simp]
-/
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl

@[simp]
/--
theorem `zipLeft'_cons_nil` / 定理 `zipLeft'_cons_nil`

English:
theorem zipLeft'_cons_nil
  proof: rfl

@[simp]

中文:
定理 zipLeft'_cons_nil
  证明: rfl

@[simp]
-/
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl

@[simp]
/--
theorem `zipLeft'_cons_cons` / 定理 `zipLeft'_cons_cons`

English:
theorem zipLeft'_cons_cons
  proof: zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl

中文:
定理 zipLeft'_cons_cons
  证明: zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl
-/
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let r := zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl

end ZipLeft'

/-! ### zipRight' -/

section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `zipRight'_nil_left` / 定理 `zipRight'_nil_left`

English:
theorem zipRight'_nil_left
  statement: zipRight' ([] : List α) bs = (bs.map fun b => (none, b), [])
  proof: by
  cases bs <;> rfl

@[simp]

中文:
定理 zipRight'_nil_left
  结论: zipRight' ([] : List α) bs = (bs.map fun b => (none, b), [])
  证明: by
  cases bs <;> rfl

@[simp]
-/
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl

@[simp]
/--
theorem `zipRight'_nil_right` / 定理 `zipRight'_nil_right`

English:
theorem zipRight'_nil_right
  statement: zipRight' as ([] : List β) = ([], as)
  proof: rfl

@[simp]

中文:
定理 zipRight'_nil_right
  结论: zipRight' as ([] : List β) = ([], as)
  证明: rfl

@[simp]
-/
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl

@[simp]
/--
theorem `zipRight'_nil_cons` / 定理 `zipRight'_nil_cons`

English:
theorem zipRight'_nil_cons
  proof: rfl

@[simp]

中文:
定理 zipRight'_nil_cons
  证明: rfl

@[simp]
-/
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl

@[simp]
/--
theorem `zipRight'_cons_cons` / 定理 `zipRight'_cons_cons`

English:
theorem zipRight'_cons_cons
  proof: zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl

中文:
定理 zipRight'_cons_cons
  证明: zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl
-/
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let r := zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl

end ZipRight'

/-! ### map₂Left -/

section Map₂Left

variable (f : α -> Option β -> γ) (as : List α)

-- The definitional equalities for `map₂Left` can already be used by the
-- simplifier because `map₂Left` is marked `@[simp]`.
@[simp]
/--
theorem `map₂Left_nil_right` / 定理 `map₂Left_nil_right`

English:
theorem map₂Left_nil_right
  statement: map₂Left f as [] = as.map fun a => f a none
  proof: by cases as <;> rfl

中文:
定理 map₂Left_nil_right
  结论: map₂Left f as [] = as.map fun a => f a none
  证明: by cases as <;> rfl
-/
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl

/--
theorem `map₂Left_eq_map₂Left'` / 定理 `map₂Left_eq_map₂Left'`

English:
theorem map₂Left_eq_map₂Left'
  statement: forall as bs, map₂Left f as bs = (map₂Left' f as bs).fst

中文:
定理 map₂Left_eq_map₂Left'
  结论: 对任意 as bs, map₂Left f as bs = (map₂Left' f as bs).fst
-/
theorem map₂Left_eq_map₂Left' : forall as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], _ => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by simp [map₂Left_eq_map₂Left']

/--
theorem `map₂Left_eq_zipWith` / 定理 `map₂Left_eq_zipWith`

English:
theorem map₂Left_eq_zipWith

中文:
定理 map₂Left_eq_zipWith
-/
theorem map₂Left_eq_zipWith :
    forall as bs, length as <= length bs -> map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | a :: as, [], h => by
    simp at h
  | a :: as, b :: bs, h => by
    simp only [length_cons, succ_le_succ_iff] at h
    simp [h, map₂Left_eq_zipWith]

end Map₂Left

/-! ### map₂Right -/

section Map₂Right

variable (f : Option α -> β -> γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `map₂Right_nil_left` / 定理 `map₂Right_nil_left`

English:
theorem map₂Right_nil_left
  statement: map₂Right f [] bs = bs.map (f none)
  proof: by cases bs <;> rfl

@[simp]

中文:
定理 map₂Right_nil_left
  结论: map₂Right f [] bs = bs.map (f none)
  证明: by cases bs <;> rfl

@[simp]
-/
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl

@[simp]
/--
theorem `map₂Right_nil_right` / 定理 `map₂Right_nil_right`

English:
theorem map₂Right_nil_right
  statement: map₂Right f as [] = []
  proof: rfl

@[simp]

中文:
定理 map₂Right_nil_right
  结论: map₂Right f as [] = []
  证明: rfl

@[simp]
-/
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl

@[simp]
/--
theorem `map₂Right_nil_cons` / 定理 `map₂Right_nil_cons`

English:
theorem map₂Right_nil_cons
  statement: map₂Right f [] (b :: bs) = f none b :: bs.map (f none)
  proof: rfl

@[simp]

中文:
定理 map₂Right_nil_cons
  结论: map₂Right f [] (b :: bs) = f none b :: bs.map (f none)
  证明: rfl

@[simp]
-/
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl

@[simp]
/--
theorem `map₂Right_cons_cons` / 定理 `map₂Right_cons_cons`

English:
theorem map₂Right_cons_cons
  proof: rfl

中文:
定理 map₂Right_cons_cons
  证明: rfl
-/
theorem map₂Right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl

/--
theorem `map₂Right_eq_map₂Right'` / 定理 `map₂Right_eq_map₂Right'`

English:
theorem map₂Right_eq_map₂Right'
  statement: map₂Right f as bs = (map₂Right' f as bs).fst
  proof: by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']

中文:
定理 map₂Right_eq_map₂Right'
  结论: map₂Right f as bs = (map₂Right' f as bs).fst
  证明: by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']
-/
theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']

/--
theorem `map₂Right_eq_zipWith` / 定理 `map₂Right_eq_zipWith`

English:
theorem map₂Right_eq_zipWith
  given: (h : length bs <= length as)
  proof: by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]

中文:
定理 map₂Right_eq_zipWith
  条件: (h : length bs <= length as)
  证明: by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]

Depends on / 依赖: zipWith_flip
-/
theorem map₂Right_eq_zipWith (h : length bs <= length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]

end Map₂Right

/-! ### zipLeft -/

section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `zipLeft_nil_right` / 定理 `zipLeft_nil_right`

English:
theorem zipLeft_nil_right
  statement: zipLeft as ([] : List β) = as.map fun a => (a, none)
  proof: by
  cases as <;> rfl

@[simp]

中文:
定理 zipLeft_nil_right
  结论: zipLeft as ([] : List β) = as.map fun a => (a, none)
  证明: by
  cases as <;> rfl

@[simp]
-/
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl

@[simp]
/--
theorem `zipLeft_nil_left` / 定理 `zipLeft_nil_left`

English:
theorem zipLeft_nil_left
  statement: zipLeft ([] : List α) bs = []
  proof: rfl

@[simp]

中文:
定理 zipLeft_nil_left
  结论: zipLeft ([] : List α) bs = []
  证明: rfl

@[simp]
-/
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl

@[simp]
/--
theorem `zipLeft_cons_nil` / 定理 `zipLeft_cons_nil`

English:
theorem zipLeft_cons_nil
  proof: rfl

@[simp]

中文:
定理 zipLeft_cons_nil
  证明: rfl

@[simp]
-/
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl

@[simp]
/--
theorem `zipLeft_cons_cons` / 定理 `zipLeft_cons_cons`

English:
theorem zipLeft_cons_cons
  statement: zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs
  proof: rfl

中文:
定理 zipLeft_cons_cons
  结论: zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs
  证明: rfl
-/
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl

/--
theorem `zipLeft_eq_zipLeft'` / 定理 `zipLeft_eq_zipLeft'`

English:
theorem zipLeft_eq_zipLeft'
  given: (as : List α) (bs : List β)
  statement: zipLeft as bs = (zipLeft' as bs).fst
  proof: by
  rw [zipLeft]; rw [zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl =>
      rw [zipWithLeft]; rw [zipWithLeft']; rw [cons_inj_right]
      exact zipLeft_eq_zipLeft' atl btl

中文:
定理 zipLeft_eq_zipLeft'
  条件: (as : List α) (bs : List β)
  结论: zipLeft as bs = (zipLeft' as bs).fst
  证明: by
  rw [zipLeft]; rw [zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl =>
      rw [zipWithLeft]; rw [zipWithLeft']; rw [cons_inj_right]
      exact zipLeft_eq_zipLeft' atl btl

Depends on / 依赖: cons_inj_right, zipLeft, zipLeft_eq_zipLeft, zipWithLeft
-/
theorem zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft' as bs).fst := by
  rw [zipLeft]; rw [zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl =>
      rw [zipWithLeft]; rw [zipWithLeft']; rw [cons_inj_right]
      exact zipLeft_eq_zipLeft' atl btl

end ZipLeft

/-! ### zipRight -/

section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
/--
theorem `zipRight_nil_left` / 定理 `zipRight_nil_left`

English:
theorem zipRight_nil_left
  statement: zipRight ([] : List α) bs = bs.map fun b => (none, b)
  proof: by
  cases bs <;> rfl

@[simp]

中文:
定理 zipRight_nil_left
  结论: zipRight ([] : List α) bs = bs.map fun b => (none, b)
  证明: by
  cases bs <;> rfl

@[simp]
-/
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl

@[simp]
/--
theorem `zipRight_nil_right` / 定理 `zipRight_nil_right`

English:
theorem zipRight_nil_right
  statement: zipRight as ([] : List β) = []
  proof: rfl

@[simp]

中文:
定理 zipRight_nil_right
  结论: zipRight as ([] : List β) = []
  证明: rfl

@[simp]
-/
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl

@[simp]
/--
theorem `zipRight_nil_cons` / 定理 `zipRight_nil_cons`

English:
theorem zipRight_nil_cons
  proof: rfl

@[simp]

中文:
定理 zipRight_nil_cons
  证明: rfl

@[simp]
-/
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl

@[simp]
/--
theorem `zipRight_cons_cons` / 定理 `zipRight_cons_cons`

English:
theorem zipRight_cons_cons
  statement: zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs
  proof: rfl

中文:
定理 zipRight_cons_cons
  结论: zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs
  证明: rfl
-/
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl

/--
theorem `zipRight_eq_zipRight'` / 定理 `zipRight_eq_zipRight'`

English:
theorem zipRight_eq_zipRight'
  statement: zipRight as bs = (zipRight' as bs).fst
  proof: by
  induction as generalizing bs <;> cases bs <;> simp [*]

中文:
定理 zipRight_eq_zipRight'
  结论: zipRight as bs = (zipRight' as bs).fst
  证明: by
  induction as generalizing bs <;> cases bs <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  induction as generalizing bs <;> cases bs <;> simp [*]

end ZipRight

end List
