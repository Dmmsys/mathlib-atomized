/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.InsertIdx
public import Mathlib.Data.List.Induction
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Finiteness.Attr

/-!
# Permutations of a list

In this file we prove properties about `List.Permutations`, a list of all permutations of a list. It
is defined in `Data.List.Defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `List.Permutations` is
rather intricate and not very amenable to induction. That's why we also provide `List.Permutations'`
as a less efficient but more straightforward way of listing permutations.

### `List.Permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `List.Permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat Function

variable {α β : Type*}

namespace List

/--
theorem `permutationsAux2_fst` / 定理 `permutationsAux2_fst`

English:
theorem permutationsAux2_fst
  given: (t : α) (ts : List α) (r : List β)

中文:
定理 permutationsAux2_fst
  条件: (t : α) (ts : 列表 α) (r : 列表 β)
-/
theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    forall (ys : List α) (f : List α -> β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], _ => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

@[simp]
/--
theorem `permutationsAux2_snd_nil` / 定理 `permutationsAux2_snd_nil`

English:
theorem permutationsAux2_snd_nil
  given: (t : α) (ts : List α) (r : List β) (f : List α -> β)
  proof: rfl

@[simp]

中文:
定理 permutationsAux2_snd_nil
  条件: (t : α) (ts : 列表 α) (r : 列表 β) (f : 列表 α -> β)
  证明: rfl

@[simp]
-/
theorem permutationsAux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α -> β) :
    (permutationsAux2 t ts r [] f).2 = r :=
  rfl

@[simp]
/--
theorem `permutationsAux2_snd_cons` / 定理 `permutationsAux2_snd_cons`

English:
theorem permutationsAux2_snd_cons
  statement: (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
  proof: by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

中文:
定理 permutationsAux2_snd_cons
  结论: (t : α) (ts : 列表 α) (r : 列表 β) (y : α) (ys : 列表 α)
  证明: by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

Depends on / 依赖: permutationsAux2, permutationsAux2_fst
-/
theorem permutationsAux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
    (f : List α -> β) :
    (permutationsAux2 t ts r (y :: ys) f).2 =
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 := by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

/--
theorem `permutationsAux2_append` / 定理 `permutationsAux2_append`

English:
theorem permutationsAux2_append
  given: (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α -> β)
  proof: by
  induction ys generalizing f <;> simp [*]

中文:
定理 permutationsAux2_append
  条件: (t : α) (ts : 列表 α) (r : 列表 β) (ys : 列表 α) (f : 列表 α -> β)
  证明: by
  induction ys generalizing f <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α -> β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]

/--
theorem `permutationsAux2_comp_append` / 定理 `permutationsAux2_comp_append`

English:
theorem permutationsAux2_comp_append
  given: {t : α} {ts ys : List α} {r : List β} (f : List α -> β)
  proof: by
  induction ys generalizing f with
  | nil => simp
  | cons ys_hd _ ys_ih => simp [ys_ih fun xs => f (ys_hd :: xs)]

中文:
定理 permutationsAux2_comp_append
  条件: {t : α} {ts ys : 列表 α} {r : 列表 β} (f : 列表 α -> β)
  证明: by
  induction ys generalizing f with
  | nil => simp
  | cons ys_hd _ ys_ih => simp [ys_ih fun xs => f (ys_hd :: xs)]

Depends on / 依赖: generalizing, ys_hd, ys_ih
-/
theorem permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α -> β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f with
  | nil => simp
  | cons ys_hd _ ys_ih => simp [ys_ih fun xs => f (ys_hd :: xs)]

/--
theorem `map_permutationsAux2'` / 定理 `map_permutationsAux2'`

English:
theorem map_permutationsAux2'
  statement: {α' β'} (g : α -> α') (g' : β -> β') (t : α) (ts ys : List α)
  proof: by
  induction ys generalizing f f' with
  | nil => simp
  | cons ys_hd _ ys_ih =>
    simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H

中文:
定理 map_permutationsAux2'
  结论: {α' β'} (g : α -> α') (g' : β -> β') (t : α) (ts ys : 列表 α)
  证明: by
  induction ys generalizing f f' with
  | nil => simp
  | cons ys_hd _ ys_ih =>
    simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H

Depends on / 依赖: cons.injEq, cons_append, generalizing, map_append, map_cons, permutationsAux2_snd_cons, ys_hd, ys_ih
-/
theorem map_permutationsAux2' {α' β'} (g : α -> α') (g' : β -> β') (t : α) (ts ys : List α)
    (r : List β) (f : List α -> β) (f' : List α' -> β') (H : forall a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 := by
  induction ys generalizing f f' with
  | nil => simp
  | cons ys_hd _ ys_ih =>
    simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H

/--
theorem `map_permutationsAux2` / 定理 `map_permutationsAux2`

English:
theorem map_permutationsAux2
  given: (t : α) (ts : List α) (ys : List α) (f : List α -> β)
  proof: by
  rw [map_permutationsAux2' id]; rw [map_id]; rw [map_id]
  · rfl
  simp

中文:
定理 map_permutationsAux2
  条件: (t : α) (ts : 列表 α) (ys : 列表 α) (f : 列表 α -> β)
  证明: by
  rw [map_permutationsAux2' id]; rw [map_id]; rw [map_id]
  · rfl
  simp

Depends on / 依赖: map_id, map_permutationsAux2
-/
theorem map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α -> β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 := by
  rw [map_permutationsAux2' id]; rw [map_id]; rw [map_id]
  · rfl
  simp

/--
theorem `permutationsAux2_snd_eq` / 定理 `permutationsAux2_snd_eq`

English:
theorem permutationsAux2_snd_eq
  given: (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α -> β)
  proof: by
  rw [← permutationsAux2_append]; rw [map_permutationsAux2]; rw [permutationsAux2_comp_append]

中文:
定理 permutationsAux2_snd_eq
  条件: (t : α) (ts : 列表 α) (r : 列表 β) (ys : 列表 α) (f : 列表 α -> β)
  证明: by
  rw [← permutationsAux2_append]; rw [map_permutationsAux2]; rw [permutationsAux2_comp_append]

Depends on / 依赖: map_permutationsAux2, permutationsAux2_append, permutationsAux2_comp_append
-/
theorem permutationsAux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α -> β) :
    (permutationsAux2 t ts r ys f).2 =
      ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r := by
  rw [← permutationsAux2_append]; rw [map_permutationsAux2]; rw [permutationsAux2_comp_append]

/--
theorem `map_map_permutationsAux2` / 定理 `map_map_permutationsAux2`

English:
theorem map_map_permutationsAux2
  given: {α'} (g : α -> α') (t : α) (ts ys : List α)
  proof: map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl

中文:
定理 map_map_permutationsAux2
  条件: {α'} (g : α -> α') (t : α) (ts ys : 列表 α)
  证明: map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl

Depends on / 依赖: map_permutationsAux2
-/
theorem map_map_permutationsAux2 {α'} (g : α -> α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl

/--
theorem `map_map_permutations'Aux` / 定理 `map_map_permutations'Aux`

English:
theorem map_map_permutations'Aux
  given: (f : α -> β) (t : α) (ts : List α)
  proof: by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [permutations'Aux, map_cons, map_map, ← ih, Function.comp_def]

中文:
定理 map_map_permutations'Aux
  条件: (f : α -> β) (t : α) (ts : 列表 α)
  证明: by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [permutations'Aux, map_cons, map_map, ← ih, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, map_cons, map_map, permutations
-/
theorem map_map_permutations'Aux (f : α -> β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [permutations'Aux, map_cons, map_map, ← ih, Function.comp_def]

/--
theorem `permutations'Aux_eq_permutationsAux2` / 定理 `permutations'Aux_eq_permutationsAux2`

English:
theorem permutations'Aux_eq_permutationsAux2
  given: (t : α) (ts : List α)
  proof: by
  induction ts with | nil => rfl | cons a ts ih => ?_
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp +singlePass only [← permutationsAux2_append]
  simp [map_permutationsAux2]

中文:
定理 permutations'Aux_eq_permutationsAux2
  条件: (t : α) (ts : 列表 α)
  证明: by
  induction ts with | nil => rfl | cons a ts ih => ?_
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp +singlePass only [← permutationsAux2_append]
  simp [map_permutationsAux2]

Depends on / 依赖: append_nil, cons.injEq, cons_append, id_eq, map_permutationsAux2, permutations, permutationsAux2_append, permutationsAux2_snd_cons, singlePass, true_and
-/
theorem permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 := by
  induction ts with | nil => rfl | cons a ts ih => ?_
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp +singlePass only [← permutationsAux2_append]
  simp [map_permutationsAux2]

/--
theorem `mem_permutationsAux2` / 定理 `mem_permutationsAux2`

English:
theorem mem_permutationsAux2
  given: {t : α} {ts : List α} {ys : List α} {l l' : List α}
  proof: by
  induction ys generalizing l with
  | nil => simp +contextual
  | cons y ys ih => ?_
  rw [permutationsAux2_snd_cons]; rw [show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by simp, mem_cons, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    

中文:
定理 mem_permutationsAux2
  条件: {t : α} {ts : 列表 α} {ys : 列表 α} {l l' : 列表 α}
  证明: by
  induction ys generalizing l with
  | nil => simp +contextual
  | cons y ys ih => ?_
  rw [permutationsAux2_snd_cons]; rw [show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by simp, mem_cons, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    

Depends on / 依赖: Or.inr, cons_append, contextual, generalizing, mem_cons, permutationsAux2_snd_cons
-/
theorem mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' in (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔
      exists l₁ l₂, l₂ != [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := by
  induction ys generalizing l with
  | nil => simp +contextual
  | cons y ys ih => ?_
  rw [permutationsAux2_snd_cons]; rw [show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by simp, mem_cons, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    · exact ⟨y :: l₁, l₂, l0, by simp⟩
  · rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩
    · simp [ye]
    · simp only [cons_append] at ye
      rcases ye with ⟨rfl, rfl⟩
      exact Or.inr ⟨l₁, l₂, l0, by simp⟩

/--
theorem `mem_permutationsAux2'` / 定理 `mem_permutationsAux2'`

English:
theorem mem_permutationsAux2'
  given: {t : α} {ts : List α} {ys : List α} {l : List α}
  proof: by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2

中文:
定理 mem_permutationsAux2'
  条件: {t : α} {ts : 列表 α} {ys : 列表 α} {l : 列表 α}
  证明: by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2

Depends on / 依赖: mem_permutationsAux2
-/
theorem mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l in (permutationsAux2 t ts [] ys id).2 ↔
      exists l₁ l₂, l₂ != [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts := by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2

/--
theorem `length_permutationsAux2` / 定理 `length_permutationsAux2`

English:
theorem length_permutationsAux2
  given: (t : α) (ts : List α) (ys : List α) (f : List α -> β)
  proof: by
  induction ys generalizing f <;> simp [*]

中文:
定理 length_permutationsAux2
  条件: (t : α) (ts : 列表 α) (ys : 列表 α) (f : 列表 α -> β)
  证明: by
  induction ys generalizing f <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α -> β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]

/--
theorem `foldr_permutationsAux2` / 定理 `foldr_permutationsAux2`

English:
theorem foldr_permutationsAux2
  given: (t : α) (ts : List α) (r L : List (List α))
  proof: by
  induction L with
  | nil => rfl
  | cons l L ih => simp_rw [foldr_cons, ih, flatMap_cons, append_assoc, permutationsAux2_append]

中文:
定理 foldr_permutationsAux2
  条件: (t : α) (ts : 列表 α) (r L : 列表 (列表 α))
  证明: by
  induction L with
  | nil => rfl
  | cons l L ih => simp_rw [foldr_cons, ih, flatMap_cons, append_assoc, permutationsAux2_append]

Depends on / 依赖: append_assoc, flatMap_cons, foldr_cons, permutationsAux2_append, simp_rw
-/
theorem foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.flatMap fun y => (permutationsAux2 t ts [] y id).2) ++ r := by
  induction L with
  | nil => rfl
  | cons l L ih => simp_rw [foldr_cons, ih, flatMap_cons, append_assoc, permutationsAux2_append]

/--
theorem `mem_foldr_permutationsAux2` / 定理 `mem_foldr_permutationsAux2`

English:
theorem mem_foldr_permutationsAux2
  given: {t : α} {ts : List α} {r L : List (List α)} {l' : List α}
  proof: by
  have :
    (exists a : List α,
        a in L ∧ exists l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      exists l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ in L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨_, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, 

中文:
定理 mem_foldr_permutationsAux2
  条件: {t : α} {ts : 列表 α} {r L : 列表 (列表 α)} {l' : 列表 α}
  证明: by
  have :
    (exists a : List α,
        a in L ∧ exists l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      exists l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ in L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨_, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, 

Depends on / 依赖: and_left_comm, append_assoc, cons_append, foldr_permutationsAux2, mem_append, mem_flatMap, mem_permutationsAux2, or_comm
-/
theorem mem_foldr_permutationsAux2 {t : α} {ts : List α} {r L : List (List α)} {l' : List α} :
    l' in foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔
      l' in r ∨ exists l₁ l₂, l₁ ++ l₂ in L ∧ l₂ != [] ∧ l' = l₁ ++ t :: l₂ ++ ts := by
  have :
    (exists a : List α,
        a in L ∧ exists l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      exists l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ in L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨_, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, aL, h⟩ =>
      ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩
  rw [foldr_permutationsAux2]
  simp only [mem_permutationsAux2', ← this, or_comm, and_left_comm, mem_append, mem_flatMap,
    append_assoc, cons_append]

/--
theorem `length_foldr_permutationsAux2` / 定理 `length_foldr_permutationsAux2`

English:
theorem length_foldr_permutationsAux2
  given: (t : α) (ts : List α) (r L : List (List α))
  proof: by
  simp [foldr_permutationsAux2, length_permutationsAux2, length_flatMap]

中文:
定理 length_foldr_permutationsAux2
  条件: (t : α) (ts : 列表 α) (r L : 列表 (列表 α))
  证明: by
  simp [foldr_permutationsAux2, length_permutationsAux2, length_flatMap]

Depends on / 依赖: foldr_permutationsAux2, length_flatMap, length_permutationsAux2
-/
theorem length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      (map length L).sum + length r := by
  simp [foldr_permutationsAux2, length_permutationsAux2, length_flatMap]

/--
theorem `length_foldr_permutationsAux2'` / 定理 `length_foldr_permutationsAux2'`

English:
theorem length_foldr_permutationsAux2'
  statement: (t : α) (ts : List α) (r L : List (List α)) (n)
  proof: by
  rw [length_foldr_permutationsAux2]; rw [(_ : (map length L).sum = n * length L)]
  induction L with
  | nil => simp
  | cons l L ih =>
    have sum_map : (map length L).sum = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
    have length_l : length l = n := H _ mem_cons_self
    simp [

中文:
定理 length_foldr_permutationsAux2'
  结论: (t : α) (ts : 列表 α) (r L : 列表 (列表 α)) (n)
  证明: by
  rw [length_foldr_permutationsAux2]; rw [(_ : (map length L).sum = n * length L)]
  induction L with
  | nil => simp
  | cons l L ih =>
    have sum_map : (map length L).sum = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
    have length_l : length l = n := H _ mem_cons_self
    simp [

Depends on / 依赖: Nat.add_comm, add_comm, length, length_foldr_permutationsAux2, length_l, mem_cons_of_mem, mem_cons_self, mul_succ, sum_map
-/
theorem length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : forall l in L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r := by
  rw [length_foldr_permutationsAux2]; rw [(_ : (map length L).sum = n * length L)]
  induction L with
  | nil => simp
  | cons l L ih =>
    have sum_map : (map length L).sum = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
    have length_l : length l = n := H _ mem_cons_self
    simp [sum_map, length_l, Nat.add_comm, mul_succ]

@[simp]
/--
theorem `permutationsAux_nil` / 定理 `permutationsAux_nil`

English:
theorem permutationsAux_nil
  given: (is : List α)
  statement: permutationsAux [] is = []
  proof: by
  rw [permutationsAux]; rw [permutationsAux.rec]

@[simp]

中文:
定理 permutationsAux_nil
  条件: (is : 列表 α)
  结论: permutationsAux [] is = []
  证明: by
  rw [permutationsAux]; rw [permutationsAux.rec]

@[simp]

Depends on / 依赖: permutationsAux, permutationsAux.rec
-/
theorem permutationsAux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutationsAux]; rw [permutationsAux.rec]

@[simp]
/--
theorem `permutationsAux_cons` / 定理 `permutationsAux_cons`

English:
theorem permutationsAux_cons
  given: (t : α) (ts is : List α)
  proof: by
  rw [permutationsAux]; rw [permutationsAux.rec]; rfl

@[simp]

中文:
定理 permutationsAux_cons
  条件: (t : α) (ts is : 列表 α)
  证明: by
  rw [permutationsAux]; rw [permutationsAux.rec]; rfl

@[simp]

Depends on / 依赖: permutationsAux, permutationsAux.rec
-/
theorem permutationsAux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) := by
  rw [permutationsAux]; rw [permutationsAux.rec]; rfl

@[simp]
/--
theorem `permutations_nil` / 定理 `permutations_nil`

English:
theorem permutations_nil
  statement: permutations ([] : List α) = [[]]
  proof: by
  rw [permutations]; rw [permutationsAux_nil]

中文:
定理 permutations_nil
  结论: permutations ([] : 列表 α) = [[]]
  证明: by
  rw [permutations]; rw [permutationsAux_nil]

Depends on / 依赖: permutations, permutationsAux_nil
-/
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations]; rw [permutationsAux_nil]

/--
theorem `map_permutationsAux` / 定理 `map_permutationsAux`

English:
theorem map_permutationsAux
  given: (f : α -> β)
  proof: by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    flatMap_map, IH1, append_assoc, permutationsAux_cons, flatMap_cons, ← IH2, map_flatMap]

中文:
定理 map_permutationsAux
  条件: (f : α -> β)
  证明: by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    flatMap_map, IH1, append_assoc, permutationsAux_cons, flatMap_cons, ← IH2, map_flatMap]

Depends on / 依赖: append_assoc, flatMap_cons, flatMap_map, foldr_permutationsAux2, introv, map_append, map_flatMap, map_map_permutationsAux2, permutations, permutationsAux, permutationsAux.rec, permutationsAux_cons
-/
theorem map_permutationsAux (f : α -> β) :
    forall ts is :
    List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) := by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    flatMap_map, IH1, append_assoc, permutationsAux_cons, flatMap_cons, ← IH2, map_flatMap]

/--
theorem `map_permutations` / 定理 `map_permutations`

English:
theorem map_permutations
  given: (f : α -> β) (ts : List α)
  proof: by
  rw [permutations]; rw [permutations]; rw [map]; rw [map_permutationsAux]; rw [map]

中文:
定理 map_permutations
  条件: (f : α -> β) (ts : 列表 α)
  证明: by
  rw [permutations]; rw [permutations]; rw [map]; rw [map_permutationsAux]; rw [map]

Depends on / 依赖: map_permutationsAux, permutations
-/
theorem map_permutations (f : α -> β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations]; rw [permutations]; rw [map]; rw [map_permutationsAux]; rw [map]

/--
theorem `map_permutations'` / 定理 `map_permutations'`

English:
theorem map_permutations'
  given: (f : α -> β) (ts : List α)
  proof: by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [← ih, map_flatMap, ← map_map_permutations'Aux, flatMap_map]

中文:
定理 map_permutations'
  条件: (f : α -> β) (ts : 列表 α)
  证明: by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [← ih, map_flatMap, ← map_map_permutations'Aux, flatMap_map]

Depends on / 依赖: flatMap_map, map_flatMap, map_map_permutations
-/
theorem map_permutations' (f : α -> β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [← ih, map_flatMap, ← map_map_permutations'Aux, flatMap_map]

/--
theorem `permutationsAux_append` / 定理 `permutationsAux_append`

English:
theorem permutationsAux_append
  given: (is is' ts : List α)
  proof: by
  induction is generalizing is' with | nil => simp | cons t is ih =>
  simp only [foldr_permutationsAux2, ih, map_flatMap, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp +singlePass only [← permutationsAux2_co

中文:
定理 permutationsAux_append
  条件: (is is' ts : 列表 α)
  证明: by
  induction is generalizing is' with | nil => simp | cons t is ih =>
  simp only [foldr_permutationsAux2, ih, map_flatMap, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp +singlePass only [← permutationsAux2_co

Depends on / 依赖: append_assoc, cons_append, foldr_permutationsAux2, generalizing, map_append, map_flatMap, map_permutationsAux2, permutationsAux2_comp_append, permutationsAux_cons, reverse_cons, singlePass
-/
theorem permutationsAux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') := by
  induction is generalizing is' with | nil => simp | cons t is ih =>
  simp only [foldr_permutationsAux2, ih, map_flatMap, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp +singlePass only [← permutationsAux2_comp_append]
  simp only [id, append_assoc]

/--
theorem `permutations_append` / 定理 `permutations_append`

English:
theorem permutations_append
  given: (is ts : List α)
  proof: by
  simp [permutations, permutationsAux_append]

中文:
定理 permutations_append
  条件: (is ts : 列表 α)
  证明: by
  simp [permutations, permutationsAux_append]

Depends on / 依赖: permutations, permutationsAux_append
-/
theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutationsAux_append]

/--
theorem `perm_of_mem_permutationsAux` / 定理 `perm_of_mem_permutationsAux`

English:
theorem perm_of_mem_permutationsAux
  proof: by
  show forall (ts is l : List α), l in permutationsAux ts is -> l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons]; rw [permutations]; rw [mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_m

中文:
定理 perm_of_mem_permutationsAux
  证明: by
  show forall (ts is l : List α), l in permutationsAux ts is -> l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons]; rw [permutations]; rw [mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_m

Depends on / 依赖: append_nil, append_right, introv, is.append_nil, mem_cons, mem_foldr_permutationsAux2, p.cons, perm_append_comm, perm_append_comm.cons, perm_middle, perm_middle.trans, permutations, permutationsAux, permutationsAux.rec, permutationsAux_cons
-/
theorem perm_of_mem_permutationsAux :
    forall {ts is l : List α}, l in permutationsAux ts is -> l ~ ts ++ is := by
  show forall (ts is l : List α), l in permutationsAux ts is -> l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons]; rw [permutations]; rw [mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_middle
  · have p : l₁ ++ l₂ ~ is := by
      simp only [mem_cons] at m
      rcases m with e | m
      · simp [e]
      exact is.append_nil ▸ IH2 _ m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)

/--
theorem `perm_of_mem_permutations` / 定理 `perm_of_mem_permutations`

English:
theorem perm_of_mem_permutations
  given: {l₁ l₂ : List α} (h : l₁ in permutations l₂)
  statement: l₁ ~ l₂
  proof: (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m

中文:
定理 perm_of_mem_permutations
  条件: {l₁ l₂ : 列表 α} (h : l₁ in permutations l₂)
  结论: l₁ ~ l₂
  证明: (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m

Depends on / 依赖: Perm.refl, append_nil, eq_or_mem_of_mem_cons, perm_of_mem_permutationsAux
-/
theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ in permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m

/--
theorem `length_permutationsAux` / 定理 `length_permutationsAux`

English:
theorem length_permutationsAux
  proof: by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [List.length_cons, factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons]; rw [length_foldr_permutationsAux2' _ _ _ _ _ f

中文:
定理 length_permutationsAux
  证明: by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [List.length_cons, factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons]; rw [length_foldr_permutationsAux2' _ _ _ _ _ f

Depends on / 依赖: List.length_cons, Nat.factorial_succ, Nat.mul_comm, Nat.succ_add, Nat.succ_eq_add_one, add_eq, factorial, factorial_succ, is.length, length, length_cons, length_eq, length_foldr_permutationsAux2, mul_comm, perm_of_mem_permutations, permutations, permutationsAux, permutationsAux.rec, permutationsAux_cons, succ_add
-/
theorem length_permutationsAux :
    forall ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! := by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [List.length_cons, factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons]; rw [length_foldr_permutationsAux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq]; rw [permutations]; rw [length]; rw [length]; rw [IH2]; rw [Nat.succ_add]; rw [Nat.factorial_succ]; rw [Nat.mul_comm (_ + 1)]; rw [← Nat.succ_eq_add_one]; rw [← IH1]; rw [Nat.add_comm (_ * _)]; rw [Nat.add_assoc]; rw [Nat.mul_succ]; rw [Nat.mul_comm]

/--
theorem `length_permutations` / 定理 `length_permutations`

English:
theorem length_permutations
  given: (l : List α)
  statement: length (permutations l) = (length l)!
  proof: length_permutationsAux l []

中文:
定理 length_permutations
  条件: (l : 列表 α)
  结论: length (permutations l) = (length l)!
  证明: length_permutationsAux l []

Depends on / 依赖: length_permutationsAux
-/
theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutationsAux l []

/--
theorem `mem_permutations_of_perm_lemma` / 定理 `mem_permutations_of_perm_lemma`

English:
theorem mem_permutations_of_perm_lemma
  statement: {is l : List α}
  proof: by simpa [permutations, perm_nil] using H

中文:
定理 mem_permutations_of_perm_lemma
  结论: {is l : 列表 α}
  证明: by simpa [permutations, perm_nil] using H

Depends on / 依赖: perm_nil, permutations
-/
theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is -> (exists (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l in permutationsAux is []) :
    l ~ is -> l in permutations is := by simpa [permutations, perm_nil] using H

/--
theorem `mem_permutationsAux_of_perm` / 定理 `mem_permutationsAux_of_perm`

English:
theorem mem_permutationsAux_of_perm
  proof: by
  show forall (ts is l : List α),
      l ~ is ++ ts -> (exists (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l in permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons]; rw [mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_mid

中文:
定理 mem_permutationsAux_of_perm
  证明: by
  show forall (ts is l : List α),
      l ~ is ++ ts -> (exists (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l in permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons]; rw [mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_mid

Depends on / 依赖: Or.inl, append_of_mem, cons_inv, mem_cons_self, mem_foldr_permutationsAux2, p.trans, perm_middle, perm_middle.symm.trans, permutationsAux, permutationsAux.rec, permutationsAux_cons, subset, symm.subset
-/
theorem mem_permutationsAux_of_perm :
    forall {ts is l : List α},
      l ~ is ++ ts -> (exists (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l in permutationsAux ts is := by
  show forall (ts is l : List α),
      l ~ is ++ ts -> (exists (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l in permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons]; rw [mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases append_of_mem (p'.symm.subset mem_cons_self) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    rcases l₂ with - | ⟨a, l₂'⟩
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma (IH2 _) p, by simp⟩)
  · exact Or.inr (Or.inl m)

@[simp]
/--
theorem `mem_permutations` / 定理 `mem_permutations`

English:
theorem mem_permutations
  given: {s t : List α}
  statement: s in permutations t ↔ s ~ t
  proof: ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

中文:
定理 mem_permutations
  条件: {s t : 列表 α}
  结论: s in permutations t ↔ s ~ t
  证明: ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

Depends on / 依赖: mem_permutationsAux_of_perm, mem_permutations_of_perm_lemma, perm_of_mem_permutations
-/
theorem mem_permutations {s t : List α} : s in permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

/--
theorem `perm_pair` / 定理 `perm_pair`

English:
theorem perm_pair
  given: {a b : α} {l : List α}
  statement: l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a]
  proof: by
  have : [a, b].permutations = [[a, b], [b, a]] := by cbv
  grind [=_ mem_permutations]

中文:
定理 perm_pair
  条件: {a b : α} {l : 列表 α}
  结论: l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a]
  证明: by
  have : [a, b].permutations = [[a, b], [b, a]] := by cbv
  grind [=_ mem_permutations]

Depends on / 依赖: mem_permutations, permutations
-/
theorem perm_pair {a b : α} {l : List α} : l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a] := by
  have : [a, b].permutations = [[a, b], [b, a]] := by cbv
  grind [=_ mem_permutations]

/--
theorem `pair_perm` / 定理 `pair_perm`

English:
theorem pair_perm
  given: {a b : α} {l : List α}
  statement: [a, b] ~ l ↔ l = [a, b] ∨ l = [b, a]
  proof: perm_comm.trans perm_pair

中文:
定理 pair_perm
  条件: {a b : α} {l : 列表 α}
  结论: [a, b] ~ l ↔ l = [a, b] ∨ l = [b, a]
  证明: perm_comm.trans perm_pair

Depends on / 依赖: perm_comm, perm_comm.trans, perm_pair
-/
theorem pair_perm {a b : α} {l : List α} : [a, b] ~ l ↔ l = [a, b] ∨ l = [b, a] :=
  perm_comm.trans perm_pair

/--
theorem `perm_permutations'Aux_comm` / 定理 `perm_permutations'Aux_comm`

English:
theorem perm_permutations'Aux_comm
  given: (a b : α) (l : List α)
  proof: by
  induction l with
  | nil => exact Perm.swap [a, b] [b, a] []
  | cons c l ih => ?_
  simp only [permutations'Aux, flatMap_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    forall a b,
      (map (cons c) (permutations'Aux a l)).flatMap (permutations'Aux b) ~
        map (con

中文:
定理 perm_permutations'Aux_comm
  条件: (a b : α) (l : 列表 α)
  证明: by
  induction l with
  | nil => exact Perm.swap [a, b] [b, a] []
  | cons c l ih => ?_
  simp only [permutations'Aux, flatMap_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    forall a b,
      (map (cons c) (permutations'Aux a l)).flatMap (permutations'Aux b) ~
        map (con

Depends on / 依赖: Perm.swap, cons_append, flatMap, flatMap_cons, flatMap_map, map_cons, map_map, permutations
-/
theorem perm_permutations'Aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).flatMap (permutations'Aux b) ~
      (permutations'Aux b l).flatMap (permutations'Aux a) := by
  induction l with
  | nil => exact Perm.swap [a, b] [b, a] []
  | cons c l ih => ?_
  simp only [permutations'Aux, flatMap_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    forall a b,
      (map (cons c) (permutations'Aux a l)).flatMap (permutations'Aux b) ~
        map (cons b ∘ cons c) (permutations'Aux a l) ++
          map (cons c) ((permutations'Aux a l).flatMap (permutations'Aux b)) := by
    intro a' b'
    simp only [flatMap_map, permutations'Aux]
    change (permutations'Aux _ l).flatMap (fun a => ([b' :: c :: a] ++
      map (cons c) (permutations'Aux _ a))) ~ _
    refine (flatMap_append_perm _ (fun x => [b' :: c :: x]) _).symm.trans ?_
    rw [← map_eq_flatMap]; rw [← map_flatMap]
    exact Perm.refl _
  refine (((this _ _).append_left _).trans ?_).trans ((this _ _).append_left _).symm
  rw [← append_assoc]; rw [← append_assoc]
  exact perm_append_comm.append (ih.map _)

/--
theorem `Perm.permutations'` / 定理 `Perm.permutations'`

English:
theorem Perm.permutations'
  given: {s t : List α} (p : s ~ t)
  statement: permutations' s ~ permutations' t
  proof: by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.flatMap_right _
  | swap =>
    dsimp
    rw [flatMap_assoc]; rw [flatMap_assoc]
    apply Perm.flatMap_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

中文:
定理 置换.permutations'
  条件: {s t : 列表 α} (p : s ~ t)
  结论: permutations' s ~ permutations' t
  证明: by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.flatMap_right _
  | swap =>
    dsimp
    rw [flatMap_assoc]; rw [flatMap_assoc]
    apply Perm.flatMap_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

Depends on / 依赖: Aux_comm, IH.flatMap_right, Perm.flatMap_left, flatMap_assoc, flatMap_left, flatMap_right, perm_permutations
-/
theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t := by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.flatMap_right _
  | swap =>
    dsimp
    rw [flatMap_assoc]; rw [flatMap_assoc]
    apply Perm.flatMap_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

/--
theorem `permutations_perm_permutations'` / 定理 `permutations_perm_permutations'`

English:
theorem permutations_perm_permutations'
  given: (ts : List α)
  statement: ts.permutations ~ ts.permutations'
  proof: by
  obtain ⟨n, h⟩ : exists n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction n generalizing ts with | zero => cases h | succ n IH => ?_
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append]; rw [length_concat]; rw [Nat.succ_lt_succ

中文:
定理 permutations_perm_permutations'
  条件: (ts : 列表 α)
  结论: ts.permutations ~ ts.permutations'
  证明: by
  obtain ⟨n, h⟩ : exists n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction n generalizing ts with | zero => cases h | succ n IH => ?_
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append]; rw [length_concat]; rw [Nat.succ_lt_succ

Depends on / 依赖: List.reverseRecOn, Nat.lt_succ_self, Nat.succ_lt_succ_iff, append_, concat_eq_append, foldr_permutationsAux2, generalizing, length, length_concat, length_reverse, lt_succ_self, permutations, permutationsAux_cons, permutationsAux_nil, permutations_append, reverse, reverseRecOn, reverse_perm, succ_lt_succ_iff, ts.reverse
-/
theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' := by
  obtain ⟨n, h⟩ : exists n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction n generalizing ts with | zero => cases h | succ n IH => ?_
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append]; rw [length_concat]; rw [Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutationsAux2, permutationsAux_nil,
    permutationsAux_cons, append_nil]
  refine
    (perm_append_comm.trans ((IH₂.flatMap_right _).append ((IH _ h).map _))).trans
      (Perm.trans ?_ perm_append_comm.permutations')
  rw [map_eq_flatMap]; rw [singleton_append]; rw [permutations']
  refine (flatMap_append_perm _ _ _).trans ?_
  refine Perm.of_eq ?_
  congr
  funext _
  rw [permutations'Aux_eq_permutationsAux2]; rw [permutationsAux2_append]

@[simp]
/--
theorem `mem_permutations'` / 定理 `mem_permutations'`

English:
theorem mem_permutations'
  given: {s t : List α}
  statement: s in permutations' t ↔ s ~ t
  proof: (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

中文:
定理 mem_permutations'
  条件: {s t : 列表 α}
  结论: s in permutations' t ↔ s ~ t
  证明: (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

Depends on / 依赖: mem_iff, mem_permutations, permutations_perm_permutations, symm.mem_iff.trans
-/
theorem mem_permutations' {s t : List α} : s in permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

/--
theorem `Perm.permutations` / 定理 `Perm.permutations`

English:
theorem Perm.permutations
  given: {s t : List α} (h : s ~ t)
  statement: permutations s ~ permutations t
  proof: (permutations_perm_permutations' _).trans
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]

中文:
定理 置换.permutations
  条件: {s t : 列表 α} (h : s ~ t)
  结论: permutations s ~ permutations t
  证明: (permutations_perm_permutations' _).trans
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]

Depends on / 依赖: h.permutations, permutations, permutations_perm_permutations
-/
theorem Perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
(permutations_perm_permutations' _).trans
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]
/--
theorem `perm_permutations_iff` / 定理 `perm_permutations_iff`

English:
theorem perm_permutations_iff
  given: {s t : List α}
  statement: permutations s ~ permutations t ↔ s ~ t
  proof: ⟨fun h => mem_permutations.1 h.mem_iff.1 mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]

中文:
定理 perm_permutations_iff
  条件: {s t : 列表 α}
  结论: permutations s ~ permutations t ↔ s ~ t
  证明: ⟨fun h => mem_permutations.1 h.mem_iff.1 mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]

Depends on / 依赖: Perm.permutations, Perm.refl, h.mem_iff, mem_iff, mem_permutations, permutations
-/
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
⟨fun h => mem_permutations.1 h.mem_iff.1 mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]
/--
theorem `perm_permutations'_iff` / 定理 `perm_permutations'_iff`

English:
theorem perm_permutations'_iff
  given: {s t : List α}
  statement: permutations' s ~ permutations' t ↔ s ~ t
  proof: ⟨fun h => mem_permutations'.1 h.mem_iff.1 mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩

中文:
定理 perm_permutations'_iff
  条件: {s t : 列表 α}
  结论: permutations' s ~ permutations' t ↔ s ~ t
  证明: ⟨fun h => mem_permutations'.1 h.mem_iff.1 mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩
-/
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
⟨fun h => mem_permutations'.1 h.mem_iff.1 mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩

/--
theorem `getElem_permutations'Aux` / 定理 `getElem_permutations'Aux`

English:
theorem getElem_permutations'Aux
  statement: (s : List α) (x : α) (n : Nat)
  proof: by
  induction s generalizing n with
  | nil =>
    simp only [permutations'Aux, length, Nat.zero_add, lt_one_iff] at hn
    simp [hn]
  | cons y s IH =>
    cases n
    · simp
    · simpa [get] using IH _ _

中文:
定理 getElem_permutations'Aux
  结论: (s : 列表 α) (x : α) (n : 自然数)
  证明: by
  induction s generalizing n with
  | nil =>
    simp only [permutations'Aux, length, Nat.zero_add, lt_one_iff] at hn
    simp [hn]
  | cons y s IH =>
    cases n
    · simp
    · simpa [get] using IH _ _

Depends on / 依赖: Nat.zero_add, generalizing, length, lt_one_iff, permutations, zero_add
-/
theorem getElem_permutations'Aux (s : List α) (x : α) (n : Nat)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s)[n] = s.insertIdx n x := by
  induction s generalizing n with
  | nil =>
    simp only [permutations'Aux, length, Nat.zero_add, lt_one_iff] at hn
    simp [hn]
  | cons y s IH =>
    cases n
    · simp
    · simpa [get] using IH _ _

/--
theorem `get_permutations'Aux` / 定理 `get_permutations'Aux`

English:
theorem get_permutations'Aux
  statement: (s : List α) (x : α) (n : Nat)
  proof: by
  simp [getElem_permutations'Aux]

中文:
定理 get_permutations'Aux
  结论: (s : 列表 α) (x : α) (n : 自然数)
  证明: by
  simp [getElem_permutations'Aux]

Depends on / 依赖: getElem_permutations
-/
theorem get_permutations'Aux (s : List α) (x : α) (n : Nat)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).get ⟨n, hn⟩ = s.insertIdx n x := by
  simp [getElem_permutations'Aux]

-- Porting note: temporary theorem to solve diamond issue
/--
theorem `DecEq_eq` / 定理 `DecEq_eq`

English:
theorem DecEq_eq
  given: [DecidableEq α]
  proof: congr_arg BEq.mk by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff]; rw [@beq_iff_eq _ (_)]; rw [decide_eq_true_iff]

中文:
定理 DecEq_eq
  条件: [DecidableEq α]
  证明: congr_arg BEq.mk by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff]; rw [@beq_iff_eq _ (_)]; rw [decide_eq_true_iff]
-/
private theorem DecEq_eq [DecidableEq α] :
    List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList :=
congr_arg BEq.mk by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff]; rw [@beq_iff_eq _ (_)]; rw [decide_eq_true_iff]

/--
theorem `count_permutations'Aux_self` / 定理 `count_permutations'Aux_self`

English:
theorem count_permutations'Aux_self
  given: [DecidableEq α] (l : List α) (x : α)
  proof: by
  induction l generalizing x with
  | nil => simp [takeWhile, count]
  | cons y l IH =>
    rw [permutations'Aux]; rw [count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj, DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.s

中文:
定理 count_permutations'Aux_self
  条件: [DecidableEq α] (l : 列表 α) (x : α)
  证明: by
  induction l generalizing x with
  | nil => simp [takeWhile, count]
  | cons y l IH =>
    rw [permutations'Aux]; rw [count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj, DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.s

Depends on / 依赖: DecEq_eq, Nat.succ_inj, Nat.zero_add, Ne.symm, and_false, cons.injEq, count_cons_self, count_eq_zero_of_not_mem, decide_false, exists_false, false_and, generalizing, length_nil, mem_map, not_false_iff, permutations, succ_inj, takeWhile, zero_add
-/
theorem count_permutations'Aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile (x = ·) l) + 1 := by
  induction l generalizing x with
  | nil => simp [takeWhile, count]
  | cons y l IH =>
    rw [permutations'Aux]; rw [count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj, DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.symm hx, false_and, and_false, exists_false,
        not_false_iff, count_eq_zero_of_not_mem, Nat.zero_add, hx, decide_false, length_nil]

@[simp]
/--
theorem `length_permutations'Aux` / 定理 `length_permutations'Aux`

English:
theorem length_permutations'Aux
  given: (s : List α) (x : α)
  proof: by
  induction s with
  | nil => simp
  | cons y s IH => simpa using IH

中文:
定理 length_permutations'Aux
  条件: (s : 列表 α) (x : α)
  证明: by
  induction s with
  | nil => simp
  | cons y s IH => simpa using IH
-/
theorem length_permutations'Aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 := by
  induction s with
  | nil => simp
  | cons y s IH => simpa using IH

/--
theorem `injective_permutations'Aux` / 定理 `injective_permutations'Aux`

English:
theorem injective_permutations'Aux
  given: (x : α)
  statement: Function.Injective (permutations'Aux x)
  proof: by
  intro s t h
  apply insertIdx_injective s.length x
  dsimp
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp)]; rw [← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]

中文:
定理 injective_permutations'Aux
  条件: (x : α)
  结论: 函数.单射 (permutations'Aux x)
  证明: by
  intro s t h
  apply insertIdx_injective s.length x
  dsimp
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp)]; rw [← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]

Depends on / 依赖: congr_arg, get_eq_getElem, get_permutations, insertIdx_injective, length, s.length, t.length
-/
theorem injective_permutations'Aux (x : α) : Function.Injective (permutations'Aux x) := by
  intro s t h
  apply insertIdx_injective s.length x
  dsimp
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp)]; rw [← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]

/--
theorem `nodup_permutations'Aux_of_notMem` / 定理 `nodup_permutations'Aux_of_notMem`

English:
theorem nodup_permutations'Aux_of_notMem
  given: (s : List α) (x : α) (hx : x ∉ s)
  proof: by
  induction s with
  | nil => simp
  | cons y s IH =>
    simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp

中文:
定理 nodup_permutations'Aux_of_notMem
  条件: (s : 列表 α) (x : α) (hx : x ∉ s)
  证明: by
  induction s with
  | nil => simp
  | cons y s IH =>
    simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp

Depends on / 依赖: Ne.symm, cons.injEq, exists_eq_right_right, hx.left, hx.right, mem_cons, mem_map, nodup_cons, nodup_map_iff, not_and, not_or, permutations
-/
theorem nodup_permutations'Aux_of_notMem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction s with
  | nil => simp
  | cons y s IH =>
    simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp

/--
theorem `nodup_permutations'Aux_iff` / 定理 `nodup_permutations'Aux_iff`

English:
theorem nodup_permutations'Aux_iff
  given: {s : List α} {x : α}
  statement: Nodup (permutations'Aux x s) ↔ x ∉ s
  proof: by
  refine ⟨fun h H => ?_, nodup_permutations'Aux_of_notMem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s

中文:
定理 nodup_permutations'Aux_iff
  条件: {s : 列表 α} {x : α}
  结论: Nodup (permutations'Aux x s) ↔ x ∉ s
  证明: by
  refine ⟨fun h H => ?_, nodup_permutations'Aux_of_notMem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s
-/
theorem nodup_permutations'Aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s := by
  refine ⟨fun h H => ?_, nodup_permutations'Aux_of_notMem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s).length := by simpa using hk
  rw [← @Fin.mk.inj_iff _ _ _ kl k1l]; apply h
  rw [get_permutations'Aux]; rw [get_permutations'Aux]
  have hl : length (s.insertIdx k x) = length (s.insertIdx (k + 1) x) := by
    rw [length_insertIdx_of_le_length hk.le]; rw [length_insertIdx_of_le_length (Nat.succ_le_of_lt hk)]
  exact ext_get hl fun n hn hn' => by grind

/--
theorem `nodup_permutations` / 定理 `nodup_permutations`

English:
theorem nodup_permutations
  given: (s : List α) (hs : Nodup s)
  statement: Nodup s.permutations
  proof: by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction hs with
  | nil => simp
  | @cons x l h h' IH =>
    rw [permutations']
    rw [nodup_flatMap]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff]; rw [hy.mem_iff]
      exact f

中文:
定理 nodup_permutations
  条件: (s : 列表 α) (hs : Nodup s)
  结论: Nodup s.permutations
  证明: by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction hs with
  | nil => simp
  | @cons x l h h' IH =>
    rw [permutations']
    rw [nodup_flatMap]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff]; rw [hy.mem_iff]
      exact f

Depends on / 依赖: Aux_iff, Function, Function.onFun, IH.pairwise_of_forall_ne, disjoint_iff_ne, get_of_mem, hy.mem_iff, mem_iff, mem_permutations, nodup_flatMap, nodup_iff, nodup_permutations, pairwise_of_forall_ne, permutations, permutations_perm_permutations
-/
theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations := by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction hs with
  | nil => simp
  | @cons x l h h' IH =>
    rw [permutations']
    rw [nodup_flatMap]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff]; rw [hy.mem_iff]
      exact fun H => h x H rfl
    · refine IH.pairwise_of_forall_ne fun as ha bs hb H => ?_
      rw [Function.onFun]; rw [disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨⟨n, hn⟩, hn'⟩ := get_of_mem ha'
      obtain ⟨⟨m, hm⟩, hm'⟩ := get_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'Aux] at hn hm
      rw [get_permutations'Aux] at hn' hm'
      have hx : (as.insertIdx n x)[m]'(by
          rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff, hl]) = x := by
        simp [hn', ← hm']
      have hx' : (bs.insertIdx m x)[n]'(by
          rwa [length_insertIdx_of_le_length hm, Nat.lt_succ_iff, ← hl]) = x := by
        simp [hm', ← hn']
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x in bs by exact h x (hb.subset this) rfl
        rw [← hx']; rw [getElem_insertIdx_of_lt ht]
        exact getElem_mem _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insertIdx_injective _ _ hn')
      · suffices x in as by exact h x (ha.subset this) rfl
        rw [← hx]; rw [getElem_insertIdx_of_lt ht]
        exact getElem_mem _

/--
lemma `permutations_take_two` / 引理 `permutations_take_two`

English:
lemma permutations_take_two
  given: (x y : α) (s : List α)
  proof: by
  induction s <;> simp [permutations]

@[simp]

中文:
引理 permutations_take_two
  条件: (x y : α) (s : 列表 α)
  证明: by
  induction s <;> simp [permutations]

@[simp]

Depends on / 依赖: permutations
-/
lemma permutations_take_two (x y : α) (s : List α) :
    (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s] := by
  induction s <;> simp [permutations]

@[simp]
/--
theorem `nodup_permutations_iff` / 定理 `nodup_permutations_iff`

English:
theorem nodup_permutations_iff
  given: {s : List α}
  statement: Nodup s.permutations ↔ Nodup s
  proof: by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht)]; rw [← exists_duplicate_iff_not_nodup]
  use x 

中文:
定理 nodup_permutations_iff
  条件: {s : 列表 α}
  结论: Nodup s.permutations ↔ Nodup s
  证明: by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht)]; rw [← exists_duplicate_iff_not_nodup]
  use x 

Depends on / 依赖: List.Perm.nodup_iff, List.Perm.permutations, List.Sublist.exists_perm_append, List.duplicate_iff_sublist, Sublist, contrapose, duplicate_iff_sublist, exists_duplicate_iff_not_nodup, exists_perm_append, nodup_iff, nodup_permutations, permutations, permutations_take_two, take_sublist
-/
theorem nodup_permutations_iff {s : List α} : Nodup s.permutations ↔ Nodup s := by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht)]; rw [← exists_duplicate_iff_not_nodup]
  use x :: x :: l
  rw [List.duplicate_iff_sublist]; rw [← permutations_take_two]
  exact take_sublist 2 _

-- TODO: `count s s.permutations = (zipWith count s s.tails).prod`

end List
