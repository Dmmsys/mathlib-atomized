/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Prod.Basic
public import Mathlib.Tactic.Finiteness.Attr

/-! # sublists

`List.Sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

/-! ### sublists -/

@[simp]
/--
theorem `sublists'_nil` / 定理 `sublists'_nil`

English:
theorem sublists'_nil
  statement: sublists' (@nil α) = [[]]
  proof: rfl

@[simp]

中文:
定理 sublists'_nil
  结论: sublists' (@nil α) = [[]]
  证明: rfl

@[simp]
-/
theorem sublists'_nil : sublists' (@nil α) = [[]] :=
  rfl

@[simp]
/--
theorem `sublists'_singleton` / 定理 `sublists'_singleton`

English:
theorem sublists'_singleton
  given: (a : α)
  statement: sublists' [a] = [[], [a]]
  proof: rfl

中文:
定理 sublists'_singleton
  条件: (a : α)
  结论: sublists' [a] = [[], [a]]
  证明: rfl
-/
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl

/--
Definition of `sublists'Aux` / `sublists'Aux` 的定义

English:
definition sublists'Aux
  signature: (a : α) (r₁ r₂ : List (List α))
  body: r₁.foldl (init := r₂) fun r l => r ++ [a :: l]

中文:
定义 sublists'Aux
  签名: (a : α) (r₁ r₂ : 列表 (列表 α))
  定义体: r₁.foldl (init := r₂) fun r l => r ++ [a :: l]
-/
def sublists'Aux (a : α) (r₁ r₂ : List (List α)) : List (List α) :=
  r₁.foldl (init := r₂) fun r l => r ++ [a :: l]

/--
theorem `sublists'Aux_eq_array_foldl` / 定理 `sublists'Aux_eq_array_foldl`

English:
theorem sublists'Aux_eq_array_foldl
  given: (a : α)
  statement: forall (r₁ r₂ : List (List α)),
  proof: by
  intro r₁ r₂
  rw [sublists'Aux]; rw [Array.foldl_toList]
  have := List.foldl_hom Array.toList (g₁ := fun r l => r.push (a :: l))
    (g₂ := fun r l => r ++ [a :: l]) (l := r₁) (init := r₂.toArray) (by simp)
  simpa using this

中文:
定理 sublists'Aux_eq_array_foldl
  条件: (a : α)
  结论: 对任意 (r₁ r₂ : 列表 (列表 α)),
  证明: by
  intro r₁ r₂
  rw [sublists'Aux]; rw [Array.foldl_toList]
  have := List.foldl_hom Array.toList (g₁ := fun r l => r.push (a :: l))
    (g₂ := fun r l => r ++ [a :: l]) (l := r₁) (init := r₂.toArray) (by simp)
  simpa using this
-/
theorem sublists'Aux_eq_array_foldl (a : α) : forall (r₁ r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = ((r₁.toArray).foldl (init := r₂.toArray)
      (fun r l => r.push (a :: l))).toList := by
  intro r₁ r₂
  rw [sublists'Aux]; rw [Array.foldl_toList]
  have := List.foldl_hom Array.toList (g₁ := fun r l => r.push (a :: l))
    (g₂ := fun r l => r ++ [a :: l]) (l := r₁) (init := r₂.toArray) (by simp)
  simpa using this

/--
theorem `sublists'_eq_sublists'Aux` / 定理 `sublists'_eq_sublists'Aux`

English:
theorem sublists'_eq_sublists'Aux
  given: (l : List α)
  proof: by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  rw [← List.foldr_hom Array.toList]
  · intros; congr

中文:
定理 sublists'_eq_sublists'Aux
  条件: (l : 列表 α)
  证明: by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  rw [← List.foldr_hom Array.toList]
  · intros; congr
-/
theorem sublists'_eq_sublists'Aux (l : List α) :
    sublists' l = l.foldr (fun a r => sublists'Aux a r r) [[]] := by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  rw [← List.foldr_hom Array.toList]
  · intros; congr

/--
theorem `sublists'Aux_eq_map` / 定理 `sublists'Aux_eq_map`

English:
theorem sublists'Aux_eq_map
  given: (a : α) (r₁ : List (List α))
  statement: forall (r₂ : List (List α)),
  proof: List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) fun r₁ l ih r₂ => by
    rw [map_append]; rw [map_singleton]; rw [← append_assoc]; rw [← ih]; rw [sublists'Aux]; rw [foldl_append]; rw [foldl]
    simp [sublists'Aux]

@[simp 900]

中文:
定理 sublists'Aux_eq_map
  条件: (a : α) (r₁ : 列表 (列表 α))
  结论: 对任意 (r₂ : 列表 (列表 α)),
  证明: List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) fun r₁ l ih r₂ => by
    rw [map_append]; rw [map_singleton]; rw [← append_assoc]; rw [← ih]; rw [sublists'Aux]; rw [foldl_append]; rw [foldl]
    simp [sublists'Aux]

@[simp 900]
-/
theorem sublists'Aux_eq_map (a : α) (r₁ : List (List α)) : forall (r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = r₂ ++ map (cons a) r₁ :=
  List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) fun r₁ l ih r₂ => by
    rw [map_append]; rw [map_singleton]; rw [← append_assoc]; rw [← ih]; rw [sublists'Aux]; rw [foldl_append]; rw [foldl]
    simp [sublists'Aux]

@[simp 900]
/--
theorem `sublists'_cons` / 定理 `sublists'_cons`

English:
theorem sublists'_cons
  given: (a : α) (l : List α)
  proof: by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]

@[simp]

中文:
定理 sublists'_cons
  条件: (a : α) (l : 列表 α)
  证明: by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]

@[simp]
-/
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]

@[simp]
/--
theorem `mem_sublists'` / 定理 `mem_sublists'`

English:
theorem mem_sublists'
  given: {s t : List α}
  statement: s in sublists' t ↔ s <+ t
  proof: by
  induction t generalizing s with
  | nil =>
    simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  | cons a t IH => ?_
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

@[simp]

中文:
定理 mem_sublists'
  条件: {s t : 列表 α}
  结论: s in sublists' t ↔ s <+ t
  证明: by
  induction t generalizing s with
  | nil =>
    simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  | cons a t IH => ?_
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

@[simp]

Depends on / 依赖: Or.inl, Or.inr, _cons, _nil, cons_cons, eq_nil_of_sublist_nil, generalizing, h.cons_cons, mem_append, mem_map, mem_singleton, sublist_cons_of_sublist, sublists
-/
theorem mem_sublists' {s t : List α} : s in sublists' t ↔ s <+ t := by
  induction t generalizing s with
  | nil =>
    simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  | cons a t IH => ?_
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

@[simp]
/--
theorem `length_sublists'` / 定理 `length_sublists'`

English:
theorem length_sublists'
  statement: forall l : List α, length (sublists' l) = 2 ^ length l

中文:
定理 length_sublists'
  结论: 对任意 l : 列表 α, length (sublists' l) = 2 ^ length l
-/
theorem length_sublists' : forall l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp +arith only [sublists'_cons, length_append, length_sublists' l,
      length_map, length, Nat.pow_succ']

@[simp]
/--
theorem `sublists_nil` / 定理 `sublists_nil`

English:
theorem sublists_nil
  statement: sublists (@nil α) = [[]]
  proof: rfl

@[simp]

中文:
定理 sublists_nil
  结论: sublists (@nil α) = [[]]
  证明: rfl

@[simp]
-/
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl

@[simp]
/--
theorem `sublists_singleton` / 定理 `sublists_singleton`

English:
theorem sublists_singleton
  given: (a : α)
  statement: sublists [a] = [[], [a]]
  proof: rfl

中文:
定理 sublists_singleton
  条件: (a : α)
  结论: sublists [a] = [[], [a]]
  证明: rfl
-/
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl

/--
Definition of `sublistsAux` / `sublistsAux` 的定义

English:
definition sublistsAux
  signature: (a : α) (r : List (List α))
  body: r.foldl (init := []) fun r l => r ++ [l, a :: l]

中文:
定义 sublistsAux
  签名: (a : α) (r : 列表 (列表 α))
  定义体: r.foldl (init := []) fun r l => r ++ [l, a :: l]

Depends on / 依赖: r.foldl
-/
def sublistsAux (a : α) (r : List (List α)) : List (List α) :=
  r.foldl (init := []) fun r l => r ++ [l, a :: l]

/--
theorem `sublistsAux_eq_array_foldl` / 定理 `sublistsAux_eq_array_foldl`

English:
theorem sublistsAux_eq_array_foldl
  proof: by
  funext a r
  simp only [sublistsAux]
  have := foldl_hom Array.toList (g₁ := fun r l => (r.push l).push (a :: l))
    (g₂ := fun r l => r ++ [l, a :: l]) (l := r) (init := #[]) (by simp)
  simpa using this

中文:
定理 sublistsAux_eq_array_foldl
  证明: by
  funext a r
  simp only [sublistsAux]
  have := foldl_hom Array.toList (g₁ := fun r l => (r.push l).push (a :: l))
    (g₂ := fun r l => r ++ [l, a :: l]) (l := r) (init := #[]) (by simp)
  simpa using this
-/
theorem sublistsAux_eq_array_foldl :
    sublistsAux = fun (a : α) (r : List (List α)) =>
      (r.toArray.foldl (init := #[])
        fun r l => (r.push l).push (a :: l)).toList := by
  funext a r
  simp only [sublistsAux]
  have := foldl_hom Array.toList (g₁ := fun r l => (r.push l).push (a :: l))
    (g₂ := fun r l => r ++ [l, a :: l]) (l := r) (init := #[]) (by simp)
  simpa using this

/--
theorem `sublistsAux_eq_flatMap` / 定理 `sublistsAux_eq_flatMap`

English:
theorem sublistsAux_eq_flatMap
  proof: funext fun a => funext fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [flatMap_append]; rw [← ih]; rw [flatMap_singleton]; rw [sublistsAux]; rw [foldl_append]
      simp [sublistsAux])

中文:
定理 sublistsAux_eq_flatMap
  证明: funext fun a => funext fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [flatMap_append]; rw [← ih]; rw [flatMap_singleton]; rw [sublistsAux]; rw [foldl_append]
      simp [sublistsAux])

Depends on / 依赖: List.reverseRecOn, flatMap_append, flatMap_singleton, foldl_append, reverseRecOn, sublistsAux
-/
theorem sublistsAux_eq_flatMap :
    sublistsAux = fun (a : α) (r : List (List α)) => r.flatMap fun l => [l, a :: l] :=
  funext fun a => funext fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [flatMap_append]; rw [← ih]; rw [flatMap_singleton]; rw [sublistsAux]; rw [foldl_append]
      simp [sublistsAux])

/--
theorem `sublists_append` / 定理 `sublists_append`

English:
theorem sublists_append
  given: (l₁ l₂ : List α)
  proof: by
  simp only [sublists, foldr_append]
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [foldr_cons]; rw [ih]
    simp [List.flatMap, flatten_flatten, Function.comp_def]

中文:
定理 sublists_append
  条件: (l₁ l₂ : 列表 α)
  证明: by
  simp only [sublists, foldr_append]
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [foldr_cons]; rw [ih]
    simp [List.flatMap, flatten_flatten, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, List.flatMap, comp_def, flatMap, flatten_flatten, foldr_append, foldr_cons, sublists
-/
theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x)) := by
  simp only [sublists, foldr_append]
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [foldr_cons]; rw [ih]
    simp [List.flatMap, flatten_flatten, Function.comp_def]

/--
theorem `sublists_cons` / 定理 `sublists_cons`

English:
theorem sublists_cons
  given: (a : α) (l : List α)
  proof: show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  simp only [sublists_singleton, map_cons, bind_eq_flatMap, nil_append, cons_append, map_nil]

@[simp]

中文:
定理 sublists_cons
  条件: (a : α) (l : 列表 α)
  证明: show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  simp only [sublists_singleton, map_cons, bind_eq_flatMap, nil_append, cons_append, map_nil]

@[simp]

Depends on / 依赖: bind_eq_flatMap, cons_append, map_cons, map_nil, nil_append, sublists, sublists_append, sublists_singleton
-/
theorem sublists_cons (a : α) (l : List α) :
    sublists (a :: l) = sublists l >>= (fun x => [x, a :: x]) :=
  show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  simp only [sublists_singleton, map_cons, bind_eq_flatMap, nil_append, cons_append, map_nil]

@[simp]
/--
theorem `sublists_concat` / 定理 `sublists_concat`

English:
theorem sublists_concat
  given: (l : List α) (a : α)
  proof: by
  rw [sublists_append]; rw [sublists_singleton]; rw [bind_eq_flatMap]; rw [flatMap_cons]; rw [flatMap_cons]; rw [flatMap_nil]; rw [map_id'' append_nil]; rw [append_nil]

中文:
定理 sublists_concat
  条件: (l : 列表 α) (a : α)
  证明: by
  rw [sublists_append]; rw [sublists_singleton]; rw [bind_eq_flatMap]; rw [flatMap_cons]; rw [flatMap_cons]; rw [flatMap_nil]; rw [map_id'' append_nil]; rw [append_nil]

Depends on / 依赖: append_nil, bind_eq_flatMap, flatMap_cons, flatMap_nil, map_id, sublists_append, sublists_singleton
-/
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append]; rw [sublists_singleton]; rw [bind_eq_flatMap]; rw [flatMap_cons]; rw [flatMap_cons]; rw [flatMap_nil]; rw [map_id'' append_nil]; rw [append_nil]

/--
theorem `sublists_reverse` / 定理 `sublists_reverse`

English:
theorem sublists_reverse
  given: (l : List α)
  statement: sublists (reverse l) = map reverse (sublists' l)
  proof: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      bind_eq_flatMap, map_map, flatMap_cons, append_nil, flatMap_nil, Function.comp_def]

中文:
定理 sublists_reverse
  条件: (l : 列表 α)
  结论: sublists (reverse l) = map reverse (sublists' l)
  证明: by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      bind_eq_flatMap, map_map, flatMap_cons, append_nil, flatMap_nil, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, _cons, append_nil, bind_eq_flatMap, comp_def, flatMap_cons, flatMap_nil, map_append, map_map, reverse_cons, sublists, sublists_append, sublists_singleton
-/
theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      bind_eq_flatMap, map_map, flatMap_cons, append_nil, flatMap_nil, Function.comp_def]

/--
theorem `sublists_eq_sublists'` / 定理 `sublists_eq_sublists'`

English:
theorem sublists_eq_sublists'
  given: (l : List α)
  statement: sublists l = map reverse (sublists' (reverse l))
  proof: by
  rw [← sublists_reverse]; rw [reverse_reverse]

中文:
定理 sublists_eq_sublists'
  条件: (l : 列表 α)
  结论: sublists l = map reverse (sublists' (reverse l))
  证明: by
  rw [← sublists_reverse]; rw [reverse_reverse]

Depends on / 依赖: reverse_reverse, sublists_reverse
-/
theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse]; rw [reverse_reverse]

/--
theorem `sublists'_reverse` / 定理 `sublists'_reverse`

English:
theorem sublists'_reverse
  given: (l : List α)
  statement: sublists' (reverse l) = map reverse (sublists l)
  proof: by
  simp only [sublists_eq_sublists', map_map, map_id'' reverse_reverse, Function.comp_def]

中文:
定理 sublists'_reverse
  条件: (l : 列表 α)
  结论: sublists' (reverse l) = map reverse (sublists l)
  证明: by
  simp only [sublists_eq_sublists', map_map, map_id'' reverse_reverse, Function.comp_def]
-/
theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id'' reverse_reverse, Function.comp_def]

/--
theorem `sublists'_eq_sublists` / 定理 `sublists'_eq_sublists`

English:
theorem sublists'_eq_sublists
  given: (l : List α)
  statement: sublists' l = map reverse (sublists (reverse l))
  proof: by
  rw [← sublists'_reverse]; rw [reverse_reverse]

@[simp]

中文:
定理 sublists'_eq_sublists
  条件: (l : 列表 α)
  结论: sublists' l = map reverse (sublists (reverse l))
  证明: by
  rw [← sublists'_reverse]; rw [reverse_reverse]

@[simp]
-/
theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse]; rw [reverse_reverse]

@[simp]
/--
theorem `mem_sublists` / 定理 `mem_sublists`

English:
theorem mem_sublists
  given: {s t : List α}
  statement: s in sublists t ↔ s <+ t
  proof: by
  rw [← reverse_sublist]; rw [← mem_sublists']; rw [sublists'_reverse]; rw [mem_map_of_injective reverse_injective]

@[simp]

中文:
定理 mem_sublists
  条件: {s t : 列表 α}
  结论: s in sublists t ↔ s <+ t
  证明: by
  rw [← reverse_sublist]; rw [← mem_sublists']; rw [sublists'_reverse]; rw [mem_map_of_injective reverse_injective]

@[simp]

Depends on / 依赖: _reverse, mem_map_of_injective, mem_sublists, reverse_injective, reverse_sublist, sublists
-/
theorem mem_sublists {s t : List α} : s in sublists t ↔ s <+ t := by
  rw [← reverse_sublist]; rw [← mem_sublists']; rw [sublists'_reverse]; rw [mem_map_of_injective reverse_injective]

@[simp]
/--
theorem `length_sublists` / 定理 `length_sublists`

English:
theorem length_sublists
  given: (l : List α)
  statement: length (sublists l) = 2 ^ length l
  proof: by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

中文:
定理 length_sublists
  条件: (l : 列表 α)
  结论: length (sublists l) = 2 ^ length l
  证明: by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

Depends on / 依赖: length_map, length_reverse, length_sublists, sublists_eq_sublists
-/
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]

/--
theorem `map_pure_sublist_sublists` / 定理 `map_pure_sublist_sublists`

English:
theorem map_pure_sublist_sublists
  given: (l : List α)
  statement: map pure l <+ sublists l
  proof: by
  induction l using reverseRecOn <;> simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons_self]
  case append_singleton l a ih =>
    exact ((append_sublist_append_left _).2 <|
singleton_sublist.2 mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)

中文:
定理 map_pure_sublist_sublists
  条件: (l : 列表 α)
  结论: map pure l <+ sublists l
  证明: by
  induction l using reverseRecOn <;> simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons_self]
  case append_singleton l a ih =>
    exact ((append_sublist_append_left _).2 <|
singleton_sublist.2 mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)

Depends on / 依赖: append_singleton, append_sublist_append_left, append_sublist_append_right, map_append, mem_map, mem_sublists, nil_sublist, reverseRecOn, singleton_sublist, sublist_cons_self, sublists_concat, sublists_nil
-/
theorem map_pure_sublist_sublists (l : List α) : map pure l <+ sublists l := by
  induction l using reverseRecOn <;> simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons_self]
  case append_singleton l a ih =>
    exact ((append_sublist_append_left _).2 <|
singleton_sublist.2 mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)

/-! ### sublistsLen -/

/--
Definition of `sublistsLenAux` / `sublistsLenAux` 的定义

English:
definition sublistsLenAux
  signature: : Nat -> List α -> (List α -> β) -> List β -> List β

中文:
定义 sublistsLenAux
  签名: : 自然数 -> 列表 α -> (列表 α -> β) -> 列表 β -> 列表 β
-/
def sublistsLenAux : Nat -> List α -> (List α -> β) -> List β -> List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)

/--
Definition of `sublistsLen` / `sublistsLen` 的定义

English:
definition sublistsLen
  signature: (n : Nat) (l : List α)
  body: sublistsLenAux n l id []

中文:
定义 sublistsLen
  签名: (n : 自然数) (l : 列表 α)
  定义体: sublistsLenAux n l id []

Depends on / 依赖: sublistsLenAux
-/
def sublistsLen (n : Nat) (l : List α) : List (List α) :=
  sublistsLenAux n l id []

/--
theorem `sublistsLenAux_append` / 定理 `sublistsLenAux_append`

English:
theorem sublistsLenAux_append

中文:
定理 sublistsLenAux_append
-/
theorem sublistsLenAux_append :
    forall (n : Nat) (l : List α) (f : List α -> β) (g : β -> γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => by unfold sublistsLenAux; simp
  | _ + 1, [], _, _, _, _ => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublistsLenAux
    simp only [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl,
      sublistsLenAux_append]

/--
theorem `sublistsLenAux_eq` / 定理 `sublistsLenAux_eq`

English:
theorem sublistsLenAux_eq
  given: (l : List α) (n) (f : List α -> β) (r)
  proof: by
  rw [sublistsLen]; rw [← sublistsLenAux_append]; rfl

中文:
定理 sublistsLenAux_eq
  条件: (l : 列表 α) (n) (f : 列表 α -> β) (r)
  证明: by
  rw [sublistsLen]; rw [← sublistsLenAux_append]; rfl

Depends on / 依赖: sublistsLen, sublistsLenAux_append
-/
theorem sublistsLenAux_eq (l : List α) (n) (f : List α -> β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublistsLen]; rw [← sublistsLenAux_append]; rfl

/--
theorem `sublistsLenAux_zero` / 定理 `sublistsLenAux_zero`

English:
theorem sublistsLenAux_zero
  given: (l : List α) (f : List α -> β) (r)
  proof: by cases l <;> rfl

@[simp]

中文:
定理 sublistsLenAux_zero
  条件: (l : 列表 α) (f : 列表 α -> β) (r)
  证明: by cases l <;> rfl

@[simp]
-/
theorem sublistsLenAux_zero (l : List α) (f : List α -> β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl

@[simp]
/--
theorem `sublistsLen_zero` / 定理 `sublistsLen_zero`

English:
theorem sublistsLen_zero
  given: (l : List α)
  statement: sublistsLen 0 l = [[]]
  proof: sublistsLenAux_zero _ _ _

@[simp]

中文:
定理 sublistsLen_zero
  条件: (l : 列表 α)
  结论: sublistsLen 0 l = [[]]
  证明: sublistsLenAux_zero _ _ _

@[simp]

Depends on / 依赖: sublistsLenAux_zero
-/
theorem sublistsLen_zero (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _

@[simp]
/--
theorem `sublistsLen_succ_nil` / 定理 `sublistsLen_succ_nil`

English:
theorem sublistsLen_succ_nil
  given: (n)
  statement: sublistsLen (n + 1) (@nil α) = []
  proof: rfl

@[simp]

中文:
定理 sublistsLen_succ_nil
  条件: (n)
  结论: sublistsLen (n + 1) (@nil α) = []
  证明: rfl

@[simp]

Depends on / 依赖: exists_notMem_finite, finite_toSet, hs.exists_notMem_finite, t.finite_toSet
-/
theorem sublistsLen_succ_nil (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl

@[simp]
/--
theorem `sublistsLen_succ_cons` / 定理 `sublistsLen_succ_cons`

English:
theorem sublistsLen_succ_cons
  given: (n) (a : α) (l)
  proof: by
  rw [sublistsLen]; rw [sublistsLenAux]; rw [sublistsLenAux_eq]; rw [sublistsLenAux_eq]; rw [map_id]; rw [append_nil]; rfl

中文:
定理 sublistsLen_succ_cons
  条件: (n) (a : α) (l)
  证明: by
  rw [sublistsLen]; rw [sublistsLenAux]; rw [sublistsLenAux_eq]; rw [sublistsLenAux_eq]; rw [map_id]; rw [append_nil]; rfl

Depends on / 依赖: append_nil, map_id, sublistsLen, sublistsLenAux, sublistsLenAux_eq
-/
theorem sublistsLen_succ_cons (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublistsLen]; rw [sublistsLenAux]; rw [sublistsLenAux_eq]; rw [sublistsLenAux_eq]; rw [map_id]; rw [append_nil]; rfl

/--
theorem `sublistsLen_one` / 定理 `sublistsLen_one`

English:
theorem sublistsLen_one
  given: (l : List α)
  statement: sublistsLen 1 l = l.reverse.map ([·])
  proof: l.rec (by rw [sublistsLen_succ_nil, reverse_nil, map_nil]) fun a s ih => by
    rw [sublistsLen_succ_cons]; rw [ih]; rw [reverse_cons]; rw [map_append]; rw [sublistsLen_zero]; rfl

@[simp]

中文:
定理 sublistsLen_one
  条件: (l : 列表 α)
  结论: sublistsLen 1 l = l.reverse.map ([·])
  证明: l.rec (by rw [sublistsLen_succ_nil, reverse_nil, map_nil]) fun a s ih => by
    rw [sublistsLen_succ_cons]; rw [ih]; rw [reverse_cons]; rw [map_append]; rw [sublistsLen_zero]; rfl

@[simp]

Depends on / 依赖: l.rec, map_append, map_nil, reverse_cons, reverse_nil, sublistsLen_succ_cons, sublistsLen_succ_nil, sublistsLen_zero
-/
theorem sublistsLen_one (l : List α) : sublistsLen 1 l = l.reverse.map ([·]) :=
  l.rec (by rw [sublistsLen_succ_nil, reverse_nil, map_nil]) fun a s ih => by
    rw [sublistsLen_succ_cons]; rw [ih]; rw [reverse_cons]; rw [map_append]; rw [sublistsLen_zero]; rfl

@[simp]
/--
theorem `length_sublistsLen` / 定理 `length_sublistsLen`

English:
theorem length_sublistsLen

中文:
定理 length_sublistsLen

Depends on / 依赖: h.to_subtype.natEmbedding, natEmbedding, to_subtype
-/
theorem length_sublistsLen :
    forall (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
  | _ + 1, [] => by simp
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons]; rw [length_append]; rw [length_sublistsLen (n + 1) l]; rw [length_map]; rw [length_sublistsLen n l]; rw [length_cons]; rw [Nat.choose_succ_succ]; rw [Nat.add_comm]

/--
theorem `sublistsLen_sublist_sublists'` / 定理 `sublistsLen_sublist_sublists'`

English:
theorem sublistsLen_sublist_sublists'

中文:
定理 sublistsLen_sublist_sublists'

Depends on / 依赖: Embedding, Embedding.subtype, Finset, Finset.range, hs.natEmbedding, natEmbedding, subtype
-/
theorem sublistsLen_sublist_sublists' :
    forall (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => by simp
  | _ + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons]; rw [sublists'_cons]
    exact (sublistsLen_sublist_sublists' _ _).append ((sublistsLen_sublist_sublists' _ _).map _)

/--
theorem `sublistsLen_sublist_of_sublist` / 定理 `sublistsLen_sublist_of_sublist`

English:
theorem sublistsLen_sublist_of_sublist
  given: (n) {l₁ l₂ : List α} (h : l₁ <+ l₂)
  proof: by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction h with
  | slnil => rfl
  | cons a _ IH =>
    refine IH.trans ?_
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  | cons_cons a s IH => simpa only [sublistsLen_succ_cons] using IH.append ((IHn s).map _)

中文:
定理 sublistsLen_sublist_of_sublist
  条件: (n) {l₁ l₂ : 列表 α} (h : l₁ <+ l₂)
  证明: by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction h with
  | slnil => rfl
  | cons a _ IH =>
    refine IH.trans ?_
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  | cons_cons a s IH => simpa only [sublistsLen_succ_cons] using IH.append ((IHn s).map _)

Depends on / 依赖: IH.append, IH.trans, append, cons_cons, generalizing, sublist_append_left, sublistsLen_succ_cons
-/
theorem sublistsLen_sublist_of_sublist (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ := by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction h with
  | slnil => rfl
  | cons a _ IH =>
    refine IH.trans ?_
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  | cons_cons a s IH => simpa only [sublistsLen_succ_cons] using IH.append ((IHn s).map _)

/--
theorem `length_of_sublistsLen` / 定理 `length_of_sublistsLen`

English:
theorem length_of_sublistsLen

中文:
定理 length_of_sublistsLen
-/
theorem length_of_sublistsLen :
    forall {n} {l l' : List α}, l' in sublistsLen n l -> length l' = n
  | 0, l, l', h => by simp_all
  | n + 1, a :: l, l', h => by
    rw [sublistsLen_succ_cons]; rw [mem_append]; rw [mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublistsLen h
    · exact congr_arg (· + 1) (length_of_sublistsLen h)

/--
theorem `mem_sublistsLen_self` / 定理 `mem_sublistsLen_self`

English:
theorem mem_sublistsLen_self
  given: {l l' : List α} (h : l' <+ l)
  proof: by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a s IH =>
    rcases l₁ with - | ⟨b, l₁⟩
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  | cons_cons a s IH =>
    rw [length]; rw [sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)

@[simp]

中文:
定理 mem_sublistsLen_self
  条件: {l l' : 列表 α} (h : l' <+ l)
  证明: by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a s IH =>
    rcases l₁ with - | ⟨b, l₁⟩
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  | cons_cons a s IH =>
    rw [length]; rw [sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)

@[simp]

Depends on / 依赖: cons_cons, length, mem_append_left, mem_append_right, mem_map, sublistsLen_succ_cons
-/
theorem mem_sublistsLen_self {l l' : List α} (h : l' <+ l) :
    l' in sublistsLen (length l') l := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a s IH =>
    rcases l₁ with - | ⟨b, l₁⟩
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  | cons_cons a s IH =>
    rw [length]; rw [sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)

@[simp]
/--
theorem `mem_sublistsLen` / 定理 `mem_sublistsLen`

English:
theorem mem_sublistsLen
  given: {n} {l l' : List α}
  proof: ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩

中文:
定理 mem_sublistsLen
  条件: {n} {l l' : 列表 α}
  证明: ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩

Depends on / 依赖: length_of_sublistsLen, mem_sublists, mem_sublistsLen_self, sublistsLen_sublist_sublists, subset
-/
theorem mem_sublistsLen {n} {l l' : List α} :
    l' in sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩

/--
theorem `sublistsLen_of_length_lt` / 定理 `sublistsLen_of_length_lt`

English:
theorem sublistsLen_of_length_lt
  given: {n} {l : List α} (h : l.length < n)
  statement: sublistsLen n l = []
  proof: eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_ge (Sublist.length_le hs)

@[simp]

中文:
定理 sublistsLen_of_length_lt
  条件: {n} {l : 列表 α} (h : l.length < n)
  结论: sublistsLen n l = []
  证明: eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_ge (Sublist.length_le hs)

@[simp]

Depends on / 依赖: Sublist, Sublist.length_le, eq_nil_iff_forall_not_mem, eq_nil_iff_forall_not_mem.mpr, h.trans_eq, hl.symm, length_le, mem_sublistsLen, mem_sublistsLen.not.mpr, not_ge, trans_eq
-/
theorem sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen n l = [] :=
  eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_ge (Sublist.length_le hs)

@[simp]
/--
theorem `sublistsLen_length` / 定理 `sublistsLen_length`

English:
theorem sublistsLen_length
  statement: forall l : List α, sublistsLen l.length l = [l]

中文:
定理 sublistsLen_length
  结论: 对任意 l : 列表 α, sublistsLen l.length l = [l]
-/
theorem sublistsLen_length : forall l : List α, sublistsLen l.length l = [l]
  | [] => rfl
  | a :: l => by
    simp only [length, sublistsLen_succ_cons, sublistsLen_length, map,
      sublistsLen_of_length_lt (lt_succ_self _), nil_append]

open Function

/--
theorem `Pairwise.sublists'` / 定理 `Pairwise.sublists'`

English:
theorem Pairwise.sublists'
  given: {R}

中文:
定理 两两.sublists'
  条件: {R}
-/
theorem Pairwise.sublists' {R} :
    forall {l : List α}, Pairwise R l -> Pairwise (Lex (Function.swap R)) (sublists' l)
  | _, Pairwise.nil => pairwise_singleton _ _
  | _, @Pairwise.cons _ _ a l H₁ H₂ => by
    simp only [sublists'_cons, pairwise_append, pairwise_map, mem_sublists', mem_map, exists_imp,
      and_imp]
    refine ⟨H₂.sublists', H₂.sublists'.imp fun l₁ => Lex.cons l₁, ?_⟩
    rintro l₁ sl₁ x l₂ _ rfl
    rcases l₁ with - | ⟨b, l₁⟩; · constructor
    exact Lex.rel (H₁ _ <| sl₁.subset mem_cons_self)

/--
theorem `pairwise_sublists` / 定理 `pairwise_sublists`

English:
theorem pairwise_sublists
  given: {R} {l : List α} (H : Pairwise R l)
  proof: by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

@[simp]

中文:
定理 pairwise_sublists
  条件: {R} {l : 列表 α} (H : 两两 R l)
  证明: by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

@[simp]

Depends on / 依赖: _reverse, pairwise_map, pairwise_reverse, sublists
-/
theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (Lex R on reverse) (sublists l) := by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

@[simp]
/--
theorem `nodup_sublists` / 定理 `nodup_sublists`

English:
theorem nodup_sublists
  given: {l : List α}
  statement: Nodup (sublists l) ↔ Nodup l
  proof: ⟨fun h => (h.sublist (map_pure_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩

@[simp]

中文:
定理 nodup_sublists
  条件: {l : 列表 α}
  结论: Nodup (sublists l) ↔ Nodup l
  证明: ⟨fun h => (h.sublist (map_pure_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩

@[simp]

Depends on / 依赖: h.sublist, h.to_ne, map_pure_sublist_sublists, of_map, pairwise_sublists, sublist, to_ne
-/
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.sublist (map_pure_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩

@[simp]
/--
theorem `nodup_sublists'` / 定理 `nodup_sublists'`

English:
theorem nodup_sublists'
  given: {l : List α}
  statement: Nodup (sublists' l) ↔ Nodup l
  proof: by
  rw [sublists'_eq_sublists]; rw [nodup_map_iff reverse_injective]; rw [nodup_sublists]; rw [nodup_reverse]

protected alias ⟨Nodup.of_sublists, Nodup.sublists⟩ := nodup_sublists

protected alias ⟨Nodup.of_sublists', _⟩ := nodup_sublists'

中文:
定理 nodup_sublists'
  条件: {l : 列表 α}
  结论: Nodup (sublists' l) ↔ Nodup l
  证明: by
  rw [sublists'_eq_sublists]; rw [nodup_map_iff reverse_injective]; rw [nodup_sublists]; rw [nodup_reverse]

protected alias ⟨Nodup.of_sublists, Nodup.sublists⟩ := nodup_sublists

protected alias ⟨Nodup.of_sublists', _⟩ := nodup_sublists'

Depends on / 依赖: _eq_sublists, nodup_map_iff, nodup_reverse, nodup_sublists, reverse_injective, sublists
-/
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists]; rw [nodup_map_iff reverse_injective]; rw [nodup_sublists]; rw [nodup_reverse]

protected alias ⟨Nodup.of_sublists, Nodup.sublists⟩ := nodup_sublists

protected alias ⟨Nodup.of_sublists', _⟩ := nodup_sublists'

/--
theorem `nodup_sublistsLen` / 定理 `nodup_sublistsLen`

English:
theorem nodup_sublistsLen
  given: (n : Nat) {l : List α} (h : Nodup l)
  statement: (sublistsLen n l).Nodup
  proof: by
  have : Pairwise (· != ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert! h using 3; simp [eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)

中文:
定理 nodup_sublistsLen
  条件: (n : 自然数) {l : 列表 α} (h : Nodup l)
  结论: (sublistsLen n l).Nodup
  证明: by
  have : Pairwise (· != ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert! h using 3; simp [eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)

Depends on / 依赖: Lex.to_ne, Pairwise, Pairwise.imp, convert, eq_comm, h.sublists, l.sublists, sublist, sublists, sublistsLen_sublist_sublists, this.sublist, to_ne
-/
theorem nodup_sublistsLen (n : Nat) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup := by
  have : Pairwise (· != ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert! h using 3; simp [eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)

/--
theorem `sublists_map` / 定理 `sublists_map`

English:
theorem sublists_map
  given: (f : α -> β)
  statement: forall (l : List α),

中文:
定理 sublists_map
  条件: (f : α -> β)
  结论: 对任意 (l : 列表 α),
-/
theorem sublists_map (f : α -> β) : forall (l : List α),
    sublists (map f l) = map (map f) (sublists l)
  | [] => by simp
  | a::l => by
    rw [map_cons]; rw [sublists_cons]; rw [bind_eq_flatMap]; rw [sublists_map f l]; rw [sublists_cons]; rw [bind_eq_flatMap]; rw [map_eq_flatMap]; rw [map_eq_flatMap]
    induction sublists l <;> simp [*]

/--
theorem `sublists'_map` / 定理 `sublists'_map`

English:
theorem sublists'_map
  given: (f : α -> β)
  statement: forall (l : List α),

中文:
定理 sublists'_map
  条件: (f : α -> β)
  结论: 对任意 (l : 列表 α),
-/
theorem sublists'_map (f : α -> β) : forall (l : List α),
    sublists' (map f l) = map (map f) (sublists' l)
  | [] => by simp
  | a::l => by simp [map_cons, sublists'_cons, sublists'_map f l, Function.comp]

/--
theorem `sublists_perm_sublists'` / 定理 `sublists_perm_sublists'`

English:
theorem sublists_perm_sublists'
  given: (l : List α)
  statement: sublists l ~ sublists' l
  proof: by
  rw [← map_get_finRange l]; rw [sublists_map]; rw [sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (nodup_finRange _)
  · exact (nodup_sublists'.mpr (nodup_finRange _))

中文:
定理 sublists_perm_sublists'
  条件: (l : 列表 α)
  结论: sublists l ~ sublists' l
  证明: by
  rw [← map_get_finRange l]; rw [sublists_map]; rw [sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (nodup_finRange _)
  · exact (nodup_sublists'.mpr (nodup_finRange _))

Depends on / 依赖: Perm.map, _map, map_get_finRange, nodup_finRange, nodup_sublists, nodup_sublists.mpr, perm_ext_iff_of_nodup, sublists, sublists_map
-/
theorem sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l := by
  rw [← map_get_finRange l]; rw [sublists_map]; rw [sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (nodup_finRange _)
  · exact (nodup_sublists'.mpr (nodup_finRange _))

/--
theorem `Sublist.sublists'` / 定理 `Sublist.sublists'`

English:
theorem Sublist.sublists'
  statement: {l₁ l₂ : List α}
  proof: by
  induction sublist with
  | slnil => exact .refl _
  | cons a _ ih =>
    rw [sublists'_cons]
    exact ih.trans (List.sublist_append_left ..)
  | cons_cons a _ ih =>
    rw [sublists'_cons]; rw [sublists'_cons]
    exact ih.append (ih.map _)

@[simp]

中文:
定理 子表.sublists'
  结论: {l₁ l₂ : 列表 α}
  证明: by
  induction sublist with
  | slnil => exact .refl _
  | cons a _ ih =>
    rw [sublists'_cons]
    exact ih.trans (List.sublist_append_left ..)
  | cons_cons a _ ih =>
    rw [sublists'_cons]; rw [sublists'_cons]
    exact ih.append (ih.map _)

@[simp]

Depends on / 依赖: List.sublist_append_left, _cons, append, cons_cons, ih.append, ih.map, ih.trans, sublist, sublist_append_left, sublists
-/
theorem Sublist.sublists' {l₁ l₂ : List α}
    (sublist : l₁ <+ l₂) :
    l₁.sublists' <+ l₂.sublists' := by
  induction sublist with
  | slnil => exact .refl _
  | cons a _ ih =>
    rw [sublists'_cons]
    exact ih.trans (List.sublist_append_left ..)
  | cons_cons a _ ih =>
    rw [sublists'_cons]; rw [sublists'_cons]
    exact ih.append (ih.map _)

@[simp]
/--
theorem `sublists'_sublist_sublists'_iff` / 定理 `sublists'_sublist_sublists'_iff`

English:
theorem sublists'_sublist_sublists'_iff
  given: {l₁ l₂ : List α}
  proof: Sublist.sublists'
mp sublist := mem_sublists'.mp sublist.subset mem_sublists'.mpr .refl _

中文:
定理 sublists'_sublist_sublists'_iff
  条件: {l₁ l₂ : 列表 α}
  证明: Sublist.sublists'
mp sublist := mem_sublists'.mp sublist.subset mem_sublists'.mpr .refl _
-/
theorem sublists'_sublist_sublists'_iff {l₁ l₂ : List α} :
    l₁.sublists' <+ l₂.sublists' ↔ l₁ <+ l₂ where
  mpr := Sublist.sublists'
mp sublist := mem_sublists'.mp sublist.subset mem_sublists'.mpr .refl _

/--
theorem `subperm_of_sublists'_subperm_sublists'` / 定理 `subperm_of_sublists'_subperm_sublists'`

English:
theorem subperm_of_sublists'_subperm_sublists'
  statement: {l₁ l₂ : List α}
  proof: Sublist.subperm mem_sublists'.mp subperm.subset mem_sublists'.mpr .refl _

中文:
定理 subperm_of_sublists'_subperm_sublists'
  结论: {l₁ l₂ : 列表 α}
  证明: Sublist.subperm mem_sublists'.mp subperm.subset mem_sublists'.mpr .refl _

Depends on / 依赖: Sublist, Sublist.subperm, mem_sublists, subperm, subperm.subset, subset
-/
theorem subperm_of_sublists'_subperm_sublists' {l₁ l₂ : List α}
    (subperm : l₁.sublists' <+~ l₂.sublists') : l₁ <+~ l₂ :=
Sublist.subperm mem_sublists'.mp subperm.subset mem_sublists'.mpr .refl _

/--
theorem `sublists_cons_perm_append` / 定理 `sublists_cons_perm_append`

English:
theorem sublists_cons_perm_append
  given: (a : α) (l : List α)
  proof: Perm.trans (sublists_perm_sublists' _) by
  rw [sublists'_cons]
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)

中文:
定理 sublists_cons_perm_append
  条件: (a : α) (l : 列表 α)
  证明: Perm.trans (sublists_perm_sublists' _) by
  rw [sublists'_cons]
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)

Depends on / 依赖: Perm.append, Perm.map, Perm.trans, _cons, append, sublists, sublists_perm_sublists
-/
theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
Perm.trans (sublists_perm_sublists' _) by
  rw [sublists'_cons]
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)

/--
theorem `revzip_sublists` / 定理 `revzip_sublists`

English:
theorem revzip_sublists
  given: (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists)
  statement: l₁ ++ l₂ ~ l
  proof: by
  rw [revzip] at h
  induction l using List.reverseRecOn generalizing l₁ l₂ with
  | nil =>
    have : l₁ = [] ∧ l₂ = [] := by simpa using h
    simp [this]
  | append_singleton l' a ih =>
    rw [sublists_concat]; rw [reverse_append]; rw [zip_append (by simp)]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
    simp only [Prod.mk_inj, mem_map, mem_append, Prod.map_apply, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _

中文:
定理 revzip_sublists
  条件: (l l₁ l₂ : 列表 α) (h : (l₁, l₂) in revzip l.sublists)
  结论: l₁ ++ l₂ ~ l
  证明: by
  rw [revzip] at h
  induction l using List.reverseRecOn generalizing l₁ l₂ with
  | nil =>
    have : l₁ = [] ∧ l₂ = [] := by simpa using h
    simp [this]
  | append_singleton l' a ih =>
    rw [sublists_concat]; rw [reverse_append]; rw [zip_append (by simp)]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
    simp only [Prod.mk_inj, mem_map, mem_append, Prod.map_apply, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _

Depends on / 依赖: List.reverseRecOn, Prod.exists, Prod.map_apply, Prod.mk_inj, append_assoc, append_ri, append_singleton, generalizing, map_apply, map_reverse, mem_append, mem_map, mk_inj, reverseRecOn, reverse_append, revzip, sublists_concat, zip_append, zip_map_left, zip_map_right
-/
theorem revzip_sublists (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists) : l₁ ++ l₂ ~ l := by
  rw [revzip] at h
  induction l using List.reverseRecOn generalizing l₁ l₂ with
  | nil =>
    have : l₁ = [] ∧ l₂ = [] := by simpa using h
    simp [this]
  | append_singleton l' a ih =>
    rw [sublists_concat]; rw [reverse_append]; rw [zip_append (by simp)]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
    simp only [Prod.mk_inj, mem_map, mem_append, Prod.map_apply, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _

/--
theorem `revzip_sublists'` / 定理 `revzip_sublists'`

English:
theorem revzip_sublists'
  given: (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists')
  statement: l₁ ++ l₂ ~ l
  proof: by
  rw [revzip] at h
  induction l generalizing l₁ l₂ with
  | nil =>
    simp_all only [sublists'_nil, reverse_cons, reverse_nil, nil_append, zip_cons_cons,
      zip_nil_right, mem_singleton, Prod.mk.injEq, append_nil, Perm.refl]
  | cons a l IH =>
    rw [sublists'_cons]; rw [reverse_append]; rw [zip_append]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
      <;> [simp only [mem_append, mem_map, Prod.map_apply, id_eq, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right] at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _

中文:
定理 revzip_sublists'
  条件: (l l₁ l₂ : 列表 α) (h : (l₁, l₂) in revzip l.sublists')
  结论: l₁ ++ l₂ ~ l
  证明: by
  rw [revzip] at h
  induction l generalizing l₁ l₂ with
  | nil =>
    simp_all only [sublists'_nil, reverse_cons, reverse_nil, nil_append, zip_cons_cons,
      zip_nil_right, mem_singleton, Prod.mk.injEq, append_nil, Perm.refl]
  | cons a l IH =>
    rw [sublists'_cons]; rw [reverse_append]; rw [zip_append]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
      <;> [simp only [mem_append, mem_map, Prod.map_apply, id_eq, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right] at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _

Depends on / 依赖: Perm.refl, Prod.exists, Prod.map_apply, Prod.mk.injEq, _cons, _nil, append_nil, exists_eq_right_right, generalizing, id_eq, map_apply, map_reverse, mem_append, mem_map, mem_singleton, nil_append, reverse_append, reverse_cons, reverse_nil, revzip
-/
theorem revzip_sublists' (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists') : l₁ ++ l₂ ~ l := by
  rw [revzip] at h
  induction l generalizing l₁ l₂ with
  | nil =>
    simp_all only [sublists'_nil, reverse_cons, reverse_nil, nil_append, zip_cons_cons,
      zip_nil_right, mem_singleton, Prod.mk.injEq, append_nil, Perm.refl]
  | cons a l IH =>
    rw [sublists'_cons]; rw [reverse_append]; rw [zip_append]; rw [← map_reverse]; rw [zip_map_right]; rw [zip_map_left] at *
      <;> [simp only [mem_append, mem_map, Prod.map_apply, id_eq, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right] at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _

/--
theorem `range_bind_sublistsLen_perm` / 定理 `range_bind_sublistsLen_perm`

English:
theorem range_bind_sublistsLen_perm
  given: (l : List α)
  proof: by
  induction l with
  | nil => simp [range_succ]
  | cons h tl l_ih =>
    simp_rw [range_succ_eq_map, length, flatMap_cons, flatMap_map, sublistsLen_succ_cons,
      sublists'_cons, List.sublistsLen_zero, List.singleton_append]
    refine ((flatMap_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans ?_
    simp_rw [← List.map_flatMap, ← cons_append]
    rw [← List.singleton_append]; rw [← List.sublistsLen_zero tl]
    refine Perm.append ?_ (l_ih.map _)
    rw [List.range_succ]; rw [flatMap_append]; rw [flatMap_singleton]; rw [sublistsLen_of_length_lt (Nat.lt_succ_self _)]; rw [append_nil]; rw [← List.flatMap_map Nat.succ fun n => sublistsLen n tl]; rw [← flatMap_cons (f := fun n => sublistsLen n tl)]; rw [← range_succ_eq_map]
    exact l_ih

中文:
定理 range_bind_sublistsLen_perm
  条件: (l : 列表 α)
  证明: by
  induction l with
  | nil => simp [range_succ]
  | cons h tl l_ih =>
    simp_rw [range_succ_eq_map, length, flatMap_cons, flatMap_map, sublistsLen_succ_cons,
      sublists'_cons, List.sublistsLen_zero, List.singleton_append]
    refine ((flatMap_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans ?_
    simp_rw [← List.map_flatMap, ← cons_append]
    rw [← List.singleton_append]; rw [← List.sublistsLen_zero tl]
    refine Perm.append ?_ (l_ih.map _)
    rw [List.range_succ]; rw [flatMap_append]; rw [flatMap_singleton]; rw [sublistsLen_of_length_lt (Nat.lt_succ_self _)]; rw [append_nil]; rw [← List.flatMap_map Nat.succ fun n => sublistsLen n tl]; rw [← flatMap_cons (f := fun n => sublistsLen n tl)]; rw [← range_succ_eq_map]
    exact l_ih

Depends on / 依赖: List.map_flatMap, List.range_succ, List.singleton_append, List.sublistsLen_zero, Perm.append, _cons, append, cons_append, flatMap_append, flatMap_append_perm, flatMap_cons, flatMap_map, flatMap_singleton, l_ih, l_ih.map, length, map_flatMap, range_succ, range_succ_eq_map, simp_rw
-/
theorem range_bind_sublistsLen_perm (l : List α) :
    ((List.range (l.length + 1)).flatMap fun n => sublistsLen n l) ~ sublists' l := by
  induction l with
  | nil => simp [range_succ]
  | cons h tl l_ih =>
    simp_rw [range_succ_eq_map, length, flatMap_cons, flatMap_map, sublistsLen_succ_cons,
      sublists'_cons, List.sublistsLen_zero, List.singleton_append]
    refine ((flatMap_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans ?_
    simp_rw [← List.map_flatMap, ← cons_append]
    rw [← List.singleton_append]; rw [← List.sublistsLen_zero tl]
    refine Perm.append ?_ (l_ih.map _)
    rw [List.range_succ]; rw [flatMap_append]; rw [flatMap_singleton]; rw [sublistsLen_of_length_lt (Nat.lt_succ_self _)]; rw [append_nil]; rw [← List.flatMap_map Nat.succ fun n => sublistsLen n tl]; rw [← flatMap_cons (f := fun n => sublistsLen n tl)]; rw [← range_succ_eq_map]
    exact l_ih

end List
