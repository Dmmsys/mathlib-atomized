/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Init

/-! ### lookmap -/

public section

variable {α β : Type*}

namespace List

variable (f : α -> Option α)

/--
theorem `lookmap.go_append` / 定理 `lookmap.go_append`

English:
theorem lookmap.go_append
  given: (l : List α) (acc : Array α)
  proof: by
  cases l with
  | nil => simp [go, lookmap]
  | cons hd tl =>
    rw [lookmap]; rw [go]; rw [go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => simp

@[simp, grind =]

中文:
定理 lookmap.go_append
  条件: (l : 列表 α) (acc : 数组 α)
  证明: by
  cases l with
  | nil => simp [go, lookmap]
  | cons hd tl =>
    rw [lookmap]; rw [go]; rw [go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => simp

@[simp, grind =]
-/
private theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => simp [go, lookmap]
  | cons hd tl =>
    rw [lookmap]; rw [go]; rw [go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => simp

@[simp, grind =]
/--
theorem `lookmap_nil` / 定理 `lookmap_nil`

English:
theorem lookmap_nil
  statement: [].lookmap f = []
  proof: rfl

@[simp]

中文:
定理 lookmap_nil
  结论: [].lookmap f = []
  证明: rfl

@[simp]
-/
theorem lookmap_nil : [].lookmap f = [] :=
  rfl

@[simp]
/--
theorem `lookmap_cons_none` / 定理 `lookmap_cons_none`

English:
theorem lookmap_cons_none
  given: {a : α} (l : List α) (h : f a = none)
  proof: by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [lookmap.go_append]; rw [lookmap]; rw [h]; simp

@[simp]

中文:
定理 lookmap_cons_none
  条件: {a : α} (l : 列表 α) (h : f a = none)
  证明: by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [lookmap.go_append]; rw [lookmap]; rw [h]; simp

@[simp]

Depends on / 依赖: Array.toListAppend_eq, go_append, lookmap, lookmap.go, lookmap.go_append, nil_append, toListAppend_eq
-/
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [lookmap.go_append]; rw [lookmap]; rw [h]; simp

@[simp]
/--
theorem `lookmap_cons_some` / 定理 `lookmap_cons_some`

English:
theorem lookmap_cons_some
  given: {a b : α} (l : List α) (h : f a = some b)
  proof: by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [h]

@[grind =]

中文:
定理 lookmap_cons_some
  条件: {a b : α} (l : 列表 α) (h : f a = some b)
  证明: by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [h]

@[grind =]

Depends on / 依赖: Array.toListAppend_eq, lookmap, lookmap.go, nil_append, toListAppend_eq
-/
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) :
    (a :: l).lookmap f = b :: l := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [h]

@[grind =]
/--
theorem `lookmap_cons` / 定理 `lookmap_cons`

English:
theorem lookmap_cons
  given: {a : α} {l : List α}
  proof: by
  cases h : f a <;> simp_all

中文:
定理 lookmap_cons
  条件: {a : α} {l : 列表 α}
  证明: by
  cases h : f a <;> simp_all
-/
theorem lookmap_cons {a : α} {l : List α} :
    (a :: l).lookmap f = match f a with
    | none => a :: l.lookmap f
    | some b => b :: l := by
  cases h : f a <;> simp_all

/--
theorem `lookmap_some` / 定理 `lookmap_some`

English:
theorem lookmap_some
  statement: forall l : List α, l.lookmap some = l

中文:
定理 lookmap_some
  结论: 对任意 l : 列表 α, l.lookmap some = l
-/
theorem lookmap_some : forall l : List α, l.lookmap some = l
  | [] => rfl
  | _ :: rest => lookmap_cons_some some rest rfl

/--
theorem `lookmap_none` / 定理 `lookmap_none`

English:
theorem lookmap_none
  statement: forall l : List α, (l.lookmap fun _ => none) = l

中文:
定理 lookmap_none
  结论: 对任意 l : 列表 α, (l.lookmap fun _ => none) = l
-/
theorem lookmap_none : forall l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => (lookmap_cons_none _ l rfl).trans (congrArg (cons a) (lookmap_none l))

/--
theorem `lookmap_congr` / 定理 `lookmap_congr`

English:
theorem lookmap_congr
  given: {f g : α -> Option α}
  proof: forall_mem_cons.1 H
    rcases h : g a with - | b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]

中文:
定理 lookmap_congr
  条件: {f g : α -> 选项类型 α}
  证明: forall_mem_cons.1 H
    rcases h : g a with - | b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]

Depends on / 依赖: forall_mem_cons
-/
theorem lookmap_congr {f g : α -> Option α} :
    forall {l : List α}, (forall a in l, f a = g a) -> l.lookmap f = l.lookmap g
  | [], _ => rfl
  | a :: l, H => by
    obtain ⟨H₁, H₂⟩ := forall_mem_cons.1 H
    rcases h : g a with - | b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]

/--
theorem `lookmap_of_forall_not` / 定理 `lookmap_of_forall_not`

English:
theorem lookmap_of_forall_not
  given: {l : List α} (H : forall a in l, f a = none)
  statement: l.lookmap f = l
  proof: (lookmap_congr H).trans (lookmap_none l)

中文:
定理 lookmap_of_对任意_not
  条件: {l : 列表 α} (H : 对任意 a in l, f a = none)
  结论: l.lookmap f = l
  证明: (lookmap_congr H).trans (lookmap_none l)

Depends on / 依赖: lookmap_congr, lookmap_none
-/
theorem lookmap_of_forall_not {l : List α} (H : forall a in l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)

/--
theorem `lookmap_map_eq` / 定理 `lookmap_map_eq`

English:
theorem lookmap_map_eq
  given: (g : α -> β) (h : forall (a), forall b in f a, g a = g b)

中文:
定理 lookmap_map_eq
  条件: (g : α -> β) (h : 对任意 (a), 对任意 b in f a, g a = g b)
-/
theorem lookmap_map_eq (g : α -> β) (h : forall (a), forall b in f a, g a = g b) :
    forall l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    rcases h' : f a with - | b
    · simpa [h'] using lookmap_map_eq _ h l
    · simp [lookmap_cons_some _ _ h', h _ _ h']

/--
theorem `lookmap_id'` / 定理 `lookmap_id'`

English:
theorem lookmap_id'
  given: (h : forall (a), forall b in f a, a = b) (l : List α)
  statement: l.lookmap f = l
  proof: by
  rw [← map_id (l.lookmap f)]; rw [lookmap_map_eq]; rw [map_id]; exact h

@[simp, grind =]

中文:
定理 lookmap_id'
  条件: (h : 对任意 (a), 对任意 b in f a, a = b) (l : 列表 α)
  结论: l.lookmap f = l
  证明: by
  rw [← map_id (l.lookmap f)]; rw [lookmap_map_eq]; rw [map_id]; exact h

@[simp, grind =]

Depends on / 依赖: l.lookmap, lookmap, lookmap_map_eq, map_id
-/
theorem lookmap_id' (h : forall (a), forall b in f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f)]; rw [lookmap_map_eq]; rw [map_id]; exact h

@[simp, grind =]
/--
theorem `length_lookmap` / 定理 `length_lookmap`

English:
theorem length_lookmap
  given: (l : List α)
  statement: length (l.lookmap f) = length l
  proof: by
  rw [← length_map]; rw [lookmap_map_eq _ fun _ => ()]; rw [length_map]; simp

中文:
定理 length_lookmap
  条件: (l : 列表 α)
  结论: length (l.lookmap f) = length l
  证明: by
  rw [← length_map]; rw [lookmap_map_eq _ fun _ => ()]; rw [length_map]; simp

Depends on / 依赖: length_map, lookmap_map_eq
-/
theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map]; rw [lookmap_map_eq _ fun _ => ()]; rw [length_map]; simp

open Perm in
/--
theorem `perm_lookmap` / 定理 `perm_lookmap`

English:
theorem perm_lookmap
  statement: (f : α -> Option α) {l₁ l₂ : List α}
  proof: by
  induction p with
  | nil => simp
  | cons a p IH =>
    cases h : f a
    · simpa [h] using IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  | swap a b l =>
    rcases h₁ : f a with - | c <;> rcases h₂ : f b with - | d
    · simpa [h₁, h₂] using Perm.swap _ _ _
    · simpa [h₁, lookmap_cons_some _ _ h₂] using Perm.swap _ _ _
    · simpa [lookmap_cons_some _ _ h₁, h₂] using Perm.swap _ _ _
    · rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    grind

中文:
定理 perm_lookmap
  结论: (f : α -> 选项类型 α) {l₁ l₂ : 列表 α}
  证明: by
  induction p with
  | nil => simp
  | cons a p IH =>
    cases h : f a
    · simpa [h] using IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  | swap a b l =>
    rcases h₁ : f a with - | c <;> rcases h₂ : f b with - | d
    · simpa [h₁, h₂] using Perm.swap _ _ _
    · simpa [h₁, lookmap_cons_some _ _ h₂] using Perm.swap _ _ _
    · simpa [lookmap_cons_some _ _ h₁, h₂] using Perm.swap _ _ _
    · rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    grind

Depends on / 依赖: Or.inl, Perm.refl, Perm.swap, Subtype, Subtype.val, lookmap_cons_some, mem_cons, pairwise_cons
-/
theorem perm_lookmap (f : α -> Option α) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => forall c in f a, forall d in f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
    lookmap f l₁ ~ lookmap f l₂ := by
  induction p with
  | nil => simp
  | cons a p IH =>
    cases h : f a
    · simpa [h] using IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  | swap a b l =>
    rcases h₁ : f a with - | c <;> rcases h₂ : f b with - | d
    · simpa [h₁, h₂] using Perm.swap _ _ _
    · simpa [h₁, lookmap_cons_some _ _ h₂] using Perm.swap _ _ _
    · simpa [lookmap_cons_some _ _ h₁, h₂] using Perm.swap _ _ _
    · rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    grind

end List
