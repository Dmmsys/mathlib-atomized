/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Pairwise
public import Mathlib.Logic.Function.Iterate

/-!
# Relation chain

This file provides basic results about `List.IsChain` from Batteries.
A list `[a₁, a₂, ..., aₙ]` satisfies `IsChain` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `IsChain r [a₁, a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

public section

assert_not_imported Mathlib.Algebra.Order.Group.Nat

open Nat

variable {α β : Type*} {R r : α -> α -> Prop} {l l₁ l₂ : List α} {a b : α}

namespace List

mk_iff_of_inductive_prop List.IsChain List.isChain_iff

/--
theorem `isChain_nil` / 定理 `isChain_nil`

English:
theorem isChain_nil
  statement: IsChain R []
  proof: .nil

中文:
定理 isChain_nil
  结论: IsChain R []
  证明: .nil
-/
theorem isChain_nil : IsChain R [] := .nil
/--
theorem `isChain_singleton` / 定理 `isChain_singleton`

English:
theorem isChain_singleton
  given: (a : α)
  statement: IsChain R [a]
  proof: .singleton _

中文:
定理 isChain_singleton
  条件: (a : α)
  结论: IsChain R [a]
  证明: .singleton _

Depends on / 依赖: singleton
-/
theorem isChain_singleton (a : α) : IsChain R [a] := .singleton _

/--
theorem `isChain_cons_iff` / 定理 `isChain_cons_iff`

English:
theorem isChain_cons_iff
  given: (R : α -> α -> Prop) (a : α) (l : List α)
  proof: (isChain_iff _ _).trans by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind

中文:
定理 isChain_cons_iff
  条件: (R : α -> α -> 命题) (a : α) (l : List α)
  证明: (isChain_iff _ _).trans by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind

Depends on / 依赖: List.cons_eq_cons, cons_eq_cons, cons_ne_nil, exists_and_left, exists_and_right, exists_eq, false_or, isChain_iff, true_and
-/
theorem isChain_cons_iff (R : α -> α -> Prop) (a : α) (l : List α) :
    IsChain R (a :: l) ↔ l = [] ∨
      exists (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l = b :: l' :=
(isChain_iff _ _).trans by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind

/--
theorem `IsChain.imp_of_mem_tail_imp` / 定理 `IsChain.imp_of_mem_tail_imp`

English:
theorem IsChain.imp_of_mem_tail_imp
  statement: {S : α -> α -> Prop} {l : List α}
  proof: by
  induction p with grind

中文:
定理 IsChain.imp_of_mem_tail_imp
  结论: {S : α -> α -> 命题} {l : List α}
  证明: by
  induction p with grind
-/
theorem IsChain.imp_of_mem_tail_imp {S : α -> α -> Prop} {l : List α}
    (H : forall a b : α, a in l -> b in l.tail -> R a b -> S a b) (p : IsChain R l) : IsChain S l := by
  induction p with grind

/--
theorem `IsChain.imp_of_mem_imp` / 定理 `IsChain.imp_of_mem_imp`

English:
theorem IsChain.imp_of_mem_imp
  statement: {S : α -> α -> Prop} {l : List α}
  proof: p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)

中文:
定理 IsChain.imp_of_mem_imp
  结论: {S : α -> α -> 命题} {l : List α}
  证明: p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)

Depends on / 依赖: imp_of_mem_tail_imp, mem_of_mem_tail, p.imp_of_mem_tail_imp
-/
theorem IsChain.imp_of_mem_imp {S : α -> α -> Prop} {l : List α}
    (H : forall a b : α, a in l -> b in l -> R a b -> S a b) (p : IsChain R l) : IsChain S l :=
  p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)

/--
theorem `IsChain.iff` / 定理 `IsChain.iff`

English:
theorem IsChain.iff
  given: {S : α -> α -> Prop} (H : forall a b, R a b ↔ S a b) {l : List α}
  proof: ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

中文:
定理 IsChain.iff
  条件: {S : α -> α -> 命题} (H : 对任意 a b, R a b ↔ S a b) {l : List α}
  证明: ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

Depends on / 依赖: IsChain, IsChain.imp
-/
theorem IsChain.iff {S : α -> α -> Prop} (H : forall a b, R a b ↔ S a b) {l : List α} :
    IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩

/--
theorem `IsChain.iff_of_mem_imp` / 定理 `IsChain.iff_of_mem_imp`

English:
theorem IsChain.iff_of_mem_imp
  statement: {S : α -> α -> Prop} {l : List α}
  proof: ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩

中文:
定理 IsChain.iff_of_mem_imp
  结论: {S : α -> α -> 命题} {l : List α}
  证明: ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩

Depends on / 依赖: Iff.mp, Iff.mpr, IsChain, IsChain.imp_of_mem_imp, imp_of_mem_imp
-/
theorem IsChain.iff_of_mem_imp {S : α -> α -> Prop} {l : List α}
    (H : forall a b : α, a in l -> b in l -> (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩

/--
theorem `IsChain.iff_of_mem_tail_imp` / 定理 `IsChain.iff_of_mem_tail_imp`

English:
theorem IsChain.iff_of_mem_tail_imp
  statement: {S : α -> α -> Prop} {l : List α}
  proof: ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩

中文:
定理 IsChain.iff_of_mem_tail_imp
  结论: {S : α -> α -> 命题} {l : List α}
  证明: ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩

Depends on / 依赖: Iff.mp, Iff.mpr, IsChain, IsChain.imp_of_mem_tail_imp, imp_of_mem_tail_imp
-/
theorem IsChain.iff_of_mem_tail_imp {S : α -> α -> Prop} {l : List α}
    (H : forall a b : α, a in l -> b in l.tail -> (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩

/--
theorem `IsChain.iff_mem` / 定理 `IsChain.iff_mem`

English:
theorem IsChain.iff_mem
  given: {l : List α}
  proof: IsChain.iff_of_mem_imp by grind

中文:
定理 IsChain.iff_mem
  条件: {l : List α}
  证明: IsChain.iff_of_mem_imp by grind

Depends on / 依赖: IsChain, IsChain.iff_of_mem_imp, iff_of_mem_imp
-/
theorem IsChain.iff_mem {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x in l ∧ y in l ∧ R x y) l :=
IsChain.iff_of_mem_imp by grind

/--
theorem `IsChain.iff_mem_mem_tail` / 定理 `IsChain.iff_mem_mem_tail`

English:
theorem IsChain.iff_mem_mem_tail
  given: {l : List α}
  proof: IsChain.iff_of_mem_tail_imp by grind

中文:
定理 IsChain.iff_mem_mem_tail
  条件: {l : List α}
  证明: IsChain.iff_of_mem_tail_imp by grind

Depends on / 依赖: IsChain, IsChain.iff_of_mem_tail_imp, iff_of_mem_tail_imp
-/
theorem IsChain.iff_mem_mem_tail {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x in l ∧ y in l.tail ∧ R x y) l :=
IsChain.iff_of_mem_tail_imp by grind

/--
theorem `isChain_pair` / 定理 `isChain_pair`

English:
theorem isChain_pair
  given: {x y}
  statement: IsChain R [x, y] ↔ R x y
  proof: by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]

中文:
定理 isChain_pair
  条件: {x y}
  结论: IsChain R [x, y] ↔ R x y
  证明: by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]

Depends on / 依赖: IsChain, IsChain.singleton, and_true, isChain_cons_cons, singleton
-/
theorem isChain_pair {x y} : IsChain R [x, y] ↔ R x y := by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]

/--
theorem `isChain_isInfix` / 定理 `isChain_isInfix`

English:
theorem isChain_isInfix
  statement: forall l : List α, IsChain (fun x y => [x, y] <:+: l) l

中文:
定理 isChain_isInfix
  结论: 对任意 l : List α, IsChain (fun x y => [x, y] <:+: l) l
-/
theorem isChain_isInfix : forall l : List α, IsChain (fun x y => [x, y] <:+: l) l
  | [] => .nil
  | [_] => .singleton _
  | a :: b :: l => .cons_cons ⟨[], l, by simp⟩
    ((isChain_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩)

/--
theorem `isChain_split` / 定理 `isChain_split`

English:
theorem isChain_split
  given: {c : α} {l₁ l₂ : List α}
  proof: by
  induction l₁ using twoStepInduction generalizing l₂ with grind

中文:
定理 isChain_split
  条件: {c : α} {l₁ l₂ : List α}
  证明: by
  induction l₁ using twoStepInduction generalizing l₂ with grind

Depends on / 依赖: generalizing, twoStepInduction
-/
theorem isChain_split {c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂) := by
  induction l₁ using twoStepInduction generalizing l₂ with grind

/--
theorem `isChain_cons_split` / 定理 `isChain_cons_split`

English:
theorem isChain_cons_split
  given: {c : α} {l₁ l₂ : List α}
  proof: by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]

@[simp]

中文:
定理 isChain_cons_split
  条件: {c : α} {l₁ l₂ : List α}
  证明: by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]

@[simp]

Depends on / 依赖: cons_append, isChain_split, simp_rw
-/
theorem isChain_cons_split {c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂) := by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]

@[simp]
/--
theorem `isChain_append_cons_cons` / 定理 `isChain_append_cons_cons`

English:
theorem isChain_append_cons_cons
  given: {b c : α} {l₁ l₂ : List α}
  proof: by
  rw [isChain_split]; rw [isChain_cons_cons]

@[simp]

中文:
定理 isChain_append_cons_cons
  条件: {b c : α} {l₁ l₂ : List α}
  证明: by
  rw [isChain_split]; rw [isChain_cons_cons]

@[simp]

Depends on / 依赖: isChain_cons_cons, isChain_split
-/
theorem isChain_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_split]; rw [isChain_cons_cons]

@[simp]
/--
theorem `isChain_cons_append_cons_cons` / 定理 `isChain_cons_append_cons_cons`

English:
theorem isChain_cons_append_cons_cons
  given: {a b c : α} {l₁ l₂ : List α}
  proof: by
  rw [isChain_cons_split]; rw [isChain_cons_cons]

中文:
定理 isChain_cons_append_cons_cons
  条件: {a b c : α} {l₁ l₂ : List α}
  证明: by
  rw [isChain_cons_split]; rw [isChain_cons_cons]

Depends on / 依赖: isChain_cons_cons, isChain_cons_split
-/
theorem isChain_cons_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ b :: c :: l₂)) ↔
    IsChain R (a :: (l₁ ++ [b])) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_cons_split]; rw [isChain_cons_cons]

/--
theorem `isChain_iff_forall_rel_of_append_cons_cons` / 定理 `isChain_iff_forall_rel_of_append_cons_cons`

English:
theorem isChain_iff_forall_rel_of_append_cons_cons
  given: {l : List α}
  proof: by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l using twoStepInduction with
  | nil | singleton => grind
  | cons_cons head head' tail _ ih =>
    refine fun h => isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih _ fun ⦃a b l₁ l₂⦄ eq => ?_⟩
    apply h
 

中文:
定理 isChain_iff_forall_rel_of_append_cons_cons
  条件: {l : List α}
  证明: by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l using twoStepInduction with
  | nil | singleton => grind
  | cons_cons head head' tail _ ih =>
    refine fun h => isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih _ fun ⦃a b l₁ l₂⦄ eq => ?_⟩
    apply h
 

Depends on / 依赖: cons_append, cons_cons, isChain_append_cons_cons, isChain_append_cons_cons.mp, isChain_cons_cons, isChain_cons_cons.mpr, nil_append, singleton, twoStepInduction
-/
theorem isChain_iff_forall_rel_of_append_cons_cons {l : List α} :
    IsChain R l ↔ forall ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ -> R a b := by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l using twoStepInduction with
  | nil | singleton => grind
  | cons_cons head head' tail _ ih =>
    refine fun h => isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih _ fun ⦃a b l₁ l₂⦄ eq => ?_⟩
    apply h
    rw [eq]; rw [cons_append]

/--
theorem `isChain_iff_forall₂` / 定理 `isChain_iff_forall₂`

English:
theorem isChain_iff_forall₂
  given: {l : List α}
  proof: by
  induction l using twoStepInduction <;> simp_all

中文:
定理 isChain_iff_forall₂
  条件: {l : List α}
  证明: by
  induction l using twoStepInduction <;> simp_all

Depends on / 依赖: twoStepInduction
-/
theorem isChain_iff_forall₂ {l : List α} :
    IsChain R l ↔ Forall₂ R l.dropLast l.tail := by
  induction l using twoStepInduction <;> simp_all

/--
theorem `isChain_cons_iff_forall₂` / 定理 `isChain_cons_iff_forall₂`

English:
theorem isChain_cons_iff_forall₂
  statement: IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l
  proof: by
  cases l <;> simp [isChain_iff_forall₂]

中文:
定理 isChain_cons_iff_forall₂
  结论: IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l
  证明: by
  cases l <;> simp [isChain_iff_forall₂]
-/
theorem isChain_cons_iff_forall₂ : IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l := by
  cases l <;> simp [isChain_iff_forall₂]

/--
theorem `isChain_cons_append_singleton_iff_forall₂` / 定理 `isChain_cons_append_singleton_iff_forall₂`

English:
theorem isChain_cons_append_singleton_iff_forall₂
  proof: by
  simp_rw [isChain_iff_forall₂, dropLast_concat, cons_append, tail_cons]

中文:
定理 isChain_cons_append_singleton_iff_forall₂
  证明: by
  simp_rw [isChain_iff_forall₂, dropLast_concat, cons_append, tail_cons]

Depends on / 依赖: cons_append, dropLast_concat, simp_rw, tail_cons
-/
theorem isChain_cons_append_singleton_iff_forall₂ :
    IsChain R (a :: l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) := by
  simp_rw [isChain_iff_forall₂, dropLast_concat, cons_append, tail_cons]

/--
theorem `isChain_map` / 定理 `isChain_map`

English:
theorem isChain_map
  given: (f : β -> α) {l : List β}
  proof: by
  induction l using twoStepInduction <;> grind

中文:
定理 isChain_map
  条件: (f : β -> α) {l : List β}
  证明: by
  induction l using twoStepInduction <;> grind

Depends on / 依赖: twoStepInduction
-/
theorem isChain_map (f : β -> α) {l : List β} :
    IsChain R (map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l := by
  induction l using twoStepInduction <;> grind

/--
theorem `isChain_of_isChain_map` / 定理 `isChain_of_isChain_map`

English:
theorem isChain_of_isChain_map
  statement: {S : β -> β -> Prop} (f : α -> β) (H : forall a b : α, S (f a) (f b) -> R a b)
  proof: ((isChain_map f).1 p).imp H

中文:
定理 isChain_of_isChain_map
  结论: {S : β -> β -> 命题} (f : α -> β) (H : 对任意 a b : α, S (f a) (f b) -> R a b)
  证明: ((isChain_map f).1 p).imp H

Depends on / 依赖: isChain_map
-/
theorem isChain_of_isChain_map {S : β -> β -> Prop} (f : α -> β) (H : forall a b : α, S (f a) (f b) -> R a b)
    {l : List α} (p : IsChain S (map f l)) : IsChain R l :=
  ((isChain_map f).1 p).imp H

/--
theorem `isChain_map_of_isChain` / 定理 `isChain_map_of_isChain`

English:
theorem isChain_map_of_isChain
  statement: {S : β -> β -> Prop} (f : α -> β) (H : forall a b : α, R a b -> S (f a) (f b))
  proof: (isChain_map f).2 p.imp H

中文:
定理 isChain_map_of_isChain
  结论: {S : β -> β -> 命题} (f : α -> β) (H : 对任意 a b : α, R a b -> S (f a) (f b))
  证明: (isChain_map f).2 p.imp H

Depends on / 依赖: isChain_map, p.imp
-/
theorem isChain_map_of_isChain {S : β -> β -> Prop} (f : α -> β) (H : forall a b : α, R a b -> S (f a) (f b))
    {l : List α} (p : IsChain R l) : IsChain S (map f l) :=
(isChain_map f).2 p.imp H

/--
theorem `isChain_cons_map` / 定理 `isChain_cons_map`

English:
theorem isChain_cons_map
  given: (f : β -> α) {l : List β} {b : β}
  proof: isChain_map f (l := b :: l)

中文:
定理 isChain_cons_map
  条件: (f : β -> α) {l : List β} {b : β}
  证明: isChain_map f (l := b :: l)

Depends on / 依赖: isChain_map
-/
theorem isChain_cons_map (f : β -> α) {l : List β} {b : β} :
    IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l) :=
  isChain_map f (l := b :: l)

/--
theorem `isChain_cons_of_isChain_cons_map` / 定理 `isChain_cons_of_isChain_cons_map`

English:
theorem isChain_cons_of_isChain_cons_map
  statement: {S : β -> β -> Prop} (f : α -> β)
  proof: ((isChain_cons_map f).1 p).imp H

中文:
定理 isChain_cons_of_isChain_cons_map
  结论: {S : β -> β -> 命题} (f : α -> β)
  证明: ((isChain_cons_map f).1 p).imp H

Depends on / 依赖: isChain_cons_map
-/
theorem isChain_cons_of_isChain_cons_map {S : β -> β -> Prop} (f : α -> β)
    (H : forall a b : α, S (f a) (f b) -> R a b)
    {l : List α} (p : IsChain S (f a :: map f l)) : IsChain R (a :: l) :=
  ((isChain_cons_map f).1 p).imp H

/--
theorem `isChain_cons_map_of_isChain_cons` / 定理 `isChain_cons_map_of_isChain_cons`

English:
theorem isChain_cons_map_of_isChain_cons
  statement: {S : β -> β -> Prop} (f : α -> β)
  proof: (isChain_cons_map f).2 p.imp H

中文:
定理 isChain_cons_map_of_isChain_cons
  结论: {S : β -> β -> 命题} (f : α -> β)
  证明: (isChain_cons_map f).2 p.imp H

Depends on / 依赖: isChain_cons_map, p.imp
-/
theorem isChain_cons_map_of_isChain_cons {S : β -> β -> Prop} (f : α -> β)
    (H : forall a b : α, R a b -> S (f a) (f b))
    {l : List α} (p : IsChain R (a :: l)) : IsChain S (f a :: map f l) :=
(isChain_cons_map f).2 p.imp H

/--
theorem `isChain_pmap` / 定理 `isChain_pmap`

English:
theorem isChain_pmap
  statement: {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β) {l : List α}
  proof: by
  induction l using twoStepInduction <;> grind

中文:
定理 isChain_pmap
  结论: {S : β -> β -> 命题} {p : α -> 命题} (f : 对任意 a, p a -> β) {l : List α}
  证明: by
  induction l using twoStepInduction <;> grind

Depends on / 依赖: twoStepInduction
-/
theorem isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β) {l : List α}
    (hl : forall a in l, p a) : IsChain S (pmap f l hl) ↔
    IsChain (fun a b => exists ha, exists hb, S (f a ha) (f b hb)) l := by
  induction l using twoStepInduction <;> grind

/--
theorem `isChain_pmap_of_isChain` / 定理 `isChain_pmap_of_isChain`

English:
theorem isChain_pmap_of_isChain
  statement: {S : β -> β -> Prop} {p : α -> Prop} {f : forall a, p a -> β}
  proof: (isChain_pmap f _).2
  hl₁.imp_of_mem_imp (by grind)

中文:
定理 isChain_pmap_of_isChain
  结论: {S : β -> β -> 命题} {p : α -> 命题} {f : 对任意 a, p a -> β}
  证明: (isChain_pmap f _).2
  hl₁.imp_of_mem_imp (by grind)

Depends on / 依赖: isChain_pmap
-/
theorem isChain_pmap_of_isChain {S : β -> β -> Prop} {p : α -> Prop} {f : forall a, p a -> β}
    (H : forall a b ha hb, R a b -> S (f a ha) (f b hb)) {l : List α} (hl₁ : IsChain R l)
(hl₂ : forall a in l, p a) : IsChain S (pmap f l hl₂) := (isChain_pmap f _).2
  hl₁.imp_of_mem_imp (by grind)

/--
theorem `isChain_of_isChain_pmap` / 定理 `isChain_of_isChain_pmap`

English:
theorem isChain_of_isChain_pmap
  statement: {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β) {l : List α}
  proof: ((isChain_pmap f _).1 hl₂).imp (by grind)

中文:
定理 isChain_of_isChain_pmap
  结论: {S : β -> β -> 命题} {p : α -> 命题} (f : 对任意 a, p a -> β) {l : List α}
  证明: ((isChain_pmap f _).1 hl₂).imp (by grind)

Depends on / 依赖: isChain_pmap
-/
theorem isChain_of_isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β) {l : List α}
    (hl₁ : forall a in l, p a) (hl₂ : IsChain S (pmap f l hl₁))
    (H : forall a b ha hb, S (f a ha) (f b hb) -> R a b) : IsChain R l :=
  ((isChain_pmap f _).1 hl₂).imp (by grind)

/--
theorem `isChain_cons_pmap` / 定理 `isChain_cons_pmap`

English:
theorem isChain_cons_pmap
  statement: {p : β -> Prop} (f : forall b, p b -> α) {l : List β} (hl : forall b in l, p b)
  proof: isChain_pmap (l := a :: _) f (by grind)

中文:
定理 isChain_cons_pmap
  结论: {p : β -> 命题} (f : 对任意 b, p b -> α) {l : List β} (hl : 对任意 b in l, p b)
  证明: isChain_pmap (l := a :: _) f (by grind)

Depends on / 依赖: isChain_pmap
-/
theorem isChain_cons_pmap {p : β -> Prop} (f : forall b, p b -> α) {l : List β} (hl : forall b in l, p b)
    {a} (ha) : IsChain R (f a ha :: pmap f l hl) ↔
    IsChain (fun a b => exists ha, exists hb, R (f a ha) (f b hb)) (a :: l) :=
  isChain_pmap (l := a :: _) f (by grind)

/--
theorem `isChain_cons_pmap_of_isChain_cons` / 定理 `isChain_cons_pmap_of_isChain_cons`

English:
theorem isChain_cons_pmap_of_isChain_cons
  statement: {S : β -> β -> Prop} {p : α -> Prop} {f : forall a, p a -> β}
  proof: (isChain_cons_pmap f _ _).2 hl₁.imp_of_mem_imp (by grind)

中文:
定理 isChain_cons_pmap_of_isChain_cons
  结论: {S : β -> β -> 命题} {p : α -> 命题} {f : 对任意 a, p a -> β}
  证明: (isChain_cons_pmap f _ _).2 hl₁.imp_of_mem_imp (by grind)

Depends on / 依赖: imp_of_mem_imp, isChain_cons_pmap
-/
theorem isChain_cons_pmap_of_isChain_cons {S : β -> β -> Prop} {p : α -> Prop} {f : forall a, p a -> β}
    (H : forall a b ha hb, R a b -> S (f a ha) (f b hb)) {l : List α} {a} (ha)
    (hl₁ : IsChain R (a :: l)) (hl₂ : forall a in l, p a) : IsChain S (f a ha :: pmap f l hl₂) :=
(isChain_cons_pmap f _ _).2 hl₁.imp_of_mem_imp (by grind)

/--
theorem `isChain_cons_of_isChain_cons_pmap` / 定理 `isChain_cons_of_isChain_cons_pmap`

English:
theorem isChain_cons_of_isChain_cons_pmap
  statement: {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β)
  proof: ((isChain_cons_pmap f _ _).1 hl₂).imp (by grind)

中文:
定理 isChain_cons_of_isChain_cons_pmap
  结论: {S : β -> β -> 命题} {p : α -> 命题} (f : 对任意 a, p a -> β)
  证明: ((isChain_cons_pmap f _ _).1 hl₂).imp (by grind)

Depends on / 依赖: isChain_cons_pmap
-/
theorem isChain_cons_of_isChain_cons_pmap {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β)
    {l : List α} (hl₁ : forall a in l, p a) {a} (ha) (hl₂ : IsChain S (f a ha :: pmap f l hl₁))
    (H : forall a b ha hb, S (f a ha) (f b hb) -> R a b) : IsChain R (a :: l) :=
  ((isChain_cons_pmap f _ _).1 hl₂).imp (by grind)

/--
theorem `IsChain.sublist` / 定理 `IsChain.sublist`

English:
theorem IsChain.sublist
  given: [Trans R R R] (hl : l₂.IsChain R) (h : l₁ <+ l₂)
  proof: by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h

中文:
定理 IsChain.sublist
  条件: [Trans R R R] (hl : l₂.IsChain R) (h : l₁ <+ l₂)
  证明: by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h
-/
protected theorem IsChain.sublist [Trans R R R] (hl : l₂.IsChain R) (h : l₁ <+ l₂) :
    l₁.IsChain R := by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h

/--
theorem `IsChain.rel_cons` / 定理 `IsChain.rel_cons`

English:
theorem IsChain.rel_cons
  given: [Trans R R R] (hl : (a :: l).IsChain R) (hb : b in l)
  proof: by
  rw [isChain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb

中文:
定理 IsChain.rel_cons
  条件: [Trans R R R] (hl : (a :: l).IsChain R) (hb : b in l)
  证明: by
  rw [isChain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb
-/
protected theorem IsChain.rel_cons [Trans R R R] (hl : (a :: l).IsChain R) (hb : b in l) :
    R a b := by
  rw [isChain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb

/--
theorem `IsChain.tail` / 定理 `IsChain.tail`

English:
theorem IsChain.tail
  given: {l : List α} (h : IsChain R l)
  statement: IsChain R l.tail
  proof: by
  grind +splitIndPred

@[deprecated (since := "2026-06-25")] alias IsChain.rel_head := IsChain.rel

中文:
定理 IsChain.tail
  条件: {l : List α} (h : IsChain R l)
  结论: IsChain R l.tail
  证明: by
  grind +splitIndPred

@[deprecated (since := "2026-06-25")] alias IsChain.rel_head := IsChain.rel

Depends on / 依赖: splitIndPred
-/
theorem IsChain.tail {l : List α} (h : IsChain R l) : IsChain R l.tail := by
  grind +splitIndPred

@[deprecated (since := "2026-06-25")] alias IsChain.rel_head := IsChain.rel

/--
theorem `IsChain.rel_head?` / 定理 `IsChain.rel_head?`

English:
theorem IsChain.rel_head?
  given: {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y in head? l)
  statement: R x y
  proof: by
  rw [← cons_head?_tail hy] at h
  exact h.rel

中文:
定理 IsChain.rel_head?
  条件: {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y in head? l)
  结论: R x y
  证明: by
  rw [← cons_head?_tail hy] at h
  exact h.rel

Depends on / 依赖: _tail, cons_head, h.rel
-/
theorem IsChain.rel_head? {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y in head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel

/--
theorem `IsChain.rel_getLast_dropLast` / 定理 `IsChain.rel_getLast_dropLast`

English:
theorem IsChain.rel_getLast_dropLast
  given: {l : List α} (h : l.IsChain R) (hne : l.dropLast != [])
  proof: match l with
  | [_, _] => h.rel
| _ :: _ :: _ :: _ => h.tail.rel_getLast_dropLast by simp

中文:
定理 IsChain.rel_getLast_dropLast
  条件: {l : List α} (h : l.IsChain R) (hne : l.dropLast != [])
  证明: match l with
  | [_, _] => h.rel
| _ :: _ :: _ :: _ => h.tail.rel_getLast_dropLast by simp

Depends on / 依赖: h.rel, h.tail.rel_getLast_dropLast, rel_getLast_dropLast
-/
theorem IsChain.rel_getLast_dropLast {l : List α} (h : l.IsChain R) (hne : l.dropLast != []) :
    R (l.dropLast.getLast hne) (l.getLast <| by grind) :=
  match l with
  | [_, _] => h.rel
| _ :: _ :: _ :: _ => h.tail.rel_getLast_dropLast by simp

/--
theorem `IsChain.cons` / 定理 `IsChain.cons`

English:
theorem IsChain.cons
  given: {x}
  statement: forall {l : List α}, IsChain R l -> (forall y in l.head?, R x y) ->

中文:
定理 IsChain.cons
  条件: {x}
  结论: 对任意 {l : List α}, IsChain R l -> (对任意 y in l.head?, R x y) ->
-/
theorem IsChain.cons {x} : forall {l : List α}, IsChain R l -> (forall y in l.head?, R x y) ->
    IsChain R (x :: l)
  | [], _, _ => .singleton x
| _ :: _, hl, H => hl.cons_cons H _ rfl

/--
lemma `IsChain.cons_of_ne_nil` / 引理 `IsChain.cons_of_ne_nil`

English:
lemma IsChain.cons_of_ne_nil
  statement: {x : α} {l : List α} (l_ne_nil : l != [])
  proof: by
  grind +splitIndPred

中文:
引理 IsChain.cons_of_ne_nil
  结论: {x : α} {l : List α} (l_ne_nil : l != [])
  证明: by
  grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
lemma IsChain.cons_of_ne_nil {x : α} {l : List α} (l_ne_nil : l != [])
    (hl : IsChain R l) (h : R x (l.head l_ne_nil)) : IsChain R (x :: l) := by
  grind +splitIndPred

/--
theorem `isChain_cons` / 定理 `isChain_cons`

English:
theorem isChain_cons
  given: {x l}
  statement: IsChain R (x :: l) ↔ (forall y in head? l, R x y) ∧ IsChain R l
  proof: ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

中文:
定理 isChain_cons
  条件: {x l}
  结论: IsChain R (x :: l) ↔ (对任意 y in head? l, R x y) ∧ IsChain R l
  证明: ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

Depends on / 依赖: h.rel_head, h.tail, rel_head
-/
theorem isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y in head? l, R x y) ∧ IsChain R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩

/--
theorem `isChain_append` / 定理 `isChain_append`

English:
theorem isChain_append

中文:
定理 isChain_append
-/
theorem isChain_append :
    forall {l₁ l₂ : List α},
      IsChain R (l₁ ++ l₂) ↔ IsChain R l₁ ∧ IsChain R l₂ ∧ forall x in l₁.getLast?, forall y in l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [isChain_cons, and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append]; rw [cons_append]; rw [isChain_cons_cons]; rw [isChain_cons_cons]; rw [← cons_append]; rw [isChain_append]; rw [and_assoc]
    simp

/--
theorem `IsChain.append` / 定理 `IsChain.append`

English:
theorem IsChain.append
  statement: (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
  proof: isChain_append.2 ⟨h₁, h₂, h⟩

中文:
定理 IsChain.append
  结论: (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
  证明: isChain_append.2 ⟨h₁, h₂, h⟩

Depends on / 依赖: isChain_append
-/
theorem IsChain.append (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
    (h : forall x in l₁.getLast?, forall y in l₂.head?, R x y) : IsChain R (l₁ ++ l₂) :=
  isChain_append.2 ⟨h₁, h₂, h⟩

/--
theorem `IsChain.left_of_append` / 定理 `IsChain.left_of_append`

English:
theorem IsChain.left_of_append
  given: (h : IsChain R (l₁ ++ l₂))
  statement: IsChain R l₁
  proof: (isChain_append.1 h).1

中文:
定理 IsChain.left_of_append
  条件: (h : IsChain R (l₁ ++ l₂))
  结论: IsChain R l₁
  证明: (isChain_append.1 h).1

Depends on / 依赖: isChain_append
-/
theorem IsChain.left_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₁ :=
  (isChain_append.1 h).1

/--
theorem `IsChain.right_of_append` / 定理 `IsChain.right_of_append`

English:
theorem IsChain.right_of_append
  given: (h : IsChain R (l₁ ++ l₂))
  statement: IsChain R l₂
  proof: (isChain_append.1 h).2.1

中文:
定理 IsChain.right_of_append
  条件: (h : IsChain R (l₁ ++ l₂))
  结论: IsChain R l₂
  证明: (isChain_append.1 h).2.1

Depends on / 依赖: isChain_append
-/
theorem IsChain.right_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₂ :=
  (isChain_append.1 h).2.1

/--
theorem `IsChain.rel_getLast_head_of_append` / 定理 `IsChain.rel_getLast_head_of_append`

English:
theorem IsChain.rel_getLast_head_of_append
  statement: {l₁ l₂ : List α} (h : (l₁ ++ l₂).IsChain R)
  proof: match l₁, l₂ with
  | [_], _ :: _ => h.rel
  | _ :: _ :: _, _ :: _ => h.tail.rel_getLast_head_of_append (by simp) (by simp)

中文:
定理 IsChain.rel_getLast_head_of_append
  结论: {l₁ l₂ : List α} (h : (l₁ ++ l₂).IsChain R)
  证明: match l₁, l₂ with
  | [_], _ :: _ => h.rel
  | _ :: _ :: _, _ :: _ => h.tail.rel_getLast_head_of_append (by simp) (by simp)

Depends on / 依赖: h.rel, h.tail.rel_getLast_head_of_append, rel_getLast_head_of_append
-/
theorem IsChain.rel_getLast_head_of_append {l₁ l₂ : List α} (h : (l₁ ++ l₂).IsChain R)
    (h₁ : l₁ != []) (h₂ : l₂ != []) : R (l₁.getLast h₁) (l₂.head h₂) :=
  match l₁, l₂ with
  | [_], _ :: _ => h.rel
  | _ :: _ :: _, _ :: _ => h.tail.rel_getLast_head_of_append (by simp) (by simp)

/--
theorem `IsChain.infix` / 定理 `IsChain.infix`

English:
theorem IsChain.infix
  given: (h : IsChain R l) (h' : l₁ <:+: l)
  statement: IsChain R l₁
  proof: by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

中文:
定理 IsChain.infix
  条件: (h : IsChain R l) (h' : l₁ <:+: l)
  结论: IsChain R l₁
  证明: by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

Depends on / 依赖: h.left_of_append.right_of_append, left_of_append, right_of_append
-/
theorem IsChain.infix (h : IsChain R l) (h' : l₁ <:+: l) : IsChain R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append

/--
theorem `IsChain.suffix` / 定理 `IsChain.suffix`

English:
theorem IsChain.suffix
  given: (h : IsChain R l) (h' : l₁ <:+ l)
  statement: IsChain R l₁
  proof: h.infix h'.isInfix

中文:
定理 IsChain.suffix
  条件: (h : IsChain R l) (h' : l₁ <:+ l)
  结论: IsChain R l₁
  证明: h.infix h'.isInfix

Depends on / 依赖: h.infix, isInfix
-/
theorem IsChain.suffix (h : IsChain R l) (h' : l₁ <:+ l) : IsChain R l₁ :=
  h.infix h'.isInfix

/--
theorem `IsChain.prefix` / 定理 `IsChain.prefix`

English:
theorem IsChain.prefix
  given: (h : IsChain R l) (h' : l₁ <+: l)
  statement: IsChain R l₁
  proof: h.infix h'.isInfix

中文:
定理 IsChain.prefix
  条件: (h : IsChain R l) (h' : l₁ <+: l)
  结论: IsChain R l₁
  证明: h.infix h'.isInfix

Depends on / 依赖: h.infix, isInfix
-/
theorem IsChain.prefix (h : IsChain R l) (h' : l₁ <+: l) : IsChain R l₁ :=
  h.infix h'.isInfix

/--
theorem `IsChain.drop` / 定理 `IsChain.drop`

English:
theorem IsChain.drop
  given: (h : IsChain R l) (n : Nat)
  statement: IsChain R (drop n l)
  proof: h.suffix (drop_suffix _ _)

中文:
定理 IsChain.drop
  条件: (h : IsChain R l) (n : 自然数)
  结论: IsChain R (drop n l)
  证明: h.suffix (drop_suffix _ _)

Depends on / 依赖: drop_suffix, h.suffix, suffix
-/
theorem IsChain.drop (h : IsChain R l) (n : Nat) : IsChain R (drop n l) :=
  h.suffix (drop_suffix _ _)

/--
theorem `IsChain.dropLast` / 定理 `IsChain.dropLast`

English:
theorem IsChain.dropLast
  given: (h : IsChain R l)
  statement: IsChain R l.dropLast
  proof: h.prefix l.dropLast_prefix

中文:
定理 IsChain.dropLast
  条件: (h : IsChain R l)
  结论: IsChain R l.dropLast
  证明: h.prefix l.dropLast_prefix

Depends on / 依赖: dropLast_prefix, h.prefix, l.dropLast_prefix, prefix
-/
theorem IsChain.dropLast (h : IsChain R l) : IsChain R l.dropLast :=
  h.prefix l.dropLast_prefix

/--
theorem `IsChain.take` / 定理 `IsChain.take`

English:
theorem IsChain.take
  given: (h : IsChain R l) (n : Nat)
  statement: IsChain R (take n l)
  proof: h.prefix (take_prefix _ _)

中文:
定理 IsChain.take
  条件: (h : IsChain R l) (n : 自然数)
  结论: IsChain R (take n l)
  证明: h.prefix (take_prefix _ _)

Depends on / 依赖: h.prefix, prefix, take_prefix
-/
theorem IsChain.take (h : IsChain R l) (n : Nat) : IsChain R (take n l) :=
  h.prefix (take_prefix _ _)

/--
theorem `IsChain.imp_head` / 定理 `IsChain.imp_head`

English:
theorem IsChain.imp_head
  given: {x y} (h : forall {z}, R x z -> R y z) {l} (hl : IsChain R (x :: l))
  proof: IsChain.cons_of_imp @h hl

中文:
定理 IsChain.imp_head
  条件: {x y} (h : 对任意 {z}, R x z -> R y z) {l} (hl : IsChain R (x :: l))
  证明: IsChain.cons_of_imp @h hl

Depends on / 依赖: IsChain, IsChain.cons_of_imp, cons_of_imp
-/
theorem IsChain.imp_head {x y} (h : forall {z}, R x z -> R y z) {l} (hl : IsChain R (x :: l)) :
    IsChain R (y :: l) :=
  IsChain.cons_of_imp @h hl

/--
theorem `exists_not_getElem_of_not_isChain` / 定理 `exists_not_getElem_of_not_isChain`

English:
theorem exists_not_getElem_of_not_isChain
  given: (h : ¬List.IsChain R l)
  proof: by simp_all [isChain_iff_getElem]

中文:
定理 exists_not_getElem_of_not_isChain
  条件: (h : ¬List.IsChain R l)
  证明: by simp_all [isChain_iff_getElem]

Depends on / 依赖: isChain_iff_getElem
-/
theorem exists_not_getElem_of_not_isChain (h : ¬List.IsChain R l) :
    exists n : Nat, exists h : n + 1 < l.length, ¬R l[n] l[n + 1] := by simp_all [isChain_iff_getElem]

/--
theorem `isChain_reverse` / 定理 `isChain_reverse`

English:
theorem isChain_reverse
  given: {l : List α}
  statement: l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a)
  proof: by
  induction l using twoStepInduction with
  | nil => grind
  | singleton a => grind
  | cons_cons a b l IH IH2 =>
    rw [isChain_cons_cons]; rw [reverse_cons]; rw [reverse_cons]; rw [append_assoc]; rw [cons_append]; rw [nil_append]; rw [isChain_split]; rw [← reverse_cons]; rw [IH2]; rw [and_comm

中文:
定理 isChain_reverse
  条件: {l : List α}
  结论: l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a)
  证明: by
  induction l using twoStepInduction with
  | nil => grind
  | singleton a => grind
  | cons_cons a b l IH IH2 =>
    rw [isChain_cons_cons]; rw [reverse_cons]; rw [reverse_cons]; rw [append_assoc]; rw [cons_append]; rw [nil_append]; rw [isChain_split]; rw [← reverse_cons]; rw [IH2]; rw [and_comm

Depends on / 依赖: and_comm, append_assoc, cons_append, cons_cons, isChain_cons_cons, isChain_pair, isChain_split, nil_append, reverse_cons, singleton, twoStepInduction
-/
theorem isChain_reverse {l : List α} : l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a) := by
  induction l using twoStepInduction with
  | nil => grind
  | singleton a => grind
  | cons_cons a b l IH IH2 =>
    rw [isChain_cons_cons]; rw [reverse_cons]; rw [reverse_cons]; rw [append_assoc]; rw [cons_append]; rw [nil_append]; rw [isChain_split]; rw [← reverse_cons]; rw [IH2]; rw [and_comm]; rw [isChain_pair]

/--
theorem `IsChain.append_overlap` / 定理 `IsChain.append_overlap`

English:
theorem IsChain.append_overlap
  statement: {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
  proof: h₁.append h₂.right_of_append by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2

中文:
定理 IsChain.append_overlap
  结论: {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
  证明: h₁.append h₂.right_of_append by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2

Depends on / 依赖: _append_of_ne_nil, append, getLast, isChain_append, right_of_append
-/
theorem IsChain.append_overlap {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
    (h₂ : IsChain R (l₂ ++ l₃)) (hn : l₂ != []) : IsChain R (l₁ ++ l₂ ++ l₃) :=
h₁.append h₂.right_of_append by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2

/--
lemma `isChain_flatten` / 引理 `isChain_flatten`

English:
lemma isChain_flatten
  statement: forall {L : List (List α)}, [] ∉ L ->

中文:
引理 isChain_flatten
  结论: 对任意 {L : List (List α)}, [] ∉ L ->
-/
lemma isChain_flatten : forall {L : List (List α)}, [] ∉ L ->
    (IsChain R L.flatten ↔ (forall l in L, IsChain R l) ∧
    L.IsChain (fun l₁ l₂ => forallᵉ (x in l₁.getLast?) (y in l₂.head?), R x y))
| [], _ => by simp
| [l], _ => by simp [flatten]
| (l₁ :: l₂ :: L), hL => by
    rw [mem_cons]; rw [not_or]; rw [← Ne] at hL
    rw [flatten_cons]; rw [isChain_append]; rw [isChain_flatten hL.2]; rw [forall_mem_cons]; rw [isChain_cons_cons]
    rw [mem_cons]; rw [not_or]; rw [← Ne] at hL
    simp only [forall_mem_cons, and_assoc, flatten_cons, head?_append_of_ne_nil _ hL.2.1.symm]
    exact Iff.rfl.and (Iff.rfl.and <| Iff.rfl.and and_comm)

/--
theorem `isChain_attachWith` / 定理 `isChain_attachWith`

English:
theorem isChain_attachWith
  statement: {l : List α} {p : α -> Prop} (h : forall x in l, p x)
  proof: by
  induction l with grind +splitIndPred

中文:
定理 isChain_attachWith
  结论: {l : List α} {p : α -> 命题} (h : 对任意 x in l, p x)
  证明: by
  induction l with grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
theorem isChain_attachWith {l : List α} {p : α -> Prop} (h : forall x in l, p x)
    {r : {a // p a} -> {a // p a} -> Prop} :
    (l.attachWith p h).IsChain r ↔ l.IsChain fun a b => exists ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction l with grind +splitIndPred

/--
theorem `isChain_attach` / 定理 `isChain_attach`

English:
theorem isChain_attach
  given: {l : List α} {r : {a // a in l} -> {a // a in l} -> Prop}
  proof: isChain_attachWith fun _ => id

中文:
定理 isChain_attach
  条件: {l : List α} {r : {a // a in l} -> {a // a in l} -> 命题}
  证明: isChain_attachWith fun _ => id

Depends on / 依赖: isChain_attachWith
-/
theorem isChain_attach {l : List α} {r : {a // a in l} -> {a // a in l} -> Prop} :
    l.attach.IsChain r ↔ l.IsChain fun a b => exists ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ :=
  isChain_attachWith fun _ => id

/--
theorem `exists_isChain_cons_of_relationReflTransGen` / 定理 `exists_isChain_cons_of_relationReflTransGen`

English:
theorem exists_isChain_cons_of_relationReflTransGen
  given: (h : Relation.ReflTransGen r a b)
  proof: by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], .singleton _, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, .cons_cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]

中文:
定理 exists_isChain_cons_of_relationReflTransGen
  条件: (h : Relation.ReflTransGen r a b)
  证明: by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], .singleton _, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, .cons_cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen.head_induction_on, cons_cons, getLast_cons_cons, head_induction_on, singleton
-/
theorem exists_isChain_cons_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    exists l, IsChain r (a :: l) ∧ getLast (a :: l) (cons_ne_nil _ _) = b := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], .singleton _, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, .cons_cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]

/--
theorem `exists_isChain_ne_nil_of_relationReflTransGen` / 定理 `exists_isChain_ne_nil_of_relationReflTransGen`

English:
theorem exists_isChain_ne_nil_of_relationReflTransGen
  given: (h : Relation.ReflTransGen r a b)
  proof: by
  rcases exists_isChain_cons_of_relationReflTransGen h with ⟨l, _⟩; grind

中文:
定理 exists_isChain_ne_nil_of_relationReflTransGen
  条件: (h : Relation.ReflTransGen r a b)
  证明: by
  rcases exists_isChain_cons_of_relationReflTransGen h with ⟨l, _⟩; grind

Depends on / 依赖: exists_isChain_cons_of_relationReflTransGen
-/
theorem exists_isChain_ne_nil_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    exists l, exists (hl : l != []), IsChain r l ∧ l.head hl = a ∧ getLast l hl = b := by
  rcases exists_isChain_cons_of_relationReflTransGen h with ⟨l, _⟩; grind

/--
theorem `IsChain.induction` / 定理 `IsChain.induction`

English:
theorem IsChain.induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r l)
  proof: by
  induction l using twoStepInduction with grind

中文:
定理 IsChain.induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r l)
  证明: by
  induction l using twoStepInduction with grind

Depends on / 依赖: twoStepInduction
-/
theorem IsChain.induction (p : α -> Prop) (l : List α) (h : IsChain r l)
    (carries : forall ⦃x y : α⦄, r x y -> p x -> p y) (initial : (lne : l != []) -> p (l.head lne)) :
    forall i in l, p i := by
  induction l using twoStepInduction with grind

/--
theorem `IsChain.cons_induction` / 定理 `IsChain.cons_induction`

English:
theorem IsChain.cons_induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
  proof: fun _ hi =>
  h.induction _ _ carries (fun _ => initial) _ (mem_cons_of_mem _ hi)

中文:
定理 IsChain.cons_induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (a :: l))
  证明: fun _ hi =>
  h.induction _ _ carries (fun _ => initial) _ (mem_cons_of_mem _ hi)
-/
theorem IsChain.cons_induction (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
    (carries : forall ⦃x y : α⦄, r x y -> p x -> p y) (initial : p a) : forall i in l, p i := fun _ hi =>
  h.induction _ _ carries (fun _ => initial) _ (mem_cons_of_mem _ hi)

/--
theorem `IsChain.concat_induction` / 定理 `IsChain.concat_induction`

English:
theorem IsChain.concat_induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
  proof: h.induction _ _ carries (fun _ => hb ▸ initial)

@[elab_as_elim]

中文:
定理 IsChain.concat_induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (l ++ [b]))
  证明: h.induction _ _ carries (fun _ => hb ▸ initial)

@[elab_as_elim]

Depends on / 依赖: carries, h.induction, initial
-/
theorem IsChain.concat_induction (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : forall ⦃x y : α⦄, r x y -> p x -> p y)
    (initial : p a) : forall i in l ++ [b], p i :=
  h.induction _ _ carries (fun _ => hb ▸ initial)

@[elab_as_elim]
/--
theorem `IsChain.concat_induction_head` / 定理 `IsChain.concat_induction_head`

English:
theorem IsChain.concat_induction_head
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
  proof: (IsChain.concat_induction p l h hb carries initial) _ mem_concat_self

中文:
定理 IsChain.concat_induction_head
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (l ++ [b]))
  证明: (IsChain.concat_induction p l h hb carries initial) _ mem_concat_self

Depends on / 依赖: IsChain, IsChain.concat_induction, carries, concat_induction, initial, mem_concat_self
-/
theorem IsChain.concat_induction_head (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : forall ⦃x y : α⦄, r x y -> p x -> p y)
    (initial : p a) : p b :=
  (IsChain.concat_induction p l h hb carries initial) _ mem_concat_self

/--
theorem `IsChain.backwards_induction` / 定理 `IsChain.backwards_induction`

English:
theorem IsChain.backwards_induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r l)
  proof: by
  have H : IsChain (flip (flip r)) l := h
  replace H := (isChain_reverse.mpr H).induction _ _ (fun _ _ h => carries h)
  grind

中文:
定理 IsChain.backwards_induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r l)
  证明: by
  have H : IsChain (flip (flip r)) l := h
  replace H := (isChain_reverse.mpr H).induction _ _ (fun _ _ h => carries h)
  grind

Depends on / 依赖: IsChain, carries, isChain_reverse, isChain_reverse.mpr, replace
-/
theorem IsChain.backwards_induction (p : α -> Prop) (l : List α) (h : IsChain r l)
    (carries : forall ⦃x y : α⦄, r x y -> p y -> p x) (final : (lne : l != []) -> p (getLast l lne)) :
    forall i in l, p i := by
  have H : IsChain (flip (flip r)) l := h
  replace H := (isChain_reverse.mpr H).induction _ _ (fun _ _ h => carries h)
  grind

/--
theorem `IsChain.backwards_concat_induction` / 定理 `IsChain.backwards_concat_induction`

English:
theorem IsChain.backwards_concat_induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
  proof: fun _ hi =>
  h.backwards_induction _ _ carries (fun _ => getLast_concat ▸ final) _ (mem_append_left _ hi)

中文:
定理 IsChain.backwards_concat_induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (l ++ [b]))
  证明: fun _ hi =>
  h.backwards_induction _ _ carries (fun _ => getLast_concat ▸ final) _ (mem_append_left _ hi)
-/
theorem IsChain.backwards_concat_induction (p : α -> Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (carries : forall ⦃x y : α⦄, r x y -> p y -> p x) (final : p b) : forall i in l, p i := fun _ hi =>
  h.backwards_induction _ _ carries (fun _ => getLast_concat ▸ final) _ (mem_append_left _ hi)

/--
theorem `IsChain.backwards_cons_induction` / 定理 `IsChain.backwards_cons_induction`

English:
theorem IsChain.backwards_cons_induction
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
  proof: h.backwards_induction _ _ carries (fun _ => hb ▸ final)

中文:
定理 IsChain.backwards_cons_induction
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (a :: l))
  证明: h.backwards_induction _ _ carries (fun _ => hb ▸ final)

Depends on / 依赖: backwards_induction, carries, h.backwards_induction
-/
theorem IsChain.backwards_cons_induction (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : forall ⦃x y : α⦄, r x y -> p y -> p x)
    (final : p b) : forall i in a :: l, p i :=
  h.backwards_induction _ _ carries (fun _ => hb ▸ final)

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_elim]
/--
theorem `IsChain.backwards_cons_induction_head` / 定理 `IsChain.backwards_cons_induction_head`

English:
theorem IsChain.backwards_cons_induction_head
  statement: (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
  proof: (IsChain.backwards_cons_induction p l h hb carries final) _ mem_cons_self

中文:
定理 IsChain.backwards_cons_induction_head
  结论: (p : α -> 命题) (l : List α) (h : IsChain r (a :: l))
  证明: (IsChain.backwards_cons_induction p l h hb carries final) _ mem_cons_self

Depends on / 依赖: IsChain, IsChain.backwards_cons_induction, backwards_cons_induction, carries, mem_cons_self
-/
theorem IsChain.backwards_cons_induction_head (p : α -> Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : forall ⦃x y : α⦄, r x y -> p y -> p x)
    (final : p b) : p a :=
  (IsChain.backwards_cons_induction p l h hb carries final) _ mem_cons_self

/--
theorem `relationReflTransGen_of_exists_isChain` / 定理 `relationReflTransGen_of_exists_isChain`

English:
theorem relationReflTransGen_of_exists_isChain
  given: (l : List α) (hl₁ : IsChain r l) (hne : l != [])
  proof: IsChain.induction (Relation.ReflTransGen r (head l hne) ·) l hl₁
  (fun _ _ h₁ h₂ => Trans.trans h₂ h₁) (fun _ => Relation.ReflTransGen.refl) _ (getLast_mem _)

中文:
定理 relationReflTransGen_of_exists_isChain
  条件: (l : List α) (hl₁ : IsChain r l) (hne : l != [])
  证明: IsChain.induction (Relation.ReflTransGen r (head l hne) ·) l hl₁
  (fun _ _ h₁ h₂ => Trans.trans h₂ h₁) (fun _ => Relation.ReflTransGen.refl) _ (getLast_mem _)

Depends on / 依赖: IsChain, IsChain.induction, ReflTransGen, Relation, Relation.ReflTransGen, Relation.ReflTransGen.refl, Trans.trans, getLast_mem
-/
theorem relationReflTransGen_of_exists_isChain (l : List α) (hl₁ : IsChain r l) (hne : l != []) :
    Relation.ReflTransGen r (head l hne) (getLast l hne) :=
  IsChain.induction (Relation.ReflTransGen r (head l hne) ·) l hl₁
  (fun _ _ h₁ h₂ => Trans.trans h₂ h₁) (fun _ => Relation.ReflTransGen.refl) _ (getLast_mem _)

/--
theorem `relationReflTransGen_of_exists_isChain_cons` / 定理 `relationReflTransGen_of_exists_isChain_cons`

English:
theorem relationReflTransGen_of_exists_isChain_cons
  statement: (l : List α) (hl₁ : IsChain r (a :: l))
  proof: IsChain.backwards_cons_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
  Relation.ReflTransGen.refl

中文:
定理 relationReflTransGen_of_exists_isChain_cons
  结论: (l : List α) (hl₁ : IsChain r (a :: l))
  证明: IsChain.backwards_cons_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
  Relation.ReflTransGen.refl

Depends on / 依赖: IsChain, IsChain.backwards_cons_induction_head, ReflTransGen, Relation, Relation.ReflTransGen.head, Relation.ReflTransGen.refl, backwards_cons_induction_head
-/
theorem relationReflTransGen_of_exists_isChain_cons (l : List α) (hl₁ : IsChain r (a :: l))
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
  IsChain.backwards_cons_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
  Relation.ReflTransGen.refl

/--
theorem `IsChain.cons_of_le` / 定理 `IsChain.cons_of_le`

English:
theorem IsChain.cons_of_le
  statement: [LinearOrder α] {a : α} {as m : List α}
  proof: by
  cases m with
  | nil => grind
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.isChain_cons_cons] at ha
      refine lt_of_le_of_l

中文:
定理 IsChain.cons_of_le
  结论: [LinearOrder α] {a : α} {as m : List α}
  证明: by
  cases m with
  | nil => grind
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.isChain_cons_cons] at ha
      refine lt_of_le_of_l

Depends on / 依赖: List.cons.injEq, List.isChain_cons_cons, List.not_lt_nil, cons_cons, head_le_of_lt, hm.cons_cons, isChain_cons_cons, le_iff_lt_or_eq, le_refl, lt_of_le_of_lt, not_lt_nil, or_false, reduceCtorEq
-/
theorem IsChain.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.IsChain (· > ·) (a :: as)) (hm : List.IsChain (· > ·) m) (hmas : m <= as) :
    List.IsChain (· > ·) (a :: m) := by
  cases m with
  | nil => grind
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.isChain_cons_cons] at ha
      refine lt_of_le_of_lt ?_ ha.1
      rw [le_iff_lt_or_eq] at hmas
      rcases hmas with hmas | hmas
      · exact head_le_of_lt hmas
      · simp_all only [List.cons.injEq, le_refl]

/--
lemma `IsChain.isChain_cons` / 引理 `IsChain.isChain_cons`

English:
lemma IsChain.isChain_cons
  statement: {α : Type*} {R : α -> α -> Prop} {l : List α} {v : α}
  proof: by
  cases l <;> grind

中文:
引理 IsChain.isChain_cons
  结论: {α : 类型} {R : α -> α -> 命题} {l : List α} {v : α}
  证明: by
  cases l <;> grind
-/
lemma IsChain.isChain_cons {α : Type*} {R : α -> α -> Prop} {l : List α} {v : α}
    (hl : l.IsChain R) (hv : (lne : l != []) -> R v (l.head lne)) : (v :: l).IsChain R := by
  cases l <;> grind

/--
lemma `IsChain.iterate_eq_of_apply_eq` / 引理 `IsChain.iterate_eq_of_apply_eq`

English:
lemma IsChain.iterate_eq_of_apply_eq
  statement: {α : Type*} {f : α -> α} {l : List α}
  proof: by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [h (by lia)]
    rw [List.isChain_iff_getElem] at hl
    apply hl

中文:
引理 IsChain.iterate_eq_of_apply_eq
  结论: {α : 类型} {f : α -> α} {l : List α}
  证明: by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [h (by lia)]
    rw [List.isChain_iff_getElem] at hl
    apply hl

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, List.isChain_iff_getElem, comp_apply, isChain_iff_getElem, iterate_succ
-/
lemma IsChain.iterate_eq_of_apply_eq {α : Type*} {f : α -> α} {l : List α}
    (hl : l.IsChain (fun x y => f x = y)) (i : Nat) (hi : i < l.length) :
    f^[i] l[0] = l[i] := by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ']; rw [Function.comp_apply]; rw [h (by lia)]
    rw [List.isChain_iff_getElem] at hl
    apply hl

/--
theorem `isChain_replicate_of_rel` / 定理 `isChain_replicate_of_rel`

English:
theorem isChain_replicate_of_rel
  given: (n : Nat) {a : α} (h : r a a)
  statement: IsChain r (replicate n a)
  proof: by
  induction n using Nat.twoStepInduction <;> grind

中文:
定理 isChain_replicate_of_rel
  条件: (n : 自然数) {a : α} (h : r a a)
  结论: IsChain r (replicate n a)
  证明: by
  induction n using Nat.twoStepInduction <;> grind

Depends on / 依赖: Nat.twoStepInduction, twoStepInduction
-/
theorem isChain_replicate_of_rel (n : Nat) {a : α} (h : r a a) : IsChain r (replicate n a) := by
  induction n using Nat.twoStepInduction <;> grind

/--
theorem `isChain_eq_iff_eq_replicate` / 定理 `isChain_eq_iff_eq_replicate`

English:
theorem isChain_eq_iff_eq_replicate
  given: {l : List α}
  proof: by
  induction l using twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b l IH IH2 =>
    simp +contextual [isChain_cons_cons, eq_comm, IH2, replicate_succ]

中文:
定理 isChain_eq_iff_eq_replicate
  条件: {l : List α}
  证明: by
  induction l using twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b l IH IH2 =>
    simp +contextual [isChain_cons_cons, eq_comm, IH2, replicate_succ]

Depends on / 依赖: cons_cons, contextual, eq_comm, isChain_cons_cons, replicate_succ, singleton, twoStepInduction
-/
theorem isChain_eq_iff_eq_replicate {l : List α} :
    IsChain (· = ·) l ↔ forall a in l.head?, l = replicate l.length a := by
  induction l using twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b l IH IH2 =>
    simp +contextual [isChain_cons_cons, eq_comm, IH2, replicate_succ]

/--
theorem `isChain_cons_eq_iff_eq_replicate` / 定理 `isChain_cons_eq_iff_eq_replicate`

English:
theorem isChain_cons_eq_iff_eq_replicate
  given: {a : α} {l : List α}
  proof: by
  simp [isChain_eq_iff_eq_replicate, replicate_succ]

中文:
定理 isChain_cons_eq_iff_eq_replicate
  条件: {a : α} {l : List α}
  证明: by
  simp [isChain_eq_iff_eq_replicate, replicate_succ]

Depends on / 依赖: isChain_eq_iff_eq_replicate, replicate_succ
-/
theorem isChain_cons_eq_iff_eq_replicate {a : α} {l : List α} :
    IsChain (· = ·) (a :: l) ↔ l = replicate l.length a := by
  simp [isChain_eq_iff_eq_replicate, replicate_succ]

end List

/--
theorem `WellFoundedRelation.asymmetricₙ` / 定理 `WellFoundedRelation.asymmetricₙ`

English:
theorem WellFoundedRelation.asymmetricₙ
  statement: [WellFoundedRelation α] {l : List α} (hne : l != [])
  proof: match l with
  | [x] => irrefl x
  | _ :: _ :: _ =>
    fun hr => asymmetricₙ (List.cons_ne_nil _ _) (h.dropLast.cons_cons hr) (h.rel_getLast_dropLast _)
termination_by l.head hne

中文:
定理 WellFoundedRelation.asymmetricₙ
  结论: [WellFoundedRelation α] {l : List α} (hne : l != [])
  证明: match l with
  | [x] => irrefl x
  | _ :: _ :: _ =>
    fun hr => asymmetricₙ (List.cons_ne_nil _ _) (h.dropLast.cons_cons hr) (h.rel_getLast_dropLast _)
termination_by l.head hne

Depends on / 依赖: List.cons_ne_nil, cons_cons, cons_ne_nil, dropLast, h.dropLast.cons_cons, h.rel_getLast_dropLast, irrefl, l.head, rel_getLast_dropLast, termination_by
-/
theorem WellFoundedRelation.asymmetricₙ [WellFoundedRelation α] {l : List α} (hne : l != [])
    (h : l.IsChain WellFoundedRelation.rel) :
    ¬WellFoundedRelation.rel (l.getLast hne) (l.head hne) :=
  match l with
  | [x] => irrefl x
  | _ :: _ :: _ =>
    fun hr => asymmetricₙ (List.cons_ne_nil _ _) (h.dropLast.cons_cons hr) (h.rel_getLast_dropLast _)
termination_by l.head hne

/--
theorem `WellFounded.asymmetricₙ` / 定理 `WellFounded.asymmetricₙ`

English:
theorem WellFounded.asymmetricₙ
  given: (wf : WellFounded r) (hne : l != []) (h : l.IsChain r)
  proof: @WellFoundedRelation.asymmetricₙ α ⟨r, wf⟩ l hne h

中文:
定理 WellFounded.asymmetricₙ
  条件: (wf : WellFounded r) (hne : l != []) (h : l.IsChain r)
  证明: @WellFoundedRelation.asymmetricₙ α ⟨r, wf⟩ l hne h

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.asymmetric
-/
theorem WellFounded.asymmetricₙ (wf : WellFounded r) (hne : l != []) (h : l.IsChain r) :
    ¬r (l.getLast hne) (l.head hne) :=
  @WellFoundedRelation.asymmetricₙ α ⟨r, wf⟩ l hne h

/--
theorem `WellFounded.listPairwise_reverse_compl` / 定理 `WellFounded.listPairwise_reverse_compl`

English:
theorem WellFounded.listPairwise_reverse_compl
  given: (wf : WellFounded r) (h : l.IsChain r)
  proof: by
  refine List.pairwise_iff_forall_infix.mpr fun l' hne hsub => ?_
have := wf.asymmetricₙ (by grind) h.infix l.reverse_reverse ▸ hsub.reverse
  simpa

中文:
定理 WellFounded.listPairwise_reverse_compl
  条件: (wf : WellFounded r) (h : l.IsChain r)
  证明: by
  refine List.pairwise_iff_forall_infix.mpr fun l' hne hsub => ?_
have := wf.asymmetricₙ (by grind) h.infix l.reverse_reverse ▸ hsub.reverse
  simpa

Depends on / 依赖: List.pairwise_iff_forall_infix.mpr, h.infix, hsub.reverse, l.reverse_reverse, pairwise_iff_forall_infix, reverse, reverse_reverse, wf.asymmetric
-/
theorem WellFounded.listPairwise_reverse_compl (wf : WellFounded r) (h : l.IsChain r) :
    l.reverse.Pairwise rᶜ := by
  refine List.pairwise_iff_forall_infix.mpr fun l' hne hsub => ?_
have := wf.asymmetricₙ (by grind) h.infix l.reverse_reverse ▸ hsub.reverse
  simpa

/-! In this section, we consider the type of `r`-decreasing chains (`List.IsChain (flip r)`)
  equipped with lexicographic order `List.Lex r`. -/

variable (r)

/--
Definition of `List.chains` / `List.chains` 的定义

English:
abbreviation List.chains
  body: { l : List α // l.IsChain (flip r) }

中文:
缩写 List.chains
  定义体: { l : List α // l.IsChain (flip r) }

Depends on / 依赖: IsChain, l.IsChain
-/
abbrev List.chains := { l : List α // l.IsChain (flip r) }

/--
Definition of `List.lex_chains` / `List.lex_chains` 的定义

English:
abbreviation List.lex_chains
  signature: (l m : List.chains r)
  body: List.Lex r l.val m.val

中文:
缩写 List.lex_chains
  签名: (l m : List.chains r)
  定义体: List.Lex r l.val m.val

Depends on / 依赖: List.Lex, l.val, m.val
-/
abbrev List.lex_chains (l m : List.chains r) : Prop := List.Lex r l.val m.val

variable {r}

/--
theorem `Acc.list_chain'` / 定理 `Acc.list_chain'`

English:
theorem Acc.list_chain'
  given: {l : List.chains r} (acc : forall a in l.val.head?, Acc r a)
  proof: by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  specialize acc a _
  · rw [List.head?_cons, Option.mem_some_iff]
  /- For an r-decreasing chain of the form a :: l, apply induction on a -/
  induction acc generalizing l with
  | intro a _ ih =>
    /- Bundle l with a proof tha

中文:
定理 Acc.list_chain'
  条件: {l : List.chains r} (acc : 对任意 a in l.val.head?, Acc r a)
  证明: by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  specialize acc a _
  · rw [List.head?_cons, Option.mem_some_iff]
  /- For an r-decreasing chain of the form a :: l, apply induction on a -/
  induction acc generalizing l with
  | intro a _ ih =>
    /- Bundle l with a proof tha

Depends on / 依赖: Acc.intro, List.head, Option.mem_some_iff, _cons, mem_some_iff, specialize
-/
theorem Acc.list_chain' {l : List.chains r} (acc : forall a in l.val.head?, Acc r a) :
    Acc (List.lex_chains r) l := by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  specialize acc a _
  · rw [List.head?_cons, Option.mem_some_iff]
  /- For an r-decreasing chain of the form a :: l, apply induction on a -/
  induction acc generalizing l with
  | intro a _ ih =>
    /- Bundle l with a proof that it is r-decreasing to form l' -/
    have hl' := (List.isChain_cons.1 hl).2
    let l' : List.chains r := ⟨l, hl'⟩
    have : Acc (List.lex_chains r) l' := by
      rcases l with - | ⟨b, l⟩
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      /- l' is accessible by induction hypothesis -/
      · apply ih b (List.isChain_cons_cons.1 hl).1
    /- make l' a free variable and induct on l' -/
    revert hl
    rw [(by rfl : l = l'.1)]
    clear_value l'
    induction this with
    | intro l _ ihl =>
      intro hl
      apply Acc.intro
      rintro ⟨_ | ⟨b, m⟩, hm⟩ (_ | hr | hr)
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      · apply ih b hr
      · apply ihl ⟨m, (List.isChain_cons.1 hm).2⟩ hr

/--
theorem `WellFounded.list_chain'` / 定理 `WellFounded.list_chain'`

English:
theorem WellFounded.list_chain'
  given: (hwf : WellFounded r)
  proof: ⟨fun _ => Acc.list_chain' (fun _ _ => hwf.apply _)⟩

中文:
定理 WellFounded.list_chain'
  条件: (hwf : WellFounded r)
  证明: ⟨fun _ => Acc.list_chain' (fun _ _ => hwf.apply _)⟩

Depends on / 依赖: Acc.list_chain, hwf.apply, list_chain
-/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ => Acc.list_chain' (fun _ _ => hwf.apply _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hwf
  signature: : IsWellFounded α r] :
  body: ⟨hwf.wf.list_chain'⟩

中文:
实例 [hwf
  签名: : IsWellFounded α r] :
  定义体: ⟨hwf.wf.list_chain'⟩

Depends on / 依赖: hwf.wf.list_chain, list_chain
-/
instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
