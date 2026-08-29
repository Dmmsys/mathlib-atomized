/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/
module

public import Mathlib.Data.List.Induction
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Group

/-!
This file defines some extra lemmas for free groups, in particular about cyclically reduced words.
We show that free groups are (strongly) torsion-free in the sense of `IsMulTorsionFree`, i.e.,
taking powers by every non-zero element `n : ℕ` is injective.

## Main declarations

* `FreeGroup.IsCyclicallyReduced`: the predicate for cyclically reduced words

-/

@[expose] public section
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

/-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced and furthermore
the first and the last letter of the word do not cancel. The empty word is by convention also
cyclically reduced. -/
@[to_additive /-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced
and furthermore the first and the last letter of the word do not cancel. The empty word is by
convention also cyclically reduced. -/]
/--
Definition of `IsCyclicallyReduced` / `IsCyclicallyReduced` 的定义

English:
definition IsCyclicallyReduced
  signature: (L : List (α × Bool))
  body: IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.1 -> a.2 = b.2

@[to_additive]

中文:
定义 IsCyclicallyReduced
  签名: (L : 列表 (α × 布尔值))
  定义体: IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.1 -> a.2 = b.2

@[to_additive]

Depends on / 依赖: IsReduced, L.getLast, L.head, getLast
-/
def IsCyclicallyReduced (L : List (α × Bool)) : Prop :=
  IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.1 -> a.2 = b.2

@[to_additive]
/--
theorem `isCyclicallyReduced_iff` / 定理 `isCyclicallyReduced_iff`

English:
theorem isCyclicallyReduced_iff
  proof: Iff.rfl

@[to_additive]

中文:
定理 isCyclicallyReduced_iff
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem isCyclicallyReduced_iff :
    IsCyclicallyReduced L ↔
    IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.1 -> a.2 = b.2 := Iff.rfl

@[to_additive]
/--
theorem `isCyclicallyReduced_cons_append_iff` / 定理 `isCyclicallyReduced_cons_append_iff`

English:
theorem isCyclicallyReduced_cons_append_iff
  given: {a b : α × Bool}
  proof: by
  rw [isCyclicallyReduced_iff]; rw [List.getLast?_concat]
  simp

中文:
定理 isCyclicallyReduced_cons_append_iff
  条件: {a b : α × 布尔值}
  证明: by
  rw [isCyclicallyReduced_iff]; rw [List.getLast?_concat]
  simp

Depends on / 依赖: List.getLast, _concat, getLast, isCyclicallyReduced_iff
-/
theorem isCyclicallyReduced_cons_append_iff {a b : α × Bool} :
    IsCyclicallyReduced (b :: L ++ [a]) ↔
    IsReduced (b :: L ++ [a]) ∧ (a.1 = b.1 -> a.2 = b.2) := by
  rw [isCyclicallyReduced_iff]; rw [List.getLast?_concat]
  simp

namespace IsCyclicallyReduced

@[to_additive (attr := simp)]
/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  statement: IsCyclicallyReduced ([] : List (α × Bool))
  proof: by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]

中文:
定理 nil
  结论: IsCyclicallyReduced ([] : 列表 (α × 布尔值))
  证明: by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]
-/
protected theorem nil : IsCyclicallyReduced ([] : List (α × Bool)) := by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]
/--
theorem `singleton` / 定理 `singleton`

English:
theorem singleton
  given: {x : (α × Bool)}
  statement: IsCyclicallyReduced [x]
  proof: by
  simp [IsCyclicallyReduced]


@[to_additive]

中文:
定理 singleton
  条件: {x : (α × 布尔值)}
  结论: IsCyclicallyReduced [x]
  证明: by
  simp [IsCyclicallyReduced]


@[to_additive]
-/
protected theorem singleton {x : (α × Bool)} : IsCyclicallyReduced [x] := by
  simp [IsCyclicallyReduced]


@[to_additive]
/--
theorem `isReduced` / 定理 `isReduced`

English:
theorem isReduced
  given: (h : IsCyclicallyReduced L)
  statement: IsReduced L
  proof: h.1

@[to_additive]

中文:
定理 isReduced
  条件: (h : IsCyclicallyReduced L)
  结论: 是既约 L
  证明: h.1

@[to_additive]
-/
theorem isReduced (h : IsCyclicallyReduced L) : IsReduced L := h.1

@[to_additive]
/--
theorem `flatten_replicate` / 定理 `flatten_replicate`

English:
theorem flatten_replicate
  given: (h : IsCyclicallyReduced L) (n : Nat)
  proof: by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff]; rw [IsReduced]; rw [List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb => ?_⟩
    rw [O

中文:
定理 flatten_replicate
  条件: (h : IsCyclicallyReduced L) (n : 自然数)
  证明: by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff]; rw [IsReduced]; rw [List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb => ?_⟩
    rw [O

Depends on / 依赖: IsReduced, List.getLast, List.head, List.isChain_flatten, List.isChain_replicate_of_rel, Option.mem_def, _flatten_replicate, getLast, h.isReduced, isChain_flatten, isChain_replicate_of_rel, isCyclicallyReduced_iff, isReduced, mem_def
-/
theorem flatten_replicate (h : IsCyclicallyReduced L) (n : Nat) :
    IsCyclicallyReduced (List.replicate n L).flatten := by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff]; rw [IsReduced]; rw [List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb => ?_⟩
    rw [Option.mem_def]; rw [List.getLast?_flatten_replicate (h := by simp +arith)] at ha
    rw [Option.mem_def]; rw [List.head?_flatten_replicate (h := by simp +arith)] at hb
    exact h.2 _ ha _ hb

end IsCyclicallyReduced

@[to_additive]
/--
theorem `IsReduced.append_flatten_replicate_append` / 定理 `IsReduced.append_flatten_replicate_append`

English:
theorem IsReduced.append_flatten_replicate_append
  statement: (h₁ : IsCyclicallyReduced L₂)
  proof: by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten != [] := by simp [h]
    refine IsReduced.append_overlap ?_ ?_ (hn := h')
    · rw [replicate_succ, flatten_cons, ← append_assoc]
      refine IsReduced.append_ove

中文:
定理 是既约.append_flatten_replicate_append
  结论: (h₁ : IsCyclicallyReduced L₂)
  证明: by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten != [] := by simp [h]
    refine IsReduced.append_overlap ?_ ?_ (hn := h')
    · rw [replicate_succ, flatten_cons, ← append_assoc]
      refine IsReduced.append_ove

Depends on / 依赖: IsReduced, IsReduced.append_overlap, append_assoc, append_overlap, flatten, flatten_concat, flatten_cons, flatten_replicate, isReduced, replicate, replicate_succ
-/
theorem IsReduced.append_flatten_replicate_append (h₁ : IsCyclicallyReduced L₂)
    (h₂ : IsReduced (L₁ ++ L₂ ++ L₃)) {n : Nat} (hn : n != 0) :
  IsReduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃) := by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten != [] := by simp [h]
    refine IsReduced.append_overlap ?_ ?_ (hn := h')
    · rw [replicate_succ, flatten_cons, ← append_assoc]
      refine IsReduced.append_overlap (h₂.infix ⟨[], L₃, by simp⟩) ?_ h
      rw [← flatten_cons]; rw [← replicate_succ]
      exact (h₁.flatten_replicate _).isReduced
    · rw [replicate_succ', flatten_concat]
      refine IsReduced.append_overlap ?_ (h₂.infix ⟨L₁, [], by simp⟩) h
      rw [← flatten_concat]; rw [← replicate_succ']
      exact (h₁.flatten_replicate _).isReduced

/-- This function produces a subword of a word `L` by cancelling the first and last letters of `L`
as long as possible. If `L` is reduced, the resulting word will be cyclically reduced. -/
@[to_additive /-- This function produces a subword of a word `L` by cancelling the first and last
letters of `L` as long as possible. If `L` is reduced, the resulting word will be cyclically
reduced. -/]
/--
Definition of `reduceCyclically` / `reduceCyclically` 的定义

English:
definition reduceCyclically
  signature: [DecidableEq α]
  body: List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a L b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: L ++ [b])

中文:
定义 reduceCyclically
  签名: [DecidableEq α]
  定义体: List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a L b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: L ++ [b])

Depends on / 依赖: List.bidirectionalRec, bidirectionalRec, cons_append, singleton
-/
def reduceCyclically [DecidableEq α] : List (α × Bool) -> List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a L b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: L ++ [b])

namespace reduceCyclically
variable [DecidableEq α]

@[to_additive (attr := simp)]
/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  statement: reduceCyclically ([] : List (α × Bool)) = []
  proof: by simp [reduceCyclically]

@[to_additive (attr := simp)]

中文:
定理 nil
  结论: reduceCyclically ([] : 列表 (α × 布尔值)) = []
  证明: by simp [reduceCyclically]

@[to_additive (attr := simp)]
-/
protected theorem nil : reduceCyclically ([] : List (α × Bool)) = [] := by simp [reduceCyclically]

@[to_additive (attr := simp)]
/--
theorem `singleton` / 定理 `singleton`

English:
theorem singleton
  given: {a : α × Bool}
  statement: reduceCyclically [a] = [a]
  proof: by
  simp [reduceCyclically]

@[to_additive]

中文:
定理 singleton
  条件: {a : α × 布尔值}
  结论: reduceCyclically [a] = [a]
  证明: by
  simp [reduceCyclically]

@[to_additive]
-/
protected theorem singleton {a : α × Bool} : reduceCyclically [a] = [a] := by
  simp [reduceCyclically]

@[to_additive]
/--
theorem `cons_append` / 定理 `cons_append`

English:
theorem cons_append
  given: {a b : α × Bool} (L : List (α × Bool))
  proof: by
  simp [reduceCyclically]


@[to_additive]

中文:
定理 cons_append
  条件: {a b : α × 布尔值} (L : 列表 (α × 布尔值))
  证明: by
  simp [reduceCyclically]


@[to_additive]
-/
protected theorem cons_append {a b : α × Bool} (L : List (α × Bool)) :
    reduceCyclically (a :: (L ++ [b])) =
    if b.1 = a.1 ∧ (!b.2) = a.2 then reduceCyclically L else a :: L ++ [b] := by
  simp [reduceCyclically]


@[to_additive]
/--
theorem `isCyclicallyReduced` / 定理 `isCyclicallyReduced`

English:
theorem isCyclicallyReduced
  given: (h : IsReduced L)
  statement: IsCyclicallyReduced (reduceCyclically L)
  proof: by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      ex

中文:
定理 isCyclicallyReduced
  条件: (h : 是既约 L)
  结论: IsCyclicallyReduced (reduceCyclically L)
  证明: by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      ex

Depends on / 依赖: List.bidirectionalRec, bidirectionalRec, cons_append, h.infix, isCyclicallyReduced_cons_append_iff, isFalse, isTrue, reduceCyclically, reduceCyclically.cons_append, singleton
-/
theorem isCyclicallyReduced (h : IsReduced L) : IsCyclicallyReduced (reduceCyclically L) := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      exact ⟨h, by simpa using h'⟩

/-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/
@[to_additive /-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/]
/--
Definition of `conjugator` / `conjugator` 的定义

English:
definition conjugator
  signature: : List (α × Bool) -> List (α × Bool)
  body: List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]

中文:
定义 conjugator
  签名: : 列表 (α × 布尔值) -> 列表 (α × 布尔值)
  定义体: List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]

Depends on / 依赖: List.bidirectionalRec, bidirectionalRec, cons_append, singleton
-/
def conjugator : List (α × Bool) -> List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]
/--
theorem `conjugator.nil` / 定理 `conjugator.nil`

English:
theorem conjugator.nil
  statement: conjugator ([] : List (α × Bool)) = []
  proof: by simp [conjugator]

@[to_additive (attr := simp)]

中文:
定理 conjugator.nil
  结论: conjugator ([] : 列表 (α × 布尔值)) = []
  证明: by simp [conjugator]

@[to_additive (attr := simp)]
-/
protected theorem conjugator.nil : conjugator ([] : List (α × Bool)) = [] := by simp [conjugator]

@[to_additive (attr := simp)]
/--
theorem `conjugator.singleton` / 定理 `conjugator.singleton`

English:
theorem conjugator.singleton
  given: {a : α × Bool}
  statement: conjugator [a] = []
  proof: by simp [conjugator]

@[to_additive]

中文:
定理 conjugator.singleton
  条件: {a : α × 布尔值}
  结论: conjugator [a] = []
  证明: by simp [conjugator]

@[to_additive]
-/
protected theorem conjugator.singleton {a : α × Bool} : conjugator [a] = [] := by simp [conjugator]

@[to_additive]
/--
theorem `conjugator.cons_append` / 定理 `conjugator.cons_append`

English:
theorem conjugator.cons_append
  given: {a b : α × Bool} (L : List (α × Bool))
  proof: by
  simp [conjugator]

@[to_additive]

中文:
定理 conjugator.cons_append
  条件: {a b : α × 布尔值} (L : 列表 (α × 布尔值))
  证明: by
  simp [conjugator]

@[to_additive]
-/
protected theorem conjugator.cons_append {a b : α × Bool} (L : List (α × Bool)) :
    conjugator (a :: (L ++ [b])) = if b.1 = a.1 ∧ (!b.2) = a.2 then a :: conjugator L else [] := by
  simp [conjugator]

@[to_additive]
/--
theorem `conj_conjugator_reduceCyclically` / 定理 `conj_conjugator_reduceCyclically`

English:
theorem conj_conjugator_reduceCyclically
  given: (L : List (α × Bool))
  proof: by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append]; rw [conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => 

中文:
定理 conj_conjugator_reduceCyclically
  条件: (L : 列表 (α × 布尔值))
  证明: by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append]; rw [conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => 

Depends on / 依赖: List.bidirectionalRec, bidirectionalRec, conjugator, conjugator.cons_append, cons_append, invRev, isFalse, isTrue, nth_rw, reduceCyclically, reduceCyclically.cons_append, singleton
-/
theorem conj_conjugator_reduceCyclically (L : List (α × Bool)) :
    conjugator L ++ reduceCyclically L ++ invRev (conjugator L) = L := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append]; rw [conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

@[to_additive]
/--
theorem `reduce_flatten_replicate_succ` / 定理 `reduce_flatten_replicate_succ`

English:
theorem reduce_flatten_replicate_succ
  given: (h : IsReduced L) (n : Nat)
  proof: by
  induction n
  case zero =>
    simpa [← append_assoc, conj_conjugator_reduceCyclically, ← isReduced_iff_reduce_eq]
  case succ n ih =>
    rw [replicate_succ]; rw [flatten_cons]; rw [← reduce_append_reduce_reduce]; rw [ih]; rw [h.reduce_eq]
    nth_rewrite 1 [← conj_conjugator_reduceCyclically 

中文:
定理 reduce_flatten_replicate_succ
  条件: (h : 是既约 L) (n : 自然数)
  证明: by
  induction n
  case zero =>
    simpa [← append_assoc, conj_conjugator_reduceCyclically, ← isReduced_iff_reduce_eq]
  case succ n ih =>
    rw [replicate_succ]; rw [flatten_cons]; rw [← reduce_append_reduce_reduce]; rw [ih]; rw [h.reduce_eq]
    nth_rewrite 1 [← conj_conjugator_reduceCyclically 

Depends on / 依赖: append_assoc, conj_conjugator_reduceCyclically, flatten_cons, h.reduce_eq, invRev, inv_mk, isReduced_iff_reduce_eq, mul_mk, nth_rewrite, reduce.sound, reduce_append_reduce_reduce, reduce_eq, repeat, replicate_succ
-/
theorem reduce_flatten_replicate_succ (h : IsReduced L) (n : Nat) :
    reduce (List.replicate (n + 1) L).flatten = conjugator L ++
    (List.replicate (n + 1) (reduceCyclically L)).flatten ++ invRev (conjugator L) := by
  induction n
  case zero =>
    simpa [← append_assoc, conj_conjugator_reduceCyclically, ← isReduced_iff_reduce_eq]
  case succ n ih =>
    rw [replicate_succ]; rw [flatten_cons]; rw [← reduce_append_reduce_reduce]; rw [ih]; rw [h.reduce_eq]
    nth_rewrite 1 [← conj_conjugator_reduceCyclically L]
    have {L₁ L₂ L₃ L₄ L₅ : List (α × Bool)} : reduce (L₁ ++ L₂ ++ invRev L₃ ++ (L₃ ++ L₄ ++ L₅)) =
        reduce (L₁ ++ (L₂ ++ L₄) ++ L₅) := by
      apply reduce.sound
      repeat rw [← mul_mk]
      rw [← inv_mk]
      group
    rw [this]; rw [← flatten_cons]; rw [← replicate_succ]; rw [← isReduced_iff_reduce_eq]
    apply IsReduced.append_flatten_replicate_append (hn := by simp)
    · exact isCyclicallyReduced h
    · rwa [conj_conjugator_reduceCyclically]

@[to_additive]
/--
theorem `reduce_flatten_replicate` / 定理 `reduce_flatten_replicate`

English:
theorem reduce_flatten_replicate
  given: (h : IsReduced L) (n : Nat)
  proof: match n with
  | 0 => by simp
  | n + 1 => reduce_flatten_replicate_succ h n

中文:
定理 reduce_flatten_replicate
  条件: (h : 是既约 L) (n : 自然数)
  证明: match n with
  | 0 => by simp
  | n + 1 => reduce_flatten_replicate_succ h n

Depends on / 依赖: reduce_flatten_replicate_succ
-/
theorem reduce_flatten_replicate (h : IsReduced L) (n : Nat) :
    reduce (List.replicate n L).flatten = if n = 0 then [] else conjugator L ++
    (List.replicate n (reduceCyclically L)).flatten ++ invRev (conjugator L) :=
  match n with
  | 0 => by simp
  | n + 1 => reduce_flatten_replicate_succ h n

end reduceCyclically

section IsMulTorsionFree
open reduceCyclically

/-- Free groups are torsion-free, i.e., taking powers is injective. Our proof idea is as follows:
if `x ^ n = y ^ n`, then also `x ^ (2 * n) = y ^ (2 * n)`. We then compare the reduced words
representing the powers in terms of the cyclic reductions of `x.toWord` and `y.toWord` using
`reduce_flatten_replicate`. We conclude that the cyclic reductions of `x.toWord` and `y.toWord` must
have the same length, and in fact they have to agree. -/
@[to_additive /-- Free additive groups are torsion free, i.e., scalar multiplication by every
non-zero element `n : ℕ` is injective. See the instance for free groups for an overview over the
proof. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMulTorsionFree (FreeGroup α)
  body: by
    classical
    let f (a : FreeGroup α) (n : Nat) : Nat :=
        (conjugator a.toWord).length + (n * (reduceCyclically a.toWord).length +
          (conjugator a.toWord).length)
    let g (a : FreeGroup α) (k : Nat) : List (α × Bool) :=
        conjugator a.toWord ++ ((replicate k (reduceCycl

中文:
实例 :
  签名: 是MulTorsionFree (自由群 α)
  定义体: by
    classical
    let f (a : FreeGroup α) (n : Nat) : Nat :=
        (conjugator a.toWord).length + (n * (reduceCyclically a.toWord).length +
          (conjugator a.toWord).length)
    let g (a : FreeGroup α) (k : Nat) : List (α × Bool) :=
        conjugator a.toWord ++ ((replicate k (reduceCycl

Depends on / 依赖: FreeGroup, a.toWord, classical, conjugator, flatten, invRev, isReduced_toWord, length, mul_comm, pow_mul, reduceCyclically, reduce_flatten_replicate, replace, replicate, simp_rw, toWord, toWord_pow
-/
instance : IsMulTorsionFree (FreeGroup α) where
  pow_left_injective n hn x y heq := by
    classical
    let f (a : FreeGroup α) (n : Nat) : Nat :=
        (conjugator a.toWord).length + (n * (reduceCyclically a.toWord).length +
          (conjugator a.toWord).length)
    let g (a : FreeGroup α) (k : Nat) : List (α × Bool) :=
        conjugator a.toWord ++ ((replicate k (reduceCyclically a.toWord)).flatten ++
          invRev (conjugator a.toWord))
    have heq₂ : x ^ (2 * n) = y ^ (2 * n) := by simp_rw [mul_comm, pow_mul, heq]
    replace heq : g x n = g y n := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq
    replace heq₂ : g x (2 * n) = g y (2 * n) := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq₂
    have leq : f x n = f y n := by simpa [g] using congr_arg List.length heq
    have leq₂ : f x (2 * n) = f y (2 * n) := by simpa [g] using congr_arg List.length heq₂
    obtain ⟨hc, heq'⟩ := List.append_inj heq (by grind)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    have hm : reduceCyclically x.toWord = reduceCyclically y.toWord := by
      simp only [replicate_succ, flatten_cons, append_assoc] at heq'
      exact (List.append_inj heq' <| mul_left_cancel₀ hn <| by grind).1
have := congr_arg mk (conj_conjugator_reduceCyclically x.toWord).symm
    rwa [hc, hm, conj_conjugator_reduceCyclically, mk_toWord, mk_toWord] at this

end IsMulTorsionFree
end FreeGroup
