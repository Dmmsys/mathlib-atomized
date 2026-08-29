/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
module

public import Mathlib.Data.List.Induction

/-!
# Palindromes

This module defines *palindromes*, lists which are equal to their reverse.

The main result is the `Palindrome` inductive type, and its associated `Palindrome.rec` induction
principle. Also provided are conversions to and from other equivalent definitions.

## References

* [Pierre Castéran, *On palindromes*][casteran]

[casteran]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html

## Tags

palindrome, reverse, induction
-/

public section


variable {α β : Type*}

namespace List

/--
Inductive type `Palindrome` / 归纳类型 `Palindrome`

English:
inductive Palindrome
  parameters: : List α -> Prop
  constructors (3):
    - nil: Palindrome []
    - singleton: forall x, Palindrome [x]
    - cons_concat: forall (x) {l}, Palindrome l -> Palindrome (x :: (l ++ [x]))

中文:
归纳类型 Palindrome
  参数: : 列表 α -> 命题
  构造子 (3 个):
    - nil: Palindrome []
    - singleton: 对任意 x, Palindrome [x]
    - cons_concat: 对任意 (x) {l}, Palindrome l -> Palindrome (x :: (l ++ [x]))
-/
inductive Palindrome : List α -> Prop
  | nil : Palindrome []
  | singleton : forall x, Palindrome [x]
  | cons_concat : forall (x) {l}, Palindrome l -> Palindrome (x :: (l ++ [x]))

namespace Palindrome

variable {l : List α}

/--
theorem `reverse_eq` / 定理 `reverse_eq`

English:
theorem reverse_eq
  given: {l : List α} (p : Palindrome l)
  statement: reverse l = l
  proof: by
  induction p <;> try (exact rfl)
  simpa

中文:
定理 reverse_eq
  条件: {l : 列表 α} (p : Palindrome l)
  结论: reverse l = l
  证明: by
  induction p <;> try (exact rfl)
  simpa
-/
theorem reverse_eq {l : List α} (p : Palindrome l) : reverse l = l := by
  induction p <;> try (exact rfl)
  simpa

/--
theorem `of_reverse_eq` / 定理 `of_reverse_eq`

English:
theorem of_reverse_eq
  given: {l : List α}
  statement: reverse l = l -> Palindrome l
  proof: by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons]; rw [reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat 

中文:
定理 of_reverse_eq
  条件: {l : 列表 α}
  结论: reverse l = l -> Palindrome l
  证明: by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons]; rw [reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat 

Depends on / 依赖: Palindrome, Palindrome.cons_concat, Palindrome.nil, Palindrome.singleton, append_inj_left, bidirectionalRecOn, cons_concat, head_eq_of_cons_eq, reverse_append, reverse_cons, singleton, tail_eq_of_cons_eq
-/
theorem of_reverse_eq {l : List α} : reverse l = l -> Palindrome l := by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons]; rw [reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat x this

/--
theorem `iff_reverse_eq` / 定理 `iff_reverse_eq`

English:
theorem iff_reverse_eq
  given: {l : List α}
  statement: Palindrome l ↔ reverse l = l
  proof: Iff.intro reverse_eq of_reverse_eq

中文:
定理 iff_reverse_eq
  条件: {l : 列表 α}
  结论: Palindrome l ↔ reverse l = l
  证明: Iff.intro reverse_eq of_reverse_eq

Depends on / 依赖: Iff.intro, of_reverse_eq, reverse_eq
-/
theorem iff_reverse_eq {l : List α} : Palindrome l ↔ reverse l = l :=
  Iff.intro reverse_eq of_reverse_eq

/--
theorem `append_reverse` / 定理 `append_reverse`

English:
theorem append_reverse
  given: (l : List α)
  statement: Palindrome (l ++ reverse l)
  proof: by
  apply of_reverse_eq
  rw [reverse_append]; rw [reverse_reverse]

中文:
定理 append_reverse
  条件: (l : 列表 α)
  结论: Palindrome (l ++ reverse l)
  证明: by
  apply of_reverse_eq
  rw [reverse_append]; rw [reverse_reverse]

Depends on / 依赖: of_reverse_eq, reverse_append, reverse_reverse
-/
theorem append_reverse (l : List α) : Palindrome (l ++ reverse l) := by
  apply of_reverse_eq
  rw [reverse_append]; rw [reverse_reverse]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (f : α -> β) (p : Palindrome l)
  statement: Palindrome (map f l)
  proof: of_reverse_eq by rw [← map_reverse, p.reverse_eq]

中文:
定理 map
  条件: (f : α -> β) (p : Palindrome l)
  结论: Palindrome (map f l)
  证明: of_reverse_eq by rw [← map_reverse, p.reverse_eq]
-/
protected theorem map (f : α -> β) (p : Palindrome l) : Palindrome (map f l) :=
of_reverse_eq by rw [← map_reverse, p.reverse_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (l
  body: decidable_of_iff' _ iff_reverse_eq

中文:
实例 [DecidableEq
  签名: α] (l
  定义体: decidable_of_iff' _ iff_reverse_eq

Depends on / 依赖: decidable_of_iff, iff_reverse_eq
-/
instance [DecidableEq α] (l : List α) : Decidable (Palindrome l) :=
  decidable_of_iff' _ iff_reverse_eq

end Palindrome

end List
