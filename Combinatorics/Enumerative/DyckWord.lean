/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

import Batteries.Data.List.Count
import Mathlib.Tactic.Positivity.Finset

/-!
# Dyck words

A Dyck word is a sequence consisting of an equal number `n` of symbols of two types such that
for all prefixes one symbol occurs at least as many times as the other.
If the symbols are `(` and `)` the latter restriction is equivalent to balanced brackets;
if they are `U = (1, 1)` and `D = (1, -1)` the sequence is a lattice path from `(0, 0)` to `(0, 2n)`
and the restriction requires the path to never go below the x-axis.

This file defines Dyck words and constructs their bijection with rooted binary trees,
one consequence being that the number of Dyck words with length `2 * n` is `catalan n`.

## Main definitions

* `DyckWord`: a list of `U`s and `D`s with as many `U`s as `D`s and with every prefix having
  at least as many `U`s as `D`s.
* `DyckWord.semilength`: semilength (half the length) of a Dyck word.
* `DyckWord.firstReturn`: for a nonempty word, the index of the `D` matching the initial `U`.

## Main results

* `DyckWord.equivTree`: equivalence between Dyck words and rooted binary trees.
  See the docstrings of `DyckWord.toTree` and `DyckWord.ofTree` for details.
* `DyckWord.equivTreesOfNumNodesEq`: equivalence between Dyck words of length `2 * n` and
  rooted binary trees with `n` internal nodes.
* `DyckWord.card_dyckWord_semilength_eq_catalan`:
  there are `catalan n` Dyck words of length `2 * n` or semilength `n`.

## Implementation notes

While any two-valued type could have been used for `DyckStep`, a new enumerated type is used here
to emphasise that the definition of a Dyck word does not depend on that underlying type.
-/

@[expose] public section

open List

/--
Inductive type `DyckStep` / 归纳类型 `DyckStep`

English:
inductive DyckStep
  constructors (2):
    - U: DyckStep
    - D: DyckStep

中文:
归纳类型 DyckStep
  构造子 (2 个):
    - U: DyckStep
    - D: DyckStep
-/
inductive DyckStep
  | U : DyckStep
  | D : DyckStep
  deriving Inhabited, DecidableEq

/--
lemma `DyckStep.dichotomy` / 引理 `DyckStep.dichotomy`

English:
lemma DyckStep.dichotomy
  given: (s : DyckStep)
  statement: s = U ∨ s = D
  proof: by cases s <;> tauto

中文:
引理 DyckStep.dichotomy
  条件: (s : DyckStep)
  结论: s = U ∨ s = D
  证明: by cases s <;> tauto
-/
lemma DyckStep.dichotomy (s : DyckStep) : s = U ∨ s = D := by cases s <;> tauto

open DyckStep

/-- A Dyck word is a list of `DyckStep`s with as many `U`s as `D`s and with every prefix having
at least as many `U`s as `D`s. -/
@[ext]
/--
Definition of `DyckWord` / `DyckWord` 的定义

English:
structure DyckWord
  parameters: where
  axioms and operations (3):
    - toList : List DyckStep
    - count_U_eq_count_D : toList.count U = toList.count D
    - count_D_le_count_U(i) : (toList.take i).count D <= (toList.take i).count U

中文:
结构 DyckWord
  参数: where
  公理与运算 (3 个):
    - toList : List DyckStep
    - count_U_eq_count_D : toList.count U = toList.count D
    - count_D_le_count_U(i) : (toList.take i).count D <= (toList.take i).count U
-/
structure DyckWord where
  /-- The underlying list -/
  toList : List DyckStep
  /-- There are as many `U`s as `D`s -/
  count_U_eq_count_D : toList.count U = toList.count D
  /-- Each prefix has at least as many `U`s as `D`s -/
  count_D_le_count_U i : (toList.take i).count D <= (toList.take i).count U
  deriving DecidableEq

attribute [coe] DyckWord.toList
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe DyckWord (List DyckStep)
  body: ⟨DyckWord.toList⟩

中文:
实例 :
  签名: Coe DyckWord (List DyckStep)
  定义体: ⟨DyckWord.toList⟩

Depends on / 依赖: DyckWord, DyckWord.toList, toList
-/
instance : Coe DyckWord (List DyckStep) := ⟨DyckWord.toList⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add DyckWord
  body: ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append, count_append]
    exact fun _ => add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩

中文:
实例 :
  签名: Add DyckWord
  定义体: ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append, count_append]
    exact fun _ => add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩

Depends on / 依赖: add_le_add, count_D_le_count_U, count_U_eq_count_D, count_append, p.count_D_le_count_U, p.count_U_eq_count_D, q.count_D_le_count_U, q.count_U_eq_count_D, take_append
-/
instance : Add DyckWord where
  add p q := ⟨p ++ q, by
    simp only [count_append, p.count_U_eq_count_D, q.count_U_eq_count_D], by
    simp only [take_append, count_append]
    exact fun _ => add_le_add (p.count_D_le_count_U _) (q.count_D_le_count_U _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero DyckWord
  body: ⟨[], by simp, by simp⟩

中文:
实例 :
  签名: Zero DyckWord
  定义体: ⟨[], by simp, by simp⟩
-/
instance : Zero DyckWord := ⟨[], by simp, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCancelMonoid DyckWord
  body: by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec
  add_left_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_left h
  add_right_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_right 

中文:
实例 :
  签名: AddCancelMonoid DyckWord
  定义体: by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec
  add_left_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_left h
  add_right_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_right 

Depends on / 依赖: DyckWord, DyckWord.ext_iff, add_assoc, add_left_cancel, add_right_cancel, append_assoc, append_cancel_left, append_cancel_right, append_nil, ext_iff, nsmulRec, zero_add
-/
instance : AddCancelMonoid DyckWord where
  add_zero p := by ext1; exact append_nil _
  zero_add p := by ext1; rfl
  add_assoc p q r := by ext1; apply append_assoc
  nsmul := nsmulRec
  add_left_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_left h
  add_right_cancel p q r h := by rw [DyckWord.ext_iff] at *; exact append_cancel_right h

namespace DyckWord

variable {p q : DyckWord}

/--
lemma `toList_eq_nil` / 引理 `toList_eq_nil`

English:
lemma toList_eq_nil
  statement: p.toList = [] ↔ p = 0
  proof: by rw [DyckWord.ext_iff]; rfl

中文:
引理 toList_eq_nil
  结论: p.toList = [] ↔ p = 0
  证明: by rw [DyckWord.ext_iff]; rfl

Depends on / 依赖: DyckWord, DyckWord.ext_iff, ext_iff
-/
lemma toList_eq_nil : p.toList = [] ↔ p = 0 := by rw [DyckWord.ext_iff]; rfl
/--
lemma `toList_ne_nil` / 引理 `toList_ne_nil`

English:
lemma toList_ne_nil
  statement: p.toList != [] ↔ p != 0
  proof: toList_eq_nil.ne

中文:
引理 toList_ne_nil
  结论: p.toList != [] ↔ p != 0
  证明: toList_eq_nil.ne

Depends on / 依赖: toList_eq_nil, toList_eq_nil.ne
-/
lemma toList_ne_nil : p.toList != [] ↔ p != 0 := toList_eq_nil.ne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (AddUnits DyckWord)
  body: by
    obtain ⟨a, b, h, -⟩ := p
    obtain ⟨ha, hb⟩ := append_eq_nil_iff.mp (toList_eq_nil.mpr h)
    congr
    · exact toList_eq_nil.mp ha
    · exact toList_eq_nil.mp hb

中文:
实例 :
  签名: Unique (AddUnits DyckWord)
  定义体: by
    obtain ⟨a, b, h, -⟩ := p
    obtain ⟨ha, hb⟩ := append_eq_nil_iff.mp (toList_eq_nil.mpr h)
    congr
    · exact toList_eq_nil.mp ha
    · exact toList_eq_nil.mp hb

Depends on / 依赖: append_eq_nil_iff, append_eq_nil_iff.mp, toList_eq_nil, toList_eq_nil.mp, toList_eq_nil.mpr
-/
instance : Unique (AddUnits DyckWord) where
  uniq p := by
    obtain ⟨a, b, h, -⟩ := p
    obtain ⟨ha, hb⟩ := append_eq_nil_iff.mp (toList_eq_nil.mpr h)
    congr
    · exact toList_eq_nil.mp ha
    · exact toList_eq_nil.mp hb

variable (h : p != 0)

/--
lemma `head_eq_U` / 引理 `head_eq_U`

English:
lemma head_eq_U
  given: (p : DyckWord) (h)
  statement: p.toList.head h = U
  proof: by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

中文:
引理 head_eq_U
  条件: (p : DyckWord) (h)
  结论: p.toList.head h = U
  证明: by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

Depends on / 依赖: dichotomy, head_cons, nonneg, rename_i, resolve_left, s.dichotomy.resolve_left
-/
lemma head_eq_U (p : DyckWord) (h) : p.toList.head h = U := by
  rcases p with - | s; · tauto
  rw [head_cons]
  by_contra f
  rename_i _ nonneg
  simpa [s.dichotomy.resolve_left f] using nonneg 1

/--
lemma `getLast_eq_D` / 引理 `getLast_eq_D`

English:
lemma getLast_eq_D
  given: (p : DyckWord) (h)
  statement: p.toList.getLast h = D
  proof: by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h]; rw [(dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, reduceCtorEq, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); lia

include h in

中文:
引理 getLast_eq_D
  条件: (p : DyckWord) (h)
  结论: p.toList.getLast h = D
  证明: by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h]; rw [(dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, reduceCtorEq, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); lia

include h in

Depends on / 依赖: count_D_le_count_U, count_U_eq_count_D, count_append, count_singleton, dichotomy, dropLast_append_getLast, dropLast_eq_take, ite_false, ite_true, length, p.count_D_le_count_U, p.count_U_eq_count_D, p.toList.length, reduceCtorEq, resolve_right, simp_rw, toList
-/
lemma getLast_eq_D (p : DyckWord) (h) : p.toList.getLast h = D := by
  by_contra f; have s := p.count_U_eq_count_D
  rw [← dropLast_append_getLast h]; rw [(dichotomy _).resolve_right f] at s
  simp_rw [dropLast_eq_take, count_append, count_singleton', ite_true, reduceCtorEq, ite_false] at s
  have := p.count_D_le_count_U (p.toList.length - 1); lia

include h in
/--
lemma `cons_tail_dropLast_concat` / 引理 `cons_tail_dropLast_concat`

English:
lemma cons_tail_dropLast_concat
  statement: U :: p.toList.dropLast.tail ++ [D] = p
  proof: by
  have h' := toList_ne_nil.mpr h
  have : p.toList.dropLast.take 1 = [p.toList.head h'] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h', ← p.toList.dropLast.take_append_drop 

中文:
引理 cons_tail_dropLast_concat
  结论: U :: p.toList.dropLast.tail ++ [D] = p
  证明: by
  have h' := toList_ne_nil.mpr h
  have : p.toList.dropLast.take 1 = [p.toList.head h'] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h', ← p.toList.dropLast.take_append_drop 

Depends on / 依赖: dropLast, dropLast_append_getLast, drop_one, getLast_eq_D, head_eq_U, nth_rw, p.toList.dropLast.take, p.toList.dropLast.take_append_drop, p.toList.dropLast_append_getLast, p.toList.head, rename_i, take_append_drop, toList, toList_ne_nil, toList_ne_nil.mpr
-/
lemma cons_tail_dropLast_concat : U :: p.toList.dropLast.tail ++ [D] = p := by
  have h' := toList_ne_nil.mpr h
  have : p.toList.dropLast.take 1 = [p.toList.head h'] := by
    rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
    · tauto
    · rename_i bal _
      cases s <;> simp at bal
    · tauto
  nth_rw 2 [← p.toList.dropLast_append_getLast h', ← p.toList.dropLast.take_append_drop 1]
  rw [getLast_eq_D]; rw [drop_one]; rw [this]; rw [head_eq_U]
  rfl

variable (p) in
/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D)
  body: p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

中文:
定义 take
  签名: (i : 自然数) (hi : (p.toList.take i).count U = (p.toList.take i).count D)
  定义体: p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

Depends on / 依赖: p.toList.take, toList
-/
def take (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.take i
  count_U_eq_count_D := hi
  count_D_le_count_U k := by rw [take_take]; exact p.count_D_le_count_U (min k i)

variable (p) in
/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D)
  body: p.toList.drop i
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← take_append_drop i p.toList]; rw [count_append]; rw [count_append] at this
    lia
  count_D_le_count_U k := by
    rw [show i = min i (i + k) by omega]; rw [← take_take] at hi
    rw [take_drop]; rw [← add_le_add_

中文:
定义 drop
  签名: (i : 自然数) (hi : (p.toList.take i).count U = (p.toList.take i).count D)
  定义体: p.toList.drop i
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← take_append_drop i p.toList]; rw [count_append]; rw [count_append] at this
    lia
  count_D_le_count_U k := by
    rw [show i = min i (i + k) by omega]; rw [← take_take] at hi
    rw [take_drop]; rw [← add_le_add_

Depends on / 依赖: p.toList.drop, toList
-/
def drop (i : Nat) (hi : (p.toList.take i).count U = (p.toList.take i).count D) : DyckWord where
  toList := p.toList.drop i
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← take_append_drop i p.toList]; rw [count_append]; rw [count_append] at this
    lia
  count_D_le_count_U k := by
    rw [show i = min i (i + k) by omega]; rw [← take_take] at hi
    rw [take_drop]; rw [← add_le_add_iff_left (((p.toList.take (i + k)).take i).count U)]; rw [← count_append]; rw [hi]; rw [← count_append]; rw [take_append_drop]
    exact p.count_D_le_count_U _

variable (p) in
/--
Definition of `nest` / `nest` 的定义

English:
definition nest
  signature: : DyckWord where
  body: [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append, count_append]
    rw [← add_rotate (count D _)]; rw [← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · s

中文:
定义 nest
  签名: : DyckWord where
  定义体: [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append, count_append]
    rw [← add_rotate (count D _)]; rw [← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · s
-/
def nest : DyckWord where
  toList := [U] ++ p ++ [D]
  count_U_eq_count_D := by simp [p.count_U_eq_count_D]
  count_D_le_count_U i := by
    simp only [take_append, count_append]
    rw [← add_rotate (count D _)]; rw [← add_rotate (count U _)]
    apply add_le_add _ (p.count_D_le_count_U _)
    rcases i.eq_zero_or_pos with hi | hi; · simp [hi]
    rw [take_of_length_le (show [U].length <= i by rwa [length_singleton]), count_singleton']
    simp only [reduceCtorEq, ite_false]
    rw [add_comm]
    exact add_le_add zero_le (count_le_length.trans (by simp))

/--
lemma `nest_ne_zero` / 引理 `nest_ne_zero`

English:
lemma nest_ne_zero
  statement: p.nest != 0
  proof: by simp [← toList_ne_nil, nest]

中文:
引理 nest_ne_zero
  结论: p.nest != 0
  证明: by simp [← toList_ne_nil, nest]
-/
@[simp] lemma nest_ne_zero : p.nest != 0 := by simp [← toList_ne_nil, nest]

variable (p) in
/--
Definition of `IsNested` / `IsNested` 的定义

English:
definition IsNested
  signature: : Prop
  body: p != 0 ∧ forall ⦃i⦄, 0 < i -> i < p.toList.length -> (p.toList.take i).count D < (p.toList.take i).count U

中文:
定义 IsNested
  签名: : 命题
  定义体: p != 0 ∧ forall ⦃i⦄, 0 < i -> i < p.toList.length -> (p.toList.take i).count D < (p.toList.take i).count U

Depends on / 依赖: length, p.toList.length, p.toList.take, toList
-/
def IsNested : Prop :=
  p != 0 ∧ forall ⦃i⦄, 0 < i -> i < p.toList.length -> (p.toList.take i).count D < (p.toList.take i).count U

/--
lemma `IsNested.nest` / 引理 `IsNested.nest`

English:
lemma IsNested.nest
  statement: p.nest.IsNested
  proof: ⟨nest_ne_zero, fun i lb ub => by
  simp_rw [nest, length_append, length_singleton] at ub ⊢
  rw [take_append_of_le_length (by rw [singleton_append]; rw [length_cons]; lia),
    take_append, take_of_length_le (by rw [length_singleton]; lia),
    length_singleton, singleton_append, count_cons_of_ne (b

中文:
引理 IsNested.nest
  结论: p.nest.IsNested
  证明: ⟨nest_ne_zero, fun i lb ub => by
  simp_rw [nest, length_append, length_singleton] at ub ⊢
  rw [take_append_of_le_length (by rw [singleton_append]; rw [length_cons]; lia),
    take_append, take_of_length_le (by rw [length_singleton]; lia),
    length_singleton, singleton_append, count_cons_of_ne (b
-/
protected lemma IsNested.nest : p.nest.IsNested := ⟨nest_ne_zero, fun i lb ub => by
  simp_rw [nest, length_append, length_singleton] at ub ⊢
  rw [take_append_of_le_length (by rw [singleton_append]; rw [length_cons]; lia),
    take_append, take_of_length_le (by rw [length_singleton]; lia),
    length_singleton, singleton_append, count_cons_of_ne (by simp), count_cons_self,
    Nat.lt_add_one_iff]
  exact p.count_D_le_count_U _⟩

variable (p) in
/--
Definition of `denest` / `denest` 的定义

English:
definition denest
  signature: (hn : p.IsNested)
  body: p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat hn.1]; rw [count_append]; rw [count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    replace h := toList_ne_nil.mpr hn.1
    have l1 : p.toList.take 1 = [p.toList

中文:
定义 denest
  签名: (hn : p.IsNested)
  定义体: p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat hn.1]; rw [count_append]; rw [count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    replace h := toList_ne_nil.mpr hn.1
    have l1 : p.toList.take 1 = [p.toList

Depends on / 依赖: dropLast, p.toList.dropLast.tail, toList
-/
def denest (hn : p.IsNested) : DyckWord where
  toList := p.toList.dropLast.tail
  count_U_eq_count_D := by
    have := p.count_U_eq_count_D
    rw [← cons_tail_dropLast_concat hn.1]; rw [count_append]; rw [count_cons] at this
    simpa using this
  count_D_le_count_U i := by
    replace h := toList_ne_nil.mpr hn.1
    have l1 : p.toList.take 1 = [p.toList.head h] := by rcases p with - | - <;> tauto
    have l3 : p.toList.length - 1 = p.toList.length - 1 - 1 + 1 := by
      rcases p with - | ⟨s, ⟨- | ⟨t, r⟩⟩⟩
      · tauto
      · rename_i bal _
        cases s <;> simp at bal
      · tauto
    rw [← drop_one]; rw [take_drop]; rw [dropLast_eq_take]; rw [take_take]
    have ub : min (1 + i) (p.toList.length - 1) < p.toList.length :=
      (min_le_right _ p.toList.length.pred).trans_lt (Nat.pred_lt ((length_pos_iff.mpr h).ne'))
    have lb : 0 < min (1 + i) (p.toList.length - 1) := by omega
    have eq := hn.2 lb ub
    set j := min (1 + i) (p.toList.length - 1)
    rw [← (p.toList.take j).take_append_drop 1]; rw [count_append]; rw [count_append]; rw [take_take]; rw [min_eq_left (by lia)]; rw [l1]; rw [head_eq_U] at eq
    simp only [count_singleton', ite_true] at eq
    lia

variable (p) in
/--
lemma `nest_denest` / 引理 `nest_denest`

English:
lemma nest_denest
  given: (hn)
  statement: (p.denest hn).nest = p
  proof: by
  simpa [DyckWord.ext_iff] using! p.cons_tail_dropLast_concat hn.1

中文:
引理 nest_denest
  条件: (hn)
  结论: (p.denest hn).nest = p
  证明: by
  simpa [DyckWord.ext_iff] using! p.cons_tail_dropLast_concat hn.1

Depends on / 依赖: DyckWord, DyckWord.ext_iff, cons_tail_dropLast_concat, ext_iff, p.cons_tail_dropLast_concat
-/
lemma nest_denest (hn) : (p.denest hn).nest = p := by
  simpa [DyckWord.ext_iff] using! p.cons_tail_dropLast_concat hn.1

variable (p) in
/--
lemma `denest_nest` / 引理 `denest_nest`

English:
lemma denest_nest
  statement: p.nest.denest .nest = p
  proof: by
  simp_rw [nest, denest, DyckWord.ext_iff, dropLast_concat]; rfl

中文:
引理 denest_nest
  结论: p.nest.denest .nest = p
  证明: by
  simp_rw [nest, denest, DyckWord.ext_iff, dropLast_concat]; rfl

Depends on / 依赖: DyckWord, DyckWord.ext_iff, denest, dropLast_concat, ext_iff, simp_rw
-/
lemma denest_nest : p.nest.denest .nest = p := by
  simp_rw [nest, denest, DyckWord.ext_iff, dropLast_concat]; rfl

section Semilength

variable (p) in
/--
Definition of `semilength` / `semilength` 的定义

English:
definition semilength
  signature: : Nat
  body: p.toList.count U

中文:
定义 semilength
  签名: : 自然数
  定义体: p.toList.count U

Depends on / 依赖: p.toList.count, toList
-/
def semilength : Nat := p.toList.count U

/--
lemma `semilength_zero` / 引理 `semilength_zero`

English:
lemma semilength_zero
  statement: semilength 0 = 0
  proof: rfl

中文:
引理 semilength_zero
  结论: semilength 0 = 0
  证明: rfl
-/
@[simp] lemma semilength_zero : semilength 0 = 0 := rfl
/--
lemma `semilength_add` / 引理 `semilength_add`

English:
lemma semilength_add
  statement: (p + q).semilength = p.semilength + q.semilength
  proof: count_append ..

中文:
引理 semilength_add
  结论: (p + q).semilength = p.semilength + q.semilength
  证明: count_append ..
-/
@[simp] lemma semilength_add : (p + q).semilength = p.semilength + q.semilength := count_append ..
/--
lemma `semilength_nest` / 引理 `semilength_nest`

English:
lemma semilength_nest
  statement: p.nest.semilength = p.semilength + 1
  proof: by simp [semilength, nest]

中文:
引理 semilength_nest
  结论: p.nest.semilength = p.semilength + 1
  证明: by simp [semilength, nest]
-/
@[simp] lemma semilength_nest : p.nest.semilength = p.semilength + 1 := by simp [semilength, nest]

/--
lemma `semilength_eq_count_D` / 引理 `semilength_eq_count_D`

English:
lemma semilength_eq_count_D
  statement: p.semilength = p.toList.count D
  proof: by
  rw [← count_U_eq_count_D]; rfl

@[simp]

中文:
引理 semilength_eq_count_D
  结论: p.semilength = p.toList.count D
  证明: by
  rw [← count_U_eq_count_D]; rfl

@[simp]

Depends on / 依赖: count_U_eq_count_D
-/
lemma semilength_eq_count_D : p.semilength = p.toList.count D := by
  rw [← count_U_eq_count_D]; rfl

@[simp]
/--
lemma `two_mul_semilength_eq_length` / 引理 `two_mul_semilength_eq_length`

English:
lemma two_mul_semilength_eq_length
  statement: 2 * p.semilength = p.toList.length
  proof: by
  nth_rw 1 [two_mul, semilength, p.count_U_eq_count_D, semilength]
  convert! (p.toList.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases s <;> tauto

中文:
引理 two_mul_semilength_eq_length
  结论: 2 * p.semilength = p.toList.length
  证明: by
  nth_rw 1 [two_mul, semilength, p.count_U_eq_count_D, semilength]
  convert! (p.toList.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases s <;> tauto

Depends on / 依赖: convert, count_U_eq_count_D, length_eq_countP_add_countP, nth_rw, p.count_U_eq_count_D, p.toList.length_eq_countP_add_countP, rename_i, semilength, toList, two_mul
-/
lemma two_mul_semilength_eq_length : 2 * p.semilength = p.toList.length := by
  nth_rw 1 [two_mul, semilength, p.count_U_eq_count_D, semilength]
  convert! (p.toList.length_eq_countP_add_countP (· == D)).symm
  rw [count]; congr!; rename_i s; cases s <;> tauto

end Semilength

section FirstReturn

variable (p) in
/--
Definition of `firstReturn` / `firstReturn` 的定义

English:
definition firstReturn
  signature: : Nat
  body: (range p.toList.length).findIdx fun i =>
    (p.toList.take (i + 1)).count U = (p.toList.take (i + 1)).count D

中文:
定义 firstReturn
  签名: : 自然数
  定义体: (range p.toList.length).findIdx fun i =>
    (p.toList.take (i + 1)).count U = (p.toList.take (i + 1)).count D

Depends on / 依赖: findIdx, length, p.toList.length, p.toList.take, toList
-/
def firstReturn : Nat :=
  (range p.toList.length).findIdx fun i =>
    (p.toList.take (i + 1)).count U = (p.toList.take (i + 1)).count D

/--
lemma `firstReturn_zero` / 引理 `firstReturn_zero`

English:
lemma firstReturn_zero
  statement: firstReturn 0 = 0
  proof: rfl

include h in

中文:
引理 firstReturn_zero
  结论: firstReturn 0 = 0
  证明: rfl

include h in
-/
@[simp] lemma firstReturn_zero : firstReturn 0 = 0 := rfl

include h in
/--
lemma `firstReturn_pos` / 引理 `firstReturn_pos`

English:
lemma firstReturn_pos
  statement: 0 < p.firstReturn
  proof: by
  rw [← not_le]; rw [Nat.le_zero]; rw [firstReturn]; rw [findIdx_eq]; rw [getElem_range]
  · rw! [← p.cons_tail_dropLast_concat h]
    simp
  · rw [length_range, length_pos_iff]
    exact toList_ne_nil.mpr h

include h in

中文:
引理 firstReturn_pos
  结论: 0 < p.firstReturn
  证明: by
  rw [← not_le]; rw [Nat.le_zero]; rw [firstReturn]; rw [findIdx_eq]; rw [getElem_range]
  · rw! [← p.cons_tail_dropLast_concat h]
    simp
  · rw [length_range, length_pos_iff]
    exact toList_ne_nil.mpr h

include h in

Depends on / 依赖: Nat.le_zero, cons_tail_dropLast_concat, findIdx_eq, firstReturn, getElem_range, le_zero, length_pos_iff, length_range, not_le, p.cons_tail_dropLast_concat, toList_ne_nil, toList_ne_nil.mpr
-/
lemma firstReturn_pos : 0 < p.firstReturn := by
  rw [← not_le]; rw [Nat.le_zero]; rw [firstReturn]; rw [findIdx_eq]; rw [getElem_range]
  · rw! [← p.cons_tail_dropLast_concat h]
    simp
  · rw [length_range, length_pos_iff]
    exact toList_ne_nil.mpr h

include h in
/--
lemma `firstReturn_lt_length` / 引理 `firstReturn_lt_length`

English:
lemma firstReturn_lt_length
  statement: p.firstReturn < p.toList.length
  proof: by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range (n := p.toList.length)]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by lia, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U

中文:
引理 firstReturn_lt_length
  结论: p.firstReturn < p.toList.length
  证明: by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range (n := p.toList.length)]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by lia, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U

Depends on / 依赖: Nat.sub_add_cancel, count_U_eq_count_D, decide_eq_true_eq, findIdx_lt_length_of_exists, le_refl, length, length_pos_of_ne_nil, length_range, mem_range, p.count_U_eq_count_D, p.toList.length, sub_add_cancel, take_of_length_le, toList, toList_ne_nil, toList_ne_nil.mpr
-/
lemma firstReturn_lt_length : p.firstReturn < p.toList.length := by
  have lp := length_pos_of_ne_nil (toList_ne_nil.mpr h)
  rw [← length_range (n := p.toList.length)]
  apply findIdx_lt_length_of_exists
  simp only [mem_range, decide_eq_true_eq]
  use p.toList.length - 1
  exact ⟨by lia, by rw [Nat.sub_add_cancel lp, take_of_length_le (le_refl _),
    p.count_U_eq_count_D]⟩

set_option backward.isDefEq.respectTransparency false in
include h in
/--
lemma `count_take_firstReturn_add_one` / 引理 `count_take_firstReturn_add_one`

English:
lemma count_take_firstReturn_add_one
  proof: by
  have := findIdx_getElem
    (w := (length_range (n := p.toList.length)).symm ▸ firstReturn_lt_length h)
  simpa using! this

中文:
引理 count_take_firstReturn_add_one
  证明: by
  have := findIdx_getElem
    (w := (length_range (n := p.toList.length)).symm ▸ firstReturn_lt_length h)
  simpa using! this

Depends on / 依赖: findIdx_getElem, firstReturn_lt_length, length, length_range, p.toList.length, toList
-/
lemma count_take_firstReturn_add_one :
    (p.toList.take (p.firstReturn + 1)).count U = (p.toList.take (p.firstReturn + 1)).count D := by
  have := findIdx_getElem
    (w := (length_range (n := p.toList.length)).symm ▸ firstReturn_lt_length h)
  simpa using! this

/--
lemma `count_D_lt_count_U_of_lt_firstReturn` / 引理 `count_D_lt_count_U_of_lt_firstReturn`

English:
lemma count_D_lt_count_U_of_lt_firstReturn
  given: {i : Nat} (hi : i < p.firstReturn)
  proof: by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_false_iff_not]; rw [← ne_eq]; rw [getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]

中文:
引理 count_D_lt_count_U_of_lt_firstReturn
  条件: {i : 自然数} (hi : i < p.firstReturn)
  证明: by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_false_iff_not]; rw [← ne_eq]; rw [getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]

Depends on / 依赖: count_D_le_count_U, decide_eq_false_iff_not, getElem_range, lt_of_le_of_ne, ne.symm, ne_eq, not_of_lt_findIdx, p.count_D_le_count_U
-/
lemma count_D_lt_count_U_of_lt_firstReturn {i : Nat} (hi : i < p.firstReturn) :
    (p.toList.take (i + 1)).count D < (p.toList.take (i + 1)).count U := by
  have ne := not_of_lt_findIdx hi
  rw [decide_eq_false_iff_not]; rw [← ne_eq]; rw [getElem_range] at ne
  exact lt_of_le_of_ne (p.count_D_le_count_U (i + 1)) ne.symm

@[simp]
/--
lemma `firstReturn_add` / 引理 `firstReturn_add`

English:
lemma firstReturn_add
  statement: (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn
  proof: by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append, show p.firstReturn + 1 - p.toList.length = 0 by

中文:
引理 firstReturn_add
  结论: (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn
  证明: by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append, show p.firstReturn + 1 - p.toList.length = 0 by

Depends on / 依赖: append_nil, count_D_lt_count_U_of_lt_firstRetur, count_take_firstReturn_add_one, decide_eq_true_eq, findIdx_eq, firstReturn, firstReturn_lt_length, getElem_range, length, p.firstReturn, p.toList, p.toList.length, q.toList, simp_rw, split_ifs, take_append, take_zero, toList
-/
lemma firstReturn_add : (p + q).firstReturn = if p = 0 then q.firstReturn else p.firstReturn := by
  split_ifs with h; · simp [h]
  have u : (p + q).toList = p.toList ++ q.toList := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    have v := firstReturn_lt_length h
    constructor
    · rw [take_append, show p.firstReturn + 1 - p.toList.length = 0 by lia,
        take_zero, append_nil, count_take_firstReturn_add_one h]
    · intro j hj
      rw [take_append]; rw [show j + 1 - p.toList.length = 0 by lia]; rw [take_zero]; rw [append_nil]
      simpa using (count_D_lt_count_U_of_lt_firstReturn hj).ne'
  · rw [length_range, u, length_append]
    exact Nat.lt_add_right _ (firstReturn_lt_length h)

@[simp]
/--
lemma `firstReturn_nest` / 引理 `firstReturn_nest`

English:
lemma firstReturn_nest
  statement: p.nest.firstReturn = p.toList.length + 1
  proof: by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_succ_cons, count_co

中文:
引理 firstReturn_nest
  结论: p.nest.firstReturn = p.toList.length + 1
  证明: by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_succ_cons, count_co

Depends on / 依赖: SecondCountableTopology, Subtype, TotallyDisconnectedSpace, add_zero, append_nil, beq_iff_eq, beq_self_eq_true, cons_append, count_D_le_count_U, count_U_eq_count_D, count_cons, decide_eq_false_iff_not, decide_eq_true_eq, findIdx_eq, firstReturn, getElem_range, ite_false, ite_true, length, ne_eq
-/
lemma firstReturn_nest : p.nest.firstReturn = p.toList.length + 1 := by
  have u : p.nest.toList = U :: p.toList ++ [D] := rfl
  rw [firstReturn]; rw [findIdx_eq]
  · simp_rw [u, decide_eq_true_eq, getElem_range]
    constructor
    · rw [take_of_length_le (by simp), ← u, p.nest.count_U_eq_count_D]
    · intro j hj
      simp_rw [cons_append, take_succ_cons, count_cons, beq_self_eq_true, ite_true,
        beq_iff_eq, reduceCtorEq, ite_false, take_append,
        show j - p.toList.length = 0 by lia, take_zero, append_nil]
      have := p.count_D_le_count_U j
      simp only [add_zero, decide_eq_false_iff_not, ne_eq]
      lia
  · simp_rw [length_range, u, length_append, length_cons]
    exact Nat.lt_add_one _

variable (p) in
/--
Definition of `insidePart` / `insidePart` 的定义

English:
definition insidePart
  signature: : DyckWord
  body: if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    ⟨by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h, fun i lb ub => by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take]; rw [min_eq_l

中文:
定义 insidePart
  签名: : DyckWord
  定义体: if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    ⟨by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h, fun i lb ub => by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take]; rw [min_eq_l

Depends on / 依赖: Nat.add_lt_add_iff_right, add_lt_add_iff_right, count_D_lt_count_U_of_lt_firstReturn, count_take_firstReturn_add_one, denest, firstReturn, length_take, lt_min_iff, min_eq_left, p.firstReturn, p.take, replace, take_take, toList_ne_nil, toList_ne_nil.mpr, ub.le
-/
def insidePart : DyckWord :=
  if h : p = 0 then 0 else
  (p.take (p.firstReturn + 1) (count_take_firstReturn_add_one h)).denest
    ⟨by rw [← toList_ne_nil, take]; simpa using toList_ne_nil.mpr h, fun i lb ub => by
      simp only [take, length_take, lt_min_iff] at ub ⊢
      replace ub := ub.1
      rw [take_take]; rw [min_eq_left ub.le]
      rw [show i = i - 1 + 1 by lia] at ub ⊢
      rw [Nat.add_lt_add_iff_right] at ub
      exact count_D_lt_count_U_of_lt_firstReturn ub⟩

variable (p) in
/--
Definition of `outsidePart` / `outsidePart` 的定义

English:
definition outsidePart
  signature: : DyckWord
  body: if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)

中文:
定义 outsidePart
  签名: : DyckWord
  定义体: if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)

Depends on / 依赖: count_take_firstReturn_add_one, firstReturn, p.drop, p.firstReturn
-/
def outsidePart : DyckWord :=
  if h : p = 0 then 0 else p.drop (p.firstReturn + 1) (count_take_firstReturn_add_one h)

/--
lemma `insidePart_zero` / 引理 `insidePart_zero`

English:
lemma insidePart_zero
  statement: insidePart 0 = 0
  proof: by simp [insidePart]

中文:
引理 insidePart_zero
  结论: insidePart 0 = 0
  证明: by simp [insidePart]
-/
@[simp] lemma insidePart_zero : insidePart 0 = 0 := by simp [insidePart]
/--
lemma `outsidePart_zero` / 引理 `outsidePart_zero`

English:
lemma outsidePart_zero
  statement: outsidePart 0 = 0
  proof: by simp [outsidePart]

include h in
@[simp]

中文:
引理 outsidePart_zero
  结论: outsidePart 0 = 0
  证明: by simp [outsidePart]

include h in
@[simp]
-/
@[simp] lemma outsidePart_zero : outsidePart 0 = 0 := by simp [outsidePart]

include h in
@[simp]
/--
lemma `insidePart_add` / 引理 `insidePart_add`

English:
lemma insidePart_add
  statement: (p + q).insidePart = p.insidePart
  proof: by
  simp_rw [insidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, take]
  congr 3
  exact take_append_of_le_length (firstReturn_lt_length h)

include h in
@[simp]

中文:
引理 insidePart_add
  结论: (p + q).insidePart = p.insidePart
  证明: by
  simp_rw [insidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, take]
  congr 3
  exact take_append_of_le_length (firstReturn_lt_length h)

include h in
@[simp]

Depends on / 依赖: DyckWord, DyckWord.ext_iff, add_eq_zero, dite_false, ext_iff, false_and, firstReturn_add, firstReturn_lt_length, insidePart, ite_false, simp_rw, take_append_of_le_length
-/
lemma insidePart_add : (p + q).insidePart = p.insidePart := by
  simp_rw [insidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, take]
  congr 3
  exact take_append_of_le_length (firstReturn_lt_length h)

include h in
@[simp]
/--
lemma `outsidePart_add` / 引理 `outsidePart_add`

English:
lemma outsidePart_add
  statement: (p + q).outsidePart = p.outsidePart + q
  proof: by
  simp_rw [outsidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, drop]
  exact drop_append_of_le_length (firstReturn_lt_length h)

@[simp]

中文:
引理 outsidePart_add
  结论: (p + q).outsidePart = p.outsidePart + q
  证明: by
  simp_rw [outsidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, drop]
  exact drop_append_of_le_length (firstReturn_lt_length h)

@[simp]

Depends on / 依赖: DyckWord, DyckWord.ext_iff, add_eq_zero, dite_false, drop_append_of_le_length, ext_iff, false_and, firstReturn_add, firstReturn_lt_length, ite_false, outsidePart, simp_rw
-/
lemma outsidePart_add : (p + q).outsidePart = p.outsidePart + q := by
  simp_rw [outsidePart, firstReturn_add, add_eq_zero', h, false_and, dite_false, ite_false,
    DyckWord.ext_iff, drop]
  exact drop_append_of_le_length (firstReturn_lt_length h)

@[simp]
/--
lemma `insidePart_nest` / 引理 `insidePart_nest`

English:
lemma insidePart_nest
  statement: p.nest.insidePart = p
  proof: by
  simp_rw [insidePart, nest_ne_zero, dite_false, firstReturn_nest]
  convert! p.denest_nest; rw [DyckWord.ext_iff]; apply take_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

@[simp]

中文:
引理 insidePart_nest
  结论: p.nest.insidePart = p
  证明: by
  simp_rw [insidePart, nest_ne_zero, dite_false, firstReturn_nest]
  convert! p.denest_nest; rw [DyckWord.ext_iff]; apply take_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

@[simp]

Depends on / 依赖: DyckWord, DyckWord.ext_iff, convert, denest_nest, dite_false, ext_iff, firstReturn_nest, insidePart, length_append, length_singleton, nest_ne_zero, p.denest_nest, simp_rw, take_of_length_le
-/
lemma insidePart_nest : p.nest.insidePart = p := by
  simp_rw [insidePart, nest_ne_zero, dite_false, firstReturn_nest]
  convert! p.denest_nest; rw [DyckWord.ext_iff]; apply take_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

@[simp]
/--
lemma `outsidePart_nest` / 引理 `outsidePart_nest`

English:
lemma outsidePart_nest
  statement: p.nest.outsidePart = 0
  proof: by
  simp_rw [outsidePart, nest_ne_zero, dite_false, firstReturn_nest]
  rw [DyckWord.ext_iff]; apply drop_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

中文:
引理 outsidePart_nest
  结论: p.nest.outsidePart = 0
  证明: by
  simp_rw [outsidePart, nest_ne_zero, dite_false, firstReturn_nest]
  rw [DyckWord.ext_iff]; apply drop_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

Depends on / 依赖: DyckWord, DyckWord.ext_iff, dite_false, drop_of_length_le, ext_iff, firstReturn_nest, length_append, length_singleton, nest_ne_zero, outsidePart, simp_rw
-/
lemma outsidePart_nest : p.nest.outsidePart = 0 := by
  simp_rw [outsidePart, nest_ne_zero, dite_false, firstReturn_nest]
  rw [DyckWord.ext_iff]; apply drop_of_length_le
  simp_rw [nest, length_append, length_singleton]; lia

set_option backward.isDefEq.respectTransparency false in
include h in
@[simp]
/--
theorem `nest_insidePart_add_outsidePart` / 定理 `nest_insidePart_add_outsidePart`

English:
theorem nest_insidePart_add_outsidePart
  statement: p.insidePart.nest + p.outsidePart = p
  proof: by
  simp_rw [insidePart, outsidePart, h, dite_false, nest_denest, DyckWord.ext_iff]
  apply take_append_drop

include h in

中文:
定理 nest_insidePart_add_outsidePart
  结论: p.insidePart.nest + p.outsidePart = p
  证明: by
  simp_rw [insidePart, outsidePart, h, dite_false, nest_denest, DyckWord.ext_iff]
  apply take_append_drop

include h in

Depends on / 依赖: DyckWord, DyckWord.ext_iff, dite_false, ext_iff, insidePart, nest_denest, outsidePart, simp_rw, take_append_drop
-/
theorem nest_insidePart_add_outsidePart : p.insidePart.nest + p.outsidePart = p := by
  simp_rw [insidePart, outsidePart, h, dite_false, nest_denest, DyckWord.ext_iff]
  apply take_append_drop

include h in
/--
lemma `semilength_insidePart_add_semilength_outsidePart_add_one` / 引理 `semilength_insidePart_add_semilength_outsidePart_add_one`

English:
lemma semilength_insidePart_add_semilength_outsidePart_add_one
  proof: by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h)]; rw [semilength_add]; rw [semilength_nest]; rw [add_right_comm]

include h in

中文:
引理 semilength_insidePart_add_semilength_outsidePart_add_one
  证明: by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h)]; rw [semilength_add]; rw [semilength_nest]; rw [add_right_comm]

include h in

Depends on / 依赖: add_right_comm, nest_insidePart_add_outsidePart, semilength, semilength_add, semilength_nest
-/
lemma semilength_insidePart_add_semilength_outsidePart_add_one :
    p.insidePart.semilength + p.outsidePart.semilength + 1 = p.semilength := by
  rw [← congrArg semilength (nest_insidePart_add_outsidePart h)]; rw [semilength_add]; rw [semilength_nest]; rw [add_right_comm]

include h in
/--
theorem `semilength_insidePart_lt` / 定理 `semilength_insidePart_lt`

English:
theorem semilength_insidePart_lt
  statement: p.insidePart.semilength < p.semilength
  proof: by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

include h in

中文:
定理 semilength_insidePart_lt
  结论: p.insidePart.semilength < p.semilength
  证明: by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

include h in

Depends on / 依赖: semilength_insidePart_add_semilength_outsidePart_add_one
-/
theorem semilength_insidePart_lt : p.insidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

include h in
/--
theorem `semilength_outsidePart_lt` / 定理 `semilength_outsidePart_lt`

English:
theorem semilength_outsidePart_lt
  statement: p.outsidePart.semilength < p.semilength
  proof: by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

中文:
定理 semilength_outsidePart_lt
  结论: p.outsidePart.semilength < p.semilength
  证明: by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

Depends on / 依赖: semilength_insidePart_add_semilength_outsidePart_add_one
-/
theorem semilength_outsidePart_lt : p.outsidePart.semilength < p.semilength := by
  have := semilength_insidePart_add_semilength_outsidePart_add_one h
  lia

end FirstReturn

section Order

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder DyckWord
  body: Relation.ReflTransGen (fun p q => p = q.insidePart ∨ p = q.outsidePart)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

中文:
实例 :
  签名: Preorder DyckWord
  定义体: Relation.ReflTransGen (fun p q => p = q.insidePart ∨ p = q.outsidePart)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

Depends on / 依赖: CompHaus, Condensed, Condensed.forget, CondensedSet, CondensedSet.LocallyConstant.iso.sym, Faithful, IsIso.comp_isIso, LocallyConstant, ReflTransGen, Relation, Relation.ReflTransGen, Sheaf.isConstant_iff_isIso_counit_app, coherentTopology, comp_isIso, constantSheaf, constantSheafAdj_counit_w, discrete, discreteUnderlyingAdj, essImage, essImage_eq_of_natIso
-/
instance : Preorder DyckWord where
  le := Relation.ReflTransGen (fun p q => p = q.insidePart ∨ p = q.outsidePart)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/--
lemma `le_add_self` / 引理 `le_add_self`

English:
lemma le_add_self
  given: (p q : DyckWord)
  statement: q <= p + q
  proof: by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_outsidePart_lt h
    exact (le_add_self p.outsidePart q).trans
      (Relation.ReflTransGen.single (Or.inr (outsidePart_add h).symm))
termination_by p.semilength

中文:
引理 le_add_self
  条件: (p q : DyckWord)
  结论: q <= p + q
  证明: by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_outsidePart_lt h
    exact (le_add_self p.outsidePart q).trans
      (Relation.ReflTransGen.single (Or.inr (outsidePart_add h).symm))
termination_by p.semilength

Depends on / 依赖: Or.inr, ReflTransGen, Relation, Relation.ReflTransGen.single, le_add_self, outsidePart, outsidePart_add, p.outsidePart, p.semilength, semilength, semilength_outsidePart_lt, single, termination_by
-/
lemma le_add_self (p q : DyckWord) : q <= p + q := by
  by_cases h : p = 0
  · simp [h]
  · have := semilength_outsidePart_lt h
    exact (le_add_self p.outsidePart q).trans
      (Relation.ReflTransGen.single (Or.inr (outsidePart_add h).symm))
termination_by p.semilength

variable (p) in protected lemma zero_le : 0 <= p := add_zero p ▸ le_add_self p 0

/--
lemma `infix_of_le` / 引理 `infix_of_le`

English:
lemma infix_of_le
  given: (h : p <= q)
  statement: p.toList <:+: q.toList
  proof: by
  induction h with
  | refl => exact infix_refl _
  | tail _pm mq ih =>
    rename_i m r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · have : [U] ++ r.insidePart ++ [D] ++ r.outsidePart = r :=
        DyckWord.ext_iff.

中文:
引理 infix_of_le
  条件: (h : p <= q)
  结论: p.toList <:+: q.toList
  证明: by
  induction h with
  | refl => exact infix_refl _
  | tail _pm mq ih =>
    rename_i m r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · have : [U] ++ r.insidePart ++ [D] ++ r.outsidePart = r :=
        DyckWord.ext_iff.

Depends on / 依赖: DyckWord, DyckWord.ext_iff.mp, eq_or_ne, ext_iff, infix_refl, insidePart, insidePart_zero, nest_insidePart_add_outsidePart, or_self, outsidePart, outsidePart_zero, r.insidePart, r.outsidePart, rename_i
-/
lemma infix_of_le (h : p <= q) : p.toList <:+: q.toList := by
  induction h with
  | refl => exact infix_refl _
  | tail _pm mq ih =>
    rename_i m r
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · have : [U] ++ r.insidePart ++ [D] ++ r.outsidePart = r :=
        DyckWord.ext_iff.mp (nest_insidePart_add_outsidePart hr)
      grind

/--
lemma `le_of_suffix` / 引理 `le_of_suffix`

English:
lemma le_of_suffix
  given: (h : p.toList <:+ q.toList)
  statement: p <= q
  proof: by
  obtain ⟨r', h⟩ := h
  have hc : (q.toList.take (q.toList.length - p.toList.length)).count U =
      (q.toList.take (q.toList.length - p.toList.length)).count D := by
    have hq := q.count_U_eq_count_D
    rw [← h] at hq ⊢
    rw [count_append]; rw [count_append]; rw [p.count_U_eq_count_D]; rw 

中文:
引理 le_of_suffix
  条件: (h : p.toList <:+ q.toList)
  结论: p <= q
  证明: by
  obtain ⟨r', h⟩ := h
  have hc : (q.toList.take (q.toList.length - p.toList.length)).count U =
      (q.toList.take (q.toList.length - p.toList.length)).count D := by
    have hq := q.count_U_eq_count_D
    rw [← h] at hq ⊢
    rw [count_append]; rw [count_append]; rw [p.count_U_eq_count_D]; rw 

Depends on / 依赖: DyckWord, DyckWord.ext, Nat.add_right_cancel_iff, add_right_cancel_iff, add_tsub_cancel_right, count_U_eq_count_D, count_append, length, length_append, p.count_U_eq_count_D, p.toList.length, q.count_U_eq_count_D, q.take, q.toList.length, q.toList.take, replace, simp_rw, take_left, toList
-/
lemma le_of_suffix (h : p.toList <:+ q.toList) : p <= q := by
  obtain ⟨r', h⟩ := h
  have hc : (q.toList.take (q.toList.length - p.toList.length)).count U =
      (q.toList.take (q.toList.length - p.toList.length)).count D := by
    have hq := q.count_U_eq_count_D
    rw [← h] at hq ⊢
    rw [count_append]; rw [count_append]; rw [p.count_U_eq_count_D]; rw [Nat.add_right_cancel_iff] at hq
    simp [hq]
  let r : DyckWord := q.take _ hc
  have e : r' = r := by
    simp_rw [r, take, ← h, length_append, add_tsub_cancel_right, take_left']
  rw [e] at h; replace h : r + p = q := DyckWord.ext h; rw [← h]; exact le_add_self ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder DyckWord
  body: by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
exact DyckWord.ext h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

中文:
实例 :
  签名: PartialOrder DyckWord
  定义体: by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
exact DyckWord.ext h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

Depends on / 依赖: DyckWord, DyckWord.ext, antisymm, eq_of_length, infix_of_le, length_le, length_le.antisymm
-/
instance : PartialOrder DyckWord where
  le_antisymm p q pq qp := by
    have h₁ := infix_of_le pq
    have h₂ := infix_of_le qp
exact DyckWord.ext h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

/--
lemma `pos_iff_ne_zero` / 引理 `pos_iff_ne_zero`

English:
lemma pos_iff_ne_zero
  statement: 0 < p ↔ p != 0
  proof: by
  rw [ne_comm]; rw [iff_comm]; rw [ne_iff_lt_iff_le]
  exact DyckWord.zero_le p

中文:
引理 pos_iff_ne_zero
  结论: 0 < p ↔ p != 0
  证明: by
  rw [ne_comm]; rw [iff_comm]; rw [ne_iff_lt_iff_le]
  exact DyckWord.zero_le p
-/
protected lemma pos_iff_ne_zero : 0 < p ↔ p != 0 := by
  rw [ne_comm]; rw [iff_comm]; rw [ne_iff_lt_iff_le]
  exact DyckWord.zero_le p

/--
lemma `monotone_semilength` / 引理 `monotone_semilength`

English:
lemma monotone_semilength
  statement: Monotone semilength
  proof: fun p q pq => by
  induction pq with
  | refl => rfl
  | tail _ mq ih =>
    rename_i m r _
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · rcases mq with hm | hm
      · exact ih.trans (hm ▸ semilength_insidePart_lt hr).le

中文:
引理 monotone_semilength
  结论: Monotone semilength
  证明: fun p q pq => by
  induction pq with
  | refl => rfl
  | tail _ mq ih =>
    rename_i m r _
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · rcases mq with hm | hm
      · exact ih.trans (hm ▸ semilength_insidePart_lt hr).le

Depends on / 依赖: eq_or_ne, ih.trans, insidePart_zero, or_self, outsidePart_zero, rename_i, semilength_insidePart_lt, semilength_outsidePart_lt
-/
lemma monotone_semilength : Monotone semilength := fun p q pq => by
  induction pq with
  | refl => rfl
  | tail _ mq ih =>
    rename_i m r _
    rcases eq_or_ne r 0 with rfl | hr
    · rw [insidePart_zero, outsidePart_zero, or_self] at mq
      rwa [mq] at ih
    · rcases mq with hm | hm
      · exact ih.trans (hm ▸ semilength_insidePart_lt hr).le
      · exact ih.trans (hm ▸ semilength_outsidePart_lt hr).le

/--
lemma `strictMono_semilength` / 引理 `strictMono_semilength`

English:
lemma strictMono_semilength
  statement: StrictMono semilength
  proof: fun p q pq => by
  obtain ⟨plq, pnq⟩ := lt_iff_le_and_ne.mp pq
  apply lt_of_le_of_ne (monotone_semilength plq)
  contrapose pnq
  replace pnq := congr(2 * $(pnq))
  simp_rw [two_mul_semilength_eq_length] at pnq
  exact DyckWord.ext ((infix_of_le plq).eq_of_length pnq)

中文:
引理 strictMono_semilength
  结论: StrictMono semilength
  证明: fun p q pq => by
  obtain ⟨plq, pnq⟩ := lt_iff_le_and_ne.mp pq
  apply lt_of_le_of_ne (monotone_semilength plq)
  contrapose pnq
  replace pnq := congr(2 * $(pnq))
  simp_rw [two_mul_semilength_eq_length] at pnq
  exact DyckWord.ext ((infix_of_le plq).eq_of_length pnq)

Depends on / 依赖: DyckWord, DyckWord.ext, contrapose, eq_of_length, infix_of_le, lt_iff_le_and_ne, lt_iff_le_and_ne.mp, lt_of_le_of_ne, monotone_semilength, replace, simp_rw, two_mul_semilength_eq_length
-/
lemma strictMono_semilength : StrictMono semilength := fun p q pq => by
  obtain ⟨plq, pnq⟩ := lt_iff_le_and_ne.mp pq
  apply lt_of_le_of_ne (monotone_semilength plq)
  contrapose pnq
  replace pnq := congr(2 * $(pnq))
  simp_rw [two_mul_semilength_eq_length] at pnq
  exact DyckWord.ext ((infix_of_le plq).eq_of_length pnq)

end Order

section BinaryTree

open BinaryTree

/--
Definition of `toTree` / `toTree` 的定义

English:
definition toTree
  signature: (p : DyckWord)
  body: if p = 0 then nil else p.insidePart.toTree △ p.outsidePart.toTree
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt ‹_›, semilength_outsidePart_lt ‹_›]

中文:
定义 toTree
  签名: (p : DyckWord)
  定义体: if p = 0 then nil else p.insidePart.toTree △ p.outsidePart.toTree
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt ‹_›, semilength_outsidePart_lt ‹_›]

Depends on / 依赖: decreasing_by, exacts, insidePart, outsidePart, p.insidePart.toTree, p.outsidePart.toTree, p.semilength, semilength, semilength_insidePart_lt, semilength_outsidePart_lt, termination_by, toTree
-/
def toTree (p : DyckWord) : BinaryTree Unit :=
  if p = 0 then nil else p.insidePart.toTree △ p.outsidePart.toTree
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt ‹_›, semilength_outsidePart_lt ‹_›]

/--
Definition of `ofTree` / `ofTree` 的定义

English:
definition ofTree
  signature: : BinaryTree Unit -> DyckWord

中文:
定义 ofTree
  签名: : BinaryTree Unit -> DyckWord
-/
def ofTree : BinaryTree Unit -> DyckWord
  | BinaryTree.nil => 0
  | BinaryTree.node _ l r => (ofTree l).nest + ofTree r

/--
lemma `ofTree_toTree` / 引理 `ofTree_toTree`

English:
lemma ofTree_toTree
  given: (p)
  statement: ofTree p.toTree = p
  proof: by
  by_cases h : p = 0
  · simp [h, toTree, ofTree]
  · rw [toTree]
    simp_rw [h, ite_false, ofTree]
    rw [ofTree_toTree p.insidePart]; rw [ofTree_toTree p.outsidePart]
    exact nest_insidePart_add_outsidePart h
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semi

中文:
引理 ofTree_toTree
  条件: (p)
  结论: ofTree p.toTree = p
  证明: by
  by_cases h : p = 0
  · simp [h, toTree, ofTree]
  · rw [toTree]
    simp_rw [h, ite_false, ofTree]
    rw [ofTree_toTree p.insidePart]; rw [ofTree_toTree p.outsidePart]
    exact nest_insidePart_add_outsidePart h
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semi

Depends on / 依赖: decreasing_by, exacts, insidePart, ite_false, nest_insidePart_add_outsidePart, ofTree, ofTree_toTree, outsidePart, p.insidePart, p.outsidePart, p.semilength, semilength, semilength_insidePart_lt, semilength_outsidePart_lt, simp_rw, termination_by, toTree
-/
lemma ofTree_toTree (p) : ofTree p.toTree = p := by
  by_cases h : p = 0
  · simp [h, toTree, ofTree]
  · rw [toTree]
    simp_rw [h, ite_false, ofTree]
    rw [ofTree_toTree p.insidePart]; rw [ofTree_toTree p.outsidePart]
    exact nest_insidePart_add_outsidePart h
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semilength_outsidePart_lt h]

/--
lemma `toTree_ofTree` / 引理 `toTree_ofTree`

English:
lemma toTree_ofTree
  statement: forall t, (ofTree t).toTree = t

中文:
引理 toTree_ofTree
  结论: 对任意 t, (ofTree t).toTree = t
-/
lemma toTree_ofTree : forall t, (ofTree t).toTree = t
  | BinaryTree.nil => by simp [ofTree, toTree]
  | BinaryTree.node _ _ _ => by simp [ofTree, toTree, toTree_ofTree]

/--
Definition of `equivTree` / `equivTree` 的定义

English:
definition equivTree
  signature: : DyckWord ≃ BinaryTree Unit where
  body: toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

@[simp]

中文:
定义 equivTree
  签名: : DyckWord ≃ BinaryTree Unit where
  定义体: toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

@[simp]
-/
@[simps] def equivTree : DyckWord ≃ BinaryTree Unit where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

@[simp]
/--
lemma `numNodes_toTree` / 引理 `numNodes_toTree`

English:
lemma numNodes_toTree
  given: (p : DyckWord)
  statement: p.toTree.numNodes = p.semilength
  proof: by
  by_cases h : p = 0
  · simp [h, toTree]
  · rw [toTree]
    simp_rw [h, ite_false, numNodes]
    rw [← semilength_insidePart_add_semilength_outsidePart_add_one h]; rw [numNodes_toTree p.insidePart]; rw [numNodes_toTree p.outsidePart]
termination_by p.semilength
decreasing_by exacts [semilength_

中文:
引理 numNodes_toTree
  条件: (p : DyckWord)
  结论: p.toTree.numNodes = p.semilength
  证明: by
  by_cases h : p = 0
  · simp [h, toTree]
  · rw [toTree]
    simp_rw [h, ite_false, numNodes]
    rw [← semilength_insidePart_add_semilength_outsidePart_add_one h]; rw [numNodes_toTree p.insidePart]; rw [numNodes_toTree p.outsidePart]
termination_by p.semilength
decreasing_by exacts [semilength_

Depends on / 依赖: decreasing_by, exacts, insidePart, ite_false, numNodes, numNodes_toTree, outsidePart, p.insidePart, p.outsidePart, p.semilength, semilength, semilength_insidePart_add_semilength_outsidePart_add_one, semilength_insidePart_lt, semilength_outsidePart_lt, simp_rw, termination_by, toTree
-/
lemma numNodes_toTree (p : DyckWord) : p.toTree.numNodes = p.semilength := by
  by_cases h : p = 0
  · simp [h, toTree]
  · rw [toTree]
    simp_rw [h, ite_false, numNodes]
    rw [← semilength_insidePart_add_semilength_outsidePart_add_one h]; rw [numNodes_toTree p.insidePart]; rw [numNodes_toTree p.outsidePart]
termination_by p.semilength
decreasing_by exacts [semilength_insidePart_lt h, semilength_outsidePart_lt h]

@[deprecated (since := "2026-02-03")] alias semilength_eq_numNodes_equivTree := numNodes_toTree

/-- Equivalence between Dyck words of semilength `n` and rooted binary trees with
`n` internal nodes. -/
@[simps!]
/--
Definition of `equivTreesOfNumNodesEq` / `equivTreesOfNumNodesEq` 的定义

English:
definition equivTreesOfNumNodesEq
  signature: (n : Nat)
  body: equivTree.subtypeEquiv (by simp)

中文:
定义 equivTreesOfNumNodesEq
  签名: (n : 自然数)
  定义体: equivTree.subtypeEquiv (by simp)

Depends on / 依赖: equivTree, equivTree.subtypeEquiv, subtypeEquiv
-/
def equivTreesOfNumNodesEq (n : Nat) : { p : DyckWord // p.semilength = n } ≃ treesOfNumNodesEq n :=
  equivTree.subtypeEquiv (by simp)

instance {n : Nat} : Fintype { p : DyckWord // p.semilength = n } :=
  Fintype.ofEquiv _ (equivTreesOfNumNodesEq n).symm

/--
theorem `card_dyckWord_semilength_eq_catalan` / 定理 `card_dyckWord_semilength_eq_catalan`

English:
theorem card_dyckWord_semilength_eq_catalan
  given: (n : Nat)
  proof: by
  rw [← Fintype.ofEquiv_card (equivTreesOfNumNodesEq n)]; rw [← treesOfNumNodesEq_card_eq_catalan]
  convert! Fintype.card_coe _

中文:
定理 card_dyckWord_semilength_eq_catalan
  条件: (n : 自然数)
  证明: by
  rw [← Fintype.ofEquiv_card (equivTreesOfNumNodesEq n)]; rw [← treesOfNumNodesEq_card_eq_catalan]
  convert! Fintype.card_coe _

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.ofEquiv_card, card_coe, convert, equivTreesOfNumNodesEq, ofEquiv_card, treesOfNumNodesEq_card_eq_catalan
-/
theorem card_dyckWord_semilength_eq_catalan (n : Nat) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n := by
  rw [← Fintype.ofEquiv_card (equivTreesOfNumNodesEq n)]; rw [← treesOfNumNodesEq_card_eq_catalan]
  convert! Fintype.card_coe _

end BinaryTree

end DyckWord

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `p.firstReturn` is positive if `p` is nonzero. -/
@[positivity DyckWord.firstReturn _]
meta def evalDyckWordFirstReturn : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(DyckWord.firstReturn $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(DyckWord.firstReturn_pos ($pa).ne'))
    | .nonzero pa => pure (.positive q(DyckWord.firstReturn_pos $pa))
    | _ => pure .none
  | _, _, _ => throwError "not DyckWord.firstReturn"

end Mathlib.Meta.Positivity
