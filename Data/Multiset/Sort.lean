/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Range
public meta import Mathlib.Util.Qq
public meta import Mathlib.Data.Multiset.Defs

/-!
# Construct a sorted list from a multiset.
-/

@[expose] public section

variable {α β : Type*}

namespace Multiset

open List

section sort


/--
Definition of `sort` / `sort` 的定义

English:
definition sort
  signature: (s : Multiset α) (r : α -> α -> Prop := by exact fun a b => a <= b)
  body: Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm).eq_of_pairwise' (r := r)
      (pairwise_mergeSort' _ _) (pairwise_mergeSort' _ _)

中文:
定义 sort
  签名: (s : Multiset α) (r : α -> α -> 命题 := by exact fun a b => a <= b)
  定义体: Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm).eq_of_pairwise' (r := r)
      (pairwise_mergeSort' _ _) (pairwise_mergeSort' _ _)

Depends on / 依赖: Antisymm, DecidableRel, IsTrans, Quot.liftOn, Std.Antisymm, Std.Total, eq_of_pairwise, h.trans, liftOn, mergeSort, mergeSort_perm, pairwise_mergeSort
-/
def sort (s : Multiset α) (r : α -> α -> Prop := by exact fun a b => a <= b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm).eq_of_pairwise' (r := r)
      (pairwise_mergeSort' _ _) (pairwise_mergeSort' _ _)

section

variable (a : α) (f : α -> β) (l : List α) (s : Multiset α)
variable (r : α -> α -> Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]
variable (r' : β -> β -> Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']

@[simp]
/--
theorem `coe_sort` / 定理 `coe_sort`

English:
theorem coe_sort
  statement: sort l r = mergeSort l (r · ·)
  proof: rfl

@[simp]

中文:
定理 coe_sort
  结论: sort l r = mergeSort l (r · ·)
  证明: rfl

@[simp]

Depends on / 依赖: toList
-/
theorem coe_sort : sort l r = mergeSort l (r · ·) :=
  rfl

@[simp]
/--
theorem `pairwise_sort` / 定理 `pairwise_sort`

English:
theorem pairwise_sort
  statement: (sort s r).Pairwise r
  proof: Quot.inductionOn s (pairwise_mergeSort' _)

@[simp]

中文:
定理 pairwise_sort
  结论: (sort s r).两两 r
  证明: Quot.inductionOn s (pairwise_mergeSort' _)

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn, pairwise_mergeSort
-/
theorem pairwise_sort : (sort s r).Pairwise r :=
  Quot.inductionOn s (pairwise_mergeSort' _)

@[simp]
/--
theorem `sort_eq` / 定理 `sort_eq`

English:
theorem sort_eq
  statement: ↑(sort s r) = s
  proof: Quot.inductionOn s fun _ => Quot.sound mergeSort_perm _ _

@[simp]

中文:
定理 sort_eq
  结论: ↑(sort s r) = s
  证明: Quot.inductionOn s fun _ => Quot.sound mergeSort_perm _ _

@[simp]

Depends on / 依赖: Quot.inductionOn, Quot.sound, inductionOn, mergeSort_perm
-/
theorem sort_eq : ↑(sort s r) = s :=
Quot.inductionOn s fun _ => Quot.sound mergeSort_perm _ _

@[simp]
/--
theorem `sort_zero` / 定理 `sort_zero`

English:
theorem sort_zero
  statement: sort 0 r = []
  proof: List.mergeSort_nil

@[simp]

中文:
定理 sort_zero
  结论: sort 0 r = []
  证明: List.mergeSort_nil

@[simp]

Depends on / 依赖: List.mergeSort_nil, mergeSort_nil
-/
theorem sort_zero : sort 0 r = [] :=
  List.mergeSort_nil

@[simp]
/--
theorem `sort_singleton` / 定理 `sort_singleton`

English:
theorem sort_singleton
  statement: sort {a} r = [a]
  proof: List.mergeSort_singleton a

中文:
定理 sort_singleton
  结论: sort {a} r = [a]
  证明: List.mergeSort_singleton a

Depends on / 依赖: List.mergeSort_singleton, mergeSort_singleton
-/
theorem sort_singleton : sort {a} r = [a] :=
  List.mergeSort_singleton a

/--
theorem `map_sort` / 定理 `map_sort`

English:
theorem map_sort
  given: (hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b))
  proof: by
  revert s
  exact Quot.ind fun l h => map_mergeSort (l := l) (by simpa using h)

中文:
定理 map_sort
  条件: (hs : 对任意 a in s, 对任意 b in s, r a b ↔ r' (f a) (f b))
  证明: by
  revert s
  exact Quot.ind fun l h => map_mergeSort (l := l) (by simpa using h)

Depends on / 依赖: Quot.ind, map_mergeSort, revert
-/
theorem map_sort (hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' := by
  revert s
  exact Quot.ind fun l h => map_mergeSort (l := l) (by simpa using h)

/--
theorem `sort_cons` / 定理 `sort_cons`

English:
theorem sort_cons
  statement: (forall b in s, r a b) -> sort (a ::ₘ s) r = a :: sort s r
  proof: by
  refine Quot.inductionOn s fun l => ?_
  simpa [mergeSort_eq_insertionSort] using insertionSort_cons_of_forall_rel r (a := a) (l := l)

@[simp]

中文:
定理 sort_cons
  结论: (对任意 b in s, r a b) -> sort (a ::ₘ s) r = a :: sort s r
  证明: by
  refine Quot.inductionOn s fun l => ?_
  simpa [mergeSort_eq_insertionSort] using insertionSort_cons_of_forall_rel r (a := a) (l := l)

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn, insertionSort_cons_of_forall_rel, mergeSort_eq_insertionSort
-/
theorem sort_cons : (forall b in s, r a b) -> sort (a ::ₘ s) r = a :: sort s r := by
  refine Quot.inductionOn s fun l => ?_
  simpa [mergeSort_eq_insertionSort] using insertionSort_cons_of_forall_rel r (a := a) (l := l)

@[simp]
/--
theorem `sort_range` / 定理 `sort_range`

English:
theorem sort_range
  given: (n : Nat)
  statement: sort (range n) = List.range n
  proof: List.mergeSort_eq_self _ (sortedLT_range n).sortedLE.pairwise

中文:
定理 sort_range
  条件: (n : 自然数)
  结论: sort (range n) = 列表.range n
  证明: List.mergeSort_eq_self _ (sortedLT_range n).sortedLE.pairwise

Depends on / 依赖: List.mergeSort_eq_self, mergeSort_eq_self, pairwise, sortedLE, sortedLE.pairwise, sortedLT_range
-/
theorem sort_range (n : Nat) : sort (range n) = List.range n :=
  List.mergeSort_eq_self _ (sortedLT_range n).sortedLE.pairwise

end

section

variable {a : α} {s : Multiset α}
variable (r : α -> α -> Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

@[simp]
/--
theorem `mem_sort` / 定理 `mem_sort`

English:
theorem mem_sort
  statement: a in sort s r ↔ a in s
  proof: by rw [← mem_coe, sort_eq]

@[simp]

中文:
定理 mem_sort
  结论: a in sort s r ↔ a in s
  证明: by rw [← mem_coe, sort_eq]

@[simp]

Depends on / 依赖: mem_coe, sort_eq
-/
theorem mem_sort : a in sort s r ↔ a in s := by rw [← mem_coe, sort_eq]

@[simp]
/--
theorem `length_sort` / 定理 `length_sort`

English:
theorem length_sort
  statement: (sort s r).length = card s
  proof: Quot.inductionOn s length_mergeSort

中文:
定理 length_sort
  结论: (sort s r).length = card s
  证明: Quot.inductionOn s length_mergeSort

Depends on / 依赖: Quot.inductionOn, inductionOn, length_mergeSort
-/
theorem length_sort : (sort s r).length = card s := Quot.inductionOn s length_mergeSort

end

end sort

open Qq in
universe u in
meta unsafe instance {α : Type u} [Lean.ToLevel.{u}] [Lean.ToExpr α] :
    Lean.ToExpr (Multiset α) :=
  haveI u' := Lean.toLevel.{u}
  haveI α' : Q(Type u') := Lean.toTypeExpr α
  { toTypeExpr := q(Multiset $α')
    toExpr s := show Q(Multiset $α') from
      if Multiset.card s = 0 then
        q(0)
      else
        mkSetLiteralQ (α := q($α')) q(Multiset $α') (s.unquot.map Lean.toExpr)}

-- TODO: use a sort order if available, gh-18166
unsafe instance [Repr α] : Repr (Multiset α) where
  reprPrec s _ :=
    if Multiset.card s = 0 then
      "0"
    else
      Std.Format.bracket "{" (Std.Format.joinSep (s.unquot.map repr) ("," ++ Std.Format.line)) "}"

end Multiset
