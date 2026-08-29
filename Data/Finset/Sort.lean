/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Order.RelIso.Set

/-!
# Construct a sorted list from a finset.
-/

@[expose] public section

namespace Finset

open Multiset Nat

variable {α β : Type*}

/-! ### sort -/


section sort

/--
Definition of `sort` / `sort` 的定义

English:
definition sort
  signature: (s : Finset α) (r : α -> α -> Prop := by exact fun a b => a <= b)
  body: Multiset.sort s.1 r

中文:
定义 sort
  签名: (s : 有限集 α) (r : α -> α -> 命题 := by exact fun a b => a <= b)
  定义体: Multiset.sort s.1 r

Depends on / 依赖: Antisymm, DecidableRel, IsTrans, Multiset, Multiset.sort, Std.Antisymm, Std.Total
-/
def sort (s : Finset α) (r : α -> α -> Prop := by exact fun a b => a <= b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Multiset.sort s.1 r

section

variable (f : α ↪ β) (s : Finset α)
variable (r : α -> α -> Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]
variable (r' : β -> β -> Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']

@[simp]
/--
theorem `sort_val` / 定理 `sort_val`

English:
theorem sort_val
  statement: Multiset.sort s.val r = sort s r
  proof: rfl

@[simp]

中文:
定理 sort_val
  结论: Multiset.sort s.val r = sort s r
  证明: rfl

@[simp]
-/
theorem sort_val : Multiset.sort s.val r = sort s r :=
  rfl

@[simp]
/--
theorem `pairwise_sort` / 定理 `pairwise_sort`

English:
theorem pairwise_sort
  statement: List.Pairwise r (sort s r)
  proof: Multiset.pairwise_sort _ _

@[simp]

中文:
定理 pairwise_sort
  结论: 列表.两两 r (sort s r)
  证明: Multiset.pairwise_sort _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.pairwise_sort, pairwise_sort
-/
theorem pairwise_sort : List.Pairwise r (sort s r) :=
  Multiset.pairwise_sort _ _

@[simp]
/--
theorem `sort_eq` / 定理 `sort_eq`

English:
theorem sort_eq
  statement: ↑(sort s r) = s.1
  proof: Multiset.sort_eq _ _

@[simp]

中文:
定理 sort_eq
  结论: ↑(sort s r) = s.1
  证明: Multiset.sort_eq _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.sort_eq, sort_eq
-/
theorem sort_eq : ↑(sort s r) = s.1 :=
  Multiset.sort_eq _ _

@[simp]
/--
theorem `sort_nodup` / 定理 `sort_nodup`

English:
theorem sort_nodup
  statement: (sort s r).Nodup
  proof: (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort s r))

@[simp]

中文:
定理 sort_nodup
  结论: (sort s r).Nodup
  证明: (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort s r))

@[simp]

Depends on / 依赖: Multiset, Multiset.Nodup, sort_eq
-/
theorem sort_nodup : (sort s r).Nodup :=
  (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort s r))

@[simp]
/--
theorem `sort_toFinset` / 定理 `sort_toFinset`

English:
theorem sort_toFinset
  given: [DecidableEq α]
  statement: (sort s r).toFinset = s
  proof: List.toFinset_eq (s.sort_nodup r) ▸ eq_of_veq (s.sort_eq r)

@[simp]

中文:
定理 sort_toFinset
  条件: [DecidableEq α]
  结论: (sort s r).toFinset = s
  证明: List.toFinset_eq (s.sort_nodup r) ▸ eq_of_veq (s.sort_eq r)

@[simp]

Depends on / 依赖: List.toFinset_eq, eq_of_veq, s.sort_eq, s.sort_nodup, sort_eq, sort_nodup, toFinset_eq
-/
theorem sort_toFinset [DecidableEq α] : (sort s r).toFinset = s :=
  List.toFinset_eq (s.sort_nodup r) ▸ eq_of_veq (s.sort_eq r)

@[simp]
/--
theorem `sort_empty` / 定理 `sort_empty`

English:
theorem sort_empty
  statement: sort ∅ r = []
  proof: Multiset.sort_zero r

@[simp]

中文:
定理 sort_empty
  结论: sort ∅ r = []
  证明: Multiset.sort_zero r

@[simp]

Depends on / 依赖: Multiset, Multiset.sort_zero, sort_zero
-/
theorem sort_empty : sort ∅ r = [] :=
  Multiset.sort_zero r

@[simp]
/--
theorem `sort_singleton` / 定理 `sort_singleton`

English:
theorem sort_singleton
  given: (a : α)
  statement: sort {a} r = [a]
  proof: Multiset.sort_singleton a r

中文:
定理 sort_singleton
  条件: (a : α)
  结论: sort {a} r = [a]
  证明: Multiset.sort_singleton a r

Depends on / 依赖: Multiset, Multiset.sort_singleton, sort_singleton
-/
theorem sort_singleton (a : α) : sort {a} r = [a] :=
  Multiset.sort_singleton a r

/--
theorem `map_sort` / 定理 `map_sort`

English:
theorem map_sort
  proof: Multiset.map_sort _ _ _ _ hs

中文:
定理 map_sort
  证明: Multiset.map_sort _ _ _ _ hs

Depends on / 依赖: Multiset, Multiset.map_sort, map_sort
-/
theorem map_sort
    (hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' :=
  Multiset.map_sort _ _ _ _ hs

/--
theorem `_root_.StrictMonoOn.map_finsetSort` / 定理 `_root_.StrictMonoOn.map_finsetSort`

English:
theorem _root_.StrictMonoOn.map_finsetSort
  statement: [LinearOrder α] [LinearOrder β]
  proof: Finset.map_sort _ _ _ _ fun _a ha _b hb => (hf.le_iff_le ha hb).symm

@[simp]

中文:
定理 _root_.StrictMonoOn.map_finsetSort
  结论: [线性序 α] [线性序 β]
  证明: Finset.map_sort _ _ _ _ fun _a ha _b hb => (hf.le_iff_le ha hb).symm

@[simp]

Depends on / 依赖: Finset, Finset.map_sort, hf.le_iff_le, le_iff_le, map_sort
-/
theorem _root_.StrictMonoOn.map_finsetSort [LinearOrder α] [LinearOrder β]
    (hf : StrictMonoOn f s) :
    s.sort.map f = (s.map f).sort :=
  Finset.map_sort _ _ _ _ fun _a ha _b hb => (hf.le_iff_le ha hb).symm

@[simp]
/--
theorem `sort_range` / 定理 `sort_range`

English:
theorem sort_range
  given: (n : Nat)
  statement: sort (range n) = List.range n
  proof: Multiset.sort_range n

中文:
定理 sort_range
  条件: (n : 自然数)
  结论: sort (range n) = 列表.range n
  证明: Multiset.sort_range n

Depends on / 依赖: Multiset, Multiset.sort_range, sort_range
-/
theorem sort_range (n : Nat) : sort (range n) = List.range n :=
  Multiset.sort_range n

open scoped List in
/--
theorem `sort_perm_toList` / 定理 `sort_perm_toList`

English:
theorem sort_perm_toList
  statement: sort s r ~ s.toList
  proof: by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]

中文:
定理 sort_perm_toList
  结论: sort s r ~ s.toList
  证明: by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]

Depends on / 依赖: Multiset, Multiset.coe_eq_coe, coe_eq_coe, coe_toList, sort_eq
-/
theorem sort_perm_toList : sort s r ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]

/--
theorem `_root_.List.toFinset_sort` / 定理 `_root_.List.toFinset_sort`

English:
theorem _root_.List.toFinset_sort
  given: [DecidableEq α] {l : List α} (hl : l.Nodup)
  proof: by
  refine ⟨?_, ((sort_perm_toList _ r).trans (List.toFinset_toList hl)).eq_of_pairwise'
    (pairwise_sort _ _)⟩
  intro h
  rw [← h]
  exact pairwise_sort _ r

中文:
定理 _root_.列表.toFinset_sort
  条件: [DecidableEq α] {l : 列表 α} (hl : l.Nodup)
  证明: by
  refine ⟨?_, ((sort_perm_toList _ r).trans (List.toFinset_toList hl)).eq_of_pairwise'
    (pairwise_sort _ _)⟩
  intro h
  rw [← h]
  exact pairwise_sort _ r

Depends on / 依赖: List.toFinset_toList, eq_of_pairwise, pairwise_sort, sort_perm_toList, toFinset_toList
-/
theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :
    sort l.toFinset r = l ↔ l.Pairwise r := by
  refine ⟨?_, ((sort_perm_toList _ r).trans (List.toFinset_toList hl)).eq_of_pairwise'
    (pairwise_sort _ _)⟩
  intro h
  rw [← h]
  exact pairwise_sort _ r

end

section

variable {m : Multiset α} {s : Finset α}
variable (r : α -> α -> Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

@[simp]
/--
theorem `sort_mk` / 定理 `sort_mk`

English:
theorem sort_mk
  given: (h : m.Nodup)
  statement: sort ⟨m, h⟩ r = m.sort r
  proof: rfl

@[simp]

中文:
定理 sort_mk
  条件: (h : m.Nodup)
  结论: sort ⟨m, h⟩ r = m.sort r
  证明: rfl

@[simp]
-/
theorem sort_mk (h : m.Nodup) : sort ⟨m, h⟩ r = m.sort r := rfl

@[simp]
/--
theorem `mem_sort` / 定理 `mem_sort`

English:
theorem mem_sort
  given: {a : α}
  statement: a in sort s r ↔ a in s
  proof: Multiset.mem_sort _

@[simp]

中文:
定理 mem_sort
  条件: {a : α}
  结论: a in sort s r ↔ a in s
  证明: Multiset.mem_sort _

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_sort, mem_sort
-/
theorem mem_sort {a : α} : a in sort s r ↔ a in s :=
  Multiset.mem_sort _

@[simp]
/--
theorem `length_sort` / 定理 `length_sort`

English:
theorem length_sort
  statement: (sort s r).length = s.card
  proof: Multiset.length_sort _

中文:
定理 length_sort
  结论: (sort s r).length = s.card
  证明: Multiset.length_sort _

Depends on / 依赖: Multiset, Multiset.length_sort, length_sort
-/
theorem length_sort : (sort s r).length = s.card :=
  Multiset.length_sort _

/--
theorem `sort_cons` / 定理 `sort_cons`

English:
theorem sort_cons
  given: {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ s)
  proof: by
  rw [sort]; rw [cons_val]; rw [Multiset.sort_cons a _ r h₁]; rw [sort_val]

中文:
定理 sort_cons
  条件: {a : α} (h₁ : 对任意 b in s, r a b) (h₂ : a ∉ s)
  证明: by
  rw [sort]; rw [cons_val]; rw [Multiset.sort_cons a _ r h₁]; rw [sort_val]

Depends on / 依赖: Multiset, Multiset.sort_cons, cons_val, sort_cons, sort_val
-/
theorem sort_cons {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ s) :
    sort (cons a s h₂) r = a :: sort s r := by
  rw [sort]; rw [cons_val]; rw [Multiset.sort_cons a _ r h₁]; rw [sort_val]

/--
theorem `sort_insert` / 定理 `sort_insert`

English:
theorem sort_insert
  given: [DecidableEq α] {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ s)
  proof: by
  rw [← cons_eq_insert _ _ h₂]; rw [sort_cons r h₁]

中文:
定理 sort_insert
  条件: [DecidableEq α] {a : α} (h₁ : 对任意 b in s, r a b) (h₂ : a ∉ s)
  证明: by
  rw [← cons_eq_insert _ _ h₂]; rw [sort_cons r h₁]

Depends on / 依赖: cons_eq_insert, sort_cons
-/
theorem sort_insert [DecidableEq α] {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ s) :
    sort (insert a s) r = a :: sort s r := by
  rw [← cons_eq_insert _ _ h₂]; rw [sort_cons r h₁]

end

end sort

section SortLinearOrder

variable [LinearOrder α]

/--
theorem `sortedLT_sort` / 定理 `sortedLT_sort`

English:
theorem sortedLT_sort
  given: (s : Finset α)
  statement: (sort s).SortedLT
  proof: (pairwise_sort _ _).sortedLE.sortedLT_of_nodup (sort_nodup _ _)

中文:
定理 sortedLT_sort
  条件: (s : 有限集 α)
  结论: (sort s).SortedLT
  证明: (pairwise_sort _ _).sortedLE.sortedLT_of_nodup (sort_nodup _ _)

Depends on / 依赖: pairwise_sort, sort_nodup, sortedLE, sortedLE.sortedLT_of_nodup, sortedLT_of_nodup
-/
theorem sortedLT_sort (s : Finset α) : (sort s).SortedLT :=
  (pairwise_sort _ _).sortedLE.sortedLT_of_nodup (sort_nodup _ _)

/--
theorem `sortedGT_sort` / 定理 `sortedGT_sort`

English:
theorem sortedGT_sort
  given: (s : Finset α)
  statement: (sort s (· >= ·)).SortedGT
  proof: (pairwise_sort _ _).sortedGE.sortedGT_of_nodup (sort_nodup _ _)

中文:
定理 sortedGT_sort
  条件: (s : 有限集 α)
  结论: (sort s (· >= ·)).SortedGT
  证明: (pairwise_sort _ _).sortedGE.sortedGT_of_nodup (sort_nodup _ _)

Depends on / 依赖: pairwise_sort, sort_nodup, sortedGE, sortedGE.sortedGT_of_nodup, sortedGT_of_nodup
-/
theorem sortedGT_sort (s : Finset α) : (sort s (· >= ·)).SortedGT :=
  (pairwise_sort _ _).sortedGE.sortedGT_of_nodup (sort_nodup _ _)

/--
theorem `sorted_zero_eq_min'_aux` / 定理 `sorted_zero_eq_min'_aux`

English:
theorem sorted_zero_eq_min'_aux
  given: (s : Finset α) (h : 0 < s.sort.length) (H : s.Nonempty)
  proof: by
  let l := s.sort
  apply le_antisymm
  · have : s.min' H in l := (s.mem_sort (· <= ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ in s := (Finset.mem_sort (α := α) (· <= ·)).1 (List.get_mem l _)
    exact s.min'_le _ this

中文:
定理 sorted_zero_eq_min'_aux
  条件: (s : 有限集 α) (h : 0 < s.sort.length) (H : s.非空)
  证明: by
  let l := s.sort
  apply le_antisymm
  · have : s.min' H in l := (s.mem_sort (· <= ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ in s := (Finset.mem_sort (α := α) (· <= ·)).1 (List.get_mem l _)
    exact s.min'_le _ this

Depends on / 依赖: Finset, Finset.mem_sort, List.get_mem, List.mem_iff_get, Nat.zero_le, _mem, get_mem, l.get, le_antisymm, mem_iff_get, mem_sort, pairwise_sort, rel_get_of_le, s.mem_sort, s.min, s.pairwise_sort, s.sort, zero_le
-/
theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < s.sort.length) (H : s.Nonempty) :
    s.sort.get ⟨0, h⟩ = s.min' H := by
  let l := s.sort
  apply le_antisymm
  · have : s.min' H in l := (s.mem_sort (· <= ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ in s := (Finset.mem_sort (α := α) (· <= ·)).1 (List.get_mem l _)
    exact s.min'_le _ this

/--
theorem `sorted_zero_eq_min'` / 定理 `sorted_zero_eq_min'`

English:
theorem sorted_zero_eq_min'
  given: {s : Finset α} {h : 0 < s.sort.length}
  proof: sorted_zero_eq_min'_aux _ _ _

中文:
定理 sorted_zero_eq_min'
  条件: {s : 有限集 α} {h : 0 < s.sort.length}
  证明: sorted_zero_eq_min'_aux _ _ _
-/
theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < s.sort.length} :
    s.sort[0] = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _

/--
theorem `min'_eq_sorted_zero` / 定理 `min'_eq_sorted_zero`

English:
theorem min'_eq_sorted_zero
  given: {s : Finset α} {h : s.Nonempty}
  proof: (sorted_zero_eq_min'_aux _ _ _).symm

中文:
定理 最小值'_eq_sorted_zero
  条件: {s : 有限集 α} {h : s.非空}
  证明: (sorted_zero_eq_min'_aux _ _ _).symm
-/
theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h = s.sort[0]'(by rw [length_sort]; exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm

/--
theorem `sorted_last_eq_max'_aux` / 定理 `sorted_last_eq_max'_aux`

English:
theorem sorted_last_eq_max'_aux
  statement: (s : Finset α)
  proof: by
  let l := s.sort
  apply le_antisymm
  · have : l.get ⟨s.sort.length - 1, h⟩ in s :=
      (s.mem_sort (· <= ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H in l := (s.mem_sort (· <= ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)

中文:
定理 sorted_last_eq_max'_aux
  结论: (s : 有限集 α)
  证明: by
  let l := s.sort
  apply le_antisymm
  · have : l.get ⟨s.sort.length - 1, h⟩ in s :=
      (s.mem_sort (· <= ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H in l := (s.mem_sort (· <= ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)

Depends on / 依赖: List.get_mem, List.mem_iff_get, Nat.le_sub_one_of_lt, _mem, get_mem, i.prop, l.get, le_antisymm, le_max, le_sub_one_of_lt, length, mem_iff_get, mem_sort, pairwise_sort, rel_get_of_le, s.le_max, s.max, s.mem_sort, s.pairwise_sort, s.sort
-/
theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : s.sort.length - 1 < s.sort.length) (H : s.Nonempty) :
    s.sort[s.sort.length - 1] = s.max' H := by
  let l := s.sort
  apply le_antisymm
  · have : l.get ⟨s.sort.length - 1, h⟩ in s :=
      (s.mem_sort (· <= ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H in l := (s.mem_sort (· <= ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : exists i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· <= ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)

/--
theorem `sorted_last_eq_max'` / 定理 `sorted_last_eq_max'`

English:
theorem sorted_last_eq_max'
  statement: {s : Finset α}
  proof: sorted_last_eq_max'_aux _ h _

中文:
定理 sorted_last_eq_max'
  结论: {s : 有限集 α}
  证明: sorted_last_eq_max'_aux _ h _
-/
theorem sorted_last_eq_max' {s : Finset α}
    {h : s.sort.length - 1 < s.sort.length} :
    s.sort[s.sort.length - 1] =
      s.max' (by rw [length_sort] at h; exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
  sorted_last_eq_max'_aux _ h _

/--
theorem `max'_eq_sorted_last` / 定理 `max'_eq_sorted_last`

English:
theorem max'_eq_sorted_last
  given: {s : Finset α} {h : s.Nonempty}
  proof: (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm

中文:
定理 最大值'_eq_sorted_last
  条件: {s : 有限集 α} {h : s.非空}
  证明: (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm
-/
theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      s.sort[s.sort.length - 1]'
        (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) :=
  (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm

/--
Definition of `orderIsoOfFin` / `orderIsoOfFin` 的定义

English:
definition orderIsoOfFin
  signature: (s : Finset α) {k : Nat} (h : s.card = k)
  body: OrderIso.trans (Fin.castOrderIso ((s.length_sort (· <= ·)).trans h).symm)
(s.sortedLT_sort.getIso _).trans OrderIso.setCongr {x | x in s.sort (· <= ·)} _ by simp

中文:
定义 orderIsoOfFin
  签名: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  定义体: OrderIso.trans (Fin.castOrderIso ((s.length_sort (· <= ·)).trans h).symm)
(s.sortedLT_sort.getIso _).trans OrderIso.setCongr {x | x in s.sort (· <= ·)} _ by simp

Depends on / 依赖: Fin.castOrderIso, OrderIso, OrderIso.setCongr, OrderIso.trans, castOrderIso, getIso, length_sort, s.length_sort, s.sort, s.sortedLT_sort.getIso, setCongr, sortedLT_sort
-/
def orderIsoOfFin (s : Finset α) {k : Nat} (h : s.card = k) : Fin k ≃o s :=
OrderIso.trans (Fin.castOrderIso ((s.length_sort (· <= ·)).trans h).symm)
(s.sortedLT_sort.getIso _).trans OrderIso.setCongr {x | x in s.sort (· <= ·)} _ by simp

/--
Definition of `orderEmbOfFin` / `orderEmbOfFin` 的定义

English:
definition orderEmbOfFin
  signature: (s : Finset α) {k : Nat} (h : s.card = k)
  body: (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]

中文:
定义 orderEmbOfFin
  签名: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  定义体: (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.subtype, orderIsoOfFin, subtype, toOrderEmbedding, toOrderEmbedding.trans
-/
def orderEmbOfFin (s : Finset α) {k : Nat} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]
/--
theorem `coe_orderIsoOfFin_apply` / 定理 `coe_orderIsoOfFin_apply`

English:
theorem coe_orderIsoOfFin_apply
  given: (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k)
  proof: rfl

中文:
定理 coe_orderIsoOfFin_apply
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k) (i : 有限集 k)
  证明: rfl
-/
theorem coe_orderIsoOfFin_apply (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl

/--
theorem `orderIsoOfFin_symm_apply` / 定理 `orderIsoOfFin_symm_apply`

English:
theorem orderIsoOfFin_symm_apply
  given: (s : Finset α) {k : Nat} (h : s.card = k) (x : s)
  proof: rfl

中文:
定理 orderIsoOfFin_symm_apply
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k) (x : s)
  证明: rfl
-/
theorem orderIsoOfFin_symm_apply (s : Finset α) {k : Nat} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = s.sort.idxOf ↑x :=
  rfl

/--
theorem `orderEmbOfFin_apply` / 定理 `orderEmbOfFin_apply`

English:
theorem orderEmbOfFin_apply
  given: (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k)
  proof: rfl

@[simp]

中文:
定理 orderEmbOfFin_apply
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k) (i : 有限集 k)
  证明: rfl

@[simp]
-/
theorem orderEmbOfFin_apply (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i = s.sort[i]'(by rw [length_sort, h]; exact i.2) :=
  rfl

@[simp]
/--
theorem `orderEmbOfFin_mem` / 定理 `orderEmbOfFin_mem`

English:
theorem orderEmbOfFin_mem
  given: (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k)
  proof: (s.orderIsoOfFin h i).2

@[simp]

中文:
定理 orderEmbOfFin_mem
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k) (i : 有限集 k)
  证明: (s.orderIsoOfFin h i).2

@[simp]

Depends on / 依赖: orderIsoOfFin, s.orderIsoOfFin
-/
theorem orderEmbOfFin_mem (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i in s :=
  (s.orderIsoOfFin h i).2

@[simp]
/--
theorem `range_orderEmbOfFin` / 定理 `range_orderEmbOfFin`

English:
theorem range_orderEmbOfFin
  given: (s : Finset α) {k : Nat} (h : s.card = k)
  proof: by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ -> α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.coe_subtype, OrderIso.coe_toOrderEmbedding,
    Subtype.range_coe_subtype, Finset.setOfPred_mem]

@[simp]

中文:
定理 range_orderEmbOfFin
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  证明: by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ -> α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.coe_subtype, OrderIso.coe_toOrderEmbedding,
    Subtype.range_coe_subtype, Finset.setOfPred_mem]

@[simp]

Depends on / 依赖: Finset, Finset.orderEmbOfFin, Finset.setOfPred_mem, OrderEmbedding, OrderEmbedding.coe_subtype, OrderIso, OrderIso.coe_toOrderEmbedding, RelEmbedding, RelEmbedding.coe_trans, RelIso, RelIso.range_eq, Set.image_univ, Set.range_comp, Subtype, Subtype.range_coe_subtype, coe_subtype, coe_toOrderEmbedding, coe_trans, image_univ, orderEmbOfFin
-/
theorem range_orderEmbOfFin (s : Finset α) {k : Nat} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ -> α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.coe_subtype, OrderIso.coe_toOrderEmbedding,
    Subtype.range_coe_subtype, Finset.setOfPred_mem]

@[simp]
/--
theorem `image_orderEmbOfFin_univ` / 定理 `image_orderEmbOfFin_univ`

English:
theorem image_orderEmbOfFin_univ
  given: (s : Finset α) {k : Nat} (h : s.card = k)
  proof: by
  apply Finset.coe_injective
  simp

@[simp]

中文:
定理 image_orderEmbOfFin_univ
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  证明: by
  apply Finset.coe_injective
  simp

@[simp]

Depends on / 依赖: Finset, Finset.coe_injective, coe_injective
-/
theorem image_orderEmbOfFin_univ (s : Finset α) {k : Nat} (h : s.card = k) :
    Finset.image (s.orderEmbOfFin h) Finset.univ = s := by
  apply Finset.coe_injective
  simp

@[simp]
/--
theorem `map_orderEmbOfFin_univ` / 定理 `map_orderEmbOfFin_univ`

English:
theorem map_orderEmbOfFin_univ
  given: (s : Finset α) {k : Nat} (h : s.card = k)
  proof: by
  simp [map_eq_image]

@[simp]

中文:
定理 map_orderEmbOfFin_univ
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  证明: by
  simp [map_eq_image]

@[simp]

Depends on / 依赖: map_eq_image
-/
theorem map_orderEmbOfFin_univ (s : Finset α) {k : Nat} (h : s.card = k) :
    Finset.map (s.orderEmbOfFin h).toEmbedding Finset.univ = s := by
  simp [map_eq_image]

@[simp]
/--
theorem `listMap_orderEmbOfFin_finRange` / 定理 `listMap_orderEmbOfFin_finRange`

English:
theorem listMap_orderEmbOfFin_finRange
  given: (s : Finset α) {k : Nat} (h : s.card = k)
  proof: by
  obtain rfl : k = s.sort.length := by simp [h]
  exact List.map_getElem_finRange s.sort

中文:
定理 listMap_orderEmbOfFin_finRange
  条件: (s : 有限集 α) {k : 自然数} (h : s.card = k)
  证明: by
  obtain rfl : k = s.sort.length := by simp [h]
  exact List.map_getElem_finRange s.sort

Depends on / 依赖: List.map_getElem_finRange, length, map_getElem_finRange, s.sort, s.sort.length
-/
theorem listMap_orderEmbOfFin_finRange (s : Finset α) {k : Nat} (h : s.card = k) :
    (List.finRange k).map (s.orderEmbOfFin h) = s.sort := by
  obtain rfl : k = s.sort.length := by simp [h]
  exact List.map_getElem_finRange s.sort

/--
theorem `orderEmbOfFin_zero` / 定理 `orderEmbOfFin_zero`

English:
theorem orderEmbOfFin_zero
  given: {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k)
  proof: by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

中文:
定理 orderEmbOfFin_zero
  条件: {s : 有限集 α} {k : 自然数} (h : s.card = k) (hz : 0 < k)
  证明: by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

Depends on / 依赖: Fin.getElem_fin, getElem_fin, orderEmbOfFin_apply, sorted_zero_eq_min
-/
theorem orderEmbOfFin_zero {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

/--
theorem `orderEmbOfFin_last` / 定理 `orderEmbOfFin_last`

English:
theorem orderEmbOfFin_last
  given: {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k)
  proof: by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

中文:
定理 orderEmbOfFin_last
  条件: {s : 有限集 α} {k : 自然数} (h : s.card = k) (hz : 0 < k)
  证明: by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

Depends on / 依赖: _eq_sorted_last, orderEmbOfFin_apply
-/
theorem orderEmbOfFin_last {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ =
      s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

/-- `orderEmbOfFin {a} h` sends any argument to `a`. -/
@[simp]
/--
theorem `orderEmbOfFin_singleton` / 定理 `orderEmbOfFin_singleton`

English:
theorem orderEmbOfFin_singleton
  given: (a : α) (i : Fin 1)
  proof: by
  rw [Subsingleton.elim i ⟨0]; rw [Nat.zero_lt_one⟩]; rw [orderEmbOfFin_zero _ Nat.zero_lt_one]; rw [min'_singleton]

中文:
定理 orderEmbOfFin_singleton
  条件: (a : α) (i : 有限集 1)
  证明: by
  rw [Subsingleton.elim i ⟨0]; rw [Nat.zero_lt_one⟩]; rw [orderEmbOfFin_zero _ Nat.zero_lt_one]; rw [min'_singleton]

Depends on / 依赖: Nat.zero_lt_one, Subsingleton, Subsingleton.elim, _singleton, orderEmbOfFin_zero, zero_lt_one
-/
theorem orderEmbOfFin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0]; rw [Nat.zero_lt_one⟩]; rw [orderEmbOfFin_zero _ Nat.zero_lt_one]; rw [min'_singleton]

/--
theorem `orderEmbOfFin_unique` / 定理 `orderEmbOfFin_unique`

English:
theorem orderEmbOfFin_unique
  statement: {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k -> α}
  proof: by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono]; rw [range_orderEmbOfFin]; rw [← Set.image_univ]; rw [← coe_univ]; rw [← coe_image]; rw [coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

中文:
定理 orderEmbOfFin_unique
  结论: {s : 有限集 α} {k : 自然数} (h : s.card = k) {f : 有限集 k -> α}
  证明: by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono]; rw [range_orderEmbOfFin]; rw [← Set.image_univ]; rw [← coe_univ]; rw [← coe_image]; rw [coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, Set.image_univ, card_fin, card_image_of_injective, card_univ, coe_image, coe_inj, coe_univ, eq_of_subset_of_card_le, hmono.injective, hmono.range_inj, image_univ, injective, mem_image, orderEmbOfFin, range_inj, range_orderEmbOfFin, s.orderEmbOfFin, strictMono
-/
theorem orderEmbOfFin_unique {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k -> α}
    (hfs : forall x, f x in s) (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono]; rw [range_orderEmbOfFin]; rw [← Set.image_univ]; rw [← coe_univ]; rw [← coe_image]; rw [coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

/--
theorem `orderEmbOfFin_unique'` / 定理 `orderEmbOfFin_unique'`

English:
theorem orderEmbOfFin_unique'
  statement: {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k ↪o α}
  proof: RelEmbedding.ext funext_iff.1 orderEmbOfFin_unique h hfs f.strictMono

中文:
定理 orderEmbOfFin_unique'
  结论: {s : 有限集 α} {k : 自然数} (h : s.card = k) {f : 有限集 k ↪o α}
  证明: RelEmbedding.ext funext_iff.1 orderEmbOfFin_unique h hfs f.strictMono

Depends on / 依赖: RelEmbedding, RelEmbedding.ext, f.strictMono, funext_iff, orderEmbOfFin_unique, strictMono
-/
theorem orderEmbOfFin_unique' {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : forall x, f x in s) : f = s.orderEmbOfFin h :=
RelEmbedding.ext funext_iff.1 orderEmbOfFin_unique h hfs f.strictMono

/-- Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
/--
theorem `orderEmbOfFin_eq_orderEmbOfFin_iff` / 定理 `orderEmbOfFin_eq_orderEmbOfFin_iff`

English:
theorem orderEmbOfFin_eq_orderEmbOfFin_iff
  statement: {k l : Nat} {s : Finset α} {i : Fin k} {j : Fin l}
  proof: by
  subst k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

中文:
定理 orderEmbOfFin_eq_orderEmbOfFin_iff
  结论: {k l : 自然数} {s : 有限集 α} {i : 有限集 k} {j : 有限集 l}
  证明: by
  subst k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

Depends on / 依赖: Fin.ext_iff, eq_iff_eq, eq_iff_eq.trans, ext_iff, orderEmbOfFin, s.orderEmbOfFin
-/
theorem orderEmbOfFin_eq_orderEmbOfFin_iff {k l : Nat} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : Nat) = (j : Nat) := by
  subst k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

/--
Definition of `orderEmbOfCardLe` / `orderEmbOfCardLe` 的定义

English:
definition orderEmbOfCardLe
  signature: (s : Finset α) {k : Nat} (h : k <= s.card)
  body: (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)

中文:
定义 orderEmbOfCardLe
  签名: (s : 有限集 α) {k : 自然数} (h : k <= s.card)
  定义体: (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)

Depends on / 依赖: Fin.castLEOrderEmb, castLEOrderEmb, orderEmbOfFin, s.orderEmbOfFin
-/
def orderEmbOfCardLe (s : Finset α) {k : Nat} (h : k <= s.card) : Fin k ↪o α :=
  (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)

/--
theorem `orderEmbOfCardLe_mem` / 定理 `orderEmbOfCardLe_mem`

English:
theorem orderEmbOfCardLe_mem
  given: (s : Finset α) {k : Nat} (h : k <= s.card) (a)
  proof: by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]

中文:
定理 orderEmbOfCardLe_mem
  条件: (s : 有限集 α) {k : 自然数} (h : k <= s.card) (a)
  证明: by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]

Depends on / 依赖: Finset, Finset.orderEmbOfFin_mem, Function, Function.comp_apply, RelEmbedding, RelEmbedding.coe_trans, coe_trans, comp_apply, orderEmbOfCardLe, orderEmbOfFin_mem
-/
theorem orderEmbOfCardLe_mem (s : Finset α) {k : Nat} (h : k <= s.card) (a) :
    orderEmbOfCardLe s h a in s := by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]

/--
lemma `orderEmbOfFin_compl_singleton` / 引理 `orderEmbOfFin_compl_singleton`

English:
lemma orderEmbOfFin_compl_singleton
  statement: {n : Nat} {i : Fin (n + 1)} {k : Nat}
  proof: by
  apply DFunLike.coe_injective
  rw [eq_comm]
  convert!
    orderEmbOfFin_unique _ (fun x => ?_) ((Fin.strictMono_succAbove _).comp (Fin.cast_strictMono _))
  · simp
  · simp [← h, card_compl]

@[simp]

中文:
引理 orderEmbOfFin_compl_singleton
  结论: {n : 自然数} {i : 有限集 (n + 1)} {k : 自然数}
  证明: by
  apply DFunLike.coe_injective
  rw [eq_comm]
  convert!
    orderEmbOfFin_unique _ (fun x => ?_) ((Fin.strictMono_succAbove _).comp (Fin.cast_strictMono _))
  · simp
  · simp [← h, card_compl]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Fin.cast_strictMono, Fin.strictMono_succAbove, card_compl, cast_strictMono, coe_injective, convert, eq_comm, orderEmbOfFin_unique, strictMono_succAbove
-/
lemma orderEmbOfFin_compl_singleton {n : Nat} {i : Fin (n + 1)} {k : Nat}
    (h : ({i}ᶜ : Finset _).card = k) :
    ({i}ᶜ : Finset _).orderEmbOfFin h =
      (Fin.castOrderIso <| by simp_all [card_compl]).toOrderEmbedding.trans
        (Fin.succAboveOrderEmb i) := by
  apply DFunLike.coe_injective
  rw [eq_comm]
  convert!
    orderEmbOfFin_unique _ (fun x => ?_) ((Fin.strictMono_succAbove _).comp (Fin.cast_strictMono _))
  · simp
  · simp [← h, card_compl]

@[simp]
/--
lemma `orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb` / 引理 `orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb`

English:
lemma orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb
  given: {n : Nat} (i : Fin (n + 1))
  proof: orderEmbOfFin_compl_singleton _

中文:
引理 orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: orderEmbOfFin_compl_singleton _

Depends on / 依赖: orderEmbOfFin_compl_singleton
-/
lemma orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb {n : Nat} (i : Fin (n + 1)) :
    ({i}ᶜ : Finset _).orderEmbOfFin (by simp [card_compl]) = Fin.succAboveOrderEmb i :=
  orderEmbOfFin_compl_singleton _

/--
lemma `orderEmbOfFin_compl_singleton_apply` / 引理 `orderEmbOfFin_compl_singleton_apply`

English:
lemma orderEmbOfFin_compl_singleton_apply
  statement: {n : Nat} {i : Fin (n + 1)} {k : Nat}
  proof: by
  rw [orderEmbOfFin_compl_singleton]
  simp

中文:
引理 orderEmbOfFin_compl_singleton_apply
  结论: {n : 自然数} {i : 有限集 (n + 1)} {k : 自然数}
  证明: by
  rw [orderEmbOfFin_compl_singleton]
  simp

Depends on / 依赖: orderEmbOfFin_compl_singleton
-/
lemma orderEmbOfFin_compl_singleton_apply {n : Nat} {i : Fin (n + 1)} {k : Nat}
    (h : ({i}ᶜ : Finset _).card = k) (j : Fin k) : ({i}ᶜ : Finset _).orderEmbOfFin h j =
      Fin.succAbove i (Fin.cast (h.symm.trans (by simp [card_compl])) j) := by
  rw [orderEmbOfFin_compl_singleton]
  simp

end SortLinearOrder

unsafe instance [Repr α] : Repr (Finset α) where
  reprPrec s _ :=
    -- multiset uses `0` not `∅` for empty sets
    if s.card = 0 then "∅" else repr s.1

end Finset

namespace Fin

/--
theorem `sort_univ` / 定理 `sort_univ`

English:
theorem sort_univ
  given: (n : Nat)
  statement: Finset.univ.sort (fun x y : Fin n => x <= y) = List.finRange n
  proof: Finset.univ.sortedLT_sort.eq_of_mem_iff (List.sortedLT_finRange n) (by simp)

中文:
定理 sort_univ
  条件: (n : 自然数)
  结论: 有限集.univ.sort (fun x y : 有限集 n => x <= y) = 列表.finRange n
  证明: Finset.univ.sortedLT_sort.eq_of_mem_iff (List.sortedLT_finRange n) (by simp)

Depends on / 依赖: Finset, Finset.univ.sortedLT_sort.eq_of_mem_iff, List.sortedLT_finRange, eq_of_mem_iff, sortedLT_finRange, sortedLT_sort
-/
theorem sort_univ (n : Nat) : Finset.univ.sort (fun x y : Fin n => x <= y) = List.finRange n :=
  Finset.univ.sortedLT_sort.eq_of_mem_iff (List.sortedLT_finRange n) (by simp)

end Fin

/--
Definition of `Fintype.orderIsoFinOfCardEq` / `Fintype.orderIsoFinOfCardEq` 的定义

English:
definition Fintype.orderIsoFinOfCardEq
  body: (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

中文:
定义 有限类型.orderIsoFinOfCardEq
  定义体: (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

Depends on / 依赖: Finset, Finset.coe_univ, Finset.univ.orderIsoOfFin, OrderIso, OrderIso.Set.univ, OrderIso.setCongr, coe_univ, orderIsoOfFin, setCongr
-/
def Fintype.orderIsoFinOfCardEq
    (α : Type*) [LinearOrder α] [Fintype α] {k : Nat} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

/--
lemma `nonempty_orderEmbedding_of_finite_infinite` / 引理 `nonempty_orderEmbedding_of_finite_infinite`

English:
lemma nonempty_orderEmbedding_of_finite_infinite
  proof: by
  have := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩

中文:
引理 nonempty_orderEmbedding_of_finite_infinite
  证明: by
  have := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩

Depends on / 依赖: Fintype, Fintype.card, Fintype.ofFinite, Fintype.orderIsoFinOfCardEq, Infinite, Infinite.exists_subset_card_eq, exists_subset_card_eq, ofFinite, orderEmbOfFin, orderIsoFinOfCardEq, s.orderEmbOfFin, symm.toOrderEmbedding, toOrderEmbedding
-/
lemma nonempty_orderEmbedding_of_finite_infinite
    (α : Type*) [LinearOrder α] [hα : Finite α]
    (β : Type*) [LinearOrder β] [hβ : Infinite β] : Nonempty (α ↪o β) := by
  have := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩
