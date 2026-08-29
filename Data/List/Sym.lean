/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Sym.Sym2

/-! # Unordered tuples of elements of a list

Defines `List.sym` and the specialized `List.sym2` for computing lists of all unordered n-tuples
from a given list. These are list versions of `Nat.multichoose`.

## Main declarations

* `List.sym`: `xs.sym n` is a list of all unordered n-tuples of elements from `xs`,
  with multiplicity. The list's values are in `Sym α n`.
* `List.sym2`: `xs.sym2` is a list of all unordered pairs of elements from `xs`,
  with multiplicity. The list's values are in `Sym2 α`.

## TODO

* Prove `protected theorem Perm.sym (n : ℕ) {xs ys : List α} (h : xs ~ ys) : xs.sym n ~ ys.sym n`
  and lift the result to `Multiset` and `Finset`.

-/

@[expose] public section

namespace List

variable {α β : Type*}

section Sym2

/--
Definition of `sym2` / `sym2` 的定义

English:
definition sym2
  signature: : List α -> List (Sym2 α)

中文:
定义 sym2
  签名: : 列表 α -> 列表 (Sym2 α)
-/
protected def sym2 : List α -> List (Sym2 α)
  | [] => []
  | x :: xs => (x :: xs).map (fun y => s(x, y)) ++ xs.sym2

/--
theorem `sym2_map` / 定理 `sym2_map`

English:
theorem sym2_map
  given: (f : α -> β) (xs : List α)
  proof: by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih => simp [List.sym2, ih, Function.comp]

中文:
定理 sym2_map
  条件: (f : α -> β) (xs : 列表 α)
  证明: by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih => simp [List.sym2, ih, Function.comp]

Depends on / 依赖: Function, Function.comp, List.sym2
-/
theorem sym2_map (f : α -> β) (xs : List α) :
    (xs.map f).sym2 = xs.sym2.map (Sym2.map f) := by
  induction xs with
  | nil => simp [List.sym2]
  | cons x xs ih => simp [List.sym2, ih, Function.comp]

/--
theorem `mem_sym2_cons_iff` / 定理 `mem_sym2_cons_iff`

English:
theorem mem_sym2_cons_iff
  given: {x : α} {xs : List α} {z : Sym2 α}
  proof: by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]

@[simp]

中文:
定理 mem_sym2_cons_iff
  条件: {x : α} {xs : 列表 α} {z : Sym2 α}
  证明: by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]

@[simp]

Depends on / 依赖: List.sym2, cons_append, eq_comm, map_cons, mem_append, mem_cons, mem_map
-/
theorem mem_sym2_cons_iff {x : α} {xs : List α} {z : Sym2 α} :
    z in (x :: xs).sym2 ↔ z = s(x, x) ∨ (exists y, y in xs ∧ z = s(x, y)) ∨ z in xs.sym2 := by
  simp only [List.sym2, map_cons, cons_append, mem_cons, mem_append, mem_map]
  simp only [eq_comm]

@[simp]
/--
theorem `sym2_eq_nil_iff` / 定理 `sym2_eq_nil_iff`

English:
theorem sym2_eq_nil_iff
  given: {xs : List α}
  statement: xs.sym2 = [] ↔ xs = []
  proof: by
  cases xs <;> simp [List.sym2]

中文:
定理 sym2_eq_nil_iff
  条件: {xs : 列表 α}
  结论: xs.sym2 = [] ↔ xs = []
  证明: by
  cases xs <;> simp [List.sym2]

Depends on / 依赖: List.sym2
-/
theorem sym2_eq_nil_iff {xs : List α} : xs.sym2 = [] ↔ xs = [] := by
  cases xs <;> simp [List.sym2]

/--
theorem `left_mem_of_mk_mem_sym2` / 定理 `left_mem_of_mk_mem_sym2`

English:
theorem left_mem_of_mk_mem_sym2
  statement: {xs : List α} {a b : α}
  proof: by
  induction xs with
  | nil => exact (not_mem_nil h).elim
  | cons x xs ih =>
    rw [mem_cons]
    rw [mem_sym2_cons_iff] at h
    obtain (h | ⟨c, hc, h⟩ | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      exact .inl h.1
    · rw [Sym2.eq_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) :

中文:
定理 left_mem_of_mk_mem_sym2
  结论: {xs : 列表 α} {a b : α}
  证明: by
  induction xs with
  | nil => exact (not_mem_nil h).elim
  | cons x xs ih =>
    rw [mem_cons]
    rw [mem_sym2_cons_iff] at h
    obtain (h | ⟨c, hc, h⟩ | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      exact .inl h.1
    · rw [Sym2.eq_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) :

Depends on / 依赖: Sym2.eq_iff, and_or_left, eq_iff, mem_cons, mem_sym2_cons_iff, not_mem_nil
-/
theorem left_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) in xs.sym2) : a in xs := by
  induction xs with
  | nil => exact (not_mem_nil h).elim
  | cons x xs ih =>
    rw [mem_cons]
    rw [mem_sym2_cons_iff] at h
    obtain (h | ⟨c, hc, h⟩ | h) := h
    · rw [Sym2.eq_iff, ← and_or_left] at h
      exact .inl h.1
    · rw [Sym2.eq_iff] at h
      obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := h <;> simp [hc]
· exact .inr ih h

/--
theorem `right_mem_of_mk_mem_sym2` / 定理 `right_mem_of_mk_mem_sym2`

English:
theorem right_mem_of_mk_mem_sym2
  statement: {xs : List α} {a b : α}
  proof: by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mk_mem_sym2 h

中文:
定理 right_mem_of_mk_mem_sym2
  结论: {xs : 列表 α} {a b : α}
  证明: by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mk_mem_sym2 h

Depends on / 依赖: Sym2.eq_swap, eq_swap, left_mem_of_mk_mem_sym2
-/
theorem right_mem_of_mk_mem_sym2 {xs : List α} {a b : α}
    (h : s(a, b) in xs.sym2) : b in xs := by
  rw [Sym2.eq_swap] at h
  exact left_mem_of_mk_mem_sym2 h

/--
theorem `mk_mem_sym2` / 定理 `mk_mem_sym2`

English:
theorem mk_mem_sym2
  given: {xs : List α} {a b : α} (ha : a in xs) (hb : b in xs)
  proof: by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [mem_sym2_cons_iff]
    grind

中文:
定理 mk_mem_sym2
  条件: {xs : 列表 α} {a b : α} (ha : a in xs) (hb : b in xs)
  证明: by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [mem_sym2_cons_iff]
    grind

Depends on / 依赖: mem_sym2_cons_iff
-/
theorem mk_mem_sym2 {xs : List α} {a b : α} (ha : a in xs) (hb : b in xs) :
    s(a, b) in xs.sym2 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [mem_sym2_cons_iff]
    grind

/--
theorem `mk_mem_sym2_iff` / 定理 `mk_mem_sym2_iff`

English:
theorem mk_mem_sym2_iff
  given: {xs : List α} {a b : α}
  proof: by
  constructor
  · intro h
    exact ⟨left_mem_of_mk_mem_sym2 h, right_mem_of_mk_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mk_mem_sym2 ha hb

中文:
定理 mk_mem_sym2_iff
  条件: {xs : 列表 α} {a b : α}
  证明: by
  constructor
  · intro h
    exact ⟨left_mem_of_mk_mem_sym2 h, right_mem_of_mk_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mk_mem_sym2 ha hb

Depends on / 依赖: left_mem_of_mk_mem_sym2, mk_mem_sym2, right_mem_of_mk_mem_sym2
-/
theorem mk_mem_sym2_iff {xs : List α} {a b : α} :
    s(a, b) in xs.sym2 ↔ a in xs ∧ b in xs := by
  constructor
  · intro h
    exact ⟨left_mem_of_mk_mem_sym2 h, right_mem_of_mk_mem_sym2 h⟩
  · rintro ⟨ha, hb⟩
    exact mk_mem_sym2 ha hb

/--
theorem `mem_sym2_iff` / 定理 `mem_sym2_iff`

English:
theorem mem_sym2_iff
  given: {xs : List α} {z : Sym2 α}
  proof: by
  refine z.ind (fun a b => ?_)
  simp [mk_mem_sym2_iff]

中文:
定理 mem_sym2_iff
  条件: {xs : 列表 α} {z : Sym2 α}
  证明: by
  refine z.ind (fun a b => ?_)
  simp [mk_mem_sym2_iff]

Depends on / 依赖: mk_mem_sym2_iff, z.ind
-/
theorem mem_sym2_iff {xs : List α} {z : Sym2 α} :
    z in xs.sym2 ↔ forall y in z, y in xs := by
  refine z.ind (fun a b => ?_)
  simp [mk_mem_sym2_iff]

/--
lemma `setOfPred_mem_sym2` / 引理 `setOfPred_mem_sym2`

English:
lemma setOfPred_mem_sym2
  given: {xs : List α}
  proof: Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

中文:
引理 setOfPred_mem_sym2
  条件: {xs : 列表 α}
  证明: Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

Depends on / 依赖: Set.ext, mk_mem_sym2_iff, z.ind
-/
lemma setOfPred_mem_sym2 {xs : List α} :
    {z : Sym2 α | z in xs.sym2} = {x : α | x in xs}.sym2 :=
  Set.ext fun z => z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2

/--
theorem `Nodup.sym2` / 定理 `Nodup.sym2`

English:
theorem Nodup.sym2
  given: {xs : List α} (h : xs.Nodup)
  statement: xs.sym2.Nodup
  proof: by
  induction xs with
  | nil => simp only [List.sym2, nodup_nil]
  | cons x xs ih =>
    rw [List.sym2]
    specialize ih h.of_cons
    rw [nodup_cons] at h
    refine Nodup.append (Nodup.cons ?notmem (h.2.map ?inj)) ih ?disj
    case disj =>
      intro z hz hz'
      simp only [mem_cons, mem_map

中文:
定理 Nodup.sym2
  条件: {xs : 列表 α} (h : xs.Nodup)
  结论: xs.sym2.Nodup
  证明: by
  induction xs with
  | nil => simp only [List.sym2, nodup_nil]
  | cons x xs ih =>
    rw [List.sym2]
    specialize ih h.of_cons
    rw [nodup_cons] at h
    refine Nodup.append (Nodup.cons ?notmem (h.2.map ?inj)) ih ?disj
    case disj =>
      intro z hz hz'
      simp only [mem_cons, mem_map
-/
protected theorem Nodup.sym2 {xs : List α} (h : xs.Nodup) : xs.sym2.Nodup := by
  induction xs with
  | nil => simp only [List.sym2, nodup_nil]
  | cons x xs ih =>
    rw [List.sym2]
    specialize ih h.of_cons
    rw [nodup_cons] at h
    refine Nodup.append (Nodup.cons ?notmem (h.2.map ?inj)) ih ?disj
    case disj =>
      intro z hz hz'
      simp only [mem_cons, mem_map] at hz
      obtain ⟨_, (rfl | _), rfl⟩ := hz
        <;> simp [left_mem_of_mk_mem_sym2 hz'] at h
    case notmem =>
      intro h'
      simp only [h.1, mem_map, Sym2.eq_iff, true_and, or_self, exists_eq_right] at h'
    case inj =>
      intro a b
      simp only [Sym2.eq_iff, true_and]
      rintro (rfl | ⟨rfl, rfl⟩) <;> rfl

/--
theorem `map_mk_sublist_sym2` / 定理 `map_mk_sublist_sym2`

English:
theorem map_mk_sublist_sym2
  given: (x : α) (xs : List α) (h : x in xs)
  proof: by
  induction xs with
  | nil => simp
  | cons x' xs ih =>
    simp only [map_cons, List.sym2, cons_append]
    cases h with
    | head =>
      exact (sublist_append_left _ _).cons_cons _
    | tail _ h =>
      refine .cons _ ?_
      rw [← singleton_append]
      refine .append ?_ (ih h)
      r

中文:
定理 map_mk_sublist_sym2
  条件: (x : α) (xs : 列表 α) (h : x in xs)
  证明: by
  induction xs with
  | nil => simp
  | cons x' xs ih =>
    simp only [map_cons, List.sym2, cons_append]
    cases h with
    | head =>
      exact (sublist_append_left _ _).cons_cons _
    | tail _ h =>
      refine .cons _ ?_
      rw [← singleton_append]
      refine .append ?_ (ih h)
      r

Depends on / 依赖: List.sym2, Sym2.eq_swap, append, cons_append, cons_cons, eq_swap, map_cons, mem_map, singleton_append, singleton_sublist, sublist_append_left
-/
theorem map_mk_sublist_sym2 (x : α) (xs : List α) (h : x in xs) :
    map (fun y => s(x, y)) xs <+ xs.sym2 := by
  induction xs with
  | nil => simp
  | cons x' xs ih =>
    simp only [map_cons, List.sym2, cons_append]
    cases h with
    | head =>
      exact (sublist_append_left _ _).cons_cons _
    | tail _ h =>
      refine .cons _ ?_
      rw [← singleton_append]
      refine .append ?_ (ih h)
      rw [singleton_sublist]; rw [mem_map]
      exact ⟨_, h, Sym2.eq_swap⟩

/--
theorem `map_mk_disjoint_sym2` / 定理 `map_mk_disjoint_sym2`

English:
theorem map_mk_disjoint_sym2
  given: (x : α) (xs : List α) (h : x ∉ xs)
  proof: by
  induction xs with
  | nil => simp
  | cons x' xs ih => aesop (add simp mk_mem_sym2_iff, unfold safe List.Disjoint)

中文:
定理 map_mk_disjoint_sym2
  条件: (x : α) (xs : 列表 α) (h : x ∉ xs)
  证明: by
  induction xs with
  | nil => simp
  | cons x' xs ih => aesop (add simp mk_mem_sym2_iff, unfold safe List.Disjoint)

Depends on / 依赖: Disjoint, List.Disjoint, mk_mem_sym2_iff
-/
theorem map_mk_disjoint_sym2 (x : α) (xs : List α) (h : x ∉ xs) :
    (map (fun y => s(x, y)) xs).Disjoint xs.sym2 := by
  induction xs with
  | nil => simp
  | cons x' xs ih => aesop (add simp mk_mem_sym2_iff, unfold safe List.Disjoint)

/--
theorem `dedup_sym2` / 定理 `dedup_sym2`

English:
theorem dedup_sym2
  given: [DecidableEq α] (xs : List α)
  statement: xs.sym2.dedup = xs.dedup.sym2
  proof: by
  induction xs with
  | nil => simp only [List.sym2, dedup_nil]
  | cons x xs ih =>
    simp only [List.sym2, map_cons, cons_append]
    obtain hm | hm := Decidable.em (x in xs)
    · rw [dedup_cons_of_mem hm, ← ih, dedup_cons_of_mem,
        List.Subset.dedup_append_right (map_mk_sublist_sym2 _ 

中文:
定理 dedup_sym2
  条件: [DecidableEq α] (xs : 列表 α)
  结论: xs.sym2.dedup = xs.dedup.sym2
  证明: by
  induction xs with
  | nil => simp only [List.sym2, dedup_nil]
  | cons x xs ih =>
    simp only [List.sym2, map_cons, cons_append]
    obtain hm | hm := Decidable.em (x in xs)
    · rw [dedup_cons_of_mem hm, ← ih, dedup_cons_of_mem,
        List.Subset.dedup_append_right (map_mk_sublist_sym2 _ 

Depends on / 依赖: Decidable, Decidable.em, Disjoint, List.Disjoint.dedup_append, List.Subset.dedup_append_right, List.sym2, Subset, Sym2.eq_swap, cons_append, dedup_append, dedup_append_right, dedup_cons_of_mem, dedup_cons_of_notMem, dedup_map_of_injective, dedup_nil, eq_swap, map_cons, map_mk_sublist_sym2, mem_append_left, mem_map
-/
theorem dedup_sym2 [DecidableEq α] (xs : List α) : xs.sym2.dedup = xs.dedup.sym2 := by
  induction xs with
  | nil => simp only [List.sym2, dedup_nil]
  | cons x xs ih =>
    simp only [List.sym2, map_cons, cons_append]
    obtain hm | hm := Decidable.em (x in xs)
    · rw [dedup_cons_of_mem hm, ← ih, dedup_cons_of_mem,
        List.Subset.dedup_append_right (map_mk_sublist_sym2 _ _ hm).subset]
      refine mem_append_left _ ?_
      rw [mem_map]
      exact ⟨_, hm, Sym2.eq_swap⟩
    · rw [dedup_cons_of_notMem hm, List.sym2, map_cons, ← ih, dedup_cons_of_notMem, cons_append,
        List.Disjoint.dedup_append, dedup_map_of_injective]
      · exact (Sym2.mkEmbedding _).injective
      · exact map_mk_disjoint_sym2 x xs hm
      · simp [hm, mem_sym2_iff]

/--
theorem `Perm.sym2` / 定理 `Perm.sym2`

English:
theorem Perm.sym2
  given: {xs ys : List α} (h : xs ~ ys)
  proof: by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1, 2, 1]; rw [Sym2.eq_swap]
    -- Explicit permutation to speed up

中文:
定理 置换.sym2
  条件: {xs ys : 列表 α} (h : xs ~ ys)
  证明: by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1, 2, 1]; rw [Sym2.eq_swap]
    -- Explicit permutation to speed up
-/
protected theorem Perm.sym2 {xs ys : List α} (h : xs ~ ys) :
    xs.sym2 ~ ys.sym2 := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [List.sym2, map_cons, cons_append, perm_cons]
    exact (h.map _).append ih
  | swap x y xs =>
    simp only [List.sym2, map_cons, cons_append]
    conv => enter [1, 2, 1]; rw [Sym2.eq_swap]
    -- Explicit permutation to speed up simps that follow.
    refine Perm.trans (Perm.swap ..) (Perm.trans (Perm.cons _ ?_) (Perm.swap ..))
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      ← Multiset.coe_add, ← Multiset.singleton_add]
    simp only [add_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/--
theorem `Sublist.sym2` / 定理 `Sublist.sym2`

English:
theorem Sublist.sym2
  given: {xs ys : List α} (h : xs <+ ys)
  statement: xs.sym2 <+ ys.sym2
  proof: by
  induction h with
  | slnil => apply slnil
  | cons a h ih =>
    simp only [List.sym2]
    exact Sublist.append (nil_sublist _) ih
  | cons_cons a h ih =>
    simp only [List.sym2, map_cons, cons_append]
    exact cons_cons _ (append (Sublist.map _ h) ih)

中文:
定理 子表.sym2
  条件: {xs ys : 列表 α} (h : xs <+ ys)
  结论: xs.sym2 <+ ys.sym2
  证明: by
  induction h with
  | slnil => apply slnil
  | cons a h ih =>
    simp only [List.sym2]
    exact Sublist.append (nil_sublist _) ih
  | cons_cons a h ih =>
    simp only [List.sym2, map_cons, cons_append]
    exact cons_cons _ (append (Sublist.map _ h) ih)
-/
protected theorem Sublist.sym2 {xs ys : List α} (h : xs <+ ys) : xs.sym2 <+ ys.sym2 := by
  induction h with
  | slnil => apply slnil
  | cons a h ih =>
    simp only [List.sym2]
    exact Sublist.append (nil_sublist _) ih
  | cons_cons a h ih =>
    simp only [List.sym2, map_cons, cons_append]
    exact cons_cons _ (append (Sublist.map _ h) ih)

/--
theorem `Subperm.sym2` / 定理 `Subperm.sym2`

English:
theorem Subperm.sym2
  given: {xs ys : List α} (h : xs <+~ ys)
  statement: xs.sym2 <+~ ys.sym2
  proof: by
  obtain ⟨xs', hx, h⟩ := h
  exact hx.sym2.symm.subperm.trans h.sym2.subperm

中文:
定理 Subperm.sym2
  条件: {xs ys : 列表 α} (h : xs <+~ ys)
  结论: xs.sym2 <+~ ys.sym2
  证明: by
  obtain ⟨xs', hx, h⟩ := h
  exact hx.sym2.symm.subperm.trans h.sym2.subperm
-/
protected theorem Subperm.sym2 {xs ys : List α} (h : xs <+~ ys) : xs.sym2 <+~ ys.sym2 := by
  obtain ⟨xs', hx, h⟩ := h
  exact hx.sym2.symm.subperm.trans h.sym2.subperm

/--
theorem `length_sym2` / 定理 `length_sym2`

English:
theorem length_sym2
  given: {xs : List α}
  statement: xs.sym2.length = Nat.choose (xs.length + 1) 2
  proof: by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym2]; rw [length_append]; rw [length_map]; rw [length_cons]; rw [Nat.choose_succ_succ]; rw [← ih]; rw [Nat.choose_one_right]

中文:
定理 length_sym2
  条件: {xs : 列表 α}
  结论: xs.sym2.length = 自然数.choose (xs.length + 1) 2
  证明: by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym2]; rw [length_append]; rw [length_map]; rw [length_cons]; rw [Nat.choose_succ_succ]; rw [← ih]; rw [Nat.choose_one_right]

Depends on / 依赖: List.sym2, Nat.choose_one_right, Nat.choose_succ_succ, choose_one_right, choose_succ_succ, length_append, length_cons, length_map
-/
theorem length_sym2 {xs : List α} : xs.sym2.length = Nat.choose (xs.length + 1) 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.sym2]; rw [length_append]; rw [length_map]; rw [length_cons]; rw [Nat.choose_succ_succ]; rw [← ih]; rw [Nat.choose_one_right]

end Sym2

section Sym

/--
Definition of `sym` / `sym` 的定义

English:
definition sym
  signature: : (n : Nat) -> List α -> List (Sym α n)

中文:
定义 sym
  签名: : (n : 自然数) -> 列表 α -> 列表 (Sym α n)
-/
protected def sym : (n : Nat) -> List α -> List (Sym α n)
  | 0, _ => [.nil]
  | _, [] => []
  | n + 1, x :: xs => ((x :: xs).sym n |>.map fun p => x ::ₛ p) ++ xs.sym (n + 1)

variable {xs ys : List α} {n : Nat}

/--
theorem `sym_one_eq` / 定理 `sym_one_eq`

English:
theorem sym_one_eq
  statement: xs.sym 1 = xs.map (· ::ₛ .nil)
  proof: by
  induction xs with
  | nil => simp only [List.sym, Nat.succ_eq_add_one, Nat.reduceAdd, map_nil]
  | cons x xs ih =>
    rw [map_cons]; rw [← ih]; rw [List.sym]; rw [List.sym]; rw [map_singleton]; rw [singleton_append]

中文:
定理 sym_one_eq
  结论: xs.sym 1 = xs.map (· ::ₛ .nil)
  证明: by
  induction xs with
  | nil => simp only [List.sym, Nat.succ_eq_add_one, Nat.reduceAdd, map_nil]
  | cons x xs ih =>
    rw [map_cons]; rw [← ih]; rw [List.sym]; rw [List.sym]; rw [map_singleton]; rw [singleton_append]

Depends on / 依赖: List.sym, Nat.reduceAdd, Nat.succ_eq_add_one, map_cons, map_nil, map_singleton, reduceAdd, singleton_append, succ_eq_add_one
-/
theorem sym_one_eq : xs.sym 1 = xs.map (· ::ₛ .nil) := by
  induction xs with
  | nil => simp only [List.sym, Nat.succ_eq_add_one, Nat.reduceAdd, map_nil]
  | cons x xs ih =>
    rw [map_cons]; rw [← ih]; rw [List.sym]; rw [List.sym]; rw [map_singleton]; rw [singleton_append]

/--
theorem `sym2_eq_sym_two` / 定理 `sym2_eq_sym_two`

English:
theorem sym2_eq_sym_two
  statement: xs.sym2.map (Sym2.equivSym α) = xs.sym 2
  proof: by
  induction xs with
  | nil => simp only [List.sym, map_eq_nil_iff, sym2_eq_nil_iff]
  | cons x xs ih =>
    rw [List.sym]; rw [← ih]; rw [sym_one_eq]; rw [map_map]; rw [List.sym2]; rw [map_append]; rw [map_map]
    rfl

中文:
定理 sym2_eq_sym_two
  结论: xs.sym2.map (Sym2.equivSym α) = xs.sym 2
  证明: by
  induction xs with
  | nil => simp only [List.sym, map_eq_nil_iff, sym2_eq_nil_iff]
  | cons x xs ih =>
    rw [List.sym]; rw [← ih]; rw [sym_one_eq]; rw [map_map]; rw [List.sym2]; rw [map_append]; rw [map_map]
    rfl

Depends on / 依赖: List.sym, List.sym2, map_append, map_eq_nil_iff, map_map, sym2_eq_nil_iff, sym_one_eq
-/
theorem sym2_eq_sym_two : xs.sym2.map (Sym2.equivSym α) = xs.sym 2 := by
  induction xs with
  | nil => simp only [List.sym, map_eq_nil_iff, sym2_eq_nil_iff]
  | cons x xs ih =>
    rw [List.sym]; rw [← ih]; rw [sym_one_eq]; rw [map_map]; rw [List.sym2]; rw [map_append]; rw [map_map]
    rfl

/--
theorem `sym_map` / 定理 `sym_map`

English:
theorem sym_map
  given: {β : Type*} (f : α -> β) (n : Nat) (xs : List α)
  proof: match n, xs with
  | 0, _ => by simp only [List.sym]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [map_cons]; rw [List.sym]; rw [← map_cons]; rw [sym_map f n (x :: xs)]; rw [sym_map f (n + 1) xs]
    simp only [map_map, List.sym, map_append, append_cancel_right_eq]
    co

中文:
定理 sym_map
  条件: {β : 类型} (f : α -> β) (n : 自然数) (xs : 列表 α)
  证明: match n, xs with
  | 0, _ => by simp only [List.sym]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [map_cons]; rw [List.sym]; rw [← map_cons]; rw [sym_map f n (x :: xs)]; rw [sym_map f (n + 1) xs]
    simp only [map_map, List.sym, map_append, append_cancel_right_eq]
    co

Depends on / 依赖: Function, Function.comp_apply, List.sym, Sym.map_cons, append_cancel_right_eq, comp_apply, map_append, map_cons, map_map, sym_map
-/
theorem sym_map {β : Type*} (f : α -> β) (n : Nat) (xs : List α) :
    (xs.map f).sym n = (xs.sym n).map (Sym.map f) :=
  match n, xs with
  | 0, _ => by simp only [List.sym]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [map_cons]; rw [List.sym]; rw [← map_cons]; rw [sym_map f n (x :: xs)]; rw [sym_map f (n + 1) xs]
    simp only [map_map, List.sym, map_append, append_cancel_right_eq]
    congr
    ext s
    simp only [Function.comp_apply, Sym.map_cons]

/--
theorem `Sublist.sym` / 定理 `Sublist.sym`

English:
theorem Sublist.sym
  given: (n : Nat) {xs ys : List α} (h : xs <+ ys)
  statement: xs.sym n <+ ys.sym n
  proof: match n, h with
  | 0, _ => by simp [List.sym]
  | n + 1, .slnil => by simp only [refl]
  | n + 1, .cons a h => by
    rw [List.sym]; rw [← nil_append (List.sym (n + 1) xs)]
    apply Sublist.append (nil_sublist _)
    exact h.sym (n + 1)
  | n + 1, .cons_cons a h => by
    rw [List.sym]; rw [List.s

中文:
定理 子表.sym
  条件: (n : 自然数) {xs ys : 列表 α} (h : xs <+ ys)
  结论: xs.sym n <+ ys.sym n
  证明: match n, h with
  | 0, _ => by simp [List.sym]
  | n + 1, .slnil => by simp only [refl]
  | n + 1, .cons a h => by
    rw [List.sym]; rw [← nil_append (List.sym (n + 1) xs)]
    apply Sublist.append (nil_sublist _)
    exact h.sym (n + 1)
  | n + 1, .cons_cons a h => by
    rw [List.sym]; rw [List.s
-/
protected theorem Sublist.sym (n : Nat) {xs ys : List α} (h : xs <+ ys) : xs.sym n <+ ys.sym n :=
  match n, h with
  | 0, _ => by simp [List.sym]
  | n + 1, .slnil => by simp only [refl]
  | n + 1, .cons a h => by
    rw [List.sym]; rw [← nil_append (List.sym (n + 1) xs)]
    apply Sublist.append (nil_sublist _)
    exact h.sym (n + 1)
  | n + 1, .cons_cons a h => by
    rw [List.sym]; rw [List.sym]
    apply Sublist.append
    · exact ((cons_cons a h).sym n).map _
    · exact h.sym (n + 1)

/--
theorem `sym_sublist_sym_cons` / 定理 `sym_sublist_sym_cons`

English:
theorem sym_sublist_sym_cons
  given: {a : α}
  statement: xs.sym n <+ (a :: xs).sym n
  proof: (sublist_cons_self a xs).sym n

中文:
定理 sym_sublist_sym_cons
  条件: {a : α}
  结论: xs.sym n <+ (a :: xs).sym n
  证明: (sublist_cons_self a xs).sym n

Depends on / 依赖: sublist_cons_self
-/
theorem sym_sublist_sym_cons {a : α} : xs.sym n <+ (a :: xs).sym n :=
  (sublist_cons_self a xs).sym n

/--
theorem `mem_of_mem_of_mem_sym` / 定理 `mem_of_mem_of_mem_sym`

English:
theorem mem_of_mem_of_mem_sym
  statement: {n : Nat} {xs : List α} {a : α} {z : Sym α n}
  proof: match n, xs with
  | 0, xs => by
    cases Sym.eq_nil_of_card_zero z
    simp at ha
  | n + 1, [] => by simp [List.sym] at hz
  | n + 1, x :: xs => by
    rw [List.sym]; rw [mem_append]; rw [mem_map] at hz
    obtain ⟨z, hz, rfl⟩ | hz := hz
    · rw [Sym.mem_cons] at ha
      obtain rfl | ha := ha
 

中文:
定理 mem_of_mem_of_mem_sym
  结论: {n : 自然数} {xs : 列表 α} {a : α} {z : Sym α n}
  证明: match n, xs with
  | 0, xs => by
    cases Sym.eq_nil_of_card_zero z
    simp at ha
  | n + 1, [] => by simp [List.sym] at hz
  | n + 1, x :: xs => by
    rw [List.sym]; rw [mem_append]; rw [mem_map] at hz
    obtain ⟨z, hz, rfl⟩ | hz := hz
    · rw [Sym.mem_cons] at ha
      obtain rfl | ha := ha
 

Depends on / 依赖: List.sym, Sym.eq_nil_of_card_zero, Sym.mem_cons, eq_nil_of_card_zero, mem_append, mem_cons, mem_map, mem_of_mem_of_mem_sym
-/
theorem mem_of_mem_of_mem_sym {n : Nat} {xs : List α} {a : α} {z : Sym α n}
    (ha : a in z) (hz : z in xs.sym n) : a in xs :=
  match n, xs with
  | 0, xs => by
    cases Sym.eq_nil_of_card_zero z
    simp at ha
  | n + 1, [] => by simp [List.sym] at hz
  | n + 1, x :: xs => by
    rw [List.sym]; rw [mem_append]; rw [mem_map] at hz
    obtain ⟨z, hz, rfl⟩ | hz := hz
    · rw [Sym.mem_cons] at ha
      obtain rfl | ha := ha
      · simp
      · exact mem_of_mem_of_mem_sym ha hz
    · rw [mem_cons]
      right
      exact mem_of_mem_of_mem_sym ha hz

/--
theorem `first_mem_of_cons_mem_sym` / 定理 `first_mem_of_cons_mem_sym`

English:
theorem first_mem_of_cons_mem_sym
  statement: {xs : List α} {n : Nat} {a : α} {z : Sym α n}
  proof: mem_of_mem_of_mem_sym (Sym.mem_cons_self a z) h

中文:
定理 first_mem_of_cons_mem_sym
  结论: {xs : 列表 α} {n : 自然数} {a : α} {z : Sym α n}
  证明: mem_of_mem_of_mem_sym (Sym.mem_cons_self a z) h

Depends on / 依赖: Sym.mem_cons_self, mem_cons_self, mem_of_mem_of_mem_sym
-/
theorem first_mem_of_cons_mem_sym {xs : List α} {n : Nat} {a : α} {z : Sym α n}
    (h : a ::ₛ z in xs.sym (n + 1)) : a in xs :=
  mem_of_mem_of_mem_sym (Sym.mem_cons_self a z) h

/--
theorem `Nodup.sym` / 定理 `Nodup.sym`

English:
theorem Nodup.sym
  given: (n : Nat) {xs : List α} (h : xs.Nodup)
  statement: (xs.sym n).Nodup
  proof: match n, xs with
  | 0, _ => by simp [List.sym]
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]
    refine Nodup.append (Nodup.map ?inj (Nodup.sym n h)) (Nodup.sym (n + 1) h.of_cons) ?disj
    case inj =>
      intro z z'
      simp
    case disj =>
      intro z hz hz

中文:
定理 Nodup.sym
  条件: (n : 自然数) {xs : 列表 α} (h : xs.Nodup)
  结论: (xs.sym n).Nodup
  证明: match n, xs with
  | 0, _ => by simp [List.sym]
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]
    refine Nodup.append (Nodup.map ?inj (Nodup.sym n h)) (Nodup.sym (n + 1) h.of_cons) ?disj
    case inj =>
      intro z z'
      simp
    case disj =>
      intro z hz hz
-/
protected theorem Nodup.sym (n : Nat) {xs : List α} (h : xs.Nodup) : (xs.sym n).Nodup :=
  match n, xs with
  | 0, _ => by simp [List.sym]
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]
    refine Nodup.append (Nodup.map ?inj (Nodup.sym n h)) (Nodup.sym (n + 1) h.of_cons) ?disj
    case inj =>
      intro z z'
      simp
    case disj =>
      intro z hz hz'
      rw [mem_map] at hz
      obtain ⟨z, _hz, rfl⟩ := hz
      have := first_mem_of_cons_mem_sym hz'
      simp only [nodup_cons, this, not_true_eq_false, false_and] at h

/--
theorem `length_sym` / 定理 `length_sym`

English:
theorem length_sym
  given: {n : Nat} {xs : List α}
  proof: match n, xs with
  | 0, _ => by rw [List.sym, Nat.multichoose]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]; rw [length_append]; rw [length_map]; rw [length_cons]
    rw [@length_sym n (x :: xs)]; rw [@length_sym (n + 1) xs]
    rw [Nat.multichoose_succ_succ]; 

中文:
定理 length_sym
  条件: {n : 自然数} {xs : 列表 α}
  证明: match n, xs with
  | 0, _ => by rw [List.sym, Nat.multichoose]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]; rw [length_append]; rw [length_map]; rw [length_cons]
    rw [@length_sym n (x :: xs)]; rw [@length_sym (n + 1) xs]
    rw [Nat.multichoose_succ_succ]; 

Depends on / 依赖: List.sym, Nat.multichoose, Nat.multichoose_succ_succ, add_comm, length_append, length_cons, length_map, length_sym, multichoose, multichoose_succ_succ
-/
theorem length_sym {n : Nat} {xs : List α} :
    (xs.sym n).length = Nat.multichoose xs.length n :=
  match n, xs with
  | 0, _ => by rw [List.sym, Nat.multichoose]; rfl
  | n + 1, [] => by simp [List.sym]
  | n + 1, x :: xs => by
    rw [List.sym]; rw [length_append]; rw [length_map]; rw [length_cons]
    rw [@length_sym n (x :: xs)]; rw [@length_sym (n + 1) xs]
    rw [Nat.multichoose_succ_succ]; rw [length_cons]; rw [add_comm]

end Sym

end List
