/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Kim Morrison, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Nat.Range
public import Mathlib.Data.Set.Finite.Basic

/-!
# Counting on ℕ

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/

@[expose] public section

assert_not_imported Mathlib.Dynamics.FixedPoints.Basic
assert_not_exists Ring

open Finset

namespace Nat

variable (p : Nat -> Prop)

section Count

variable [DecidablePred p]

/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: (n : Nat)
  body: (List.range n).countP p

@[simp, grind =]

中文:
定义 count
  签名: (n : 自然数)
  定义体: (List.range n).countP p

@[simp, grind =]

Depends on / 依赖: List.range, countP
-/
def count (n : Nat) : Nat :=
  (List.range n).countP p

@[simp, grind =]
/--
theorem `count_zero` / 定理 `count_zero`

English:
theorem count_zero
  statement: count p 0 = 0
  proof: by simp [count]

中文:
定理 count_zero
  结论: count p 0 = 0
  证明: by simp [count]
-/
theorem count_zero : count p 0 = 0 := by simp [count]

/-- A fintype instance for the set relevant to `Nat.count`. Locally an instance in scope `count` -/
@[instance_reducible]
/--
Definition of `CountSet.fintype` / `CountSet.fintype` 的定义

English:
definition CountSet.fintype
  signature: (n : Nat)
  body: Fintype.subtype {x in range n | p x} by simp

scoped[Count] attribute [instance] Nat.CountSet.fintype

中文:
定义 CountSet.fintype
  签名: (n : 自然数)
  定义体: Fintype.subtype {x in range n | p x} by simp

scoped[Count] attribute [instance] Nat.CountSet.fintype

Depends on / 依赖: Fintype, Fintype.subtype, subtype
-/
def CountSet.fintype (n : Nat) : Fintype { i // i < n ∧ p i } :=
Fintype.subtype {x in range n | p x} by simp

scoped[Count] attribute [instance] Nat.CountSet.fintype

open Count

/--
theorem `count_eq_card_filter_range` / 定理 `count_eq_card_filter_range`

English:
theorem count_eq_card_filter_range
  given: (n : Nat)
  statement: count p n = #{x in range n | p x}
  proof: by
  rw [count]; rw [List.countP_eq_length_filter]
  rfl

中文:
定理 count_eq_card_filter_range
  条件: (n : 自然数)
  结论: count p n = #{x in range n | p x}
  证明: by
  rw [count]; rw [List.countP_eq_length_filter]
  rfl

Depends on / 依赖: List.countP_eq_length_filter, countP_eq_length_filter
-/
theorem count_eq_card_filter_range (n : Nat) : count p n = #{x in range n | p x} := by
  rw [count]; rw [List.countP_eq_length_filter]
  rfl

/--
theorem `count_eq_card_fintype` / 定理 `count_eq_card_fintype`

English:
theorem count_eq_card_fintype
  given: (n : Nat)
  statement: count p n = Fintype.card { k : Nat // k < n ∧ p k }
  proof: by
  rw [count_eq_card_filter_range]; rw [Fintype.card_of_subtype]
  simp

中文:
定理 count_eq_card_fintype
  条件: (n : 自然数)
  结论: count p n = Fintype.card { k : 自然数 // k < n ∧ p k }
  证明: by
  rw [count_eq_card_filter_range]; rw [Fintype.card_of_subtype]
  simp

Depends on / 依赖: Fintype, Fintype.card_of_subtype, card_of_subtype, count_eq_card_filter_range
-/
theorem count_eq_card_fintype (n : Nat) : count p n = Fintype.card { k : Nat // k < n ∧ p k } := by
  rw [count_eq_card_filter_range]; rw [Fintype.card_of_subtype]
  simp

/--
theorem `count_le` / 定理 `count_le`

English:
theorem count_le
  given: {n : Nat}
  statement: count p n <= n
  proof: by
  rw [count_eq_card_filter_range]
  exact (card_filter_le _ _).trans_eq (card_range _)

@[grind =]

中文:
定理 count_le
  条件: {n : 自然数}
  结论: count p n <= n
  证明: by
  rw [count_eq_card_filter_range]
  exact (card_filter_le _ _).trans_eq (card_range _)

@[grind =]

Depends on / 依赖: card_filter_le, card_range, count_eq_card_filter_range, trans_eq
-/
theorem count_le {n : Nat} : count p n <= n := by
  rw [count_eq_card_filter_range]
  exact (card_filter_le _ _).trans_eq (card_range _)

@[grind =]
/--
theorem `count_succ` / 定理 `count_succ`

English:
theorem count_succ
  given: (n : Nat)
  statement: count p (n + 1) = count p n + if p n then 1 else 0
  proof: by
  grind [count, List.range_succ]

@[gcongr, mono]

中文:
定理 count_succ
  条件: (n : 自然数)
  结论: count p (n + 1) = count p n + if p n then 1 else 0
  证明: by
  grind [count, List.range_succ]

@[gcongr, mono]

Depends on / 依赖: List.range_succ, range_succ
-/
theorem count_succ (n : Nat) : count p (n + 1) = count p n + if p n then 1 else 0 := by
  grind [count, List.range_succ]

@[gcongr, mono]
/--
theorem `count_monotone` / 定理 `count_monotone`

English:
theorem count_monotone
  statement: Monotone (count p)
  proof: monotone_nat_of_le_succ (by grind)

中文:
定理 count_monotone
  结论: Monotone (count p)
  证明: monotone_nat_of_le_succ (by grind)

Depends on / 依赖: monotone_nat_of_le_succ
-/
theorem count_monotone : Monotone (count p) :=
  monotone_nat_of_le_succ (by grind)

/--
theorem `count_add` / 定理 `count_add`

English:
theorem count_add
  given: (a b : Nat)
  statement: count p (a + b) = count p a + count (fun k => p (a + k)) b
  proof: by
  simp [count, List.range_add, Function.comp_def]

中文:
定理 count_add
  条件: (a b : 自然数)
  结论: count p (a + b) = count p a + count (fun k => p (a + k)) b
  证明: by
  simp [count, List.range_add, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, List.range_add, comp_def, range_add
-/
theorem count_add (a b : Nat) : count p (a + b) = count p a + count (fun k => p (a + k)) b := by
  simp [count, List.range_add, Function.comp_def]

/--
theorem `count_add'` / 定理 `count_add'`

English:
theorem count_add'
  given: (a b : Nat)
  statement: count p (a + b) = count (fun k => p (k + b)) a + count p b
  proof: by
  rw [add_comm]; rw [count_add]; rw [add_comm]
  simp_rw [add_comm b]

中文:
定理 count_add'
  条件: (a b : 自然数)
  结论: count p (a + b) = count (fun k => p (k + b)) a + count p b
  证明: by
  rw [add_comm]; rw [count_add]; rw [add_comm]
  simp_rw [add_comm b]

Depends on / 依赖: add_comm, count_add, simp_rw
-/
theorem count_add' (a b : Nat) : count p (a + b) = count (fun k => p (k + b)) a + count p b := by
  rw [add_comm]; rw [count_add]; rw [add_comm]
  simp_rw [add_comm b]

/--
theorem `count_one` / 定理 `count_one`

English:
theorem count_one
  statement: count p 1 = if p 0 then 1 else 0
  proof: by simp [count_succ]

中文:
定理 count_one
  结论: count p 1 = if p 0 then 1 else 0
  证明: by simp [count_succ]

Depends on / 依赖: count_succ
-/
theorem count_one : count p 1 = if p 0 then 1 else 0 := by simp [count_succ]

/--
theorem `count_succ'` / 定理 `count_succ'`

English:
theorem count_succ'
  given: (n : Nat)
  proof: by
  rw [count_add']; rw [count_one]

中文:
定理 count_succ'
  条件: (n : 自然数)
  证明: by
  rw [count_add']; rw [count_one]

Depends on / 依赖: count_add, count_one
-/
theorem count_succ' (n : Nat) :
    count p (n + 1) = count (fun k => p (k + 1)) n + if p 0 then 1 else 0 := by
  rw [count_add']; rw [count_one]

variable {p}

@[simp]
/--
theorem `count_lt_count_succ_iff` / 定理 `count_lt_count_succ_iff`

English:
theorem count_lt_count_succ_iff
  given: {n : Nat}
  statement: count p n < count p (n + 1) ↔ p n
  proof: by grind

中文:
定理 count_lt_count_succ_iff
  条件: {n : 自然数}
  结论: count p n < count p (n + 1) ↔ p n
  证明: by grind
-/
theorem count_lt_count_succ_iff {n : Nat} : count p n < count p (n + 1) ↔ p n := by grind

/--
theorem `count_succ_eq_succ_count_iff` / 定理 `count_succ_eq_succ_count_iff`

English:
theorem count_succ_eq_succ_count_iff
  given: {n : Nat}
  statement: count p (n + 1) = count p n + 1 ↔ p n
  proof: by grind

中文:
定理 count_succ_eq_succ_count_iff
  条件: {n : 自然数}
  结论: count p (n + 1) = count p n + 1 ↔ p n
  证明: by grind
-/
theorem count_succ_eq_succ_count_iff {n : Nat} : count p (n + 1) = count p n + 1 ↔ p n := by grind

/--
theorem `count_succ_eq_count_iff` / 定理 `count_succ_eq_count_iff`

English:
theorem count_succ_eq_count_iff
  given: {n : Nat}
  statement: count p (n + 1) = count p n ↔ ¬p n
  proof: by grind

alias ⟨_, count_succ_eq_succ_count⟩ := count_succ_eq_succ_count_iff

alias ⟨_, count_succ_eq_count⟩ := count_succ_eq_count_iff

中文:
定理 count_succ_eq_count_iff
  条件: {n : 自然数}
  结论: count p (n + 1) = count p n ↔ ¬p n
  证明: by grind

alias ⟨_, count_succ_eq_succ_count⟩ := count_succ_eq_succ_count_iff

alias ⟨_, count_succ_eq_count⟩ := count_succ_eq_count_iff
-/
theorem count_succ_eq_count_iff {n : Nat} : count p (n + 1) = count p n ↔ ¬p n := by grind

alias ⟨_, count_succ_eq_succ_count⟩ := count_succ_eq_succ_count_iff

alias ⟨_, count_succ_eq_count⟩ := count_succ_eq_count_iff

/--
theorem `lt_of_count_lt_count` / 定理 `lt_of_count_lt_count`

English:
theorem lt_of_count_lt_count
  given: {a b : Nat} (h : count p a < count p b)
  statement: a < b
  proof: (count_monotone p).reflect_lt h

中文:
定理 lt_of_count_lt_count
  条件: {a b : 自然数} (h : count p a < count p b)
  结论: a < b
  证明: (count_monotone p).reflect_lt h

Depends on / 依赖: count_monotone, reflect_lt
-/
theorem lt_of_count_lt_count {a b : Nat} (h : count p a < count p b) : a < b :=
  (count_monotone p).reflect_lt h

/--
theorem `count_strict_mono` / 定理 `count_strict_mono`

English:
theorem count_strict_mono
  given: {m n : Nat} (hm : p m) (hmn : m < n)
  statement: count p m < count p n
  proof: (count_lt_count_succ_iff.2 hm).trans_le count_monotone _ (Nat.succ_le_iff.2 hmn)

中文:
定理 count_strict_mono
  条件: {m n : 自然数} (hm : p m) (hmn : m < n)
  结论: count p m < count p n
  证明: (count_lt_count_succ_iff.2 hm).trans_le count_monotone _ (Nat.succ_le_iff.2 hmn)

Depends on / 依赖: Nat.succ_le_iff, count_lt_count_succ_iff, count_monotone, succ_le_iff, trans_le
-/
theorem count_strict_mono {m n : Nat} (hm : p m) (hmn : m < n) : count p m < count p n :=
(count_lt_count_succ_iff.2 hm).trans_le count_monotone _ (Nat.succ_le_iff.2 hmn)

/--
theorem `count_injective` / 定理 `count_injective`

English:
theorem count_injective
  given: {m n : Nat} (hm : p m) (hn : p n) (heq : count p m = count p n)
  statement: m = n
  proof: by
  by_contra h : m != n
  wlog hmn : m < n
  · exact this hn hm heq.symm h.symm (by grind)
  · simpa [heq] using count_strict_mono hm hmn

中文:
定理 count_injective
  条件: {m n : 自然数} (hm : p m) (hn : p n) (heq : count p m = count p n)
  结论: m = n
  证明: by
  by_contra h : m != n
  wlog hmn : m < n
  · exact this hn hm heq.symm h.symm (by grind)
  · simpa [heq] using count_strict_mono hm hmn

Depends on / 依赖: count_strict_mono, h.symm, heq.symm
-/
theorem count_injective {m n : Nat} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n := by
  by_contra h : m != n
  wlog hmn : m < n
  · exact this hn hm heq.symm h.symm (by grind)
  · simpa [heq] using count_strict_mono hm hmn

/--
theorem `count_le_card` / 定理 `count_le_card`

English:
theorem count_le_card
  given: (hp : (Set.ofPred p).Finite) (n : Nat)
  statement: count p n <= #hp.toFinset
  proof: by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx => hp.mem_toFinset.2 (mem_filter.1 hx).2

中文:
定理 count_le_card
  条件: (hp : (Set.ofPred p).Finite) (n : 自然数)
  结论: count p n <= #hp.toFinset
  证明: by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx => hp.mem_toFinset.2 (mem_filter.1 hx).2

Depends on / 依赖: Finset, Finset.card_mono, card_mono, count_eq_card_filter_range, hp.mem_toFinset, mem_filter, mem_toFinset
-/
theorem count_le_card (hp : (Set.ofPred p).Finite) (n : Nat) : count p n <= #hp.toFinset := by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx => hp.mem_toFinset.2 (mem_filter.1 hx).2

/--
theorem `count_lt_card` / 定理 `count_lt_card`

English:
theorem count_lt_card
  given: {n : Nat} (hp : (Set.ofPred p).Finite) (hpn : p n)
  statement: count p n < #hp.toFinset
  proof: (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)

中文:
定理 count_lt_card
  条件: {n : 自然数} (hp : (Set.ofPred p).Finite) (hpn : p n)
  结论: count p n < #hp.toFinset
  证明: (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)

Depends on / 依赖: count_le_card, count_lt_count_succ_iff, trans_le
-/
theorem count_lt_card {n : Nat} (hp : (Set.ofPred p).Finite) (hpn : p n) : count p n < #hp.toFinset :=
  (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)

/--
theorem `count_iff_forall` / 定理 `count_iff_forall`

English:
theorem count_iff_forall
  given: {n : Nat}
  statement: count p n = n ↔ forall n' < n, p n'
  proof: by
  simpa [count_eq_card_filter_range, card_range, mem_range] using
    card_filter_eq_iff (p := p) (s := range n)

alias ⟨_, count_of_forall⟩ := count_iff_forall

中文:
定理 count_iff_forall
  条件: {n : 自然数}
  结论: count p n = n ↔ 对任意 n' < n, p n'
  证明: by
  simpa [count_eq_card_filter_range, card_range, mem_range] using
    card_filter_eq_iff (p := p) (s := range n)

alias ⟨_, count_of_forall⟩ := count_iff_forall

Depends on / 依赖: card_filter_eq_iff, card_range, count_eq_card_filter_range, mem_range
-/
theorem count_iff_forall {n : Nat} : count p n = n ↔ forall n' < n, p n' := by
  simpa [count_eq_card_filter_range, card_range, mem_range] using
    card_filter_eq_iff (p := p) (s := range n)

alias ⟨_, count_of_forall⟩ := count_iff_forall

/--
theorem `count_true` / 定理 `count_true`

English:
theorem count_true
  given: (n : Nat)
  statement: count (fun _ => True) n = n
  proof: count_of_forall fun _ _ => trivial

中文:
定理 count_true
  条件: (n : 自然数)
  结论: count (fun _ => True) n = n
  证明: count_of_forall fun _ _ => trivial
-/
@[simp] theorem count_true (n : Nat) : count (fun _ => True) n = n := count_of_forall fun _ _ => trivial

/--
theorem `count_iff_forall_not` / 定理 `count_iff_forall_not`

English:
theorem count_iff_forall_not
  given: {n : Nat}
  statement: count p n = 0 ↔ forall m < n, ¬p m
  proof: by
  simp [count_eq_card_filter_range]

alias ⟨_, count_of_forall_not⟩ := count_iff_forall_not

中文:
定理 count_iff_forall_not
  条件: {n : 自然数}
  结论: count p n = 0 ↔ 对任意 m < n, ¬p m
  证明: by
  simp [count_eq_card_filter_range]

alias ⟨_, count_of_forall_not⟩ := count_iff_forall_not

Depends on / 依赖: count_eq_card_filter_range
-/
theorem count_iff_forall_not {n : Nat} : count p n = 0 ↔ forall m < n, ¬p m := by
  simp [count_eq_card_filter_range]

alias ⟨_, count_of_forall_not⟩ := count_iff_forall_not

/--
theorem `count_ne_iff_exists` / 定理 `count_ne_iff_exists`

English:
theorem count_ne_iff_exists
  given: {n : Nat}
  statement: n.count p != 0 ↔ exists m < n, p m
  proof: by
  simp [Nat.count_iff_forall_not]

中文:
定理 count_ne_iff_exists
  条件: {n : 自然数}
  结论: n.count p != 0 ↔ 存在 m < n, p m
  证明: by
  simp [Nat.count_iff_forall_not]

Depends on / 依赖: Nat.count_iff_forall_not, count_iff_forall_not
-/
theorem count_ne_iff_exists {n : Nat} : n.count p != 0 ↔ exists m < n, p m := by
  simp [Nat.count_iff_forall_not]

/--
theorem `count_false` / 定理 `count_false`

English:
theorem count_false
  given: (n : Nat)
  statement: count (fun _ => False) n = 0
  proof: count_of_forall_not fun _ _ => id

中文:
定理 count_false
  条件: (n : 自然数)
  结论: count (fun _ => False) n = 0
  证明: count_of_forall_not fun _ _ => id
-/
@[simp] theorem count_false (n : Nat) : count (fun _ => False) n = 0 :=
  count_of_forall_not fun _ _ => id

/--
lemma `exists_of_count_lt_count` / 引理 `exists_of_count_lt_count`

English:
lemma exists_of_count_lt_count
  given: {a b : Nat} (h : a.count p < b.count p)
  statement: exists x in Set.Ico a b, p x
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_count_lt_count h)
  rw [add_assoc]; rw [count_add]; rw [Nat.lt_add_right_iff_pos] at h
  obtain ⟨t, ht, hp⟩ := count_ne_iff_exists.mp h.ne'
  simp_rw [Set.mem_Ico]
  exact ⟨a + t, by grind⟩

中文:
引理 exists_of_count_lt_count
  条件: {a b : 自然数} (h : a.count p < b.count p)
  结论: 存在 x in Set.Ico a b, p x
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_count_lt_count h)
  rw [add_assoc]; rw [count_add]; rw [Nat.lt_add_right_iff_pos] at h
  obtain ⟨t, ht, hp⟩ := count_ne_iff_exists.mp h.ne'
  simp_rw [Set.mem_Ico]
  exact ⟨a + t, by grind⟩

Depends on / 依赖: Nat.exists_eq_add_of_lt, Nat.lt_add_right_iff_pos, Set.mem_Ico, add_assoc, count_add, count_ne_iff_exists, count_ne_iff_exists.mp, exists_eq_add_of_lt, h.ne, lt_add_right_iff_pos, lt_of_count_lt_count, mem_Ico, simp_rw
-/
lemma exists_of_count_lt_count {a b : Nat} (h : a.count p < b.count p) : exists x in Set.Ico a b, p x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_count_lt_count h)
  rw [add_assoc]; rw [count_add]; rw [Nat.lt_add_right_iff_pos] at h
  obtain ⟨t, ht, hp⟩ := count_ne_iff_exists.mp h.ne'
  simp_rw [Set.mem_Ico]
  exact ⟨a + t, by grind⟩

variable {q : Nat -> Prop}
variable [DecidablePred q]

@[gcongr]
/--
theorem `count_mono_left` / 定理 `count_mono_left`

English:
theorem count_mono_left
  given: {n : Nat} (hpq : forall k < n, p k -> q k)
  statement: count p n <= count q n
  proof: List.countP_mono_left by simpa

中文:
定理 count_mono_left
  条件: {n : 自然数} (hpq : 对任意 k < n, p k -> q k)
  结论: count p n <= count q n
  证明: List.countP_mono_left by simpa

Depends on / 依赖: List.countP_mono_left, countP_mono_left
-/
theorem count_mono_left {n : Nat} (hpq : forall k < n, p k -> q k) : count p n <= count q n :=
List.countP_mono_left by simpa

end Count

end Nat
