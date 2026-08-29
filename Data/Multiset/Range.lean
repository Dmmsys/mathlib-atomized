/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.UnionInter

/-! # `Multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/

@[expose] public section

assert_not_exists Monoid

open List Nat

namespace Multiset

-- range
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (n : Nat)
  body: List.range n

中文:
定义 range
  签名: (n : 自然数)
  定义体: List.range n

Depends on / 依赖: List.range
-/
def range (n : Nat) : Multiset Nat :=
  List.range n

/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (n : Nat)
  statement: ↑(List.range n) = range n
  proof: rfl

@[simp]

中文:
定理 coe_range
  条件: (n : 自然数)
  结论: ↑(List.range n) = range n
  证明: rfl

@[simp]
-/
theorem coe_range (n : Nat) : ↑(List.range n) = range n :=
  rfl

@[simp]
/--
theorem `range_zero` / 定理 `range_zero`

English:
theorem range_zero
  statement: range 0 = 0
  proof: rfl

@[simp]

中文:
定理 range_zero
  结论: range 0 = 0
  证明: rfl

@[simp]
-/
theorem range_zero : range 0 = 0 :=
  rfl

@[simp]
/--
theorem `range_succ` / 定理 `range_succ`

English:
theorem range_succ
  given: (n : Nat)
  statement: range (succ n) = n ::ₘ range n
  proof: by
  rw [range]; rw [List.range_succ]; rw [← coe_add]; rw [Multiset.add_comm]; rw [range]; rw [coe_singleton]; rw [singleton_add]

@[simp]

中文:
定理 range_succ
  条件: (n : 自然数)
  结论: range (succ n) = n ::ₘ range n
  证明: by
  rw [range]; rw [List.range_succ]; rw [← coe_add]; rw [Multiset.add_comm]; rw [range]; rw [coe_singleton]; rw [singleton_add]

@[simp]

Depends on / 依赖: List.range_succ, Multiset, Multiset.add_comm, add_comm, coe_add, coe_singleton, range_succ, singleton_add
-/
theorem range_succ (n : Nat) : range (succ n) = n ::ₘ range n := by
  rw [range]; rw [List.range_succ]; rw [← coe_add]; rw [Multiset.add_comm]; rw [range]; rw [coe_singleton]; rw [singleton_add]

@[simp]
/--
theorem `card_range` / 定理 `card_range`

English:
theorem card_range
  given: (n : Nat)
  statement: card (range n) = n
  proof: length_range

中文:
定理 card_range
  条件: (n : 自然数)
  结论: card (range n) = n
  证明: length_range

Depends on / 依赖: length_range
-/
theorem card_range (n : Nat) : card (range n) = n :=
  length_range

/--
theorem `range_subset` / 定理 `range_subset`

English:
theorem range_subset
  given: {m n : Nat}
  statement: range m subseteq range n ↔ m <= n
  proof: List.range_subset

@[simp]

中文:
定理 range_subset
  条件: {m n : 自然数}
  结论: range m subseteq range n ↔ m <= n
  证明: List.range_subset

@[simp]

Depends on / 依赖: List.range_subset, head_terminates_of_head_tail_terminates, range_subset
-/
theorem range_subset {m n : Nat} : range m subseteq range n ↔ m <= n :=
  List.range_subset

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {m n : Nat}
  statement: m in range n ↔ m < n
  proof: List.mem_range

中文:
定理 mem_range
  条件: {m n : 自然数}
  结论: m in range n ↔ m < n
  证明: List.mem_range

Depends on / 依赖: List.mem_range, mem_range
-/
theorem mem_range {m n : Nat} : m in range n ↔ m < n :=
  List.mem_range

/--
theorem `notMem_range_self` / 定理 `notMem_range_self`

English:
theorem notMem_range_self
  given: {n : Nat}
  statement: n ∉ range n
  proof: List.not_mem_range_self

中文:
定理 notMem_range_self
  条件: {n : 自然数}
  结论: n ∉ range n
  证明: List.not_mem_range_self

Depends on / 依赖: List.not_mem_range_self, not_mem_range_self
-/
theorem notMem_range_self {n : Nat} : n ∉ range n :=
  List.not_mem_range_self

/--
theorem `self_mem_range_succ` / 定理 `self_mem_range_succ`

English:
theorem self_mem_range_succ
  given: (n : Nat)
  statement: n in range (n + 1)
  proof: List.self_mem_range_succ

中文:
定理 self_mem_range_succ
  条件: (n : 自然数)
  结论: n in range (n + 1)
  证明: List.self_mem_range_succ

Depends on / 依赖: List.self_mem_range_succ, self_mem_range_succ
-/
theorem self_mem_range_succ (n : Nat) : n in range (n + 1) :=
  List.self_mem_range_succ

/--
theorem `range_add` / 定理 `range_add`

English:
theorem range_add
  given: (a b : Nat)
  statement: range (a + b) = range a + (range b).map (a + ·)
  proof: congr_arg ((↑) : List Nat -> Multiset Nat) List.range_add

中文:
定理 range_add
  条件: (a b : 自然数)
  结论: range (a + b) = range a + (range b).map (a + ·)
  证明: congr_arg ((↑) : List Nat -> Multiset Nat) List.range_add

Depends on / 依赖: List.range_add, Multiset, congr_arg, range_add
-/
theorem range_add (a b : Nat) : range (a + b) = range a + (range b).map (a + ·) :=
  congr_arg ((↑) : List Nat -> Multiset Nat) List.range_add

/--
theorem `range_disjoint_map_add` / 定理 `range_disjoint_map_add`

English:
theorem range_disjoint_map_add
  given: (a : Nat) (m : Multiset Nat)
  proof: by
  rw [disjoint_left]
  intro x hxa hxb
  rw [range]; rw [mem_coe]; rw [List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (Nat.le_add_right _ _).not_gt hxa

中文:
定理 range_disjoint_map_add
  条件: (a : 自然数) (m : Multiset 自然数)
  证明: by
  rw [disjoint_left]
  intro x hxa hxb
  rw [range]; rw [mem_coe]; rw [List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (Nat.le_add_right _ _).not_gt hxa

Depends on / 依赖: List.mem_range, Nat.le_add_right, disjoint_left, le_add_right, mem_coe, mem_map, mem_range, not_gt
-/
theorem range_disjoint_map_add (a : Nat) (m : Multiset Nat) :
    Disjoint (range a) (m.map (a + ·)) := by
  rw [disjoint_left]
  intro x hxa hxb
  rw [range]; rw [mem_coe]; rw [List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (Nat.le_add_right _ _).not_gt hxa

/--
theorem `range_add_eq_union` / 定理 `range_add_eq_union`

English:
theorem range_add_eq_union
  given: (a b : Nat)
  statement: range (a + b) = range a union (range b).map (a + ·)
  proof: by
  rw [range_add]; rw [add_eq_union_iff_disjoint]
  apply range_disjoint_map_add

中文:
定理 range_add_eq_union
  条件: (a b : 自然数)
  结论: range (a + b) = range a union (range b).map (a + ·)
  证明: by
  rw [range_add]; rw [add_eq_union_iff_disjoint]
  apply range_disjoint_map_add

Depends on / 依赖: add_eq_union_iff_disjoint, range_add, range_disjoint_map_add
-/
theorem range_add_eq_union (a b : Nat) : range (a + b) = range a union (range b).map (a + ·) := by
  rw [range_add]; rw [add_eq_union_iff_disjoint]
  apply range_disjoint_map_add

section Nodup

/--
theorem `nodup_range` / 定理 `nodup_range`

English:
theorem nodup_range
  given: (n : Nat)
  statement: Nodup (range n)
  proof: List.nodup_range

中文:
定理 nodup_range
  条件: (n : 自然数)
  结论: Nodup (range n)
  证明: List.nodup_range

Depends on / 依赖: List.nodup_range, nodup_range
-/
theorem nodup_range (n : Nat) : Nodup (range n) :=
  List.nodup_range

/--
theorem `range_le` / 定理 `range_le`

English:
theorem range_le
  given: {m n : Nat}
  statement: range m <= range n ↔ m <= n
  proof: (le_iff_subset (nodup_range _)).trans range_subset

中文:
定理 range_le
  条件: {m n : 自然数}
  结论: range m <= range n ↔ m <= n
  证明: (le_iff_subset (nodup_range _)).trans range_subset

Depends on / 依赖: le_iff_subset, nodup_range, range_subset
-/
theorem range_le {m n : Nat} : range m <= range n ↔ m <= n :=
  (le_iff_subset (nodup_range _)).trans range_subset

end Nodup

end Multiset
