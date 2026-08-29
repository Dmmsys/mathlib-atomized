/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.List.NatAntidiagonal
public import Mathlib.Data.Multiset.MapFold

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `Data.List.NatAntidiagonal` and is further refined by file
`Data.Finset.NatAntidiagonal`.
-/

@[expose] public section

assert_not_exists Monoid

namespace Multiset

namespace Nat

/--
Definition of `antidiagonal` / `antidiagonal` 的定义

English:
definition antidiagonal
  signature: (n : Nat)
  body: List.Nat.antidiagonal n

中文:
定义 antidiagonal
  签名: (n : 自然数)
  定义体: List.Nat.antidiagonal n

Depends on / 依赖: List.Nat.antidiagonal, antidiagonal
-/
def antidiagonal (n : Nat) : Multiset (Nat × Nat) :=
  List.Nat.antidiagonal n

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
/--
theorem `mem_antidiagonal` / 定理 `mem_antidiagonal`

English:
theorem mem_antidiagonal
  given: {n : Nat} {x : Nat × Nat}
  statement: x in antidiagonal n ↔ x.1 + x.2 = n
  proof: by
  rw [antidiagonal]; rw [mem_coe]; rw [List.Nat.mem_antidiagonal]

中文:
定理 mem_antidiagonal
  条件: {n : 自然数} {x : 自然数 × 自然数}
  结论: x in antidiagonal n ↔ x.1 + x.2 = n
  证明: by
  rw [antidiagonal]; rw [mem_coe]; rw [List.Nat.mem_antidiagonal]

Depends on / 依赖: List.Nat.mem_antidiagonal, antidiagonal, mem_antidiagonal, mem_coe
-/
theorem mem_antidiagonal {n : Nat} {x : Nat × Nat} : x in antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal]; rw [mem_coe]; rw [List.Nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp]
/--
theorem `card_antidiagonal` / 定理 `card_antidiagonal`

English:
theorem card_antidiagonal
  given: (n : Nat)
  statement: card (antidiagonal n) = n + 1
  proof: by
  rw [antidiagonal]; rw [coe_card]; rw [List.Nat.length_antidiagonal]

中文:
定理 card_antidiagonal
  条件: (n : 自然数)
  结论: card (antidiagonal n) = n + 1
  证明: by
  rw [antidiagonal]; rw [coe_card]; rw [List.Nat.length_antidiagonal]

Depends on / 依赖: List.Nat.length_antidiagonal, antidiagonal, coe_card, length_antidiagonal
-/
theorem card_antidiagonal (n : Nat) : card (antidiagonal n) = n + 1 := by
  rw [antidiagonal]; rw [coe_card]; rw [List.Nat.length_antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
/--
theorem `antidiagonal_zero` / 定理 `antidiagonal_zero`

English:
theorem antidiagonal_zero
  statement: antidiagonal 0 = {(0, 0)}
  proof: rfl

中文:
定理 antidiagonal_zero
  结论: antidiagonal 0 = {(0, 0)}
  证明: rfl
-/
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp]
/--
theorem `nodup_antidiagonal` / 定理 `nodup_antidiagonal`

English:
theorem nodup_antidiagonal
  given: (n : Nat)
  statement: Nodup (antidiagonal n)
  proof: coe_nodup.2 List.Nat.nodup_antidiagonal n

@[simp]

中文:
定理 nodup_antidiagonal
  条件: (n : 自然数)
  结论: Nodup (antidiagonal n)
  证明: coe_nodup.2 List.Nat.nodup_antidiagonal n

@[simp]

Depends on / 依赖: List.Nat.nodup_antidiagonal, coe_nodup, nodup_antidiagonal
-/
theorem nodup_antidiagonal (n : Nat) : Nodup (antidiagonal n) :=
coe_nodup.2 List.Nat.nodup_antidiagonal n

@[simp]
/--
theorem `antidiagonal_succ` / 定理 `antidiagonal_succ`

English:
theorem antidiagonal_succ
  given: {n : Nat}
  proof: by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, map_coe, cons_coe]

中文:
定理 antidiagonal_succ
  条件: {n : 自然数}
  证明: by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, map_coe, cons_coe]

Depends on / 依赖: List.Nat.antidiagonal_succ, antidiagonal, antidiagonal_succ, cons_coe, map_coe
-/
theorem antidiagonal_succ {n : Nat} :
    antidiagonal (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, map_coe, cons_coe]

/--
theorem `antidiagonal_succ'` / 定理 `antidiagonal_succ'`

English:
theorem antidiagonal_succ'
  given: {n : Nat}
  proof: by
  rw [antidiagonal]; rw [List.Nat.antidiagonal_succ']; rw [← coe_add]; rw [Multiset.add_comm]; rw [antidiagonal]; rw [map_coe]; rw [coe_add]; rw [List.singleton_append]; rw [cons_coe]

中文:
定理 antidiagonal_succ'
  条件: {n : 自然数}
  证明: by
  rw [antidiagonal]; rw [List.Nat.antidiagonal_succ']; rw [← coe_add]; rw [Multiset.add_comm]; rw [antidiagonal]; rw [map_coe]; rw [coe_add]; rw [List.singleton_append]; rw [cons_coe]

Depends on / 依赖: List.Nat.antidiagonal_succ, List.singleton_append, Multiset, Multiset.add_comm, add_comm, antidiagonal, antidiagonal_succ, coe_add, cons_coe, map_coe, singleton_append
-/
theorem antidiagonal_succ' {n : Nat} :
    antidiagonal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ) := by
  rw [antidiagonal]; rw [List.Nat.antidiagonal_succ']; rw [← coe_add]; rw [Multiset.add_comm]; rw [antidiagonal]; rw [map_coe]; rw [coe_add]; rw [List.singleton_append]; rw [cons_coe]

/--
theorem `antidiagonal_succ_succ'` / 定理 `antidiagonal_succ_succ'`

English:
theorem antidiagonal_succ_succ'
  given: {n : Nat}
  proof: by
  rw [antidiagonal_succ]; rw [antidiagonal_succ']; rw [map_cons]; rw [map_map]; rw [Prod.map_apply]
  rfl

中文:
定理 antidiagonal_succ_succ'
  条件: {n : 自然数}
  证明: by
  rw [antidiagonal_succ]; rw [antidiagonal_succ']; rw [map_cons]; rw [map_map]; rw [Prod.map_apply]
  rfl

Depends on / 依赖: Prod.map_apply, antidiagonal_succ, map_apply, map_cons, map_map
-/
theorem antidiagonal_succ_succ' {n : Nat} :
    antidiagonal (n + 2) =
      (0, n + 2) ::ₘ (n + 2, 0) ::ₘ (antidiagonal n).map (Prod.map Nat.succ Nat.succ) := by
  rw [antidiagonal_succ]; rw [antidiagonal_succ']; rw [map_cons]; rw [map_map]; rw [Prod.map_apply]
  rfl

/--
theorem `map_swap_antidiagonal` / 定理 `map_swap_antidiagonal`

English:
theorem map_swap_antidiagonal
  given: {n : Nat}
  statement: (antidiagonal n).map Prod.swap = antidiagonal n
  proof: by
  rw [antidiagonal]; rw [map_coe]; rw [List.Nat.map_swap_antidiagonal]; rw [coe_reverse]

中文:
定理 map_swap_antidiagonal
  条件: {n : 自然数}
  结论: (antidiagonal n).map 积类型.swap = antidiagonal n
  证明: by
  rw [antidiagonal]; rw [map_coe]; rw [List.Nat.map_swap_antidiagonal]; rw [coe_reverse]

Depends on / 依赖: List.Nat.map_swap_antidiagonal, antidiagonal, coe_reverse, map_coe, map_swap_antidiagonal
-/
theorem map_swap_antidiagonal {n : Nat} : (antidiagonal n).map Prod.swap = antidiagonal n := by
  rw [antidiagonal]; rw [map_coe]; rw [List.Nat.map_swap_antidiagonal]; rw [coe_reverse]

end Nat

end Multiset
