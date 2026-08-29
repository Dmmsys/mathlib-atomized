/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.List.Nodup

/-!
# Antidiagonals in ℕ × ℕ as lists

This file defines the antidiagonals of ℕ × ℕ as lists: the `n`-th antidiagonal is the list of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

Files `Data.Multiset.NatAntidiagonal` and `Data.Finset.NatAntidiagonal` successively turn the
`List` definition we have here into `Multiset` and `Finset`.
-/

@[expose] public section

open Function

namespace List

namespace Nat

/--
Definition of `antidiagonal` / `antidiagonal` 的定义

English:
definition antidiagonal
  signature: (n : Nat)
  body: (range (n + 1)).map fun i => (i, n - i)

中文:
定义 antidiagonal
  签名: (n : 自然数)
  定义体: (range (n + 1)).map fun i => (i, n - i)
-/
def antidiagonal (n : Nat) : List (Nat × Nat) :=
  (range (n + 1)).map fun i => (i, n - i)

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
/--
theorem `mem_antidiagonal` / 定理 `mem_antidiagonal`

English:
theorem mem_antidiagonal
  given: {n : Nat} {x : Nat × Nat}
  statement: x in antidiagonal n ↔ x.1 + x.2 = n
  proof: by
  rcases x with ⟨x, y⟩
  simp [antidiagonal]
  grind

中文:
定理 mem_antidiagonal
  条件: {n : 自然数} {x : 自然数 × 自然数}
  结论: x in antidiagonal n ↔ x.1 + x.2 = n
  证明: by
  rcases x with ⟨x, y⟩
  simp [antidiagonal]
  grind

Depends on / 依赖: antidiagonal
-/
theorem mem_antidiagonal {n : Nat} {x : Nat × Nat} : x in antidiagonal n ↔ x.1 + x.2 = n := by
  rcases x with ⟨x, y⟩
  simp [antidiagonal]
  grind

/-- The length of the antidiagonal of `n` is `n + 1`. -/
@[simp]
/--
theorem `length_antidiagonal` / 定理 `length_antidiagonal`

English:
theorem length_antidiagonal
  given: (n : Nat)
  statement: (antidiagonal n).length = n + 1
  proof: by
  rw [antidiagonal]; rw [length_map]; rw [length_range]

中文:
定理 length_antidiagonal
  条件: (n : 自然数)
  结论: (antidiagonal n).length = n + 1
  证明: by
  rw [antidiagonal]; rw [length_map]; rw [length_range]

Depends on / 依赖: antidiagonal, length_map, length_range
-/
theorem length_antidiagonal (n : Nat) : (antidiagonal n).length = n + 1 := by
  rw [antidiagonal]; rw [length_map]; rw [length_range]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
/--
theorem `antidiagonal_zero` / 定理 `antidiagonal_zero`

English:
theorem antidiagonal_zero
  statement: antidiagonal 0 = [(0, 0)]
  proof: rfl

中文:
定理 antidiagonal_zero
  结论: antidiagonal 0 = [(0, 0)]
  证明: rfl
-/
theorem antidiagonal_zero : antidiagonal 0 = [(0, 0)] :=
  rfl

/--
theorem `nodup_antidiagonal` / 定理 `nodup_antidiagonal`

English:
theorem nodup_antidiagonal
  given: (n : Nat)
  statement: Nodup (antidiagonal n)
  proof: nodup_range.map ((@LeftInverse.injective Nat (Nat × Nat) Prod.fst fun i => (i, n - i)) fun _ => rfl)

@[simp]

中文:
定理 nodup_antidiagonal
  条件: (n : 自然数)
  结论: Nodup (antidiagonal n)
  证明: nodup_range.map ((@LeftInverse.injective Nat (Nat × Nat) Prod.fst fun i => (i, n - i)) fun _ => rfl)

@[simp]

Depends on / 依赖: LeftInverse, LeftInverse.injective, Prod.fst, injective, nodup_range, nodup_range.map
-/
theorem nodup_antidiagonal (n : Nat) : Nodup (antidiagonal n) :=
  nodup_range.map ((@LeftInverse.injective Nat (Nat × Nat) Prod.fst fun i => (i, n - i)) fun _ => rfl)

@[simp]
/--
theorem `antidiagonal_succ` / 定理 `antidiagonal_succ`

English:
theorem antidiagonal_succ
  given: {n : Nat}
  proof: by
  simp only [antidiagonal, range_succ_eq_map, map_cons, Nat.add_succ_sub_one,
    Nat.add_zero, id, Nat.sub_zero, map_map, Prod.map_apply]
  apply congr rfl (congr rfl _)
  ext; simp

中文:
定理 antidiagonal_succ
  条件: {n : 自然数}
  证明: by
  simp only [antidiagonal, range_succ_eq_map, map_cons, Nat.add_succ_sub_one,
    Nat.add_zero, id, Nat.sub_zero, map_map, Prod.map_apply]
  apply congr rfl (congr rfl _)
  ext; simp

Depends on / 依赖: Nat.add_succ_sub_one, Nat.add_zero, Nat.sub_zero, Prod.map_apply, add_succ_sub_one, add_zero, antidiagonal, map_apply, map_cons, map_map, range_succ_eq_map, sub_zero
-/
theorem antidiagonal_succ {n : Nat} :
    antidiagonal (n + 1) = (0, n + 1) :: (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, range_succ_eq_map, map_cons, Nat.add_succ_sub_one,
    Nat.add_zero, id, Nat.sub_zero, map_map, Prod.map_apply]
  apply congr rfl (congr rfl _)
  ext; simp

/--
theorem `antidiagonal_succ'` / 定理 `antidiagonal_succ'`

English:
theorem antidiagonal_succ'
  given: {n : Nat}
  proof: by
  simp +contextual [antidiagonal, range_succ, Nat.le_of_lt, Nat.sub_add_comm]

中文:
定理 antidiagonal_succ'
  条件: {n : 自然数}
  证明: by
  simp +contextual [antidiagonal, range_succ, Nat.le_of_lt, Nat.sub_add_comm]

Depends on / 依赖: Nat.le_of_lt, Nat.sub_add_comm, antidiagonal, contextual, le_of_lt, range_succ, sub_add_comm
-/
theorem antidiagonal_succ' {n : Nat} :
    antidiagonal (n + 1) = (antidiagonal n).map (Prod.map id Nat.succ) ++ [(n + 1, 0)] := by
  simp +contextual [antidiagonal, range_succ, Nat.le_of_lt, Nat.sub_add_comm]

/--
theorem `antidiagonal_succ_succ'` / 定理 `antidiagonal_succ_succ'`

English:
theorem antidiagonal_succ_succ'
  given: {n : Nat}
  proof: by
  rw [antidiagonal_succ']; rw [antidiagonal_succ]
  simp

中文:
定理 antidiagonal_succ_succ'
  条件: {n : 自然数}
  证明: by
  rw [antidiagonal_succ']; rw [antidiagonal_succ]
  simp

Depends on / 依赖: antidiagonal_succ
-/
theorem antidiagonal_succ_succ' {n : Nat} :
    antidiagonal (n + 2) =
      (0, n + 2) :: (antidiagonal n).map (Prod.map Nat.succ Nat.succ) ++ [(n + 2, 0)] := by
  rw [antidiagonal_succ']; rw [antidiagonal_succ]
  simp

/--
theorem `map_swap_antidiagonal` / 定理 `map_swap_antidiagonal`

English:
theorem map_swap_antidiagonal
  given: {n : Nat}
  proof: by
  rw [antidiagonal]; rw [map_map]; rw [← List.map_reverse]; rw [range_eq_range']; rw [reverse_range']; rw [←
    range_eq_range']; rw [map_map]
  apply map_congr_left
  simp +contextual [Nat.sub_sub_self, Nat.lt_succ_iff]

中文:
定理 map_swap_antidiagonal
  条件: {n : 自然数}
  证明: by
  rw [antidiagonal]; rw [map_map]; rw [← List.map_reverse]; rw [range_eq_range']; rw [reverse_range']; rw [←
    range_eq_range']; rw [map_map]
  apply map_congr_left
  simp +contextual [Nat.sub_sub_self, Nat.lt_succ_iff]

Depends on / 依赖: List.map_reverse, Nat.lt_succ_iff, Nat.sub_sub_self, antidiagonal, contextual, lt_succ_iff, map_congr_left, map_map, map_reverse, range_eq_range, reverse_range, sub_sub_self
-/
theorem map_swap_antidiagonal {n : Nat} :
    (antidiagonal n).map Prod.swap = (antidiagonal n).reverse := by
  rw [antidiagonal]; rw [map_map]; rw [← List.map_reverse]; rw [range_eq_range']; rw [reverse_range']; rw [←
    range_eq_range']; rw [map_map]
  apply map_congr_left
  simp +contextual [Nat.sub_sub_self, Nat.lt_succ_iff]

end Nat

end List
