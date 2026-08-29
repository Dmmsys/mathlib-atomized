/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Intervals in ℤ

This file defines integer ranges. `range m n` is the set of integers greater than `m` and strictly
less than `n`.

## Note

This could be unified with `Data.List.Intervals`. See the TODOs there.
-/

@[expose] public section

namespace Int

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (m n : Int)
  body: ((List.range (toNat (n - m))) : List Nat).map fun (r : Nat) => (m + r : Int)

中文:
定义 range
  签名: (m n : 整数)
  定义体: ((List.range (toNat (n - m))) : List Nat).map fun (r : Nat) => (m + r : Int)

Depends on / 依赖: List.range
-/
def range (m n : Int) : List Int :=
  ((List.range (toNat (n - m))) : List Nat).map fun (r : Nat) => (m + r : Int)

/--
theorem `mem_range_iff` / 定理 `mem_range_iff`

English:
theorem mem_range_iff
  given: {m n r : Int}
  statement: r in range m n ↔ m <= r ∧ r < n
  proof: by
  simp only [range, List.mem_map, List.mem_range, lt_toNat, lt_sub_iff_add_lt, add_comm]
  exact ⟨fun ⟨a, ha⟩ => ha.2 ▸ ⟨le_add_of_nonneg_right (Int.natCast_nonneg _), ha.1⟩,
    fun h => ⟨toNat (r - m), by simp [toNat_of_nonneg (sub_nonneg.2 h.1), h.2] ⟩⟩

中文:
定理 mem_range_iff
  条件: {m n r : 整数}
  结论: r in range m n ↔ m <= r ∧ r < n
  证明: by
  simp only [range, List.mem_map, List.mem_range, lt_toNat, lt_sub_iff_add_lt, add_comm]
  exact ⟨fun ⟨a, ha⟩ => ha.2 ▸ ⟨le_add_of_nonneg_right (Int.natCast_nonneg _), ha.1⟩,
    fun h => ⟨toNat (r - m), by simp [toNat_of_nonneg (sub_nonneg.2 h.1), h.2] ⟩⟩

Depends on / 依赖: Int.natCast_nonneg, List.mem_map, List.mem_range, add_comm, le_add_of_nonneg_right, lt_sub_iff_add_lt, lt_toNat, mem_map, mem_range, natCast_nonneg, sub_nonneg, toNat_of_nonneg
-/
theorem mem_range_iff {m n r : Int} : r in range m n ↔ m <= r ∧ r < n := by
  simp only [range, List.mem_map, List.mem_range, lt_toNat, lt_sub_iff_add_lt, add_comm]
  exact ⟨fun ⟨a, ha⟩ => ha.2 ▸ ⟨le_add_of_nonneg_right (Int.natCast_nonneg _), ha.1⟩,
    fun h => ⟨toNat (r - m), by simp [toNat_of_nonneg (sub_nonneg.2 h.1), h.2] ⟩⟩

/--
Instance `decidableLELT` / 实例 `decidableLELT`

English:
instance decidableLELT
  signature: (P : Int -> Prop) [DecidablePred P] (m n : Int)
  body: decidable_of_iff (forall r in range m n, P r) by simp only [mem_range_iff, and_imp]

中文:
实例 decidableLELT
  签名: (P : 整数 -> 命题) [DecidablePred P] (m n : 整数)
  定义体: decidable_of_iff (forall r in range m n, P r) by simp only [mem_range_iff, and_imp]

Depends on / 依赖: and_imp, decidable_of_iff, mem_range_iff
-/
instance decidableLELT (P : Int -> Prop) [DecidablePred P] (m n : Int) :
    Decidable (forall r, m <= r -> r < n -> P r) :=
decidable_of_iff (forall r in range m n, P r) by simp only [mem_range_iff, and_imp]

/--
Instance `decidableLELE` / 实例 `decidableLELE`

English:
instance decidableLELE
  signature: (P : Int -> Prop) [DecidablePred P] (m n : Int)
  body: -- Add empty type ascription, otherwise it fails to find `Decidable` instance.
decidable_of_iff (forall r in range m (n + 1), P r :) by
    simp only [mem_range_iff, and_imp, lt_add_one_iff]

中文:
实例 decidableLELE
  签名: (P : 整数 -> 命题) [DecidablePred P] (m n : 整数)
  定义体: -- Add empty type ascription, otherwise it fails to find `Decidable` instance.
decidable_of_iff (forall r in range m (n + 1), P r :) by
    simp only [mem_range_iff, and_imp, lt_add_one_iff]
-/
instance decidableLELE (P : Int -> Prop) [DecidablePred P] (m n : Int) :
    Decidable (forall r, m <= r -> r <= n -> P r) :=
  -- Add empty type ascription, otherwise it fails to find `Decidable` instance.
decidable_of_iff (forall r in range m (n + 1), P r :) by
    simp only [mem_range_iff, and_imp, lt_add_one_iff]

/--
Instance `decidableLTLT` / 实例 `decidableLTLT`

English:
instance decidableLTLT
  signature: (P : Int -> Prop) [DecidablePred P] (m n : Int)
  body: Int.decidableLELT P _ _

中文:
实例 decidableLTLT
  签名: (P : 整数 -> 命题) [DecidablePred P] (m n : 整数)
  定义体: Int.decidableLELT P _ _

Depends on / 依赖: Int.decidableLELT, decidableLELT
-/
instance decidableLTLT (P : Int -> Prop) [DecidablePred P] (m n : Int) :
    Decidable (forall r, m < r -> r < n -> P r) :=
  Int.decidableLELT P _ _

/--
Instance `decidableLTLE` / 实例 `decidableLTLE`

English:
instance decidableLTLE
  signature: (P : Int -> Prop) [DecidablePred P] (m n : Int)
  body: Int.decidableLELE P _ _

中文:
实例 decidableLTLE
  签名: (P : 整数 -> 命题) [DecidablePred P] (m n : 整数)
  定义体: Int.decidableLELE P _ _

Depends on / 依赖: Int.decidableLELE, decidableLELE
-/
instance decidableLTLE (P : Int -> Prop) [DecidablePred P] (m n : Int) :
    Decidable (forall r, m < r -> r <= n -> P r) :=
  Int.decidableLELE P _ _

end Int
