/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Init

/-!
# Basic lemmas about division and modulo for integers

-/

public section

namespace Int


/--
theorem `mul_ediv_le_mul_ediv_assoc` / 定理 `mul_ediv_le_mul_ediv_assoc`

English:
theorem mul_ediv_le_mul_ediv_assoc
  given: {a : Int} (ha : 0 <= a) (b : Int) {c : Int} (hc : 0 <= c)
  proof: by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by lia
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha

中文:
定理 mul_ediv_le_mul_ediv_assoc
  条件: {a : 整数} (ha : 0 <= a) (b : 整数) {c : 整数} (hc : 0 <= c)
  证明: by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by lia
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha

Depends on / 依赖: Int.ediv_mul_le, Int.le_ediv_iff_mul_le, Int.mul_assoc, Int.mul_le_mul_of_nonneg_left, Int.ne_of_gt, ediv_mul_le, le_ediv_iff_mul_le, mul_assoc, mul_le_mul_of_nonneg_left, ne_of_gt
-/
theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 <= a) (b : Int) {c : Int} (hc : 0 <= c) :
    a * (b / c) <= a * b / c := by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by lia
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha

/--
theorem `fdiv_fdiv_eq_fdiv_mul` / 定理 `fdiv_fdiv_eq_fdiv_mul`

English:
theorem fdiv_fdiv_eq_fdiv_mul
  given: (m : Int) {n k : Int} (hn : 0 <= n) (hk : 0 <= k)
  proof: by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn]; rw [Int.fdiv_eq_ediv_of_nonneg _ hk]; rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk)]; rw [ediv_ediv_of_nonneg hn]

中文:
定理 fdiv_fdiv_eq_fdiv_mul
  条件: (m : 整数) {n k : 整数} (hn : 0 <= n) (hk : 0 <= k)
  证明: by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn]; rw [Int.fdiv_eq_ediv_of_nonneg _ hk]; rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk)]; rw [ediv_ediv_of_nonneg hn]

Depends on / 依赖: Int.fdiv_eq_ediv_of_nonneg, Int.mul_nonneg, ediv_ediv_of_nonneg, fdiv_eq_ediv_of_nonneg, mul_nonneg
-/
theorem fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 <= n) (hk : 0 <= k) :
    (m.fdiv n).fdiv k = m.fdiv (n * k) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn]; rw [Int.fdiv_eq_ediv_of_nonneg _ hk]; rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk)]; rw [ediv_ediv_of_nonneg hn]


/--
theorem `emod_eq_sub_self_emod` / 定理 `emod_eq_sub_self_emod`

English:
theorem emod_eq_sub_self_emod
  given: {a b : Int}
  statement: a % b = (a - b) % b
  proof: (sub_emod_right a b).symm

中文:
定理 emod_eq_sub_self_emod
  条件: {a b : 整数}
  结论: a % b = (a - b) % b
  证明: (sub_emod_right a b).symm

Depends on / 依赖: sub_emod_right
-/
theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (sub_emod_right a b).symm

end Int
