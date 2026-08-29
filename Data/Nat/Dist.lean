/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Distance function on ℕ

This file defines a simple distance function on naturals from truncated subtraction.
-/

@[expose] public section


namespace Nat

/--
Definition of `dist` / `dist` 的定义

English:
definition dist
  signature: (n m : Nat)
  body: n - m + (m - n)

中文:
定义 dist
  签名: (n m : 自然数)
  定义体: n - m + (m - n)
-/
def dist (n m : Nat) :=
  n - m + (m - n)

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  given: (n m : Nat)
  statement: dist n m = dist m n
  proof: by simp [dist, add_comm]

@[simp]

中文:
定理 dist_comm
  条件: (n m : 自然数)
  结论: dist n m = dist m n
  证明: by simp [dist, add_comm]

@[simp]

Depends on / 依赖: add_comm
-/
theorem dist_comm (n m : Nat) : dist n m = dist m n := by simp [dist, add_comm]

@[simp]
/--
theorem `dist_self` / 定理 `dist_self`

English:
theorem dist_self
  given: (n : Nat)
  statement: dist n n = 0
  proof: by simp [dist, tsub_self]

中文:
定理 dist_self
  条件: (n : 自然数)
  结论: dist n n = 0
  证明: by simp [dist, tsub_self]

Depends on / 依赖: tsub_self
-/
theorem dist_self (n : Nat) : dist n n = 0 := by simp [dist, tsub_self]

/--
theorem `eq_of_dist_eq_zero` / 定理 `eq_of_dist_eq_zero`

English:
theorem eq_of_dist_eq_zero
  given: {n m : Nat} (h : dist n m = 0)
  statement: n = m
  proof: by unfold Nat.dist at h; lia

中文:
定理 eq_of_dist_eq_zero
  条件: {n m : 自然数} (h : dist n m = 0)
  结论: n = m
  证明: by unfold Nat.dist at h; lia

Depends on / 依赖: Nat.dist
-/
theorem eq_of_dist_eq_zero {n m : Nat} (h : dist n m = 0) : n = m := by unfold Nat.dist at h; lia

/--
theorem `dist_eq_zero` / 定理 `dist_eq_zero`

English:
theorem dist_eq_zero
  given: {n m : Nat} (h : n = m)
  statement: dist n m = 0
  proof: by unfold Nat.dist; lia

中文:
定理 dist_eq_zero
  条件: {n m : 自然数} (h : n = m)
  结论: dist n m = 0
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_eq_zero {n m : Nat} (h : n = m) : dist n m = 0 := by unfold Nat.dist; lia

/--
theorem `dist_eq_sub_of_le` / 定理 `dist_eq_sub_of_le`

English:
theorem dist_eq_sub_of_le
  given: {n m : Nat} (h : n <= m)
  statement: dist n m = m - n
  proof: by unfold Nat.dist; lia

中文:
定理 dist_eq_sub_of_le
  条件: {n m : 自然数} (h : n <= m)
  结论: dist n m = m - n
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_eq_sub_of_le {n m : Nat} (h : n <= m) : dist n m = m - n := by unfold Nat.dist; lia

/--
theorem `dist_eq_sub_of_le_right` / 定理 `dist_eq_sub_of_le_right`

English:
theorem dist_eq_sub_of_le_right
  given: {n m : Nat} (h : m <= n)
  statement: dist n m = n - m
  proof: by
  unfold Nat.dist; lia

中文:
定理 dist_eq_sub_of_le_right
  条件: {n m : 自然数} (h : m <= n)
  结论: dist n m = n - m
  证明: by
  unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_eq_sub_of_le_right {n m : Nat} (h : m <= n) : dist n m = n - m := by
  unfold Nat.dist; lia

/--
theorem `dist_tri_left` / 定理 `dist_tri_left`

English:
theorem dist_tri_left
  given: (n m : Nat)
  statement: m <= dist n m + n
  proof: by unfold Nat.dist; lia

中文:
定理 dist_tri_left
  条件: (n m : 自然数)
  结论: m <= dist n m + n
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_tri_left (n m : Nat) : m <= dist n m + n := by unfold Nat.dist; lia
/--
theorem `dist_tri_right` / 定理 `dist_tri_right`

English:
theorem dist_tri_right
  given: (n m : Nat)
  statement: m <= n + dist n m
  proof: by unfold Nat.dist; lia

中文:
定理 dist_tri_right
  条件: (n m : 自然数)
  结论: m <= n + dist n m
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_tri_right (n m : Nat) : m <= n + dist n m := by unfold Nat.dist; lia
/--
theorem `dist_tri_left'` / 定理 `dist_tri_left'`

English:
theorem dist_tri_left'
  given: (n m : Nat)
  statement: n <= dist n m + m
  proof: by unfold Nat.dist; lia

中文:
定理 dist_tri_left'
  条件: (n m : 自然数)
  结论: n <= dist n m + m
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_tri_left' (n m : Nat) : n <= dist n m + m := by unfold Nat.dist; lia
/--
theorem `dist_tri_right'` / 定理 `dist_tri_right'`

English:
theorem dist_tri_right'
  given: (n m : Nat)
  statement: n <= m + dist n m
  proof: by unfold Nat.dist; lia

中文:
定理 dist_tri_right'
  条件: (n m : 自然数)
  结论: n <= m + dist n m
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_tri_right' (n m : Nat) : n <= m + dist n m := by unfold Nat.dist; lia

/--
theorem `dist_zero_right` / 定理 `dist_zero_right`

English:
theorem dist_zero_right
  given: (n : Nat)
  statement: dist n 0 = n
  proof: by unfold Nat.dist; lia

中文:
定理 dist_zero_right
  条件: (n : 自然数)
  结论: dist n 0 = n
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_zero_right (n : Nat) : dist n 0 = n := by unfold Nat.dist; lia
/--
theorem `dist_zero_left` / 定理 `dist_zero_left`

English:
theorem dist_zero_left
  given: (n : Nat)
  statement: dist 0 n = n
  proof: by unfold Nat.dist; lia

中文:
定理 dist_zero_left
  条件: (n : 自然数)
  结论: dist 0 n = n
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_zero_left (n : Nat) : dist 0 n = n := by unfold Nat.dist; lia

/--
theorem `dist_add_add_right` / 定理 `dist_add_add_right`

English:
theorem dist_add_add_right
  given: (n k m : Nat)
  statement: dist (n + k) (m + k) = dist n m
  proof: by
  unfold Nat.dist; lia

中文:
定理 dist_add_add_right
  条件: (n k m : 自然数)
  结论: dist (n + k) (m + k) = dist n m
  证明: by
  unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_add_add_right (n k m : Nat) : dist (n + k) (m + k) = dist n m := by
  unfold Nat.dist; lia

/--
theorem `dist_add_add_left` / 定理 `dist_add_add_left`

English:
theorem dist_add_add_left
  given: (k n m : Nat)
  statement: dist (k + n) (k + m) = dist n m
  proof: by
  unfold Nat.dist; lia

中文:
定理 dist_add_add_left
  条件: (k n m : 自然数)
  结论: dist (k + n) (k + m) = dist n m
  证明: by
  unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_add_add_left (k n m : Nat) : dist (k + n) (k + m) = dist n m := by
  unfold Nat.dist; lia

/--
theorem `dist_eq_intro` / 定理 `dist_eq_intro`

English:
theorem dist_eq_intro
  given: {n m k l : Nat} (h : n + m = k + l)
  statement: dist n k = dist l m
  proof: by
  unfold Nat.dist; lia

中文:
定理 dist_eq_intro
  条件: {n m k l : 自然数} (h : n + m = k + l)
  结论: dist n k = dist l m
  证明: by
  unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_eq_intro {n m k l : Nat} (h : n + m = k + l) : dist n k = dist l m := by
  unfold Nat.dist; lia

/--
theorem `dist.triangle_inequality` / 定理 `dist.triangle_inequality`

English:
theorem dist.triangle_inequality
  given: (n m k : Nat)
  statement: dist n k <= dist n m + dist m k
  proof: by
  unfold Nat.dist; lia

中文:
定理 dist.triangle_inequality
  条件: (n m k : 自然数)
  结论: dist n k <= dist n m + dist m k
  证明: by
  unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist.triangle_inequality (n m k : Nat) : dist n k <= dist n m + dist m k := by
  unfold Nat.dist; lia

/--
theorem `dist_mul_right` / 定理 `dist_mul_right`

English:
theorem dist_mul_right
  given: (n k m : Nat)
  statement: dist (n * k) (m * k) = dist n m * k
  proof: by
  rw [dist]; rw [dist]; rw [right_distrib]; rw [tsub_mul n]; rw [tsub_mul m]

中文:
定理 dist_mul_right
  条件: (n k m : 自然数)
  结论: dist (n * k) (m * k) = dist n m * k
  证明: by
  rw [dist]; rw [dist]; rw [right_distrib]; rw [tsub_mul n]; rw [tsub_mul m]

Depends on / 依赖: right_distrib, tsub_mul
-/
theorem dist_mul_right (n k m : Nat) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist]; rw [dist]; rw [right_distrib]; rw [tsub_mul n]; rw [tsub_mul m]

/--
theorem `dist_mul_left` / 定理 `dist_mul_left`

English:
theorem dist_mul_left
  given: (k n m : Nat)
  statement: dist (k * n) (k * m) = k * dist n m
  proof: by
  rw [mul_comm k n]; rw [mul_comm k m]; rw [dist_mul_right]; rw [mul_comm]

中文:
定理 dist_mul_left
  条件: (k n m : 自然数)
  结论: dist (k * n) (k * m) = k * dist n m
  证明: by
  rw [mul_comm k n]; rw [mul_comm k m]; rw [dist_mul_right]; rw [mul_comm]

Depends on / 依赖: dist_mul_right, mul_comm
-/
theorem dist_mul_left (k n m : Nat) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n]; rw [mul_comm k m]; rw [dist_mul_right]; rw [mul_comm]

/--
theorem `dist_eq_max_sub_min` / 定理 `dist_eq_max_sub_min`

English:
theorem dist_eq_max_sub_min
  given: {i j : Nat}
  statement: dist i j = (max i j) - min i j
  proof: by
  cases le_total i j <;> simp [Nat.dist, *]

中文:
定理 dist_eq_max_sub_min
  条件: {i j : 自然数}
  结论: dist i j = (max i j) - min i j
  证明: by
  cases le_total i j <;> simp [Nat.dist, *]

Depends on / 依赖: Nat.dist, le_total
-/
theorem dist_eq_max_sub_min {i j : Nat} : dist i j = (max i j) - min i j := by
  cases le_total i j <;> simp [Nat.dist, *]

/--
theorem `dist_succ_succ` / 定理 `dist_succ_succ`

English:
theorem dist_succ_succ
  given: {i j : Nat}
  statement: dist (succ i) (succ j) = dist i j
  proof: by unfold Nat.dist; lia

中文:
定理 dist_succ_succ
  条件: {i j : 自然数}
  结论: dist (succ i) (succ j) = dist i j
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j := by unfold Nat.dist; lia

/--
theorem `dist_pos_of_ne` / 定理 `dist_pos_of_ne`

English:
theorem dist_pos_of_ne
  given: {i j : Nat} (h : i != j)
  statement: 0 < dist i j
  proof: by unfold Nat.dist; lia

中文:
定理 dist_pos_of_ne
  条件: {i j : 自然数} (h : i != j)
  结论: 0 < dist i j
  证明: by unfold Nat.dist; lia

Depends on / 依赖: Nat.dist
-/
theorem dist_pos_of_ne {i j : Nat} (h : i != j) : 0 < dist i j := by unfold Nat.dist; lia

end Nat
