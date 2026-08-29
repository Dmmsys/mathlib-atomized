/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.GroupTheory.Index

/-! # Lemmas about units of ordered rings -/

public section

/--
lemma `Units.index_posSubgroup` / 引理 `Units.index_posSubgroup`

English:
lemma Units.index_posSubgroup
  given: (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun a => ?_⟩
  obtain h | h := lt_or_gt_of_ne a.ne_zero
  · simp [h, h.le]
  · simp [h, xor_comm, h.le]

中文:
引理 Units.index_posSubgroup
  条件: (R : 类型) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  证明: by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun a => ?_⟩
  obtain h | h := lt_or_gt_of_ne a.ne_zero
  · simp [h, h.le]
  · simp [h, xor_comm, h.le]

Depends on / 依赖: Subgroup, Subgroup.index_eq_two_iff, a.ne_zero, h.le, index_eq_two_iff, lt_or_gt_of_ne, ne_zero, xor_comm
-/
lemma Units.index_posSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (posSubgroup R).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun a => ?_⟩
  obtain h | h := lt_or_gt_of_ne a.ne_zero
  · simp [h, h.le]
  · simp [h, xor_comm, h.le]
