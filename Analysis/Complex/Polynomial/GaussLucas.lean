/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Gauss-Lucas Theorem

In this file we prove Gauss-Lucas Theorem:
the roots of the derivative of a nonconstant complex polynomial
are included in the convex hull of the roots of the polynomial.
-/

@[expose] public section
open scoped Polynomial ComplexConjugate

namespace Polynomial

/--
Definition of `derivRootWeight` / `derivRootWeight` 的定义

English:
definition derivRootWeight
  signature: (P : Complex[X]) (z w : Complex)
  body: if P.eval z = 0 then (Pi.single z 1 : Complex -> Real) w
  else P.rootMultiplicity w / ‖z - w‖ ^ 2

中文:
定义 derivRootWeight
  签名: (P : 复形[X]) (z w : 复形)
  定义体: if P.eval z = 0 then (Pi.single z 1 : Complex -> Real) w
  else P.rootMultiplicity w / ‖z - w‖ ^ 2

Depends on / 依赖: P.eval, P.rootMultiplicity, Pi.single, rootMultiplicity, single
-/
noncomputable def derivRootWeight (P : Complex[X]) (z w : Complex) : Real :=
  if P.eval z = 0 then (Pi.single z 1 : Complex -> Real) w
  else P.rootMultiplicity w / ‖z - w‖ ^ 2

/--
theorem `derivRootWeight_nonneg` / 定理 `derivRootWeight_nonneg`

English:
theorem derivRootWeight_nonneg
  given: (P : Complex[X]) (z w : Complex)
  statement: 0 <= derivRootWeight P z w
  proof: by
  simp only [derivRootWeight, Pi.single, Function.update_apply]
  split_ifs <;> first | positivity | simp

中文:
定理 derivRootWeight_nonneg
  条件: (P : 复形[X]) (z w : 复形)
  结论: 0 <= derivRootWeight P z w
  证明: by
  simp only [derivRootWeight, Pi.single, Function.update_apply]
  split_ifs <;> first | positivity | simp

Depends on / 依赖: Function, Function.update_apply, Pi.single, derivRootWeight, single, split_ifs, update_apply
-/
theorem derivRootWeight_nonneg (P : Complex[X]) (z w : Complex) : 0 <= derivRootWeight P z w := by
  simp only [derivRootWeight, Pi.single, Function.update_apply]
  split_ifs <;> first | positivity | simp

variable {P : Complex[X]} {z : Complex}

/--
theorem `sum_derivRootWeight_pos` / 定理 `sum_derivRootWeight_pos`

English:
theorem sum_derivRootWeight_pos
  given: (hP : 0 < degree P) (z : Complex)
  proof: by
  have hP₀ : P != 0 := by rintro rfl; simp at hP
  by_cases hPz : P.eval z = 0
  · simp [derivRootWeight, hPz, hP₀]
  · simp only [derivRootWeight, if_neg hPz]
    apply Finset.sum_pos
    · intro w hw
      apply div_pos (by simp_all)
      suffices z != w by simpa [sq_pos_iff, sub_eq_zero]
    

中文:
定理 sum_derivRootWeight_pos
  条件: (hP : 0 < degree P) (z : 复形)
  证明: by
  have hP₀ : P != 0 := by rintro rfl; simp at hP
  by_cases hPz : P.eval z = 0
  · simp [derivRootWeight, hPz, hP₀]
  · simp only [derivRootWeight, if_neg hPz]
    apply Finset.sum_pos
    · intro w hw
      apply div_pos (by simp_all)
      suffices z != w by simpa [sq_pos_iff, sub_eq_zero]
    

Depends on / 依赖: Finset, Finset.sum_pos, IsAlgClosed, IsAlgClosed.splits, Multiset, Multiset.toFinset_nonempty, P.eval, Splits, Splits.roots_ne_zero, derivRootWeight, div_pos, if_neg, natDegree_pos_iff_degree_pos, pos_iff_ne_zero, roots_ne_zero, splits, sq_pos_iff, sub_eq_zero, sum_pos, toFinset_nonempty
-/
theorem sum_derivRootWeight_pos (hP : 0 < degree P) (z : Complex) :
    0 < ∑ w in P.roots.toFinset, derivRootWeight P z w := by
  have hP₀ : P != 0 := by rintro rfl; simp at hP
  by_cases hPz : P.eval z = 0
  · simp [derivRootWeight, hPz, hP₀]
  · simp only [derivRootWeight, if_neg hPz]
    apply Finset.sum_pos
    · intro w hw
      apply div_pos (by simp_all)
      suffices z != w by simpa [sq_pos_iff, sub_eq_zero]
      rintro rfl
      simp_all
    · rw [Multiset.toFinset_nonempty]
      apply Splits.roots_ne_zero (IsAlgClosed.splits _)
      rwa [← pos_iff_ne_zero, natDegree_pos_iff_degree_pos]

/--
theorem `eq_centerMass_of_eval_derivative_eq_zero` / 定理 `eq_centerMass_of_eval_derivative_eq_zero`

English:
theorem eq_centerMass_of_eval_derivative_eq_zero
  statement: (hP : 0 < P.degree)
  proof: by
  set weight : Complex -> Real := P.derivRootWeight z
  set s := P.roots.toFinset
  suffices ∑ x in s, weight x • (z - x) = 0 by calc
    z = s.centerMass weight fun _ => z := by
      rw [Finset.centerMass]; rw [← Finset.sum_smul]; rw [inv_smul_smul₀]
      exact (sum_derivRootWeight_pos hP z).n

中文:
定理 eq_centerMass_of_eval_derivative_eq_zero
  结论: (hP : 0 < P.degree)
  证明: by
  set weight : Complex -> Real := P.derivRootWeight z
  set s := P.roots.toFinset
  suffices ∑ x in s, weight x • (z - x) = 0 by calc
    z = s.centerMass weight fun _ => z := by
      rw [Finset.centerMass]; rw [← Finset.sum_smul]; rw [inv_smul_smul₀]
      exact (sum_derivRootWeight_pos hP z).n

Depends on / 依赖: Finset, Finset.cen, Finset.centerMass, Finset.sum_add_distrib, Finset.sum_smul, P.derivRootWeight, P.roots.toFinset, add_eq_right, centerMass, derivRootWeight, s.centerMass, smul_add, sub_add_cancel, sum_add_distrib, sum_derivRootWeight_pos, sum_smul, toFinset, weight
-/
theorem eq_centerMass_of_eval_derivative_eq_zero (hP : 0 < P.degree)
    (hz : P.derivative.eval z = 0) :
    z = P.roots.toFinset.centerMass (P.derivRootWeight z) id := by
  set weight : Complex -> Real := P.derivRootWeight z
  set s := P.roots.toFinset
  suffices ∑ x in s, weight x • (z - x) = 0 by calc
    z = s.centerMass weight fun _ => z := by
      rw [Finset.centerMass]; rw [← Finset.sum_smul]; rw [inv_smul_smul₀]
      exact (sum_derivRootWeight_pos hP z).ne'
    _ = s.centerMass weight (z - ·) + s.centerMass weight id := by
      simp only [Finset.centerMass, ← smul_add, ← Finset.sum_add_distrib, id, sub_add_cancel]
    _ = s.centerMass weight id := by
      simp only [add_eq_right, Finset.centerMass, this, smul_zero]
  by_cases hzP : P.eval z = 0
  · simp only [weight, derivRootWeight, if_pos hzP]
    rw [Finset.sum_eq_single z] <;> simp_all
  calc
    ∑ x in s, weight x • (z - x) = conj (∑ x in s, P.rootMultiplicity x • (1 / (z - x))) := by
      simp only [map_sum, weight, derivRootWeight, if_neg hzP]
      refine Finset.sum_congr rfl fun x hx => ?_
      have : z - x != 0 := by
        rw [sub_ne_zero]
        rintro rfl
        simp_all [s]
      simp [← Complex.conj_mul', field]
    _ = conj (P.roots.map fun x => 1 / (z - x)).sum := by
      simp only [Finset.sum_multiset_map_count, P.count_roots, s]
    _ = 0 := by
      rw [← (IsAlgClosed.splits _).eval_derivative_div_eval_of_ne_zero hzP]
      simp [hz]

/--
theorem `rootSet_derivative_subset_convexHull_rootSet` / 定理 `rootSet_derivative_subset_convexHull_rootSet`

English:
theorem rootSet_derivative_subset_convexHull_rootSet
  given: (h₀ : 0 < P.degree)
  proof: by
  intro z hz
  rw [mem_rootSet]; rw [coe_aeval_eq_eval] at hz
  rw [eq_centerMass_of_eval_derivative_eq_zero h₀ hz.2]
  apply Finset.centerMass_mem_convexHull
  · simp [derivRootWeight_nonneg]
  · apply sum_derivRootWeight_pos h₀
  · simp [mem_rootSet]

中文:
定理 rootSet_derivative_subset_convexHull_rootSet
  条件: (h₀ : 0 < P.degree)
  证明: by
  intro z hz
  rw [mem_rootSet]; rw [coe_aeval_eq_eval] at hz
  rw [eq_centerMass_of_eval_derivative_eq_zero h₀ hz.2]
  apply Finset.centerMass_mem_convexHull
  · simp [derivRootWeight_nonneg]
  · apply sum_derivRootWeight_pos h₀
  · simp [mem_rootSet]

Depends on / 依赖: Finset, Finset.centerMass_mem_convexHull, centerMass_mem_convexHull, coe_aeval_eq_eval, derivRootWeight_nonneg, eq_centerMass_of_eval_derivative_eq_zero, mem_rootSet, sum_derivRootWeight_pos
-/
theorem rootSet_derivative_subset_convexHull_rootSet (h₀ : 0 < P.degree) :
    P.derivative.rootSet Complex subseteq convexHull Real (P.rootSet Complex) := by
  intro z hz
  rw [mem_rootSet]; rw [coe_aeval_eq_eval] at hz
  rw [eq_centerMass_of_eval_derivative_eq_zero h₀ hz.2]
  apply Finset.centerMass_mem_convexHull
  · simp [derivRootWeight_nonneg]
  · apply sum_derivRootWeight_pos h₀
  · simp [mem_rootSet]

end Polynomial
