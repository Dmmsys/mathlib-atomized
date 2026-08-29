/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Lemmas about distances between points in intervals in `ℝ`.
-/

public section

open Bornology Filter Metric Set
open scoped NNReal Topology

namespace Real

variable {ι : Type*}

/--
lemma `dist_left_le_of_mem_uIcc` / 引理 `dist_left_le_of_mem_uIcc`

English:
lemma dist_left_le_of_mem_uIcc
  given: {x y z : Real} (h : y in uIcc x z)
  statement: dist x y <= dist x z
  proof: by
  simpa only [dist_comm x] using! abs_sub_left_of_mem_uIcc h

中文:
引理 dist_left_le_of_mem_uIcc
  条件: {x y z : 实数} (h : y in uIcc x z)
  结论: dist x y <= dist x z
  证明: by
  simpa only [dist_comm x] using! abs_sub_left_of_mem_uIcc h

Depends on / 依赖: abs_sub_left_of_mem_uIcc, dist_comm
-/
lemma dist_left_le_of_mem_uIcc {x y z : Real} (h : y in uIcc x z) : dist x y <= dist x z := by
  simpa only [dist_comm x] using! abs_sub_left_of_mem_uIcc h

/--
lemma `dist_right_le_of_mem_uIcc` / 引理 `dist_right_le_of_mem_uIcc`

English:
lemma dist_right_le_of_mem_uIcc
  given: {x y z : Real} (h : y in uIcc x z)
  statement: dist y z <= dist x z
  proof: by
  simpa only [dist_comm _ z] using! abs_sub_right_of_mem_uIcc h

中文:
引理 dist_right_le_of_mem_uIcc
  条件: {x y z : 实数} (h : y in uIcc x z)
  结论: dist y z <= dist x z
  证明: by
  simpa only [dist_comm _ z] using! abs_sub_right_of_mem_uIcc h

Depends on / 依赖: abs_sub_right_of_mem_uIcc, dist_comm
-/
lemma dist_right_le_of_mem_uIcc {x y z : Real} (h : y in uIcc x z) : dist y z <= dist x z := by
  simpa only [dist_comm _ z] using! abs_sub_right_of_mem_uIcc h

/--
lemma `dist_le_of_mem_uIcc` / 引理 `dist_le_of_mem_uIcc`

English:
lemma dist_le_of_mem_uIcc
  given: {x y x' y' : Real} (hx : x in uIcc x' y') (hy : y in uIcc x' y')
  proof: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])

中文:
引理 dist_le_of_mem_uIcc
  条件: {x y x' y' : 实数} (hx : x in uIcc x' y') (hy : y in uIcc x' y')
  证明: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])

Depends on / 依赖: abs_sub_le_of_uIcc_subset_uIcc, uIcc_comm, uIcc_subset_uIcc
-/
lemma dist_le_of_mem_uIcc {x y x' y' : Real} (hx : x in uIcc x' y') (hy : y in uIcc x' y') :
    dist x y <= dist x' y' :=
abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])

/--
lemma `dist_le_of_mem_Icc` / 引理 `dist_le_of_mem_Icc`

English:
lemma dist_le_of_mem_Icc
  given: {x y x' y' : Real} (hx : x in Icc x' y') (hy : y in Icc x' y')
  proof: by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)

中文:
引理 dist_le_of_mem_Icc
  条件: {x y x' y' : 实数} (hx : x in Icc x' y') (hy : y in Icc x' y')
  证明: by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)

Depends on / 依赖: Icc_subset_uIcc, Real.dist_eq, Real.dist_le_of_mem_uIcc, abs_of_nonpos, dist_eq, dist_le_of_mem_uIcc, neg_sub, sub_nonpos
-/
lemma dist_le_of_mem_Icc {x y x' y' : Real} (hx : x in Icc x' y') (hy : y in Icc x' y') :
    dist x y <= y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)

/--
lemma `dist_le_of_mem_Icc_01` / 引理 `dist_le_of_mem_Icc_01`

English:
lemma dist_le_of_mem_Icc_01
  given: {x y : Real} (hx : x in Icc (0 : Real) 1) (hy : y in Icc (0 : Real) 1)
  proof: by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

中文:
引理 dist_le_of_mem_Icc_01
  条件: {x y : 实数} (hx : x in Icc (0 : 实数) 1) (hy : y in Icc (0 : 实数) 1)
  证明: by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

Depends on / 依赖: Real.dist_le_of_mem_Icc, dist_le_of_mem_Icc, sub_zero
-/
lemma dist_le_of_mem_Icc_01 {x y : Real} (hx : x in Icc (0 : Real) 1) (hy : y in Icc (0 : Real) 1) :
    dist x y <= 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

variable [Fintype ι] {x y x' y' : ι -> Real}

/--
lemma `dist_le_of_mem_pi_Icc` / 引理 `dist_le_of_mem_pi_Icc`

English:
lemma dist_le_of_mem_pi_Icc
  given: (hx : x in Icc x' y') (hy : y in Icc x' y')
  statement: dist x y <= dist x' y'
  proof: by
  refine (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc ?_ ?_).trans (dist_le_pi_dist x' y' b) <;> refine Icc_subset_uIcc ?_
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]

中文:
引理 dist_le_of_mem_pi_Icc
  条件: (hx : x in Icc x' y') (hy : y in Icc x' y')
  结论: dist x y <= dist x' y'
  证明: by
  refine (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc ?_ ?_).trans (dist_le_pi_dist x' y' b) <;> refine Icc_subset_uIcc ?_
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]

Depends on / 依赖: Icc_subset_uIcc, Real.dist_le_of_mem_uIcc, dist_le_of_mem_uIcc, dist_le_pi_dist, dist_nonneg, dist_pi_le_iff, exacts
-/
lemma dist_le_of_mem_pi_Icc (hx : x in Icc x' y') (hy : y in Icc x' y') : dist x y <= dist x' y' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc ?_ ?_).trans (dist_le_pi_dist x' y' b) <;> refine Icc_subset_uIcc ?_
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]

end Real
