/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations in strictly convex sets and spaces.

This file proves lemmas about convex combinations of points in strictly convex sets and strictly
convex spaces.

-/

public section


open Finset Metric

variable {R V P ι : Type*}

section Set

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace V] [AddCommGroup V]
variable [Module R V]

/--
lemma `StrictConvex.centerMass_mem_interior` / 引理 `StrictConvex.centerMass_mem_interior`

English:
lemma StrictConvex.centerMass_mem_interior
  statement: {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V}
  proof: by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ i' j' hi' hj' hi'j' hi'0 hj'0 hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    by_cases hsum_t : 

中文:
引理 严格凸.centerMass_mem_interior
  结论: {s : 集合 V} {t : 有限集 ι} {w : ι -> R} {z : ι -> V}
  证明: by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ i' j' hi' hj' hi'j' hi'0 hj'0 hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    by_cases hsum_t : 

Depends on / 依赖: Finset, Finset.c, Finset.induction, classical, hsum_t, insert, mem_insert_of_mem, mem_insert_self, sum_eq_zero_iff_of_nonneg
-/
lemma StrictConvex.centerMass_mem_interior {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V}
    (hs : StrictConvex R s) :
    (forall i in t, 0 <= w i) -> forall i j, i in t -> j in t -> z i != z j -> w i != 0 -> w j != 0 ->
      (forall i in t, z i in s) -> t.centerMass w z in interior s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ i' j' hi' hj' hi'j' hi'0 hj'0 hmem
    have zi : z i in s := hmem _ (mem_insert_self _ _)
have hs₀ : forall j in t, 0 <= w j := fun j hj => h₀ j mem_insert_of_mem hj
    by_cases hsum_t : ∑ j in t, w j = 0
    · have ws : forall j in t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have h : i' in t ∨ j' in t := by grind
      exfalso
      rcases h with h | h
      · exact hi'0 (ws _ h)
      · exact hj'0 (ws _ h)
    rw [Finset.centerMass_insert _ _ _ hi hsum_t]
    by_cases hi : w i = 0
    · simp only [hi, zero_add, zero_div, zero_smul, ne_eq, hsum_t, not_false_eq_true, div_self,
        one_smul]
      grind
    by_cases hzi : z i = t.centerMass w z
    · have hwi : w i + ∑ j in t, w j != 0 := by
        refine LT.lt.ne' ?_
        have hwi : 0 < w i := by grind
        grw [← hwi, ← sum_nonneg hs₀, add_zero]
      simp only [hzi, ← add_smul, ← add_div, ne_eq, hwi, not_false_eq_true, div_self, one_smul]
      by_cases! hijt : exists i'' j'', i'' in t ∧ j'' in t ∧ z i'' != z j'' ∧ w i'' != 0 ∧ w j'' != 0
      · grind
      · exfalso
        obtain ⟨i'', hi'', hwi''⟩ : exists i'' in t, w i'' != 0 := by grind
        have hijt' : forall j'', j'' in t -> w j'' != 0 -> z j'' = Function.const _ (z i'') j'' := by
          grind
        have hi : i = i' ∨ i = j' := by grind
        have hzi'' : t.centerMass w z = z i'' := by
          rw [t.centerMass_congr_fun hijt']; rw [t.centerMass_const hsum_t]
        grind
    · exact strictConvex_iff_div.1 hs zi
        (hs.convex.centerMass_mem hs₀ (lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t))
          (fun j hj => hmem j (mem_insert_of_mem hj))) hzi (by grind)
        ((sum_nonneg hs₀).lt_of_ne' hsum_t)

/--
lemma `StrictConvex.sum_mem_interior` / 引理 `StrictConvex.sum_mem_interior`

English:
lemma StrictConvex.sum_mem_interior
  statement: {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V}
  proof: by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact hs.centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

中文:
引理 严格凸.sum_mem_interior
  结论: {s : 集合 V} {t : 有限集 ι} {w : ι -> R} {z : ι -> V}
  证明: by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact hs.centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

Depends on / 依赖: centerMass_eq_of_sum_1, centerMass_mem_interior, hs.centerMass_mem_interior, t.centerMass_eq_of_sum_1
-/
lemma StrictConvex.sum_mem_interior {s : Set V} {t : Finset ι} {w : ι -> R} {z : ι -> V}
    (hs : StrictConvex R s) (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {i j : ι}
    (hi : i in t) (hj : j in t) (hij : z i != z j) (hi0 : w i != 0) (hj0 : w j != 0)
    (hz : forall i in t, z i in s) : ∑ k in t, w k • z k in interior s := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact hs.centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

end Set

section Space

variable [NormedAddCommGroup V] [NormedSpace Real V] [StrictConvexSpace Real V]

/--
lemma `centerMass_mem_ball_of_strictConvexSpace` / 引理 `centerMass_mem_ball_of_strictConvexSpace`

English:
lemma centerMass_mem_ball_of_strictConvexSpace
  statement: {t : Finset ι} {w : ι -> Real} {p : V} {r : Real}
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · rw [← interior_closedBall _ hr]
    exact (strictConvex_closedBall _ _ _).centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

中文:
引理 centerMass_mem_ball_of_strictConvexSpace
  结论: {t : 有限集 ι} {w : ι -> 实数} {p : V} {r : 实数}
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · rw [← interior_closedBall _ hr]
    exact (strictConvex_closedBall _ _ _).centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

Depends on / 依赖: centerMass_mem_interior, eq_or_ne, interior_closedBall, strictConvex_closedBall
-/
lemma centerMass_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p : V} {r : Real}
    {z : ι -> V} (h0 : forall i in t, 0 <= w i) {i j : ι} (hi : i in t) (hj : j in t) (hij : z i != z j)
    (hi0 : w i != 0) (hj0 : w j != 0) (hz : forall i in t, z i in closedBall p r) :
    t.centerMass w z in ball p r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · rw [← interior_closedBall _ hr]
    exact (strictConvex_closedBall _ _ _).centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

/--
lemma `sum_mem_ball_of_strictConvexSpace` / 引理 `sum_mem_ball_of_strictConvexSpace`

English:
lemma sum_mem_ball_of_strictConvexSpace
  statement: {t : Finset ι} {w : ι -> Real} {p : V} {r : Real} {z : ι -> V}
  proof: by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact centerMass_mem_ball_of_strictConvexSpace h0 hi hj hij hi0 hj0 hz

中文:
引理 sum_mem_ball_of_strictConvexSpace
  结论: {t : 有限集 ι} {w : ι -> 实数} {p : V} {r : 实数} {z : ι -> V}
  证明: by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact centerMass_mem_ball_of_strictConvexSpace h0 hi hj hij hi0 hj0 hz

Depends on / 依赖: centerMass_eq_of_sum_1, centerMass_mem_ball_of_strictConvexSpace, t.centerMass_eq_of_sum_1
-/
lemma sum_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p : V} {r : Real} {z : ι -> V}
    (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {i j : ι} (hi : i in t) (hj : j in t)
    (hij : z i != z j) (hi0 : w i != 0) (hj0 : w j != 0) (hz : forall i in t, z i in closedBall p r) :
    ∑ k in t, w k • z k in ball p r := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact centerMass_mem_ball_of_strictConvexSpace h0 hi hj hij hi0 hj0 hz

/--
lemma `norm_sum_lt_of_strictConvexSpace` / 引理 `norm_sum_lt_of_strictConvexSpace`

English:
lemma norm_sum_lt_of_strictConvexSpace
  statement: {t : Finset ι} {w : ι -> Real} {r : Real} {z : ι -> V}
  proof: by
  simp_rw [← mem_closedBall_zero_iff] at hz
  rw [← mem_ball_zero_iff]
  exact sum_mem_ball_of_strictConvexSpace h0 h1 hi hj hij hi0 hj0 hz

中文:
引理 norm_sum_lt_of_strictConvexSpace
  结论: {t : 有限集 ι} {w : ι -> 实数} {r : 实数} {z : ι -> V}
  证明: by
  simp_rw [← mem_closedBall_zero_iff] at hz
  rw [← mem_ball_zero_iff]
  exact sum_mem_ball_of_strictConvexSpace h0 h1 hi hj hij hi0 hj0 hz

Depends on / 依赖: mem_ball_zero_iff, mem_closedBall_zero_iff, simp_rw, sum_mem_ball_of_strictConvexSpace
-/
lemma norm_sum_lt_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {r : Real} {z : ι -> V}
    (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {i j : ι} (hi : i in t) (hj : j in t)
    (hij : z i != z j) (hi0 : w i != 0) (hj0 : w j != 0) (hz : forall i in t, ‖z i‖ <= r) :
    ‖∑ k in t, w k • z k‖ < r := by
  simp_rw [← mem_closedBall_zero_iff] at hz
  rw [← mem_ball_zero_iff]
  exact sum_mem_ball_of_strictConvexSpace h0 h1 hi hj hij hi0 hj0 hz

variable [PseudoMetricSpace P] [NormedAddTorsor V P]

/--
lemma `dist_affineCombination_lt_of_strictConvexSpace` / 引理 `dist_affineCombination_lt_of_strictConvexSpace`

English:
lemma dist_affineCombination_lt_of_strictConvexSpace
  statement: {t : Finset ι} {w : ι -> Real} {p₀ : P} {r : Real}
  proof: by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ h1 p₀]; rw [weightedVSubOfPoint_apply]; rw [dist_vadd_left]
  simp_rw [dist_eq_norm_vsub] at hp
  exact norm_sum_lt_of_strictConvexSpace h0 h1 hi hj (by simpa using hij) hi0 hj0 hp

中文:
引理 dist_affineCombination_lt_of_strictConvexSpace
  结论: {t : 有限集 ι} {w : ι -> 实数} {p₀ : P} {r : 实数}
  证明: by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ h1 p₀]; rw [weightedVSubOfPoint_apply]; rw [dist_vadd_left]
  simp_rw [dist_eq_norm_vsub] at hp
  exact norm_sum_lt_of_strictConvexSpace h0 h1 hi hj (by simpa using hij) hi0 hj0 hp

Depends on / 依赖: affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one, dist_eq_norm_vsub, dist_vadd_left, norm_sum_lt_of_strictConvexSpace, simp_rw, weightedVSubOfPoint_apply
-/
lemma dist_affineCombination_lt_of_strictConvexSpace {t : Finset ι} {w : ι -> Real} {p₀ : P} {r : Real}
    {p : ι -> P} (h0 : forall i in t, 0 <= w i) (h1 : ∑ i in t, w i = 1) {i j : ι} (hi : i in t)
    (hj : j in t) (hij : p i != p j) (hi0 : w i != 0) (hj0 : w j != 0)
    (hp : forall i in t, dist (p i) p₀ <= r) :
    dist (t.affineCombination Real p w) p₀ < r := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ h1 p₀]; rw [weightedVSubOfPoint_apply]; rw [dist_vadd_left]
  simp_rw [dist_eq_norm_vsub] at hp
  exact norm_sum_lt_of_strictConvexSpace h0 h1 hi hj (by simpa using hij) hi0 hj0 hp

namespace Affine

namespace Simplex

/--
lemma `dist_lt_of_mem_closedInterior_of_strictConvexSpace` / 引理 `dist_lt_of_mem_closedInterior_of_strictConvexSpace`

English:
lemma dist_lt_of_mem_closedInterior_of_strictConvexSpace
  statement: {n : Nat} (s : Simplex Real P n) {r : Real}
  proof: by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : exists i, w i != 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : exists j, i != j ∧ w j != 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ i)]
    cong

中文:
引理 dist_lt_of_mem_closed整数erior_of_strictConvexSpace
  结论: {n : 自然数} (s : 单纯形 实数 P n) {r : 实数}
  证明: by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : exists i, w i != 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : exists j, i != j ∧ w j != 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ i)]
    cong

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Pi.single_eq_of_ne, Pi.single_eq_same, affineCombination_piSingle, dist_affineCombinat, eq_comm, eq_or_ne, hk.symm, mem_univ, points, s.points, single_eq_of_ne, single_eq_same, sum_eq_single
-/
lemma dist_lt_of_mem_closedInterior_of_strictConvexSpace {n : Nat} (s : Simplex Real P n) {r : Real}
    {p₀ p : P} (hp : p in s.closedInterior) (hp' : forall i, p != s.points i)
    (hr : forall i, dist (s.points i) p₀ <= r) : dist p p₀ < r := by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : exists i, w i != 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : exists j, i != j ∧ w j != 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_piSingle Real s.points (Finset.mem_univ i)]
    congr 1
    ext j
    obtain rfl | hj := eq_or_ne i j
    · simp only [Pi.single_eq_same]
      rw [← hw]; rw [eq_comm]
      exact sum_eq_single i (fun k _ hk => hij k hk.symm) (by simp)
    · rw [Pi.single_eq_of_ne' hj]
      exact hij j hj
  exact dist_affineCombination_lt_of_strictConvexSpace (fun k _ => (hw01 k).1) hw
    (Finset.mem_univ i) (Finset.mem_univ j) (s.independent.injective.ne hij) hi hj (fun k _ => hr k)

/--
lemma `dist_lt_of_mem_interior_of_strictConvexSpace` / 引理 `dist_lt_of_mem_interior_of_strictConvexSpace`

English:
lemma dist_lt_of_mem_interior_of_strictConvexSpace
  statement: {n : Nat} (s : Simplex Real P n) {r : Real}
  proof: s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h => s.point_notMem_interior i (h ▸ hp)) hr

中文:
引理 dist_lt_of_mem_interior_of_strictConvexSpace
  结论: {n : 自然数} (s : 单纯形 实数 P n) {r : 实数}
  证明: s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h => s.point_notMem_interior i (h ▸ hp)) hr

Depends on / 依赖: Set.mem_of_mem_of_subset, dist_lt_of_mem_closedInterior_of_strictConvexSpace, interior_subset_closedInterior, mem_of_mem_of_subset, point_notMem_interior, s.dist_lt_of_mem_closedInterior_of_strictConvexSpace, s.interior_subset_closedInterior, s.point_notMem_interior
-/
lemma dist_lt_of_mem_interior_of_strictConvexSpace {n : Nat} (s : Simplex Real P n) {r : Real}
    {p₀ p : P} (hp : p in s.interior) (hr : forall i, dist (s.points i) p₀ <= r) : dist p p₀ < r :=
  s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h => s.point_notMem_interior i (h ▸ hp)) hr

end Simplex

end Affine

end Space
