/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.StrictConvexSpace

import Mathlib.Algebra.CharP.Invertible

/-! # Extreme points of (strictly convex) sets

This file collects some results of extreme points of (strictly convex) sets.

## Main results
* `disjoint_interior_extremePoints`: the interior and extreme points of a set in a
  nontrivial topological vector space are disjoint.
* `StrictConvex.sdiff_interior_subset_extremePoints`:
  when `C` is a strictly convex set then `C \ interior C ⊆ extremePoints 𝕜 C`.
* `StrictConvex.extremePoints_eq_sdiff_interior`: the extreme points of a strictly convex set `S`
  in nontrivial normed space is exactly `S \ interior S`.

Corollaries of the above is that, in a nontrivial normed space, the extreme points of the
closed ball is contained in the sphere (see `extremePoints_closedBall_subset_sphere`).
And in a nontrivial strictly convex space, the extreme points of the closed ball is exactly the
sphere (see `StrictConvexSpace.extremePoints_closedBall_eq_sphere`). -/

public section

open Set Metric

open Filter in
open scoped Topology in
/--
theorem `disjoint_interior_extremePoints` / 定理 `disjoint_interior_extremePoints`

English:
theorem disjoint_interior_extremePoints
  statement: {E : Type*} [AddCommGroup E] [Module Real E]
  proof: by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ => ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : forallᶠ v in 𝓝[!=] 0, x - v in S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : forallᶠ v in 𝓝[!=] 0, x + v in S :=
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
.exists .and eventually_mem_nhdsWithin obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v != 0)⟩ := h₁.and h₂
  have key : x in openSegment Real (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]

中文:
定理 disjoint_interior_extremePoints
  结论: {E : 类型} [加法交换群 E] [模 实数 E]
  证明: by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ => ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : forallᶠ v in 𝓝[!=] 0, x - v in S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : forallᶠ v in 𝓝[!=] 0, x + v in S :=
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
.exists .and eventually_mem_nhdsWithin obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v != 0)⟩ := h₁.and h₂
  have key : x in openSegment Real (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]

Depends on / 依赖: Set.disjoint_iff.mpr, add_zero, continuous_const_add, continuous_sub_left, disjoint_iff, eventually, eventually_mem_nhdsWithin, mem_interior_iff_mem_nhds, openSegment, sub_zero, tendsto, tendsto_inf_left, v_ne, x_ext, x_int
-/
theorem disjoint_interior_extremePoints {E : Type*} [AddCommGroup E] [Module Real E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul Real E] [Nontrivial E]
    (S : Set E) : Disjoint (interior S) (extremePoints Real S) := by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ => ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : forallᶠ v in 𝓝[!=] 0, x - v in S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : forallᶠ v in 𝓝[!=] 0, x + v in S :=
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
.exists .and eventually_mem_nhdsWithin obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v != 0)⟩ := h₁.and h₂
  have key : x in openSegment Real (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]

/--
lemma `StrictConvex.sdiff_interior_subset_extremePoints` / 引理 `StrictConvex.sdiff_interior_subset_extremePoints`

English:
lemma StrictConvex.sdiff_interior_subset_extremePoints
  statement: {𝕜 A : Type*} [Semiring 𝕜]
  proof: by
  refine fun x hx => ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ => ?_⟩
  have hyz : y = z := by
    by_contra
exact hx.2 hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

@[deprecated (since := "2026-06-03")]
alias StrictConvex.diff_interior_subset_extremePoints :=
  StrictConvex.sdiff_interior_subset_extremePoints

中文:
引理 严格凸.sdiff_interior_subset_extremePoints
  结论: {𝕜 A : 类型} [半环 𝕜]
  证明: by
  refine fun x hx => ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ => ?_⟩
  have hyz : y = z := by
    by_contra
exact hx.2 hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

@[deprecated (since := "2026-06-03")]
alias StrictConvex.diff_interior_subset_extremePoints :=
  StrictConvex.sdiff_interior_subset_extremePoints

Depends on / 依赖: add_smul, one_smul
-/
lemma StrictConvex.sdiff_interior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set A}
    (hc : StrictConvex 𝕜 C) : C \ interior C subseteq extremePoints 𝕜 C := by
  refine fun x hx => ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ => ?_⟩
  have hyz : y = z := by
    by_contra
exact hx.2 hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

@[deprecated (since := "2026-06-03")]
alias StrictConvex.diff_interior_subset_extremePoints :=
  StrictConvex.sdiff_interior_subset_extremePoints

section Normed
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]

/--
theorem `extremePoints_closedBall_subset_sphere` / 定理 `extremePoints_closedBall_subset_sphere`

English:
theorem extremePoints_closedBall_subset_sphere
  given: [Nontrivial A] {x : A} {r : Real}
  proof: by
  rw [← closedBall_sdiff_ball]; rw [subset_sdiff]; rw [← interior_closedBall' _]
.symm⟩ exact ⟨extremePoints_subset, disjoint_interior_extremePoints _

中文:
定理 extremePoints_closedBall_subset_sphere
  条件: [非平凡 A] {x : A} {r : 实数}
  证明: by
  rw [← closedBall_sdiff_ball]; rw [subset_sdiff]; rw [← interior_closedBall' _]
.symm⟩ exact ⟨extremePoints_subset, disjoint_interior_extremePoints _

Depends on / 依赖: closedBall_sdiff_ball, disjoint_interior_extremePoints, extremePoints_subset, interior_closedBall, subset_sdiff
-/
theorem extremePoints_closedBall_subset_sphere [Nontrivial A] {x : A} {r : Real} :
    extremePoints Real (closedBall x r) subseteq sphere x r := by
  rw [← closedBall_sdiff_ball]; rw [subset_sdiff]; rw [← interior_closedBall' _]
.symm⟩ exact ⟨extremePoints_subset, disjoint_interior_extremePoints _

/--
theorem `StrictConvex.extremePoints_eq_sdiff_interior` / 定理 `StrictConvex.extremePoints_eq_sdiff_interior`

English:
theorem StrictConvex.extremePoints_eq_sdiff_interior
  statement: [Nontrivial A] {S : Set A}
  proof: antisymm (subset_sdiff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.sdiff_interior_subset_extremePoints

@[deprecated (since := "2026-06-03")]
alias StrictConvex.extremePoints_eq_diff_interior := StrictConvex.extremePoints_eq_sdiff_interior

中文:
定理 严格凸.extremePoints_eq_sdiff_interior
  结论: [非平凡 A] {S : 集合 A}
  证明: antisymm (subset_sdiff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.sdiff_interior_subset_extremePoints

@[deprecated (since := "2026-06-03")]
alias StrictConvex.extremePoints_eq_diff_interior := StrictConvex.extremePoints_eq_sdiff_interior

Depends on / 依赖: antisymm, disjoint_interior_extremePoints, extremePoints_subset, hS.sdiff_interior_subset_extremePoints, sdiff_interior_subset_extremePoints, subset_sdiff, subset_sdiff.mpr
-/
theorem StrictConvex.extremePoints_eq_sdiff_interior [Nontrivial A] {S : Set A}
    (hS : StrictConvex Real S) : extremePoints Real S = S \ interior S :=
  antisymm (subset_sdiff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.sdiff_interior_subset_extremePoints

@[deprecated (since := "2026-06-03")]
alias StrictConvex.extremePoints_eq_diff_interior := StrictConvex.extremePoints_eq_sdiff_interior

/--
lemma `StrictConvexSpace.sphere_subset_extremePoints_closedBall` / 引理 `StrictConvexSpace.sphere_subset_extremePoints_closedBall`

English:
lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall
  statement: [StrictConvexSpace Real A]
  proof: fun _ hx => by
  rw [← frontier_closedBall _ hr]; rw [frontier]; rw [closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall Real _ _).sdiff_interior_subset_extremePoints hx

中文:
引理 严格凸空间.sphere_subset_extremePoints_closedBall
  结论: [严格凸空间 实数 A]
  证明: fun _ hx => by
  rw [← frontier_closedBall _ hr]; rw [frontier]; rw [closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall Real _ _).sdiff_interior_subset_extremePoints hx

Depends on / 依赖: _root_, _root_.strictConvex_closedBall, closure_closedBall, frontier, frontier_closedBall, sdiff_interior_subset_extremePoints, strictConvex_closedBall
-/
lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpace Real A]
    (a : A) {r : Real} (hr : r != 0) : sphere a r subseteq extremePoints Real (closedBall a r) := fun _ hx => by
  rw [← frontier_closedBall _ hr]; rw [frontier]; rw [closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall Real _ _).sdiff_interior_subset_extremePoints hx

/--
theorem `StrictConvexSpace.extremePoints_closedBall_eq_sphere` / 定理 `StrictConvexSpace.extremePoints_closedBall_eq_sphere`

English:
theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere
  statement: [Nontrivial A] {x : A} {r : Real}
  proof: by
  rw [(_root_.strictConvex_closedBall Real x r).extremePoints_eq_sdiff_interior]; rw [interior_closedBall']; rw [closedBall_sdiff_ball]

中文:
定理 严格凸空间.extremePoints_closedBall_eq_sphere
  结论: [非平凡 A] {x : A} {r : 实数}
  证明: by
  rw [(_root_.strictConvex_closedBall Real x r).extremePoints_eq_sdiff_interior]; rw [interior_closedBall']; rw [closedBall_sdiff_ball]

Depends on / 依赖: _root_, _root_.strictConvex_closedBall, closedBall_sdiff_ball, extremePoints_eq_sdiff_interior, interior_closedBall, strictConvex_closedBall
-/
theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A} {r : Real}
    [StrictConvexSpace Real A] : extremePoints Real (closedBall x r) = sphere x r := by
  rw [(_root_.strictConvex_closedBall Real x r).extremePoints_eq_sdiff_interior]; rw [interior_closedBall']; rw [closedBall_sdiff_ball]

end Normed

/--
lemma `Set.extremePoints_Icc` / 引理 `Set.extremePoints_Icc`

English:
lemma Set.extremePoints_Icc
  given: {a b : Real} (hab : a <= b)
  proof: by
  rw [Real.Icc_eq_closedBall]; rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]

中文:
引理 集合.extremePoints_Icc
  条件: {a b : 实数} (hab : a <= b)
  证明: by
  rw [Real.Icc_eq_closedBall]; rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]
-/
@[simp] lemma Set.extremePoints_Icc {a b : Real} (hab : a <= b) :
    extremePoints Real (Icc a b) = {a, b} := by
  rw [Real.Icc_eq_closedBall]; rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]
