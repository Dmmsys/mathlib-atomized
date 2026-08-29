/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Strictly convex spaces

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).

## Main definitions

`StrictConvexSpace`: a typeclass saying that a given normed space over a normed linear ordered
field (e.g., `ℝ` or `ℚ`) is strictly convex. The definition requires strict convexity of a closed
ball of positive radius with center at the origin; strict convexity of any other closed ball follows
from this assumption.

## Main results

In a strictly convex space, we prove

- `strictConvex_closedBall`: a closed ball is strictly convex.
- `combo_mem_ball_of_ne`, `openSegment_subset_ball_of_ne`, `norm_combo_lt_of_ne`:
  a nontrivial convex combination of two points in a closed ball belong to the corresponding open
  ball;
- `norm_add_lt_of_not_sameRay`, `sameRay_iff_norm_add`, `dist_add_dist_eq_iff`:
  the triangle inequality `dist x y + dist y z ≤ dist x z` is a strict inequality unless `y` belongs
  to the segment `[x -[ℝ] z]`.
- `Isometry.affineIsometryOfStrictConvexSpace`: an isometry of `NormedAddTorsor`s for real
  normed spaces, strictly convex in the case of the codomain, is an affine isometry.

We also provide several lemmas that can be used as alternative constructors for `StrictConvex ℝ E`:

- `StrictConvexSpace.of_strictConvex_unitClosedBall`: if `closed_ball (0 : E) 1` is strictly
  convex, then `E` is a strictly convex space;

- `StrictConvexSpace.of_norm_add`: if `‖x + y‖ = ‖x‖ + ‖y‖` implies `SameRay ℝ x y` for all
  nonzero `x y : E`, then `E` is a strictly convex space.

## Implementation notes

While the definition is formulated for any normed linear ordered field, most of the lemmas are
formulated only for the case `𝕜 = ℝ`.

## Tags

convex, strictly convex
-/

public section

open Convex Pointwise Set Metric

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strictConvex_closedBall` below.

See also `StrictConvexSpace.of_strictConvex_unitClosedBall`. -/
@[mk_iff]
/--
Definition of `StrictConvexSpace` / `StrictConvexSpace` 的定义

English:
class StrictConvexSpace
  parameters: (𝕜 E : Type*) [NormedField 𝕜] [PartialOrder 𝕜]
  axioms and operations (1):
    - strictConvex_closedBall : forall r : Real, 0 < r -> StrictConvex 𝕜 (closedBall (0 : E) r)

中文:
类 严格凸空间
  参数: (𝕜 E : 类型) [赋范域 𝕜] [偏序 𝕜]
  公理与运算 (1 个):
    - strictConvex_closedBall : 对任意 r : 实数, 0 < r -> 严格凸 𝕜 (closedBall (0 : E) r)
-/
class StrictConvexSpace (𝕜 E : Type*) [NormedField 𝕜] [PartialOrder 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop where
  strictConvex_closedBall : forall r : Real, 0 < r -> StrictConvex 𝕜 (closedBall (0 : E) r)

variable (𝕜 : Type*) {E : Type*} [NormedField 𝕜] [PartialOrder 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `strictConvex_closedBall` / 定理 `strictConvex_closedBall`

English:
theorem strictConvex_closedBall
  given: [StrictConvexSpace 𝕜 E] (x : E) (r : Real)
  proof: by
  rcases le_or_gt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _

中文:
定理 strictConvex_closedBall
  条件: [严格凸空间 𝕜 E] (x : E) (r : 实数)
  证明: by
  rcases le_or_gt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _

Depends on / 依赖: StrictConvexSpace, StrictConvexSpace.strictConvex_closedBall, le_or_gt, strictConvex, strictConvex_closedBall, subsingleton_closedBall, vadd_closedBall_zero
-/
theorem strictConvex_closedBall [StrictConvexSpace 𝕜 E] (x : E) (r : Real) :
    StrictConvex 𝕜 (closedBall x r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _

variable [NormedSpace Real E]

/--
theorem `StrictConvexSpace.of_strictConvex_unitClosedBall` / 定理 `StrictConvexSpace.of_strictConvex_unitClosedBall`

English:
theorem StrictConvexSpace.of_strictConvex_unitClosedBall
  statement: [LinearMap.CompatibleSMul E E 𝕜 Real]
  proof: ⟨fun r hr => by simpa only [smul_unitClosedBall_of_nonneg hr.le] using h.smul r⟩

中文:
定理 严格凸空间.of_strictConvex_unitClosedBall
  结论: [线性映射.余mpatibleSMul E E 𝕜 实数]
  证明: ⟨fun r hr => by simpa only [smul_unitClosedBall_of_nonneg hr.le] using h.smul r⟩

Depends on / 依赖: h.smul, hr.le, smul_unitClosedBall_of_nonneg
-/
theorem StrictConvexSpace.of_strictConvex_unitClosedBall [LinearMap.CompatibleSMul E E 𝕜 Real]
    (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) : StrictConvexSpace 𝕜 E :=
  ⟨fun r hr => by simpa only [smul_unitClosedBall_of_nonneg hr.le] using h.smul r⟩

/--
theorem `StrictConvexSpace.of_norm_combo_lt_one` / 定理 `StrictConvexSpace.of_norm_combo_lt_one`

English:
theorem StrictConvexSpace.of_norm_combo_lt_one
  proof: by
  refine
    StrictConvexSpace.of_strictConvex_unitClosedBall Real
      ((convex_closedBall _ _).strictConvex' fun x hx y hy hne => ?_)
  rw [interior_closedBall (0 : E) one_ne_zero]; rw [closedBall_sdiff_ball]; rw [mem_sphere_zero_iff_norm] at hx hy
  rcases h x y hx hy hne with ⟨a, b, hab, hlt

中文:
定理 严格凸空间.of_norm_combo_lt_one
  证明: by
  refine
    StrictConvexSpace.of_strictConvex_unitClosedBall Real
      ((convex_closedBall _ _).strictConvex' fun x hx y hy hne => ?_)
  rw [interior_closedBall (0 : E) one_ne_zero]; rw [closedBall_sdiff_ball]; rw [mem_sphere_zero_iff_norm] at hx hy
  rcases h x y hx hy hne with ⟨a, b, hab, hlt

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, StrictConvexSpace, StrictConvexSpace.of_strictConvex_unitClosedBall, closedBall_sdiff_ball, convex_closedBall, hab.symm, interior_closedBall, lineMap_apply_module, mem_ball_zero_iff, mem_sphere_zero_iff_norm, of_strictConvex_unitClosedBall, one_ne_zero, strictConvex, sub_eq_iff_eq_add
-/
theorem StrictConvexSpace.of_norm_combo_lt_one
    (h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> exists a b : Real, a + b = 1 ∧ ‖a • x + b • y‖ < 1) :
    StrictConvexSpace Real E := by
  refine
    StrictConvexSpace.of_strictConvex_unitClosedBall Real
      ((convex_closedBall _ _).strictConvex' fun x hx y hy hne => ?_)
  rw [interior_closedBall (0 : E) one_ne_zero]; rw [closedBall_sdiff_ball]; rw [mem_sphere_zero_iff_norm] at hx hy
  rcases h x y hx hy hne with ⟨a, b, hab, hlt⟩
  use b
  rwa [AffineMap.lineMap_apply_module, interior_closedBall (0 : E) one_ne_zero, mem_ball_zero_iff,
    sub_eq_iff_eq_add.2 hab.symm]

/--
theorem `StrictConvexSpace.of_norm_combo_ne_one` / 定理 `StrictConvexSpace.of_norm_combo_ne_one`

English:
theorem StrictConvexSpace.of_norm_combo_ne_one
  proof: by
  refine StrictConvexSpace.of_strictConvex_unitClosedBall Real
    ((convex_closedBall _ _).strictConvex ?_)
  simp only [interior_closedBall _ one_ne_zero, closedBall_sdiff_ball, Set.Pairwise,
    frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
  intro x hx y hy hne
  rcases h x y h

中文:
定理 严格凸空间.of_norm_combo_ne_one
  证明: by
  refine StrictConvexSpace.of_strictConvex_unitClosedBall Real
    ((convex_closedBall _ _).strictConvex ?_)
  simp only [interior_closedBall _ one_ne_zero, closedBall_sdiff_ball, Set.Pairwise,
    frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
  intro x hx y hy hne
  rcases h x y h

Depends on / 依赖: Pairwise, Set.Pairwise, StrictConvexSpace, StrictConvexSpace.of_strictConvex_unitClosedBall, closedBall_sdiff_ball, convex_closedBall, frontier_closedBall, interior_closedBall, mem_sphere_zero_iff_norm, of_strictConvex_unitClosedBall, one_ne_zero, strictConvex
-/
theorem StrictConvexSpace.of_norm_combo_ne_one
    (h :
      forall x y : E,
        ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> exists a b : Real, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ ‖a • x + b • y‖ != 1) :
    StrictConvexSpace Real E := by
  refine StrictConvexSpace.of_strictConvex_unitClosedBall Real
    ((convex_closedBall _ _).strictConvex ?_)
  simp only [interior_closedBall _ one_ne_zero, closedBall_sdiff_ball, Set.Pairwise,
    frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
  intro x hx y hy hne
  rcases h x y hx hy hne with ⟨a, b, ha, hb, hab, hne'⟩
  exact ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, mt mem_sphere_zero_iff_norm.1 hne'⟩

/--
theorem `StrictConvexSpace.of_norm_add_ne_two` / 定理 `StrictConvexSpace.of_norm_add_ne_two`

English:
theorem StrictConvexSpace.of_norm_add_ne_two
  proof: by
  refine
    StrictConvexSpace.of_norm_combo_ne_one fun x y hx hy hne =>
      ⟨1 / 2, 1 / 2, one_half_pos.le, one_half_pos.le, add_halves _, ?_⟩
  rw [← smul_add]; rw [norm_smul]; rw [Real.norm_of_nonneg one_half_pos.le]; rw [one_div]; rw [← div_eq_inv_mul]; rw [Ne]; rw [div_eq_one_iff_eq (two_n

中文:
定理 严格凸空间.of_norm_add_ne_two
  证明: by
  refine
    StrictConvexSpace.of_norm_combo_ne_one fun x y hx hy hne =>
      ⟨1 / 2, 1 / 2, one_half_pos.le, one_half_pos.le, add_halves _, ?_⟩
  rw [← smul_add]; rw [norm_smul]; rw [Real.norm_of_nonneg one_half_pos.le]; rw [one_div]; rw [← div_eq_inv_mul]; rw [Ne]; rw [div_eq_one_iff_eq (two_n

Depends on / 依赖: Real.norm_of_nonneg, StrictConvexSpace, StrictConvexSpace.of_norm_combo_ne_one, add_halves, div_eq_inv_mul, div_eq_one_iff_eq, norm_of_nonneg, norm_smul, of_norm_combo_ne_one, one_div, one_half_pos, one_half_pos.le, smul_add, two_ne_zero
-/
theorem StrictConvexSpace.of_norm_add_ne_two
    (h : forall ⦃x y : E⦄, ‖x‖ = 1 -> ‖y‖ = 1 -> x != y -> ‖x + y‖ != 2) : StrictConvexSpace Real E := by
  refine
    StrictConvexSpace.of_norm_combo_ne_one fun x y hx hy hne =>
      ⟨1 / 2, 1 / 2, one_half_pos.le, one_half_pos.le, add_halves _, ?_⟩
  rw [← smul_add]; rw [norm_smul]; rw [Real.norm_of_nonneg one_half_pos.le]; rw [one_div]; rw [← div_eq_inv_mul]; rw [Ne]; rw [div_eq_one_iff_eq (two_ne_zero' Real)]
  exact h hx hy hne

/--
theorem `StrictConvexSpace.of_pairwise_sphere_norm_ne_two` / 定理 `StrictConvexSpace.of_pairwise_sphere_norm_ne_two`

English:
theorem StrictConvexSpace.of_pairwise_sphere_norm_ne_two
  proof: StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy =>
    h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)

中文:
定理 严格凸空间.of_pairwise_sphere_norm_ne_two
  证明: StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy =>
    h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)

Depends on / 依赖: StrictConvexSpace, StrictConvexSpace.of_norm_add_ne_two, mem_sphere_zero_iff_norm, of_norm_add_ne_two
-/
theorem StrictConvexSpace.of_pairwise_sphere_norm_ne_two
    (h : (sphere (0 : E) 1).Pairwise fun x y => ‖x + y‖ != 2) : StrictConvexSpace Real E :=
  StrictConvexSpace.of_norm_add_ne_two fun _ _ hx hy =>
    h (mem_sphere_zero_iff_norm.2 hx) (mem_sphere_zero_iff_norm.2 hy)

/--
theorem `StrictConvexSpace.of_norm_add` / 定理 `StrictConvexSpace.of_norm_add`

English:
theorem StrictConvexSpace.of_norm_add
  proof: by
  refine StrictConvexSpace.of_pairwise_sphere_norm_ne_two fun x hx y hy => mt fun h₂ => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  exact (sameRay_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)

中文:
定理 严格凸空间.of_norm_add
  证明: by
  refine StrictConvexSpace.of_pairwise_sphere_norm_ne_two fun x hx y hy => mt fun h₂ => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  exact (sameRay_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)

Depends on / 依赖: StrictConvexSpace, StrictConvexSpace.of_pairwise_sphere_norm_ne_two, hx.trans, hy.symm, mem_sphere_zero_iff_norm, of_pairwise_sphere_norm_ne_two, sameRay_iff_of_norm_eq
-/
theorem StrictConvexSpace.of_norm_add
    (h : forall x y : E, ‖x‖ = 1 -> ‖y‖ = 1 -> ‖x + y‖ = 2 -> SameRay Real x y) : StrictConvexSpace Real E := by
  refine StrictConvexSpace.of_pairwise_sphere_norm_ne_two fun x hx y hy => mt fun h₂ => ?_
  rw [mem_sphere_zero_iff_norm] at hx hy
  exact (sameRay_iff_of_norm_eq (hx.trans hy.symm)).1 (h x y hx hy h₂)

variable [StrictConvexSpace Real E] {x y z : E} {a b r : Real}

/--
theorem `combo_mem_ball_of_ne` / 定理 `combo_mem_ball_of_ne`

English:
theorem combo_mem_ball_of_ne
  statement: (hx : x in closedBall z r) (hy : y in closedBall z r) (hne : x != y)
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, mem_singleton_iff] at hx hy
    exact (hne (hx.trans hy.symm)).elim
  · simp only [← interior_closedBall _ hr] at hx hy ⊢
    exact strictConvex_closedBall Real z r hx hy hne ha hb hab

中文:
定理 combo_mem_ball_of_ne
  结论: (hx : x in closedBall z r) (hy : y in closedBall z r) (hne : x != y)
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, mem_singleton_iff] at hx hy
    exact (hne (hx.trans hy.symm)).elim
  · simp only [← interior_closedBall _ hr] at hx hy ⊢
    exact strictConvex_closedBall Real z r hx hy hne ha hb hab

Depends on / 依赖: closedBall_zero, eq_or_ne, hx.trans, hy.symm, interior_closedBall, mem_singleton_iff, strictConvex_closedBall
-/
theorem combo_mem_ball_of_ne (hx : x in closedBall z r) (hy : y in closedBall z r) (hne : x != y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a • x + b • y in ball z r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, mem_singleton_iff] at hx hy
    exact (hne (hx.trans hy.symm)).elim
  · simp only [← interior_closedBall _ hr] at hx hy ⊢
    exact strictConvex_closedBall Real z r hx hy hne ha hb hab

/--
theorem `openSegment_subset_ball_of_ne` / 定理 `openSegment_subset_ball_of_ne`

English:
theorem openSegment_subset_ball_of_ne
  statement: (hx : x in closedBall z r) (hy : y in closedBall z r)
  proof: (openSegment_subset_iff _).2 fun _ _ => combo_mem_ball_of_ne hx hy hne

中文:
定理 openSegment_subset_ball_of_ne
  结论: (hx : x in closedBall z r) (hy : y in closedBall z r)
  证明: (openSegment_subset_iff _).2 fun _ _ => combo_mem_ball_of_ne hx hy hne

Depends on / 依赖: combo_mem_ball_of_ne, openSegment_subset_iff
-/
theorem openSegment_subset_ball_of_ne (hx : x in closedBall z r) (hy : y in closedBall z r)
    (hne : x != y) : openSegment Real x y subseteq ball z r :=
  (openSegment_subset_iff _).2 fun _ _ => combo_mem_ball_of_ne hx hy hne

/--
theorem `norm_combo_lt_of_ne` / 定理 `norm_combo_lt_of_ne`

English:
theorem norm_combo_lt_of_ne
  statement: (hx : ‖x‖ <= r) (hy : ‖y‖ <= r) (hne : x != y) (ha : 0 < a) (hb : 0 < b)
  proof: by
  simp only [← mem_ball_zero_iff, ← mem_closedBall_zero_iff] at hx hy ⊢
  exact combo_mem_ball_of_ne hx hy hne ha hb hab

中文:
定理 norm_combo_lt_of_ne
  结论: (hx : ‖x‖ <= r) (hy : ‖y‖ <= r) (hne : x != y) (ha : 0 < a) (hb : 0 < b)
  证明: by
  simp only [← mem_ball_zero_iff, ← mem_closedBall_zero_iff] at hx hy ⊢
  exact combo_mem_ball_of_ne hx hy hne ha hb hab

Depends on / 依赖: combo_mem_ball_of_ne, mem_ball_zero_iff, mem_closedBall_zero_iff
-/
theorem norm_combo_lt_of_ne (hx : ‖x‖ <= r) (hy : ‖y‖ <= r) (hne : x != y) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : ‖a • x + b • y‖ < r := by
  simp only [← mem_ball_zero_iff, ← mem_closedBall_zero_iff] at hx hy ⊢
  exact combo_mem_ball_of_ne hx hy hne ha hb hab

/--
theorem `norm_add_lt_of_not_sameRay` / 定理 `norm_add_lt_of_not_sameRay`

English:
theorem norm_add_lt_of_not_sameRay
  given: (h : ¬SameRay Real x y)
  statement: ‖x + y‖ < ‖x‖ + ‖y‖
  proof: by
  simp only [sameRay_iff_inv_norm_smul_eq, not_or, ← Ne.eq_def] at h
  rcases h with ⟨hx, hy, hne⟩
  rw [← norm_pos_iff] at hx hy
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy
  have :=
    combo_mem_ball_of_ne (inv_norm_smul_mem_unitClosedBall x)
      (inv_norm_smul_mem_unitClosedBall y) hne (div

中文:
定理 norm_add_lt_of_not_sameRay
  条件: (h : ¬SameRay 实数 x y)
  结论: ‖x + y‖ < ‖x‖ + ‖y‖
  证明: by
  simp only [sameRay_iff_inv_norm_smul_eq, not_or, ← Ne.eq_def] at h
  rcases h with ⟨hx, hy, hne⟩
  rw [← norm_pos_iff] at hx hy
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy
  have :=
    combo_mem_ball_of_ne (inv_norm_smul_mem_unitClosedBall x)
      (inv_norm_smul_mem_unitClosedBall y) hne (div

Depends on / 依赖: Ne.eq_def, Real.no, add_div, add_pos, combo_mem_ball_of_ne, div_eq_inv_mul, div_pos, div_self, eq_def, hx.ne, hxy.ne, hy.ne, inv_norm_smul_mem_unitClosedBall, mem_ball_zero_iff, mul_smul, norm_pos_iff, norm_smul, not_or, sameRay_iff_inv_norm_smul_eq, smul_add
-/
theorem norm_add_lt_of_not_sameRay (h : ¬SameRay Real x y) : ‖x + y‖ < ‖x‖ + ‖y‖ := by
  simp only [sameRay_iff_inv_norm_smul_eq, not_or, ← Ne.eq_def] at h
  rcases h with ⟨hx, hy, hne⟩
  rw [← norm_pos_iff] at hx hy
  have hxy : 0 < ‖x‖ + ‖y‖ := add_pos hx hy
  have :=
    combo_mem_ball_of_ne (inv_norm_smul_mem_unitClosedBall x)
      (inv_norm_smul_mem_unitClosedBall y) hne (div_pos hx hxy) (div_pos hy hxy)
      (by rw [← add_div, div_self hxy.ne'])
  rwa [mem_ball_zero_iff, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, smul_inv_smul₀ hx.ne',
    smul_inv_smul₀ hy.ne', ← smul_add, norm_smul, Real.norm_of_nonneg (inv_pos.2 hxy).le, ←
    div_eq_inv_mul, div_lt_one hxy] at this

/--
theorem `lt_norm_sub_of_not_sameRay` / 定理 `lt_norm_sub_of_not_sameRay`

English:
theorem lt_norm_sub_of_not_sameRay
  given: (h : ¬SameRay Real x y)
  statement: ‖x‖ - ‖y‖ < ‖x - y‖
  proof: by
  nth_rw 1 [← sub_add_cancel x y] at h ⊢
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_sameRay fun H' => h <| H'.add_left SameRay.rfl)

中文:
定理 lt_norm_sub_of_not_sameRay
  条件: (h : ¬SameRay 实数 x y)
  结论: ‖x‖ - ‖y‖ < ‖x - y‖
  证明: by
  nth_rw 1 [← sub_add_cancel x y] at h ⊢
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_sameRay fun H' => h <| H'.add_left SameRay.rfl)

Depends on / 依赖: SameRay, SameRay.rfl, add_left, norm_add_lt_of_not_sameRay, nth_rw, sub_add_cancel, sub_lt_iff_lt_add
-/
theorem lt_norm_sub_of_not_sameRay (h : ¬SameRay Real x y) : ‖x‖ - ‖y‖ < ‖x - y‖ := by
  nth_rw 1 [← sub_add_cancel x y] at h ⊢
  exact sub_lt_iff_lt_add.2 (norm_add_lt_of_not_sameRay fun H' => h <| H'.add_left SameRay.rfl)

/--
theorem `abs_lt_norm_sub_of_not_sameRay` / 定理 `abs_lt_norm_sub_of_not_sameRay`

English:
theorem abs_lt_norm_sub_of_not_sameRay
  given: (h : ¬SameRay Real x y)
  statement: |‖x‖ - ‖y‖| < ‖x - y‖
  proof: by
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_sameRay h, ?_⟩
  rw [norm_sub_rev]
  exact lt_norm_sub_of_not_sameRay (mt SameRay.symm h)

中文:
定理 abs_lt_norm_sub_of_not_sameRay
  条件: (h : ¬SameRay 实数 x y)
  结论: |‖x‖ - ‖y‖| < ‖x - y‖
  证明: by
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_sameRay h, ?_⟩
  rw [norm_sub_rev]
  exact lt_norm_sub_of_not_sameRay (mt SameRay.symm h)

Depends on / 依赖: SameRay, SameRay.symm, abs_sub_lt_iff, lt_norm_sub_of_not_sameRay, norm_sub_rev
-/
theorem abs_lt_norm_sub_of_not_sameRay (h : ¬SameRay Real x y) : |‖x‖ - ‖y‖| < ‖x - y‖ := by
  refine abs_sub_lt_iff.2 ⟨lt_norm_sub_of_not_sameRay h, ?_⟩
  rw [norm_sub_rev]
  exact lt_norm_sub_of_not_sameRay (mt SameRay.symm h)

/--
theorem `sameRay_iff_norm_add` / 定理 `sameRay_iff_norm_add`

English:
theorem sameRay_iff_norm_add
  statement: SameRay Real x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖
  proof: ⟨SameRay.norm_add, fun h => Classical.not_not.1 fun h' => (norm_add_lt_of_not_sameRay h').ne h⟩

中文:
定理 sameRay_iff_norm_add
  结论: SameRay 实数 x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖
  证明: ⟨SameRay.norm_add, fun h => Classical.not_not.1 fun h' => (norm_add_lt_of_not_sameRay h').ne h⟩

Depends on / 依赖: Classical, Classical.not_not, SameRay, SameRay.norm_add, norm_add, norm_add_lt_of_not_sameRay, not_not
-/
theorem sameRay_iff_norm_add : SameRay Real x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖ :=
  ⟨SameRay.norm_add, fun h => Classical.not_not.1 fun h' => (norm_add_lt_of_not_sameRay h').ne h⟩

/--
theorem `eq_of_norm_eq_of_norm_add_eq` / 定理 `eq_of_norm_eq_of_norm_add_eq`

English:
theorem eq_of_norm_eq_of_norm_add_eq
  given: (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖)
  statement: x = y
  proof: (sameRay_iff_norm_add.mpr h₂).eq_of_norm_eq h₁

中文:
定理 eq_of_norm_eq_of_norm_add_eq
  条件: (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖)
  结论: x = y
  证明: (sameRay_iff_norm_add.mpr h₂).eq_of_norm_eq h₁

Depends on / 依赖: eq_of_norm_eq, sameRay_iff_norm_add, sameRay_iff_norm_add.mpr
-/
theorem eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y :=
  (sameRay_iff_norm_add.mpr h₂).eq_of_norm_eq h₁

/--
theorem `not_sameRay_iff_norm_add_lt` / 定理 `not_sameRay_iff_norm_add_lt`

English:
theorem not_sameRay_iff_norm_add_lt
  statement: ¬SameRay Real x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖
  proof: sameRay_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm

中文:
定理 not_sameRay_iff_norm_add_lt
  结论: ¬SameRay 实数 x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖
  证明: sameRay_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm

Depends on / 依赖: lt_iff_ne, lt_iff_ne.symm, norm_add_le, sameRay_iff_norm_add, sameRay_iff_norm_add.not.trans
-/
theorem not_sameRay_iff_norm_add_lt : ¬SameRay Real x y ↔ ‖x + y‖ < ‖x‖ + ‖y‖ :=
  sameRay_iff_norm_add.not.trans (norm_add_le _ _).lt_iff_ne.symm

/--
theorem `sameRay_iff_norm_sub` / 定理 `sameRay_iff_norm_sub`

English:
theorem sameRay_iff_norm_sub
  statement: SameRay Real x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖|
  proof: ⟨SameRay.norm_sub, fun h =>
    Classical.not_not.1 fun h' => (abs_lt_norm_sub_of_not_sameRay h').ne' h⟩

中文:
定理 sameRay_iff_norm_sub
  结论: SameRay 实数 x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖|
  证明: ⟨SameRay.norm_sub, fun h =>
    Classical.not_not.1 fun h' => (abs_lt_norm_sub_of_not_sameRay h').ne' h⟩

Depends on / 依赖: Classical, Classical.not_not, SameRay, SameRay.norm_sub, abs_lt_norm_sub_of_not_sameRay, norm_sub, not_not
-/
theorem sameRay_iff_norm_sub : SameRay Real x y ↔ ‖x - y‖ = |‖x‖ - ‖y‖| :=
  ⟨SameRay.norm_sub, fun h =>
    Classical.not_not.1 fun h' => (abs_lt_norm_sub_of_not_sameRay h').ne' h⟩

/--
theorem `not_sameRay_iff_abs_lt_norm_sub` / 定理 `not_sameRay_iff_abs_lt_norm_sub`

English:
theorem not_sameRay_iff_abs_lt_norm_sub
  statement: ¬SameRay Real x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖
  proof: sameRay_iff_norm_sub.not.trans ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm

中文:
定理 not_sameRay_iff_abs_lt_norm_sub
  结论: ¬SameRay 实数 x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖
  证明: sameRay_iff_norm_sub.not.trans ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm

Depends on / 依赖: abs_norm_sub_norm_le, lt_iff_ne, lt_iff_ne.symm, ne_comm, ne_comm.trans, sameRay_iff_norm_sub, sameRay_iff_norm_sub.not.trans
-/
theorem not_sameRay_iff_abs_lt_norm_sub : ¬SameRay Real x y ↔ |‖x‖ - ‖y‖| < ‖x - y‖ :=
sameRay_iff_norm_sub.not.trans ne_comm.trans (abs_norm_sub_norm_le _ _).lt_iff_ne.symm

/--
theorem `norm_midpoint_lt_iff` / 定理 `norm_midpoint_lt_iff`

English:
theorem norm_midpoint_lt_iff
  given: (h : ‖x‖ = ‖y‖)
  statement: ‖(1 / 2 : Real) • (x + y)‖ < ‖x‖ ↔ x != y
  proof: by
  rw [norm_smul]; rw [Real.norm_of_nonneg (one_div_nonneg.2 zero_le_two)]; rw [← inv_eq_one_div]; rw [←
    div_eq_inv_mul]; rw [div_lt_iff₀ (zero_lt_two' Real)]; rw [mul_two]; rw [← not_sameRay_iff_of_norm_eq h]; rw [not_sameRay_iff_norm_add_lt]; rw [h]

中文:
定理 norm_midpoint_lt_iff
  条件: (h : ‖x‖ = ‖y‖)
  结论: ‖(1 / 2 : 实数) • (x + y)‖ < ‖x‖ ↔ x != y
  证明: by
  rw [norm_smul]; rw [Real.norm_of_nonneg (one_div_nonneg.2 zero_le_two)]; rw [← inv_eq_one_div]; rw [←
    div_eq_inv_mul]; rw [div_lt_iff₀ (zero_lt_two' Real)]; rw [mul_two]; rw [← not_sameRay_iff_of_norm_eq h]; rw [not_sameRay_iff_norm_add_lt]; rw [h]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Real.norm_of_nonneg, SeparatingDual, SeparatingDual.exists_separating_of_ne, WeakBilin, WeakBilin.isEmbedding, congr_fun, div_eq_inv_mul, exists_separating_of_ne, inv_eq_one_div, isEmbedding, mul_two, norm_of_nonneg, norm_smul, not_sameRay_iff_norm_add_lt, not_sameRay_iff_of_norm_eq, one_div_nonneg, t2Space, topDualPairing
-/
theorem norm_midpoint_lt_iff (h : ‖x‖ = ‖y‖) : ‖(1 / 2 : Real) • (x + y)‖ < ‖x‖ ↔ x != y := by
  rw [norm_smul]; rw [Real.norm_of_nonneg (one_div_nonneg.2 zero_le_two)]; rw [← inv_eq_one_div]; rw [←
    div_eq_inv_mul]; rw [div_lt_iff₀ (zero_lt_two' Real)]; rw [mul_two]; rw [← not_sameRay_iff_of_norm_eq h]; rw [not_sameRay_iff_norm_add_lt]; rw [h]

/--
Instance `Real.instStrictConvexSpace` / 实例 `Real.instStrictConvexSpace`

English:
instance Real.instStrictConvexSpace
  signature: : StrictConvexSpace Real Real where
  body: strictConvex_iff_convex.mpr (convex_closedBall _ _)

中文:
实例 实数.instStrictConvexSpace
  签名: : 严格凸空间 实数 实数 where
  定义体: strictConvex_iff_convex.mpr (convex_closedBall _ _)

Depends on / 依赖: convex_closedBall, strictConvex_iff_convex, strictConvex_iff_convex.mpr
-/
instance Real.instStrictConvexSpace : StrictConvexSpace Real Real where
  strictConvex_closedBall _ _ := strictConvex_iff_convex.mpr (convex_closedBall _ _)
