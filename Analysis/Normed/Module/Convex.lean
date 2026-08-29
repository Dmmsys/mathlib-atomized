/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Metric properties of convex sets in normed spaces

We prove the following facts:

* `convexOn_norm`, `convexOn_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convexOn_univ_norm`, `convexOn_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convexHull_ediam`, `convexHull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `isBounded_convexHull` : convex hull of a set is bounded if and only if the original set
  is bounded.
-/

public section

-- TODO assert_not_exists Cardinal

variable {E : Type*}

open Metric Set

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace Real E]
variable {s : Set E}

/--
theorem `convexOn_norm` / 定理 `convexOn_norm`

English:
theorem convexOn_norm
  given: (hs : Convex Real s)
  statement: ConvexOn Real s norm
  proof: ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ <= ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul]; rw [norm_smul]; rw [Real.norm_of_nonneg ha]; rw [Real.norm_of_nonneg hb]⟩

中文:
定理 convexOn_norm
  条件: (hs : 凸 实数 s)
  结论: ConvexOn 实数 s norm
  证明: ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ <= ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul]; rw [norm_smul]; rw [Real.norm_of_nonneg ha]; rw [Real.norm_of_nonneg hb]⟩

Depends on / 依赖: Real.norm_of_nonneg, norm_add_le, norm_of_nonneg, norm_smul
-/
theorem convexOn_norm (hs : Convex Real s) : ConvexOn Real s norm :=
  ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ <= ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul]; rw [norm_smul]; rw [Real.norm_of_nonneg ha]; rw [Real.norm_of_nonneg hb]⟩

/--
theorem `convexOn_univ_norm` / 定理 `convexOn_univ_norm`

English:
theorem convexOn_univ_norm
  statement: ConvexOn Real univ (norm : E -> Real)
  proof: convexOn_norm convex_univ

中文:
定理 convexOn_univ_norm
  结论: ConvexOn 实数 univ (norm : E -> 实数)
  证明: convexOn_norm convex_univ

Depends on / 依赖: convexOn_norm, convex_univ
-/
theorem convexOn_univ_norm : ConvexOn Real univ (norm : E -> Real) :=
  convexOn_norm convex_univ

/--
theorem `convexOn_dist` / 定理 `convexOn_dist`

English:
theorem convexOn_dist
  given: (z : E) (hs : Convex Real s)
  statement: ConvexOn Real s fun z' => dist z' z
  proof: by
  simpa [dist_eq_norm, preimage_preimage] using!
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id Real E - AffineMap.const Real E z)

中文:
定理 convexOn_dist
  条件: (z : E) (hs : 凸 实数 s)
  结论: ConvexOn 实数 s fun z' => dist z' z
  证明: by
  simpa [dist_eq_norm, preimage_preimage] using!
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id Real E - AffineMap.const Real E z)

Depends on / 依赖: AffineMap, AffineMap.const, AffineMap.id, comp_affineMap, convexOn_norm, dist_eq_norm, hs.translate, preimage_preimage, translate
-/
theorem convexOn_dist (z : E) (hs : Convex Real s) : ConvexOn Real s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using!
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id Real E - AffineMap.const Real E z)

/--
theorem `convexOn_univ_dist` / 定理 `convexOn_univ_dist`

English:
theorem convexOn_univ_dist
  given: (z : E)
  statement: ConvexOn Real univ fun z' => dist z' z
  proof: convexOn_dist z convex_univ

中文:
定理 convexOn_univ_dist
  条件: (z : E)
  结论: ConvexOn 实数 univ fun z' => dist z' z
  证明: convexOn_dist z convex_univ

Depends on / 依赖: convexOn_dist, convex_univ
-/
theorem convexOn_univ_dist (z : E) : ConvexOn Real univ fun z' => dist z' z :=
  convexOn_dist z convex_univ

/--
theorem `convex_ball` / 定理 `convex_ball`

English:
theorem convex_ball
  given: (a : E) (r : Real)
  statement: Convex Real (ball a r)
  proof: by
  simpa only [ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

中文:
定理 convex_ball
  条件: (a : E) (r : 实数)
  结论: 凸 实数 (ball a r)
  证明: by
  simpa only [ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

Depends on / 依赖: convexOn_univ_dist, convex_lt, sep_univ
-/
theorem convex_ball (a : E) (r : Real) : Convex Real (ball a r) := by
  simpa only [ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

/--
theorem `convex_eball` / 定理 `convex_eball`

English:
theorem convex_eball
  given: (a : E) (r : ENNReal)
  statement: Convex Real (eball a r)
  proof: by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]

中文:
定理 convex_eball
  条件: (a : E) (r : 广义非负实数)
  结论: 凸 实数 (eball a r)
  证明: by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]

Depends on / 依赖: convex_ball, convex_univ, eball_coe
-/
theorem convex_eball (a : E) (r : ENNReal) : Convex Real (eball a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]

/--
theorem `convex_closedBall` / 定理 `convex_closedBall`

English:
theorem convex_closedBall
  given: (a : E) (r : Real)
  statement: Convex Real (closedBall a r)
  proof: by
  simpa only [closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

中文:
定理 convex_closedBall
  条件: (a : E) (r : 实数)
  结论: 凸 实数 (closedBall a r)
  证明: by
  simpa only [closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

Depends on / 依赖: closedBall, convexOn_univ_dist, convex_le, sep_univ
-/
theorem convex_closedBall (a : E) (r : Real) : Convex Real (closedBall a r) := by
  simpa only [closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

/--
theorem `segment_subset_closedBall_left` / 定理 `segment_subset_closedBall_left`

English:
theorem segment_subset_closedBall_left
  given: (x y : E)
  statement: segment Real x y subseteq closedBall x (dist x y)
  proof: (convex_closedBall x _).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

中文:
定理 segment_subset_closedBall_left
  条件: (x y : E)
  结论: segment 实数 x y subseteq closedBall x (dist x y)
  证明: (convex_closedBall x _).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

Depends on / 依赖: convex_closedBall, dist_comm, dist_nonneg, le_refl, mem_closedBall, mem_closedBall.mpr, mem_closedBall_self, segment_subset
-/
theorem segment_subset_closedBall_left (x y : E) : segment Real x y subseteq closedBall x (dist x y) :=
  (convex_closedBall x _).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.mpr (dist_comm y x ▸ le_refl _))

/--
theorem `segment_subset_closedBall_right` / 定理 `segment_subset_closedBall_right`

English:
theorem segment_subset_closedBall_right
  given: (x y : E)
  proof: by
  rw [segment_symm]
  exact dist_comm x y ▸ segment_subset_closedBall_left y x

中文:
定理 segment_subset_closedBall_right
  条件: (x y : E)
  证明: by
  rw [segment_symm]
  exact dist_comm x y ▸ segment_subset_closedBall_left y x

Depends on / 依赖: dist_comm, segment_subset_closedBall_left, segment_symm
-/
theorem segment_subset_closedBall_right (x y : E) :
    segment Real x y subseteq closedBall y (dist x y) := by
  rw [segment_symm]
  exact dist_comm x y ▸ segment_subset_closedBall_left y x

/--
theorem `convex_closedEBall` / 定理 `convex_closedEBall`

English:
theorem convex_closedEBall
  given: (a : E) (r : ENNReal)
  statement: Convex Real (closedEBall a r)
  proof: by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

中文:
定理 convex_closedEBall
  条件: (a : E) (r : 广义非负实数)
  结论: 凸 实数 (closedEBall a r)
  证明: by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

Depends on / 依赖: closedEBall_coe, convex_closedBall, convex_univ
-/
theorem convex_closedEBall (a : E) (r : ENNReal) : Convex Real (closedEBall a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

open scoped Pointwise in
/--
theorem `convexHull_sphere_eq_closedBall` / 定理 `convexHull_sphere_eq_closedBall`

English:
theorem convexHull_sphere_eq_closedBall
  statement: {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  proof: by
  suffices convexHull Real (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x]; rw [← vadd_eq_add]; rw [← vadd_sphere]; rw [convexHull_vadd]; rw [this]; rw [vadd_closedBall_zero]; rw [vadd_eq_add]; rw [add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_cl

中文:
定理 convexHull_sphere_eq_closedBall
  结论: {F : 类型} [赋范交换加群 F] [赋范空间 实数 F]
  证明: by
  suffices convexHull Real (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x]; rw [← vadd_eq_add]; rw [← vadd_sphere]; rw [convexHull_vadd]; rw [this]; rw [vadd_closedBall_zero]; rw [vadd_eq_add]; rw [add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_cl

Depends on / 依赖: Invertible, NormedSpace, NormedSpace.sphere_nonempty, add_zero, closedBall, convexHull, convexHull_min, convexHull_vadd, convex_closedBall, hU_sub, mem_convexHull_iff, mem_convexHull_iff.mpr, sphere, sphere_nonempty, sphere_subset_closedBall, subset_antisymm, vadd_closedBall_zero, vadd_eq_add, vadd_sphere, zero_mem
-/
theorem convexHull_sphere_eq_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    [Nontrivial F] (x : F) {r : Real} (hr : 0 <= r) :
    convexHull Real (sphere x r) = closedBall x r := by
  suffices convexHull Real (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x]; rw [← vadd_eq_add]; rw [← vadd_sphere]; rw [convexHull_vadd]; rw [this]; rw [vadd_closedBall_zero]; rw [vadd_eq_add]; rw [add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_closedBall 0 r))
    (fun x h => mem_convexHull_iff.mpr fun U hU_sub hU => ?_)
  have zero_mem : (0 : F) in U := by
    have _ : Invertible (2 : Real) := by use 2⁻¹ <;> grind
    obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (E := F).mpr hr
    rw [← midpoint_self_neg (R := Real) (x := z)]
exact Convex.midpoint_mem hU (hU_sub hz) hU_sub (by simp_all)
  by_cases hr₀ : r = 0
  · simp_all
  by_cases x_zero : x = 0
  · rwa [x_zero]
  set z := (r * ‖x‖⁻¹) • x with hz_def
  have hr₁ : r⁻¹ * ‖x‖ <= 1 := by
    simp only [mem_closedBall, dist_zero_right] at h
    grw [h, inv_mul_le_one]
  have hz : z in U := by
    apply hU_sub
    simp_all [norm_smul]
  have := StarConvex.smul_mem (hU.starConvex zero_mem) hz (by positivity) hr₁
  rwa [hz_def, ← smul_assoc, smul_eq_mul, ← mul_assoc, mul_comm, mul_comm r⁻¹, mul_assoc _ r⁻¹,
    inv_mul_cancel₀ hr₀, mul_one, inv_mul_cancel₀ (by simp_all), one_smul] at this

/--
theorem `convexHull_exists_dist_ge` / 定理 `convexHull_exists_dist_ge`

English:
theorem convexHull_exists_dist_ge
  given: {s : Set E} {x : E} (hx : x in convexHull Real s) (y : E)
  proof: (convexOn_dist y (convex_convexHull Real _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

中文:
定理 convexHull_存在_dist_ge
  条件: {s : 集合 E} {x : E} (hx : x in convexHull 实数 s) (y : E)
  证明: (convexOn_dist y (convex_convexHull Real _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

Depends on / 依赖: convexOn_dist, convex_convexHull, exists_ge_of_mem_convexHull, subset_convexHull
-/
theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x in convexHull Real s) (y : E) :
    exists x' in s, dist x y <= dist x' y :=
  (convexOn_dist y (convex_convexHull Real _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

/--
theorem `Convex.thickening` / 定理 `Convex.thickening`

English:
theorem Convex.thickening
  given: (hs : Convex Real s) (δ : Real)
  statement: Convex Real (thickening δ s)
  proof: by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

中文:
定理 凸.thickening
  条件: (hs : 凸 实数 s) (δ : 实数)
  结论: 凸 实数 (thickening δ s)
  证明: by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

Depends on / 依赖: add_ball_zero, convex_ball, hs.add
-/
theorem Convex.thickening (hs : Convex Real s) (δ : Real) : Convex Real (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

/--
theorem `Convex.cthickening` / 定理 `Convex.cthickening`

English:
theorem Convex.cthickening
  given: (hs : Convex Real s) (δ : Real)
  statement: Convex Real (cthickening δ s)
  proof: by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

中文:
定理 凸.cthickening
  条件: (hs : 凸 实数 s) (δ : 实数)
  结论: 凸 实数 (cthickening δ s)
  证明: by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

Depends on / 依赖: closure, cthickening_eq_iInter_thickening, cthickening_of_nonpos, hs.closure, hs.thickening, le_total, thickening
-/
theorem Convex.cthickening (hs : Convex Real s) (δ : Real) : Convex Real (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

/--
theorem `convexHull_exists_dist_ge2` / 定理 `convexHull_exists_dist_ge2`

English:
theorem convexHull_exists_dist_ge2
  statement: {s t : Set E} {x y : E} (hx : x in convexHull Real s)
  proof: by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

中文:
定理 convexHull_存在_dist_ge2
  结论: {s t : 集合 E} {x y : E} (hx : x in convexHull 实数 s)
  证明: by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

Depends on / 依赖: convexHull_exists_dist_ge, dist_comm, le_trans
-/
theorem convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x in convexHull Real s)
    (hy : y in convexHull Real t) : exists x' in s, exists y' in t, dist x y <= dist x' y' := by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
/--
theorem `convexHull_ediam` / 定理 `convexHull_ediam`

English:
theorem convexHull_ediam
  given: (s : Set E)
  statement: ediam (convexHull Real s) = ediam s
  proof: by
  refine (ediam_le fun x hx y hy => ?_).antisymm (ediam_mono <| subset_convexHull Real s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact edist_le_ediam_of_mem hx' hy'

中文:
定理 convexHull_ediam
  条件: (s : 集合 E)
  结论: ediam (convexHull 实数 s) = ediam s
  证明: by
  refine (ediam_le fun x hx y hy => ?_).antisymm (ediam_mono <| subset_convexHull Real s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact edist_le_ediam_of_mem hx' hy'

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, antisymm, convexHull_exists_dist_ge2, ediam_le, ediam_mono, edist_dist, edist_le_ediam_of_mem, le_trans, ofReal_le_ofReal, subset_convexHull
-/
theorem convexHull_ediam (s : Set E) : ediam (convexHull Real s) = ediam s := by
  refine (ediam_le fun x hx y hy => ?_).antisymm (ediam_mono <| subset_convexHull Real s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact edist_le_ediam_of_mem hx' hy'

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
/--
theorem `convexHull_diam` / 定理 `convexHull_diam`

English:
theorem convexHull_diam
  given: (s : Set E)
  statement: diam (convexHull Real s) = diam s
  proof: by
  simp only [diam, convexHull_ediam]

中文:
定理 convexHull_diam
  条件: (s : 集合 E)
  结论: diam (convexHull 实数 s) = diam s
  证明: by
  simp only [diam, convexHull_ediam]

Depends on / 依赖: convexHull_ediam
-/
theorem convexHull_diam (s : Set E) : diam (convexHull Real s) = diam s := by
  simp only [diam, convexHull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
/--
theorem `isBounded_convexHull` / 定理 `isBounded_convexHull`

English:
theorem isBounded_convexHull
  given: {s : Set E}
  proof: by
  simp only [isBounded_iff_ediam_ne_top, convexHull_ediam]

中文:
定理 isBounded_convexHull
  条件: {s : 集合 E}
  证明: by
  simp only [isBounded_iff_ediam_ne_top, convexHull_ediam]

Depends on / 依赖: convexHull_ediam, isBounded_iff_ediam_ne_top
-/
theorem isBounded_convexHull {s : Set E} :
    Bornology.IsBounded (convexHull Real s) ↔ Bornology.IsBounded s := by
  simp only [isBounded_iff_ediam_ne_top, convexHull_ediam]

instance (priority := 100) NormedSpace.instPathConnectedSpace : PathConnectedSpace E :=
  IsTopologicalAddGroup.pathConnectedSpace

/--
theorem `isConnected_setOfPred_sameRay` / 定理 `isConnected_setOfPred_sameRay`

English:
theorem isConnected_setOfPred_sameRay
  given: (x : E)
  statement: IsConnected { y | SameRay Real x y }
  proof: by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay := isConnected_setOfPred_sameRay

中文:
定理 isConnected_setOfPred_sameRay
  条件: (x : E)
  结论: 是连通 { y | SameRay 实数 x y }
  证明: by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay := isConnected_setOfPred_sameRay

Depends on / 依赖: exists_nonneg_left_iff_sameRay, fun_prop, isConnected_Ici, isConnected_Ici.image, isConnected_univ, simp_rw
-/
theorem isConnected_setOfPred_sameRay (x : E) : IsConnected { y | SameRay Real x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay := isConnected_setOfPred_sameRay

/--
theorem `isConnected_setOfPred_sameRay_and_ne_zero` / 定理 `isConnected_setOfPred_sameRay_and_ne_zero`

English:
theorem isConnected_setOfPred_sameRay_and_ne_zero
  given: {x : E} (hx : x != 0)
  proof: by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay_and_ne_zero := isConnected_setOfPred_sameRay_and_ne_zero

中文:
定理 isConnected_setOfPred_sameRay_and_ne_zero
  条件: {x : E} (hx : x != 0)
  证明: by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay_and_ne_zero := isConnected_setOfPred_sameRay_and_ne_zero

Depends on / 依赖: exists_pos_left_iff_sameRay_and_ne_zero, fun_prop, isConnected_Ioi, isConnected_Ioi.image, simp_rw
-/
theorem isConnected_setOfPred_sameRay_and_ne_zero {x : E} (hx : x != 0) :
    IsConnected { y | SameRay Real x y ∧ y != 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sameRay_and_ne_zero := isConnected_setOfPred_sameRay_and_ne_zero

/--
lemma `norm_sub_le_of_mem_segment` / 引理 `norm_sub_le_of_mem_segment`

English:
lemma norm_sub_le_of_mem_segment
  given: {x y z : E} (hy : y in segment Real x z)
  proof: by
  rw [segment_eq_image'] at hy
  simp only [mem_image, mem_Icc] at hy
  obtain ⟨u, ⟨hu_nonneg, hu_le_one⟩, rfl⟩ := hy
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hu_nonneg]
  conv_rhs => rw [← one_mul (‖z - x‖)]
  gcongr

中文:
引理 norm_sub_le_of_mem_segment
  条件: {x y z : E} (hy : y in segment 实数 x z)
  证明: by
  rw [segment_eq_image'] at hy
  simp only [mem_image, mem_Icc] at hy
  obtain ⟨u, ⟨hu_nonneg, hu_le_one⟩, rfl⟩ := hy
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hu_nonneg]
  conv_rhs => rw [← one_mul (‖z - x‖)]
  gcongr

Depends on / 依赖: Real.norm_eq_abs, abs_of_nonneg, add_sub_cancel_left, conv_rhs, hu_le_one, hu_nonneg, mem_Icc, mem_image, norm_eq_abs, norm_smul, one_mul, segment_eq_image
-/
lemma norm_sub_le_of_mem_segment {x y z : E} (hy : y in segment Real x z) :
    ‖y - x‖ <= ‖z - x‖ := by
  rw [segment_eq_image'] at hy
  simp only [mem_image, mem_Icc] at hy
  obtain ⟨u, ⟨hu_nonneg, hu_le_one⟩, rfl⟩ := hy
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hu_nonneg]
  conv_rhs => rw [← one_mul (‖z - x‖)]
  gcongr

namespace Filter

open scoped Convex Topology
variable {α : Type*} {f : Filter α} {x : E} {y z : α -> E} {r : α -> E -> Prop}

/--
theorem `Eventually.segment_of_prod_nhds` / 定理 `Eventually.segment_of_prod_nhds`

English:
theorem Eventually.segment_of_prod_nhds
  statement: (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
  proof: by
  obtain ⟨p, hp, δ, hδ, hr⟩ := eventually_prod_nhds_iff.mp hr
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ] with χ hp hy hz
exact fun v hv => hr hp convex_iff_segment_subset.mp (convex_ball x δ) hy hz hv

中文:
定理 Eventually.segment_of_prod_nhds
  结论: (hy : 收敛 y f (𝓝 x)) (hz : 收敛 z f (𝓝 x))
  证明: by
  obtain ⟨p, hp, δ, hδ, hr⟩ := eventually_prod_nhds_iff.mp hr
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ] with χ hp hy hz
exact fun v hv => hr hp convex_iff_segment_subset.mp (convex_ball x δ) hy hz hv

Depends on / 依赖: Metric, Metric.tendsto_nhds, convex_ball, convex_iff_segment_subset, convex_iff_segment_subset.mp, eventually_prod_nhds_iff, eventually_prod_nhds_iff.mp, filter_upwards, tendsto_nhds
-/
theorem Eventually.segment_of_prod_nhds (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : forallᶠ p in f ×ˢ 𝓝 x, r p.1 p.2) : forallᶠ χ in f, forall v in [y χ -[Real] z χ], r χ v := by
  obtain ⟨p, hp, δ, hδ, hr⟩ := eventually_prod_nhds_iff.mp hr
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ] with χ hp hy hz
exact fun v hv => hr hp convex_iff_segment_subset.mp (convex_ball x δ) hy hz hv

/--
theorem `Eventually.segment_of_prod_nhdsWithin` / 定理 `Eventually.segment_of_prod_nhdsWithin`

English:
theorem Eventually.segment_of_prod_nhdsWithin
  statement: (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
  proof: by
refine seg.mp .mono ?_ (fun _ => forall₂_imp)
  apply Eventually.segment_of_prod_nhds hy hz
  simpa [nhdsWithin, prod_eq_inf, ← inf_assoc, eventually_inf_principal] using hr

中文:
定理 Eventually.segment_of_prod_nhdsWithin
  结论: (hy : 收敛 y f (𝓝 x)) (hz : 收敛 z f (𝓝 x))
  证明: by
refine seg.mp .mono ?_ (fun _ => forall₂_imp)
  apply Eventually.segment_of_prod_nhds hy hz
  simpa [nhdsWithin, prod_eq_inf, ← inf_assoc, eventually_inf_principal] using hr

Depends on / 依赖: Eventually, Eventually.segment_of_prod_nhds, eventually_inf_principal, inf_assoc, nhdsWithin, prod_eq_inf, seg.mp, segment_of_prod_nhds
-/
theorem Eventually.segment_of_prod_nhdsWithin (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : forallᶠ p in f ×ˢ 𝓝[s] x, r p.1 p.2) (seg : forallᶠ χ in f, [y χ -[Real] z χ] subseteq s) :
    forallᶠ χ in f, forall v in [y χ -[Real] z χ], r χ v := by
refine seg.mp .mono ?_ (fun _ => forall₂_imp)
  apply Eventually.segment_of_prod_nhds hy hz
  simpa [nhdsWithin, prod_eq_inf, ← inf_assoc, eventually_inf_principal] using hr

end Filter

end SeminormedAddCommGroup
