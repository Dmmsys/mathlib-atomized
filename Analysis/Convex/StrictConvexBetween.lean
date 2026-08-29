/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Betweenness in affine spaces for strictly convex spaces

This file proves results about betweenness for points in an affine space for a strictly convex
space.

-/

@[expose] public section

open Metric
open scoped Convex

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
variable [StrictConvexSpace Real V]

section PseudoMetricSpace
variable [PseudoMetricSpace P] [NormedAddTorsor V P]

/--
theorem `Sbtw.dist_lt_max_dist` / 定理 `Sbtw.dist_lt_max_dist`

English:
theorem Sbtw.dist_lt_max_dist
  given: (p : P) {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  proof: by
  have hp₁p₃ : p₁ -ᵥ p != p₃ -ᵥ p := by simpa using h.left_ne_right
  rw [Sbtw]; rw [← wbtw_vsub_const_iff p]; rw [Wbtw]; rw [affineSegment_eq_segment]; rw [← insert_endpoints_openSegment]; rw [Set.mem_insert_iff]; rw [Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₁ h)
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₃ h)
  · rw [openSegment_eq_image, Set.mem_image] at h
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)

中文:
定理 Sbtw.dist_lt_max_dist
  条件: (p : P) {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  证明: by
  have hp₁p₃ : p₁ -ᵥ p != p₃ -ᵥ p := by simpa using h.left_ne_right
  rw [Sbtw]; rw [← wbtw_vsub_const_iff p]; rw [Wbtw]; rw [affineSegment_eq_segment]; rw [← insert_endpoints_openSegment]; rw [Set.mem_insert_iff]; rw [Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₁ h)
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₃ h)
  · rw [openSegment_eq_image, Set.mem_image] at h
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)

Depends on / 依赖: False.elim, Set.mem_image, Set.mem_insert_iff, affineSegment_eq_segment, dist_, h.left_ne_right, insert_endpoints_openSegment, left_ne_right, mem_image, mem_insert_iff, openSegment_eq_image, simp_rw, vsub_left_cancel_iff, wbtw_vsub_const_iff
-/
theorem Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) :
    dist p₂ p < max (dist p₁ p) (dist p₃ p) := by
  have hp₁p₃ : p₁ -ᵥ p != p₃ -ᵥ p := by simpa using h.left_ne_right
  rw [Sbtw]; rw [← wbtw_vsub_const_iff p]; rw [Wbtw]; rw [affineSegment_eq_segment]; rw [← insert_endpoints_openSegment]; rw [Set.mem_insert_iff]; rw [Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₁ h)
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₃ h)
  · rw [openSegment_eq_image, Set.mem_image] at h
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)

/--
theorem `Wbtw.dist_le_max_dist` / 定理 `Wbtw.dist_le_max_dist`

English:
theorem Wbtw.dist_le_max_dist
  given: (p : P) {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃)
  proof: by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw Real p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le

中文:
定理 Wbtw.dist_le_max_dist
  条件: (p : P) {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃)
  证明: by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw Real p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le

Depends on / 依赖: dist_lt_max_dist, hs.dist_lt_max_dist
-/
theorem Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) :
    dist p₂ p <= max (dist p₁ p) (dist p₃ p) := by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw Real p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le

/--
theorem `Collinear.wbtw_of_dist_eq_of_dist_le` / 定理 `Collinear.wbtw_of_dist_eq_of_dist_le`

English:
theorem Collinear.wbtw_of_dist_eq_of_dist_le
  statement: {p p₁ p₂ p₃ : P} {r : Real}
  proof: by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
  · by_cases hp₃p₂ : p₃ = p₂
    · simp [hp₃p₂]
    have hs : Sbtw Real p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [or_false] at hs'
    exact False.elim (hp₂.not_gt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw Real p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [false_or] at hs'
    exact False.elim (hp₂.not_gt hs')

中文:
定理 Collinear.wbtw_of_dist_eq_of_dist_le
  结论: {p p₁ p₂ p₃ : P} {r : 实数}
  证明: by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
  · by_cases hp₃p₂ : p₃ = p₂
    · simp [hp₃p₂]
    have hs : Sbtw Real p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [or_false] at hs'
    exact False.elim (hp₂.not_gt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw Real p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [false_or] at hs'
    exact False.elim (hp₂.not_gt hs')

Depends on / 依赖: False.elim, dist_lt_max_dist, h.wbtw_or_wbtw_or_wbtw, hs.dist_lt_max_dist, lt_max_iff, lt_self_iff_false, not_gt, or_false, wbtw_or_wbtw_or_wbtw
-/
theorem Collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : Real}
    (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p <= r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ != p₃) : Wbtw Real p₁ p₂ p₃ := by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
  · by_cases hp₃p₂ : p₃ = p₂
    · simp [hp₃p₂]
    have hs : Sbtw Real p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [or_false] at hs'
    exact False.elim (hp₂.not_gt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw Real p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁]; rw [hp₃]; rw [lt_max_iff]; rw [lt_self_iff_false]; rw [false_or] at hs'
    exact False.elim (hp₂.not_gt hs')

/--
theorem `Collinear.sbtw_of_dist_eq_of_dist_lt` / 定理 `Collinear.sbtw_of_dist_eq_of_dist_lt`

English:
theorem Collinear.sbtw_of_dist_eq_of_dist_lt
  statement: {p p₁ p₂ p₃ : P} {r : Real}
  proof: by
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, ?_, ?_⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃

中文:
定理 Collinear.sbtw_of_dist_eq_of_dist_lt
  结论: {p p₁ p₂ p₃ : P} {r : 实数}
  证明: by
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, ?_, ?_⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_smul_of_tower, continuous_const_smul, continuous_dual_apply, continuous_of_dual_apply_continuous, h.wbtw_of_dist_eq_of_dist_le, map_smul_of_tower, smul_apply, wbtw_of_dist_eq_of_dist_le
-/
theorem Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : Real}
    (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ != p₃) : Sbtw Real p₁ p₂ p₃ := by
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, ?_, ?_⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃

end PseudoMetricSpace

section MetricSpace
variable [MetricSpace P] [NormedAddTorsor V P] {a b c : P}

/--
lemma `dist_add_dist_eq_iff` / 引理 `dist_add_dist_eq_iff`

English:
lemma dist_add_dist_eq_iff
  statement: dist a b + dist b c = dist a c ↔ Wbtw Real a b c
  proof: by
  have :
      dist (a -ᵥ a) (b -ᵥ a) + dist (b -ᵥ a) (c -ᵥ a) = dist (a -ᵥ a) (c -ᵥ a) ↔
        b -ᵥ a in segment Real (a -ᵥ a) (c -ᵥ a) := by
    simp only [mem_segment_iff_sameRay, sameRay_iff_norm_add, dist_eq_norm', sub_add_sub_cancel',
      eq_comm]
  simp_rw [dist_vsub_cancel_right, ← affineSegment_eq_segment, ← affineSegment_vsub_const_image]
    at this
  rwa [(vsub_left_injective _).mem_set_image] at this

中文:
引理 dist_add_dist_eq_iff
  结论: dist a b + dist b c = dist a c ↔ Wbtw 实数 a b c
  证明: by
  have :
      dist (a -ᵥ a) (b -ᵥ a) + dist (b -ᵥ a) (c -ᵥ a) = dist (a -ᵥ a) (c -ᵥ a) ↔
        b -ᵥ a in segment Real (a -ᵥ a) (c -ᵥ a) := by
    simp only [mem_segment_iff_sameRay, sameRay_iff_norm_add, dist_eq_norm', sub_add_sub_cancel',
      eq_comm]
  simp_rw [dist_vsub_cancel_right, ← affineSegment_eq_segment, ← affineSegment_vsub_const_image]
    at this
  rwa [(vsub_left_injective _).mem_set_image] at this

Depends on / 依赖: affineSegment_eq_segment, affineSegment_vsub_const_image, dist_eq_norm, dist_vsub_cancel_right, eq_comm, mem_segment_iff_sameRay, mem_set_image, sameRay_iff_norm_add, segment, simp_rw, sub_add_sub_cancel, vsub_left_injective
-/
lemma dist_add_dist_eq_iff : dist a b + dist b c = dist a c ↔ Wbtw Real a b c := by
  have :
      dist (a -ᵥ a) (b -ᵥ a) + dist (b -ᵥ a) (c -ᵥ a) = dist (a -ᵥ a) (c -ᵥ a) ↔
        b -ᵥ a in segment Real (a -ᵥ a) (c -ᵥ a) := by
    simp only [mem_segment_iff_sameRay, sameRay_iff_norm_add, dist_eq_norm', sub_add_sub_cancel',
      eq_comm]
  simp_rw [dist_vsub_cancel_right, ← affineSegment_eq_segment, ← affineSegment_vsub_const_image]
    at this
  rwa [(vsub_left_injective _).mem_set_image] at this

/--
theorem `dist_lt_dist_add_dist_iff` / 定理 `dist_lt_dist_add_dist_iff`

English:
theorem dist_lt_dist_add_dist_iff
  given: {a b c : P}
  proof: by
  rw [← ne_iff_lt_iff_le.mpr (dist_triangle _ _ _)]; rw [not_iff_not]; rw [eq_comm]; rw [dist_add_dist_eq_iff]

中文:
定理 dist_lt_dist_add_dist_iff
  条件: {a b c : P}
  证明: by
  rw [← ne_iff_lt_iff_le.mpr (dist_triangle _ _ _)]; rw [not_iff_not]; rw [eq_comm]; rw [dist_add_dist_eq_iff]

Depends on / 依赖: dist_add_dist_eq_iff, dist_triangle, eq_comm, ne_iff_lt_iff_le, ne_iff_lt_iff_le.mpr, not_iff_not
-/
theorem dist_lt_dist_add_dist_iff {a b c : P} :
    dist a c < dist a b + dist b c ↔ ¬ Wbtw Real a b c := by
  rw [← ne_iff_lt_iff_le.mpr (dist_triangle _ _ _)]; rw [not_iff_not]; rw [eq_comm]; rw [dist_add_dist_eq_iff]

end MetricSpace

variable {E F PE PF : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E]
  [NormedSpace Real F] [StrictConvexSpace Real E] [MetricSpace PE] [MetricSpace PF] [NormedAddTorsor E PE]
  [NormedAddTorsor F PF] {r : Real} {f : PF -> PE} {x y z : PE}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_lineMap_of_dist_eq_mul_of_dist_eq_mul` / 引理 `eq_lineMap_of_dist_eq_mul_of_dist_eq_mul`

English:
lemma eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  statement: (hxy : dist x y = r * dist x z)
  proof: by
  have : y -ᵥ x in [(0 : E) -[Real] z -ᵥ x] := by
    rw [mem_segment_iff_wbtw]; rw [← dist_add_dist_eq_iff]; rw [dist_zero]; rw [dist_vsub_cancel_right]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [hyz]; rw [← add_mul]; rw [add_sub_cancel]; rw [one_mul]
  obtain rfl | hne := eq_or_ne x z
  · obtain rfl : y = x := by simpa
    simp
  · rw [← dist_ne_zero] at hne
    obtain ⟨a, b, _, hb, _, H⟩ := this
    rw [smul_zero]; rw [zero_add] at H
    have H' := congr_arg norm H
    rw [norm_smul]; rw [Real.norm_of_nonneg hb]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [mul_left_inj' hne] at H'
    rw [AffineMap.lineMap_apply]; rw [← H']; rw [H]; rw [vsub_vadd]

中文:
引理 eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  结论: (hxy : dist x y = r * dist x z)
  证明: by
  have : y -ᵥ x in [(0 : E) -[Real] z -ᵥ x] := by
    rw [mem_segment_iff_wbtw]; rw [← dist_add_dist_eq_iff]; rw [dist_zero]; rw [dist_vsub_cancel_right]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [hyz]; rw [← add_mul]; rw [add_sub_cancel]; rw [one_mul]
  obtain rfl | hne := eq_or_ne x z
  · obtain rfl : y = x := by simpa
    simp
  · rw [← dist_ne_zero] at hne
    obtain ⟨a, b, _, hb, _, H⟩ := this
    rw [smul_zero]; rw [zero_add] at H
    have H' := congr_arg norm H
    rw [norm_smul]; rw [Real.norm_of_nonneg hb]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [mul_left_inj' hne] at H'
    rw [AffineMap.lineMap_apply]; rw [← H']; rw [H]; rw [vsub_vadd]

Depends on / 依赖: Real.n, add_mul, add_sub_cancel, congr_arg, dist_add_dist_eq_iff, dist_eq_norm_vsub, dist_ne_zero, dist_vsub_cancel_right, dist_zero, eq_or_ne, mem_segment_iff_wbtw, norm_smul, one_mul, smul_zero, zero_add
-/
lemma eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (hxy : dist x y = r * dist x z)
    (hyz : dist y z = (1 - r) * dist x z) : y = AffineMap.lineMap x z r := by
  have : y -ᵥ x in [(0 : E) -[Real] z -ᵥ x] := by
    rw [mem_segment_iff_wbtw]; rw [← dist_add_dist_eq_iff]; rw [dist_zero]; rw [dist_vsub_cancel_right]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [hyz]; rw [← add_mul]; rw [add_sub_cancel]; rw [one_mul]
  obtain rfl | hne := eq_or_ne x z
  · obtain rfl : y = x := by simpa
    simp
  · rw [← dist_ne_zero] at hne
    obtain ⟨a, b, _, hb, _, H⟩ := this
    rw [smul_zero]; rw [zero_add] at H
    have H' := congr_arg norm H
    rw [norm_smul]; rw [Real.norm_of_nonneg hb]; rw [← dist_eq_norm_vsub']; rw [← dist_eq_norm_vsub']; rw [hxy]; rw [mul_left_inj' hne] at H'
    rw [AffineMap.lineMap_apply]; rw [← H']; rw [H]; rw [vsub_vadd]

/--
lemma `eq_midpoint_of_dist_eq_half` / 引理 `eq_midpoint_of_dist_eq_half`

English:
lemma eq_midpoint_of_dist_eq_half
  given: (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2)
  proof: by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rwa [invOf_eq_inv, ← div_eq_inv_mul]
  · rwa [invOf_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul]

中文:
引理 eq_midpoint_of_dist_eq_half
  条件: (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2)
  证明: by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rwa [invOf_eq_inv, ← div_eq_inv_mul]
  · rwa [invOf_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul]

Depends on / 依赖: div_eq_inv_mul, eq_lineMap_of_dist_eq_mul_of_dist_eq_mul, invOf_eq_inv, one_div, sub_half
-/
lemma eq_midpoint_of_dist_eq_half (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2) :
    y = midpoint Real x z := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rwa [invOf_eq_inv, ← div_eq_inv_mul]
  · rwa [invOf_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul]

namespace Isometry

/--
Definition of `affineIsometryOfStrictConvexSpace` / `affineIsometryOfStrictConvexSpace` 的定义

English:
definition affineIsometryOfStrictConvexSpace
  signature: (hi : Isometry f)
  body: { AffineMap.ofMapMidpoint f
      (fun x y => by
        apply eq_midpoint_of_dist_eq_half
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_left_midpoint, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul]
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_midpoint_right, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul])
      hi.continuous with
    norm_map := fun x => by simp [AffineMap.ofMapMidpoint, ← dist_eq_norm_vsub E, hi.dist_eq] }

中文:
定义 affineIsometryOfStrictConvexSpace
  签名: (hi : 等距 f)
  定义体: { AffineMap.ofMapMidpoint f
      (fun x y => by
        apply eq_midpoint_of_dist_eq_half
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_left_midpoint, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul]
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_midpoint_right, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul])
      hi.continuous with
    norm_map := fun x => by simp [AffineMap.ofMapMidpoint, ← dist_eq_norm_vsub E, hi.dist_eq] }

Depends on / 依赖: AffineMap, AffineMap.ofMapMidpoint, Real.norm_of_nonneg, continuous, dist_eq, dist_eq_norm_vsub, dist_left_midpoint, dist_midpoint_right, div_eq_inv_mul, eq_midpoint_of_dist_eq_half, hi.continuous, hi.dist_eq, norm_map, norm_of_nonneg, ofMapMidpoint, zero_le_two
-/
noncomputable def affineIsometryOfStrictConvexSpace (hi : Isometry f) : PF ->ᵃⁱ[Real] PE :=
  { AffineMap.ofMapMidpoint f
      (fun x y => by
        apply eq_midpoint_of_dist_eq_half
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_left_midpoint, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul]
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_midpoint_right, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul])
      hi.continuous with
    norm_map := fun x => by simp [AffineMap.ofMapMidpoint, ← dist_eq_norm_vsub E, hi.dist_eq] }

/--
lemma `coe_affineIsometryOfStrictConvexSpace` / 引理 `coe_affineIsometryOfStrictConvexSpace`

English:
lemma coe_affineIsometryOfStrictConvexSpace
  given: (hi : Isometry f)
  proof: rfl

中文:
引理 coe_affineIsometryOfStrictConvexSpace
  条件: (hi : 等距 f)
  证明: rfl
-/
@[simp] lemma coe_affineIsometryOfStrictConvexSpace (hi : Isometry f) :
    ⇑hi.affineIsometryOfStrictConvexSpace = f := rfl

/--
lemma `affineIsometryOfStrictConvexSpace_apply` / 引理 `affineIsometryOfStrictConvexSpace_apply`

English:
lemma affineIsometryOfStrictConvexSpace_apply
  given: (hi : Isometry f) (p : PF)
  proof: rfl

中文:
引理 affineIsometryOfStrictConvexSpace_apply
  条件: (hi : 等距 f) (p : PF)
  证明: rfl
-/
@[simp] lemma affineIsometryOfStrictConvexSpace_apply (hi : Isometry f) (p : PF) :
    hi.affineIsometryOfStrictConvexSpace p = f p := rfl

end Isometry
