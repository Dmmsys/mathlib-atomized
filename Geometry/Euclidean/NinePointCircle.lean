/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection

/-!
# Nine-point circle

This file defines the nine-point circle of a triangle, and its higher dimension analogue, the
3(n+1)-point sphere of a simplex. Specifically for triangles, we show that it passes through nine
specific points as desired.

## Main definitions
* `Affine.Simplex.ninePointCircle`: the 3(n+1)-point sphere of a simplex.
* `Affine.Simplex.eulerPoint`: the $1/n$th of the way from the Monge point to a vertex.
* `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`: the 3(n+1)-point sphere passes through
  the centroid of each face of the simplex
* `Affine.Simplex.eulerPoint_mem_ninePointCircle`: the 3(n+1)-point sphere passes through all Euler
  points.
* `Affine.Triangle.altitudeFoot_mem_ninePointCircle`: the nine-point circle passes through all
  three altitude feet of the triangle.

## References
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)
-/

@[expose] public section

noncomputable section

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

/--
Definition of `ninePointCircle` / `ninePointCircle` 的定义

English:
definition ninePointCircle
  signature: {n : Nat} (s : Simplex Real P n)
  body: ((n + 1) / n : Real) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : Real)

中文:
定义 ninePointCircle
  签名: {n : 自然数} (s : 单纯形 实数 P n)
  定义体: ((n + 1) / n : Real) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : Real)

Depends on / 依赖: centroid, circumcenter, s.centroid, s.circumcenter
-/
def ninePointCircle {n : Nat} (s : Simplex Real P n) : Sphere P where
  center := ((n + 1) / n : Real) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : Real)

/--
theorem `ninePointCircle_center` / 定理 `ninePointCircle_center`

English:
theorem ninePointCircle_center
  given: {n : Nat} (s : Simplex Real P n)
  statement: s.ninePointCircle.center =
  proof: rfl

中文:
定理 ninePointCircle_center
  条件: {n : 自然数} (s : 单纯形 实数 P n)
  结论: s.ninePointCircle.center =
  证明: rfl
-/
theorem ninePointCircle_center {n : Nat} (s : Simplex Real P n) : s.ninePointCircle.center =
    ((n + 1) / n : Real) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter := rfl

/--
theorem `ninePointCircle_center_mem_affineSpan` / 定理 `ninePointCircle_center_mem_affineSpan`

English:
theorem ninePointCircle_center_mem_affineSpan
  given: {n : Nat} (s : Simplex Real P n)
  proof: by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan

中文:
定理 ninePointCircle_center_mem_affineSpan
  条件: {n : 自然数} (s : 单纯形 实数 P n)
  证明: by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan

Depends on / 依赖: AffineSubspace, AffineSubspace.vadd_mem_of_mem_direction, AffineSubspace.vsub_mem_direction, Submodule, Submodule.smul_mem, centroid_mem_affineSpan, circumcenter_mem_affineSpan, ninePointCircle_center, s.centroid_mem_affineSpan, s.circumcenter_mem_affineSpan, smul_mem, vadd_mem_of_mem_direction, vsub_mem_direction
-/
theorem ninePointCircle_center_mem_affineSpan {n : Nat} (s : Simplex Real P n) :
    s.ninePointCircle.center in affineSpan Real (Set.range s.points) := by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan

/--
theorem `ninePointCircle_radius` / 定理 `ninePointCircle_radius`

English:
theorem ninePointCircle_radius
  given: {n : Nat} (s : Simplex Real P n)
  proof: rfl

@[simp]

中文:
定理 ninePointCircle_radius
  条件: {n : 自然数} (s : 单纯形 实数 P n)
  证明: rfl

@[simp]
-/
theorem ninePointCircle_radius {n : Nat} (s : Simplex Real P n) :
    s.ninePointCircle.radius = s.circumradius / (n : Real) := rfl

@[simp]
/--
theorem `ninePointCircle_reindex` / 定理 `ninePointCircle_reindex`

English:
theorem ninePointCircle_reindex
  given: {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]

中文:
定理 ninePointCircle_reindex
  条件: {m n : 自然数} (s : 单纯形 实数 P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]

Depends on / 依赖: Fin.equiv_iff_eq.mp, centroid_reindex, equiv_iff_eq, ninePointCircle_center, ninePointCircle_radius
-/
theorem ninePointCircle_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).ninePointCircle = s.ninePointCircle := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext
  · simp [ninePointCircle_center, centroid_reindex, h]
  · simp [ninePointCircle_radius, h]

/--
theorem `ninePointCircle_map` / 定理 `ninePointCircle_map`

English:
theorem ninePointCircle_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
  proof: by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]

中文:
定理 ninePointCircle_map
  结论: {V₂ P₂ : 类型} [赋范交换加群 V₂] [内积空间 实数 V₂]
  证明: by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]

Depends on / 依赖: center, centroid_map, ninePointCircle, ninePointCircle_center, ninePointCircle_radius, radius, s.ninePointCircle.center, s.ninePointCircle.radius
-/
theorem ninePointCircle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) :
    (s.map f.toAffineMap f.injective).ninePointCircle =
    { center := f s.ninePointCircle.center, radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_map]
  · simp [ninePointCircle_radius]

/--
theorem `ninePointCircle_restrict` / 定理 `ninePointCircle_restrict`

English:
theorem ninePointCircle_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]

中文:
定理 ninePointCircle_restrict
  结论: {n : 自然数} (s : 单纯形 实数 P n) (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem ninePointCircle_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ninePointCircle =
    { center := ⟨s.ninePointCircle.center,
      Set.mem_of_mem_of_subset (s.ninePointCircle_center_mem_affineSpan) hS⟩,
      radius := s.ninePointCircle.radius } := by
  ext
  · simp [ninePointCircle_center, centroid_restrict]
  · simp [ninePointCircle_radius]

/--
theorem `faceOppositeCentroid_mem_ninePointCircle` / 定理 `faceOppositeCentroid_mem_ninePointCircle`

English:
theorem faceOppositeCentroid_mem_ninePointCircle
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: by
  rw [mem_sphere]; rw [ninePointCircle_center]; rw [ninePointCircle_radius]; rw [← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [eq_div_iff_mul_eq (by simpa using NeZero.ne n)]; rw [mul_comm]
  nth_rw 1 [show (n : Real) = ‖(n : Real)‖ by simp]
  rw [← norm_smul]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [mul_div_cancel₀ _ (by simpa using NeZero.ne n)]; rw [add_smul]; rw [one_smul]; rw [← sub_sub]; rw [← smul_sub]; rw [vsub_sub_vsub_cancel_right]; rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_sub_vsub_cancel_left]

中文:
定理 faceOppositeCentroid_mem_ninePointCircle
  结论: {n : 自然数} [NeZero n] (s : 单纯形 实数 P n)
  证明: by
  rw [mem_sphere]; rw [ninePointCircle_center]; rw [ninePointCircle_radius]; rw [← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [eq_div_iff_mul_eq (by simpa using NeZero.ne n)]; rw [mul_comm]
  nth_rw 1 [show (n : Real) = ‖(n : Real)‖ by simp]
  rw [← norm_smul]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [mul_div_cancel₀ _ (by simpa using NeZero.ne n)]; rw [add_smul]; rw [one_smul]; rw [← sub_sub]; rw [← smul_sub]; rw [vsub_sub_vsub_cancel_right]; rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_sub_vsub_cancel_left]

Depends on / 依赖: NeZero, NeZero.ne, add_smul, dist_circumcenter_eq_circumradius, dist_eq_norm_vsub, eq_div_iff_mul_eq, mem_sphere, mul_comm, ninePointCircle_center, ninePointCircle_radius, norm_smul, nth_rw, one_smul, simp_rw, smul_smul, smul_sub, sub_sub, vsub_sub_vsub_cancel_right, vsub_vadd_eq_vsub_sub
-/
theorem faceOppositeCentroid_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) : s.faceOppositeCentroid i in s.ninePointCircle := by
  rw [mem_sphere]; rw [ninePointCircle_center]; rw [ninePointCircle_radius]; rw [← dist_circumcenter_eq_circumradius' s i]
  simp_rw [dist_eq_norm_vsub]
  rw [eq_div_iff_mul_eq (by simpa using NeZero.ne n)]; rw [mul_comm]
  nth_rw 1 [show (n : Real) = ‖(n : Real)‖ by simp]
  rw [← norm_smul]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [smul_smul]; rw [mul_div_cancel₀ _ (by simpa using NeZero.ne n)]; rw [add_smul]; rw [one_smul]; rw [← sub_sub]; rw [← smul_sub]; rw [vsub_sub_vsub_cancel_right]; rw [← centroid_vsub_point_eq_smul_vsub]; rw [vsub_sub_vsub_cancel_left]

/--
theorem `ninePointCircle_eq_circumsphere_medial` / 定理 `ninePointCircle_eq_circumsphere_medial`

English:
theorem ninePointCircle_eq_circumsphere_medial
  given: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

中文:
定理 ninePointCircle_eq_circumsphere_medial
  条件: {n : 自然数} [NeZero n] (s : 单纯形 实数 P n)
  证明: by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

Depends on / 依赖: Set.range_subset_iff, circumsphere_unique_dist_eq, faceOppositeCentroid_mem_ninePointCircle, medial, medial_points, ninePointCircle_center_mem_affineSpan, range_subset_iff, s.faceOppositeCentroid_mem_ninePointCircle, s.medial.circumsphere_unique_dist_eq, s.ninePointCircle_center_mem_affineSpan
-/
theorem ninePointCircle_eq_circumsphere_medial {n : Nat} [NeZero n] (s : Simplex Real P n) :
    s.ninePointCircle = s.medial.circumsphere := by
  apply s.medial.circumsphere_unique_dist_eq.2
  constructor
  · simpa using s.ninePointCircle_center_mem_affineSpan
  · rw [Set.range_subset_iff]
    simpa [medial_points] using s.faceOppositeCentroid_mem_ninePointCircle

/--
Definition of `eulerPoint` / `eulerPoint` 的定义

English:
definition eulerPoint
  signature: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  body: (n : Real)⁻¹ • (s.points i -ᵥ s.mongePoint) +ᵥ s.mongePoint

@[simp]

中文:
定义 eulerPoint
  签名: {n : 自然数} (s : 单纯形 实数 P n) (i : 有限集 (n + 1))
  定义体: (n : Real)⁻¹ • (s.points i -ᵥ s.mongePoint) +ᵥ s.mongePoint

@[simp]

Depends on / 依赖: mongePoint, points, s.mongePoint, s.points
-/
def eulerPoint {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :=
  (n : Real)⁻¹ • (s.points i -ᵥ s.mongePoint) +ᵥ s.mongePoint

@[simp]
/--
theorem `eulerPoint_reindex` / 定理 `eulerPoint_reindex`

English:
theorem eulerPoint_reindex
  given: {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]

中文:
定理 eulerPoint_reindex
  条件: {m n : 自然数} (s : 单纯形 实数 P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]

Depends on / 依赖: Fin.equiv_iff_eq.mp, equiv_iff_eq, eulerPoint
-/
theorem eulerPoint_reindex {m n : Nat} (s : Simplex Real P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).eulerPoint = s.eulerPoint ∘ e.symm := by
  have h : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  ext i
  simp [eulerPoint, h]

@[simp]
/--
theorem `eulerPoint_map` / 定理 `eulerPoint_map`

English:
theorem eulerPoint_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
  proof: by
  simp [eulerPoint]

@[simp]

中文:
定理 eulerPoint_map
  结论: {V₂ P₂ : 类型} [赋范交换加群 V₂] [内积空间 实数 V₂]
  证明: by
  simp [eulerPoint]

@[simp]

Depends on / 依赖: eulerPoint
-/
theorem eulerPoint_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).eulerPoint i = f (s.eulerPoint i) := by
  simp [eulerPoint]

@[simp]
/--
theorem `eulerPoint_restrict` / 定理 `eulerPoint_restrict`

English:
theorem eulerPoint_restrict
  statement: {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  simp [eulerPoint]

中文:
定理 eulerPoint_restrict
  结论: {n : 自然数} (s : 单纯形 实数 P n) (S : 仿射子空间 实数 P)
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  simp [eulerPoint]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem eulerPoint_restrict {n : Nat} (s : Simplex Real P n) (S : AffineSubspace Real P)
    (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).eulerPoint i = s.eulerPoint i := by
  simp [eulerPoint]

/--
theorem `points_vsub_eulerPoint` / 定理 `points_vsub_eulerPoint`

English:
theorem points_vsub_eulerPoint
  given: {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1))
  proof: by
  rw [eulerPoint]; rw [vsub_vadd_eq_vsub_sub]
  by_cases hn : n = 0
  · obtain rfl := hn
    have hrange : Set.range s.points = {s.points i} := by simp [Subsingleton.eq_zero (α := Fin 1) i]
    obtain hmonge := s.mongePoint_mem_affineSpan
    rw [hrange]; rw [mem_affineSpan_singleton] at hmonge
    simp [hmonge]
  rw [sub_div]; rw [div_self (by simpa using hn)]; rw [one_div]; rw [sub_smul]; rw [one_smul]

中文:
定理 points_vsub_eulerPoint
  条件: {n : 自然数} (s : 单纯形 实数 P n) (i : 有限集 (n + 1))
  证明: by
  rw [eulerPoint]; rw [vsub_vadd_eq_vsub_sub]
  by_cases hn : n = 0
  · obtain rfl := hn
    have hrange : Set.range s.points = {s.points i} := by simp [Subsingleton.eq_zero (α := Fin 1) i]
    obtain hmonge := s.mongePoint_mem_affineSpan
    rw [hrange]; rw [mem_affineSpan_singleton] at hmonge
    simp [hmonge]
  rw [sub_div]; rw [div_self (by simpa using hn)]; rw [one_div]; rw [sub_smul]; rw [one_smul]

Depends on / 依赖: Set.range, Subsingleton, Subsingleton.eq_zero, div_self, eq_zero, eulerPoint, hmonge, hrange, mem_affineSpan_singleton, mongePoint_mem_affineSpan, one_div, one_smul, points, s.mongePoint_mem_affineSpan, s.points, sub_div, sub_smul, vsub_vadd_eq_vsub_sub
-/
theorem points_vsub_eulerPoint {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.eulerPoint i = ((n - 1) / n : Real) • (s.points i -ᵥ s.mongePoint) := by
  rw [eulerPoint]; rw [vsub_vadd_eq_vsub_sub]
  by_cases hn : n = 0
  · obtain rfl := hn
    have hrange : Set.range s.points = {s.points i} := by simp [Subsingleton.eq_zero (α := Fin 1) i]
    obtain hmonge := s.mongePoint_mem_affineSpan
    rw [hrange]; rw [mem_affineSpan_singleton] at hmonge
    simp [hmonge]
  rw [sub_div]; rw [div_self (by simpa using hn)]; rw [one_div]; rw [sub_smul]; rw [one_smul]

/--
theorem `midpoint_faceOppositeCentroid_eulerPoint` / 定理 `midpoint_faceOppositeCentroid_eulerPoint`

English:
theorem midpoint_faceOppositeCentroid_eulerPoint
  statement: {n : Nat} [hn : NeZero n] (s : Simplex Real P n)
  proof: by
  apply vsub_left_cancel (p := s.circumcenter)
  rw [ninePointCircle_center]; rw [midpoint_vsub]; rw [vadd_vsub]; rw [eulerPoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [← centroid]
  by_cases hn1 : n = 1
  · obtain rfl := hn1
    suffices (2⁻¹ : Real) • (s.faceOppositeCentroid i -ᵥ s.centroid) +
        (2⁻¹ : Real) • (s.points i -ᵥ s.centroid) = 0 by
      simpa [circumcenter_eq_centroid, centroid]
    rw [faceOppositeCentroid_vsub_centroid_eq_smul_vsub]; rw [← smul_add]
    exact (smul_eq_zero_of_right _ (by simp))
  have hltn : 1 < n := by
    have _ := hn.out
    lia
  have hnsub1 : (n - 1 : Nat) = (n : Real) - 1 := by
    push_cast [hltn]
    rfl
  rw [vadd_vadd]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [sub_add]; rw [smul_smul]; rw [← sub_smul]; rw [← sub_one_mul]; rw [show ((n : Real)⁻¹ - 1) = -(n - 1) / n by field [hn.out],
    neg_div, neg_mul, hnsub1, div_mul_div_cancel₀' (by simpa [sub_eq_zero] using hn1),
    neg_smul, sub_neg_eq_add, faceOppositeCentroid_eq_smul_vsub_vadd_point,
    ← smul_add, vadd_vsub_assoc, add_add_add_comm, ← smul_add, vsub_add_vsub_cancel, ← add_assoc]
  push_cast
  have : (n : Real)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) =
      (((n + 1) / n : Real)) • (s.centroid -ᵥ s.circumcenter) := by
    rw [add_comm (n : Real) 1]; rw [add_div]; rw [div_self (by simpa using hn.out)]; rw [add_smul]; rw [one_smul]; rw [one_div]
  rw [this]; rw [← two_smul Real]; rw [smul_smul]
  norm_num

中文:
定理 midpoint_faceOppositeCentroid_eulerPoint
  结论: {n : 自然数} [hn : NeZero n] (s : 单纯形 实数 P n)
  证明: by
  apply vsub_left_cancel (p := s.circumcenter)
  rw [ninePointCircle_center]; rw [midpoint_vsub]; rw [vadd_vsub]; rw [eulerPoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [← centroid]
  by_cases hn1 : n = 1
  · obtain rfl := hn1
    suffices (2⁻¹ : Real) • (s.faceOppositeCentroid i -ᵥ s.centroid) +
        (2⁻¹ : Real) • (s.points i -ᵥ s.centroid) = 0 by
      simpa [circumcenter_eq_centroid, centroid]
    rw [faceOppositeCentroid_vsub_centroid_eq_smul_vsub]; rw [← smul_add]
    exact (smul_eq_zero_of_right _ (by simp))
  have hltn : 1 < n := by
    have _ := hn.out
    lia
  have hnsub1 : (n - 1 : Nat) = (n : Real) - 1 := by
    push_cast [hltn]
    rfl
  rw [vadd_vadd]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [sub_add]; rw [smul_smul]; rw [← sub_smul]; rw [← sub_one_mul]; rw [show ((n : Real)⁻¹ - 1) = -(n - 1) / n by field [hn.out],
    neg_div, neg_mul, hnsub1, div_mul_div_cancel₀' (by simpa [sub_eq_zero] using hn1),
    neg_smul, sub_neg_eq_add, faceOppositeCentroid_eq_smul_vsub_vadd_point,
    ← smul_add, vadd_vsub_assoc, add_add_add_comm, ← smul_add, vsub_add_vsub_cancel, ← add_assoc]
  push_cast
  have : (n : Real)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) =
      (((n + 1) / n : Real)) • (s.centroid -ᵥ s.circumcenter) := by
    rw [add_comm (n : Real) 1]; rw [add_div]; rw [div_self (by simpa using hn.out)]; rw [add_smul]; rw [one_smul]; rw [one_div]
  rw [this]; rw [← two_smul Real]; rw [smul_smul]
  norm_num

Depends on / 依赖: centroid, circumcenter, circumcenter_eq_centroid, eulerPoint, faceOppositeCentroid, faceOppositeCentroid_vsub_centroid_eq_smul_vsub, midpoint_vsub, mongePoint_eq_smul_vsub_vadd_circumcenter, ninePointCircle_center, points, s.centroid, s.circumcenter, s.faceOppositeCentroid, s.points, smul_add, smul_eq_zero_of_right, vadd_vsub, vsub_left_cancel
-/
theorem midpoint_faceOppositeCentroid_eulerPoint {n : Nat} [hn : NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) :
    midpoint Real (s.faceOppositeCentroid i) (s.eulerPoint i) = s.ninePointCircle.center := by
  apply vsub_left_cancel (p := s.circumcenter)
  rw [ninePointCircle_center]; rw [midpoint_vsub]; rw [vadd_vsub]; rw [eulerPoint]; rw [mongePoint_eq_smul_vsub_vadd_circumcenter]; rw [← centroid]
  by_cases hn1 : n = 1
  · obtain rfl := hn1
    suffices (2⁻¹ : Real) • (s.faceOppositeCentroid i -ᵥ s.centroid) +
        (2⁻¹ : Real) • (s.points i -ᵥ s.centroid) = 0 by
      simpa [circumcenter_eq_centroid, centroid]
    rw [faceOppositeCentroid_vsub_centroid_eq_smul_vsub]; rw [← smul_add]
    exact (smul_eq_zero_of_right _ (by simp))
  have hltn : 1 < n := by
    have _ := hn.out
    lia
  have hnsub1 : (n - 1 : Nat) = (n : Real) - 1 := by
    push_cast [hltn]
    rfl
  rw [vadd_vadd]; rw [vadd_vsub]; rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [sub_add]; rw [smul_smul]; rw [← sub_smul]; rw [← sub_one_mul]; rw [show ((n : Real)⁻¹ - 1) = -(n - 1) / n by field [hn.out],
    neg_div, neg_mul, hnsub1, div_mul_div_cancel₀' (by simpa [sub_eq_zero] using hn1),
    neg_smul, sub_neg_eq_add, faceOppositeCentroid_eq_smul_vsub_vadd_point,
    ← smul_add, vadd_vsub_assoc, add_add_add_comm, ← smul_add, vsub_add_vsub_cancel, ← add_assoc]
  push_cast
  have : (n : Real)⁻¹ • (s.centroid -ᵥ s.circumcenter) + (s.centroid -ᵥ s.circumcenter) =
      (((n + 1) / n : Real)) • (s.centroid -ᵥ s.circumcenter) := by
    rw [add_comm (n : Real) 1]; rw [add_div]; rw [div_self (by simpa using hn.out)]; rw [add_smul]; rw [one_smul]; rw [one_div]
  rw [this]; rw [← two_smul Real]; rw [smul_smul]
  norm_num

/--
theorem `isDiameter_ninePointCircle` / 定理 `isDiameter_ninePointCircle`

English:
theorem isDiameter_ninePointCircle
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i

中文:
定理 isDiameter_ninePointCircle
  结论: {n : 自然数} [NeZero n] (s : 单纯形 实数 P n)
  证明: s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i

Depends on / 依赖: faceOppositeCentroid_mem_ninePointCircle, s.faceOppositeCentroid_mem_ninePointCircle
-/
theorem isDiameter_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) :
    s.ninePointCircle.IsDiameter (s.faceOppositeCentroid i) (s.eulerPoint i) where
  left_mem := s.faceOppositeCentroid_mem_ninePointCircle i
  midpoint_eq_center := s.midpoint_faceOppositeCentroid_eulerPoint i

/--
theorem `eulerPoint_mem_ninePointCircle` / 定理 `eulerPoint_mem_ninePointCircle`

English:
theorem eulerPoint_mem_ninePointCircle
  statement: {n : Nat} [NeZero n] (s : Simplex Real P n)
  proof: (s.isDiameter_ninePointCircle i).right_mem

中文:
定理 eulerPoint_mem_ninePointCircle
  结论: {n : 自然数} [NeZero n] (s : 单纯形 实数 P n)
  证明: (s.isDiameter_ninePointCircle i).right_mem

Depends on / 依赖: isDiameter_ninePointCircle, right_mem, s.isDiameter_ninePointCircle
-/
theorem eulerPoint_mem_ninePointCircle {n : Nat} [NeZero n] (s : Simplex Real P n)
    (i : Fin (n + 1)) : s.eulerPoint i in s.ninePointCircle :=
  (s.isDiameter_ninePointCircle i).right_mem

/--
theorem `orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle` / 定理 `orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle`

English:
theorem orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle
  statement: {n : Nat} [NeZero n]
  proof: by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i)]; rw [orthogonalProjectionSpan]
exact angle_orthogonalProjection_self _ faceOppositeCentroid_mem_affineSpan_face s i

中文:
定理 orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle
  结论: {n : 自然数} [NeZero n]
  证明: by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i)]; rw [orthogonalProjectionSpan]
exact angle_orthogonalProjection_self _ faceOppositeCentroid_mem_affineSpan_face s i

Depends on / 依赖: Sphere, Sphere.thales_theorem, angle_orthogonalProjection_self, faceOppositeCentroid_mem_affineSpan_face, isDiameter_ninePointCircle, orthogonalProjectionSpan, s.isDiameter_ninePointCircle, thales_theorem
-/
theorem orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle {n : Nat} [NeZero n]
    (s : Simplex Real P n) (i : Fin (n + 1)) :
    ((s.faceOpposite i).orthogonalProjectionSpan (s.eulerPoint i)).val in s.ninePointCircle := by
  rw [← Sphere.thales_theorem (s.isDiameter_ninePointCircle i)]; rw [orthogonalProjectionSpan]
exact angle_orthogonalProjection_self _ faceOppositeCentroid_mem_affineSpan_face s i

end Affine.Simplex

namespace Affine.Triangle

/--
theorem `eulerPoint_eq_midpoint` / 定理 `eulerPoint_eq_midpoint`

English:
theorem eulerPoint_eq_midpoint
  given: (s : Triangle Real P) (i : Fin 3)
  proof: by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint]; rw [Simplex.points_vsub_eulerPoint]; rw [vsub_midpoint]
  norm_num

中文:
定理 eulerPoint_eq_midpoint
  条件: (s : Triangle 实数 P) (i : 有限集 3)
  证明: by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint]; rw [Simplex.points_vsub_eulerPoint]; rw [vsub_midpoint]
  norm_num

Depends on / 依赖: Simplex, Simplex.points_vsub_eulerPoint, orthocenter_eq_mongePoint, points, points_vsub_eulerPoint, s.points, vsub_midpoint, vsub_right_cancel
-/
theorem eulerPoint_eq_midpoint (s : Triangle Real P) (i : Fin 3) :
    s.eulerPoint i = midpoint Real s.orthocenter (s.points i) := by
  apply vsub_right_cancel (p := s.points i)
  rw [orthocenter_eq_mongePoint]; rw [Simplex.points_vsub_eulerPoint]; rw [vsub_midpoint]
  norm_num

/--
theorem `altitudeFoot_mem_ninePointCircle` / 定理 `altitudeFoot_mem_ninePointCircle`

English:
theorem altitudeFoot_mem_ninePointCircle
  given: (s : Triangle Real P) (i : Fin 3)
  proof: by
  convert! s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]; rw [Simplex.points_vsub_eulerPoint]; rw [Submodule.smul_mem_iff _ (by norm_num)]; rw [← orthocenter_eq_mongePoint]; rw [direction_affineSpan]; rw [Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

中文:
定理 altitudeFoot_mem_ninePointCircle
  条件: (s : Triangle 实数 P) (i : 有限集 3)
  证明: by
  convert! s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]; rw [Simplex.points_vsub_eulerPoint]; rw [Submodule.smul_mem_iff _ (by norm_num)]; rw [← orthocenter_eq_mongePoint]; rw [direction_affineSpan]; rw [Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

Depends on / 依赖: Set.mem_of_mem_of_subset, Simplex, Simplex.altitudeFoot, Simplex.orthogonalProjectionSpan, Simplex.points_vsub_eulerPoint, Simplex.range_faceOpposite_points, Submodule, Submodule.smul_mem_iff, altitudeFoot, convert, direction_affineSpan, mem_of_mem_of_subset, orthocenter_eq_mongePoint, orthogonalProjectionSpan, orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle, orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem, points_vsub_eulerPoint, range_faceOpposite_points, s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle, s.vectorSpan_isOrtho_altitude_direction
-/
theorem altitudeFoot_mem_ninePointCircle (s : Triangle Real P) (i : Fin 3) :
    s.altitudeFoot i in s.ninePointCircle := by
  convert! s.orthogonalProjectionSpan_eulerPoint_mem_ninePointCircle i
  rw [Simplex.altitudeFoot]
  unfold Simplex.orthogonalProjectionSpan
  congr 1
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]; rw [Simplex.points_vsub_eulerPoint]; rw [Submodule.smul_mem_iff _ (by norm_num)]; rw [← orthocenter_eq_mongePoint]; rw [direction_affineSpan]; rw [Simplex.range_faceOpposite_points]
  refine Set.mem_of_mem_of_subset ?_ (s.vectorSpan_isOrtho_altitude_direction i).ge
  exact vsub_mem_direction (s.mem_altitude i) (s.orthocenter_mem_altitude)

end Affine.Triangle

end
