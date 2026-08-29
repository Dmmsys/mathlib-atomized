/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.StrictCombination
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `EuclideanGeometry.Sphere.secondInter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/

@[expose] public section


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace Real V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

/--
Definition of `Sphere.secondInter` / `Sphere.secondInter` 的定义

English:
definition Sphere.secondInter
  signature: (s : Sphere P) (p : P) (v : V)
  body: (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p

中文:
定义 球面.second整数er
  签名: (s : 球面 P) (p : P) (v : V)
  定义体: (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p

Depends on / 依赖: center, s.center
-/
def Sphere.secondInter (s : Sphere P) (p : P) (v : V) : P :=
  (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Sphere.secondInter_map` / 引理 `Sphere.secondInter_map`

English:
lemma Sphere.secondInter_map
  given: (s : Sphere P) (p : P) (v : V) (f : P ->ᵃⁱ[Real] P₂)
  proof: by
  simp [secondInter, ← AffineIsometry.map_vsub]

中文:
引理 球面.second整数er_map
  条件: (s : 球面 P) (p : P) (v : V) (f : P ->ᵃⁱ[实数] P₂)
  证明: by
  simp [secondInter, ← AffineIsometry.map_vsub]
-/
@[simp] lemma Sphere.secondInter_map (s : Sphere P) (p : P) (v : V) (f : P ->ᵃⁱ[Real] P₂) :
    Sphere.secondInter ⟨f s.center, s.radius⟩ (f p) (f.linearIsometry v) =
      f (s.secondInter p v) := by
  simp [secondInter, ← AffineIsometry.map_vsub]

/--
lemma `Sphere.coe_secondInter` / 引理 `Sphere.coe_secondInter`

English:
lemma Sphere.coe_secondInter
  statement: (as : AffineSubspace Real P) [Nonempty as] (s : Sphere as)
  proof: rfl

中文:
引理 球面.coe_second整数er
  结论: (as : 仿射子空间 实数 P) [非空 as] (s : 球面 as)
  证明: rfl
-/
lemma Sphere.coe_secondInter (as : AffineSubspace Real P) [Nonempty as] (s : Sphere as)
    (p : as) (v : as.direction) :
    s.secondInter p v = Sphere.secondInter ⟨(s.center : P), s.radius⟩ (p : P) (v : V) :=
  rfl

/-- The distance between `secondInter` and the center equals the distance between the original
point and the center. -/
@[simp]
/--
theorem `Sphere.secondInter_dist` / 定理 `Sphere.secondInter_dist`

English:
theorem Sphere.secondInter_dist
  given: (s : Sphere P) (p : P) (v : V)
  proof: by
  rw [Sphere.secondInter]
  by_cases hv : v = 0; · simp [hv]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl

中文:
定理 球面.second整数er_dist
  条件: (s : 球面 P) (p : P) (v : V)
  证明: by
  rw [Sphere.secondInter]
  by_cases hv : v = 0; · simp [hv]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl

Depends on / 依赖: Or.inr, Sphere, Sphere.secondInter, dist_smul_vadd_eq_dist, secondInter
-/
theorem Sphere.secondInter_dist (s : Sphere P) (p : P) (v : V) :
    dist (s.secondInter p v) s.center = dist p s.center := by
  rw [Sphere.secondInter]
  by_cases hv : v = 0; · simp [hv]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl

/-- The point given by `secondInter` lies on the sphere. -/
@[simp]
/--
theorem `Sphere.secondInter_mem` / 定理 `Sphere.secondInter_mem`

English:
theorem Sphere.secondInter_mem
  given: {s : Sphere P} {p : P} (v : V)
  statement: s.secondInter p v in s ↔ p in s
  proof: by
  simp_rw [mem_sphere, Sphere.secondInter_dist]

中文:
定理 球面.second整数er_mem
  条件: {s : 球面 P} {p : P} (v : V)
  结论: s.second整数er p v in s ↔ p in s
  证明: by
  simp_rw [mem_sphere, Sphere.secondInter_dist]

Depends on / 依赖: Sphere, Sphere.secondInter_dist, mem_sphere, secondInter_dist, simp_rw
-/
theorem Sphere.secondInter_mem {s : Sphere P} {p : P} (v : V) : s.secondInter p v in s ↔ p in s := by
  simp_rw [mem_sphere, Sphere.secondInter_dist]

variable (V) in
/-- If the vector is zero, `secondInter` gives the original point. -/
@[simp]
/--
theorem `Sphere.secondInter_zero` / 定理 `Sphere.secondInter_zero`

English:
theorem Sphere.secondInter_zero
  given: (s : Sphere P) (p : P)
  statement: s.secondInter p (0 : V) = p
  proof: by
  simp [Sphere.secondInter]

中文:
定理 球面.second整数er_zero
  条件: (s : 球面 P) (p : P)
  结论: s.second整数er p (0 : V) = p
  证明: by
  simp [Sphere.secondInter]

Depends on / 依赖: Sphere, Sphere.secondInter, secondInter
-/
theorem Sphere.secondInter_zero (s : Sphere P) (p : P) : s.secondInter p (0 : V) = p := by
  simp [Sphere.secondInter]

/--
theorem `Sphere.secondInter_eq_self_iff` / 定理 `Sphere.secondInter_eq_self_iff`

English:
theorem Sphere.secondInter_eq_self_iff
  given: {s : Sphere P} {p : P} {v : V}
  proof: by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by simp : (-2 : Real) != 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]

中文:
定理 球面.second整数er_eq_self_iff
  条件: {s : 球面 P} {p : P} {v : V}
  证明: by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by simp : (-2 : Real) != 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]

Depends on / 依赖: Sphere, Sphere.secondInter, div_eq_zero_iff, eq_comm, eq_vadd_iff_vsub_eq, inner_self_eq_zero, mul_eq_zero, mul_zero, or_iff_left, or_iff_right, secondInter, smul_eq_zero, vsub_self, zero_div, zero_smul, zero_vadd
-/
theorem Sphere.secondInter_eq_self_iff {s : Sphere P} {p : P} {v : V} :
    s.secondInter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by simp : (-2 : Real) != 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]

/--
theorem `Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem` / 定理 `Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem`

English:
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
  statement: {s : Sphere P} {p : P}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, Sphere.secondInter_mem]
  · rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    subst hr
    by_cases hv : v = 0
    · simp [hv]
    rw [Sphere.secondInter]
    rw [mem_sphere] at h hp
    rw [← hp]; rw [dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]

中文:
定理 球面.eq_or_eq_second整数er_of_mem_mk'_span_singleton_iff_mem
  结论: {s : 球面 P} {p : P}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, Sphere.secondInter_mem]
  · rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    subst hr
    by_cases hv : v = 0
    · simp [hv]
    rw [Sphere.secondInter]
    rw [mem_sphere] at h hp
    rw [← hp]; rw [dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_mk, Sphere, Sphere.secondInter, Sphere.secondInter_mem, Submodule, Submodule.mem_span_singleton, dist_smul_vadd_eq_dist, eq_comm, eq_vadd_iff_vsub_eq, mem_mk, mem_span_singleton, mem_sphere, secondInter, secondInter_mem
-/
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P} {p : P}
    (hp : p in s) {v : V} {p' : P} (hp' : p' in AffineSubspace.mk' p (Real ∙ v)) :
    p' = p ∨ p' = s.secondInter p v ↔ p' in s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, Sphere.secondInter_mem]
  · rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    subst hr
    by_cases hv : v = 0
    · simp [hv]
    rw [Sphere.secondInter]
    rw [mem_sphere] at h hp
    rw [← hp]; rw [dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]

/--
lemma `Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair` / 引理 `Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair`

English:
lemma Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
  statement: {s : Sphere P} {p q : P}
  proof: by
  convert! s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp ?_
  convert! hp'
  rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineSubspace.self_mem_mk' p _)
    (left_mem_affineSpan_pair _ _ _)]
  simp [direction_affineSpan, vectorSpan_pair_rev]

中文:
引理 球面.eq_or_eq_second整数er_iff_mem_of_mem_affineSpan_pair
  结论: {s : 球面 P} {p q : P}
  证明: by
  convert! s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp ?_
  convert! hp'
  rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineSubspace.self_mem_mk' p _)
    (left_mem_affineSpan_pair _ _ _)]
  simp [direction_affineSpan, vectorSpan_pair_rev]

Depends on / 依赖: AffineSubspace, AffineSubspace.eq_iff_direction_eq_of_mem, AffineSubspace.self_mem_mk, _span_singleton_iff_mem, convert, direction_affineSpan, eq_iff_direction_eq_of_mem, eq_or_eq_secondInter_of_mem_mk, left_mem_affineSpan_pair, s.eq_or_eq_secondInter_of_mem_mk, self_mem_mk, vectorSpan_pair_rev
-/
lemma Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair {s : Sphere P} {p q : P}
    (hp : p in s) {p' : P} (hp' : p' in line[Real, p, q]) :
    p' = p ∨ p' = s.secondInter p (q -ᵥ p) ↔ p' in s := by
  convert! s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp ?_
  convert! hp'
  rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineSubspace.self_mem_mk' p _)
    (left_mem_affineSpan_pair _ _ _)]
  simp [direction_affineSpan, vectorSpan_pair_rev]

/-- `secondInter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp]
/--
theorem `Sphere.secondInter_smul` / 定理 `Sphere.secondInter_smul`

English:
theorem Sphere.secondInter_smul
  given: (s : Sphere P) (p : P) (v : V) {r : Real} (hr : r != 0)
  proof: by
  simp_rw [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]

中文:
定理 球面.second整数er_smul
  条件: (s : 球面 P) (p : P) (v : V) {r : 实数} (hr : r != 0)
  证明: by
  simp_rw [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]

Depends on / 依赖: Sphere, Sphere.secondInter, div_mul_eq_div_div, inner_smul_right, mul_assoc, mul_comm, mul_div_assoc, real_inner_smul_left, secondInter, simp_rw, smul_smul
-/
theorem Sphere.secondInter_smul (s : Sphere P) (p : P) (v : V) {r : Real} (hr : r != 0) :
    s.secondInter p (r • v) = s.secondInter p v := by
  simp_rw [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ hr]; rw [mul_comm]

/-- `secondInter` is unchanged by negating the vector. -/
@[simp]
/--
theorem `Sphere.secondInter_neg` / 定理 `Sphere.secondInter_neg`

English:
theorem Sphere.secondInter_neg
  given: (s : Sphere P) (p : P) (v : V)
  proof: by
  rw [← neg_one_smul Real v]; rw [s.secondInter_smul p v (by simp : (-1 : Real) != 0)]

中文:
定理 球面.second整数er_neg
  条件: (s : 球面 P) (p : P) (v : V)
  证明: by
  rw [← neg_one_smul Real v]; rw [s.secondInter_smul p v (by simp : (-1 : Real) != 0)]

Depends on / 依赖: neg_one_smul, s.secondInter_smul, secondInter_smul
-/
theorem Sphere.secondInter_neg (s : Sphere P) (p : P) (v : V) :
    s.secondInter p (-v) = s.secondInter p v := by
  rw [← neg_one_smul Real v]; rw [s.secondInter_smul p v (by simp : (-1 : Real) != 0)]

/-- Applying `secondInter` twice returns the original point. -/
@[simp]
/--
theorem `Sphere.secondInter_secondInter` / 定理 `Sphere.secondInter_secondInter`

English:
theorem Sphere.secondInter_secondInter
  given: (s : Sphere P) (p : P) (v : V)
  proof: by
  by_cases hv : v = 0; · simp [hv]
  have hv' : ⟪v, v⟫ != 0 := inner_self_ne_zero.2 hv
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel₀ _ hv']
  rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [← add_smul]; rw [← add_div]
  convert! zero_smul Real _
  convert! zero_div (G₀ := Real) _
  ring

中文:
定理 球面.second整数er_second整数er
  条件: (s : 球面 P) (p : P) (v : V)
  证明: by
  by_cases hv : v = 0; · simp [hv]
  have hv' : ⟪v, v⟫ != 0 := inner_self_ne_zero.2 hv
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel₀ _ hv']
  rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [← add_smul]; rw [← add_div]
  convert! zero_smul Real _
  convert! zero_div (G₀ := Real) _
  ring

Depends on / 依赖: Sphere, Sphere.secondInter, add_div, add_smul, convert, inner_add_right, inner_self_ne_zero, inner_smul_right, secondInter, vadd_vadd, vadd_vsub, vadd_vsub_assoc, vsub_eq_zero_iff_eq, zero_div, zero_smul
-/
theorem Sphere.secondInter_secondInter (s : Sphere P) (p : P) (v : V) :
    s.secondInter (s.secondInter p v) v = p := by
  by_cases hv : v = 0; · simp [hv]
  have hv' : ⟪v, v⟫ != 0 := inner_self_ne_zero.2 hv
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel₀ _ hv']
  rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [← add_smul]; rw [← add_div]
  convert! zero_smul Real _
  convert! zero_div (G₀ := Real) _
  ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Sphere.secondInter_eq_lineMap` / 定理 `Sphere.secondInter_eq_lineMap`

English:
theorem Sphere.secondInter_eq_lineMap
  given: (s : Sphere P) (p p' : P)
  proof: rfl

中文:
定理 球面.second整数er_eq_lineMap
  条件: (s : 球面 P) (p p' : P)
  证明: rfl
-/
theorem Sphere.secondInter_eq_lineMap (s : Sphere P) (p p' : P) :
    s.secondInter p (p' -ᵥ p) =
      AffineMap.lineMap p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
  rfl

/--
theorem `Sphere.secondInter_vsub_mem_affineSpan` / 定理 `Sphere.secondInter_vsub_mem_affineSpan`

English:
theorem Sphere.secondInter_vsub_mem_affineSpan
  given: (s : Sphere P) (p₁ p₂ : P)
  proof: smul_vsub_vadd_mem_affineSpan_pair _ _ _

中文:
定理 球面.second整数er_vsub_mem_affineSpan
  条件: (s : 球面 P) (p₁ p₂ : P)
  证明: smul_vsub_vadd_mem_affineSpan_pair _ _ _

Depends on / 依赖: smul_vsub_vadd_mem_affineSpan_pair
-/
theorem Sphere.secondInter_vsub_mem_affineSpan (s : Sphere P) (p₁ p₂ : P) :
    s.secondInter p₁ (p₂ -ᵥ p₁) in line[Real, p₁, p₂] :=
  smul_vsub_vadd_mem_affineSpan_pair _ _ _

/--
theorem `Sphere.secondInter_collinear` / 定理 `Sphere.secondInter_collinear`

English:
theorem Sphere.secondInter_collinear
  given: (s : Sphere P) (p p' : P)
  proof: by
  rw [Set.pair_comm]; rw [Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _)).2
      (collinear_pair Real _ _)

中文:
定理 球面.second整数er_collinear
  条件: (s : 球面 P) (p p' : P)
  证明: by
  rw [Set.pair_comm]; rw [Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _)).2
      (collinear_pair Real _ _)

Depends on / 依赖: Set.insert_comm, Set.pair_comm, collinear_insert_iff_of_mem_affineSpan, collinear_pair, insert_comm, pair_comm, s.secondInter_vsub_mem_affineSpan, secondInter_vsub_mem_affineSpan
-/
theorem Sphere.secondInter_collinear (s : Sphere P) (p p' : P) :
    Collinear Real ({p, p', s.secondInter p (p' -ᵥ p)} : Set P) := by
  rw [Set.pair_comm]; rw [Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _)).2
      (collinear_pair Real _ _)

/--
theorem `Sphere.wbtw_secondInter` / 定理 `Sphere.wbtw_secondInter`

English:
theorem Sphere.wbtw_secondInter
  statement: {s : Sphere P} {p p' : P} (hp : p in s)
  proof: by
  by_cases h : p' = p; · simp [h]
  refine
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p') hp hp'
      ((Sphere.secondInter_mem _).2 hp) ?_
  intro he
  rw [eq_comm]; rw [Sphere.secondInter_eq_self_iff]; rw [← neg_neg (p' -ᵥ p)]; rw [inner_neg_left]; rw [neg_vsub_eq_vsub_rev]; rw [neg_eq_zero]; rw [eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he

中文:
定理 球面.wbtw_second整数er
  结论: {s : 球面 P} {p p' : P} (hp : p in s)
  证明: by
  by_cases h : p' = p; · simp [h]
  refine
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p') hp hp'
      ((Sphere.secondInter_mem _).2 hp) ?_
  intro he
  rw [eq_comm]; rw [Sphere.secondInter_eq_self_iff]; rw [← neg_neg (p' -ᵥ p)]; rw [inner_neg_left]; rw [neg_vsub_eq_vsub_rev]; rw [neg_eq_zero]; rw [eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he

Depends on / 依赖: Ne.symm, Sphere, Sphere.secondInter_eq_self_iff, Sphere.secondInter_mem, eq_comm, inner_neg_left, inner_pos_or_eq_of_dist_le_radius, neg_eq_zero, neg_neg, neg_vsub_eq_vsub_rev, resolve_right, s.secondInter_collinear, secondInter_collinear, secondInter_eq_self_iff, secondInter_mem, wbtw_of_collinear_of_dist_center_le_radius
-/
theorem Sphere.wbtw_secondInter {s : Sphere P} {p p' : P} (hp : p in s)
    (hp' : dist p' s.center <= s.radius) : Wbtw Real p p' (s.secondInter p (p' -ᵥ p)) := by
  by_cases h : p' = p; · simp [h]
  refine
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p') hp hp'
      ((Sphere.secondInter_mem _).2 hp) ?_
  intro he
  rw [eq_comm]; rw [Sphere.secondInter_eq_self_iff]; rw [← neg_neg (p' -ᵥ p)]; rw [inner_neg_left]; rw [neg_vsub_eq_vsub_rev]; rw [neg_eq_zero]; rw [eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he

/--
theorem `Sphere.sbtw_secondInter` / 定理 `Sphere.sbtw_secondInter`

English:
theorem Sphere.sbtw_secondInter
  statement: {s : Sphere P} {p p' : P} (hp : p in s)
  proof: by
  refine ⟨Sphere.wbtw_secondInter hp hp'.le, ?_, ?_⟩
  · rintro rfl
    rw [mem_sphere] at hp
    simp [hp] at hp'
  · rintro h
    rw [h]; rw [mem_sphere.1 ((Sphere.secondInter_mem _).2 hp)] at hp'
    exact lt_irrefl _ hp'

中文:
定理 球面.sbtw_second整数er
  结论: {s : 球面 P} {p p' : P} (hp : p in s)
  证明: by
  refine ⟨Sphere.wbtw_secondInter hp hp'.le, ?_, ?_⟩
  · rintro rfl
    rw [mem_sphere] at hp
    simp [hp] at hp'
  · rintro h
    rw [h]; rw [mem_sphere.1 ((Sphere.secondInter_mem _).2 hp)] at hp'
    exact lt_irrefl _ hp'

Depends on / 依赖: Sphere, Sphere.secondInter_mem, Sphere.wbtw_secondInter, lt_irrefl, mem_sphere, secondInter_mem, wbtw_secondInter
-/
theorem Sphere.sbtw_secondInter {s : Sphere P} {p p' : P} (hp : p in s)
    (hp' : dist p' s.center < s.radius) : Sbtw Real p p' (s.secondInter p (p' -ᵥ p)) := by
  refine ⟨Sphere.wbtw_secondInter hp hp'.le, ?_, ?_⟩
  · rintro rfl
    rw [mem_sphere] at hp
    simp [hp] at hp'
  · rintro h
    rw [h]; rw [mem_sphere.1 ((Sphere.secondInter_mem _).2 hp)] at hp'
    exact lt_irrefl _ hp'

/--
lemma `Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite` / 引理 `Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite`

English:
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite
  statement: {s : Sphere P}
  proof: Sbtw.sOppSide_of_notMem_of_mem
    (s.sbtw_secondInter hi ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
      (fun j => hsx _)))
    (by simp)
    (Set.mem_of_mem_of_subset hp ((sx.faceOpposite i).interior_subset_closedInterior.trans
      (sx.faceOpposite i).closedInterior_subset_affineSpan))

中文:
引理 球面.sOppSide_faceOpposite_second整数er_of_mem_interior_faceOpposite
  结论: {s : 球面 P}
  证明: Sbtw.sOppSide_of_notMem_of_mem
    (s.sbtw_secondInter hi ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
      (fun j => hsx _)))
    (by simp)
    (Set.mem_of_mem_of_subset hp ((sx.faceOpposite i).interior_subset_closedInterior.trans
      (sx.faceOpposite i).closedInterior_subset_affineSpan))

Depends on / 依赖: Sbtw.sOppSide_of_notMem_of_mem, Set.mem_of_mem_of_subset, closedInterior_subset_affineSpan, dist_lt_of_mem_interior_of_strictConvexSpace, faceOpposite, interior_subset_closedInterior, interior_subset_closedInterior.trans, mem_of_mem_of_subset, s.sbtw_secondInter, sOppSide_of_notMem_of_mem, sbtw_secondInter, sx.faceOpposite
-/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite {s : Sphere P}
    {n : Nat} [NeZero n] {sx : Affine.Simplex Real P n} {i : Fin (n + 1)} (hi : sx.points i in s)
    (hsx : forall j, dist (sx.points j) s.center <= s.radius) {p : P}
    (hp : p in (sx.faceOpposite i).interior) :
    (affineSpan Real (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i))) :=
  Sbtw.sOppSide_of_notMem_of_mem
    (s.sbtw_secondInter hi ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
      (fun j => hsx _)))
    (by simp)
    (Set.mem_of_mem_of_subset hp ((sx.faceOpposite i).interior_subset_closedInterior.trans
      (sx.faceOpposite i).closedInterior_subset_affineSpan))

attribute [local instance] Nat.AtLeastTwo.neZero_sub_one

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior` / 引理 `Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior`

English:
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior
  statement: {s : Sphere P}
  proof: by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  let r : Real := (1 - w i)⁻¹
  have hrpos : 0 < r := by simp [inv_pos, sub_pos, r, (hw01 i).2]
  let p' : P := AffineMap.lineMap (sx.points i) (Finset.univ.affineCombination Real sx.points w) r
  have hp' : (p' -ᵥ (sx.points i)) =
      r • (Finset.univ.affineCombination Real sx.points w -ᵥ (sx.points i)) := by simp [p']
  suffices (affineSpan Real (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p' -ᵥ (sx.points i))) by
    rwa [hp', s.secondInter_smul _ _ hrpos.ne'] at this
  refine s.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite hi hsx ?_
  simp_rw [p', ← Finset.univ.affineCombination_piSingle Real (sx.points)
    (Finset.mem_univ i), AffineMap.lineMap_apply, Finset.affineCombination_vsub,
    ← LinearMap.map_smul, Finset.weightedVSub_vadd_affineCombination,
    Affine.Simplex.faceOpposite]
  rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos]
  · simp only [Finset.mem_compl, Finset.mem_singleton, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Decidable.not_not, forall_eq, Pi.single_eq_same]
    refine ⟨fun j hj => ?_, by grind⟩
    simp [hj, hrpos, (hw01 j).1]
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw]

中文:
引理 球面.sOppSide_faceOpposite_second整数er_of_mem_interior
  结论: {s : 球面 P}
  证明: by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  let r : Real := (1 - w i)⁻¹
  have hrpos : 0 < r := by simp [inv_pos, sub_pos, r, (hw01 i).2]
  let p' : P := AffineMap.lineMap (sx.points i) (Finset.univ.affineCombination Real sx.points w) r
  have hp' : (p' -ᵥ (sx.points i)) =
      r • (Finset.univ.affineCombination Real sx.points w -ᵥ (sx.points i)) := by simp [p']
  suffices (affineSpan Real (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p' -ᵥ (sx.points i))) by
    rwa [hp', s.secondInter_smul _ _ hrpos.ne'] at this
  refine s.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite hi hsx ?_
  simp_rw [p', ← Finset.univ.affineCombination_piSingle Real (sx.points)
    (Finset.mem_univ i), AffineMap.lineMap_apply, Finset.affineCombination_vsub,
    ← LinearMap.map_smul, Finset.weightedVSub_vadd_affineCombination,
    Affine.Simplex.faceOpposite]
  rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos]
  · simp only [Finset.mem_compl, Finset.mem_singleton, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Decidable.not_not, forall_eq, Pi.single_eq_same]
    refine ⟨fun j hj => ?_, by grind⟩
    simp [hj, hrpos, (hw01 j).1]
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw]

Depends on / 依赖: AffineMap, AffineMap.lineMap, Finset, Finset.univ.affineCombination, SOppSide, Set.range, affineCombination, affineSpan, faceOpposite, inv_pos, lineMap, points, s.secondInter, secondInter, sub_pos, sx.faceOpposite, sx.points
-/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior {s : Sphere P}
    {n : Nat} [Nat.AtLeastTwo n] {sx : Affine.Simplex Real P n} {i : Fin (n + 1)} (hi : sx.points i in s)
    (hsx : forall j, dist (sx.points j) s.center <= s.radius) {p : P}
    (hp : p in sx.interior) :
    (affineSpan Real (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i))) := by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  let r : Real := (1 - w i)⁻¹
  have hrpos : 0 < r := by simp [inv_pos, sub_pos, r, (hw01 i).2]
  let p' : P := AffineMap.lineMap (sx.points i) (Finset.univ.affineCombination Real sx.points w) r
  have hp' : (p' -ᵥ (sx.points i)) =
      r • (Finset.univ.affineCombination Real sx.points w -ᵥ (sx.points i)) := by simp [p']
  suffices (affineSpan Real (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p' -ᵥ (sx.points i))) by
    rwa [hp', s.secondInter_smul _ _ hrpos.ne'] at this
  refine s.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite hi hsx ?_
  simp_rw [p', ← Finset.univ.affineCombination_piSingle Real (sx.points)
    (Finset.mem_univ i), AffineMap.lineMap_apply, Finset.affineCombination_vsub,
    ← LinearMap.map_smul, Finset.weightedVSub_vadd_affineCombination,
    Affine.Simplex.faceOpposite]
  rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos]
  · simp only [Finset.mem_compl, Finset.mem_singleton, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Decidable.not_not, forall_eq, Pi.single_eq_same]
    refine ⟨fun j hj => ?_, by grind⟩
    simp [hj, hrpos, (hw01 j).1]
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw]

end EuclideanGeometry
