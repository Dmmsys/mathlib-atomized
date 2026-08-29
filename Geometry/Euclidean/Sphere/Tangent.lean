/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

/-!
# Tangency for spheres.

This file defines notions of spheres being tangent to affine subspaces and other spheres.

## Main definitions

* `EuclideanGeometry.Sphere.IsTangentAt`: the property of an affine subspace being tangent to a
  sphere at a given point.

* `EuclideanGeometry.Sphere.IsTangent`: the property of an affine subspace being tangent to a
  sphere at some point.

* `EuclideanGeometry.Sphere.tangentSet`: the set of all maximal tangent spaces to a given sphere.

* `EuclideanGeometry.Sphere.tangentsFrom`: the set of all maximal tangent spaces to a given
  sphere and containing a given point.

* `EuclideanGeometry.Sphere.commonTangents`: the set of all maximal common tangent spaces to two
  given spheres.

* `EuclideanGeometry.Sphere.commonIntTangents`: the set of all maximal common internal tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.commonExtTangents`: the set of all maximal common external tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.IsExtTangentAt`: the property of two spheres being externally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsIntTangentAt`: the property of two spheres being internally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsExtTangent`: the property of two spheres being externally tangent.

* `EuclideanGeometry.Sphere.IsIntTangent`: the property of two spheres being internally tangent.

-/

@[expose] public section


namespace EuclideanGeometry

namespace Sphere

open AffineSubspace RealInnerProductSpace
open scoped Affine

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P] [NormedAddTorsor V P]

/--
Definition of `IsTangentAt` / `IsTangentAt` 的定义

English:
structure IsTangentAt
  parameters: (s : Sphere P) (p : P) (as : AffineSubspace Real P)
  axioms and operations (3):
    - mem_sphere : p in s
    - mem_space : p in as
    - le_orthRadius : as <= s.orthRadius p

中文:
结构 是TangentAt
  参数: (s : 球面 P) (p : P) (as : 仿射子空间 实数 P)
  公理与运算 (3 个):
    - mem_sphere : p in s
    - mem_space : p in as
    - le_orthRadius : as <= s.orthRadius p
-/
structure IsTangentAt (s : Sphere P) (p : P) (as : AffineSubspace Real P) : Prop where
  mem_sphere : p in s
  mem_space : p in as
  le_orthRadius : as <= s.orthRadius p

/--
lemma `isTangentAt_orthRadius_iff_mem` / 引理 `isTangentAt_orthRadius_iff_mem`

English:
lemma isTangentAt_orthRadius_iff_mem
  given: {s : Sphere P} {p : P}
  proof: ⟨fun h => h.mem_sphere, fun h => ⟨h, self_mem_orthRadius _ _, le_rfl⟩⟩

中文:
引理 isTangentAt_orthRadius_iff_mem
  条件: {s : 球面 P} {p : P}
  证明: ⟨fun h => h.mem_sphere, fun h => ⟨h, self_mem_orthRadius _ _, le_rfl⟩⟩
-/
@[simp] lemma isTangentAt_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangentAt p (s.orthRadius p) ↔ p in s :=
  ⟨fun h => h.mem_sphere, fun h => ⟨h, self_mem_orthRadius _ _, le_rfl⟩⟩

/--
lemma `IsTangentAt.inner_left_eq_zero_of_mem` / 引理 `IsTangentAt.inner_left_eq_zero_of_mem`

English:
lemma IsTangentAt.inner_left_eq_zero_of_mem
  statement: {s : Sphere P} {p : P} {as : AffineSubspace Real P}
  proof: mem_orthRadius_iff_inner_left.1 (h.le_orthRadius hx)

中文:
引理 是TangentAt.inner_left_eq_zero_of_mem
  结论: {s : 球面 P} {p : P} {as : 仿射子空间 实数 P}
  证明: mem_orthRadius_iff_inner_left.1 (h.le_orthRadius hx)

Depends on / 依赖: h.le_orthRadius, le_orthRadius, mem_orthRadius_iff_inner_left
-/
lemma IsTangentAt.inner_left_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) {x : P} (hx : x in as) : ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 :=
  mem_orthRadius_iff_inner_left.1 (h.le_orthRadius hx)

/--
lemma `IsTangentAt.inner_right_eq_zero_of_mem` / 引理 `IsTangentAt.inner_right_eq_zero_of_mem`

English:
lemma IsTangentAt.inner_right_eq_zero_of_mem
  statement: {s : Sphere P} {p : P} {as : AffineSubspace Real P}
  proof: mem_orthRadius_iff_inner_right.1 (h.le_orthRadius hx)

中文:
引理 是TangentAt.inner_right_eq_zero_of_mem
  结论: {s : 球面 P} {p : P} {as : 仿射子空间 实数 P}
  证明: mem_orthRadius_iff_inner_right.1 (h.le_orthRadius hx)

Depends on / 依赖: h.le_orthRadius, le_orthRadius, mem_orthRadius_iff_inner_right
-/
lemma IsTangentAt.inner_right_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) {x : P} (hx : x in as) : ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 :=
  mem_orthRadius_iff_inner_right.1 (h.le_orthRadius hx)

/--
lemma `IsTangentAt.eq_of_isTangentAt` / 引理 `IsTangentAt.eq_of_isTangentAt`

English:
lemma IsTangentAt.eq_of_isTangentAt
  statement: {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
  proof: by
  have hqp := hp.inner_left_eq_zero_of_mem hq.mem_space
  have hpq := hq.inner_left_eq_zero_of_mem hp.mem_space
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]; rw [← hpq]; rw [← sub_eq_zero]; rw [← inner_sub_right]; rw [vsub_sub_vsub_cancel_right] at hqp
  simpa using hqp

中文:
引理 是TangentAt.eq_of_isTangentAt
  结论: {s : 球面 P} {p q : P} {as : 仿射子空间 实数 P}
  证明: by
  have hqp := hp.inner_left_eq_zero_of_mem hq.mem_space
  have hpq := hq.inner_left_eq_zero_of_mem hp.mem_space
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]; rw [← hpq]; rw [← sub_eq_zero]; rw [← inner_sub_right]; rw [vsub_sub_vsub_cancel_right] at hqp
  simpa using hqp

Depends on / 依赖: hp.inner_left_eq_zero_of_mem, hp.mem_space, hq.inner_left_eq_zero_of_mem, hq.mem_space, inner_left_eq_zero_of_mem, inner_neg_left, inner_sub_right, mem_space, neg_eq_zero, neg_vsub_eq_vsub_rev, sub_eq_zero, vsub_sub_vsub_cancel_right
-/
lemma IsTangentAt.eq_of_isTangentAt {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
    (hp : s.IsTangentAt p as) (hq : s.IsTangentAt q as) : p = q := by
  have hqp := hp.inner_left_eq_zero_of_mem hq.mem_space
  have hpq := hq.inner_left_eq_zero_of_mem hp.mem_space
  rw [← neg_vsub_eq_vsub_rev]; rw [inner_neg_left]; rw [neg_eq_zero]; rw [← hpq]; rw [← sub_eq_zero]; rw [← inner_sub_right]; rw [vsub_sub_vsub_cancel_right] at hqp
  simpa using hqp

/--
lemma `isTangentAt_center_iff` / 引理 `isTangentAt_center_iff`

English:
lemma isTangentAt_center_iff
  given: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hm, -⟩
    rw [center_mem_iff] at hr
    exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    refine ⟨?_, hm, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

中文:
引理 isTangentAt_center_iff
  条件: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hm, -⟩
    rw [center_mem_iff] at hr
    exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    refine ⟨?_, hm, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

Depends on / 依赖: center_mem_iff
-/
lemma isTangentAt_center_iff {s : Sphere P} {as : AffineSubspace Real P} :
    s.IsTangentAt s.center as ↔ s.radius = 0 ∧ s.center in as := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hm, -⟩
    rw [center_mem_iff] at hr
    exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    refine ⟨?_, hm, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

/--
lemma `IsTangentAt.dist_sq_eq_of_mem` / 引理 `IsTangentAt.dist_sq_eq_of_mem`

English:
lemma IsTangentAt.dist_sq_eq_of_mem
  statement: {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
  proof: by
  rw [← h.mem_sphere]
  exact s.dist_sq_eq_of_mem_orthRadius (SetLike.le_def.1 h.le_orthRadius hq)

中文:
引理 是TangentAt.dist_sq_eq_of_mem
  结论: {s : 球面 P} {p q : P} {as : 仿射子空间 实数 P}
  证明: by
  rw [← h.mem_sphere]
  exact s.dist_sq_eq_of_mem_orthRadius (SetLike.le_def.1 h.le_orthRadius hq)

Depends on / 依赖: SetLike, SetLike.le_def, dist_sq_eq_of_mem_orthRadius, h.le_orthRadius, h.mem_sphere, le_def, le_orthRadius, mem_sphere, s.dist_sq_eq_of_mem_orthRadius
-/
lemma IsTangentAt.dist_sq_eq_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) (hq : q in as) :
    (dist q s.center) ^ 2 = s.radius ^ 2 + (dist q p) ^ 2 := by
  rw [← h.mem_sphere]
  exact s.dist_sq_eq_of_mem_orthRadius (SetLike.le_def.1 h.le_orthRadius hq)

/--
lemma `IsTangentAt.mem_and_mem_iff_eq` / 引理 `IsTangentAt.mem_and_mem_iff_eq`

English:
lemma IsTangentAt.mem_and_mem_iff_eq
  statement: {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
  proof: by
  refine ⟨fun ⟨hs, has⟩ => ?_, ?_⟩
  · have hd := h.dist_sq_eq_of_mem has
    rw [hs] at hd
    simpa using hd
  · rintro rfl
    exact ⟨h.mem_sphere, h.mem_space⟩

中文:
引理 是TangentAt.mem_and_mem_iff_eq
  结论: {s : 球面 P} {p q : P} {as : 仿射子空间 实数 P}
  证明: by
  refine ⟨fun ⟨hs, has⟩ => ?_, ?_⟩
  · have hd := h.dist_sq_eq_of_mem has
    rw [hs] at hd
    simpa using hd
  · rintro rfl
    exact ⟨h.mem_sphere, h.mem_space⟩

Depends on / 依赖: dist_sq_eq_of_mem, h.dist_sq_eq_of_mem, h.mem_space, h.mem_sphere, mem_space, mem_sphere
-/
lemma IsTangentAt.mem_and_mem_iff_eq {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) : (q in s ∧ q in as) ↔ q = p := by
  refine ⟨fun ⟨hs, has⟩ => ?_, ?_⟩
  · have hd := h.dist_sq_eq_of_mem has
    rw [hs] at hd
    simpa using hd
  · rintro rfl
    exact ⟨h.mem_sphere, h.mem_space⟩

/--
lemma `IsTangentAt.eq_of_mem_of_mem` / 引理 `IsTangentAt.eq_of_mem_of_mem`

English:
lemma IsTangentAt.eq_of_mem_of_mem
  statement: {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
  proof: h.mem_and_mem_iff_eq.1 ⟨hs, has⟩

中文:
引理 是TangentAt.eq_of_mem_of_mem
  结论: {s : 球面 P} {p q : P} {as : 仿射子空间 实数 P}
  证明: h.mem_and_mem_iff_eq.1 ⟨hs, has⟩

Depends on / 依赖: h.mem_and_mem_iff_eq, mem_and_mem_iff_eq
-/
lemma IsTangentAt.eq_of_mem_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) (hs : q in s) (has : q in as) : q = p :=
  h.mem_and_mem_iff_eq.1 ⟨hs, has⟩

/--
lemma `IsTangentAt.dist_eq_of_mem_of_mem` / 引理 `IsTangentAt.dist_eq_of_mem_of_mem`

English:
lemma IsTangentAt.dist_eq_of_mem_of_mem
  statement: {s : Sphere P} {p₁ p₂ q : P}
  proof: by
  have h1 := dist_sq_eq_of_mem h₁ hq_mem₁
  have h2 := dist_sq_eq_of_mem h₂ hq_mem₂
  rwa [h1, add_left_cancel_iff, sq_eq_sq₀ dist_nonneg dist_nonneg] at h2

中文:
引理 是TangentAt.dist_eq_of_mem_of_mem
  结论: {s : 球面 P} {p₁ p₂ q : P}
  证明: by
  have h1 := dist_sq_eq_of_mem h₁ hq_mem₁
  have h2 := dist_sq_eq_of_mem h₂ hq_mem₂
  rwa [h1, add_left_cancel_iff, sq_eq_sq₀ dist_nonneg dist_nonneg] at h2

Depends on / 依赖: add_left_cancel_iff, dist_nonneg, dist_sq_eq_of_mem
-/
lemma IsTangentAt.dist_eq_of_mem_of_mem {s : Sphere P} {p₁ p₂ q : P}
    {as₁ as₂ : AffineSubspace Real P}
    (h₁ : s.IsTangentAt p₁ as₁) (h₂ : s.IsTangentAt p₂ as₂) (hq_mem₁ : q in as₁)
    (hq_mem₂ : q in as₂) :
    dist q p₁ = dist q p₂ := by
  have h1 := dist_sq_eq_of_mem h₁ hq_mem₁
  have h2 := dist_sq_eq_of_mem h₂ hq_mem₂
  rwa [h1, add_left_cancel_iff, sq_eq_sq₀ dist_nonneg dist_nonneg] at h2

/--
lemma `IsTangentAt.radius_lt_dist_center` / 引理 `IsTangentAt.radius_lt_dist_center`

English:
lemma IsTangentAt.radius_lt_dist_center
  statement: {s : Sphere P} {as : AffineSubspace Real P} {p q : P}
  proof: by
  suffices s.radius ^ 2 < dist q s.center ^ 2 by
    simpa [sq_lt_sq, abs_of_nonneg (s.radius_nonneg_of_mem h.mem_sphere)] using this
  rw [h.dist_sq_eq_of_mem hq]
  simp [hqp]

中文:
引理 是TangentAt.radius_lt_dist_center
  结论: {s : 球面 P} {as : 仿射子空间 实数 P} {p q : P}
  证明: by
  suffices s.radius ^ 2 < dist q s.center ^ 2 by
    simpa [sq_lt_sq, abs_of_nonneg (s.radius_nonneg_of_mem h.mem_sphere)] using this
  rw [h.dist_sq_eq_of_mem hq]
  simp [hqp]

Depends on / 依赖: abs_of_nonneg, center, dist_sq_eq_of_mem, h.dist_sq_eq_of_mem, h.mem_sphere, mem_sphere, radius, radius_nonneg_of_mem, s.center, s.radius, s.radius_nonneg_of_mem, sq_lt_sq
-/
lemma IsTangentAt.radius_lt_dist_center {s : Sphere P} {as : AffineSubspace Real P} {p q : P}
    (h : s.IsTangentAt p as) (hq : q in as) (hqp : q != p) : s.radius < dist q s.center := by
  suffices s.radius ^ 2 < dist q s.center ^ 2 by
    simpa [sq_lt_sq, abs_of_nonneg (s.radius_nonneg_of_mem h.mem_sphere)] using this
  rw [h.dist_sq_eq_of_mem hq]
  simp [hqp]

/--
lemma `IsTangentAt.eq_orthRadius_of_finrank_add_one_eq` / 引理 `IsTangentAt.eq_orthRadius_of_finrank_add_one_eq`

English:
lemma IsTangentAt.eq_orthRadius_of_finrank_add_one_eq
  statement: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  have : FiniteDimensional Real V := Module.finite_of_finrank_eq_succ hfr.symm
  have hp : p != s.center := fun h => (h ▸ s.center_mem_iff).not.2 hr ht.mem_sphere
  rw [← finrank_orthRadius hp]; rw [Nat.add_right_cancel_iff] at hfr
  exact eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of

中文:
引理 是TangentAt.eq_orthRadius_of_finrank_add_one_eq
  结论: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  have : FiniteDimensional Real V := Module.finite_of_finrank_eq_succ hfr.symm
  have hp : p != s.center := fun h => (h ▸ s.center_mem_iff).not.2 hr ht.mem_sphere
  rw [← finrank_orthRadius hp]; rw [Nat.add_right_cancel_iff] at hfr
  exact eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of

Depends on / 依赖: FiniteDimensional, Module, Module.finite_of_finrank_eq_succ, Nat.add_right_cancel_iff, Submodule, Submodule.eq_of_le_of_finrank_eq, add_right_cancel_iff, center, center_mem_iff, direction_le, eq_of_direction_eq_of_nonempty_of_le, eq_of_le_of_finrank_eq, finite_of_finrank_eq_succ, finrank_orthRadius, hfr.symm, ht.le_orthRadius, ht.mem_space, ht.mem_sphere, le_orthRadius, mem_space
-/
lemma IsTangentAt.eq_orthRadius_of_finrank_add_one_eq {s : Sphere P} {as : AffineSubspace Real P}
    {p : P} (ht : s.IsTangentAt p as) (hr : s.radius != 0)
    (hfr : Module.finrank Real as.direction + 1 = Module.finrank Real V) : as = s.orthRadius p := by
  have : FiniteDimensional Real V := Module.finite_of_finrank_eq_succ hfr.symm
  have hp : p != s.center := fun h => (h ▸ s.center_mem_iff).not.2 hr ht.mem_sphere
  rw [← finrank_orthRadius hp]; rw [Nat.add_right_cancel_iff] at hfr
  exact eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (direction_le ht.le_orthRadius) hfr) ⟨p, ht.mem_space⟩
    ht.le_orthRadius

/--
Definition of `IsTangent` / `IsTangent` 的定义

English:
definition IsTangent
  signature: (s : Sphere P) (as : AffineSubspace Real P)
  body: exists p, s.IsTangentAt p as

中文:
定义 IsTangent
  签名: (s : 球面 P) (as : 仿射子空间 实数 P)
  定义体: exists p, s.IsTangentAt p as

Depends on / 依赖: IsTangentAt, s.IsTangentAt
-/
def IsTangent (s : Sphere P) (as : AffineSubspace Real P) : Prop :=
  exists p, s.IsTangentAt p as

/--
lemma `IsTangentAt.isTangent` / 引理 `IsTangentAt.isTangent`

English:
lemma IsTangentAt.isTangent
  statement: {s : Sphere P} {p : P} {as : AffineSubspace Real P}
  proof: ⟨p, h⟩

中文:
引理 是TangentAt.isTangent
  结论: {s : 球面 P} {p : P} {as : 仿射子空间 实数 P}
  证明: ⟨p, h⟩
-/
lemma IsTangentAt.isTangent {s : Sphere P} {p : P} {as : AffineSubspace Real P}
    (h : s.IsTangentAt p as) : s.IsTangent as :=
  ⟨p, h⟩

/--
lemma `isTangent_orthRadius_iff_mem` / 引理 `isTangent_orthRadius_iff_mem`

English:
lemma isTangent_orthRadius_iff_mem
  given: {s : Sphere P} {p : P}
  proof: by
  refine ⟨?_, fun h => (isTangentAt_orthRadius_iff_mem.2 h).isTangent⟩
  rintro ⟨q, hs, hsp, hle⟩
  rw [orthRadius_le_orthRadius_iff] at hle
  rcases hle with rfl | rfl
  · exact hs
  · rw [center_mem_orthRadius_iff] at hsp
    rwa [← hsp] at hs

中文:
引理 isTangent_orthRadius_iff_mem
  条件: {s : 球面 P} {p : P}
  证明: by
  refine ⟨?_, fun h => (isTangentAt_orthRadius_iff_mem.2 h).isTangent⟩
  rintro ⟨q, hs, hsp, hle⟩
  rw [orthRadius_le_orthRadius_iff] at hle
  rcases hle with rfl | rfl
  · exact hs
  · rw [center_mem_orthRadius_iff] at hsp
    rwa [← hsp] at hs
-/
@[simp] lemma isTangent_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangent (s.orthRadius p) ↔ p in s := by
  refine ⟨?_, fun h => (isTangentAt_orthRadius_iff_mem.2 h).isTangent⟩
  rintro ⟨q, hs, hsp, hle⟩
  rw [orthRadius_le_orthRadius_iff] at hle
  rcases hle with rfl | rfl
  · exact hs
  · rw [center_mem_orthRadius_iff] at hsp
    rwa [← hsp] at hs

/--
lemma `IsTangent.radius_le_dist_center` / 引理 `IsTangent.radius_le_dist_center`

English:
lemma IsTangent.radius_le_dist_center
  statement: {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as)
  proof: by
  obtain ⟨x, h⟩ := h
  refine le_of_sq_le_sq ?_ dist_nonneg
  rw [h.dist_sq_eq_of_mem hp]; rw [le_add_iff_nonneg_right]
  exact sq_nonneg _

中文:
引理 IsTangent.radius_le_dist_center
  结论: {s : 球面 P} {as : 仿射子空间 实数 P} (h : s.IsTangent as)
  证明: by
  obtain ⟨x, h⟩ := h
  refine le_of_sq_le_sq ?_ dist_nonneg
  rw [h.dist_sq_eq_of_mem hp]; rw [le_add_iff_nonneg_right]
  exact sq_nonneg _

Depends on / 依赖: dist_nonneg, dist_sq_eq_of_mem, h.dist_sq_eq_of_mem, le_add_iff_nonneg_right, le_of_sq_le_sq, sq_nonneg
-/
lemma IsTangent.radius_le_dist_center {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as)
    {p : P} (hp : p in as) : s.radius <= dist p s.center := by
  obtain ⟨x, h⟩ := h
  refine le_of_sq_le_sq ?_ dist_nonneg
  rw [h.dist_sq_eq_of_mem hp]; rw [le_add_iff_nonneg_right]
  exact sq_nonneg _

/--
lemma `IsTangent.notMem_of_dist_lt` / 引理 `IsTangent.notMem_of_dist_lt`

English:
lemma IsTangent.notMem_of_dist_lt
  statement: {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as)
  proof: by
  contrapose! hp
  exact h.radius_le_dist_center hp

中文:
引理 IsTangent.notMem_of_dist_lt
  结论: {s : 球面 P} {as : 仿射子空间 实数 P} (h : s.IsTangent as)
  证明: by
  contrapose! hp
  exact h.radius_le_dist_center hp

Depends on / 依赖: contrapose, h.radius_le_dist_center, radius_le_dist_center
-/
lemma IsTangent.notMem_of_dist_lt {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as)
    {p : P} (hp : dist p s.center < s.radius) : p ∉ as := by
  contrapose! hp
  exact h.radius_le_dist_center hp

/--
lemma `IsTangent.infDist_eq_radius` / 引理 `IsTangent.infDist_eq_radius`

English:
lemma IsTangent.infDist_eq_radius
  given: {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as)
  proof: by
  obtain ⟨p, h⟩ := h
  refine le_antisymm ?_ ?_
  · convert! Metric.infDist_le_dist_of_mem h.mem_space
    rw [mem_sphere'.1 h.mem_sphere]
  · rw [Metric.infDist_eq_iInf]
    have : Nonempty as := ⟨⟨p, h.mem_space⟩⟩
    refine le_ciInf fun x => ?_
    rw [dist_comm]
    exact h.isTangent.radius_l

中文:
引理 IsTangent.infDist_eq_radius
  条件: {s : 球面 P} {as : 仿射子空间 实数 P} (h : s.IsTangent as)
  证明: by
  obtain ⟨p, h⟩ := h
  refine le_antisymm ?_ ?_
  · convert! Metric.infDist_le_dist_of_mem h.mem_space
    rw [mem_sphere'.1 h.mem_sphere]
  · rw [Metric.infDist_eq_iInf]
    have : Nonempty as := ⟨⟨p, h.mem_space⟩⟩
    refine le_ciInf fun x => ?_
    rw [dist_comm]
    exact h.isTangent.radius_l

Depends on / 依赖: Metric, Metric.infDist_eq_iInf, Metric.infDist_le_dist_of_mem, Nonempty, convert, dist_comm, h.isTangent.radius_le_dist_center, h.mem_space, h.mem_sphere, infDist_eq_iInf, infDist_le_dist_of_mem, isTangent, le_antisymm, le_ciInf, mem_space, mem_sphere, property, radius_le_dist_center, x.property
-/
lemma IsTangent.infDist_eq_radius {s : Sphere P} {as : AffineSubspace Real P} (h : s.IsTangent as) :
    Metric.infDist s.center as = s.radius := by
  obtain ⟨p, h⟩ := h
  refine le_antisymm ?_ ?_
  · convert! Metric.infDist_le_dist_of_mem h.mem_space
    rw [mem_sphere'.1 h.mem_sphere]
  · rw [Metric.infDist_eq_iInf]
    have : Nonempty as := ⟨⟨p, h.mem_space⟩⟩
    refine le_ciInf fun x => ?_
    rw [dist_comm]
    exact h.isTangent.radius_le_dist_center x.property

/--
lemma `dist_orthogonalProjection_eq_radius_iff_isTangentAt` / 引理 `dist_orthogonalProjection_eq_radius_iff_isTangentAt`

English:
lemma dist_orthogonalProjection_eq_radius_iff_isTangentAt
  statement: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨?_, orthogonalProjection_mem _, fun p hp => ?_⟩
    · rwa [mem_sphere']
    · rw [mem_orthRadius_iff_inner_left]
      exact orthogonalProjection_vsub_mem_direction_orthogonal as s.center _
        (vsub_orthogonalProjection_mem_direction s.center h

中文:
引理 dist_orthogonalProjection_eq_radius_iff_isTangentAt
  结论: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨?_, orthogonalProjection_mem _, fun p hp => ?_⟩
    · rwa [mem_sphere']
    · rw [mem_orthRadius_iff_inner_left]
      exact orthogonalProjection_vsub_mem_direction_orthogonal as s.center _
        (vsub_orthogonalProjection_mem_direction s.center h

Depends on / 依赖: center, dist_orthogonalProjection_eq_infDist, h.isTangent.infDist_eq_radius, infDist_eq_radius, isTangent, mem_orthRadius_iff_inner_left, mem_sphere, orthogonalProjection_mem, orthogonalProjection_vsub_mem_direction_orthogonal, s.center, vsub_orthogonalProjection_mem_direction
-/
lemma dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : AffineSubspace Real P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔
      s.IsTangentAt (orthogonalProjection as s.center) as := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨?_, orthogonalProjection_mem _, fun p hp => ?_⟩
    · rwa [mem_sphere']
    · rw [mem_orthRadius_iff_inner_left]
      exact orthogonalProjection_vsub_mem_direction_orthogonal as s.center _
        (vsub_orthogonalProjection_mem_direction s.center hp)
  · rw [dist_orthogonalProjection_eq_infDist, h.isTangent.infDist_eq_radius]

/--
lemma `dist_orthogonalProjection_eq_radius_iff_isTangent` / 引理 `dist_orthogonalProjection_eq_radius_iff_isTangent`

English:
lemma dist_orthogonalProjection_eq_radius_iff_isTangent
  statement: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  refine ⟨fun h => (dist_orthogonalProjection_eq_radius_iff_isTangentAt.1 h).isTangent, fun h => ?_⟩
  rw [dist_orthogonalProjection_eq_infDist]; rw [h.infDist_eq_radius]

中文:
引理 dist_orthogonalProjection_eq_radius_iff_isTangent
  结论: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  refine ⟨fun h => (dist_orthogonalProjection_eq_radius_iff_isTangentAt.1 h).isTangent, fun h => ?_⟩
  rw [dist_orthogonalProjection_eq_infDist]; rw [h.infDist_eq_radius]

Depends on / 依赖: dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_radius_iff_isTangentAt, h.infDist_eq_radius, infDist_eq_radius, isTangent
-/
lemma dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace Real P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔ s.IsTangent as := by
  refine ⟨fun h => (dist_orthogonalProjection_eq_radius_iff_isTangentAt.1 h).isTangent, fun h => ?_⟩
  rw [dist_orthogonalProjection_eq_infDist]; rw [h.infDist_eq_radius]

/--
lemma `infDist_eq_radius_iff_isTangent` / 引理 `infDist_eq_radius_iff_isTangent`

English:
lemma infDist_eq_radius_iff_isTangent
  statement: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  rw [← dist_orthogonalProjection_eq_infDist]; rw [dist_orthogonalProjection_eq_radius_iff_isTangent]

中文:
引理 infDist_eq_radius_iff_isTangent
  结论: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  rw [← dist_orthogonalProjection_eq_infDist]; rw [dist_orthogonalProjection_eq_radius_iff_isTangent]

Depends on / 依赖: dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_radius_iff_isTangent
-/
lemma infDist_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace Real P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    Metric.infDist s.center as = s.radius ↔ s.IsTangent as := by
  rw [← dist_orthogonalProjection_eq_infDist]; rw [dist_orthogonalProjection_eq_radius_iff_isTangent]

/--
lemma `isTangent_iff_isTangentAt_orthogonalProjection` / 引理 `isTangent_iff_isTangentAt_orthogonalProjection`

English:
lemma isTangent_iff_isTangentAt_orthogonalProjection
  statement: {s : Sphere P} {as : AffineSubspace Real P}
  proof: by
  rw [← dist_orthogonalProjection_eq_radius_iff_isTangent]; rw [dist_orthogonalProjection_eq_radius_iff_isTangentAt]

alias ⟨IsTangent.isTangentAt, _⟩ := isTangent_iff_isTangentAt_orthogonalProjection

中文:
引理 isTangent_iff_isTangentAt_orthogonalProjection
  结论: {s : 球面 P} {as : 仿射子空间 实数 P}
  证明: by
  rw [← dist_orthogonalProjection_eq_radius_iff_isTangent]; rw [dist_orthogonalProjection_eq_radius_iff_isTangentAt]

alias ⟨IsTangent.isTangentAt, _⟩ := isTangent_iff_isTangentAt_orthogonalProjection

Depends on / 依赖: dist_orthogonalProjection_eq_radius_iff_isTangent, dist_orthogonalProjection_eq_radius_iff_isTangentAt
-/
lemma isTangent_iff_isTangentAt_orthogonalProjection {s : Sphere P} {as : AffineSubspace Real P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    s.IsTangent as ↔ s.IsTangentAt (orthogonalProjection as s.center) as := by
  rw [← dist_orthogonalProjection_eq_radius_iff_isTangent]; rw [dist_orthogonalProjection_eq_radius_iff_isTangentAt]

alias ⟨IsTangent.isTangentAt, _⟩ := isTangent_iff_isTangentAt_orthogonalProjection

/--
lemma `IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius` / 引理 `IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius`

English:
lemma IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius
  statement: {s : Sphere P}
  proof: by
  rcases h with ⟨q, hqs, hqas, hqo⟩
  have hd := direction_le hqo
  rw [hpar.direction_eq]; rw [direction_orthRadius_le_iff] at hd
  obtain ⟨r, hr⟩ := hd
  rcases eq_or_ne s.radius 0 with hrad | hrad
  · rw [mem_sphere, hrad, dist_eq_zero] at hp hqs
    rw [hp]; rw [orthRadius_center] at hpar ⊢
 

中文:
引理 IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius
  结论: {s : 球面 P}
  证明: by
  rcases h with ⟨q, hqs, hqas, hqo⟩
  have hd := direction_le hqo
  rw [hpar.direction_eq]; rw [direction_orthRadius_le_iff] at hd
  obtain ⟨r, hr⟩ := hd
  rcases eq_or_ne s.radius 0 with hrad | hrad
  · rw [mem_sphere, hrad, dist_eq_zero] at hp hqs
    rw [hp]; rw [orthRadius_center] at hpar ⊢
 

Depends on / 依赖: direction_eq, direction_le, direction_orthRadius_le_iff, dist_eq_zero, eq_of_direction_eq_of_nonempty_of_le, eq_or_ne, hpar.direction_eq, mem_sphere, orthRadius, orthRadius_center, radius, s.orthRadius, s.radius
-/
lemma IsTangent.eq_orthRadius_or_eq_orthRadius_pointReflection_of_parallel_orthRadius {s : Sphere P}
    {as : AffineSubspace Real P} {p : P} (h : s.IsTangent as) (hpar : as ∥ s.orthRadius p)
    (hp : p in s) :
    as = s.orthRadius p ∨ as = s.orthRadius (Equiv.pointReflection s.center p) := by
  rcases h with ⟨q, hqs, hqas, hqo⟩
  have hd := direction_le hqo
  rw [hpar.direction_eq]; rw [direction_orthRadius_le_iff] at hd
  obtain ⟨r, hr⟩ := hd
  rcases eq_or_ne s.radius 0 with hrad | hrad
  · rw [mem_sphere, hrad, dist_eq_zero] at hp hqs
    rw [hp]; rw [orthRadius_center] at hpar ⊢
    rw [hqs]; rw [orthRadius_center] at hqo
    exact .inl (eq_of_direction_eq_of_nonempty_of_le hpar.direction_eq ⟨q, hqas⟩ hqo)
  obtain rfl : as = s.orthRadius q := by
    refine eq_of_direction_eq_of_nonempty_of_le ?_ ⟨q, hqas⟩ hqo
    rw [hpar.direction_eq]; rw [direction_orthRadius]; rw [direction_orthRadius]
    congr 1
    rcases eq_or_ne r 0 with rfl | hr0
    · simp_all
    · rw [hr, Submodule.span_singleton_smul_eq hr0.isUnit]
  rcases eq_or_ne r 0 with rfl | hr0
  · simp_all
  · have hr' : ‖q -ᵥ s.center‖ = ‖r • (p -ᵥ s.center)‖ := by
      rw [hr]
    simp_rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm_vsub, mem_sphere.1 hp,
      mem_sphere.1 hqs, right_eq_mul₀ hrad] at hr'
    rcases eq_or_eq_neg_of_abs_eq hr' with rfl | rfl
    · simp_all
    · right
      convert! rfl
      rw [← eq_vadd_iff_vsub_eq] at hr
      rw [hr]
      simp [Equiv.pointReflection_apply]

/--
lemma `IsTangentAt.eq_orthogonalProjection` / 引理 `IsTangentAt.eq_orthogonalProjection`

English:
lemma IsTangentAt.eq_orthogonalProjection
  statement: {s : Sphere P} {p : P} {as : AffineSubspace Real P}
  proof: by
  refine h.eq_of_isTangentAt ?_
  have h' := h.isTangent
  rwa [isTangent_iff_isTangentAt_orthogonalProjection] at h'

中文:
引理 是TangentAt.eq_orthogonalProjection
  结论: {s : 球面 P} {p : P} {as : 仿射子空间 实数 P}
  证明: by
  refine h.eq_of_isTangentAt ?_
  have h' := h.isTangent
  rwa [isTangent_iff_isTangentAt_orthogonalProjection] at h'

Depends on / 依赖: eq_of_isTangentAt, h.eq_of_isTangentAt, h.isTangent, isTangent, isTangent_iff_isTangentAt_orthogonalProjection
-/
lemma IsTangentAt.eq_orthogonalProjection {s : Sphere P} {p : P} {as : AffineSubspace Real P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] (h : s.IsTangentAt p as) :
    p = orthogonalProjection as s.center := by
  refine h.eq_of_isTangentAt ?_
  have h' := h.isTangent
  rwa [isTangent_iff_isTangentAt_orthogonalProjection] at h'

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `tangentSet` / `tangentSet` 的定义

English:
definition tangentSet
  signature: (s : Sphere P)
  body: s.orthRadius '' s

中文:
定义 tangentSet
  签名: (s : 球面 P)
  定义体: s.orthRadius '' s

Depends on / 依赖: orthRadius, s.orthRadius
-/
noncomputable def tangentSet (s : Sphere P) : Set (AffineSubspace Real P) :=
  s.orthRadius '' s

/--
lemma `mem_tangentSet_iff` / 引理 `mem_tangentSet_iff`

English:
lemma mem_tangentSet_iff
  given: {as : AffineSubspace Real P} {s : Sphere P}
  proof: Iff.rfl

中文:
引理 mem_tangentSet_iff
  条件: {as : 仿射子空间 实数 P} {s : 球面 P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_tangentSet_iff {as : AffineSubspace Real P} {s : Sphere P} :
    as in s.tangentSet ↔ exists p, p in s ∧ s.orthRadius p = as :=
  Iff.rfl

/--
lemma `isTangent_of_mem_tangentSet` / 引理 `isTangent_of_mem_tangentSet`

English:
lemma isTangent_of_mem_tangentSet
  statement: {as : AffineSubspace Real P} {s : Sphere P}
  proof: by
  rcases h with ⟨p, hps, rfl⟩
  exact isTangent_orthRadius_iff_mem.2 hps

中文:
引理 isTangent_of_mem_tangentSet
  结论: {as : 仿射子空间 实数 P} {s : 球面 P}
  证明: by
  rcases h with ⟨p, hps, rfl⟩
  exact isTangent_orthRadius_iff_mem.2 hps

Depends on / 依赖: isTangent_orthRadius_iff_mem
-/
lemma isTangent_of_mem_tangentSet {as : AffineSubspace Real P} {s : Sphere P}
    (h : as in s.tangentSet) : s.IsTangent as := by
  rcases h with ⟨p, hps, rfl⟩
  exact isTangent_orthRadius_iff_mem.2 hps

/--
Definition of `tangentsFrom` / `tangentsFrom` 的定义

English:
definition tangentsFrom
  signature: (s : Sphere P) (p : P)
  body: {as in s.tangentSet | p in as}

中文:
定义 tangentsFrom
  签名: (s : 球面 P) (p : P)
  定义体: {as in s.tangentSet | p in as}

Depends on / 依赖: s.tangentSet, tangentSet
-/
def tangentsFrom (s : Sphere P) (p : P) : Set (AffineSubspace Real P) :=
  {as in s.tangentSet | p in as}

/--
lemma `mem_tangentsFrom_iff` / 引理 `mem_tangentsFrom_iff`

English:
lemma mem_tangentsFrom_iff
  given: {as : AffineSubspace Real P} {s : Sphere P} {p : P}
  proof: Iff.rfl

中文:
引理 mem_tangentsFrom_iff
  条件: {as : 仿射子空间 实数 P} {s : 球面 P} {p : P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_tangentsFrom_iff {as : AffineSubspace Real P} {s : Sphere P} {p : P} :
    as in s.tangentsFrom p ↔ as in s.tangentSet ∧ p in as :=
  Iff.rfl

/--
lemma `mem_tangentSet_of_mem_tangentsFrom` / 引理 `mem_tangentSet_of_mem_tangentsFrom`

English:
lemma mem_tangentSet_of_mem_tangentsFrom
  statement: {as : AffineSubspace Real P} {s : Sphere P} {p : P}
  proof: h.1

中文:
引理 mem_tangentSet_of_mem_tangentsFrom
  结论: {as : 仿射子空间 实数 P} {s : 球面 P} {p : P}
  证明: h.1
-/
lemma mem_tangentSet_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Sphere P} {p : P}
    (h : as in s.tangentsFrom p) : as in s.tangentSet :=
  h.1

/--
lemma `mem_of_mem_tangentsFrom` / 引理 `mem_of_mem_tangentsFrom`

English:
lemma mem_of_mem_tangentsFrom
  statement: {as : AffineSubspace Real P} {s : Sphere P} {p : P}
  proof: h.2

中文:
引理 mem_of_mem_tangentsFrom
  结论: {as : 仿射子空间 实数 P} {s : 球面 P} {p : P}
  证明: h.2
-/
lemma mem_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Sphere P} {p : P}
    (h : as in s.tangentsFrom p) : p in as :=
  h.2

/--
lemma `isTangent_of_mem_tangentsFrom` / 引理 `isTangent_of_mem_tangentsFrom`

English:
lemma isTangent_of_mem_tangentsFrom
  statement: {as : AffineSubspace Real P} {s : Sphere P} {p : P}
  proof: isTangent_of_mem_tangentSet h.1

中文:
引理 isTangent_of_mem_tangentsFrom
  结论: {as : 仿射子空间 实数 P} {s : 球面 P} {p : P}
  证明: isTangent_of_mem_tangentSet h.1

Depends on / 依赖: isTangent_of_mem_tangentSet
-/
lemma isTangent_of_mem_tangentsFrom {as : AffineSubspace Real P} {s : Sphere P} {p : P}
    (h : as in s.tangentsFrom p) : s.IsTangent as :=
  isTangent_of_mem_tangentSet h.1

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `commonTangents` / `commonTangents` 的定义

English:
definition commonTangents
  signature: (s₁ s₂ : Sphere P)
  body: s₁.tangentSet inter s₂.tangentSet

中文:
定义 commonTangents
  签名: (s₁ s₂ : 球面 P)
  定义体: s₁.tangentSet inter s₂.tangentSet

Depends on / 依赖: tangentSet
-/
noncomputable def commonTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P) :=
  s₁.tangentSet inter s₂.tangentSet

/--
lemma `mem_commonTangents_iff` / 引理 `mem_commonTangents_iff`

English:
lemma mem_commonTangents_iff
  given: {as : AffineSubspace Real P} {s₁ s₂ : Sphere P}
  proof: Iff.rfl

中文:
引理 mem_commonTangents_iff
  条件: {as : 仿射子空间 实数 P} {s₁ s₂ : 球面 P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_commonTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} :
    as in s₁.commonTangents s₂ ↔ as in s₁.tangentSet ∧ as in s₂.tangentSet :=
  Iff.rfl

/--
lemma `commonTangents_comm` / 引理 `commonTangents_comm`

English:
lemma commonTangents_comm
  given: (s₁ s₂ : Sphere P)
  statement: s₁.commonTangents s₂ = s₂.commonTangents s₁
  proof: Set.inter_comm _ _

中文:
引理 commonTangents_comm
  条件: (s₁ s₂ : 球面 P)
  结论: s₁.commonTangents s₂ = s₂.commonTangents s₁
  证明: Set.inter_comm _ _

Depends on / 依赖: Set.inter_comm, inter_comm
-/
lemma commonTangents_comm (s₁ s₂ : Sphere P) : s₁.commonTangents s₂ = s₂.commonTangents s₁ :=
  Set.inter_comm _ _

/--
Definition of `commonIntTangents` / `commonIntTangents` 的定义

English:
definition commonIntTangents
  signature: (s₁ s₂ : Sphere P)
  body: {as in s₁.commonTangents s₂ | exists p in as, Wbtw Real s₁.center p s₂.center}

中文:
定义 common整数Tangents
  签名: (s₁ s₂ : 球面 P)
  定义体: {as in s₁.commonTangents s₂ | exists p in as, Wbtw Real s₁.center p s₂.center}

Depends on / 依赖: center, commonTangents
-/
def commonIntTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P) :=
  {as in s₁.commonTangents s₂ | exists p in as, Wbtw Real s₁.center p s₂.center}

/--
Definition of `commonExtTangents` / `commonExtTangents` 的定义

English:
definition commonExtTangents
  signature: (s₁ s₂ : Sphere P)
  body: {as in s₁.commonTangents s₂ | forall p in as, ¬Sbtw Real s₁.center p s₂.center}

中文:
定义 commonExtTangents
  签名: (s₁ s₂ : 球面 P)
  定义体: {as in s₁.commonTangents s₂ | forall p in as, ¬Sbtw Real s₁.center p s₂.center}

Depends on / 依赖: center, commonTangents
-/
def commonExtTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace Real P) :=
  {as in s₁.commonTangents s₂ | forall p in as, ¬Sbtw Real s₁.center p s₂.center}

/--
lemma `mem_commonIntTangents_iff` / 引理 `mem_commonIntTangents_iff`

English:
lemma mem_commonIntTangents_iff
  given: {as : AffineSubspace Real P} {s₁ s₂ : Sphere P}
  proof: Iff.rfl

中文:
引理 mem_common整数Tangents_iff
  条件: {as : 仿射子空间 实数 P} {s₁ s₂ : 球面 P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_commonIntTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} :
    as in s₁.commonIntTangents s₂ ↔
      as in s₁.commonTangents s₂ ∧ exists p in as, Wbtw Real s₁.center p s₂.center :=
  Iff.rfl

/--
lemma `mem_commonExtTangents_iff` / 引理 `mem_commonExtTangents_iff`

English:
lemma mem_commonExtTangents_iff
  given: {as : AffineSubspace Real P} {s₁ s₂ : Sphere P}
  proof: Iff.rfl

中文:
引理 mem_commonExtTangents_iff
  条件: {as : 仿射子空间 实数 P} {s₁ s₂ : 球面 P}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_commonExtTangents_iff {as : AffineSubspace Real P} {s₁ s₂ : Sphere P} :
    as in s₁.commonExtTangents s₂ ↔
      as in s₁.commonTangents s₂ ∧ forall p in as, ¬Sbtw Real s₁.center p s₂.center :=
  Iff.rfl

/--
lemma `commonIntTangents_union_commonExtTangents` / 引理 `commonIntTangents_union_commonExtTangents`

English:
lemma commonIntTangents_union_commonExtTangents
  given: (s₁ s₂ : Sphere P)
  proof: by
  ext as
  rw [Set.mem_union]; rw [mem_commonIntTangents_iff]; rw [mem_commonExtTangents_iff]; rw [← and_or_left]; rw [and_iff_left_iff_imp]
  rintro -
  by_cases! h : exists p in as, Wbtw Real s₁.center p s₂.center
  · exact .inl h
  · refine .inr ?_
    rintro p hp
    exact mt Sbtw.wbtw (h p h

中文:
引理 common整数Tangents_union_commonExtTangents
  条件: (s₁ s₂ : 球面 P)
  证明: by
  ext as
  rw [Set.mem_union]; rw [mem_commonIntTangents_iff]; rw [mem_commonExtTangents_iff]; rw [← and_or_left]; rw [and_iff_left_iff_imp]
  rintro -
  by_cases! h : exists p in as, Wbtw Real s₁.center p s₂.center
  · exact .inl h
  · refine .inr ?_
    rintro p hp
    exact mt Sbtw.wbtw (h p h
-/
@[simp] lemma commonIntTangents_union_commonExtTangents (s₁ s₂ : Sphere P) :
    s₁.commonIntTangents s₂ union s₁.commonExtTangents s₂ = s₁.commonTangents s₂ := by
  ext as
  rw [Set.mem_union]; rw [mem_commonIntTangents_iff]; rw [mem_commonExtTangents_iff]; rw [← and_or_left]; rw [and_iff_left_iff_imp]
  rintro -
  by_cases! h : exists p in as, Wbtw Real s₁.center p s₂.center
  · exact .inl h
  · refine .inr ?_
    rintro p hp
    exact mt Sbtw.wbtw (h p hp)

/--
Definition of `IsExtTangentAt` / `IsExtTangentAt` 的定义

English:
structure IsExtTangentAt
  parameters: (s₁ s₂ : Sphere P) (p : P)
  axioms and operations (3):
    - mem_left : p in s₁
    - mem_right : p in s₂
    - wbtw : Wbtw Real s₁.center p s₂.center

中文:
结构 是ExtTangentAt
  参数: (s₁ s₂ : 球面 P) (p : P)
  公理与运算 (3 个):
    - mem_left : p in s₁
    - mem_right : p in s₂
    - wbtw : Wbtw 实数 s₁.center p s₂.center
-/
structure IsExtTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p in s₁
  mem_right : p in s₂
  wbtw : Wbtw Real s₁.center p s₂.center

/--
lemma `IsExtTangentAt.symm` / 引理 `IsExtTangentAt.symm`

English:
lemma IsExtTangentAt.symm
  given: {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p)
  proof: h.mem_right
  mem_right := h.mem_left
  wbtw := h.wbtw.symm

中文:
引理 是ExtTangentAt.symm
  条件: {s₁ s₂ : 球面 P} {p : P} (h : s₁.是ExtTangentAt s₂ p)
  证明: h.mem_right
  mem_right := h.mem_left
  wbtw := h.wbtw.symm

Depends on / 依赖: h.mem_right, mem_right
-/
lemma IsExtTangentAt.symm {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₂.IsExtTangentAt s₁ p where
  mem_left := h.mem_right
  mem_right := h.mem_left
  wbtw := h.wbtw.symm

/--
lemma `isExtTangentAt_comm` / 引理 `isExtTangentAt_comm`

English:
lemma isExtTangentAt_comm
  given: {s₁ s₂ : Sphere P} {p : P}
  proof: ⟨IsExtTangentAt.symm, IsExtTangentAt.symm⟩

中文:
引理 isExtTangentAt_comm
  条件: {s₁ s₂ : 球面 P} {p : P}
  证明: ⟨IsExtTangentAt.symm, IsExtTangentAt.symm⟩

Depends on / 依赖: IsExtTangentAt, IsExtTangentAt.symm
-/
lemma isExtTangentAt_comm {s₁ s₂ : Sphere P} {p : P} :
    s₁.IsExtTangentAt s₂ p ↔ s₂.IsExtTangentAt s₁ p :=
  ⟨IsExtTangentAt.symm, IsExtTangentAt.symm⟩

/--
lemma `isExtTangentAt_center_iff` / 引理 `isExtTangentAt_center_iff`

English:
lemma isExtTangentAt_center_iff
  given: {s₁ s₂ : Sphere P}
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

中文:
引理 isExtTangentAt_center_iff
  条件: {s₁ s₂ : 球面 P}
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

Depends on / 依赖: center_mem_iff
-/
lemma isExtTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsExtTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center in s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

/--
Definition of `IsIntTangentAt` / `IsIntTangentAt` 的定义

English:
structure IsIntTangentAt
  parameters: (s₁ s₂ : Sphere P) (p : P)
  axioms and operations (3):
    - mem_left : p in s₁
    - mem_right : p in s₂
    - wbtw : Wbtw Real s₂.center s₁.center p

中文:
结构 是整数TangentAt
  参数: (s₁ s₂ : 球面 P) (p : P)
  公理与运算 (3 个):
    - mem_left : p in s₁
    - mem_right : p in s₂
    - wbtw : Wbtw 实数 s₂.center s₁.center p
-/
structure IsIntTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p in s₁
  mem_right : p in s₂
  wbtw : Wbtw Real s₂.center s₁.center p

/--
lemma `isIntTangentAt_center_iff` / 引理 `isIntTangentAt_center_iff`

English:
lemma isIntTangentAt_center_iff
  given: {s₁ s₂ : Sphere P}
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

中文:
引理 is整数TangentAt_center_iff
  条件: {s₁ s₂ : 球面 P}
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

Depends on / 依赖: center_mem_iff
-/
lemma isIntTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsIntTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center in s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

/--
lemma `isIntTangentAt_self_iff_mem` / 引理 `isIntTangentAt_self_iff_mem`

English:
lemma isIntTangentAt_self_iff_mem
  given: {s : Sphere P} {p : P}
  proof: ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, by simp⟩⟩

中文:
引理 is整数TangentAt_self_iff_mem
  条件: {s : 球面 P} {p : P}
  证明: ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, by simp⟩⟩
-/
@[simp] lemma isIntTangentAt_self_iff_mem {s : Sphere P} {p : P} :
    s.IsIntTangentAt s p ↔ p in s :=
  ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, by simp⟩⟩

/--
Definition of `IsExtTangent` / `IsExtTangent` 的定义

English:
definition IsExtTangent
  signature: (s₁ s₂ : Sphere P)
  body: exists p, s₁.IsExtTangentAt s₂ p

中文:
定义 IsExtTangent
  签名: (s₁ s₂ : 球面 P)
  定义体: exists p, s₁.IsExtTangentAt s₂ p

Depends on / 依赖: IsExtTangentAt
-/
def IsExtTangent (s₁ s₂ : Sphere P) : Prop :=
  exists p, s₁.IsExtTangentAt s₂ p

/--
lemma `IsExtTangent.symm` / 引理 `IsExtTangent.symm`

English:
lemma IsExtTangent.symm
  given: {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂)
  statement: s₂.IsExtTangent s₁
  proof: by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩

中文:
引理 IsExtTangent.symm
  条件: {s₁ s₂ : 球面 P} (h : s₁.IsExtTangent s₂)
  结论: s₂.IsExtTangent s₁
  证明: by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩

Depends on / 依赖: hp.symm
-/
lemma IsExtTangent.symm {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) : s₂.IsExtTangent s₁ := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩

/--
lemma `isExtTangent_comm` / 引理 `isExtTangent_comm`

English:
lemma isExtTangent_comm
  given: {s₁ s₂ : Sphere P}
  statement: s₁.IsExtTangent s₂ ↔ s₂.IsExtTangent s₁
  proof: ⟨IsExtTangent.symm, IsExtTangent.symm⟩

中文:
引理 isExtTangent_comm
  条件: {s₁ s₂ : 球面 P}
  结论: s₁.IsExtTangent s₂ ↔ s₂.IsExtTangent s₁
  证明: ⟨IsExtTangent.symm, IsExtTangent.symm⟩

Depends on / 依赖: IsExtTangent, IsExtTangent.symm
-/
lemma isExtTangent_comm {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔ s₂.IsExtTangent s₁ :=
  ⟨IsExtTangent.symm, IsExtTangent.symm⟩

/--
Definition of `IsIntTangent` / `IsIntTangent` 的定义

English:
definition IsIntTangent
  signature: (s₁ s₂ : Sphere P)
  body: exists p, s₁.IsIntTangentAt s₂ p

中文:
定义 Is整数Tangent
  签名: (s₁ s₂ : 球面 P)
  定义体: exists p, s₁.IsIntTangentAt s₂ p

Depends on / 依赖: IsIntTangentAt
-/
def IsIntTangent (s₁ s₂ : Sphere P) : Prop :=
  exists p, s₁.IsIntTangentAt s₂ p

/--
lemma `IsExtTangentAt.isExtTangent` / 引理 `IsExtTangentAt.isExtTangent`

English:
lemma IsExtTangentAt.isExtTangent
  given: {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p)
  proof: ⟨p, h⟩

中文:
引理 是ExtTangentAt.isExtTangent
  条件: {s₁ s₂ : 球面 P} {p : P} (h : s₁.是ExtTangentAt s₂ p)
  证明: ⟨p, h⟩
-/
lemma IsExtTangentAt.isExtTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₁.IsExtTangent s₂ :=
  ⟨p, h⟩

/--
lemma `IsIntTangentAt.isIntTangent` / 引理 `IsIntTangentAt.isIntTangent`

English:
lemma IsIntTangentAt.isIntTangent
  given: {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsIntTangentAt s₂ p)
  proof: ⟨p, h⟩

中文:
引理 是整数TangentAt.is整数Tangent
  条件: {s₁ s₂ : 球面 P} {p : P} (h : s₁.是整数TangentAt s₂ p)
  证明: ⟨p, h⟩
-/
lemma IsIntTangentAt.isIntTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsIntTangentAt s₂ p) :
    s₁.IsIntTangent s₂ :=
  ⟨p, h⟩

/--
lemma `isIntTangent_self_iff` / 引理 `isIntTangent_self_iff`

English:
lemma isIntTangent_self_iff
  given: [Nontrivial V] {s : Sphere P}
  proof: by
  simp_rw [IsIntTangent, isIntTangentAt_self_iff_mem]
  rw [← nonempty_iff]
  simp [Set.Nonempty]

中文:
引理 is整数Tangent_self_iff
  条件: [非平凡 V] {s : 球面 P}
  证明: by
  simp_rw [IsIntTangent, isIntTangentAt_self_iff_mem]
  rw [← nonempty_iff]
  simp [Set.Nonempty]
-/
@[simp] lemma isIntTangent_self_iff [Nontrivial V] {s : Sphere P} :
    s.IsIntTangent s ↔ 0 <= s.radius := by
  simp_rw [IsIntTangent, isIntTangentAt_self_iff_mem]
  rw [← nonempty_iff]
  simp [Set.Nonempty]

/--
lemma `IsExtTangent.dist_center` / 引理 `IsExtTangent.dist_center`

English:
lemma IsExtTangent.dist_center
  given: {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂)
  proof: by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff] at h
  rw [← h]; rw [mem_sphere'.1 h₁]; rw [h₂]

中文:
引理 IsExtTangent.dist_center
  条件: {s₁ s₂ : 球面 P} (h : s₁.IsExtTangent s₂)
  证明: by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff] at h
  rw [← h]; rw [mem_sphere'.1 h₁]; rw [h₂]

Depends on / 依赖: dist_add_dist_eq_iff, mem_sphere
-/
lemma IsExtTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) :
    dist s₁.center s₂.center = s₁.radius + s₂.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff] at h
  rw [← h]; rw [mem_sphere'.1 h₁]; rw [h₂]

/--
lemma `IsIntTangent.dist_center` / 引理 `IsIntTangent.dist_center`

English:
lemma IsIntTangent.dist_center
  given: {s₁ s₂ : Sphere P} (h : s₁.IsIntTangent s₂)
  proof: by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff]; rw [mem_sphere'.1 h₁]; rw [mem_sphere'.1 h₂] at h
  simp [← h, dist_comm]

中文:
引理 Is整数Tangent.dist_center
  条件: {s₁ s₂ : 球面 P} (h : s₁.Is整数Tangent s₂)
  证明: by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff]; rw [mem_sphere'.1 h₁]; rw [mem_sphere'.1 h₂] at h
  simp [← h, dist_comm]

Depends on / 依赖: dist_add_dist_eq_iff, dist_comm, mem_sphere
-/
lemma IsIntTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsIntTangent s₂) :
    dist s₁.center s₂.center = s₂.radius - s₁.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff]; rw [mem_sphere'.1 h₁]; rw [mem_sphere'.1 h₂] at h
  simp [← h, dist_comm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isExtTangent_iff_dist_center` / 引理 `isExtTangent_iff_dist_center`

English:
lemma isExtTangent_iff_dist_center
  given: {s₁ s₂ : Sphere P}
  statement: s₁.IsExtTangent s₂ ↔
  proof: by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius + s₂.radius)), ?_⟩
    by_cases h0 : s₁.radius + s₂.radius = 0

中文:
引理 isExtTangent_iff_dist_center
  条件: {s₁ s₂ : 球面 P}
  结论: s₁.IsExtTangent s₂ ↔
  证明: by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius + s₂.radius)), ?_⟩
    by_cases h0 : s₁.radius + s₂.radius = 0

Depends on / 依赖: AffineMap, AffineMap.lineMap, AffineMap.lineMap_apply_zero, Real.norm_eq, center, dist_center, dist_lineMap_left, div_zero, h.dist_center, isExtTangentAt_center_iff, lineMap, lineMap_apply_zero, mem_sphere, norm_div, norm_eq, radius, radius_nonneg_of_mem
-/
lemma isExtTangent_iff_dist_center {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔
    dist s₁.center s₂.center = s₁.radius + s₂.radius ∧ 0 <= s₁.radius ∧ 0 <= s₂.radius := by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius + s₂.radius)), ?_⟩
    by_cases h0 : s₁.radius + s₂.radius = 0
    · simp only [h0, div_zero, AffineMap.lineMap_apply_zero, isExtTangentAt_center_iff, mem_sphere]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, abs_of_nonneg h₁,
          abs_of_nonneg (add_nonneg h₁ h₂)]
        field
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h]
        rw [one_sub_div h0]; rw [add_sub_cancel_left]; rw [abs_div]; rw [abs_of_nonneg h₂]; rw [abs_of_nonneg (add_nonneg h₁ h₂)]
        field
      · simp only [wbtw_lineMap_iff]
        refine .inr ⟨?_, ?_⟩
        · positivity
        · rw [div_le_one (by positivity)]
          linarith

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIntTangent_iff_dist_center` / 引理 `isIntTangent_iff_dist_center`

English:
lemma isIntTangent_iff_dist_center
  given: [Nontrivial V] {s₁ s₂ : Sphere P}
  statement: s₁.IsIntTangent s₂ ↔
  proof: by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    by_cases h0 : s₁.center = s₂.center
    · rw [h0, dist_self, eq_comm, sub_eq_zero, eq_comm] at h
      have hs : s₁ = s₂ := by
     

中文:
引理 is整数Tangent_iff_dist_center
  条件: [非平凡 V] {s₁ s₂ : 球面 P}
  结论: s₁.Is整数Tangent s₂ ↔
  证明: by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    by_cases h0 : s₁.center = s₂.center
    · rw [h0, dist_self, eq_comm, sub_eq_zero, eq_comm] at h
      have hs : s₁ = s₂ := by
     

Depends on / 依赖: abs_of_nonneg, center, dist_center, dist_comm, dist_nonneg, dist_self, eq_comm, h.dist_center, radius, radius_nonneg_of_mem, sub_eq_zero
-/
lemma isIntTangent_iff_dist_center [Nontrivial V] {s₁ s₂ : Sphere P} : s₁.IsIntTangent s₂ ↔
    dist s₁.center s₂.center = s₂.radius - s₁.radius ∧ 0 <= s₁.radius ∧ 0 <= s₂.radius := by
  refine ⟨fun h => ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    by_cases h0 : s₁.center = s₂.center
    · rw [h0, dist_self, eq_comm, sub_eq_zero, eq_comm] at h
      have hs : s₁ = s₂ := by
        ext <;> assumption
      simp [hs, h₂]
    · rw [dist_comm] at h
      have ha : |s₂.radius - s₁.radius| = s₂.radius - s₁.radius := by
        refine abs_of_nonneg ?_
        rw [← h]
        exact dist_nonneg
      have hr0 : s₂.radius - s₁.radius != 0 := by
        intro hr0
        rw [hr0]; rw [dist_eq_zero] at h
        exact h0 h.symm
      refine ⟨AffineMap.lineMap s₂.center s₁.center (s₂.radius / (s₂.radius - s₁.radius)),
              ?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h, one_sub_div hr0, abs_div,
          sub_sub_cancel_left, abs_neg, abs_of_nonneg h₁, ha]
        field
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, ha,
          abs_of_nonneg h₂]
        field
      · rw [wbtw_iff_left_eq_or_right_mem_image_Ici]
        simp only [Ne.symm h0, Set.mem_image, Set.mem_Ici, AffineMap.lineMap_eq_lineMap_iff,
          false_or, exists_eq_right]
        rw [one_le_div]
        · linarith
        · rw [← h]
          simp [Ne.symm h0]

end Sphere

end EuclideanGeometry
