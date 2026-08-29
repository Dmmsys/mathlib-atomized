/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Spheres

This file defines and proves basic results about spheres and cospherical sets of points in
Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.Sphere` bundles a `center` and a `radius`.

* `EuclideanGeometry.Sphere.IsDiameter` is the property of two points being the two endpoints
  of a diameter of a sphere.

* `EuclideanGeometry.Sphere.ofDiameter` constructs the sphere on a given diameter.

* `EuclideanGeometry.Cospherical` is the property of a set of points being equidistant from some
  point.

* `EuclideanGeometry.Concyclic` is the property of a set of points being cospherical and
  coplanar.

-/

@[expose] public section


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} (P : Type*)

open Module

/-- A `Sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext]
/--
Definition of `Sphere` / `Sphere` 的定义

English:
structure Sphere
  parameters: [MetricSpace P]
  axioms and operations (2):
    - center : P
    - radius : Real

中文:
结构 Sphere
  参数: [MetricSpace P]
  公理与运算 (2 个):
    - center : P
    - radius : 实数
-/
structure Sphere [MetricSpace P] where
  /-- center of this sphere -/
  center : P
  /-- radius of the sphere; not required to be positive -/
  radius : Real

variable {P}

section MetricSpace

variable [MetricSpace P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: P] : Nonempty (Sphere P)
  body: ⟨⟨Classical.arbitrary P, 0⟩⟩

中文:
实例 [Nonempty
  签名: P] : Nonempty (Sphere P)
  定义体: ⟨⟨Classical.arbitrary P, 0⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
instance [Nonempty P] : Nonempty (Sphere P) :=
  ⟨⟨Classical.arbitrary P, 0⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Sphere P) (Set P)
  body: ⟨fun s => Metric.sphere s.center s.radius⟩

中文:
实例 :
  签名: Coe (Sphere P) (Set P)
  定义体: ⟨fun s => Metric.sphere s.center s.radius⟩

Depends on / 依赖: Metric, Metric.sphere, center, radius, s.center, s.radius, sphere
-/
instance : Coe (Sphere P) (Set P) :=
  ⟨fun s => Metric.sphere s.center s.radius⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership P (Sphere P)
  body: ⟨fun s p => p in (s : Set P)⟩

中文:
实例 :
  签名: Membership P (Sphere P)
  定义体: ⟨fun s p => p in (s : Set P)⟩
-/
instance : Membership P (Sphere P) :=
  ⟨fun s p => p in (s : Set P)⟩

/--
theorem `Sphere.mk_center` / 定理 `Sphere.mk_center`

English:
theorem Sphere.mk_center
  given: (c : P) (r : Real)
  statement: (⟨c, r⟩ : Sphere P).center = c
  proof: rfl

中文:
定理 Sphere.mk_center
  条件: (c : P) (r : 实数)
  结论: (⟨c, r⟩ : Sphere P).center = c
  证明: rfl
-/
theorem Sphere.mk_center (c : P) (r : Real) : (⟨c, r⟩ : Sphere P).center = c :=
  rfl

/--
theorem `Sphere.mk_radius` / 定理 `Sphere.mk_radius`

English:
theorem Sphere.mk_radius
  given: (c : P) (r : Real)
  statement: (⟨c, r⟩ : Sphere P).radius = r
  proof: rfl

@[simp]

中文:
定理 Sphere.mk_radius
  条件: (c : P) (r : 实数)
  结论: (⟨c, r⟩ : Sphere P).radius = r
  证明: rfl

@[simp]
-/
theorem Sphere.mk_radius (c : P) (r : Real) : (⟨c, r⟩ : Sphere P).radius = r :=
  rfl

@[simp]
/--
theorem `Sphere.mk_center_radius` / 定理 `Sphere.mk_center_radius`

English:
theorem Sphere.mk_center_radius
  given: (s : Sphere P)
  statement: (⟨s.center, s.radius⟩ : Sphere P) = s
  proof: by
  ext <;> rfl

@[simp]

中文:
定理 Sphere.mk_center_radius
  条件: (s : Sphere P)
  结论: (⟨s.center, s.radius⟩ : Sphere P) = s
  证明: by
  ext <;> rfl

@[simp]
-/
theorem Sphere.mk_center_radius (s : Sphere P) : (⟨s.center, s.radius⟩ : Sphere P) = s := by
  ext <;> rfl

@[simp]
/--
theorem `Sphere.coe_mk` / 定理 `Sphere.coe_mk`

English:
theorem Sphere.coe_mk
  given: (c : P) (r : Real)
  statement: ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r
  proof: rfl

中文:
定理 Sphere.coe_mk
  条件: (c : P) (r : 实数)
  结论: ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r
  证明: rfl
-/
theorem Sphere.coe_mk (c : P) (r : Real) : ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r :=
  rfl

-- simp-normal form is `Sphere.mem_coe'`
/--
theorem `Sphere.mem_coe` / 定理 `Sphere.mem_coe`

English:
theorem Sphere.mem_coe
  given: {p : P} {s : Sphere P}
  statement: p in (s : Set P) ↔ p in s
  proof: Iff.rfl

@[simp]

中文:
定理 Sphere.mem_coe
  条件: {p : P} {s : Sphere P}
  结论: p in (s : Set P) ↔ p in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem Sphere.mem_coe {p : P} {s : Sphere P} : p in (s : Set P) ↔ p in s :=
  Iff.rfl

@[simp]
/--
theorem `Sphere.mem_coe'` / 定理 `Sphere.mem_coe'`

English:
theorem Sphere.mem_coe'
  given: {p : P} {s : Sphere P}
  statement: dist p s.center = s.radius ↔ p in s
  proof: Iff.rfl

中文:
定理 Sphere.mem_coe'
  条件: {p : P} {s : Sphere P}
  结论: dist p s.center = s.radius ↔ p in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Sphere.mem_coe' {p : P} {s : Sphere P} : dist p s.center = s.radius ↔ p in s :=
  Iff.rfl

/--
theorem `mem_sphere` / 定理 `mem_sphere`

English:
theorem mem_sphere
  given: {p : P} {s : Sphere P}
  statement: p in s ↔ dist p s.center = s.radius
  proof: Iff.rfl

中文:
定理 mem_sphere
  条件: {p : P} {s : Sphere P}
  结论: p in s ↔ dist p s.center = s.radius
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_sphere {p : P} {s : Sphere P} : p in s ↔ dist p s.center = s.radius :=
  Iff.rfl

/--
theorem `mem_sphere'` / 定理 `mem_sphere'`

English:
theorem mem_sphere'
  given: {p : P} {s : Sphere P}
  statement: p in s ↔ dist s.center p = s.radius
  proof: Metric.mem_sphere'

中文:
定理 mem_sphere'
  条件: {p : P} {s : Sphere P}
  结论: p in s ↔ dist s.center p = s.radius
  证明: Metric.mem_sphere'

Depends on / 依赖: Metric, Metric.mem_sphere, mem_sphere
-/
theorem mem_sphere' {p : P} {s : Sphere P} : p in s ↔ dist s.center p = s.radius :=
  Metric.mem_sphere'

/--
theorem `subset_sphere` / 定理 `subset_sphere`

English:
theorem subset_sphere
  given: {ps : Set P} {s : Sphere P}
  statement: ps subseteq s ↔ forall p in ps, p in s
  proof: Iff.rfl

中文:
定理 subset_sphere
  条件: {ps : Set P} {s : Sphere P}
  结论: ps subseteq s ↔ 对任意 p in ps, p in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subset_sphere {ps : Set P} {s : Sphere P} : ps subseteq s ↔ forall p in ps, p in s :=
  Iff.rfl

/--
theorem `dist_of_mem_subset_sphere` / 定理 `dist_of_mem_subset_sphere`

English:
theorem dist_of_mem_subset_sphere
  statement: {p : P} {ps : Set P} {s : Sphere P} (hp : p in ps)
  proof: mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))

中文:
定理 dist_of_mem_subset_sphere
  结论: {p : P} {ps : Set P} {s : Sphere P} (hp : p in ps)
  证明: mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))

Depends on / 依赖: Set.mem_of_mem_of_subset, Sphere, Sphere.mem_coe, mem_coe, mem_of_mem_of_subset, mem_sphere
-/
theorem dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p in ps)
    (hps : ps subseteq (s : Set P)) : dist p s.center = s.radius :=
  mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))

/--
theorem `dist_of_mem_subset_mk_sphere` / 定理 `dist_of_mem_subset_mk_sphere`

English:
theorem dist_of_mem_subset_mk_sphere
  statement: {p c : P} {ps : Set P} {r : Real} (hp : p in ps)
  proof: dist_of_mem_subset_sphere hp hps

中文:
定理 dist_of_mem_subset_mk_sphere
  结论: {p c : P} {ps : Set P} {r : 实数} (hp : p in ps)
  证明: dist_of_mem_subset_sphere hp hps

Depends on / 依赖: dist_of_mem_subset_sphere
-/
theorem dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : Real} (hp : p in ps)
    (hps : ps subseteq ↑(⟨c, r⟩ : Sphere P)) : dist p c = r :=
  dist_of_mem_subset_sphere hp hps

/--
theorem `Sphere.ne_iff` / 定理 `Sphere.ne_iff`

English:
theorem Sphere.ne_iff
  given: {s₁ s₂ : Sphere P}
  proof: by
  rw [← not_and_or]; rw [← Sphere.ext_iff]

中文:
定理 Sphere.ne_iff
  条件: {s₁ s₂ : Sphere P}
  证明: by
  rw [← not_and_or]; rw [← Sphere.ext_iff]

Depends on / 依赖: Sphere, Sphere.ext_iff, ext_iff, not_and_or
-/
theorem Sphere.ne_iff {s₁ s₂ : Sphere P} :
    s₁ != s₂ ↔ s₁.center != s₂.center ∨ s₁.radius != s₂.radius := by
  rw [← not_and_or]; rw [← Sphere.ext_iff]

/--
theorem `Sphere.center_eq_iff_eq_of_mem` / 定理 `Sphere.center_eq_iff_eq_of_mem`

English:
theorem Sphere.center_eq_iff_eq_of_mem
  given: {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂)
  proof: by
  refine ⟨fun h => Sphere.ext h ?_, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁]; rw [← hs₂]; rw [h]

中文:
定理 Sphere.center_eq_iff_eq_of_mem
  条件: {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂)
  证明: by
  refine ⟨fun h => Sphere.ext h ?_, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁]; rw [← hs₂]; rw [h]

Depends on / 依赖: Sphere, Sphere.ext, mem_sphere
-/
theorem Sphere.center_eq_iff_eq_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂) :
    s₁.center = s₂.center ↔ s₁ = s₂ := by
  refine ⟨fun h => Sphere.ext h ?_, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁]; rw [← hs₂]; rw [h]

/--
theorem `Sphere.center_ne_iff_ne_of_mem` / 定理 `Sphere.center_ne_iff_ne_of_mem`

English:
theorem Sphere.center_ne_iff_ne_of_mem
  given: {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂)
  proof: (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not

中文:
定理 Sphere.center_ne_iff_ne_of_mem
  条件: {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂)
  证明: (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not

Depends on / 依赖: Sphere, Sphere.center_eq_iff_eq_of_mem, center_eq_iff_eq_of_mem
-/
theorem Sphere.center_ne_iff_ne_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p in s₁) (hs₂ : p in s₂) :
    s₁.center != s₂.center ↔ s₁ != s₂ :=
  (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not

/--
theorem `dist_center_eq_dist_center_of_mem_sphere` / 定理 `dist_center_eq_dist_center_of_mem_sphere`

English:
theorem dist_center_eq_dist_center_of_mem_sphere
  statement: {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
  proof: by
  rw [mem_sphere.1 hp₁]; rw [mem_sphere.1 hp₂]

中文:
定理 dist_center_eq_dist_center_of_mem_sphere
  结论: {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
  证明: by
  rw [mem_sphere.1 hp₁]; rw [mem_sphere.1 hp₂]

Depends on / 依赖: mem_sphere
-/
theorem dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) : dist p₁ s.center = dist p₂ s.center := by
  rw [mem_sphere.1 hp₁]; rw [mem_sphere.1 hp₂]

/--
theorem `dist_center_eq_dist_center_of_mem_sphere'` / 定理 `dist_center_eq_dist_center_of_mem_sphere'`

English:
theorem dist_center_eq_dist_center_of_mem_sphere'
  statement: {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
  proof: by
  rw [mem_sphere'.1 hp₁]; rw [mem_sphere'.1 hp₂]

中文:
定理 dist_center_eq_dist_center_of_mem_sphere'
  结论: {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
  证明: by
  rw [mem_sphere'.1 hp₁]; rw [mem_sphere'.1 hp₂]

Depends on / 依赖: mem_sphere
-/
theorem dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) : dist s.center p₁ = dist s.center p₂ := by
  rw [mem_sphere'.1 hp₁]; rw [mem_sphere'.1 hp₂]

/--
lemma `Sphere.radius_nonneg_of_mem` / 引理 `Sphere.radius_nonneg_of_mem`

English:
lemma Sphere.radius_nonneg_of_mem
  given: {s : Sphere P} {p : P} (h : p in s)
  statement: 0 <= s.radius
  proof: Metric.nonneg_of_mem_sphere h

中文:
引理 Sphere.radius_nonneg_of_mem
  条件: {s : Sphere P} {p : P} (h : p in s)
  结论: 0 <= s.radius
  证明: Metric.nonneg_of_mem_sphere h

Depends on / 依赖: Metric, Metric.nonneg_of_mem_sphere, nonneg_of_mem_sphere
-/
lemma Sphere.radius_nonneg_of_mem {s : Sphere P} {p : P} (h : p in s) : 0 <= s.radius :=
  Metric.nonneg_of_mem_sphere h

/--
lemma `Sphere.center_mem_iff` / 引理 `Sphere.center_mem_iff`

English:
lemma Sphere.center_mem_iff
  given: {s : Sphere P}
  statement: s.center in s ↔ s.radius = 0
  proof: by
  simp [mem_sphere, eq_comm]

中文:
引理 Sphere.center_mem_iff
  条件: {s : Sphere P}
  结论: s.center in s ↔ s.radius = 0
  证明: by
  simp [mem_sphere, eq_comm]
-/
@[simp] lemma Sphere.center_mem_iff {s : Sphere P} : s.center in s ↔ s.radius = 0 := by
  simp [mem_sphere, eq_comm]

/--
lemma `Sphere.ne_center_of_mem_of_mem_of_ne` / 引理 `Sphere.ne_center_of_mem_of_mem_of_ne`

English:
lemma Sphere.ne_center_of_mem_of_mem_of_ne
  statement: {s : Sphere P} {p q : P}
  proof: by
  grind [dist_eq_zero, mem_sphere']

中文:
引理 Sphere.ne_center_of_mem_of_mem_of_ne
  结论: {s : Sphere P} {p q : P}
  证明: by
  grind [dist_eq_zero, mem_sphere']

Depends on / 依赖: dist_eq_zero, mem_sphere
-/
lemma Sphere.ne_center_of_mem_of_mem_of_ne {s : Sphere P} {p q : P}
    (hp : p in s) (hq : q in s) (hpq : p != q) : p != s.center := by
  grind [dist_eq_zero, mem_sphere']

/--
Definition of `Cospherical` / `Cospherical` 的定义

English:
definition Cospherical
  signature: (ps : Set P)
  body: exists (center : P) (radius : Real), forall p in ps, dist p center = radius

中文:
定义 Cospherical
  签名: (ps : Set P)
  定义体: exists (center : P) (radius : Real), forall p in ps, dist p center = radius

Depends on / 依赖: center, radius
-/
def Cospherical (ps : Set P) : Prop :=
  exists (center : P) (radius : Real), forall p in ps, dist p center = radius

/--
theorem `cospherical_def` / 定理 `cospherical_def`

English:
theorem cospherical_def
  given: (ps : Set P)
  proof: Iff.rfl

中文:
定理 cospherical_def
  条件: (ps : Set P)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ exists (center : P) (radius : Real), forall p in ps, dist p center = radius :=
  Iff.rfl

/--
theorem `cospherical_iff_exists_sphere` / 定理 `cospherical_iff_exists_sphere`

English:
theorem cospherical_iff_exists_sphere
  given: {ps : Set P}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩

中文:
定理 cospherical_iff_exists_sphere
  条件: {ps : Set P}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩

Depends on / 依赖: center, radius, s.center, s.radius
-/
theorem cospherical_iff_exists_sphere {ps : Set P} :
    Cospherical ps ↔ exists s : Sphere P, ps subseteq (s : Set P) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩

/--
theorem `Sphere.cospherical` / 定理 `Sphere.cospherical`

English:
theorem Sphere.cospherical
  given: (s : Sphere P)
  statement: Cospherical (s : Set P)
  proof: cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩

中文:
定理 Sphere.cospherical
  条件: (s : Sphere P)
  结论: Cospherical (s : Set P)
  证明: cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩

Depends on / 依赖: Set.Subset.rfl, Subset, cospherical_iff_exists_sphere
-/
theorem Sphere.cospherical (s : Sphere P) : Cospherical (s : Set P) :=
  cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩

/--
theorem `Cospherical.subset` / 定理 `Cospherical.subset`

English:
theorem Cospherical.subset
  given: {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (hc : Cospherical ps₂)
  proof: by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩

中文:
定理 Cospherical.subset
  条件: {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (hc : Cospherical ps₂)
  证明: by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩
-/
theorem Cospherical.subset {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (hc : Cospherical ps₂) :
    Cospherical ps₁ := by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩

/--
theorem `cospherical_empty` / 定理 `cospherical_empty`

English:
theorem cospherical_empty
  given: [Nonempty P]
  statement: Cospherical (∅ : Set P)
  proof: let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun _ => False.elim⟩

中文:
定理 cospherical_empty
  条件: [Nonempty P]
  结论: Cospherical (∅ : Set P)
  证明: let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun _ => False.elim⟩

Depends on / 依赖: False.elim, Nonempty
-/
theorem cospherical_empty [Nonempty P] : Cospherical (∅ : Set P) :=
  let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun _ => False.elim⟩

/--
theorem `cospherical_singleton` / 定理 `cospherical_singleton`

English:
theorem cospherical_singleton
  given: (p : P)
  statement: Cospherical ({p} : Set P)
  proof: by
  use p
  simp

中文:
定理 cospherical_singleton
  条件: (p : P)
  结论: Cospherical ({p} : Set P)
  证明: by
  use p
  simp
-/
theorem cospherical_singleton (p : P) : Cospherical ({p} : Set P) := by
  use p
  simp

/--
theorem `_root_.Isometry.cospherical` / 定理 `_root_.Isometry.cospherical`

English:
theorem _root_.Isometry.cospherical
  statement: {E F : Type*} [MetricSpace E] [MetricSpace F] {f : E -> F}
  proof: by
  rcases hps with ⟨c, r, hc⟩
  refine ⟨f c, r, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [hf.dist_eq]; rw [hc p hp]

中文:
定理 _root_.Isometry.cospherical
  结论: {E F : 类型} [MetricSpace E] [MetricSpace F] {f : E -> F}
  证明: by
  rcases hps with ⟨c, r, hc⟩
  refine ⟨f c, r, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [hf.dist_eq]; rw [hc p hp]

Depends on / 依赖: dist_eq, hf.dist_eq
-/
theorem _root_.Isometry.cospherical {E F : Type*} [MetricSpace E] [MetricSpace F] {f : E -> F}
    (hf : Isometry f) {ps : Set E} (hps : Cospherical ps) : Cospherical (f '' ps) := by
  rcases hps with ⟨c, r, hc⟩
  refine ⟨f c, r, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [hf.dist_eq]; rw [hc p hp]

end MetricSpace

section NormedSpace

variable [NormedAddCommGroup V] [NormedSpace Real V] [MetricSpace P] [NormedAddTorsor V P]

/--
theorem `Cospherical.inclusion` / 定理 `Cospherical.inclusion`

English:
theorem Cospherical.inclusion
  statement: {S₁ S₂ : AffineSubspace Real P} [Nonempty S₁] {ps : Set S₁}
  proof: by
  refine Isometry.cospherical ?_ hps
  exact S₁.subtypeₐᵢ.isometry

中文:
定理 Cospherical.inclusion
  结论: {S₁ S₂ : AffineSubspace 实数 P} [Nonempty S₁] {ps : Set S₁}
  证明: by
  refine Isometry.cospherical ?_ hps
  exact S₁.subtypeₐᵢ.isometry

Depends on / 依赖: Isometry, Isometry.cospherical, cospherical, isometry
-/
theorem Cospherical.inclusion {S₁ S₂ : AffineSubspace Real P} [Nonempty S₁] {ps : Set S₁}
    (hps : Cospherical ps) (hS : S₁ <= S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) := by
  refine Isometry.cospherical ?_ hps
  exact S₁.subtypeₐᵢ.isometry

/--
theorem `Cospherical.subtype_val` / 定理 `Cospherical.subtype_val`

English:
theorem Cospherical.subtype_val
  statement: {S : AffineSubspace Real P} [Nonempty S] {ps : Set S}
  proof: Isometry.cospherical S.subtypeₐᵢ.isometry hps

omit [NormedSpace Real V] in

中文:
定理 Cospherical.subtype_val
  结论: {S : AffineSubspace 实数 P} [Nonempty S] {ps : Set S}
  证明: Isometry.cospherical S.subtypeₐᵢ.isometry hps

omit [NormedSpace Real V] in

Depends on / 依赖: Isometry, Isometry.cospherical, S.subtype, cospherical, isometry
-/
theorem Cospherical.subtype_val {S : AffineSubspace Real P} [Nonempty S] {ps : Set S}
    (hps : Cospherical ps) : Cospherical (Subtype.val '' ps) :=
  Isometry.cospherical S.subtypeₐᵢ.isometry hps

omit [NormedSpace Real V] in
/--
theorem `norm_vsub_center_eq_radius` / 定理 `norm_vsub_center_eq_radius`

English:
theorem norm_vsub_center_eq_radius
  given: {s : Sphere P} {p : P} (hp : p in s)
  proof: by
  rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp

中文:
定理 norm_vsub_center_eq_radius
  条件: {s : Sphere P} {p : P} (hp : p in s)
  证明: by
  rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp

Depends on / 依赖: dist_eq_norm_vsub, mem_sphere
-/
theorem norm_vsub_center_eq_radius {s : Sphere P} {p : P} (hp : p in s) :
    ‖p -ᵥ s.center‖ = s.radius := by
  rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp

/--
lemma `Sphere.nonempty_iff` / 引理 `Sphere.nonempty_iff`

English:
lemma Sphere.nonempty_iff
  given: [Nontrivial V] {s : Sphere P}
  statement: (s : Set P).Nonempty ↔ 0 <= s.radius
  proof: by
  refine ⟨fun ⟨p, hp⟩ => radius_nonneg_of_mem hp, fun h => ?_⟩
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : V)) (r := s.radius)).2 h
  refine ⟨v +ᵥ s.center, ?_⟩
  simpa [mem_sphere] using hv

include V in

中文:
引理 Sphere.nonempty_iff
  条件: [Nontrivial V] {s : Sphere P}
  结论: (s : Set P).Nonempty ↔ 0 <= s.radius
  证明: by
  refine ⟨fun ⟨p, hp⟩ => radius_nonneg_of_mem hp, fun h => ?_⟩
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : V)) (r := s.radius)).2 h
  refine ⟨v +ᵥ s.center, ?_⟩
  simpa [mem_sphere] using hv

include V in

Depends on / 依赖: NormedSpace, NormedSpace.sphere_nonempty, center, mem_sphere, radius, radius_nonneg_of_mem, s.center, s.radius, sphere_nonempty
-/
lemma Sphere.nonempty_iff [Nontrivial V] {s : Sphere P} : (s : Set P).Nonempty ↔ 0 <= s.radius := by
  refine ⟨fun ⟨p, hp⟩ => radius_nonneg_of_mem hp, fun h => ?_⟩
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : V)) (r := s.radius)).2 h
  refine ⟨v +ᵥ s.center, ?_⟩
  simpa [mem_sphere] using hv

include V in
/--
theorem `cospherical_pair` / 定理 `cospherical_pair`

English:
theorem cospherical_pair
  given: (p₁ p₂ : P)
  statement: Cospherical ({p₁, p₂} : Set P)
  proof: ⟨midpoint Real p₁ p₂, ‖(2 : Real)‖⁻¹ * dist p₁ p₂, by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left (𝕜 := Real)]
    · rw [dist_comm, dist_midpoint_right (𝕜 := Real)]⟩

中文:
定理 cospherical_pair
  条件: (p₁ p₂ : P)
  结论: Cospherical ({p₁, p₂} : Set P)
  证明: ⟨midpoint Real p₁ p₂, ‖(2 : Real)‖⁻¹ * dist p₁ p₂, by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left (𝕜 := Real)]
    · rw [dist_comm, dist_midpoint_right (𝕜 := Real)]⟩

Depends on / 依赖: dist_comm, dist_midpoint_left, dist_midpoint_right, midpoint
-/
theorem cospherical_pair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) :=
  ⟨midpoint Real p₁ p₂, ‖(2 : Real)‖⁻¹ * dist p₁ p₂, by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left (𝕜 := Real)]
    · rw [dist_comm, dist_midpoint_right (𝕜 := Real)]⟩

/--
Definition of `Concyclic` / `Concyclic` 的定义

English:
structure Concyclic
  parameters: (ps : Set P)
  axioms and operations (2):
    - Cospherical : Cospherical ps
    - Coplanar : Coplanar Real ps

中文:
结构 Concyclic
  参数: (ps : Set P)
  公理与运算 (2 个):
    - Cospherical : Cospherical ps
    - Coplanar : Coplanar 实数 ps
-/
structure Concyclic (ps : Set P) : Prop where
  Cospherical : Cospherical ps
  Coplanar : Coplanar Real ps

/--
theorem `Concyclic.subset` / 定理 `Concyclic.subset`

English:
theorem Concyclic.subset
  given: {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (h : Concyclic ps₂)
  statement: Concyclic ps₁
  proof: ⟨h.1.subset hs, h.2.subset hs⟩

中文:
定理 Concyclic.subset
  条件: {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (h : Concyclic ps₂)
  结论: Concyclic ps₁
  证明: ⟨h.1.subset hs, h.2.subset hs⟩

Depends on / 依赖: subset
-/
theorem Concyclic.subset {ps₁ ps₂ : Set P} (hs : ps₁ subseteq ps₂) (h : Concyclic ps₂) : Concyclic ps₁ :=
  ⟨h.1.subset hs, h.2.subset hs⟩

/--
theorem `concyclic_empty` / 定理 `concyclic_empty`

English:
theorem concyclic_empty
  statement: Concyclic (∅ : Set P)
  proof: ⟨cospherical_empty, coplanar_empty Real P⟩

中文:
定理 concyclic_empty
  结论: Concyclic (∅ : Set P)
  证明: ⟨cospherical_empty, coplanar_empty Real P⟩

Depends on / 依赖: coplanar_empty, cospherical_empty
-/
theorem concyclic_empty : Concyclic (∅ : Set P) :=
  ⟨cospherical_empty, coplanar_empty Real P⟩

/--
theorem `concyclic_singleton` / 定理 `concyclic_singleton`

English:
theorem concyclic_singleton
  given: (p : P)
  statement: Concyclic ({p} : Set P)
  proof: ⟨cospherical_singleton p, coplanar_singleton Real p⟩

中文:
定理 concyclic_singleton
  条件: (p : P)
  结论: Concyclic ({p} : Set P)
  证明: ⟨cospherical_singleton p, coplanar_singleton Real p⟩

Depends on / 依赖: coplanar_singleton, cospherical_singleton
-/
theorem concyclic_singleton (p : P) : Concyclic ({p} : Set P) :=
  ⟨cospherical_singleton p, coplanar_singleton Real p⟩

/--
theorem `concyclic_pair` / 定理 `concyclic_pair`

English:
theorem concyclic_pair
  given: (p₁ p₂ : P)
  statement: Concyclic ({p₁, p₂} : Set P)
  proof: ⟨cospherical_pair p₁ p₂, coplanar_pair Real p₁ p₂⟩

中文:
定理 concyclic_pair
  条件: (p₁ p₂ : P)
  结论: Concyclic ({p₁, p₂} : Set P)
  证明: ⟨cospherical_pair p₁ p₂, coplanar_pair Real p₁ p₂⟩

Depends on / 依赖: coplanar_pair, cospherical_pair
-/
theorem concyclic_pair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P) :=
  ⟨cospherical_pair p₁ p₂, coplanar_pair Real p₁ p₂⟩

namespace Sphere

/--
Definition of `IsDiameter` / `IsDiameter` 的定义

English:
structure IsDiameter
  parameters: (s : Sphere P) (p₁ p₂ : P)
  axioms and operations (2):
    - left_mem : p₁ in s
    - midpoint_eq_center : midpoint Real p₁ p₂ = s.center

中文:
结构 IsDiameter
  参数: (s : Sphere P) (p₁ p₂ : P)
  公理与运算 (2 个):
    - left_mem : p₁ in s
    - midpoint_eq_center : midpoint 实数 p₁ p₂ = s.center
-/
structure IsDiameter (s : Sphere P) (p₁ p₂ : P) : Prop where
  left_mem : p₁ in s
  midpoint_eq_center : midpoint Real p₁ p₂ = s.center

variable {s : Sphere P} {p₁ p₂ p₃ : P}

/--
lemma `IsDiameter.right_mem` / 引理 `IsDiameter.right_mem`

English:
lemma IsDiameter.right_mem
  given: (h : s.IsDiameter p₁ p₂)
  statement: p₂ in s
  proof: by
  rw [mem_sphere]; rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint_eq_dist_right_midpoint]

中文:
引理 IsDiameter.right_mem
  条件: (h : s.IsDiameter p₁ p₂)
  结论: p₂ in s
  证明: by
  rw [mem_sphere]; rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint_eq_dist_right_midpoint]

Depends on / 依赖: dist_left_midpoint_eq_dist_right_midpoint, h.left_mem, h.midpoint_eq_center, left_mem, mem_sphere, midpoint_eq_center
-/
lemma IsDiameter.right_mem (h : s.IsDiameter p₁ p₂) : p₂ in s := by
  rw [mem_sphere]; rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint_eq_dist_right_midpoint]

/--
lemma `IsDiameter.symm` / 引理 `IsDiameter.symm`

English:
lemma IsDiameter.symm
  given: (h : s.IsDiameter p₁ p₂)
  statement: s.IsDiameter p₂ p₁
  proof: ⟨h.right_mem, midpoint_comm (R := Real) p₁ p₂ ▸ h.midpoint_eq_center⟩

中文:
引理 IsDiameter.symm
  条件: (h : s.IsDiameter p₁ p₂)
  结论: s.IsDiameter p₂ p₁
  证明: ⟨h.right_mem, midpoint_comm (R := Real) p₁ p₂ ▸ h.midpoint_eq_center⟩
-/
protected lemma IsDiameter.symm (h : s.IsDiameter p₁ p₂) : s.IsDiameter p₂ p₁ :=
  ⟨h.right_mem, midpoint_comm (R := Real) p₁ p₂ ▸ h.midpoint_eq_center⟩

/--
lemma `isDiameter_comm` / 引理 `isDiameter_comm`

English:
lemma isDiameter_comm
  statement: s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁
  proof: ⟨IsDiameter.symm, IsDiameter.symm⟩

中文:
引理 isDiameter_comm
  结论: s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁
  证明: ⟨IsDiameter.symm, IsDiameter.symm⟩

Depends on / 依赖: IsDiameter, IsDiameter.symm
-/
lemma isDiameter_comm : s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁ :=
  ⟨IsDiameter.symm, IsDiameter.symm⟩

/--
lemma `isDiameter_iff_left_mem_and_midpoint_eq_center` / 引理 `isDiameter_iff_left_mem_and_midpoint_eq_center`

English:
lemma isDiameter_iff_left_mem_and_midpoint_eq_center
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
引理 isDiameter_iff_left_mem_and_midpoint_eq_center
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
lemma isDiameter_iff_left_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ midpoint Real p₁ p₂ = s.center :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/--
lemma `isDiameter_iff_right_mem_and_midpoint_eq_center` / 引理 `isDiameter_iff_right_mem_and_midpoint_eq_center`

English:
lemma isDiameter_iff_right_mem_and_midpoint_eq_center
  proof: ⟨fun h => ⟨h.right_mem, h.2⟩, fun h => IsDiameter.symm ⟨h.1, midpoint_comm (R := Real) p₁ p₂ ▸ h.2⟩⟩

中文:
引理 isDiameter_iff_right_mem_and_midpoint_eq_center
  证明: ⟨fun h => ⟨h.right_mem, h.2⟩, fun h => IsDiameter.symm ⟨h.1, midpoint_comm (R := Real) p₁ p₂ ▸ h.2⟩⟩

Depends on / 依赖: IsDiameter, IsDiameter.symm, h.right_mem, midpoint_comm, right_mem
-/
lemma isDiameter_iff_right_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₂ in s ∧ midpoint Real p₁ p₂ = s.center :=
  ⟨fun h => ⟨h.right_mem, h.2⟩, fun h => IsDiameter.symm ⟨h.1, midpoint_comm (R := Real) p₁ p₂ ▸ h.2⟩⟩

/--
lemma `IsDiameter.pointReflection_center_left` / 引理 `IsDiameter.pointReflection_center_left`

English:
lemma IsDiameter.pointReflection_center_left
  given: (h : s.IsDiameter p₁ p₂)
  proof: by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_left]

中文:
引理 IsDiameter.pointReflection_center_left
  条件: (h : s.IsDiameter p₁ p₂)
  证明: by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_left]

Depends on / 依赖: Equiv.pointReflection_midpoint_left, h.midpoint_eq_center, midpoint_eq_center, pointReflection_midpoint_left
-/
lemma IsDiameter.pointReflection_center_left (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₁ = p₂ := by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_left]

/--
lemma `IsDiameter.pointReflection_center_right` / 引理 `IsDiameter.pointReflection_center_right`

English:
lemma IsDiameter.pointReflection_center_right
  given: (h : s.IsDiameter p₁ p₂)
  proof: by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_right]

中文:
引理 IsDiameter.pointReflection_center_right
  条件: (h : s.IsDiameter p₁ p₂)
  证明: by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_right]

Depends on / 依赖: Equiv.pointReflection_midpoint_right, h.midpoint_eq_center, midpoint_eq_center, pointReflection_midpoint_right
-/
lemma IsDiameter.pointReflection_center_right (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₂ = p₁ := by
  rw [← h.midpoint_eq_center]; rw [Equiv.pointReflection_midpoint_right]

/--
lemma `isDiameter_iff_left_mem_and_pointReflection_center_left` / 引理 `isDiameter_iff_left_mem_and_pointReflection_center_left`

English:
lemma isDiameter_iff_left_mem_and_pointReflection_center_left
  proof: ⟨fun h => ⟨h.1, h.pointReflection_center_left⟩, fun h => ⟨h.1, by simp [← h.2]⟩⟩

中文:
引理 isDiameter_iff_left_mem_and_pointReflection_center_left
  证明: ⟨fun h => ⟨h.1, h.pointReflection_center_left⟩, fun h => ⟨h.1, by simp [← h.2]⟩⟩

Depends on / 依赖: h.pointReflection_center_left, pointReflection_center_left
-/
lemma isDiameter_iff_left_mem_and_pointReflection_center_left :
    s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ Equiv.pointReflection s.center p₁ = p₂ :=
  ⟨fun h => ⟨h.1, h.pointReflection_center_left⟩, fun h => ⟨h.1, by simp [← h.2]⟩⟩

/--
lemma `isDiameter_iff_right_mem_and_pointReflection_center_right` / 引理 `isDiameter_iff_right_mem_and_pointReflection_center_right`

English:
lemma isDiameter_iff_right_mem_and_pointReflection_center_right
  proof: by
  rw [isDiameter_comm]; rw [isDiameter_iff_left_mem_and_pointReflection_center_left]

中文:
引理 isDiameter_iff_right_mem_and_pointReflection_center_right
  证明: by
  rw [isDiameter_comm]; rw [isDiameter_iff_left_mem_and_pointReflection_center_left]

Depends on / 依赖: isDiameter_comm, isDiameter_iff_left_mem_and_pointReflection_center_left
-/
lemma isDiameter_iff_right_mem_and_pointReflection_center_right :
    s.IsDiameter p₁ p₂ ↔ p₂ in s ∧ Equiv.pointReflection s.center p₂ = p₁ := by
  rw [isDiameter_comm]; rw [isDiameter_iff_left_mem_and_pointReflection_center_left]

/--
lemma `IsDiameter.right_eq_of_isDiameter` / 引理 `IsDiameter.right_eq_of_isDiameter`

English:
lemma IsDiameter.right_eq_of_isDiameter
  given: (h₁₂ : s.IsDiameter p₁ p₂) (h₁₃ : s.IsDiameter p₁ p₃)
  proof: by
  rw [← h₁₂.pointReflection_center_left]; rw [← h₁₃.pointReflection_center_left]

中文:
引理 IsDiameter.right_eq_of_isDiameter
  条件: (h₁₂ : s.IsDiameter p₁ p₂) (h₁₃ : s.IsDiameter p₁ p₃)
  证明: by
  rw [← h₁₂.pointReflection_center_left]; rw [← h₁₃.pointReflection_center_left]

Depends on / 依赖: pointReflection_center_left
-/
lemma IsDiameter.right_eq_of_isDiameter (h₁₂ : s.IsDiameter p₁ p₂) (h₁₃ : s.IsDiameter p₁ p₃) :
    p₂ = p₃ := by
  rw [← h₁₂.pointReflection_center_left]; rw [← h₁₃.pointReflection_center_left]

/--
lemma `IsDiameter.left_eq_of_isDiameter` / 引理 `IsDiameter.left_eq_of_isDiameter`

English:
lemma IsDiameter.left_eq_of_isDiameter
  given: (h₁₃ : s.IsDiameter p₁ p₃) (h₂₃ : s.IsDiameter p₂ p₃)
  proof: by
  rw [← h₁₃.pointReflection_center_right]; rw [← h₂₃.pointReflection_center_right]

中文:
引理 IsDiameter.left_eq_of_isDiameter
  条件: (h₁₃ : s.IsDiameter p₁ p₃) (h₂₃ : s.IsDiameter p₂ p₃)
  证明: by
  rw [← h₁₃.pointReflection_center_right]; rw [← h₂₃.pointReflection_center_right]

Depends on / 依赖: pointReflection_center_right
-/
lemma IsDiameter.left_eq_of_isDiameter (h₁₃ : s.IsDiameter p₁ p₃) (h₂₃ : s.IsDiameter p₂ p₃) :
    p₁ = p₂ := by
  rw [← h₁₃.pointReflection_center_right]; rw [← h₂₃.pointReflection_center_right]

/--
lemma `IsDiameter.dist_left_right` / 引理 `IsDiameter.dist_left_right`

English:
lemma IsDiameter.dist_left_right
  given: (h : s.IsDiameter p₁ p₂)
  statement: dist p₁ p₂ = 2 * s.radius
  proof: by
  rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint]
  simp

中文:
引理 IsDiameter.dist_left_right
  条件: (h : s.IsDiameter p₁ p₂)
  结论: dist p₁ p₂ = 2 * s.radius
  证明: by
  rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint]
  simp

Depends on / 依赖: dist_left_midpoint, h.left_mem, h.midpoint_eq_center, left_mem, mem_sphere, midpoint_eq_center
-/
lemma IsDiameter.dist_left_right (h : s.IsDiameter p₁ p₂) : dist p₁ p₂ = 2 * s.radius := by
  rw [← mem_sphere.1 h.left_mem]; rw [← h.midpoint_eq_center]; rw [dist_left_midpoint]
  simp

/--
lemma `IsDiameter.dist_left_right_div_two` / 引理 `IsDiameter.dist_left_right_div_two`

English:
lemma IsDiameter.dist_left_right_div_two
  given: (h : s.IsDiameter p₁ p₂)
  proof: by
  simp [h.dist_left_right]

中文:
引理 IsDiameter.dist_left_right_div_two
  条件: (h : s.IsDiameter p₁ p₂)
  证明: by
  simp [h.dist_left_right]

Depends on / 依赖: dist_left_right, h.dist_left_right
-/
lemma IsDiameter.dist_left_right_div_two (h : s.IsDiameter p₁ p₂) :
    (dist p₁ p₂) / 2 = s.radius := by
  simp [h.dist_left_right]

/--
lemma `IsDiameter.left_eq_right_iff` / 引理 `IsDiameter.left_eq_right_iff`

English:
lemma IsDiameter.left_eq_right_iff
  given: (h : s.IsDiameter p₁ p₂)
  statement: p₁ = p₂ ↔ s.radius = 0
  proof: by
  rw [← dist_eq_zero]; rw [h.dist_left_right]
  simp

中文:
引理 IsDiameter.left_eq_right_iff
  条件: (h : s.IsDiameter p₁ p₂)
  结论: p₁ = p₂ ↔ s.radius = 0
  证明: by
  rw [← dist_eq_zero]; rw [h.dist_left_right]
  simp

Depends on / 依赖: dist_eq_zero, dist_left_right, h.dist_left_right
-/
lemma IsDiameter.left_eq_right_iff (h : s.IsDiameter p₁ p₂) : p₁ = p₂ ↔ s.radius = 0 := by
  rw [← dist_eq_zero]; rw [h.dist_left_right]
  simp

/--
lemma `IsDiameter.left_ne_right_iff_radius_ne_zero` / 引理 `IsDiameter.left_ne_right_iff_radius_ne_zero`

English:
lemma IsDiameter.left_ne_right_iff_radius_ne_zero
  given: (h : s.IsDiameter p₁ p₂)
  proof: h.left_eq_right_iff.not

中文:
引理 IsDiameter.left_ne_right_iff_radius_ne_zero
  条件: (h : s.IsDiameter p₁ p₂)
  证明: h.left_eq_right_iff.not

Depends on / 依赖: h.left_eq_right_iff.not, left_eq_right_iff
-/
lemma IsDiameter.left_ne_right_iff_radius_ne_zero (h : s.IsDiameter p₁ p₂) :
    p₁ != p₂ ↔ s.radius != 0 :=
  h.left_eq_right_iff.not

/--
lemma `IsDiameter.left_ne_right_iff_radius_pos` / 引理 `IsDiameter.left_ne_right_iff_radius_pos`

English:
lemma IsDiameter.left_ne_right_iff_radius_pos
  given: (h : s.IsDiameter p₁ p₂)
  proof: by
  rw [h.left_ne_right_iff_radius_ne_zero]; rw [lt_iff_le_and_ne]
  simp [radius_nonneg_of_mem h.left_mem, eq_comm]

中文:
引理 IsDiameter.left_ne_right_iff_radius_pos
  条件: (h : s.IsDiameter p₁ p₂)
  证明: by
  rw [h.left_ne_right_iff_radius_ne_zero]; rw [lt_iff_le_and_ne]
  simp [radius_nonneg_of_mem h.left_mem, eq_comm]

Depends on / 依赖: eq_comm, h.left_mem, h.left_ne_right_iff_radius_ne_zero, left_mem, left_ne_right_iff_radius_ne_zero, lt_iff_le_and_ne, radius_nonneg_of_mem
-/
lemma IsDiameter.left_ne_right_iff_radius_pos (h : s.IsDiameter p₁ p₂) :
    p₁ != p₂ ↔ 0 < s.radius := by
  rw [h.left_ne_right_iff_radius_ne_zero]; rw [lt_iff_le_and_ne]
  simp [radius_nonneg_of_mem h.left_mem, eq_comm]

/--
lemma `IsDiameter.wbtw` / 引理 `IsDiameter.wbtw`

English:
lemma IsDiameter.wbtw
  given: (h : s.IsDiameter p₁ p₂)
  statement: Wbtw Real p₁ s.center p₂
  proof: by
  rw [← h.midpoint_eq_center]
  exact wbtw_midpoint _ _ _

中文:
引理 IsDiameter.wbtw
  条件: (h : s.IsDiameter p₁ p₂)
  结论: Wbtw 实数 p₁ s.center p₂
  证明: by
  rw [← h.midpoint_eq_center]
  exact wbtw_midpoint _ _ _
-/
protected lemma IsDiameter.wbtw (h : s.IsDiameter p₁ p₂) : Wbtw Real p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact wbtw_midpoint _ _ _

/--
lemma `IsDiameter.sbtw` / 引理 `IsDiameter.sbtw`

English:
lemma IsDiameter.sbtw
  given: (h : s.IsDiameter p₁ p₂) (hr : s.radius != 0)
  proof: by
  rw [← h.midpoint_eq_center]
  exact sbtw_midpoint_of_ne _ (h.left_ne_right_iff_radius_ne_zero.2 hr)

中文:
引理 IsDiameter.sbtw
  条件: (h : s.IsDiameter p₁ p₂) (hr : s.radius != 0)
  证明: by
  rw [← h.midpoint_eq_center]
  exact sbtw_midpoint_of_ne _ (h.left_ne_right_iff_radius_ne_zero.2 hr)
-/
protected lemma IsDiameter.sbtw (h : s.IsDiameter p₁ p₂) (hr : s.radius != 0) :
    Sbtw Real p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact sbtw_midpoint_of_ne _ (h.left_ne_right_iff_radius_ne_zero.2 hr)

/--
Definition of `ofDiameter` / `ofDiameter` 的定义

English:
definition ofDiameter
  signature: (p₁ p₂ : P)
  body: ⟨midpoint Real p₁ p₂, (dist p₁ p₂) / 2⟩

中文:
定义 ofDiameter
  签名: (p₁ p₂ : P)
  定义体: ⟨midpoint Real p₁ p₂, (dist p₁ p₂) / 2⟩
-/
protected def ofDiameter (p₁ p₂ : P) : Sphere P :=
  ⟨midpoint Real p₁ p₂, (dist p₁ p₂) / 2⟩

/--
lemma `isDiameter_ofDiameter` / 引理 `isDiameter_ofDiameter`

English:
lemma isDiameter_ofDiameter
  given: (p₁ p₂ : P)
  statement: (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂
  proof: ⟨by simp [Sphere.ofDiameter, mem_sphere, inv_mul_eq_div], rfl⟩

中文:
引理 isDiameter_ofDiameter
  条件: (p₁ p₂ : P)
  结论: (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂
  证明: ⟨by simp [Sphere.ofDiameter, mem_sphere, inv_mul_eq_div], rfl⟩

Depends on / 依赖: Sphere, Sphere.ofDiameter, inv_mul_eq_div, mem_sphere, ofDiameter
-/
lemma isDiameter_ofDiameter (p₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂ :=
  ⟨by simp [Sphere.ofDiameter, mem_sphere, inv_mul_eq_div], rfl⟩

/--
lemma `IsDiameter.ofDiameter_eq` / 引理 `IsDiameter.ofDiameter_eq`

English:
lemma IsDiameter.ofDiameter_eq
  given: (h : s.IsDiameter p₁ p₂)
  statement: .ofDiameter p₁ p₂ = s
  proof: by
  ext
  · simp [Sphere.ofDiameter, h.midpoint_eq_center]
  · simp [Sphere.ofDiameter, ← h.dist_left_right_div_two]

中文:
引理 IsDiameter.ofDiameter_eq
  条件: (h : s.IsDiameter p₁ p₂)
  结论: .ofDiameter p₁ p₂ = s
  证明: by
  ext
  · simp [Sphere.ofDiameter, h.midpoint_eq_center]
  · simp [Sphere.ofDiameter, ← h.dist_left_right_div_two]

Depends on / 依赖: Sphere, Sphere.ofDiameter, dist_left_right_div_two, h.dist_left_right_div_two, h.midpoint_eq_center, midpoint_eq_center, ofDiameter
-/
lemma IsDiameter.ofDiameter_eq (h : s.IsDiameter p₁ p₂) : .ofDiameter p₁ p₂ = s := by
  ext
  · simp [Sphere.ofDiameter, h.midpoint_eq_center]
  · simp [Sphere.ofDiameter, ← h.dist_left_right_div_two]

/--
lemma `isDiameter_iff_ofDiameter_eq` / 引理 `isDiameter_iff_ofDiameter_eq`

English:
lemma isDiameter_iff_ofDiameter_eq
  statement: s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s
  proof: ⟨IsDiameter.ofDiameter_eq, by rintro rfl; exact isDiameter_ofDiameter _ _⟩

中文:
引理 isDiameter_iff_ofDiameter_eq
  结论: s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s
  证明: ⟨IsDiameter.ofDiameter_eq, by rintro rfl; exact isDiameter_ofDiameter _ _⟩

Depends on / 依赖: IsDiameter, IsDiameter.ofDiameter_eq, isDiameter_ofDiameter, ofDiameter_eq
-/
lemma isDiameter_iff_ofDiameter_eq : s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s :=
  ⟨IsDiameter.ofDiameter_eq, by rintro rfl; exact isDiameter_ofDiameter _ _⟩

end Sphere

end NormedSpace

section EuclideanSpace

variable [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P] [NormedAddTorsor V P]

/-- A set of points in an affine subspace is cospherical if and only if its image in the ambient
space is cospherical. -/
@[simp]
/--
theorem `Cospherical.subtype_val_iff` / 定理 `Cospherical.subtype_val_iff`

English:
theorem Cospherical.subtype_val_iff
  statement: {S : AffineSubspace Real P} [Nonempty S]
  proof: by
  refine ⟨fun h => ?_, Cospherical.subtype_val⟩
  rcases ps.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact cospherical_empty
  · rcases h with ⟨c, r, hr⟩
    let c' : S := orthogonalProjection S c
    refine ⟨c', dist p₀ c', fun p hp => ?_⟩
    have hp_dist : dist (p : P) c = r := by grind
 

中文:
定理 Cospherical.subtype_val_iff
  结论: {S : AffineSubspace 实数 P} [Nonempty S]
  证明: by
  refine ⟨fun h => ?_, Cospherical.subtype_val⟩
  rcases ps.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact cospherical_empty
  · rcases h with ⟨c, r, hr⟩
    let c' : S := orthogonalProjection S c
    refine ⟨c', dist p₀ c', fun p hp => ?_⟩
    have hp_dist : dist (p : P) c = r := by grind
 

Depends on / 依赖: Cospherical, Cospherical.subtype_val, _dist.symm, cospherical_empty, dist_eq_iff_dist_orthogonalProjection_eq, eq_empty_or_nonempty, hp_dist, hp_dist.trans, orthogonalProjection, ps.eq_empty_or_nonempty, subtype_val
-/
theorem Cospherical.subtype_val_iff {S : AffineSubspace Real P} [Nonempty S]
    [S.direction.HasOrthogonalProjection] {ps : Set S} :
    Cospherical (Subtype.val '' ps) ↔ Cospherical ps := by
  refine ⟨fun h => ?_, Cospherical.subtype_val⟩
  rcases ps.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact cospherical_empty
  · rcases h with ⟨c, r, hr⟩
    let c' : S := orthogonalProjection S c
    refine ⟨c', dist p₀ c', fun p hp => ?_⟩
    have hp_dist : dist (p : P) c = r := by grind
    have hp₀_dist : dist (p₀ : P) c = r := by grind
    have hpp₀ : dist (p : P) (c : P) = dist (p₀ : P) (c : P) := hp_dist.trans hp₀_dist.symm
    exact (dist_eq_iff_dist_orthogonalProjection_eq (s := S) (p₃ := c) p.2 p₀.2).1 hpp₀

/--
theorem `Cospherical.inclusion_iff` / 定理 `Cospherical.inclusion_iff`

English:
theorem Cospherical.inclusion_iff
  statement: {S₁ S₂ : AffineSubspace Real P} [Nonempty S₁] {ps : Set S₁}
  proof: by
  have : Nonempty S₂ := by obtain ⟨p⟩ := ‹Nonempty S₁›; exact ⟨⟨p, hS p.property⟩⟩
  simp [(Cospherical.subtype_val_iff (S := S₂) (ps := AffineSubspace.inclusion hS '' ps)).symm,
    Set.image_image]

中文:
定理 Cospherical.inclusion_iff
  结论: {S₁ S₂ : AffineSubspace 实数 P} [Nonempty S₁] {ps : Set S₁}
  证明: by
  have : Nonempty S₂ := by obtain ⟨p⟩ := ‹Nonempty S₁›; exact ⟨⟨p, hS p.property⟩⟩
  simp [(Cospherical.subtype_val_iff (S := S₂) (ps := AffineSubspace.inclusion hS '' ps)).symm,
    Set.image_image]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Cospherical, Cospherical.subtype_val_iff, Nonempty, Set.image_image, image_image, inclusion, p.property, property, subtype_val_iff
-/
theorem Cospherical.inclusion_iff {S₁ S₂ : AffineSubspace Real P} [Nonempty S₁] {ps : Set S₁}
    [S₁.direction.HasOrthogonalProjection] [S₂.direction.HasOrthogonalProjection] (hS : S₁ <= S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) ↔ Cospherical ps := by
  have : Nonempty S₂ := by obtain ⟨p⟩ := ‹Nonempty S₁›; exact ⟨⟨p, hS p.property⟩⟩
  simp [(Cospherical.subtype_val_iff (S := S₂) (ps := AffineSubspace.inclusion hS '' ps)).symm,
    Set.image_image]

/--
theorem `Cospherical.affineIndependent` / 定理 `Cospherical.affineIndependent`

English:
theorem Cospherical.affineIndependent
  statement: {s : Set P} (hs : Cospherical s) {p : Fin 3 -> P}
  proof: by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_mem_range] at hv
  have hv0 : v != 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : 

中文:
定理 Cospherical.affineIndependent
  结论: {s : Set P} (hs : Cospherical s) {p : Fin 3 -> P}
  证明: by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_mem_range] at hv
  have hv0 : v != 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : 

Depends on / 依赖: Set.forall_mem_range, Set.mem_of_mem_of_subset, Set.mem_range_self, affineIndependent_iff_not_collinear, collinear_iff_of_mem, forall_mem_range, mem_of_mem_of_subset, mem_range_self
-/
theorem Cospherical.affineIndependent {s : Set P} (hs : Cospherical s) {p : Fin 3 -> P}
    (hps : Set.range p subseteq s) (hpi : Function.Injective p) : AffineIndependent Real p := by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_mem_range] at hv
  have hv0 : v != 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : Fin 3) != 0) (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : forall i, dist (f i • v +ᵥ p 0) c = r := by
    intro i
    rw [← hf]
    exact hs' i
  have hf0 : f 0 = 0 := by
    have hf0' := hf 0
    rw [eq_comm]; rw [← @vsub_eq_zero_iff_eq V]; rw [vadd_vsub]; rw [smul_eq_zero] at hf0'
    simpa [hv0] using hf0'
  have hfi : Function.Injective f := by
    intro i j h
    have hi := hf i
    rw [h]; rw [← hf j] at hi
    exact hpi hi
  simp_rw [← hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd
  have hfn0 : forall i, i != 0 -> f i != 0 := fun i => (hfi.ne_iff' hf0).2
  have hfn0' : forall i, i != 0 -> f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ := by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by rw [hfn0' 1 (by decide), hfn0' 2 (by decide)]
  exact (by decide : (1 : Fin 3) != 2) (hfi hf12)

/--
theorem `Cospherical.affineIndependent_of_mem_of_ne` / 定理 `Cospherical.affineIndependent_of_mem_of_ne`

English:
theorem Cospherical.affineIndependent_of_mem_of_ne
  statement: {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
  proof: by
  refine hs.affineIndependent ?_ ?_
  · simp [h₁, h₂, h₃, Set.insert_subset_iff]
  · simp only [Matrix.vecCons, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective, eq_iff_true_of_subsingleton]

中文:
定理 Cospherical.affineIndependent_of_mem_of_ne
  结论: {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
  证明: by
  refine hs.affineIndependent ?_ ?_
  · simp [h₁, h₂, h₃, Set.insert_subset_iff]
  · simp only [Matrix.vecCons, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective, eq_iff_true_of_subsingleton]

Depends on / 依赖: Fin.cons_injective_iff, Function, Function.Injective, Injective, Matrix, Matrix.vecCons, Set.insert_subset_iff, affineIndependent, cons_injective_iff, eq_iff_true_of_subsingleton, hs.affineIndependent, insert_subset_iff, vecCons
-/
theorem Cospherical.affineIndependent_of_mem_of_ne {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
    (h₁ : p₁ in s) (h₂ : p₂ in s) (h₃ : p₃ in s) (h₁₂ : p₁ != p₂) (h₁₃ : p₁ != p₃) (h₂₃ : p₂ != p₃) :
    AffineIndependent Real ![p₁, p₂, p₃] := by
  refine hs.affineIndependent ?_ ?_
  · simp [h₁, h₂, h₃, Set.insert_subset_iff]
  · simp only [Matrix.vecCons, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective, eq_iff_true_of_subsingleton]

/--
theorem `Cospherical.affineIndependent_of_ne` / 定理 `Cospherical.affineIndependent_of_ne`

English:
theorem Cospherical.affineIndependent_of_ne
  statement: {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
  proof: hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃

中文:
定理 Cospherical.affineIndependent_of_ne
  结论: {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
  证明: hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃

Depends on / 依赖: Set.mem_insert, Set.mem_insert_of_mem, Set.mem_singleton, affineIndependent_of_mem_of_ne, hs.affineIndependent_of_mem_of_ne, mem_insert, mem_insert_of_mem, mem_singleton
-/
theorem Cospherical.affineIndependent_of_ne {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
    (h₁₂ : p₁ != p₂) (h₁₃ : p₁ != p₃) (h₂₃ : p₂ != p₃) : AffineIndependent Real ![p₁, p₂, p₃] :=
  hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃

/--
theorem `inner_vsub_vsub_of_mem_sphere_of_mem_sphere` / 定理 `inner_vsub_vsub_of_mem_sphere_of_mem_sphere`

English:
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere
  statement: {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ in s₁)
  proof: inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

中文:
定理 inner_vsub_vsub_of_mem_sphere_of_mem_sphere
  结论: {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ in s₁)
  证明: inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

Depends on / 依赖: dist_center_eq_dist_center_of_mem_sphere, inner_vsub_vsub_of_dist_eq_of_dist_eq
-/
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ in s₁)
    (hp₂s₁ : p₂ in s₁) (hp₁s₂ : p₁ in s₂) (hp₂s₂ : p₂ in s₂) :
    ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

/--
theorem `Sphere.inner_vsub_center_midpoint_vsub` / 定理 `Sphere.inner_vsub_center_midpoint_vsub`

English:
theorem Sphere.inner_vsub_center_midpoint_vsub
  statement: {p₁ p₂ : P} {s : Sphere P}
  proof: inner_vsub_vsub_of_dist_eq_of_dist_eq
    (dist_left_midpoint_eq_dist_right_midpoint p₁ p₂)
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)

中文:
定理 Sphere.inner_vsub_center_midpoint_vsub
  结论: {p₁ p₂ : P} {s : Sphere P}
  证明: inner_vsub_vsub_of_dist_eq_of_dist_eq
    (dist_left_midpoint_eq_dist_right_midpoint p₁ p₂)
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)

Depends on / 依赖: dist_center_eq_dist_center_of_mem_sphere, dist_left_midpoint_eq_dist_right_midpoint, inner_vsub_vsub_of_dist_eq_of_dist_eq
-/
theorem Sphere.inner_vsub_center_midpoint_vsub {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) :
    ⟪s.center -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq
    (dist_left_midpoint_eq_dist_right_midpoint p₁ p₂)
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Sphere.dist_center_lt_radius_of_sbtw` / 定理 `Sphere.dist_center_lt_radius_of_sbtw`

English:
theorem Sphere.dist_center_lt_radius_of_sbtw
  statement: {p₁ p₂ p : P} {s : Sphere P}
  proof: by
  set o := s.center
  obtain ⟨⟨t, ⟨ht₀, ht₁⟩, hpt⟩, hne₁, hne₂⟩ := hp
have ht₀' : 0 < t := lt_of_le_of_ne ht₀ fun h => hne₁ by
    rw [← hpt]; rw [← h]; rw [AffineMap.lineMap_apply_zero]
have ht₁' : t < 1 := lt_of_le_of_ne ht₁ fun h => hne₂ by
    rw [← hpt]; rw [h]; rw [AffineMap.lineMap_apply_o

中文:
定理 Sphere.dist_center_lt_radius_of_sbtw
  结论: {p₁ p₂ p : P} {s : Sphere P}
  证明: by
  set o := s.center
  obtain ⟨⟨t, ⟨ht₀, ht₁⟩, hpt⟩, hne₁, hne₂⟩ := hp
have ht₀' : 0 < t := lt_of_le_of_ne ht₀ fun h => hne₁ by
    rw [← hpt]; rw [← h]; rw [AffineMap.lineMap_apply_zero]
have ht₁' : t < 1 := lt_of_le_of_ne ht₁ fun h => hne₂ by
    rw [← hpt]; rw [h]; rw [AffineMap.lineMap_apply_o

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, center, lineMap_apply_one, lineMap_apply_zero, lt_of_le_of_ne, norm_vsub_center_eq_radius, radius, s.center, s.radius
-/
theorem Sphere.dist_center_lt_radius_of_sbtw {p₁ p₂ p : P} {s : Sphere P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp : Sbtw Real p₁ p p₂) :
    dist s.center p < s.radius := by
  set o := s.center
  obtain ⟨⟨t, ⟨ht₀, ht₁⟩, hpt⟩, hne₁, hne₂⟩ := hp
have ht₀' : 0 < t := lt_of_le_of_ne ht₀ fun h => hne₁ by
    rw [← hpt]; rw [← h]; rw [AffineMap.lineMap_apply_zero]
have ht₁' : t < 1 := lt_of_le_of_ne ht₁ fun h => hne₂ by
    rw [← hpt]; rw [h]; rw [AffineMap.lineMap_apply_one]
  set u := p₁ -ᵥ o; set v := p₂ -ᵥ o
  have hu : ‖u‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hv : ‖v‖ = s.radius := norm_vsub_center_eq_radius hp₂
have huv : u != v := fun h => hne₁ by
    rw [← hpt]; rw [vsub_left_cancel h]; rw [AffineMap.lineMap_same]; rw [AffineMap.const_apply]
  have hpo : p -ᵥ o = (1 - t) • u + t • v := by
    rw [show p = (AffineMap.lineMap p₁ p₂) t from hpt.symm]; rw [AffineMap.lineMap_apply]; rw [vadd_vsub_assoc]; rw [show (p₂ -ᵥ p₁ : V) = v - u from
      (vsub_sub_vsub_cancel_right p₂ p₁ o).symm]
    module
  rw [dist_comm]; rw [dist_eq_norm_vsub]; rw [hpo]
  have hmem := (strictConvex_closedBall Real (0 : V) s.radius)
    (by simp [Metric.mem_closedBall, hu]) (by simp [Metric.mem_closedBall, hv])
    huv (sub_pos.mpr ht₁') ht₀' (sub_add_cancel 1 t)
  rwa [interior_closedBall _ (fun h : s.radius = 0 => huv <|
      (norm_eq_zero.mp (hu.trans h)).trans (norm_eq_zero.mp (hv.trans h)).symm),
    Metric.mem_ball, dist_zero_right] at hmem

/--
theorem `Sphere.dist_center_midpoint_lt_radius` / 定理 `Sphere.dist_center_midpoint_lt_radius`

English:
theorem Sphere.dist_center_midpoint_lt_radius
  statement: {p₁ p₂ : P} {s : Sphere P}
  proof: s.dist_center_lt_radius_of_sbtw hp₁ hp₂ (sbtw_midpoint_of_ne Real hp₁p₂)

中文:
定理 Sphere.dist_center_midpoint_lt_radius
  结论: {p₁ p₂ : P} {s : Sphere P}
  证明: s.dist_center_lt_radius_of_sbtw hp₁ hp₂ (sbtw_midpoint_of_ne Real hp₁p₂)

Depends on / 依赖: dist_center_lt_radius_of_sbtw, s.dist_center_lt_radius_of_sbtw, sbtw_midpoint_of_ne
-/
theorem Sphere.dist_center_midpoint_lt_radius {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₁p₂ : p₁ != p₂) :
    dist s.center (midpoint Real p₁ p₂) < s.radius :=
  s.dist_center_lt_radius_of_sbtw hp₁ hp₂ (sbtw_midpoint_of_ne Real hp₁p₂)

/--
theorem `eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two` / 定理 `eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two`

English:
theorem eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two
  statement: {s : AffineSubspace Real P}
  proof: eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

中文:
定理 eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two
  结论: {s : AffineSubspace 实数 P}
  证明: eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

Depends on / 依赖: Sphere, Sphere.center_ne_iff_ne_of_mem, center_ne_iff_ne_of_mem, eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
-/
theorem eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : AffineSubspace Real P}
    [FiniteDimensional Real s.direction] (hd : finrank Real s.direction = 2) {s₁ s₂ : Sphere P}
    {p₁ p₂ p : P} (hs₁ : s₁.center in s) (hs₂ : s₂.center in s) (hp₁s : p₁ in s) (hp₂s : p₂ in s)
    (hps : p in s) (hs : s₁ != s₂) (hp : p₁ != p₂) (hp₁s₁ : p₁ in s₁) (hp₂s₁ : p₂ in s₁) (hps₁ : p in s₁)
    (hp₁s₂ : p₁ in s₂) (hp₂s₂ : p₂ in s₂) (hps₂ : p in s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/--
theorem `eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two` / 定理 `eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two`

English:
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
  statement: [FiniteDimensional Real V]
  proof: eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

中文:
定理 eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
  结论: [FiniteDimensional 实数 V]
  证明: eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

Depends on / 依赖: Sphere, Sphere.center_ne_iff_ne_of_mem, center_ne_iff_ne_of_mem, eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
-/
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional Real V]
    (hd : finrank Real V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ != s₂) (hp : p₁ != p₂)
    (hp₁s₁ : p₁ in s₁) (hp₂s₁ : p₂ in s₁) (hps₁ : p in s₁) (hp₁s₂ : p₁ in s₂) (hp₂s₂ : p₂ in s₂)
    (hps₂ : p in s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/--
theorem `inner_pos_or_eq_of_dist_le_radius` / 定理 `inner_pos_or_eq_of_dist_le_radius`

English:
theorem inner_pos_or_eq_of_dist_le_radius
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine Or.inl ?_
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [inner_sub_left]; rw [real_inner_self_eq_norm_mul_norm]; rw [sub_pos]
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right

中文:
定理 inner_pos_or_eq_of_dist_le_radius
  结论: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine Or.inl ?_
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [inner_sub_left]; rw [real_inner_self_eq_norm_mul_norm]; rw [sub_pos]
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right

Depends on / 依赖: Or.inl, Or.inr, center, dist_eq_norm_vsub, inner_sub_left, lt_of_le_of_ne, lt_or_eq, mem_sphere, mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_right, norm_nonneg, real_inner_le_norm, real_inner_self_eq_norm_mul_norm, s.center, sub_pos, trans_lt, vsub_sub_vsub_cancel_right
-/
theorem inner_pos_or_eq_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : dist p₂ s.center <= s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = p₂ := by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine Or.inl ?_
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center]; rw [inner_sub_left]; rw [real_inner_self_eq_norm_mul_norm]; rw [sub_pos]
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) ?_
  · rwa [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hp₁]
  · rcases hp₂.lt_or_eq with (hp₂' | hp₂')
    · refine ((real_inner_le_norm _ _).trans_lt (mul_lt_mul_of_pos_right ?_ ?_)).ne
      · rwa [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      · rw [norm_pos_iff, vsub_ne_zero]
        rintro rfl
        rw [← hp₁] at hp₂'
        refine (dist_nonneg.not_gt : ¬dist p₂ s.center < 0) ?_
        simpa using hp₂'
    · rw [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      nth_rw 1 [← hp₂']
      rw [Ne]; rw [inner_eq_norm_mul_iff_real]; rw [hp₂']; rw [← sub_eq_zero]; rw [← smul_sub]; rw [vsub_sub_vsub_cancel_right]; rw [← Ne]; rw [smul_ne_zero_iff]; rw [vsub_ne_zero]; rw [and_iff_left (Ne.symm h)]; rw [norm_ne_zero_iff]; rw [vsub_ne_zero]
      rintro rfl
      refine h (Eq.symm ?_)
      simpa using hp₂'

/--
theorem `inner_nonneg_of_dist_le_radius` / 定理 `inner_nonneg_of_dist_le_radius`

English:
theorem inner_nonneg_of_dist_le_radius
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp

中文:
定理 inner_nonneg_of_dist_le_radius
  结论: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp

Depends on / 依赖: h.le, inner_pos_or_eq_of_dist_le_radius
-/
theorem inner_nonneg_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : dist p₂ s.center <= s.radius) : 0 <= ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp

/--
theorem `inner_pos_of_dist_lt_radius` / 定理 `inner_pos_of_dist_lt_radius`

English:
theorem inner_pos_of_dist_lt_radius
  statement: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  proof: by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h

中文:
定理 inner_pos_of_dist_lt_radius
  结论: {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
  证明: by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h

Depends on / 依赖: False.elim, inner_pos_or_eq_of_dist_le_radius, mem_sphere, resolve_right
-/
theorem inner_pos_of_dist_lt_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s)
    (hp₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h

/--
theorem `inner_vsub_center_vsub_pos` / 定理 `inner_vsub_center_vsub_pos`

English:
theorem inner_vsub_center_vsub_pos
  statement: {p₁ p₂ : P} {s : Sphere P}
  proof: by
  have hp₁' : ‖p₁ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hp₂' : ‖p₂ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₂
  have hd : ‖p₂ -ᵥ s.center‖ ^ 2 =
      ‖p₂ -ᵥ p₁‖ ^ 2 + 2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ s.center⟫ + ‖p₁ -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_can

中文:
定理 inner_vsub_center_vsub_pos
  结论: {p₁ p₂ : P} {s : Sphere P}
  证明: by
  have hp₁' : ‖p₁ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hp₂' : ‖p₂ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₂
  have hd : ‖p₂ -ᵥ s.center‖ ^ 2 =
      ‖p₂ -ᵥ p₁‖ ^ 2 + 2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ s.center⟫ + ‖p₁ -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_can

Depends on / 依赖: center, inner_neg_right, neg_vsub_eq_vsub_rev, norm_add_sq_real, norm_pos_iff, norm_pos_iff.mpr, norm_vsub_center_eq_radius, radius, s.center, s.radius, sq_pos_of_pos, vsub_add_vsub_cancel, vsub_ne_zero, vsub_ne_zero.mpr
-/
theorem inner_vsub_center_vsub_pos {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₁p₂ : p₁ != p₂) :
    0 < ⟪p₂ -ᵥ p₁, s.center -ᵥ p₁⟫ := by
  have hp₁' : ‖p₁ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₁
  have hp₂' : ‖p₂ -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hp₂
  have hd : ‖p₂ -ᵥ s.center‖ ^ 2 =
      ‖p₂ -ᵥ p₁‖ ^ 2 + 2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ s.center⟫ + ‖p₁ -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_cancel p₂ p₁ s.center]; rw [norm_add_sq_real]
  rw [hp₂']; rw [hp₁']; rw [← neg_vsub_eq_vsub_rev s.center p₁]; rw [inner_neg_right] at hd
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hp₁p₂.symm))]

/--
theorem `wbtw_of_collinear_of_dist_center_le_radius` / 定理 `wbtw_of_collinear_of_dist_center_le_radius`

English:
theorem wbtw_of_collinear_of_dist_center_le_radius
  statement: {s : Sphere P} {p₁ p₂ p₃ : P}
  proof: h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

中文:
定理 wbtw_of_collinear_of_dist_center_le_radius
  结论: {s : Sphere P} {p₁ p₂ p₃ : P}
  证明: h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

Depends on / 依赖: h.wbtw_of_dist_eq_of_dist_le, wbtw_of_dist_eq_of_dist_le
-/
theorem wbtw_of_collinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : dist p₂ s.center <= s.radius)
    (hp₃ : p₃ in s) (hp₁p₃ : p₁ != p₃) : Wbtw Real p₁ p₂ p₃ :=
  h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

/--
theorem `sbtw_of_collinear_of_dist_center_lt_radius` / 定理 `sbtw_of_collinear_of_dist_center_lt_radius`

English:
theorem sbtw_of_collinear_of_dist_center_lt_radius
  statement: {s : Sphere P} {p₁ p₂ p₃ : P}
  proof: h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

中文:
定理 sbtw_of_collinear_of_dist_center_lt_radius
  结论: {s : Sphere P} {p₁ p₂ p₃ : P}
  证明: h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

Depends on / 依赖: h.sbtw_of_dist_eq_of_dist_lt, sbtw_of_dist_eq_of_dist_lt
-/
theorem sbtw_of_collinear_of_dist_center_lt_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear Real ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : dist p₂ s.center < s.radius)
    (hp₃ : p₃ in s) (hp₁p₃ : p₁ != p₃) : Sbtw Real p₁ p₂ p₃ :=
  h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

namespace Sphere

variable {s : Sphere P} {p₁ p₂ : P}

/--
lemma `isDiameter_iff_mem_and_mem_and_dist` / 引理 `isDiameter_iff_mem_and_mem_and_dist`

English:
lemma isDiameter_iff_mem_and_mem_and_dist
  proof: by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.dist_left_right⟩, fun ⟨h₁, h₂, hr⟩ => ⟨h₁, ?_⟩⟩
  rw [midpoint_eq_iff]; rw [AffineEquiv.pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]
  apply eq_of_norm_eq_of_norm_add_eq
  · simp_rw [← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere

中文:
引理 isDiameter_iff_mem_and_mem_and_dist
  证明: by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.dist_left_right⟩, fun ⟨h₁, h₂, hr⟩ => ⟨h₁, ?_⟩⟩
  rw [midpoint_eq_iff]; rw [AffineEquiv.pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]
  apply eq_of_norm_eq_of_norm_add_eq
  · simp_rw [← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_apply, dist_comm, dist_eq_norm_vsub, dist_left_right, eq_comm, eq_of_norm_eq_of_norm_add_eq, eq_vadd_iff_vsub_eq, h.dist_left_right, h.left_mem, h.right_mem, left_mem, mem_sphere, midpoint_eq_iff, pointReflection_apply, right_mem, simp_rw, two_mul, vsub_add_vsub_cancel
-/
lemma isDiameter_iff_mem_and_mem_and_dist :
    s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in s ∧ dist p₁ p₂ = 2 * s.radius := by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.dist_left_right⟩, fun ⟨h₁, h₂, hr⟩ => ⟨h₁, ?_⟩⟩
  rw [midpoint_eq_iff]; rw [AffineEquiv.pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]
  apply eq_of_norm_eq_of_norm_add_eq
  · simp_rw [← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
  · simp_rw [vsub_add_vsub_cancel, ← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
    rw [dist_comm]; rw [hr]; rw [two_mul]

/--
lemma `isDiameter_iff_mem_and_mem_and_wbtw` / 引理 `isDiameter_iff_mem_and_mem_and_wbtw`

English:
lemma isDiameter_iff_mem_and_mem_and_wbtw
  proof: by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.wbtw⟩, fun ⟨h₁, h₂, hr⟩ => ?_⟩
  have hd := hr.dist_add_dist
  rw [mem_sphere.1 h₁]; rw [mem_sphere'.1 h₂]; rw [← two_mul]; rw [eq_comm] at hd
  exact isDiameter_iff_mem_and_mem_and_dist.2 ⟨h₁, h₂, hd⟩

中文:
引理 isDiameter_iff_mem_and_mem_and_wbtw
  证明: by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.wbtw⟩, fun ⟨h₁, h₂, hr⟩ => ?_⟩
  have hd := hr.dist_add_dist
  rw [mem_sphere.1 h₁]; rw [mem_sphere'.1 h₂]; rw [← two_mul]; rw [eq_comm] at hd
  exact isDiameter_iff_mem_and_mem_and_dist.2 ⟨h₁, h₂, hd⟩

Depends on / 依赖: dist_add_dist, eq_comm, h.left_mem, h.right_mem, h.wbtw, hr.dist_add_dist, isDiameter_iff_mem_and_mem_and_dist, left_mem, mem_sphere, right_mem, two_mul
-/
lemma isDiameter_iff_mem_and_mem_and_wbtw :
    s.IsDiameter p₁ p₂ ↔ p₁ in s ∧ p₂ in s ∧ Wbtw Real p₁ s.center p₂ := by
  refine ⟨fun h => ⟨h.left_mem, h.right_mem, h.wbtw⟩, fun ⟨h₁, h₂, hr⟩ => ?_⟩
  have hd := hr.dist_add_dist
  rw [mem_sphere.1 h₁]; rw [mem_sphere'.1 h₂]; rw [← two_mul]; rw [eq_comm] at hd
  exact isDiameter_iff_mem_and_mem_and_dist.2 ⟨h₁, h₂, hd⟩

/--
theorem `center_mem_affineSpan_pair_iff_isDiameter` / 定理 `center_mem_affineSpan_pair_iff_isDiameter`

English:
theorem center_mem_affineSpan_pair_iff_isDiameter
  given: (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  proof: by
  rcases eq_or_ne p₁ p₂ with rfl | hp₁p₂
  · simp [isDiameter_iff_left_mem_and_midpoint_eq_center, hp₁, eq_comm]
  · rw [isDiameter_iff_mem_and_mem_and_wbtw]
    refine ⟨fun h => ⟨hp₁, hp₂, ?_⟩, fun h => h.2.2.mem_affineSpan⟩
    refine wbtw_of_collinear_of_dist_center_le_radius ?_ hp₁ ?_ hp₂ hp₁

中文:
定理 center_mem_affineSpan_pair_iff_isDiameter
  条件: (hp₁ : p₁ in s) (hp₂ : p₂ in s)
  证明: by
  rcases eq_or_ne p₁ p₂ with rfl | hp₁p₂
  · simp [isDiameter_iff_left_mem_and_midpoint_eq_center, hp₁, eq_comm]
  · rw [isDiameter_iff_mem_and_mem_and_wbtw]
    refine ⟨fun h => ⟨hp₁, hp₂, ?_⟩, fun h => h.2.2.mem_affineSpan⟩
    refine wbtw_of_collinear_of_dist_center_le_radius ?_ hp₁ ?_ hp₂ hp₁

Depends on / 依赖: Set.insert_comm, collinear_insert_of_mem_affineSpan_pair, eq_comm, eq_or_ne, insert_comm, isDiameter_iff_left_mem_and_midpoint_eq_center, isDiameter_iff_mem_and_mem_and_wbtw, mem_affineSpan, radius_nonneg_of_mem, wbtw_of_collinear_of_dist_center_le_radius
-/
theorem center_mem_affineSpan_pair_iff_isDiameter (hp₁ : p₁ in s) (hp₂ : p₂ in s) :
    s.center in line[Real, p₁, p₂] ↔ s.IsDiameter p₁ p₂ := by
  rcases eq_or_ne p₁ p₂ with rfl | hp₁p₂
  · simp [isDiameter_iff_left_mem_and_midpoint_eq_center, hp₁, eq_comm]
  · rw [isDiameter_iff_mem_and_mem_and_wbtw]
    refine ⟨fun h => ⟨hp₁, hp₂, ?_⟩, fun h => h.2.2.mem_affineSpan⟩
    refine wbtw_of_collinear_of_dist_center_le_radius ?_ hp₁ ?_ hp₂ hp₁p₂
    · rw [Set.insert_comm]; exact collinear_insert_of_mem_affineSpan_pair h
    · simpa using radius_nonneg_of_mem hp₁

end Sphere

end EuclideanSpace

end EuclideanGeometry
