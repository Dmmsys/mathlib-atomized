/-
Copyright (c) 2026 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Cover

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **Uniformly Discrete**: there exists `packingRadius > 0` such that distinct points of `D`
  are separated by a distance strictly greater than `packingRadius`;
* **Relatively Dense**: there exists `coveringRadius > 0` such that every point of `X`
  lies within distance `coveringRadius` of some point of `D`.

The `DeloneSet` structure stores the set together with explicit radii witnessing
these properties. The definitions use metric entourages so that the theory fits
naturally into the uniformity framework.

Delone sets appear in discrete geometry, crystallography, aperiodic order, and tiling theory.

## Main definitions

* `Delone.DeloneSet X`: The main structure representing a Delone set in a metric space `X`.
* `DeloneSet.mapBilipschitz`: Transports a Delone set along a bilipschitz equivalence,
  scaling the radii.
* `DeloneSet.mapIsometry` Preserves the packing and covering radii exactly.

## Basic properties

* `packingRadius_lt_dist_of_mem_ne` : Distinct points in a Delone set are further apart than
  the packing radius.
* `exists_dist_le_coveringRadius` : Every point of the space lies within the covering radius
  of the set.
* `subset_ball_singleton` : Any ball of sufficiently small radius contains at most one point of
  the set.

## Implementation notes

* **Bundled Structure**: `DeloneSet` is bundled as a structure rather than a predicate
  (e.g., `IsDelone`). This facilitates dynamical systems constructions like hulls and patches by
  ensuring operations automatically preserve the required properties, eliminating the need to
  manually pass around proofs that the set remains Delone.
* **Explicit Data**: Since radii are stored as explicit data, the map from `DeloneSet X` to `Set X`
  is not injective. We provide a `Membership` instance and `mem_carrier` to allow the convenience
  of `∈` notation while ensuring radii remain bundled, computationally accessible, and tracked by
  extensionality.
-/

@[expose] public section

open Metric
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Delone

/-- A **Delone set** consists of a set together with explicit radii
witnessing uniform discreteness and relative denseness. -/
@[ext]
/--
Definition of `DeloneSet` / `DeloneSet` 的定义

English:
structure DeloneSet
  parameters: (X : Type*) [MetricSpace X]
  axioms and operations (7):
    - carrier : Set X
    - packingRadius : Real>=0
    - packingRadius_pos : 0 < packingRadius
    - isSeparated_packingRadius : IsSeparated packingRadius carrier
    - coveringRadius : Real>=0
    - coveringRadius_pos : 0 < coveringRadius
    - isCover_coveringRadius : IsCover coveringRadius .univ carrier

中文:
结构 DeloneSet
  参数: (X : 类型) [度量空间 X]
  公理与运算 (7 个):
    - carrier : 集合 X
    - packingRadius : 实数>=0
    - packingRadius_pos : 0 < packingRadius
    - isSeparated_packingRadius : 是分离 packingRadius carrier
    - coveringRadius : 实数>=0
    - coveringRadius_pos : 0 < coveringRadius
    - isCover_coveringRadius : IsCover coveringRadius .univ carrier
-/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set. -/
  carrier : Set X
  /-- Radius such that distinct points of `carrier` are separated by more than `r`. -/
  packingRadius : Real>=0
  packingRadius_pos : 0 < packingRadius
  isSeparated_packingRadius : IsSeparated packingRadius carrier
  /-- Radius such that every point of the space is within `R` of `carrier`. -/
  coveringRadius : Real>=0
  coveringRadius_pos : 0 < coveringRadius
  isCover_coveringRadius : IsCover coveringRadius .univ carrier

namespace DeloneSet

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (D : DeloneSet X)
  body: D.carrier

中文:
定义 toSet
  签名: (D : DeloneSet X)
  定义体: D.carrier
-/
@[coe] def toSet (D : DeloneSet X) : Set X := D.carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (DeloneSet X) (Set X)
  body: DeloneSet.toSet

中文:
实例 :
  签名: Coe (DeloneSet X) (集合 X)
  定义体: DeloneSet.toSet

Depends on / 依赖: DeloneSet, DeloneSet.toSet
-/
instance : Coe (DeloneSet X) (Set X) where
  coe := DeloneSet.toSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership X (DeloneSet X)
  body: x in (D : Set X)

@[simp, norm_cast]

中文:
实例 :
  签名: Membership X (DeloneSet X)
  定义体: x in (D : Set X)

@[simp, norm_cast]
-/
instance : Membership X (DeloneSet X) where
  mem D x := x in (D : Set X)

@[simp, norm_cast]
/--
lemma `mem_coe` / 引理 `mem_coe`

English:
lemma mem_coe
  given: {D : DeloneSet X} {x : X}
  statement: x in (D : Set X) ↔ x in D
  proof: .rfl

中文:
引理 mem_coe
  条件: {D : DeloneSet X} {x : X}
  结论: x in (D : 集合 X) ↔ x in D
  证明: .rfl
-/
lemma mem_coe {D : DeloneSet X} {x : X} : x in (D : Set X) ↔ x in D := .rfl

/--
lemma `mem_carrier` / 引理 `mem_carrier`

English:
lemma mem_carrier
  given: {D : DeloneSet X} {x : X}
  proof: .rfl

中文:
引理 mem_carrier
  条件: {D : DeloneSet X} {x : X}
  证明: .rfl
-/
@[simp] lemma mem_carrier {D : DeloneSet X} {x : X} :
    x in D.carrier ↔ x in D := .rfl

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: [Nonempty X] (D : DeloneSet X)
  statement: (D : Set X).Nonempty
  proof: D.isCover_coveringRadius.nonempty Set.univ_nonempty

中文:
引理 nonempty
  条件: [非空 X] (D : DeloneSet X)
  结论: (D : 集合 X).非空
  证明: D.isCover_coveringRadius.nonempty Set.univ_nonempty

Depends on / 依赖: D.isCover_coveringRadius.nonempty, Set.univ_nonempty, isCover_coveringRadius, nonempty, univ_nonempty
-/
lemma nonempty [Nonempty X] (D : DeloneSet X) : (D : Set X).Nonempty :=
  D.isCover_coveringRadius.nonempty Set.univ_nonempty

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (D : DeloneSet X) (carrier : Set X) (packingRadius coveringRadius : Real>=0)
  body: carrier
  packingRadius := packingRadius
  packingRadius_pos := by simpa [h_packing] using D.packingRadius_pos
  isSeparated_packingRadius := by
    simpa [h_carrier, h_packing] using D.isSeparated_packingRadius
  coveringRadius := coveringRadius
  coveringRadius_pos := by simpa [h_covering] using D

中文:
定义 copy
  签名: (D : DeloneSet X) (carrier : 集合 X) (packingRadius coveringRadius : 实数>=0)
  定义体: carrier
  packingRadius := packingRadius
  packingRadius_pos := by simpa [h_packing] using D.packingRadius_pos
  isSeparated_packingRadius := by
    simpa [h_carrier, h_packing] using D.isSeparated_packingRadius
  coveringRadius := coveringRadius
  coveringRadius_pos := by simpa [h_covering] using D
-/
protected def copy (D : DeloneSet X) (carrier : Set X) (packingRadius coveringRadius : Real>=0)
    (h_carrier : carrier = D.carrier) (h_packing : packingRadius = D.packingRadius)
    (h_covering : coveringRadius = D.coveringRadius) :
    DeloneSet X where
  carrier := carrier
  packingRadius := packingRadius
  packingRadius_pos := by simpa [h_packing] using D.packingRadius_pos
  isSeparated_packingRadius := by
    simpa [h_carrier, h_packing] using D.isSeparated_packingRadius
  coveringRadius := coveringRadius
  coveringRadius_pos := by simpa [h_covering] using D.coveringRadius_pos
  isCover_coveringRadius := by
    simpa [h_carrier, h_covering] using D.isCover_coveringRadius

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  statement: (D : DeloneSet X)
  proof: DeloneSet.ext h_carrier h_packing h_covering

中文:
定理 copy_eq
  结论: (D : DeloneSet X)
  证明: DeloneSet.ext h_carrier h_packing h_covering

Depends on / 依赖: DeloneSet, DeloneSet.ext, h_carrier, h_covering, h_packing
-/
theorem copy_eq (D : DeloneSet X)
    (carrier packingRadius coveringRadius h_carrier h_packing h_covering) :
    D.copy carrier packingRadius coveringRadius h_carrier h_packing h_covering = D :=
  DeloneSet.ext h_carrier h_packing h_covering

/--
lemma `packingRadius_lt_dist_of_mem_ne` / 引理 `packingRadius_lt_dist_of_mem_ne`

English:
lemma packingRadius_lt_dist_of_mem_ne
  statement: (D : DeloneSet X) {x y : X}
  proof: by
  have hsep : ENNReal.ofReal D.packingRadius < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.isSeparated_packingRadius hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep

中文:
引理 packingRadius_lt_dist_of_mem_ne
  结论: (D : DeloneSet X) {x y : X}
  证明: by
  have hsep : ENNReal.ofReal D.packingRadius < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.isSeparated_packingRadius hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep

Depends on / 依赖: D.isSeparated_packingRadius, D.packingRadius, ENNReal, ENNReal.ofReal, ENNReal.ofReal_lt_ofReal_iff, dist_pos, dist_pos.mpr, edist_dist, isSeparated_packingRadius, ofReal, ofReal_lt_ofReal_iff, packingRadius
-/
lemma packingRadius_lt_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x in D) (hy : y in D) (hne : x != y) :
    D.packingRadius < dist x y := by
  have hsep : ENNReal.ofReal D.packingRadius < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.isSeparated_packingRadius hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep

/--
lemma `exists_dist_le_coveringRadius` / 引理 `exists_dist_le_coveringRadius`

English:
lemma exists_dist_le_coveringRadius
  given: (D : DeloneSet X) (x : X)
  proof: by
  obtain ⟨y, hy, hdist⟩ := D.isCover_coveringRadius (x := x) (by trivial)
  exact ⟨y, hy, by simpa [edist_dist] using hdist⟩

中文:
引理 存在_dist_le_coveringRadius
  条件: (D : DeloneSet X) (x : X)
  证明: by
  obtain ⟨y, hy, hdist⟩ := D.isCover_coveringRadius (x := x) (by trivial)
  exact ⟨y, hy, by simpa [edist_dist] using hdist⟩

Depends on / 依赖: D.isCover_coveringRadius, edist_dist, isCover_coveringRadius
-/
lemma exists_dist_le_coveringRadius (D : DeloneSet X) (x : X) :
    exists y in D, dist x y <= D.coveringRadius := by
  obtain ⟨y, hy, hdist⟩ := D.isCover_coveringRadius (x := x) (by trivial)
  exact ⟨y, hy, by simpa [edist_dist] using hdist⟩

/--
lemma `eq_of_mem_ball` / 引理 `eq_of_mem_ball`

English:
lemma eq_of_mem_ball
  statement: (D : DeloneSet X) {r : Real>=0} (hr : r <= D.packingRadius / 2)
  proof: by
  by_contra hne
exact (D.packingRadius_lt_dist_of_mem_ne hx hy hne).not_gt calc
    dist x y <= dist x z + dist y z := dist_triangle_right x y z
    _ < r + r := by gcongr <;> simpa
    _ <= D.packingRadius := by rw [← add_halves D.packingRadius, NNReal.coe_add]; gcongr

中文:
引理 eq_of_mem_ball
  结论: (D : DeloneSet X) {r : 实数>=0} (hr : r <= D.packingRadius / 2)
  证明: by
  by_contra hne
exact (D.packingRadius_lt_dist_of_mem_ne hx hy hne).not_gt calc
    dist x y <= dist x z + dist y z := dist_triangle_right x y z
    _ < r + r := by gcongr <;> simpa
    _ <= D.packingRadius := by rw [← add_halves D.packingRadius, NNReal.coe_add]; gcongr

Depends on / 依赖: D.packingRadius, D.packingRadius_lt_dist_of_mem_ne, NNReal, NNReal.coe_add, add_halves, coe_add, dist_triangle_right, not_gt, packingRadius, packingRadius_lt_dist_of_mem_ne
-/
lemma eq_of_mem_ball (D : DeloneSet X) {r : Real>=0} (hr : r <= D.packingRadius / 2)
    {x y z : X} (hx : x in D) (hy : y in D) (hxz : x in ball z r) (hyz : y in ball z r) :
    x = y := by
  by_contra hne
exact (D.packingRadius_lt_dist_of_mem_ne hx hy hne).not_gt calc
    dist x y <= dist x z + dist y z := dist_triangle_right x y z
    _ < r + r := by gcongr <;> simpa
    _ <= D.packingRadius := by rw [← add_halves D.packingRadius, NNReal.coe_add]; gcongr

/--
lemma `subset_ball_singleton` / 引理 `subset_ball_singleton`

English:
lemma subset_ball_singleton
  given: (D : DeloneSet X)
  proof: ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, fun hx hy => D.eq_of_mem_ball le_rfl hx hy⟩

中文:
引理 subset_ball_singleton
  条件: (D : DeloneSet X)
  证明: ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, fun hx hy => D.eq_of_mem_ball le_rfl hx hy⟩

Depends on / 依赖: D.eq_of_mem_ball, D.packingRadius, D.packingRadius_pos, eq_of_mem_ball, half_pos, le_rfl, packingRadius, packingRadius_pos
-/
lemma subset_ball_singleton (D : DeloneSet X) :
    exists r > 0, forall {x y z}, x in D -> y in D -> x in ball z r -> y in ball z r -> x = y :=
  ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, fun hx hy => D.eq_of_mem_ball le_rfl hx hy⟩

/-- Bilipschitz maps send Delone sets to Delone sets. -/
@[simps]
/--
Definition of `mapBilipschitz` / `mapBilipschitz` 的定义

English:
definition mapBilipschitz
  signature: (f : X ≃ Y) (K₁ K₂ : Real>=0) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
  body: f '' D.carrier
  packingRadius := D.packingRadius / K₁
  packingRadius_pos := div_pos D.packingRadius_pos hK₁
  isSeparated_packingRadius := D.isSeparated_packingRadius.image_antilipschitz hf₁ hK₁
  coveringRadius := K₂ * D.coveringRadius
  coveringRadius_pos := mul_pos hK₂ D.coveringRadius_pos
  is

中文:
定义 mapBilipschitz
  签名: (f : X ≃ Y) (K₁ K₂ : 实数>=0) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
  定义体: f '' D.carrier
  packingRadius := D.packingRadius / K₁
  packingRadius_pos := div_pos D.packingRadius_pos hK₁
  isSeparated_packingRadius := D.isSeparated_packingRadius.image_antilipschitz hf₁ hK₁
  coveringRadius := K₂ * D.coveringRadius
  coveringRadius_pos := mul_pos hK₂ D.coveringRadius_pos
  is

Depends on / 依赖: D.carrier, carrier
-/
noncomputable def mapBilipschitz (f : X ≃ Y) (K₁ K₂ : Real>=0) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) (D : DeloneSet X) : DeloneSet Y where
  carrier := f '' D.carrier
  packingRadius := D.packingRadius / K₁
  packingRadius_pos := div_pos D.packingRadius_pos hK₁
  isSeparated_packingRadius := D.isSeparated_packingRadius.image_antilipschitz hf₁ hK₁
  coveringRadius := K₂ * D.coveringRadius
  coveringRadius_pos := mul_pos hK₂ D.coveringRadius_pos
  isCover_coveringRadius := D.isCover_coveringRadius.image_lipschitz_of_surjective hf₂ f.surjective

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapBilipschitz_refl` / 引理 `mapBilipschitz_refl`

English:
lemma mapBilipschitz_refl
  given: (D : DeloneSet X) (hK1 hK2 hA hL)
  proof: by
  ext <;> simp only [mapBilipschitz, Equiv.refl_apply, Set.image_id', div_one, one_mul]

中文:
引理 mapBilipschitz_refl
  条件: (D : DeloneSet X) (hK1 hK2 hA hL)
  证明: by
  ext <;> simp only [mapBilipschitz, Equiv.refl_apply, Set.image_id', div_one, one_mul]
-/
@[simp] lemma mapBilipschitz_refl (D : DeloneSet X) (hK1 hK2 hA hL) :
    D.mapBilipschitz (.refl X) 1 1 hK1 hK2 hA hL = D := by
  ext <;> simp only [mapBilipschitz, Equiv.refl_apply, Set.image_id', div_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapBilipschitz_trans` / 引理 `mapBilipschitz_trans`

English:
lemma mapBilipschitz_trans
  statement: {Z : Type*} [MetricSpace Z] (D : DeloneSet X)
  proof: by
  ext
  · simp only [mapBilipschitz_carrier, Equiv.trans_apply, Set.mem_image]
    exact exists_exists_and_eq_and
  · simp only [mapBilipschitz_packingRadius, NNReal.coe_div, div_div]
  · simp only [mapBilipschitz_coveringRadius, NNReal.coe_mul, mul_assoc]

中文:
引理 mapBilipschitz_trans
  结论: {Z : 类型} [度量空间 Z] (D : DeloneSet X)
  证明: by
  ext
  · simp only [mapBilipschitz_carrier, Equiv.trans_apply, Set.mem_image]
    exact exists_exists_and_eq_and
  · simp only [mapBilipschitz_packingRadius, NNReal.coe_div, div_div]
  · simp only [mapBilipschitz_coveringRadius, NNReal.coe_mul, mul_assoc]

Depends on / 依赖: Equiv.trans_apply, NNReal, NNReal.coe_div, NNReal.coe_mul, Set.mem_image, coe_div, coe_mul, div_div, exists_exists_and_eq_and, mapBilipschitz_carrier, mapBilipschitz_coveringRadius, mapBilipschitz_packingRadius, mem_image, mul_assoc, trans_apply
-/
lemma mapBilipschitz_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X)
    (f : X ≃ Y) (g : Y ≃ Z) (K₁f K₂f K₁g K₂g : Real>=0)
    (hf₁_pos : 0 < K₁f) (hf₂_pos : 0 < K₂f)
    (hg₁_pos : 0 < K₁g) (hg₂_pos : 0 < K₂g)
    (hf_anti : AntilipschitzWith K₁f f) (hf_lip : LipschitzWith K₂f f)
    (hg_anti : AntilipschitzWith K₁g g) (hg_lip : LipschitzWith K₂g g) :
    (D.mapBilipschitz f K₁f K₂f hf₁_pos hf₂_pos hf_anti hf_lip).mapBilipschitz
      g K₁g K₂g hg₁_pos hg₂_pos hg_anti hg_lip =
    D.mapBilipschitz (f.trans g) (K₁f * K₁g) (K₂g * K₂f)
      (mul_pos hf₁_pos hg₁_pos) (mul_pos hg₂_pos hf₂_pos)
      (hg_anti.comp hf_anti) (hg_lip.comp hf_lip) := by
  ext
  · simp only [mapBilipschitz_carrier, Equiv.trans_apply, Set.mem_image]
    exact exists_exists_and_eq_and
  · simp only [mapBilipschitz_packingRadius, NNReal.coe_div, div_div]
  · simp only [mapBilipschitz_coveringRadius, NNReal.coe_mul, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The image of a Delone set under an isometry. This is a specialization of
`DeloneSet.mapBilipschitz` where the packing and covering radii are preserved because the
Lipschitz constants are both 1. -/
@[simps!]
/--
Definition of `mapIsometry` / `mapIsometry` 的定义

English:
definition mapIsometry
  signature: (f : X ≃ᵢ Y)
  body: (D.mapBilipschitz f.toEquiv 1 1 zero_lt_one zero_lt_one
      f.isometry.antilipschitz f.isometry.lipschitz).copy (f '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  invFun D := (D.mapBilipschitz f.symm.toEquiv 1 1 zero_lt_one zero_lt_o

中文:
定义 mapIsometry
  签名: (f : X ≃ᵢ Y)
  定义体: (D.mapBilipschitz f.toEquiv 1 1 zero_lt_one zero_lt_one
      f.isometry.antilipschitz f.isometry.lipschitz).copy (f '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  invFun D := (D.mapBilipschitz f.symm.toEquiv 1 1 zero_lt_one zero_lt_o

Depends on / 依赖: D.mapBilipschitz, f.toEquiv, mapBilipschitz, toEquiv, zero_lt_one
-/
noncomputable def mapIsometry (f : X ≃ᵢ Y) : DeloneSet X ≃ DeloneSet Y where
  toFun D := (D.mapBilipschitz f.toEquiv 1 1 zero_lt_one zero_lt_one
      f.isometry.antilipschitz f.isometry.lipschitz).copy (f '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  invFun D := (D.mapBilipschitz f.symm.toEquiv 1 1 zero_lt_one zero_lt_one
      f.symm.isometry.antilipschitz f.symm.isometry.lipschitz).copy (f.symm '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  left_inv D := by ext <;> simp [copy_eq]
  right_inv D := by ext <;> simp [copy_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapIsometry_refl` / 引理 `mapIsometry_refl`

English:
lemma mapIsometry_refl
  given: (D : DeloneSet X)
  statement: D.mapIsometry (.refl X) = D
  proof: by
  ext <;> simp [mapIsometry, IsometryEquiv.refl, DeloneSet.copy]

中文:
引理 mapIsometry_refl
  条件: (D : DeloneSet X)
  结论: D.mapIsometry (.refl X) = D
  证明: by
  ext <;> simp [mapIsometry, IsometryEquiv.refl, DeloneSet.copy]
-/
@[simp] lemma mapIsometry_refl (D : DeloneSet X) : D.mapIsometry (.refl X) = D := by
  ext <;> simp [mapIsometry, IsometryEquiv.refl, DeloneSet.copy]

/--
lemma `mapIsometry_symm` / 引理 `mapIsometry_symm`

English:
lemma mapIsometry_symm
  given: (f : X ≃ᵢ Y)
  statement: (mapIsometry f).symm = mapIsometry f.symm
  proof: rfl

中文:
引理 mapIsometry_symm
  条件: (f : X ≃ᵢ Y)
  结论: (mapIsometry f).symm = mapIsometry f.symm
  证明: rfl
-/
lemma mapIsometry_symm (f : X ≃ᵢ Y) : (mapIsometry f).symm = mapIsometry f.symm := rfl

/--
lemma `mapIsometry_trans` / 引理 `mapIsometry_trans`

English:
lemma mapIsometry_trans
  given: {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z)
  proof: by
  ext <;> simp [mapIsometry, DeloneSet.copy]

中文:
引理 mapIsometry_trans
  条件: {Z : 类型} [度量空间 Z] (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z)
  证明: by
  ext <;> simp [mapIsometry, DeloneSet.copy]

Depends on / 依赖: DeloneSet, DeloneSet.copy, mapIsometry
-/
lemma mapIsometry_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.mapIsometry (f.trans g) = (D.mapIsometry f).mapIsometry g := by
  ext <;> simp [mapIsometry, DeloneSet.copy]

end DeloneSet

end Delone
