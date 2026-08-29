/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.
-/

@[expose] public section


noncomputable section

open Real RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] {p p₀ : P}

/-- The undirected angle at `p₂` between the line segments to `p₁` and
`p₃`. If either of those points equals `p₂`, this is π/2. Use
`open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃`
notation. -/
nonrec def angle (p₁ p₂ p₃ : P) : Real :=
  angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∠" => EuclideanGeometry.angle

/--
theorem `continuousAt_angle` / 定理 `continuousAt_angle`

English:
theorem continuousAt_angle
  given: {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1)
  proof: by
  let f : P × P × P -> V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 != 0 := by simp [f, hx12]
  have hf2 : (f x).2 != 0 := by simp [f, hx32]
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp (by fun_prop)

@[simp]

中文:
定理 continuousAt_angle
  条件: {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1)
  证明: by
  let f : P × P × P -> V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 != 0 := by simp [f, hx12]
  have hf2 : (f x).2 != 0 := by simp [f, hx32]
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp (by fun_prop)

@[simp]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.continuousAt_angle, continuousAt_angle, fun_prop
-/
theorem continuousAt_angle {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1) :
    ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x := by
  let f : P × P × P -> V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 != 0 := by simp [f, hx12]
  have hf2 : (f x).2 != 0 := by simp [f, hx32]
  exact (InnerProductGeometry.continuousAt_angle hf1 hf2).comp (by fun_prop)

@[simp]
/--
theorem `_root_.AffineIsometry.angle_map` / 定理 `_root_.AffineIsometry.angle_map`

English:
theorem _root_.AffineIsometry.angle_map
  statement: {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
  proof: by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]

@[simp, norm_cast]

中文:
定理 _root_.AffineIsometry.angle_map
  结论: {V₂ P₂ : 类型} [NormedAddCommGroup V₂]
  证明: by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]

@[simp, norm_cast]

Depends on / 依赖: AffineIsometry, AffineIsometry.map_vsub, LinearIsometry, LinearIsometry.angle_map, angle_map, map_vsub, simp_rw
-/
theorem _root_.AffineIsometry.angle_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂]
    [InnerProductSpace Real V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (f : P ->ᵃⁱ[Real] P₂) (p₁ p₂ p₃ : P) : ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]

@[simp, norm_cast]
/--
theorem `_root_.AffineSubspace.angle_coe` / 定理 `_root_.AffineSubspace.angle_coe`

English:
theorem _root_.AffineSubspace.angle_coe
  given: {s : AffineSubspace Real P} (p₁ p₂ p₃ : s)
  proof: ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃

中文:
定理 _root_.AffineSubspace.angle_coe
  条件: {s : AffineSubspace 实数 P} (p₁ p₂ p₃ : s)
  证明: ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃
-/
theorem _root_.AffineSubspace.angle_coe {s : AffineSubspace Real P} (p₁ p₂ p₃ : s) :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃

/--
lemma `angle_homothety` / 引理 `angle_homothety`

English:
lemma angle_homothety
  given: (p p₁ p₂ p₃ : P) {r : Real} (h : r != 0)
  proof: by
  simp_rw [angle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

中文:
引理 angle_homothety
  条件: (p p₁ p₂ p₃ : P) {r : 实数} (h : r != 0)
  证明: by
  simp_rw [angle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]
-/
@[simp] lemma angle_homothety (p p₁ p₂ p₃ : P) {r : Real} (h : r != 0) :
    ∠ (AffineMap.homothety p r p₁) (AffineMap.homothety p r p₂) (AffineMap.homothety p r p₃) =
      ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

/-- Angles are translation invariant. -/
@[simp]
/--
theorem `angle_const_vadd` / 定理 `angle_const_vadd`

English:
theorem angle_const_vadd
  given: (v : V) (p₁ p₂ p₃ : P)
  statement: ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃
  proof: (AffineIsometryEquiv.constVAdd Real P v).toAffineIsometry.angle_map _ _ _

中文:
定理 angle_const_vadd
  条件: (v : V) (p₁ p₂ p₃ : P)
  结论: ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃
  证明: (AffineIsometryEquiv.constVAdd Real P v).toAffineIsometry.angle_map _ _ _

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.constVAdd, angle_map, constVAdd, toAffineIsometry, toAffineIsometry.angle_map
-/
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVAdd Real P v).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/--
theorem `angle_vadd_const` / 定理 `angle_vadd_const`

English:
theorem angle_vadd_const
  given: (v₁ v₂ v₃ : V) (p : P)
  statement: ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃
  proof: (AffineIsometryEquiv.vaddConst Real p).toAffineIsometry.angle_map _ _ _

中文:
定理 angle_vadd_const
  条件: (v₁ v₂ v₃ : V) (p : P)
  结论: ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃
  证明: (AffineIsometryEquiv.vaddConst Real p).toAffineIsometry.angle_map _ _ _

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.vaddConst, angle_map, toAffineIsometry, toAffineIsometry.angle_map, vaddConst
-/
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst Real p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/--
theorem `angle_const_vsub` / 定理 `angle_const_vsub`

English:
theorem angle_const_vsub
  given: (p p₁ p₂ p₃ : P)
  statement: ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃
  proof: (AffineIsometryEquiv.constVSub Real p).toAffineIsometry.angle_map _ _ _

中文:
定理 angle_const_vsub
  条件: (p p₁ p₂ p₃ : P)
  结论: ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃
  证明: (AffineIsometryEquiv.constVSub Real p).toAffineIsometry.angle_map _ _ _

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.constVSub, angle_map, constVSub, toAffineIsometry, toAffineIsometry.angle_map
-/
theorem angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVSub Real p).toAffineIsometry.angle_map _ _ _

/-- Angles are translation invariant. -/
@[simp]
/--
theorem `angle_vsub_const` / 定理 `angle_vsub_const`

English:
theorem angle_vsub_const
  given: (p₁ p₂ p₃ p : P)
  statement: ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃
  proof: (AffineIsometryEquiv.vaddConst Real p).symm.toAffineIsometry.angle_map _ _ _

中文:
定理 angle_vsub_const
  条件: (p₁ p₂ p₃ p : P)
  结论: ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃
  证明: (AffineIsometryEquiv.vaddConst Real p).symm.toAffineIsometry.angle_map _ _ _

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.vaddConst, angle_map, symm.toAffineIsometry.angle_map, toAffineIsometry, vaddConst
-/
theorem angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst Real p).symm.toAffineIsometry.angle_map _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/--
theorem `angle_add_const` / 定理 `angle_add_const`

English:
theorem angle_add_const
  given: (v₁ v₂ v₃ : V) (v : V)
  statement: ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃
  proof: angle_vadd_const _ _ _ _

中文:
定理 angle_add_const
  条件: (v₁ v₂ v₃ : V) (v : V)
  结论: ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃
  证明: angle_vadd_const _ _ _ _

Depends on / 依赖: angle_vadd_const
-/
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/--
theorem `angle_const_add` / 定理 `angle_const_add`

English:
theorem angle_const_add
  given: (v : V) (v₁ v₂ v₃ : V)
  statement: ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃
  proof: angle_const_vadd _ _ _ _

中文:
定理 angle_const_add
  条件: (v : V) (v₁ v₂ v₃ : V)
  结论: ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃
  证明: angle_const_vadd _ _ _ _

Depends on / 依赖: angle_const_vadd
-/
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _

/-- Angles in a vector space are translation invariant. -/
@[simp]
/--
theorem `angle_sub_const` / 定理 `angle_sub_const`

English:
theorem angle_sub_const
  given: (v₁ v₂ v₃ : V) (v : V)
  statement: ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃
  proof: by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

中文:
定理 angle_sub_const
  条件: (v₁ v₂ v₃ : V) (v : V)
  结论: ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃
  证明: by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

Depends on / 依赖: angle_vsub_const, vsub_eq_sub
-/
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
/--
theorem `angle_const_sub` / 定理 `angle_const_sub`

English:
theorem angle_const_sub
  given: (v : V) (v₁ v₂ v₃ : V)
  statement: ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃
  proof: by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

中文:
定理 angle_const_sub
  条件: (v : V) (v₁ v₂ v₃ : V)
  结论: ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃
  证明: by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

Depends on / 依赖: angle_const_vsub, vsub_eq_sub
-/
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub v v₁ v₂ v₃

/-- Angles in a vector space are invariant under inversion. -/
@[simp]
/--
theorem `angle_neg` / 定理 `angle_neg`

English:
theorem angle_neg
  given: (v₁ v₂ v₃ : V)
  statement: ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃
  proof: by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

中文:
定理 angle_neg
  条件: (v₁ v₂ v₃ : V)
  结论: ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃
  证明: by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

Depends on / 依赖: angle_const_sub, zero_sub
-/
theorem angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃

/--
theorem `angle_smul_right_of_pos` / 定理 `angle_smul_right_of_pos`

English:
theorem angle_smul_right_of_pos
  statement: (p₁ : P) {p₂ p₃ p₄ : P} {r : Real} (hr : 0 < r)
  proof: by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_right_of_pos (p₁ -ᵥ p₂) (p₄ -ᵥ p₂) hr

中文:
定理 angle_smul_right_of_pos
  结论: (p₁ : P) {p₂ p₃ p₄ : P} {r : 实数} (hr : 0 < r)
  证明: by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_right_of_pos (p₁ -ᵥ p₂) (p₄ -ᵥ p₂) hr

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_smul_right_of_pos, angle_smul_right_of_pos
-/
theorem angle_smul_right_of_pos (p₁ : P) {p₂ p₃ p₄ : P} {r : Real} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₃ -ᵥ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_right_of_pos (p₁ -ᵥ p₂) (p₄ -ᵥ p₂) hr

/--
theorem `angle_smul_left_of_pos` / 定理 `angle_smul_left_of_pos`

English:
theorem angle_smul_left_of_pos
  statement: {p₁ p₂ p₄ : P} (p₃ : P) {r : Real} (hr : 0 < r)
  proof: by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_left_of_pos (p₄ -ᵥ p₂) (p₃ -ᵥ p₂) hr

中文:
定理 angle_smul_left_of_pos
  结论: {p₁ p₂ p₄ : P} (p₃ : P) {r : 实数} (hr : 0 < r)
  证明: by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_left_of_pos (p₄ -ᵥ p₂) (p₃ -ᵥ p₂) hr

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_smul_left_of_pos, angle_smul_left_of_pos
-/
theorem angle_smul_left_of_pos {p₁ p₂ p₄ : P} (p₃ : P) {r : Real} (hr : 0 < r)
    (hrv : r • (p₄ -ᵥ p₂) = p₁ -ᵥ p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₂ p₃ := by
  simp only [angle, ← hrv]
  exact InnerProductGeometry.angle_smul_left_of_pos (p₄ -ᵥ p₂) (p₃ -ᵥ p₂) hr

/-- The angle at a point does not depend on the order of the other two
points. -/
nonrec theorem angle_comm (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₁ :=
  angle_comm _ _

/-- The angle at a point is nonnegative. -/
nonrec theorem angle_nonneg (p₁ p₂ p₃ : P) : 0 <= ∠ p₁ p₂ p₃ :=
  angle_nonneg _ _

/-- The angle at a point is at most π. -/
nonrec theorem angle_le_pi (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ <= π :=
  angle_le_pi _ _

/--
lemma `angle_self_left` / 引理 `angle_self_left`

English:
lemma angle_self_left
  given: (p₀ p : P)
  statement: ∠ p₀ p₀ p = π / 2
  proof: by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _

中文:
引理 angle_self_left
  条件: (p₀ p : P)
  结论: ∠ p₀ p₀ p = π / 2
  证明: by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _
-/
@[simp] lemma angle_self_left (p₀ p : P) : ∠ p₀ p₀ p = π / 2 := by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _

/--
lemma `angle_self_right` / 引理 `angle_self_right`

English:
lemma angle_self_right
  given: (p₀ p : P)
  statement: ∠ p p₀ p₀ = π / 2
  proof: by rw [angle_comm, angle_self_left]

中文:
引理 angle_self_right
  条件: (p₀ p : P)
  结论: ∠ p p₀ p₀ = π / 2
  证明: by rw [angle_comm, angle_self_left]
-/
@[simp] lemma angle_self_right (p₀ p : P) : ∠ p p₀ p₀ = π / 2 := by rw [angle_comm, angle_self_left]

/--
theorem `angle_self_of_ne` / 定理 `angle_self_of_ne`

English:
theorem angle_self_of_ne
  given: (h : p != p₀)
  statement: ∠ p p₀ p = 0
  proof: angle_self vsub_ne_zero.2 h

中文:
定理 angle_self_of_ne
  条件: (h : p != p₀)
  结论: ∠ p p₀ p = 0
  证明: angle_self vsub_ne_zero.2 h

Depends on / 依赖: angle_self, vsub_ne_zero
-/
theorem angle_self_of_ne (h : p != p₀) : ∠ p p₀ p = 0 := angle_self vsub_ne_zero.2 h


/--
theorem `angle_eq_zero_of_angle_eq_pi_left` / 定理 `angle_eq_zero_of_angle_eq_pi_left`

English:
theorem angle_eq_zero_of_angle_eq_pi_left
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  statement: ∠ p₂ p₁ p₃ = 0
  proof: by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp₁p₂, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev]; rw [neg_ne_zero] at hp₁p₂
  use hp₁p₂, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₁ p₂];

中文:
定理 angle_eq_zero_of_angle_eq_pi_left
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  结论: ∠ p₂ p₁ p₃ = 0
  证明: by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp₁p₂, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev]; rw [neg_ne_zero] at hp₁p₂
  use hp₁p₂, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₁ p₂];

Depends on / 依赖: add_pos, add_smul, angle_eq_pi_iff, angle_eq_zero_iff, neg_ne_zero, neg_pos_of_neg, neg_vsub_eq_vsub_rev, smul_neg, zero_lt_one
-/
theorem angle_eq_zero_of_angle_eq_pi_left {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : ∠ p₂ p₁ p₃ = 0 := by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp₁p₂, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev]; rw [neg_ne_zero] at hp₁p₂
  use hp₁p₂, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₁ p₂]; rw [smul_neg]
  simp [← hpr]

/--
theorem `angle_eq_zero_of_angle_eq_pi_right` / 定理 `angle_eq_zero_of_angle_eq_pi_right`

English:
theorem angle_eq_zero_of_angle_eq_pi_right
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  proof: by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

中文:
定理 angle_eq_zero_of_angle_eq_pi_right
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  证明: by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

Depends on / 依赖: angle_comm, angle_eq_zero_of_angle_eq_pi_left
-/
theorem angle_eq_zero_of_angle_eq_pi_right {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    ∠ p₂ p₃ p₁ = 0 := by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

/--
theorem `angle_eq_angle_of_angle_eq_pi` / 定理 `angle_eq_angle_of_angle_eq_pi`

English:
theorem angle_eq_angle_of_angle_eq_pi
  given: (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π)
  proof: by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  replace hpr : (-r + 1) • (p₃ -ᵥ p₂) = p₄ -ᵥ p₂ := by
    rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [smul_neg]; rw [neg_smul]; rw [← hpr]
    simp
  replace hr : 0 < -r + 1 := by linarith
  exact 

中文:
定理 angle_eq_angle_of_angle_eq_pi
  条件: (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π)
  证明: by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  replace hpr : (-r + 1) • (p₃ -ᵥ p₂) = p₄ -ᵥ p₂ := by
    rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [smul_neg]; rw [neg_smul]; rw [← hpr]
    simp
  replace hr : 0 < -r + 1 := by linarith
  exact 

Depends on / 依赖: add_smul, angle_eq_pi_iff, angle_smul_right_of_pos, eq_comm, neg_smul, neg_vsub_eq_vsub_rev, replace, smul_neg
-/
theorem angle_eq_angle_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ := by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨_, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  replace hpr : (-r + 1) • (p₃ -ᵥ p₂) = p₄ -ᵥ p₂ := by
    rw [add_smul]; rw [← neg_vsub_eq_vsub_rev p₂ p₃]; rw [smul_neg]; rw [neg_smul]; rw [← hpr]
    simp
  replace hr : 0 < -r + 1 := by linarith
  exact angle_smul_right_of_pos p₁ hr hpr

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
nonrec theorem angle_add_angle_eq_pi_of_angle_eq_pi (p₁ : P) {p₂ p₃ p₄ : P} (h : ∠ p₂ p₃ p₄ = π) :
    ∠ p₁ p₃ p₂ + ∠ p₁ p₃ p₄ = π := by
  unfold angle at h
  rw [angle_comm p₁ p₃ p₂]; rw [angle_comm p₁ p₃ p₄]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h

/--
theorem `angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi` / 定理 `angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi`

English:
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi
  statement: {p₁ p₂ p₃ p₄ p₅ : P} (hapc : ∠ p₁ p₅ p₃ = π)
  proof: by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₁ hbpd, angle_comm p₄ p₅ p₁,
    angle_add_angle_eq_pi_of_angle_eq_pi p₄ hapc, angle_comm p₄ p₅ p₃]

中文:
定理 angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi
  结论: {p₁ p₂ p₃ p₄ p₅ : P} (hapc : ∠ p₁ p₅ p₃ = π)
  证明: by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₁ hbpd, angle_comm p₄ p₅ p₁,
    angle_add_angle_eq_pi_of_angle_eq_pi p₄ hapc, angle_comm p₄ p₅ p₃]

Depends on / 依赖: angle_add_angle_eq_pi_of_angle_eq_pi, angle_comm
-/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p₁ p₂ p₃ p₄ p₅ : P} (hapc : ∠ p₁ p₅ p₃ = π)
    (hbpd : ∠ p₂ p₅ p₄ = π) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₁ hbpd, angle_comm p₄ p₅ p₁,
    angle_add_angle_eq_pi_of_angle_eq_pi p₄ hapc, angle_comm p₄ p₅ p₃]

/--
theorem `left_dist_ne_zero_of_angle_eq_pi` / 定理 `left_dist_ne_zero_of_angle_eq_pi`

English:
theorem left_dist_ne_zero_of_angle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  statement: dist p₁ p₂ != 0
  proof: by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [heq]; rw [angle_self_left] at h
  exact Real.pi_ne_zero (by linarith)

中文:
定理 left_dist_ne_zero_of_angle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  结论: dist p₁ p₂ != 0
  证明: by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [heq]; rw [angle_self_left] at h
  exact Real.pi_ne_zero (by linarith)

Depends on / 依赖: Real.pi_ne_zero, angle_self_left, dist_eq_zero, pi_ne_zero
-/
theorem left_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₁ p₂ != 0 := by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [heq]; rw [angle_self_left] at h
  exact Real.pi_ne_zero (by linarith)

/--
theorem `right_dist_ne_zero_of_angle_eq_pi` / 定理 `right_dist_ne_zero_of_angle_eq_pi`

English:
theorem right_dist_ne_zero_of_angle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  statement: dist p₃ p₂ != 0
  proof: left_dist_ne_zero_of_angle_eq_pi (angle_comm _ _ _).trans h

中文:
定理 right_dist_ne_zero_of_angle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  结论: dist p₃ p₂ != 0
  证明: left_dist_ne_zero_of_angle_eq_pi (angle_comm _ _ _).trans h

Depends on / 依赖: angle_comm, left_dist_ne_zero_of_angle_eq_pi
-/
theorem right_dist_ne_zero_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) : dist p₃ p₂ != 0 :=
left_dist_ne_zero_of_angle_eq_pi (angle_comm _ _ _).trans h

/--
theorem `dist_eq_add_dist_of_angle_eq_pi` / 定理 `dist_eq_add_dist_of_angle_eq_pi`

English:
theorem dist_eq_add_dist_of_angle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

中文:
定理 dist_eq_add_dist_of_angle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

Depends on / 依赖: dist_eq_norm_vsub, norm_sub_eq_add_norm_of_angle_eq_pi, vsub_sub_vsub_cancel_right
-/
theorem dist_eq_add_dist_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

/--
theorem `dist_eq_add_dist_iff_angle_eq_pi` / 定理 `dist_eq_add_dist_iff_angle_eq_pi`

English:
theorem dist_eq_add_dist_iff_angle_eq_pi
  given: {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂)
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

中文:
定理 dist_eq_add_dist_iff_angle_eq_pi
  条件: {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂)
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

Depends on / 依赖: dist_eq_norm_vsub, norm_sub_eq_add_norm_iff_angle_eq_pi, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right
-/
theorem dist_eq_add_dist_iff_angle_eq_pi {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂) :
    dist p₁ p₃ = dist p₁ p₂ + dist p₃ p₂ ↔ ∠ p₁ p₂ p₃ = π := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

/--
theorem `dist_eq_abs_sub_dist_of_angle_eq_zero` / 定理 `dist_eq_abs_sub_dist_of_angle_eq_zero`

English:
theorem dist_eq_abs_sub_dist_of_angle_eq_zero
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0)
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

中文:
定理 dist_eq_abs_sub_dist_of_angle_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0)
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

Depends on / 依赖: dist_eq_norm_vsub, norm_sub_eq_abs_sub_norm_of_angle_eq_zero, vsub_sub_vsub_cancel_right
-/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

/--
theorem `dist_eq_abs_sub_dist_iff_angle_eq_zero` / 定理 `dist_eq_abs_sub_dist_iff_angle_eq_zero`

English:
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero
  given: {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂)
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he))
      fun he => hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

中文:
定理 dist_eq_abs_sub_dist_iff_angle_eq_zero
  条件: {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂)
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he))
      fun he => hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

Depends on / 依赖: dist_eq_norm_vsub, norm_sub_eq_abs_sub_norm_iff_angle_eq_zero, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right
-/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₃p₂ : p₃ != p₂) :
    dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂| ↔ ∠ p₁ p₂ p₃ = 0 := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]; rw [← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp₁p₂ (vsub_eq_zero_iff_eq.1 he))
      fun he => hp₃p₂ (vsub_eq_zero_iff_eq.1 he)

/--
theorem `angle_midpoint_eq_pi` / 定理 `angle_midpoint_eq_pi`

English:
theorem angle_midpoint_eq_pi
  given: (p₁ p₂ : P) (hp₁p₂ : p₁ != p₂)
  statement: ∠ p₁ (midpoint Real p₁ p₂) p₂ = π
  proof: by
  suffices dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) + dist (midpoint Real p₁ p₂) p₂ by
    rwa [← dist_eq_add_dist_iff_angle_eq_pi (by simpa) (by simpa), dist_comm p₂]
  simp [dist_eq_norm_vsub V, left_vsub_midpoint, midpoint_vsub_right, norm_smul, ← two_mul]

中文:
定理 angle_midpoint_eq_pi
  条件: (p₁ p₂ : P) (hp₁p₂ : p₁ != p₂)
  结论: ∠ p₁ (midpoint 实数 p₁ p₂) p₂ = π
  证明: by
  suffices dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) + dist (midpoint Real p₁ p₂) p₂ by
    rwa [← dist_eq_add_dist_iff_angle_eq_pi (by simpa) (by simpa), dist_comm p₂]
  simp [dist_eq_norm_vsub V, left_vsub_midpoint, midpoint_vsub_right, norm_smul, ← two_mul]

Depends on / 依赖: dist_comm, dist_eq_add_dist_iff_angle_eq_pi, dist_eq_norm_vsub, left_vsub_midpoint, midpoint, midpoint_vsub_right, norm_smul, two_mul
-/
theorem angle_midpoint_eq_pi (p₁ p₂ : P) (hp₁p₂ : p₁ != p₂) : ∠ p₁ (midpoint Real p₁ p₂) p₂ = π := by
  suffices dist p₁ p₂ = dist p₁ (midpoint Real p₁ p₂) + dist (midpoint Real p₁ p₂) p₂ by
    rwa [← dist_eq_add_dist_iff_angle_eq_pi (by simpa) (by simpa), dist_comm p₂]
  simp [dist_eq_norm_vsub V, left_vsub_midpoint, midpoint_vsub_right, norm_smul, ← two_mul]

/--
theorem `angle_left_midpoint_eq_pi_div_two_of_dist_eq` / 定理 `angle_left_midpoint_eq_pi_div_two_of_dist_eq`

English:
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq
  given: {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂)
  proof: by
  let m : P := midpoint Real p₁ p₂
  have h1 : p₃ -ᵥ p₁ = p₃ -ᵥ m - (p₁ -ᵥ m) := (vsub_sub_vsub_cancel_right p₃ p₁ m).symm
  have h2 : p₃ -ᵥ p₂ = p₃ -ᵥ m + (p₁ -ᵥ m) := by
    rw [left_vsub_midpoint]; rw [← midpoint_vsub_right]; rw [vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p₃ p₁]; rw [dist

中文:
定理 angle_left_midpoint_eq_pi_div_two_of_dist_eq
  条件: {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂)
  证明: by
  let m : P := midpoint Real p₁ p₂
  have h1 : p₃ -ᵥ p₁ = p₃ -ᵥ m - (p₁ -ᵥ m) := (vsub_sub_vsub_cancel_right p₃ p₁ m).symm
  have h2 : p₃ -ᵥ p₂ = p₃ -ᵥ m + (p₁ -ᵥ m) := by
    rw [left_vsub_midpoint]; rw [← midpoint_vsub_right]; rw [vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p₃ p₁]; rw [dist

Depends on / 依赖: dist_eq_norm_vsub, h.symm, left_vsub_midpoint, midpoint, midpoint_vsub_right, norm_add_eq_norm_sub_iff_angle_eq_pi_div_two, vsub_add_vsub_cancel, vsub_sub_vsub_cancel_right
-/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂) :
    ∠ p₃ (midpoint Real p₁ p₂) p₁ = π / 2 := by
  let m : P := midpoint Real p₁ p₂
  have h1 : p₃ -ᵥ p₁ = p₃ -ᵥ m - (p₁ -ᵥ m) := (vsub_sub_vsub_cancel_right p₃ p₁ m).symm
  have h2 : p₃ -ᵥ p₂ = p₃ -ᵥ m + (p₁ -ᵥ m) := by
    rw [left_vsub_midpoint]; rw [← midpoint_vsub_right]; rw [vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p₃ p₁]; rw [dist_eq_norm_vsub V p₃ p₂]; rw [h1]; rw [h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p₃ -ᵥ m) (p₁ -ᵥ m)).mp h.symm

/--
theorem `angle_right_midpoint_eq_pi_div_two_of_dist_eq` / 定理 `angle_right_midpoint_eq_pi_div_two_of_dist_eq`

English:
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq
  given: {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂)
  proof: by
  rw [midpoint_comm p₁ p₂]; rw [angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

中文:
定理 angle_right_midpoint_eq_pi_div_two_of_dist_eq
  条件: {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂)
  证明: by
  rw [midpoint_comm p₁ p₂]; rw [angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

Depends on / 依赖: angle_left_midpoint_eq_pi_div_two_of_dist_eq, h.symm, midpoint_comm
-/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₃ p₁ = dist p₃ p₂) :
    ∠ p₃ (midpoint Real p₁ p₂) p₂ = π / 2 := by
  rw [midpoint_comm p₁ p₂]; rw [angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

/--
theorem `_root_.Sbtw.angle₁₂₃_eq_pi` / 定理 `_root_.Sbtw.angle₁₂₃_eq_pi`

English:
theorem _root_.Sbtw.angle₁₂₃_eq_pi
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₁ p₂ p₃ = π
  proof: by
  rw [angle]; rw [angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, ?_⟩
  have hr0' : r != 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r != 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    

中文:
定理 _root_.Sbtw.angle₁₂₃_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₁ p₂ p₃ = π
  证明: by
  rw [angle]; rw [angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, ?_⟩
  have hr0' : r != 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r != 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, Left.neg_neg_iff, angle_eq_pi_iff, div_neg_of_neg_of_pos, hr0.lt_of_ne, hr1.lt_of_ne, lineMap_apply, lt_of_ne, neg_neg_iff, replace, sub_pos, vsub_ne_zero, vsub_vadd_eq_vsub_sub
-/
theorem _root_.Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π := by
  rw [angle]; rw [angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, ?_⟩
  have hr0' : r != 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simp at hp₂p₁
  have hr1' : r != 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simp at hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  replace hr1 := hr1.lt_of_ne hr1'
  refine ⟨div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, ?_⟩
  rw [← hp₂]; rw [AffineMap.lineMap_apply]; rw [vsub_vadd_eq_vsub_sub]; rw [vsub_vadd_eq_vsub_sub]; rw [vsub_self]; rw [zero_sub]; rw [smul_neg]; rw [smul_smul]; rw [div_mul_cancel₀ _ hr0']; rw [neg_smul]; rw [neg_neg]; rw [sub_eq_iff_eq_add]; rw [←
    add_smul]; rw [sub_add_cancel]; rw [one_smul]

/--
theorem `_root_.Sbtw.angle₃₂₁_eq_pi` / 定理 `_root_.Sbtw.angle₃₂₁_eq_pi`

English:
theorem _root_.Sbtw.angle₃₂₁_eq_pi
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₃ p₂ p₁ = π
  proof: by
  rw [← h.angle₁₂₃_eq_pi]; rw [angle_comm]

中文:
定理 _root_.Sbtw.angle₃₂₁_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₃ p₂ p₁ = π
  证明: by
  rw [← h.angle₁₂₃_eq_pi]; rw [angle_comm]

Depends on / 依赖: angle_comm, h.angle
-/
theorem _root_.Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π := by
  rw [← h.angle₁₂₃_eq_pi]; rw [angle_comm]

/--
theorem `angle_eq_pi_iff_sbtw` / 定理 `angle_eq_pi_iff_sbtw`

English:
theorem angle_eq_pi_iff_sbtw
  given: {p₁ p₂ p₃ : P}
  statement: ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
  proof: by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle]; rw [angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub

中文:
定理 angle_eq_pi_iff_sbtw
  条件: {p₁ p₂ p₃ : P}
  结论: ∠ p₁ p₂ p₃ = π ↔ Sbtw 实数 p₁ p₂ p₃
  证明: by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle]; rw [angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, angle_eq_pi_iff, div_le_one, div_nonneg, eq_vadd_iff_vsub_eq, h.angle, hr.le, hr.le.trans, hr.trans, le_sub_self_iff, lineMap_apply, neg_smul, neg_vsub_eq_vsub_rev, smul_add, smul_neg, sub_nonneg, sub_pos, vadd_vsub_assoc, vsub_ne_zero
-/
theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃ := by
  refine ⟨?_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle]; rw [angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine ⟨⟨1 / (1 - r), ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
    (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, ?_⟩,
    (vsub_ne_zero.1 hp₁p₂).symm, ?_⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    rw [AffineMap.lineMap_apply]; rw [hp₃p₂]; rw [vadd_vsub_assoc]; rw [← neg_vsub_eq_vsub_rev p₂ p₁]; rw [smul_neg]; rw [←
      neg_smul]; rw [smul_add]; rw [smul_smul]; rw [← add_smul]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]
    convert! (one_smul Real (p₂ -ᵥ p₁)).symm
    field [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm]
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    exact ⟨hr.ne, hp₁p₂⟩

/--
theorem `_root_.Wbtw.angle₂₁₃_eq_zero_of_ne` / 定理 `_root_.Wbtw.angle₂₁₃_eq_zero_of_ne`

English:
theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁)
  proof: by
  rw [angle]; rw [angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r != 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_self

中文:
定理 _root_.Wbtw.angle₂₁₃_eq_zero_of_ne
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁)
  证明: by
  rw [angle]; rw [angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r != 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_self

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, add_zero, angle_eq_zero_iff, hr0.lt_of_ne, inv_pos, lineMap_apply, lt_of_ne, one_smul, replace, smul_smul, vadd_vsub_assoc, vsub_ne_zero, vsub_self
-/
theorem _root_.Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁) :
    ∠ p₂ p₁ p₃ = 0 := by
  rw [angle]; rw [angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r != 0 := by
    rintro rfl
    simp at hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, ?_⟩
  rw [AffineMap.lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_self]; rw [add_zero]; rw [smul_smul]; rw [inv_mul_cancel₀ hr0']; rw [one_smul]

/--
theorem `_root_.Sbtw.angle₂₁₃_eq_zero` / 定理 `_root_.Sbtw.angle₂₁₃_eq_zero`

English:
theorem _root_.Sbtw.angle₂₁₃_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₂ p₁ p₃ = 0
  proof: h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

中文:
定理 _root_.Sbtw.angle₂₁₃_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₂ p₁ p₃ = 0
  证明: h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

Depends on / 依赖: h.ne_left, h.wbtw.angle, ne_left
-/
theorem _root_.Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
  h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

/--
theorem `_root_.Wbtw.angle₃₁₂_eq_zero_of_ne` / 定理 `_root_.Wbtw.angle₃₁₂_eq_zero_of_ne`

English:
theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁)
  proof: by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

中文:
定理 _root_.Wbtw.angle₃₁₂_eq_zero_of_ne
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁)
  证明: by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

Depends on / 依赖: angle_comm, h.angle
-/
theorem _root_.Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₁ : p₂ != p₁) :
    ∠ p₃ p₁ p₂ = 0 := by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

/--
theorem `_root_.Sbtw.angle₃₁₂_eq_zero` / 定理 `_root_.Sbtw.angle₃₁₂_eq_zero`

English:
theorem _root_.Sbtw.angle₃₁₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₃ p₁ p₂ = 0
  proof: h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

中文:
定理 _root_.Sbtw.angle₃₁₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₃ p₁ p₂ = 0
  证明: h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

Depends on / 依赖: h.ne_left, h.wbtw.angle, ne_left
-/
theorem _root_.Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
  h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

/--
theorem `_root_.Wbtw.angle₂₃₁_eq_zero_of_ne` / 定理 `_root_.Wbtw.angle₂₃₁_eq_zero_of_ne`

English:
theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃)
  proof: h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

中文:
定理 _root_.Wbtw.angle₂₃₁_eq_zero_of_ne
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃)
  证明: h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

Depends on / 依赖: h.symm.angle
-/
theorem _root_.Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃) :
    ∠ p₂ p₃ p₁ = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

/--
theorem `_root_.Sbtw.angle₂₃₁_eq_zero` / 定理 `_root_.Sbtw.angle₂₃₁_eq_zero`

English:
theorem _root_.Sbtw.angle₂₃₁_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₂ p₃ p₁ = 0
  proof: h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

中文:
定理 _root_.Sbtw.angle₂₃₁_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₂ p₃ p₁ = 0
  证明: h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

Depends on / 依赖: h.ne_right, h.wbtw.angle, ne_right
-/
theorem _root_.Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
  h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

/--
theorem `_root_.Wbtw.angle₁₃₂_eq_zero_of_ne` / 定理 `_root_.Wbtw.angle₁₃₂_eq_zero_of_ne`

English:
theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃)
  proof: h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

中文:
定理 _root_.Wbtw.angle₁₃₂_eq_zero_of_ne
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃)
  证明: h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

Depends on / 依赖: h.symm.angle
-/
theorem _root_.Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) (hp₂p₃ : p₂ != p₃) :
    ∠ p₁ p₃ p₂ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

/--
theorem `_root_.Sbtw.angle₁₃₂_eq_zero` / 定理 `_root_.Sbtw.angle₁₃₂_eq_zero`

English:
theorem _root_.Sbtw.angle₁₃₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∠ p₁ p₃ p₂ = 0
  proof: h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

中文:
定理 _root_.Sbtw.angle₁₃₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∠ p₁ p₃ p₂ = 0
  证明: h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

Depends on / 依赖: h.ne_right, h.wbtw.angle, ne_right
-/
theorem _root_.Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
  h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

/--
theorem `angle_eq_zero_iff_ne_and_wbtw` / 定理 `angle_eq_zero_iff_ne_and_wbtw`

English:
theorem angle_eq_zero_iff_ne_and_wbtw
  given: {p₁ p₂ p₃ : P}
  proof: by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_gt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply]; rw [hp₃p₂]; rw [smul_smul]; rw [inv_m

中文:
定理 angle_eq_zero_iff_ne_and_wbtw
  条件: {p₁ p₂ p₃ : P}
  证明: by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_gt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply]; rw [hp₃p₂]; rw [smul_smul]; rw [inv_m

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, Or.inl, Or.inr, angle_eq_zero_iff, hr0.le, hr0.ne.symm, hr1.le, inv_pos, le_or_gt, lineMap_apply, one_smul, smul_ne_zero_iff, smul_smul, vsub_ne_zero, vsub_vadd
-/
theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ != p₂ ∧ Wbtw Real p₂ p₁ p₃ ∨ p₃ != p₂ ∧ Wbtw Real p₂ p₃ p₁ := by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_gt 1 r with (hr1 | hr1)
    · refine Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one_of_one_le₀ hr1⟩, ?_⟩
      rw [AffineMap.lineMap_apply]; rw [hp₃p₂]; rw [smul_smul]; rw [inv_mul_cancel₀ hr0.ne.symm]; rw [one_smul]; rw [vsub_vadd]
    · refine Or.inr ⟨?_, r, ⟨hr0.le, hr1.le⟩, ?_⟩
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        exact ⟨hr0.ne.symm, hp₁p₂⟩
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂

/--
theorem `angle_eq_zero_iff_eq_and_ne_or_sbtw` / 定理 `angle_eq_zero_iff_eq_and_ne_or_sbtw`

English:
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

中文:
定理 angle_eq_zero_iff_eq_and_ne_or_sbtw
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

Depends on / 依赖: Ne.symm, angle_eq_zero_iff_ne_and_wbtw
-/
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ != p₂ ∨ Sbtw Real p₂ p₁ p₃ ∨ Sbtw Real p₂ p₃ p₁ := by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]

/--
theorem `_root_.Sbtw.angle_eq_right` / 定理 `_root_.Sbtw.angle_eq_right`

English:
theorem _root_.Sbtw.angle_eq_right
  given: {p₂ p₃ p : P} (p₁ : P) (h : Sbtw Real p₂ p₃ p)
  proof: angle_eq_angle_of_angle_eq_pi _ h.angle₁₂₃_eq_pi

中文:
定理 _root_.Sbtw.angle_eq_right
  条件: {p₂ p₃ p : P} (p₁ : P) (h : Sbtw 实数 p₂ p₃ p)
  证明: angle_eq_angle_of_angle_eq_pi _ h.angle₁₂₃_eq_pi

Depends on / 依赖: angle_eq_angle_of_angle_eq_pi, h.angle
-/
theorem _root_.Sbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) (h : Sbtw Real p₂ p₃ p) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p :=
  angle_eq_angle_of_angle_eq_pi _ h.angle₁₂₃_eq_pi

/--
theorem `_root_.Sbtw.angle_eq_left` / 定理 `_root_.Sbtw.angle_eq_left`

English:
theorem _root_.Sbtw.angle_eq_left
  given: {p₁ p p₂ : P} (p₃ : P) (h : Sbtw Real p₂ p₁ p)
  proof: by
  simpa only [angle_comm] using h.angle_eq_right p₃

中文:
定理 _root_.Sbtw.angle_eq_left
  条件: {p₁ p p₂ : P} (p₃ : P) (h : Sbtw 实数 p₂ p₁ p)
  证明: by
  simpa only [angle_comm] using h.angle_eq_right p₃

Depends on / 依赖: angle_comm, angle_eq_right, h.angle_eq_right
-/
theorem _root_.Sbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) (h : Sbtw Real p₂ p₁ p) :
    ∠ p₁ p₂ p₃ = ∠ p p₂ p₃ := by
  simpa only [angle_comm] using h.angle_eq_right p₃

/--
theorem `_root_.Wbtw.angle_eq_right` / 定理 `_root_.Wbtw.angle_eq_right`

English:
theorem _root_.Wbtw.angle_eq_right
  given: {p₂ p₃ p : P} (p₁ : P) (h : Wbtw Real p₂ p₃ p) (hp₃p₂ : p₃ != p₂)
  proof: by
  by_cases hp₃p : p₃ = p; · simp [hp₃p]
  exact Sbtw.angle_eq_right _ ⟨h, hp₃p₂, hp₃p⟩

中文:
定理 _root_.Wbtw.angle_eq_right
  条件: {p₂ p₃ p : P} (p₁ : P) (h : Wbtw 实数 p₂ p₃ p) (hp₃p₂ : p₃ != p₂)
  证明: by
  by_cases hp₃p : p₃ = p; · simp [hp₃p]
  exact Sbtw.angle_eq_right _ ⟨h, hp₃p₂, hp₃p⟩

Depends on / 依赖: Sbtw.angle_eq_right, angle_eq_right
-/
theorem _root_.Wbtw.angle_eq_right {p₂ p₃ p : P} (p₁ : P) (h : Wbtw Real p₂ p₃ p) (hp₃p₂ : p₃ != p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p := by
  by_cases hp₃p : p₃ = p; · simp [hp₃p]
  exact Sbtw.angle_eq_right _ ⟨h, hp₃p₂, hp₃p⟩

/--
theorem `_root_.Wbtw.angle_eq_left` / 定理 `_root_.Wbtw.angle_eq_left`

English:
theorem _root_.Wbtw.angle_eq_left
  given: {p₁ p p₂ : P} (p₃ : P) (h : Wbtw Real p₂ p₁ p) (hp₁p₂ : p₁ != p₂)
  proof: by
  simpa only [angle_comm] using h.angle_eq_right p₃ hp₁p₂

中文:
定理 _root_.Wbtw.angle_eq_left
  条件: {p₁ p p₂ : P} (p₃ : P) (h : Wbtw 实数 p₂ p₁ p) (hp₁p₂ : p₁ != p₂)
  证明: by
  simpa only [angle_comm] using h.angle_eq_right p₃ hp₁p₂

Depends on / 依赖: angle_comm, angle_eq_right, h.angle_eq_right
-/
theorem _root_.Wbtw.angle_eq_left {p₁ p p₂ : P} (p₃ : P) (h : Wbtw Real p₂ p₁ p) (hp₁p₂ : p₁ != p₂) :
    ∠ p₁ p₂ p₃ = ∠ p p₂ p₃ := by
  simpa only [angle_comm] using h.angle_eq_right p₃ hp₁p₂

/--
lemma `angle_pointReflection_right` / 引理 `angle_pointReflection_right`

English:
lemma angle_pointReflection_right
  given: {p₁ p₂ p₃ : P}
  proof: by
  by_cases! h₃₂ : p₃ = p₂
  · simp [h₃₂]
    field
  rw [eq_sub_iff_add_eq]
  apply EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
exact Sbtw.angle₁₂₃_eq_pi (sbtw_pointReflection_of_ne Real h₃₂.symm).symm

中文:
引理 angle_pointReflection_right
  条件: {p₁ p₂ p₃ : P}
  证明: by
  by_cases! h₃₂ : p₃ = p₂
  · simp [h₃₂]
    field
  rw [eq_sub_iff_add_eq]
  apply EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
exact Sbtw.angle₁₂₃_eq_pi (sbtw_pointReflection_of_ne Real h₃₂.symm).symm

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi, Sbtw.angle, angle_add_angle_eq_pi_of_angle_eq_pi, eq_sub_iff_add_eq, sbtw_pointReflection_of_ne
-/
lemma angle_pointReflection_right {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = π - ∠ p₁ p₂ p₃ := by
  by_cases! h₃₂ : p₃ = p₂
  · simp [h₃₂]
    field
  rw [eq_sub_iff_add_eq]
  apply EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
exact Sbtw.angle₁₂₃_eq_pi (sbtw_pointReflection_of_ne Real h₃₂.symm).symm

/--
theorem `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` / 定理 `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`

English:
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
  given: {p₁ p₂ p₃ : P}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂]; rw [or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_i

中文:
定理 collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
  条件: {p₁ p₂ p₃ : P}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂]; rw [or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_i

Depends on / 依赖: Ne.symm, Or.inl, Or.inr, angle_eq_pi_iff_sbtw, collinear, collinear_pair, h.angle, h.wbtw_or_wbtw_or_wbtw, or_iff_right, replace, wbtw_or_wbtw_or_wbtw
-/
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂]; rw [or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
  · rcases h with (rfl | rfl | h | h)
    · simpa using collinear_pair Real p₁ p₃
    · simpa using collinear_pair Real p₁ p₃
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      · rw [Set.insert_comm]
        exact h.collinear
      · rw [Set.insert_comm, Set.pair_comm]
        exact h.collinear
    · rw [angle_eq_pi_iff_sbtw] at h
      exact h.wbtw.collinear

/--
theorem `collinear_of_angle_eq_zero` / 定理 `collinear_of_angle_eq_zero`

English:
theorem collinear_of_angle_eq_zero
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0)
  proof: collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inl h

中文:
定理 collinear_of_angle_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0)
  证明: collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inl h

Depends on / 依赖: Or.inl, Or.inr, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
-/
theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear Real ({p₁, p₂, p₃} : Set P) :=
collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inl h

/--
theorem `collinear_of_angle_eq_pi` / 定理 `collinear_of_angle_eq_pi`

English:
theorem collinear_of_angle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  proof: collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inr h

中文:
定理 collinear_of_angle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π)
  证明: collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inr h

Depends on / 依赖: Or.inr, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi
-/
theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    Collinear Real ({p₁, p₂, p₃} : Set P) :=
collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 Or.inr Or.inr Or.inr h

/--
theorem `angle_ne_zero_of_not_collinear` / 定理 `angle_ne_zero_of_not_collinear`

English:
theorem angle_ne_zero_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: mt collinear_of_angle_eq_zero h

中文:
定理 angle_ne_zero_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: mt collinear_of_angle_eq_zero h

Depends on / 依赖: collinear_of_angle_eq_zero
-/
theorem angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ != 0 :=
  mt collinear_of_angle_eq_zero h

/--
theorem `angle_ne_pi_of_not_collinear` / 定理 `angle_ne_pi_of_not_collinear`

English:
theorem angle_ne_pi_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: mt collinear_of_angle_eq_pi h

中文:
定理 angle_ne_pi_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: mt collinear_of_angle_eq_pi h

Depends on / 依赖: collinear_of_angle_eq_pi
-/
theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ != π :=
  mt collinear_of_angle_eq_pi h

/--
theorem `angle_pos_of_not_collinear` / 定理 `angle_pos_of_not_collinear`

English:
theorem angle_pos_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

中文:
定理 angle_pos_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

Depends on / 依赖: angle_ne_zero_of_not_collinear, angle_nonneg, lt_of_ne
-/
theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    0 < ∠ p₁ p₂ p₃ :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm

/--
theorem `angle_lt_pi_of_not_collinear` / 定理 `angle_lt_pi_of_not_collinear`

English:
theorem angle_lt_pi_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: (angle_le_pi _ _ _).lt_of_ne angle_ne_pi_of_not_collinear h

中文:
定理 angle_lt_pi_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: (angle_le_pi _ _ _).lt_of_ne angle_ne_pi_of_not_collinear h

Depends on / 依赖: angle_le_pi, angle_ne_pi_of_not_collinear, lt_of_ne
-/
theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ < π :=
(angle_le_pi _ _ _).lt_of_ne angle_ne_pi_of_not_collinear h

/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
nonrec theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero

/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
nonrec theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two

/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
nonrec theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi

/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
nonrec theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
nonrec theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two

/--
theorem `collinear_iff_eq_or_eq_or_sin_eq_zero` / 定理 `collinear_iff_eq_or_eq_or_sin_eq_zero`

English:
theorem collinear_iff_eq_or_eq_or_sin_eq_zero
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]; rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

中文:
定理 collinear_iff_eq_or_eq_or_sin_eq_zero
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]; rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

Depends on / 依赖: collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi
-/
theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear Real ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0 := by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi]; rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]

/--
theorem `sin_pos_of_not_collinear` / 定理 `sin_pos_of_not_collinear`

English:
theorem sin_pos_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

中文:
定理 sin_pos_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

Depends on / 依赖: Real.sin_pos_of_pos_of_lt_pi, angle_lt_pi_of_not_collinear, angle_pos_of_not_collinear, sin_pos_of_pos_of_lt_pi
-/
theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (∠ p₁ p₂ p₃) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)

/--
theorem `sin_ne_zero_of_not_collinear` / 定理 `sin_ne_zero_of_not_collinear`

English:
theorem sin_ne_zero_of_not_collinear
  given: {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P))
  proof: ne_of_gt (sin_pos_of_not_collinear h)

中文:
定理 sin_ne_zero_of_not_collinear
  条件: {p₁ p₂ p₃ : P} (h : ¬Collinear 实数 ({p₁, p₂, p₃} : Set P))
  证明: ne_of_gt (sin_pos_of_not_collinear h)

Depends on / 依赖: ne_of_gt, sin_pos_of_not_collinear
-/
theorem sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    Real.sin (∠ p₁ p₂ p₃) != 0 :=
  ne_of_gt (sin_pos_of_not_collinear h)

/--
theorem `collinear_of_sin_eq_zero` / 定理 `collinear_of_sin_eq_zero`

English:
theorem collinear_of_sin_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0)
  proof: by
  revert h
  contrapose
  exact sin_ne_zero_of_not_collinear

中文:
定理 collinear_of_sin_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : 实数.sin (∠ p₁ p₂ p₃) = 0)
  证明: by
  revert h
  contrapose
  exact sin_ne_zero_of_not_collinear

Depends on / 依赖: contrapose, revert, sin_ne_zero_of_not_collinear
-/
theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) :
    Collinear Real ({p₁, p₂, p₃} : Set P) := by
  revert h
  contrapose
  exact sin_ne_zero_of_not_collinear

end EuclideanGeometry
