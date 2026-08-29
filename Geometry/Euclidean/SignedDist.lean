/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between two points, in the direction of a given vector, and
the signed distance between an affine subspace and a point, in the direction of a given
reference point.

## Main definitions

* `signedDist` is the signed distance between two points
* `AffineSubspace.signedInfDist` is the signed distance between an affine subspace and a point.
* `Affine.Simplex.signedInfDist` is the signed distance between a face of a simplex and a point.
  In the case of a triangle, these distances are trilinear coordinates.

## References

* https://en.wikipedia.org/wiki/Trilinear_coordinates

-/

@[expose] public section


open EuclideanGeometry NormedSpace
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
variable [NormedAddTorsor V P]

section signedDist

/--
Definition of `signedDist` / `signedDist` 的定义

English:
definition signedDist
  signature: (v : V)
  body: (innerSL Real (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id Real P -ᵥ .const Real P p)
  linear := {
    toFun w := .const Real P ⟪-normalize v, w⟫
    map_add' x y := by ext; simp [inner_add_right]
    map_smul' r x := by ext; simp [inner_smul_right] }
  map_vadd' p v' := by
    ext q
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

中文:
定义 signedDist
  签名: (v : V)
  定义体: (innerSL Real (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id Real P -ᵥ .const Real P p)
  linear := {
    toFun w := .const Real P ⟪-normalize v, w⟫
    map_add' x y := by ext; simp [inner_add_right]
    map_smul' r x := by ext; simp [inner_smul_right] }
  map_vadd' p v' := by
    ext q
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

Depends on / 依赖: innerSL, normalize, toContinuousAffineMap, toContinuousAffineMap.comp
-/
noncomputable def signedDist (v : V) : P ->ᵃ[Real] P ->ᴬ[Real] Real where
  toFun p := (innerSL Real (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id Real P -ᵥ .const Real P p)
  linear := {
    toFun w := .const Real P ⟪-normalize v, w⟫
    map_add' x y := by ext; simp [inner_add_right]
    map_smul' r x := by ext; simp [inner_smul_right] }
  map_vadd' p v' := by
    ext q
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

variable (v w : V) (p q r : P)

-- Lemmas about the definition of `signedDist`

/--
lemma `signedDist_apply` / 引理 `signedDist_apply`

English:
lemma signedDist_apply
  statement: signedDist v p = (innerSL Real (normalize v)).toContinuousAffineMap.comp
  proof: rfl

中文:
引理 signedDist_apply
  结论: signedDist v p = (innerSL 实数 (normalize v)).toContinuousAffineMap.comp
  证明: rfl
-/
lemma signedDist_apply : signedDist v p = (innerSL Real (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id Real P -ᵥ .const Real P p) :=
  rfl

/--
lemma `signedDist_apply_apply` / 引理 `signedDist_apply_apply`

English:
lemma signedDist_apply_apply
  statement: signedDist v p q = ⟪normalize v, q -ᵥ p⟫
  proof: rfl

中文:
引理 signedDist_apply_apply
  结论: signedDist v p q = ⟪normalize v, q -ᵥ p⟫
  证明: rfl
-/
lemma signedDist_apply_apply : signedDist v p q = ⟪normalize v, q -ᵥ p⟫ :=
  rfl

/--
lemma `signedDist_apply_linear` / 引理 `signedDist_apply_linear`

English:
lemma signedDist_apply_linear
  statement: (signedDist v p).linear = innerₗ V (normalize v)
  proof: by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp

中文:
引理 signedDist_apply_linear
  结论: (signedDist v p).linear = innerₗ V (normalize v)
  证明: by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp

Depends on / 依赖: LinearMap, LinearMap.id, normalize
-/
lemma signedDist_apply_linear : (signedDist v p).linear = innerₗ V (normalize v) := by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp

/--
lemma `signedDist_apply_linear_apply` / 引理 `signedDist_apply_linear_apply`

English:
lemma signedDist_apply_linear_apply
  statement: (signedDist v p).linear w = ⟪normalize v, w⟫
  proof: by
  simp [signedDist_apply_linear]

中文:
引理 signedDist_apply_linear_apply
  结论: (signedDist v p).linear w = ⟪normalize v, w⟫
  证明: by
  simp [signedDist_apply_linear]

Depends on / 依赖: signedDist_apply_linear
-/
lemma signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪normalize v, w⟫ := by
  simp [signedDist_apply_linear]

/--
lemma `signedDist_linear_apply` / 引理 `signedDist_linear_apply`

English:
lemma signedDist_linear_apply
  statement: (signedDist v).linear w = .const Real P ⟪-normalize v, w⟫
  proof: rfl

中文:
引理 signedDist_linear_apply
  结论: (signedDist v).linear w = .const 实数 P ⟪-normalize v, w⟫
  证明: rfl
-/
lemma signedDist_linear_apply : (signedDist v).linear w = .const Real P ⟪-normalize v, w⟫ :=
  rfl

/--
lemma `signedDist_linear_apply_apply` / 引理 `signedDist_linear_apply_apply`

English:
lemma signedDist_linear_apply_apply
  statement: (signedDist v).linear w p = ⟪-normalize v, w⟫
  proof: rfl

中文:
引理 signedDist_linear_apply_apply
  结论: (signedDist v).linear w p = ⟪-normalize v, w⟫
  证明: rfl
-/
lemma signedDist_linear_apply_apply : (signedDist v).linear w p = ⟪-normalize v, w⟫ :=
  rfl

-- Lemmas about the vector argument of `signedDist`

/--
lemma `signedDist_smul` / 引理 `signedDist_smul`

English:
lemma signedDist_smul
  given: (r : Real)
  statement: signedDist (r • v) p q = SignType.sign r * signedDist v p q
  proof: by
  simp only [signedDist_apply_apply]
  rw [normalize_smul]; rw [real_inner_smul_left]

中文:
引理 signedDist_smul
  条件: (r : 实数)
  结论: signedDist (r • v) p q = SignType.sign r * signedDist v p q
  证明: by
  simp only [signedDist_apply_apply]
  rw [normalize_smul]; rw [real_inner_smul_left]

Depends on / 依赖: normalize_smul, real_inner_smul_left, signedDist_apply_apply
-/
lemma signedDist_smul (r : Real) : signedDist (r • v) p q = SignType.sign r * signedDist v p q := by
  simp only [signedDist_apply_apply]
  rw [normalize_smul]; rw [real_inner_smul_left]

/--
lemma `signedDist_smul_of_pos` / 引理 `signedDist_smul_of_pos`

English:
lemma signedDist_smul_of_pos
  given: {r : Real} (h : 0 < r)
  statement: signedDist (r • v) p q = signedDist v p q
  proof: by
  simp [signedDist_smul, h]

中文:
引理 signedDist_smul_of_pos
  条件: {r : 实数} (h : 0 < r)
  结论: signedDist (r • v) p q = signedDist v p q
  证明: by
  simp [signedDist_smul, h]

Depends on / 依赖: signedDist_smul
-/
lemma signedDist_smul_of_pos {r : Real} (h : 0 < r) : signedDist (r • v) p q = signedDist v p q := by
  simp [signedDist_smul, h]

/--
lemma `signedDist_smul_of_neg` / 引理 `signedDist_smul_of_neg`

English:
lemma signedDist_smul_of_neg
  given: {r : Real} (h : r < 0)
  statement: signedDist (r • v) p q = -signedDist v p q
  proof: by
  simp [signedDist_smul, h]

中文:
引理 signedDist_smul_of_neg
  条件: {r : 实数} (h : r < 0)
  结论: signedDist (r • v) p q = -signedDist v p q
  证明: by
  simp [signedDist_smul, h]

Depends on / 依赖: signedDist_smul
-/
lemma signedDist_smul_of_neg {r : Real} (h : r < 0) : signedDist (r • v) p q = -signedDist v p q := by
  simp [signedDist_smul, h]

/--
lemma `signedDist_zero` / 引理 `signedDist_zero`

English:
lemma signedDist_zero
  statement: signedDist 0 p q = 0
  proof: by
  simpa using signedDist_smul 0 p q 0

中文:
引理 signedDist_zero
  结论: signedDist 0 p q = 0
  证明: by
  simpa using signedDist_smul 0 p q 0
-/
@[simp] lemma signedDist_zero : signedDist 0 p q = 0 := by
  simpa using signedDist_smul 0 p q 0

/--
lemma `signedDist_neg` / 引理 `signedDist_neg`

English:
lemma signedDist_neg
  statement: signedDist (-v) p q = -signedDist v p q
  proof: by
  simpa using signedDist_smul v p q (-1)

中文:
引理 signedDist_neg
  结论: signedDist (-v) p q = -signedDist v p q
  证明: by
  simpa using signedDist_smul v p q (-1)
-/
@[simp] lemma signedDist_neg : signedDist (-v) p q = -signedDist v p q := by
  simpa using signedDist_smul v p q (-1)

/--
lemma `signedDist_congr` / 引理 `signedDist_congr`

English:
lemma signedDist_congr
  given: (h : exists r > (0 : Real), r • v = w)
  statement: signedDist (P := P) v = signedDist w
  proof: by
  obtain ⟨r, _, _⟩ := h
  ext p q
  simpa [*] using (signedDist_smul v p q r).symm

中文:
引理 signedDist_congr
  条件: (h : 存在 r > (0 : 实数), r • v = w)
  结论: signedDist (P := P) v = signedDist w
  证明: by
  obtain ⟨r, _, _⟩ := h
  ext p q
  simpa [*] using (signedDist_smul v p q r).symm

Depends on / 依赖: signedDist, signedDist_smul
-/
lemma signedDist_congr (h : exists r > (0 : Real), r • v = w) : signedDist (P := P) v = signedDist w := by
  obtain ⟨r, _, _⟩ := h
  ext p q
  simpa [*] using (signedDist_smul v p q r).symm

-- Lemmas about permuting the point arguments of `signedDist`, analogous to lemmas about `dist`

/--
lemma `signedDist_self` / 引理 `signedDist_self`

English:
lemma signedDist_self
  statement: signedDist v p p = 0
  proof: by
  simp [signedDist_apply_apply]

中文:
引理 signedDist_self
  结论: signedDist v p p = 0
  证明: by
  simp [signedDist_apply_apply]
-/
@[simp] lemma signedDist_self : signedDist v p p = 0 := by
  simp [signedDist_apply_apply]

/--
lemma `signedDist_anticomm` / 引理 `signedDist_anticomm`

English:
lemma signedDist_anticomm
  statement: -signedDist v p q = signedDist v q p
  proof: by
  simp [signedDist_apply_apply, ← inner_neg_right]

@[simp]

中文:
引理 signedDist_anticomm
  结论: -signedDist v p q = signedDist v q p
  证明: by
  simp [signedDist_apply_apply, ← inner_neg_right]

@[simp]
-/
@[simp] lemma signedDist_anticomm : -signedDist v p q = signedDist v q p := by
  simp [signedDist_apply_apply, ← inner_neg_right]

@[simp]
/--
lemma `signedDist_triangle` / 引理 `signedDist_triangle`

English:
lemma signedDist_triangle
  statement: signedDist v p q + signedDist v q r = signedDist v p r
  proof: by
  simp only [signedDist_apply_apply]
  rw [add_comm]; rw [← inner_add_right]; rw [vsub_add_vsub_cancel]

@[simp]

中文:
引理 signedDist_triangle
  结论: signedDist v p q + signedDist v q r = signedDist v p r
  证明: by
  simp only [signedDist_apply_apply]
  rw [add_comm]; rw [← inner_add_right]; rw [vsub_add_vsub_cancel]

@[simp]

Depends on / 依赖: add_comm, inner_add_right, signedDist_apply_apply, vsub_add_vsub_cancel
-/
lemma signedDist_triangle : signedDist v p q + signedDist v q r = signedDist v p r := by
  simp only [signedDist_apply_apply]
  rw [add_comm]; rw [← inner_add_right]; rw [vsub_add_vsub_cancel]

@[simp]
/--
lemma `signedDist_triangle_left` / 引理 `signedDist_triangle_left`

English:
lemma signedDist_triangle_left
  statement: signedDist v p q - signedDist v p r = signedDist v r q
  proof: by
  rw [sub_eq_iff_eq_add']; rw [signedDist_triangle]

@[simp]

中文:
引理 signedDist_triangle_left
  结论: signedDist v p q - signedDist v p r = signedDist v r q
  证明: by
  rw [sub_eq_iff_eq_add']; rw [signedDist_triangle]

@[simp]

Depends on / 依赖: signedDist_triangle, sub_eq_iff_eq_add
-/
lemma signedDist_triangle_left : signedDist v p q - signedDist v p r = signedDist v r q := by
  rw [sub_eq_iff_eq_add']; rw [signedDist_triangle]

@[simp]
/--
lemma `signedDist_triangle_right` / 引理 `signedDist_triangle_right`

English:
lemma signedDist_triangle_right
  statement: signedDist v p r - signedDist v q r = signedDist v p q
  proof: by
  rw [sub_eq_iff_eq_add]; rw [signedDist_triangle]

中文:
引理 signedDist_triangle_right
  结论: signedDist v p r - signedDist v q r = signedDist v p q
  证明: by
  rw [sub_eq_iff_eq_add]; rw [signedDist_triangle]

Depends on / 依赖: signedDist_triangle, sub_eq_iff_eq_add
-/
lemma signedDist_triangle_right : signedDist v p r - signedDist v q r = signedDist v p q := by
  rw [sub_eq_iff_eq_add]; rw [signedDist_triangle]

-- Lemmas about offsetting the point arguments of `signedDist` (with `+ᵥ` or `-ᵥ`)

/--
lemma `signedDist_vadd_left` / 引理 `signedDist_vadd_left`

English:
lemma signedDist_vadd_left
  statement: signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signedDist v p q
  proof: by
  simp [signedDist_linear_apply_apply]

中文:
引理 signedDist_vadd_left
  结论: signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signedDist v p q
  证明: by
  simp [signedDist_linear_apply_apply]

Depends on / 依赖: signedDist_linear_apply_apply
-/
lemma signedDist_vadd_left : signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_linear_apply_apply]

/--
lemma `signedDist_vadd_right` / 引理 `signedDist_vadd_right`

English:
lemma signedDist_vadd_right
  statement: signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signedDist v p q
  proof: by
  simp [signedDist_apply_linear_apply]

中文:
引理 signedDist_vadd_right
  结论: signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signedDist v p q
  证明: by
  simp [signedDist_apply_linear_apply]

Depends on / 依赖: signedDist_apply_linear_apply
-/
lemma signedDist_vadd_right : signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_apply_linear_apply]

-- TODO: find a better name for these 2 lemmas
/--
lemma `signedDist_vadd_left_swap` / 引理 `signedDist_vadd_left_swap`

English:
lemma signedDist_vadd_left_swap
  statement: signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q)
  proof: by
  rw [signedDist_vadd_left]; rw [signedDist_vadd_right]; rw [inner_neg_right]

中文:
引理 signedDist_vadd_left_swap
  结论: signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q)
  证明: by
  rw [signedDist_vadd_left]; rw [signedDist_vadd_right]; rw [inner_neg_right]

Depends on / 依赖: inner_neg_right, signedDist_vadd_left, signedDist_vadd_right
-/
lemma signedDist_vadd_left_swap : signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q) := by
  rw [signedDist_vadd_left]; rw [signedDist_vadd_right]; rw [inner_neg_right]

/--
lemma `signedDist_vadd_right_swap` / 引理 `signedDist_vadd_right_swap`

English:
lemma signedDist_vadd_right_swap
  statement: signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q
  proof: by
  rw [signedDist_vadd_left_swap]; rw [neg_neg]

中文:
引理 signedDist_vadd_right_swap
  结论: signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q
  证明: by
  rw [signedDist_vadd_left_swap]; rw [neg_neg]

Depends on / 依赖: neg_neg, signedDist_vadd_left_swap
-/
lemma signedDist_vadd_right_swap : signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q := by
  rw [signedDist_vadd_left_swap]; rw [neg_neg]

/--
lemma `signedDist_vadd_vadd` / 引理 `signedDist_vadd_vadd`

English:
lemma signedDist_vadd_vadd
  statement: signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q
  proof: by
  rw [signedDist_vadd_left_swap]; rw [neg_vadd_vadd]

中文:
引理 signedDist_vadd_vadd
  结论: signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q
  证明: by
  rw [signedDist_vadd_left_swap]; rw [neg_vadd_vadd]

Depends on / 依赖: neg_vadd_vadd, signedDist_vadd_left_swap
-/
lemma signedDist_vadd_vadd : signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q := by
  rw [signedDist_vadd_left_swap]; rw [neg_vadd_vadd]

variable {v p q} in
/--
lemma `signedDist_left_congr` / 引理 `signedDist_left_congr`

English:
lemma signedDist_left_congr
  given: (h : ⟪v, p -ᵥ q⟫ = 0)
  statement: signedDist v p = signedDist v q
  proof: by
  ext r
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_left v (p -ᵥ q) q r

中文:
引理 signedDist_left_congr
  条件: (h : ⟪v, p -ᵥ q⟫ = 0)
  结论: signedDist v p = signedDist v q
  证明: by
  ext r
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_left v (p -ᵥ q) q r

Depends on / 依赖: NormedSpace, NormedSpace.normalize, normalize, real_inner_smul_left, signedDist_vadd_left
-/
lemma signedDist_left_congr (h : ⟪v, p -ᵥ q⟫ = 0) : signedDist v p = signedDist v q := by
  ext r
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_left v (p -ᵥ q) q r

variable {v q r} in
/--
lemma `signedDist_right_congr` / 引理 `signedDist_right_congr`

English:
lemma signedDist_right_congr
  given: (h : ⟪v, q -ᵥ r⟫ = 0)
  statement: signedDist v p q = signedDist v p r
  proof: by
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_right v (q -ᵥ r) p r

中文:
引理 signedDist_right_congr
  条件: (h : ⟪v, q -ᵥ r⟫ = 0)
  结论: signedDist v p q = signedDist v p r
  证明: by
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_right v (q -ᵥ r) p r

Depends on / 依赖: NormedSpace, NormedSpace.normalize, normalize, real_inner_smul_left, signedDist_vadd_right
-/
lemma signedDist_right_congr (h : ⟪v, q -ᵥ r⟫ = 0) : signedDist v p q = signedDist v p r := by
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_right v (q -ᵥ r) p r

variable {v p q} in
/--
lemma `signedDist_eq_zero_of_orthogonal` / 引理 `signedDist_eq_zero_of_orthogonal`

English:
lemma signedDist_eq_zero_of_orthogonal
  given: (h : ⟪v, q -ᵥ p⟫ = 0)
  statement: signedDist v p q = 0
  proof: by
  simpa using signedDist_right_congr p h

中文:
引理 signedDist_eq_zero_of_orthogonal
  条件: (h : ⟪v, q -ᵥ p⟫ = 0)
  结论: signedDist v p q = 0
  证明: by
  simpa using signedDist_right_congr p h

Depends on / 依赖: signedDist_right_congr
-/
lemma signedDist_eq_zero_of_orthogonal (h : ⟪v, q -ᵥ p⟫ = 0) : signedDist v p q = 0 := by
  simpa using signedDist_right_congr p h

-- Lemmas relating `signedDist` to `dist`

/--
lemma `abs_signedDist_le_dist` / 引理 `abs_signedDist_le_dist`

English:
lemma abs_signedDist_le_dist
  statement: |signedDist v p q| <= dist p q
  proof: by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · grw [abs_real_inner_le_norm]
    simp [norm_normalize h, dist_eq_norm_vsub']

中文:
引理 abs_signedDist_le_dist
  结论: |signedDist v p q| <= dist p q
  证明: by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · grw [abs_real_inner_le_norm]
    simp [norm_normalize h, dist_eq_norm_vsub']

Depends on / 依赖: abs_real_inner_le_norm, dist_eq_norm_vsub, norm_normalize, signedDist_apply_apply
-/
lemma abs_signedDist_le_dist : |signedDist v p q| <= dist p q := by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · grw [abs_real_inner_le_norm]
    simp [norm_normalize h, dist_eq_norm_vsub']

/--
lemma `signedDist_le_dist` / 引理 `signedDist_le_dist`

English:
lemma signedDist_le_dist
  statement: signedDist v p q <= dist p q
  proof: le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)

中文:
引理 signedDist_le_dist
  结论: signedDist v p q <= dist p q
  证明: le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)

Depends on / 依赖: abs_signedDist_le_dist, le_abs_self, le_trans
-/
lemma signedDist_le_dist : signedDist v p q <= dist p q :=
  le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)

/--
lemma `abs_signedDist_eq_dist_iff_vsub_mem_span` / 引理 `abs_signedDist_eq_dist_iff_vsub_mem_span`

English:
lemma abs_signedDist_eq_dist_iff_vsub_mem_span
  proof: by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]; rw [abs_mul]; rw [abs_inv]; rw [abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [← Real.norm_eq_abs]; rw [((norm_inner_eq_norm_tfae Real v (q -ᵥ p)).out 0 2 :)]
  simp [h, eq_comm]

中文:
引理 abs_signedDist_eq_dist_iff_vsub_mem_span
  证明: by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]; rw [abs_mul]; rw [abs_inv]; rw [abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [← Real.norm_eq_abs]; rw [((norm_inner_eq_norm_tfae Real v (q -ᵥ p)).out 0 2 :)]
  simp [h, eq_comm]

Depends on / 依赖: NormedSpace, NormedSpace.normalize, Real.norm_eq_abs, Submodule, Submodule.mem_span_singleton, abs_inv, abs_mul, abs_norm, dist_eq_norm_vsub, eq_comm, mem_span_singleton, norm_eq_abs, norm_inner_eq_norm_tfae, normalize, real_inner_smul_left, signedDist_apply_apply
-/
lemma abs_signedDist_eq_dist_iff_vsub_mem_span :
    |signedDist v p q| = dist p q ↔ q -ᵥ p in Real ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]; rw [abs_mul]; rw [abs_inv]; rw [abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [← Real.norm_eq_abs]; rw [((norm_inner_eq_norm_tfae Real v (q -ᵥ p)).out 0 2 :)]
  simp [h, eq_comm]

open NNReal in
/--
lemma `signedDist_eq_dist_iff_vsub_mem_span` / 引理 `signedDist_eq_dist_iff_vsub_mem_span`

English:
lemma signedDist_eq_dist_iff_vsub_mem_span
  statement: signedDist v p q = dist p q ↔ q -ᵥ p in Real>=0 ∙ v
  proof: by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [inner_eq_norm_mul_iff_real]
  simp only [smul_def]
  refine ⟨fun h => ?_, fun ⟨c, h⟩ => ?_⟩
  · simp only [NNReal.exists, coe_mk, exists_prop]
    use ‖v‖⁻¹ * ‖q -ᵥ p‖
    constructor
    · positivity
    · rw [← smul_smul, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rw [← h, norm_smul, smul_smul, mul_comm]
    simp

中文:
引理 signedDist_eq_dist_iff_vsub_mem_span
  结论: signedDist v p q = dist p q ↔ q -ᵥ p in 实数>=0 ∙ v
  证明: by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [inner_eq_norm_mul_iff_real]
  simp only [smul_def]
  refine ⟨fun h => ?_, fun ⟨c, h⟩ => ?_⟩
  · simp only [NNReal.exists, coe_mk, exists_prop]
    use ‖v‖⁻¹ * ‖q -ᵥ p‖
    constructor
    · positivity
    · rw [← smul_smul, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rw [← h, norm_smul, smul_smul, mul_comm]
    simp

Depends on / 依赖: NNReal, NNReal.exists, NormedSpace, NormedSpace.normalize, Submodule, Submodule.mem_span_singleton, coe_mk, dist_eq_norm_vsub, eq_comm, exists_prop, inner_eq_norm_mul_iff_real, inv_mul_ca, mem_span_singleton, normalize, real_inner_smul_left, signedDist_apply_apply, smul_def, smul_smul
-/
lemma signedDist_eq_dist_iff_vsub_mem_span : signedDist v p q = dist p q ↔ q -ᵥ p in Real>=0 ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply]; rw [dist_eq_norm_vsub']; rw [NormedSpace.normalize]; rw [real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : Real)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [inner_eq_norm_mul_iff_real]
  simp only [smul_def]
  refine ⟨fun h => ?_, fun ⟨c, h⟩ => ?_⟩
  · simp only [NNReal.exists, coe_mk, exists_prop]
    use ‖v‖⁻¹ * ‖q -ᵥ p‖
    constructor
    · positivity
    · rw [← smul_smul, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rw [← h, norm_smul, smul_smul, mul_comm]
    simp

/--
lemma `signedDist_vsub_self` / 引理 `signedDist_vsub_self`

English:
lemma signedDist_vsub_self
  statement: signedDist (q -ᵥ p) p q = dist p q
  proof: by
  rw [signedDist_eq_dist_iff_vsub_mem_span]
  apply Submodule.mem_span_singleton_self

中文:
引理 signedDist_vsub_self
  结论: signedDist (q -ᵥ p) p q = dist p q
  证明: by
  rw [signedDist_eq_dist_iff_vsub_mem_span]
  apply Submodule.mem_span_singleton_self
-/
@[simp] lemma signedDist_vsub_self : signedDist (q -ᵥ p) p q = dist p q := by
  rw [signedDist_eq_dist_iff_vsub_mem_span]
  apply Submodule.mem_span_singleton_self

/--
lemma `signedDist_vsub_self_rev` / 引理 `signedDist_vsub_self_rev`

English:
lemma signedDist_vsub_self_rev
  statement: signedDist (p -ᵥ q) p q = -dist p q
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← signedDist_neg]; rw [neg_vsub_eq_vsub_rev]
  apply signedDist_vsub_self

中文:
引理 signedDist_vsub_self_rev
  结论: signedDist (p -ᵥ q) p q = -dist p q
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← signedDist_neg]; rw [neg_vsub_eq_vsub_rev]
  apply signedDist_vsub_self
-/
@[simp] lemma signedDist_vsub_self_rev : signedDist (p -ᵥ q) p q = -dist p q := by
  rw [← neg_eq_iff_eq_neg]; rw [← signedDist_neg]; rw [neg_vsub_eq_vsub_rev]
  apply signedDist_vsub_self

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedDist_lineMap_lineMap` / 引理 `signedDist_lineMap_lineMap`

English:
lemma signedDist_lineMap_lineMap
  given: (c₁ c₂ : Real)
  proof: by
  trans c₂ * signedDist v p q + c₁ * signedDist v q p
  · simp [AffineMap.lineMap_apply_ring']
  · rw [sub_mul, ← signedDist_anticomm v p, mul_neg, sub_eq_add_neg]

中文:
引理 signedDist_lineMap_lineMap
  条件: (c₁ c₂ : 实数)
  证明: by
  trans c₂ * signedDist v p q + c₁ * signedDist v q p
  · simp [AffineMap.lineMap_apply_ring']
  · rw [sub_mul, ← signedDist_anticomm v p, mul_neg, sub_eq_add_neg]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_ring, lineMap_apply_ring, mul_neg, signedDist, signedDist_anticomm, sub_eq_add_neg, sub_mul
-/
lemma signedDist_lineMap_lineMap (c₁ c₂ : Real) :
    signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) =
      (c₂ - c₁) * signedDist v p q := by
  trans c₂ * signedDist v p q + c₁ * signedDist v q p
  · simp [AffineMap.lineMap_apply_ring']
  · rw [sub_mul, ← signedDist_anticomm v p, mul_neg, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedDist_lineMap_left` / 引理 `signedDist_lineMap_left`

English:
lemma signedDist_lineMap_left
  given: (c : Real)
  proof: by
  simpa using signedDist_lineMap_lineMap v p q c 0

中文:
引理 signedDist_lineMap_left
  条件: (c : 实数)
  证明: by
  simpa using signedDist_lineMap_lineMap v p q c 0

Depends on / 依赖: signedDist_lineMap_lineMap
-/
lemma signedDist_lineMap_left (c : Real) :
    signedDist v (AffineMap.lineMap p q c) p = -c * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q c 0

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedDist_left_lineMap` / 引理 `signedDist_left_lineMap`

English:
lemma signedDist_left_lineMap
  given: (c : Real)
  proof: by
  simpa using signedDist_lineMap_lineMap v p q 0 c

中文:
引理 signedDist_left_lineMap
  条件: (c : 实数)
  证明: by
  simpa using signedDist_lineMap_lineMap v p q 0 c

Depends on / 依赖: signedDist_lineMap_lineMap
-/
lemma signedDist_left_lineMap (c : Real) :
    signedDist v p (AffineMap.lineMap p q c) = c * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q 0 c

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedDist_lineMap_right` / 引理 `signedDist_lineMap_right`

English:
lemma signedDist_lineMap_right
  given: (c : Real)
  proof: by
  simpa using signedDist_lineMap_lineMap v p q c 1

中文:
引理 signedDist_lineMap_right
  条件: (c : 实数)
  证明: by
  simpa using signedDist_lineMap_lineMap v p q c 1

Depends on / 依赖: signedDist_lineMap_lineMap
-/
lemma signedDist_lineMap_right (c : Real) :
    signedDist v (AffineMap.lineMap p q c) q = (1 - c) * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q c 1

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedDist_right_lineMap` / 引理 `signedDist_right_lineMap`

English:
lemma signedDist_right_lineMap
  given: (c : Real)
  proof: by
  simpa using signedDist_lineMap_lineMap v p q 1 c

中文:
引理 signedDist_right_lineMap
  条件: (c : 实数)
  证明: by
  simpa using signedDist_lineMap_lineMap v p q 1 c

Depends on / 依赖: signedDist_lineMap_lineMap
-/
lemma signedDist_right_lineMap (c : Real) :
    signedDist v q (AffineMap.lineMap p q c) = (c - 1) * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q 1 c

end signedDist

namespace AffineSubspace

variable (s : AffineSubspace Real P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p q : P)

/--
Definition of `signedInfDist` / `signedInfDist` 的定义

English:
definition signedInfDist
  signature: : P ->ᴬ[Real] Real
  body: signedDist (p -ᵥ orthogonalProjection s p) (Classical.ofNonempty : s)

中文:
定义 signedInfDist
  签名: : P ->ᴬ[实数] 实数
  定义体: signedDist (p -ᵥ orthogonalProjection s p) (Classical.ofNonempty : s)

Depends on / 依赖: Classical, Classical.ofNonempty, ofNonempty, orthogonalProjection, signedDist
-/
noncomputable def signedInfDist : P ->ᴬ[Real] Real :=
  signedDist (p -ᵥ orthogonalProjection s p) (Classical.ofNonempty : s)

/--
lemma `signedInfDist_def` / 引理 `signedInfDist_def`

English:
lemma signedInfDist_def
  proof: rfl

中文:
引理 signedInfDist_def
  证明: rfl
-/
lemma signedInfDist_def :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) ↑(Classical.ofNonempty : s) :=
  rfl

variable {s p q} in
/--
lemma `signedInfDist_eq_signedDist_of_mem` / 引理 `signedInfDist_eq_signedDist_of_mem`

English:
lemma signedInfDist_eq_signedDist_of_mem
  given: (h : q in s)
  proof: by
  apply signedDist_left_congr
  apply s.direction.inner_left_of_mem_orthogonal
  · exact vsub_mem_direction (SetLike.coe_mem _) h
  · exact vsub_orthogonalProjection_mem_direction_orthogonal s p

中文:
引理 signedInfDist_eq_signedDist_of_mem
  条件: (h : q in s)
  证明: by
  apply signedDist_left_congr
  apply s.direction.inner_left_of_mem_orthogonal
  · exact vsub_mem_direction (SetLike.coe_mem _) h
  · exact vsub_orthogonalProjection_mem_direction_orthogonal s p

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, direction, inner_left_of_mem_orthogonal, s.direction.inner_left_of_mem_orthogonal, signedDist_left_congr, vsub_mem_direction, vsub_orthogonalProjection_mem_direction_orthogonal
-/
lemma signedInfDist_eq_signedDist_of_mem (h : q in s) :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) q := by
  apply signedDist_left_congr
  apply s.direction.inner_left_of_mem_orthogonal
  · exact vsub_mem_direction (SetLike.coe_mem _) h
  · exact vsub_orthogonalProjection_mem_direction_orthogonal s p

/--
lemma `signedInfDist_eq_signedDist_orthogonalProjection` / 引理 `signedInfDist_eq_signedDist_orthogonalProjection`

English:
lemma signedInfDist_eq_signedDist_orthogonalProjection
  given: {x : P}
  statement: s.signedInfDist p x =
  proof: by
  rw [signedInfDist_eq_signedDist_of_mem (orthogonalProjection_mem x)]

中文:
引理 signedInfDist_eq_signedDist_orthogonalProjection
  条件: {x : P}
  结论: s.signedInfDist p x =
  证明: by
  rw [signedInfDist_eq_signedDist_of_mem (orthogonalProjection_mem x)]

Depends on / 依赖: orthogonalProjection_mem, signedInfDist_eq_signedDist_of_mem
-/
lemma signedInfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist p x =
    signedDist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProjection s x) x := by
  rw [signedInfDist_eq_signedDist_of_mem (orthogonalProjection_mem x)]

/--
lemma `signedInfDist_apply_self` / 引理 `signedInfDist_apply_self`

English:
lemma signedInfDist_apply_self
  statement: s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖
  proof: by
  rw [signedInfDist_eq_signedDist_orthogonalProjection]; rw [signedDist_vsub_self]; rw [dist_eq_norm_vsub']

中文:
引理 signedInfDist_apply_self
  结论: s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖
  证明: by
  rw [signedInfDist_eq_signedDist_orthogonalProjection]; rw [signedDist_vsub_self]; rw [dist_eq_norm_vsub']
-/
@[simp] lemma signedInfDist_apply_self : s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  rw [signedInfDist_eq_signedDist_orthogonalProjection]; rw [signedDist_vsub_self]; rw [dist_eq_norm_vsub']

variable {s} in
/--
lemma `signedInfDist_apply_of_mem` / 引理 `signedInfDist_apply_of_mem`

English:
lemma signedInfDist_apply_of_mem
  given: {x : P} (hx : x in s)
  statement: s.signedInfDist p x = 0
  proof: by
  simp [signedInfDist_eq_signedDist_orthogonalProjection, orthogonalProjection_eq_self_iff.2 hx]

中文:
引理 signedInfDist_apply_of_mem
  条件: {x : P} (hx : x in s)
  结论: s.signedInfDist p x = 0
  证明: by
  simp [signedInfDist_eq_signedDist_orthogonalProjection, orthogonalProjection_eq_self_iff.2 hx]
-/
@[simp] lemma signedInfDist_apply_of_mem {x : P} (hx : x in s) : s.signedInfDist p x = 0 := by
  simp [signedInfDist_eq_signedDist_orthogonalProjection, orthogonalProjection_eq_self_iff.2 hx]

variable {s p} in
/--
lemma `signedInfDist_eq_const_of_mem` / 引理 `signedInfDist_eq_const_of_mem`

English:
lemma signedInfDist_eq_const_of_mem
  given: (h : p in s)
  proof: by
  ext x
  simp [signedInfDist_def, orthogonalProjection_eq_self_iff.2 h]

中文:
引理 signedInfDist_eq_const_of_mem
  条件: (h : p in s)
  证明: by
  ext x
  simp [signedInfDist_def, orthogonalProjection_eq_self_iff.2 h]
-/
@[simp] lemma signedInfDist_eq_const_of_mem (h : p in s) :
    s.signedInfDist p = AffineMap.const Real P (0 : Real) := by
  ext x
  simp [signedInfDist_def, orthogonalProjection_eq_self_iff.2 h]

variable {s p} in
/--
lemma `abs_signedInfDist_eq_dist_of_mem_affineSpan_insert` / 引理 `abs_signedInfDist_eq_dist_of_mem_affineSpan_insert`

English:
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_insert
  statement: {x : P}
  proof: by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]

中文:
引理 abs_signedInfDist_eq_dist_of_mem_affineSpan_insert
  结论: {x : P}
  证明: by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]

Depends on / 依赖: abs_mul, dist_eq_norm_vsub, mem_affineSpan_insert_iff, norm_smul, orthogonalProjection, orthogonalProjection_eq_self_iff, orthogonalProjection_vsub_orthogonalProjection, property
-/
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_insert {x : P}
    (h : x in affineSpan Real (insert p s)) :
    |s.signedInfDist p x| = dist x (orthogonalProjection s x) := by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]

/--
lemma `signedInfDist_singleton` / 引理 `signedInfDist_singleton`

English:
lemma signedInfDist_singleton
  proof: by
  simpa using signedInfDist_eq_signedDist_of_mem (mem_affineSpan Real (Set.mem_singleton q))

中文:
引理 signedInfDist_singleton
  证明: by
  simpa using signedInfDist_eq_signedDist_of_mem (mem_affineSpan Real (Set.mem_singleton q))

Depends on / 依赖: Set.mem_singleton, mem_affineSpan, mem_singleton, signedInfDist_eq_signedDist_of_mem
-/
lemma signedInfDist_singleton :
    (affineSpan Real ({q} : Set P)).signedInfDist p = signedDist (p -ᵥ q) q := by
  simpa using signedInfDist_eq_signedDist_of_mem (mem_affineSpan Real (Set.mem_singleton q))

end AffineSubspace

namespace Affine

namespace Simplex

variable {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))

/--
Definition of `signedInfDist` / `signedInfDist` 的定义

English:
definition signedInfDist
  signature: : P ->ᴬ[Real] Real
  body: AffineSubspace.signedInfDist (affineSpan Real (s.points '' {i}ᶜ)) (s.points i)

中文:
定义 signedInfDist
  签名: : P ->ᴬ[实数] 实数
  定义体: AffineSubspace.signedInfDist (affineSpan Real (s.points '' {i}ᶜ)) (s.points i)

Depends on / 依赖: AffineSubspace, AffineSubspace.signedInfDist, affineSpan, points, s.points, signedInfDist
-/
noncomputable def signedInfDist : P ->ᴬ[Real] Real :=
  AffineSubspace.signedInfDist (affineSpan Real (s.points '' {i}ᶜ)) (s.points i)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `signedInfDist_reindex` / 引理 `signedInfDist_reindex`

English:
lemma signedInfDist_reindex
  statement: {m : Nat} [NeZero m] (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by
  simp_rw [signedInfDist, reindex_points, Set.image_comp, Set.image_compl_eq e.symm.bijective,
    Set.image_singleton, Function.comp_apply]

中文:
引理 signedInfDist_reindex
  结论: {m : 自然数} [NeZero m] (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by
  simp_rw [signedInfDist, reindex_points, Set.image_comp, Set.image_compl_eq e.symm.bijective,
    Set.image_singleton, Function.comp_apply]
-/
@[simp] lemma signedInfDist_reindex {m : Nat} [NeZero m] (e : Fin (n + 1) ≃ Fin (m + 1))
    (j : Fin (m + 1)) : (s.reindex e).signedInfDist j = s.signedInfDist (e.symm j) := by
  simp_rw [signedInfDist, reindex_points, Set.image_comp, Set.image_compl_eq e.symm.bijective,
    Set.image_singleton, Function.comp_apply]

/--
lemma `signedInfDist_apply_self` / 引理 `signedInfDist_apply_self`

English:
lemma signedInfDist_apply_self
  proof: (AffineSubspace.signedInfDist_apply_self _ _).trans by simp [orthogonalProjectionSpan]

中文:
引理 signedInfDist_apply_self
  证明: (AffineSubspace.signedInfDist_apply_self _ _).trans by simp [orthogonalProjectionSpan]

Depends on / 依赖: AffineSubspace, AffineSubspace.signedInfDist_apply_self, orthogonalProjectionSpan, signedInfDist_apply_self
-/
lemma signedInfDist_apply_self :
    s.signedInfDist i (s.points i) =
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ :=
(AffineSubspace.signedInfDist_apply_self _ _).trans by simp [orthogonalProjectionSpan]

variable {i} in
/--
lemma `signedInfDist_apply_of_ne` / 引理 `signedInfDist_apply_of_ne`

English:
lemma signedInfDist_apply_of_ne
  given: {j : Fin (n + 1)} (h : j != i)
  proof: AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)

中文:
引理 signedInfDist_apply_of_ne
  条件: {j : 有限集 (n + 1)} (h : j != i)
  证明: AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)

Depends on / 依赖: AffineSubspace, AffineSubspace.signedInfDist_apply_of_mem, mem_affineSpan_image_iff, s.mem_affineSpan_image_iff, signedInfDist_apply_of_mem
-/
lemma signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j != i) :
    s.signedInfDist i (s.points j) = 0 :=
  AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)

/--
lemma `signedInfDist_affineCombination` / 引理 `signedInfDist_affineCombination`

English:
lemma signedInfDist_affineCombination
  given: {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1)
  proof: by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [Finset.map_affineCombination _ _ _ h]; rw [Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s.points) 0
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

中文:
引理 signedInfDist_affineCombination
  条件: {w : 有限集 (n + 1) -> 实数} (h : ∑ i, w i = 1)
  证明: by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [Finset.map_affineCombination _ _ _ h]; rw [Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s.points) 0
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, ContinuousAffineMap, ContinuousAffineMap.coe_toAffineMap, Finset, Finset.map_affineCombination, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, Finset.univ.affineCombination_apply_eq_lineMap_sum, Function, Function.comp_apply, affineCombination_apply_eq_lineMap_sum, coe_toAffineMap, comp_apply, faceOpposite, lineMap_apply, map_affineCombination, mem_sdiff, mem_singleton
-/
lemma signedInfDist_affineCombination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1) :
    s.signedInfDist i (Finset.univ.affineCombination Real s.points w) = w i * ‖s.points i -ᵥ
      (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ := by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [Finset.map_affineCombination _ _ _ h]; rw [Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s.points) 0
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

variable {s} in
/--
lemma `abs_signedInfDist_eq_dist_of_mem_affineSpan_range` / 引理 `abs_signedInfDist_eq_dist_of_mem_affineSpan_range`

English:
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_range
  statement: {p : P}
  proof: by
  rw [signedInfDist]; rw [AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert]; rw [orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert! h
  exact Set.insert_image_compl_eq_range s.points i

中文:
引理 abs_signedInfDist_eq_dist_of_mem_affineSpan_range
  结论: {p : P}
  证明: by
  rw [signedInfDist]; rw [AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert]; rw [orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert! h
  exact Set.insert_image_compl_eq_range s.points i

Depends on / 依赖: AffineSubspace, AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert, Set.insert_image_compl_eq_range, abs_signedInfDist_eq_dist_of_mem_affineSpan_insert, affineSpan_insert_affineSpan, convert, insert_image_compl_eq_range, orthogonalProjectionSpan, points, range_faceOpposite_points, s.points, signedInfDist, simp_rw
-/
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_range {p : P}
    (h : p in affineSpan Real (Set.range s.points)) :
    |s.signedInfDist i p| =
      dist p ((s.faceOpposite i).orthogonalProjectionSpan p) := by
  rw [signedInfDist]; rw [AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert]; rw [orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert! h
  exact Set.insert_image_compl_eq_range s.points i

end Simplex

end Affine
