/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle
* https://en.wikipedia.org/wiki/Law_of_sines

-/

public section

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

/--
theorem `norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle` / 定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle`

English:
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
  given: (x y : V)
  proof: by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring]; rw [cos_angle_mul_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
    real_inner_self_eq_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [real_inner_sub_sub_self]; rw [s

中文:
定理 norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
  条件: (x y : V)
  证明: by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring]; rw [cos_angle_mul_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
    real_inner_self_eq_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [real_inner_sub_sub_self]; rw [s

Depends on / 依赖: Real.cos, cos_angle_mul_norm_mul_norm, real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self, sub_add_eq_add_sub
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring]; rw [cos_angle_mul_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
    real_inner_self_eq_norm_mul_norm]; rw [← real_inner_self_eq_norm_mul_norm]; rw [real_inner_sub_sub_self]; rw [sub_add_eq_add_sub]

/--
theorem `sin_angle_mul_norm_eq_sin_angle_mul_norm` / 定理 `sin_angle_mul_norm_eq_sin_angle_mul_norm`

English:
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm
  given: (x y : V)
  proof: by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x != 0) (hy : y != 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫)

中文:
定理 sin_angle_mul_norm_eq_sin_angle_mul_norm
  条件: (x y : V)
  证明: by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x != 0) (hy : y != 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫)

Depends on / 依赖: Real.sin, angle_neg_right, angle_self, eq_or_ne, h_sin, inner_sub_left, inner_sub_right, mul_assoc, real_inner_comm, sin_angle_mul_norm_mul_norm, sub_ne_zero_of_ne
-/
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x != 0) (hy : y != 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
    simp [field, mul_assoc, sin_angle_mul_norm_mul_norm]
  rw [h_sin x y hx hy]; rw [h_sin y (x - y) hy (sub_ne_zero_of_ne hxy)]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm x y]
  have hsub : x - y != 0 := sub_ne_zero_of_ne hxy
  field_simp
  ring_nf

/--
theorem `sin_angle_div_norm_eq_sin_angle_div_norm` / 定理 `sin_angle_div_norm_eq_sin_angle_div_norm`

English:
theorem sin_angle_div_norm_eq_sin_angle_div_norm
  given: (x y : V) (hx : x != 0) (hxy : x - y != 0)
  proof: by
  simp [field, sin_angle_mul_norm_eq_sin_angle_mul_norm x y]

中文:
定理 sin_angle_div_norm_eq_sin_angle_div_norm
  条件: (x y : V) (hx : x != 0) (hxy : x - y != 0)
  证明: by
  simp [field, sin_angle_mul_norm_eq_sin_angle_mul_norm x y]

Depends on / 依赖: sin_angle_mul_norm_eq_sin_angle_mul_norm
-/
theorem sin_angle_div_norm_eq_sin_angle_div_norm (x y : V) (hx : x != 0) (hxy : x - y != 0) :
    Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖ := by
  simp [field, sin_angle_mul_norm_eq_sin_angle_mul_norm x y]

/--
theorem `angle_sub_eq_angle_sub_rev_of_norm_eq` / 定理 `angle_sub_eq_angle_sub_rev_of_norm_eq`

English:
theorem angle_sub_eq_angle_sub_rev_of_norm_eq
  given: {x y : V} (h : ‖x‖ = ‖y‖)
  proof: by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle]; rw [cos_angle]; rw [h]; rw [← neg_sub]; rw [norm_neg]; rw [neg_sub]; rw [inner_sub_right]; rw [inner_sub_right]; rw [real_inner_self_eq_norm_mul_norm]; rw [real_inner_self_eq_norm_

中文:
定理 angle_sub_eq_angle_sub_rev_of_norm_eq
  条件: {x y : V} (h : ‖x‖ = ‖y‖)
  证明: by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle]; rw [cos_angle]; rw [h]; rw [← neg_sub]; rw [norm_neg]; rw [neg_sub]; rw [inner_sub_right]; rw [inner_sub_right]; rw [real_inner_self_eq_norm_mul_norm]; rw [real_inner_self_eq_norm_

Depends on / 依赖: Real.injOn_cos, angle_le_pi, angle_nonneg, cos_angle, injOn_cos, inner_sub_right, neg_sub, norm_neg, real_inner_comm, real_inner_self_eq_norm_mul_norm
-/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle]; rw [cos_angle]; rw [h]; rw [← neg_sub]; rw [norm_neg]; rw [neg_sub]; rw [inner_sub_right]; rw [inner_sub_right]; rw [real_inner_self_eq_norm_mul_norm]; rw [real_inner_self_eq_norm_mul_norm]; rw [h]; rw [real_inner_comm x y]

/--
theorem `norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi` / 定理 `norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi`

English:
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
  statement: {x y : V}
  proof: by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
 

中文:
定理 norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
  结论: {x y : V}
  证明: by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
 

Depends on / 依赖: Real.arccos_injOn, abs_le, abs_le.mp, abs_real_inner_div_norm_mul_norm_le_one, arccos_injOn, div_eq_mul_inv, eq_of_sub_eq_zero, inner_sub_right, inv_ne_zero, mul_assoc, mul_comm, mul_inv_rev, neg_sub, norm_eq_zero, norm_neg, real_in, replace
-/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y != π) : ‖x‖ = ‖y‖ := by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv_rev, mul_inv_rev, ← mul_assoc, ← mul_assoc] at h
    replace h :=
      mul_right_cancel₀ (inv_ne_zero fun hz => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz))) h
    rw [inner_sub_right]; rw [inner_sub_right]; rw [real_inner_comm x y]; rw [real_inner_self_eq_norm_mul_norm]; rw [real_inner_self_eq_norm_mul_norm]; rw [mul_sub_right_distrib]; rw [mul_sub_right_distrib]; rw [mul_self_mul_inv]; rw [mul_self_mul_inv]; rw [sub_eq_sub_iff_sub_eq_sub]; rw [← mul_sub_left_distrib] at h
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h
      rw [hx0]; rw [norm_zero]; rw [h]
    · by_cases hy0 : y = 0
      · rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h
        rw [hy0]; rw [norm_zero]; rw [h]
      · rw [inv_sub_inv (fun hz => hx0 (norm_eq_zero.1 hz)) fun hz => hy0 (norm_eq_zero.1 hz), ←
          neg_sub, ← mul_div_assoc, mul_comm, mul_div_assoc, ← mul_neg_one] at h
        symm
        by_contra hyx
        replace h := (mul_left_cancel₀ (sub_ne_zero_of_ne hyx) h).symm
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff]; rw [← angle_eq_pi_iff] at h
        exact hpi h

/--
theorem `cos_angle_eq_cos_angle_add_add_angle_add` / 定理 `cos_angle_eq_cos_angle_add_add_angle_add`

English:
theorem cos_angle_eq_cos_angle_add_add_angle_add
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.cos_add, cos_angle, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), mul_comm ⟪y, y⟫ ⟪x, x⟫, real_inner_comm x y, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-

中文:
定理 cos_angle_eq_cos_angle_add_add_angle_add
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.cos_add, cos_angle, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), mul_comm ⟪y, y⟫ ⟪x, x⟫, real_inner_comm x y, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-
-/
private theorem cos_angle_eq_cos_angle_add_add_angle_add {x y : V} (hx : x != 0) (hy : y != 0) :
    Real.cos (angle x y) = Real.cos (angle x (x + y) + angle y (y + x)) := by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.cos_add, cos_angle, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), mul_comm ⟪y, y⟫ ⟪x, x⟫, real_inner_comm x y, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    rw [Real.sq_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y))]
    simp only [← real_inner_self_eq_norm_sq, inner_add_right, inner_add_left, real_inner_comm]
    ring

/--
theorem `sin_angle_eq_sin_angle_add_add_angle_add` / 定理 `sin_angle_eq_sin_angle_add_add_angle_add`

English:
theorem sin_angle_eq_sin_angle_add_add_angle_add
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.sin_add, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), sin_angle hx hy, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    simp only [←

中文:
定理 sin_angle_eq_sin_angle_add_add_angle_add
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.sin_add, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), sin_angle hx hy, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    simp only [←
-/
private theorem sin_angle_eq_sin_angle_add_add_angle_add {x y : V} (hx : x != 0) (hy : y != 0) :
    Real.sin (angle x y) = Real.sin (angle x (x + y) + angle y (y + x)) := by
  rcases eq_or_ne x (-y) with (rfl | hxy)
  · simp [hy]
  · rw [Real.sin_add, cos_angle, cos_angle, sin_angle_add hx (by grind),
      sin_angle_add hy (by grind), sin_angle hx hy, add_comm y x]
    have : x + y != 0 := by grind
    simp only [field] -- non-recursive `field_simp`
    simp only [← real_inner_self_eq_norm_sq, inner_add_right, inner_add_left, real_inner_comm]
    ring_nf

/--
theorem `angle_eq_angle_add_add_angle_add` / 定理 `angle_eq_angle_add_add_angle_add`

English:
theorem angle_eq_angle_add_add_angle_add
  given: (x : V) {y : V} (hy : y != 0)
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp [hy]
  have h := Real.Angle.cos_sin_inj
    (cos_angle_eq_cos_angle_add_add_angle_add hx hy)
    (sin_angle_eq_sin_angle_add_add_angle_add hx hy)
  rw [add_comm y x] at h
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp h
  simp only a

中文:
定理 angle_eq_angle_add_add_angle_add
  条件: (x : V) {y : V} (hy : y != 0)
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp [hy]
  have h := Real.Angle.cos_sin_inj
    (cos_angle_eq_cos_angle_add_add_angle_add hx hy)
    (sin_angle_eq_sin_angle_add_add_angle_add hx hy)
  rw [add_comm y x] at h
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp h
  simp only a

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk, Real.Angle.cos_sin_inj, Real.pi_pos, _eq_mk, add_comm, angle_le_pi, angle_nonneg, contrapose, cos_angle_eq_cos_angle_add_add_angle_add, cos_sin_inj, eq_or_ne, h.ge, h.le, linear_combination, neg_smul, one_smul, pi_pos, replace, sin_angle_eq_sin_angle_add_add_angle_add
-/
theorem angle_eq_angle_add_add_angle_add (x : V) {y : V} (hy : y != 0) :
    angle x y = angle x (x + y) + angle y (x + y) := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp [hy]
  have h := Real.Angle.cos_sin_inj
    (cos_angle_eq_cos_angle_add_add_angle_add hx hy)
    (sin_angle_eq_sin_angle_add_add_angle_add hx hy)
  rw [add_comm y x] at h
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp h
  simp only at h
  have : -1 < n := by
    replace h := h.ge
    contrapose! h
    grw [h, neg_smul, one_smul, angle_le_pi, ← angle_nonneg, ← angle_nonneg]
    linear_combination Real.pi_pos
  have : n < 1 := by
    replace h := h.le
    by_contra! hn
    grw [← hn, one_smul, ← angle_nonneg x y, zero_add, two_mul] at h
    have h' := h.trans_eq (add_comm _ _)
    grw [angle_le_pi] at h' h
    rw [add_le_add_iff_left]; rw [(angle_le_pi _ _).ge_iff_eq]; rw [angle_comm]; rw [angle_eq_pi_iff] at h' h
    obtain ⟨hxy, r₁, r₁_pos, hr₁⟩ := h'
    obtain ⟨-, r₂, r₂_pos, hr₂⟩ := h
    have : (r₁ + r₂ - 1) • (x + y) = 0 := by
      rw [sub_smul]; rw [add_smul]; rw [one_smul]; rw [← hr₁]; rw [← hr₂]; rw [sub_eq_zero]
    cases smul_eq_zero.1 this
    · linarith
    · contradiction
  obtain rfl : n = 0 := by lia
  simpa using h

/--
theorem `angle_add_angle_sub_add_angle_sub_eq_pi` / 定理 `angle_add_angle_sub_add_angle_sub_eq_pi`

English:
theorem angle_add_angle_sub_add_angle_sub_eq_pi
  given: (x : V) {y : V} (hy : y != 0)
  proof: by
  have h := angle_eq_angle_add_add_angle_add (x - y) hy
  rw [sub_add_cancel] at h
  rw [← neg_sub x y]; rw [angle_neg_right]
  simp only [angle_comm] at h ⊢
  linear_combination -h

中文:
定理 angle_add_angle_sub_add_angle_sub_eq_pi
  条件: (x : V) {y : V} (hy : y != 0)
  证明: by
  have h := angle_eq_angle_add_add_angle_add (x - y) hy
  rw [sub_add_cancel] at h
  rw [← neg_sub x y]; rw [angle_neg_right]
  simp only [angle_comm] at h ⊢
  linear_combination -h

Depends on / 依赖: angle_comm, angle_eq_angle_add_add_angle_add, angle_neg_right, linear_combination, neg_sub, sub_add_cancel
-/
theorem angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y != 0) :
    angle x y + angle x (x - y) + angle y (y - x) = π := by
  have h := angle_eq_angle_add_add_angle_add (x - y) hy
  rw [sub_add_cancel] at h
  rw [← neg_sub x y]; rw [angle_neg_right]
  simp only [angle_comm] at h ⊢
  linear_combination -h

end InnerProductGeometry

namespace Orientation

open Module InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [Fact (finrank Real V = 2)]
variable (o : Orientation Real V (Fin 2))

/--
theorem `norm_eq_of_two_zsmul_oangle_sub_eq` / 定理 `norm_eq_of_two_zsmul_oangle_sub_eq`

English:
theorem norm_eq_of_two_zsmul_oangle_sub_eq
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x - y)).sign = (o.oangle (y - x) y).sign := by simp
  rw [Real.Angle.two_zsmul_eq_iff] at h
  rcases h with h | h
  · rw [← o.angle_eq_iff_oangle_eq_of_sign_eq (o.left_ne_zero_of_oangle_ne_zero h0)
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0))
      (sub_ne_zero_o

中文:
定理 norm_eq_of_two_zsmul_oangle_sub_eq
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x - y)).sign = (o.oangle (y - x) y).sign := by simp
  rw [Real.Angle.two_zsmul_eq_iff] at h
  rcases h with h | h
  · rw [← o.angle_eq_iff_oangle_eq_of_sign_eq (o.left_ne_zero_of_oangle_ne_zero h0)
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0))
      (sub_ne_zero_o

Depends on / 依赖: Real.Angle.two_zsmul_eq_iff, angle_comm, angle_eq_iff_oangle_eq_of_sign_eq, left_ne_zero_of_oangle_ne_zero, ne_eq, ne_of_oangle_ne_zero, norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi, o.angle_eq_iff_oangle_eq_of_sign_eq, o.left_ne_zero_of_oangle_ne_zero, o.ne_of_oangle_ne_zero, o.oangle, o.oangle_eq_pi_iff_angle_eq_pi, o.right_ne_zero_of_oangle_ne_zero, oangle, oangle_eq_pi_iff_angle_eq_pi, right_ne_zero_of_oangle_ne_zero, sub_ne_zero_of_ne, two_zsmul_eq_iff
-/
theorem norm_eq_of_two_zsmul_oangle_sub_eq {x y : V}
    (h : (2 : Int) • o.oangle x (x - y) = (2 : Int) • o.oangle (y - x) y) (h0 : o.oangle x y != 0)
    (hpi : o.oangle x y != π) : ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x - y)).sign = (o.oangle (y - x) y).sign := by simp
  rw [Real.Angle.two_zsmul_eq_iff] at h
  rcases h with h | h
  · rw [← o.angle_eq_iff_oangle_eq_of_sign_eq (o.left_ne_zero_of_oangle_ne_zero h0)
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0))
      (sub_ne_zero_of_ne (o.ne_of_oangle_ne_zero h0).symm)
      (o.right_ne_zero_of_oangle_ne_zero h0) hs, angle_comm (y - x)] at h
    refine norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h ?_
    rw [ne_eq]; rw [← o.oangle_eq_pi_iff_angle_eq_pi]
    exact hpi
  · rw [h, Real.Angle.sign_add_pi, SignType.neg_eq_self_iff, oangle_sign_sub_left_swap,
      o.oangle_rev, Real.Angle.sign_neg, SignType.neg_eq_zero_iff,
      Real.Angle.sign_eq_zero_iff] at hs
    simp [h0, hpi] at hs

end Orientation

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P]

/--
theorem `dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle` / 定理 `dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`

English:
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
  given: (p₁ p₂ p₃ : P)
  proof: by
  rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert!
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (p₁ -ᵥ p₂ : V)
      (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · ex

中文:
定理 dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
  条件: (p₁ p₂ p₃ : P)
  证明: by
  rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert!
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (p₁ -ᵥ p₂ : V)
      (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · ex

Depends on / 依赖: convert, dist_eq_norm_vsub, norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle, vsub_sub_vsub_cancel_right
-/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by
  rw [dist_eq_norm_vsub V p₁ p₃]; rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert!
    norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (p₁ -ᵥ p₂ : V)
      (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

/--
theorem `sin_angle_mul_dist_eq_sin_angle_mul_dist` / 定理 `sin_angle_mul_dist_eq_sin_angle_mul_dist`

English:
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist
  given: (p₁ p₂ p₃ : P)
  proof: by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂]; rw [dist_eq_norm_vsub V p₃ p₁]; rw [InnerProductGeometry.angle_comm]; rw [sin_angle_mul_norm_eq_sin_angle_mul_norm]; rw [vsub_sub_vsub_cancel_right]; rw [mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm]; rw 

中文:
定理 sin_angle_mul_dist_eq_sin_angle_mul_dist
  条件: (p₁ p₂ p₃ : P)
  证明: by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂]; rw [dist_eq_norm_vsub V p₃ p₁]; rw [InnerProductGeometry.angle_comm]; rw [sin_angle_mul_norm_eq_sin_angle_mul_norm]; rw [vsub_sub_vsub_cancel_right]; rw [mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm]; rw 

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_comm, Real.sin_pi_sub, angle_comm, angle_neg_right, dist_comm, dist_eq_norm_vsub, mul_eq_mul_right_iff, neg_vsub_eq_vsub_rev, sin_angle_mul_norm_eq_sin_angle_mul_norm, sin_pi_sub, vsub_sub_vsub_cancel_right
-/
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂]; rw [dist_eq_norm_vsub V p₃ p₁]; rw [InnerProductGeometry.angle_comm]; rw [sin_angle_mul_norm_eq_sin_angle_mul_norm]; rw [vsub_sub_vsub_cancel_right]; rw [mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm]; rw [← neg_vsub_eq_vsub_rev p₁ p₂]; rw [angle_neg_right]; rw [Real.sin_pi_sub]

alias law_sin := sin_angle_mul_dist_eq_sin_angle_mul_dist

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `sin_angle_div_dist_eq_sin_angle_div_dist` / 定理 `sin_angle_div_dist_eq_sin_angle_div_dist`

English:
theorem sin_angle_div_dist_eq_sin_angle_div_dist
  given: {p₁ p₂ p₃ : P} (h23 : p₂ != p₃) (h31 : p₃ != p₁)
  proof: by
  simp [field, dist_ne_zero.mpr h23, dist_ne_zero.mpr h31, mul_comm (dist ..), ← law_sin]

中文:
定理 sin_angle_div_dist_eq_sin_angle_div_dist
  条件: {p₁ p₂ p₃ : P} (h23 : p₂ != p₃) (h31 : p₃ != p₁)
  证明: by
  simp [field, dist_ne_zero.mpr h23, dist_ne_zero.mpr h31, mul_comm (dist ..), ← law_sin]

Depends on / 依赖: dist_ne_zero, dist_ne_zero.mpr, law_sin, mul_comm
-/
theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ != p₃) (h31 : p₃ != p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by
  simp [field, dist_ne_zero.mpr h23, dist_ne_zero.mpr h31, mul_comm (dist ..), ← law_sin]

/--
theorem `dist_eq_dist_mul_sin_angle_div_sin_angle` / 定理 `dist_eq_dist_mul_sin_angle_div_sin_angle`

English:
theorem dist_eq_dist_mul_sin_angle_div_sin_angle
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  field_simp
  rw [mul_comm]; rw [mul_comm (dist p₃ p₁)]; rw [law_sin]

中文:
定理 dist_eq_dist_mul_sin_angle_div_sin_angle
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  field_simp
  rw [mul_comm]; rw [mul_comm (dist p₃ p₁)]; rw [law_sin]

Depends on / 依赖: Real.sin, law_sin, mul_comm, sin_gt_zero, sin_pos_of_not_collinear
-/
theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear Real ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / Real.sin (∠ p₁ p₂ p₃) := by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := sin_pos_of_not_collinear h
  field_simp
  rw [mul_comm]; rw [mul_comm (dist p₃ p₁)]; rw [law_sin]

/--
theorem `angle_eq_angle_of_dist_eq` / 定理 `angle_eq_angle_of_dist_eq`

English:
theorem angle_eq_angle_of_dist_eq
  given: {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃)
  proof: by
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert! angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

中文:
定理 angle_eq_angle_of_dist_eq
  条件: {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃)
  证明: by
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert! angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

Depends on / 依赖: angle_sub_eq_angle_sub_rev_of_norm_eq, convert, dist_eq_norm_vsub, vsub_sub_vsub_cancel_left
-/
theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert! angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

/--
theorem `dist_eq_of_angle_eq_angle_of_angle_ne_pi` / 定理 `dist_eq_of_angle_eq_angle_of_angle_ne_pi`

English:
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi
  statement: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
  proof: by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_

中文:
定理 dist_eq_of_angle_eq_angle_of_angle_ne_pi
  结论: {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
  证明: by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_

Depends on / 依赖: angle_neg_neg, dist_eq_norm_vsub, neg_vsub_eq_vsub_rev, norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi, vsub_sub_vsub_cancel_left
-/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
    (hpi : ∠ p₂ p₁ p₃ != π) : dist p₁ p₂ = dist p₁ p₃ := by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂]; rw [dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

/--
theorem `dist_eq_of_two_zsmul_oangle_eq` / 定理 `dist_eq_of_two_zsmul_oangle_eq`

English:
theorem dist_eq_of_two_zsmul_oangle_eq
  statement: [Module.Oriented Real V (Fin 2)]
  proof: by
  convert!
    (Orientation.norm_eq_of_two_zsmul_oangle_sub_eq (x := p₃ -ᵥ p₁) (y := p₂ -ᵥ p₁) ?_ ?_ h0
        hpi).symm
  · rw [dist_eq_norm_vsub']
  · rw [dist_eq_norm_vsub']
  · rw [eq_comm, o.oangle_rev, ← o.oangle_neg_neg]
    nth_rw 2 [o.oangle_rev, ← o.oangle_neg_neg]
    simp_rw [smul_ne

中文:
定理 dist_eq_of_two_zsmul_oangle_eq
  结论: [Module.Oriented 实数 V (Fin 2)]
  证明: by
  convert!
    (Orientation.norm_eq_of_two_zsmul_oangle_sub_eq (x := p₃ -ᵥ p₁) (y := p₂ -ᵥ p₁) ?_ ?_ h0
        hpi).symm
  · rw [dist_eq_norm_vsub']
  · rw [dist_eq_norm_vsub']
  · rw [eq_comm, o.oangle_rev, ← o.oangle_neg_neg]
    nth_rw 2 [o.oangle_rev, ← o.oangle_neg_neg]
    simp_rw [smul_ne

Depends on / 依赖: Orientation, Orientation.norm_eq_of_two_zsmul_oangle_sub_eq, convert, dist_eq_norm_vsub, eq_comm, neg_inj, norm_eq_of_two_zsmul_oangle_sub_eq, nth_rw, o.oangle_neg_neg, o.oangle_rev, oangle, oangle_neg_neg, oangle_rev, simp_rw, smul_neg
-/
theorem dist_eq_of_two_zsmul_oangle_eq [Module.Oriented Real V (Fin 2)]
    [Fact (Module.finrank Real V = 2)] {p₁ p₂ p₃ : P} (h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₂ p₃ p₁)
    (h0 : ∡ p₃ p₁ p₂ != 0) (hpi : ∡ p₃ p₁ p₂ != π) : dist p₁ p₂ = dist p₁ p₃ := by
  convert!
    (Orientation.norm_eq_of_two_zsmul_oangle_sub_eq (x := p₃ -ᵥ p₁) (y := p₂ -ᵥ p₁) ?_ ?_ h0
        hpi).symm
  · rw [dist_eq_norm_vsub']
  · rw [dist_eq_norm_vsub']
  · rw [eq_comm, o.oangle_rev, ← o.oangle_neg_neg]
    nth_rw 2 [o.oangle_rev, ← o.oangle_neg_neg]
    simp_rw [smul_neg, neg_inj]
    simp_rw [oangle] at h
    convert! h <;> simp

/--
theorem `angle_add_angle_add_angle_eq_pi` / 定理 `angle_add_angle_add_angle_eq_pi`

English:
theorem angle_add_angle_add_angle_eq_pi
  given: {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁)
  proof: by
  rw [add_assoc]; rw [add_comm]; rw [add_comm (∠ p₂ p₃ p₁)]; rw [angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃)]; rw [← angle_neg_neg (p₁ -ᵥ p₂)]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_v

中文:
定理 angle_add_angle_add_angle_eq_pi
  条件: {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁)
  证明: by
  rw [add_assoc]; rw [add_comm]; rw [add_comm (∠ p₂ p₃ p₁)]; rw [angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃)]; rw [← angle_neg_neg (p₁ -ᵥ p₂)]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_v

Depends on / 依赖: add_assoc, add_comm, angle_add_angle_sub_add_angle_sub_eq_pi, angle_comm, angle_neg_neg, neg_vsub_eq_vsub_rev, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right
-/
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ != p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by
  rw [add_assoc]; rw [add_comm]; rw [add_comm (∠ p₂ p₃ p₁)]; rw [angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃)]; rw [← angle_neg_neg (p₁ -ᵥ p₂)]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_vsub_cancel_right p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_right p₂ p₃ p₁]
  exact angle_add_angle_sub_add_angle_sub_eq_pi _ fun he => h (vsub_eq_zero_iff_eq.1 he)

/--
theorem `exterior_angle_eq_angle_add_angle` / 定理 `exterior_angle_eq_angle_add_angle`

English:
theorem exterior_angle_eq_angle_add_angle
  given: {p₁ p₂ p₃ : P} (p : P) (h : Sbtw Real p p₁ p₂)
  proof: by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₃ h.angle₁₂₃_eq_pi,
    angle_add_angle_add_angle_eq_pi p₃ h.right_ne.symm, angle_comm p₃ p₁ p₂]

中文:
定理 exterior_angle_eq_angle_add_angle
  条件: {p₁ p₂ p₃ : P} (p : P) (h : Sbtw 实数 p p₁ p₂)
  证明: by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₃ h.angle₁₂₃_eq_pi,
    angle_add_angle_add_angle_eq_pi p₃ h.right_ne.symm, angle_comm p₃ p₁ p₂]

Depends on / 依赖: angle_add_angle_add_angle_eq_pi, angle_add_angle_eq_pi_of_angle_eq_pi, angle_comm, h.angle, h.right_ne.symm, right_ne
-/
theorem exterior_angle_eq_angle_add_angle {p₁ p₂ p₃ : P} (p : P) (h : Sbtw Real p p₁ p₂) :
    ∠ p₃ p₁ p = ∠ p₁ p₃ p₂ + ∠ p₃ p₂ p₁ := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p₃ h.angle₁₂₃_eq_pi,
    angle_add_angle_add_angle_eq_pi p₃ h.right_ne.symm, angle_comm p₃ p₁ p₂]

/--
theorem `oangle_add_oangle_add_oangle_eq_pi` / 定理 `oangle_add_oangle_add_oangle_eq_pi`

English:
theorem oangle_add_oangle_add_oangle_eq_pi
  statement: [Module.Oriented Real V (Fin 2)]
  proof: by
  simpa only [neg_vsub_eq_vsub_rev] using!
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

中文:
定理 oangle_add_oangle_add_oangle_eq_pi
  结论: [Module.Oriented 实数 V (Fin 2)]
  证明: by
  simpa only [neg_vsub_eq_vsub_rev] using!
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

Depends on / 依赖: neg_vsub_eq_vsub_rev, oangle_add_cyc3_neg_left, positiveOrientation, positiveOrientation.oangle_add_cyc3_neg_left, vsub_ne_zero, vsub_ne_zero.mpr
-/
theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented Real V (Fin 2)]
    [Fact (Module.finrank Real V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ != p₁) (h32 : p₃ != p₂)
    (h13 : p₁ != p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by
  simpa only [neg_vsub_eq_vsub_rev] using!
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

/--
lemma `angle_add_of_ne_of_ne` / 引理 `angle_add_of_ne_of_ne`

English:
lemma angle_add_of_ne_of_ne
  given: {a b c p : P} (hb : a != b) (hc : a != c) (hp : Wbtw Real b p c)
  proof: by
  by_cases pb : p = b; · simpa [pb] using angle_self_of_ne hb.symm
  by_cases pc : p = c; · simpa [pc] using angle_self_of_ne hc.symm
  have ea := angle_add_angle_add_angle_eq_pi c hb
  have eb := angle_add_angle_add_angle_eq_pi p hb
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm
  replac

中文:
引理 angle_add_of_ne_of_ne
  条件: {a b c p : P} (hb : a != b) (hc : a != c) (hp : Wbtw 实数 b p c)
  证明: by
  by_cases pb : p = b; · simpa [pb] using angle_self_of_ne hb.symm
  by_cases pc : p = c; · simpa [pc] using angle_self_of_ne hc.symm
  have ea := angle_add_angle_add_angle_eq_pi c hb
  have eb := angle_add_angle_add_angle_eq_pi p hb
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm
  replac

Depends on / 依赖: angle_add_angle_add_angle_eq_pi, angle_comm, angle_eq_angle_of_angle_eq_pi, angle_eq_pi_iff_sbtw, angle_eq_pi_iff_sbtw.mpr, angle_self_of_ne, hb.symm, hc.symm, replace
-/
lemma angle_add_of_ne_of_ne {a b c p : P} (hb : a != b) (hc : a != c) (hp : Wbtw Real b p c) :
    ∠ b a p + ∠ p a c = ∠ b a c := by
  by_cases pb : p = b; · simpa [pb] using angle_self_of_ne hb.symm
  by_cases pc : p = c; · simpa [pc] using angle_self_of_ne hc.symm
  have ea := angle_add_angle_add_angle_eq_pi c hb
  have eb := angle_add_angle_add_angle_eq_pi p hb
  have ec := angle_add_angle_add_angle_eq_pi p hc.symm
  replace hp : ∠ b p c = π := angle_eq_pi_iff_sbtw.mpr ⟨hp, pb, pc⟩
  have hp' : ∠ c p b = π := by rwa [angle_comm] at hp
  rw [angle_comm p b a]; rw [angle_eq_angle_of_angle_eq_pi a hp]; rw [angle_comm a b c] at eb
  rw [angle_eq_angle_of_angle_eq_pi a hp']; rw [angle_comm c p a] at ec
  have ep := angle_add_angle_eq_pi_of_angle_eq_pi a hp
  linarith only [ea, eb, ec, ep]

/--
lemma `angle_add_angle_eq_of_sbtw` / 引理 `angle_add_angle_eq_of_sbtw`

English:
lemma angle_add_angle_eq_of_sbtw
  given: {a c p x : P} (hx : Sbtw Real a x c)
  proof: by
  rcases eq_or_ne p a with rfl | hpa
  · simp [(hx.angle_eq_right x).symm.trans (angle_self_of_ne hx.ne_left)]
  rcases eq_or_ne p c with rfl | hpc
  · simp [(hx.symm.angle_eq_right a).trans (angle_self_of_ne hx.left_ne_right)]
  exact angle_add_of_ne_of_ne hpa hpc hx.wbtw

中文:
引理 angle_add_angle_eq_of_sbtw
  条件: {a c p x : P} (hx : Sbtw 实数 a x c)
  证明: by
  rcases eq_or_ne p a with rfl | hpa
  · simp [(hx.angle_eq_right x).symm.trans (angle_self_of_ne hx.ne_left)]
  rcases eq_or_ne p c with rfl | hpc
  · simp [(hx.symm.angle_eq_right a).trans (angle_self_of_ne hx.left_ne_right)]
  exact angle_add_of_ne_of_ne hpa hpc hx.wbtw

Depends on / 依赖: angle_add_of_ne_of_ne, angle_eq_right, angle_self_of_ne, eq_or_ne, hx.angle_eq_right, hx.left_ne_right, hx.ne_left, hx.symm.angle_eq_right, hx.wbtw, left_ne_right, ne_left, symm.trans
-/
lemma angle_add_angle_eq_of_sbtw {a c p x : P} (hx : Sbtw Real a x c) :
    ∠ a p x + ∠ x p c = ∠ a p c := by
  rcases eq_or_ne p a with rfl | hpa
  · simp [(hx.angle_eq_right x).symm.trans (angle_self_of_ne hx.ne_left)]
  rcases eq_or_ne p c with rfl | hpc
  · simp [(hx.symm.angle_eq_right a).trans (angle_self_of_ne hx.left_ne_right)]
  exact angle_add_of_ne_of_ne hpa hpc hx.wbtw

/--
theorem `angle_add_angle_eq_of_sbtw_of_sameRay` / 定理 `angle_add_angle_eq_of_sbtw_of_sameRay`

English:
theorem angle_add_angle_eq_of_sbtw_of_sameRay
  statement: {a b c p x : P}
  proof: by
  rcases eq_or_ne p x with rfl | hpx
  · have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi]; rw [angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  obtain ⟨r, hr, hrb⟩ := (exists_pos_left_iff_sameRay (by aesop) (by aesop)).2 hxb
  have hab : ∠ a p b = ∠ a p x := angle_

中文:
定理 angle_add_angle_eq_of_sbtw_of_sameRay
  结论: {a b c p x : P}
  证明: by
  rcases eq_or_ne p x with rfl | hpx
  · have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi]; rw [angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  obtain ⟨r, hr, hrb⟩ := (exists_pos_left_iff_sameRay (by aesop) (by aesop)).2 hxb
  have hab : ∠ a p b = ∠ a p x := angle_

Depends on / 依赖: angle_add_angle_eq_of_sbtw, angle_add_angle_eq_pi_of_angle_eq_pi, angle_comm, angle_smul_left_of_pos, angle_smul_right_of_pos, eq_or_ne, exists_pos_left_iff_sameRay, hx.angle
-/
theorem angle_add_angle_eq_of_sbtw_of_sameRay {a b c p x : P}
    (hx : Sbtw Real a x c) (hxb : SameRay Real (x -ᵥ p) (b -ᵥ p)) (hb : b != p) :
    ∠ a p b + ∠ b p c = ∠ a p c := by
  rcases eq_or_ne p x with rfl | hpx
  · have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi]; rw [angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  obtain ⟨r, hr, hrb⟩ := (exists_pos_left_iff_sameRay (by aesop) (by aesop)).2 hxb
  have hab : ∠ a p b = ∠ a p x := angle_smul_right_of_pos a hr hrb
  have hbc : ∠ b p c = ∠ x p c := angle_smul_left_of_pos c hr hrb
  rw [hab]; rw [hbc]
  exact angle_add_angle_eq_of_sbtw hx

/--
theorem `dist_sq_mul_dist_add_dist_sq_mul_dist` / 定理 `dist_sq_mul_dist_add_dist_sq_mul_dist`

English:
theorem dist_sq_mul_dist_add_dist_sq_mul_dist
  given: (a b c p : P) (h : ∠ b p c = π)
  proof: by
  rw [pow_two]; rw [pow_two]; rw [law_cos a p b]; rw [law_cos a p c]; rw [eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h)]; rw [Real.cos_pi_sub]; rw [dist_eq_add_dist_of_angle_eq_pi h]
  ring

中文:
定理 dist_sq_mul_dist_add_dist_sq_mul_dist
  条件: (a b c p : P) (h : ∠ b p c = π)
  证明: by
  rw [pow_two]; rw [pow_two]; rw [law_cos a p b]; rw [law_cos a p c]; rw [eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h)]; rw [Real.cos_pi_sub]; rw [dist_eq_add_dist_of_angle_eq_pi h]
  ring

Depends on / 依赖: Real.cos_pi_sub, angle_add_angle_eq_pi_of_angle_eq_pi, cos_pi_sub, dist_eq_add_dist_of_angle_eq_pi, eq_sub_of_add_eq, law_cos, pow_two
-/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  rw [pow_two]; rw [pow_two]; rw [law_cos a p b]; rw [law_cos a p c]; rw [eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h)]; rw [Real.cos_pi_sub]; rw [dist_eq_add_dist_of_angle_eq_pi h]
  ring

/--
theorem `dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq` / 定理 `dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`

English:
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
  given: (a b c : P)
  proof: by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint Real b c
    have : dist b c != 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_m

中文:
定理 dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
  条件: (a b c : P)
  证明: by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint Real b c
    have : dist b c != 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_m

Depends on / 依赖: Real.norm_two, angle_midpoint_eq_pi, dist_left_midpoint, dist_pos, dist_pos.mpr, dist_right_midpoint, dist_self, dist_sq_mul_dist_add_dist_sq_mul_dist, midpoint, midpoint_self, norm_two, two_mul
-/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint Real b c) ^ 2 + (dist b c / 2) ^ 2) := by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint Real b c
    have : dist b c != 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm
    calc
      dist a b ^ 2 + dist a c ^ 2 = 2 / dist b c * (dist a b ^ 2 *
        ((2 : Real)⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) := by
        field
      _ = 2 * (dist a (midpoint Real b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        field

/--
theorem `dist_mul_of_eq_angle_of_dist_mul` / 定理 `dist_mul_of_eq_angle_of_dist_mul`

English:
theorem dist_mul_of_eq_angle_of_dist_mul
  statement: (a b c a' b' c' : P) (r : Real) (h : ∠ a' b' c' = ∠ a b c)
  proof: by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos

中文:
定理 dist_mul_of_eq_angle_of_dist_mul
  结论: (a b c a' b' c' : P) (r : 实数) (h : ∠ a' b' c' = ∠ a b c)
  证明: by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos

Depends on / 依赖: Real.cos, dist_eq_zero, dist_eq_zero.mpr, law_cos, pow_two
-/
theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : Real) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h]; rw [hab]; rw [hcb]; ring
    _ = (r * dist a c) ^ 2 := by simp [pow_two, ← law_cos a b c]; ring
  by_cases hab₁ : a = b
  · have hab'₁ : a' = b' := by
      rw [← dist_eq_zero]; rw [hab]; rw [dist_eq_zero.mpr hab₁]; rw [mul_zero r]
    rw [hab₁]; rw [hab'₁]; rw [dist_comm b' c']; rw [dist_comm b c]; rw [hcb]
  · have h1 : 0 <= r * dist a b := by rw [← hab]; exact dist_nonneg
    have h2 : 0 <= r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁)
    exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

/--
theorem `dist_lt_of_angle_lt` / 定理 `dist_lt_of_angle_lt`

English:
theorem dist_lt_of_angle_lt
  given: {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P))
  proof: by
  have hsin := law_sin c b a
  rw [dist_comm b a]; rw [angle_comm c b a] at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hsinabc : Real.sin (∠ a b c) >= 0 := by
    apply Real.sin_nonneg_of_mem_Icc
    simp [angle_nonneg, angle_le_pi]
  intro h1
  by_cases! h2 :

中文:
定理 dist_lt_of_angle_lt
  条件: {a b c : P} (h : ¬Collinear 实数 ({a, b, c} : Set P))
  证明: by
  have hsin := law_sin c b a
  rw [dist_comm b a]; rw [angle_comm c b a] at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hsinabc : Real.sin (∠ a b c) >= 0 := by
    apply Real.sin_nonneg_of_mem_Icc
    simp [angle_nonneg, angle_le_pi]
  intro h1
  by_cases! h2 :

Depends on / 依赖: Real.sin, Real.sin_lt_sin_of_lt_of_le_pi_div_two, Real.sin_nonneg_of_mem_Icc, angle_comm, angle_le_pi, angle_nonneg, dist_comm, dist_pos, dist_pos.mpr, hsinabc, law_sin, sin_lt_sin_of_lt_of_le_pi_div_two, sin_nonneg_of_mem_Icc
-/
theorem dist_lt_of_angle_lt {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c -> dist a b < dist a c := by
  have hsin := law_sin c b a
  rw [dist_comm b a]; rw [angle_comm c b a] at hsin
  have hac : dist a c > 0 := dist_pos.mpr (ne₁₃_of_not_collinear h)
  have hsinabc : Real.sin (∠ a b c) >= 0 := by
    apply Real.sin_nonneg_of_mem_Icc
    simp [angle_nonneg, angle_le_pi]
  intro h1
  by_cases! h2 : ∠ a b c <= π / 2
  · have h3 : Real.sin (∠ a c b) < Real.sin (∠ a b c) := by
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h2 h1
    by_contra! w
    have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
      exact mul_lt_mul h3 w hac hsinabc
    linarith
  · by_contra! w
    have h3 : Real.sin (∠ a b c) <= Real.sin (∠ a c b) := by
      by_contra! w1
      have h4 : Real.sin (∠ a c b) * dist a c < Real.sin (∠ a b c) * dist a b := by
        exact mul_lt_mul w1 w hac hsinabc
      linarith
    rw [← Real.sin_pi_sub (∠ a b c)] at h3
    have h5 : π - ∠ a b c < π / 2 := by linarith
    have h6 : π - ∠ a b c <= ∠ a c b := by
      by_contra! w1
      have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [angle_nonneg a c b]) h5.le w1
      linarith
    have h7 := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h).symm
    rw [angle_comm b c a] at h7
    have h8 : ∠ c a b > 0 := by
      rw [angle_comm]
      rw [show ({a]; rw [b]; rw [c} : Set P) = {b]; rw [a]; rw [c} by exact Set.insert_comm a b {c}] at h
      exact angle_pos_of_not_collinear h
    linarith

/--
theorem `angle_lt_iff_dist_lt` / 定理 `angle_lt_iff_dist_lt`

English:
theorem angle_lt_iff_dist_lt
  given: {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P))
  proof: by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        rw [show ({a]; rw [b]; rw [c} : Set P) = {b]; rw [a

中文:
定理 angle_lt_iff_dist_lt
  条件: {a b c : P} (h : ¬Collinear 实数 ({a, b, c} : Set P))
  证明: by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        rw [show ({a]; rw [b]; rw [c} : Set P) = {b]; rw [a

Depends on / 依赖: Set.insert_comm, angle_lt_pi_of_not_collinear, dist_eq_of_angle_eq_angle_of_angle_ne_pi, dist_lt_of_angle_lt, eq_or_lt, insert_comm, w.eq_or_lt
-/
theorem angle_lt_iff_dist_lt {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P)) :
    ∠ a c b < ∠ a b c ↔ dist a b < dist a c := by
  constructor
  case mp =>
    exact dist_lt_of_angle_lt h
  case mpr =>
    intro h1
    by_contra! w
    rcases w.eq_or_lt with h2 | h3
    · have h4 : dist a b = dist a c := by
        apply dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
        rw [show ({a]; rw [b]; rw [c} : Set P) = {b]; rw [a]; rw [c} by exact Set.insert_comm a b {c}] at h
        linarith [angle_lt_pi_of_not_collinear h]
      linarith
    · rw [show ({a, b, c} : Set P) = {a, c, b} by grind] at h
      have h5 := dist_lt_of_angle_lt h h3
      linarith

/--
theorem `angle_le_iff_dist_le` / 定理 `angle_le_iff_dist_le`

English:
theorem angle_le_iff_dist_le
  given: {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P))
  proof: by
  rw [show ({a]; rw [b]; rw [c} : Set P) = {a]; rw [c]; rw [b} by grind] at h
  simpa using (angle_lt_iff_dist_lt h).not

中文:
定理 angle_le_iff_dist_le
  条件: {a b c : P} (h : ¬Collinear 实数 ({a, b, c} : Set P))
  证明: by
  rw [show ({a]; rw [b]; rw [c} : Set P) = {a]; rw [c]; rw [b} by grind] at h
  simpa using (angle_lt_iff_dist_lt h).not

Depends on / 依赖: angle_lt_iff_dist_lt
-/
theorem angle_le_iff_dist_le {a b c : P} (h : ¬Collinear Real ({a, b, c} : Set P)) :
    ∠ a c b <= ∠ a b c ↔ dist a b <= dist a c := by
  rw [show ({a]; rw [b]; rw [c} : Set P) = {a]; rw [c]; rw [b} by grind] at h
  simpa using (angle_lt_iff_dist_lt h).not

/--
lemma `pi_div_three_le_angle_of_le_of_le` / 引理 `pi_div_three_le_angle_of_le_of_le`

English:
lemma pi_div_three_le_angle_of_le_of_le
  statement: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
  proof: by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

中文:
引理 pi_div_three_le_angle_of_le_of_le
  结论: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
  证明: by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

Depends on / 依赖: Real.pi_pos, angle_add_angle_add_angle_eq_pi, angle_self_left, pi_pos
-/
lemma pi_div_three_le_angle_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃) : π / 3 <= ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/--
lemma `pi_div_three_lt_angle_of_le_of_le_of_ne` / 引理 `pi_div_three_lt_angle_of_le_of_le_of_ne`

English:
lemma pi_div_three_lt_angle_of_le_of_le_of_ne
  statement: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
  proof: by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

中文:
引理 pi_div_three_lt_angle_of_le_of_le_of_ne
  结论: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
  证明: by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

Depends on / 依赖: Real.pi_pos, angle_add_angle_add_angle_eq_pi, angle_self_left, hne.lt_or_gt, lt_or_gt, pi_pos
-/
lemma pi_div_three_lt_angle_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₂ p₃ p₁ <= ∠ p₁ p₂ p₃)
    (h₃₁₂ : ∠ p₃ p₁ p₂ <= ∠ p₁ p₂ p₃)
    (hne : ∠ p₁ p₂ p₃ != ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂) :
    π / 3 < ∠ p₁ p₂ p₃ := by
  by_cases h : p₂ = p₁
  · rw [h, angle_self_left]
    linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/--
lemma `angle_le_pi_div_three_of_le_of_le` / 引理 `angle_le_pi_div_three_of_le_of_le`

English:
lemma angle_le_pi_div_three_of_le_of_le
  statement: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
  proof: by
  by_cases h : p₂ = p₁
  · subst h
    simp_all [angle_self_of_ne]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

中文:
引理 angle_le_pi_div_three_of_le_of_le
  结论: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
  证明: by
  by_cases h : p₂ = p₁
  · subst h
    simp_all [angle_self_of_ne]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

Depends on / 依赖: Real.pi_pos, angle_add_angle_add_angle_eq_pi, angle_self_of_ne, pi_pos
-/
lemma angle_le_pi_div_three_of_le_of_le {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂) (hnd : p₁ != p₂ ∨ p₁ != p₃ ∨ p₂ != p₃) :
    ∠ p₁ p₂ p₃ <= π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    simp_all [angle_self_of_ne]
    linarith [Real.pi_pos]
  · linarith [angle_add_angle_add_angle_eq_pi p₃ h]

/--
lemma `angle_lt_pi_div_three_of_le_of_le_of_ne` / 引理 `angle_lt_pi_div_three_of_le_of_le_of_ne`

English:
lemma angle_lt_pi_div_three_of_le_of_le_of_ne
  statement: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
  proof: by
  by_cases h : p₂ = p₁
  · subst h
    by_cases h₂₃ : p₂ = p₃
    · subst h₂₃
      simp at hne
    · simp_all [angle_self_of_ne]
      linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

中文:
引理 angle_lt_pi_div_three_of_le_of_le_of_ne
  结论: {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
  证明: by
  by_cases h : p₂ = p₁
  · subst h
    by_cases h₂₃ : p₂ = p₃
    · subst h₂₃
      simp at hne
    · simp_all [angle_self_of_ne]
      linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

Depends on / 依赖: Real.pi_pos, angle_add_angle_add_angle_eq_pi, angle_self_of_ne, hne.lt_or_gt, lt_or_gt, pi_pos
-/
lemma angle_lt_pi_div_three_of_le_of_le_of_ne {p₁ p₂ p₃ : P} (h₂₃₁ : ∠ p₁ p₂ p₃ <= ∠ p₂ p₃ p₁)
    (h₃₁₂ : ∠ p₁ p₂ p₃ <= ∠ p₃ p₁ p₂)
    (hne : ∠ p₁ p₂ p₃ != ∠ p₂ p₃ p₁ ∨ ∠ p₁ p₂ p₃ != ∠ p₃ p₁ p₂ ∨ ∠ p₂ p₃ p₁ != ∠ p₃ p₁ p₂) :
    ∠ p₁ p₂ p₃ < π / 3 := by
  by_cases h : p₂ = p₁
  · subst h
    by_cases h₂₃ : p₂ = p₃
    · subst h₂₃
      simp at hne
    · simp_all [angle_self_of_ne]
      linarith [Real.pi_pos]
  · rcases hne with hne | hne | hne <;>
      rcases hne.lt_or_gt with hne | hne <;>
      linarith [angle_add_angle_add_angle_eq_pi p₃ h]

end EuclideanGeometry
