/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometric results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
variable [hd2 : Fact (finrank Real V = 2)] (o : Orientation Real V (Fin 2))

/--
theorem `oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

中文:
定理 oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, angle_add_eq_arccos_of_inner_eq_zero, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h

中文:
定理 oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h

/--
theorem `oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.

中文:
定理 oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, angle_add_eq_arcsin_of_inner_eq_zero, inner_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h

中文:
定理 oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h

/--
theorem `oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_o

中文:
定理 oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_o

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, angle_add_eq_arctan_of_inner_eq_zero, inner_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h

中文:
定理 oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h

/--
theorem `cos_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

中文:
定理 cos_oangle_add_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.cos_angle_add_of_inner_eq_zero, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_angle_add_of_inner_eq_zero, cos_coe, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 cos_oangle_add_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, cos_oangle_add_right_of_oangle_eq_pi_div_two, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `sin_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
    

中文:
定理 sin_oangle_add_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
    

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.sin_angle_add_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two, sin_angle_add_of_inner_eq_zero, sin_coe
-/
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `sin_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 sin_oangle_add_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, sin_oangle_add_right_of_oangle_eq_pi_div_two
-/
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `tan_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

中文:
定理 tan_oangle_add_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.tan_angle_add_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two, tan_angle_add_of_inner_eq_zero, tan_coe
-/
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `tan_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 tan_oangle_add_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, tan_oangle_add_right_of_oangle_eq_pi_div_two
-/
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_angle_add_mul_norm_of_inner_eq_zero, cos_coe, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two, sin_angle_add_mul_norm_of_inner_eq_zero, sin_coe
-/
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
-/
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two, tan_angle_add_mul_norm_of_inner_eq_zero, tan_coe
-/
theorem tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) * ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two
-/
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero, Or.inl, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_coe, inner_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, norm_div_cos_angle_add_of_inner_eq_zero, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, sign_coe_pi_div_two
-/
theorem norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero, Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_eq_zero_of_oangle_eq_pi_div_two, norm_div_sin_angle_add_of_inner_eq_zero, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, sin_coe
-/
theorem norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

中文:
定理 norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero, Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_eq_zero_of_oangle_eq_pi_div_two, norm_div_tan_angle_add_of_inner_eq_zero, o.inner_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_add_right, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, tan_coe
-/
theorem norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle x (x + y)) = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: add_comm, neg_inj, norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle (x + y) y) = ‖y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h

/--
theorem `oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

中文:
定理 oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, angle_sub_eq_arccos_of_inner_eq_zero, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two
-/
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h

中文:
定理 oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two
-/
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h

/--
theorem `oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (O

中文:
定理 oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (O

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, angle_sub_eq_arcsin_of_inner_eq_zero, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two
-/
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h

中文:
定理 oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two
-/
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h

/--
theorem `oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right

中文:
定理 oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, angle_sub_eq_arctan_of_inner_eq_zero, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two
-/
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h

中文:
定理 oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two
-/
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h

/--
theorem `cos_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

中文:
定理 cos_oangle_sub_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.cos_angle_sub_of_inner_eq_zero, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_angle_sub_of_inner_eq_zero, cos_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two
-/
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 cos_oangle_sub_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: cos_oangle_sub_right_of_oangle_eq_pi_div_two, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `sin_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_sub_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

中文:
定理 sin_oangle_sub_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.sin_angle_sub_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, sin_angle_sub_of_inner_eq_zero, sin_coe
-/
theorem sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `sin_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 sin_oangle_sub_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, sin_oangle_sub_right_of_oangle_eq_pi_div_two
-/
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `tan_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

中文:
定理 tan_oangle_sub_right_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.tan_angle_sub_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two, tan_angle_sub_of_inner_eq_zero, tan_coe
-/
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `tan_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = ↑(π / 2))
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 tan_oangle_sub_left_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = ↑(π / 2))
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, tan_oangle_sub_right_of_oangle_eq_pi_div_two
-/
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_angle_sub_mul_norm_of_inner_eq_zero, cos_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two
-/
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two, neg_inj, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two, sin_angle_sub_mul_norm_of_inner_eq_zero, sin_coe
-/
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/--
theorem `sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
-/
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero, Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, tan_angle_sub_mul_norm_of_inner_eq_zero, tan_coe
-/
theorem tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) * ‖y‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

中文:
定理 tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, oangle_neg_orientation_eq_neg, oangle_rev, tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two
-/
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero, Or.inl, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, cos_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, norm_div_cos_angle_sub_of_inner_eq_zero, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, o.right_ne_zero_of_oangle_eq_pi_div_two, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, right_ne_zero_of_oangle_eq_pi_div_two, sign_coe_pi_div_two
-/
theorem norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero, Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, norm_div_sin_angle_sub_of_inner_eq_zero, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two, sin_coe
-/
theorem norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two` / 定理 `norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two`

English:
theorem norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

中文:
定理 norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oang

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero, Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, inner_rev_eq_zero_of_oangle_eq_pi_div_two, left_ne_zero_of_oangle_eq_pi_div_two, norm_div_tan_angle_sub_of_inner_eq_zero, o.inner_rev_eq_zero_of_oangle_eq_pi_div_two, o.left_ne_zero_of_oangle_eq_pi_div_two, o.oangle, o.oangle_eq_angle_of_sign_eq_one, oangle, oangle_eq_angle_of_sign_eq_one, oangle_sign_sub_right_swap, sign_coe_pi_div_two, tan_coe
-/
theorem norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle y (y - x)) = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/--
theorem `norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two` / 定理 `norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two`

English:
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two
  statement: {x y : V}
  proof: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h

中文:
定理 norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two
  结论: {x y : V}
  证明: by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h

Depends on / 依赖: neg_inj, norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev
-/
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle (x - y) x) = ‖x‖ := by
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj] at h ⊢
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h

/--
theorem `oangle_add_right_smul_rotation_pi_div_two` / 定理 `oangle_add_right_smul_rotation_pi_div_two`

English:
theorem oangle_add_right_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : Real) x) = -(π / 2 : Real) := by
      rw [o.oangle_smul_right_of_neg _ _ hr]; rw [o.oangle_neg_right h]; rw [o.oangle_rotation_self_right h]; rw [←
        sub_eq_zero]; rw [add_comm]; rw [sub_neg_e

中文:
定理 oangle_add_right_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : Real) x) = -(π / 2 : Real) := by
      rw [o.oangle_smul_right_of_neg _ _ hr]; rw [o.oangle_neg_right h]; rw [o.oangle_rotation_self_right h]; rw [←
        sub_eq_zero]; rw [add_comm]; rw [sub_neg_e

Depends on / 依赖: Real.Angle.coe_add, Real.Angle.coe_two_pi, add_assoc, add_comm, add_halves, coe_add, coe_two_pi, lt_trichotomy, neg_inj, neg_neg, o.oangle, o.oangle_neg_right, o.oangle_rotation_self_right, o.oangle_smul_right_of_neg, o.rotation, oangle, oangle_neg_orientation_eq_neg, oangle_neg_right, oangle_rotation_self_right, oangle_smul_right_of_neg
-/
theorem oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    o.oangle x (x + r • o.rotation (π / 2 : Real) x) = Real.arctan r := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : Real) x) = -(π / 2 : Real) := by
      rw [o.oangle_smul_right_of_neg _ _ hr]; rw [o.oangle_neg_right h]; rw [o.oangle_rotation_self_right h]; rw [←
        sub_eq_zero]; rw [add_comm]; rw [sub_neg_eq_add]; rw [← Real.Angle.coe_add]; rw [← Real.Angle.coe_add]; rw [add_assoc]; rw [add_halves]; rw [← two_mul]; rw [Real.Angle.coe_two_pi]
      simpa using h
    rw [← neg_inj]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_neg] at ha
    rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj]; rw [oangle_rev]; rw [(-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha]; rw [norm_smul]; rw [LinearIsometryEquiv.norm_map]; rw [mul_div_assoc]; rw [div_self (norm_ne_zero_iff.2 h)]; rw [mul_one]; rw [Real.norm_eq_abs]; rw [abs_of_neg hr]; rw [Real.arctan_neg]; rw [Real.Angle.coe_neg]; rw [neg_neg]
  · simp
  · have ha : o.oangle x (r • o.rotation (π / 2 : Real) x) = (π / 2 : Real) := by
      rw [o.oangle_smul_right_of_pos _ _ hr]; rw [o.oangle_rotation_self_right h]
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha]; rw [norm_smul]; rw [LinearIsometryEquiv.norm_map]; rw [mul_div_assoc]; rw [div_self (norm_ne_zero_iff.2 h)]; rw [mul_one]; rw [Real.norm_eq_abs]; rw [abs_of_pos hr]

/--
theorem `oangle_add_left_smul_rotation_pi_div_two` / 定理 `oangle_add_left_smul_rotation_pi_div_two`

English:
theorem oangle_add_left_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  by_cases hr : r = 0; · simp [hr]
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj]; rw [←
    neg_neg ((π / 2 : Real) : Real.Angle)]; rw [← rotation_neg_orientation_eq_neg]; rw [add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : Real) (r • (-o).rotation (

中文:
定理 oangle_add_left_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  by_cases hr : r = 0; · simp [hr]
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj]; rw [←
    neg_neg ((π / 2 : Real) : Real.Angle)]; rw [← rotation_neg_orientation_eq_neg]; rw [add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : Real) (r • (-o).rotation (

Depends on / 依赖: Real.Angle, add_comm, neg_inj, neg_neg, nth_rw, oangle_add_right_smul_rotation_pi_div_two, oangle_neg_orientation_eq_neg, oangle_rev, rotation, rotation_neg_orientation_eq_neg
-/
theorem oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    o.oangle (x + r • o.rotation (π / 2 : Real) x) (r • o.rotation (π / 2 : Real) x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  rw [← neg_inj]; rw [oangle_rev]; rw [← oangle_neg_orientation_eq_neg]; rw [neg_inj]; rw [←
    neg_neg ((π / 2 : Real) : Real.Angle)]; rw [← rotation_neg_orientation_eq_neg]; rw [add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : Real) (r • (-o).rotation (-(π / 2 : Real)) x) := by simp [hr]
  nth_rw 3 [hx]
  refine (-o).oangle_add_right_smul_rotation_pi_div_two ?_ _
  simp [hr, h]

/--
theorem `tan_oangle_add_right_smul_rotation_pi_div_two` / 定理 `tan_oangle_add_right_smul_rotation_pi_div_two`

English:
theorem tan_oangle_add_right_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

中文:
定理 tan_oangle_add_right_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

Depends on / 依赖: Real.Angle.tan_coe, Real.tan_arctan, o.oangle_add_right_smul_rotation_pi_div_two, oangle_add_right_smul_rotation_pi_div_two, tan_arctan, tan_coe
-/
theorem tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : Real) x)) = r := by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

/--
theorem `tan_oangle_add_left_smul_rotation_pi_div_two` / 定理 `tan_oangle_add_left_smul_rotation_pi_div_two`

English:
theorem tan_oangle_add_left_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

中文:
定理 tan_oangle_add_left_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

Depends on / 依赖: Real.Angle.tan_coe, Real.tan_arctan, o.oangle_add_left_smul_rotation_pi_div_two, oangle_add_left_smul_rotation_pi_div_two, tan_arctan, tan_coe
-/
theorem tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : Real) x) (r • o.rotation (π / 2 : Real) x)) =
      r⁻¹ := by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h]; rw [Real.Angle.tan_coe]; rw [Real.tan_arctan]

/--
theorem `oangle_sub_right_smul_rotation_pi_div_two` / 定理 `oangle_sub_right_smul_rotation_pi_div_two`

English:
theorem oangle_sub_right_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  by_cases hr : r = 0; · simp [hr]
  have hx : -x = r⁻¹ • o.rotation (π / 2 : Real) (r • o.rotation (π / 2 : Real) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [hx]; rw [o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

中文:
定理 oangle_sub_right_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  by_cases hr : r = 0; · simp [hr]
  have hx : -x = r⁻¹ • o.rotation (π / 2 : Real) (r • o.rotation (π / 2 : Real) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [hx]; rw [o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

Depends on / 依赖: Real.Angle.coe_add, coe_add, o.oangle_add_right_smul_rotation_pi_div_two, o.rotation, oangle_add_right_smul_rotation_pi_div_two, rotation, sub_eq_add_neg
-/
theorem oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    o.oangle (r • o.rotation (π / 2 : Real) x) (r • o.rotation (π / 2 : Real) x - x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  have hx : -x = r⁻¹ • o.rotation (π / 2 : Real) (r • o.rotation (π / 2 : Real) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [hx]; rw [o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

/--
theorem `oangle_sub_left_smul_rotation_pi_div_two` / 定理 `oangle_sub_left_smul_rotation_pi_div_two`

English:
theorem oangle_sub_left_smul_rotation_pi_div_two
  given: {x : V} (h : x != 0) (r : Real)
  proof: by
  by_cases hr : r = 0; · simp [hr]
  have hx : x = r⁻¹ • o.rotation (π / 2 : Real) (-(r • o.rotation (π / 2 : Real) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [add_comm]
  nth_rw 3 [hx]
  nth_rw 2 [hx]
  rw [o.oangle_add_left_smul_rotation_pi_div_two]; rw [inv_inv]
  

中文:
定理 oangle_sub_left_smul_rotation_pi_div_two
  条件: {x : V} (h : x != 0) (r : 实数)
  证明: by
  by_cases hr : r = 0; · simp [hr]
  have hx : x = r⁻¹ • o.rotation (π / 2 : Real) (-(r • o.rotation (π / 2 : Real) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [add_comm]
  nth_rw 3 [hx]
  nth_rw 2 [hx]
  rw [o.oangle_add_left_smul_rotation_pi_div_two]; rw [inv_inv]
  

Depends on / 依赖: Real.Angle.coe_add, add_comm, coe_add, inv_inv, nth_rw, o.oangle_add_left_smul_rotation_pi_div_two, o.rotation, oangle_add_left_smul_rotation_pi_div_two, rotation, sub_eq_add_neg
-/
theorem oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
    o.oangle (x - r • o.rotation (π / 2 : Real) x) x = Real.arctan r := by
  by_cases hr : r = 0; · simp [hr]
  have hx : x = r⁻¹ • o.rotation (π / 2 : Real) (-(r • o.rotation (π / 2 : Real) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg]; rw [add_comm]
  nth_rw 3 [hx]
  nth_rw 2 [hx]
  rw [o.oangle_add_left_smul_rotation_pi_div_two]; rw [inv_inv]
  simpa [hr] using h

end Orientation

namespace EuclideanGeometry

open Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

/--
theorem `oangle_right_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_right_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 oangle_right_eq_arccos_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, angle_eq_arccos_of_angle_eq_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_left_eq_arccos_of_oangle_eq_pi_div_two` / 定理 `oangle_left_eq_arccos_of_oangle_eq_pi_div_two`

English:
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

中文:
定理 oangle_left_eq_arccos_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, angle_comm, angle_eq_arccos_of_angle_eq_pi_div_two, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_comm, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arccos (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

/--
theorem `oangle_right_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_right_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

中文:
定理 oangle_right_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, angle_eq_arcsin_of_angle_eq_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `oangle_left_eq_arcsin_of_oangle_eq_pi_div_two` / 定理 `oangle_left_eq_arcsin_of_oangle_eq_pi_div_two`

English:
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div

中文:
定理 oangle_left_eq_arcsin_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div

Depends on / 依赖: Or.inr, Real.Angle.sign_coe_pi_div_two, angle_comm, angle_eq_arcsin_of_angle_eq_pi_div_two, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_comm, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arcsin (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]; rw [dist_comm p₁ p₃]

/--
theorem `oangle_right_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_right_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]

中文:
定理 oangle_right_eq_arctan_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, angle_eq_arctan_of_angle_eq_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, right_ne_of_oangle_eq_pi_div_two, sign_coe_pi_div_two
-/
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]

/--
theorem `oangle_left_eq_arctan_of_oangle_eq_pi_div_two` / 定理 `oangle_left_eq_arctan_of_oangle_eq_pi_div_two`

English:
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]

中文:
定理 oangle_left_eq_arctan_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, angle_comm, angle_eq_arctan_of_angle_eq_pi_div_two, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arctan (dist p₃ p₂ / dist p₁ p₂) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]

/--
lemma `abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two` / 引理 `abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two`

English:
lemma abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  by_cases hp₂ : p₂ = p₃
  · simp [hp₂, Real.pi_pos]
  by_cases hp₁ : p₁ = p₃
  · simp [hp₁, Real.pi_pos]
  rw [← angle_eq_abs_oangle_toReal hp₂ hp₁]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h (Ne.symm hp₂)

中文:
引理 abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  by_cases hp₂ : p₂ = p₃
  · simp [hp₂, Real.pi_pos]
  by_cases hp₁ : p₁ = p₃
  · simp [hp₁, Real.pi_pos]
  rw [← angle_eq_abs_oangle_toReal hp₂ hp₁]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h (Ne.symm hp₂)

Depends on / 依赖: Ne.symm, Real.pi_pos, angle_eq_abs_oangle_toReal, angle_lt_pi_div_two_of_angle_eq_pi_div_two, pi_pos
-/
lemma abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∠ p₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2 := by
  by_cases hp₂ : p₂ = p₃
  · simp [hp₂, Real.pi_pos]
  by_cases hp₁ : p₁ = p₃
  · simp [hp₁, Real.pi_pos]
  rw [← angle_eq_abs_oangle_toReal hp₂ hp₁]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h (Ne.symm hp₂)

/--
lemma `oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two` / 引理 `oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two`

English:
lemma oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

中文:
引理 oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

Depends on / 依赖: Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two, abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two, two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
-/
lemma oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₅ p₆ p₄) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₅ p₆ p₄ := by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

/--
lemma `oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two` / 引理 `oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two`

English:
lemma oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev]; rw [Real.Angle.abs_toReal_neg]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

中文:
引理 oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev]; rw [Real.Angle.abs_toReal_neg]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

Depends on / 依赖: Real.Angle.abs_toReal_neg, Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two, abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two, abs_toReal_neg, oangle_rev, two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
-/
lemma oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₄ p₆ p₅) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₄ p₆ p₅ := by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev]; rw [Real.Angle.abs_toReal_neg]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

/--
theorem `cos_oangle_right_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_right_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 cos_oangle_right_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_angle_of_angle_eq_pi_div_two, cos_coe, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_left_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_left_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

中文:
定理 cos_oangle_left_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

Depends on / 依赖: Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_angle_of_angle_eq_pi_div_two, cos_coe, dist_comm, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]; rw [dist_comm p₁ p₃]

/--
theorem `sin_oangle_right_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_right_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two

中文:
定理 sin_oangle_right_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, sin_angle_of_angle_eq_pi_div_two, sin_coe
-/
theorem sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `sin_oangle_left_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_left_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_

中文:
定理 sin_oangle_left_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_

Depends on / 依赖: Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_comm, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, sin_angle_of_angle_eq_pi_div_two, sin_coe
-/
theorem sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]; rw [dist_comm p₁ p₃]

/--
theorem `tan_oangle_right_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_right_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 tan_oangle_right_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, tan_angle_of_angle_eq_pi_div_two, tan_coe
-/
theorem tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `tan_oangle_left_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_left_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 tan_oangle_left_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, tan_angle_of_angle_eq_pi_div_two, tan_coe
-/
theorem tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_angle_mul_dist_of_angle_eq_pi_div_two, cos_coe, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two` / 定理 `cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

中文:
定理 cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

Depends on / 依赖: Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_angle_mul_dist_of_angle_eq_pi_div_two, cos_coe, dist_comm, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

中文:
定理 sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, sin_angle_mul_dist_of_angle_eq_pi_div_two, sin_coe
-/
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two` / 定理 `sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

中文:
定理 sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

Depends on / 依赖: Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_comm, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, sin_angle_mul_dist_of_angle_eq_pi_div_two, sin_coe
-/
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/--
theorem `tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_

中文:
定理 tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_

Depends on / 依赖: Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, right_ne_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, tan_angle_mul_dist_of_angle_eq_pi_div_two, tan_coe
-/
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two` / 定理 `tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two`

English:
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr 

中文:
定理 tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr 

Depends on / 依赖: Or.inr, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, tan_angle_mul_dist_of_angle_eq_pi_div_two, tan_coe
-/
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_cos_oangle_right_of_oangle_eq_pi_div_two` / 定理 `dist_div_cos_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_

中文:
定理 dist_div_cos_oangle_right_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_

Depends on / 依赖: Or.inr, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_coe, dist_div_cos_angle_of_angle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, right_ne_of_oangle_eq_pi_div_two, sign_coe_pi_div_two
-/
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.cos_coe]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_cos_oangle_left_of_oangle_eq_pi_div_two` / 定理 `dist_div_cos_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

中文:
定理 dist_div_cos_oangle_left_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

Depends on / 依赖: Or.inr, Real.Angle.cos_coe, Real.Angle.sign_coe_pi_div_two, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, cos_coe, dist_comm, dist_div_cos_angle_of_angle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two
-/
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.cos_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_sin_oangle_right_of_oangle_eq_pi_div_two` / 定理 `dist_div_sin_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_p

中文:
定理 dist_div_sin_oangle_right_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_p

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_div_sin_angle_of_angle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, sin_coe
-/
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.sin_coe]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_sin_oangle_left_of_oangle_eq_pi_div_two` / 定理 `dist_div_sin_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

中文:
定理 dist_div_sin_oangle_left_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.sin_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_comm, dist_div_sin_angle_of_angle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, right_ne_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, sin_coe
-/
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.sin_coe]; rw [dist_comm p₁ p₃]; rw [dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_tan_oangle_right_of_oangle_eq_pi_div_two` / 定理 `dist_div_tan_oangle_right_of_oangle_eq_pi_div_two`

English:
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_p

中文:
定理 dist_div_tan_oangle_right_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_p

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_div_tan_angle_of_angle_eq_pi_div_two, left_ne_of_oangle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, sign_coe_pi_div_two, tan_coe
-/
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/--
theorem `dist_div_tan_oangle_left_of_oangle_eq_pi_div_two` / 定理 `dist_div_tan_oangle_left_of_oangle_eq_pi_div_two`

English:
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl 

中文:
定理 dist_div_tan_oangle_left_of_oangle_eq_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl 

Depends on / 依赖: Or.inl, Real.Angle.sign_coe_pi_div_two, Real.Angle.tan_coe, angle_comm, angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two, dist_div_tan_angle_of_angle_eq_pi_div_two, oangle_eq_angle_of_sign_eq_one, oangle_rotate_sign, right_ne_of_oangle_eq_pi_div_two, sign_coe_pi_div_two, tan_coe
-/
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs]; rw [angle_comm]; rw [Real.Angle.tan_coe]; rw [dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

end EuclideanGeometry
