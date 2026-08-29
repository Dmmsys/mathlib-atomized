/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `Orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

## Implementation notes

The definitions here use the `Real.Angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/

@[expose] public section


noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup V']
variable [InnerProductSpace Real V] [InnerProductSpace Real V']
variable [Fact (finrank Real V = 2)] [Fact (finrank Real V' = 2)] (o : Orientation Real V (Fin 2))

local notation "ω" => o.areaForm

/--
Definition of `oangle` / `oangle` 的定义

English:
definition oangle
  signature: (x y : V)
  body: Complex.arg (o.kahler x y)

中文:
定义 oangle
  签名: (x y : V)
  定义体: Complex.arg (o.kahler x y)

Depends on / 依赖: Complex.arg, kahler, o.kahler
-/
def oangle (x y : V) : Real.Angle :=
  Complex.arg (o.kahler x y)

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
@[fun_prop]
/--
theorem `continuousAt_oangle` / 定理 `continuousAt_oangle`

English:
theorem continuousAt_oangle
  given: {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0)
  proof: by
  refine (Complex.continuousAt_arg_coe_angle ?_).comp ?_
  · exact o.kahler_ne_zero hx1 hx2
  exact ((continuous_ofReal.comp continuous_inner).add
    ((continuous_ofReal.comp o.areaForm'.continuous₂).mul continuous_const)).continuousAt

中文:
定理 continuousAt_oangle
  条件: {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0)
  证明: by
  refine (Complex.continuousAt_arg_coe_angle ?_).comp ?_
  · exact o.kahler_ne_zero hx1 hx2
  exact ((continuous_ofReal.comp continuous_inner).add
    ((continuous_ofReal.comp o.areaForm'.continuous₂).mul continuous_const)).continuousAt

Depends on / 依赖: Complex.continuousAt_arg_coe_angle, areaForm, continuousAt, continuousAt_arg_coe_angle, continuous_const, continuous_inner, continuous_ofReal, continuous_ofReal.comp, kahler_ne_zero, o.areaForm, o.kahler_ne_zero
-/
theorem continuousAt_oangle {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0) :
    ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x := by
  refine (Complex.continuousAt_arg_coe_angle ?_).comp ?_
  · exact o.kahler_ne_zero hx1 hx2
  exact ((continuous_ofReal.comp continuous_inner).add
    ((continuous_ofReal.comp o.areaForm'.continuous₂).mul continuous_const)).continuousAt

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp]
/--
theorem `oangle_zero_left` / 定理 `oangle_zero_left`

English:
theorem oangle_zero_left
  given: (x : V)
  statement: o.oangle 0 x = 0
  proof: by simp [oangle]

中文:
定理 oangle_zero_left
  条件: (x : V)
  结论: o.oangle 0 x = 0
  证明: by simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_zero_left (x : V) : o.oangle 0 x = 0 := by simp [oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp]
/--
theorem `oangle_zero_right` / 定理 `oangle_zero_right`

English:
theorem oangle_zero_right
  given: (x : V)
  statement: o.oangle x 0 = 0
  proof: by simp [oangle]

中文:
定理 oangle_zero_right
  条件: (x : V)
  结论: o.oangle x 0 = 0
  证明: by simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_zero_right (x : V) : o.oangle x 0 = 0 := by simp [oangle]

set_option backward.isDefEq.respectTransparency false in
/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp]
/--
theorem `oangle_self` / 定理 `oangle_self`

English:
theorem oangle_self
  given: (x : V)
  statement: o.oangle x x = 0
  proof: by
  rw [oangle]; rw [kahler_apply_self]; rw [← ofReal_pow]
  convert! QuotientAddGroup.mk_zero (AddSubgroup.zmultiples (2 * π))
  apply arg_ofReal_of_nonneg
  positivity

中文:
定理 oangle_self
  条件: (x : V)
  结论: o.oangle x x = 0
  证明: by
  rw [oangle]; rw [kahler_apply_self]; rw [← ofReal_pow]
  convert! QuotientAddGroup.mk_zero (AddSubgroup.zmultiples (2 * π))
  apply arg_ofReal_of_nonneg
  positivity

Depends on / 依赖: AddSubgroup, AddSubgroup.zmultiples, QuotientAddGroup, QuotientAddGroup.mk_zero, arg_ofReal_of_nonneg, convert, kahler_apply_self, mk_zero, oangle, ofReal_pow, zmultiples
-/
theorem oangle_self (x : V) : o.oangle x x = 0 := by
  rw [oangle]; rw [kahler_apply_self]; rw [← ofReal_pow]
  convert! QuotientAddGroup.mk_zero (AddSubgroup.zmultiples (2 * π))
  apply arg_ofReal_of_nonneg
  positivity

/--
theorem `left_ne_zero_of_oangle_ne_zero` / 定理 `left_ne_zero_of_oangle_ne_zero`

English:
theorem left_ne_zero_of_oangle_ne_zero
  given: {x y : V} (h : o.oangle x y != 0)
  statement: x != 0
  proof: by
  rintro rfl; simp at h

中文:
定理 left_ne_zero_of_oangle_ne_zero
  条件: {x y : V} (h : o.oangle x y != 0)
  结论: x != 0
  证明: by
  rintro rfl; simp at h
-/
theorem left_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : x != 0 := by
  rintro rfl; simp at h

/--
theorem `right_ne_zero_of_oangle_ne_zero` / 定理 `right_ne_zero_of_oangle_ne_zero`

English:
theorem right_ne_zero_of_oangle_ne_zero
  given: {x y : V} (h : o.oangle x y != 0)
  statement: y != 0
  proof: by
  rintro rfl; simp at h

中文:
定理 right_ne_zero_of_oangle_ne_zero
  条件: {x y : V} (h : o.oangle x y != 0)
  结论: y != 0
  证明: by
  rintro rfl; simp at h
-/
theorem right_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : y != 0 := by
  rintro rfl; simp at h

/--
theorem `ne_of_oangle_ne_zero` / 定理 `ne_of_oangle_ne_zero`

English:
theorem ne_of_oangle_ne_zero
  given: {x y : V} (h : o.oangle x y != 0)
  statement: x != y
  proof: by
  rintro rfl; simp at h

中文:
定理 ne_of_oangle_ne_zero
  条件: {x y : V} (h : o.oangle x y != 0)
  结论: x != y
  证明: by
  rintro rfl; simp at h
-/
theorem ne_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : x != y := by
  rintro rfl; simp at h

/--
theorem `left_ne_zero_of_oangle_eq_pi` / 定理 `left_ne_zero_of_oangle_eq_pi`

English:
theorem left_ne_zero_of_oangle_eq_pi
  given: {x y : V} (h : o.oangle x y = π)
  statement: x != 0
  proof: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

中文:
定理 left_ne_zero_of_oangle_eq_pi
  条件: {x y : V} (h : o.oangle x y = π)
  结论: x != 0
  证明: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, left_ne_zero_of_oangle_ne_zero, o.left_ne_zero_of_oangle_ne_zero, o.oangle, oangle, pi_ne_zero
-/
theorem left_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x != 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

/--
theorem `right_ne_zero_of_oangle_eq_pi` / 定理 `right_ne_zero_of_oangle_eq_pi`

English:
theorem right_ne_zero_of_oangle_eq_pi
  given: {x y : V} (h : o.oangle x y = π)
  statement: y != 0
  proof: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

中文:
定理 right_ne_zero_of_oangle_eq_pi
  条件: {x y : V} (h : o.oangle x y = π)
  结论: y != 0
  证明: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, o.oangle, o.right_ne_zero_of_oangle_ne_zero, oangle, pi_ne_zero, right_ne_zero_of_oangle_ne_zero
-/
theorem right_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : y != 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

/--
theorem `ne_of_oangle_eq_pi` / 定理 `ne_of_oangle_eq_pi`

English:
theorem ne_of_oangle_eq_pi
  given: {x y : V} (h : o.oangle x y = π)
  statement: x != y
  proof: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

中文:
定理 ne_of_oangle_eq_pi
  条件: {x y : V} (h : o.oangle x y = π)
  结论: x != y
  证明: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, ne_of_oangle_ne_zero, o.ne_of_oangle_ne_zero, o.oangle, oangle, pi_ne_zero
-/
theorem ne_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x != y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y != 0)

/--
theorem `left_ne_zero_of_oangle_eq_pi_div_two` / 定理 `left_ne_zero_of_oangle_eq_pi_div_two`

English:
theorem left_ne_zero_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = (π / 2 : Real))
  statement: x != 0
  proof: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 left_ne_zero_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (π / 2 : 实数))
  结论: x != 0
  证明: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, left_ne_zero_of_oangle_ne_zero, o.left_ne_zero_of_oangle_ne_zero, o.oangle, oangle, pi_div_two_ne_zero
-/
theorem left_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `right_ne_zero_of_oangle_eq_pi_div_two` / 定理 `right_ne_zero_of_oangle_eq_pi_div_two`

English:
theorem right_ne_zero_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = (π / 2 : Real))
  statement: y != 0
  proof: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 right_ne_zero_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (π / 2 : 实数))
  结论: y != 0
  证明: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, o.oangle, o.right_ne_zero_of_oangle_ne_zero, oangle, pi_div_two_ne_zero, right_ne_zero_of_oangle_ne_zero
-/
theorem right_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `ne_of_oangle_eq_pi_div_two` / 定理 `ne_of_oangle_eq_pi_div_two`

English:
theorem ne_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = (π / 2 : Real))
  statement: x != y
  proof: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 ne_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (π / 2 : 实数))
  结论: x != y
  证明: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, ne_of_oangle_ne_zero, o.ne_of_oangle_ne_zero, o.oangle, oangle, pi_div_two_ne_zero
-/
theorem ne_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `left_ne_zero_of_oangle_eq_neg_pi_div_two` / 定理 `left_ne_zero_of_oangle_eq_neg_pi_div_two`

English:
theorem left_ne_zero_of_oangle_eq_neg_pi_div_two
  given: {x y : V} (h : o.oangle x y = (-π / 2 : Real))
  proof: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 left_ne_zero_of_oangle_eq_neg_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (-π / 2 : 实数))
  证明: o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, left_ne_zero_of_oangle_ne_zero, neg_pi_div_two_ne_zero, o.left_ne_zero_of_oangle_ne_zero, o.oangle, oangle
-/
theorem left_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) :
    x != 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `right_ne_zero_of_oangle_eq_neg_pi_div_two` / 定理 `right_ne_zero_of_oangle_eq_neg_pi_div_two`

English:
theorem right_ne_zero_of_oangle_eq_neg_pi_div_two
  given: {x y : V} (h : o.oangle x y = (-π / 2 : Real))
  proof: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 right_ne_zero_of_oangle_eq_neg_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (-π / 2 : 实数))
  证明: o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, neg_pi_div_two_ne_zero, o.oangle, o.right_ne_zero_of_oangle_ne_zero, oangle, right_ne_zero_of_oangle_ne_zero
-/
theorem right_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) :
    y != 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `ne_of_oangle_eq_neg_pi_div_two` / 定理 `ne_of_oangle_eq_neg_pi_div_two`

English:
theorem ne_of_oangle_eq_neg_pi_div_two
  given: {x y : V} (h : o.oangle x y = (-π / 2 : Real))
  statement: x != y
  proof: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

中文:
定理 ne_of_oangle_eq_neg_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (-π / 2 : 实数))
  结论: x != y
  证明: o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, ne_of_oangle_ne_zero, neg_pi_div_two_ne_zero, o.ne_of_oangle_ne_zero, o.oangle, oangle
-/
theorem ne_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) : x != y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y != 0)

/--
theorem `left_ne_zero_of_oangle_sign_ne_zero` / 定理 `left_ne_zero_of_oangle_sign_ne_zero`

English:
theorem left_ne_zero_of_oangle_sign_ne_zero
  given: {x y : V} (h : (o.oangle x y).sign != 0)
  statement: x != 0
  proof: o.left_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 left_ne_zero_of_oangle_sign_ne_zero
  条件: {x y : V} (h : (o.oangle x y).sign != 0)
  结论: x != 0
  证明: o.left_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, left_ne_zero_of_oangle_ne_zero, o.left_ne_zero_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem left_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : x != 0 :=
  o.left_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `right_ne_zero_of_oangle_sign_ne_zero` / 定理 `right_ne_zero_of_oangle_sign_ne_zero`

English:
theorem right_ne_zero_of_oangle_sign_ne_zero
  given: {x y : V} (h : (o.oangle x y).sign != 0)
  statement: y != 0
  proof: o.right_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 right_ne_zero_of_oangle_sign_ne_zero
  条件: {x y : V} (h : (o.oangle x y).sign != 0)
  结论: y != 0
  证明: o.right_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, o.right_ne_zero_of_oangle_ne_zero, right_ne_zero_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem right_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : y != 0 :=
  o.right_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `ne_of_oangle_sign_ne_zero` / 定理 `ne_of_oangle_sign_ne_zero`

English:
theorem ne_of_oangle_sign_ne_zero
  given: {x y : V} (h : (o.oangle x y).sign != 0)
  statement: x != y
  proof: o.ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 ne_of_oangle_sign_ne_zero
  条件: {x y : V} (h : (o.oangle x y).sign != 0)
  结论: x != y
  证明: o.ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, ne_of_oangle_ne_zero, o.ne_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem ne_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : x != y :=
  o.ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `left_ne_zero_of_oangle_sign_eq_one` / 定理 `left_ne_zero_of_oangle_sign_eq_one`

English:
theorem left_ne_zero_of_oangle_sign_eq_one
  given: {x y : V} (h : (o.oangle x y).sign = 1)
  statement: x != 0
  proof: o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 left_ne_zero_of_oangle_sign_eq_one
  条件: {x y : V} (h : (o.oangle x y).sign = 1)
  结论: x != 0
  证明: o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, left_ne_zero_of_oangle_sign_ne_zero, o.left_ne_zero_of_oangle_sign_ne_zero, o.oangle, oangle
-/
theorem left_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x != 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `right_ne_zero_of_oangle_sign_eq_one` / 定理 `right_ne_zero_of_oangle_sign_eq_one`

English:
theorem right_ne_zero_of_oangle_sign_eq_one
  given: {x y : V} (h : (o.oangle x y).sign = 1)
  statement: y != 0
  proof: o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 right_ne_zero_of_oangle_sign_eq_one
  条件: {x y : V} (h : (o.oangle x y).sign = 1)
  结论: y != 0
  证明: o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, o.oangle, o.right_ne_zero_of_oangle_sign_ne_zero, oangle, right_ne_zero_of_oangle_sign_ne_zero
-/
theorem right_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : y != 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `ne_of_oangle_sign_eq_one` / 定理 `ne_of_oangle_sign_eq_one`

English:
theorem ne_of_oangle_sign_eq_one
  given: {x y : V} (h : (o.oangle x y).sign = 1)
  statement: x != y
  proof: o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 ne_of_oangle_sign_eq_one
  条件: {x y : V} (h : (o.oangle x y).sign = 1)
  结论: x != y
  证明: o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, ne_of_oangle_sign_ne_zero, o.ne_of_oangle_sign_ne_zero, o.oangle, oangle
-/
theorem ne_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x != y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `left_ne_zero_of_oangle_sign_eq_neg_one` / 定理 `left_ne_zero_of_oangle_sign_eq_neg_one`

English:
theorem left_ne_zero_of_oangle_sign_eq_neg_one
  given: {x y : V} (h : (o.oangle x y).sign = -1)
  statement: x != 0
  proof: o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 left_ne_zero_of_oangle_sign_eq_neg_one
  条件: {x y : V} (h : (o.oangle x y).sign = -1)
  结论: x != 0
  证明: o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, left_ne_zero_of_oangle_sign_ne_zero, o.left_ne_zero_of_oangle_sign_ne_zero, o.oangle, oangle
-/
theorem left_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x != 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `right_ne_zero_of_oangle_sign_eq_neg_one` / 定理 `right_ne_zero_of_oangle_sign_eq_neg_one`

English:
theorem right_ne_zero_of_oangle_sign_eq_neg_one
  given: {x y : V} (h : (o.oangle x y).sign = -1)
  statement: y != 0
  proof: o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 right_ne_zero_of_oangle_sign_eq_neg_one
  条件: {x y : V} (h : (o.oangle x y).sign = -1)
  结论: y != 0
  证明: o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, o.oangle, o.right_ne_zero_of_oangle_sign_ne_zero, oangle, right_ne_zero_of_oangle_sign_ne_zero
-/
theorem right_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : y != 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `ne_of_oangle_sign_eq_neg_one` / 定理 `ne_of_oangle_sign_eq_neg_one`

English:
theorem ne_of_oangle_sign_eq_neg_one
  given: {x y : V} (h : (o.oangle x y).sign = -1)
  statement: x != y
  proof: o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

中文:
定理 ne_of_oangle_sign_eq_neg_one
  条件: {x y : V} (h : (o.oangle x y).sign = -1)
  结论: x != y
  证明: o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

Depends on / 依赖: h.symm, ne_of_oangle_sign_ne_zero, o.ne_of_oangle_sign_ne_zero, o.oangle, oangle
-/
theorem ne_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x != y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign != 0)

/--
theorem `oangle_rev` / 定理 `oangle_rev`

English:
theorem oangle_rev
  given: (x y : V)
  statement: o.oangle y x = -o.oangle x y
  proof: by
  simp only [oangle, o.kahler_swap y x, Complex.arg_conj_coe_angle]

中文:
定理 oangle_rev
  条件: (x y : V)
  结论: o.oangle y x = -o.oangle x y
  证明: by
  simp only [oangle, o.kahler_swap y x, Complex.arg_conj_coe_angle]

Depends on / 依赖: Complex.arg_conj_coe_angle, arg_conj_coe_angle, kahler_swap, o.kahler_swap, oangle
-/
theorem oangle_rev (x y : V) : o.oangle y x = -o.oangle x y := by
  simp only [oangle, o.kahler_swap y x, Complex.arg_conj_coe_angle]

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp]
/--
theorem `oangle_add_oangle_rev` / 定理 `oangle_add_oangle_rev`

English:
theorem oangle_add_oangle_rev
  given: (x y : V)
  statement: o.oangle x y + o.oangle y x = 0
  proof: by
  simp [o.oangle_rev y x]

中文:
定理 oangle_add_oangle_rev
  条件: (x y : V)
  结论: o.oangle x y + o.oangle y x = 0
  证明: by
  simp [o.oangle_rev y x]

Depends on / 依赖: o.oangle_rev, oangle_rev
-/
theorem oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 := by
  simp [o.oangle_rev y x]

/--
theorem `oangle_neg_left` / 定理 `oangle_neg_left`

English:
theorem oangle_neg_left
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

中文:
定理 oangle_neg_left
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

Depends on / 依赖: Complex.arg_neg_coe_angle, arg_neg_coe_angle, convert, kahler_ne_zero, map_neg, o.kahler_ne_zero, oangle
-/
theorem oangle_neg_left {x y : V} (hx : x != 0) (hy : y != 0) :
    o.oangle (-x) y = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/--
theorem `oangle_neg_right` / 定理 `oangle_neg_right`

English:
theorem oangle_neg_right
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

中文:
定理 oangle_neg_right
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

Depends on / 依赖: Complex.arg_neg_coe_angle, arg_neg_coe_angle, convert, kahler_ne_zero, map_neg, o.kahler_ne_zero, oangle
-/
theorem oangle_neg_right {x y : V} (hx : x != 0) (hy : y != 0) :
    o.oangle x (-y) = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp]
/--
theorem `two_zsmul_oangle_neg_left` / 定理 `two_zsmul_oangle_neg_left`

English:
theorem two_zsmul_oangle_neg_left
  given: (x y : V)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_left hx hy]

中文:
定理 two_zsmul_oangle_neg_left
  条件: (x y : V)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_left hx hy]

Depends on / 依赖: o.oangle_neg_left, oangle_neg_left
-/
theorem two_zsmul_oangle_neg_left (x y : V) :
    (2 : Int) • o.oangle (-x) y = (2 : Int) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_left hx hy]

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp]
/--
theorem `two_zsmul_oangle_neg_right` / 定理 `two_zsmul_oangle_neg_right`

English:
theorem two_zsmul_oangle_neg_right
  given: (x y : V)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_right hx hy]

中文:
定理 two_zsmul_oangle_neg_right
  条件: (x y : V)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_right hx hy]

Depends on / 依赖: o.oangle_neg_right, oangle_neg_right
-/
theorem two_zsmul_oangle_neg_right (x y : V) :
    (2 : Int) • o.oangle x (-y) = (2 : Int) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_right hx hy]

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp]
/--
theorem `oangle_neg_neg` / 定理 `oangle_neg_neg`

English:
theorem oangle_neg_neg
  given: (x y : V)
  statement: o.oangle (-x) (-y) = o.oangle x y
  proof: by simp [oangle]

中文:
定理 oangle_neg_neg
  条件: (x y : V)
  结论: o.oangle (-x) (-y) = o.oangle x y
  证明: by simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y := by simp [oangle]

/--
theorem `oangle_neg_left_eq_neg_right` / 定理 `oangle_neg_left_eq_neg_right`

English:
theorem oangle_neg_left_eq_neg_right
  given: (x y : V)
  statement: o.oangle (-x) y = o.oangle x (-y)
  proof: by
  rw [← neg_neg y]; rw [oangle_neg_neg]; rw [neg_neg]

中文:
定理 oangle_neg_left_eq_neg_right
  条件: (x y : V)
  结论: o.oangle (-x) y = o.oangle x (-y)
  证明: by
  rw [← neg_neg y]; rw [oangle_neg_neg]; rw [neg_neg]

Depends on / 依赖: neg_neg, oangle_neg_neg
-/
theorem oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) := by
  rw [← neg_neg y]; rw [oangle_neg_neg]; rw [neg_neg]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp]
/--
theorem `oangle_neg_self_left` / 定理 `oangle_neg_self_left`

English:
theorem oangle_neg_self_left
  given: {x : V} (hx : x != 0)
  statement: o.oangle (-x) x = π
  proof: by
  simp [oangle_neg_left, hx]

中文:
定理 oangle_neg_self_left
  条件: {x : V} (hx : x != 0)
  结论: o.oangle (-x) x = π
  证明: by
  simp [oangle_neg_left, hx]

Depends on / 依赖: oangle_neg_left
-/
theorem oangle_neg_self_left {x : V} (hx : x != 0) : o.oangle (-x) x = π := by
  simp [oangle_neg_left, hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp]
/--
theorem `oangle_neg_self_right` / 定理 `oangle_neg_self_right`

English:
theorem oangle_neg_self_right
  given: {x : V} (hx : x != 0)
  statement: o.oangle x (-x) = π
  proof: by
  simp [oangle_neg_right, hx]

中文:
定理 oangle_neg_self_right
  条件: {x : V} (hx : x != 0)
  结论: o.oangle x (-x) = π
  证明: by
  simp [oangle_neg_right, hx]

Depends on / 依赖: oangle_neg_right
-/
theorem oangle_neg_self_right {x : V} (hx : x != 0) : o.oangle x (-x) = π := by
  simp [oangle_neg_right, hx]

/--
theorem `two_zsmul_oangle_neg_self_left` / 定理 `two_zsmul_oangle_neg_self_left`

English:
theorem two_zsmul_oangle_neg_self_left
  given: (x : V)
  statement: (2 : Int) • o.oangle (-x) x = 0
  proof: by
  by_cases hx : x = 0 <;> simp [hx]

中文:
定理 two_zsmul_oangle_neg_self_left
  条件: (x : V)
  结论: (2 : 整数) • o.oangle (-x) x = 0
  证明: by
  by_cases hx : x = 0 <;> simp [hx]
-/
theorem two_zsmul_oangle_neg_self_left (x : V) : (2 : Int) • o.oangle (-x) x = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/--
theorem `two_zsmul_oangle_neg_self_right` / 定理 `two_zsmul_oangle_neg_self_right`

English:
theorem two_zsmul_oangle_neg_self_right
  given: (x : V)
  statement: (2 : Int) • o.oangle x (-x) = 0
  proof: by
  by_cases hx : x = 0 <;> simp [hx]

中文:
定理 two_zsmul_oangle_neg_self_right
  条件: (x : V)
  结论: (2 : 整数) • o.oangle x (-x) = 0
  证明: by
  by_cases hx : x = 0 <;> simp [hx]
-/
theorem two_zsmul_oangle_neg_self_right (x : V) : (2 : Int) • o.oangle x (-x) = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp]
/--
theorem `oangle_add_oangle_rev_neg_left` / 定理 `oangle_add_oangle_rev_neg_left`

English:
theorem oangle_add_oangle_rev_neg_left
  given: (x y : V)
  statement: o.oangle (-x) y + o.oangle (-y) x = 0
  proof: by
  rw [oangle_neg_left_eq_neg_right]; rw [oangle_rev]; rw [neg_add_cancel]

中文:
定理 oangle_add_oangle_rev_neg_left
  条件: (x y : V)
  结论: o.oangle (-x) y + o.oangle (-y) x = 0
  证明: by
  rw [oangle_neg_left_eq_neg_right]; rw [oangle_rev]; rw [neg_add_cancel]

Depends on / 依赖: neg_add_cancel, oangle_neg_left_eq_neg_right, oangle_rev
-/
theorem oangle_add_oangle_rev_neg_left (x y : V) : o.oangle (-x) y + o.oangle (-y) x = 0 := by
  rw [oangle_neg_left_eq_neg_right]; rw [oangle_rev]; rw [neg_add_cancel]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp]
/--
theorem `oangle_add_oangle_rev_neg_right` / 定理 `oangle_add_oangle_rev_neg_right`

English:
theorem oangle_add_oangle_rev_neg_right
  given: (x y : V)
  statement: o.oangle x (-y) + o.oangle y (-x) = 0
  proof: by
  rw [o.oangle_rev (-x)]; rw [oangle_neg_left_eq_neg_right]; rw [add_neg_cancel]

中文:
定理 oangle_add_oangle_rev_neg_right
  条件: (x y : V)
  结论: o.oangle x (-y) + o.oangle y (-x) = 0
  证明: by
  rw [o.oangle_rev (-x)]; rw [oangle_neg_left_eq_neg_right]; rw [add_neg_cancel]

Depends on / 依赖: add_neg_cancel, o.oangle_rev, oangle_neg_left_eq_neg_right, oangle_rev
-/
theorem oangle_add_oangle_rev_neg_right (x y : V) : o.oangle x (-y) + o.oangle y (-x) = 0 := by
  rw [o.oangle_rev (-x)]; rw [oangle_neg_left_eq_neg_right]; rw [add_neg_cancel]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
/--
theorem `oangle_smul_left_of_pos` / 定理 `oangle_smul_left_of_pos`

English:
theorem oangle_smul_left_of_pos
  given: (x y : V) {r : Real} (hr : 0 < r)
  proof: by simp [oangle, Complex.arg_real_mul _ hr]

中文:
定理 oangle_smul_left_of_pos
  条件: (x y : V) {r : 实数} (hr : 0 < r)
  证明: by simp [oangle, Complex.arg_real_mul _ hr]

Depends on / 依赖: Complex.arg_real_mul, arg_real_mul, oangle
-/
theorem oangle_smul_left_of_pos (x y : V) {r : Real} (hr : 0 < r) :
    o.oangle (r • x) y = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
/--
theorem `oangle_smul_right_of_pos` / 定理 `oangle_smul_right_of_pos`

English:
theorem oangle_smul_right_of_pos
  given: (x y : V) {r : Real} (hr : 0 < r)
  proof: by simp [oangle, Complex.arg_real_mul _ hr]

中文:
定理 oangle_smul_right_of_pos
  条件: (x y : V) {r : 实数} (hr : 0 < r)
  证明: by simp [oangle, Complex.arg_real_mul _ hr]

Depends on / 依赖: Complex.arg_real_mul, arg_real_mul, oangle
-/
theorem oangle_smul_right_of_pos (x y : V) {r : Real} (hr : 0 < r) :
    o.oangle x (r • y) = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
/--
theorem `oangle_smul_left_of_neg` / 定理 `oangle_smul_left_of_neg`

English:
theorem oangle_smul_left_of_neg
  given: (x y : V) {r : Real} (hr : r < 0)
  proof: by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

中文:
定理 oangle_smul_left_of_neg
  条件: (x y : V) {r : 实数} (hr : r < 0)
  证明: by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

Depends on / 依赖: neg_neg, neg_pos_of_neg, neg_smul, o.oangle_smul_left_of_pos, oangle_smul_left_of_pos, smul_neg
-/
theorem oangle_smul_left_of_neg (x y : V) {r : Real} (hr : r < 0) :
    o.oangle (r • x) y = o.oangle (-x) y := by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
/--
theorem `oangle_smul_right_of_neg` / 定理 `oangle_smul_right_of_neg`

English:
theorem oangle_smul_right_of_neg
  given: (x y : V) {r : Real} (hr : r < 0)
  proof: by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

中文:
定理 oangle_smul_right_of_neg
  条件: (x y : V) {r : 实数} (hr : r < 0)
  证明: by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

Depends on / 依赖: neg_neg, neg_pos_of_neg, neg_smul, o.oangle_smul_right_of_pos, oangle_smul_right_of_pos, smul_neg
-/
theorem oangle_smul_right_of_neg (x y : V) {r : Real} (hr : r < 0) :
    o.oangle x (r • y) = o.oangle x (-y) := by
  rw [← neg_neg r]; rw [neg_smul]; rw [← smul_neg]; rw [o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp]
/--
theorem `oangle_smul_left_self_of_nonneg` / 定理 `oangle_smul_left_self_of_nonneg`

English:
theorem oangle_smul_left_self_of_nonneg
  given: (x : V) {r : Real} (hr : 0 <= r)
  statement: o.oangle (r • x) x = 0
  proof: by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

中文:
定理 oangle_smul_left_self_of_nonneg
  条件: (x : V) {r : 实数} (hr : 0 <= r)
  结论: o.oangle (r • x) x = 0
  证明: by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

Depends on / 依赖: h.symm, hr.lt_or_eq, lt_or_eq
-/
theorem oangle_smul_left_self_of_nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oangle (r • x) x = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp]
/--
theorem `oangle_smul_right_self_of_nonneg` / 定理 `oangle_smul_right_self_of_nonneg`

English:
theorem oangle_smul_right_self_of_nonneg
  given: (x : V) {r : Real} (hr : 0 <= r)
  statement: o.oangle x (r • x) = 0
  proof: by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

中文:
定理 oangle_smul_right_self_of_nonneg
  条件: (x : V) {r : 实数} (hr : 0 <= r)
  结论: o.oangle x (r • x) = 0
  证明: by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

Depends on / 依赖: h.symm, hr.lt_or_eq, lt_or_eq
-/
theorem oangle_smul_right_self_of_nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oangle x (r • x) = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp]
/--
theorem `oangle_smul_smul_self_of_nonneg` / 定理 `oangle_smul_smul_self_of_nonneg`

English:
theorem oangle_smul_smul_self_of_nonneg
  given: (x : V) {r₁ r₂ : Real} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂)
  proof: by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [h, hr₂]
  · simp [h.symm]

中文:
定理 oangle_smul_smul_self_of_nonneg
  条件: (x : V) {r₁ r₂ : 实数} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂)
  证明: by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [h, hr₂]
  · simp [h.symm]

Depends on / 依赖: h.symm, lt_or_eq
-/
theorem oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : Real} (hr₁ : 0 <= r₁) (hr₂ : 0 <= r₂) :
    o.oangle (r₁ • x) (r₂ • x) = 0 := by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [h, hr₂]
  · simp [h.symm]

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
/--
theorem `two_zsmul_oangle_smul_left_of_ne_zero` / 定理 `two_zsmul_oangle_smul_left_of_ne_zero`

English:
theorem two_zsmul_oangle_smul_left_of_ne_zero
  given: (x y : V) {r : Real} (hr : r != 0)
  proof: by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

中文:
定理 two_zsmul_oangle_smul_left_of_ne_zero
  条件: (x y : V) {r : 实数} (hr : r != 0)
  证明: by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

Depends on / 依赖: hr.lt_or_gt, lt_or_gt
-/
theorem two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : Real} (hr : r != 0) :
    (2 : Int) • o.oangle (r • x) y = (2 : Int) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
/--
theorem `two_zsmul_oangle_smul_right_of_ne_zero` / 定理 `two_zsmul_oangle_smul_right_of_ne_zero`

English:
theorem two_zsmul_oangle_smul_right_of_ne_zero
  given: (x y : V) {r : Real} (hr : r != 0)
  proof: by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

中文:
定理 two_zsmul_oangle_smul_right_of_ne_zero
  条件: (x y : V) {r : 实数} (hr : r != 0)
  证明: by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

Depends on / 依赖: hr.lt_or_gt, lt_or_gt
-/
theorem two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : Real} (hr : r != 0) :
    (2 : Int) • o.oangle x (r • y) = (2 : Int) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp]
/--
theorem `two_zsmul_oangle_smul_left_self` / 定理 `two_zsmul_oangle_smul_left_self`

English:
theorem two_zsmul_oangle_smul_left_self
  given: (x : V) {r : Real}
  statement: (2 : Int) • o.oangle (r • x) x = 0
  proof: by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

中文:
定理 two_zsmul_oangle_smul_left_self
  条件: (x : V) {r : 实数}
  结论: (2 : 整数) • o.oangle (r • x) x = 0
  证明: by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

Depends on / 依赖: lt_or_ge
-/
theorem two_zsmul_oangle_smul_left_self (x : V) {r : Real} : (2 : Int) • o.oangle (r • x) x = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp]
/--
theorem `two_zsmul_oangle_smul_right_self` / 定理 `two_zsmul_oangle_smul_right_self`

English:
theorem two_zsmul_oangle_smul_right_self
  given: (x : V) {r : Real}
  statement: (2 : Int) • o.oangle x (r • x) = 0
  proof: by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

中文:
定理 two_zsmul_oangle_smul_right_self
  条件: (x : V) {r : 实数}
  结论: (2 : 整数) • o.oangle x (r • x) = 0
  证明: by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

Depends on / 依赖: lt_or_ge
-/
theorem two_zsmul_oangle_smul_right_self (x : V) {r : Real} : (2 : Int) • o.oangle x (r • x) = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp]
/--
theorem `two_zsmul_oangle_smul_smul_self` / 定理 `two_zsmul_oangle_smul_smul_self`

English:
theorem two_zsmul_oangle_smul_smul_self
  given: (x : V) {r₁ r₂ : Real}
  proof: by by_cases h : r₁ = 0 <;> simp [h]

中文:
定理 two_zsmul_oangle_smul_smul_self
  条件: (x : V) {r₁ r₂ : 实数}
  证明: by by_cases h : r₁ = 0 <;> simp [h]
-/
theorem two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : Real} :
    (2 : Int) • o.oangle (r₁ • x) (r₂ • x) = 0 := by by_cases h : r₁ = 0 <;> simp [h]

/--
theorem `two_zsmul_oangle_left_of_span_eq` / 定理 `two_zsmul_oangle_left_of_span_eq`

English:
theorem two_zsmul_oangle_left_of_span_eq
  given: {x y : V} (z : V) (h : Real ∙ x = Real ∙ y)
  proof: by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_left_of_ne_zero _ _ (Units.ne_zero _)).symm

中文:
定理 two_zsmul_oangle_left_of_span_eq
  条件: {x y : V} (z : V) (h : 实数 ∙ x = 实数 ∙ y)
  证明: by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_left_of_ne_zero _ _ (Units.ne_zero _)).symm

Depends on / 依赖: Submodule, Submodule.span_singleton_eq_span_singleton, Units.ne_zero, ne_zero, o.two_zsmul_oangle_smul_left_of_ne_zero, span_singleton_eq_span_singleton, two_zsmul_oangle_smul_left_of_ne_zero
-/
theorem two_zsmul_oangle_left_of_span_eq {x y : V} (z : V) (h : Real ∙ x = Real ∙ y) :
    (2 : Int) • o.oangle x z = (2 : Int) • o.oangle y z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_left_of_ne_zero _ _ (Units.ne_zero _)).symm

/--
theorem `two_zsmul_oangle_right_of_span_eq` / 定理 `two_zsmul_oangle_right_of_span_eq`

English:
theorem two_zsmul_oangle_right_of_span_eq
  given: (x : V) {y z : V} (h : Real ∙ y = Real ∙ z)
  proof: by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_right_of_ne_zero _ _ (Units.ne_zero _)).symm

中文:
定理 two_zsmul_oangle_right_of_span_eq
  条件: (x : V) {y z : V} (h : 实数 ∙ y = 实数 ∙ z)
  证明: by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_right_of_ne_zero _ _ (Units.ne_zero _)).symm

Depends on / 依赖: Submodule, Submodule.span_singleton_eq_span_singleton, Units.ne_zero, ne_zero, o.two_zsmul_oangle_smul_right_of_ne_zero, span_singleton_eq_span_singleton, two_zsmul_oangle_smul_right_of_ne_zero
-/
theorem two_zsmul_oangle_right_of_span_eq (x : V) {y z : V} (h : Real ∙ y = Real ∙ z) :
    (2 : Int) • o.oangle x y = (2 : Int) • o.oangle x z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_right_of_ne_zero _ _ (Units.ne_zero _)).symm

/--
theorem `two_zsmul_oangle_of_span_eq_of_span_eq` / 定理 `two_zsmul_oangle_of_span_eq_of_span_eq`

English:
theorem two_zsmul_oangle_of_span_eq_of_span_eq
  statement: {w x y z : V} (hwx : Real ∙ w = Real ∙ x)
  proof: by
  rw [o.two_zsmul_oangle_left_of_span_eq y hwx]; rw [o.two_zsmul_oangle_right_of_span_eq x hyz]

中文:
定理 two_zsmul_oangle_of_span_eq_of_span_eq
  结论: {w x y z : V} (hwx : 实数 ∙ w = 实数 ∙ x)
  证明: by
  rw [o.two_zsmul_oangle_left_of_span_eq y hwx]; rw [o.two_zsmul_oangle_right_of_span_eq x hyz]

Depends on / 依赖: o.two_zsmul_oangle_left_of_span_eq, o.two_zsmul_oangle_right_of_span_eq, two_zsmul_oangle_left_of_span_eq, two_zsmul_oangle_right_of_span_eq
-/
theorem two_zsmul_oangle_of_span_eq_of_span_eq {w x y z : V} (hwx : Real ∙ w = Real ∙ x)
    (hyz : Real ∙ y = Real ∙ z) : (2 : Int) • o.oangle w y = (2 : Int) • o.oangle x z := by
  rw [o.two_zsmul_oangle_left_of_span_eq y hwx]; rw [o.two_zsmul_oangle_right_of_span_eq x hyz]

/--
theorem `oangle_eq_zero_iff_oangle_rev_eq_zero` / 定理 `oangle_eq_zero_iff_oangle_rev_eq_zero`

English:
theorem oangle_eq_zero_iff_oangle_rev_eq_zero
  given: {x y : V}
  statement: o.oangle x y = 0 ↔ o.oangle y x = 0
  proof: by
  rw [oangle_rev]; rw [neg_eq_zero]

中文:
定理 oangle_eq_zero_iff_oangle_rev_eq_zero
  条件: {x y : V}
  结论: o.oangle x y = 0 ↔ o.oangle y x = 0
  证明: by
  rw [oangle_rev]; rw [neg_eq_zero]

Depends on / 依赖: neg_eq_zero, oangle_rev
-/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oangle y x = 0 := by
  rw [oangle_rev]; rw [neg_eq_zero]

/--
theorem `oangle_eq_zero_iff_sameRay` / 定理 `oangle_eq_zero_iff_sameRay`

English:
theorem oangle_eq_zero_iff_sameRay
  given: {x y : V}
  statement: o.oangle x y = 0 ↔ SameRay Real x y
  proof: by
  rw [oangle]; rw [kahler_apply_apply]; rw [Complex.arg_coe_angle_eq_iff_eq_toReal]; rw [Real.Angle.toReal_zero]; rw [Complex.arg_eq_zero_iff]
  simpa using o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay x y

中文:
定理 oangle_eq_zero_iff_sameRay
  条件: {x y : V}
  结论: o.oangle x y = 0 ↔ SameRay 实数 x y
  证明: by
  rw [oangle]; rw [kahler_apply_apply]; rw [Complex.arg_coe_angle_eq_iff_eq_toReal]; rw [Real.Angle.toReal_zero]; rw [Complex.arg_eq_zero_iff]
  simpa using o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay x y

Depends on / 依赖: Complex.arg_coe_angle_eq_iff_eq_toReal, Complex.arg_eq_zero_iff, Real.Angle.toReal_zero, arg_coe_angle_eq_iff_eq_toReal, arg_eq_zero_iff, kahler_apply_apply, nonneg_inner_and_areaForm_eq_zero_iff_sameRay, o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay, oangle, toReal_zero
-/
theorem oangle_eq_zero_iff_sameRay {x y : V} : o.oangle x y = 0 ↔ SameRay Real x y := by
  rw [oangle]; rw [kahler_apply_apply]; rw [Complex.arg_coe_angle_eq_iff_eq_toReal]; rw [Real.Angle.toReal_zero]; rw [Complex.arg_eq_zero_iff]
  simpa using o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay x y

/--
theorem `oangle_eq_pi_iff_oangle_rev_eq_pi` / 定理 `oangle_eq_pi_iff_oangle_rev_eq_pi`

English:
theorem oangle_eq_pi_iff_oangle_rev_eq_pi
  given: {x y : V}
  statement: o.oangle x y = π ↔ o.oangle y x = π
  proof: by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [Real.Angle.neg_coe_pi]

中文:
定理 oangle_eq_pi_iff_oangle_rev_eq_pi
  条件: {x y : V}
  结论: o.oangle x y = π ↔ o.oangle y x = π
  证明: by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [Real.Angle.neg_coe_pi]

Depends on / 依赖: Real.Angle.neg_coe_pi, neg_coe_pi, neg_eq_iff_eq_neg, oangle_rev
-/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π := by
  rw [oangle_rev]; rw [neg_eq_iff_eq_neg]; rw [Real.Angle.neg_coe_pi]

/--
theorem `oangle_eq_pi_iff_sameRay_neg` / 定理 `oangle_eq_pi_iff_sameRay_neg`

English:
theorem oangle_eq_pi_iff_sameRay_neg
  given: {x y : V}
  proof: by
  rw [← o.oangle_eq_zero_iff_sameRay]
  constructor
  · intro h
    by_cases hx : x = 0; · simp [hx, Real.Angle.pi_ne_zero.symm] at h
    by_cases hy : y = 0; · simp [hy, Real.Angle.pi_ne_zero.symm] at h
    refine ⟨hx, hy, ?_⟩
    rw [o.oangle_neg_right hx hy]; rw [h]; rw [Real.Angle.coe_pi_add_coe_pi]
  · rintro ⟨hx, hy, h⟩
    rwa [o.oangle_neg_right hx hy, ← Real.Angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h

中文:
定理 oangle_eq_pi_iff_sameRay_neg
  条件: {x y : V}
  证明: by
  rw [← o.oangle_eq_zero_iff_sameRay]
  constructor
  · intro h
    by_cases hx : x = 0; · simp [hx, Real.Angle.pi_ne_zero.symm] at h
    by_cases hy : y = 0; · simp [hy, Real.Angle.pi_ne_zero.symm] at h
    refine ⟨hx, hy, ?_⟩
    rw [o.oangle_neg_right hx hy]; rw [h]; rw [Real.Angle.coe_pi_add_coe_pi]
  · rintro ⟨hx, hy, h⟩
    rwa [o.oangle_neg_right hx hy, ← Real.Angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h

Depends on / 依赖: Real.Angle.coe_pi_add_coe_pi, Real.Angle.pi_ne_zero.symm, Real.Angle.sub_coe_pi_eq_add_coe_pi, coe_pi_add_coe_pi, o.oangle_eq_zero_iff_sameRay, o.oangle_neg_right, oangle_eq_zero_iff_sameRay, oangle_neg_right, pi_ne_zero, sub_coe_pi_eq_add_coe_pi, sub_eq_zero
-/
theorem oangle_eq_pi_iff_sameRay_neg {x y : V} :
    o.oangle x y = π ↔ x != 0 ∧ y != 0 ∧ SameRay Real x (-y) := by
  rw [← o.oangle_eq_zero_iff_sameRay]
  constructor
  · intro h
    by_cases hx : x = 0; · simp [hx, Real.Angle.pi_ne_zero.symm] at h
    by_cases hy : y = 0; · simp [hy, Real.Angle.pi_ne_zero.symm] at h
    refine ⟨hx, hy, ?_⟩
    rw [o.oangle_neg_right hx hy]; rw [h]; rw [Real.Angle.coe_pi_add_coe_pi]
  · rintro ⟨hx, hy, h⟩
    rwa [o.oangle_neg_right hx hy, ← Real.Angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h

/--
theorem `oangle_eq_zero_or_eq_pi_iff_not_linearIndependent` / 定理 `oangle_eq_zero_or_eq_pi_iff_not_linearIndependent`

English:
theorem oangle_eq_zero_or_eq_pi_iff_not_linearIndependent
  given: {x y : V}
  proof: by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]; rw [sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent]

中文:
定理 oangle_eq_zero_or_eq_pi_iff_not_linearIndependent
  条件: {x y : V}
  证明: by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]; rw [sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent]

Depends on / 依赖: oangle_eq_pi_iff_sameRay_neg, oangle_eq_zero_iff_sameRay, sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent
-/
theorem oangle_eq_zero_or_eq_pi_iff_not_linearIndependent {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ ¬LinearIndependent Real ![x, y] := by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]; rw [sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent]

/--
theorem `oangle_eq_zero_or_eq_pi_iff_right_eq_smul` / 定理 `oangle_eq_zero_or_eq_pi_iff_right_eq_smul`

English:
theorem oangle_eq_zero_or_eq_pi_iff_right_eq_smul
  given: {x y : V}
  proof: by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | ⟨-, -, h⟩)
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx
      exact Or.inr ⟨r, rfl⟩
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx
      refine Or.inr ⟨-r, ?_⟩
      simp [hy]
  · rcases h with (rfl | ⟨r, rfl⟩); · simp
    by_cases hx : x = 0; · simp [hx]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · rw [← neg_smul]
      exact Or.inr ⟨hx, smul_ne_zero hr.ne hx,
        SameRay.sameRay_pos_smul_right x (Left.neg_pos_iff.2 hr)⟩
    · simp [hr]
    · exact Or.inl (SameRay.sameRay_pos_smul_right x hr)

中文:
定理 oangle_eq_zero_or_eq_pi_iff_right_eq_smul
  条件: {x y : V}
  证明: by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | ⟨-, -, h⟩)
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx
      exact Or.inr ⟨r, rfl⟩
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx
      refine Or.inr ⟨-r, ?_⟩
      simp [hy]
  · rcases h with (rfl | ⟨r, rfl⟩); · simp
    by_cases hx : x = 0; · simp [hx]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · rw [← neg_smul]
      exact Or.inr ⟨hx, smul_ne_zero hr.ne hx,
        SameRay.sameRay_pos_smul_right x (Left.neg_pos_iff.2 hr)⟩
    · simp [hr]
    · exact Or.inl (SameRay.sameRay_pos_smul_right x hr)

Depends on / 依赖: Or.in, Or.inr, exists_nonneg_left, h.exists_nonneg_left, lt_trichotomy, neg_smul, oangle_eq_pi_iff_sameRay_neg, oangle_eq_zero_iff_sameRay
-/
theorem oangle_eq_zero_or_eq_pi_iff_right_eq_smul {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ x = 0 ∨ exists r : Real, y = r • x := by
  rw [oangle_eq_zero_iff_sameRay]; rw [oangle_eq_pi_iff_sameRay_neg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | ⟨-, -, h⟩)
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx
      exact Or.inr ⟨r, rfl⟩
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx
      refine Or.inr ⟨-r, ?_⟩
      simp [hy]
  · rcases h with (rfl | ⟨r, rfl⟩); · simp
    by_cases hx : x = 0; · simp [hx]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · rw [← neg_smul]
      exact Or.inr ⟨hx, smul_ne_zero hr.ne hx,
        SameRay.sameRay_pos_smul_right x (Left.neg_pos_iff.2 hr)⟩
    · simp [hr]
    · exact Or.inl (SameRay.sameRay_pos_smul_right x hr)

/--
theorem `oangle_ne_zero_and_ne_pi_iff_linearIndependent` / 定理 `oangle_ne_zero_and_ne_pi_iff_linearIndependent`

English:
theorem oangle_ne_zero_and_ne_pi_iff_linearIndependent
  given: {x y : V}
  proof: by
  contrapose! +distrib; exact oangle_eq_zero_or_eq_pi_iff_not_linearIndependent o

中文:
定理 oangle_ne_zero_and_ne_pi_iff_linearIndependent
  条件: {x y : V}
  证明: by
  contrapose! +distrib; exact oangle_eq_zero_or_eq_pi_iff_not_linearIndependent o

Depends on / 依赖: contrapose, distrib, oangle_eq_zero_or_eq_pi_iff_not_linearIndependent
-/
theorem oangle_ne_zero_and_ne_pi_iff_linearIndependent {x y : V} :
    o.oangle x y != 0 ∧ o.oangle x y != π ↔ LinearIndependent Real ![x, y] := by
  contrapose! +distrib; exact oangle_eq_zero_or_eq_pi_iff_not_linearIndependent o

/--
theorem `eq_iff_norm_eq_and_oangle_eq_zero` / 定理 `eq_iff_norm_eq_and_oangle_eq_zero`

English:
theorem eq_iff_norm_eq_and_oangle_eq_zero
  given: (x y : V)
  statement: x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0
  proof: by
  rw [oangle_eq_zero_iff_sameRay]
  constructor
  · rintro rfl
    simp; rfl
  · rcases eq_or_ne y 0 with (rfl | hy)
    · simp
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy
    have : ‖y‖ != 0 := by simpa using hy
    obtain rfl : r = 1 := by
      apply mul_right_cancel₀ this
      simpa [norm_smul, abs_of_nonneg hr] using h₁
    simp

中文:
定理 eq_iff_norm_eq_and_oangle_eq_zero
  条件: (x y : V)
  结论: x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0
  证明: by
  rw [oangle_eq_zero_iff_sameRay]
  constructor
  · rintro rfl
    simp; rfl
  · rcases eq_or_ne y 0 with (rfl | hy)
    · simp
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy
    have : ‖y‖ != 0 := by simpa using hy
    obtain rfl : r = 1 := by
      apply mul_right_cancel₀ this
      simpa [norm_smul, abs_of_nonneg hr] using h₁
    simp

Depends on / 依赖: abs_of_nonneg, eq_or_ne, exists_nonneg_right, norm_smul, oangle_eq_zero_iff_sameRay
-/
theorem eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0 := by
  rw [oangle_eq_zero_iff_sameRay]
  constructor
  · rintro rfl
    simp; rfl
  · rcases eq_or_ne y 0 with (rfl | hy)
    · simp
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy
    have : ‖y‖ != 0 := by simpa using hy
    obtain rfl : r = 1 := by
      apply mul_right_cancel₀ this
      simpa [norm_smul, abs_of_nonneg hr] using h₁
    simp

/--
theorem `eq_iff_oangle_eq_zero_of_norm_eq` / 定理 `eq_iff_oangle_eq_zero_of_norm_eq`

English:
theorem eq_iff_oangle_eq_zero_of_norm_eq
  given: {x y : V} (h : ‖x‖ = ‖y‖)
  statement: x = y ↔ o.oangle x y = 0
  proof: ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

中文:
定理 eq_iff_oangle_eq_zero_of_norm_eq
  条件: {x y : V} (h : ‖x‖ = ‖y‖)
  结论: x = y ↔ o.oangle x y = 0
  证明: ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

Depends on / 依赖: eq_iff_norm_eq_and_oangle_eq_zero, o.eq_iff_norm_eq_and_oangle_eq_zero
-/
theorem eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : x = y ↔ o.oangle x y = 0 :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/--
theorem `eq_iff_norm_eq_of_oangle_eq_zero` / 定理 `eq_iff_norm_eq_of_oangle_eq_zero`

English:
theorem eq_iff_norm_eq_of_oangle_eq_zero
  given: {x y : V} (h : o.oangle x y = 0)
  statement: x = y ↔ ‖x‖ = ‖y‖
  proof: ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

中文:
定理 eq_iff_norm_eq_of_oangle_eq_zero
  条件: {x y : V} (h : o.oangle x y = 0)
  结论: x = y ↔ ‖x‖ = ‖y‖
  证明: ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

Depends on / 依赖: eq_iff_norm_eq_and_oangle_eq_zero, o.eq_iff_norm_eq_and_oangle_eq_zero
-/
theorem eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ‖x‖ = ‖y‖ :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp]
/--
theorem `oangle_add` / 定理 `oangle_add`

English:
theorem oangle_add
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle]; rw [o.kahler_mul y x z]
  · congr 1
    exact mod_cast Complex.arg_real_mul _ (by positivity : 0 < ‖y‖ ^ 2)
  · exact o.kahler_ne_zero hx hy
  · exact o.kahler_ne_zero hy hz

中文:
定理 oangle_add
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle]; rw [o.kahler_mul y x z]
  · congr 1
    exact mod_cast Complex.arg_real_mul _ (by positivity : 0 < ‖y‖ ^ 2)
  · exact o.kahler_ne_zero hx hy
  · exact o.kahler_ne_zero hy hz

Depends on / 依赖: Complex.arg_mul_coe_angle, Complex.arg_real_mul, arg_mul_coe_angle, arg_real_mul, kahler_mul, kahler_ne_zero, mod_cast, o.kahler_mul, o.kahler_ne_zero, oangle, simp_rw
-/
theorem oangle_add {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle x y + o.oangle y z = o.oangle x z := by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle]; rw [o.kahler_mul y x z]
  · congr 1
    exact mod_cast Complex.arg_real_mul _ (by positivity : 0 < ‖y‖ ^ 2)
  · exact o.kahler_ne_zero hx hy
  · exact o.kahler_ne_zero hy hz

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp]
/--
theorem `oangle_add_swap` / 定理 `oangle_add_swap`

English:
theorem oangle_add_swap
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by rw [add_comm, o.oangle_add hx hy hz]

中文:
定理 oangle_add_swap
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by rw [add_comm, o.oangle_add hx hy hz]

Depends on / 依赖: add_comm, o.oangle_add, oangle_add
-/
theorem oangle_add_swap {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle y z + o.oangle x y = o.oangle x z := by rw [add_comm, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp]
/--
theorem `oangle_sub_left` / 定理 `oangle_sub_left`

English:
theorem oangle_sub_left
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by
  rw [sub_eq_iff_eq_add]; rw [o.oangle_add_swap hx hy hz]

中文:
定理 oangle_sub_left
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by
  rw [sub_eq_iff_eq_add]; rw [o.oangle_add_swap hx hy hz]

Depends on / 依赖: o.oangle_add_swap, oangle_add_swap, sub_eq_iff_eq_add
-/
theorem oangle_sub_left {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle x z - o.oangle x y = o.oangle y z := by
  rw [sub_eq_iff_eq_add]; rw [o.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp]
/--
theorem `oangle_sub_right` / 定理 `oangle_sub_right`

English:
theorem oangle_sub_right
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

中文:
定理 oangle_sub_right
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

Depends on / 依赖: o.oangle_add, oangle_add, sub_eq_iff_eq_add
-/
theorem oangle_sub_right {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle x z - o.oangle y z = o.oangle x y := by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

/--
theorem `oangle_add_cyc3` / 定理 `oangle_add_cyc3`

English:
theorem oangle_add_cyc3
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by simp [hx, hy, hz]

中文:
定理 oangle_add_cyc3
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by simp [hx, hy, hz]
-/
theorem oangle_add_cyc3 {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle x y + o.oangle y z + o.oangle z x = 0 := by simp [hx, hy, hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
/--
theorem `oangle_add_cyc3_neg_left` / 定理 `oangle_add_cyc3_neg_left`

English:
theorem oangle_add_cyc3_neg_left
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by
  rw [o.oangle_neg_left hx hy]; rw [o.oangle_neg_left hy hz]; rw [o.oangle_neg_left hz hx]; rw [show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
      o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : Real.Angle) by abel]; rw [o.oangle_add_cyc3 hx hy hz]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [zero_add]; rw [zero_add]

中文:
定理 oangle_add_cyc3_neg_left
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by
  rw [o.oangle_neg_left hx hy]; rw [o.oangle_neg_left hy hz]; rw [o.oangle_neg_left hz hx]; rw [show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
      o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : Real.Angle) by abel]; rw [o.oangle_add_cyc3 hx hy hz]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [zero_add]; rw [zero_add]

Depends on / 依赖: Real.Angle, Real.Angle.coe_pi_add_coe_pi, coe_pi_add_coe_pi, o.oangle, o.oangle_add_cyc3, o.oangle_neg_left, oangle, oangle_add_cyc3, oangle_neg_left, zero_add
-/
theorem oangle_add_cyc3_neg_left {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π := by
  rw [o.oangle_neg_left hx hy]; rw [o.oangle_neg_left hy hz]; rw [o.oangle_neg_left hz hx]; rw [show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
      o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : Real.Angle) by abel]; rw [o.oangle_add_cyc3 hx hy hz]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [zero_add]; rw [zero_add]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
/--
theorem `oangle_add_cyc3_neg_right` / 定理 `oangle_add_cyc3_neg_right`

English:
theorem oangle_add_cyc3_neg_right
  given: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  proof: by
  simp_rw [← oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

中文:
定理 oangle_add_cyc3_neg_right
  条件: {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0)
  证明: by
  simp_rw [← oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

Depends on / 依赖: o.oangle_add_cyc3_neg_left, oangle_add_cyc3_neg_left, oangle_neg_left_eq_neg_right, simp_rw
-/
theorem oangle_add_cyc3_neg_right {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) :
    o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π := by
  simp_rw [← oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

/--
theorem `oangle_sub_eq_oangle_sub_rev_of_norm_eq` / 定理 `oangle_sub_eq_oangle_sub_rev_of_norm_eq`

English:
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq
  given: {x y : V} (h : ‖x‖ = ‖y‖)
  proof: by simp [oangle, h]

中文:
定理 oangle_sub_eq_oangle_sub_rev_of_norm_eq
  条件: {x y : V} (h : ‖x‖ = ‖y‖)
  证明: by simp [oangle, h]

Depends on / 依赖: oangle
-/
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    o.oangle x (x - y) = o.oangle (y - x) y := by simp [oangle, h]

/--
theorem `oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq` / 定理 `oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq`

English:
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
  given: {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖)
  proof: by
  rw [two_zsmul]
  nth_rw 1 [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq]; rw [← oangle_neg_neg]; rw [← add_assoc]
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at h
    exact hn h
  have hx : x != 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert! o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) using 1
  simp

中文:
定理 oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq
  条件: {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖)
  证明: by
  rw [two_zsmul]
  nth_rw 1 [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq]; rw [← oangle_neg_neg]; rw [← add_assoc]
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at h
    exact hn h
  have hx : x != 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert! o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) using 1
  simp

Depends on / 依赖: add_assoc, convert, eq_sub_iff_add_eq, h.symm, hn.symm, neg_ne_zero, norm_eq_zero, norm_ne_zero_iff, norm_zero, nth_rw, o.oangle_add_cyc3_neg_right, o.oangle_sub_eq_oangle_sub_rev_of_norm_eq, oangle_add_cyc3_neg_right, oangle_neg_neg, oangle_sub_eq_oangle_sub_rev_of_norm_eq, sub_ne_zero_of_ne, two_zsmul
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖) :
    o.oangle y x = π - (2 : Int) • o.oangle (y - x) y := by
  rw [two_zsmul]
  nth_rw 1 [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq]; rw [← oangle_neg_neg]; rw [← add_assoc]
  have hy : y != 0 := by
    rintro rfl
    rw [norm_zero]; rw [norm_eq_zero] at h
    exact hn h
  have hx : x != 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert! o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) using 1
  simp

/-- The angle between two vectors, with respect to an orientation given by `Orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp]
/--
theorem `oangle_map` / 定理 `oangle_map`

English:
theorem oangle_map
  given: (x y : V') (f : V ≃ₗᵢ[Real] V')
  proof: by
  simp [oangle, o.kahler_map]

@[simp]

中文:
定理 oangle_map
  条件: (x y : V') (f : V ≃ₗᵢ[实数] V')
  证明: by
  simp [oangle, o.kahler_map]

@[simp]

Depends on / 依赖: kahler_map, o.kahler_map, oangle
-/
theorem oangle_map (x y : V') (f : V ≃ₗᵢ[Real] V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).oangle x y = o.oangle (f.symm x) (f.symm y) := by
  simp [oangle, o.kahler_map]

@[simp]
/--
theorem `_root_.Complex.oangle` / 定理 `_root_.Complex.oangle`

English:
theorem _root_.Complex.oangle
  given: (w z : Complex)
  proof: by
  simp [oangle, mul_comm z]

中文:
定理 _root_.复形.oangle
  条件: (w z : 复形)
  证明: by
  simp [oangle, mul_comm z]
-/
protected theorem _root_.Complex.oangle (w z : Complex) :
    Complex.orientation.oangle w z = Complex.arg (conj w * z) := by
  simp [oangle, mul_comm z]

/--
theorem `oangle_map_complex` / 定理 `oangle_map_complex`

English:
theorem oangle_map_complex
  statement: (f : V ≃ₗᵢ[Real] Complex)
  proof: by
  rw [← Complex.oangle]; rw [← hf]; rw [o.oangle_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 oangle_map_complex
  结论: (f : V ≃ₗᵢ[实数] 复形)
  证明: by
  rw [← Complex.oangle]; rw [← hf]; rw [o.oangle_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: Complex.oangle, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, iterate, o.oangle_map, oangle, oangle_map, symm_apply_apply
-/
theorem oangle_map_complex (f : V ≃ₗᵢ[Real] Complex)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : V) :
    o.oangle x y = Complex.arg (conj (f x) * f y) := by
  rw [← Complex.oangle]; rw [← hf]; rw [o.oangle_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

/--
theorem `oangle_neg_orientation_eq_neg` / 定理 `oangle_neg_orientation_eq_neg`

English:
theorem oangle_neg_orientation_eq_neg
  given: (x y : V)
  statement: (-o).oangle x y = -o.oangle x y
  proof: by
  simp [oangle]

中文:
定理 oangle_neg_orientation_eq_neg
  条件: (x y : V)
  结论: (-o).oangle x y = -o.oangle x y
  证明: by
  simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -o.oangle x y := by
  simp [oangle]

/--
theorem `inner_eq_norm_mul_norm_mul_cos_oangle` / 定理 `inner_eq_norm_mul_norm_mul_cos_oangle`

English:
theorem inner_eq_norm_mul_norm_mul_cos_oangle
  given: (x y : V)
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle]; rw [Real.Angle.cos_coe]; rw [Complex.cos_arg]; rw [o.norm_kahler]
  · simp only [kahler_apply_apply, real_smul, add_re, ofReal_re, mul_re, I_re, ofReal_im]
    simp [field]
  · exact o.kahler_ne_zero hx hy

中文:
定理 inner_eq_norm_mul_norm_mul_cos_oangle
  条件: (x y : V)
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle]; rw [Real.Angle.cos_coe]; rw [Complex.cos_arg]; rw [o.norm_kahler]
  · simp only [kahler_apply_apply, real_smul, add_re, ofReal_re, mul_re, I_re, ofReal_im]
    simp [field]
  · exact o.kahler_ne_zero hx hy

Depends on / 依赖: Complex.cos_arg, I_re, Real.Angle.cos_coe, add_re, cos_arg, cos_coe, kahler_apply_apply, kahler_ne_zero, mul_re, norm_kahler, o.kahler_ne_zero, o.norm_kahler, oangle, ofReal_im, ofReal_re, real_smul
-/
theorem inner_eq_norm_mul_norm_mul_cos_oangle (x y : V) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ * Real.Angle.cos (o.oangle x y) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle]; rw [Real.Angle.cos_coe]; rw [Complex.cos_arg]; rw [o.norm_kahler]
  · simp only [kahler_apply_apply, real_smul, add_re, ofReal_re, mul_re, I_re, ofReal_im]
    simp [field]
  · exact o.kahler_ne_zero hx hy

/--
theorem `cos_oangle_eq_inner_div_norm_mul_norm` / 定理 `cos_oangle_eq_inner_div_norm_mul_norm`

English:
theorem cos_oangle_eq_inner_div_norm_mul_norm
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle]
  field

中文:
定理 cos_oangle_eq_inner_div_norm_mul_norm
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle]
  field

Depends on / 依赖: inner_eq_norm_mul_norm_mul_cos_oangle, o.inner_eq_norm_mul_norm_mul_cos_oangle
-/
theorem cos_oangle_eq_inner_div_norm_mul_norm {x y : V} (hx : x != 0) (hy : y != 0) :
    Real.Angle.cos (o.oangle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle]
  field

/--
theorem `cos_oangle_eq_cos_angle` / 定理 `cos_oangle_eq_cos_angle`

English:
theorem cos_oangle_eq_cos_angle
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy]; rw [InnerProductGeometry.cos_angle]

中文:
定理 cos_oangle_eq_cos_angle
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy]; rw [InnerProductGeometry.cos_angle]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.cos_angle, cos_angle, cos_oangle_eq_inner_div_norm_mul_norm, o.cos_oangle_eq_inner_div_norm_mul_norm
-/
theorem cos_oangle_eq_cos_angle {x y : V} (hx : x != 0) (hy : y != 0) :
    Real.Angle.cos (o.oangle x y) = Real.cos (InnerProductGeometry.angle x y) := by
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy]; rw [InnerProductGeometry.cos_angle]

/--
theorem `oangle_eq_angle_or_eq_neg_angle` / 定理 `oangle_eq_angle_or_eq_neg_angle`

English:
theorem oangle_eq_angle_or_eq_neg_angle
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 o.cos_oangle_eq_cos_angle hx hy

中文:
定理 oangle_eq_angle_or_eq_neg_angle
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 o.cos_oangle_eq_cos_angle hx hy

Depends on / 依赖: Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg, cos_eq_real_cos_iff_eq_or_eq_neg, cos_oangle_eq_cos_angle, o.cos_oangle_eq_cos_angle
-/
theorem oangle_eq_angle_or_eq_neg_angle {x y : V} (hx : x != 0) (hy : y != 0) :
    o.oangle x y = InnerProductGeometry.angle x y ∨
      o.oangle x y = -InnerProductGeometry.angle x y :=
Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 o.cos_oangle_eq_cos_angle hx hy

/--
theorem `angle_eq_abs_oangle_toReal` / 定理 `angle_eq_abs_oangle_toReal`

English:
theorem angle_eq_abs_oangle_toReal
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  have h0 := InnerProductGeometry.angle_nonneg x y
  have hpi := InnerProductGeometry.angle_le_pi x y
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h | h)
  · rw [h, eq_comm, Real.Angle.abs_toReal_coe_eq_self_iff]
    exact ⟨h0, hpi⟩
  · rw [h, eq_comm, Real.Angle.abs_toReal_neg_coe_eq_self_iff]
    exact ⟨h0, hpi⟩

中文:
定理 angle_eq_abs_oangle_to实数
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  have h0 := InnerProductGeometry.angle_nonneg x y
  have hpi := InnerProductGeometry.angle_le_pi x y
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h | h)
  · rw [h, eq_comm, Real.Angle.abs_toReal_coe_eq_self_iff]
    exact ⟨h0, hpi⟩
  · rw [h, eq_comm, Real.Angle.abs_toReal_neg_coe_eq_self_iff]
    exact ⟨h0, hpi⟩

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_le_pi, InnerProductGeometry.angle_nonneg, Real.Angle.abs_toReal_coe_eq_self_iff, Real.Angle.abs_toReal_neg_coe_eq_self_iff, abs_toReal_coe_eq_self_iff, abs_toReal_neg_coe_eq_self_iff, angle_le_pi, angle_nonneg, eq_comm, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle
-/
theorem angle_eq_abs_oangle_toReal {x y : V} (hx : x != 0) (hy : y != 0) :
    InnerProductGeometry.angle x y = |(o.oangle x y).toReal| := by
  have h0 := InnerProductGeometry.angle_nonneg x y
  have hpi := InnerProductGeometry.angle_le_pi x y
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h | h)
  · rw [h, eq_comm, Real.Angle.abs_toReal_coe_eq_self_iff]
    exact ⟨h0, hpi⟩
  · rw [h, eq_comm, Real.Angle.abs_toReal_neg_coe_eq_self_iff]
    exact ⟨h0, hpi⟩

/--
theorem `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero` / 定理 `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero`

English:
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
  statement: {x y : V}
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.angle_eq_abs_oangle_toReal hx hy]
  rw [Real.Angle.sign_eq_zero_iff] at h
  rcases h with (h | h) <;> simp [h, Real.pi_pos.le]

中文:
定理 eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
  结论: {x y : V}
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.angle_eq_abs_oangle_toReal hx hy]
  rw [Real.Angle.sign_eq_zero_iff] at h
  rcases h with (h | h) <;> simp [h, Real.pi_pos.le]

Depends on / 依赖: Real.Angle.sign_eq_zero_iff, Real.pi_pos.le, angle_eq_abs_oangle_toReal, o.angle_eq_abs_oangle_toReal, pi_pos, sign_eq_zero_iff
-/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V}
    (h : (o.oangle x y).sign = 0) :
    x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x y = 0 ∨ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.angle_eq_abs_oangle_toReal hx hy]
  rw [Real.Angle.sign_eq_zero_iff] at h
  rcases h with (h | h) <;> simp [h, Real.pi_pos.le]

/--
theorem `oangle_eq_of_angle_eq_of_sign_eq` / 定理 `oangle_eq_of_angle_eq_of_sign_eq`

English:
theorem oangle_eq_of_angle_eq_of_sign_eq
  statement: {w x y z : V}
  proof: by
  by_cases! h0 : (w = 0 ∨ x = 0) ∨ y = 0 ∨ z = 0
  · have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using hs.symm
      · simpa using hs.symm
      · simpa using hs
      · simpa using hs
    rcases hs' with ⟨hswx, hsyz⟩
    have h' : InnerProductGeometry.angle w x = π / 2 ∧ InnerProductGeometry.angle y z = π / 2 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using h.symm
      · simpa using h.symm
      · simpa using h
      · simpa using h
    rcases h' with ⟨hwx, hyz⟩
    have hpi : π / 2 != π := by
      intro hpi
      rw [div_eq_iff]; rw [eq_comm]; rw [← sub_eq_zero]; rw [mul_two]; rw [add_sub_cancel_right] at hpi
      · exact Real.pi_pos.ne.symm hpi
      · exact two_ne_zero
    have h0wx : w = 0 ∨ x = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx
      simpa [hwx, Real.pi_pos.ne.symm, hpi] using h0'
    have h0yz : y = 0 ∨ z = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz
      simpa [hyz, Real.pi_pos.ne.symm, hpi] using h0'
    rcases h0wx with (h0wx | h0wx) <;> rcases h0yz with (h0yz | h0yz) <;> simp [h0wx, h0yz]
  · rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hs]
    rwa [o.angle_eq_abs_oangle_toReal h0.1.1 h0.1.2,
      o.angle_eq_abs_oangle_toReal h0.2.1 h0.2.2] at h

中文:
定理 oangle_eq_of_angle_eq_of_sign_eq
  结论: {w x y z : V}
  证明: by
  by_cases! h0 : (w = 0 ∨ x = 0) ∨ y = 0 ∨ z = 0
  · have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using hs.symm
      · simpa using hs.symm
      · simpa using hs
      · simpa using hs
    rcases hs' with ⟨hswx, hsyz⟩
    have h' : InnerProductGeometry.angle w x = π / 2 ∧ InnerProductGeometry.angle y z = π / 2 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using h.symm
      · simpa using h.symm
      · simpa using h
      · simpa using h
    rcases h' with ⟨hwx, hyz⟩
    have hpi : π / 2 != π := by
      intro hpi
      rw [div_eq_iff]; rw [eq_comm]; rw [← sub_eq_zero]; rw [mul_two]; rw [add_sub_cancel_right] at hpi
      · exact Real.pi_pos.ne.symm hpi
      · exact two_ne_zero
    have h0wx : w = 0 ∨ x = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx
      simpa [hwx, Real.pi_pos.ne.symm, hpi] using h0'
    have h0yz : y = 0 ∨ z = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz
      simpa [hyz, Real.pi_pos.ne.symm, hpi] using h0'
    rcases h0wx with (h0wx | h0wx) <;> rcases h0yz with (h0yz | h0yz) <;> simp [h0wx, h0yz]
  · rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hs]
    rwa [o.angle_eq_abs_oangle_toReal h0.1.1 h0.1.2,
      o.angle_eq_abs_oangle_toReal h0.2.1 h0.2.2] at h

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle, h.symm, hs.symm, o.oangle, oangle
-/
theorem oangle_eq_of_angle_eq_of_sign_eq {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = (o.oangle y z).sign) : o.oangle w x = o.oangle y z := by
  by_cases! h0 : (w = 0 ∨ x = 0) ∨ y = 0 ∨ z = 0
  · have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using hs.symm
      · simpa using hs.symm
      · simpa using hs
      · simpa using hs
    rcases hs' with ⟨hswx, hsyz⟩
    have h' : InnerProductGeometry.angle w x = π / 2 ∧ InnerProductGeometry.angle y z = π / 2 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using h.symm
      · simpa using h.symm
      · simpa using h
      · simpa using h
    rcases h' with ⟨hwx, hyz⟩
    have hpi : π / 2 != π := by
      intro hpi
      rw [div_eq_iff]; rw [eq_comm]; rw [← sub_eq_zero]; rw [mul_two]; rw [add_sub_cancel_right] at hpi
      · exact Real.pi_pos.ne.symm hpi
      · exact two_ne_zero
    have h0wx : w = 0 ∨ x = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx
      simpa [hwx, Real.pi_pos.ne.symm, hpi] using h0'
    have h0yz : y = 0 ∨ z = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz
      simpa [hyz, Real.pi_pos.ne.symm, hpi] using h0'
    rcases h0wx with (h0wx | h0wx) <;> rcases h0yz with (h0yz | h0yz) <;> simp [h0wx, h0yz]
  · rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hs]
    rwa [o.angle_eq_abs_oangle_toReal h0.1.1 h0.1.2,
      o.angle_eq_abs_oangle_toReal h0.2.1 h0.2.2] at h

/--
theorem `angle_eq_iff_oangle_eq_of_sign_eq` / 定理 `angle_eq_iff_oangle_eq_of_sign_eq`

English:
theorem angle_eq_iff_oangle_eq_of_sign_eq
  statement: {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => o.oangle_eq_of_angle_eq_of_sign_eq h hs, fun h => ?_⟩
  rw [o.angle_eq_abs_oangle_toReal hw hx]; rw [o.angle_eq_abs_oangle_toReal hy hz]; rw [h]

中文:
定理 angle_eq_iff_oangle_eq_of_sign_eq
  结论: {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => o.oangle_eq_of_angle_eq_of_sign_eq h hs, fun h => ?_⟩
  rw [o.angle_eq_abs_oangle_toReal hw hx]; rw [o.angle_eq_abs_oangle_toReal hy hz]; rw [h]

Depends on / 依赖: angle_eq_abs_oangle_toReal, o.angle_eq_abs_oangle_toReal, o.oangle_eq_of_angle_eq_of_sign_eq, oangle_eq_of_angle_eq_of_sign_eq
-/
theorem angle_eq_iff_oangle_eq_of_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0)
    (hz : z != 0) (hs : (o.oangle w x).sign = (o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
    o.oangle w x = o.oangle y z := by
  refine ⟨fun h => o.oangle_eq_of_angle_eq_of_sign_eq h hs, fun h => ?_⟩
  rw [o.angle_eq_abs_oangle_toReal hw hx]; rw [o.angle_eq_abs_oangle_toReal hy hz]; rw [h]

/--
lemma `oangle_eq_neg_of_angle_eq_of_sign_eq_neg` / 引理 `oangle_eq_neg_of_angle_eq_of_sign_eq_neg`

English:
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg
  statement: {w x y z : V}
  proof: by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm] at h
  exact o.oangle_eq_of_angle_eq_of_sign_eq h hs

中文:
引理 oangle_eq_neg_of_angle_eq_of_sign_eq_neg
  结论: {w x y z : V}
  证明: by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm] at h
  exact o.oangle_eq_of_angle_eq_of_sign_eq h hs

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_comm, Real.Angle.sign_neg, angle_comm, nth_rw, o.oangle_eq_of_angle_eq_of_sign_eq, oangle_eq_of_angle_eq_of_sign_eq, oangle_rev, sign_neg
-/
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = -(o.oangle y z).sign) : o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm] at h
  exact o.oangle_eq_of_angle_eq_of_sign_eq h hs

/--
lemma `angle_eq_iff_oangle_eq_neg_of_sign_eq_neg` / 引理 `angle_eq_iff_oangle_eq_neg_of_sign_eq_neg`

English:
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg
  statement: {w x y z : V} (hw : w != 0) (hx : x != 0)
  proof: by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm]
  exact o.angle_eq_iff_oangle_eq_of_sign_eq hw hx hz hy hs

中文:
引理 angle_eq_iff_oangle_eq_neg_of_sign_eq_neg
  结论: {w x y z : V} (hw : w != 0) (hx : x != 0)
  证明: by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm]
  exact o.angle_eq_iff_oangle_eq_of_sign_eq hw hx hz hy hs

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_comm, Real.Angle.sign_neg, angle_comm, angle_eq_iff_oangle_eq_of_sign_eq, nth_rw, o.angle_eq_iff_oangle_eq_of_sign_eq, oangle_rev, sign_neg
-/
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w != 0) (hx : x != 0)
    (hy : y != 0) (hz : z != 0) (hs : (o.oangle w x).sign = -(o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
      o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg]; rw [← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm]
  exact o.angle_eq_iff_oangle_eq_of_sign_eq hw hx hz hy hs

/--
theorem `oangle_eq_angle_of_sign_eq_one` / 定理 `oangle_eq_angle_of_sign_eq_one`

English:
theorem oangle_eq_angle_of_sign_eq_one
  given: {x y : V} (h : (o.oangle x y).sign = 1)
  proof: by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_right ?_
  intro hxy
  rw [hxy]; rw [Real.Angle.sign_neg]; rw [neg_eq_iff_eq_neg]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

中文:
定理 oangle_eq_angle_of_sign_eq_one
  条件: {x y : V} (h : (o.oangle x y).sign = 1)
  证明: by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_right ?_
  intro hxy
  rw [hxy]; rw [Real.Angle.sign_neg]; rw [neg_eq_iff_eq_neg]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_le_pi, InnerProductGeometry.angle_nonneg, Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi, Real.Angle.sign_neg, SignType, SignType.neg_iff, angle_le_pi, angle_nonneg, neg_eq_iff_eq_neg, neg_iff, not_le, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle, resolve_right, sign_coe_nonneg_of_nonneg_of_le_pi, sign_neg
-/
theorem oangle_eq_angle_of_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) :
    o.oangle x y = InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_right ?_
  intro hxy
  rw [hxy]; rw [Real.Angle.sign_neg]; rw [neg_eq_iff_eq_neg]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/--
theorem `oangle_eq_neg_angle_of_sign_eq_neg_one` / 定理 `oangle_eq_neg_angle_of_sign_eq_neg_one`

English:
theorem oangle_eq_neg_angle_of_sign_eq_neg_one
  given: {x y : V} (h : (o.oangle x y).sign = -1)
  proof: by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_left ?_
  intro hxy
  rw [hxy]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

中文:
定理 oangle_eq_neg_angle_of_sign_eq_neg_one
  条件: {x y : V} (h : (o.oangle x y).sign = -1)
  证明: by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_left ?_
  intro hxy
  rw [hxy]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_le_pi, InnerProductGeometry.angle_nonneg, Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi, SignType, SignType.neg_iff, angle_le_pi, angle_nonneg, neg_iff, not_le, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle, resolve_left, sign_coe_nonneg_of_nonneg_of_le_pi
-/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) :
    o.oangle x y = -InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_left ?_
  intro hxy
  rw [hxy]; rw [← SignType.neg_iff]; rw [← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/--
theorem `oangle_eq_zero_iff_angle_eq_zero` / 定理 `oangle_eq_zero_iff_angle_eq_zero`

English:
theorem oangle_eq_zero_iff_angle_eq_zero
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [o.angle_eq_abs_oangle_toReal hx hy]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

中文:
定理 oangle_eq_zero_iff_angle_eq_zero
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [o.angle_eq_abs_oangle_toReal hx hy]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

Depends on / 依赖: angle_eq_abs_oangle_toReal, o.angle_eq_abs_oangle_toReal, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle
-/
theorem oangle_eq_zero_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) :
    o.oangle x y = 0 ↔ InnerProductGeometry.angle x y = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [o.angle_eq_abs_oangle_toReal hx hy]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/--
theorem `oangle_eq_pi_iff_angle_eq_pi` / 定理 `oangle_eq_pi_iff_angle_eq_pi`

English:
theorem oangle_eq_pi_iff_angle_eq_pi
  given: {x y : V}
  proof: by
  by_cases hx : x = 0
  · simp [hx, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  by_cases hy : y = 0
  · simp [hy, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [o.angle_eq_abs_oangle_toReal hx hy, h]
    simp [Real.pi_pos.le]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

中文:
定理 oangle_eq_pi_iff_angle_eq_pi
  条件: {x y : V}
  证明: by
  by_cases hx : x = 0
  · simp [hx, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  by_cases hy : y = 0
  · simp [hy, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [o.angle_eq_abs_oangle_toReal hx hy, h]
    simp [Real.pi_pos.le]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

Depends on / 依赖: Real.Angle.pi_ne_zero.symm, Real.pi_ne_zero, Real.pi_pos.le, angle_eq_abs_oangle_toReal, div_eq_mul_inv, o.angle_eq_abs_oangle_toReal, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle, pi_ne_zero, pi_pos
-/
theorem oangle_eq_pi_iff_angle_eq_pi {x y : V} :
    o.oangle x y = π ↔ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0
  · simp [hx, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  by_cases hy : y = 0
  · simp [hy, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [o.angle_eq_abs_oangle_toReal hx hy, h]
    simp [Real.pi_pos.le]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/--
theorem `eq_zero_or_oangle_eq_iff_inner_eq_zero` / 定理 `eq_zero_or_oangle_eq_iff_inner_eq_zero`

English:
theorem eq_zero_or_oangle_eq_iff_inner_eq_zero
  given: {x y : V}
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]; rw [or_iff_right hx]; rw [or_iff_right hy]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [o.angle_eq_abs_oangle_toReal hx hy, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  · convert! o.oangle_eq_angle_or_eq_neg_angle hx hy using 2 <;> rw [h]
    simp only [neg_div, Real.Angle.coe_neg]

中文:
定理 eq_zero_or_oangle_eq_iff_inner_eq_zero
  条件: {x y : V}
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]; rw [or_iff_right hx]; rw [or_iff_right hy]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [o.angle_eq_abs_oangle_toReal hx hy, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  · convert! o.oangle_eq_angle_or_eq_neg_angle hx hy using 2 <;> rw [h]
    simp only [neg_div, Real.Angle.coe_neg]

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, Real.Angle.abs_toReal_eq_pi_div_two_iff, Real.Angle.coe_neg, abs_toReal_eq_pi_div_two_iff, angle_eq_abs_oangle_toReal, coe_neg, convert, inner_eq_zero_iff_angle_eq_pi_div_two, neg_div, o.angle_eq_abs_oangle_toReal, o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle, or_iff_right
-/
theorem eq_zero_or_oangle_eq_iff_inner_eq_zero {x y : V} :
    x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : Real) ∨ o.oangle x y = (-π / 2 : Real) ↔ ⟪x, y⟫ = 0 := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]; rw [or_iff_right hx]; rw [or_iff_right hy]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [o.angle_eq_abs_oangle_toReal hx hy, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  · convert! o.oangle_eq_angle_or_eq_neg_angle hx hy using 2 <;> rw [h]
    simp only [neg_div, Real.Angle.coe_neg]

/--
theorem `inner_eq_zero_of_oangle_eq_pi_div_two` / 定理 `inner_eq_zero_of_oangle_eq_pi_div_two`

English:
theorem inner_eq_zero_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = (π / 2 : Real))
  proof: o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inl h

中文:
定理 inner_eq_zero_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (π / 2 : 实数))
  证明: o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inl h

Depends on / 依赖: Or.inl, Or.inr, eq_zero_or_oangle_eq_iff_inner_eq_zero, o.eq_zero_or_oangle_eq_iff_inner_eq_zero
-/
theorem inner_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) :
    ⟪x, y⟫ = 0 :=
o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inl h

/--
theorem `inner_rev_eq_zero_of_oangle_eq_pi_div_two` / 定理 `inner_rev_eq_zero_of_oangle_eq_pi_div_two`

English:
theorem inner_rev_eq_zero_of_oangle_eq_pi_div_two
  given: {x y : V} (h : o.oangle x y = (π / 2 : Real))
  proof: by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_pi_div_two h]

中文:
定理 inner_rev_eq_zero_of_oangle_eq_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (π / 2 : 实数))
  证明: by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_pi_div_two h]

Depends on / 依赖: inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two, real_inner_comm
-/
theorem inner_rev_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_pi_div_two h]

/--
theorem `inner_eq_zero_of_oangle_eq_neg_pi_div_two` / 定理 `inner_eq_zero_of_oangle_eq_neg_pi_div_two`

English:
theorem inner_eq_zero_of_oangle_eq_neg_pi_div_two
  given: {x y : V} (h : o.oangle x y = (-π / 2 : Real))
  proof: o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inr h

中文:
定理 inner_eq_zero_of_oangle_eq_neg_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (-π / 2 : 实数))
  证明: o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inr h

Depends on / 依赖: Or.inr, eq_zero_or_oangle_eq_iff_inner_eq_zero, o.eq_zero_or_oangle_eq_iff_inner_eq_zero
-/
theorem inner_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) :
    ⟪x, y⟫ = 0 :=
o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 Or.inr Or.inr Or.inr h

/--
theorem `inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two` / 定理 `inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two`

English:
theorem inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two
  given: {x y : V} (h : o.oangle x y = (-π / 2 : Real))
  proof: by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h]

中文:
定理 inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two
  条件: {x y : V} (h : o.oangle x y = (-π / 2 : 实数))
  证明: by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h]

Depends on / 依赖: inner_eq_zero_of_oangle_eq_neg_pi_div_two, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two, real_inner_comm
-/
theorem inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h]

/-- Negating the first vector passed to `oangle` negates the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_neg_left` / 定理 `oangle_sign_neg_left`

English:
theorem oangle_sign_neg_left
  given: (x y : V)
  statement: (o.oangle (-x) y).sign = -(o.oangle x y).sign
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_left hx hy]; rw [Real.Angle.sign_add_pi]

中文:
定理 oangle_sign_neg_left
  条件: (x y : V)
  结论: (o.oangle (-x) y).sign = -(o.oangle x y).sign
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_left hx hy]; rw [Real.Angle.sign_add_pi]

Depends on / 依赖: Real.Angle.sign_add_pi, o.oangle_neg_left, oangle_neg_left, sign_add_pi
-/
theorem oangle_sign_neg_left (x y : V) : (o.oangle (-x) y).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_left hx hy]; rw [Real.Angle.sign_add_pi]

/-- Negating the second vector passed to `oangle` negates the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_neg_right` / 定理 `oangle_sign_neg_right`

English:
theorem oangle_sign_neg_right
  given: (x y : V)
  statement: (o.oangle x (-y)).sign = -(o.oangle x y).sign
  proof: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_right hx hy]; rw [Real.Angle.sign_add_pi]

中文:
定理 oangle_sign_neg_right
  条件: (x y : V)
  结论: (o.oangle x (-y)).sign = -(o.oangle x y).sign
  证明: by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_right hx hy]; rw [Real.Angle.sign_add_pi]

Depends on / 依赖: Real.Angle.sign_add_pi, o.oangle_neg_right, oangle_neg_right, sign_add_pi
-/
theorem oangle_sign_neg_right (x y : V) : (o.oangle x (-y)).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_right hx hy]; rw [Real.Angle.sign_add_pi]

/-- Multiplying the first vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
/--
theorem `oangle_sign_smul_left` / 定理 `oangle_sign_smul_left`

English:
theorem oangle_sign_smul_left
  given: (x y : V) (r : Real)
  proof: by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

中文:
定理 oangle_sign_smul_left
  条件: (x y : V) (r : 实数)
  证明: by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

Depends on / 依赖: lt_trichotomy
-/
theorem oangle_sign_smul_left (x y : V) (r : Real) :
    (o.oangle (r • x) y).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
/--
theorem `oangle_sign_smul_right` / 定理 `oangle_sign_smul_right`

English:
theorem oangle_sign_smul_right
  given: (x y : V) (r : Real)
  proof: by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

中文:
定理 oangle_sign_smul_right
  条件: (x y : V) (r : 实数)
  证明: by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

Depends on / 依赖: lt_trichotomy
-/
theorem oangle_sign_smul_right (x y : V) (r : Real) :
    (o.oangle x (r • y)).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/--
theorem `oangle_smul_add_right_eq_zero_or_eq_pi_iff` / 定理 `oangle_smul_add_right_eq_zero_or_eq_pi_iff`

English:
theorem oangle_smul_add_right_eq_zero_or_eq_pi_iff
  given: {x y : V} (r : Real)
  proof: by
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, Fintype.not_linearIndependent_iff,
    Fin.sum_univ_two, Fin.exists_fin_two]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • (r • x + y) = 0 at h
    refine ⟨![m 0 + m 1 * r, m 1], ?_⟩
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r != 0 ∨ m 1 != 0)
    rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [← add_smul] at h
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [add_zero] at h0
    simp [h0] at hm
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • y = 0 at h
    refine ⟨![m 0 - m 1 * r, m 1], ?_⟩
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r != 0 ∨ m 1 != 0)
    rw [sub_smul]; rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [sub_add_cancel]
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [sub_zero] at h0
    simp [h0] at hm

中文:
定理 oangle_smul_add_right_eq_zero_or_eq_pi_iff
  条件: {x y : V} (r : 实数)
  证明: by
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, Fintype.not_linearIndependent_iff,
    Fin.sum_univ_two, Fin.exists_fin_two]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • (r • x + y) = 0 at h
    refine ⟨![m 0 + m 1 * r, m 1], ?_⟩
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r != 0 ∨ m 1 != 0)
    rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [← add_smul] at h
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [add_zero] at h0
    simp [h0] at hm
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • y = 0 at h
    refine ⟨![m 0 - m 1 * r, m 1], ?_⟩
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r != 0 ∨ m 1 != 0)
    rw [sub_smul]; rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [sub_add_cancel]
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [sub_zero] at h0
    simp [h0] at hm

Depends on / 依赖: Fin.exists_fin_two, Fin.sum_univ_two, Fintype, Fintype.not_linearIndependent_iff, add_assoc, add_smul, exists_fin_two, not_and_or, not_linearIndependent_iff, oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, simp_rw, smul_add, smul_smul, sum_univ_two
-/
theorem oangle_smul_add_right_eq_zero_or_eq_pi_iff {x y : V} (r : Real) :
    o.oangle x (r • x + y) = 0 ∨ o.oangle x (r • x + y) = π ↔
    o.oangle x y = 0 ∨ o.oangle x y = π := by
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, Fintype.not_linearIndependent_iff,
    Fin.sum_univ_two, Fin.exists_fin_two]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • (r • x + y) = 0 at h
    refine ⟨![m 0 + m 1 * r, m 1], ?_⟩
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r != 0 ∨ m 1 != 0)
    rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [← add_smul] at h
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [add_zero] at h0
    simp [h0] at hm
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • y = 0 at h
    refine ⟨![m 0 - m 1 * r, m 1], ?_⟩
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r != 0 ∨ m 1 != 0)
    rw [sub_smul]; rw [smul_add]; rw [smul_smul]; rw [← add_assoc]; rw [sub_add_cancel]
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul]; rw [sub_zero] at h0
    simp [h0] at hm

/-- Adding a multiple of the first vector passed to `oangle` to the second vector does not change
the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_smul_add_right` / 定理 `oangle_sign_smul_add_right`

English:
theorem oangle_sign_smul_add_right
  given: (x y : V) (r : Real)
  proof: by
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π
  · rwa [Real.Angle.sign_eq_zero_iff.2 h, Real.Angle.sign_eq_zero_iff,
      oangle_smul_add_right_eq_zero_or_eq_pi_iff]
  have h' : forall r' : Real, o.oangle x (r' • x + y) != 0 ∧ o.oangle x (r' • x + y) != π := by
    intro r'
    rwa [← o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or] at h
  let s : Set (V × V) := (fun r' : Real => (x, r' • x + y)) '' Set.univ
  have hc : IsConnected s := isConnected_univ.image _ (by fun_prop)
  have hf : ContinuousOn (fun z : V × V => o.oangle z.1 z.2) s := by
    refine continuousOn_of_forall_continuousAt fun z hz => o.continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [s, Set.mem_image] at hz
      obtain ⟨r', -, rfl⟩ := hz
      simp only
      intro hz
    · simpa [hz] using (h' 0).1
    · simpa [hz] using (h' r').1
  have hs : forall z : V × V, z in s -> o.oangle z.1 z.2 != 0 ∧ o.oangle z.1 z.2 != π := by grind
  have hx : (x, y) in s := by
    convert! Set.mem_image_of_mem (fun r' : Real => (x, r' • x + y)) (Set.mem_univ 0)
    simp
  have hy : (x, r • x + y) in s := Set.mem_image_of_mem _ (Set.mem_univ _)
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hs hx hy

中文:
定理 oangle_sign_smul_add_right
  条件: (x y : V) (r : 实数)
  证明: by
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π
  · rwa [Real.Angle.sign_eq_zero_iff.2 h, Real.Angle.sign_eq_zero_iff,
      oangle_smul_add_right_eq_zero_or_eq_pi_iff]
  have h' : forall r' : Real, o.oangle x (r' • x + y) != 0 ∧ o.oangle x (r' • x + y) != π := by
    intro r'
    rwa [← o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or] at h
  let s : Set (V × V) := (fun r' : Real => (x, r' • x + y)) '' Set.univ
  have hc : IsConnected s := isConnected_univ.image _ (by fun_prop)
  have hf : ContinuousOn (fun z : V × V => o.oangle z.1 z.2) s := by
    refine continuousOn_of_forall_continuousAt fun z hz => o.continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [s, Set.mem_image] at hz
      obtain ⟨r', -, rfl⟩ := hz
      simp only
      intro hz
    · simpa [hz] using (h' 0).1
    · simpa [hz] using (h' r').1
  have hs : forall z : V × V, z in s -> o.oangle z.1 z.2 != 0 ∧ o.oangle z.1 z.2 != π := by grind
  have hx : (x, y) in s := by
    convert! Set.mem_image_of_mem (fun r' : Real => (x, r' • x + y)) (Set.mem_univ 0)
    simp
  have hy : (x, r • x + y) in s := Set.mem_image_of_mem _ (Set.mem_univ _)
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hs hx hy

Depends on / 依赖: ContinuousOn, IsConnected, Real.Angle.sign_eq_zero_iff, Set.univ, fun_prop, isConnected_univ, isConnected_univ.image, not_or, o.oangle, o.oangle_smul_add_right_eq_zero_or_eq_pi_iff, oangle, oangle_smul_add_right_eq_zero_or_eq_pi_iff, sign_eq_zero_iff
-/
theorem oangle_sign_smul_add_right (x y : V) (r : Real) :
    (o.oangle x (r • x + y)).sign = (o.oangle x y).sign := by
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π
  · rwa [Real.Angle.sign_eq_zero_iff.2 h, Real.Angle.sign_eq_zero_iff,
      oangle_smul_add_right_eq_zero_or_eq_pi_iff]
  have h' : forall r' : Real, o.oangle x (r' • x + y) != 0 ∧ o.oangle x (r' • x + y) != π := by
    intro r'
    rwa [← o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or] at h
  let s : Set (V × V) := (fun r' : Real => (x, r' • x + y)) '' Set.univ
  have hc : IsConnected s := isConnected_univ.image _ (by fun_prop)
  have hf : ContinuousOn (fun z : V × V => o.oangle z.1 z.2) s := by
    refine continuousOn_of_forall_continuousAt fun z hz => o.continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [s, Set.mem_image] at hz
      obtain ⟨r', -, rfl⟩ := hz
      simp only
      intro hz
    · simpa [hz] using (h' 0).1
    · simpa [hz] using (h' r').1
  have hs : forall z : V × V, z in s -> o.oangle z.1 z.2 != 0 ∧ o.oangle z.1 z.2 != π := by grind
  have hx : (x, y) in s := by
    convert! Set.mem_image_of_mem (fun r' : Real => (x, r' • x + y)) (Set.mem_univ 0)
    simp
  have hy : (x, r • x + y) in s := Set.mem_image_of_mem _ (Set.mem_univ _)
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hs hx hy

/-- Adding a multiple of the second vector passed to `oangle` to the first vector does not change
the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_add_smul_left` / 定理 `oangle_sign_add_smul_left`

English:
theorem oangle_sign_add_smul_left
  given: (x y : V) (r : Real)
  proof: by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

中文:
定理 oangle_sign_add_smul_left
  条件: (x y : V) (r : 实数)
  证明: by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

Depends on / 依赖: Real.Angle.sign_neg, add_comm, o.oangle_rev, oangle_rev, oangle_sign_smul_add_right, sign_neg, simp_rw
-/
theorem oangle_sign_add_smul_left (x y : V) (r : Real) :
    (o.oangle (x + r • y) y).sign = (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the first vector passed to `oangle` from the second vector does
not change the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_smul_right` / 定理 `oangle_sign_sub_smul_right`

English:
theorem oangle_sign_sub_smul_right
  given: (x y : V) (r : Real)
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm]; rw [oangle_sign_smul_add_right]

中文:
定理 oangle_sign_sub_smul_right
  条件: (x y : V) (r : 实数)
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm]; rw [oangle_sign_smul_add_right]

Depends on / 依赖: add_comm, neg_smul, oangle_sign_smul_add_right, sub_eq_add_neg
-/
theorem oangle_sign_sub_smul_right (x y : V) (r : Real) :
    (o.oangle x (y - r • x)).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [add_comm]; rw [oangle_sign_smul_add_right]

/-- Subtracting a multiple of the second vector passed to `oangle` from the first vector does
not change the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_smul_left` / 定理 `oangle_sign_sub_smul_left`

English:
theorem oangle_sign_sub_smul_left
  given: (x y : V) (r : Real)
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [oangle_sign_add_smul_left]

中文:
定理 oangle_sign_sub_smul_left
  条件: (x y : V) (r : 实数)
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [oangle_sign_add_smul_left]

Depends on / 依赖: neg_smul, oangle_sign_add_smul_left, sub_eq_add_neg
-/
theorem oangle_sign_sub_smul_left (x y : V) (r : Real) :
    (o.oangle (x - r • y) y).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [oangle_sign_add_smul_left]

/-- Adding the first vector passed to `oangle` to the second vector does not change the sign of
the angle. -/
@[simp]
/--
theorem `oangle_sign_add_right` / 定理 `oangle_sign_add_right`

English:
theorem oangle_sign_add_right
  given: (x y : V)
  statement: (o.oangle x (x + y)).sign = (o.oangle x y).sign
  proof: by
  rw [← o.oangle_sign_smul_add_right x y 1]; rw [one_smul]

中文:
定理 oangle_sign_add_right
  条件: (x y : V)
  结论: (o.oangle x (x + y)).sign = (o.oangle x y).sign
  证明: by
  rw [← o.oangle_sign_smul_add_right x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_smul_add_right, oangle_sign_smul_add_right, one_smul
-/
theorem oangle_sign_add_right (x y : V) : (o.oangle x (x + y)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_add_right x y 1]; rw [one_smul]

/-- Adding the second vector passed to `oangle` to the first vector does not change the sign of
the angle. -/
@[simp]
/--
theorem `oangle_sign_add_left` / 定理 `oangle_sign_add_left`

English:
theorem oangle_sign_add_left
  given: (x y : V)
  statement: (o.oangle (x + y) y).sign = (o.oangle x y).sign
  proof: by
  rw [← o.oangle_sign_add_smul_left x y 1]; rw [one_smul]

中文:
定理 oangle_sign_add_left
  条件: (x y : V)
  结论: (o.oangle (x + y) y).sign = (o.oangle x y).sign
  证明: by
  rw [← o.oangle_sign_add_smul_left x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_add_smul_left, oangle_sign_add_smul_left, one_smul
-/
theorem oangle_sign_add_left (x y : V) : (o.oangle (x + y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_add_smul_left x y 1]; rw [one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector does not change the
sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_right` / 定理 `oangle_sign_sub_right`

English:
theorem oangle_sign_sub_right
  given: (x y : V)
  statement: (o.oangle x (y - x)).sign = (o.oangle x y).sign
  proof: by
  rw [← o.oangle_sign_sub_smul_right x y 1]; rw [one_smul]

中文:
定理 oangle_sign_sub_right
  条件: (x y : V)
  结论: (o.oangle x (y - x)).sign = (o.oangle x y).sign
  证明: by
  rw [← o.oangle_sign_sub_smul_right x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_sub_smul_right, oangle_sign_sub_smul_right, one_smul
-/
theorem oangle_sign_sub_right (x y : V) : (o.oangle x (y - x)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_right x y 1]; rw [one_smul]

/-- Subtracting the second vector passed to `oangle` from the first vector does not change the
sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_left` / 定理 `oangle_sign_sub_left`

English:
theorem oangle_sign_sub_left
  given: (x y : V)
  statement: (o.oangle (x - y) y).sign = (o.oangle x y).sign
  proof: by
  rw [← o.oangle_sign_sub_smul_left x y 1]; rw [one_smul]

中文:
定理 oangle_sign_sub_left
  条件: (x y : V)
  结论: (o.oangle (x - y) y).sign = (o.oangle x y).sign
  证明: by
  rw [← o.oangle_sign_sub_smul_left x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_sub_smul_left, oangle_sign_sub_smul_left, one_smul
-/
theorem oangle_sign_sub_left (x y : V) : (o.oangle (x - y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_left x y 1]; rw [one_smul]

/-- Subtracting the second vector passed to `oangle` from a multiple of the first vector negates
the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_smul_sub_right` / 定理 `oangle_sign_smul_sub_right`

English:
theorem oangle_sign_smul_sub_right
  given: (x y : V) (r : Real)
  proof: by
  rw [← oangle_sign_neg_right]; rw [sub_eq_add_neg]; rw [oangle_sign_smul_add_right]

中文:
定理 oangle_sign_smul_sub_right
  条件: (x y : V) (r : 实数)
  证明: by
  rw [← oangle_sign_neg_right]; rw [sub_eq_add_neg]; rw [oangle_sign_smul_add_right]

Depends on / 依赖: oangle_sign_neg_right, oangle_sign_smul_add_right, sub_eq_add_neg
-/
theorem oangle_sign_smul_sub_right (x y : V) (r : Real) :
    (o.oangle x (r • x - y)).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_right]; rw [sub_eq_add_neg]; rw [oangle_sign_smul_add_right]

/-- Subtracting the first vector passed to `oangle` from a multiple of the second vector negates
the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_smul_sub_left` / 定理 `oangle_sign_smul_sub_left`

English:
theorem oangle_sign_smul_sub_left
  given: (x y : V) (r : Real)
  proof: by
  rw [← oangle_sign_neg_left]; rw [sub_eq_neg_add]; rw [oangle_sign_add_smul_left]

中文:
定理 oangle_sign_smul_sub_left
  条件: (x y : V) (r : 实数)
  证明: by
  rw [← oangle_sign_neg_left]; rw [sub_eq_neg_add]; rw [oangle_sign_add_smul_left]

Depends on / 依赖: oangle_sign_add_smul_left, oangle_sign_neg_left, sub_eq_neg_add
-/
theorem oangle_sign_smul_sub_left (x y : V) (r : Real) :
    (o.oangle (r • y - x) y).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_left]; rw [sub_eq_neg_add]; rw [oangle_sign_add_smul_left]

/--
theorem `oangle_sign_sub_right_eq_neg` / 定理 `oangle_sign_sub_right_eq_neg`

English:
theorem oangle_sign_sub_right_eq_neg
  given: (x y : V)
  proof: by
  rw [← o.oangle_sign_smul_sub_right x y 1]; rw [one_smul]

中文:
定理 oangle_sign_sub_right_eq_neg
  条件: (x y : V)
  证明: by
  rw [← o.oangle_sign_smul_sub_right x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_smul_sub_right, oangle_sign_smul_sub_right, one_smul
-/
theorem oangle_sign_sub_right_eq_neg (x y : V) :
    (o.oangle x (x - y)).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_right x y 1]; rw [one_smul]

/--
theorem `oangle_sign_sub_left_eq_neg` / 定理 `oangle_sign_sub_left_eq_neg`

English:
theorem oangle_sign_sub_left_eq_neg
  given: (x y : V)
  proof: by
  rw [← o.oangle_sign_smul_sub_left x y 1]; rw [one_smul]

中文:
定理 oangle_sign_sub_left_eq_neg
  条件: (x y : V)
  证明: by
  rw [← o.oangle_sign_smul_sub_left x y 1]; rw [one_smul]

Depends on / 依赖: o.oangle_sign_smul_sub_left, oangle_sign_smul_sub_left, one_smul
-/
theorem oangle_sign_sub_left_eq_neg (x y : V) :
    (o.oangle (y - x) y).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_left x y 1]; rw [one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_right_swap` / 定理 `oangle_sign_sub_right_swap`

English:
theorem oangle_sign_sub_right_swap
  given: (x y : V)
  statement: (o.oangle y (y - x)).sign = (o.oangle x y).sign
  proof: by
  rw [oangle_sign_sub_right_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

中文:
定理 oangle_sign_sub_right_swap
  条件: (x y : V)
  结论: (o.oangle y (y - x)).sign = (o.oangle x y).sign
  证明: by
  rw [oangle_sign_sub_right_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

Depends on / 依赖: Real.Angle.sign_neg, o.oangle_rev, oangle_rev, oangle_sign_sub_right_eq_neg, sign_neg
-/
theorem oangle_sign_sub_right_swap (x y : V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_right_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

/-- Subtracting the second vector passed to `oangle` from the first vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
/--
theorem `oangle_sign_sub_left_swap` / 定理 `oangle_sign_sub_left_swap`

English:
theorem oangle_sign_sub_left_swap
  given: (x y : V)
  statement: (o.oangle (x - y) x).sign = (o.oangle x y).sign
  proof: by
  rw [oangle_sign_sub_left_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

中文:
定理 oangle_sign_sub_left_swap
  条件: (x y : V)
  结论: (o.oangle (x - y) x).sign = (o.oangle x y).sign
  证明: by
  rw [oangle_sign_sub_left_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

Depends on / 依赖: Real.Angle.sign_neg, o.oangle_rev, oangle_rev, oangle_sign_sub_left_eq_neg, sign_neg
-/
theorem oangle_sign_sub_left_swap (x y : V) : (o.oangle (x - y) x).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_left_eq_neg]; rw [o.oangle_rev y x]; rw [Real.Angle.sign_neg]

/--
theorem `oangle_sign_smul_add_smul_right` / 定理 `oangle_sign_smul_add_smul_right`

English:
theorem oangle_sign_smul_add_smul_right
  given: (x y : V) (r₁ r₂ : Real)
  proof: by
  simp

中文:
定理 oangle_sign_smul_add_smul_right
  条件: (x y : V) (r₁ r₂ : 实数)
  证明: by
  simp
-/
theorem oangle_sign_smul_add_smul_right (x y : V) (r₁ r₂ : Real) :
    (o.oangle x (r₁ • x + r₂ • y)).sign = SignType.sign r₂ * (o.oangle x y).sign := by
  simp

/--
theorem `oangle_sign_smul_add_smul_left` / 定理 `oangle_sign_smul_add_smul_left`

English:
theorem oangle_sign_smul_add_smul_left
  given: (x y : V) (r₁ r₂ : Real)
  proof: by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm (r₁ • x), oangle_sign_smul_add_smul_right,
    mul_neg]

中文:
定理 oangle_sign_smul_add_smul_left
  条件: (x y : V) (r₁ r₂ : 实数)
  证明: by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm (r₁ • x), oangle_sign_smul_add_smul_right,
    mul_neg]

Depends on / 依赖: Real.Angle.sign_neg, add_comm, mul_neg, o.oangle_rev, oangle_rev, oangle_sign_smul_add_smul_right, sign_neg, simp_rw
-/
theorem oangle_sign_smul_add_smul_left (x y : V) (r₁ r₂ : Real) :
    (o.oangle (r₁ • x + r₂ • y) y).sign = SignType.sign r₁ * (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm (r₁ • x), oangle_sign_smul_add_smul_right,
    mul_neg]

/--
theorem `oangle_sign_smul_add_smul_smul_add_smul` / 定理 `oangle_sign_smul_add_smul_smul_add_smul`

English:
theorem oangle_sign_smul_add_smul_smul_add_smul
  given: (x y : V) (r₁ r₂ r₃ r₄ : Real)
  proof: by
  by_cases hr₁ : r₁ = 0
  · rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, Left.sign_neg,
      oangle_sign_smul_left, add_comm, oangle_sign_smul_add_smul_right, oangle_rev,
      Real.Angle.sign_neg, sign_mul, mul_neg, mul_neg, neg_mul, mul_assoc]
  · rw [← o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁), smul_add,
      smul_smul, smul_smul, div_mul_cancel₀ _ hr₁, neg_smul, ← add_assoc, add_comm (-(r₃ • x)), ←
      sub_eq_add_neg, sub_add_cancel, ← add_smul, oangle_sign_smul_right,
      oangle_sign_smul_add_smul_left, ← mul_assoc, ← sign_mul, add_mul, mul_assoc, mul_comm r₂ r₁, ←
      mul_assoc, div_mul_cancel₀ _ hr₁, add_comm, neg_mul, ← sub_eq_add_neg, mul_comm r₄,
      mul_comm r₃]

中文:
定理 oangle_sign_smul_add_smul_smul_add_smul
  条件: (x y : V) (r₁ r₂ r₃ r₄ : 实数)
  证明: by
  by_cases hr₁ : r₁ = 0
  · rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, Left.sign_neg,
      oangle_sign_smul_left, add_comm, oangle_sign_smul_add_smul_right, oangle_rev,
      Real.Angle.sign_neg, sign_mul, mul_neg, mul_neg, neg_mul, mul_assoc]
  · rw [← o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁), smul_add,
      smul_smul, smul_smul, div_mul_cancel₀ _ hr₁, neg_smul, ← add_assoc, add_comm (-(r₃ • x)), ←
      sub_eq_add_neg, sub_add_cancel, ← add_smul, oangle_sign_smul_right,
      oangle_sign_smul_add_smul_left, ← mul_assoc, ← sign_mul, add_mul, mul_assoc, mul_comm r₂ r₁, ←
      mul_assoc, div_mul_cancel₀ _ hr₁, add_comm, neg_mul, ← sub_eq_add_neg, mul_comm r₄,
      mul_comm r₃]

Depends on / 依赖: Left.sign_neg, Real.Angle.sign_neg, add_assoc, add_comm, add_smul, mul_assoc, mul_neg, neg_mul, neg_smul, o.oangle_sign_smul_add_right, oangle, oangle_rev, oangle_sign_smul_add_right, oangle_sign_smul_add_smul_right, oangle_sign_smul_left, oangle_sign_smul_right, sign_mul, sign_neg, smul_add, smul_smul
-/
theorem oangle_sign_smul_add_smul_smul_add_smul (x y : V) (r₁ r₂ r₃ r₄ : Real) :
    (o.oangle (r₁ • x + r₂ • y) (r₃ • x + r₄ • y)).sign =
      SignType.sign (r₁ * r₄ - r₂ * r₃) * (o.oangle x y).sign := by
  by_cases hr₁ : r₁ = 0
  · rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, Left.sign_neg,
      oangle_sign_smul_left, add_comm, oangle_sign_smul_add_smul_right, oangle_rev,
      Real.Angle.sign_neg, sign_mul, mul_neg, mul_neg, neg_mul, mul_assoc]
  · rw [← o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁), smul_add,
      smul_smul, smul_smul, div_mul_cancel₀ _ hr₁, neg_smul, ← add_assoc, add_comm (-(r₃ • x)), ←
      sub_eq_add_neg, sub_add_cancel, ← add_smul, oangle_sign_smul_right,
      oangle_sign_smul_add_smul_left, ← mul_assoc, ← sign_mul, add_mul, mul_assoc, mul_comm r₂ r₁, ←
      mul_assoc, div_mul_cancel₀ _ hr₁, add_comm, neg_mul, ← sub_eq_add_neg, mul_comm r₄,
      mul_comm r₃]

/--
theorem `abs_oangle_sub_left_toReal_lt_pi_div_two` / 定理 `abs_oangle_sub_left_toReal_lt_pi_div_two`

English:
theorem abs_oangle_sub_left_toReal_lt_pi_div_two
  given: {x y : V} (h : ‖x‖ = ‖y‖)
  proof: by
  by_cases hn : x = y; · simp [hn, Real.pi_pos]
  have hs : ((2 : Int) • o.oangle (y - x) y).sign = (o.oangle (y - x) y).sign := by
    conv_rhs => rw [oangle_sign_sub_left_swap]
    rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h]; rw [Real.Angle.sign_pi_sub]
  rw [Real.Angle.sign_two_zsmul_eq_sign_iff] at hs
  rcases hs with (hs | hs)
  · rw [oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, neg_sub] at hs
    rcases hs with ⟨hy, -, hr⟩
    rw [← exists_nonneg_left_iff_sameRay hy] at hr
    rcases hr with ⟨r, hr0, hr⟩
    rw [eq_sub_iff_add_eq] at hr
    nth_rw 2 [← one_smul Real y] at hr
    rw [← add_smul] at hr
    rw [← hr]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (Left.add_pos_of_nonneg_of_pos hr0 one_pos)]; rw [mul_left_eq_self₀]; rw [or_iff_left (norm_ne_zero_iff.2 hy)]; rw [add_eq_right] at h
    rw [h]; rw [zero_add]; rw [one_smul] at hr
    exact False.elim (hn hr.symm)
  · exact hs

中文:
定理 abs_oangle_sub_left_to实数_lt_pi_div_two
  条件: {x y : V} (h : ‖x‖ = ‖y‖)
  证明: by
  by_cases hn : x = y; · simp [hn, Real.pi_pos]
  have hs : ((2 : Int) • o.oangle (y - x) y).sign = (o.oangle (y - x) y).sign := by
    conv_rhs => rw [oangle_sign_sub_left_swap]
    rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h]; rw [Real.Angle.sign_pi_sub]
  rw [Real.Angle.sign_two_zsmul_eq_sign_iff] at hs
  rcases hs with (hs | hs)
  · rw [oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, neg_sub] at hs
    rcases hs with ⟨hy, -, hr⟩
    rw [← exists_nonneg_left_iff_sameRay hy] at hr
    rcases hr with ⟨r, hr0, hr⟩
    rw [eq_sub_iff_add_eq] at hr
    nth_rw 2 [← one_smul Real y] at hr
    rw [← add_smul] at hr
    rw [← hr]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (Left.add_pos_of_nonneg_of_pos hr0 one_pos)]; rw [mul_left_eq_self₀]; rw [or_iff_left (norm_ne_zero_iff.2 hy)]; rw [add_eq_right] at h
    rw [h]; rw [zero_add]; rw [one_smul] at hr
    exact False.elim (hn hr.symm)
  · exact hs

Depends on / 依赖: Real.Angle.sign_pi_sub, Real.Angle.sign_two_zsmul_eq_sign_iff, Real.pi_pos, conv_rhs, exists_nonneg_left_iff_sameRay, neg_sub, o.oangle, o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, oangle, oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, oangle_sign_sub_left_swap, pi_pos, sign_pi_sub, sign_two_zsmul_eq_sign_iff
-/
theorem abs_oangle_sub_left_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle (y - x) y).toReal| < π / 2 := by
  by_cases hn : x = y; · simp [hn, Real.pi_pos]
  have hs : ((2 : Int) • o.oangle (y - x) y).sign = (o.oangle (y - x) y).sign := by
    conv_rhs => rw [oangle_sign_sub_left_swap]
    rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h]; rw [Real.Angle.sign_pi_sub]
  rw [Real.Angle.sign_two_zsmul_eq_sign_iff] at hs
  rcases hs with (hs | hs)
  · rw [oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, neg_sub] at hs
    rcases hs with ⟨hy, -, hr⟩
    rw [← exists_nonneg_left_iff_sameRay hy] at hr
    rcases hr with ⟨r, hr0, hr⟩
    rw [eq_sub_iff_add_eq] at hr
    nth_rw 2 [← one_smul Real y] at hr
    rw [← add_smul] at hr
    rw [← hr]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (Left.add_pos_of_nonneg_of_pos hr0 one_pos)]; rw [mul_left_eq_self₀]; rw [or_iff_left (norm_ne_zero_iff.2 hy)]; rw [add_eq_right] at h
    rw [h]; rw [zero_add]; rw [one_smul] at hr
    exact False.elim (hn hr.symm)
  · exact hs

/--
theorem `abs_oangle_sub_right_toReal_lt_pi_div_two` / 定理 `abs_oangle_sub_right_toReal_lt_pi_div_two`

English:
theorem abs_oangle_sub_right_toReal_lt_pi_div_two
  given: {x y : V} (h : ‖x‖ = ‖y‖)
  proof: (o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h).symm ▸ o.abs_oangle_sub_left_toReal_lt_pi_div_two h

中文:
定理 abs_oangle_sub_right_to实数_lt_pi_div_two
  条件: {x y : V} (h : ‖x‖ = ‖y‖)
  证明: (o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h).symm ▸ o.abs_oangle_sub_left_toReal_lt_pi_div_two h

Depends on / 依赖: abs_oangle_sub_left_toReal_lt_pi_div_two, o.abs_oangle_sub_left_toReal_lt_pi_div_two, o.oangle_sub_eq_oangle_sub_rev_of_norm_eq, oangle_sub_eq_oangle_sub_rev_of_norm_eq
-/
theorem abs_oangle_sub_right_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle x (x - y)).toReal| < π / 2 :=
  (o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h).symm ▸ o.abs_oangle_sub_left_toReal_lt_pi_div_two h

/--
lemma `angle_eq_iff_oangle_eq_or_sameRay` / 引理 `angle_eq_iff_oangle_eq_or_sameRay`

English:
lemma angle_eq_iff_oangle_eq_or_sameRay
  given: {x y z : V} (hx : x != 0) (hz : z != 0)
  proof: by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hr : SameRay Real x z
  · obtain ⟨r, hrp, rfl⟩ := hr.exists_pos_left hx hz
    simp [hr, hrp, InnerProductGeometry.angle_comm]
  simp only [hr, or_false]
  by_cases hs : (o.oangle x y).sign = (o.oangle y z).sign
  · rw [o.angle_eq_iff_oangle_eq_of_sign_eq hx hy hy hz hs]
  · have hn : o.oangle x y != o.oangle y z := by grind
    simp only [hn, iff_false]
    intro he
    apply hr
    by_cases hs' : (o.oangle x y).sign = -(o.oangle y z).sign
    · rw [o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg hx hy hy hz hs'] at he
      rw [← o.oangle_eq_zero_iff_sameRay]; rw [← o.oangle_add hx hy hz]
      simp [he]
    · have h0 : (o.oangle x y).sign = 0 ∨ (o.oangle y z).sign = 0 := by
        revert hs hs'
        generalize (o.oangle x y).sign = sxy
        generalize (o.oangle y z).sign = syz
        decide +revert
      have h0' : InnerProductGeometry.angle y z = 0 ∨ InnerProductGeometry.angle y z = π := by
        rcases h0 with h0 | h0
          <;> simpa [*] using o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0
      rcases h0' with h0' | h0'
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 he
        simp_all
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 he
        simp_all

中文:
引理 angle_eq_iff_oangle_eq_or_sameRay
  条件: {x y z : V} (hx : x != 0) (hz : z != 0)
  证明: by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hr : SameRay Real x z
  · obtain ⟨r, hrp, rfl⟩ := hr.exists_pos_left hx hz
    simp [hr, hrp, InnerProductGeometry.angle_comm]
  simp only [hr, or_false]
  by_cases hs : (o.oangle x y).sign = (o.oangle y z).sign
  · rw [o.angle_eq_iff_oangle_eq_of_sign_eq hx hy hy hz hs]
  · have hn : o.oangle x y != o.oangle y z := by grind
    simp only [hn, iff_false]
    intro he
    apply hr
    by_cases hs' : (o.oangle x y).sign = -(o.oangle y z).sign
    · rw [o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg hx hy hy hz hs'] at he
      rw [← o.oangle_eq_zero_iff_sameRay]; rw [← o.oangle_add hx hy hz]
      simp [he]
    · have h0 : (o.oangle x y).sign = 0 ∨ (o.oangle y z).sign = 0 := by
        revert hs hs'
        generalize (o.oangle x y).sign = sxy
        generalize (o.oangle y z).sign = syz
        decide +revert
      have h0' : InnerProductGeometry.angle y z = 0 ∨ InnerProductGeometry.angle y z = π := by
        rcases h0 with h0 | h0
          <;> simpa [*] using o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0
      rcases h0' with h0' | h0'
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 he
        simp_all
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 he
        simp_all

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.angle_comm, SameRay, angle_comm, angle_eq_iff_oangle_eq_neg_of_sig, angle_eq_iff_oangle_eq_of_sign_eq, exists_pos_left, hr.exists_pos_left, iff_false, o.angle_eq_iff_oangle_eq_neg_of_sig, o.angle_eq_iff_oangle_eq_of_sign_eq, o.oangle, oangle, or_false
-/
lemma angle_eq_iff_oangle_eq_or_sameRay {x y z : V} (hx : x != 0) (hz : z != 0) :
    InnerProductGeometry.angle x y = InnerProductGeometry.angle y z ↔
      o.oangle x y = o.oangle y z ∨ SameRay Real x z := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hr : SameRay Real x z
  · obtain ⟨r, hrp, rfl⟩ := hr.exists_pos_left hx hz
    simp [hr, hrp, InnerProductGeometry.angle_comm]
  simp only [hr, or_false]
  by_cases hs : (o.oangle x y).sign = (o.oangle y z).sign
  · rw [o.angle_eq_iff_oangle_eq_of_sign_eq hx hy hy hz hs]
  · have hn : o.oangle x y != o.oangle y z := by grind
    simp only [hn, iff_false]
    intro he
    apply hr
    by_cases hs' : (o.oangle x y).sign = -(o.oangle y z).sign
    · rw [o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg hx hy hy hz hs'] at he
      rw [← o.oangle_eq_zero_iff_sameRay]; rw [← o.oangle_add hx hy hz]
      simp [he]
    · have h0 : (o.oangle x y).sign = 0 ∨ (o.oangle y z).sign = 0 := by
        revert hs hs'
        generalize (o.oangle x y).sign = sxy
        generalize (o.oangle y z).sign = syz
        decide +revert
      have h0' : InnerProductGeometry.angle y z = 0 ∨ InnerProductGeometry.angle y z = π := by
        rcases h0 with h0 | h0
          <;> simpa [*] using o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0
      rcases h0' with h0' | h0'
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 he
        simp_all
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 he
        simp_all

end Orientation
