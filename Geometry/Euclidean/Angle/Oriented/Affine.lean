/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Oriented angles.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/

@[expose] public section


noncomputable section

open Module Complex

open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank Real V = 2)] [Module.Oriented Real V (Fin 2)]

/--
Definition of `o` / `o` 的定义

English:
abbreviation o
  body: @Module.Oriented.positiveOrientation

中文:
缩写 o
  定义体: @Module.Oriented.positiveOrientation

Depends on / 依赖: Module, Module.Oriented.positiveOrientation, Oriented, positiveOrientation
-/
abbrev o := @Module.Oriented.positiveOrientation

/--
Definition of `oangle` / `oangle` 的定义

English:
definition oangle
  signature: (p₁ p₂ p₃ : P)
  body: o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∡" => EuclideanGeometry.oangle

中文:
定义 oangle
  签名: (p₁ p₂ p₃ : P)
  定义体: o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∡" => EuclideanGeometry.oangle

Depends on / 依赖: o.oangle, oangle
-/
def oangle (p₁ p₂ p₃ : P) : Real.Angle :=
  o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

@[inherit_doc] scoped notation "∡" => EuclideanGeometry.oangle

/--
theorem `continuousAt_oangle` / 定理 `continuousAt_oangle`

English:
theorem continuousAt_oangle
  given: {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1)
  proof: by
  unfold oangle
  fun_prop (disch := simp [*])

中文:
定理 continuousAt_oangle
  条件: {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1)
  证明: by
  unfold oangle
  fun_prop (disch := simp [*])

Depends on / 依赖: fun_prop, oangle
-/
theorem continuousAt_oangle {x : P × P × P} (hx12 : x.1 != x.2.1) (hx32 : x.2.2 != x.2.1) :
    ContinuousAt (fun y : P × P × P => ∡ y.1 y.2.1 y.2.2) x := by
  unfold oangle
  fun_prop (disch := simp [*])

/-- The angle ∡AAB at a point. -/
@[simp]
/--
theorem `oangle_self_left` / 定理 `oangle_self_left`

English:
theorem oangle_self_left
  given: (p₁ p₂ : P)
  statement: ∡ p₁ p₁ p₂ = 0
  proof: by simp [oangle]

中文:
定理 oangle_self_left
  条件: (p₁ p₂ : P)
  结论: ∡ p₁ p₁ p₂ = 0
  证明: by simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 := by simp [oangle]

/-- The angle ∡ABB at a point. -/
@[simp]
/--
theorem `oangle_self_right` / 定理 `oangle_self_right`

English:
theorem oangle_self_right
  given: (p₁ p₂ : P)
  statement: ∡ p₁ p₂ p₂ = 0
  proof: by simp [oangle]

中文:
定理 oangle_self_right
  条件: (p₁ p₂ : P)
  结论: ∡ p₁ p₂ p₂ = 0
  证明: by simp [oangle]

Depends on / 依赖: oangle
-/
theorem oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 := by simp [oangle]

/-- The angle ∡ABA at a point. -/
@[simp]
/--
theorem `oangle_self_left_right` / 定理 `oangle_self_left_right`

English:
theorem oangle_self_left_right
  given: (p₁ p₂ : P)
  statement: ∡ p₁ p₂ p₁ = 0
  proof: o.oangle_self _

中文:
定理 oangle_self_left_right
  条件: (p₁ p₂ : P)
  结论: ∡ p₁ p₂ p₁ = 0
  证明: o.oangle_self _

Depends on / 依赖: o.oangle_self, oangle_self
-/
theorem oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0 :=
  o.oangle_self _

/--
theorem `left_ne_of_oangle_ne_zero` / 定理 `left_ne_of_oangle_ne_zero`

English:
theorem left_ne_of_oangle_ne_zero
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  statement: p₁ != p₂
  proof: by
  rw [← @vsub_ne_zero V]; exact o.left_ne_zero_of_oangle_ne_zero h

中文:
定理 left_ne_of_oangle_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  结论: p₁ != p₂
  证明: by
  rw [← @vsub_ne_zero V]; exact o.left_ne_zero_of_oangle_ne_zero h

Depends on / 依赖: left_ne_zero_of_oangle_ne_zero, o.left_ne_zero_of_oangle_ne_zero, vsub_ne_zero
-/
theorem left_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₂ := by
  rw [← @vsub_ne_zero V]; exact o.left_ne_zero_of_oangle_ne_zero h

/--
theorem `right_ne_of_oangle_ne_zero` / 定理 `right_ne_of_oangle_ne_zero`

English:
theorem right_ne_of_oangle_ne_zero
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  statement: p₃ != p₂
  proof: by
  rw [← @vsub_ne_zero V]; exact o.right_ne_zero_of_oangle_ne_zero h

中文:
定理 right_ne_of_oangle_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  结论: p₃ != p₂
  证明: by
  rw [← @vsub_ne_zero V]; exact o.right_ne_zero_of_oangle_ne_zero h

Depends on / 依赖: o.right_ne_zero_of_oangle_ne_zero, right_ne_zero_of_oangle_ne_zero, vsub_ne_zero
-/
theorem right_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₃ != p₂ := by
  rw [← @vsub_ne_zero V]; exact o.right_ne_zero_of_oangle_ne_zero h

/--
theorem `left_ne_right_of_oangle_ne_zero` / 定理 `left_ne_right_of_oangle_ne_zero`

English:
theorem left_ne_right_of_oangle_ne_zero
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  statement: p₁ != p₃
  proof: by
  rw [← (vsub_left_injective p₂).ne_iff]; exact o.ne_of_oangle_ne_zero h

中文:
定理 left_ne_right_of_oangle_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0)
  结论: p₁ != p₃
  证明: by
  rw [← (vsub_left_injective p₂).ne_iff]; exact o.ne_of_oangle_ne_zero h

Depends on / 依赖: ne_iff, ne_of_oangle_ne_zero, o.ne_of_oangle_ne_zero, vsub_left_injective
-/
theorem left_ne_right_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ != 0) : p₁ != p₃ := by
  rw [← (vsub_left_injective p₂).ne_iff]; exact o.ne_of_oangle_ne_zero h

/--
theorem `left_ne_of_oangle_eq_pi` / 定理 `left_ne_of_oangle_eq_pi`

English:
theorem left_ne_of_oangle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  statement: p₁ != p₂
  proof: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_of_oangle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  结论: p₁ != p₂
  证明: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, left_ne_of_oangle_ne_zero, pi_ne_zero
-/
theorem left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ != p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `right_ne_of_oangle_eq_pi` / 定理 `right_ne_of_oangle_eq_pi`

English:
theorem right_ne_of_oangle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  statement: p₃ != p₂
  proof: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 right_ne_of_oangle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  结论: p₃ != p₂
  证明: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, pi_ne_zero, right_ne_of_oangle_ne_zero
-/
theorem right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ != p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_right_of_oangle_eq_pi` / 定理 `left_ne_right_of_oangle_eq_pi`

English:
theorem left_ne_right_of_oangle_eq_pi
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  statement: p₁ != p₃
  proof: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_right_of_oangle_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π)
  结论: p₁ != p₃
  证明: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_ne_zero, h.symm, left_ne_right_of_oangle_ne_zero, pi_ne_zero
-/
theorem left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ != p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_of_oangle_eq_pi_div_two` / 定理 `left_ne_of_oangle_eq_pi_div_two`

English:
theorem left_ne_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real))
  statement: p₁ != p₂
  proof: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : 实数))
  结论: p₁ != p₂
  证明: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, left_ne_of_oangle_ne_zero, pi_div_two_ne_zero
-/
theorem left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `right_ne_of_oangle_eq_pi_div_two` / 定理 `right_ne_of_oangle_eq_pi_div_two`

English:
theorem right_ne_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real))
  statement: p₃ != p₂
  proof: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 right_ne_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : 实数))
  结论: p₃ != p₂
  证明: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, pi_div_two_ne_zero, right_ne_of_oangle_ne_zero
-/
theorem right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_right_of_oangle_eq_pi_div_two` / 定理 `left_ne_right_of_oangle_eq_pi_div_two`

English:
theorem left_ne_right_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real))
  proof: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_right_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : 实数))
  证明: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.pi_div_two_ne_zero, h.symm, left_ne_right_of_oangle_ne_zero, pi_div_two_ne_zero
-/
theorem left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) :
    p₁ != p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_of_oangle_eq_neg_pi_div_two` / 定理 `left_ne_of_oangle_eq_neg_pi_div_two`

English:
theorem left_ne_of_oangle_eq_neg_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real))
  proof: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_of_oangle_eq_neg_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : 实数))
  证明: left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, left_ne_of_oangle_ne_zero, neg_pi_div_two_ne_zero
-/
theorem left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)) :
    p₁ != p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `right_ne_of_oangle_eq_neg_pi_div_two` / 定理 `right_ne_of_oangle_eq_neg_pi_div_two`

English:
theorem right_ne_of_oangle_eq_neg_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real))
  proof: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 right_ne_of_oangle_eq_neg_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : 实数))
  证明: right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, neg_pi_div_two_ne_zero, right_ne_of_oangle_ne_zero
-/
theorem right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)) :
    p₃ != p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_right_of_oangle_eq_neg_pi_div_two` / 定理 `left_ne_right_of_oangle_eq_neg_pi_div_two`

English:
theorem left_ne_right_of_oangle_eq_neg_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real))
  proof: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

中文:
定理 left_ne_right_of_oangle_eq_neg_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : 实数))
  证明: left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

Depends on / 依赖: Real.Angle.neg_pi_div_two_ne_zero, h.symm, left_ne_right_of_oangle_ne_zero, neg_pi_div_two_ne_zero
-/
theorem left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : Real)) :
    p₁ != p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ != 0)

/--
theorem `left_ne_of_oangle_sign_ne_zero` / 定理 `left_ne_of_oangle_sign_ne_zero`

English:
theorem left_ne_of_oangle_sign_ne_zero
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  statement: p₁ != p₂
  proof: left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 left_ne_of_oangle_sign_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  结论: p₁ != p₂
  证明: left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, left_ne_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₂ :=
  left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `right_ne_of_oangle_sign_ne_zero` / 定理 `right_ne_of_oangle_sign_ne_zero`

English:
theorem right_ne_of_oangle_sign_ne_zero
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  statement: p₃ != p₂
  proof: right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 right_ne_of_oangle_sign_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  结论: p₃ != p₂
  证明: right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, right_ne_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₃ != p₂ :=
  right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `left_ne_right_of_oangle_sign_ne_zero` / 定理 `left_ne_right_of_oangle_sign_ne_zero`

English:
theorem left_ne_right_of_oangle_sign_ne_zero
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  statement: p₁ != p₃
  proof: left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

中文:
定理 left_ne_right_of_oangle_sign_ne_zero
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0)
  结论: p₁ != p₃
  证明: left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

Depends on / 依赖: Real.Angle.sign_ne_zero_iff, left_ne_right_of_oangle_ne_zero, sign_ne_zero_iff
-/
theorem left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign != 0) : p₁ != p₃ :=
  left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/--
theorem `left_ne_of_oangle_sign_eq_one` / 定理 `left_ne_of_oangle_sign_eq_one`

English:
theorem left_ne_of_oangle_sign_eq_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  statement: p₁ != p₂
  proof: left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 left_ne_of_oangle_sign_eq_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  结论: p₁ != p₂
  证明: left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, left_ne_of_oangle_sign_ne_zero
-/
theorem left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ != p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `right_ne_of_oangle_sign_eq_one` / 定理 `right_ne_of_oangle_sign_eq_one`

English:
theorem right_ne_of_oangle_sign_eq_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  statement: p₃ != p₂
  proof: right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 right_ne_of_oangle_sign_eq_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  结论: p₃ != p₂
  证明: right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, right_ne_of_oangle_sign_ne_zero
-/
theorem right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₃ != p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `left_ne_right_of_oangle_sign_eq_one` / 定理 `left_ne_right_of_oangle_sign_eq_one`

English:
theorem left_ne_right_of_oangle_sign_eq_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  statement: p₁ != p₃
  proof: left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 left_ne_right_of_oangle_sign_eq_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  结论: p₁ != p₃
  证明: left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, left_ne_right_of_oangle_sign_ne_zero
-/
theorem left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ != p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `left_ne_of_oangle_sign_eq_neg_one` / 定理 `left_ne_of_oangle_sign_eq_neg_one`

English:
theorem left_ne_of_oangle_sign_eq_neg_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  statement: p₁ != p₂
  proof: left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 left_ne_of_oangle_sign_eq_neg_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  结论: p₁ != p₂
  证明: left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, left_ne_of_oangle_sign_ne_zero
-/
theorem left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₁ != p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `right_ne_of_oangle_sign_eq_neg_one` / 定理 `right_ne_of_oangle_sign_eq_neg_one`

English:
theorem right_ne_of_oangle_sign_eq_neg_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  statement: p₃ != p₂
  proof: right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 right_ne_of_oangle_sign_eq_neg_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  结论: p₃ != p₂
  证明: right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, right_ne_of_oangle_sign_ne_zero
-/
theorem right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₃ != p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `left_ne_right_of_oangle_sign_eq_neg_one` / 定理 `left_ne_right_of_oangle_sign_eq_neg_one`

English:
theorem left_ne_right_of_oangle_sign_eq_neg_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  proof: left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

中文:
定理 left_ne_right_of_oangle_sign_eq_neg_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  证明: left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

Depends on / 依赖: h.symm, left_ne_right_of_oangle_sign_ne_zero
-/
theorem left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    p₁ != p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign != 0)

/--
theorem `oangle_rev` / 定理 `oangle_rev`

English:
theorem oangle_rev
  given: (p₁ p₂ p₃ : P)
  statement: ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃
  proof: o.oangle_rev _ _

中文:
定理 oangle_rev
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃
  证明: o.oangle_rev _ _

Depends on / 依赖: o.oangle_rev, oangle_rev
-/
theorem oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃ :=
  o.oangle_rev _ _

/-- Adding an angle to that with the order of the points reversed results in 0. -/
@[simp]
/--
theorem `oangle_add_oangle_rev` / 定理 `oangle_add_oangle_rev`

English:
theorem oangle_add_oangle_rev
  given: (p₁ p₂ p₃ : P)
  statement: ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0
  proof: o.oangle_add_oangle_rev _ _

中文:
定理 oangle_add_oangle_rev
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0
  证明: o.oangle_add_oangle_rev _ _

Depends on / 依赖: o.oangle_add_oangle_rev, oangle_add_oangle_rev
-/
theorem oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_add_oangle_rev _ _

/--
theorem `oangle_eq_zero_iff_oangle_rev_eq_zero` / 定理 `oangle_eq_zero_iff_oangle_rev_eq_zero`

English:
theorem oangle_eq_zero_iff_oangle_rev_eq_zero
  given: {p₁ p₂ p₃ : P}
  statement: ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0
  proof: o.oangle_eq_zero_iff_oangle_rev_eq_zero

中文:
定理 oangle_eq_zero_iff_oangle_rev_eq_zero
  条件: {p₁ p₂ p₃ : P}
  结论: ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0
  证明: o.oangle_eq_zero_iff_oangle_rev_eq_zero

Depends on / 依赖: o.oangle_eq_zero_iff_oangle_rev_eq_zero, oangle_eq_zero_iff_oangle_rev_eq_zero
-/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0 :=
  o.oangle_eq_zero_iff_oangle_rev_eq_zero

/--
theorem `oangle_eq_pi_iff_oangle_rev_eq_pi` / 定理 `oangle_eq_pi_iff_oangle_rev_eq_pi`

English:
theorem oangle_eq_pi_iff_oangle_rev_eq_pi
  given: {p₁ p₂ p₃ : P}
  statement: ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π
  proof: o.oangle_eq_pi_iff_oangle_rev_eq_pi

中文:
定理 oangle_eq_pi_iff_oangle_rev_eq_pi
  条件: {p₁ p₂ p₃ : P}
  结论: ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π
  证明: o.oangle_eq_pi_iff_oangle_rev_eq_pi

Depends on / 依赖: o.oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_oangle_rev_eq_pi
-/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π :=
  o.oangle_eq_pi_iff_oangle_rev_eq_pi

/--
lemma `oangle_homothety` / 引理 `oangle_homothety`

English:
lemma oangle_homothety
  given: (p p₁ p₂ p₃ : P) {r : Real} (h : r != 0)
  proof: by
  simp_rw [oangle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

中文:
引理 oangle_homothety
  条件: (p p₁ p₂ p₃ : P) {r : 实数} (h : r != 0)
  证明: by
  simp_rw [oangle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]
-/
@[simp] lemma oangle_homothety (p p₁ p₂ p₃ : P) {r : Real} (h : r != 0) :
    ∡ (AffineMap.homothety p r p₁) (AffineMap.homothety p r p₂) (AffineMap.homothety p r p₃) =
      ∡ p₁ p₂ p₃ := by
  simp_rw [oangle, ← AffineMap.linearMap_vsub, AffineMap.homothety_linear, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rcases h.lt_or_gt with hlt | hlt <;> simp [hlt, -neg_vsub_eq_vsub_rev]

/--
theorem `oangle_ne_zero_and_ne_pi_iff_affineIndependent` / 定理 `oangle_ne_zero_and_ne_pi_iff_affineIndependent`

English:
theorem oangle_ne_zero_and_ne_pi_iff_affineIndependent
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [oangle]; rw [o.oangle_ne_zero_and_ne_pi_iff_linearIndependent]; rw [affineIndependent_iff_linearIndependent_vsub Real _ (1 : Fin 3)]; rw [←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert! Iff.rfl
  ext i
  fin_cases i <;> rfl

中文:
定理 oangle_ne_zero_and_ne_pi_iff_affineIndependent
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [oangle]; rw [o.oangle_ne_zero_and_ne_pi_iff_linearIndependent]; rw [affineIndependent_iff_linearIndependent_vsub Real _ (1 : Fin 3)]; rw [←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert! Iff.rfl
  ext i
  fin_cases i <;> rfl

Depends on / 依赖: Iff.rfl, affineIndependent_iff_linearIndependent_vsub, convert, finSuccAboveEquiv, fin_cases, linearIndependent_equiv, o.oangle_ne_zero_and_ne_pi_iff_linearIndependent, oangle, oangle_ne_zero_and_ne_pi_iff_linearIndependent
-/
theorem oangle_ne_zero_and_ne_pi_iff_affineIndependent {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ != 0 ∧ ∡ p₁ p₂ p₃ != π ↔ AffineIndependent Real ![p₁, p₂, p₃] := by
  rw [oangle]; rw [o.oangle_ne_zero_and_ne_pi_iff_linearIndependent]; rw [affineIndependent_iff_linearIndependent_vsub Real _ (1 : Fin 3)]; rw [←
    linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))]
  convert! Iff.rfl
  ext i
  fin_cases i <;> rfl

/--
theorem `oangle_eq_zero_or_eq_pi_iff_collinear` / 定理 `oangle_eq_zero_or_eq_pi_iff_collinear`

English:
theorem oangle_eq_zero_or_eq_pi_iff_collinear
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [← not_iff_not]; rw [not_or]; rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

中文:
定理 oangle_eq_zero_or_eq_pi_iff_collinear
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [← not_iff_not]; rw [not_or]; rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

Depends on / 依赖: affineIndependent_iff_not_collinear_set, not_iff_not, not_or, oangle_ne_zero_and_ne_pi_iff_affineIndependent
-/
theorem oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collinear Real ({p₁, p₂, p₃} : Set P) := by
  rw [← not_iff_not]; rw [not_or]; rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

/--
theorem `oangle_sign_eq_zero_iff_collinear` / 定理 `oangle_sign_eq_zero_iff_collinear`

English:
theorem oangle_sign_eq_zero_iff_collinear
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [Real.Angle.sign_eq_zero_iff]; rw [oangle_eq_zero_or_eq_pi_iff_collinear]

中文:
定理 oangle_sign_eq_zero_iff_collinear
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [Real.Angle.sign_eq_zero_iff]; rw [oangle_eq_zero_or_eq_pi_iff_collinear]

Depends on / 依赖: Real.Angle.sign_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear, sign_eq_zero_iff
-/
theorem oangle_sign_eq_zero_iff_collinear {p₁ p₂ p₃ : P} :
    (∡ p₁ p₂ p₃).sign = 0 ↔ Collinear Real ({p₁, p₂, p₃} : Set P) := by
  rw [Real.Angle.sign_eq_zero_iff]; rw [oangle_eq_zero_or_eq_pi_iff_collinear]

/--
theorem `oangle_ne_zero_and_ne_pi_iff_not_collinear` / 定理 `oangle_ne_zero_and_ne_pi_iff_not_collinear`

English:
theorem oangle_ne_zero_and_ne_pi_iff_not_collinear
  given: {p₁ p₂ p₃ : P}
  proof: by
  rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

中文:
定理 oangle_ne_zero_and_ne_pi_iff_not_collinear
  条件: {p₁ p₂ p₃ : P}
  证明: by
  rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

Depends on / 依赖: affineIndependent_iff_not_collinear_set, oangle_ne_zero_and_ne_pi_iff_affineIndependent
-/
theorem oangle_ne_zero_and_ne_pi_iff_not_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ != 0 ∧ ∡ p₁ p₂ p₃ != π ↔ ¬ Collinear Real {p₁, p₂, p₃} := by
  rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]; rw [affineIndependent_iff_not_collinear_set]

/--
theorem `affineIndependent_iff_of_two_zsmul_oangle_eq` / 定理 `affineIndependent_iff_of_two_zsmul_oangle_eq`

English:
theorem affineIndependent_iff_of_two_zsmul_oangle_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.two_zsmul_ne_zero_iff, h]

中文:
定理 affineIndependent_iff_of_two_zsmul_oangle_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.two_zsmul_ne_zero_iff, h]

Depends on / 依赖: Real.Angle.two_zsmul_ne_zero_iff, oangle_ne_zero_and_ne_pi_iff_affineIndependent, simp_rw, two_zsmul_ne_zero_iff
-/
theorem affineIndependent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆) :
    AffineIndependent Real ![p₁, p₂, p₃] ↔ AffineIndependent Real ![p₄, p₅, p₆] := by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.two_zsmul_ne_zero_iff, h]

/--
theorem `collinear_iff_of_two_zsmul_oangle_eq` / 定理 `collinear_iff_of_two_zsmul_oangle_eq`

English:
theorem collinear_iff_of_two_zsmul_oangle_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]

中文:
定理 collinear_iff_of_two_zsmul_oangle_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]

Depends on / 依赖: Real.Angle.two_zsmul_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear, simp_rw, two_zsmul_eq_zero_iff
-/
theorem collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆) :
    Collinear Real ({p₁, p₂, p₃} : Set P) ↔ Collinear Real ({p₄, p₅, p₆} : Set P) := by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]

/--
theorem `two_zsmul_oangle_of_vectorSpan_eq` / 定理 `two_zsmul_oangle_of_vectorSpan_eq`

English:
theorem two_zsmul_oangle_of_vectorSpan_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  simp_rw [vectorSpan_pair] at h₁₂₄₅ h₃₂₆₅
  exact o.two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅

中文:
定理 two_zsmul_oangle_of_vectorSpan_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  simp_rw [vectorSpan_pair] at h₁₂₄₅ h₃₂₆₅
  exact o.two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅

Depends on / 依赖: o.two_zsmul_oangle_of_span_eq_of_span_eq, simp_rw, two_zsmul_oangle_of_span_eq_of_span_eq, vectorSpan_pair
-/
theorem two_zsmul_oangle_of_vectorSpan_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : vectorSpan Real ({p₁, p₂} : Set P) = vectorSpan Real ({p₄, p₅} : Set P))
    (h₃₂₆₅ : vectorSpan Real ({p₃, p₂} : Set P) = vectorSpan Real ({p₆, p₅} : Set P)) :
    (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆ := by
  simp_rw [vectorSpan_pair] at h₁₂₄₅ h₃₂₆₅
  exact o.two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅

/--
theorem `two_zsmul_oangle_of_parallel` / 定理 `two_zsmul_oangle_of_parallel`

English:
theorem two_zsmul_oangle_of_parallel
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq] at h₁₂₄₅ h₃₂₆₅
  exact two_zsmul_oangle_of_vectorSpan_eq h₁₂₄₅ h₃₂₆₅

中文:
定理 two_zsmul_oangle_of_parallel
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq] at h₁₂₄₅ h₃₂₆₅
  exact two_zsmul_oangle_of_vectorSpan_eq h₁₂₄₅ h₃₂₆₅

Depends on / 依赖: AffineSubspace, AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, affineSpan_pair_parallel_iff_vectorSpan_eq, two_zsmul_oangle_of_vectorSpan_eq
-/
theorem two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : line[Real, p₁, p₂] ∥ line[Real, p₄, p₅]) (h₃₂₆₅ : line[Real, p₃, p₂] ∥ line[Real, p₆, p₅]) :
    (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₄ p₅ p₆ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq] at h₁₂₄₅ h₃₂₆₅
  exact two_zsmul_oangle_of_vectorSpan_eq h₁₂₄₅ h₃₂₆₅

/--
theorem `oangle_eq_of_parallel` / 定理 `oangle_eq_of_parallel`

English:
theorem oangle_eq_of_parallel
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[Real, p₁, p₃])
  proof: by
  rw [oangle]; rw [oangle]
  have hd : line[Real, p₆, p₄].direction <= line[Real, p₃, p₁].direction := by
    rw [Set.pair_comm p₃]
    exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem h₆ h₄)
  obtain ⟨r, hr, h₅₄, h₆₅, -⟩ := exists_eq_smul_of_parallel h₂ h₁₂₄₅
    (Set.pair_comm p₃ p₂ ▸ Set.pair_comm p₆ p₅ ▸ h₃₂₆₅).direction_eq.symm.le hd
  rw [← neg_inj]; rw [neg_vsub_eq_vsub_rev]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev] at h₅₄
  rw [h₅₄]; rw [h₆₅]
  rcases hr.lt_or_gt with hlt | hlt
  · simp [-neg_vsub_eq_vsub_rev, hlt]
  · simp [hlt]

中文:
定理 oangle_eq_of_parallel
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[实数, p₁, p₃])
  证明: by
  rw [oangle]; rw [oangle]
  have hd : line[Real, p₆, p₄].direction <= line[Real, p₃, p₁].direction := by
    rw [Set.pair_comm p₃]
    exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem h₆ h₄)
  obtain ⟨r, hr, h₅₄, h₆₅, -⟩ := exists_eq_smul_of_parallel h₂ h₁₂₄₅
    (Set.pair_comm p₃ p₂ ▸ Set.pair_comm p₆ p₅ ▸ h₃₂₆₅).direction_eq.symm.le hd
  rw [← neg_inj]; rw [neg_vsub_eq_vsub_rev]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev] at h₅₄
  rw [h₅₄]; rw [h₆₅]
  rcases hr.lt_or_gt with hlt | hlt
  · simp [-neg_vsub_eq_vsub_rev, hlt]
  · simp [hlt]

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_le, Set.pair_comm, affineSpan_pair_le_of_mem_of_mem, direction, direction_eq, direction_eq.symm.le, direction_le, exists_eq_smul_of_parallel, hr.lt_or_gt, lt_or_gt, neg_inj, neg_vsub_eq_vsub_rev, oangle, pair_comm, smul_neg
-/
theorem oangle_eq_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[Real, p₁, p₃])
    (h₄ : p₄ in line[Real, p₁, p₃]) (h₆ : p₆ in line[Real, p₁, p₃])
    (h₁₂₄₅ : line[Real, p₁, p₂] ∥ line[Real, p₄, p₅]) (h₃₂₆₅ : line[Real, p₃, p₂] ∥ line[Real, p₆, p₅]) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ := by
  rw [oangle]; rw [oangle]
  have hd : line[Real, p₆, p₄].direction <= line[Real, p₃, p₁].direction := by
    rw [Set.pair_comm p₃]
    exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem h₆ h₄)
  obtain ⟨r, hr, h₅₄, h₆₅, -⟩ := exists_eq_smul_of_parallel h₂ h₁₂₄₅
    (Set.pair_comm p₃ p₂ ▸ Set.pair_comm p₆ p₅ ▸ h₃₂₆₅).direction_eq.symm.le hd
  rw [← neg_inj]; rw [neg_vsub_eq_vsub_rev]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev] at h₅₄
  rw [h₅₄]; rw [h₆₅]
  rcases hr.lt_or_gt with hlt | hlt
  · simp [-neg_vsub_eq_vsub_rev, hlt]
  · simp [hlt]

/-- Given three points not equal to `p`, the angle between the first and the second at `p` plus
the angle between the second and the third equals the angle between the first and the third. -/
@[simp]
/--
theorem `oangle_add` / 定理 `oangle_add`

English:
theorem oangle_add
  given: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  proof: o.oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

中文:
定理 oangle_add
  条件: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  证明: o.oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

Depends on / 依赖: o.oangle_add, oangle_add, vsub_ne_zero
-/
theorem oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ :=
  o.oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the second and the third at `p` plus
the angle between the first and the second equals the angle between the first and the third. -/
@[simp]
/--
theorem `oangle_add_swap` / 定理 `oangle_add_swap`

English:
theorem oangle_add_swap
  given: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  proof: o.oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

中文:
定理 oangle_add_swap
  条件: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  证明: o.oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

Depends on / 依赖: o.oangle_add_swap, oangle_add_swap, vsub_ne_zero
-/
theorem oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) :
    ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃ :=
  o.oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the first and the second equals the angle between the second and the third. -/
@[simp]
/--
theorem `oangle_sub_left` / 定理 `oangle_sub_left`

English:
theorem oangle_sub_left
  given: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  proof: o.oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

中文:
定理 oangle_sub_left
  条件: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  证明: o.oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

Depends on / 依赖: o.oangle_sub_left, oangle_sub_left, vsub_ne_zero
-/
theorem oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) :
    ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃ :=
  o.oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the second and the third equals the angle between the first and the second. -/
@[simp]
/--
theorem `oangle_sub_right` / 定理 `oangle_sub_right`

English:
theorem oangle_sub_right
  given: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  proof: o.oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

中文:
定理 oangle_sub_right
  条件: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  证明: o.oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

Depends on / 依赖: o.oangle_sub_right, oangle_sub_right, vsub_ne_zero
-/
theorem oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) :
    ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂ :=
  o.oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/--
theorem `oangle_add_cyc3` / 定理 `oangle_add_cyc3`

English:
theorem oangle_add_cyc3
  given: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  proof: by
  simp [*]

中文:
定理 oangle_add_cyc3
  条件: {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p)
  证明: by
  simp [*]
-/
theorem oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) (hp₃ : p₃ != p) :
    ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 := by
  simp [*]

/--
theorem `oangle_eq_oangle_of_dist_eq` / 定理 `oangle_eq_oangle_of_dist_eq`

English:
theorem oangle_eq_oangle_of_dist_eq
  given: {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃)
  proof: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁]; rw [o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]

中文:
定理 oangle_eq_oangle_of_dist_eq
  条件: {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃)
  证明: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁]; rw [o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]

Depends on / 依赖: dist_eq_norm_vsub, o.oangle_sub_eq_oangle_sub_rev_of_norm_eq, oangle, oangle_sub_eq_oangle_sub_rev_of_norm_eq, simp_rw, vsub_sub_vsub_cancel_left
-/
theorem oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁ := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]; rw [← vsub_sub_vsub_cancel_left p₂ p₃ p₁]; rw [o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]

/--
theorem `oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq` / 定理 `oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq`

English:
theorem oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq
  statement: {p₁ p₂ p₃ : P} (hn : p₂ != p₃)
  proof: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]
  convert! o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
  · rw [← neg_vsub_eq_vsub_rev p₁ p₃, ← neg_vsub_eq_vsub_rev p₁ p₂, o.oangle_neg_neg]
  · rw [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]; simp
  · simpa using hn

中文:
定理 oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq
  结论: {p₁ p₂ p₃ : P} (hn : p₂ != p₃)
  证明: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]
  convert! o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
  · rw [← neg_vsub_eq_vsub_rev p₁ p₃, ← neg_vsub_eq_vsub_rev p₁ p₂, o.oangle_neg_neg]
  · rw [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]; simp
  · simpa using hn

Depends on / 依赖: convert, dist_eq_norm_vsub, neg_vsub_eq_vsub_rev, o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, o.oangle_neg_neg, o.oangle_sub_eq_oangle_sub_rev_of_norm_eq, oangle, oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq, oangle_neg_neg, oangle_sub_eq_oangle_sub_rev_of_norm_eq, simp_rw
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ != p₃)
    (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : Int) • ∡ p₁ p₂ p₃ := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [oangle]
  convert! o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
  · rw [← neg_vsub_eq_vsub_rev p₁ p₃, ← neg_vsub_eq_vsub_rev p₁ p₂, o.oangle_neg_neg]
  · rw [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]; simp
  · simpa using hn

/--
theorem `abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq` / 定理 `abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq`

English:
theorem abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
  statement: {p₁ p₂ p₃ : P}
  proof: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]
  exact o.abs_oangle_sub_right_toReal_lt_pi_div_two h

中文:
定理 abs_oangle_right_to实数_lt_pi_div_two_of_dist_eq
  结论: {p₁ p₂ p₃ : P}
  证明: by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]
  exact o.abs_oangle_sub_right_toReal_lt_pi_div_two h

Depends on / 依赖: abs_oangle_sub_right_toReal_lt_pi_div_two, dist_eq_norm_vsub, o.abs_oangle_sub_right_toReal_lt_pi_div_two, oangle, simp_rw, vsub_sub_vsub_cancel_left
-/
theorem abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₁ p₂ p₃).toReal| < π / 2 := by
  simp_rw [dist_eq_norm_vsub V] at h
  rw [oangle]; rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁]
  exact o.abs_oangle_sub_right_toReal_lt_pi_div_two h

/--
theorem `abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq` / 定理 `abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq`

English:
theorem abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
  statement: {p₁ p₂ p₃ : P}
  proof: oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq h

中文:
定理 abs_oangle_left_to实数_lt_pi_div_two_of_dist_eq
  结论: {p₁ p₂ p₃ : P}
  证明: oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq h

Depends on / 依赖: abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq, oangle_eq_oangle_of_dist_eq
-/
theorem abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2 :=
  oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq h

/--
theorem `cos_oangle_eq_cos_angle` / 定理 `cos_oangle_eq_cos_angle`

English:
theorem cos_oangle_eq_cos_angle
  given: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  proof: o.cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

中文:
定理 cos_oangle_eq_cos_angle
  条件: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  证明: o.cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

Depends on / 依赖: cos_oangle_eq_cos_angle, o.cos_oangle_eq_cos_angle, vsub_ne_zero
-/
theorem cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) :
    Real.Angle.cos (∡ p₁ p p₂) = Real.cos (∠ p₁ p p₂) :=
  o.cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/--
theorem `oangle_eq_angle_or_eq_neg_angle` / 定理 `oangle_eq_angle_or_eq_neg_angle`

English:
theorem oangle_eq_angle_or_eq_neg_angle
  given: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  proof: o.oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

中文:
定理 oangle_eq_angle_or_eq_neg_angle
  条件: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  证明: o.oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

Depends on / 依赖: o.oangle_eq_angle_or_eq_neg_angle, oangle_eq_angle_or_eq_neg_angle, vsub_ne_zero
-/
theorem oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) :
    ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂ :=
  o.oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/--
theorem `angle_eq_abs_oangle_toReal` / 定理 `angle_eq_abs_oangle_toReal`

English:
theorem angle_eq_abs_oangle_toReal
  given: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  proof: o.angle_eq_abs_oangle_toReal (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

中文:
定理 angle_eq_abs_oangle_to实数
  条件: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  证明: o.angle_eq_abs_oangle_toReal (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

Depends on / 依赖: angle_eq_abs_oangle_toReal, o.angle_eq_abs_oangle_toReal, vsub_ne_zero
-/
theorem angle_eq_abs_oangle_toReal {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) :
    ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal| :=
  o.angle_eq_abs_oangle_toReal (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/--
theorem `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero` / 定理 `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero`

English:
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
  statement: {p p₁ p₂ : P}
  proof: by
  convert! o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp

中文:
定理 eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
  结论: {p p₁ p₂ : P}
  证明: by
  convert! o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp

Depends on / 依赖: convert, eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero, o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
-/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P}
    (h : (∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π := by
  convert! o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp

/--
theorem `oangle_eq_of_angle_eq_of_sign_eq` / 定理 `oangle_eq_of_angle_eq_of_sign_eq`

English:
theorem oangle_eq_of_angle_eq_of_sign_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  proof: o.oangle_eq_of_angle_eq_of_sign_eq h hs

中文:
定理 oangle_eq_of_angle_eq_of_sign_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  证明: o.oangle_eq_of_angle_eq_of_sign_eq h hs

Depends on / 依赖: o.oangle_eq_of_angle_eq_of_sign_eq, oangle_eq_of_angle_eq_of_sign_eq
-/
theorem oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.oangle_eq_of_angle_eq_of_sign_eq h hs

/--
theorem `angle_eq_iff_oangle_eq_of_sign_eq` / 定理 `angle_eq_iff_oangle_eq_of_sign_eq`

English:
theorem angle_eq_iff_oangle_eq_of_sign_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂) (hp₃ : p₃ != p₂)
  proof: o.angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃) (vsub_ne_zero.2 hp₄)
    (vsub_ne_zero.2 hp₆) hs

中文:
定理 angle_eq_iff_oangle_eq_of_sign_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂) (hp₃ : p₃ != p₂)
  证明: o.angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃) (vsub_ne_zero.2 hp₄)
    (vsub_ne_zero.2 hp₆) hs

Depends on / 依赖: angle_eq_iff_oangle_eq_of_sign_eq, o.angle_eq_iff_oangle_eq_of_sign_eq, vsub_ne_zero
-/
theorem angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂) (hp₃ : p₃ != p₂)
    (hp₄ : p₄ != p₅) (hp₆ : p₆ != p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
  o.angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃) (vsub_ne_zero.2 hp₄)
    (vsub_ne_zero.2 hp₆) hs

/--
theorem `oangle_eq_or_eq_neg_of_angle_eq` / 定理 `oangle_eq_or_eq_neg_of_angle_eq`

English:
theorem oangle_eq_or_eq_neg_of_angle_eq
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  proof: by
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h1.symm h2.symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h3.symm h4.symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left
    rw [h₁]; rw [h₂]; rw [h]
  · right
    rw [h₁]; rw [h₂]; rw [h]; rw [neg_neg]
  · right
    rw [h₁]; rw [h₂]; rw [h]
  · left
    rw [h₁]; rw [h₂]; rw [h]

中文:
定理 oangle_eq_or_eq_neg_of_angle_eq
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  证明: by
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h1.symm h2.symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h3.symm h4.symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left
    rw [h₁]; rw [h₂]; rw [h]
  · right
    rw [h₁]; rw [h₂]; rw [h]; rw [neg_neg]
  · right
    rw [h₁]; rw [h₂]; rw [h]
  · left
    rw [h₁]; rw [h₂]; rw [h]

Depends on / 依赖: EuclideanGeometry, EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle, h1.symm, h2.symm, h3.symm, h4.symm, neg_neg, oangle_eq_angle_or_eq_neg_angle
-/
theorem oangle_eq_or_eq_neg_of_angle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
    (h1 : p₂ != p₁) (h2 : p₂ != p₃) (h3 : p₅ != p₄) (h4 : p₅ != p₆) :
    ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ ∨ ∡ p₁ p₂ p₃ = - ∡ p₄ p₅ p₆ := by
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h1.symm h2.symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle h3.symm h4.symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left
    rw [h₁]; rw [h₂]; rw [h]
  · right
    rw [h₁]; rw [h₂]; rw [h]; rw [neg_neg]
  · right
    rw [h₁]; rw [h₂]; rw [h]
  · left
    rw [h₁]; rw [h₂]; rw [h]

/--
lemma `oangle_eq_neg_of_angle_eq_of_sign_eq_neg` / 引理 `oangle_eq_neg_of_angle_eq_of_sign_eq_neg`

English:
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  proof: o.oangle_eq_neg_of_angle_eq_of_sign_eq_neg h hs

中文:
引理 oangle_eq_neg_of_angle_eq_of_sign_eq_neg
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  证明: o.oangle_eq_neg_of_angle_eq_of_sign_eq_neg h hs

Depends on / 依赖: o.oangle_eq_neg_of_angle_eq_of_sign_eq_neg, oangle_eq_neg_of_angle_eq_of_sign_eq_neg
-/
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆) (hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign) :
    ∡ p₁ p₂ p₃ = -∡ p₄ p₅ p₆ :=
  o.oangle_eq_neg_of_angle_eq_of_sign_eq_neg h hs

/--
lemma `angle_eq_iff_oangle_eq_neg_of_sign_eq_neg` / 引理 `angle_eq_iff_oangle_eq_neg_of_sign_eq_neg`

English:
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg
  statement: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂)
  proof: o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
    (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

中文:
引理 angle_eq_iff_oangle_eq_neg_of_sign_eq_neg
  结论: {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂)
  证明: o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
    (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

Depends on / 依赖: angle_eq_iff_oangle_eq_neg_of_sign_eq_neg, o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg, vsub_ne_zero
-/
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ != p₂)
    (hp₃ : p₃ != p₂) (hp₄ : p₄ != p₅) (hp₆ : p₆ != p₅) (hs : (∡ p₁ p₂ p₃).sign = -(∡ p₄ p₅ p₆).sign) :
    ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = -∡ p₄ p₅ p₆ :=
  o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
    (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

/--
theorem `oangle_eq_angle_of_sign_eq_one` / 定理 `oangle_eq_angle_of_sign_eq_one`

English:
theorem oangle_eq_angle_of_sign_eq_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  proof: o.oangle_eq_angle_of_sign_eq_one h

中文:
定理 oangle_eq_angle_of_sign_eq_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1)
  证明: o.oangle_eq_angle_of_sign_eq_one h

Depends on / 依赖: o.oangle_eq_angle_of_sign_eq_one, oangle_eq_angle_of_sign_eq_one
-/
theorem oangle_eq_angle_of_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) :
    ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃ :=
  o.oangle_eq_angle_of_sign_eq_one h

/--
theorem `oangle_eq_neg_angle_of_sign_eq_neg_one` / 定理 `oangle_eq_neg_angle_of_sign_eq_neg_one`

English:
theorem oangle_eq_neg_angle_of_sign_eq_neg_one
  given: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  proof: o.oangle_eq_neg_angle_of_sign_eq_neg_one h

中文:
定理 oangle_eq_neg_angle_of_sign_eq_neg_one
  条件: {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1)
  证明: o.oangle_eq_neg_angle_of_sign_eq_neg_one h

Depends on / 依赖: o.oangle_eq_neg_angle_of_sign_eq_neg_one, oangle_eq_neg_angle_of_sign_eq_neg_one
-/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    ∡ p₁ p₂ p₃ = -∠ p₁ p₂ p₃ :=
  o.oangle_eq_neg_angle_of_sign_eq_neg_one h

/--
theorem `oangle_eq_zero_iff_angle_eq_zero` / 定理 `oangle_eq_zero_iff_angle_eq_zero`

English:
theorem oangle_eq_zero_iff_angle_eq_zero
  given: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  proof: o.oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

中文:
定理 oangle_eq_zero_iff_angle_eq_zero
  条件: {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p)
  证明: o.oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

Depends on / 依赖: o.oangle_eq_zero_iff_angle_eq_zero, oangle_eq_zero_iff_angle_eq_zero, vsub_ne_zero
-/
theorem oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) :
    ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0 :=
  o.oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/--
theorem `oangle_eq_pi_iff_angle_eq_pi` / 定理 `oangle_eq_pi_iff_angle_eq_pi`

English:
theorem oangle_eq_pi_iff_angle_eq_pi
  given: {p₁ p₂ p₃ : P}
  statement: ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π
  proof: o.oangle_eq_pi_iff_angle_eq_pi

中文:
定理 oangle_eq_pi_iff_angle_eq_pi
  条件: {p₁ p₂ p₃ : P}
  结论: ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π
  证明: o.oangle_eq_pi_iff_angle_eq_pi

Depends on / 依赖: o.oangle_eq_pi_iff_angle_eq_pi, oangle_eq_pi_iff_angle_eq_pi
-/
theorem oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π :=
  o.oangle_eq_pi_iff_angle_eq_pi

/--
theorem `angle_eq_pi_div_two_of_oangle_eq_pi_div_two` / 定理 `angle_eq_pi_div_two_of_oangle_eq_pi_div_two`

English:
theorem angle_eq_pi_div_two_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_pi_div_two h

中文:
定理 angle_eq_pi_div_two_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_pi_div_two h

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, inner_eq_zero_iff_angle_eq_pi_div_two, inner_eq_zero_of_oangle_eq_pi_div_two, o.inner_eq_zero_of_oangle_eq_pi_div_two
-/
theorem angle_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_pi_div_two h

/--
theorem `angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two` / 定理 `angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`

English:
theorem angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two
  given: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  proof: by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h

中文:
定理 angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two
  条件: {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2))
  证明: by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h

Depends on / 依赖: angle_comm, angle_eq_pi_div_two_of_oangle_eq_pi_div_two
-/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h

/--
theorem `angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two` / 定理 `angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two`

English:
theorem angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h

中文:
定理 angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h

Depends on / 依赖: InnerProductGeometry, InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, inner_eq_zero_iff_angle_eq_pi_div_two, inner_eq_zero_of_oangle_eq_neg_pi_div_two, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two
-/
theorem angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₁ p₂ p₃ = π / 2 := by
  rw [angle]; rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h

/--
theorem `angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two` / 定理 `angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two`

English:
theorem angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
  statement: {p₁ p₂ p₃ : P}
  proof: by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h

中文:
定理 angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
  结论: {p₁ p₂ p₃ : P}
  证明: by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h

Depends on / 依赖: angle_comm, angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
-/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h

/--
theorem `oangle_swap₁₂_sign` / 定理 `oangle_swap₁₂_sign`

English:
theorem oangle_swap₁₂_sign
  given: (p₁ p₂ p₃ : P)
  statement: -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign
  proof: by
  rw [eq_comm]; rw [oangle]; rw [oangle]; rw [← o.oangle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_vsub_cancel_left p₁ p₃ p₂]; rw [← neg_vsub_eq_vsub_rev p₃ p₂]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev p₂ p₁]; rw [add_comm]; rw [← @neg_one_smul Real]
  nth_rw 2 [← one_smul Real (p₁ -ᵥ p₂)]
  rw [o.oangle_sign_smul_add_smul_right]
  simp

中文:
定理 oangle_swap₁₂_sign
  条件: (p₁ p₂ p₃ : P)
  结论: -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign
  证明: by
  rw [eq_comm]; rw [oangle]; rw [oangle]; rw [← o.oangle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_vsub_cancel_left p₁ p₃ p₂]; rw [← neg_vsub_eq_vsub_rev p₃ p₂]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev p₂ p₁]; rw [add_comm]; rw [← @neg_one_smul Real]
  nth_rw 2 [← one_smul Real (p₁ -ᵥ p₂)]
  rw [o.oangle_sign_smul_add_smul_right]
  simp

Depends on / 依赖: add_comm, eq_comm, neg_one_smul, neg_vsub_eq_vsub_rev, nth_rw, o.oangle_neg_neg, o.oangle_sign_smul_add_smul_right, oangle, oangle_neg_neg, oangle_sign_smul_add_smul_right, one_smul, sub_eq_add_neg, vsub_sub_vsub_cancel_left
-/
theorem oangle_swap₁₂_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign := by
  rw [eq_comm]; rw [oangle]; rw [oangle]; rw [← o.oangle_neg_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]; rw [←
    vsub_sub_vsub_cancel_left p₁ p₃ p₂]; rw [← neg_vsub_eq_vsub_rev p₃ p₂]; rw [sub_eq_add_neg]; rw [neg_vsub_eq_vsub_rev p₂ p₁]; rw [add_comm]; rw [← @neg_one_smul Real]
  nth_rw 2 [← one_smul Real (p₁ -ᵥ p₂)]
  rw [o.oangle_sign_smul_add_smul_right]
  simp

/--
theorem `oangle_swap₁₃_sign` / 定理 `oangle_swap₁₃_sign`

English:
theorem oangle_swap₁₃_sign
  given: (p₁ p₂ p₃ : P)
  statement: -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign
  proof: by
  rw [oangle_rev]; rw [Real.Angle.sign_neg]; rw [neg_neg]

中文:
定理 oangle_swap₁₃_sign
  条件: (p₁ p₂ p₃ : P)
  结论: -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign
  证明: by
  rw [oangle_rev]; rw [Real.Angle.sign_neg]; rw [neg_neg]

Depends on / 依赖: Real.Angle.sign_neg, neg_neg, oangle_rev, sign_neg
-/
theorem oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign := by
  rw [oangle_rev]; rw [Real.Angle.sign_neg]; rw [neg_neg]

/--
theorem `oangle_swap₂₃_sign` / 定理 `oangle_swap₂₃_sign`

English:
theorem oangle_swap₂₃_sign
  given: (p₁ p₂ p₃ : P)
  statement: -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign
  proof: by
  rw [oangle_swap₁₃_sign]; rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]

中文:
定理 oangle_swap₂₃_sign
  条件: (p₁ p₂ p₃ : P)
  结论: -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign
  证明: by
  rw [oangle_swap₁₃_sign]; rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]
-/
theorem oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign := by
  rw [oangle_swap₁₃_sign]; rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]

/--
theorem `oangle_rotate_sign` / 定理 `oangle_rotate_sign`

English:
theorem oangle_rotate_sign
  given: (p₁ p₂ p₃ : P)
  statement: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
  proof: by
  rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]

中文:
定理 oangle_rotate_sign
  条件: (p₁ p₂ p₃ : P)
  结论: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
  证明: by
  rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]
-/
theorem oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign := by
  rw [← oangle_swap₁₂_sign]; rw [oangle_swap₁₃_sign]

/--
theorem `oangle_eq_pi_iff_sbtw` / 定理 `oangle_eq_pi_iff_sbtw`

English:
theorem oangle_eq_pi_iff_sbtw
  given: {p₁ p₂ p₃ : P}
  statement: ∡ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃
  proof: by
  rw [oangle_eq_pi_iff_angle_eq_pi]; rw [angle_eq_pi_iff_sbtw]

中文:
定理 oangle_eq_pi_iff_sbtw
  条件: {p₁ p₂ p₃ : P}
  结论: ∡ p₁ p₂ p₃ = π ↔ Sbtw 实数 p₁ p₂ p₃
  证明: by
  rw [oangle_eq_pi_iff_angle_eq_pi]; rw [angle_eq_pi_iff_sbtw]

Depends on / 依赖: angle_eq_pi_iff_sbtw, oangle_eq_pi_iff_angle_eq_pi
-/
theorem oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ Sbtw Real p₁ p₂ p₃ := by
  rw [oangle_eq_pi_iff_angle_eq_pi]; rw [angle_eq_pi_iff_sbtw]

/--
theorem `_root_.Sbtw.oangle₁₂₃_eq_pi` / 定理 `_root_.Sbtw.oangle₁₂₃_eq_pi`

English:
theorem _root_.Sbtw.oangle₁₂₃_eq_pi
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₁ p₂ p₃ = π
  proof: oangle_eq_pi_iff_sbtw.2 h

中文:
定理 _root_.Sbtw.oangle₁₂₃_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₁ p₂ p₃ = π
  证明: oangle_eq_pi_iff_sbtw.2 h

Depends on / 依赖: oangle_eq_pi_iff_sbtw
-/
theorem _root_.Sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
  oangle_eq_pi_iff_sbtw.2 h

/--
theorem `_root_.Sbtw.oangle₃₂₁_eq_pi` / 定理 `_root_.Sbtw.oangle₃₂₁_eq_pi`

English:
theorem _root_.Sbtw.oangle₃₂₁_eq_pi
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₃ p₂ p₁ = π
  proof: by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi]; rw [← h.oangle₁₂₃_eq_pi]

中文:
定理 _root_.Sbtw.oangle₃₂₁_eq_pi
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₃ p₂ p₁ = π
  证明: by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi]; rw [← h.oangle₁₂₃_eq_pi]

Depends on / 依赖: h.oangle, oangle_eq_pi_iff_oangle_rev_eq_pi
-/
theorem _root_.Sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π := by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi]; rw [← h.oangle₁₂₃_eq_pi]

/--
theorem `_root_.Wbtw.oangle₂₁₃_eq_zero` / 定理 `_root_.Wbtw.oangle₂₁₃_eq_zero`

English:
theorem _root_.Wbtw.oangle₂₁₃_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃)
  statement: ∡ p₂ p₁ p₃ = 0
  proof: by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁

中文:
定理 _root_.Wbtw.oangle₂₁₃_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₂ p₁ p₃ = 0
  证明: by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁

Depends on / 依赖: h.angle, oangle_eq_zero_iff_angle_eq_zero
-/
theorem _root_.Wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 := by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁

/--
theorem `_root_.Sbtw.oangle₂₁₃_eq_zero` / 定理 `_root_.Sbtw.oangle₂₁₃_eq_zero`

English:
theorem _root_.Sbtw.oangle₂₁₃_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₂ p₁ p₃ = 0
  proof: h.wbtw.oangle₂₁₃_eq_zero

中文:
定理 _root_.Sbtw.oangle₂₁₃_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₂ p₁ p₃ = 0
  证明: h.wbtw.oangle₂₁₃_eq_zero

Depends on / 依赖: h.wbtw.oangle
-/
theorem _root_.Sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
  h.wbtw.oangle₂₁₃_eq_zero

/--
theorem `_root_.Wbtw.oangle₃₁₂_eq_zero` / 定理 `_root_.Wbtw.oangle₃₁₂_eq_zero`

English:
theorem _root_.Wbtw.oangle₃₁₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃)
  statement: ∡ p₃ p₁ p₂ = 0
  proof: by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero]; rw [h.oangle₂₁₃_eq_zero]

中文:
定理 _root_.Wbtw.oangle₃₁₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₃ p₁ p₂ = 0
  证明: by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero]; rw [h.oangle₂₁₃_eq_zero]

Depends on / 依赖: h.oangle, oangle_eq_zero_iff_oangle_rev_eq_zero
-/
theorem _root_.Wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 := by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero]; rw [h.oangle₂₁₃_eq_zero]

/--
theorem `_root_.Sbtw.oangle₃₁₂_eq_zero` / 定理 `_root_.Sbtw.oangle₃₁₂_eq_zero`

English:
theorem _root_.Sbtw.oangle₃₁₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₃ p₁ p₂ = 0
  proof: h.wbtw.oangle₃₁₂_eq_zero

中文:
定理 _root_.Sbtw.oangle₃₁₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₃ p₁ p₂ = 0
  证明: h.wbtw.oangle₃₁₂_eq_zero

Depends on / 依赖: h.wbtw.oangle
-/
theorem _root_.Sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
  h.wbtw.oangle₃₁₂_eq_zero

/--
theorem `_root_.Wbtw.oangle₂₃₁_eq_zero` / 定理 `_root_.Wbtw.oangle₂₃₁_eq_zero`

English:
theorem _root_.Wbtw.oangle₂₃₁_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃)
  statement: ∡ p₂ p₃ p₁ = 0
  proof: h.symm.oangle₂₁₃_eq_zero

中文:
定理 _root_.Wbtw.oangle₂₃₁_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₂ p₃ p₁ = 0
  证明: h.symm.oangle₂₁₃_eq_zero

Depends on / 依赖: h.symm.oangle
-/
theorem _root_.Wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.symm.oangle₂₁₃_eq_zero

/--
theorem `_root_.Sbtw.oangle₂₃₁_eq_zero` / 定理 `_root_.Sbtw.oangle₂₃₁_eq_zero`

English:
theorem _root_.Sbtw.oangle₂₃₁_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₂ p₃ p₁ = 0
  proof: h.wbtw.oangle₂₃₁_eq_zero

中文:
定理 _root_.Sbtw.oangle₂₃₁_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₂ p₃ p₁ = 0
  证明: h.wbtw.oangle₂₃₁_eq_zero

Depends on / 依赖: h.wbtw.oangle
-/
theorem _root_.Sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.wbtw.oangle₂₃₁_eq_zero

/--
theorem `_root_.Wbtw.oangle₁₃₂_eq_zero` / 定理 `_root_.Wbtw.oangle₁₃₂_eq_zero`

English:
theorem _root_.Wbtw.oangle₁₃₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃)
  statement: ∡ p₁ p₃ p₂ = 0
  proof: h.symm.oangle₃₁₂_eq_zero

中文:
定理 _root_.Wbtw.oangle₁₃₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Wbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₁ p₃ p₂ = 0
  证明: h.symm.oangle₃₁₂_eq_zero

Depends on / 依赖: h.symm.oangle
-/
theorem _root_.Wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw Real p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.symm.oangle₃₁₂_eq_zero

/--
theorem `_root_.Sbtw.oangle₁₃₂_eq_zero` / 定理 `_root_.Sbtw.oangle₁₃₂_eq_zero`

English:
theorem _root_.Sbtw.oangle₁₃₂_eq_zero
  given: {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃)
  statement: ∡ p₁ p₃ p₂ = 0
  proof: h.wbtw.oangle₁₃₂_eq_zero

中文:
定理 _root_.Sbtw.oangle₁₃₂_eq_zero
  条件: {p₁ p₂ p₃ : P} (h : Sbtw 实数 p₁ p₂ p₃)
  结论: ∡ p₁ p₃ p₂ = 0
  证明: h.wbtw.oangle₁₃₂_eq_zero

Depends on / 依赖: h.wbtw.oangle
-/
theorem _root_.Sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.wbtw.oangle₁₃₂_eq_zero

/--
theorem `oangle_eq_zero_iff_wbtw` / 定理 `oangle_eq_zero_iff_wbtw`

English:
theorem oangle_eq_zero_iff_wbtw
  given: {p₁ p₂ p₃ : P}
  proof: by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂]; rw [angle_eq_zero_iff_ne_and_wbtw]
  simp [hp₁p₂, hp₃p₂]

中文:
定理 oangle_eq_zero_iff_wbtw
  条件: {p₁ p₂ p₃ : P}
  证明: by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂]; rw [angle_eq_zero_iff_ne_and_wbtw]
  simp [hp₁p₂, hp₃p₂]

Depends on / 依赖: angle_eq_zero_iff_ne_and_wbtw, oangle_eq_zero_iff_angle_eq_zero
-/
theorem oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ↔ Wbtw Real p₂ p₁ p₃ ∨ Wbtw Real p₂ p₃ p₁ := by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂]; rw [angle_eq_zero_iff_ne_and_wbtw]
  simp [hp₁p₂, hp₃p₂]

/--
theorem `_root_.Wbtw.oangle_eq_left` / 定理 `_root_.Wbtw.oangle_eq_left`

English:
theorem _root_.Wbtw.oangle_eq_left
  given: {p₁ p₁' p₂ p₃ : P} (h : Wbtw Real p₂ p₁ p₁') (hp₁p₂ : p₁ != p₂)
  proof: by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  by_cases hp₁'p₂ : p₁' = p₂; · rw [hp₁'p₂, wbtw_self_iff] at h; exact False.elim (hp₁p₂ h)
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂]; rw [h.oangle₃₁₂_eq_zero]; rw [zero_add]

中文:
定理 _root_.Wbtw.oangle_eq_left
  条件: {p₁ p₁' p₂ p₃ : P} (h : Wbtw 实数 p₂ p₁ p₁') (hp₁p₂ : p₁ != p₂)
  证明: by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  by_cases hp₁'p₂ : p₁' = p₂; · rw [hp₁'p₂, wbtw_self_iff] at h; exact False.elim (hp₁p₂ h)
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂]; rw [h.oangle₃₁₂_eq_zero]; rw [zero_add]

Depends on / 依赖: False.elim, h.oangle, oangle_add, wbtw_self_iff, zero_add
-/
theorem _root_.Wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Wbtw Real p₂ p₁ p₁') (hp₁p₂ : p₁ != p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  by_cases hp₁'p₂ : p₁' = p₂; · rw [hp₁'p₂, wbtw_self_iff] at h; exact False.elim (hp₁p₂ h)
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂]; rw [h.oangle₃₁₂_eq_zero]; rw [zero_add]

/--
theorem `_root_.Sbtw.oangle_eq_left` / 定理 `_root_.Sbtw.oangle_eq_left`

English:
theorem _root_.Sbtw.oangle_eq_left
  given: {p₁ p₁' p₂ p₃ : P} (h : Sbtw Real p₂ p₁ p₁')
  proof: h.wbtw.oangle_eq_left h.ne_left

中文:
定理 _root_.Sbtw.oangle_eq_left
  条件: {p₁ p₁' p₂ p₃ : P} (h : Sbtw 实数 p₂ p₁ p₁')
  证明: h.wbtw.oangle_eq_left h.ne_left

Depends on / 依赖: h.ne_left, h.wbtw.oangle_eq_left, ne_left, oangle_eq_left
-/
theorem _root_.Sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Sbtw Real p₂ p₁ p₁') :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
  h.wbtw.oangle_eq_left h.ne_left

/--
theorem `_root_.Wbtw.oangle_eq_right` / 定理 `_root_.Wbtw.oangle_eq_right`

English:
theorem _root_.Wbtw.oangle_eq_right
  given: {p₁ p₂ p₃ p₃' : P} (h : Wbtw Real p₂ p₃ p₃') (hp₃p₂ : p₃ != p₂)
  proof: by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]

中文:
定理 _root_.Wbtw.oangle_eq_right
  条件: {p₁ p₂ p₃ p₃' : P} (h : Wbtw 实数 p₂ p₃ p₃') (hp₃p₂ : p₃ != p₂)
  证明: by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]

Depends on / 依赖: h.oangle_eq_left, oangle_eq_left, oangle_rev
-/
theorem _root_.Wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Wbtw Real p₂ p₃ p₃') (hp₃p₂ : p₃ != p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' := by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]

/--
theorem `_root_.Sbtw.oangle_eq_right` / 定理 `_root_.Sbtw.oangle_eq_right`

English:
theorem _root_.Sbtw.oangle_eq_right
  given: {p₁ p₂ p₃ p₃' : P} (h : Sbtw Real p₂ p₃ p₃')
  proof: h.wbtw.oangle_eq_right h.ne_left

中文:
定理 _root_.Sbtw.oangle_eq_right
  条件: {p₁ p₂ p₃ p₃' : P} (h : Sbtw 实数 p₂ p₃ p₃')
  证明: h.wbtw.oangle_eq_right h.ne_left

Depends on / 依赖: h.ne_left, h.wbtw.oangle_eq_right, ne_left, oangle_eq_right
-/
theorem _root_.Sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Sbtw Real p₂ p₃ p₃') :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
  h.wbtw.oangle_eq_right h.ne_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between it and the second point. -/
@[simp]
/--
theorem `oangle_midpoint_left` / 定理 `oangle_midpoint_left`

English:
theorem oangle_midpoint_left
  given: (p₁ p₂ p₃ : P)
  statement: ∡ (midpoint Real p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃
  proof: by
  by_cases h : p₁ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_left

中文:
定理 oangle_midpoint_left
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ (midpoint 实数 p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃
  证明: by
  by_cases h : p₁ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_left

Depends on / 依赖: oangle_eq_left, sbtw_midpoint_of_ne, symm.oangle_eq_left
-/
theorem oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint Real p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  by_cases h : p₁ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between the second point and that point. -/
@[simp]
/--
theorem `oangle_midpoint_rev_left` / 定理 `oangle_midpoint_rev_left`

English:
theorem oangle_midpoint_rev_left
  given: (p₁ p₂ p₃ : P)
  statement: ∡ (midpoint Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃
  proof: by
  rw [midpoint_comm]; rw [oangle_midpoint_left]

中文:
定理 oangle_midpoint_rev_left
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ (midpoint 实数 p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃
  证明: by
  rw [midpoint_comm]; rw [oangle_midpoint_left]

Depends on / 依赖: midpoint_comm, oangle_midpoint_left
-/
theorem oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm]; rw [oangle_midpoint_left]

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between it and the second point. -/
@[simp]
/--
theorem `oangle_midpoint_right` / 定理 `oangle_midpoint_right`

English:
theorem oangle_midpoint_right
  given: (p₁ p₂ p₃ : P)
  statement: ∡ p₁ p₂ (midpoint Real p₃ p₂) = ∡ p₁ p₂ p₃
  proof: by
  by_cases h : p₃ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_right

中文:
定理 oangle_midpoint_right
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ p₁ p₂ (midpoint 实数 p₃ p₂) = ∡ p₁ p₂ p₃
  证明: by
  by_cases h : p₃ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_right

Depends on / 依赖: oangle_eq_right, sbtw_midpoint_of_ne, symm.oangle_eq_right
-/
theorem oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint Real p₃ p₂) = ∡ p₁ p₂ p₃ := by
  by_cases h : p₃ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne Real h).symm.oangle_eq_right

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between the second point and that point. -/
@[simp]
/--
theorem `oangle_midpoint_rev_right` / 定理 `oangle_midpoint_rev_right`

English:
theorem oangle_midpoint_rev_right
  given: (p₁ p₂ p₃ : P)
  statement: ∡ p₁ p₂ (midpoint Real p₂ p₃) = ∡ p₁ p₂ p₃
  proof: by
  rw [midpoint_comm]; rw [oangle_midpoint_right]

中文:
定理 oangle_midpoint_rev_right
  条件: (p₁ p₂ p₃ : P)
  结论: ∡ p₁ p₂ (midpoint 实数 p₂ p₃) = ∡ p₁ p₂ p₃
  证明: by
  rw [midpoint_comm]; rw [oangle_midpoint_right]

Depends on / 依赖: midpoint_comm, oangle_midpoint_right
-/
theorem oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint Real p₂ p₃) = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm]; rw [oangle_midpoint_right]

/--
theorem `_root_.Sbtw.oangle_eq_add_pi_left` / 定理 `_root_.Sbtw.oangle_eq_add_pi_left`

English:
theorem _root_.Sbtw.oangle_eq_add_pi_left
  proof: by
  rw [← h.oangle₁₂₃_eq_pi]; rw [oangle_add_swap h.left_ne h.right_ne hp₃p₂]

中文:
定理 _root_.Sbtw.oangle_eq_add_pi_left
  证明: by
  rw [← h.oangle₁₂₃_eq_pi]; rw [oangle_add_swap h.left_ne h.right_ne hp₃p₂]

Depends on / 依赖: h.left_ne, h.oangle, h.right_ne, left_ne, oangle_add_swap, right_ne
-/
theorem _root_.Sbtw.oangle_eq_add_pi_left
    {p₁ p₁' p₂ p₃ : P} (h : Sbtw Real p₁ p₂ p₁') (hp₃p₂ : p₃ != p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π := by
  rw [← h.oangle₁₂₃_eq_pi]; rw [oangle_add_swap h.left_ne h.right_ne hp₃p₂]

/--
theorem `_root_.Sbtw.oangle_eq_add_pi_right` / 定理 `_root_.Sbtw.oangle_eq_add_pi_right`

English:
theorem _root_.Sbtw.oangle_eq_add_pi_right
  proof: by
  rw [← h.oangle₃₂₁_eq_pi]; rw [oangle_add hp₁p₂ h.right_ne h.left_ne]

中文:
定理 _root_.Sbtw.oangle_eq_add_pi_right
  证明: by
  rw [← h.oangle₃₂₁_eq_pi]; rw [oangle_add hp₁p₂ h.right_ne h.left_ne]

Depends on / 依赖: h.left_ne, h.oangle, h.right_ne, left_ne, oangle_add, right_ne
-/
theorem _root_.Sbtw.oangle_eq_add_pi_right
    {p₁ p₂ p₃ p₃' : P} (h : Sbtw Real p₃ p₂ p₃') (hp₁p₂ : p₁ != p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π := by
  rw [← h.oangle₃₂₁_eq_pi]; rw [oangle_add hp₁p₂ h.right_ne h.left_ne]

/--
theorem `_root_.Sbtw.oangle_eq_left_right` / 定理 `_root_.Sbtw.oangle_eq_left_right`

English:
theorem _root_.Sbtw.oangle_eq_left_right
  statement: {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw Real p₁ p₂ p₁')
  proof: by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne]; rw [h₃.oangle_eq_add_pi_right h₁.right_ne]; rw [add_assoc]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [add_zero]

中文:
定理 _root_.Sbtw.oangle_eq_left_right
  结论: {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw 实数 p₁ p₂ p₁')
  证明: by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne]; rw [h₃.oangle_eq_add_pi_right h₁.right_ne]; rw [add_assoc]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [add_zero]

Depends on / 依赖: Real.Angle.coe_pi_add_coe_pi, add_assoc, add_zero, coe_pi_add_coe_pi, left_ne, oangle_eq_add_pi_left, oangle_eq_add_pi_right, right_ne
-/
theorem _root_.Sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw Real p₁ p₂ p₁')
    (h₃ : Sbtw Real p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' := by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne]; rw [h₃.oangle_eq_add_pi_right h₁.right_ne]; rw [add_assoc]; rw [Real.Angle.coe_pi_add_coe_pi]; rw [add_zero]

/--
lemma `oangle_pointReflection_right` / 引理 `oangle_pointReflection_right`

English:
lemma oangle_pointReflection_right
  given: {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂)
  proof: by
  have h₂₃' : (AffineEquiv.pointReflection Real p₂) p₃ != p₂ := by
    conv_rhs => rw [← AffineEquiv.pointReflection_self Real p₂]
    rw [(AffineEquiv.pointReflection Real p₂).injective.ne_iff]
    exact h₃₂
  rw [← sub_eq_iff_eq_add']; rw [oangle_sub_left h₁₂ h₃₂ h₂₃']
exact Sbtw.oangle₁₂₃_eq_pi sbtw_pointReflection_of_ne Real h₃₂.symm

中文:
引理 oangle_pointReflection_right
  条件: {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂)
  证明: by
  have h₂₃' : (AffineEquiv.pointReflection Real p₂) p₃ != p₂ := by
    conv_rhs => rw [← AffineEquiv.pointReflection_self Real p₂]
    rw [(AffineEquiv.pointReflection Real p₂).injective.ne_iff]
    exact h₃₂
  rw [← sub_eq_iff_eq_add']; rw [oangle_sub_left h₁₂ h₃₂ h₂₃']
exact Sbtw.oangle₁₂₃_eq_pi sbtw_pointReflection_of_ne Real h₃₂.symm

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection, AffineEquiv.pointReflection_self, Sbtw.oangle, conv_rhs, injective, injective.ne_iff, ne_iff, oangle_sub_left, pointReflection, pointReflection_self, sbtw_pointReflection_of_ne, sub_eq_iff_eq_add
-/
lemma oangle_pointReflection_right {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) :
    ∡ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) = ∡ p₁ p₂ p₃ + π := by
  have h₂₃' : (AffineEquiv.pointReflection Real p₂) p₃ != p₂ := by
    conv_rhs => rw [← AffineEquiv.pointReflection_self Real p₂]
    rw [(AffineEquiv.pointReflection Real p₂).injective.ne_iff]
    exact h₃₂
  rw [← sub_eq_iff_eq_add']; rw [oangle_sub_left h₁₂ h₃₂ h₂₃']
exact Sbtw.oangle₁₂₃_eq_pi sbtw_pointReflection_of_ne Real h₃₂.symm

/--
lemma `oangle_pointReflection_left` / 引理 `oangle_pointReflection_left`

English:
lemma oangle_pointReflection_left
  given: {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂)
  proof: by
  rw [oangle_rev]; rw [oangle_pointReflection_right h₃₂ h₁₂]; rw [neg_add]; rw [← oangle_rev]
  simp

中文:
引理 oangle_pointReflection_left
  条件: {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂)
  证明: by
  rw [oangle_rev]; rw [oangle_pointReflection_right h₃₂ h₁₂]; rw [neg_add]; rw [← oangle_rev]
  simp

Depends on / 依赖: neg_add, oangle_pointReflection_right, oangle_rev
-/
lemma oangle_pointReflection_left {p₁ p₂ p₃ : P} (h₁₂ : p₁ != p₂) (h₃₂ : p₃ != p₂) :
    ∡ (AffineEquiv.pointReflection Real p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ + π := by
  rw [oangle_rev]; rw [oangle_pointReflection_right h₃₂ h₁₂]; rw [neg_add]; rw [← oangle_rev]
  simp

/--
theorem `_root_.Collinear.two_zsmul_oangle_eq_left` / 定理 `_root_.Collinear.two_zsmul_oangle_eq_left`

English:
theorem _root_.Collinear.two_zsmul_oangle_eq_left
  statement: {p₁ p₁' p₂ p₃ : P}
  proof: by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw Real p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    rw [hw'.oangle_eq_add_pi_left hp₃p₂]; rw [smul_add]; rw [Real.Angle.two_zsmul_coe_pi]; rw [add_zero]
  · rw [hw.oangle_eq_left hp₁'p₂]
  · rw [hw.symm.oangle_eq_left hp₁p₂]

中文:
定理 _root_.Collinear.two_zsmul_oangle_eq_left
  结论: {p₁ p₁' p₂ p₃ : P}
  证明: by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw Real p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    rw [hw'.oangle_eq_add_pi_left hp₃p₂]; rw [smul_add]; rw [Real.Angle.two_zsmul_coe_pi]; rw [add_zero]
  · rw [hw.oangle_eq_left hp₁'p₂]
  · rw [hw.symm.oangle_eq_left hp₁p₂]

Depends on / 依赖: Real.Angle.two_zsmul_coe_pi, add_zero, h.wbtw_or_wbtw_or_wbtw, hw.oangle_eq_left, hw.symm.oangle_eq_left, oangle_eq_add_pi_left, oangle_eq_left, smul_add, two_zsmul_coe_pi, wbtw_or_wbtw_or_wbtw
-/
theorem _root_.Collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
    (h : Collinear Real ({p₁, p₂, p₁'} : Set P)) (hp₁p₂ : p₁ != p₂) (hp₁'p₂ : p₁' != p₂) :
    (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw Real p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    rw [hw'.oangle_eq_add_pi_left hp₃p₂]; rw [smul_add]; rw [Real.Angle.two_zsmul_coe_pi]; rw [add_zero]
  · rw [hw.oangle_eq_left hp₁'p₂]
  · rw [hw.symm.oangle_eq_left hp₁p₂]

/--
theorem `_root_.Collinear.two_zsmul_oangle_eq_right` / 定理 `_root_.Collinear.two_zsmul_oangle_eq_right`

English:
theorem _root_.Collinear.two_zsmul_oangle_eq_right
  statement: {p₁ p₂ p₃ p₃' : P}
  proof: by
  rw [oangle_rev]; rw [smul_neg]; rw [h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂]; rw [← smul_neg]; rw [← oangle_rev]

中文:
定理 _root_.Collinear.two_zsmul_oangle_eq_right
  结论: {p₁ p₂ p₃ p₃' : P}
  证明: by
  rw [oangle_rev]; rw [smul_neg]; rw [h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂]; rw [← smul_neg]; rw [← oangle_rev]

Depends on / 依赖: h.two_zsmul_oangle_eq_left, oangle_rev, smul_neg, two_zsmul_oangle_eq_left
-/
theorem _root_.Collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
    (h : Collinear Real ({p₃, p₂, p₃'} : Set P)) (hp₃p₂ : p₃ != p₂) (hp₃'p₂ : p₃' != p₂) :
    (2 : Int) • ∡ p₁ p₂ p₃ = (2 : Int) • ∡ p₁ p₂ p₃' := by
  rw [oangle_rev]; rw [smul_neg]; rw [h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂]; rw [← smul_neg]; rw [← oangle_rev]

/--
theorem `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint` / 定理 `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint`

English:
theorem dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint
  given: {p₁ p₂ p : P} (h : p₁ != p₂)
  proof: by
  refine ⟨fun hd => ?_, fun hr => ?_⟩
  · have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint Real p₁ p₂⟫ = 0 := by
      rw [@dist_eq_norm_vsub' V]; rw [@dist_eq_norm_vsub' V]; rw [←
        mul_self_inj (norm_nonneg _) (norm_nonneg _)]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
        real_inner_self_eq_norm_mul_norm] at hd
      simp_rw [vsub_midpoint, ← vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left, inner_add_right,
        inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)]
      abel
    rw [@Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o]; rw [or_iff_right (vsub_ne_zero.2 h.symm)] at hi
    rcases hi with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    exact ⟨r, hr.symm⟩
  · rcases hr with ⟨r, rfl⟩
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint, right_vsub_midpoint,
      invOf_eq_inv, ← neg_vsub_eq_vsub_rev p₂ p₁, ← mul_self_inj (norm_nonneg _) (norm_nonneg _), ←
      real_inner_self_eq_norm_mul_norm, inner_sub_sub_self]
    simp [-neg_vsub_eq_vsub_rev]

中文:
定理 dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint
  条件: {p₁ p₂ p : P} (h : p₁ != p₂)
  证明: by
  refine ⟨fun hd => ?_, fun hr => ?_⟩
  · have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint Real p₁ p₂⟫ = 0 := by
      rw [@dist_eq_norm_vsub' V]; rw [@dist_eq_norm_vsub' V]; rw [←
        mul_self_inj (norm_nonneg _) (norm_nonneg _)]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
        real_inner_self_eq_norm_mul_norm] at hd
      simp_rw [vsub_midpoint, ← vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left, inner_add_right,
        inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)]
      abel
    rw [@Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o]; rw [or_iff_right (vsub_ne_zero.2 h.symm)] at hi
    rcases hi with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    exact ⟨r, hr.symm⟩
  · rcases hr with ⟨r, rfl⟩
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint, right_vsub_midpoint,
      invOf_eq_inv, ← neg_vsub_eq_vsub_rev p₂ p₁, ← mul_self_inj (norm_nonneg _) (norm_nonneg _), ←
      real_inner_self_eq_norm_mul_norm, inner_sub_sub_self]
    simp [-neg_vsub_eq_vsub_rev]

Depends on / 依赖: Orientation, Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rota, dist_eq_norm_vsub, inner_add_right, inner_eq_zero_iff_eq_zero_or_eq_smul_rota, inner_smul_right, inner_sub_left, midpoint, mul_self_inj, norm_nonneg, real_inner_comm, real_inner_self_eq_norm_mul_norm, simp_rw, vsub_midpoint, vsub_sub_vsub_cancel_left
-/
theorem dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p₁ != p₂) :
    dist p₁ p = dist p₂ p ↔
      exists r : Real, r • o.rotation (π / 2 : Real) (p₂ -ᵥ p₁) +ᵥ midpoint Real p₁ p₂ = p := by
  refine ⟨fun hd => ?_, fun hr => ?_⟩
  · have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint Real p₁ p₂⟫ = 0 := by
      rw [@dist_eq_norm_vsub' V]; rw [@dist_eq_norm_vsub' V]; rw [←
        mul_self_inj (norm_nonneg _) (norm_nonneg _)]; rw [← real_inner_self_eq_norm_mul_norm]; rw [←
        real_inner_self_eq_norm_mul_norm] at hd
      simp_rw [vsub_midpoint, ← vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left, inner_add_right,
        inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)]
      abel
    rw [@Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o]; rw [or_iff_right (vsub_ne_zero.2 h.symm)] at hi
    rcases hi with ⟨r, hr⟩
    rw [eq_comm]; rw [← eq_vadd_iff_vsub_eq] at hr
    exact ⟨r, hr.symm⟩
  · rcases hr with ⟨r, rfl⟩
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint, right_vsub_midpoint,
      invOf_eq_inv, ← neg_vsub_eq_vsub_rev p₂ p₁, ← mul_self_inj (norm_nonneg _) (norm_nonneg _), ←
      real_inner_self_eq_norm_mul_norm, inner_sub_sub_self]
    simp [-neg_vsub_eq_vsub_rev]

open AffineSubspace

/--
theorem `_root_.Collinear.oangle_sign_of_sameRay_vsub` / 定理 `_root_.Collinear.oangle_sign_of_sameRay_vsub`

English:
theorem _root_.Collinear.oangle_sign_of_sameRay_vsub
  statement: {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ != p₂)
  proof: by
  by_cases hc₅₁₂ : Collinear Real ({p₅, p₁, p₂} : Set P)
  · have hc₅₁₂₃₄ : Collinear Real ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂
    have hc₅₃₄ : Collinear Real ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    rw [hs₁₅₂]; rw [hs₃₅₄]
  · let s : Set (P × P × P) :=
      (fun x : line[Real, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ (x.1 : P))) ''
        Set.univ ×ˢ {v | SameRay Real (p₂ -ᵥ p₁) v ∧ v != 0}
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[Real, p₁, p₂] := AddTorsor.connectedSpace _ _
      (isConnected_univ.prod (isConnected_setOfPred_sameRay_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _ (by fun_prop)
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s := by
      refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
      all_goals
        simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp ⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair _ _ _))
      · exact hq
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hsp : forall p : P × P × P, p in s -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
      intro p hp
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp ⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q in line[Real, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
      refine affineIndependent_of_ne_of_mem_of_notMem_of_mem ?_ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan h).2 (collinear_pair _ _ _))) ?_
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₁, left_mem_affineSpan_pair Real _ _⟩, p₂ -ᵥ p₁⟩,
        ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, ?_⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₃, hc.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩, p₄ -ᵥ p₃⟩,
        ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, ?_⟩
      simp
    convert! Real.Angle.sign_eq_of_continuousOn hco hf hsp hp₃p₄s hp₁p₂s

中文:
定理 _root_.Collinear.oangle_sign_of_sameRay_vsub
  结论: {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ != p₂)
  证明: by
  by_cases hc₅₁₂ : Collinear Real ({p₅, p₁, p₂} : Set P)
  · have hc₅₁₂₃₄ : Collinear Real ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂
    have hc₅₃₄ : Collinear Real ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    rw [hs₁₅₂]; rw [hs₃₅₄]
  · let s : Set (P × P × P) :=
      (fun x : line[Real, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ (x.1 : P))) ''
        Set.univ ×ˢ {v | SameRay Real (p₂ -ᵥ p₁) v ∧ v != 0}
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[Real, p₁, p₂] := AddTorsor.connectedSpace _ _
      (isConnected_univ.prod (isConnected_setOfPred_sameRay_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _ (by fun_prop)
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s := by
      refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
      all_goals
        simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp ⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair _ _ _))
      · exact hq
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hsp : forall p : P × P × P, p in s -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
      intro p hp
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp ⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q in line[Real, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
      refine affineIndependent_of_ne_of_mem_of_notMem_of_mem ?_ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan h).2 (collinear_pair _ _ _))) ?_
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₁, left_mem_affineSpan_pair Real _ _⟩, p₂ -ᵥ p₁⟩,
        ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, ?_⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₃, hc.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩, p₄ -ᵥ p₃⟩,
        ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, ?_⟩
      simp
    convert! Real.Angle.sign_eq_of_continuousOn hco hf hsp hp₃p₄s hp₁p₂s

Depends on / 依赖: Collinear, Set.mem_insert, Set.mem_insert_of_mem, Set.mem_singleton, collinear_insert_iff_of_ne, hc.collinear_insert_iff_of_ne, mem_insert, mem_insert_of_mem, mem_singleton
-/
theorem _root_.Collinear.oangle_sign_of_sameRay_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ != p₂)
    (hp₃p₄ : p₃ != p₄) (hc : Collinear Real ({p₁, p₂, p₃, p₄} : Set P))
    (hr : SameRay Real (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign := by
  by_cases hc₅₁₂ : Collinear Real ({p₅, p₁, p₂} : Set P)
  · have hc₅₁₂₃₄ : Collinear Real ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂
    have hc₅₃₄ : Collinear Real ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    rw [hs₁₅₂]; rw [hs₃₅₄]
  · let s : Set (P × P × P) :=
      (fun x : line[Real, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ (x.1 : P))) ''
        Set.univ ×ˢ {v | SameRay Real (p₂ -ᵥ p₁) v ∧ v != 0}
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[Real, p₁, p₂] := AddTorsor.connectedSpace _ _
      (isConnected_univ.prod (isConnected_setOfPred_sameRay_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _ (by fun_prop)
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s := by
      refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
      all_goals
        simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp ⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair _ _ _))
      · exact hq
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hsp : forall p : P × P × P, p in s -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
      intro p hp
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp ⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_ofPred] at hv ⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_sameRay (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q in line[Real, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
      refine affineIndependent_of_ne_of_mem_of_notMem_of_mem ?_ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affineSpan h).2 (collinear_pair _ _ _))) ?_
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine vadd_mem_of_mem_direction ?_ hq
        rw [direction_affineSpan]
        exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₁, left_mem_affineSpan_pair Real _ _⟩, p₂ -ᵥ p₁⟩,
        ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, ?_⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) in s := by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_ofPred, Set.mem_univ, true_and,
        Prod.ext_iff]
      refine ⟨⟨⟨p₃, hc.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩, p₄ -ᵥ p₃⟩,
        ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, ?_⟩
      simp
    convert! Real.Angle.sign_eq_of_continuousOn hco hf hsp hp₃p₄s hp₁p₂s

/--
theorem `_root_.Sbtw.oangle_sign_eq` / 定理 `_root_.Sbtw.oangle_sign_eq`

English:
theorem _root_.Sbtw.oangle_sign_eq
  given: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃)
  proof: haveI hc : Collinear Real ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
  hc.oangle_sign_of_sameRay_vsub _ h.left_ne h.ne_right h.wbtw.sameRay_vsub

中文:
定理 _root_.Sbtw.oangle_sign_eq
  条件: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw 实数 p₁ p₂ p₃)
  证明: haveI hc : Collinear Real ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
  hc.oangle_sign_of_sameRay_vsub _ h.left_ne h.ne_right h.wbtw.sameRay_vsub

Depends on / 依赖: Collinear, collinear, h.left_ne, h.ne_right, h.wbtw.collinear, h.wbtw.sameRay_vsub, hc.oangle_sign_of_sameRay_vsub, left_ne, ne_right, oangle_sign_of_sameRay_vsub, sameRay_vsub
-/
theorem _root_.Sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
  haveI hc : Collinear Real ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
  hc.oangle_sign_of_sameRay_vsub _ h.left_ne h.ne_right h.wbtw.sameRay_vsub

/--
theorem `_root_.Wbtw.oangle_sign_eq_of_ne_left` / 定理 `_root_.Wbtw.oangle_sign_eq_of_ne_left`

English:
theorem _root_.Wbtw.oangle_sign_eq_of_ne_left
  statement: {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw Real p₁ p₂ p₃)
  proof: haveI hc : Collinear Real ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
  hc.oangle_sign_of_sameRay_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.sameRay_vsub_left

中文:
定理 _root_.Wbtw.oangle_sign_eq_of_ne_left
  结论: {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw 实数 p₁ p₂ p₃)
  证明: haveI hc : Collinear Real ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
  hc.oangle_sign_of_sameRay_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.sameRay_vsub_left

Depends on / 依赖: Collinear, Set.insert_comm, collinear, h.collinear, h.left_ne_right_of_ne_left, h.sameRay_vsub_left, hc.oangle_sign_of_sameRay_vsub, hne.symm, insert_comm, left_ne_right_of_ne_left, oangle_sign_of_sameRay_vsub, sameRay_vsub_left
-/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw Real p₁ p₂ p₃)
    (hne : p₁ != p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  haveI hc : Collinear Real ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
  hc.oangle_sign_of_sameRay_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.sameRay_vsub_left

/--
theorem `_root_.Sbtw.oangle_sign_eq_left` / 定理 `_root_.Sbtw.oangle_sign_eq_left`

English:
theorem _root_.Sbtw.oangle_sign_eq_left
  given: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃)
  proof: h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

中文:
定理 _root_.Sbtw.oangle_sign_eq_left
  条件: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw 实数 p₁ p₂ p₃)
  证明: h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

Depends on / 依赖: h.left_ne, h.wbtw.oangle_sign_eq_of_ne_left, left_ne, oangle_sign_eq_of_ne_left
-/
theorem _root_.Sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

/--
theorem `_root_.Wbtw.oangle_sign_eq_of_ne_right` / 定理 `_root_.Wbtw.oangle_sign_eq_of_ne_right`

English:
theorem _root_.Wbtw.oangle_sign_eq_of_ne_right
  statement: {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw Real p₁ p₂ p₃)
  proof: by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

中文:
定理 _root_.Wbtw.oangle_sign_eq_of_ne_right
  结论: {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw 实数 p₁ p₂ p₃)
  证明: by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

Depends on / 依赖: Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left, hne.symm, oangle_rev, oangle_sign_eq_of_ne_left, sign_neg, simp_rw
-/
theorem _root_.Wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw Real p₁ p₂ p₃)
    (hne : p₂ != p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign := by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

/--
theorem `_root_.Sbtw.oangle_sign_eq_right` / 定理 `_root_.Sbtw.oangle_sign_eq_right`

English:
theorem _root_.Sbtw.oangle_sign_eq_right
  given: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃)
  proof: h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

中文:
定理 _root_.Sbtw.oangle_sign_eq_right
  条件: {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw 实数 p₁ p₂ p₃)
  证明: h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

Depends on / 依赖: h.ne_right, h.wbtw.oangle_sign_eq_of_ne_right, ne_right, oangle_sign_eq_of_ne_right
-/
theorem _root_.Sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw Real p₁ p₂ p₃) :
    (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
  h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

/--
theorem `_root_.Sbtw.oangle_sign_eq_of_sbtw` / 定理 `_root_.Sbtw.oangle_sign_eq_of_sbtw`

English:
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw
  statement: {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw Real p₁ p p₃)
  proof: by
  rw [← Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq _ hp₁₃]; rw [← oangle_rotate_sign]; rw [Sbtw.oangle_sign_eq _ hp₂₄.symm]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

中文:
定理 _root_.Sbtw.oangle_sign_eq_of_sbtw
  结论: {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw 实数 p₁ p p₃)
  证明: by
  rw [← Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq _ hp₁₃]; rw [← oangle_rotate_sign]; rw [Sbtw.oangle_sign_eq _ hp₂₄.symm]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

Depends on / 依赖: Sbtw.oangle_eq_left, Sbtw.oangle_eq_right, Sbtw.oangle_sign_eq, oangle_eq_left, oangle_eq_right, oangle_rotate_sign, oangle_sign_eq
-/
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw Real p₁ p p₃)
    (hp₂₄ : Sbtw Real p₂ p p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [← Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq _ hp₁₃]; rw [← oangle_rotate_sign]; rw [Sbtw.oangle_sign_eq _ hp₂₄.symm]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

/--
theorem `_root_.Sbtw.oangle_sign_eq_of_sbtw_left` / 定理 `_root_.Sbtw.oangle_sign_eq_of_sbtw_left`

English:
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw_left
  statement: {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw Real p p₁ p₃)
  proof: by
  rw [Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq_right _ hp₁₃.symm]; rw [oangle_rotate_sign]; rw [← Sbtw.oangle_sign_eq_left p₃ hp₂₄]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

中文:
定理 _root_.Sbtw.oangle_sign_eq_of_sbtw_left
  结论: {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw 实数 p p₁ p₃)
  证明: by
  rw [Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq_right _ hp₁₃.symm]; rw [oangle_rotate_sign]; rw [← Sbtw.oangle_sign_eq_left p₃ hp₂₄]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

Depends on / 依赖: Sbtw.oangle_eq_left, Sbtw.oangle_eq_right, Sbtw.oangle_sign_eq_left, Sbtw.oangle_sign_eq_right, oangle_eq_left, oangle_eq_right, oangle_rotate_sign, oangle_sign_eq_left, oangle_sign_eq_right
-/
theorem _root_.Sbtw.oangle_sign_eq_of_sbtw_left {p p₁ p₂ p₃ p₄ : P} (hp₁₃ : Sbtw Real p p₁ p₃)
    (hp₂₄ : Sbtw Real p p₂ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  rw [Sbtw.oangle_eq_right hp₂₄.symm]; rw [Sbtw.oangle_sign_eq_right _ hp₁₃.symm]; rw [oangle_rotate_sign]; rw [← Sbtw.oangle_sign_eq_left p₃ hp₂₄]; rw [Sbtw.oangle_eq_left hp₁₃.symm]

/--
theorem `_root_.AffineSubspace.SSameSide.oangle_sign_eq` / 定理 `_root_.AffineSubspace.SSameSide.oangle_sign_eq`

English:
theorem _root_.AffineSubspace.SSameSide.oangle_sign_eq
  statement: {s : AffineSubspace Real P} {p₁ p₂ p₃ p₄ : P}
  proof: by
  by_cases h : p₁ = p₂; · simp [h]
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' {p | s.SSameSide p₃ p}
  have hc : IsConnected sp :=
    (isConnected_setOfPred_sSameSide hp₃p₄.2.1 hp₃p₄.nonempty).image _ (by fun_prop)
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp := by
    refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : forall p : P × P × P, p in sp -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
    intro p hp
    simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
    exact affineIndependent_of_ne_of_mem_of_notMem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) in sp :=
    Set.mem_image_of_mem _ (sSameSide_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) in sp := Set.mem_image_of_mem _ hp₃p₄
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hsp hp₃ hp₄

中文:
定理 _root_.仿射子空间.SSameSide.oangle_sign_eq
  结论: {s : 仿射子空间 实数 P} {p₁ p₂ p₃ p₄ : P}
  证明: by
  by_cases h : p₁ = p₂; · simp [h]
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' {p | s.SSameSide p₃ p}
  have hc : IsConnected sp :=
    (isConnected_setOfPred_sSameSide hp₃p₄.2.1 hp₃p₄.nonempty).image _ (by fun_prop)
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp := by
    refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : forall p : P × P × P, p in sp -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
    intro p hp
    simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
    exact affineIndependent_of_ne_of_mem_of_notMem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) in sp :=
    Set.mem_image_of_mem _ (sSameSide_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) in sp := Set.mem_image_of_mem _ hp₃p₄
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hsp hp₃ hp₄

Depends on / 依赖: ContinuousOn, IsConnected, SSameSide, Set.mem_image, Set.mem_ofPred, all_goals, continuousAt_oangle, continuousOn_of_forall_continuousAt, fun_prop, isConnected_setOfPred_sSameSide, mem_image, mem_ofPred, nonempty, s.SSameSide, simp_rw
-/
theorem _root_.AffineSubspace.SSameSide.oangle_sign_eq {s : AffineSubspace Real P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃p₄ : s.SSameSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign := by
  by_cases h : p₁ = p₂; · simp [h]
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' {p | s.SSameSide p₃ p}
  have hc : IsConnected sp :=
    (isConnected_setOfPred_sSameSide hp₃p₄.2.1 hp₃p₄.nonempty).image _ (by fun_prop)
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp := by
    refine continuousOn_of_forall_continuousAt fun p hp => continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : forall p : P × P × P, p in sp -> ∡ p.1 p.2.1 p.2.2 != 0 ∧ ∡ p.1 p.2.1 p.2.2 != π := by
    intro p hp
    simp_rw [sp, Set.mem_image, Set.mem_ofPred] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affineIndependent]
    exact affineIndependent_of_ne_of_mem_of_notMem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) in sp :=
    Set.mem_image_of_mem _ (sSameSide_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) in sp := Set.mem_image_of_mem _ hp₃p₄
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hsp hp₃ hp₄

/--
theorem `_root_.AffineSubspace.SOppSide.oangle_sign_eq_neg` / 定理 `_root_.AffineSubspace.SOppSide.oangle_sign_eq_neg`

English:
theorem _root_.AffineSubspace.SOppSide.oangle_sign_eq_neg
  statement: {s : AffineSubspace Real P} {p₁ p₂ p₃ p₄ : P}
  proof: by
  have hp₁p₃ : p₁ != p₃ := by rintro rfl; exact hp₃p₄.left_notMem hp₁
  rw [← (hp₃p₄.symm.trans (sOppSide_pointReflection hp₁ hp₃p₄.left_notMem)).oangle_sign_eq hp₁ hp₂]; rw [← oangle_rotate_sign p₁]; rw [← oangle_rotate_sign p₁]; rw [oangle_swap₁₃_sign]; rw [(sbtw_pointReflection_of_ne Real hp₁p₃).symm.oangle_sign_eq _]

中文:
定理 _root_.仿射子空间.SOppSide.oangle_sign_eq_neg
  结论: {s : 仿射子空间 实数 P} {p₁ p₂ p₃ p₄ : P}
  证明: by
  have hp₁p₃ : p₁ != p₃ := by rintro rfl; exact hp₃p₄.left_notMem hp₁
  rw [← (hp₃p₄.symm.trans (sOppSide_pointReflection hp₁ hp₃p₄.left_notMem)).oangle_sign_eq hp₁ hp₂]; rw [← oangle_rotate_sign p₁]; rw [← oangle_rotate_sign p₁]; rw [oangle_swap₁₃_sign]; rw [(sbtw_pointReflection_of_ne Real hp₁p₃).symm.oangle_sign_eq _]

Depends on / 依赖: left_notMem, oangle_rotate_sign, oangle_sign_eq, sOppSide_pointReflection, sbtw_pointReflection_of_ne, symm.oangle_sign_eq, symm.trans
-/
theorem _root_.AffineSubspace.SOppSide.oangle_sign_eq_neg {s : AffineSubspace Real P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃p₄ : s.SOppSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign := by
  have hp₁p₃ : p₁ != p₃ := by rintro rfl; exact hp₃p₄.left_notMem hp₁
  rw [← (hp₃p₄.symm.trans (sOppSide_pointReflection hp₁ hp₃p₄.left_notMem)).oangle_sign_eq hp₁ hp₂]; rw [← oangle_rotate_sign p₁]; rw [← oangle_rotate_sign p₁]; rw [oangle_swap₁₃_sign]; rw [(sbtw_pointReflection_of_ne Real hp₁p₃).symm.oangle_sign_eq _]

/--
lemma `angle_eq_iff_oangle_eq_or_wbtw` / 引理 `angle_eq_iff_oangle_eq_or_wbtw`

English:
lemma angle_eq_iff_oangle_eq_or_wbtw
  given: {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p₄ != p₂)
  proof: by
  simp_rw [angle, oangle,
    o.angle_eq_iff_oangle_eq_or_sameRay (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)]
  apply or_congr_right
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, hr, he⟩ := h.exists_pos_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)
    rw [← vsub_vadd p₁ p₂]; rw [← vsub_vadd p₄ p₂]; rw [← he]
    nth_rw 1 4 [← one_smul Real (p₁ -ᵥ p₂)]
    exact wbtw_or_wbtw_smul_vadd_of_nonneg _ _ zero_le_one hr.le
  · rcases h with h | h
    · exact h.sameRay_vsub_left
    · exact h.sameRay_vsub_left.symm

中文:
引理 angle_eq_iff_oangle_eq_or_wbtw
  条件: {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p₄ != p₂)
  证明: by
  simp_rw [angle, oangle,
    o.angle_eq_iff_oangle_eq_or_sameRay (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)]
  apply or_congr_right
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, hr, he⟩ := h.exists_pos_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)
    rw [← vsub_vadd p₁ p₂]; rw [← vsub_vadd p₄ p₂]; rw [← he]
    nth_rw 1 4 [← one_smul Real (p₁ -ᵥ p₂)]
    exact wbtw_or_wbtw_smul_vadd_of_nonneg _ _ zero_le_one hr.le
  · rcases h with h | h
    · exact h.sameRay_vsub_left
    · exact h.sameRay_vsub_left.symm

Depends on / 依赖: angle_eq_iff_oangle_eq_or_sameRay, exists_pos_left, h.exists_pos_left, h.sameRay_vsub_left, h.sameRay_vsub_left.symm, hr.le, nth_rw, o.angle_eq_iff_oangle_eq_or_sameRay, oangle, one_smul, or_congr_right, sameRay_vsub_left, simp_rw, vsub_ne_zero, vsub_vadd, wbtw_or_wbtw_smul_vadd_of_nonneg, zero_le_one
-/
lemma angle_eq_iff_oangle_eq_or_wbtw {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ != p₂) (hp₄ : p₄ != p₂) :
    ∠ p₁ p₂ p₃ = ∠ p₃ p₂ p₄ ↔ ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ ∨ Wbtw Real p₂ p₁ p₄ ∨ Wbtw Real p₂ p₄ p₁ := by
  simp_rw [angle, oangle,
    o.angle_eq_iff_oangle_eq_or_sameRay (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)]
  apply or_congr_right
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨r, hr, he⟩ := h.exists_pos_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₄)
    rw [← vsub_vadd p₁ p₂]; rw [← vsub_vadd p₄ p₂]; rw [← he]
    nth_rw 1 4 [← one_smul Real (p₁ -ᵥ p₂)]
    exact wbtw_or_wbtw_smul_vadd_of_nonneg _ _ zero_le_one hr.le
  · rcases h with h | h
    · exact h.sameRay_vsub_left
    · exact h.sameRay_vsub_left.symm

/--
lemma `angle_eq_angle_div_two_of_oangle_eq_of_sSameSide` / 引理 `angle_eq_angle_div_two_of_oangle_eq_of_sSameSide`

English:
lemma angle_eq_angle_div_two_of_oangle_eq_of_sSameSide
  statement: {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
  proof: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  suffices ((∡ p₁ p₂ p₃).toReal + (∡ p₃ p₂ p₄).toReal) / 2 = (∡ p₁ p₂ p₄).toReal / 2 by
    rw [← ha]; rw [add_self_div_two] at this
    rw [angle_eq_abs_oangle_toReal h₁₂ h₃₂]; rw [angle_eq_abs_oangle_toReal h₁₂ h₄₂]; rw [this]; rw [abs_div]
    simp
  have hadd := oangle_add h₁₂ h₃₂ h₄₂
  rw [div_left_inj' (by norm_num)]; rw [← hadd]
  have h : ∡ p₁ p₂ p₃ != π := fun h => hs.left_notMem ((oangle_eq_zero_or_eq_pi_iff_collinear.1
    (.inr h)).mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) h₁₂)
  refine (Real.Angle.toReal_add_eq_toReal_add_toReal h (ha ▸ h) (.inr ?_)).symm
  rw [hadd]; rw [← oangle_swap₂₃_sign p₁ p₃ p₂]; rw [← oangle_swap₂₃_sign p₁ p₄ p₂]; rw [neg_inj]; rw [eq_comm]
  exact hs.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

中文:
引理 angle_eq_angle_div_two_of_oangle_eq_of_sSameSide
  结论: {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
  证明: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  suffices ((∡ p₁ p₂ p₃).toReal + (∡ p₃ p₂ p₄).toReal) / 2 = (∡ p₁ p₂ p₄).toReal / 2 by
    rw [← ha]; rw [add_self_div_two] at this
    rw [angle_eq_abs_oangle_toReal h₁₂ h₃₂]; rw [angle_eq_abs_oangle_toReal h₁₂ h₄₂]; rw [this]; rw [abs_div]
    simp
  have hadd := oangle_add h₁₂ h₃₂ h₄₂
  rw [div_left_inj' (by norm_num)]; rw [← hadd]
  have h : ∡ p₁ p₂ p₃ != π := fun h => hs.left_notMem ((oangle_eq_zero_or_eq_pi_iff_collinear.1
    (.inr h)).mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) h₁₂)
  refine (Real.Angle.toReal_add_eq_toReal_add_toReal h (ha ▸ h) (.inr ?_)).symm
  rw [hadd]; rw [← oangle_swap₂₃_sign p₁ p₃ p₂]; rw [← oangle_swap₂₃_sign p₁ p₄ p₂]; rw [neg_inj]; rw [eq_comm]
  exact hs.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

Depends on / 依赖: abs_div, add_self_div_two, angle_eq_abs_oangle_toReal, div_left_inj, hs.left_notMem, hs.right_notMem, left_notMem, oangle_add, right_mem_affineSpan_pair, right_notMem, toReal
-/
lemma angle_eq_angle_div_two_of_oangle_eq_of_sSameSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
    (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].SSameSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₂ p₄ / 2 := by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  suffices ((∡ p₁ p₂ p₃).toReal + (∡ p₃ p₂ p₄).toReal) / 2 = (∡ p₁ p₂ p₄).toReal / 2 by
    rw [← ha]; rw [add_self_div_two] at this
    rw [angle_eq_abs_oangle_toReal h₁₂ h₃₂]; rw [angle_eq_abs_oangle_toReal h₁₂ h₄₂]; rw [this]; rw [abs_div]
    simp
  have hadd := oangle_add h₁₂ h₃₂ h₄₂
  rw [div_left_inj' (by norm_num)]; rw [← hadd]
  have h : ∡ p₁ p₂ p₃ != π := fun h => hs.left_notMem ((oangle_eq_zero_or_eq_pi_iff_collinear.1
    (.inr h)).mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) h₁₂)
  refine (Real.Angle.toReal_add_eq_toReal_add_toReal h (ha ▸ h) (.inr ?_)).symm
  rw [hadd]; rw [← oangle_swap₂₃_sign p₁ p₃ p₂]; rw [← oangle_swap₂₃_sign p₁ p₄ p₂]; rw [neg_inj]; rw [eq_comm]
  exact hs.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

/--
lemma `angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide` / 引理 `angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide`

English:
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide
  statement: {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
  proof: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) =
      ∡ (AffineEquiv.pointReflection Real p₂ p₃) p₂ p₄ := by
    rw [oangle_pointReflection_left h₃₂ h₄₂]; rw [oangle_pointReflection_right h₁₂ h₃₂]
    simpa using ha
  have hs' : line[Real, p₁, p₂].SOppSide p₃ (AffineEquiv.pointReflection Real p₂ p₃) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.left_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs'.symm.trans hs)
  rw [angle_pointReflection_right] at h
  linear_combination -h

中文:
引理 angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide
  结论: {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
  证明: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) =
      ∡ (AffineEquiv.pointReflection Real p₂ p₃) p₂ p₄ := by
    rw [oangle_pointReflection_left h₃₂ h₄₂]; rw [oangle_pointReflection_right h₁₂ h₃₂]
    simpa using ha
  have hs' : line[Real, p₁, p₂].SOppSide p₃ (AffineEquiv.pointReflection Real p₂ p₃) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.left_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs'.symm.trans hs)
  rw [angle_pointReflection_right] at h
  linear_combination -h

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection, AffineSubs, SOppSide, hs.left_notMem, hs.right_notMem, left_notMem, oangle_pointReflection_left, oangle_pointReflection_right, pointReflection, right_mem_affineSpan_pair, right_notMem
-/
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide {p₁ p₂ p₃ p₄ : P} (h₁₂ : p₁ != p₂)
    (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄) (hs : line[Real, p₁, p₂].SOppSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = π - ∠ p₁ p₂ p₄ / 2 := by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ (AffineEquiv.pointReflection Real p₂ p₃) =
      ∡ (AffineEquiv.pointReflection Real p₂ p₃) p₂ p₄ := by
    rw [oangle_pointReflection_left h₃₂ h₄₂]; rw [oangle_pointReflection_right h₁₂ h₃₂]
    simpa using ha
  have hs' : line[Real, p₁, p₂].SOppSide p₃ (AffineEquiv.pointReflection Real p₂ p₃) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.left_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs'.symm.trans hs)
  rw [angle_pointReflection_right] at h
  linear_combination -h

/--
lemma `angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide` / 引理 `angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide`

English:
lemma angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide h₁₂ ha' (hs.trans_sOppSide hs')
  rw [angle_pointReflection_right] at h
  linear_combination h

中文:
引理 angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide h₁₂ ha' (hs.trans_sOppSide hs')
  rw [angle_pointReflection_right] at h
  linear_combination h

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection, AffineSubspace, AffineSubspace.sOppSide_pointReflection, SOppSide, hs.left_notMem, hs.right_notMem, left_notMem, oangle_pointReflection_right, pointReflection, right_mem_affineSpan_pair, right_notMem, sOppSide_pointReflection
-/
lemma angle_eq_angle_add_pi_div_two_of_oangle_eq_add_pi_of_sSameSide {p₁ p₂ p₃ p₄ : P}
    (h₁₂ : p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[Real, p₁, p₂].SSameSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = (∠ p₁ p₂ p₄ + π) / 2 := by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_pi_sub_angle_div_two_of_oangle_eq_of_sOppSide h₁₂ ha' (hs.trans_sOppSide hs')
  rw [angle_pointReflection_right] at h
  linear_combination h

/--
lemma `angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide` / 引理 `angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide`

English:
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide
  statement: {p₁ p₂ p₃ p₄ : P}
  proof: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs.trans hs')
  rw [angle_pointReflection_right] at h
  exact h

中文:
引理 angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide
  结论: {p₁ p₂ p₃ p₄ : P}
  证明: by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs.trans hs')
  rw [angle_pointReflection_right] at h
  exact h

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection, AffineSubspace, AffineSubspace.sOppSide_pointReflection, SOppSide, hs.left_notMem, hs.right_notMem, left_notMem, oangle_pointReflection_right, pointReflection, right_mem_affineSpan_pair, right_notMem, sOppSide_pointReflection
-/
lemma angle_eq_pi_sub_angle_div_two_of_oangle_eq_add_pi_of_sOppSide {p₁ p₂ p₃ p₄ : P}
    (h₁₂ : p₁ != p₂) (ha : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ p₄ + π) (hs : line[Real, p₁, p₂].SOppSide p₃ p₄) :
    ∠ p₁ p₂ p₃ = (π - ∠ p₁ p₂ p₄) / 2 := by
  have h₃₂ : p₃ != p₂ := by
    rintro rfl
    exact hs.left_notMem (right_mem_affineSpan_pair _ _ _)
  have h₄₂ : p₄ != p₂ := by
    rintro rfl
    exact hs.right_notMem (right_mem_affineSpan_pair _ _ _)
  have ha' : ∡ p₁ p₂ p₃ = ∡ p₃ p₂ (AffineEquiv.pointReflection Real p₂ p₄) := by
    rw [oangle_pointReflection_right h₃₂ h₄₂]
    exact ha
  have hs' : line[Real, p₁, p₂].SOppSide p₄ (AffineEquiv.pointReflection Real p₂ p₄) :=
    AffineSubspace.sOppSide_pointReflection (right_mem_affineSpan_pair _ _ _) (hs.right_notMem)
  obtain h := angle_eq_angle_div_two_of_oangle_eq_of_sSameSide h₁₂ ha' (hs.trans hs')
  rw [angle_pointReflection_right] at h
  exact h

end EuclideanGeometry
