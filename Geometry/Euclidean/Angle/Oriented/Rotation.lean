/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

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

local notation "J" => o.rightAngleRotation

/--
Definition of `rotationAux` / `rotationAux` 的定义

English:
definition rotationAux
  signature: (θ : Real.Angle)
  body: LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, Lin

中文:
定义 rotationAux
  签名: (θ : 实数.Angle)
  定义体: LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, Lin

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearIsometryEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.toLinearEquiv, LinearMap, LinearMap.add_apply, LinearMap.id, LinearMap.id_coe, LinearMap.isometryOfInner, LinearMap.smul_apply, Orientation, Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left, Orientation.inner_rightAngleRotation_right, RCLike, RCLike.conj_to_real, Real.Angle.cos, Real.Angle.sin, add_apply
-/
def rotationAux (θ : Real.Angle) : V ->ₗᵢ[Real] V :=
  LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination ⟪x, y⟫ * θ.cos_sq_add_sin_sq)

@[simp]
/--
theorem `rotationAux_apply` / 定理 `rotationAux_apply`

English:
theorem rotationAux_apply
  given: (θ : Real.Angle) (x : V)
  proof: rfl

中文:
定理 rotationAux_apply
  条件: (θ : 实数.Angle) (x : V)
  证明: rfl
-/
theorem rotationAux_apply (θ : Real.Angle) (x : V) :
    o.rotationAux θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

/--
Definition of `rotation` / `rotation` 的定义

English:
definition rotation
  signature: (θ : Real.Angle)
  body: LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert! congr_arg (fun t : Real => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRo

中文:
定义 rotation
  签名: (θ : 实数.Angle)
  定义体: LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert! congr_arg (fun t : Real => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRo

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearIsometry, LinearIsometry.coe_toLinearMap, LinearIsometryEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.ofLinearIsometry, LinearIsometryEquiv.toLinearEquiv, LinearMap, LinearMap.coe_comp, LinearMap.id, LinearMap.id_coe, Real.Angle.cos, Real.Angle.sin, coe_coe, coe_comp, coe_toLinearEquiv, coe_toLinearMap
-/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[Real] V :=
  LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert! congr_arg (fun t : Real => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_smul, map_sub, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)
    (by
      ext x
      convert! congr_arg (fun t : Real => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_add, map_smul, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)

/--
theorem `rotation_apply` / 定理 `rotation_apply`

English:
theorem rotation_apply
  given: (θ : Real.Angle) (x : V)
  proof: rfl

中文:
定理 rotation_apply
  条件: (θ : 实数.Angle) (x : V)
  证明: rfl
-/
theorem rotation_apply (θ : Real.Angle) (x : V) :
    o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

/--
theorem `rotation_symm_apply` / 定理 `rotation_symm_apply`

English:
theorem rotation_symm_apply
  given: (θ : Real.Angle) (x : V)
  proof: rfl

中文:
定理 rotation_symm_apply
  条件: (θ : 实数.Angle) (x : V)
  证明: rfl
-/
theorem rotation_symm_apply (θ : Real.Angle) (x : V) :
    (o.rotation θ).symm x = Real.Angle.cos θ • x - Real.Angle.sin θ • J x :=
  rfl

/--
theorem `rotation_eq_matrix_toLin` / 定理 `rotation_eq_matrix_toLin`

English:
theorem rotation_eq_matrix_toLin
  given: (θ : Real.Angle) {x : V} (hx : x != 0)
  proof: by
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  fin_cases i
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ]
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]

中文:
定理 rotation_eq_matrix_toLin
  条件: (θ : 实数.Angle) {x : V} (hx : x != 0)
  证明: by
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  fin_cases i
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ]
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]

Depends on / 依赖: Fin.sum_univ_succ, Matrix, Matrix.toLin_self, add_comm, basisRightAngleRotation, fin_cases, o.basisRightAngleRotation, rotation_apply, sum_univ_succ, toLin_self
-/
theorem rotation_eq_matrix_toLin (θ : Real.Angle) {x : V} (hx : x != 0) :
    (o.rotation θ).toLinearMap =
      Matrix.toLin (o.basisRightAngleRotation x hx) (o.basisRightAngleRotation x hx)
        !![θ.cos, -θ.sin; θ.sin, θ.cos] := by
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  fin_cases i
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ]
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
/--
theorem `det_rotation` / 定理 `det_rotation`

English:
theorem det_rotation
  given: (θ : Real.Angle)
  statement: LinearMap.det (o.rotation θ).toLinearMap = 1
  proof: by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

中文:
定理 det_rotation
  条件: (θ : 实数.Angle)
  结论: 线性映射.det (o.rotation θ).toLinearMap = 1
  证明: by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

Depends on / 依赖: Fact.out, Nontrivial, cos_sq_add_sin_sq, exists_ne, finrank, nontrivial_of_finrank_eq_succ, o.rotation_eq_matrix_toLin, rotation_eq_matrix_toLin
-/
theorem det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap = 1 := by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
/--
theorem `linearEquiv_det_rotation` / 定理 `linearEquiv_det_rotation`

English:
theorem linearEquiv_det_rotation
  given: (θ : Real.Angle)
  proof: Units.ext by
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

中文:
定理 linearEquiv_det_rotation
  条件: (θ : 实数.Angle)
  证明: Units.ext by
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_det, Units.ext, Units.val_one, coe_det, det_rotation, o.det_rotation, val_one
-/
theorem linearEquiv_det_rotation (θ : Real.Angle) :
    LinearEquiv.det (o.rotation θ).toLinearEquiv = 1 :=
Units.ext by
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
/--
theorem `rotation_symm` / 定理 `rotation_symm`

English:
theorem rotation_symm
  given: (θ : Real.Angle)
  statement: (o.rotation θ).symm = o.rotation (-θ)
  proof: by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

中文:
定理 rotation_symm
  条件: (θ : 实数.Angle)
  结论: (o.rotation θ).symm = o.rotation (-θ)
  证明: by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

Depends on / 依赖: o.rotation_apply, o.rotation_symm_apply, rotation_apply, rotation_symm_apply, sub_eq_add_neg
-/
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) := by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

/-- Rotation by 0 is the identity. -/
@[simp]
/--
theorem `rotation_zero` / 定理 `rotation_zero`

English:
theorem rotation_zero
  statement: o.rotation 0 = LinearIsometryEquiv.refl Real V
  proof: by ext; simp [rotation]

中文:
定理 rotation_zero
  结论: o.rotation 0 = 线性等距等价.refl 实数 V
  证明: by ext; simp [rotation]

Depends on / 依赖: rotation
-/
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl Real V := by ext; simp [rotation]

/-- Rotation by π is negation. -/
@[simp]
/--
theorem `rotation_pi` / 定理 `rotation_pi`

English:
theorem rotation_pi
  statement: o.rotation π = LinearIsometryEquiv.neg Real
  proof: by
  ext x
  simp [rotation]

中文:
定理 rotation_pi
  结论: o.rotation π = 线性等距等价.neg 实数
  证明: by
  ext x
  simp [rotation]

Depends on / 依赖: rotation
-/
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg Real := by
  ext x
  simp [rotation]

/--
theorem `rotation_pi_apply` / 定理 `rotation_pi_apply`

English:
theorem rotation_pi_apply
  given: (x : V)
  statement: o.rotation π x = -x
  proof: by simp

中文:
定理 rotation_pi_apply
  条件: (x : V)
  结论: o.rotation π x = -x
  证明: by simp
-/
theorem rotation_pi_apply (x : V) : o.rotation π x = -x := by simp

/--
theorem `rotation_pi_div_two` / 定理 `rotation_pi_div_two`

English:
theorem rotation_pi_div_two
  statement: o.rotation (π / 2 : Real) = J
  proof: by
  ext x
  simp [rotation]

中文:
定理 rotation_pi_div_two
  结论: o.rotation (π / 2 : 实数) = J
  证明: by
  ext x
  simp [rotation]

Depends on / 依赖: rotation
-/
theorem rotation_pi_div_two : o.rotation (π / 2 : Real) = J := by
  ext x
  simp [rotation]

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
/--
theorem `rotation_rotation` / 定理 `rotation_rotation`

English:
theorem rotation_rotation
  given: (θ₁ θ₂ : Real.Angle) (x : V)
  proof: by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, map_add,
    map_smul, rightAngleRotation_rightAngleRotation]
  module

中文:
定理 rotation_rotation
  条件: (θ₁ θ₂ : 实数.Angle) (x : V)
  证明: by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, map_add,
    map_smul, rightAngleRotation_rightAngleRotation]
  module

Depends on / 依赖: Real.Angle.cos_add, Real.Angle.sin_add, cos_add, map_add, map_smul, module, o.rotation_apply, rightAngleRotation_rightAngleRotation, rotation_apply, sin_add
-/
theorem rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) :
    o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x := by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, map_add,
    map_smul, rightAngleRotation_rightAngleRotation]
  module

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
/--
theorem `rotation_trans` / 定理 `rotation_trans`

English:
theorem rotation_trans
  given: (θ₁ θ₂ : Real.Angle)
  proof: LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

中文:
定理 rotation_trans
  条件: (θ₁ θ₂ : 实数.Angle)
  证明: LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, LinearIsometryEquiv.trans_apply, rotation_rotation, trans_apply
-/
theorem rotation_trans (θ₁ θ₂ : Real.Angle) :
    (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

/-- Rotating the first of two vectors by `θ` scales their Kähler form by `cos θ - sin θ * I`. -/
@[simp]
/--
theorem `kahler_rotation_left` / 定理 `kahler_rotation_left`

English:
theorem kahler_rotation_left
  given: (x y : V) (θ : Real.Angle)
  proof: by
  simp only [o.rotation_apply, map_add, map_mul, map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

中文:
定理 kahler_rotation_left
  条件: (x y : V) (θ : 实数.Angle)
  证明: by
  simp only [o.rotation_apply, map_add, map_mul, map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

Depends on / 依赖: Complex.conj_ofReal, LinearMap, LinearMap.add_apply, LinearMap.smul_apply, Real.Angle.coe_toCircle, RingHom, RingHom.id_apply, add_apply, coe_toCircle, conj_I, conj_ofReal, id_apply, kahler_rightAngleRotation_left, map_add, map_mul, o.rotation_apply, real_smul, rotation_apply, smul_apply
-/
theorem kahler_rotation_left (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = conj (θ.toCircle : Complex) * o.kahler x y := by
  simp only [o.rotation_apply, map_add, map_mul, map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

/--
theorem `neg_rotation` / 定理 `neg_rotation`

English:
theorem neg_rotation
  given: (θ : Real.Angle) (x : V)
  statement: -o.rotation θ x = o.rotation (π + θ) x
  proof: by
  rw [← o.rotation_pi_apply]; rw [rotation_rotation]

中文:
定理 neg_rotation
  条件: (θ : 实数.Angle) (x : V)
  结论: -o.rotation θ x = o.rotation (π + θ) x
  证明: by
  rw [← o.rotation_pi_apply]; rw [rotation_rotation]

Depends on / 依赖: o.rotation_pi_apply, rotation_pi_apply, rotation_rotation
-/
theorem neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x := by
  rw [← o.rotation_pi_apply]; rw [rotation_rotation]

/-- Negating a rotation by -π / 2 is equivalent to rotation by π / 2. -/
@[simp]
/--
theorem `neg_rotation_neg_pi_div_two` / 定理 `neg_rotation_neg_pi_div_two`

English:
theorem neg_rotation_neg_pi_div_two
  given: (x : V)
  proof: by
  rw [neg_rotation]; rw [← Real.Angle.coe_add]; rw [neg_div]; rw [← sub_eq_add_neg]; rw [sub_half]

中文:
定理 neg_rotation_neg_pi_div_two
  条件: (x : V)
  证明: by
  rw [neg_rotation]; rw [← Real.Angle.coe_add]; rw [neg_div]; rw [← sub_eq_add_neg]; rw [sub_half]

Depends on / 依赖: Real.Angle.coe_add, coe_add, neg_div, neg_rotation, sub_eq_add_neg, sub_half
-/
theorem neg_rotation_neg_pi_div_two (x : V) :
    -o.rotation (-π / 2 : Real) x = o.rotation (π / 2 : Real) x := by
  rw [neg_rotation]; rw [← Real.Angle.coe_add]; rw [neg_div]; rw [← sub_eq_add_neg]; rw [sub_half]

/--
theorem `neg_rotation_pi_div_two` / 定理 `neg_rotation_pi_div_two`

English:
theorem neg_rotation_pi_div_two
  given: (x : V)
  statement: -o.rotation (π / 2 : Real) x = o.rotation (-π / 2 : Real) x
  proof: (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

中文:
定理 neg_rotation_pi_div_two
  条件: (x : V)
  结论: -o.rotation (π / 2 : 实数) x = o.rotation (-π / 2 : 实数) x
  证明: (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

Depends on / 依赖: neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mp, neg_rotation_neg_pi_div_two, o.neg_rotation_neg_pi_div_two
-/
theorem neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : Real) x = o.rotation (-π / 2 : Real) x :=
  (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

/--
theorem `kahler_rotation_left'` / 定理 `kahler_rotation_left'`

English:
theorem kahler_rotation_left'
  given: (x y : V) (θ : Real.Angle)
  proof: by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

中文:
定理 kahler_rotation_left'
  条件: (x y : V) (θ : 实数.Angle)
  证明: by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

Depends on / 依赖: Circle, Circle.coe_inv_eq_conj, Real.Angle.toCircle_neg, coe_inv_eq_conj, kahler_rotation_left, toCircle_neg
-/
theorem kahler_rotation_left' (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = (-θ).toCircle * o.kahler x y := by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

/-- Rotating the second of two vectors by `θ` scales their Kähler form by `cos θ + sin θ * I`. -/
@[simp]
/--
theorem `kahler_rotation_right` / 定理 `kahler_rotation_right`

English:
theorem kahler_rotation_right
  given: (x y : V) (θ : Real.Angle)
  proof: by
  simp only [o.rotation_apply, map_add, map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

中文:
定理 kahler_rotation_right
  条件: (x y : V) (θ : 实数.Angle)
  证明: by
  simp only [o.rotation_apply, map_add, map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

Depends on / 依赖: Real.Angle.coe_toCircle, RingHom, RingHom.id_apply, coe_toCircle, id_apply, kahler_rightAngleRotation_right, map_add, o.rotation_apply, real_smul, rotation_apply
-/
theorem kahler_rotation_right (x y : V) (θ : Real.Angle) :
    o.kahler x (o.rotation θ y) = θ.toCircle * o.kahler x y := by
  simp only [o.rotation_apply, map_add, map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
/--
theorem `oangle_rotation_left` / 定理 `oangle_rotation_left`

English:
theorem oangle_rotation_left
  given: {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angle)
  proof: by
  simp only [oangle, o.kahler_rotation_left']
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

中文:
定理 oangle_rotation_left
  条件: {x y : V} (hx : x != 0) (hy : y != 0) (θ : 实数.Angle)
  证明: by
  simp only [oangle, o.kahler_rotation_left']
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

Depends on / 依赖: Circle, Circle.coe_ne_zero, Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle, arg_mul_coe_angle, arg_toCircle, coe_ne_zero, kahler_ne_zero, kahler_rotation_left, o.kahler_ne_zero, o.kahler_rotation_left, oangle
-/
theorem oangle_rotation_left {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) y = o.oangle x y - θ := by
  simp only [oangle, o.kahler_rotation_left']
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
/--
theorem `oangle_rotation_right` / 定理 `oangle_rotation_right`

English:
theorem oangle_rotation_right
  given: {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angle)
  proof: by
  simp only [oangle, o.kahler_rotation_right]
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

中文:
定理 oangle_rotation_right
  条件: {x y : V} (hx : x != 0) (hy : y != 0) (θ : 实数.Angle)
  证明: by
  simp only [oangle, o.kahler_rotation_right]
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

Depends on / 依赖: Circle, Circle.coe_ne_zero, Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle, arg_mul_coe_angle, arg_toCircle, coe_ne_zero, kahler_ne_zero, kahler_rotation_right, o.kahler_ne_zero, o.kahler_rotation_right, oangle
-/
theorem oangle_rotation_right {x y : V} (hx : x != 0) (hy : y != 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ y) = o.oangle x y + θ := by
  simp only [oangle, o.kahler_rotation_right]
  rw [Complex.arg_mul_coe_angle]; rw [Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/--
theorem `oangle_rotation_self_left` / 定理 `oangle_rotation_self_left`

English:
theorem oangle_rotation_self_left
  given: {x : V} (hx : x != 0) (θ : Real.Angle)
  proof: by simp [hx]

中文:
定理 oangle_rotation_self_left
  条件: {x : V} (hx : x != 0) (θ : 实数.Angle)
  证明: by simp [hx]
-/
theorem oangle_rotation_self_left {x : V} (hx : x != 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) x = -θ := by simp [hx]

/--
theorem `oangle_rotation_self_right` / 定理 `oangle_rotation_self_right`

English:
theorem oangle_rotation_self_right
  given: {x : V} (hx : x != 0) (θ : Real.Angle)
  proof: by simp [hx]

中文:
定理 oangle_rotation_self_right
  条件: {x : V} (hx : x != 0) (θ : 实数.Angle)
  证明: by simp [hx]
-/
theorem oangle_rotation_self_right {x : V} (hx : x != 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ x) = θ := by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results in an angle of 0. -/
@[simp]
/--
theorem `oangle_rotation_oangle_left` / 定理 `oangle_rotation_oangle_left`

English:
theorem oangle_rotation_oangle_left
  given: (x y : V)
  statement: o.oangle (o.rotation (o.oangle x y) x) y = 0
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]

中文:
定理 oangle_rotation_oangle_left
  条件: (x y : V)
  结论: o.oangle (o.rotation (o.oangle x y) x) y = 0
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]
-/
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results in an angle of 0. -/
@[simp]
/--
theorem `oangle_rotation_oangle_right` / 定理 `oangle_rotation_oangle_right`

English:
theorem oangle_rotation_oangle_right
  given: (x y : V)
  statement: o.oangle y (o.rotation (o.oangle x y) x) = 0
  proof: by
  rw [oangle_rev]
  simp

中文:
定理 oangle_rotation_oangle_right
  条件: (x y : V)
  结论: o.oangle y (o.rotation (o.oangle x y) x) = 0
  证明: by
  rw [oangle_rev]
  simp

Depends on / 依赖: oangle_rev
-/
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 := by
  rw [oangle_rev]
  simp

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
/--
theorem `oangle_rotation` / 定理 `oangle_rotation`

English:
theorem oangle_rotation
  given: (x y : V) (θ : Real.Angle)
  proof: by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

中文:
定理 oangle_rotation
  条件: (x y : V) (θ : 实数.Angle)
  证明: by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
-/
theorem oangle_rotation (x y : V) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
/--
theorem `rotation_eq_self_iff_angle_eq_zero` / 定理 `rotation_eq_self_iff_angle_eq_zero`

English:
theorem rotation_eq_self_iff_angle_eq_zero
  given: {x : V} (hx : x != 0) (θ : Real.Angle)
  proof: by
  constructor
  · intro h
    rw [eq_comm]
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
  · intro h
    simp [h]

中文:
定理 rotation_eq_self_iff_angle_eq_zero
  条件: {x : V} (hx : x != 0) (θ : 实数.Angle)
  证明: by
  constructor
  · intro h
    rw [eq_comm]
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
  · intro h
    simp [h]

Depends on / 依赖: eq_comm, o.oangle_rotation_right, oangle_rotation_right
-/
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x != 0) (θ : Real.Angle) :
    o.rotation θ x = x ↔ θ = 0 := by
  constructor
  · intro h
    rw [eq_comm]
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
  · intro h
    simp [h]

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
/--
theorem `eq_rotation_self_iff_angle_eq_zero` / 定理 `eq_rotation_self_iff_angle_eq_zero`

English:
theorem eq_rotation_self_iff_angle_eq_zero
  given: {x : V} (hx : x != 0) (θ : Real.Angle)
  proof: by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

中文:
定理 eq_rotation_self_iff_angle_eq_zero
  条件: {x : V} (hx : x != 0) (θ : 实数.Angle)
  证明: by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

Depends on / 依赖: add_sub_cancel_right, eq_comm, inv_smul_le_iff_of_pos, lineMap_apply, mul_inv_rev, mul_smul, o.rotation_eq_self_iff_angle_eq_zero, right_ne_zero_of_mul, rotation_eq_self_iff_angle_eq_zero, smul_add, smul_eq_mul, smul_smul, smul_sub, sub_le_iff_le_add, vadd_eq_add, vsub_eq_sub
-/
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x != 0) (θ : Real.Angle) :
    x = o.rotation θ x ↔ θ = 0 := by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/--
theorem `rotation_eq_self_iff` / 定理 `rotation_eq_self_iff`

English:
theorem rotation_eq_self_iff
  given: (x : V) (θ : Real.Angle)
  statement: o.rotation θ x = x ↔ x = 0 ∨ θ = 0
  proof: by
  by_cases h : x = 0 <;> simp [h]

中文:
定理 rotation_eq_self_iff
  条件: (x : V) (θ : 实数.Angle)
  结论: o.rotation θ x = x ↔ x = 0 ∨ θ = 0
  证明: by
  by_cases h : x = 0 <;> simp [h]
-/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases h : x = 0 <;> simp [h]

/--
theorem `eq_rotation_self_iff` / 定理 `eq_rotation_self_iff`

English:
theorem eq_rotation_self_iff
  given: (x : V) (θ : Real.Angle)
  statement: x = o.rotation θ x ↔ x = 0 ∨ θ = 0
  proof: by
  rw [← rotation_eq_self_iff]; rw [eq_comm]

中文:
定理 eq_rotation_self_iff
  条件: (x : V) (θ : 实数.Angle)
  结论: x = o.rotation θ x ↔ x = 0 ∨ θ = 0
  证明: by
  rw [← rotation_eq_self_iff]; rw [eq_comm]

Depends on / 依赖: eq_comm, rotation_eq_self_iff
-/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff]; rw [eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
/--
theorem `rotation_oangle_eq_iff_norm_eq` / 定理 `rotation_oangle_eq_iff_norm_eq`

English:
theorem rotation_oangle_eq_iff_norm_eq
  given: (x y : V)
  statement: o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖
  proof: by
  constructor
  · intro h
    rw [← h]; rw [LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

中文:
定理 rotation_oangle_eq_iff_norm_eq
  条件: (x y : V)
  结论: o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖
  证明: by
  constructor
  · intro h
    rw [← h]; rw [LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, eq_iff_oangle_eq_zero_of_norm_eq, norm_map, o.eq_iff_oangle_eq_zero_of_norm_eq
-/
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ := by
  constructor
  · intro h
    rw [← h]; rw [LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

/--
theorem `oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero` / 定理 `oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero`

English:
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
  statement: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← map_smul]; rw [← o.oangle_smul_left_of_pos x y hp]; rw [eq_comm]; rw [rotation_oangle_eq_iff_norm_eq]; rw [norm_smul]; rw [Real.norm_of_nonneg hp.le]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]

中文:
定理 oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
  结论: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← map_smul]; rw [← o.oangle_smul_left_of_pos x y hp]; rw [eq_comm]; rw [rotation_oangle_eq_iff_norm_eq]; rw [norm_smul]; rw [Real.norm_of_nonneg hp.le]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]

Depends on / 依赖: Real.norm_of_nonneg, div_pos, eq_comm, hp.le, map_smul, norm_ne_zero_iff, norm_of_nonneg, norm_pos_iff, norm_smul, o.oangle_rotation_self_right, o.oangle_smul_left_of_pos, o.oangle_smul_right_of_pos, oangle_rotation_self_right, oangle_smul_left_of_pos, oangle_smul_right_of_pos, rotation_oangle_eq_iff_norm_eq
-/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy : y != 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.rotation θ x := by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← map_smul]; rw [← o.oangle_smul_left_of_pos x y hp]; rw [eq_comm]; rw [rotation_oangle_eq_iff_norm_eq]; rw [norm_smul]; rw [Real.norm_of_nonneg hp.le]; rw [div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  · intro hye
    rw [hye]; rw [o.oangle_smul_right_of_pos _ _ hp]; rw [o.oangle_rotation_self_right hx]

/--
theorem `oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero` / 定理 `oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero`

English:
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
  statement: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  constructor
  · intro h
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [o.oangle_smul_right_of_pos _ _ hr]; rw [o.oangle_rotation_self_right hx]

中文:
定理 oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
  结论: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  constructor
  · intro h
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [o.oangle_smul_right_of_pos _ _ hr]; rw [o.oangle_rotation_self_right hx]

Depends on / 依赖: div_pos, norm_pos_iff, o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero, o.oangle_rotation_self_right, o.oangle_smul_right_of_pos, oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero, oangle_rotation_self_right, oangle_smul_right_of_pos
-/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x != 0) (hy : y != 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ exists r : Real, 0 < r ∧ y = r • o.rotation θ x := by
  constructor
  · intro h
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [o.oangle_smul_right_of_pos _ _ hr]; rw [o.oangle_rotation_self_right hx]

/--
theorem `oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero` / 定理 `oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero`

English:
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
  given: {x y : V} (θ : Real.Angle)
  proof: by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

中文:
定理 oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero
  条件: {x y : V} (θ : 实数.Angle)
  证明: by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

Depends on / 依赖: eq_comm, o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero, oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
-/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      x != 0 ∧ y != 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/--
theorem `oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero` / 定理 `oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero`

English:
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
  given: {x y : V} (θ : Real.Angle)
  proof: by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

中文:
定理 oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero
  条件: {x y : V} (θ : 实数.Angle)
  证明: by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

Depends on / 依赖: eq_comm, o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero, oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
-/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      (x != 0 ∧ y != 0 ∧ exists r : Real, 0 < r ∧ y = r • o.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/--
theorem `exists_linearIsometryEquiv_eq_of_det_pos` / 定理 `exists_linearIsometryEquiv_eq_of_det_pos`

English:
theorem exists_linearIsometryEquiv_eq_of_det_pos
  statement: {f : V ≃ₗᵢ[Real] V}
  proof: by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleR

中文:
定理 存在_linearIsometryEquiv_eq_of_det_pos
  结论: {f : V ≃ₗᵢ[实数] V}
  证明: by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleR

Depends on / 依赖: Fact.out, LinearEquiv, LinearEquiv.toLinearMap_injective, LinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_injective, Nontrivial, basisRightAngleRotation, exists_ne, fin_cases, finrank, kahler_comp_rightAngleRotation, linearIsometryEquiv_comp_rightAngleRotation, nontrivial_of_finrank_eq_succ, o.basisRightAngleRotation, o.kahler_comp_rightAngleRotation, o.linearIsometryEquiv_comp_rightAngleRotation, o.oangle, oangle, toLinearEquiv_injective, toLinearMap_injective
-/
theorem exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[Real] V}
    (hd : 0 < LinearMap.det (f.toLinearEquiv : V ->ₗ[Real] V)) :
    exists θ : Real.Angle, f = o.rotation θ := by
  have : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank Real V = 2) _)
  obtain ⟨x, hx⟩ : exists x, x != (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  symm
  fin_cases i
  · simp
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x) := by
    simp only [oangle, o.linearIsometryEquiv_comp_rightAngleRotation f hd,
      o.kahler_comp_rightAngleRotation]
  simp [← this]

/--
theorem `rotation_map` / 定理 `rotation_map`

English:
theorem rotation_map
  given: (θ : Real.Angle) (f : V ≃ₗᵢ[Real] V') (x : V')
  proof: by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]

中文:
定理 rotation_map
  条件: (θ : 实数.Angle) (f : V ≃ₗᵢ[实数] V') (x : V')
  证明: by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]

Depends on / 依赖: o.rightAngleRotation_map, rightAngleRotation_map, rotation_apply
-/
theorem rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[Real] V') (x : V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x)) := by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]
/--
theorem `_root_.Complex.rotation` / 定理 `_root_.Complex.rotation`

English:
theorem _root_.Complex.rotation
  given: (θ : Real.Angle) (z : Complex)
  proof: by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring

中文:
定理 _root_.复形.rotation
  条件: (θ : 实数.Angle) (z : 复形)
  证明: by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring
-/
protected theorem _root_.Complex.rotation (θ : Real.Angle) (z : Complex) :
    Complex.orientation.rotation θ z = θ.toCircle * z := by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring

/--
theorem `rotation_map_complex` / 定理 `rotation_map_complex`

English:
theorem rotation_map_complex
  statement: (θ : Real.Angle) (f : V ≃ₗᵢ[Real] Complex)
  proof: by
  rw [← Complex.rotation]; rw [← hf]; rw [o.rotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 rotation_map_complex
  结论: (θ : 实数.Angle) (f : V ≃ₗᵢ[实数] 复形)
  证明: by
  rw [← Complex.rotation]; rw [← hf]; rw [o.rotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: Complex.rotation, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, o.rotation_map, rotation, rotation_map, symm_apply_apply
-/
theorem rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[Real] Complex)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (o.rotation θ x) = θ.toCircle * f x := by
  rw [← Complex.rotation]; rw [← hf]; rw [o.rotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

/--
theorem `rotation_neg_orientation_eq_neg` / 定理 `rotation_neg_orientation_eq_neg`

English:
theorem rotation_neg_orientation_eq_neg
  given: (θ : Real.Angle)
  statement: (-o).rotation θ = o.rotation (-θ)
  proof: LinearIsometryEquiv.ext by simp [rotation_apply]

中文:
定理 rotation_neg_orientation_eq_neg
  条件: (θ : 实数.Angle)
  结论: (-o).rotation θ = o.rotation (-θ)
  证明: LinearIsometryEquiv.ext by simp [rotation_apply]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, rotation_apply
-/
theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) :=
LinearIsometryEquiv.ext by simp [rotation_apply]

/-- The inner product between a `π / 2` rotation of a vector and that vector is zero. -/
@[simp]
/--
theorem `inner_rotation_pi_div_two_left` / 定理 `inner_rotation_pi_div_two_left`

English:
theorem inner_rotation_pi_div_two_left
  given: (x : V)
  statement: ⟪o.rotation (π / 2 : Real) x, x⟫ = 0
  proof: by
  rw [rotation_pi_div_two]; rw [inner_rightAngleRotation_self]

中文:
定理 inner_rotation_pi_div_two_left
  条件: (x : V)
  结论: ⟪o.rotation (π / 2 : 实数) x, x⟫ = 0
  证明: by
  rw [rotation_pi_div_two]; rw [inner_rightAngleRotation_self]

Depends on / 依赖: inner_rightAngleRotation_self, rotation_pi_div_two
-/
theorem inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : Real) x, x⟫ = 0 := by
  rw [rotation_pi_div_two]; rw [inner_rightAngleRotation_self]

/-- The inner product between a vector and a `π / 2` rotation of that vector is zero. -/
@[simp]
/--
theorem `inner_rotation_pi_div_two_right` / 定理 `inner_rotation_pi_div_two_right`

English:
theorem inner_rotation_pi_div_two_right
  given: (x : V)
  statement: ⟪x, o.rotation (π / 2 : Real) x⟫ = 0
  proof: by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left]

中文:
定理 inner_rotation_pi_div_two_right
  条件: (x : V)
  结论: ⟪x, o.rotation (π / 2 : 实数) x⟫ = 0
  证明: by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left]

Depends on / 依赖: inner_rotation_pi_div_two_left, real_inner_comm
-/
theorem inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : Real) x⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and that vector is
zero. -/
@[simp]
/--
theorem `inner_smul_rotation_pi_div_two_left` / 定理 `inner_smul_rotation_pi_div_two_left`

English:
theorem inner_smul_rotation_pi_div_two_left
  given: (x : V) (r : Real)
  proof: by
  rw [inner_smul_left]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

中文:
定理 inner_smul_rotation_pi_div_two_left
  条件: (x : V) (r : 实数)
  证明: by
  rw [inner_smul_left]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

Depends on / 依赖: inner_rotation_pi_div_two_left, inner_smul_left, mul_zero
-/
theorem inner_smul_rotation_pi_div_two_left (x : V) (r : Real) :
    ⟪r • o.rotation (π / 2 : Real) x, x⟫ = 0 := by
  rw [inner_smul_left]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

/-- The inner product between a vector and a multiple of a `π / 2` rotation of that vector is
zero. -/
@[simp]
/--
theorem `inner_smul_rotation_pi_div_two_right` / 定理 `inner_smul_rotation_pi_div_two_right`

English:
theorem inner_smul_rotation_pi_div_two_right
  given: (x : V) (r : Real)
  proof: by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_left]

中文:
定理 inner_smul_rotation_pi_div_two_right
  条件: (x : V) (r : 实数)
  证明: by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_left]

Depends on / 依赖: inner_smul_rotation_pi_div_two_left, real_inner_comm
-/
theorem inner_smul_rotation_pi_div_two_right (x : V) (r : Real) :
    ⟪x, r • o.rotation (π / 2 : Real) x⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_left]

/-- The inner product between a `π / 2` rotation of a vector and a multiple of that vector is
zero. -/
@[simp]
/--
theorem `inner_rotation_pi_div_two_left_smul` / 定理 `inner_rotation_pi_div_two_left_smul`

English:
theorem inner_rotation_pi_div_two_left_smul
  given: (x : V) (r : Real)
  proof: by
  rw [inner_smul_right]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

中文:
定理 inner_rotation_pi_div_two_left_smul
  条件: (x : V) (r : 实数)
  证明: by
  rw [inner_smul_right]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

Depends on / 依赖: inner_rotation_pi_div_two_left, inner_smul_right, mul_zero
-/
theorem inner_rotation_pi_div_two_left_smul (x : V) (r : Real) :
    ⟪o.rotation (π / 2 : Real) x, r • x⟫ = 0 := by
  rw [inner_smul_right]; rw [inner_rotation_pi_div_two_left]; rw [mul_zero]

/-- The inner product between a multiple of a vector and a `π / 2` rotation of that vector is
zero. -/
@[simp]
/--
theorem `inner_rotation_pi_div_two_right_smul` / 定理 `inner_rotation_pi_div_two_right_smul`

English:
theorem inner_rotation_pi_div_two_right_smul
  given: (x : V) (r : Real)
  proof: by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left_smul]

中文:
定理 inner_rotation_pi_div_two_right_smul
  条件: (x : V) (r : 实数)
  证明: by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left_smul]

Depends on / 依赖: inner_rotation_pi_div_two_left_smul, real_inner_comm
-/
theorem inner_rotation_pi_div_two_right_smul (x : V) (r : Real) :
    ⟪r • x, o.rotation (π / 2 : Real) x⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_rotation_pi_div_two_left_smul]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and a multiple of
that vector is zero. -/
@[simp]
/--
theorem `inner_smul_rotation_pi_div_two_smul_left` / 定理 `inner_smul_rotation_pi_div_two_smul_left`

English:
theorem inner_smul_rotation_pi_div_two_smul_left
  given: (x : V) (r₁ r₂ : Real)
  proof: by
  rw [inner_smul_right]; rw [inner_smul_rotation_pi_div_two_left]; rw [mul_zero]

中文:
定理 inner_smul_rotation_pi_div_two_smul_left
  条件: (x : V) (r₁ r₂ : 实数)
  证明: by
  rw [inner_smul_right]; rw [inner_smul_rotation_pi_div_two_left]; rw [mul_zero]

Depends on / 依赖: inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero
-/
theorem inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : Real) :
    ⟪r₁ • o.rotation (π / 2 : Real) x, r₂ • x⟫ = 0 := by
  rw [inner_smul_right]; rw [inner_smul_rotation_pi_div_two_left]; rw [mul_zero]

/-- The inner product between a multiple of a vector and a multiple of a `π / 2` rotation of
that vector is zero. -/
@[simp]
/--
theorem `inner_smul_rotation_pi_div_two_smul_right` / 定理 `inner_smul_rotation_pi_div_two_smul_right`

English:
theorem inner_smul_rotation_pi_div_two_smul_right
  given: (x : V) (r₁ r₂ : Real)
  proof: by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_smul_left]

中文:
定理 inner_smul_rotation_pi_div_two_smul_right
  条件: (x : V) (r₁ r₂ : 实数)
  证明: by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_smul_left]

Depends on / 依赖: inner_smul_rotation_pi_div_two_smul_left, real_inner_comm
-/
theorem inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : Real) :
    ⟪r₂ • x, r₁ • o.rotation (π / 2 : Real) x⟫ = 0 := by
  rw [real_inner_comm]; rw [inner_smul_rotation_pi_div_two_smul_left]

/--
theorem `inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two` / 定理 `inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two`

English:
theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two
  given: {x y : V}
  proof: by
  by_cases! +distrib H : x = 0 ∨ y = 0
  · rcases H with (rfl | rfl) <;> simp
  simp only [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero, H, ← neg_smul, false_or,
    o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero H.1 H.2, ← o.neg_rotation_pi_div_two, smul_neg]
  constructor
  · grind
  · rintro ⟨r

中文:
定理 inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two
  条件: {x y : V}
  证明: by
  by_cases! +distrib H : x = 0 ∨ y = 0
  · rcases H with (rfl | rfl) <;> simp
  simp only [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero, H, ← neg_smul, false_or,
    o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero H.1 H.2, ← o.neg_rotation_pi_div_two, smul_neg]
  constructor
  · grind
  · rintro ⟨r

Depends on / 依赖: distrib, eq_zero_or_oangle_eq_iff_inner_eq_zero, false_or, lt_trichotomy, neg_rotation_pi_div_two, neg_smul, o.eq_zero_or_oangle_eq_iff_inner_eq_zero, o.neg_rotation_pi_div_two, o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero, oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero, smul_neg
-/
theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
    ⟪x, y⟫ = 0 ↔ x = 0 ∨ exists r : Real, r • o.rotation (π / 2 : Real) x = y := by
  by_cases! +distrib H : x = 0 ∨ y = 0
  · rcases H with (rfl | rfl) <;> simp
  simp only [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero, H, ← neg_smul, false_or,
    o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero H.1 H.2, ← o.neg_rotation_pi_div_two, smul_neg]
  constructor
  · grind
  · rintro ⟨r, rfl⟩
    rcases lt_trichotomy 0 r with (hr0 | rfl | hr0)
    · grind
    · simp_all
    · right
      use -r
      simp_all

end Orientation
