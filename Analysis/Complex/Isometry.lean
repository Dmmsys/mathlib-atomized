/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.SuppressCompilation

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`

The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `LinearIsometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/

@[expose] public section


noncomputable section
suppress_compilation -- needed to avoid a panic!

open Complex

open CharZero

open ComplexConjugate

local notation "|" x "|" => Complex.abs x

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `rotation` / `rotation` 的定义

English:
definition rotation
  signature: : Circle ->* Complex ≃ₗᵢ[Real] Complex where
  body: { DistribMulAction.toLinearEquiv Real Complex a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul]; rw [Circle.norm_coe]; rw [one_mul] }
map_one' := LinearIsometryEquiv.ext by simp
map_mul' a b := LinearIsometryEquiv.ext mul_smul a b

@[simp]

中文:
定义 rotation
  签名: : Circle ->* 复形 ≃ₗᵢ[实数] 复形 where
  定义体: { DistribMulAction.toLinearEquiv Real Complex a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul]; rw [Circle.norm_coe]; rw [one_mul] }
map_one' := LinearIsometryEquiv.ext by simp
map_mul' a b := LinearIsometryEquiv.ext mul_smul a b

@[simp]

Depends on / 依赖: Circle, Circle.norm_coe, DistribMulAction, DistribMulAction.toLinearEquiv, LinearIsometryEquiv, LinearIsometryEquiv.ext, map_mul, map_one, mul_smul, norm_coe, norm_map, norm_mul, one_mul, toLinearEquiv
-/
def rotation : Circle ->* Complex ≃ₗᵢ[Real] Complex where
  toFun a :=
    { DistribMulAction.toLinearEquiv Real Complex a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul]; rw [Circle.norm_coe]; rw [one_mul] }
map_one' := LinearIsometryEquiv.ext by simp
map_mul' a b := LinearIsometryEquiv.ext mul_smul a b

@[simp]
/--
theorem `rotation_apply` / 定理 `rotation_apply`

English:
theorem rotation_apply
  given: (a : Circle) (z : Complex)
  statement: rotation a z = a * z
  proof: rfl

@[simp]

中文:
定理 rotation_apply
  条件: (a : Circle) (z : 复形)
  结论: rotation a z = a * z
  证明: rfl

@[simp]
-/
theorem rotation_apply (a : Circle) (z : Complex) : rotation a z = a * z :=
  rfl

@[simp]
/--
theorem `rotation_symm` / 定理 `rotation_symm`

English:
theorem rotation_symm
  given: (a : Circle)
  statement: (rotation a).symm = rotation a⁻¹
  proof: LinearIsometryEquiv.ext fun _ => rfl

@[simp]

中文:
定理 rotation_symm
  条件: (a : Circle)
  结论: (rotation a).symm = rotation a⁻¹
  证明: LinearIsometryEquiv.ext fun _ => rfl

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext
-/
theorem rotation_symm (a : Circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun _ => rfl

@[simp]
/--
theorem `rotation_trans` / 定理 `rotation_trans`

English:
theorem rotation_trans
  given: (a b : Circle)
  statement: (rotation a).trans (rotation b) = rotation (b * a)
  proof: by
  ext1
  simp

中文:
定理 rotation_trans
  条件: (a b : Circle)
  结论: (rotation a).trans (rotation b) = rotation (b * a)
  证明: by
  ext1
  simp
-/
theorem rotation_trans (a b : Circle) : (rotation a).trans (rotation b) = rotation (b * a) := by
  ext1
  simp

/--
theorem `rotation_ne_conjLIE` / 定理 `rotation_ne_conjLIE`

English:
theorem rotation_ne_conjLIE
  given: (a : Circle)
  statement: rotation a != conjLIE
  proof: by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply]; rw [map_one]; rw [mul_one] at h1
  rw [rotation_apply]; rw [conj_I]; rw [← neg_one_mul]; rw [mul_left_inj' I_ne_zero]; rw [h1]; rw [eq_neg_self_iff] at hI
  exact one_ne_zero hI

中文:
定理 rotation_ne_conjLIE
  条件: (a : Circle)
  结论: rotation a != conjLIE
  证明: by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply]; rw [map_one]; rw [mul_one] at h1
  rw [rotation_apply]; rw [conj_I]; rw [← neg_one_mul]; rw [mul_left_inj' I_ne_zero]; rw [h1]; rw [eq_neg_self_iff] at hI
  exact one_ne_zero hI

Depends on / 依赖: I_ne_zero, LinearIsometryEquiv, LinearIsometryEquiv.congr_fun, congr_fun, conj_I, eq_neg_self_iff, map_one, mul_left_inj, mul_one, neg_one_mul, one_ne_zero, rotation, rotation_apply
-/
theorem rotation_ne_conjLIE (a : Circle) : rotation a != conjLIE := by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply]; rw [map_one]; rw [mul_one] at h1
  rw [rotation_apply]; rw [conj_I]; rw [← neg_one_mul]; rw [mul_left_inj' I_ne_zero]; rw [h1]; rw [eq_neg_self_iff] at hI
  exact one_ne_zero hI

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
/--
Definition of `rotationOf` / `rotationOf` 的定义

English:
definition rotationOf
  signature: (e : Complex ≃ₗᵢ[Real] Complex)
  body: ⟨e 1 / ‖e 1‖, by simp [Submonoid.unitSphere]⟩

中文:
定义 rotationOf
  签名: (e : 复形 ≃ₗᵢ[实数] 复形)
  定义体: ⟨e 1 / ‖e 1‖, by simp [Submonoid.unitSphere]⟩

Depends on / 依赖: Submonoid, Submonoid.unitSphere, unitSphere
-/
def rotationOf (e : Complex ≃ₗᵢ[Real] Complex) : Circle :=
  ⟨e 1 / ‖e 1‖, by simp [Submonoid.unitSphere]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `rotationOf_rotation` / 定理 `rotationOf_rotation`

English:
theorem rotationOf_rotation
  given: (a : Circle)
  statement: rotationOf (rotation a) = a
  proof: Subtype.ext by simp

中文:
定理 rotationOf_rotation
  条件: (a : Circle)
  结论: rotationOf (rotation a) = a
  证明: Subtype.ext by simp

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem rotationOf_rotation (a : Circle) : rotationOf (rotation a) = a :=
Subtype.ext by simp

/--
theorem `rotation_injective` / 定理 `rotation_injective`

English:
theorem rotation_injective
  statement: Function.Injective rotation
  proof: Function.LeftInverse.injective rotationOf_rotation

中文:
定理 rotation_injective
  结论: 函数.单射 rotation
  证明: Function.LeftInverse.injective rotationOf_rotation

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, rotationOf_rotation
-/
theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotationOf_rotation

/--
theorem `LinearIsometry.re_apply_eq_re_of_add_conj_eq` / 定理 `LinearIsometry.re_apply_eq_re_of_add_conj_eq`

English:
theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq
  statement: (f : Complex ->ₗᵢ[Real] Complex)
  proof: by
  simpa [Complex.ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : Real) != 0 by simp] using (h₃ z).symm

中文:
定理 线性等距.re_apply_eq_re_of_add_conj_eq
  结论: (f : 复形 ->ₗᵢ[实数] 复形)
  证明: by
  simpa [Complex.ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : Real) != 0 by simp] using (h₃ z).symm

Depends on / 依赖: BorelSpace, Complex.ext_iff, add_im, add_re, conj_im, conj_re, ext_iff, two_mul
-/
theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : Complex ->ₗᵢ[Real] Complex)
    (h₃ : forall z, z + conj z = f z + conj (f z)) (z : Complex) : (f z).re = z.re := by
  simpa [Complex.ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : Real) != 0 by simp] using (h₃ z).symm

/--
theorem `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re` / 定理 `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re`

English:
theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re
  statement: {f : Complex ->ₗᵢ[Real] Complex}
  proof: by
  have h₁ := f.norm_map z
  simp only [norm_def] at h₁
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁

中文:
定理 线性等距.im_apply_eq_im_or_neg_of_re_apply_eq_re
  结论: {f : 复形 ->ₗᵢ[实数] 复形}
  证明: by
  have h₁ := f.norm_map z
  simp only [norm_def] at h₁
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁

Depends on / 依赖: Real.sqrt_inj, add_left_cancel_iff, f.norm_map, mul_self_eq_mul_self_iff, normSq_apply, normSq_nonneg, norm_def, norm_map, sqrt_inj
-/
theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : Complex ->ₗᵢ[Real] Complex}
    (h₂ : forall z, (f z).re = z.re) (z : Complex) : (f z).im = z.im ∨ (f z).im = -z.im := by
  have h₁ := f.norm_map z
  simp only [norm_def] at h₁
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁

/--
theorem `LinearIsometry.im_apply_eq_im` / 定理 `LinearIsometry.im_apply_eq_im`

English:
theorem LinearIsometry.im_apply_eq_im
  given: {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex)
  proof: by
  have hsq : ‖f z - 1‖ ^ 2 = ‖z - 1‖ ^ 2 := by simpa [h] using f.norm_map (z - 1)
  simp_rw [← normSq_eq_norm_sq, Complex.normSq_sub] at hsq
  simpa [normSq_eq_norm_sq, Complex.add_conj, LinearIsometry.norm_map] using hsq.symm

中文:
定理 线性等距.im_apply_eq_im
  条件: {f : 复形 ->ₗᵢ[实数] 复形} (h : f 1 = 1) (z : 复形)
  证明: by
  have hsq : ‖f z - 1‖ ^ 2 = ‖z - 1‖ ^ 2 := by simpa [h] using f.norm_map (z - 1)
  simp_rw [← normSq_eq_norm_sq, Complex.normSq_sub] at hsq
  simpa [normSq_eq_norm_sq, Complex.add_conj, LinearIsometry.norm_map] using hsq.symm

Depends on / 依赖: Complex.add_conj, Complex.normSq_sub, LinearIsometry, LinearIsometry.norm_map, add_conj, f.norm_map, hsq.symm, normSq_eq_norm_sq, normSq_sub, norm_map, simp_rw
-/
theorem LinearIsometry.im_apply_eq_im {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex) :
    z + conj z = f z + conj (f z) := by
  have hsq : ‖f z - 1‖ ^ 2 = ‖z - 1‖ ^ 2 := by simpa [h] using f.norm_map (z - 1)
  simp_rw [← normSq_eq_norm_sq, Complex.normSq_sub] at hsq
  simpa [normSq_eq_norm_sq, Complex.add_conj, LinearIsometry.norm_map] using hsq.symm

/--
theorem `LinearIsometry.re_apply_eq_re` / 定理 `LinearIsometry.re_apply_eq_re`

English:
theorem LinearIsometry.re_apply_eq_re
  given: {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex)
  statement: (f z).re = z.re
  proof: by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  apply LinearIsometry.im_apply_eq_im h

中文:
定理 线性等距.re_apply_eq_re
  条件: {f : 复形 ->ₗᵢ[实数] 复形} (h : f 1 = 1) (z : 复形)
  结论: (f z).re = z.re
  证明: by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  apply LinearIsometry.im_apply_eq_im h

Depends on / 依赖: LinearIsometry, LinearIsometry.im_apply_eq_im, LinearIsometry.re_apply_eq_re_of_add_conj_eq, im_apply_eq_im, re_apply_eq_re_of_add_conj_eq
-/
theorem LinearIsometry.re_apply_eq_re {f : Complex ->ₗᵢ[Real] Complex} (h : f 1 = 1) (z : Complex) : (f z).re = z.re := by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  apply LinearIsometry.im_apply_eq_im h

/--
theorem `linear_isometry_complex_aux` / 定理 `linear_isometry_complex_aux`

English:
theorem linear_isometry_complex_aux
  given: {f : Complex ≃ₗᵢ[Real] Complex} (h : f 1 = 1)
  proof: by
  have h0 : f I = I ∨ f I = -I := by
    simp only [Complex.ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine h0.imp (fun h' : f I = I => ?_) fun h' : f I = -I => ?_ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply Complex.basisOneI.ext'
      intro i
      fin_cases i <;> simp [h, h']

中文:
定理 linear_isometry_complex_aux
  条件: {f : 复形 ≃ₗᵢ[实数] 复形} (h : f 1 = 1)
  证明: by
  have h0 : f I = I ∨ f I = -I := by
    simp only [Complex.ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine h0.imp (fun h' : f I = I => ?_) fun h' : f I = -I => ?_ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply Complex.basisOneI.ext'
      intro i
      fin_cases i <;> simp [h, h']

Depends on / 依赖: Complex.basisOneI.ext, Complex.ext_iff, I_re, LinearIsometry, LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re, LinearIsometry.re_apply_eq_re, LinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_injective, and_or_left, basisOneI, ext_iff, f.toLinearIsometry, h0.imp, im_apply_eq_im_or_neg_of_re_apply_eq_re, neg_im, neg_re, neg_zero, re_apply_eq_re, toLinearEquiv_injective, toLinearIsometry
-/
theorem linear_isometry_complex_aux {f : Complex ≃ₗᵢ[Real] Complex} (h : f 1 = 1) :
    f = LinearIsometryEquiv.refl Real Complex ∨ f = conjLIE := by
  have h0 : f I = I ∨ f I = -I := by
    simp only [Complex.ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine h0.imp (fun h' : f I = I => ?_) fun h' : f I = -I => ?_ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply Complex.basisOneI.ext'
      intro i
      fin_cases i <;> simp [h, h']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `linear_isometry_complex` / 定理 `linear_isometry_complex`

English:
theorem linear_isometry_complex
  given: (f : Complex ≃ₗᵢ[Real] Complex)
  proof: by
  let a : Circle := ⟨f 1, by simp [Submonoid.unitSphere, f.norm_map]⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa [a] using rotation_apply a⁻¹ (f 1)
  refine (linear_isometry_complex_aux this).imp (fun h₁ => ?_) fun h₂ => ?_
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂

中文:
定理 linear_isometry_complex
  条件: (f : 复形 ≃ₗᵢ[实数] 复形)
  证明: by
  let a : Circle := ⟨f 1, by simp [Submonoid.unitSphere, f.norm_map]⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa [a] using rotation_apply a⁻¹ (f 1)
  refine (linear_isometry_complex_aux this).imp (fun h₁ => ?_) fun h₂ => ?_
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂

Depends on / 依赖: Circle, Submonoid, Submonoid.unitSphere, eq_mul_of_inv_mul_eq, f.norm_map, f.trans, linear_isometry_complex_aux, norm_map, rotation, rotation_apply, unitSphere
-/
theorem linear_isometry_complex (f : Complex ≃ₗᵢ[Real] Complex) :
    exists a : Circle, f = rotation a ∨ f = conjLIE.trans (rotation a) := by
  let a : Circle := ⟨f 1, by simp [Submonoid.unitSphere, f.norm_map]⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa [a] using rotation_apply a⁻¹ (f 1)
  refine (linear_isometry_complex_aux this).imp (fun h₁ => ?_) fun h₂ => ?_
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂

/--
theorem `toMatrix_rotation` / 定理 `toMatrix_rotation`

English:
theorem toMatrix_rotation
  given: (a : Circle)
  proof: by
  ext i j
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, coe_basisOneI_repr, mul_re, mul_im,
    Matrix.val_planeConformalMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp

中文:
定理 toMatrix_rotation
  条件: (a : Circle)
  证明: by
  ext i j
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, coe_basisOneI_repr, mul_re, mul_im,
    Matrix.val_planeConformalMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearIsometryEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.empty_val, Matrix.of_apply, Matrix.val_planeConformalMatrix, coe_basisOneI, coe_basisOneI_repr, coe_coe, coe_toLinearEquiv, cons_val, cons_val_fin_one, empty_val, fin_cases
-/
theorem toMatrix_rotation (a : Circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← normSq_apply]) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, coe_basisOneI_repr, mul_re, mul_im,
    Matrix.val_planeConformalMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
/--
theorem `det_rotation` / 定理 `det_rotation`

English:
theorem det_rotation
  given: (a : Circle)
  statement: LinearMap.det ((rotation a).toLinearEquiv : Complex ->ₗ[Real] Complex) = 1
  proof: by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_rotation]; rw [Matrix.det_fin_two]
  simp [← normSq_apply]

中文:
定理 det_rotation
  条件: (a : Circle)
  结论: 线性映射.det ((rotation a).toLinearEquiv : 复形 ->ₗ[实数] 复形) = 1
  证明: by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_rotation]; rw [Matrix.det_fin_two]
  simp [← normSq_apply]

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.det_fin_two, basisOneI, continuous, det_fin_two, det_toMatrix, map_contDiff, normSq_apply, toMatrix_rotation
-/
theorem det_rotation (a : Circle) : LinearMap.det ((rotation a).toLinearEquiv : Complex ->ₗ[Real] Complex) = 1 := by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_rotation]; rw [Matrix.det_fin_two]
  simp [← normSq_apply]

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
/--
theorem `linearEquiv_det_rotation` / 定理 `linearEquiv_det_rotation`

English:
theorem linearEquiv_det_rotation
  given: (a : Circle)
  statement: LinearEquiv.det (rotation a).toLinearEquiv = 1
  proof: by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [det_rotation]; rw [Units.val_one]

中文:
定理 linearEquiv_det_rotation
  条件: (a : Circle)
  结论: 线性等价.det (rotation a).toLinearEquiv = 1
  证明: by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [det_rotation]; rw [Units.val_one]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ofNormedAddCommGroup, HasCompactSupport, HasCompactSupport.intro, K.isCompact, LinearEquiv, LinearEquiv.coe_det, Units.val_inj, Units.val_one, bounded_above_of_compact_support, coe_det, det_rotation, isCompact, map_bounded, map_continuous, map_zero_on_compl, ofNormedAddCommGroup, val_inj, val_one
-/
theorem linearEquiv_det_rotation (a : Circle) : LinearEquiv.det (rotation a).toLinearEquiv = 1 := by
  rw [← Units.val_inj]; rw [LinearEquiv.coe_det]; rw [det_rotation]; rw [Units.val_one]
