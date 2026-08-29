/-
Copyright (c) 2026 Jon Bannon, Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Unitary maps in C⋆-algebras

This file defines some basic maps by unitaries in C⋆-algebras. -/

@[expose] public section

namespace Unitary
variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Ring R] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: : unitary A ->* A ≃ₗᵢ[R] A where
  body: { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 mulLeft
  签名: : unitary A ->* A ≃ₗᵢ[R] A where
  定义体: { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

Depends on / 依赖: CStarRing, CStarRing.norm_coe_unitary_mul, map_mul, map_one, mulLeftLinearEquiv, norm_coe_unitary_mul, norm_map, toUnits
-/
noncomputable def mulLeft : unitary A ->* A ≃ₗᵢ[R] A where
  toFun u :=
    { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

variable (R) in
/--
lemma `mulLeft_apply` / 引理 `mulLeft_apply`

English:
lemma mulLeft_apply
  given: (u : unitary A) (x : A)
  proof: rfl

中文:
引理 mulLeft_apply
  条件: (u : unitary A) (x : A)
  证明: rfl
-/
@[simp] lemma mulLeft_apply (u : unitary A) (x : A) :
    mulLeft R A u x = u * x := rfl

variable (R) in
/--
lemma `symm_mulLeft_apply` / 引理 `symm_mulLeft_apply`

English:
lemma symm_mulLeft_apply
  given: (u : unitary A) (x : A)
  proof: rfl

中文:
引理 symm_mulLeft_apply
  条件: (u : unitary A) (x : A)
  证明: rfl
-/
lemma symm_mulLeft_apply (u : unitary A) (x : A) :
    (mulLeft R A u).symm x = (star u : A) * x := rfl

/--
lemma `symm_mulLeft` / 引理 `symm_mulLeft`

English:
lemma symm_mulLeft
  given: (u : unitary A)
  proof: by ext; rfl

中文:
引理 symm_mulLeft
  条件: (u : unitary A)
  证明: by ext; rfl
-/
@[simp] lemma symm_mulLeft (u : unitary A) :
    (mulLeft R A u).symm = mulLeft R A (star u) := by ext; rfl

/--
lemma `mulLeft_trans_mulLeft` / 引理 `mulLeft_trans_mulLeft`

English:
lemma mulLeft_trans_mulLeft
  given: (u v : unitary A)
  proof: map_mul _ _ _

中文:
引理 mulLeft_trans_mulLeft
  条件: (u v : unitary A)
  证明: map_mul _ _ _

Depends on / 依赖: map_mul
-/
lemma mulLeft_trans_mulLeft (u v : unitary A) :
.symm (mulLeft R A u).trans (mulLeft R A v) = mulLeft R A (v * u) := map_mul _ _ _

/--
lemma `mulLeft_mul_apply` / 引理 `mulLeft_mul_apply`

English:
lemma mulLeft_mul_apply
  given: (u v : unitary A) (x : A)
  proof: by simp

中文:
引理 mulLeft_mul_apply
  条件: (u v : unitary A) (x : A)
  证明: by simp
-/
lemma mulLeft_mul_apply (u v : unitary A) (x : A) :
    mulLeft R A (u * v) x = mulLeft R A u (mulLeft R A v x) := by simp

/--
lemma `toLinearEquiv_mulLeft` / 引理 `toLinearEquiv_mulLeft`

English:
lemma toLinearEquiv_mulLeft
  given: (u : unitary A)
  proof: rfl

中文:
引理 toLinearEquiv_mulLeft
  条件: (u : unitary A)
  证明: rfl
-/
@[simp] lemma toLinearEquiv_mulLeft (u : unitary A) :
    (mulLeft R A u).toLinearEquiv = (toUnits u).mulLeftLinearEquiv R A := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (u : unitary A)
  body: (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

中文:
定义 mulRight
  签名: (u : unitary A)
  定义体: (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

Depends on / 依赖: mulRightLinearEquiv, toUnits
-/
noncomputable def mulRight (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearEquiv := (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

variable (R) in
/--
lemma `mulRight_apply` / 引理 `mulRight_apply`

English:
lemma mulRight_apply
  given: (u : unitary A) (x : A)
  proof: rfl

中文:
引理 mulRight_apply
  条件: (u : unitary A) (x : A)
  证明: rfl
-/
@[simp] lemma mulRight_apply (u : unitary A) (x : A) :
    mulRight R u x = x * u := rfl

variable (R) in
/--
lemma `symm_mulRight_apply` / 引理 `symm_mulRight_apply`

English:
lemma symm_mulRight_apply
  given: (u : unitary A) (x : A)
  proof: rfl

中文:
引理 symm_mulRight_apply
  条件: (u : unitary A) (x : A)
  证明: rfl
-/
lemma symm_mulRight_apply (u : unitary A) (x : A) :
    (mulRight R u).symm x = x * (star u : A) := rfl

/--
lemma `symm_mulRight` / 引理 `symm_mulRight`

English:
lemma symm_mulRight
  given: (u : unitary A)
  proof: by
  ext; rfl

中文:
引理 symm_mulRight
  条件: (u : unitary A)
  证明: by
  ext; rfl
-/
@[simp] lemma symm_mulRight (u : unitary A) :
    (mulRight R u).symm = mulRight R (star u) := by
  ext; rfl

/--
lemma `mulRight_trans_mulRight` / 引理 `mulRight_trans_mulRight`

English:
lemma mulRight_trans_mulRight
  given: (u v : unitary A)
  proof: by ext; simp [mul_assoc]

中文:
引理 mulRight_trans_mulRight
  条件: (u v : unitary A)
  证明: by ext; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulRight_trans_mulRight (u v : unitary A) :
    (mulRight R u).trans (mulRight R v) = mulRight R (u * v) := by ext; simp [mul_assoc]

/--
lemma `mulRight_mul_apply` / 引理 `mulRight_mul_apply`

English:
lemma mulRight_mul_apply
  given: (u v : unitary A) (x : A)
  proof: by simp [mul_assoc]

中文:
引理 mulRight_mul_apply
  条件: (u v : unitary A) (x : A)
  证明: by simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulRight_mul_apply (u v : unitary A) (x : A) :
    mulRight R (u * v) x = mulRight R v (mulRight R u x) := by simp [mul_assoc]

/--
lemma `toLinearMap_mulRight` / 引理 `toLinearMap_mulRight`

English:
lemma toLinearMap_mulRight
  given: (u : unitary A)
  proof: rfl

中文:
引理 toLinearMap_mulRight
  条件: (u : unitary A)
  证明: rfl
-/
lemma toLinearMap_mulRight (u : unitary A) :
    (mulRight R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl

/--
lemma `mulRight_one` / 引理 `mulRight_one`

English:
lemma mulRight_one
  statement: mulRight R 1 = .refl R A
  proof: by
  ext; simp

中文:
引理 mulRight_one
  结论: mulRight R 1 = .refl R A
  证明: by
  ext; simp
-/
@[simp] lemma mulRight_one : mulRight R 1 = .refl R A := by
  ext; simp

/--
lemma `toLinearEquiv_mulRight` / 引理 `toLinearEquiv_mulRight`

English:
lemma toLinearEquiv_mulRight
  given: (u : unitary A)
  proof: rfl

中文:
引理 toLinearEquiv_mulRight
  条件: (u : unitary A)
  证明: rfl
-/
@[simp] lemma toLinearEquiv_mulRight (u : unitary A) :
    (mulRight R u).toLinearEquiv = (toUnits u).mulRightLinearEquiv R := rfl

end mulRight

end Unitary
