/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/

public section


namespace Complex

/-- The determinant of `conjAe`, as a linear map. -/
@[simp]
/--
theorem `det_conjAe` / 定理 `det_conjAe`

English:
theorem det_conjAe
  statement: conjAe.toLinearEquiv.toLinearMap.det = -1
  proof: by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_conjAe]; rw [Matrix.det_fin_two_of]
  simp

中文:
定理 det_conjAe
  结论: conjAe.toLinearEquiv.toLinearMap.det = -1
  证明: by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_conjAe]; rw [Matrix.det_fin_two_of]
  simp

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.det_fin_two_of, basisOneI, det_fin_two_of, det_toMatrix, toMatrix_conjAe
-/
theorem det_conjAe : conjAe.toLinearEquiv.toLinearMap.det = -1 := by
  rw [← LinearMap.det_toMatrix basisOneI]; rw [toMatrix_conjAe]; rw [Matrix.det_fin_two_of]
  simp

/-- The determinant of `conjAe`, as a linear equiv. -/
@[simp]
/--
theorem `linearEquiv_det_conjAe` / 定理 `linearEquiv_det_conjAe`

English:
theorem linearEquiv_det_conjAe
  statement: conjAe.toLinearEquiv.det = -1
  proof: by simp [← Units.val_inj]

中文:
定理 linearEquiv_det_conjAe
  结论: conjAe.toLinearEquiv.det = -1
  证明: by simp [← Units.val_inj]

Depends on / 依赖: Units.val_inj, val_inj
-/
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by simp [← Units.val_inj]

end Complex
