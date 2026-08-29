/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Complex.Determinant

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `Complex.reCLM` (real part), `Complex.imCLM` (imaginary part),
`Complex.conjCLE` (conjugation), and `Complex.ofRealCLM` (inclusion of `ℝ`) were introduced in
`Analysis.Complex.Basic`. This file contains a few calculations requiring more imports:
the operator norm and (for `Complex.conjCLE`) the determinant.
-/

public section

open ContinuousLinearMap

namespace Complex

/-- The determinant of `conjLIE`, as a linear map. -/
@[simp]
/--
theorem `det_conjLIE` / 定理 `det_conjLIE`

English:
theorem det_conjLIE
  statement: LinearMap.det (conjLIE.toLinearEquiv : Complex ->ₗ[Real] Complex) = -1
  proof: det_conjAe

中文:
定理 det_conjLIE
  结论: 线性映射.det (conjLIE.toLinearEquiv : 复形 ->ₗ[实数] 复形) = -1
  证明: det_conjAe

Depends on / 依赖: det_conjAe
-/
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : Complex ->ₗ[Real] Complex) = -1 :=
  det_conjAe

/-- The determinant of `conjLIE`, as a linear equiv. -/
@[simp]
/--
theorem `linearEquiv_det_conjLIE` / 定理 `linearEquiv_det_conjLIE`

English:
theorem linearEquiv_det_conjLIE
  statement: LinearEquiv.det conjLIE.toLinearEquiv = -1
  proof: linearEquiv_det_conjAe

@[simp]

中文:
定理 linearEquiv_det_conjLIE
  结论: 线性等价.det conjLIE.toLinearEquiv = -1
  证明: linearEquiv_det_conjAe

@[simp]

Depends on / 依赖: linearEquiv_det_conjAe
-/
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

@[simp]
/--
theorem `reCLM_norm` / 定理 `reCLM_norm`

English:
theorem reCLM_norm
  statement: ‖reCLM‖ = 1
  proof: le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖reCLM 1‖ := by simp
      _ <= ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]

中文:
定理 reCLM_norm
  结论: ‖reCLM‖ = 1
  证明: le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖reCLM 1‖ := by simp
      _ <= ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, le_antisymm, mkContinuous_norm_le, unit_le_opNorm, zero_le_one
-/
theorem reCLM_norm : ‖reCLM‖ = 1 :=
le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖reCLM 1‖ := by simp
      _ <= ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
/--
theorem `reCLM_enorm` / 定理 `reCLM_enorm`

English:
theorem reCLM_enorm
  statement: ‖reCLM‖ₑ = 1
  proof: by simp [← ofReal_norm]

@[simp]

中文:
定理 reCLM_enorm
  结论: ‖reCLM‖ₑ = 1
  证明: by simp [← ofReal_norm]

@[simp]

Depends on / 依赖: ofReal_norm
-/
theorem reCLM_enorm : ‖reCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/--
theorem `reCLM_nnnorm` / 定理 `reCLM_nnnorm`

English:
theorem reCLM_nnnorm
  statement: ‖reCLM‖₊ = 1
  proof: Subtype.ext reCLM_norm

@[simp]

中文:
定理 reCLM_nnnorm
  结论: ‖reCLM‖₊ = 1
  证明: Subtype.ext reCLM_norm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, reCLM_norm
-/
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm

@[simp]
/--
theorem `imCLM_norm` / 定理 `imCLM_norm`

English:
theorem imCLM_norm
  statement: ‖imCLM‖ = 1
  proof: le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖imCLM I‖ := by simp
      _ <= ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]

中文:
定理 imCLM_norm
  结论: ‖imCLM‖ = 1
  证明: le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖imCLM I‖ := by simp
      _ <= ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, le_antisymm, mkContinuous_norm_le, unit_le_opNorm, zero_le_one
-/
theorem imCLM_norm : ‖imCLM‖ = 1 :=
le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
    calc
      1 = ‖imCLM I‖ := by simp
      _ <= ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
/--
theorem `imCLM_enorm` / 定理 `imCLM_enorm`

English:
theorem imCLM_enorm
  statement: ‖imCLM‖ₑ = 1
  proof: by simp [← ofReal_norm]

@[simp]

中文:
定理 imCLM_enorm
  结论: ‖imCLM‖ₑ = 1
  证明: by simp [← ofReal_norm]

@[simp]

Depends on / 依赖: ofReal_norm
-/
theorem imCLM_enorm : ‖imCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/--
theorem `imCLM_nnnorm` / 定理 `imCLM_nnnorm`

English:
theorem imCLM_nnnorm
  statement: ‖imCLM‖₊ = 1
  proof: Subtype.ext imCLM_norm

@[simp]

中文:
定理 imCLM_nnnorm
  结论: ‖imCLM‖₊ = 1
  证明: Subtype.ext imCLM_norm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, imCLM_norm
-/
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm

@[simp]
/--
theorem `conjCLE_norm` / 定理 `conjCLE_norm`

English:
theorem conjCLE_norm
  statement: ‖(conjCLE : Complex ->L[Real] Complex)‖ = 1
  proof: conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]

中文:
定理 conjCLE_norm
  结论: ‖(conjCLE : 复形 ->L[实数] 复形)‖ = 1
  证明: conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]

Depends on / 依赖: conjLIE, conjLIE.toLinearIsometry.norm_toContinuousLinearMap, norm_toContinuousLinearMap, toLinearIsometry
-/
theorem conjCLE_norm : ‖(conjCLE : Complex ->L[Real] Complex)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]
/--
theorem `conjCLE_enorm` / 定理 `conjCLE_enorm`

English:
theorem conjCLE_enorm
  statement: ‖(conjCLE : Complex ->L[Real] Complex)‖ₑ = 1
  proof: by simp [← ofReal_norm]

@[simp]

中文:
定理 conjCLE_enorm
  结论: ‖(conjCLE : 复形 ->L[实数] 复形)‖ₑ = 1
  证明: by simp [← ofReal_norm]

@[simp]

Depends on / 依赖: ofReal_norm
-/
theorem conjCLE_enorm : ‖(conjCLE : Complex ->L[Real] Complex)‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/--
theorem `conjCLE_nnorm` / 定理 `conjCLE_nnorm`

English:
theorem conjCLE_nnorm
  statement: ‖(conjCLE : Complex ->L[Real] Complex)‖₊ = 1
  proof: Subtype.ext conjCLE_norm

@[simp]

中文:
定理 conjCLE_nnorm
  结论: ‖(conjCLE : 复形 ->L[实数] 复形)‖₊ = 1
  证明: Subtype.ext conjCLE_norm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, conjCLE_norm
-/
theorem conjCLE_nnorm : ‖(conjCLE : Complex ->L[Real] Complex)‖₊ = 1 :=
  Subtype.ext conjCLE_norm

@[simp]
/--
theorem `ofRealCLM_norm` / 定理 `ofRealCLM_norm`

English:
theorem ofRealCLM_norm
  statement: ‖ofRealCLM‖ = 1
  proof: ofRealLI.norm_toContinuousLinearMap

@[simp]

中文:
定理 of实数CLM_norm
  结论: ‖of实数CLM‖ = 1
  证明: ofRealLI.norm_toContinuousLinearMap

@[simp]

Depends on / 依赖: norm_toContinuousLinearMap, ofRealLI, ofRealLI.norm_toContinuousLinearMap
-/
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap

@[simp]
/--
theorem `ofRealCLM_enorm` / 定理 `ofRealCLM_enorm`

English:
theorem ofRealCLM_enorm
  statement: ‖ofRealCLM‖ₑ = 1
  proof: by simp [← ofReal_norm]

@[simp]

中文:
定理 of实数CLM_enorm
  结论: ‖of实数CLM‖ₑ = 1
  证明: by simp [← ofReal_norm]

@[simp]

Depends on / 依赖: ofReal_norm
-/
theorem ofRealCLM_enorm : ‖ofRealCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/--
theorem `ofRealCLM_nnnorm` / 定理 `ofRealCLM_nnnorm`

English:
theorem ofRealCLM_nnnorm
  statement: ‖ofRealCLM‖₊ = 1
  proof: Subtype.ext ofRealCLM_norm

中文:
定理 of实数CLM_nnnorm
  结论: ‖of实数CLM‖₊ = 1
  证明: Subtype.ext ofRealCLM_norm

Depends on / 依赖: Subtype, Subtype.ext, ofRealCLM_norm
-/
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
Subtype.ext ofRealCLM_norm

end Complex
