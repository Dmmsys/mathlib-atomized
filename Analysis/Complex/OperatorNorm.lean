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
/-
**Complex.det_conjLIE** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : Complex ->ₗ[Real] Com
plex) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.det_conjAe`：det_conjAe : conjAe.toLinearEquiv.toLinearMap.det = 
-1

--- 原说明 ---
The determinant of `conjLIE`, as a linear map.
-/
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe

/-- The determinant of `conjLIE`, as a linear equiv. -/
@[simp]
/-
**Complex.linearEquiv_det_conjLIE** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.linearEquiv_det_conjAe`：linearEquiv_det_conjAe : conjAe.toLinear
Equiv.det = -1

--- 原说明 ---
The determinant of `conjLIE`, as a linear equiv.
-/
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

@[simp]
/-
**Complex.reCLM_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：reCLM_norm : ‖reCLM‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.unit_le_opNorm`：unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <
= ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
/-
**Complex.reCLM_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：reCLM_enorm : ‖reCLM‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.reCLM_norm`：reCLM_norm : ‖reCLM‖ = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reCLM_enorm : ‖reCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/-
**Complex.reCLM_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：reCLM_nnnorm : ‖reCLM‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.reCLM_norm`：reCLM_norm : ‖reCLM‖ = 1
-/
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm

@[simp]
/-
**Complex.imCLM_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：imCLM_norm : ‖imCLM‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.unit_le_opNorm`：unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <
= ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
-/
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
/-
**Complex.imCLM_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：imCLM_enorm : ‖imCLM‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.imCLM_norm`：imCLM_norm : ‖imCLM‖ = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imCLM_enorm : ‖imCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/-
**Complex.imCLM_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：imCLM_nnnorm : ‖imCLM‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.imCLM_norm`：imCLM_norm : ‖imCLM‖ = 1
-/
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm

@[simp]
/-
**Complex.conjCLE_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conjCLE_norm : ‖(conjCLE : Complex ->L[Real] Complex)‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]
/-
**Complex.conjCLE_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conjCLE_enorm : ‖(conjCLE : Complex ->L[Real] Complex)‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.conjCLE_norm`：conjCLE_norm : ‖(conjCLE : Complex ->L[Real] Compl
ex)‖ = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjCLE_enorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/-
**Complex.conjCLE_nnorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conjCLE_nnorm : ‖(conjCLE : Complex ->L[Real] Complex)‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.conjCLE_norm`：conjCLE_norm : ‖(conjCLE : Complex ->L[Real] Compl
ex)‖ = 1
-/
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm

@[simp]
/-
**Complex.ofRealCLM_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofRealCLM_norm : ‖ofRealCLM‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
-/
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap

@[simp]
/-
**Complex.ofRealCLM_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofRealCLM_enorm : ‖ofRealCLM‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofRealCLM_norm`：ofRealCLM_norm : ‖ofRealCLM‖ = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofRealCLM_enorm : ‖ofRealCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
/-
**Complex.ofRealCLM_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.ofRealCLM_norm`：ofRealCLM_norm : ‖ofRealCLM‖ = 1
-/
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm

end Complex

