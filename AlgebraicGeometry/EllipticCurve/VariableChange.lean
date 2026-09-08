/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata, Jz Pan
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Change of variables of Weierstrass curves

This file defines admissible linear change of variables of Weierstrass curves.

## Main definitions

* `WeierstrassCurve.VariableChange`: a change of variables of Weierstrass curves.
* An instance which states that change of variables forms a group.
* An instance which states that change of variables acts on Weierstrass curves.

## Main statements

* An instance which states that change of variables preserves elliptic curves.
* `WeierstrassCurve.variableChange_j`: the j-invariant of an elliptic curve is invariant under an
  admissible linear change of variables.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, change of variables
-/

@[expose] public section

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section VariableChange

/-! ## Variable changes -/

/-- An admissible linear change of variables of Weierstrass curves defined over a ring `R` given by
a tuple `(u, r, s, t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. As a matrix, it is
$$\begin{pmatrix} u^2 & 0 & r \cr u^2s & u^3 & t \cr 0 & 0 & 1 \end{pmatrix}.$$
In other words, this is the change of variables `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)`.
When `R` is a field, any two isomorphic Weierstrass equations are related by this. -/
@[ext]
/-
**WeierstrassCurve.VariableChange** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve`
。
形式化陈述：(R : Type u) → [CommRing R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An admissible linear change of variables of Weierstrass curves defined over a ri
ng `R` given by
a tuple `(u, r, s, t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. As a matr
ix, it is
$$\begin{pmatrix} u^2 & 0 & r \cr u^2s & u^3 & t \cr 0 & 0 & 1 \end{pmatrix}.$$
In other words, this is the change of variables `(X, Y) ↦ (u²X + r, u³Y + u²sX +
 t)`.
When `R` is a field, any two isomorphic Weierstrass equations are related by thi
s.
-/
structure VariableChange (R : Type u) [CommRing R] where
  /-- The `u` coefficient of an admissible linear change of variables, which must be a unit. -/
  u : Rˣ
  /-- The `r` coefficient of an admissible linear change of variables. -/
  r : R
  /-- The `s` coefficient of an admissible linear change of variables. -/
  s : R
  /-- The `t` coefficient of an admissible linear change of variables. -/
  t : R

namespace VariableChange

variable (C C' : VariableChange R)

/-
**WeierstrassCurve.VariableChange.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.V
ariableChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (VariableChange R) where
  one := ⟨1, 0, 0, 0⟩

/-- The identity linear change of variables given by the identity matrix. -/
/-
**WeierstrassCurve.VariableChange.one_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.VariableChange`。
形式化陈述：one_def : (1 : VariableChange R) = ⟨1, 0, 0, 0⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity linear change of variables given by the identity matrix.
-/
lemma one_def : (1 : VariableChange R) = ⟨1, 0, 0, 0⟩ := rfl
/-
**WeierstrassCurve.VariableChange.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.V
ariableChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (VariableChange R) where
  mul C C' := {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t }

/-- The composition of two linear changes of variables given by matrix multiplication. -/
/-
**WeierstrassCurve.VariableChange.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.VariableChange`。
形式化陈述：mul_def : C * C' = { u
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two linear changes of variables given by matrix multiplicatio
n.
-/
lemma mul_def : C * C' = {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t } := rfl
/-
**WeierstrassCurve.VariableChange.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.V
ariableChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (VariableChange R) where
  inv C := {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 }

/-- The inverse of a linear change of variables given by matrix inversion. -/
/-
**WeierstrassCurve.VariableChange.inv_def** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.VariableChange`。
形式化陈述：inv_def : C⁻¹ = { u
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a linear change of variables given by matrix inversion.
-/
lemma inv_def : C⁻¹ = {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 } := rfl
/-
**WeierstrassCurve.VariableChange.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve.V
ariableChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (VariableChange R) where
  one_mul C := by
    simp only [mul_def, one_def, zero_add, zero_mul, mul_zero, one_mul]
  mul_one C := by
    simp only [mul_def, one_def, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]
  inv_mul_cancel C := by
    rw [mul_def, one_def, inv_def]
    ext <;> dsimp only
    · exact C.u.inv_mul
    · linear_combination -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
    · linear_combination -C.s * C.u.inv_mul
    · linear_combination (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
        + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul
  mul_assoc _ _ _ := by
    ext <;> simp only [mul_def, Units.val_mul] <;> ring1

end VariableChange

variable (C : VariableChange R)

/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (VariableChange R) (WeierstrassCurve R) where
  smul C W := {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) }

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` for some `u` in `Rˣ` and some `r, s, t` in `R`. -/
/-
**WeierstrassCurve.variableChange_def** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：variableChange_def : C • W = { a₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve over `R` induced by an admissible linear change of variabl
es
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` for some `u` in `Rˣ` and some `r, s, t` in 
`R`.
-/
lemma variableChange_def : C • W = {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) } := rfl
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (VariableChange R) (WeierstrassCurve R) where
  one_smul W := by
    rw [VariableChange.one_def, variableChange_def, inv_one, Units.val_one]
    ext <;> dsimp only <;> ring1
  mul_smul C C' W := by
    simp only [VariableChange.mul_def, variableChange_def]
    ext <;> simp only [mul_inv, Units.val_mul]
    · linear_combination ↑C.u⁻¹ * C.s * 2 * C'.u.inv_mul
    · linear_combination
        C.s * (-C'.s * 2 - W.a₁) * C.u⁻¹ ^ 2 * ↑C'.u⁻¹ * C'.u.inv_mul
          + (C.r * 3 - C.s ^ 2) * C.u⁻¹ ^ 2 * pow_mul_pow_eq_one 2 C'.u.inv_mul
    · linear_combination
        C.r * (C'.s * 2 + W.a₁) * C.u⁻¹ ^ 3 * ↑C'.u⁻¹ * pow_mul_pow_eq_one 2 C'.u.inv_mul
          + C.t * 2 * C.u⁻¹ ^ 3 * pow_mul_pow_eq_one 3 C'.u.inv_mul
    · linear_combination
        C.s * (-W.a₃ - C'.r * W.a₁ - C'.t * 2) * C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 3 * C'.u.inv_mul
          + C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 2 * (C.r * C'.r * 6 + C.r * W.a₂ * 2 - C'.s * C.r * W.a₁ * 2
            - C'.s ^ 2 * C.r * 2) * pow_mul_pow_eq_one 2 C'.u.inv_mul
          - C.u⁻¹ ^ 4 * ↑C'.u⁻¹ * (C.s * C'.s * C.r * 2 + C.s * C.r * W.a₁ + C'.s * C.t * 2
            + C.t * W.a₁) * pow_mul_pow_eq_one 3 C'.u.inv_mul
          + C.u⁻¹ ^ 4 * (C.r ^ 2 * 3 - C.s * C.t * 2) * pow_mul_pow_eq_one 4 C'.u.inv_mul
    · linear_combination
        C.r * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 4 * (C'.r * W.a₂ * 2 - C'.r * C'.s * W.a₁ + C'.r ^ 2 * 3 + W.a₄
            - C'.s * C'.t * 2 - C'.s * W.a₃ - C'.t * W.a₁) * pow_mul_pow_eq_one 2 C'.u.inv_mul
          - C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 3 * C.t * (C'.r * W.a₁ + C'.t * 2 + W.a₃)
            * pow_mul_pow_eq_one 3 C'.u.inv_mul
          + C.r ^ 2 * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 2 * (C'.r * 3 + W.a₂ - C'.s * W.a₁ - C'.s ^ 2)
            * pow_mul_pow_eq_one 4 C'.u.inv_mul
          - C.r * C.t * C.u⁻¹ ^ 6 * ↑C'.u⁻¹ * (C'.s * 2 + W.a₁) * pow_mul_pow_eq_one 5 C'.u.inv_mul
          + C.u⁻¹ ^ 6 * (C.r ^ 3 - C.t ^ 2) * pow_mul_pow_eq_one 6 C'.u.inv_mul
/-
**WeierstrassCurve.variableChange_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_a₁ : (C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s) := rfl
/-
**WeierstrassCurve.variableChange_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_a₂ : (C • W).a₂ = C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl
/-
**WeierstrassCurve.variableChange_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_a₃ : (C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := rfl
/-
**WeierstrassCurve.variableChange_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_a₄ : (C • W).a₄ =
    C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t) := rfl
/-
**WeierstrassCurve.variableChange_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_a₆ : (C • W).a₆ =
    C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) := rfl
/-
**WeierstrassCurve.variableChange_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_b₂ : (C • W).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r) := by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1
/-
**WeierstrassCurve.variableChange_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_b₄ : (C • W).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) := by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1
/-
**WeierstrassCurve.variableChange_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_b₆ : (C • W).b₆ =
    C.u⁻¹ ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1
/-
**WeierstrassCurve.variableChange_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_b₈ : (C • W).b₈ = C.u⁻¹ ^ 8 *
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) := by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1
/-
**WeierstrassCurve.variableChange_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_c₄ : (C • W).c₄ = C.u⁻¹ ^ 4 * W.c₄ := by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1
/-
**WeierstrassCurve.variableChange_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_c₆ : (C • W).c₆ = C.u⁻¹ ^ 6 * W.c₆ := by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1
/-
**WeierstrassCurve.variableChange_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_Δ : (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

variable [W.IsElliptic]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (C • W).IsElliptic := by
  rw [isElliptic_iff, variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

set_option linter.docPrime false in
/-
**WeierstrassCurve.variableChange_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variableChange_Δ' : (C • W).Δ' = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

set_option linter.docPrime false in
/-
**WeierstrassCurve.coe_variableChange_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_variableChange_Δ' : ((C • W).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [coe_Δ', variableChange_Δ]

set_option linter.docPrime false in
/-
**WeierstrassCurve.inv_variableChange_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCur
ve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_variableChange_Δ' : (C • W).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [variableChange_Δ', mul_inv, inv_pow, inv_inv]

set_option linter.docPrime false in
/-
**WeierstrassCurve.coe_inv_variableChange_** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_inv_variableChange_Δ' : (↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [inv_variableChange_Δ', Units.val_mul, Units.val_pow_eq_pow_val]

@[simp]
/-
**WeierstrassCurve.variableChange_j** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
形式化陈述：variableChange_j : (C • W).j = W.j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.instIsEllipticHSMulVariableChange`：∀ {R : Type u} [inst
 : CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) 
[W.IsElliptic],   (C • W).IsElliptic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用引理 `WeierstrassCurve.coe_inv_variableChange_Δ'`：coe_inv_variableChange_Δ' : 
(↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹
· 使用引理 `WeierstrassCurve.variableChange_c₄`：variableChange_c₄ : (C • W).c₄ = C.u
⁻¹ ^ 4 * W.c₄
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma variableChange_j : (C • W).j = W.j := by
  rw [j, coe_inv_variableChange_Δ', variableChange_c₄, j, mul_pow, ← pow_mul, ← mul_assoc,
    mul_right_comm (C.u.val ^ 12), ← mul_pow, C.u.mul_inv, one_pow, one_mul]

end VariableChange

section BaseChange

/-! ## Maps and base changes -/

variable (C : VariableChange R) {A : Type v} [CommRing A] (φ : R →+* A)

namespace VariableChange

/-- The change of variables mapped over a ring homomorphism `φ : R →+* A`. -/
@[simps]
/-
**WeierstrassCurve.VariableChange.map** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e.VariableChange`。
形式化陈述：map : VariableChange A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The change of variables mapped over a ring homomorphism `φ : R →+* A`.
-/
def map : VariableChange A :=
  ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

variable (A) in
/-- The change of variables base changed to an algebra `A` over `R`. -/
/-
**WeierstrassCurve.VariableChange.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Weierstr
assCurve.VariableChange`。
形式化陈述：baseChange [Algebra R A] : VariableChange A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The change of variables base changed to an algebra `A` over `R`.
-/
def baseChange [Algebra R A] : VariableChange A :=
  C.map <| algebraMap R A

/-- The notation `\textf` for `WeierstrassCurve.VariableChange.baseChange C A`. -/
scoped notation:max (priority := low) C:max "⁄" A:max => baseChange C A

@[simp]
/-
**WeierstrassCurve.VariableChange.map_id** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassC
urve.VariableChange`。
形式化陈述：map_id : C.map (RingHom.id R) = C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id : C.map (RingHom.id R) = C :=
  rfl
/-
**WeierstrassCurve.VariableChange.map_map** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve.VariableChange`。
形式化陈述：map_map {A : Type v} [CommRing A] (φ : R ->+* A) {B : Type w} [CommRing B]
 (ψ : A ->+* B) : (C.map φ).map ψ = C.map (ψ.comp φ)
参数：φ : R ->+* A；ψ : A ->+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_map {A : Type v} [CommRing A] (φ : R →+* A) {B : Type w} [CommRing B] (ψ : A →+* B) :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  rfl

@[simp]
/-
**WeierstrassCurve.VariableChange.map_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Weie
rstrassCurve.VariableChange`。
形式化陈述：map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommR
ing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing 
B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (ψ : A ->ₐ[S] B) : (C⁄A).ma
p ψ = C⁄B
参数：ψ : A ->ₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
-/
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A →ₐ[S] B) : (C⁄A).map ψ = C⁄B :=
  congr_arg C.map <| ψ.comp_algebraMap_of_tower R
/-
**WeierstrassCurve.VariableChange.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `Weier
strassCurve.VariableChange`。
形式化陈述：map_injective {φ : R ->+* A} (hφ : Function.Injective φ) : Function.Inject
ive map (φ
参数：hφ : Function.Injective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.VariableChange.mk.inj`：∀ {R : Type u} {inst : CommRing 
R} {u : Rˣ} {r s t : R} {u_1 : Rˣ} {r_1 s_1 t_1 : R},   { u := u, r := r, s := s
, t := t } = { u := u_1, r :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Units.mk.inj`：∀ {α : Type u} {inst : Monoid α} {val inv : α} {val_inv : 
val * inv = 1} {inv_val : inv * val = 1} {val_1 inv_1 : α}   {val_inv_1 : val_1 
* …
· 使用定理 `WeierstrassCurve.VariableChange.ext`：∀ {R : Type u} {inst : CommRing R} 
{x y : WeierstrassCurve.VariableChange R},   x.u = y.u → x.r = y.r → x.s = y.s →
 x.t = y.t → x = y
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma map_injective {φ : R →+* A} (hφ : Function.Injective φ) :
    Function.Injective <| map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

/-- The map over a ring homomorphism of a change of variables is a group homomorphism. -/
/-
**WeierstrassCurve.VariableChange.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassC
urve.VariableChange`。
形式化陈述：mapHom : VariableChange R ->* VariableChange A where toFun C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map over a ring homomorphism of a change of variables is a group homomorphis
m.
-/
def mapHom : VariableChange R →* VariableChange A where
  toFun C := C.map φ
  map_one' := by
    simp only [one_def, map]
    ext <;> simp only [map_one, Units.val_one, map_zero]
  map_mul' C C' := by
    simp only [mul_def, map]
    ext <;> map_simp <;> simp only [Units.coe_map, MonoidHom.coe_coe]

end VariableChange

/-
**WeierstrassCurve.map_variableChange** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：map_variableChange : (C.map φ) • (W.map φ) = (C • W).map φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.ext`：∀ {R : Type u} {x y : WeierstrassCurve R}, x.a₁ = 
y.a₁ → x.a₂ = y.a₂ → x.a₃ = y.a₃ → x.a₄ = y.a₄ → x.a₆ = y.a₆ → x = y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
-/
lemma map_variableChange : (C.map φ) • (W.map φ) = (C • W).map φ := by
  simp only [map, variableChange_def, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map_inv, MonoidHom.coe_coe]

end BaseChange

end WeierstrassCurve

