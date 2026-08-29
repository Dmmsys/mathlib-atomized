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
/--
Definition of `VariableChange` / `VariableChange` 的定义

English:
structure VariableChange
  parameters: (R : Type u) [CommRing R]
  axioms and operations (4):
    - u : Rˣ
    - r : R
    - s : R
    - t : R

中文:
结构 VariableChange
  参数: (R : 类型u) [交换环 R]
  公理与运算 (4 个):
    - u : Rˣ
    - r : R
    - s : R
    - t : R
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (VariableChange R)
  body: ⟨1, 0, 0, 0⟩

中文:
实例 :
  签名: 幺 (VariableChange R)
  定义体: ⟨1, 0, 0, 0⟩
-/
instance : One (VariableChange R) where
  one := ⟨1, 0, 0, 0⟩

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : VariableChange R) = ⟨1, 0, 0, 0⟩
  proof: rfl

中文:
引理 one_def
  结论: (1 : VariableChange R) = ⟨1, 0, 0, 0⟩
  证明: rfl
-/
lemma one_def : (1 : VariableChange R) = ⟨1, 0, 0, 0⟩ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (VariableChange R)
  body: {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t }

中文:
实例 :
  签名: 乘法 (VariableChange R)
  定义体: {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t }
-/
instance : Mul (VariableChange R) where
  mul C C' := {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t }

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  statement: C * C' = {
  proof: rfl

中文:
引理 mul_def
  结论: C * C' = {
  证明: rfl
-/
lemma mul_def : C * C' = {
    u := C.u * C'.u
    r := C.r * C'.u ^ 2 + C'.r
    s := C'.u * C.s + C'.s
    t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t } := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (VariableChange R)
  body: {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 }

中文:
实例 :
  签名: 取逆 (VariableChange R)
  定义体: {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 }
-/
instance : Inv (VariableChange R) where
  inv C := {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 }

/--
lemma `inv_def` / 引理 `inv_def`

English:
lemma inv_def
  statement: C⁻¹ = {
  proof: rfl

中文:
引理 inv_def
  结论: C⁻¹ = {
  证明: rfl
-/
lemma inv_def : C⁻¹ = {
    u := C.u⁻¹
    r := -C.r * C.u⁻¹ ^ 2
    s := -C.s * C.u⁻¹
    t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3 } := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (VariableChange R)
  body: by
    simp only [mul_def, one_def, zero_add, zero_mul, mul_zero, one_mul]
  mul_one C := by
    simp only [mul_def, one_def, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]
  inv_mul_cancel C := by
    rw [mul_def]; rw [one_def]; rw [inv_def]
    ext <;> dsimp only
    · exact C.u.inv_mul
    · linear_combination -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
    · linear_combination -C.s * C.u.inv_mul
    · linear_combination (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
        + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul
  mul_assoc _ _ _ := by
    ext <;> simp only [mul_def, Units.val_mul] <;> ring1

中文:
实例 :
  签名: 群 (VariableChange R)
  定义体: by
    simp only [mul_def, one_def, zero_add, zero_mul, mul_zero, one_mul]
  mul_one C := by
    simp only [mul_def, one_def, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]
  inv_mul_cancel C := by
    rw [mul_def]; rw [one_def]; rw [inv_def]
    ext <;> dsimp only
    · exact C.u.inv_mul
    · linear_combination -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
    · linear_combination -C.s * C.u.inv_mul
    · linear_combination (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
        + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul
  mul_assoc _ _ _ := by
    ext <;> simp only [mul_def, Units.val_mul] <;> ring1

Depends on / 依赖: C.u.inv_, C.u.inv_mul, Units.val_one, add_zero, inv_, inv_def, inv_mul, inv_mul_cancel, linear_combination, mul_def, mul_one, mul_zero, one_def, one_mul, one_pow, pow_mul_pow_eq_one, val_one, zero_add, zero_mul
-/
instance : Group (VariableChange R) where
  one_mul C := by
    simp only [mul_def, one_def, zero_add, zero_mul, mul_zero, one_mul]
  mul_one C := by
    simp only [mul_def, one_def, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]
  inv_mul_cancel C := by
    rw [mul_def]; rw [one_def]; rw [inv_def]
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (VariableChange R) (WeierstrassCurve R)
  body: {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) }

中文:
实例 :
  签名: 标量乘法 (VariableChange R) (WeierstrassCurve R)
  定义体: {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) }
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

/--
lemma `variableChange_def` / 引理 `variableChange_def`

English:
lemma variableChange_def
  statement: C • W = {
  proof: rfl

中文:
引理 variableChange_def
  结论: C • W = {
  证明: rfl
-/
lemma variableChange_def : C • W = {
    a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
    a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
    a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
    a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t)
    a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) } := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (VariableChange R) (WeierstrassCurve R)
  body: by
    rw [VariableChange.one_def]; rw [variableChange_def]; rw [inv_one]; rw [Units.val_one]
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

中文:
实例 :
  签名: 乘法作用 (VariableChange R) (WeierstrassCurve R)
  定义体: by
    rw [VariableChange.one_def]; rw [variableChange_def]; rw [inv_one]; rw [Units.val_one]
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

Depends on / 依赖: Units.val_mul, Units.val_one, VariableChange, VariableChange.mul_def, VariableChange.one_def, inv_mul, inv_one, linear_combination, mul_def, mul_inv, mul_smul, one_def, pow_mul_pow_eq_one, u.inv_mul, val_mul, val_one, variableChange_def
-/
instance : MulAction (VariableChange R) (WeierstrassCurve R) where
  one_smul W := by
    rw [VariableChange.one_def]; rw [variableChange_def]; rw [inv_one]; rw [Units.val_one]
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

/--
lemma `variableChange_a₁` / 引理 `variableChange_a₁`

English:
lemma variableChange_a₁
  statement: (C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s)
  proof: rfl

中文:
引理 variableChange_a₁
  结论: (C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s)
  证明: rfl
-/
lemma variableChange_a₁ : (C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s) := rfl

/--
lemma `variableChange_a₂` / 引理 `variableChange_a₂`

English:
lemma variableChange_a₂
  statement: (C • W).a₂ = C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
  proof: rfl

中文:
引理 variableChange_a₂
  结论: (C • W).a₂ = C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
  证明: rfl
-/
lemma variableChange_a₂ : (C • W).a₂ = C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) := rfl

/--
lemma `variableChange_a₃` / 引理 `variableChange_a₃`

English:
lemma variableChange_a₃
  statement: (C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
  proof: rfl

中文:
引理 variableChange_a₃
  结论: (C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
  证明: rfl
-/
lemma variableChange_a₃ : (C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) := rfl

/--
lemma `variableChange_a₄` / 引理 `variableChange_a₄`

English:
lemma variableChange_a₄
  statement: (C • W).a₄ =
  proof: rfl

中文:
引理 variableChange_a₄
  结论: (C • W).a₄ =
  证明: rfl
-/
lemma variableChange_a₄ : (C • W).a₄ =
    C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
      - 2 * C.s * C.t) := rfl

/--
lemma `variableChange_a₆` / 引理 `variableChange_a₆`

English:
lemma variableChange_a₆
  statement: (C • W).a₆ =
  proof: rfl

中文:
引理 variableChange_a₆
  结论: (C • W).a₆ =
  证明: rfl
-/
lemma variableChange_a₆ : (C • W).a₆ =
    C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
      - C.r * C.t * W.a₁) := rfl

/--
lemma `variableChange_b₂` / 引理 `variableChange_b₂`

English:
lemma variableChange_b₂
  statement: (C • W).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r)
  proof: by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1

中文:
引理 variableChange_b₂
  结论: (C • W).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r)
  证明: by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1
-/
lemma variableChange_b₂ : (C • W).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r) := by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1

/--
lemma `variableChange_b₄` / 引理 `variableChange_b₄`

English:
lemma variableChange_b₄
  statement: (C • W).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)
  proof: by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1

中文:
引理 variableChange_b₄
  结论: (C • W).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)
  证明: by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1
-/
lemma variableChange_b₄ : (C • W).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) := by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1

/--
lemma `variableChange_b₆` / 引理 `variableChange_b₆`

English:
lemma variableChange_b₆
  statement: (C • W).b₆ =
  proof: by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1

中文:
引理 variableChange_b₆
  结论: (C • W).b₆ =
  证明: by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1
-/
lemma variableChange_b₆ : (C • W).b₆ =
    C.u⁻¹ ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1

/--
lemma `variableChange_b₈` / 引理 `variableChange_b₈`

English:
lemma variableChange_b₈
  statement: (C • W).b₈ = C.u⁻¹ ^ 8 *
  proof: by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

中文:
引理 variableChange_b₈
  结论: (C • W).b₈ = C.u⁻¹ ^ 8 *
  证明: by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1
-/
lemma variableChange_b₈ : (C • W).b₈ = C.u⁻¹ ^ 8 *
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) := by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

/--
lemma `variableChange_c₄` / 引理 `variableChange_c₄`

English:
lemma variableChange_c₄
  statement: (C • W).c₄ = C.u⁻¹ ^ 4 * W.c₄
  proof: by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1

中文:
引理 variableChange_c₄
  结论: (C • W).c₄ = C.u⁻¹ ^ 4 * W.c₄
  证明: by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1
-/
lemma variableChange_c₄ : (C • W).c₄ = C.u⁻¹ ^ 4 * W.c₄ := by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1

/--
lemma `variableChange_c₆` / 引理 `variableChange_c₆`

English:
lemma variableChange_c₆
  statement: (C • W).c₆ = C.u⁻¹ ^ 6 * W.c₆
  proof: by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1

中文:
引理 variableChange_c₆
  结论: (C • W).c₆ = C.u⁻¹ ^ 6 * W.c₆
  证明: by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1
-/
lemma variableChange_c₆ : (C • W).c₆ = C.u⁻¹ ^ 6 * W.c₆ := by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1

/--
lemma `variableChange_Δ` / 引理 `variableChange_Δ`

English:
lemma variableChange_Δ
  statement: (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ
  proof: by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

中文:
引理 variableChange_Δ
  结论: (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ
  证明: by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1
-/
lemma variableChange_Δ : (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

variable [W.IsElliptic]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (C • W).IsElliptic
  body: by
  rw [isElliptic_iff]; rw [variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

中文:
实例 :
  签名: (C • W).是Elliptic
  定义体: by
  rw [isElliptic_iff]; rw [variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

Depends on / 依赖: W.isUnit_, isElliptic_iff, isUnit, isUnit.pow
-/
instance : (C • W).IsElliptic := by
  rw [isElliptic_iff]; rw [variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

set_option linter.docPrime false in
/--
lemma `variableChange_Δ'` / 引理 `variableChange_Δ'`

English:
lemma variableChange_Δ'
  statement: (C • W).Δ' = C.u⁻¹ ^ 12 * W.Δ'
  proof: by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

中文:
引理 variableChange_Δ'
  结论: (C • W).Δ' = C.u⁻¹ ^ 12 * W.Δ'
  证明: by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

Depends on / 依赖: Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, ext_iff, simp_rw, val_mul, val_pow_eq_pow_val
-/
lemma variableChange_Δ' : (C • W).Δ' = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

set_option linter.docPrime false in
/--
lemma `coe_variableChange_Δ'` / 引理 `coe_variableChange_Δ'`

English:
lemma coe_variableChange_Δ'
  statement: ((C • W).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ'
  proof: by
  simp_rw [coe_Δ', variableChange_Δ]

中文:
引理 coe_variableChange_Δ'
  结论: ((C • W).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ'
  证明: by
  simp_rw [coe_Δ', variableChange_Δ]

Depends on / 依赖: simp_rw
-/
lemma coe_variableChange_Δ' : ((C • W).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [coe_Δ', variableChange_Δ]

set_option linter.docPrime false in
/--
lemma `inv_variableChange_Δ'` / 引理 `inv_variableChange_Δ'`

English:
lemma inv_variableChange_Δ'
  statement: (C • W).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹
  proof: by
  rw [variableChange_Δ']; rw [mul_inv]; rw [inv_pow]; rw [inv_inv]

中文:
引理 inv_variableChange_Δ'
  结论: (C • W).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹
  证明: by
  rw [variableChange_Δ']; rw [mul_inv]; rw [inv_pow]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pow, mul_inv
-/
lemma inv_variableChange_Δ' : (C • W).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [variableChange_Δ']; rw [mul_inv]; rw [inv_pow]; rw [inv_inv]

set_option linter.docPrime false in
/--
lemma `coe_inv_variableChange_Δ'` / 引理 `coe_inv_variableChange_Δ'`

English:
lemma coe_inv_variableChange_Δ'
  statement: (↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹
  proof: by
  rw [inv_variableChange_Δ']; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]

@[simp]

中文:
引理 coe_inv_variableChange_Δ'
  结论: (↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹
  证明: by
  rw [inv_variableChange_Δ']; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]

@[simp]

Depends on / 依赖: Units.val_mul, Units.val_pow_eq_pow_val, val_mul, val_pow_eq_pow_val
-/
lemma coe_inv_variableChange_Δ' : (↑(C • W).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [inv_variableChange_Δ']; rw [Units.val_mul]; rw [Units.val_pow_eq_pow_val]

@[simp]
/--
lemma `variableChange_j` / 引理 `variableChange_j`

English:
lemma variableChange_j
  statement: (C • W).j = W.j
  proof: by
  rw [j]; rw [coe_inv_variableChange_Δ']; rw [variableChange_c₄]; rw [j]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_right_comm (C.u.val ^ 12)]; rw [← mul_pow]; rw [C.u.mul_inv]; rw [one_pow]; rw [one_mul]

中文:
引理 variableChange_j
  结论: (C • W).j = W.j
  证明: by
  rw [j]; rw [coe_inv_variableChange_Δ']; rw [variableChange_c₄]; rw [j]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_right_comm (C.u.val ^ 12)]; rw [← mul_pow]; rw [C.u.mul_inv]; rw [one_pow]; rw [one_mul]

Depends on / 依赖: C.u.mul_inv, C.u.val, mul_assoc, mul_inv, mul_pow, mul_right_comm, one_mul, one_pow, pow_mul
-/
lemma variableChange_j : (C • W).j = W.j := by
  rw [j]; rw [coe_inv_variableChange_Δ']; rw [variableChange_c₄]; rw [j]; rw [mul_pow]; rw [← pow_mul]; rw [← mul_assoc]; rw [mul_right_comm (C.u.val ^ 12)]; rw [← mul_pow]; rw [C.u.mul_inv]; rw [one_pow]; rw [one_mul]

end VariableChange

section BaseChange

/-! ## Maps and base changes -/

variable (C : VariableChange R) {A : Type v} [CommRing A] (φ : R ->+* A)

namespace VariableChange

/-- The change of variables mapped over a ring homomorphism `φ : R →+* A`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : VariableChange A
  body: ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

中文:
定义 map
  签名: : VariableChange A
  定义体: ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

Depends on / 依赖: Units.map
-/
def map : VariableChange A :=
  ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: [Algebra R A]
  body: C.map algebraMap R A

中文:
定义 baseChange
  签名: [代数 R A]
  定义体: C.map algebraMap R A

Depends on / 依赖: C.map, algebraMap
-/
def baseChange [Algebra R A] : VariableChange A :=
C.map algebraMap R A

/-- The notation `\textf` for `WeierstrassCurve.VariableChange.baseChange C A`. -/
scoped notation:max (priority := low) C:max "⁄" A:max => baseChange C A

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: C.map (RingHom.id R) = C
  proof: rfl

中文:
引理 map_id
  结论: C.map (环态射.id R) = C
  证明: rfl
-/
lemma map_id : C.map (RingHom.id R) = C :=
  rfl

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: {A : Type v} [CommRing A] (φ : R ->+* A) {B : Type w} [CommRing B] (ψ : A ->+* B)
  proof: rfl

@[simp]

中文:
引理 map_map
  条件: {A : 类型v} [交换环 A] (φ : R ->+* A) {B : 类型 w} [交换环 B] (ψ : A ->+* B)
  证明: rfl

@[simp]
-/
lemma map_map {A : Type v} [CommRing A] (φ : R ->+* A) {B : Type w} [CommRing B] (ψ : A ->+* B) :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  rfl

@[simp]
/--
lemma `map_baseChange` / 引理 `map_baseChange`

English:
lemma map_baseChange
  statement: {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
  proof: congr_arg C.map ψ.comp_algebraMap_of_tower R

中文:
引理 map_baseChange
  结论: {S : 类型 s} [交换环 S] [代数 R S] {A : 类型v} [交换环 A] [代数 R A]
  证明: congr_arg C.map ψ.comp_algebraMap_of_tower R

Depends on / 依赖: C.map, comp_algebraMap_of_tower, congr_arg
-/
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A ->ₐ[S] B) : (C⁄A).map ψ = C⁄B :=
congr_arg C.map ψ.comp_algebraMap_of_tower R

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {φ : R ->+* A} (hφ : Function.Injective φ)
  proof: fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

中文:
引理 map_injective
  条件: {φ : R ->+* A} (hφ : 函数.单射 φ)
  证明: fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

Depends on / 依赖: Units.mk.inj, apply_fun, mk.inj, replace
-/
lemma map_injective {φ : R ->+* A} (hφ : Function.Injective φ) :
Function.Injective map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

/--
Definition of `mapHom` / `mapHom` 的定义

English:
definition mapHom
  signature: : VariableChange R ->* VariableChange A where
  body: C.map φ
  map_one' := by
    simp only [one_def, map]
    ext <;> simp only [map_one, Units.val_one, map_zero]
  map_mul' C C' := by
    simp only [mul_def, map]
    ext <;> map_simp <;> simp only [Units.coe_map, MonoidHom.coe_coe]

中文:
定义 mapHom
  签名: : VariableChange R ->* VariableChange A where
  定义体: C.map φ
  map_one' := by
    simp only [one_def, map]
    ext <;> simp only [map_one, Units.val_one, map_zero]
  map_mul' C C' := by
    simp only [mul_def, map]
    ext <;> map_simp <;> simp only [Units.coe_map, MonoidHom.coe_coe]

Depends on / 依赖: C.map
-/
def mapHom : VariableChange R ->* VariableChange A where
  toFun C := C.map φ
  map_one' := by
    simp only [one_def, map]
    ext <;> simp only [map_one, Units.val_one, map_zero]
  map_mul' C C' := by
    simp only [mul_def, map]
    ext <;> map_simp <;> simp only [Units.coe_map, MonoidHom.coe_coe]

end VariableChange

/--
lemma `map_variableChange` / 引理 `map_variableChange`

English:
lemma map_variableChange
  statement: (C.map φ) • (W.map φ) = (C • W).map φ
  proof: by
  simp only [map, variableChange_def, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map_inv, MonoidHom.coe_coe]

中文:
引理 map_variableChange
  结论: (C.map φ) • (W.map φ) = (C • W).map φ
  证明: by
  simp only [map, variableChange_def, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map_inv, MonoidHom.coe_coe]

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, Units.coe_map_inv, VariableChange, VariableChange.map, coe_coe, coe_map_inv, map_simp, variableChange_def
-/
lemma map_variableChange : (C.map φ) • (W.map φ) = (C • W).map φ := by
  simp only [map, variableChange_def, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map_inv, MonoidHom.coe_coe]

end BaseChange

end WeierstrassCurve
