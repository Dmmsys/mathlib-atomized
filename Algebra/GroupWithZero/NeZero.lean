/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero

/-!
# `NeZero 1` in a nontrivial `MulZeroOneClass`.

This file exists to minimize the dependencies of `Mathlib/Algebra/GroupWithZero/Defs.lean`,
which is a part of the algebraic hierarchy used by basic tactics.
-/

public section

assert_not_exists DenselyOrdered Ring

universe u

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

/--
Instance `NeZero.one` / 实例 `NeZero.one`

English:
instance NeZero.one
  signature: : NeZero (1 : M₀)
  body: ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩

中文:
实例 NeZero.one
  签名: : NeZero (1 : M₀)
  定义体: ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩

Depends on / 依赖: exists_pair_ne, one_mul, zero_mul
-/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩

/--
theorem `domain_nontrivial` / 定理 `domain_nontrivial`

English:
theorem domain_nontrivial
  given: [Zero M₀'] [One M₀'] (f : M₀' -> M₀) (zero : f 0 = 0) (one : f 1 = 1)
  proof: ⟨⟨0, 1, mt (congr_arg f) by
    rw [zero]; rw [one]
    exact zero_ne_one⟩⟩

中文:
定理 domain_nontrivial
  条件: [Zero M₀'] [One M₀'] (f : M₀' -> M₀) (zero : f 0 = 0) (one : f 1 = 1)
  证明: ⟨⟨0, 1, mt (congr_arg f) by
    rw [zero]; rw [one]
    exact zero_ne_one⟩⟩

Depends on / 依赖: congr_arg, zero_ne_one
-/
theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' -> M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
⟨⟨0, 1, mt (congr_arg f) by
    rw [zero]; rw [one]
    exact zero_ne_one⟩⟩

section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

/--
theorem `inv_ne_zero` / 定理 `inv_ne_zero`

English:
theorem inv_ne_zero
  given: (h : a != 0)
  statement: a⁻¹ != 0
  proof: fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

@[simp high] -- should take priority over `IsUnit.inv_mul_cancel`

中文:
定理 inv_ne_zero
  条件: (h : a != 0)
  结论: a⁻¹ != 0
  证明: fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

@[simp high] -- should take priority over `IsUnit.inv_mul_cancel`

Depends on / 依赖: a_eq_0
-/
theorem inv_ne_zero (h : a != 0) : a⁻¹ != 0 := fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

@[simp high] -- should take priority over `IsUnit.inv_mul_cancel`
/--
theorem `inv_mul_cancel₀` / 定理 `inv_mul_cancel₀`

English:
theorem inv_mul_cancel₀
  given: (h : a != 0)
  statement: a⁻¹ * a = 1
  proof: calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

中文:
定理 inv_mul_cancel₀
  条件: (h : a != 0)
  结论: a⁻¹ * a = 1
  证明: calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

Depends on / 依赖: inv_ne_zero
-/
theorem inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

end GroupWithZero
