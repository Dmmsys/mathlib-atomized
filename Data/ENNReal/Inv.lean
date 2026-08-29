/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Operations

/-!
# Results about division in extended non-negative reals

This file establishes basic properties related to the inversion and division operations on `ℝ≥0∞`.
For instance, as a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation
with integer exponent.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : Real>=0∞} {r p q : Real>=0}

/--
theorem `div_eq_inv_mul` / 定理 `div_eq_inv_mul`

English:
theorem div_eq_inv_mul
  statement: a / b = b⁻¹ * a
  proof: by rw [div_eq_mul_inv, mul_comm]

中文:
定理 div_eq_inv_mul
  结论: a / b = b⁻¹ * a
  证明: by rw [div_eq_mul_inv, mul_comm]
-/
protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

/--
theorem `div_right_comm` / 定理 `div_right_comm`

English:
theorem div_right_comm
  statement: a / b / c = a / c / b
  proof: by
  simp only [div_eq_mul_inv, mul_right_comm]

中文:
定理 div_right_comm
  结论: a / b / c = a / c / b
  证明: by
  simp only [div_eq_mul_inv, mul_right_comm]
-/
protected theorem div_right_comm : a / b / c = a / c / b := by
  simp only [div_eq_mul_inv, mul_right_comm]

/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0 : Real>=0∞)⁻¹ = ∞
  proof: show sInf { b : Real>=0∞ | 1 <= 0 * b } = ∞ by simp

中文:
定理 inv_zero
  结论: (0 : 实数>=0∞)⁻¹ = ∞
  证明: show sInf { b : Real>=0∞ | 1 <= 0 * b } = ∞ by simp
-/
@[simp] theorem inv_zero : (0 : Real>=0∞)⁻¹ = ∞ :=
  show sInf { b : Real>=0∞ | 1 <= 0 * b } = ∞ by simp

/--
theorem `inv_top` / 定理 `inv_top`

English:
theorem inv_top
  statement: ∞⁻¹ = 0
  proof: bot_unique le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le by
    simp [*, h.ne', top_mul]

中文:
定理 inv_top
  结论: ∞⁻¹ = 0
  证明: bot_unique le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le by
    simp [*, h.ne', top_mul]
-/
@[simp] theorem inv_top : ∞⁻¹ = 0 :=
bot_unique le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le by
    simp [*, h.ne', top_mul]

/--
theorem `coe_inv_le` / 定理 `coe_inv_le`

English:
theorem coe_inv_le
  statement: (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹
  proof: le_sInf fun b (hb : 1 <= ↑r * b) =>
coe_le_iff.2 by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]

中文:
定理 coe_inv_le
  结论: (↑r⁻¹ : 实数>=0∞) <= (↑r)⁻¹
  证明: le_sInf fun b (hb : 1 <= ↑r * b) =>
coe_le_iff.2 by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]

Depends on / 依赖: NNReal, NNReal.inv_le_of_le_mul, coe_le_coe, coe_le_iff, coe_mul, coe_one, inv_le_of_le_mul, le_sInf
-/
theorem coe_inv_le : (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 <= ↑r * b) =>
coe_le_iff.2 by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (hr : r != 0)
  statement: (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
  proof: coe_inv_le.antisymm sInf_le mem_ofPred.2 by rw [← coe_mul, mul_inv_cancel₀ hr, coe_one]

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: (hr : r != 0)
  结论: (↑r⁻¹ : 实数>=0∞) = (↑r)⁻¹
  证明: coe_inv_le.antisymm sInf_le mem_ofPred.2 by rw [← coe_mul, mul_inv_cancel₀ hr, coe_one]

@[simp, norm_cast]

Depends on / 依赖: antisymm, coe_inv_le, coe_inv_le.antisymm, coe_mul, coe_one, mem_ofPred, sInf_le
-/
theorem coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹ :=
coe_inv_le.antisymm sInf_le mem_ofPred.2 by rw [← coe_mul, mul_inv_cancel₀ hr, coe_one]

@[simp, norm_cast]
/--
theorem `coe_inv'` / 定理 `coe_inv'`

English:
theorem coe_inv'
  given: [NeZero r]
  statement: (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
  proof: coe_inv (NeZero.ne r)

@[norm_cast]

中文:
定理 coe_inv'
  条件: [NeZero r]
  结论: (↑r⁻¹ : 实数>=0∞) = (↑r)⁻¹
  证明: coe_inv (NeZero.ne r)

@[norm_cast]

Depends on / 依赖: NeZero, NeZero.ne, coe_inv
-/
theorem coe_inv' [NeZero r] : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹ := coe_inv (NeZero.ne r)

@[norm_cast]
/--
theorem `coe_inv_two` / 定理 `coe_inv_two`

English:
theorem coe_inv_two
  statement: ((2⁻¹ : Real>=0) : Real>=0∞) = 2⁻¹
  proof: by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]

中文:
定理 coe_inv_two
  结论: ((2⁻¹ : 实数>=0) : 实数>=0∞) = 2⁻¹
  证明: by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]

Depends on / 依赖: IsSymmOp, IsSymmOp.symm_op, _root_, _root_.two_ne_zero, coe_inv, coe_two, symm_op, two_ne_zero, zipWith_comm_of_comm
-/
theorem coe_inv_two : ((2⁻¹ : Real>=0) : Real>=0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (hr : r != 0)
  statement: (↑(p / r) : Real>=0∞) = p / r
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [coe_mul]; rw [coe_inv hr]

@[simp, norm_cast]

中文:
定理 coe_div
  条件: (hr : r != 0)
  结论: (↑(p / r) : 实数>=0∞) = p / r
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [coe_mul]; rw [coe_inv hr]

@[simp, norm_cast]

Depends on / 依赖: coe_inv, coe_mul, div_eq_mul_inv
-/
theorem coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [coe_mul]; rw [coe_inv hr]

@[simp, norm_cast]
/--
theorem `coe_div'` / 定理 `coe_div'`

English:
theorem coe_div'
  given: [NeZero r]
  statement: (↑(p / r) : Real>=0∞) = p / r
  proof: coe_div (NeZero.ne r)

中文:
定理 coe_div'
  条件: [NeZero r]
  结论: (↑(p / r) : 实数>=0∞) = p / r
  证明: coe_div (NeZero.ne r)

Depends on / 依赖: NeZero, NeZero.ne, coe_div
-/
theorem coe_div' [NeZero r] : (↑(p / r) : Real>=0∞) = p / r := coe_div (NeZero.ne r)

/--
lemma `coe_div_le` / 引理 `coe_div_le`

English:
lemma coe_div_le
  statement: ↑(p / r) <= (p / r : Real>=0∞)
  proof: by
  simpa only [div_eq_mul_inv, coe_mul] using _root_.mul_le_mul_right coe_inv_le _

中文:
引理 coe_div_le
  结论: ↑(p / r) <= (p / r : 实数>=0∞)
  证明: by
  simpa only [div_eq_mul_inv, coe_mul] using _root_.mul_le_mul_right coe_inv_le _

Depends on / 依赖: _root_, _root_.mul_le_mul_right, coe_inv_le, coe_mul, div_eq_mul_inv, mul_le_mul_right
-/
lemma coe_div_le : ↑(p / r) <= (p / r : Real>=0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using _root_.mul_le_mul_right coe_inv_le _

/--
theorem `div_zero` / 定理 `div_zero`

English:
theorem div_zero
  given: (h : a != 0)
  statement: a / 0 = ∞
  proof: by simp [div_eq_mul_inv, h]

中文:
定理 div_zero
  条件: (h : a != 0)
  结论: a / 0 = ∞
  证明: by simp [div_eq_mul_inv, h]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_zero (h : a != 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvOneMonoid Real>=0∞
  body: { (inferInstance : DivInvMonoid Real>=0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

中文:
实例 :
  签名: DivInvOne幺半群 实数>=0∞
  定义体: { (inferInstance : DivInvMonoid Real>=0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

Depends on / 依赖: DivInvMonoid, coe_inj, coe_inv, coe_one, inv_one, one_ne_zero
-/
instance : DivInvOneMonoid Real>=0∞ :=
  { (inferInstance : DivInvMonoid Real>=0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

/--
theorem `inv_pow` / 定理 `inv_pow`

English:
theorem inv_pow
  statement: forall {a : Real>=0∞} {n : Nat}, (a ^ n)⁻¹ = a⁻¹ ^ n
  proof: pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]

中文:
定理 inv_pow
  结论: 对任意 {a : 实数>=0∞} {n : 自然数}, (a ^ n)⁻¹ = a⁻¹ ^ n
  证明: pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]
-/
protected theorem inv_pow : forall {a : Real>=0∞} {n : Nat}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : Real>=0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (h0 : a != 0) (ht : a != ∞)
  statement: a * a⁻¹ = 1
  proof: by
  lift a to Real>=0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel₀ h0

中文:
定理 mul_inv_cancel
  条件: (h0 : a != 0) (ht : a != ∞)
  结论: a * a⁻¹ = 1
  证明: by
  lift a to Real>=0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel₀ h0
-/
protected theorem mul_inv_cancel (h0 : a != 0) (ht : a != ∞) : a * a⁻¹ = 1 := by
  lift a to Real>=0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel₀ h0

/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: (h0 : a != 0) (ht : a != ∞)
  statement: a⁻¹ * a = 1
  proof: mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht

中文:
定理 inv_mul_cancel
  条件: (h0 : a != 0) (ht : a != ∞)
  结论: a⁻¹ * a = 1
  证明: mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht
-/
protected theorem inv_mul_cancel (h0 : a != 0) (ht : a != ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht

/--
lemma `inv_mul_cancel_left'` / 引理 `inv_mul_cancel_left'`

English:
lemma inv_mul_cancel_left'
  given: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

中文:
引理 inv_mul_cancel_left'
  条件: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]
-/
protected lemma inv_mul_cancel_left' (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

/--
lemma `inv_mul_cancel_left` / 引理 `inv_mul_cancel_left`

English:
lemma inv_mul_cancel_left
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a⁻¹ * (a * b) = b
  proof: ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

中文:
引理 inv_mul_cancel_left
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a⁻¹ * (a * b) = b
  证明: ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])
-/
protected lemma inv_mul_cancel_left (ha₀ : a != 0) (ha : a != ∞) : a⁻¹ * (a * b) = b :=
  ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

/--
lemma `mul_inv_cancel_left'` / 引理 `mul_inv_cancel_left'`

English:
lemma mul_inv_cancel_left'
  given: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

中文:
引理 mul_inv_cancel_left'
  条件: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]
-/
protected lemma mul_inv_cancel_left' (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

/--
lemma `mul_inv_cancel_left` / 引理 `mul_inv_cancel_left`

English:
lemma mul_inv_cancel_left
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a * (a⁻¹ * b) = b
  proof: ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

中文:
引理 mul_inv_cancel_left
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a * (a⁻¹ * b) = b
  证明: ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])
-/
protected lemma mul_inv_cancel_left (ha₀ : a != 0) (ha : a != ∞) : a * (a⁻¹ * b) = b :=
  ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

/--
lemma `mul_inv_cancel_right'` / 引理 `mul_inv_cancel_right'`

English:
lemma mul_inv_cancel_right'
  given: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  proof: by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

中文:
引理 mul_inv_cancel_right'
  条件: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  证明: by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]
-/
protected lemma mul_inv_cancel_right' (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

/--
lemma `mul_inv_cancel_right` / 引理 `mul_inv_cancel_right`

English:
lemma mul_inv_cancel_right
  given: (hb₀ : b != 0) (hb : b != ∞)
  statement: a * b * b⁻¹ = a
  proof: ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

中文:
引理 mul_inv_cancel_right
  条件: (hb₀ : b != 0) (hb : b != ∞)
  结论: a * b * b⁻¹ = a
  证明: ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])
-/
protected lemma mul_inv_cancel_right (hb₀ : b != 0) (hb : b != ∞) : a * b * b⁻¹ = a :=
  ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

/--
lemma `inv_mul_cancel_right'` / 引理 `inv_mul_cancel_right'`

English:
lemma inv_mul_cancel_right'
  given: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  proof: by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

中文:
引理 inv_mul_cancel_right'
  条件: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  证明: by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]
-/
protected lemma inv_mul_cancel_right' (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

/--
lemma `inv_mul_cancel_right` / 引理 `inv_mul_cancel_right`

English:
lemma inv_mul_cancel_right
  given: (hb₀ : b != 0) (hb : b != ∞)
  statement: a * b⁻¹ * b = a
  proof: ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

中文:
引理 inv_mul_cancel_right
  条件: (hb₀ : b != 0) (hb : b != ∞)
  结论: a * b⁻¹ * b = a
  证明: ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])
-/
protected lemma inv_mul_cancel_right (hb₀ : b != 0) (hb : b != ∞) : a * b⁻¹ * b = a :=
  ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

/--
lemma `mul_div_cancel_right'` / 引理 `mul_div_cancel_right'`

English:
lemma mul_div_cancel_right'
  given: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  proof: ENNReal.mul_inv_cancel_right' hb₀ hb

中文:
引理 mul_div_cancel_right'
  条件: (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0)
  证明: ENNReal.mul_inv_cancel_right' hb₀ hb
-/
protected lemma mul_div_cancel_right' (hb₀ : b = 0 -> a = 0) (hb : b = ∞ -> a = 0) :
    a * b / b = a := ENNReal.mul_inv_cancel_right' hb₀ hb

/--
lemma `mul_div_cancel_right` / 引理 `mul_div_cancel_right`

English:
lemma mul_div_cancel_right
  given: (hb₀ : b != 0) (hb : b != ∞)
  statement: a * b / b = a
  proof: ENNReal.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])

中文:
引理 mul_div_cancel_right
  条件: (hb₀ : b != 0) (hb : b != ∞)
  结论: a * b / b = a
  证明: ENNReal.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])
-/
protected lemma mul_div_cancel_right (hb₀ : b != 0) (hb : b != ∞) : a * b / b = a :=
  ENNReal.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])

/--
lemma `div_mul_cancel'` / 引理 `div_mul_cancel'`

English:
lemma div_mul_cancel'
  given: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  statement: b / a * a = b
  proof: ENNReal.inv_mul_cancel_right' ha₀ ha

中文:
引理 div_mul_cancel'
  条件: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  结论: b / a * a = b
  证明: ENNReal.inv_mul_cancel_right' ha₀ ha
-/
protected lemma div_mul_cancel' (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0) : b / a * a = b :=
  ENNReal.inv_mul_cancel_right' ha₀ ha

/--
lemma `div_mul_cancel` / 引理 `div_mul_cancel`

English:
lemma div_mul_cancel
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: b / a * a = b
  proof: ENNReal.div_mul_cancel' (by simp [ha₀]) (by simp [ha])

中文:
引理 div_mul_cancel
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: b / a * a = b
  证明: ENNReal.div_mul_cancel' (by simp [ha₀]) (by simp [ha])
-/
protected lemma div_mul_cancel (ha₀ : a != 0) (ha : a != ∞) : b / a * a = b :=
  ENNReal.div_mul_cancel' (by simp [ha₀]) (by simp [ha])

/--
lemma `mul_div_cancel'` / 引理 `mul_div_cancel'`

English:
lemma mul_div_cancel'
  given: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  statement: a * (b / a) = b
  proof: by
  rw [mul_comm]; rw [ENNReal.div_mul_cancel' ha₀ ha]

中文:
引理 mul_div_cancel'
  条件: (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0)
  结论: a * (b / a) = b
  证明: by
  rw [mul_comm]; rw [ENNReal.div_mul_cancel' ha₀ ha]
-/
protected lemma mul_div_cancel' (ha₀ : a = 0 -> b = 0) (ha : a = ∞ -> b = 0) : a * (b / a) = b := by
  rw [mul_comm]; rw [ENNReal.div_mul_cancel' ha₀ ha]

/--
lemma `mul_div_cancel` / 引理 `mul_div_cancel`

English:
lemma mul_div_cancel
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a * (b / a) = b
  proof: ENNReal.mul_div_cancel' (by simp [ha₀]) (by simp [ha])

中文:
引理 mul_div_cancel
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a * (b / a) = b
  证明: ENNReal.mul_div_cancel' (by simp [ha₀]) (by simp [ha])
-/
protected lemma mul_div_cancel (ha₀ : a != 0) (ha : a != ∞) : a * (b / a) = b :=
  ENNReal.mul_div_cancel' (by simp [ha₀]) (by simp [ha])

/--
theorem `mul_comm_div` / 定理 `mul_comm_div`

English:
theorem mul_comm_div
  statement: a / b * c = a * (c / b)
  proof: by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]

中文:
定理 mul_comm_div
  结论: a / b * c = a * (c / b)
  证明: by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]
-/
protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]

/--
theorem `mul_div_right_comm` / 定理 `mul_div_right_comm`

English:
theorem mul_div_right_comm
  statement: a * b / c = a / c * b
  proof: by
  simp only [div_eq_mul_inv, mul_right_comm]

中文:
定理 mul_div_right_comm
  结论: a * b / c = a / c * b
  证明: by
  simp only [div_eq_mul_inv, mul_right_comm]
-/
protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveInv Real>=0∞
  body: by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]

中文:
实例 :
  签名: InvolutiveInv 实数>=0∞
  定义体: by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]

Depends on / 依赖: coe_inv
-/
instance : InvolutiveInv Real>=0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]

/--
lemma `inv_eq_one` / 引理 `inv_eq_one`

English:
lemma inv_eq_one
  statement: a⁻¹ = 1 ↔ a = 1
  proof: by rw [← inv_inj, inv_inv, inv_one]

中文:
引理 inv_eq_one
  结论: a⁻¹ = 1 ↔ a = 1
  证明: by rw [← inv_inj, inv_inv, inv_one]
-/
@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]

/--
theorem `inv_eq_top` / 定理 `inv_eq_top`

English:
theorem inv_eq_top
  statement: a⁻¹ = ∞ ↔ a = 0
  proof: inv_zero ▸ inv_inj

中文:
定理 inv_eq_top
  结论: a⁻¹ = ∞ ↔ a = 0
  证明: inv_zero ▸ inv_inj
-/
@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj

/--
theorem `inv_ne_top` / 定理 `inv_ne_top`

English:
theorem inv_ne_top
  statement: a⁻¹ != ∞ ↔ a != 0
  proof: by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]

中文:
定理 inv_ne_top
  结论: a⁻¹ != ∞ ↔ a != 0
  证明: by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
-/
theorem inv_ne_top : a⁻¹ != ∞ ↔ a != 0 := by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
/--
theorem `inv_lt_top` / 定理 `inv_lt_top`

English:
theorem inv_lt_top
  given: {x : Real>=0∞}
  statement: x⁻¹ < ∞ ↔ 0 < x
  proof: by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

中文:
定理 inv_lt_top
  条件: {x : 实数>=0∞}
  结论: x⁻¹ < ∞ ↔ 0 < x
  证明: by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

Depends on / 依赖: inv_ne_top, lt_top_iff_ne_top, pos_iff_ne_zero
-/
theorem inv_lt_top {x : Real>=0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

/--
theorem `div_lt_top` / 定理 `div_lt_top`

English:
theorem div_lt_top
  given: {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0)
  statement: x / y < ∞
  proof: mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 div_lt_top
  条件: {x y : 实数>=0∞} (h1 : x != ∞) (h2 : y != 0)
  结论: x / y < ∞
  证明: mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: h1.lt_top, inv_ne_top, inv_ne_top.mpr, lt_top, mul_lt_top
-/
theorem div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0) : x / y < ∞ :=
  mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `div_ne_top` / 定理 `div_ne_top`

English:
theorem div_ne_top
  given: {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0)
  statement: x / y != ∞
  proof: (div_lt_top h1 h2).ne

@[simp]

中文:
定理 div_ne_top
  条件: {x y : 实数>=0∞} (h1 : x != ∞) (h2 : y != 0)
  结论: x / y != ∞
  证明: (div_lt_top h1 h2).ne

@[simp]

Depends on / 依赖: div_lt_top
-/
theorem div_ne_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0) : x / y != ∞ := (div_lt_top h1 h2).ne

@[simp]
/--
theorem `inv_eq_zero` / 定理 `inv_eq_zero`

English:
theorem inv_eq_zero
  statement: a⁻¹ = 0 ↔ a = ∞
  proof: inv_top ▸ inv_inj

中文:
定理 inv_eq_zero
  结论: a⁻¹ = 0 ↔ a = ∞
  证明: inv_top ▸ inv_inj
-/
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

/--
theorem `inv_ne_zero` / 定理 `inv_ne_zero`

English:
theorem inv_ne_zero
  statement: a⁻¹ != 0 ↔ a != ∞
  proof: by simp

中文:
定理 inv_ne_zero
  结论: a⁻¹ != 0 ↔ a != ∞
  证明: by simp
-/
protected theorem inv_ne_zero : a⁻¹ != 0 ↔ a != ∞ := by simp

/--
theorem `div_pos` / 定理 `div_pos`

English:
theorem div_pos
  given: (ha : a != 0) (hb : b != ∞)
  statement: 0 < a / b
  proof: ENNReal.mul_pos ha ENNReal.inv_ne_zero.2 hb

中文:
定理 div_pos
  条件: (ha : a != 0) (hb : b != ∞)
  结论: 0 < a / b
  证明: ENNReal.mul_pos ha ENNReal.inv_ne_zero.2 hb
-/
protected theorem div_pos (ha : a != 0) (hb : b != ∞) : 0 < a / b :=
ENNReal.mul_pos ha ENNReal.inv_ne_zero.2 hb

/--
theorem `inv_mul_le_iff` / 定理 `inv_mul_le_iff`

English:
theorem inv_mul_le_iff
  given: {x y z : Real>=0∞} (h1 : x != 0) (h2 : x != ∞)
  proof: by
  rw [← ENNReal.mul_le_mul_iff_right h1 h2]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel h1 h2]; rw [one_mul]

中文:
定理 inv_mul_le_iff
  条件: {x y z : 实数>=0∞} (h1 : x != 0) (h2 : x != ∞)
  证明: by
  rw [← ENNReal.mul_le_mul_iff_right h1 h2]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel h1 h2]; rw [one_mul]
-/
protected theorem inv_mul_le_iff {x y z : Real>=0∞} (h1 : x != 0) (h2 : x != ∞) :
    x⁻¹ * y <= z ↔ y <= x * z := by
  rw [← ENNReal.mul_le_mul_iff_right h1 h2]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel h1 h2]; rw [one_mul]

/--
theorem `mul_inv_le_iff` / 定理 `mul_inv_le_iff`

English:
theorem mul_inv_le_iff
  given: {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞)
  proof: by
  rw [mul_comm]; rw [ENNReal.inv_mul_le_iff h1 h2]; rw [mul_comm]

中文:
定理 mul_inv_le_iff
  条件: {x y z : 实数>=0∞} (h1 : y != 0) (h2 : y != ∞)
  证明: by
  rw [mul_comm]; rw [ENNReal.inv_mul_le_iff h1 h2]; rw [mul_comm]
-/
protected theorem mul_inv_le_iff {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞) :
    x * y⁻¹ <= z ↔ x <= z * y := by
  rw [mul_comm]; rw [ENNReal.inv_mul_le_iff h1 h2]; rw [mul_comm]

/--
theorem `div_le_iff` / 定理 `div_le_iff`

English:
theorem div_le_iff
  given: {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞)
  proof: by
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_le_iff h1 h2]

中文:
定理 div_le_iff
  条件: {x y z : 实数>=0∞} (h1 : y != 0) (h2 : y != ∞)
  证明: by
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_le_iff h1 h2]
-/
protected theorem div_le_iff {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞) :
    x / y <= z ↔ x <= z * y := by
  rw [div_eq_mul_inv]; rw [ENNReal.mul_inv_le_iff h1 h2]

/--
theorem `div_le_iff'` / 定理 `div_le_iff'`

English:
theorem div_le_iff'
  given: {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞)
  proof: by
  rw [mul_comm]; rw [ENNReal.div_le_iff h1 h2]

中文:
定理 div_le_iff'
  条件: {x y z : 实数>=0∞} (h1 : y != 0) (h2 : y != ∞)
  证明: by
  rw [mul_comm]; rw [ENNReal.div_le_iff h1 h2]
-/
protected theorem div_le_iff' {x y z : Real>=0∞} (h1 : y != 0) (h2 : y != ∞) :
    x / y <= z ↔ x <= y * z := by
  rw [mul_comm]; rw [ENNReal.div_le_iff h1 h2]

/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  given: {a b : Real>=0∞} (ha : a != 0 ∨ b != ∞) (hb : a != ∞ ∨ b != 0)
  proof: by
  cases b
  case top =>
    simp_all only [Ne, not_true_eq_false, or_false, top_ne_zero, not_false_eq_true, or_true,
      mul_top, inv_top, mul_zero]
  cases a
  case top =>
    simp_all only [Ne, top_ne_zero, not_false_eq_true, coe_ne_top, or_self, not_true_eq_false,
      coe_eq_zero, false_or, top_mul, inv_top, zero_mul]
  grind [_=_ coe_mul, coe_zero, inv_zero, = mul_inv, coe_ne_top, ENNReal.inv_eq_zero,
    =_ coe_inv, zero_mul, = mul_eq_zero, mul_top, mul_zero, top_mul]

中文:
定理 mul_inv
  条件: {a b : 实数>=0∞} (ha : a != 0 ∨ b != ∞) (hb : a != ∞ ∨ b != 0)
  证明: by
  cases b
  case top =>
    simp_all only [Ne, not_true_eq_false, or_false, top_ne_zero, not_false_eq_true, or_true,
      mul_top, inv_top, mul_zero]
  cases a
  case top =>
    simp_all only [Ne, top_ne_zero, not_false_eq_true, coe_ne_top, or_self, not_true_eq_false,
      coe_eq_zero, false_or, top_mul, inv_top, zero_mul]
  grind [_=_ coe_mul, coe_zero, inv_zero, = mul_inv, coe_ne_top, ENNReal.inv_eq_zero,
    =_ coe_inv, zero_mul, = mul_eq_zero, mul_top, mul_zero, top_mul]
-/
protected theorem mul_inv {a b : Real>=0∞} (ha : a != 0 ∨ b != ∞) (hb : a != ∞ ∨ b != 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  cases b
  case top =>
    simp_all only [Ne, not_true_eq_false, or_false, top_ne_zero, not_false_eq_true, or_true,
      mul_top, inv_top, mul_zero]
  cases a
  case top =>
    simp_all only [Ne, top_ne_zero, not_false_eq_true, coe_ne_top, or_self, not_true_eq_false,
      coe_eq_zero, false_or, top_mul, inv_top, zero_mul]
  grind [_=_ coe_mul, coe_zero, inv_zero, = mul_inv, coe_ne_top, ENNReal.inv_eq_zero,
    =_ coe_inv, zero_mul, = mul_eq_zero, mul_top, mul_zero, top_mul]

/--
theorem `inv_div` / 定理 `inv_div`

English:
theorem inv_div
  given: {a b : Real>=0∞} (htop : b != ∞ ∨ a != ∞) (hzero : b != 0 ∨ a != 0)
  proof: by
  rw [← ENNReal.inv_ne_zero] at htop
  rw [← ENNReal.inv_ne_top] at hzero
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.mul_inv htop hzero]; rw [mul_comm]; rw [inv_inv]

中文:
定理 inv_div
  条件: {a b : 实数>=0∞} (htop : b != ∞ ∨ a != ∞) (hzero : b != 0 ∨ a != 0)
  证明: by
  rw [← ENNReal.inv_ne_zero] at htop
  rw [← ENNReal.inv_ne_top] at hzero
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.mul_inv htop hzero]; rw [mul_comm]; rw [inv_inv]
-/
protected theorem inv_div {a b : Real>=0∞} (htop : b != ∞ ∨ a != ∞) (hzero : b != 0 ∨ a != 0) :
    (a / b)⁻¹ = b / a := by
  rw [← ENNReal.inv_ne_zero] at htop
  rw [← ENNReal.inv_ne_top] at hzero
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.mul_inv htop hzero]; rw [mul_comm]; rw [inv_inv]

/--
theorem `mul_div_mul_left` / 定理 `mul_div_mul_left`

English:
theorem mul_div_mul_left
  given: (a b : Real>=0∞) (hc : c != 0) (hc' : c != ⊤)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hc')]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [one_mul]

中文:
定理 mul_div_mul_left
  条件: (a b : 实数>=0∞) (hc : c != 0) (hc' : c != ⊤)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hc')]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [one_mul]
-/
protected theorem mul_div_mul_left (a b : Real>=0∞) (hc : c != 0) (hc' : c != ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hc')]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [one_mul]

/--
theorem `mul_div_mul_right` / 定理 `mul_div_mul_right`

English:
theorem mul_div_mul_right
  given: (a b : Real>=0∞) (hc : c != 0) (hc' : c != ⊤)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inr hc') (Or.inr hc)]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [mul_one]

中文:
定理 mul_div_mul_right
  条件: (a b : 实数>=0∞) (hc : c != 0) (hc' : c != ⊤)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inr hc') (Or.inr hc)]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [mul_one]
-/
protected theorem mul_div_mul_right (a b : Real>=0∞) (hc : c != 0) (hc' : c != ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inr hc') (Or.inr hc)]; rw [mul_mul_mul_comm]; rw [ENNReal.mul_inv_cancel hc hc']; rw [mul_one]

/--
theorem `sub_div` / 定理 `sub_div`

English:
theorem sub_div
  given: (h : 0 < b -> b < a -> c != 0)
  statement: (a - b) / c = a / c - b / c
  proof: by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)

@[simp]

中文:
定理 sub_div
  条件: (h : 0 < b -> b < a -> c != 0)
  结论: (a - b) / c = a / c - b / c
  证明: by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)

@[simp]
-/
protected theorem sub_div (h : 0 < b -> b < a -> c != 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)

@[simp]
/--
theorem `inv_pos` / 定理 `inv_pos`

English:
theorem inv_pos
  statement: 0 < a⁻¹ ↔ a != ∞
  proof: pos_iff_ne_zero.trans ENNReal.inv_ne_zero

中文:
定理 inv_pos
  结论: 0 < a⁻¹ ↔ a != ∞
  证明: pos_iff_ne_zero.trans ENNReal.inv_ne_zero
-/
protected theorem inv_pos : 0 < a⁻¹ ↔ a != ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero

/--
theorem `inv_strictAnti` / 定理 `inv_strictAnti`

English:
theorem inv_strictAnti
  statement: StrictAnti (Inv.inv : Real>=0∞ -> Real>=0∞)
  proof: by
  intro a b h
  lift a to Real>=0 using h.ne_top
  cases b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot]; rw [← coe_inv ha]; rw [coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]

中文:
定理 inv_strictAnti
  结论: 严格递减 (取逆.inv : 实数>=0∞ -> 实数>=0∞)
  证明: by
  intro a b h
  lift a to Real>=0 using h.ne_top
  cases b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot]; rw [← coe_inv ha]; rw [coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]

Depends on / 依赖: NNReal, NNReal.inv_lt_inv, coe_inv, coe_lt_coe, eq_or_ne, h.ne_bot, h.ne_top, inv_lt_inv, ne_bot, ne_top
-/
theorem inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ -> Real>=0∞) := by
  intro a b h
  lift a to Real>=0 using h.ne_top
  cases b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot]; rw [← coe_inv ha]; rw [coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]
/--
theorem `inv_lt_inv` / 定理 `inv_lt_inv`

English:
theorem inv_lt_inv
  statement: a⁻¹ < b⁻¹ ↔ b < a
  proof: inv_strictAnti.lt_iff_gt

中文:
定理 inv_lt_inv
  结论: a⁻¹ < b⁻¹ ↔ b < a
  证明: inv_strictAnti.lt_iff_gt
-/
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_gt

/--
theorem `inv_lt_iff_inv_lt` / 定理 `inv_lt_iff_inv_lt`

English:
theorem inv_lt_iff_inv_lt
  statement: a⁻¹ < b ↔ b⁻¹ < a
  proof: by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

中文:
定理 inv_lt_iff_inv_lt
  结论: a⁻¹ < b ↔ b⁻¹ < a
  证明: by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

Depends on / 依赖: ENNReal, ENNReal.inv_lt_inv, inv_inv, inv_lt_inv
-/
theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

/--
theorem `lt_inv_iff_lt_inv` / 定理 `lt_inv_iff_lt_inv`

English:
theorem lt_inv_iff_lt_inv
  statement: a < b⁻¹ ↔ b < a⁻¹
  proof: by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]

中文:
定理 lt_inv_iff_lt_inv
  结论: a < b⁻¹ ↔ b < a⁻¹
  证明: by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]

Depends on / 依赖: ENNReal, ENNReal.inv_lt_inv, inv_inv, inv_lt_inv
-/
theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]
/--
theorem `inv_le_inv` / 定理 `inv_le_inv`

English:
theorem inv_le_inv
  statement: a⁻¹ <= b⁻¹ ↔ b <= a
  proof: inv_strictAnti.le_iff_ge

中文:
定理 inv_le_inv
  结论: a⁻¹ <= b⁻¹ ↔ b <= a
  证明: inv_strictAnti.le_iff_ge
-/
protected theorem inv_le_inv : a⁻¹ <= b⁻¹ ↔ b <= a :=
  inv_strictAnti.le_iff_ge

/--
theorem `inv_le_iff_inv_le` / 定理 `inv_le_iff_inv_le`

English:
theorem inv_le_iff_inv_le
  statement: a⁻¹ <= b ↔ b⁻¹ <= a
  proof: by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

中文:
定理 inv_le_iff_inv_le
  结论: a⁻¹ <= b ↔ b⁻¹ <= a
  证明: by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, Fintype, inv_inv, inv_le_inv
-/
theorem inv_le_iff_inv_le : a⁻¹ <= b ↔ b⁻¹ <= a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

/--
theorem `le_inv_iff_le_inv` / 定理 `le_inv_iff_le_inv`

English:
theorem le_inv_iff_le_inv
  statement: a <= b⁻¹ ↔ b <= a⁻¹
  proof: by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

中文:
定理 le_inv_iff_le_inv
  结论: a <= b⁻¹ ↔ b <= a⁻¹
  证明: by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, Finite, inv_inv, inv_le_inv
-/
theorem le_inv_iff_le_inv : a <= b⁻¹ ↔ b <= a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

/--
theorem `inv_le_inv'` / 定理 `inv_le_inv'`

English:
theorem inv_le_inv'
  given: (h : a <= b)
  statement: b⁻¹ <= a⁻¹
  proof: ENNReal.inv_strictAnti.antitone h

中文:
定理 inv_le_inv'
  条件: (h : a <= b)
  结论: b⁻¹ <= a⁻¹
  证明: ENNReal.inv_strictAnti.antitone h

Depends on / 依赖: Finite, IsStablyFiniteRing, Semiring
-/
@[gcongr] protected theorem inv_le_inv' (h : a <= b) : b⁻¹ <= a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

/--
theorem `inv_lt_inv'` / 定理 `inv_lt_inv'`

English:
theorem inv_lt_inv'
  given: (h : a < b)
  statement: b⁻¹ < a⁻¹
  proof: ENNReal.inv_strictAnti h

@[simp]

中文:
定理 inv_lt_inv'
  条件: (h : a < b)
  结论: b⁻¹ < a⁻¹
  证明: ENNReal.inv_strictAnti h

@[simp]
-/
@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
/--
theorem `inv_le_one` / 定理 `inv_le_one`

English:
theorem inv_le_one
  statement: a⁻¹ <= 1 ↔ 1 <= a
  proof: by rw [inv_le_iff_inv_le, inv_one]

中文:
定理 inv_le_one
  结论: a⁻¹ <= 1 ↔ 1 <= a
  证明: by rw [inv_le_iff_inv_le, inv_one]
-/
protected theorem inv_le_one : a⁻¹ <= 1 ↔ 1 <= a := by rw [inv_le_iff_inv_le, inv_one]

/--
theorem `one_le_inv` / 定理 `one_le_inv`

English:
theorem one_le_inv
  statement: 1 <= a⁻¹ ↔ a <= 1
  proof: by rw [le_inv_iff_le_inv, inv_one]

@[simp]

中文:
定理 one_le_inv
  结论: 1 <= a⁻¹ ↔ a <= 1
  证明: by rw [le_inv_iff_le_inv, inv_one]

@[simp]
-/
protected theorem one_le_inv : 1 <= a⁻¹ ↔ a <= 1 := by rw [le_inv_iff_le_inv, inv_one]

@[simp]
/--
theorem `inv_lt_one` / 定理 `inv_lt_one`

English:
theorem inv_lt_one
  statement: a⁻¹ < 1 ↔ 1 < a
  proof: by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]

中文:
定理 inv_lt_one
  结论: a⁻¹ < 1 ↔ 1 < a
  证明: by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
-/
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
/--
theorem `one_lt_inv` / 定理 `one_lt_inv`

English:
theorem one_lt_inv
  statement: 1 < a⁻¹ ↔ a < 1
  proof: by rw [lt_inv_iff_lt_inv, inv_one]

中文:
定理 one_lt_inv
  结论: 1 < a⁻¹ ↔ a < 1
  证明: by rw [lt_inv_iff_lt_inv, inv_one]
-/
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
/--
Definition of `_root_.OrderIso.invENNReal` / `_root_.OrderIso.invENNReal` 的定义

English:
definition _root_.OrderIso.invENNReal
  signature: : Real>=0∞ ≃o Real>=0∞ᵒᵈ where
  body: ENNReal.inv_le_inv
  toEquiv := (Equiv.inv Real>=0∞).trans OrderDual.toDual

@[simp]

中文:
定义 _root_.OrderIso.invENN实数
  签名: : 实数>=0∞ ≃o 实数>=0∞ᵒᵈ where
  定义体: ENNReal.inv_le_inv
  toEquiv := (Equiv.inv Real>=0∞).trans OrderDual.toDual

@[simp]

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, inv_le_inv
-/
def _root_.OrderIso.invENNReal : Real>=0∞ ≃o Real>=0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv Real>=0∞).trans OrderDual.toDual

@[simp]
/--
theorem `_root_.OrderIso.invENNReal_symm_apply` / 定理 `_root_.OrderIso.invENNReal_symm_apply`

English:
theorem _root_.OrderIso.invENNReal_symm_apply
  given: (a : Real>=0∞ᵒᵈ)
  proof: rfl

中文:
定理 _root_.OrderIso.invENN实数_symm_apply
  条件: (a : 实数>=0∞ᵒᵈ)
  证明: rfl
-/
theorem _root_.OrderIso.invENNReal_symm_apply (a : Real>=0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

/--
theorem `div_top` / 定理 `div_top`

English:
theorem div_top
  statement: a / ∞ = 0
  proof: by rw [div_eq_mul_inv, inv_top, mul_zero]

中文:
定理 div_top
  结论: a / ∞ = 0
  证明: by rw [div_eq_mul_inv, inv_top, mul_zero]
-/
@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

/--
theorem `top_div` / 定理 `top_div`

English:
theorem top_div
  statement: ∞ / a = if a = ∞ then 0 else ∞
  proof: by simp [div_eq_mul_inv, top_mul']

中文:
定理 top_div
  结论: ∞ / a = if a = ∞ then 0 else ∞
  证明: by simp [div_eq_mul_inv, top_mul']

Depends on / 依赖: div_eq_mul_inv, top_mul
-/
theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']

/--
theorem `top_div_of_ne_top` / 定理 `top_div_of_ne_top`

English:
theorem top_div_of_ne_top
  given: (h : a != ∞)
  statement: ∞ / a = ∞
  proof: by simp [top_div, h]

中文:
定理 top_div_of_ne_top
  条件: (h : a != ∞)
  结论: ∞ / a = ∞
  证明: by simp [top_div, h]

Depends on / 依赖: top_div
-/
theorem top_div_of_ne_top (h : a != ∞) : ∞ / a = ∞ := by simp [top_div, h]

/--
theorem `top_div_coe` / 定理 `top_div_coe`

English:
theorem top_div_coe
  statement: ∞ / p = ∞
  proof: top_div_of_ne_top coe_ne_top

中文:
定理 top_div_coe
  结论: ∞ / p = ∞
  证明: top_div_of_ne_top coe_ne_top
-/
@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top

/--
theorem `top_div_of_lt_top` / 定理 `top_div_of_lt_top`

English:
theorem top_div_of_lt_top
  given: (h : a < ∞)
  statement: ∞ / a = ∞
  proof: top_div_of_ne_top h.ne

中文:
定理 top_div_of_lt_top
  条件: (h : a < ∞)
  结论: ∞ / a = ∞
  证明: top_div_of_ne_top h.ne

Depends on / 依赖: h.ne, top_div_of_ne_top
-/
theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne

/--
theorem `zero_div` / 定理 `zero_div`

English:
theorem zero_div
  statement: 0 / a = 0
  proof: zero_mul a⁻¹

中文:
定理 zero_div
  结论: 0 / a = 0
  证明: zero_mul a⁻¹
-/
@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹

/--
theorem `div_eq_top` / 定理 `div_eq_top`

English:
theorem div_eq_top
  statement: a / b = ∞ ↔ a != 0 ∧ b = 0 ∨ a = ∞ ∧ b != ∞
  proof: by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]

中文:
定理 div_eq_top
  结论: a / b = ∞ ↔ a != 0 ∧ b = 0 ∨ a = ∞ ∧ b != ∞
  证明: by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, div_eq_mul_inv, mul_eq_top
-/
theorem div_eq_top : a / b = ∞ ↔ a != 0 ∧ b = 0 ∨ a = ∞ ∧ b != ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]

/--
lemma `div_div_cancel'` / 引理 `div_div_cancel'`

English:
lemma div_div_cancel'
  given: (h₀ : a = 0 -> b = 0) (h₁ : a = ∞ -> b = 0)
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.inv_div (Or.inr ha') (Or.inr ha)]; rw [ENNReal.div_mul_cancel ha ha']

中文:
引理 div_div_cancel'
  条件: (h₀ : a = 0 -> b = 0) (h₁ : a = ∞ -> b = 0)
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.inv_div (Or.inr ha') (Or.inr ha)]; rw [ENNReal.div_mul_cancel ha ha']
-/
protected lemma div_div_cancel' (h₀ : a = 0 -> b = 0) (h₁ : a = ∞ -> b = 0) :
    a / (a / b) = b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul]; rw [ENNReal.inv_div (Or.inr ha') (Or.inr ha)]; rw [ENNReal.div_mul_cancel ha ha']

/--
lemma `div_div_cancel` / 引理 `div_div_cancel`

English:
lemma div_div_cancel
  given: {a b : Real>=0∞} (h₀ : a != 0) (h₁ : a != ∞)
  proof: ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])

中文:
引理 div_div_cancel
  条件: {a b : 实数>=0∞} (h₀ : a != 0) (h₁ : a != ∞)
  证明: ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])
-/
protected lemma div_div_cancel {a b : Real>=0∞} (h₀ : a != 0) (h₁ : a != ∞) :
    a / (a / b) = b :=
  ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])

/--
theorem `le_div_iff_mul_le` / 定理 `le_div_iff_mul_le`

English:
theorem le_div_iff_mul_le
  given: (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞)
  proof: by
  cases b with
  | top =>
    lift c to Real>=0 using ht.neg_resolve_left rfl
    rw [div_top]; rw [nonpos_iff_eq_zero]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  | coe b => ?_
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c != 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_iff_left hb coe_ne_top]; rw [ENNReal.div_mul_cancel hb coe_ne_top]

中文:
定理 le_div_iff_mul_le
  条件: (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞)
  证明: by
  cases b with
  | top =>
    lift c to Real>=0 using ht.neg_resolve_left rfl
    rw [div_top]; rw [nonpos_iff_eq_zero]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  | coe b => ?_
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c != 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_iff_left hb coe_ne_top]; rw [ENNReal.div_mul_cancel hb coe_ne_top]
-/
protected theorem le_div_iff_mul_le (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞) :
    a <= c / b ↔ a * b <= c := by
  cases b with
  | top =>
    lift c to Real>=0 using ht.neg_resolve_left rfl
    rw [div_top]; rw [nonpos_iff_eq_zero]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  | coe b => ?_
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c != 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_iff_left hb coe_ne_top]; rw [ENNReal.div_mul_cancel hb coe_ne_top]

/--
theorem `div_le_iff_le_mul` / 定理 `div_le_iff_le_mul`

English:
theorem div_le_iff_le_mul
  given: (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0)
  proof: by
  suffices a * b⁻¹ <= c ↔ a <= c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa

中文:
定理 div_le_iff_le_mul
  条件: (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0)
  证明: by
  suffices a * b⁻¹ <= c ↔ a <= c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa
-/
protected theorem div_le_iff_le_mul (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0) :
    a / b <= c ↔ a <= c * b := by
  suffices a * b⁻¹ <= c ↔ a <= c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa

/--
theorem `lt_div_iff_mul_lt` / 定理 `lt_div_iff_mul_lt`

English:
theorem lt_div_iff_mul_lt
  given: (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0)
  proof: lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)

中文:
定理 lt_div_iff_mul_lt
  条件: (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0)
  证明: lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)
-/
protected theorem lt_div_iff_mul_lt (hb0 : b != 0 ∨ c != ∞) (hbt : b != ∞ ∨ c != 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)

/--
theorem `div_le_of_le_mul` / 定理 `div_le_of_le_mul`

English:
theorem div_le_of_le_mul
  given: (h : a <= b * c)
  statement: a / c <= b
  proof: by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

中文:
定理 div_le_of_le_mul
  条件: (h : a <= b * c)
  结论: a / c <= b
  证明: by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

Depends on / 依赖: ENNReal, ENNReal.div_le_iff_le_mul, Or.inl, div_le_iff_le_mul
-/
theorem div_le_of_le_mul (h : a <= b * c) : a / c <= b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

/--
theorem `div_le_of_le_mul'` / 定理 `div_le_of_le_mul'`

English:
theorem div_le_of_le_mul'
  given: (h : a <= b * c)
  statement: a / b <= c
  proof: div_le_of_le_mul mul_comm b c ▸ h

中文:
定理 div_le_of_le_mul'
  条件: (h : a <= b * c)
  结论: a / b <= c
  证明: div_le_of_le_mul mul_comm b c ▸ h

Depends on / 依赖: div_le_of_le_mul, mul_comm
-/
theorem div_le_of_le_mul' (h : a <= b * c) : a / b <= c :=
div_le_of_le_mul mul_comm b c ▸ h

/--
theorem `div_self_le_one` / 定理 `div_self_le_one`

English:
theorem div_self_le_one
  statement: a / a <= 1
  proof: div_le_of_le_mul by rw [one_mul]

中文:
定理 div_self_le_one
  结论: a / a <= 1
  证明: div_le_of_le_mul by rw [one_mul]
-/
@[simp] protected theorem div_self_le_one : a / a <= 1 := div_le_of_le_mul by rw [one_mul]

/--
lemma `mul_inv_le_one` / 引理 `mul_inv_le_one`

English:
lemma mul_inv_le_one
  given: (a : Real>=0∞)
  statement: a * a⁻¹ <= 1
  proof: ENNReal.div_self_le_one

中文:
引理 mul_inv_le_one
  条件: (a : 实数>=0∞)
  结论: a * a⁻¹ <= 1
  证明: ENNReal.div_self_le_one
-/
@[simp] protected lemma mul_inv_le_one (a : Real>=0∞) : a * a⁻¹ <= 1 := ENNReal.div_self_le_one
/--
lemma `inv_mul_le_one` / 引理 `inv_mul_le_one`

English:
lemma inv_mul_le_one
  given: (a : Real>=0∞)
  statement: a⁻¹ * a <= 1
  proof: by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]

中文:
引理 inv_mul_le_one
  条件: (a : 实数>=0∞)
  结论: a⁻¹ * a <= 1
  证明: by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
-/
@[simp] protected lemma inv_mul_le_one (a : Real>=0∞) : a⁻¹ * a <= 1 := by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
/--
lemma `mul_inv_ne_top` / 引理 `mul_inv_ne_top`

English:
lemma mul_inv_ne_top
  given: (a : Real>=0∞)
  statement: a * a⁻¹ != ⊤
  proof: ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]

中文:
引理 mul_inv_ne_top
  条件: (a : 实数>=0∞)
  结论: a * a⁻¹ != ⊤
  证明: ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]

Depends on / 依赖: a.mul_inv_le_one, mul_inv_le_one, ne_top_of_le_ne_top, one_ne_top
-/
lemma mul_inv_ne_top (a : Real>=0∞) : a * a⁻¹ != ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]
/--
lemma `inv_mul_ne_top` / 引理 `inv_mul_ne_top`

English:
lemma inv_mul_ne_top
  given: (a : Real>=0∞)
  statement: a⁻¹ * a != ⊤
  proof: by simp [mul_comm]

中文:
引理 inv_mul_ne_top
  条件: (a : 实数>=0∞)
  结论: a⁻¹ * a != ⊤
  证明: by simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma inv_mul_ne_top (a : Real>=0∞) : a⁻¹ * a != ⊤ := by simp [mul_comm]

/--
theorem `mul_le_of_le_div` / 定理 `mul_le_of_le_div`

English:
theorem mul_le_of_le_div
  given: (h : a <= b / c)
  statement: a * c <= b
  proof: by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

中文:
定理 mul_le_of_le_div
  条件: (h : a <= b / c)
  结论: a * c <= b
  证明: by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

Depends on / 依赖: div_le_of_le_mul, inv_inv
-/
theorem mul_le_of_le_div (h : a <= b / c) : a * c <= b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

/--
theorem `mul_le_of_le_div'` / 定理 `mul_le_of_le_div'`

English:
theorem mul_le_of_le_div'
  given: (h : a <= b / c)
  statement: c * a <= b
  proof: mul_comm a c ▸ mul_le_of_le_div h

中文:
定理 mul_le_of_le_div'
  条件: (h : a <= b / c)
  结论: c * a <= b
  证明: mul_comm a c ▸ mul_le_of_le_div h

Depends on / 依赖: mul_comm, mul_le_of_le_div
-/
theorem mul_le_of_le_div' (h : a <= b / c) : c * a <= b :=
  mul_comm a c ▸ mul_le_of_le_div h

/--
theorem `div_lt_iff` / 定理 `div_lt_iff`

English:
theorem div_lt_iff
  given: (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞)
  statement: c / b < a ↔ c < a * b
  proof: lt_iff_lt_of_le_iff_le ENNReal.le_div_iff_mul_le h0 ht

中文:
定理 div_lt_iff
  条件: (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞)
  结论: c / b < a ↔ c < a * b
  证明: lt_iff_lt_of_le_iff_le ENNReal.le_div_iff_mul_le h0 ht
-/
protected theorem div_lt_iff (h0 : b != 0 ∨ c != 0) (ht : b != ∞ ∨ c != ∞) : c / b < a ↔ c < a * b :=
lt_iff_lt_of_le_iff_le ENNReal.le_div_iff_mul_le h0 ht

/--
theorem `mul_lt_of_lt_div` / 定理 `mul_lt_of_lt_div`

English:
theorem mul_lt_of_lt_div
  given: (h : a < b / c)
  statement: a * c < b
  proof: by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

中文:
定理 mul_lt_of_lt_div
  条件: (h : a < b / c)
  结论: a * c < b
  证明: by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, contrapose, div_le_of_le_mul
-/
theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

/--
theorem `mul_lt_of_lt_div'` / 定理 `mul_lt_of_lt_div'`

English:
theorem mul_lt_of_lt_div'
  given: (h : a < b / c)
  statement: c * a < b
  proof: mul_comm a c ▸ mul_lt_of_lt_div h

中文:
定理 mul_lt_of_lt_div'
  条件: (h : a < b / c)
  结论: c * a < b
  证明: mul_comm a c ▸ mul_lt_of_lt_div h

Depends on / 依赖: mul_comm, mul_lt_of_lt_div
-/
theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h

/--
theorem `div_lt_of_lt_mul` / 定理 `div_lt_of_lt_mul`

English:
theorem div_lt_of_lt_mul
  given: (h : a < b * c)
  statement: a / c < b
  proof: mul_lt_of_lt_div by rwa [div_eq_mul_inv, inv_inv]

中文:
定理 div_lt_of_lt_mul
  条件: (h : a < b * c)
  结论: a / c < b
  证明: mul_lt_of_lt_div by rwa [div_eq_mul_inv, inv_inv]

Depends on / 依赖: div_eq_mul_inv, inv_inv, mul_lt_of_lt_div
-/
theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
mul_lt_of_lt_div by rwa [div_eq_mul_inv, inv_inv]

/--
theorem `div_lt_of_lt_mul'` / 定理 `div_lt_of_lt_mul'`

English:
theorem div_lt_of_lt_mul'
  given: (h : a < b * c)
  statement: a / b < c
  proof: div_lt_of_lt_mul by rwa [mul_comm]

中文:
定理 div_lt_of_lt_mul'
  条件: (h : a < b * c)
  结论: a / b < c
  证明: div_lt_of_lt_mul by rwa [mul_comm]

Depends on / 依赖: div_lt_of_lt_mul, mul_comm
-/
theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
div_lt_of_lt_mul by rwa [mul_comm]

/--
lemma `div_lt_div_iff_left` / 引理 `div_lt_div_iff_left`

English:
lemma div_lt_div_iff_left
  given: (hc₀ : c != 0) (hc : c != ∞)
  statement: a / c < b / c ↔ a < b
  proof: ENNReal.mul_lt_mul_iff_left (by simpa) (by simpa)

中文:
引理 div_lt_div_iff_left
  条件: (hc₀ : c != 0) (hc : c != ∞)
  结论: a / c < b / c ↔ a < b
  证明: ENNReal.mul_lt_mul_iff_left (by simpa) (by simpa)
-/
protected lemma div_lt_div_iff_left (hc₀ : c != 0) (hc : c != ∞) : a / c < b / c ↔ a < b :=
  ENNReal.mul_lt_mul_iff_left (by simpa) (by simpa)

/--
lemma `div_lt_div_iff_right` / 引理 `div_lt_div_iff_right`

English:
lemma div_lt_div_iff_right
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a / b < a / c ↔ c < b
  proof: (ENNReal.mul_lt_mul_iff_right ha₀ ha).trans (by simp)

@[gcongr]

中文:
引理 div_lt_div_iff_right
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a / b < a / c ↔ c < b
  证明: (ENNReal.mul_lt_mul_iff_right ha₀ ha).trans (by simp)

@[gcongr]
-/
protected lemma div_lt_div_iff_right (ha₀ : a != 0) (ha : a != ∞) : a / b < a / c ↔ c < b :=
  (ENNReal.mul_lt_mul_iff_right ha₀ ha).trans (by simp)

@[gcongr]
/--
lemma `div_lt_div_right` / 引理 `div_lt_div_right`

English:
lemma div_lt_div_right
  given: (hc₀ : c != 0) (hc : c != ∞) (hab : a < b)
  statement: a / c < b / c
  proof: (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

@[gcongr]

中文:
引理 div_lt_div_right
  条件: (hc₀ : c != 0) (hc : c != ∞) (hab : a < b)
  结论: a / c < b / c
  证明: (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

@[gcongr]
-/
protected lemma div_lt_div_right (hc₀ : c != 0) (hc : c != ∞) (hab : a < b) : a / c < b / c :=
  (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

@[gcongr]
/--
lemma `div_lt_div_left` / 引理 `div_lt_div_left`

English:
lemma div_lt_div_left
  given: (ha₀ : a != 0) (ha : a != ∞) (hcb : c < b)
  statement: a / b < a / c
  proof: (ENNReal.div_lt_div_iff_right ha₀ ha).2 hcb

中文:
引理 div_lt_div_left
  条件: (ha₀ : a != 0) (ha : a != ∞) (hcb : c < b)
  结论: a / b < a / c
  证明: (ENNReal.div_lt_div_iff_right ha₀ ha).2 hcb
-/
protected lemma div_lt_div_left (ha₀ : a != 0) (ha : a != ∞) (hcb : c < b) : a / b < a / c :=
  (ENNReal.div_lt_div_iff_right ha₀ ha).2 hcb

/--
lemma `exists_pos_mul_lt` / 引理 `exists_pos_mul_lt`

English:
lemma exists_pos_mul_lt
  given: (ha : a != ∞) (hb₀ : b != 0)
  statement: exists c, 0 < c ∧ c * a < b
  proof: by
  obtain rfl | hb := eq_or_ne b ∞
  · exact ⟨1, by simpa [lt_top_iff_ne_top]⟩
  refine ⟨b / (a + 1), ENNReal.div_pos hb₀ (by finiteness), ENNReal.mul_lt_of_lt_div ?_⟩
  gcongr
  exact ENNReal.lt_add_right ha one_ne_zero

中文:
引理 存在_pos_mul_lt
  条件: (ha : a != ∞) (hb₀ : b != 0)
  结论: 存在 c, 0 < c ∧ c * a < b
  证明: by
  obtain rfl | hb := eq_or_ne b ∞
  · exact ⟨1, by simpa [lt_top_iff_ne_top]⟩
  refine ⟨b / (a + 1), ENNReal.div_pos hb₀ (by finiteness), ENNReal.mul_lt_of_lt_div ?_⟩
  gcongr
  exact ENNReal.lt_add_right ha one_ne_zero
-/
protected lemma exists_pos_mul_lt (ha : a != ∞) (hb₀ : b != 0) : exists c, 0 < c ∧ c * a < b := by
  obtain rfl | hb := eq_or_ne b ∞
  · exact ⟨1, by simpa [lt_top_iff_ne_top]⟩
  refine ⟨b / (a + 1), ENNReal.div_pos hb₀ (by finiteness), ENNReal.mul_lt_of_lt_div ?_⟩
  gcongr
  exact ENNReal.lt_add_right ha one_ne_zero

/--
theorem `inv_le_iff_le_mul` / 定理 `inv_le_iff_le_mul`

English:
theorem inv_le_iff_le_mul
  given: (h₁ : b = ∞ -> a != 0) (h₂ : a = ∞ -> b != 0)
  statement: a⁻¹ <= b ↔ 1 <= a * b
  proof: by
  rw [← one_div]; rw [ENNReal.div_le_iff_le_mul]; rw [mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]

中文:
定理 inv_le_iff_le_mul
  条件: (h₁ : b = ∞ -> a != 0) (h₂ : a = ∞ -> b != 0)
  结论: a⁻¹ <= b ↔ 1 <= a * b
  证明: by
  rw [← one_div]; rw [ENNReal.div_le_iff_le_mul]; rw [mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]

Depends on / 依赖: ENNReal, ENNReal.div_le_iff_le_mul, div_le_iff_le_mul, exacts, mul_comm, not_or_of_imp, one_div, or_not_of_imp
-/
theorem inv_le_iff_le_mul (h₁ : b = ∞ -> a != 0) (h₂ : a = ∞ -> b != 0) : a⁻¹ <= b ↔ 1 <= a * b := by
  rw [← one_div]; rw [ENNReal.div_le_iff_le_mul]; rw [mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]
/--
theorem `le_inv_iff_mul_le` / 定理 `le_inv_iff_mul_le`

English:
theorem le_inv_iff_mul_le
  statement: a <= b⁻¹ ↔ a * b <= 1
  proof: by
  rw [← one_div]; rw [ENNReal.le_div_iff_mul_le] <;>
    · right
      simp

中文:
定理 le_inv_iff_mul_le
  结论: a <= b⁻¹ ↔ a * b <= 1
  证明: by
  rw [← one_div]; rw [ENNReal.le_div_iff_mul_le] <;>
    · right
      simp

Depends on / 依赖: ENNReal, ENNReal.le_div_iff_mul_le, le_div_iff_mul_le, one_div
-/
theorem le_inv_iff_mul_le : a <= b⁻¹ ↔ a * b <= 1 := by
  rw [← one_div]; rw [ENNReal.le_div_iff_mul_le] <;>
    · right
      simp

/--
theorem `div_le_div` / 定理 `div_le_div`

English:
theorem div_le_div
  given: (hab : a <= b) (hdc : d <= c)
  statement: a / c <= b / d
  proof: div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)

中文:
定理 div_le_div
  条件: (hab : a <= b) (hdc : d <= c)
  结论: a / c <= b / d
  证明: div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)
-/
@[gcongr] protected theorem div_le_div (hab : a <= b) (hdc : d <= c) : a / c <= b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)

/--
theorem `div_le_div_left` / 定理 `div_le_div_left`

English:
theorem div_le_div_left
  given: (h : a <= b) (c : Real>=0∞)
  statement: c / b <= c / a
  proof: ENNReal.div_le_div le_rfl h

中文:
定理 div_le_div_left
  条件: (h : a <= b) (c : 实数>=0∞)
  结论: c / b <= c / a
  证明: ENNReal.div_le_div le_rfl h
-/
protected theorem div_le_div_left (h : a <= b) (c : Real>=0∞) : c / b <= c / a :=
  ENNReal.div_le_div le_rfl h

/--
theorem `div_le_div_right` / 定理 `div_le_div_right`

English:
theorem div_le_div_right
  given: (h : a <= b) (c : Real>=0∞)
  statement: a / c <= b / c
  proof: ENNReal.div_le_div h le_rfl

中文:
定理 div_le_div_right
  条件: (h : a <= b) (c : 实数>=0∞)
  结论: a / c <= b / c
  证明: ENNReal.div_le_div h le_rfl
-/
protected theorem div_le_div_right (h : a <= b) (c : Real>=0∞) : a / c <= b / c :=
  ENNReal.div_le_div h le_rfl

/--
theorem `eq_inv_of_mul_eq_one_left` / 定理 `eq_inv_of_mul_eq_one_left`

English:
theorem eq_inv_of_mul_eq_one_left
  given: (h : a * b = 1)
  statement: a = b⁻¹
  proof: by
  rw [← mul_one a]; rw [← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h)]; rw [← mul_assoc]; rw [h]; rw [one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

中文:
定理 eq_inv_of_mul_eq_one_left
  条件: (h : a * b = 1)
  结论: a = b⁻¹
  证明: by
  rw [← mul_one a]; rw [← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h)]; rw [← mul_assoc]; rw [h]; rw [one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h
-/
protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a]; rw [← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h)]; rw [← mul_assoc]; rw [h]; rw [one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

/--
theorem `mul_le_iff_le_inv` / 定理 `mul_le_iff_le_inv`

English:
theorem mul_le_iff_le_inv
  given: {a b r : Real>=0∞} (hr₀ : r != 0) (hr₁ : r != ∞)
  statement: r * a <= b ↔ a <= r⁻¹ * b
  proof: by
  rw [← @ENNReal.mul_le_mul_iff_right _ a _ hr₀ hr₁]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hr₀ hr₁]; rw [one_mul]

中文:
定理 mul_le_iff_le_inv
  条件: {a b r : 实数>=0∞} (hr₀ : r != 0) (hr₁ : r != ∞)
  结论: r * a <= b ↔ a <= r⁻¹ * b
  证明: by
  rw [← @ENNReal.mul_le_mul_iff_right _ a _ hr₀ hr₁]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hr₀ hr₁]; rw [one_mul]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.mul_le_mul_iff_right, mul_assoc, mul_inv_cancel, mul_le_mul_iff_right, one_mul
-/
theorem mul_le_iff_le_inv {a b r : Real>=0∞} (hr₀ : r != 0) (hr₁ : r != ∞) : r * a <= b ↔ a <= r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_iff_right _ a _ hr₀ hr₁]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hr₀ hr₁]; rw [one_mul]

/--
theorem `le_of_forall_nnreal_lt` / 定理 `le_of_forall_nnreal_lt`

English:
theorem le_of_forall_nnreal_lt
  given: {x y : Real>=0∞} (h : forall r : Real>=0, ↑r < x -> ↑r <= y)
  statement: x <= y
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to Real>=0 using ne_top_of_lt hr
  exact h r hr

中文:
定理 le_of_对任意_nnreal_lt
  条件: {x y : 实数>=0∞} (h : 对任意 r : 实数>=0, ↑r < x -> ↑r <= y)
  结论: x <= y
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to Real>=0 using ne_top_of_lt hr
  exact h r hr

Depends on / 依赖: le_of_forall_lt_imp_le_of_dense, ne_top_of_lt
-/
theorem le_of_forall_nnreal_lt {x y : Real>=0∞} (h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to Real>=0 using ne_top_of_lt hr
  exact h r hr

/--
lemma `eq_of_forall_nnreal_le_iff` / 引理 `eq_of_forall_nnreal_le_iff`

English:
lemma eq_of_forall_nnreal_le_iff
  given: {x y : Real>=0∞}
  statement: (forall r : Real>=0, ↑r <= x ↔ ↑r <= y) -> x = y
  proof: WithTop.eq_of_forall_coe_le_iff

中文:
引理 eq_of_对任意_nnreal_le_iff
  条件: {x y : 实数>=0∞}
  结论: (对任意 r : 实数>=0, ↑r <= x ↔ ↑r <= y) -> x = y
  证明: WithTop.eq_of_forall_coe_le_iff

Depends on / 依赖: WithTop, WithTop.eq_of_forall_coe_le_iff, eq_of_forall_coe_le_iff
-/
lemma eq_of_forall_nnreal_le_iff {x y : Real>=0∞} : (forall r : Real>=0, ↑r <= x ↔ ↑r <= y) -> x = y :=
  WithTop.eq_of_forall_coe_le_iff

/--
lemma `eq_of_forall_le_nnreal_iff` / 引理 `eq_of_forall_le_nnreal_iff`

English:
lemma eq_of_forall_le_nnreal_iff
  given: {x y : Real>=0∞}
  statement: (forall r : Real>=0, x <= r ↔ y <= r) -> x = y
  proof: WithTop.eq_of_forall_le_coe_iff

中文:
引理 eq_of_对任意_le_nnreal_iff
  条件: {x y : 实数>=0∞}
  结论: (对任意 r : 实数>=0, x <= r ↔ y <= r) -> x = y
  证明: WithTop.eq_of_forall_le_coe_iff

Depends on / 依赖: WithTop, WithTop.eq_of_forall_le_coe_iff, eq_of_forall_le_coe_iff
-/
lemma eq_of_forall_le_nnreal_iff {x y : Real>=0∞} : (forall r : Real>=0, x <= r ↔ y <= r) -> x = y :=
  WithTop.eq_of_forall_le_coe_iff

/--
theorem `le_of_forall_pos_nnreal_lt` / 定理 `le_of_forall_pos_nnreal_lt`

English:
theorem le_of_forall_pos_nnreal_lt
  given: {x y : Real>=0∞} (h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y)
  statement: x <= y
  proof: le_of_forall_nnreal_lt fun r hr =>
    (eq_zero_or_pos r).elim (fun h => h ▸ zero_le) fun h0 => h r h0 hr

中文:
定理 le_of_对任意_pos_nnreal_lt
  条件: {x y : 实数>=0∞} (h : 对任意 r : 实数>=0, 0 < r -> ↑r < x -> ↑r <= y)
  结论: x <= y
  证明: le_of_forall_nnreal_lt fun r hr =>
    (eq_zero_or_pos r).elim (fun h => h ▸ zero_le) fun h0 => h r h0 hr

Depends on / 依赖: eq_zero_or_pos, le_of_forall_nnreal_lt, zero_le
-/
theorem le_of_forall_pos_nnreal_lt {x y : Real>=0∞} (h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y) : x <= y :=
  le_of_forall_nnreal_lt fun r hr =>
    (eq_zero_or_pos r).elim (fun h => h ▸ zero_le) fun h0 => h r h0 hr

/--
theorem `eq_top_of_forall_nnreal_le` / 定理 `eq_top_of_forall_nnreal_le`

English:
theorem eq_top_of_forall_nnreal_le
  given: {x : Real>=0∞} (h : forall r : Real>=0, ↑r <= x)
  statement: x = ∞
  proof: top_unique le_of_forall_nnreal_lt fun r _ => h r

中文:
定理 eq_top_of_对任意_nnreal_le
  条件: {x : 实数>=0∞} (h : 对任意 r : 实数>=0, ↑r <= x)
  结论: x = ∞
  证明: top_unique le_of_forall_nnreal_lt fun r _ => h r

Depends on / 依赖: le_of_forall_nnreal_lt, top_unique
-/
theorem eq_top_of_forall_nnreal_le {x : Real>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞ :=
top_unique le_of_forall_nnreal_lt fun r _ => h r

/--
theorem `add_div` / 定理 `add_div`

English:
theorem add_div
  statement: (a + b) / c = a / c + b / c
  proof: right_distrib a b c⁻¹

中文:
定理 add_div
  结论: (a + b) / c = a / c + b / c
  证明: right_distrib a b c⁻¹
-/
protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹

/--
theorem `div_add_div_same` / 定理 `div_add_div_same`

English:
theorem div_add_div_same
  given: {a b c : Real>=0∞}
  statement: a / c + b / c = (a + b) / c
  proof: ENNReal.add_div.symm

中文:
定理 div_add_div_same
  条件: {a b c : 实数>=0∞}
  结论: a / c + b / c = (a + b) / c
  证明: ENNReal.add_div.symm
-/
protected theorem div_add_div_same {a b c : Real>=0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm

/--
theorem `div_self` / 定理 `div_self`

English:
theorem div_self
  given: (h0 : a != 0) (hI : a != ∞)
  statement: a / a = 1
  proof: ENNReal.mul_inv_cancel h0 hI

中文:
定理 div_self
  条件: (h0 : a != 0) (hI : a != ∞)
  结论: a / a = 1
  证明: ENNReal.mul_inv_cancel h0 hI
-/
protected theorem div_self (h0 : a != 0) (hI : a != ∞) : a / a = 1 :=
  ENNReal.mul_inv_cancel h0 hI

/--
theorem `mul_div_le` / 定理 `mul_div_le`

English:
theorem mul_div_le
  statement: a * (b / a) <= b
  proof: mul_le_of_le_div' le_rfl

中文:
定理 mul_div_le
  结论: a * (b / a) <= b
  证明: mul_le_of_le_div' le_rfl

Depends on / 依赖: le_rfl, mul_le_of_le_div
-/
theorem mul_div_le : a * (b / a) <= b :=
  mul_le_of_le_div' le_rfl

/--
theorem `eq_div_iff` / 定理 `eq_div_iff`

English:
theorem eq_div_iff
  given: (ha : a != 0) (ha' : a != ∞)
  statement: b = c / a ↔ a * b = c
  proof: ⟨fun h => by rw [h, ENNReal.mul_div_cancel ha ha'], fun h => by
    rw [← h]; rw [mul_div_assoc]; rw [ENNReal.mul_div_cancel ha ha']⟩

中文:
定理 eq_div_iff
  条件: (ha : a != 0) (ha' : a != ∞)
  结论: b = c / a ↔ a * b = c
  证明: ⟨fun h => by rw [h, ENNReal.mul_div_cancel ha ha'], fun h => by
    rw [← h]; rw [mul_div_assoc]; rw [ENNReal.mul_div_cancel ha ha']⟩

Depends on / 依赖: ENNReal, ENNReal.mul_div_cancel, mul_div_assoc, mul_div_cancel
-/
theorem eq_div_iff (ha : a != 0) (ha' : a != ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNReal.mul_div_cancel ha ha'], fun h => by
    rw [← h]; rw [mul_div_assoc]; rw [ENNReal.mul_div_cancel ha ha']⟩

/--
theorem `div_eq_div_iff` / 定理 `div_eq_div_iff`

English:
theorem div_eq_div_iff
  given: (ha : a != 0) (ha' : a != ∞) (hb : b != 0) (hb' : b != ∞)
  proof: by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb']; rw [mul_div_assoc]; rw [eq_comm]

中文:
定理 div_eq_div_iff
  条件: (ha : a != 0) (ha' : a != ∞) (hb : b != 0) (hb' : b != ∞)
  证明: by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb']; rw [mul_div_assoc]; rw [eq_comm]
-/
protected theorem div_eq_div_iff (ha : a != 0) (ha' : a != ∞) (hb : b != 0) (hb' : b != ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb']; rw [mul_div_assoc]; rw [eq_comm]

/--
theorem `div_eq_one_iff` / 定理 `div_eq_one_iff`

English:
theorem div_eq_one_iff
  given: {a b : Real>=0∞} (hb₀ : b != 0) (hb₁ : b != ∞)
  statement: a / b = 1 ↔ a = b
  proof: ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩

中文:
定理 div_eq_one_iff
  条件: {a b : 实数>=0∞} (hb₀ : b != 0) (hb₁ : b != ∞)
  结论: a / b = 1 ↔ a = b
  证明: ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩

Depends on / 依赖: ENNReal, ENNReal.div_self, div_self, eq_div_iff, h.symm, mul_one
-/
theorem div_eq_one_iff {a b : Real>=0∞} (hb₀ : b != 0) (hb₁ : b != ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩

/--
theorem `inv_two_add_inv_two` / 定理 `inv_two_add_inv_two`

English:
theorem inv_two_add_inv_two
  statement: (2 : Real>=0∞)⁻¹ + 2⁻¹ = 1
  proof: by
  rw [← two_mul]; rw [← div_eq_mul_inv]; rw [ENNReal.div_self two_ne_zero ofNat_ne_top]

中文:
定理 inv_two_add_inv_two
  结论: (2 : 实数>=0∞)⁻¹ + 2⁻¹ = 1
  证明: by
  rw [← two_mul]; rw [← div_eq_mul_inv]; rw [ENNReal.div_self two_ne_zero ofNat_ne_top]

Depends on / 依赖: ENNReal, ENNReal.div_self, div_eq_mul_inv, div_self, ofNat_ne_top, two_mul, two_ne_zero
-/
theorem inv_two_add_inv_two : (2 : Real>=0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul]; rw [← div_eq_mul_inv]; rw [ENNReal.div_self two_ne_zero ofNat_ne_top]

/--
theorem `inv_three_add_inv_three` / 定理 `inv_three_add_inv_three`

English:
theorem inv_three_add_inv_three
  statement: (3 : Real>=0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1
  proof: by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]

中文:
定理 inv_three_add_inv_three
  结论: (3 : 实数>=0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1
  证明: by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, mul_inv_cancel, ofNat_ne_top, three_ne_zero
-/
theorem inv_three_add_inv_three : (3 : Real>=0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]
/--
theorem `add_halves` / 定理 `add_halves`

English:
theorem add_halves
  given: (a : Real>=0∞)
  statement: a / 2 + a / 2 = a
  proof: by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_two_add_inv_two]; rw [mul_one]

@[simp]

中文:
定理 add_halves
  条件: (a : 实数>=0∞)
  结论: a / 2 + a / 2 = a
  证明: by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_two_add_inv_two]; rw [mul_one]

@[simp]
-/
protected theorem add_halves (a : Real>=0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [inv_two_add_inv_two]; rw [mul_one]

@[simp]
/--
theorem `add_thirds` / 定理 `add_thirds`

English:
theorem add_thirds
  given: (a : Real>=0∞)
  statement: a / 3 + a / 3 + a / 3 = a
  proof: by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [← mul_add]; rw [inv_three_add_inv_three]; rw [mul_one]

中文:
定理 add_thirds
  条件: (a : 实数>=0∞)
  结论: a / 3 + a / 3 + a / 3 = a
  证明: by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [← mul_add]; rw [inv_three_add_inv_three]; rw [mul_one]

Depends on / 依赖: div_eq_mul_inv, inv_three_add_inv_three, mul_add, mul_one
-/
theorem add_thirds (a : Real>=0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv]; rw [← mul_add]; rw [← mul_add]; rw [inv_three_add_inv_three]; rw [mul_one]

/--
theorem `div_eq_zero_iff` / 定理 `div_eq_zero_iff`

English:
theorem div_eq_zero_iff
  statement: a / b = 0 ↔ a = 0 ∨ b = ∞
  proof: by simp [div_eq_mul_inv]

中文:
定理 div_eq_zero_iff
  结论: a / b = 0 ↔ a = 0 ∨ b = ∞
  证明: by simp [div_eq_mul_inv]
-/
@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]

/--
theorem `div_pos_iff` / 定理 `div_pos_iff`

English:
theorem div_pos_iff
  statement: 0 < a / b ↔ a != 0 ∧ b != ∞
  proof: by simp [pos_iff_ne_zero, not_or]

中文:
定理 div_pos_iff
  结论: 0 < a / b ↔ a != 0 ∧ b != ∞
  证明: by simp [pos_iff_ne_zero, not_or]
-/
@[simp] theorem div_pos_iff : 0 < a / b ↔ a != 0 ∧ b != ∞ := by simp [pos_iff_ne_zero, not_or]

/--
lemma `div_ne_zero` / 引理 `div_ne_zero`

English:
lemma div_ne_zero
  statement: a / b != 0 ↔ a != 0 ∧ b != ∞
  proof: by
  rw [← pos_iff_ne_zero]; rw [div_pos_iff]

中文:
引理 div_ne_zero
  结论: a / b != 0 ↔ a != 0 ∧ b != ∞
  证明: by
  rw [← pos_iff_ne_zero]; rw [div_pos_iff]
-/
protected lemma div_ne_zero : a / b != 0 ↔ a != 0 ∧ b != ∞ := by
  rw [← pos_iff_ne_zero]; rw [div_pos_iff]

/--
lemma `div_mul` / 引理 `div_mul`

English:
lemma div_mul
  given: (a : Real>=0∞) (h0 : b != 0 ∨ c != 0) (htop : b != ∞ ∨ c != ∞)
  proof: by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv]; rw [inv_inv]
  · ring
  · simpa
  · simpa

中文:
引理 div_mul
  条件: (a : 实数>=0∞) (h0 : b != 0 ∨ c != 0) (htop : b != ∞ ∨ c != ∞)
  证明: by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv]; rw [inv_inv]
  · ring
  · simpa
  · simpa
-/
protected lemma div_mul (a : Real>=0∞) (h0 : b != 0 ∨ c != 0) (htop : b != ∞ ∨ c != ∞) :
    a / b * c = a / (b / c) := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv]; rw [inv_inv]
  · ring
  · simpa
  · simpa

/--
lemma `mul_div_mul_comm` / 引理 `mul_div_mul_comm`

English:
lemma mul_div_mul_comm
  given: (hc : c != 0 ∨ d != ∞) (hd : c != ∞ ∨ d != 0)
  proof: by
  simp only [div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring

中文:
引理 mul_div_mul_comm
  条件: (hc : c != 0 ∨ d != ∞) (hd : c != ∞ ∨ d != 0)
  证明: by
  simp only [div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring
-/
protected lemma mul_div_mul_comm (hc : c != 0 ∨ d != ∞) (hd : c != ∞ ∨ d != 0) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring

/--
theorem `half_pos` / 定理 `half_pos`

English:
theorem half_pos
  given: (h : a != 0)
  statement: 0 < a / 2
  proof: ENNReal.div_pos h ofNat_ne_top

中文:
定理 half_pos
  条件: (h : a != 0)
  结论: 0 < a / 2
  证明: ENNReal.div_pos h ofNat_ne_top
-/
protected theorem half_pos (h : a != 0) : 0 < a / 2 :=
  ENNReal.div_pos h ofNat_ne_top

/--
theorem `one_half_lt_one` / 定理 `one_half_lt_one`

English:
theorem one_half_lt_one
  statement: (2⁻¹ : Real>=0∞) < 1
  proof: ENNReal.inv_lt_one.2 one_lt_two

中文:
定理 one_half_lt_one
  结论: (2⁻¹ : 实数>=0∞) < 1
  证明: ENNReal.inv_lt_one.2 one_lt_two
-/
protected theorem one_half_lt_one : (2⁻¹ : Real>=0∞) < 1 :=
ENNReal.inv_lt_one.2 one_lt_two

/--
theorem `half_lt_self` / 定理 `half_lt_self`

English:
theorem half_lt_self
  given: (hz : a != 0) (ht : a != ∞)
  statement: a / 2 < a
  proof: by
  lift a to Real>=0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two]; rw [← coe_div]; rw [coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]

中文:
定理 half_lt_self
  条件: (hz : a != 0) (ht : a != ∞)
  结论: a / 2 < a
  证明: by
  lift a to Real>=0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two]; rw [← coe_div]; rw [coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]
-/
protected theorem half_lt_self (hz : a != 0) (ht : a != ∞) : a / 2 < a := by
  lift a to Real>=0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two]; rw [← coe_div]; rw [coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]

/--
theorem `half_le_self` / 定理 `half_le_self`

English:
theorem half_le_self
  statement: a / 2 <= a
  proof: le_add_self.trans_eq ENNReal.add_halves _

中文:
定理 half_le_self
  结论: a / 2 <= a
  证明: le_add_self.trans_eq ENNReal.add_halves _
-/
protected theorem half_le_self : a / 2 <= a :=
le_add_self.trans_eq ENNReal.add_halves _

/--
theorem `sub_half` / 定理 `sub_half`

English:
theorem sub_half
  given: (h : a != ∞)
  statement: a - a / 2 = a / 2
  proof: ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]

中文:
定理 sub_half
  条件: (h : a != ∞)
  结论: a - a / 2 = a / 2
  证明: ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]

Depends on / 依赖: ENNReal, ENNReal.sub_eq_of_eq_add, a.add_halves.symm, add_halves, sub_eq_of_eq_add
-/
theorem sub_half (h : a != ∞) : a - a / 2 = a / 2 := ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]
/--
theorem `one_sub_inv_two` / 定理 `one_sub_inv_two`

English:
theorem one_sub_inv_two
  statement: (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
  proof: by
  rw [← one_div]; rw [sub_half one_ne_top]

中文:
定理 one_sub_inv_two
  结论: (1 : 实数>=0∞) - 2⁻¹ = 2⁻¹
  证明: by
  rw [← one_div]; rw [sub_half one_ne_top]

Depends on / 依赖: MonoidHom, MonoidHom.mk, of_injective, one_div, one_ne_top, sub_half
-/
theorem one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹ := by
  rw [← one_div]; rw [sub_half one_ne_top]

/--
lemma `exists_lt_mul_left` / 引理 `exists_lt_mul_left`

English:
lemma exists_lt_mul_left
  given: {a b c : Real>=0∞} (hc : c < a * b)
  statement: exists a' < a, c < a' * b
  proof: by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩

中文:
引理 存在_lt_mul_left
  条件: {a b c : 实数>=0∞} (hc : c < a * b)
  结论: 存在 a' < a, c < a' * b
  证明: by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩
-/
private lemma exists_lt_mul_left {a b c : Real>=0∞} (hc : c < a * b) : exists a' < a, c < a' * b := by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩

/--
lemma `exists_lt_mul_right` / 引理 `exists_lt_mul_right`

English:
lemma exists_lt_mul_right
  given: {a b c : Real>=0∞} (hc : c < a * b)
  statement: exists b' < b, c < a * b'
  proof: by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc

中文:
引理 存在_lt_mul_right
  条件: {a b c : 实数>=0∞} (hc : c < a * b)
  结论: 存在 b' < b, c < a * b'
  证明: by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc
-/
private lemma exists_lt_mul_right {a b c : Real>=0∞} (hc : c < a * b) : exists b' < b, c < a * b' := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc

/--
lemma `mul_le_of_forall_lt` / 引理 `mul_le_of_forall_lt`

English:
lemma mul_le_of_forall_lt
  given: {a b c : Real>=0∞} (h : forall a' < a, forall b' < b, a' * b' <= c)
  statement: a * b <= c
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
exact le_trans hd.le h _ ha' _ hb'

中文:
引理 mul_le_of_对任意_lt
  条件: {a b c : 实数>=0∞} (h : 对任意 a' < a, 对任意 b' < b, a' * b' <= c)
  结论: a * b <= c
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
exact le_trans hd.le h _ ha' _ hb'

Depends on / 依赖: exists_lt_mul_left, exists_lt_mul_right, hd.le, le_of_forall_lt_imp_le_of_dense, le_trans
-/
lemma mul_le_of_forall_lt {a b c : Real>=0∞} (h : forall a' < a, forall b' < b, a' * b' <= c) : a * b <= c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
exact le_trans hd.le h _ ha' _ hb'

/--
lemma `le_mul_of_forall_lt` / 引理 `le_mul_of_forall_lt`

English:
lemma le_mul_of_forall_lt
  statement: {a b c : Real>=0∞} (h₁ : a != 0 ∨ b != ∞) (h₂ : a != ∞ ∨ b != 0)
  proof: by
  rw [← ENNReal.inv_le_inv]; rw [ENNReal.mul_inv h₁ h₂]
exact mul_le_of_forall_lt fun a' ha' b' hb' => ENNReal.le_inv_iff_le_inv.1
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

中文:
引理 le_mul_of_对任意_lt
  结论: {a b c : 实数>=0∞} (h₁ : a != 0 ∨ b != ∞) (h₂ : a != ∞ ∨ b != 0)
  证明: by
  rw [← ENNReal.inv_le_inv]; rw [ENNReal.mul_inv h₁ h₂]
exact mul_le_of_forall_lt fun a' ha' b' hb' => ENNReal.le_inv_iff_le_inv.1
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, ENNReal.le_inv_iff_le_inv, ENNReal.lt_inv_iff_lt_inv, ENNReal.mul_inv, Or.inl, Or.inr, inv_le_inv, le_inv_iff_le_inv, lt_inv_iff_lt_inv, mul_inv, mul_le_of_forall_lt, ne_top, trans_eq
-/
lemma le_mul_of_forall_lt {a b c : Real>=0∞} (h₁ : a != 0 ∨ b != ∞) (h₂ : a != ∞ ∨ b != 0)
    (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b := by
  rw [← ENNReal.inv_le_inv]; rw [ENNReal.mul_inv h₁ h₂]
exact mul_le_of_forall_lt fun a' ha' b' hb' => ENNReal.le_inv_iff_le_inv.1
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
/--
Definition of `orderIsoIicOneBirational` / `orderIsoIicOneBirational` 的定义

English:
definition orderIsoIicOneBirational
  signature: : Real>=0∞ ≃o Iic (1 : Real>=0∞)
  body: by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : Real>=0∞) <= x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]

中文:
定义 orderIsoIicOneBirational
  签名: : 实数>=0∞ ≃o 左无界右闭区间 (1 : 实数>=0∞)
  定义体: by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : Real>=0∞) <= x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_iff_right, ENNReal.inv_le_one, ENNReal.inv_lt_inv, ENNReal.one_le_inv, StrictMono, StrictMono.orderIsoOfRightInverse, Subtype, Subtype.ext, Subtype.mk_lt_mk, add_lt_add_iff_right, inv_inv, inv_le_one, inv_lt_inv, le_add_self, mk_lt_mk, one_le_inv, one_ne_top, orderIsoOfRightInverse, tsub_add_cancel_of_le
-/
def orderIsoIicOneBirational : Real>=0∞ ≃o Iic (1 : Real>=0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : Real>=0∞) <= x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]
/--
theorem `orderIsoIicOneBirational_symm_apply` / 定理 `orderIsoIicOneBirational_symm_apply`

English:
theorem orderIsoIicOneBirational_symm_apply
  given: (x : Iic (1 : Real>=0∞))
  proof: rfl

中文:
定理 orderIsoIicOneBirational_symm_apply
  条件: (x : 左无界右闭区间 (1 : 实数>=0∞))
  证明: rfl
-/
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : Real>=0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
/--
Definition of `orderIsoIicCoe` / `orderIsoIicCoe` 的定义

English:
definition orderIsoIicCoe
  signature: (a : Real>=0)
  body: OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 coe_toNNReal_le_self.trans x.2⟩
left_inv := fun _ => Subtype.ext toNNReal_coe _
right_inv := fun x => Subtype.ext coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]

中文:
定义 orderIsoIicCoe
  签名: (a : 实数>=0)
  定义体: OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 coe_toNNReal_le_self.trans x.2⟩
left_inv := fun _ => Subtype.ext toNNReal_coe _
right_inv := fun x => Subtype.ext coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toNNReal, Equiv.coe_fn_mk, OrderIso, OrderIso.symm, Subtype, Subtype.coe_le_coe, Subtype.ext, Subtype.mk_le_mk, coe_fn_mk, coe_le_coe, coe_ne_top, coe_toNNReal, coe_toNNReal_le_self, coe_toNNReal_le_self.trans, invFun, left_inv, map_rel_iff, mk_le_mk, ne_top_of_le_ne_top
-/
def orderIsoIicCoe (a : Real>=0) : Iic (a : Real>=0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 coe_toNNReal_le_self.trans x.2⟩
left_inv := fun _ => Subtype.ext toNNReal_coe _
right_inv := fun x => Subtype.ext coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]
/--
theorem `orderIsoIicCoe_symm_apply_coe` / 定理 `orderIsoIicCoe_symm_apply_coe`

English:
theorem orderIsoIicCoe_symm_apply_coe
  given: (a : Real>=0) (b : Iic a)
  proof: rfl

中文:
定理 orderIsoIicCoe_symm_apply_coe
  条件: (a : 实数>=0) (b : 左无界右闭区间 a)
  证明: rfl
-/
theorem orderIsoIicCoe_symm_apply_coe (a : Real>=0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : Real>=0∞) = b :=
  rfl

/--
Definition of `orderIsoUnitIntervalBirational` / `orderIsoUnitIntervalBirational` 的定义

English:
definition orderIsoUnitIntervalBirational
  signature: : Real>=0∞ ≃o Icc (0 : Real) 1
  body: orderIsoIicOneBirational.trans (orderIsoIicCoe 1).trans (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]

中文:
定义 orderIsoUnit整数ervalBirational
  签名: : 实数>=0∞ ≃o 闭区间 (0 : 实数) 1
  定义体: orderIsoIicOneBirational.trans (orderIsoIicCoe 1).trans (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]

Depends on / 依赖: NNReal, NNReal.orderIsoIccZeroCoe, orderIsoIccZeroCoe, orderIsoIicCoe, orderIsoIicOneBirational, orderIsoIicOneBirational.trans
-/
def orderIsoUnitIntervalBirational : Real>=0∞ ≃o Icc (0 : Real) 1 :=
orderIsoIicOneBirational.trans (orderIsoIicCoe 1).trans (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]
/--
theorem `orderIsoUnitIntervalBirational_apply_coe` / 定理 `orderIsoUnitIntervalBirational_apply_coe`

English:
theorem orderIsoUnitIntervalBirational_apply_coe
  given: (x : Real>=0∞)
  proof: rfl

中文:
定理 orderIsoUnit整数ervalBirational_apply_coe
  条件: (x : 实数>=0∞)
  证明: rfl
-/
theorem orderIsoUnitIntervalBirational_apply_coe (x : Real>=0∞) :
    (orderIsoUnitIntervalBirational x : Real) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl

/--
theorem `exists_inv_nat_lt` / 定理 `exists_inv_nat_lt`

English:
theorem exists_inv_nat_lt
  given: {a : Real>=0∞} (h : a != 0)
  statement: exists n : Nat, (n : Real>=0∞)⁻¹ < a
  proof: inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]

中文:
定理 存在_inv_nat_lt
  条件: {a : 实数>=0∞} (h : a != 0)
  结论: 存在 n : 自然数, (n : 实数>=0∞)⁻¹ < a
  证明: inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]

Depends on / 依赖: ENNReal, ENNReal.exists_nat_gt, ENNReal.inv_lt_inv, exists_nat_gt, inv_inv, inv_lt_inv, inv_ne_top
-/
theorem exists_inv_nat_lt {a : Real>=0∞} (h : a != 0) : exists n : Nat, (n : Real>=0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]

/--
theorem `exists_nat_pos_mul_gt` / 定理 `exists_nat_pos_mul_gt`

English:
theorem exists_nat_pos_mul_gt
  given: (ha : a != 0) (hb : b != ∞)
  statement: exists n > 0, b < (n : Nat) * a
  proof: let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 hn.pos, by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩

中文:
定理 存在_nat_pos_mul_gt
  条件: (ha : a != 0) (hb : b != ∞)
  结论: 存在 n > 0, b < (n : 自然数) * a
  证明: let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 hn.pos, by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩

Depends on / 依赖: ENNReal, ENNReal.div_lt_iff, ENNReal.exists_nat_gt, Nat.cast_pos, Or.inl, Or.inr, cast_pos, div_lt_iff, div_lt_top, exists_nat_gt, hn.pos
-/
theorem exists_nat_pos_mul_gt (ha : a != 0) (hb : b != ∞) : exists n > 0, b < (n : Nat) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 hn.pos, by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩

/--
theorem `exists_nat_mul_gt` / 定理 `exists_nat_mul_gt`

English:
theorem exists_nat_mul_gt
  given: (ha : a != 0) (hb : b != ∞)
  statement: exists n : Nat, b < n * a
  proof: (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

中文:
定理 存在_nat_mul_gt
  条件: (ha : a != 0) (hb : b != ∞)
  结论: 存在 n : 自然数, b < n * a
  证明: (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

Depends on / 依赖: And.right, exists_nat_pos_mul_gt
-/
theorem exists_nat_mul_gt (ha : a != 0) (hb : b != ∞) : exists n : Nat, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

/--
theorem `exists_nat_pos_inv_mul_lt` / 定理 `exists_nat_pos_inv_mul_lt`

English:
theorem exists_nat_pos_inv_mul_lt
  given: (ha : a != ∞) (hb : b != 0)
  proof: by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn

中文:
定理 存在_nat_pos_inv_mul_lt
  条件: (ha : a != ∞) (hb : b != 0)
  证明: by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, div_eq_inv_mul, div_lt_of_lt_mul, exists_nat_pos_mul_gt
-/
theorem exists_nat_pos_inv_mul_lt (ha : a != ∞) (hb : b != 0) :
    exists n > 0, ((n : Nat) : Real>=0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn

/--
theorem `exists_nnreal_pos_mul_lt` / 定理 `exists_nnreal_pos_mul_lt`

English:
theorem exists_nnreal_pos_mul_lt
  given: (ha : a != ∞) (hb : b != 0)
  statement: exists n > 0, ↑(n : Real>=0) * a < b
  proof: by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : Real>=0)⁻¹
  simp [*, npos.ne']

中文:
定理 存在_nnreal_pos_mul_lt
  条件: (ha : a != ∞) (hb : b != 0)
  结论: 存在 n > 0, ↑(n : 实数>=0) * a < b
  证明: by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : Real>=0)⁻¹
  simp [*, npos.ne']

Depends on / 依赖: exists_nat_pos_inv_mul_lt, npos.ne
-/
theorem exists_nnreal_pos_mul_lt (ha : a != ∞) (hb : b != 0) : exists n > 0, ↑(n : Real>=0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : Real>=0)⁻¹
  simp [*, npos.ne']

/--
theorem `exists_inv_two_pow_lt` / 定理 `exists_inv_two_pow_lt`

English:
theorem exists_inv_two_pow_lt
  given: (ha : a != 0)
  statement: exists n : Nat, 2⁻¹ ^ n < a
  proof: by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow]; rw [ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]

中文:
定理 存在_inv_two_pow_lt
  条件: (ha : a != 0)
  结论: 存在 n : 自然数, 2⁻¹ ^ n < a
  证明: by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow]; rw [ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]

Depends on / 依赖: ENNReal, ENNReal.inv_lt_inv, ENNReal.inv_pow, exists_inv_nat_lt, inv_lt_inv, inv_pow, lt_trans, lt_two_pow_self, n.lt_two_pow_self
-/
theorem exists_inv_two_pow_lt (ha : a != 0) : exists n : Nat, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow]; rw [ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (hr : r != 0) (n : Int)
  statement: (↑(r ^ n) : Real>=0∞) = (r : Real>=0∞) ^ n
  proof: by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, coe_pow, zpow_natCast]
  · have : r ^ n.succ != 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]

中文:
定理 coe_zpow
  条件: (hr : r != 0) (n : 整数)
  结论: (↑(r ^ n) : 实数>=0∞) = (r : 实数>=0∞) ^ n
  证明: by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, coe_pow, zpow_natCast]
  · have : r ^ n.succ != 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]

Depends on / 依赖: Int.ofNat_eq_natCast, coe_inv, coe_pow, n.succ, ofNat_eq_natCast, pow_ne_zero, zpow_natCast, zpow_negSucc
-/
theorem coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0∞) = (r : Real>=0∞) ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, coe_pow, zpow_natCast]
  · have : r ^ n.succ != 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]

/--
lemma `zero_zpow_def` / 引理 `zero_zpow_def`

English:
lemma zero_zpow_def
  given: (n : Int)
  statement: (0 : Real>=0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤
  proof: by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

中文:
引理 zero_zpow_def
  条件: (n : 整数)
  结论: (0 : 实数>=0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤
  证明: by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

Depends on / 依赖: Int.natCast_add, Nat.cast_add, cast_add, natCast_add
-/
lemma zero_zpow_def (n : Int) : (0 : Real>=0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤ := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

/--
lemma `top_zpow_def` / 引理 `top_zpow_def`

English:
lemma top_zpow_def
  given: (n : Int)
  statement: (⊤ : Real>=0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0
  proof: by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

中文:
引理 top_zpow_def
  条件: (n : 整数)
  结论: (⊤ : 实数>=0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0
  证明: by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

Depends on / 依赖: Int.natCast_add, Nat.cast_add, cast_add, natCast_add
-/
lemma top_zpow_def (n : Int) : (⊤ : Real>=0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0 := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

/--
theorem `zpow_pos` / 定理 `zpow_pos`

English:
theorem zpow_pos
  given: (ha : a != 0) (h'a : a != ∞) (n : Int)
  statement: 0 < a ^ n
  proof: by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]

中文:
定理 zpow_pos
  条件: (ha : a != 0) (h'a : a != ∞) (n : 整数)
  结论: 0 < a ^ n
  证明: by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]

Depends on / 依赖: ENNReal, ENNReal.inv_pos, ENNReal.pow_pos, bot_lt, false_and, ha.bot_lt, inv_pos, not_false_eq_true, pow_eq_top_iff, pow_pos, zpow_negSucc
-/
theorem zpow_pos (ha : a != 0) (h'a : a != ∞) (n : Int) : 0 < a ^ n := by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]

/--
theorem `zpow_lt_top` / 定理 `zpow_lt_top`

English:
theorem zpow_lt_top
  given: (ha : a != 0) (h'a : a != ∞) (n : Int)
  statement: a ^ n < ∞
  proof: by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]

中文:
定理 zpow_lt_top
  条件: (ha : a != 0) (h'a : a != ∞) (n : 整数)
  结论: a ^ n < ∞
  证明: by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]

Depends on / 依赖: ENNReal, ENNReal.pow_lt_top, ENNReal.pow_pos, a.lt_top, bot_lt, ha.bot_lt, inv_lt_top, lt_top, pow_lt_top, pow_pos, zpow_negSucc
-/
theorem zpow_lt_top (ha : a != 0) (h'a : a != ∞) (n : Int) : a ^ n < ∞ := by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
lemma `zpow_ne_top` / 引理 `zpow_ne_top`

English:
lemma zpow_ne_top
  given: {a : Real>=0∞} (ha : a != 0) (h'a : a != ∞) (n : Int)
  statement: a ^ n != ∞
  proof: (ENNReal.zpow_lt_top ha h'a n).ne

中文:
引理 zpow_ne_top
  条件: {a : 实数>=0∞} (ha : a != 0) (h'a : a != ∞) (n : 整数)
  结论: a ^ n != ∞
  证明: (ENNReal.zpow_lt_top ha h'a n).ne

Depends on / 依赖: ENNReal, ENNReal.zpow_lt_top, zpow_lt_top
-/
lemma zpow_ne_top {a : Real>=0∞} (ha : a != 0) (h'a : a != ∞) (n : Int) : a ^ n != ∞ :=
  (ENNReal.zpow_lt_top ha h'a n).ne

/--
theorem `exists_mem_Ico_zpow` / 定理 `exists_mem_Ico_zpow`

English:
theorem exists_mem_Ico_zpow
  given: {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤)
  proof: by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n <= x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]

中文:
定理 存在_mem_Ico_zpow
  条件: {x y : 实数>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤)
  证明: by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n <= x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_lt_coe, ENNReal.coe_zpow, NNReal, NNReal.exists_mem_Ico_zpow, coe_eq_zero, coe_le_coe, coe_lt_coe, coe_zpow, exists_mem_Ico_zpow, one_lt_coe_iff, zero_lt_one, zero_lt_one.trans
-/
theorem exists_mem_Ico_zpow {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤) :
    exists n : Int, x in Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n <= x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]

/--
theorem `exists_mem_Ioc_zpow` / 定理 `exists_mem_Ioc_zpow`

English:
theorem exists_mem_Ioc_zpow
  given: {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤)
  proof: by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n < x ∧ x <= y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]

中文:
定理 存在_mem_Ioc_zpow
  条件: {x y : 实数>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤)
  证明: by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n < x ∧ x <= y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_lt_coe, ENNReal.coe_zpow, NNReal, NNReal.exists_mem_Ioc_zpow, coe_eq_zero, coe_le_coe, coe_lt_coe, coe_zpow, exists_mem_Ioc_zpow, one_lt_coe_iff, zero_lt_one, zero_lt_one.trans
-/
theorem exists_mem_Ioc_zpow {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤) :
    exists n : Int, x in Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to Real>=0 using h'x
  lift y to Real>=0 using h'y
  have A : y != 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : exists n : Int, y ^ n < x ∧ x <= y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]

/--
theorem `Ioo_zero_top_eq_iUnion_Ico_zpow` / 定理 `Ioo_zero_top_eq_iUnion_Ico_zpow`

English:
theorem Ioo_zero_top_eq_iUnion_Ico_zpow
  given: {y : Real>=0∞} (hy : 1 < y) (h'y : y != ⊤)
  proof: by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]

中文:
定理 Ioo_zero_top_eq_iUnion_Ico_zpow
  条件: {y : 实数>=0∞} (hy : 1 < y) (h'y : y != ⊤)
  证明: by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]

Depends on / 依赖: ENNReal, ENNReal.zpow_lt_top, ENNReal.zpow_pos, exists_mem_Ico_zpow, hx.ne, lt_of_lt_of_le, lt_trans, mem_Ico, mem_Ioo, mem_iUnion, x.ne, zero_lt_one, zero_lt_one.trans, zpow_lt_top, zpow_pos
-/
theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : Real>=0∞} (hy : 1 < y) (h'y : y != ⊤) :
    Ioo (0 : Real>=0∞) (∞ : Real>=0∞) = ⋃ n : Int, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
/--
theorem `zpow_le_of_le` / 定理 `zpow_le_of_le`

English:
theorem zpow_le_of_le
  given: {x : Real>=0∞} (hx : 1 <= x) {a b : Int} (h : a <= b)
  statement: x ^ a <= x ^ b
  proof: by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_natCast, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using! h

中文:
定理 zpow_le_of_le
  条件: {x : 实数>=0∞} (hx : 1 <= x) {a b : 整数} (h : a <= b)
  结论: x ^ a <= x ^ b
  证明: by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_natCast, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using! h

Depends on / 依赖: ENNReal, ENNReal.inv_le_inv, ENNReal.inv_le_one, Int.le_of_ofNat_le_ofNat, Int.natCast_nonneg, Int.negSucc_lt_zero, Int.ofNat_eq_natCast, Int.ofNat_le, absurd, inv_le_inv, inv_le_one, le_of_ofNat_le_ofNat, lt_of_lt_of_le, natCast_nonneg, negSucc_lt_zero, neg_le_neg, not_le_of_gt, ofNat_eq_natCast, ofNat_le, one_le_pow_of_one_le
-/
theorem zpow_le_of_le {x : Real>=0∞} (hx : 1 <= x) {a b : Int} (h : a <= b) : x ^ a <= x ^ b := by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_natCast, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using! h

/--
theorem `monotone_zpow` / 定理 `monotone_zpow`

English:
theorem monotone_zpow
  given: {x : Real>=0∞} (hx : 1 <= x)
  statement: Monotone ((x ^ ·) : Int -> Real>=0∞)
  proof: fun _ _ h =>
  zpow_le_of_le hx h

中文:
定理 monotone_zpow
  条件: {x : 实数>=0∞} (hx : 1 <= x)
  结论: 递增 ((x ^ ·) : 整数 -> 实数>=0∞)
  证明: fun _ _ h =>
  zpow_le_of_le hx h
-/
theorem monotone_zpow {x : Real>=0∞} (hx : 1 <= x) : Monotone ((x ^ ·) : Int -> Real>=0∞) := fun _ _ h =>
  zpow_le_of_le hx h

/--
theorem `zpow_add` / 定理 `zpow_add`

English:
theorem zpow_add
  given: {x : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (m n : Int)
  proof: by
  lift x to Real>=0 using h'x
  replace hx : x != 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]

中文:
定理 zpow_add
  条件: {x : 实数>=0∞} (hx : x != 0) (h'x : x != ∞) (m n : 整数)
  证明: by
  lift x to Real>=0 using h'x
  replace hx : x != 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
-/
protected theorem zpow_add {x : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (m n : Int) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to Real>=0 using h'x
  replace hx : x != 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]

/--
theorem `zpow_neg` / 定理 `zpow_neg`

English:
theorem zpow_neg
  given: (x : Real>=0∞) (m : Int)
  statement: x ^ (-m) = (x ^ m)⁻¹
  proof: by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])

中文:
定理 zpow_neg
  条件: (x : 实数>=0∞) (m : 整数)
  结论: x ^ (-m) = (x ^ m)⁻¹
  证明: by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])
-/
protected theorem zpow_neg (x : Real>=0∞) (m : Int) : x ^ (-m) = (x ^ m)⁻¹ := by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])

/--
theorem `zpow_sub` / 定理 `zpow_sub`

English:
theorem zpow_sub
  given: {x : Real>=0∞} (x_ne_zero : x != 0) (x_ne_top : x != ⊤) (m n : Int)
  proof: by
  rw [sub_eq_add_neg]; rw [ENNReal.zpow_add x_ne_zero x_ne_top]; rw [ENNReal.zpow_neg]

中文:
定理 zpow_sub
  条件: {x : 实数>=0∞} (x_ne_zero : x != 0) (x_ne_top : x != ⊤) (m n : 整数)
  证明: by
  rw [sub_eq_add_neg]; rw [ENNReal.zpow_add x_ne_zero x_ne_top]; rw [ENNReal.zpow_neg]
-/
protected theorem zpow_sub {x : Real>=0∞} (x_ne_zero : x != 0) (x_ne_top : x != ⊤) (m n : Int) :
    x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ := by
  rw [sub_eq_add_neg]; rw [ENNReal.zpow_add x_ne_zero x_ne_top]; rw [ENNReal.zpow_neg]

/--
lemma `inv_zpow` / 引理 `inv_zpow`

English:
lemma inv_zpow
  given: (x : Real>=0∞) (n : Int)
  statement: x⁻¹ ^ n = (x ^ n)⁻¹
  proof: by
  cases n <;> simp [ENNReal.inv_pow]

中文:
引理 inv_zpow
  条件: (x : 实数>=0∞) (n : 整数)
  结论: x⁻¹ ^ n = (x ^ n)⁻¹
  证明: by
  cases n <;> simp [ENNReal.inv_pow]
-/
protected lemma inv_zpow (x : Real>=0∞) (n : Int) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  cases n <;> simp [ENNReal.inv_pow]

/--
lemma `inv_zpow'` / 引理 `inv_zpow'`

English:
lemma inv_zpow'
  given: (x : Real>=0∞) (n : Int)
  statement: x⁻¹ ^ n = x ^ (-n)
  proof: by
  rw [ENNReal.zpow_neg]; rw [ENNReal.inv_zpow]

中文:
引理 inv_zpow'
  条件: (x : 实数>=0∞) (n : 整数)
  结论: x⁻¹ ^ n = x ^ (-n)
  证明: by
  rw [ENNReal.zpow_neg]; rw [ENNReal.inv_zpow]
-/
protected lemma inv_zpow' (x : Real>=0∞) (n : Int) : x⁻¹ ^ n = x ^ (-n) := by
  rw [ENNReal.zpow_neg]; rw [ENNReal.inv_zpow]

/--
lemma `zpow_le_one_of_nonpos` / 引理 `zpow_le_one_of_nonpos`

English:
lemma zpow_le_one_of_nonpos
  given: {n : Int} (hn : n <= 0) {x : Real>=0∞} (hx : 1 <= x)
  statement: x ^ n <= 1
  proof: by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to Nat using by simpa using hn
  rw [← ENNReal.inv_zpow']; rw [ENNReal.inv_zpow]; rw [ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx

中文:
引理 zpow_le_one_of_nonpos
  条件: {n : 整数} (hn : n <= 0) {x : 实数>=0∞} (hx : 1 <= x)
  结论: x ^ n <= 1
  证明: by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to Nat using by simpa using hn
  rw [← ENNReal.inv_zpow']; rw [ENNReal.inv_zpow]; rw [ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx

Depends on / 依赖: ENNReal, ENNReal.inv_le_one, ENNReal.inv_zpow, inv_le_one, inv_zpow, mod_cast, neg_surjective
-/
lemma zpow_le_one_of_nonpos {n : Int} (hn : n <= 0) {x : Real>=0∞} (hx : 1 <= x) : x ^ n <= 1 := by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to Nat using by simpa using hn
  rw [← ENNReal.inv_zpow']; rw [ENNReal.inv_zpow]; rw [ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx

/--
lemma `isUnit_iff` / 引理 `isUnit_iff`

English:
lemma isUnit_iff
  statement: IsUnit a ↔ a != 0 ∧ a != ∞
  proof: by
  refine ⟨fun ha => ⟨ha.ne_zero, ?_⟩,
    fun ha => ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  simp at this

中文:
引理 isUnit_iff
  结论: 是单位 a ↔ a != 0 ∧ a != ∞
  证明: by
  refine ⟨fun ha => ⟨ha.ne_zero, ?_⟩,
    fun ha => ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  simp at this

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.mul_inv_cancel, ha.ne_zero, inv_mul_cancel, mul_inv_cancel, ne_zero
-/
lemma isUnit_iff : IsUnit a ↔ a != 0 ∧ a != ∞ := by
  refine ⟨fun ha => ⟨ha.ne_zero, ?_⟩,
    fun ha => ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  simp at this

/-- Left multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
/--
Definition of `mulLeftOrderIso` / `mulLeftOrderIso` 的定义

English:
definition mulLeftOrderIso
  signature: (a : Real>=0∞) (ha : IsUnit a)
  body: ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_right, ha.ne_zero, (isUnit_iff.1 ha).2]

中文:
定义 mulLeftOrderIso
  签名: (a : 实数>=0∞) (ha : 是单位 a)
  定义体: ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_right, ha.ne_zero, (isUnit_iff.1 ha).2]

Depends on / 依赖: ha.unit.mulLeft, mulLeft
-/
def mulLeftOrderIso (a : Real>=0∞) (ha : IsUnit a) : Real>=0∞ ≃o Real>=0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_right, ha.ne_zero, (isUnit_iff.1 ha).2]

/-- Right multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
/--
Definition of `mulRightOrderIso` / `mulRightOrderIso` 的定义

English:
definition mulRightOrderIso
  signature: (a : Real>=0∞) (ha : IsUnit a)
  body: ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_left, ha.ne_zero, (isUnit_iff.1 ha).2]

中文:
定义 mulRightOrderIso
  签名: (a : 实数>=0∞) (ha : 是单位 a)
  定义体: ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_left, ha.ne_zero, (isUnit_iff.1 ha).2]

Depends on / 依赖: ha.unit.mulRight, mulRight
-/
def mulRightOrderIso (a : Real>=0∞) (ha : IsUnit a) : Real>=0∞ ≃o Real>=0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_left, ha.ne_zero, (isUnit_iff.1 ha).2]

variable {ι κ : Sort*} {f g : ι -> Real>=0∞} {s : Set Real>=0∞} {a : Real>=0∞}

/--
lemma `mul_iSup` / 引理 `mul_iSup`

English:
lemma mul_iSup
  given: (a : Real>=0∞) (f : ι -> Real>=0∞)
  statement: a * ⨆ i, f i = ⨆ i, a * f i
  proof: by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

中文:
引理 mul_iSup
  条件: (a : 实数>=0∞) (f : ι -> 实数>=0∞)
  结论: a * ⨆ i, f i = ⨆ i, a * f i
  证明: by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

Depends on / 依赖: eq_comm, eq_or_ne, iSup_eq_zero, iSup_eq_zero.not, isUnit_iff, le_iSup_of_le, map_iSup, mulLeftOrderIso, not_forall, top_mul
-/
lemma mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  by_cases hf : forall i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

/--
lemma `iSup_mul` / 引理 `iSup_mul`

English:
lemma iSup_mul
  given: (f : ι -> Real>=0∞) (a : Real>=0∞)
  statement: (⨆ i, f i) * a = ⨆ i, f i * a
  proof: by
  simp [mul_comm, mul_iSup]

中文:
引理 iSup_mul
  条件: (f : ι -> 实数>=0∞) (a : 实数>=0∞)
  结论: (⨆ i, f i) * a = ⨆ i, f i * a
  证明: by
  simp [mul_comm, mul_iSup]

Depends on / 依赖: mul_comm, mul_iSup
-/
lemma iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp [mul_comm, mul_iSup]

/--
lemma `mul_sSup` / 引理 `mul_sSup`

English:
lemma mul_sSup
  given: {a : Real>=0∞}
  statement: a * sSup s = ⨆ b in s, a * b
  proof: by
  simp only [sSup_eq_iSup, mul_iSup]

中文:
引理 mul_sSup
  条件: {a : 实数>=0∞}
  结论: a * sSup s = ⨆ b in s, a * b
  证明: by
  simp only [sSup_eq_iSup, mul_iSup]

Depends on / 依赖: mul_iSup, sSup_eq_iSup
-/
lemma mul_sSup {a : Real>=0∞} : a * sSup s = ⨆ b in s, a * b := by
  simp only [sSup_eq_iSup, mul_iSup]

/--
lemma `sSup_mul` / 引理 `sSup_mul`

English:
lemma sSup_mul
  given: {a : Real>=0∞}
  statement: sSup s * a = ⨆ b in s, b * a
  proof: by
  simp only [sSup_eq_iSup, iSup_mul]

中文:
引理 sSup_mul
  条件: {a : 实数>=0∞}
  结论: sSup s * a = ⨆ b in s, b * a
  证明: by
  simp only [sSup_eq_iSup, iSup_mul]

Depends on / 依赖: iSup_mul, sSup_eq_iSup
-/
lemma sSup_mul {a : Real>=0∞} : sSup s * a = ⨆ b in s, b * a := by
  simp only [sSup_eq_iSup, iSup_mul]

/--
lemma `iSup_div` / 引理 `iSup_div`

English:
lemma iSup_div
  given: (f : ι -> Real>=0∞) (a : Real>=0∞)
  statement: iSup f / a = ⨆ i, f i / a
  proof: iSup_mul ..

中文:
引理 iSup_div
  条件: (f : ι -> 实数>=0∞) (a : 实数>=0∞)
  结论: iSup f / a = ⨆ i, f i / a
  证明: iSup_mul ..

Depends on / 依赖: iSup_mul
-/
lemma iSup_div (f : ι -> Real>=0∞) (a : Real>=0∞) : iSup f / a = ⨆ i, f i / a := iSup_mul ..
/--
lemma `sSup_div` / 引理 `sSup_div`

English:
lemma sSup_div
  given: (s : Set Real>=0∞) (a : Real>=0∞)
  statement: sSup s / a = ⨆ b in s, b / a
  proof: sSup_mul ..

中文:
引理 sSup_div
  条件: (s : 集合 实数>=0∞) (a : 实数>=0∞)
  结论: sSup s / a = ⨆ b in s, b / a
  证明: sSup_mul ..

Depends on / 依赖: sSup_mul
-/
lemma sSup_div (s : Set Real>=0∞) (a : Real>=0∞) : sSup s / a = ⨆ b in s, b / a := sSup_mul ..

/--
lemma `mul_iInf'` / 引理 `mul_iInf'`

English:
lemma mul_iInf'
  given: (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 0 -> Nonempty ι)
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (exists i, f i = 0)
    · rw [iInf_eq_bot.2, iInf_eq_bot.2, bot_eq_zero, mul_zero] <;>
        exact fun _ _ => ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i => top_mul fun hi => hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

中文:
引理 mul_iInf'
  条件: (hinfty : a = ∞ -> ⨅ i, f i = 0 -> 存在 i, f i = 0) (h₀ : a = 0 -> 非空 ι)
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (exists i, f i = 0)
    · rw [iInf_eq_bot.2, iInf_eq_bot.2, bot_eq_zero, mul_zero] <;>
        exact fun _ _ => ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i => top_mul fun hi => hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

Depends on / 依赖: bot_eq_zero, eq_comm, eq_or_ne, hinfty, iInf_eq_bot, iInf_eq_top, isUnit_iff, map_iInf, mulLeftOrderIso, mul_zero, top_mul
-/
lemma mul_iInf' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 0 -> Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (exists i, f i = 0)
    · rw [iInf_eq_bot.2, iInf_eq_bot.2, bot_eq_zero, mul_zero] <;>
        exact fun _ _ => ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i => top_mul fun hi => hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

/--
lemma `iInf_mul'` / 引理 `iInf_mul'`

English:
lemma iInf_mul'
  given: (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 0 -> Nonempty ι)
  proof: by simpa only [mul_comm a] using mul_iInf' hinfty h₀

中文:
引理 iInf_mul'
  条件: (hinfty : a = ∞ -> ⨅ i, f i = 0 -> 存在 i, f i = 0) (h₀ : a = 0 -> 非空 ι)
  证明: by simpa only [mul_comm a] using mul_iInf' hinfty h₀

Depends on / 依赖: hinfty, mul_comm, mul_iInf
-/
lemma iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 0 -> Nonempty ι) :
    (⨅ i, f i) * a = ⨅ i, f i * a := by simpa only [mul_comm a] using mul_iInf' hinfty h₀

/--
lemma `mul_iInf_of_ne` / 引理 `mul_iInf_of_ne`

English:
lemma mul_iInf_of_ne
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a * ⨅ i, f i = ⨅ i, a * f i
  proof: mul_iInf' (by simp [ha]) (by simp [ha₀])

中文:
引理 mul_iInf_of_ne
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a * ⨅ i, f i = ⨅ i, a * f i
  证明: mul_iInf' (by simp [ha]) (by simp [ha₀])

Depends on / 依赖: mul_iInf
-/
lemma mul_iInf_of_ne (ha₀ : a != 0) (ha : a != ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' (by simp [ha]) (by simp [ha₀])

/--
lemma `iInf_mul_of_ne` / 引理 `iInf_mul_of_ne`

English:
lemma iInf_mul_of_ne
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: (⨅ i, f i) * a = ⨅ i, f i * a
  proof: iInf_mul' (by simp [ha]) (by simp [ha₀])

中文:
引理 iInf_mul_of_ne
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: (⨅ i, f i) * a = ⨅ i, f i * a
  证明: iInf_mul' (by simp [ha]) (by simp [ha₀])

Depends on / 依赖: iInf_mul
-/
lemma iInf_mul_of_ne (ha₀ : a != 0) (ha : a != ∞) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' (by simp [ha]) (by simp [ha₀])

/--
lemma `mul_iInf` / 引理 `mul_iInf`

English:
lemma mul_iInf
  given: [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0)
  proof: mul_iInf' hinfty fun _ => ‹Nonempty ι›

中文:
引理 mul_iInf
  条件: [非空 ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> 存在 i, f i = 0)
  证明: mul_iInf' hinfty fun _ => ‹Nonempty ι›

Depends on / 依赖: Nonempty, hinfty, mul_iInf
-/
lemma mul_iInf [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := mul_iInf' hinfty fun _ => ‹Nonempty ι›

/--
lemma `iInf_mul` / 引理 `iInf_mul`

English:
lemma iInf_mul
  given: [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0)
  proof: iInf_mul' hinfty fun _ => ‹Nonempty ι›

中文:
引理 iInf_mul
  条件: [非空 ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> 存在 i, f i = 0)
  证明: iInf_mul' hinfty fun _ => ‹Nonempty ι›

Depends on / 依赖: Nonempty, hinfty, iInf_mul
-/
lemma iInf_mul [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := iInf_mul' hinfty fun _ => ‹Nonempty ι›

/--
lemma `iInf_div'` / 引理 `iInf_div'`

English:
lemma iInf_div'
  given: (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = ∞ -> Nonempty ι)
  proof: iInf_mul' (by simpa) (by simpa)

中文:
引理 iInf_div'
  条件: (hinfty : a = 0 -> ⨅ i, f i = 0 -> 存在 i, f i = 0) (h₀ : a = ∞ -> 非空 ι)
  证明: iInf_mul' (by simpa) (by simpa)

Depends on / 依赖: iInf_mul
-/
lemma iInf_div' (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = ∞ -> Nonempty ι) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_mul' (by simpa) (by simpa)

/--
lemma `iInf_div_of_ne` / 引理 `iInf_div_of_ne`

English:
lemma iInf_div_of_ne
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: (⨅ i, f i) / a = ⨅ i, f i / a
  proof: iInf_div' (by simp [ha₀]) (by simp [ha])

中文:
引理 iInf_div_of_ne
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: (⨅ i, f i) / a = ⨅ i, f i / a
  证明: iInf_div' (by simp [ha₀]) (by simp [ha])

Depends on / 依赖: iInf_div
-/
lemma iInf_div_of_ne (ha₀ : a != 0) (ha : a != ∞) : (⨅ i, f i) / a = ⨅ i, f i / a :=
  iInf_div' (by simp [ha₀]) (by simp [ha])

/--
lemma `iInf_div` / 引理 `iInf_div`

English:
lemma iInf_div
  given: [Nonempty ι] (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0)
  proof: iInf_div' hinfty fun _ => ‹Nonempty ι›

中文:
引理 iInf_div
  条件: [非空 ι] (hinfty : a = 0 -> ⨅ i, f i = 0 -> 存在 i, f i = 0)
  证明: iInf_div' hinfty fun _ => ‹Nonempty ι›

Depends on / 依赖: Nonempty, hinfty, iInf_div
-/
lemma iInf_div [Nonempty ι] (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_div' hinfty fun _ => ‹Nonempty ι›

/--
lemma `inv_iInf` / 引理 `inv_iInf`

English:
lemma inv_iInf
  given: (f : ι -> Real>=0∞)
  statement: (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹
  proof: OrderIso.invENNReal.map_iInf _

中文:
引理 inv_iInf
  条件: (f : ι -> 实数>=0∞)
  结论: (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹
  证明: OrderIso.invENNReal.map_iInf _

Depends on / 依赖: OrderIso, OrderIso.invENNReal.map_iInf, invENNReal, map_iInf
-/
lemma inv_iInf (f : ι -> Real>=0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := OrderIso.invENNReal.map_iInf _
/--
lemma `inv_iSup` / 引理 `inv_iSup`

English:
lemma inv_iSup
  given: (f : ι -> Real>=0∞)
  statement: (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹
  proof: OrderIso.invENNReal.map_iSup _

中文:
引理 inv_iSup
  条件: (f : ι -> 实数>=0∞)
  结论: (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹
  证明: OrderIso.invENNReal.map_iSup _

Depends on / 依赖: OrderIso, OrderIso.invENNReal.map_iSup, invENNReal, map_iSup
-/
lemma inv_iSup (f : ι -> Real>=0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := OrderIso.invENNReal.map_iSup _

/--
lemma `inv_sInf` / 引理 `inv_sInf`

English:
lemma inv_sInf
  given: (s : Set Real>=0∞)
  statement: (sInf s)⁻¹ = ⨆ a in s, a⁻¹
  proof: by simp [sInf_eq_iInf, inv_iInf]

中文:
引理 inv_sInf
  条件: (s : 集合 实数>=0∞)
  结论: (sInf s)⁻¹ = ⨆ a in s, a⁻¹
  证明: by simp [sInf_eq_iInf, inv_iInf]

Depends on / 依赖: inv_iInf, sInf_eq_iInf
-/
lemma inv_sInf (s : Set Real>=0∞) : (sInf s)⁻¹ = ⨆ a in s, a⁻¹ := by simp [sInf_eq_iInf, inv_iInf]
/--
lemma `inv_sSup` / 引理 `inv_sSup`

English:
lemma inv_sSup
  given: (s : Set Real>=0∞)
  statement: (sSup s)⁻¹ = ⨅ a in s, a⁻¹
  proof: by simp [sSup_eq_iSup, inv_iSup]

中文:
引理 inv_sSup
  条件: (s : 集合 实数>=0∞)
  结论: (sSup s)⁻¹ = ⨅ a in s, a⁻¹
  证明: by simp [sSup_eq_iSup, inv_iSup]

Depends on / 依赖: inv_iSup, sSup_eq_iSup
-/
lemma inv_sSup (s : Set Real>=0∞) : (sSup s)⁻¹ = ⨅ a in s, a⁻¹ := by simp [sSup_eq_iSup, inv_iSup]

/--
lemma `le_iInf_mul` / 引理 `le_iInf_mul`

English:
lemma le_iInf_mul
  given: {ι : Type*} (u v : ι -> Real>=0∞)
  proof: le_iInf fun i => mul_le_mul' (iInf_le u i) (iInf_le v i)

中文:
引理 le_iInf_mul
  条件: {ι : 类型} (u v : ι -> 实数>=0∞)
  证明: le_iInf fun i => mul_le_mul' (iInf_le u i) (iInf_le v i)

Depends on / 依赖: iInf_le, le_iInf, mul_le_mul
-/
lemma le_iInf_mul {ι : Type*} (u v : ι -> Real>=0∞) :
    (⨅ i, u i) * ⨅ i, v i <= ⨅ i, u i * v i :=
  le_iInf fun i => mul_le_mul' (iInf_le u i) (iInf_le v i)

/--
lemma `iSup_mul_le` / 引理 `iSup_mul_le`

English:
lemma iSup_mul_le
  given: {ι : Type*} {u v : ι -> Real>=0∞}
  proof: iSup_le fun i => mul_le_mul' (le_iSup u i) (le_iSup v i)

中文:
引理 iSup_mul_le
  条件: {ι : 类型} {u v : ι -> 实数>=0∞}
  证明: iSup_le fun i => mul_le_mul' (le_iSup u i) (le_iSup v i)

Depends on / 依赖: iSup_le, le_iSup, mul_le_mul
-/
lemma iSup_mul_le {ι : Type*} {u v : ι -> Real>=0∞} :
    ⨆ i, u i * v i <= (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun i => mul_le_mul' (le_iSup u i) (le_iSup v i)


/--
lemma `le_iInf_mul_iInf` / 引理 `le_iInf_mul_iInf`

English:
lemma le_iInf_mul_iInf
  statement: {g : κ -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exists j, g j != ∞)
  proof: by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j != ∞ := by simpa using hg
  rw [iInf_mul fun h => (hg h).elim]; rw [le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h => (hi h).elim] using ha i

中文:
引理 le_iInf_mul_iInf
  结论: {g : κ -> 实数>=0∞} (hf : 存在 i, f i != ∞) (hg : 存在 j, g j != ∞)
  证明: by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j != ∞ := by simpa using hg
  rw [iInf_mul fun h => (hg h).elim]; rw [le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h => (hi h).elim] using ha i

Depends on / 依赖: hg.nonempty, iInf_mul, iInf_ne_top_subtype, le_iInf_iff, mul_iInf, nonempty, nonempty_subtype, replace
-/
lemma le_iInf_mul_iInf {g : κ -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exists j, g j != ∞)
    (ha : forall i j, a <= f i * g j) : a <= (⨅ i, f i) * ⨅ j, g j := by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j != ∞ := by simpa using hg
  rw [iInf_mul fun h => (hg h).elim]; rw [le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h => (hi h).elim] using ha i

/--
lemma `iInf_mul_iInf` / 引理 `iInf_mul_iInf`

English:
lemma iInf_mul_iInf
  statement: {f g : ι -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exists j, g j != ∞)
  proof: by
  refine le_antisymm (le_iInf fun i => mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j => ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

中文:
引理 iInf_mul_iInf
  结论: {f g : ι -> 实数>=0∞} (hf : 存在 i, f i != ∞) (hg : 存在 j, g j != ∞)
  证明: by
  refine le_antisymm (le_iInf fun i => mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j => ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

Depends on / 依赖: iInf_le, iInf_le_of_le, le_antisymm, le_iInf, le_iInf_mul_iInf, mul_le_mul
-/
lemma iInf_mul_iInf {f g : ι -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exists j, g j != ∞)
    (h : forall i j, exists k, f k * g k <= f i * g j) : (⨅ i, f i) * ⨅ i, g i = ⨅ i, f i * g i := by
  refine le_antisymm (le_iInf fun i => mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j => ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

/--
lemma `smul_iSup` / 引理 `smul_iSup`

English:
lemma smul_iSup
  given: {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (f : ι -> Real>=0∞) (c : R)
  proof: by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

中文:
引理 smul_iSup
  条件: {R} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (f : ι -> 实数>=0∞) (c : R)
  证明: by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

Depends on / 依赖: ENNReal, ENNReal.mul_iSup, mul_iSup, smul_one_mul
-/
lemma smul_iSup {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (f : ι -> Real>=0∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

/--
lemma `smul_sSup` / 引理 `smul_sSup`

English:
lemma smul_sSup
  given: {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (s : Set Real>=0∞) (c : R)
  proof: by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]

中文:
引理 smul_sSup
  条件: {R} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (s : 集合 实数>=0∞) (c : R)
  证明: by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.mul_sSup, mul_sSup, simp_rw, smul_one_mul
-/
lemma smul_sSup {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (s : Set Real>=0∞) (c : R) :
    c • sSup s = ⨆ a in s, c • a := by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]
/--
theorem `ofReal_inv_of_pos` / 定理 `ofReal_inv_of_pos`

English:
theorem ofReal_inv_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
  proof: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]

中文:
定理 of实数_inv_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: 广义非负实数.of实数 x⁻¹ = (广义非负实数.of实数 x)⁻¹
  证明: by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal, Real.toNNReal_inv, coe_inj, coe_inv, ofReal, toNNReal, toNNReal_inv
-/
theorem ofReal_inv_of_pos {x : Real} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := by
  rw [ENNReal.ofReal]; rw [ENNReal.ofReal]; rw [← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]

/--
theorem `ofReal_inv_le` / 定理 `ofReal_inv_le`

English:
theorem ofReal_inv_le
  given: {x : Real}
  statement: ENNReal.ofReal x⁻¹ <= (ENNReal.ofReal x)⁻¹
  proof: by
  obtain hx | hx := lt_or_ge 0 x
  · simp [ofReal_inv_of_pos hx]
  · simp [ofReal_of_nonpos hx]

中文:
定理 of实数_inv_le
  条件: {x : 实数}
  结论: 广义非负实数.of实数 x⁻¹ <= (广义非负实数.of实数 x)⁻¹
  证明: by
  obtain hx | hx := lt_or_ge 0 x
  · simp [ofReal_inv_of_pos hx]
  · simp [ofReal_of_nonpos hx]

Depends on / 依赖: lt_or_ge, ofReal_inv_of_pos, ofReal_of_nonpos
-/
theorem ofReal_inv_le {x : Real} : ENNReal.ofReal x⁻¹ <= (ENNReal.ofReal x)⁻¹ := by
  obtain hx | hx := lt_or_ge 0 x
  · simp [ofReal_inv_of_pos hx]
  · simp [ofReal_of_nonpos hx]

/--
theorem `ofReal_div_le` / 定理 `ofReal_div_le`

English:
theorem ofReal_div_le
  given: {x y : Real} (hy : 0 <= y)
  proof: by
  simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
  gcongr
  exact ofReal_inv_le

中文:
定理 of实数_div_le
  条件: {x y : 实数} (hy : 0 <= y)
  证明: by
  simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
  gcongr
  exact ofReal_inv_le

Depends on / 依赖: div_eq_mul_inv, inv_nonneg, ofReal_inv_le, ofReal_mul, simp_rw
-/
theorem ofReal_div_le {x y : Real} (hy : 0 <= y) :
    ENNReal.ofReal (x / y) <= ENNReal.ofReal x / ENNReal.ofReal y := by
  simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
  gcongr
  exact ofReal_inv_le

/--
theorem `ofReal_div_of_pos` / 定理 `ofReal_div_of_pos`

English:
theorem ofReal_div_of_pos
  given: {x y : Real} (hy : 0 < y)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ofReal_mul' (inv_nonneg.2 hy.le)]; rw [ofReal_inv_of_pos hy]

中文:
定理 of实数_div_of_pos
  条件: {x y : 实数} (hy : 0 < y)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ofReal_mul' (inv_nonneg.2 hy.le)]; rw [ofReal_inv_of_pos hy]

Depends on / 依赖: div_eq_mul_inv, hy.le, inv_nonneg, ofReal_inv_of_pos, ofReal_mul
-/
theorem ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [ofReal_mul' (inv_nonneg.2 hy.le)]; rw [ofReal_inv_of_pos hy]

/--
theorem `toNNReal_inv` / 定理 `toNNReal_inv`

English:
theorem toNNReal_inv
  given: (a : Real>=0∞)
  statement: a⁻¹.toNNReal = a.toNNReal⁻¹
  proof: by
  cases a with
  | top => simp
  | coe a =>
    rcases eq_or_ne a 0 with (rfl | ha); · simp
    rw [← coe_inv ha]; rw [toNNReal_coe]; rw [toNNReal_coe]

中文:
定理 toNN实数_inv
  条件: (a : 实数>=0∞)
  结论: a⁻¹.toNN实数 = a.toNN实数⁻¹
  证明: by
  cases a with
  | top => simp
  | coe a =>
    rcases eq_or_ne a 0 with (rfl | ha); · simp
    rw [← coe_inv ha]; rw [toNNReal_coe]; rw [toNNReal_coe]
-/
@[simp] theorem toNNReal_inv (a : Real>=0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  cases a with
  | top => simp
  | coe a =>
    rcases eq_or_ne a 0 with (rfl | ha); · simp
    rw [← coe_inv ha]; rw [toNNReal_coe]; rw [toNNReal_coe]

/--
theorem `toNNReal_div` / 定理 `toNNReal_div`

English:
theorem toNNReal_div
  given: (a b : Real>=0∞)
  statement: (a / b).toNNReal = a.toNNReal / b.toNNReal
  proof: by
  rw [div_eq_mul_inv]; rw [toNNReal_mul]; rw [toNNReal_inv]; rw [div_eq_mul_inv]

中文:
定理 toNN实数_div
  条件: (a b : 实数>=0∞)
  结论: (a / b).toNN实数 = a.toNN实数 / b.toNN实数
  证明: by
  rw [div_eq_mul_inv]; rw [toNNReal_mul]; rw [toNNReal_inv]; rw [div_eq_mul_inv]
-/
@[simp] theorem toNNReal_div (a b : Real>=0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv]; rw [toNNReal_mul]; rw [toNNReal_inv]; rw [div_eq_mul_inv]

/--
theorem `toReal_inv` / 定理 `toReal_inv`

English:
theorem toReal_inv
  given: (a : Real>=0∞)
  statement: a⁻¹.toReal = a.toReal⁻¹
  proof: by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]

中文:
定理 to实数_inv
  条件: (a : 实数>=0∞)
  结论: a⁻¹.to实数 = a.to实数⁻¹
  证明: by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]
-/
@[simp] theorem toReal_inv (a : Real>=0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]

/--
theorem `toReal_div` / 定理 `toReal_div`

English:
theorem toReal_div
  given: (a b : Real>=0∞)
  statement: (a / b).toReal = a.toReal / b.toReal
  proof: by
  rw [div_eq_mul_inv]; rw [toReal_mul]; rw [toReal_inv]; rw [div_eq_mul_inv]

中文:
定理 to实数_div
  条件: (a b : 实数>=0∞)
  结论: (a / b).to实数 = a.to实数 / b.to实数
  证明: by
  rw [div_eq_mul_inv]; rw [toReal_mul]; rw [toReal_inv]; rw [div_eq_mul_inv]
-/
@[simp] theorem toReal_div (a b : Real>=0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv]; rw [toReal_mul]; rw [toReal_inv]; rw [div_eq_mul_inv]

end Inv
end ENNReal
