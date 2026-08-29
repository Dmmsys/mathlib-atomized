/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Zify

/-!
# Field and action structures on the nonnegative rationals

This file provides additional results about `NNRat` that cannot live in earlier files due to import
cycles.
-/

@[expose] public section

open Function
open scoped NNRat

namespace NNRat
variable {α : Type*} {q : Rat>=0}

@[simp, norm_cast]
/--
lemma `coe_indicator` / 引理 `coe_indicator`

English:
lemma coe_indicator
  given: (s : Set α) (f : α -> Rat>=0) (a : α)
  proof: map_indicator coeHom _ _ _

中文:
引理 coe_indicator
  条件: (s : Set α) (f : α -> Rat>=0) (a : α)
  证明: map_indicator coeHom _ _ _

Depends on / 依赖: coeHom, map_indicator
-/
lemma coe_indicator (s : Set α) (f : α -> Rat>=0) (a : α) :
    ((s.indicator f a : Rat>=0) : Rat) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator coeHom _ _ _

end NNRat

open NNRat

namespace Rat

variable {p q : Rat}

/--
lemma `toNNRat_inv` / 引理 `toNNRat_inv`

English:
lemma toNNRat_inv
  given: (q : Rat)
  statement: toNNRat q⁻¹ = (toNNRat q)⁻¹
  proof: by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv]; rw [toNNRat_coe]

中文:
引理 toNNRat_inv
  条件: (q : Rat)
  结论: toNNRat q⁻¹ = (toNNRat q)⁻¹
  证明: by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv]; rw [toNNRat_coe]

Depends on / 依赖: Rat.coe_toNNRat, coe_inv, coe_toNNRat, inv_nonpos, inv_nonpos.mpr, inv_zero, le_total, nth_rw, toNNRat_coe, toNNRat_eq_zero, toNNRat_eq_zero.mpr
-/
lemma toNNRat_inv (q : Rat) : toNNRat q⁻¹ = (toNNRat q)⁻¹ := by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv]; rw [toNNRat_coe]

/--
lemma `toNNRat_div` / 引理 `toNNRat_div`

English:
lemma toNNRat_div
  given: (hp : 0 <= p)
  statement: toNNRat (p / q) = toNNRat p / toNNRat q
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← toNNRat_inv]; rw [← toNNRat_mul hp]

中文:
引理 toNNRat_div
  条件: (hp : 0 <= p)
  结论: toNNRat (p / q) = toNNRat p / toNNRat q
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← toNNRat_inv]; rw [← toNNRat_mul hp]

Depends on / 依赖: div_eq_mul_inv, toNNRat_inv, toNNRat_mul
-/
lemma toNNRat_div (hp : 0 <= p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [← toNNRat_inv]; rw [← toNNRat_mul hp]

/--
lemma `toNNRat_div'` / 引理 `toNNRat_div'`

English:
lemma toNNRat_div'
  given: (hq : 0 <= q)
  statement: toNNRat (p / q) = toNNRat p / toNNRat q
  proof: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [toNNRat_mul (inv_nonneg.2 hq)]; rw [toNNRat_inv]

中文:
引理 toNNRat_div'
  条件: (hq : 0 <= q)
  结论: toNNRat (p / q) = toNNRat p / toNNRat q
  证明: by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [toNNRat_mul (inv_nonneg.2 hq)]; rw [toNNRat_inv]

Depends on / 依赖: div_eq_inv_mul, inv_nonneg, toNNRat_inv, toNNRat_mul
-/
lemma toNNRat_div' (hq : 0 <= q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul]; rw [div_eq_inv_mul]; rw [toNNRat_mul (inv_nonneg.2 hq)]; rw [toNNRat_inv]

end Rat

/-! ### Numerator and denominator -/

namespace NNRat

variable {q : Rat>=0}

/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {α : Rat>=0 -> Sort*} (h : forall m n : Nat, α (m / n)) (q : Rat>=0)
  body: by
  rw [← num_div_den q]; apply h

中文:
定义 rec
  签名: {α : Rat>=0 -> Sort*} (h : 对任意 m n : 自然数, α (m / n)) (q : Rat>=0)
  定义体: by
  rw [← num_div_den q]; apply h
-/
protected def rec {α : Rat>=0 -> Sort*} (h : forall m n : Nat, α (m / n)) (q : Rat>=0) : α q := by
  rw [← num_div_den q]; apply h

/--
theorem `mul_num` / 定理 `mul_num`

English:
theorem mul_num
  given: (q₁ q₂ : Rat>=0)
  proof: by
  zify
  convert! Rat.mul_num q₁ q₂ <;> norm_cast

中文:
定理 mul_num
  条件: (q₁ q₂ : Rat>=0)
  证明: by
  zify
  convert! Rat.mul_num q₁ q₂ <;> norm_cast

Depends on / 依赖: Rat.mul_num, convert, mul_num
-/
theorem mul_num (q₁ q₂ : Rat>=0) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  zify
  convert! Rat.mul_num q₁ q₂ <;> norm_cast

/--
theorem `mul_den` / 定理 `mul_den`

English:
theorem mul_den
  given: (q₁ q₂ : Rat>=0)
  proof: by
  convert! Rat.mul_den q₁ q₂
  norm_cast

中文:
定理 mul_den
  条件: (q₁ q₂ : Rat>=0)
  证明: by
  convert! Rat.mul_den q₁ q₂
  norm_cast

Depends on / 依赖: Rat.mul_den, convert, mul_den
-/
theorem mul_den (q₁ q₂ : Rat>=0) :
    (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  convert! Rat.mul_den q₁ q₂
  norm_cast

/--
theorem `den_mul_den_eq_den_mul_gcd` / 定理 `den_mul_den_eq_den_mul_gcd`

English:
theorem den_mul_den_eq_den_mul_gcd
  given: (q₁ q₂ : Rat>=0)
  proof: by
  convert! Rat.den_mul_den_eq_den_mul_gcd q₁ q₂
  norm_cast

中文:
定理 den_mul_den_eq_den_mul_gcd
  条件: (q₁ q₂ : Rat>=0)
  证明: by
  convert! Rat.den_mul_den_eq_den_mul_gcd q₁ q₂
  norm_cast

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.of_isFractionRing, Rat.den_mul_den_eq_den_mul_gcd, convert, den_mul_den_eq_den_mul_gcd, of_isFractionRing
-/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : Rat>=0) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  convert! Rat.den_mul_den_eq_den_mul_gcd q₁ q₂
  norm_cast

/--
theorem `num_mul_num_eq_num_mul_gcd` / 定理 `num_mul_num_eq_num_mul_gcd`

English:
theorem num_mul_num_eq_num_mul_gcd
  given: (q₁ q₂ : Rat>=0)
  proof: by
  zify
  convert! Rat.num_mul_num_eq_num_mul_gcd q₁ q₂ <;> norm_cast

中文:
定理 num_mul_num_eq_num_mul_gcd
  条件: (q₁ q₂ : Rat>=0)
  证明: by
  zify
  convert! Rat.num_mul_num_eq_num_mul_gcd q₁ q₂ <;> norm_cast

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.of_isFractionRing, Rat.num_mul_num_eq_num_mul_gcd, convert, num_mul_num_eq_num_mul_gcd, of_isFractionRing
-/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : Rat>=0) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  zify
  convert! Rat.num_mul_num_eq_num_mul_gcd q₁ q₂ <;> norm_cast

end NNRat
