/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Subsingleton
public import Mathlib.Tactic.Attr.Core

import Mathlib.Tactic.Attr.Register

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.
This file contains the basic lemmas on units in a monoid, especially focusing on singleton types
and unique types.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

public section

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

section HasElem

@[to_additive]
/--
theorem `unique_one` / 定理 `unique_one`

English:
theorem unique_one
  given: {α : Type*} [Unique α] [One α]
  statement: default = (1 : α)
  proof: Unique.default_eq 1

中文:
定理 unique_one
  条件: {α : 类型} [唯一 α] [幺 α]
  结论: default = (1 : α)
  证明: Unique.default_eq 1

Depends on / 依赖: Unique, Unique.default_eq, default_eq
-/
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units
section Monoid
variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel_right` / 定理 `mul_inv_cancel_right`

English:
theorem mul_inv_cancel_right
  given: (a : α) (b : αˣ)
  statement: a * b * ↑b⁻¹ = a
  proof: by
  rw [mul_assoc]; rw [mul_inv]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_cancel_right
  条件: (a : α) (b : αˣ)
  结论: a * b * ↑b⁻¹ = a
  证明: by
  rw [mul_assoc]; rw [mul_inv]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_inv, mul_one
-/
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc]; rw [mul_inv]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel_right` / 定理 `inv_mul_cancel_right`

English:
theorem inv_mul_cancel_right
  given: (a : α) (b : αˣ)
  statement: a * ↑b⁻¹ * b = a
  proof: by
  rw [mul_assoc]; rw [inv_mul]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 inv_mul_cancel_right
  条件: (a : α) (b : αˣ)
  结论: a * ↑b⁻¹ * b = a
  证明: by
  rw [mul_assoc]; rw [inv_mul]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul, mul_assoc, mul_one
-/
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc]; rw [inv_mul]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `mul_right_inj` / 定理 `mul_right_inj`

English:
theorem mul_right_inj
  given: (a : αˣ) {b c : α}
  statement: (a : α) * b = a * c ↔ b = c
  proof: ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]

中文:
定理 mul_right_inj
  条件: (a : αˣ) {b c : α}
  结论: (a : α) * b = a * c ↔ b = c
  证明: ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]

Depends on / 依赖: congr_arg, inv_mul_cancel_left
-/
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]
/--
theorem `mul_left_inj` / 定理 `mul_left_inj`

English:
theorem mul_left_inj
  given: (a : αˣ) {b c : α}
  statement: b * a = c * a ↔ b = c
  proof: ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]

中文:
定理 mul_left_inj
  条件: (a : αˣ) {b c : α}
  结论: b * a = c * a ↔ b = c
  证明: ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]

Depends on / 依赖: a.val, congr_arg, mul_inv_cancel_right
-/
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]
/--
theorem `eq_mul_inv_iff_mul_eq` / 定理 `eq_mul_inv_iff_mul_eq`

English:
theorem eq_mul_inv_iff_mul_eq
  given: {a b : α}
  statement: a = b * ↑c⁻¹ ↔ a * c = b
  proof: ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]

中文:
定理 eq_mul_inv_iff_mul_eq
  条件: {a b : α}
  结论: a = b * ↑c⁻¹ ↔ a * c = b
  证明: ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_inv_cancel_right
-/
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
/--
theorem `eq_inv_mul_iff_mul_eq` / 定理 `eq_inv_mul_iff_mul_eq`

English:
theorem eq_inv_mul_iff_mul_eq
  given: {a c : α}
  statement: a = ↑b⁻¹ * c ↔ ↑b * a = c
  proof: ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]

中文:
定理 eq_inv_mul_iff_mul_eq
  条件: {a c : α}
  结论: a = ↑b⁻¹ * c ↔ ↑b * a = c
  证明: ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left, mul_inv_cancel_left
-/
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
/--
theorem `mul_inv_eq_iff_eq_mul` / 定理 `mul_inv_eq_iff_eq_mul`

English:
theorem mul_inv_eq_iff_eq_mul
  given: {a c : α}
  statement: a * ↑b⁻¹ = c ↔ a = c * b
  proof: ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]

中文:
定理 mul_inv_eq_iff_eq_mul
  条件: {a c : α}
  结论: a * ↑b⁻¹ = c ↔ a = c * b
  证明: ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]

Depends on / 依赖: MulZeroClass, MulZeroClass.toSMulWithZero, SMulWithZero, inv_mul_cancel_right, mul_inv_cancel_right, toSMulWithZero
-/
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
/--
theorem `inv_eq_of_mul_eq_one_left` / 定理 `inv_eq_of_mul_eq_one_left`

English:
theorem inv_eq_of_mul_eq_one_left
  given: {a : α} (h : a * u = 1)
  statement: ↑u⁻¹ = a
  proof: calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]

中文:
定理 inv_eq_of_mul_eq_one_left
  条件: {a : α} (h : a * u = 1)
  结论: ↑u⁻¹ = a
  证明: calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]
-/
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]
/--
theorem `inv_eq_of_mul_eq_one_right` / 定理 `inv_eq_of_mul_eq_one_right`

English:
theorem inv_eq_of_mul_eq_one_right
  given: {a : α} (h : ↑u * a = 1)
  statement: ↑u⁻¹ = a
  proof: calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]

中文:
定理 inv_eq_of_mul_eq_one_right
  条件: {a : α} (h : ↑u * a = 1)
  结论: ↑u⁻¹ = a
  证明: calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]
-/
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]
/--
theorem `eq_inv_of_mul_eq_one_left` / 定理 `eq_inv_of_mul_eq_one_left`

English:
theorem eq_inv_of_mul_eq_one_left
  given: {a : α} (h : ↑u * a = 1)
  statement: a = ↑u⁻¹
  proof: (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]

中文:
定理 eq_inv_of_mul_eq_one_left
  条件: {a : α} (h : ↑u * a = 1)
  结论: a = ↑u⁻¹
  证明: (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
-/
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
/--
theorem `eq_inv_of_mul_eq_one_right` / 定理 `eq_inv_of_mul_eq_one_right`

English:
theorem eq_inv_of_mul_eq_one_right
  given: {a : α} (h : a * u = 1)
  statement: a = ↑u⁻¹
  proof: (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]

中文:
定理 eq_inv_of_mul_eq_one_right
  条件: {a : α} (h : a * u = 1)
  结论: a = ↑u⁻¹
  证明: (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]
-/
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]
/--
theorem `mul_inv_eq_one` / 定理 `mul_inv_eq_one`

English:
theorem mul_inv_eq_one
  given: {a : α}
  statement: a * ↑u⁻¹ = 1 ↔ a = u
  proof: ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]

中文:
定理 mul_inv_eq_one
  条件: {a : α}
  结论: a * ↑u⁻¹ = 1 ↔ a = u
  证明: ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Units.eq_inv_of_mul_eq_one_right, eq_inv_of_mul_eq_one_right, h.symm, inv_inv, mul_inv_of_eq
-/
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]
/--
theorem `inv_mul_eq_one` / 定理 `inv_mul_eq_one`

English:
theorem inv_mul_eq_one
  given: {a : α}
  statement: ↑u⁻¹ * a = 1 ↔ ↑u = a
  proof: ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]

中文:
定理 inv_mul_eq_one
  条件: {a : α}
  结论: ↑u⁻¹ * a = 1 ↔ ↑u = a
  证明: ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]

Depends on / 依赖: Units.inv_eq_of_mul_eq_one_right, inv_eq_of_mul_eq_one_right, inv_inv, inv_mul_of_eq
-/
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
/--
theorem `mul_eq_one_iff_eq_inv` / 定理 `mul_eq_one_iff_eq_inv`

English:
theorem mul_eq_one_iff_eq_inv
  given: {a : α}
  statement: a * u = 1 ↔ a = ↑u⁻¹
  proof: by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]

中文:
定理 mul_eq_one_iff_eq_inv
  条件: {a : α}
  结论: a * u = 1 ↔ a = ↑u⁻¹
  证明: by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]

Depends on / 依赖: inv_inv, mul_inv_eq_one
-/
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
/--
theorem `mul_eq_one_iff_inv_eq` / 定理 `mul_eq_one_iff_inv_eq`

English:
theorem mul_eq_one_iff_inv_eq
  given: {a : α}
  statement: ↑u * a = 1 ↔ ↑u⁻¹ = a
  proof: by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]

中文:
定理 mul_eq_one_iff_inv_eq
  条件: {a : α}
  结论: ↑u * a = 1 ↔ ↑u⁻¹ = a
  证明: by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]

Depends on / 依赖: MonoidWithZero, MulActionWithZero, MulActionWithZero.toSMulWithZero, inv_inv, inv_mul_eq_one, toSMulWithZero
-/
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
/--
theorem `inv_unique` / 定理 `inv_unique`

English:
theorem inv_unique
  given: {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂)
  statement: (↑u₁⁻¹ : α) = ↑u₂⁻¹
  proof: Units.inv_eq_of_mul_eq_one_right by rw [h, u₂.mul_inv]

@[to_additive (attr := simp)]

中文:
定理 inv_unique
  条件: {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂)
  结论: (↑u₁⁻¹ : α) = ↑u₂⁻¹
  证明: Units.inv_eq_of_mul_eq_one_right by rw [h, u₂.mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidWithZero, MonoidWithZero.toMulActionWithZero, MulActionWithZero, Units.inv_eq_of_mul_eq_one_right, inv_eq_of_mul_eq_one_right, mul_inv, toMulActionWithZero
-/
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
Units.inv_eq_of_mul_eq_one_right by rw [h, u₂.mul_inv]

@[to_additive (attr := simp)]
/--
theorem `val_inv_inj` / 定理 `val_inv_inj`

English:
theorem val_inv_inj
  given: {u₁ u₂ : αˣ}
  statement: ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂
  proof: Units.ext_iff.symm.trans inv_inj.trans Units.ext_iff

中文:
定理 val_inv_inj
  条件: {u₁ u₂ : αˣ}
  结论: ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂
  证明: Units.ext_iff.symm.trans inv_inj.trans Units.ext_iff

Depends on / 依赖: Units.ext_iff, Units.ext_iff.symm.trans, ext_iff, inv_inj, inv_inj.trans
-/
theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ :=
Units.ext_iff.symm.trans inv_inj.trans Units.ext_iff

end Monoid

section CommMonoid

variable [CommMonoid α] (a c : α) (b d : αˣ)

@[to_additive]
/--
theorem `mul_inv_eq_mul_inv_iff` / 定理 `mul_inv_eq_mul_inv_iff`

English:
theorem mul_inv_eq_mul_inv_iff
  statement: a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
  proof: by
  rw [mul_comm c]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [mul_comm]

@[to_additive]

中文:
定理 mul_inv_eq_mul_inv_iff
  结论: a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
  证明: by
  rw [mul_comm c]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [mul_comm]

@[to_additive]

Depends on / 依赖: Units.eq_inv_mul_iff_mul_eq, Units.mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq, mul_assoc, mul_comm, mul_inv_eq_iff_eq_mul
-/
theorem mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [mul_comm c]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [mul_comm]

@[to_additive]
/--
theorem `inv_mul_eq_inv_mul_iff` / 定理 `inv_mul_eq_inv_mul_iff`

English:
theorem inv_mul_eq_inv_mul_iff
  statement: b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
  proof: by
  rw [mul_comm]; rw [mul_comm _ c]; rw [mul_inv_eq_mul_inv_iff]

中文:
定理 inv_mul_eq_inv_mul_iff
  结论: b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
  证明: by
  rw [mul_comm]; rw [mul_comm _ c]; rw [mul_inv_eq_mul_inv_iff]

Depends on / 依赖: mul_comm, mul_inv_eq_mul_inv_iff
-/
theorem inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [mul_comm]; rw [mul_comm _ c]; rw [mul_inv_eq_mul_inv_iff]

end CommMonoid

end Units

section Monoid

variable [Monoid α]

@[simp]
/--
theorem `divp_left_inj` / 定理 `divp_left_inj`

English:
theorem divp_left_inj
  given: (u : αˣ) {a b : α}
  statement: a /ₚ u = b /ₚ u ↔ a = b
  proof: Units.mul_left_inj _

中文:
定理 divp_left_inj
  条件: (u : αˣ) {a b : α}
  结论: a /ₚ u = b /ₚ u ↔ a = b
  证明: Units.mul_left_inj _

Depends on / 依赖: Units.mul_left_inj, mul_left_inj
-/
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _

/--
theorem `divp_eq_iff_mul_eq` / 定理 `divp_eq_iff_mul_eq`

English:
theorem divp_eq_iff_mul_eq
  given: {x : α} {u : αˣ} {y : α}
  statement: x /ₚ u = y ↔ y * u = x
  proof: u.mul_left_inj.symm.trans by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

中文:
定理 divp_eq_iff_mul_eq
  条件: {x : α} {u : αˣ} {y : α}
  结论: x /ₚ u = y ↔ y * u = x
  证明: u.mul_left_inj.symm.trans by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

Depends on / 依赖: Eq.symm, divp_mul_cancel, mul_left_inj, u.mul_left_inj.symm.trans
-/
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
u.mul_left_inj.symm.trans by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

/--
theorem `eq_divp_iff_mul_eq` / 定理 `eq_divp_iff_mul_eq`

English:
theorem eq_divp_iff_mul_eq
  given: {x : α} {u : αˣ} {y : α}
  statement: x = y /ₚ u ↔ x * u = y
  proof: by
  rw [eq_comm]; rw [divp_eq_iff_mul_eq]

中文:
定理 eq_divp_iff_mul_eq
  条件: {x : α} {u : αˣ} {y : α}
  结论: x = y /ₚ u ↔ x * u = y
  证明: by
  rw [eq_comm]; rw [divp_eq_iff_mul_eq]

Depends on / 依赖: divp_eq_iff_mul_eq, eq_comm
-/
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm]; rw [divp_eq_iff_mul_eq]

/--
theorem `divp_eq_one_iff_eq` / 定理 `divp_eq_one_iff_eq`

English:
theorem divp_eq_one_iff_eq
  given: {a : α} {u : αˣ}
  statement: a /ₚ u = 1 ↔ a = u
  proof: (Units.mul_left_inj u).symm.trans by rw [divp_mul_cancel, one_mul]

中文:
定理 divp_eq_one_iff_eq
  条件: {a : α} {u : αˣ}
  结论: a /ₚ u = 1 ↔ a = u
  证明: (Units.mul_left_inj u).symm.trans by rw [divp_mul_cancel, one_mul]

Depends on / 依赖: Units.mul_left_inj, divp_mul_cancel, mul_left_inj, one_mul, symm.trans
-/
theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
(Units.mul_left_inj u).symm.trans by rw [divp_mul_cancel, one_mul]

/--
theorem `inv_eq_one_divp'` / 定理 `inv_eq_one_divp'`

English:
theorem inv_eq_one_divp'
  given: (u : αˣ)
  statement: ((1 / u : αˣ) : α) = 1 /ₚ u
  proof: by
  rw [one_div]; rw [one_divp]

中文:
定理 inv_eq_one_divp'
  条件: (u : αˣ)
  结论: ((1 / u : αˣ) : α) = 1 /ₚ u
  证明: by
  rw [one_div]; rw [one_divp]

Depends on / 依赖: one_div, one_divp
-/
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div]; rw [one_divp]

end Monoid

namespace LeftCancelMonoid

variable [LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/--
theorem `eq_one_of_mul_right` / 定理 `eq_one_of_mul_right`

English:
theorem eq_one_of_mul_right
  given: (h : a * b = 1)
  statement: a = 1
  proof: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a)]; rw [← mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]

中文:
定理 eq_one_of_mul_right
  条件: (h : a * b = 1)
  结论: a = 1
  证明: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a)]; rw [← mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]
-/
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a)]; rw [← mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]
/--
theorem `eq_one_of_mul_left` / 定理 `eq_one_of_mul_left`

English:
theorem eq_one_of_mul_left
  given: (h : a * b = 1)
  statement: b = 1
  proof: by
  rwa [LeftCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]

中文:
定理 eq_one_of_mul_left
  条件: (h : a * b = 1)
  结论: b = 1
  证明: by
  rwa [LeftCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
-/
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [LeftCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
/--
theorem `mul_eq_one` / 定理 `mul_eq_one`

English:
theorem mul_eq_one
  statement: a * b = 1 ↔ a = 1 ∧ b = 1
  proof: ⟨fun h => ⟨LeftCancelMonoid.eq_one_of_mul_right h, LeftCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]

中文:
定理 mul_eq_one
  结论: a * b = 1 ↔ a = 1 ∧ b = 1
  证明: ⟨fun h => ⟨LeftCancelMonoid.eq_one_of_mul_right h, LeftCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
-/
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨LeftCancelMonoid.eq_one_of_mul_right h, LeftCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
/--
theorem `mul_ne_one` / 定理 `mul_ne_one`

English:
theorem mul_ne_one
  statement: a * b != 1 ↔ a != 1 ∨ b != 1
  proof: by rw [not_iff_comm]; simp

中文:
定理 mul_ne_one
  结论: a * b != 1 ↔ a != 1 ∨ b != 1
  证明: by rw [not_iff_comm]; simp
-/
protected theorem mul_ne_one : a * b != 1 ↔ a != 1 ∨ b != 1 := by rw [not_iff_comm]; simp

end LeftCancelMonoid

namespace RightCancelMonoid

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/--
theorem `eq_one_of_mul_right` / 定理 `eq_one_of_mul_right`

English:
theorem eq_one_of_mul_right
  given: (h : a * b = 1)
  statement: a = 1
  proof: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_right_cancel_iff (a := b)]; rw [mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]

中文:
定理 eq_one_of_mul_right
  条件: (h : a * b = 1)
  结论: a = 1
  证明: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_right_cancel_iff (a := b)]; rw [mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]

Depends on / 依赖: DistribMulAction, DistribMulAction.toDistribSMul, DistribSMul, toDistribSMul
-/
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_right_cancel_iff (a := b)]; rw [mul_assoc]; rw [h]; rw [one_mul]; rw [mul_one]) h) 1

@[to_additive]
/--
theorem `eq_one_of_mul_left` / 定理 `eq_one_of_mul_left`

English:
theorem eq_one_of_mul_left
  given: (h : a * b = 1)
  statement: b = 1
  proof: by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]

中文:
定理 eq_one_of_mul_left
  条件: (h : a * b = 1)
  结论: b = 1
  证明: by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
-/
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
/--
theorem `mul_eq_one` / 定理 `mul_eq_one`

English:
theorem mul_eq_one
  statement: a * b = 1 ↔ a = 1 ∧ b = 1
  proof: ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]

中文:
定理 mul_eq_one
  结论: a * b = 1 ↔ a = 1 ∧ b = 1
  证明: ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
-/
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
/--
theorem `mul_ne_one` / 定理 `mul_ne_one`

English:
theorem mul_ne_one
  statement: a * b != 1 ↔ a != 1 ∨ b != 1
  proof: by rw [not_iff_comm]; simp

中文:
定理 mul_ne_one
  结论: a * b != 1 ↔ a != 1 ∨ b != 1
  证明: by rw [not_iff_comm]; simp
-/
protected theorem mul_ne_one : a * b != 1 ↔ a != 1 ∨ b != 1 := by rw [not_iff_comm]; simp

end RightCancelMonoid

section CancelMonoid

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/--
theorem `eq_one_of_mul_right'` / 定理 `eq_one_of_mul_right'`

English:
theorem eq_one_of_mul_right'
  given: (h : a * b = 1)
  statement: a = 1
  proof: LeftCancelMonoid.eq_one_of_mul_right h

@[to_additive]

中文:
定理 eq_one_of_mul_right'
  条件: (h : a * b = 1)
  结论: a = 1
  证明: LeftCancelMonoid.eq_one_of_mul_right h

@[to_additive]

Depends on / 依赖: LeftCancelMonoid, LeftCancelMonoid.eq_one_of_mul_right, eq_one_of_mul_right
-/
theorem eq_one_of_mul_right' (h : a * b = 1) : a = 1 := LeftCancelMonoid.eq_one_of_mul_right h

@[to_additive]
/--
theorem `eq_one_of_mul_left'` / 定理 `eq_one_of_mul_left'`

English:
theorem eq_one_of_mul_left'
  given: (h : a * b = 1)
  statement: b = 1
  proof: LeftCancelMonoid.eq_one_of_mul_left h

@[to_additive]

中文:
定理 eq_one_of_mul_left'
  条件: (h : a * b = 1)
  结论: b = 1
  证明: LeftCancelMonoid.eq_one_of_mul_left h

@[to_additive]

Depends on / 依赖: LeftCancelMonoid, LeftCancelMonoid.eq_one_of_mul_left, eq_one_of_mul_left
-/
theorem eq_one_of_mul_left' (h : a * b = 1) : b = 1 := LeftCancelMonoid.eq_one_of_mul_left h

@[to_additive]
/--
theorem `mul_eq_one'` / 定理 `mul_eq_one'`

English:
theorem mul_eq_one'
  statement: a * b = 1 ↔ a = 1 ∧ b = 1
  proof: LeftCancelMonoid.mul_eq_one

@[to_additive]

中文:
定理 mul_eq_one'
  结论: a * b = 1 ↔ a = 1 ∧ b = 1
  证明: LeftCancelMonoid.mul_eq_one

@[to_additive]

Depends on / 依赖: LeftCancelMonoid, LeftCancelMonoid.mul_eq_one, mul_eq_one
-/
theorem mul_eq_one' : a * b = 1 ↔ a = 1 ∧ b = 1 := LeftCancelMonoid.mul_eq_one

@[to_additive]
/--
theorem `mul_ne_one'` / 定理 `mul_ne_one'`

English:
theorem mul_ne_one'
  statement: a * b != 1 ↔ a != 1 ∨ b != 1
  proof: LeftCancelMonoid.mul_ne_one

中文:
定理 mul_ne_one'
  结论: a * b != 1 ↔ a != 1 ∨ b != 1
  证明: LeftCancelMonoid.mul_ne_one

Depends on / 依赖: LeftCancelMonoid, LeftCancelMonoid.mul_ne_one, mul_ne_one
-/
theorem mul_ne_one' : a * b != 1 ↔ a != 1 ∨ b != 1 := LeftCancelMonoid.mul_ne_one

end CancelMonoid

section CommMonoid

variable [CommMonoid α]

/--
theorem `divp_mul_eq_mul_divp` / 定理 `divp_mul_eq_mul_divp`

English:
theorem divp_mul_eq_mul_divp
  given: (x y : α) (u : αˣ)
  statement: x /ₚ u * y = x * y /ₚ u
  proof: by
  rw [divp]; rw [divp]; rw [mul_right_comm]

中文:
定理 divp_mul_eq_mul_divp
  条件: (x y : α) (u : αˣ)
  结论: x /ₚ u * y = x * y /ₚ u
  证明: by
  rw [divp]; rw [divp]; rw [mul_right_comm]

Depends on / 依赖: mul_right_comm
-/
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp]; rw [divp]; rw [mul_right_comm]

/--
theorem `divp_eq_divp_iff` / 定理 `divp_eq_divp_iff`

English:
theorem divp_eq_divp_iff
  given: {x y : α} {ux uy : αˣ}
  statement: x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux
  proof: by
  rw [divp_eq_iff_mul_eq]; rw [divp_mul_eq_mul_divp]; rw [divp_eq_iff_mul_eq]

中文:
定理 divp_eq_divp_iff
  条件: {x y : α} {ux uy : αˣ}
  结论: x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux
  证明: by
  rw [divp_eq_iff_mul_eq]; rw [divp_mul_eq_mul_divp]; rw [divp_eq_iff_mul_eq]

Depends on / 依赖: divp_eq_iff_mul_eq, divp_mul_eq_mul_divp
-/
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq]; rw [divp_mul_eq_mul_divp]; rw [divp_eq_iff_mul_eq]

/--
theorem `divp_mul_divp` / 定理 `divp_mul_divp`

English:
theorem divp_mul_divp
  given: (x y : α) (ux uy : αˣ)
  statement: x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy)
  proof: by
  rw [divp_mul_eq_mul_divp]; rw [← divp_assoc]; rw [divp_divp_eq_divp_mul]

中文:
定理 divp_mul_divp
  条件: (x y : α) (ux uy : αˣ)
  结论: x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy)
  证明: by
  rw [divp_mul_eq_mul_divp]; rw [← divp_assoc]; rw [divp_divp_eq_divp_mul]

Depends on / 依赖: divp_assoc, divp_divp_eq_divp_mul, divp_mul_eq_mul_divp
-/
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp]; rw [← divp_assoc]; rw [divp_divp_eq_divp_mul]

variable [Subsingleton αˣ] {a b : α}

@[to_additive]
/--
theorem `eq_one_of_mul_right` / 定理 `eq_one_of_mul_right`

English:
theorem eq_one_of_mul_right
  given: (h : a * b = 1)
  statement: a = 1
  proof: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]

中文:
定理 eq_one_of_mul_right
  条件: (h : a * b = 1)
  结论: a = 1
  证明: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]

Depends on / 依赖: Subsingleton, Subsingleton.elim, Units.inv, Units.mk, congr_arg, mul_comm
-/
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
congr_arg Units.inv Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]
/--
theorem `eq_one_of_mul_left` / 定理 `eq_one_of_mul_left`

English:
theorem eq_one_of_mul_left
  given: (h : a * b = 1)
  statement: b = 1
  proof: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]

中文:
定理 eq_one_of_mul_left
  条件: (h : a * b = 1)
  结论: b = 1
  证明: congr_arg Units.inv Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]

Depends on / 依赖: Subsingleton, Subsingleton.elim, Units.inv, Units.mk, congr_arg, mul_comm
-/
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
congr_arg Units.inv Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]
/--
theorem `mul_eq_one` / 定理 `mul_eq_one`

English:
theorem mul_eq_one
  statement: a * b = 1 ↔ a = 1 ∧ b = 1
  proof: ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

中文:
定理 mul_eq_one
  结论: a * b = 1 ↔ a = 1 ∧ b = 1
  证明: ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

Depends on / 依赖: eq_one_of_mul_left, eq_one_of_mul_right, mul_one
-/
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

/--
theorem `mul_ne_one` / 定理 `mul_ne_one`

English:
theorem mul_ne_one
  statement: a * b != 1 ↔ a != 1 ∨ b != 1
  proof: by rw [not_iff_comm]; simp

中文:
定理 mul_ne_one
  结论: a * b != 1 ↔ a != 1 ∨ b != 1
  证明: by rw [not_iff_comm]; simp
-/
@[to_additive] theorem mul_ne_one : a * b != 1 ↔ a != 1 ∨ b != 1 := by rw [not_iff_comm]; simp

end CommMonoid

/-!
### `IsUnit` predicate
-/


section IsUnit

variable {M : Type*}

@[to_additive (attr := nontriviality)]
/--
theorem `isUnit_of_subsingleton` / 定理 `isUnit_of_subsingleton`

English:
theorem isUnit_of_subsingleton
  given: [Monoid M] [Subsingleton M] (a : M)
  statement: IsUnit a
  proof: ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]

中文:
定理 isUnit_of_subsingleton
  条件: [幺半群 M] [子单例 M] (a : M)
  结论: 是单位 a
  证明: ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]

Depends on / 依赖: subsingleton
-/
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] : CanLift M Mˣ Units.val IsUnit
  body: { prf := fun _ => id }

中文:
实例 [幺半群
  签名: M] : CanLift M Mˣ 单位群.val 是单位
  定义体: { prf := fun _ => id }
-/
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ => id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive /-- A subsingleton `AddMonoid` has a unique additive unit. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [Subsingleton M] : Unique Mˣ where
  body: Units.val_eq_one.mp (by subsingleton)

中文:
实例 [幺半群
  签名: M] [子单例 M] : 唯一 Mˣ where
  定义体: Units.val_eq_one.mp (by subsingleton)

Depends on / 依赖: Units.val_eq_one.mp, subsingleton, val_eq_one
-/
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  uniq _ := Units.val_eq_one.mp (by subsingleton)

namespace IsUnit

section Monoid

variable [Monoid M] {a b c : M}

@[to_additive]
/--
theorem `mul_left_inj` / 定理 `mul_left_inj`

English:
theorem mul_left_inj
  given: (h : IsUnit a)
  statement: b * a = c * a ↔ b = c
  proof: let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]

中文:
定理 mul_left_inj
  条件: (h : 是单位 a)
  结论: b * a = c * a ↔ b = c
  证明: let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]

Depends on / 依赖: mul_left_inj, u.mul_left_inj
-/
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]
/--
theorem `mul_right_inj` / 定理 `mul_right_inj`

English:
theorem mul_right_inj
  given: (h : IsUnit a)
  statement: a * b = a * c ↔ b = c
  proof: let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]

中文:
定理 mul_right_inj
  条件: (h : 是单位 a)
  结论: a * b = a * c ↔ b = c
  证明: let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]

Depends on / 依赖: mul_right_inj, u.mul_right_inj
-/
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]
/--
theorem `mul_left_cancel` / 定理 `mul_left_cancel`

English:
theorem mul_left_cancel
  given: (h : IsUnit a)
  statement: a * b = a * c -> b = c
  proof: h.mul_right_inj.1

@[to_additive]

中文:
定理 mul_left_cancel
  条件: (h : 是单位 a)
  结论: a * b = a * c -> b = c
  证明: h.mul_right_inj.1

@[to_additive]
-/
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c -> b = c :=
  h.mul_right_inj.1

@[to_additive]
/--
theorem `mul_right_cancel` / 定理 `mul_right_cancel`

English:
theorem mul_right_cancel
  given: (h : IsUnit b)
  statement: a * b = c * b -> a = c
  proof: h.mul_left_inj.1

@[to_additive]

中文:
定理 mul_right_cancel
  条件: (h : 是单位 b)
  结论: a * b = c * b -> a = c
  证明: h.mul_left_inj.1

@[to_additive]
-/
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b -> a = c :=
  h.mul_left_inj.1

@[to_additive]
/--
theorem `mul_eq_right` / 定理 `mul_eq_right`

English:
theorem mul_eq_right
  given: (h : IsUnit b)
  statement: a * b = b ↔ a = 1
  proof: calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]

中文:
定理 mul_eq_right
  条件: (h : 是单位 b)
  结论: a * b = b ↔ a = 1
  证明: calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]
-/
theorem mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]
/--
theorem `mul_eq_left` / 定理 `mul_eq_left`

English:
theorem mul_eq_left
  given: (h : IsUnit a)
  statement: a * b = a ↔ b = 1
  proof: calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]

中文:
定理 mul_eq_left
  条件: (h : 是单位 a)
  结论: a * b = a ↔ b = 1
  证明: calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]
-/
theorem mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]
/--
theorem `mul_right_injective` / 定理 `mul_right_injective`

English:
theorem mul_right_injective
  given: (h : IsUnit a)
  statement: Injective (a * ·)
  proof: fun _ _ => h.mul_left_cancel

@[to_additive]

中文:
定理 mul_right_injective
  条件: (h : 是单位 a)
  结论: 单射 (a * ·)
  证明: fun _ _ => h.mul_left_cancel

@[to_additive]
-/
protected theorem mul_right_injective (h : IsUnit a) : Injective (a * ·) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
/--
theorem `mul_left_injective` / 定理 `mul_left_injective`

English:
theorem mul_left_injective
  given: (h : IsUnit b)
  statement: Injective (· * b)
  proof: fun _ _ => h.mul_right_cancel

@[to_additive]

中文:
定理 mul_left_injective
  条件: (h : 是单位 b)
  结论: 单射 (· * b)
  证明: fun _ _ => h.mul_right_cancel

@[to_additive]
-/
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

@[to_additive]
/--
theorem `isUnit_iff_mulLeft_bijective` / 定理 `isUnit_iff_mulLeft_bijective`

English:
theorem isUnit_iff_mulLeft_bijective
  given: {a : M}
  proof: ⟨fun h => ⟨h.mul_right_injective, fun y => ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h =>
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]

中文:
定理 isUnit_iff_mulLeft_bijective
  条件: {a : M}
  证明: ⟨fun h => ⟨h.mul_right_injective, fun y => ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h =>
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]

Depends on / 依赖: choose_spec, congr_arg, h.mul_right_injective, h.unit, mul_assoc, mul_right_injective
-/
theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) :=
  ⟨fun h => ⟨h.mul_right_injective, fun y => ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h =>
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]
/--
theorem `isUnit_iff_mulRight_bijective` / 定理 `isUnit_iff_mulRight_bijective`

English:
theorem isUnit_iff_mulRight_bijective
  given: {a : M}
  proof: ⟨fun h => ⟨h.mul_left_injective, fun y => ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h => ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

中文:
定理 isUnit_iff_mulRight_bijective
  条件: {a : M}
  证明: ⟨fun h => ⟨h.mul_left_injective, fun y => ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h => ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

Depends on / 依赖: choose_spec, congr_arg, h.mul_left_injective, h.unit, mul_assoc, mul_left_injective
-/
theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) :=
  ⟨fun h => ⟨h.mul_left_injective, fun y => ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h => ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
/--
lemma `mul_inv_cancel_right` / 引理 `mul_inv_cancel_right`

English:
lemma mul_inv_cancel_right
  given: (h : IsUnit b) (a : α)
  statement: a * b * b⁻¹ = a
  proof: h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]

中文:
引理 mul_inv_cancel_right
  条件: (h : 是单位 b) (a : α)
  结论: a * b * b⁻¹ = a
  证明: h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
-/
protected lemma mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
/--
lemma `inv_mul_cancel_right` / 引理 `inv_mul_cancel_right`

English:
lemma inv_mul_cancel_right
  given: (h : IsUnit b) (a : α)
  statement: a * b⁻¹ * b = a
  proof: h.unit'.inv_mul_cancel_right _

@[to_additive]

中文:
引理 inv_mul_cancel_right
  条件: (h : 是单位 b) (a : α)
  结论: a * b⁻¹ * b = a
  证明: h.unit'.inv_mul_cancel_right _

@[to_additive]
-/
protected lemma inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
/--
lemma `eq_mul_inv_iff_mul_eq` / 引理 `eq_mul_inv_iff_mul_eq`

English:
lemma eq_mul_inv_iff_mul_eq
  given: (h : IsUnit c)
  statement: a = b * c⁻¹ ↔ a * c = b
  proof: h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]

中文:
引理 eq_mul_inv_iff_mul_eq
  条件: (h : 是单位 c)
  结论: a = b * c⁻¹ ↔ a * c = b
  证明: h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
-/
protected lemma eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
/--
lemma `eq_inv_mul_iff_mul_eq` / 引理 `eq_inv_mul_iff_mul_eq`

English:
lemma eq_inv_mul_iff_mul_eq
  given: (h : IsUnit b)
  statement: a = b⁻¹ * c ↔ b * a = c
  proof: h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]

中文:
引理 eq_inv_mul_iff_mul_eq
  条件: (h : 是单位 b)
  结论: a = b⁻¹ * c ↔ b * a = c
  证明: h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
-/
protected lemma eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
/--
lemma `inv_mul_eq_iff_eq_mul` / 引理 `inv_mul_eq_iff_eq_mul`

English:
lemma inv_mul_eq_iff_eq_mul
  given: (h : IsUnit a)
  statement: a⁻¹ * b = c ↔ b = a * c
  proof: h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]

中文:
引理 inv_mul_eq_iff_eq_mul
  条件: (h : 是单位 a)
  结论: a⁻¹ * b = c ↔ b = a * c
  证明: h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
-/
protected lemma inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
/--
lemma `mul_inv_eq_iff_eq_mul` / 引理 `mul_inv_eq_iff_eq_mul`

English:
lemma mul_inv_eq_iff_eq_mul
  given: (h : IsUnit b)
  statement: a * b⁻¹ = c ↔ a = c * b
  proof: h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]

中文:
引理 mul_inv_eq_iff_eq_mul
  条件: (h : 是单位 b)
  结论: a * b⁻¹ = c ↔ a = c * b
  证明: h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
-/
protected lemma mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
/--
lemma `mul_inv_eq_one` / 引理 `mul_inv_eq_one`

English:
lemma mul_inv_eq_one
  given: (h : IsUnit b)
  statement: a * b⁻¹ = 1 ↔ a = b
  proof: @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]

中文:
引理 mul_inv_eq_one
  条件: (h : 是单位 b)
  结论: a * b⁻¹ = 1 ↔ a = b
  证明: @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
-/
protected lemma mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
/--
lemma `inv_mul_eq_one` / 引理 `inv_mul_eq_one`

English:
lemma inv_mul_eq_one
  given: (h : IsUnit a)
  statement: a⁻¹ * b = 1 ↔ a = b
  proof: @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]

中文:
引理 inv_mul_eq_one
  条件: (h : 是单位 a)
  结论: a⁻¹ * b = 1 ↔ a = b
  证明: @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
-/
protected lemma inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
/--
lemma `mul_eq_one_iff_eq_inv` / 引理 `mul_eq_one_iff_eq_inv`

English:
lemma mul_eq_one_iff_eq_inv
  given: (h : IsUnit b)
  statement: a * b = 1 ↔ a = b⁻¹
  proof: @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]

中文:
引理 mul_eq_one_iff_eq_inv
  条件: (h : 是单位 b)
  结论: a * b = 1 ↔ a = b⁻¹
  证明: @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
-/
protected lemma mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
/--
lemma `mul_eq_one_iff_inv_eq` / 引理 `mul_eq_one_iff_inv_eq`

English:
lemma mul_eq_one_iff_inv_eq
  given: (h : IsUnit a)
  statement: a * b = 1 ↔ a⁻¹ = b
  proof: @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]

中文:
引理 mul_eq_one_iff_inv_eq
  条件: (h : 是单位 a)
  结论: a * b = 1 ↔ a⁻¹ = b
  证明: @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
-/
protected lemma mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
/--
lemma `div_mul_cancel` / 引理 `div_mul_cancel`

English:
lemma div_mul_cancel
  given: (h : IsUnit b) (a : α)
  statement: a / b * b = a
  proof: by
  rw [div_eq_mul_inv]; rw [h.inv_mul_cancel_right]

@[to_additive (attr := simp)]

中文:
引理 div_mul_cancel
  条件: (h : 是单位 b) (a : α)
  结论: a / b * b = a
  证明: by
  rw [div_eq_mul_inv]; rw [h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
-/
protected lemma div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv]; rw [h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
/--
lemma `mul_div_cancel_right` / 引理 `mul_div_cancel_right`

English:
lemma mul_div_cancel_right
  given: (h : IsUnit b) (a : α)
  statement: a * b / b = a
  proof: by
  rw [div_eq_mul_inv]; rw [h.mul_inv_cancel_right]

@[to_additive]

中文:
引理 mul_div_cancel_right
  条件: (h : 是单位 b) (a : α)
  结论: a * b / b = a
  证明: by
  rw [div_eq_mul_inv]; rw [h.mul_inv_cancel_right]

@[to_additive]
-/
protected lemma mul_div_cancel_right (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv]; rw [h.mul_inv_cancel_right]

@[to_additive]
/--
lemma `mul_one_div_cancel` / 引理 `mul_one_div_cancel`

English:
lemma mul_one_div_cancel
  given: (h : IsUnit a)
  statement: a * (1 / a) = 1
  proof: by simp [h]

@[to_additive]

中文:
引理 mul_one_div_cancel
  条件: (h : 是单位 a)
  结论: a * (1 / a) = 1
  证明: by simp [h]

@[to_additive]
-/
protected lemma mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]

@[to_additive]
/--
lemma `one_div_mul_cancel` / 引理 `one_div_mul_cancel`

English:
lemma one_div_mul_cancel
  given: (h : IsUnit a)
  statement: 1 / a * a = 1
  proof: by simp [h]

@[to_additive]

中文:
引理 one_div_mul_cancel
  条件: (h : 是单位 a)
  结论: 1 / a * a = 1
  证明: by simp [h]

@[to_additive]
-/
protected lemma one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]

@[to_additive]
/--
lemma `div_left_inj` / 引理 `div_left_inj`

English:
lemma div_left_inj
  given: (h : IsUnit c)
  statement: a / c = b / c ↔ a = b
  proof: by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]

中文:
引理 div_left_inj
  条件: (h : 是单位 c)
  结论: a / c = b / c ↔ a = b
  证明: by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
-/
protected lemma div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
/--
lemma `div_eq_iff` / 引理 `div_eq_iff`

English:
lemma div_eq_iff
  given: (h : IsUnit b)
  statement: a / b = c ↔ a = c * b
  proof: by
  rw [div_eq_mul_inv]; rw [h.mul_inv_eq_iff_eq_mul]

@[to_additive]

中文:
引理 div_eq_iff
  条件: (h : 是单位 b)
  结论: a / b = c ↔ a = c * b
  证明: by
  rw [div_eq_mul_inv]; rw [h.mul_inv_eq_iff_eq_mul]

@[to_additive]
-/
protected lemma div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv]; rw [h.mul_inv_eq_iff_eq_mul]

@[to_additive]
/--
lemma `eq_div_iff` / 引理 `eq_div_iff`

English:
lemma eq_div_iff
  given: (h : IsUnit c)
  statement: a = b / c ↔ a * c = b
  proof: by
  rw [div_eq_mul_inv]; rw [h.eq_mul_inv_iff_mul_eq]

@[to_additive]

中文:
引理 eq_div_iff
  条件: (h : 是单位 c)
  结论: a = b / c ↔ a * c = b
  证明: by
  rw [div_eq_mul_inv]; rw [h.eq_mul_inv_iff_mul_eq]

@[to_additive]
-/
protected lemma eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv]; rw [h.eq_mul_inv_iff_mul_eq]

@[to_additive]
/--
lemma `div_eq_of_eq_mul` / 引理 `div_eq_of_eq_mul`

English:
lemma div_eq_of_eq_mul
  given: (h : IsUnit b)
  statement: a = c * b -> a / b = c
  proof: h.div_eq_iff.2

@[to_additive]

中文:
引理 div_eq_of_eq_mul
  条件: (h : 是单位 b)
  结论: a = c * b -> a / b = c
  证明: h.div_eq_iff.2

@[to_additive]
-/
protected lemma div_eq_of_eq_mul (h : IsUnit b) : a = c * b -> a / b = c :=
  h.div_eq_iff.2

@[to_additive]
/--
lemma `eq_div_of_mul_eq` / 引理 `eq_div_of_mul_eq`

English:
lemma eq_div_of_mul_eq
  given: (h : IsUnit c)
  statement: a * c = b -> a = b / c
  proof: h.eq_div_iff.2

@[to_additive]

中文:
引理 eq_div_of_mul_eq
  条件: (h : 是单位 c)
  结论: a * c = b -> a = b / c
  证明: h.eq_div_iff.2

@[to_additive]
-/
protected lemma eq_div_of_mul_eq (h : IsUnit c) : a * c = b -> a = b / c :=
  h.eq_div_iff.2

@[to_additive]
/--
lemma `div_eq_one_iff_eq` / 引理 `div_eq_one_iff_eq`

English:
lemma div_eq_one_iff_eq
  given: (h : IsUnit b)
  statement: a / b = 1 ↔ a = b
  proof: ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]

中文:
引理 div_eq_one_iff_eq
  条件: (h : 是单位 b)
  结论: a / b = 1 ↔ a = b
  证明: ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
-/
protected lemma div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
/--
lemma `div_mul_left` / 引理 `div_mul_left`

English:
lemma div_mul_left
  given: (h : IsUnit b)
  statement: b / (a * b) = 1 / a
  proof: by
  rw [h.div_mul_cancel_right]; rw [one_div]

@[to_additive]

中文:
引理 div_mul_left
  条件: (h : 是单位 b)
  结论: b / (a * b) = 1 / a
  证明: by
  rw [h.div_mul_cancel_right]; rw [one_div]

@[to_additive]
-/
protected lemma div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [h.div_mul_cancel_right]; rw [one_div]

@[to_additive]
/--
lemma `mul_mul_div` / 引理 `mul_mul_div`

English:
lemma mul_mul_div
  given: (a : α) (h : IsUnit b)
  statement: a * b * (1 / b) = a
  proof: by simp [h]

中文:
引理 mul_mul_div
  条件: (a : α) (h : 是单位 b)
  结论: a * b * (1 / b) = a
  证明: by simp [h]
-/
protected lemma mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
/--
lemma `div_mul_right` / 引理 `div_mul_right`

English:
lemma div_mul_right
  given: (h : IsUnit a) (b : α)
  statement: a / (a * b) = 1 / b
  proof: by
  rw [mul_comm]; rw [h.div_mul_left]

@[to_additive]

中文:
引理 div_mul_right
  条件: (h : 是单位 a) (b : α)
  结论: a / (a * b) = 1 / b
  证明: by
  rw [mul_comm]; rw [h.div_mul_left]

@[to_additive]
-/
protected lemma div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm]; rw [h.div_mul_left]

@[to_additive]
/--
lemma `mul_div_cancel_left` / 引理 `mul_div_cancel_left`

English:
lemma mul_div_cancel_left
  given: (h : IsUnit a) (b : α)
  statement: a * b / a = b
  proof: by
  rw [mul_comm]; rw [h.mul_div_cancel_right]

@[to_additive]

中文:
引理 mul_div_cancel_left
  条件: (h : 是单位 a) (b : α)
  结论: a * b / a = b
  证明: by
  rw [mul_comm]; rw [h.mul_div_cancel_right]

@[to_additive]
-/
protected lemma mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm]; rw [h.mul_div_cancel_right]

@[to_additive]
/--
lemma `mul_div_cancel` / 引理 `mul_div_cancel`

English:
lemma mul_div_cancel
  given: (h : IsUnit a) (b : α)
  statement: a * (b / a) = b
  proof: by
  rw [mul_comm]; rw [h.div_mul_cancel]

@[to_additive]

中文:
引理 mul_div_cancel
  条件: (h : 是单位 a) (b : α)
  结论: a * (b / a) = b
  证明: by
  rw [mul_comm]; rw [h.div_mul_cancel]

@[to_additive]
-/
protected lemma mul_div_cancel (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm]; rw [h.div_mul_cancel]

@[to_additive]
/--
lemma `mul_eq_mul_of_div_eq_div` / 引理 `mul_eq_mul_of_div_eq_div`

English:
lemma mul_eq_mul_of_div_eq_div
  statement: (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← mul_one a]; rw [← hb.div_self]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [hd.div_mul_cancel]

@[to_additive]

中文:
引理 mul_eq_mul_of_div_eq_div
  结论: (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← mul_one a]; rw [← hb.div_self]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [hd.div_mul_cancel]

@[to_additive]
-/
protected lemma mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : α) (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a]; rw [← hb.div_self]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [hd.div_mul_cancel]

@[to_additive]
/--
lemma `div_eq_div_iff` / 引理 `div_eq_div_iff`

English:
lemma div_eq_div_iff
  given: (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [mul_right_comm]; rw [hd.div_mul_cancel]

@[to_additive]

中文:
引理 div_eq_div_iff
  条件: (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [mul_right_comm]; rw [hd.div_mul_cancel]

@[to_additive]
-/
protected lemma div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [mul_right_comm]; rw [hd.div_mul_cancel]

@[to_additive]
/--
lemma `mul_inv_eq_mul_inv_iff` / 引理 `mul_inv_eq_mul_inv_iff`

English:
lemma mul_inv_eq_mul_inv_iff
  given: (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hb.div_eq_div_iff hd]

@[to_additive]

中文:
引理 mul_inv_eq_mul_inv_iff
  条件: (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hb.div_eq_div_iff hd]

@[to_additive]
-/
protected lemma mul_inv_eq_mul_inv_iff (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hb.div_eq_div_iff hd]

@[to_additive]
/--
lemma `inv_mul_eq_inv_mul_iff` / 引理 `inv_mul_eq_inv_mul_iff`

English:
lemma inv_mul_eq_inv_mul_iff
  given: (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [hb.div_eq_div_iff hd]

@[to_additive]

中文:
引理 inv_mul_eq_inv_mul_iff
  条件: (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [hb.div_eq_div_iff hd]

@[to_additive]
-/
protected lemma inv_mul_eq_inv_mul_iff (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [hb.div_eq_div_iff hd]

@[to_additive]
/--
lemma `div_div_cancel` / 引理 `div_div_cancel`

English:
lemma div_div_cancel
  given: (h : IsUnit a)
  statement: a / (a / b) = b
  proof: by
  rw [div_div_eq_mul_div]; rw [h.mul_div_cancel_left]

@[to_additive]

中文:
引理 div_div_cancel
  条件: (h : 是单位 a)
  结论: a / (a / b) = b
  证明: by
  rw [div_div_eq_mul_div]; rw [h.mul_div_cancel_left]

@[to_additive]
-/
protected lemma div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div]; rw [h.mul_div_cancel_left]

@[to_additive]
/--
lemma `div_div_cancel_left` / 引理 `div_div_cancel_left`

English:
lemma div_div_cancel_left
  given: (h : IsUnit a)
  statement: a / b / a = b⁻¹
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_right_comm]; rw [h.mul_inv_cancel]; rw [one_mul]

中文:
引理 div_div_cancel_left
  条件: (h : 是单位 a)
  结论: a / b / a = b⁻¹
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_right_comm]; rw [h.mul_inv_cancel]; rw [one_mul]
-/
protected lemma div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_right_comm]; rw [h.mul_inv_cancel]; rw [one_mul]

end DivisionCommMonoid
end IsUnit

-- namespace
end IsUnit
