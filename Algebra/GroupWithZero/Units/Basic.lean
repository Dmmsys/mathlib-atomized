/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Nat.Basic -- shake: keep (non-recorded `nontrivial` dependency?)
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

We also define `Ring.inverse`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which inverts units and sends non-units to zero.
-/

@[expose] public section

assert_not_exists DenselyOrdered Equiv Subtype.restrict Multiplicative Ring

variable {α M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
of the monoid is nonzero. -/
@[simp]
/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial M₀] (u : M₀ˣ)
  statement: (u : M₀) != 0
  proof: left_ne_zero_of_mul_eq_one u.mul_inv

中文:
定理 ne_zero
  条件: [Nontrivial M₀] (u : M₀ˣ)
  结论: (u : M₀) != 0
  证明: left_ne_zero_of_mul_eq_one u.mul_inv

Depends on / 依赖: left_ne_zero_of_mul_eq_one, mul_inv, u.mul_inv
-/
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nontrivial M₀`.
@[simp]
/--
theorem `mul_left_eq_zero` / 定理 `mul_left_eq_zero`

English:
theorem mul_left_eq_zero
  given: (u : M₀ˣ) {a : M₀}
  statement: a * u = 0 ↔ a = 0
  proof: ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]

中文:
定理 mul_left_eq_zero
  条件: (u : M₀ˣ) {a : M₀}
  结论: a * u = 0 ↔ a = 0
  证明: ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]

Depends on / 依赖: mul_eq_zero_of_left
-/
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
/--
theorem `mul_right_eq_zero` / 定理 `mul_right_eq_zero`

English:
theorem mul_right_eq_zero
  given: (u : M₀ˣ) {a : M₀}
  statement: ↑u * a = 0 ↔ a = 0
  proof: ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

中文:
定理 mul_right_eq_zero
  条件: (u : M₀ˣ) {a : M₀}
  结论: ↑u * a = 0 ↔ a = 0
  证明: ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

Depends on / 依赖: mul_eq_zero_of_right
-/
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

end Units

namespace IsUnit

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial M₀] {a : M₀} (ha : IsUnit a)
  statement: a != 0
  proof: let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

中文:
定理 ne_zero
  条件: [Nontrivial M₀] {a : M₀} (ha : IsUnit a)
  结论: a != 0
  证明: let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

Depends on / 依赖: ne_zero, u.ne_zero
-/
theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

/--
theorem `mul_right_eq_zero` / 定理 `mul_right_eq_zero`

English:
theorem mul_right_eq_zero
  given: {a b : M₀} (ha : IsUnit a)
  statement: a * b = 0 ↔ b = 0
  proof: let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

中文:
定理 mul_right_eq_zero
  条件: {a b : M₀} (ha : IsUnit a)
  结论: a * b = 0 ↔ b = 0
  证明: let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

Depends on / 依赖: mul_right_eq_zero, u.mul_right_eq_zero
-/
theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

/--
theorem `mul_left_eq_zero` / 定理 `mul_left_eq_zero`

English:
theorem mul_left_eq_zero
  given: {a b : M₀} (hb : IsUnit b)
  statement: a * b = 0 ↔ a = 0
  proof: let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

中文:
定理 mul_left_eq_zero
  条件: {a b : M₀} (hb : IsUnit b)
  结论: a * b = 0 ↔ a = 0
  证明: let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

Depends on / 依赖: mul_left_eq_zero, u.mul_left_eq_zero
-/
theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
/--
theorem `isUnit_zero_iff` / 定理 `isUnit_zero_iff`

English:
theorem isUnit_zero_iff
  statement: IsUnit (0 : M₀) ↔ (0 : M₀) = 1
  proof: ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

中文:
定理 isUnit_zero_iff
  结论: IsUnit (0 : M₀) ↔ (0 : M₀) = 1
  证明: ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

Depends on / 依赖: isUnit_of_subsingleton, subsingleton_of_zero_eq_one, zero_mul
-/
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

/--
theorem `not_isUnit_zero` / 定理 `not_isUnit_zero`

English:
theorem not_isUnit_zero
  given: [Nontrivial M₀]
  statement: ¬IsUnit (0 : M₀)
  proof: mt isUnit_zero_iff.1 zero_ne_one

中文:
定理 not_isUnit_zero
  条件: [Nontrivial M₀]
  结论: ¬IsUnit (0 : M₀)
  证明: mt isUnit_zero_iff.1 zero_ne_one

Depends on / 依赖: isUnit_zero_iff, zero_ne_one
-/
theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one

namespace Ring

open scoped Classical in
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : M₀ -> M₀
  body: fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

@[inherit_doc]
scoped postfix:max "⁻¹ʳ" => inverse

中文:
定义 inverse
  签名: : M₀ -> M₀
  定义体: fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

@[inherit_doc]
scoped postfix:max "⁻¹ʳ" => inverse

Depends on / 依赖: IsUnit, h.unit
-/
noncomputable def inverse : M₀ -> M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

@[inherit_doc]
scoped postfix:max "⁻¹ʳ" => inverse

/--
theorem `inverse_unit` / 定理 `inverse_unit`

English:
theorem inverse_unit
  given: (u : M₀ˣ)
  statement: (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
  proof: by
  rw [inverse]; rw [dif_pos u.isUnit]; rw [IsUnit.unit_of_val_units]

中文:
定理 inverse_unit
  条件: (u : M₀ˣ)
  结论: (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
  证明: by
  rw [inverse]; rw [dif_pos u.isUnit]; rw [IsUnit.unit_of_val_units]

Depends on / 依赖: IsUnit, IsUnit.unit_of_val_units, dif_pos, inverse, isUnit, u.isUnit, unit_of_val_units
-/
theorem inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ) := by
  rw [inverse]; rw [dif_pos u.isUnit]; rw [IsUnit.unit_of_val_units]

/--
theorem `inverse_of_isUnit` / 定理 `inverse_of_isUnit`

English:
theorem inverse_of_isUnit
  given: {x : M₀} (h : IsUnit x)
  statement: x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀)
  proof: dif_pos h

中文:
定理 inverse_of_isUnit
  条件: {x : M₀} (h : IsUnit x)
  结论: x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀) := dif_pos h

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
/--
theorem `inverse_non_unit` / 定理 `inverse_non_unit`

English:
theorem inverse_non_unit
  given: (x : M₀) (h : ¬IsUnit x)
  statement: x⁻¹ʳ = 0
  proof: dif_neg h

中文:
定理 inverse_non_unit
  条件: (x : M₀) (h : ¬IsUnit x)
  结论: x⁻¹ʳ = 0
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ = 0 :=
  dif_neg h

/--
theorem `mul_inverse_cancel` / 定理 `mul_inverse_cancel`

English:
theorem mul_inverse_cancel
  given: (x : M₀) (h : IsUnit x)
  statement: x * x⁻¹ʳ = 1
  proof: by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.mul_inv]

中文:
定理 mul_inverse_cancel
  条件: (x : M₀) (h : IsUnit x)
  结论: x * x⁻¹ʳ = 1
  证明: by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.mul_inv]

Depends on / 依赖: Units.mul_inv, inverse_unit, mul_inv
-/
theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * x⁻¹ʳ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.mul_inv]

/--
theorem `inverse_mul_cancel` / 定理 `inverse_mul_cancel`

English:
theorem inverse_mul_cancel
  given: (x : M₀) (h : IsUnit x)
  statement: x⁻¹ʳ * x = 1
  proof: by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.inv_mul]

中文:
定理 inverse_mul_cancel
  条件: (x : M₀) (h : IsUnit x)
  结论: x⁻¹ʳ * x = 1
  证明: by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.inv_mul]

Depends on / 依赖: Units.inv_mul, inv_mul, inverse_unit
-/
theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻¹ʳ * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit]; rw [Units.inv_mul]

/--
theorem `mul_inverse_cancel_right` / 定理 `mul_inverse_cancel_right`

English:
theorem mul_inverse_cancel_right
  given: (x y : M₀) (h : IsUnit x)
  statement: y * x * x⁻¹ʳ = y
  proof: by
  rw [mul_assoc]; rw [mul_inverse_cancel x h]; rw [mul_one]

中文:
定理 mul_inverse_cancel_right
  条件: (x y : M₀) (h : IsUnit x)
  结论: y * x * x⁻¹ʳ = y
  证明: by
  rw [mul_assoc]; rw [mul_inverse_cancel x h]; rw [mul_one]

Depends on / 依赖: mul_assoc, mul_inverse_cancel, mul_one
-/
theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * x⁻¹ʳ = y := by
  rw [mul_assoc]; rw [mul_inverse_cancel x h]; rw [mul_one]

/--
theorem `inverse_mul_cancel_right` / 定理 `inverse_mul_cancel_right`

English:
theorem inverse_mul_cancel_right
  given: (x y : M₀) (h : IsUnit x)
  statement: y * x⁻¹ʳ * x = y
  proof: by
  rw [mul_assoc]; rw [inverse_mul_cancel x h]; rw [mul_one]

中文:
定理 inverse_mul_cancel_right
  条件: (x y : M₀) (h : IsUnit x)
  结论: y * x⁻¹ʳ * x = y
  证明: by
  rw [mul_assoc]; rw [inverse_mul_cancel x h]; rw [mul_one]

Depends on / 依赖: inverse_mul_cancel, mul_assoc, mul_one
-/
theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * x⁻¹ʳ * x = y := by
  rw [mul_assoc]; rw [inverse_mul_cancel x h]; rw [mul_one]

/--
theorem `mul_inverse_cancel_left` / 定理 `mul_inverse_cancel_left`

English:
theorem mul_inverse_cancel_left
  given: (x y : M₀) (h : IsUnit x)
  statement: x * (x⁻¹ʳ * y) = y
  proof: by
  rw [← mul_assoc]; rw [mul_inverse_cancel x h]; rw [one_mul]

中文:
定理 mul_inverse_cancel_left
  条件: (x y : M₀) (h : IsUnit x)
  结论: x * (x⁻¹ʳ * y) = y
  证明: by
  rw [← mul_assoc]; rw [mul_inverse_cancel x h]; rw [one_mul]

Depends on / 依赖: mul_assoc, mul_inverse_cancel, one_mul
-/
theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (x⁻¹ʳ * y) = y := by
  rw [← mul_assoc]; rw [mul_inverse_cancel x h]; rw [one_mul]

/--
theorem `inverse_mul_cancel_left` / 定理 `inverse_mul_cancel_left`

English:
theorem inverse_mul_cancel_left
  given: (x y : M₀) (h : IsUnit x)
  statement: x⁻¹ʳ * (x * y) = y
  proof: by
  rw [← mul_assoc]; rw [inverse_mul_cancel x h]; rw [one_mul]

中文:
定理 inverse_mul_cancel_left
  条件: (x y : M₀) (h : IsUnit x)
  结论: x⁻¹ʳ * (x * y) = y
  证明: by
  rw [← mul_assoc]; rw [inverse_mul_cancel x h]; rw [one_mul]

Depends on / 依赖: inverse_mul_cancel, mul_assoc, one_mul
-/
theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : x⁻¹ʳ * (x * y) = y := by
  rw [← mul_assoc]; rw [inverse_mul_cancel x h]; rw [one_mul]

/--
theorem `inverse_mul_eq_iff_eq_mul` / 定理 `inverse_mul_eq_iff_eq_mul`

English:
theorem inverse_mul_eq_iff_eq_mul
  given: (x y z : M₀) (h : IsUnit x)
  statement: x⁻¹ʳ * y = z ↔ y = x * z
  proof: ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩

中文:
定理 inverse_mul_eq_iff_eq_mul
  条件: (x y z : M₀) (h : IsUnit x)
  结论: x⁻¹ʳ * y = z ↔ y = x * z
  证明: ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩

Depends on / 依赖: inverse_mul_cancel_left, mul_inverse_cancel_left
-/
theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩

/--
theorem `eq_mul_inverse_iff_mul_eq` / 定理 `eq_mul_inverse_iff_mul_eq`

English:
theorem eq_mul_inverse_iff_mul_eq
  given: (x y z : M₀) (h : IsUnit z)
  statement: x = y * z⁻¹ʳ ↔ x * z = y
  proof: ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

中文:
定理 eq_mul_inverse_iff_mul_eq
  条件: (x y z : M₀) (h : IsUnit z)
  结论: x = y * z⁻¹ʳ ↔ x * z = y
  证明: ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

Depends on / 依赖: inverse_mul_cancel_right, mul_inverse_cancel_right
-/
theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variable (M₀) in
@[simp, grind =]
/--
theorem `inverse_one` / 定理 `inverse_one`

English:
theorem inverse_one
  statement: (1 : M₀)⁻¹ʳ = 1
  proof: inverse_unit 1

中文:
定理 inverse_one
  结论: (1 : M₀)⁻¹ʳ = 1
  证明: inverse_unit 1

Depends on / 依赖: inverse_unit
-/
theorem inverse_one : (1 : M₀)⁻¹ʳ = 1 :=
  inverse_unit 1

variable (M₀) in
@[simp, grind =]
/--
theorem `inverse_zero` / 定理 `inverse_zero`

English:
theorem inverse_zero
  statement: (0 : M₀)⁻¹ʳ = 0
  proof: by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero

@[grind =]

中文:
定理 inverse_zero
  结论: (0 : M₀)⁻¹ʳ = 0
  证明: by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero

@[grind =]

Depends on / 依赖: inverse_non_unit, nontriviality, not_isUnit_zero
-/
theorem inverse_zero : (0 : M₀)⁻¹ʳ = 0 := by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero

@[grind =]
/--
theorem `inverse_inverse` / 定理 `inverse_inverse`

English:
theorem inverse_inverse
  given: {a : M₀} (h : IsUnit a)
  statement: a⁻¹ʳ⁻¹ʳ = a
  proof: by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit]; rw [inverse_unit]; rw [inv_inv]

中文:
定理 inverse_inverse
  条件: {a : M₀} (h : IsUnit a)
  结论: a⁻¹ʳ⁻¹ʳ = a
  证明: by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit]; rw [inverse_unit]; rw [inv_inv]

Depends on / 依赖: inv_inv, inverse_unit
-/
theorem inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ = a := by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit]; rw [inverse_unit]; rw [inv_inv]

end Ring

open scoped Ring

/--
theorem `IsUnit.ringInverse` / 定理 `IsUnit.ringInverse`

English:
theorem IsUnit.ringInverse
  given: {a : M₀}
  statement: IsUnit a -> IsUnit a⁻¹ʳ

中文:
定理 IsUnit.ringInverse
  条件: {a : M₀}
  结论: IsUnit a -> IsUnit a⁻¹ʳ
-/
theorem IsUnit.ringInverse {a : M₀} : IsUnit a -> IsUnit a⁻¹ʳ
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp, grind =]
/--
theorem `isUnit_ringInverse` / 定理 `isUnit_ringInverse`

English:
theorem isUnit_ringInverse
  given: {a : M₀}
  statement: IsUnit a⁻¹ʳ ↔ IsUnit a
  proof: ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert! h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

@[grind =]

中文:
定理 isUnit_ringInverse
  条件: {a : M₀}
  结论: IsUnit a⁻¹ʳ ↔ IsUnit a
  证明: ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert! h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

@[grind =]

Depends on / 依赖: IsUnit, IsUnit.ringInverse, Ring.inverse_non_unit, contrapose, convert, inverse_non_unit, not_isUnit_zero, ringInverse, subsingleton_or_nontrivial
-/
theorem isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert! h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

@[grind =]
/--
theorem `Ring.inverse_mul` / 定理 `Ring.inverse_mul`

English:
theorem Ring.inverse_mul
  given: {a b : M₀} (h : IsUnit a ∨ IsUnit b)
  statement: (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ
  proof: by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
 

中文:
定理 Ring.inverse_mul
  条件: {a b : M₀} (h : IsUnit a ∨ IsUnit b)
  结论: (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ
  证明: by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
 

Depends on / 依赖: IsUnit, Ring.inverse_non_unit, Ring.inverse_of_isUnit, Units.val_mul, ha.mul, ha.mul_left_iff, hb.mul_right_iff, inverse_non_unit, inverse_of_isUnit, mul_inv_rev, mul_left_iff, mul_right_iff, val_mul
-/
theorem Ring.inverse_mul {a b : M₀} (h : IsUnit a ∨ IsUnit b) : (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
    simp [Ring.inverse_non_unit, ha, this]
  · simp [Ring.inverse_of_isUnit, ha, hb, ha.mul hb, ← Units.val_mul, ← mul_inv_rev]
    simp

/--
theorem `Ring.isUnit_iff_inverse_ne_zero` / 定理 `Ring.isUnit_iff_inverse_ne_zero`

English:
theorem Ring.isUnit_iff_inverse_ne_zero
  given: [Nontrivial M₀] {x : M₀}
  statement: IsUnit x ↔ x⁻¹ʳ != 0
  proof: ⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ

中文:
定理 Ring.isUnit_iff_inverse_ne_zero
  条件: [Nontrivial M₀] {x : M₀}
  结论: IsUnit x ↔ x⁻¹ʳ != 0
  证明: ⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ

Depends on / 依赖: IsUnit, IsUnit.ringInverse, Ring.inverse_non_unit, inverse_non_unit, ne_zero, ringInverse
-/
theorem Ring.isUnit_iff_inverse_ne_zero [Nontrivial M₀] {x : M₀} : IsUnit x ↔ x⁻¹ʳ != 0 :=
⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ

/--
theorem `Ring.not_isUnit_iff_inverse_eq_zero` / 定理 `Ring.not_isUnit_iff_inverse_eq_zero`

English:
theorem Ring.not_isUnit_iff_inverse_eq_zero
  given: [Nontrivial M₀] {x : M₀}
  statement: ¬ IsUnit x ↔ x⁻¹ʳ = 0
  proof: by
  grind

中文:
定理 Ring.not_isUnit_iff_inverse_eq_zero
  条件: [Nontrivial M₀] {x : M₀}
  结论: ¬ IsUnit x ↔ x⁻¹ʳ = 0
  证明: by
  grind
-/
theorem Ring.not_isUnit_iff_inverse_eq_zero [Nontrivial M₀] {x : M₀} : ¬ IsUnit x ↔ x⁻¹ʳ = 0 := by
  grind

/--
theorem `Ring.isUnit_iff_mul_inverse_cancel` / 定理 `Ring.isUnit_iff_mul_inverse_cancel`

English:
theorem Ring.isUnit_iff_mul_inverse_cancel
  given: {x : M₀}
  statement: IsUnit x ↔ x * x⁻¹ʳ = 1
  proof: by
  nontriviality M₀
  refine ⟨mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ

中文:
定理 Ring.isUnit_iff_mul_inverse_cancel
  条件: {x : M₀}
  结论: IsUnit x ↔ x * x⁻¹ʳ = 1
  证明: by
  nontriviality M₀
  refine ⟨mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ

Depends on / 依赖: contextual, contrapose, mul_inverse_cancel, nontriviality, not_isUnit_iff_inverse_eq_zero
-/
theorem Ring.isUnit_iff_mul_inverse_cancel {x : M₀} : IsUnit x ↔ x * x⁻¹ʳ = 1 := by
  nontriviality M₀
  refine ⟨mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ

/--
theorem `Ring.isUnit_iff_inverse_mul_cancel` / 定理 `Ring.isUnit_iff_inverse_mul_cancel`

English:
theorem Ring.isUnit_iff_inverse_mul_cancel
  given: (x : M₀)
  statement: IsUnit x ↔ x⁻¹ʳ * x = 1
  proof: by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

@[simp, grind =]

中文:
定理 Ring.isUnit_iff_inverse_mul_cancel
  条件: (x : M₀)
  结论: IsUnit x ↔ x⁻¹ʳ * x = 1
  证明: by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

@[simp, grind =]

Depends on / 依赖: Ring.inverse_mul_cancel, contextual, contrapose, inverse_mul_cancel, nontriviality, not_isUnit_iff_inverse_eq_zero
-/
theorem Ring.isUnit_iff_inverse_mul_cancel (x : M₀) : IsUnit x ↔ x⁻¹ʳ * x = 1 := by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

@[simp, grind =]
/--
theorem `Ring.inverse_inverse_inverse` / 定理 `Ring.inverse_inverse_inverse`

English:
theorem Ring.inverse_inverse_inverse
  given: {a : M₀}
  statement: a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ
  proof: by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

中文:
定理 Ring.inverse_inverse_inverse
  条件: {a : M₀}
  结论: a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ
  证明: by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

Depends on / 依赖: IsUnit, Ring.inverse_inverse, Ring.not_isUnit_iff_inverse_eq_zero.mp, inverse_inverse, nontriviality, not_isUnit_iff_inverse_eq_zero
-/
theorem Ring.inverse_inverse_inverse {a : M₀} : a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ := by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

namespace Units

variable [GroupWithZero G₀]

/--
Definition of `mk0` / `mk0` 的定义

English:
definition mk0
  signature: (a : G₀) (ha : a != 0)
  body: ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[simp]

中文:
定义 mk0
  签名: (a : G₀) (ha : a != 0)
  定义体: ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[simp]
-/
def mk0 (a : G₀) (ha : a != 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[simp]
/--
theorem `mk0_one` / 定理 `mk0_one`

English:
theorem mk0_one
  given: (h := one_ne_zero)
  statement: mk0 (1 : G₀) h = 1
  proof: by
  ext
  rfl

@[simp]

中文:
定理 mk0_one
  条件: (h := one_ne_zero)
  结论: mk0 (1 : G₀) h = 1
  证明: by
  ext
  rfl

@[simp]

Depends on / 依赖: one_ne_zero
-/
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
/--
theorem `val_mk0` / 定理 `val_mk0`

English:
theorem val_mk0
  given: {a : G₀} (h : a != 0)
  statement: (mk0 a h : G₀) = a
  proof: rfl

@[simp]

中文:
定理 val_mk0
  条件: {a : G₀} (h : a != 0)
  结论: (mk0 a h : G₀) = a
  证明: rfl

@[simp]
-/
theorem val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a :=
  rfl

@[simp]
/--
theorem `mk0_val` / 定理 `mk0_val`

English:
theorem mk0_val
  given: (u : G₀ˣ) (h : (u : G₀) != 0)
  statement: mk0 (u : G₀) h = u
  proof: Units.ext rfl

中文:
定理 mk0_val
  条件: (u : G₀ˣ) (h : (u : G₀) != 0)
  结论: mk0 (u : G₀) h = u
  证明: Units.ext rfl

Depends on / 依赖: Units.ext
-/
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl

/--
theorem `mul_inv'` / 定理 `mul_inv'`

English:
theorem mul_inv'
  given: (u : G₀ˣ)
  statement: u * (u : G₀)⁻¹ = 1
  proof: mul_inv_cancel₀ u.ne_zero

中文:
定理 mul_inv'
  条件: (u : G₀ˣ)
  结论: u * (u : G₀)⁻¹ = 1
  证明: mul_inv_cancel₀ u.ne_zero

Depends on / 依赖: ne_zero, u.ne_zero
-/
theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel₀ u.ne_zero

/--
theorem `inv_mul'` / 定理 `inv_mul'`

English:
theorem inv_mul'
  given: (u : G₀ˣ)
  statement: (u⁻¹ : G₀) * u = 1
  proof: inv_mul_cancel₀ u.ne_zero

@[simp]

中文:
定理 inv_mul'
  条件: (u : G₀ˣ)
  结论: (u⁻¹ : G₀) * u = 1
  证明: inv_mul_cancel₀ u.ne_zero

@[simp]

Depends on / 依赖: ne_zero, u.ne_zero
-/
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel₀ u.ne_zero

@[simp]
/--
theorem `mk0_inj` / 定理 `mk0_inj`

English:
theorem mk0_inj
  given: {a b : G₀} (ha : a != 0) (hb : b != 0)
  statement: Units.mk0 a ha = Units.mk0 b hb ↔ a = b
  proof: ⟨fun h => by injection h, fun h => Units.ext h⟩

中文:
定理 mk0_inj
  条件: {a b : G₀} (ha : a != 0) (hb : b != 0)
  结论: Units.mk0 a ha = Units.mk0 b hb ↔ a = b
  证明: ⟨fun h => by injection h, fun h => Units.ext h⟩

Depends on / 依赖: Units.ext, injection
-/
theorem mk0_inj {a b : G₀} (ha : a != 0) (hb : b != 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/--
theorem `exists0` / 定理 `exists0`

English:
theorem exists0
  given: {p : G₀ˣ -> Prop}
  statement: (exists g : G₀ˣ, p g) ↔ exists (g : G₀) (hg : g != 0), p (Units.mk0 g hg)
  proof: ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

中文:
定理 exists0
  条件: {p : G₀ˣ -> 命题}
  结论: (存在 g : G₀ˣ, p g) ↔ 存在 (g : G₀) (hg : g != 0), p (Units.mk0 g hg)
  证明: ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

Depends on / 依赖: Units.mk0, g.mk0_val, g.ne_zero, mk0_val, ne_zero
-/
theorem exists0 {p : G₀ˣ -> Prop} : (exists g : G₀ˣ, p g) ↔ exists (g : G₀) (hg : g != 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/--
theorem `exists0'` / 定理 `exists0'`

English:
theorem exists0'
  given: {p : forall g : G₀, g != 0 -> Prop}
  proof: Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]

中文:
定理 exists0'
  条件: {p : 对任意 g : G₀, g != 0 -> 命题}
  证明: Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]

Depends on / 依赖: Iff.trans, exists0, exists0.symm, simp_rw, val_mk0
-/
theorem exists0' {p : forall g : G₀, g != 0 -> Prop} :
    (exists (g : G₀) (hg : g != 0), p g hg) ↔ exists g : G₀ˣ, p g g.ne_zero :=
  Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]
/--
theorem `exists_iff_ne_zero` / 定理 `exists_iff_ne_zero`

English:
theorem exists_iff_ne_zero
  given: {p : G₀ -> Prop}
  statement: (exists u : G₀ˣ, p u) ↔ exists x != 0, p x
  proof: by
  simp [exists0]

中文:
定理 exists_iff_ne_zero
  条件: {p : G₀ -> 命题}
  结论: (存在 u : G₀ˣ, p u) ↔ 存在 x != 0, p x
  证明: by
  simp [exists0]

Depends on / 依赖: exists0
-/
theorem exists_iff_ne_zero {p : G₀ -> Prop} : (exists u : G₀ˣ, p u) ↔ exists x != 0, p x := by
  simp [exists0]

/--
theorem `_root_.GroupWithZero.eq_zero_or_unit` / 定理 `_root_.GroupWithZero.eq_zero_or_unit`

English:
theorem _root_.GroupWithZero.eq_zero_or_unit
  given: (a : G₀)
  statement: a = 0 ∨ exists u : G₀ˣ, a = u
  proof: by
  simpa using em _

中文:
定理 _root_.GroupWithZero.eq_zero_or_unit
  条件: (a : G₀)
  结论: a = 0 ∨ 存在 u : G₀ˣ, a = u
  证明: by
  simpa using em _
-/
theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ exists u : G₀ˣ, a = u := by
  simpa using em _

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c : G₀} {m n : Nat}

/--
theorem `IsUnit.mk0` / 定理 `IsUnit.mk0`

English:
theorem IsUnit.mk0
  given: (x : G₀) (hx : x != 0)
  statement: IsUnit x
  proof: (Units.mk0 x hx).isUnit

@[simp]

中文:
定理 IsUnit.mk0
  条件: (x : G₀) (hx : x != 0)
  结论: IsUnit x
  证明: (Units.mk0 x hx).isUnit

@[simp]

Depends on / 依赖: Units.mk0, isUnit
-/
theorem IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x :=
  (Units.mk0 x hx).isUnit

@[simp]
/--
theorem `isUnit_iff_ne_zero` / 定理 `isUnit_iff_ne_zero`

English:
theorem isUnit_iff_ne_zero
  statement: IsUnit a ↔ a != 0
  proof: (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

中文:
定理 isUnit_iff_ne_zero
  结论: IsUnit a ↔ a != 0
  证明: (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

Depends on / 依赖: Units.exists_iff_ne_zero, exists_iff_ne_zero
-/
theorem isUnit_iff_ne_zero : IsUnit a ↔ a != 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := @fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `NoZeroDivisors` instance, which depends on `mk0`.
@[simp]
/--
theorem `Units.mk0_mul` / 定理 `Units.mk0_mul`

English:
theorem Units.mk0_mul
  given: (x y : G₀) (hxy)
  proof: by
  ext; rfl

中文:
定理 Units.mk0_mul
  条件: (x y : G₀) (hxy)
  证明: by
  ext; rfl
-/
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl

/--
theorem `div_ne_zero` / 定理 `div_ne_zero`

English:
theorem div_ne_zero
  given: (ha : a != 0) (hb : b != 0)
  statement: a / b != 0
  proof: by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]

中文:
定理 div_ne_zero
  条件: (ha : a != 0) (hb : b != 0)
  结论: a / b != 0
  证明: by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]

Depends on / 依赖: div_eq_mul_inv, inv_ne_zero, mul_ne_zero
-/
theorem div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]
/--
theorem `div_eq_zero_iff` / 定理 `div_eq_zero_iff`

English:
theorem div_eq_zero_iff
  statement: a / b = 0 ↔ a = 0 ∨ b = 0
  proof: by simp [div_eq_mul_inv]

中文:
定理 div_eq_zero_iff
  结论: a / b = 0 ↔ a = 0 ∨ b = 0
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]

/--
theorem `div_ne_zero_iff` / 定理 `div_ne_zero_iff`

English:
theorem div_ne_zero_iff
  statement: a / b != 0 ↔ a != 0 ∧ b != 0
  proof: div_eq_zero_iff.not.trans not_or

中文:
定理 div_ne_zero_iff
  结论: a / b != 0 ↔ a != 0 ∧ b != 0
  证明: div_eq_zero_iff.not.trans not_or

Depends on / 依赖: div_eq_zero_iff, div_eq_zero_iff.not.trans, not_or
-/
theorem div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0 :=
  div_eq_zero_iff.not.trans not_or

/--
lemma `div_self` / 引理 `div_self`

English:
lemma div_self
  given: (h : a != 0)
  statement: a / a = 1
  proof: h.isUnit.div_self

@[simp]

中文:
引理 div_self
  条件: (h : a != 0)
  结论: a / a = 1
  证明: h.isUnit.div_self

@[simp]
-/
@[simp] lemma div_self (h : a != 0) : a / a = 1 := h.isUnit.div_self

@[simp]
/--
lemma `div_self_eq_one₀` / 引理 `div_self_eq_one₀`

English:
lemma div_self_eq_one₀
  statement: a / a = 1 ↔ a != 0 where
  proof: by contrapose!; simp +contextual
  mpr := div_self

中文:
引理 div_self_eq_one₀
  结论: a / a = 1 ↔ a != 0 where
  证明: by contrapose!; simp +contextual
  mpr := div_self

Depends on / 依赖: contextual, contrapose, div_self
-/
lemma div_self_eq_one₀ : a / a = 1 ↔ a != 0 where
  mp := by contrapose!; simp +contextual
  mpr := div_self

/--
lemma `eq_mul_inv_iff_mul_eq₀` / 引理 `eq_mul_inv_iff_mul_eq₀`

English:
lemma eq_mul_inv_iff_mul_eq₀
  given: (hc : c != 0)
  statement: a = b * c⁻¹ ↔ a * c = b
  proof: hc.isUnit.eq_mul_inv_iff_mul_eq

中文:
引理 eq_mul_inv_iff_mul_eq₀
  条件: (hc : c != 0)
  结论: a = b * c⁻¹ ↔ a * c = b
  证明: hc.isUnit.eq_mul_inv_iff_mul_eq

Depends on / 依赖: eq_mul_inv_iff_mul_eq, hc.isUnit.eq_mul_inv_iff_mul_eq, isUnit
-/
lemma eq_mul_inv_iff_mul_eq₀ (hc : c != 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.isUnit.eq_mul_inv_iff_mul_eq

/--
lemma `eq_inv_mul_iff_mul_eq₀` / 引理 `eq_inv_mul_iff_mul_eq₀`

English:
lemma eq_inv_mul_iff_mul_eq₀
  given: (hb : b != 0)
  statement: a = b⁻¹ * c ↔ b * a = c
  proof: hb.isUnit.eq_inv_mul_iff_mul_eq

中文:
引理 eq_inv_mul_iff_mul_eq₀
  条件: (hb : b != 0)
  结论: a = b⁻¹ * c ↔ b * a = c
  证明: hb.isUnit.eq_inv_mul_iff_mul_eq

Depends on / 依赖: eq_inv_mul_iff_mul_eq, hb.isUnit.eq_inv_mul_iff_mul_eq, isUnit
-/
lemma eq_inv_mul_iff_mul_eq₀ (hb : b != 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.isUnit.eq_inv_mul_iff_mul_eq

/--
lemma `inv_mul_eq_iff_eq_mul₀` / 引理 `inv_mul_eq_iff_eq_mul₀`

English:
lemma inv_mul_eq_iff_eq_mul₀
  given: (ha : a != 0)
  statement: a⁻¹ * b = c ↔ b = a * c
  proof: ha.isUnit.inv_mul_eq_iff_eq_mul

中文:
引理 inv_mul_eq_iff_eq_mul₀
  条件: (ha : a != 0)
  结论: a⁻¹ * b = c ↔ b = a * c
  证明: ha.isUnit.inv_mul_eq_iff_eq_mul

Depends on / 依赖: ha.isUnit.inv_mul_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul, isUnit
-/
lemma inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.isUnit.inv_mul_eq_iff_eq_mul

/--
lemma `mul_inv_eq_iff_eq_mul₀` / 引理 `mul_inv_eq_iff_eq_mul₀`

English:
lemma mul_inv_eq_iff_eq_mul₀
  given: (hb : b != 0)
  statement: a * b⁻¹ = c ↔ a = c * b
  proof: hb.isUnit.mul_inv_eq_iff_eq_mul

中文:
引理 mul_inv_eq_iff_eq_mul₀
  条件: (hb : b != 0)
  结论: a * b⁻¹ = c ↔ a = c * b
  证明: hb.isUnit.mul_inv_eq_iff_eq_mul

Depends on / 依赖: hb.isUnit.mul_inv_eq_iff_eq_mul, isUnit, mul_inv_eq_iff_eq_mul
-/
lemma mul_inv_eq_iff_eq_mul₀ (hb : b != 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.isUnit.mul_inv_eq_iff_eq_mul

/--
lemma `mul_inv_eq_one₀` / 引理 `mul_inv_eq_one₀`

English:
lemma mul_inv_eq_one₀
  given: (hb : b != 0)
  statement: a * b⁻¹ = 1 ↔ a = b
  proof: hb.isUnit.mul_inv_eq_one

中文:
引理 mul_inv_eq_one₀
  条件: (hb : b != 0)
  结论: a * b⁻¹ = 1 ↔ a = b
  证明: hb.isUnit.mul_inv_eq_one

Depends on / 依赖: hb.isUnit.mul_inv_eq_one, isUnit, mul_inv_eq_one
-/
lemma mul_inv_eq_one₀ (hb : b != 0) : a * b⁻¹ = 1 ↔ a = b := hb.isUnit.mul_inv_eq_one

/--
lemma `inv_mul_eq_one₀` / 引理 `inv_mul_eq_one₀`

English:
lemma inv_mul_eq_one₀
  given: (ha : a != 0)
  statement: a⁻¹ * b = 1 ↔ a = b
  proof: ha.isUnit.inv_mul_eq_one

中文:
引理 inv_mul_eq_one₀
  条件: (ha : a != 0)
  结论: a⁻¹ * b = 1 ↔ a = b
  证明: ha.isUnit.inv_mul_eq_one

Depends on / 依赖: ha.isUnit.inv_mul_eq_one, inv_mul_eq_one, isUnit
-/
lemma inv_mul_eq_one₀ (ha : a != 0) : a⁻¹ * b = 1 ↔ a = b := ha.isUnit.inv_mul_eq_one

/--
lemma `mul_eq_one_iff_eq_inv₀` / 引理 `mul_eq_one_iff_eq_inv₀`

English:
lemma mul_eq_one_iff_eq_inv₀
  given: (hb : b != 0)
  statement: a * b = 1 ↔ a = b⁻¹
  proof: hb.isUnit.mul_eq_one_iff_eq_inv

中文:
引理 mul_eq_one_iff_eq_inv₀
  条件: (hb : b != 0)
  结论: a * b = 1 ↔ a = b⁻¹
  证明: hb.isUnit.mul_eq_one_iff_eq_inv

Depends on / 依赖: hb.isUnit.mul_eq_one_iff_eq_inv, isUnit, mul_eq_one_iff_eq_inv
-/
lemma mul_eq_one_iff_eq_inv₀ (hb : b != 0) : a * b = 1 ↔ a = b⁻¹ := hb.isUnit.mul_eq_one_iff_eq_inv

/--
lemma `mul_eq_one_iff_inv_eq₀` / 引理 `mul_eq_one_iff_inv_eq₀`

English:
lemma mul_eq_one_iff_inv_eq₀
  given: (ha : a != 0)
  statement: a * b = 1 ↔ a⁻¹ = b
  proof: ha.isUnit.mul_eq_one_iff_inv_eq

中文:
引理 mul_eq_one_iff_inv_eq₀
  条件: (ha : a != 0)
  结论: a * b = 1 ↔ a⁻¹ = b
  证明: ha.isUnit.mul_eq_one_iff_inv_eq

Depends on / 依赖: ha.isUnit.mul_eq_one_iff_inv_eq, isUnit, mul_eq_one_iff_inv_eq
-/
lemma mul_eq_one_iff_inv_eq₀ (ha : a != 0) : a * b = 1 ↔ a⁻¹ = b := ha.isUnit.mul_eq_one_iff_inv_eq

/--
lemma `mul_eq_of_eq_mul_inv₀` / 引理 `mul_eq_of_eq_mul_inv₀`

English:
lemma mul_eq_of_eq_mul_inv₀
  given: (ha : a != 0) (h : a = c * b⁻¹)
  statement: a * b = c
  proof: by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

中文:
引理 mul_eq_of_eq_mul_inv₀
  条件: (ha : a != 0) (h : a = c * b⁻¹)
  结论: a * b = c
  证明: by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h
-/
lemma mul_eq_of_eq_mul_inv₀ (ha : a != 0) (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

/--
lemma `mul_eq_of_eq_inv_mul₀` / 引理 `mul_eq_of_eq_inv_mul₀`

English:
lemma mul_eq_of_eq_inv_mul₀
  given: (hb : b != 0) (h : b = a⁻¹ * c)
  statement: a * b = c
  proof: by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h

中文:
引理 mul_eq_of_eq_inv_mul₀
  条件: (hb : b != 0) (h : b = a⁻¹ * c)
  结论: a * b = c
  证明: by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h
-/
lemma mul_eq_of_eq_inv_mul₀ (hb : b != 0) (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h

/--
lemma `eq_mul_of_inv_mul_eq₀` / 引理 `eq_mul_of_inv_mul_eq₀`

English:
lemma eq_mul_of_inv_mul_eq₀
  given: (hc : c != 0) (h : b⁻¹ * a = c)
  statement: a = b * c
  proof: (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

中文:
引理 eq_mul_of_inv_mul_eq₀
  条件: (hc : c != 0) (h : b⁻¹ * a = c)
  结论: a = b * c
  证明: (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

Depends on / 依赖: h.symm
-/
lemma eq_mul_of_inv_mul_eq₀ (hc : c != 0) (h : b⁻¹ * a = c) : a = b * c :=
  (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

/--
lemma `eq_mul_of_mul_inv_eq₀` / 引理 `eq_mul_of_mul_inv_eq₀`

English:
lemma eq_mul_of_mul_inv_eq₀
  given: (hb : b != 0) (h : a * c⁻¹ = b)
  statement: a = b * c
  proof: (mul_eq_of_eq_mul_inv₀ hb h.symm).symm

中文:
引理 eq_mul_of_mul_inv_eq₀
  条件: (hb : b != 0) (h : a * c⁻¹ = b)
  结论: a = b * c
  证明: (mul_eq_of_eq_mul_inv₀ hb h.symm).symm

Depends on / 依赖: GradedObject, GradedObject.HasGoodTensor, h.symm
-/
lemma eq_mul_of_mul_inv_eq₀ (hb : b != 0) (h : a * c⁻¹ = b) : a = b * c :=
  (mul_eq_of_eq_mul_inv₀ hb h.symm).symm

/--
lemma `div_mul_cancel₀` / 引理 `div_mul_cancel₀`

English:
lemma div_mul_cancel₀
  given: (a : G₀) (h : b != 0)
  statement: a / b * b = a
  proof: by simp [h]

中文:
引理 div_mul_cancel₀
  条件: (a : G₀) (h : b != 0)
  结论: a / b * b = a
  证明: by simp [h]

Depends on / 依赖: GradedObject, GradedObject.HasGoodTensorTensor
-/
lemma div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a := by simp [h]

/--
lemma `mul_one_div_cancel` / 引理 `mul_one_div_cancel`

English:
lemma mul_one_div_cancel
  given: (h : a != 0)
  statement: a * (1 / a) = 1
  proof: h.isUnit.mul_one_div_cancel

中文:
引理 mul_one_div_cancel
  条件: (h : a != 0)
  结论: a * (1 / a) = 1
  证明: h.isUnit.mul_one_div_cancel

Depends on / 依赖: h.isUnit.mul_one_div_cancel, isUnit, mul_one_div_cancel
-/
lemma mul_one_div_cancel (h : a != 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel

/--
lemma `one_div_mul_cancel` / 引理 `one_div_mul_cancel`

English:
lemma one_div_mul_cancel
  given: (h : a != 0)
  statement: 1 / a * a = 1
  proof: h.isUnit.one_div_mul_cancel

@[simp]

中文:
引理 one_div_mul_cancel
  条件: (h : a != 0)
  结论: 1 / a * a = 1
  证明: h.isUnit.one_div_mul_cancel

@[simp]

Depends on / 依赖: h.isUnit.one_div_mul_cancel, isUnit, one_div_mul_cancel
-/
lemma one_div_mul_cancel (h : a != 0) : 1 / a * a = 1 := h.isUnit.one_div_mul_cancel

@[simp]
/--
lemma `div_left_inj'` / 引理 `div_left_inj'`

English:
lemma div_left_inj'
  given: (hc : c != 0)
  statement: a / c = b / c ↔ a = b
  proof: hc.isUnit.div_left_inj

中文:
引理 div_left_inj'
  条件: (hc : c != 0)
  结论: a / c = b / c ↔ a = b
  证明: hc.isUnit.div_left_inj

Depends on / 依赖: div_left_inj, hc.isUnit.div_left_inj, isUnit
-/
lemma div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj

/--
lemma `div_eq_iff` / 引理 `div_eq_iff`

English:
lemma div_eq_iff
  given: (hb : b != 0)
  statement: a / b = c ↔ a = c * b
  proof: hb.isUnit.div_eq_iff

中文:
引理 div_eq_iff
  条件: (hb : b != 0)
  结论: a / b = c ↔ a = c * b
  证明: hb.isUnit.div_eq_iff

Depends on / 依赖: div_eq_iff, hb.isUnit.div_eq_iff, isUnit
-/
lemma div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff

/--
lemma `eq_div_iff` / 引理 `eq_div_iff`

English:
lemma eq_div_iff
  given: (hb : b != 0)
  statement: c = a / b ↔ c * b = a
  proof: hb.isUnit.eq_div_iff

中文:
引理 eq_div_iff
  条件: (hb : b != 0)
  结论: c = a / b ↔ c * b = a
  证明: hb.isUnit.eq_div_iff

Depends on / 依赖: eq_div_iff, hb.isUnit.eq_div_iff, isUnit
-/
lemma eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff

-- TODO: Swap RHS around
/--
lemma `div_eq_iff_mul_eq` / 引理 `div_eq_iff_mul_eq`

English:
lemma div_eq_iff_mul_eq
  given: (hb : b != 0)
  statement: a / b = c ↔ c * b = a
  proof: hb.isUnit.div_eq_iff.trans eq_comm

中文:
引理 div_eq_iff_mul_eq
  条件: (hb : b != 0)
  结论: a / b = c ↔ c * b = a
  证明: hb.isUnit.div_eq_iff.trans eq_comm

Depends on / 依赖: div_eq_iff, eq_comm, hb.isUnit.div_eq_iff.trans, isUnit
-/
lemma div_eq_iff_mul_eq (hb : b != 0) : a / b = c ↔ c * b = a := hb.isUnit.div_eq_iff.trans eq_comm

/--
lemma `eq_div_iff_mul_eq` / 引理 `eq_div_iff_mul_eq`

English:
lemma eq_div_iff_mul_eq
  given: (hc : c != 0)
  statement: a = b / c ↔ a * c = b
  proof: hc.isUnit.eq_div_iff

中文:
引理 eq_div_iff_mul_eq
  条件: (hc : c != 0)
  结论: a = b / c ↔ a * c = b
  证明: hc.isUnit.eq_div_iff

Depends on / 依赖: eq_div_iff, hc.isUnit.eq_div_iff, isUnit
-/
lemma eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c = b := hc.isUnit.eq_div_iff

/--
lemma `div_eq_of_eq_mul` / 引理 `div_eq_of_eq_mul`

English:
lemma div_eq_of_eq_mul
  given: (hb : b != 0)
  statement: a = c * b -> a / b = c
  proof: hb.isUnit.div_eq_of_eq_mul

中文:
引理 div_eq_of_eq_mul
  条件: (hb : b != 0)
  结论: a = c * b -> a / b = c
  证明: hb.isUnit.div_eq_of_eq_mul

Depends on / 依赖: GradedObject, GradedObject.Monoidal, GradedObject.Monoidal.leftUnitor_inv_apply, GradedObject.Monoidal.tensorUnit, Iso.cancel_iso_inv_left, Iso.hom_inv_id_assoc, Monoidal, cancel_epi, cancel_iso_inv_left, comp_whiskerRight_assoc, dif_pos, div_eq_of_eq_mul, hb.isUnit.div_eq_of_eq_mul, hom_inv_id_assoc, isUnit, leftUnitor, leftUnitor_inv_apply, tensorHom_id, tensorUnitIso
-/
lemma div_eq_of_eq_mul (hb : b != 0) : a = c * b -> a / b = c := hb.isUnit.div_eq_of_eq_mul

/--
lemma `eq_div_of_mul_eq` / 引理 `eq_div_of_mul_eq`

English:
lemma eq_div_of_mul_eq
  given: (hc : c != 0)
  statement: a * c = b -> a = b / c
  proof: hc.isUnit.eq_div_of_mul_eq

中文:
引理 eq_div_of_mul_eq
  条件: (hc : c != 0)
  结论: a * c = b -> a = b / c
  证明: hc.isUnit.eq_div_of_mul_eq

Depends on / 依赖: ComplexShape, Iso.inv_hom_id_assoc, Preadditive, Preadditive.comp_add, _inv, c.Rel, comp_add, comp_zero, d_eq, eq_div_of_mul_eq, hc.isUnit.eq_div_of_mul_eq, id_whiskerLeft, inv_hom_id_assoc, isUnit, leftUnitor, mapBifunctor, mapBifunctor.d, mapBifunctor.d_eq, one_smul, whisker_exchange_assoc
-/
lemma eq_div_of_mul_eq (hc : c != 0) : a * c = b -> a = b / c := hc.isUnit.eq_div_of_mul_eq

/--
lemma `div_eq_one_iff_eq` / 引理 `div_eq_one_iff_eq`

English:
lemma div_eq_one_iff_eq
  given: (hb : b != 0)
  statement: a / b = 1 ↔ a = b
  proof: hb.isUnit.div_eq_one_iff_eq

中文:
引理 div_eq_one_iff_eq
  条件: (hb : b != 0)
  结论: a / b = 1 ↔ a = b
  证明: hb.isUnit.div_eq_one_iff_eq

Depends on / 依赖: div_eq_one_iff_eq, hb.isUnit.div_eq_one_iff_eq, isUnit
-/
lemma div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq

/--
lemma `div_mul_cancel_right₀` / 引理 `div_mul_cancel_right₀`

English:
lemma div_mul_cancel_right₀
  given: (hb : b != 0) (a : G₀)
  statement: b / (a * b) = a⁻¹
  proof: hb.isUnit.div_mul_cancel_right _

中文:
引理 div_mul_cancel_right₀
  条件: (hb : b != 0) (a : G₀)
  结论: b / (a * b) = a⁻¹
  证明: hb.isUnit.div_mul_cancel_right _

Depends on / 依赖: div_mul_cancel_right, hb.isUnit.div_mul_cancel_right, isUnit
-/
lemma div_mul_cancel_right₀ (hb : b != 0) (a : G₀) : b / (a * b) = a⁻¹ :=
  hb.isUnit.div_mul_cancel_right _

/--
lemma `mul_div_mul_right` / 引理 `mul_div_mul_right`

English:
lemma mul_div_mul_right
  given: (a b : G₀) (hc : c != 0)
  statement: a * c / (b * c) = a / b
  proof: hc.isUnit.mul_div_mul_right _ _

中文:
引理 mul_div_mul_right
  条件: (a b : G₀) (hc : c != 0)
  结论: a * c / (b * c) = a / b
  证明: hc.isUnit.mul_div_mul_right _ _

Depends on / 依赖: GradedObject, GradedObject.Monoidal, GradedObject.Monoidal.rightUnitor_inv_apply, GradedObject.Monoidal.tensorUnit, Iso.cancel_iso_inv_left, Iso.hom_inv_id_assoc, Monoidal, cancel_epi, cancel_iso_inv_left, dif_pos, hc.isUnit.mul_div_mul_right, hom_inv_id_assoc, id_tensorHom, isUnit, mul_div_mul_right, rightUnitor, rightUnitor_inv_apply, tensorUnitIso, whiskerLeft_comp_assoc
-/
lemma mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / (b * c) = a / b :=
  hc.isUnit.mul_div_mul_right _ _

-- TODO: Duplicate of `mul_inv_cancel_right₀`
/--
lemma `mul_mul_div` / 引理 `mul_mul_div`

English:
lemma mul_mul_div
  given: (a : G₀) (hb : b != 0)
  statement: a = a * b * (1 / b)
  proof: (hb.isUnit.mul_mul_div _).symm

中文:
引理 mul_mul_div
  条件: (a : G₀) (hb : b != 0)
  结论: a = a * b * (1 / b)
  证明: (hb.isUnit.mul_mul_div _).symm

Depends on / 依赖: Iso.inv_hom_id_assoc, Preadditive, Preadditive.comp_add, _inv, add_zero, c.Rel, comp_add, comp_zero, d_eq, hb.isUnit.mul_mul_div, inv_hom_id_assoc, isUnit, mapBifunctor, mapBifunctor.d, mapBifunctor.d_eq, mul_mul_div, one_smul, rightUnitor, whiskerRight_id, whisker_exchange_assoc
-/
lemma mul_mul_div (a : G₀) (hb : b != 0) : a = a * b * (1 / b) := (hb.isUnit.mul_mul_div _).symm

/--
lemma `div_div_div_cancel_right₀` / 引理 `div_div_div_cancel_right₀`

English:
lemma div_div_div_cancel_right₀
  given: (hc : c != 0) (a b : G₀)
  statement: a / c / (b / c) = a / b
  proof: by
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ hc]

中文:
引理 div_div_div_cancel_right₀
  条件: (hc : c != 0) (a b : G₀)
  结论: a / c / (b / c) = a / b
  证明: by
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ hc]

Depends on / 依赖: div_div_eq_mul_div
-/
lemma div_div_div_cancel_right₀ (hc : c != 0) (a b : G₀) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div]; rw [div_mul_cancel₀ _ hc]

/--
lemma `div_mul_div_cancel₀` / 引理 `div_mul_div_cancel₀`

English:
lemma div_mul_div_cancel₀
  given: (hb : b != 0)
  statement: a / b * (b / c) = a / c
  proof: by
  rw [← mul_div_assoc]; rw [div_mul_cancel₀ _ hb]

中文:
引理 div_mul_div_cancel₀
  条件: (hb : b != 0)
  结论: a / b * (b / c) = a / c
  证明: by
  rw [← mul_div_assoc]; rw [div_mul_cancel₀ _ hb]

Depends on / 依赖: mul_div_assoc
-/
lemma div_mul_div_cancel₀ (hb : b != 0) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc]; rw [div_mul_cancel₀ _ hb]

/--
lemma `div_mul_cancel_of_imp` / 引理 `div_mul_cancel_of_imp`

English:
lemma div_mul_cancel_of_imp
  given: (h : b = 0 -> a = 0)
  statement: a / b * b = a
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 div_mul_cancel_of_imp
  条件: (h : b = 0 -> a = 0)
  结论: a / b * b = a
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `mul_div_cancel_of_imp` / 引理 `mul_div_cancel_of_imp`

English:
lemma mul_div_cancel_of_imp
  given: (h : b = 0 -> a = 0)
  statement: a * b / b = a
  proof: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

中文:
引理 mul_div_cancel_of_imp
  条件: (h : b = 0 -> a = 0)
  结论: a * b / b = a
  证明: by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma mul_div_cancel_of_imp (h : b = 0 -> a = 0) : a * b / b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/--
lemma `divp_mk0` / 引理 `divp_mk0`

English:
lemma divp_mk0
  given: (a : G₀) (hb : b != 0)
  statement: a /ₚ Units.mk0 b hb = a / b
  proof: divp_eq_div _ _

中文:
引理 divp_mk0
  条件: (a : G₀) (hb : b != 0)
  结论: a /ₚ Units.mk0 b hb = a / b
  证明: divp_eq_div _ _
-/
@[simp] lemma divp_mk0 (a : G₀) (hb : b != 0) : a /ₚ Units.mk0 b hb = a / b := divp_eq_div _ _

/--
lemma `pow_sub₀` / 引理 `pow_sub₀`

English:
lemma pow_sub₀
  given: (a : G₀) (ha : a != 0) (h : n <= m)
  statement: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  proof: by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

中文:
引理 pow_sub₀
  条件: (a : G₀) (ha : a != 0) (h : n <= m)
  结论: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  证明: by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

Depends on / 依赖: Nat.sub_add_cancel, div_eq_mul_inv, eq_div_of_mul_eq, pow_add, pow_ne_zero, sub_add_cancel
-/
lemma pow_sub₀ (a : G₀) (ha : a != 0) (h : n <= m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

/--
lemma `pow_sub_of_lt` / 引理 `pow_sub_of_lt`

English:
lemma pow_sub_of_lt
  given: (a : G₀) (h : n < m)
  statement: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
· exact pow_sub₀ _ ha Nat.le_of_lt h

中文:
引理 pow_sub_of_lt
  条件: (a : G₀) (h : n < m)
  结论: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
· exact pow_sub₀ _ ha Nat.le_of_lt h

Depends on / 依赖: Nat.le_of_lt, Nat.ne_of_gt, Nat.sub_pos_of_lt, eq_or_ne, le_of_lt, ne_of_gt, sub_pos_of_lt, zero_mul, zero_pow
-/
lemma pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
· exact pow_sub₀ _ ha Nat.le_of_lt h

/--
lemma `inv_pow_sub₀` / 引理 `inv_pow_sub₀`

English:
lemma inv_pow_sub₀
  given: (ha : a != 0) (h : n <= m)
  statement: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  proof: by
  rw [pow_sub₀ _ (inv_ne_zero ha) h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

中文:
引理 inv_pow_sub₀
  条件: (ha : a != 0) (h : n <= m)
  结论: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  证明: by
  rw [pow_sub₀ _ (inv_ne_zero ha) h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_ne_zero, inv_pow
-/
lemma inv_pow_sub₀ (ha : a != 0) (h : n <= m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

/--
lemma `inv_pow_sub_of_lt` / 引理 `inv_pow_sub_of_lt`

English:
lemma inv_pow_sub_of_lt
  given: (a : G₀) (h : n < m)
  statement: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  proof: by
  rw [pow_sub_of_lt a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

中文:
引理 inv_pow_sub_of_lt
  条件: (a : G₀) (h : n < m)
  结论: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  证明: by
  rw [pow_sub_of_lt a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

Depends on / 依赖: inv_inv, inv_pow, pow_sub_of_lt
-/
lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

/--
lemma `zpow_sub₀` / 引理 `zpow_sub₀`

English:
lemma zpow_sub₀
  given: (ha : a != 0) (m n : Int)
  statement: a ^ (m - n) = a ^ m / a ^ n
  proof: by
  rw [Int.sub_eq_add_neg]; rw [zpow_add₀ ha]; rw [zpow_neg]; rw [div_eq_mul_inv]

中文:
引理 zpow_sub₀
  条件: (ha : a != 0) (m n : 整数)
  结论: a ^ (m - n) = a ^ m / a ^ n
  证明: by
  rw [Int.sub_eq_add_neg]; rw [zpow_add₀ ha]; rw [zpow_neg]; rw [div_eq_mul_inv]

Depends on / 依赖: Int.sub_eq_add_neg, div_eq_mul_inv, sub_eq_add_neg, zpow_neg
-/
lemma zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg]; rw [zpow_add₀ ha]; rw [zpow_neg]; rw [div_eq_mul_inv]

/--
lemma `zpow_natCast_sub_natCast₀` / 引理 `zpow_natCast_sub_natCast₀`

English:
lemma zpow_natCast_sub_natCast₀
  given: (ha : a != 0) (m n : Nat)
  statement: a ^ (m - n : Int) = a ^ m / a ^ n
  proof: by
  simpa using zpow_sub₀ ha m n

中文:
引理 zpow_natCast_sub_natCast₀
  条件: (ha : a != 0) (m n : 自然数)
  结论: a ^ (m - n : 整数) = a ^ m / a ^ n
  证明: by
  simpa using zpow_sub₀ ha m n
-/
lemma zpow_natCast_sub_natCast₀ (ha : a != 0) (m n : Nat) : a ^ (m - n : Int) = a ^ m / a ^ n := by
  simpa using zpow_sub₀ ha m n

/--
lemma `zpow_natCast_sub_one₀` / 引理 `zpow_natCast_sub_one₀`

English:
lemma zpow_natCast_sub_one₀
  given: (ha : a != 0) (n : Nat)
  statement: a ^ (n - 1 : Int) = a ^ n / a
  proof: by
  simpa using zpow_sub₀ ha n 1

中文:
引理 zpow_natCast_sub_one₀
  条件: (ha : a != 0) (n : 自然数)
  结论: a ^ (n - 1 : 整数) = a ^ n / a
  证明: by
  simpa using zpow_sub₀ ha n 1
-/
lemma zpow_natCast_sub_one₀ (ha : a != 0) (n : Nat) : a ^ (n - 1 : Int) = a ^ n / a := by
  simpa using zpow_sub₀ ha n 1

/--
lemma `zpow_one_sub_natCast₀` / 引理 `zpow_one_sub_natCast₀`

English:
lemma zpow_one_sub_natCast₀
  given: (ha : a != 0) (n : Nat)
  statement: a ^ (1 - n : Int) = a / a ^ n
  proof: by
  simpa using zpow_sub₀ ha 1 n

中文:
引理 zpow_one_sub_natCast₀
  条件: (ha : a != 0) (n : 自然数)
  结论: a ^ (1 - n : 整数) = a / a ^ n
  证明: by
  simpa using zpow_sub₀ ha 1 n
-/
lemma zpow_one_sub_natCast₀ (ha : a != 0) (n : Nat) : a ^ (1 - n : Int) = a / a ^ n := by
  simpa using zpow_sub₀ ha 1 n

/--
lemma `zpow_ne_zero` / 引理 `zpow_ne_zero`

English:
lemma zpow_ne_zero
  given: {a : G₀}
  statement: forall n : Int, a != 0 -> a ^ n != 0

中文:
引理 zpow_ne_zero
  条件: {a : G₀}
  结论: 对任意 n : 整数, a != 0 -> a ^ n != 0
-/
lemma zpow_ne_zero {a : G₀} : forall n : Int, a != 0 -> a ^ n != 0
  | (_ : Nat) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha => by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)

/--
lemma `eq_zero_of_zpow_eq_zero` / 引理 `eq_zero_of_zpow_eq_zero`

English:
lemma eq_zero_of_zpow_eq_zero
  given: {n : Int}
  statement: a ^ n = 0 -> a = 0
  proof: not_imp_not.1 (zpow_ne_zero _)

中文:
引理 eq_zero_of_zpow_eq_zero
  条件: {n : 整数}
  结论: a ^ n = 0 -> a = 0
  证明: not_imp_not.1 (zpow_ne_zero _)

Depends on / 依赖: not_imp_not, zpow_ne_zero
-/
lemma eq_zero_of_zpow_eq_zero {n : Int} : a ^ n = 0 -> a = 0 := not_imp_not.1 (zpow_ne_zero _)

/--
lemma `zpow_eq_zero_iff` / 引理 `zpow_eq_zero_iff`

English:
lemma zpow_eq_zero_iff
  given: {n : Int} (hn : n != 0)
  statement: a ^ n = 0 ↔ a = 0
  proof: ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩

中文:
引理 zpow_eq_zero_iff
  条件: {n : 整数} (hn : n != 0)
  结论: a ^ n = 0 ↔ a = 0
  证明: ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩

Depends on / 依赖: eq_zero_of_zpow_eq_zero, ha.symm, zero_zpow
-/
lemma zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩

/--
lemma `zpow_ne_zero_iff` / 引理 `zpow_ne_zero_iff`

English:
lemma zpow_ne_zero_iff
  given: {n : Int} (hn : n != 0)
  statement: a ^ n != 0 ↔ a != 0
  proof: (zpow_eq_zero_iff hn).ne

中文:
引理 zpow_ne_zero_iff
  条件: {n : 整数} (hn : n != 0)
  结论: a ^ n != 0 ↔ a != 0
  证明: (zpow_eq_zero_iff hn).ne

Depends on / 依赖: zpow_eq_zero_iff
-/
lemma zpow_ne_zero_iff {n : Int} (hn : n != 0) : a ^ n != 0 ↔ a != 0 := (zpow_eq_zero_iff hn).ne

/--
lemma `zpow_neg_mul_zpow_self` / 引理 `zpow_neg_mul_zpow_self`

English:
lemma zpow_neg_mul_zpow_self
  given: (n : Int) (ha : a != 0)
  statement: a ^ (-n) * a ^ n = 1
  proof: by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

@[grind =]

中文:
引理 zpow_neg_mul_zpow_self
  条件: (n : 整数) (ha : a != 0)
  结论: a ^ (-n) * a ^ n = 1
  证明: by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

@[grind =]

Depends on / 依赖: zpow_ne_zero, zpow_neg
-/
lemma zpow_neg_mul_zpow_self (n : Int) (ha : a != 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

@[grind =]
/--
theorem `Ring.inverse_eq_inv` / 定理 `Ring.inverse_eq_inv`

English:
theorem Ring.inverse_eq_inv
  given: (a : G₀)
  statement: a⁻¹ʳ = a⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[simp]

中文:
定理 Ring.inverse_eq_inv
  条件: (a : G₀)
  结论: a⁻¹ʳ = a⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[simp]

Depends on / 依赖: Ring.inverse_unit, Units.mk0, eq_or_ne, inverse_unit
-/
theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[simp]
/--
theorem `Ring.inverse_eq_inv'` / 定理 `Ring.inverse_eq_inv'`

English:
theorem Ring.inverse_eq_inv'
  statement: (Ring.inverse : G₀ -> G₀) = Inv.inv
  proof: funext Ring.inverse_eq_inv

中文:
定理 Ring.inverse_eq_inv'
  结论: (Ring.inverse : G₀ -> G₀) = Inv.inv
  证明: funext Ring.inverse_eq_inv

Depends on / 依赖: Ring.inverse_eq_inv, inverse_eq_inv
-/
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid :
    DivisionCommMonoid G₀ where
  __ := ‹CommGroupWithZero G₀›
  __ := GroupWithZero.toDivisionMonoid

/--
lemma `div_mul_cancel_left₀` / 引理 `div_mul_cancel_left₀`

English:
lemma div_mul_cancel_left₀
  given: (ha : a != 0) (b : G₀)
  statement: a / (a * b) = b⁻¹
  proof: ha.isUnit.div_mul_cancel_left _

中文:
引理 div_mul_cancel_left₀
  条件: (ha : a != 0) (b : G₀)
  结论: a / (a * b) = b⁻¹
  证明: ha.isUnit.div_mul_cancel_left _

Depends on / 依赖: HasHomology, K.sc, div_mul_cancel_left, ha.isUnit.div_mul_cancel_left, isUnit, op.HasHomology
-/
lemma div_mul_cancel_left₀ (ha : a != 0) (b : G₀) : a / (a * b) = b⁻¹ :=
  ha.isUnit.div_mul_cancel_left _

/--
lemma `mul_div_cancel_left_of_imp` / 引理 `mul_div_cancel_left_of_imp`

English:
lemma mul_div_cancel_left_of_imp
  given: (h : a = 0 -> b = 0)
  statement: a * b / a = b
  proof: by
  rw [mul_comm]; rw [mul_div_cancel_of_imp h]

中文:
引理 mul_div_cancel_left_of_imp
  条件: (h : a = 0 -> b = 0)
  结论: a * b / a = b
  证明: by
  rw [mul_comm]; rw [mul_div_cancel_of_imp h]

Depends on / 依赖: HasHomology, K.sc, mul_comm, mul_div_cancel_of_imp, unop.HasHomology
-/
lemma mul_div_cancel_left_of_imp (h : a = 0 -> b = 0) : a * b / a = b := by
  rw [mul_comm]; rw [mul_div_cancel_of_imp h]

/--
lemma `mul_div_cancel_of_imp'` / 引理 `mul_div_cancel_of_imp'`

English:
lemma mul_div_cancel_of_imp'
  given: (h : b = 0 -> a = 0)
  statement: b * (a / b) = a
  proof: by
  rw [mul_comm]; rw [div_mul_cancel_of_imp h]

中文:
引理 mul_div_cancel_of_imp'
  条件: (h : b = 0 -> a = 0)
  结论: b * (a / b) = a
  证明: by
  rw [mul_comm]; rw [div_mul_cancel_of_imp h]

Depends on / 依赖: div_mul_cancel_of_imp, infer_instance, mul_comm
-/
lemma mul_div_cancel_of_imp' (h : b = 0 -> a = 0) : b * (a / b) = a := by
  rw [mul_comm]; rw [div_mul_cancel_of_imp h]

/--
lemma `mul_div_cancel₀` / 引理 `mul_div_cancel₀`

English:
lemma mul_div_cancel₀
  given: (a : G₀) (hb : b != 0)
  statement: b * (a / b) = a
  proof: hb.isUnit.mul_div_cancel _

中文:
引理 mul_div_cancel₀
  条件: (a : G₀) (hb : b != 0)
  结论: b * (a / b) = a
  证明: hb.isUnit.mul_div_cancel _

Depends on / 依赖: hb.isUnit.mul_div_cancel, infer_instance, isUnit, mul_div_cancel
-/
lemma mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = a :=
  hb.isUnit.mul_div_cancel _

/--
lemma `mul_div_mul_left` / 引理 `mul_div_mul_left`

English:
lemma mul_div_mul_left
  given: (a b : G₀) (hc : c != 0)
  statement: c * a / (c * b) = a / b
  proof: hc.isUnit.mul_div_mul_left _ _

中文:
引理 mul_div_mul_left
  条件: (a b : G₀) (hc : c != 0)
  结论: c * a / (c * b) = a / b
  证明: hc.isUnit.mul_div_mul_left _ _

Depends on / 依赖: hc.isUnit.mul_div_mul_left, isUnit, mul_div_mul_left
-/
lemma mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c * b) = a / b :=
  hc.isUnit.mul_div_mul_left _ _

/--
lemma `mul_eq_mul_of_div_eq_div` / 引理 `mul_eq_mul_of_div_eq_div`

English:
lemma mul_eq_mul_of_div_eq_div
  statement: (a c : G₀) (hb : b != 0) (hd : d != 0)
  proof: by
  rw [← mul_one a]; rw [← div_self hb]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [div_mul_cancel₀ _ hd]

中文:
引理 mul_eq_mul_of_div_eq_div
  结论: (a c : G₀) (hb : b != 0) (hd : d != 0)
  证明: by
  rw [← mul_one a]; rw [← div_self hb]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [div_mul_cancel₀ _ hd]

Depends on / 依赖: div_mul_eq_mul_div, div_self, mul_comm_div, mul_one
-/
lemma mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b != 0) (hd : d != 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a]; rw [← div_self hb]; rw [← mul_comm_div]; rw [h]; rw [div_mul_eq_mul_div]; rw [div_mul_cancel₀ _ hd]

/--
lemma `div_eq_div_iff` / 引理 `div_eq_div_iff`

English:
lemma div_eq_div_iff
  given: (hb : b != 0) (hd : d != 0)
  statement: a / b = c / d ↔ a * d = c * b
  proof: hb.isUnit.div_eq_div_iff hd.isUnit

中文:
引理 div_eq_div_iff
  条件: (hb : b != 0) (hd : d != 0)
  结论: a / b = c / d ↔ a * d = c * b
  证明: hb.isUnit.div_eq_div_iff hd.isUnit

Depends on / 依赖: div_eq_div_iff, hb.isUnit.div_eq_div_iff, hd.isUnit, infer_instance, isUnit, quasiIsoAt_opFunctor_map_iff
-/
lemma div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c / d ↔ a * d = c * b :=
  hb.isUnit.div_eq_div_iff hd.isUnit

/--
lemma `mul_inv_eq_mul_inv_iff` / 引理 `mul_inv_eq_mul_inv_iff`

English:
lemma mul_inv_eq_mul_inv_iff
  given: (hb : b != 0) (hd : d != 0)
  proof: hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit

中文:
引理 mul_inv_eq_mul_inv_iff
  条件: (hb : b != 0) (hd : d != 0)
  证明: hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit

Depends on / 依赖: hb.isUnit.mul_inv_eq_mul_inv_iff, hd.isUnit, infer_instance, isUnit, mul_inv_eq_mul_inv_iff, quasiIsoAt_unopFunctor_map_iff
-/
lemma mul_inv_eq_mul_inv_iff (hb : b != 0) (hd : d != 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit

/--
lemma `inv_mul_eq_inv_mul_iff` / 引理 `inv_mul_eq_inv_mul_iff`

English:
lemma inv_mul_eq_inv_mul_iff
  given: (hb : b != 0) (hd : d != 0)
  proof: hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

中文:
引理 inv_mul_eq_inv_mul_iff
  条件: (hb : b != 0) (hd : d != 0)
  证明: hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

Depends on / 依赖: hb.isUnit.inv_mul_eq_inv_mul_iff, hd.isUnit, inv_mul_eq_inv_mul_iff, isUnit
-/
lemma inv_mul_eq_inv_mul_iff (hb : b != 0) (hd : d != 0) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b :=
  hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

/--
lemma `div_eq_div_iff_div_eq_div'` / 引理 `div_eq_div_iff_div_eq_div'`

English:
lemma div_eq_div_iff_div_eq_div'
  given: (hb : b != 0) (hc : c != 0)
  statement: a / b = c / d ↔ a / c = b / d
  proof: by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

中文:
引理 div_eq_div_iff_div_eq_div'
  条件: (hb : b != 0) (hc : c != 0)
  结论: a / b = c / d ↔ a / c = b / d
  证明: by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

Depends on / 依赖: conv_lhs, conv_rhs, div_mul_eq_mul_div, mul_comm, mul_div_assoc, mul_left_inj
-/
lemma div_eq_div_iff_div_eq_div' (hb : b != 0) (hc : c != 0) : a / b = c / d ↔ a / c = b / d := by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c]; rw [div_mul_eq_mul_div]; rw [mul_div_assoc]

/--
lemma `div_eq_div_of_div_eq_div` / 引理 `div_eq_div_of_div_eq_div`

English:
lemma div_eq_div_of_div_eq_div
  given: (hc : c != 0) (hd : d != 0) (h : a / b = c / d)
  statement: a / c = b / d
  proof: have hb : b != 0 := by
    intro hb
    rw [hb]; rw [div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h

中文:
引理 div_eq_div_of_div_eq_div
  条件: (hc : c != 0) (hd : d != 0) (h : a / b = c / d)
  结论: a / c = b / d
  证明: have hb : b != 0 := by
    intro hb
    rw [hb]; rw [div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h

Depends on / 依赖: div_eq_div_iff_div_eq_div, div_ne_zero, div_zero, h.symm, infer_instance, quasiIso_opFunctor_map_iff
-/
lemma div_eq_div_of_div_eq_div (hc : c != 0) (hd : d != 0) (h : a / b = c / d) : a / c = b / d :=
  have hb : b != 0 := by
    intro hb
    rw [hb]; rw [div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h

/--
lemma `div_div_cancel₀` / 引理 `div_div_cancel₀`

English:
lemma div_div_cancel₀
  given: (ha : a != 0)
  statement: a / (a / b) = b
  proof: ha.isUnit.div_div_cancel

中文:
引理 div_div_cancel₀
  条件: (ha : a != 0)
  结论: a / (a / b) = b
  证明: ha.isUnit.div_div_cancel

Depends on / 依赖: infer_instance, quasiIso_unopFunctor_map_iff
-/
@[simp] lemma div_div_cancel₀ (ha : a != 0) : a / (a / b) = b := ha.isUnit.div_div_cancel

/--
lemma `div_div_cancel_left'` / 引理 `div_div_cancel_left'`

English:
lemma div_div_cancel_left'
  given: (ha : a != 0)
  statement: a / b / a = b⁻¹
  proof: ha.isUnit.div_div_cancel_left

中文:
引理 div_div_cancel_left'
  条件: (ha : a != 0)
  结论: a / b / a = b⁻¹
  证明: ha.isUnit.div_div_cancel_left

Depends on / 依赖: div_div_cancel_left, ha.isUnit.div_div_cancel_left, isUnit
-/
lemma div_div_cancel_left' (ha : a != 0) : a / b / a = b⁻¹ := ha.isUnit.div_div_cancel_left

/--
lemma `div_helper` / 引理 `div_helper`

English:
lemma div_helper
  given: (b : G₀) (h : a != 0)
  statement: 1 / (a * b) * a = 1 / b
  proof: by
  rw [div_mul_eq_mul_div]; rw [one_mul]; rw [div_mul_cancel_left₀ h]; rw [one_div]

中文:
引理 div_helper
  条件: (b : G₀) (h : a != 0)
  结论: 1 / (a * b) * a = 1 / b
  证明: by
  rw [div_mul_eq_mul_div]; rw [one_mul]; rw [div_mul_cancel_left₀ h]; rw [one_div]

Depends on / 依赖: div_mul_eq_mul_div, one_div, one_mul
-/
lemma div_helper (b : G₀) (h : a != 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div]; rw [one_mul]; rw [div_mul_cancel_left₀ h]; rw [one_div]

/--
lemma `div_div_div_cancel_left'` / 引理 `div_div_div_cancel_left'`

English:
lemma div_div_div_cancel_left'
  given: (a b : G₀) (hc : c != 0)
  statement: c / a / (c / b) = b / a
  proof: by
  rw [div_div_div_eq]; rw [mul_comm]; rw [mul_div_mul_right _ _ hc]

中文:
引理 div_div_div_cancel_left'
  条件: (a b : G₀) (hc : c != 0)
  结论: c / a / (c / b) = b / a
  证明: by
  rw [div_div_div_eq]; rw [mul_comm]; rw [mul_div_mul_right _ _ hc]

Depends on / 依赖: div_div_div_eq, mul_comm, mul_div_mul_right
-/
lemma div_div_div_cancel_left' (a b : G₀) (hc : c != 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq]; rw [mul_comm]; rw [mul_div_mul_right _ _ hc]

/--
lemma `div_mul_div_cancel₀'` / 引理 `div_mul_div_cancel₀'`

English:
lemma div_mul_div_cancel₀'
  given: (ha : a != 0) (b c : G₀)
  statement: a / b * (c / a) = c / b
  proof: by
  rw [mul_comm]; rw [div_mul_div_cancel₀ ha]

中文:
引理 div_mul_div_cancel₀'
  条件: (ha : a != 0) (b c : G₀)
  结论: a / b * (c / a) = c / b
  证明: by
  rw [mul_comm]; rw [div_mul_div_cancel₀ ha]
-/
@[simp] lemma div_mul_div_cancel₀' (ha : a != 0) (b c : G₀) : a / b * (c / a) = c / b := by
  rw [mul_comm]; rw [div_mul_div_cancel₀ ha]

end CommGroupWithZero

section NoncomputableDefs

variable {M : Type*} [Nontrivial M]

open scoped Classical in
/-- Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0. -/
@[instance_reducible]
/--
Definition of `groupWithZeroOfIsUnitOrEqZero` / `groupWithZeroOfIsUnitOrEqZero` 的定义

English:
definition groupWithZeroOfIsUnitOrEqZero
  signature: [hM : MonoidWithZero M]
  body: { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [o

中文:
定义 groupWithZeroOfIsUnitOrEqZero
  签名: [hM : MonoidWithZero M]
  定义体: { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [o

Depends on / 依赖: IsUnit, IsUnit.unit_spec, Units.mul_inv_eq_iff_eq_mul, dif_neg, dif_pos, inv_zero, mul_inv_cancel, mul_inv_eq_iff_eq_mul, one_mul, resolve_right, unit_spec
-/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : forall a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [IsUnit.unit_spec] }

/-- Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
@[instance_reducible]
/--
Definition of `commGroupWithZeroOfIsUnitOrEqZero` / `commGroupWithZeroOfIsUnitOrEqZero` 的定义

English:
definition commGroupWithZeroOfIsUnitOrEqZero
  signature: [hM : CommMonoidWithZero M]
  body: { groupWithZeroOfIsUnitOrEqZero h, hM with }

中文:
定义 commGroupWithZeroOfIsUnitOrEqZero
  签名: [hM : CommMonoidWithZero M]
  定义体: { groupWithZeroOfIsUnitOrEqZero h, hM with }

Depends on / 依赖: groupWithZeroOfIsUnitOrEqZero
-/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : forall a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs
