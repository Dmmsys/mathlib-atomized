/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Lemmas about units in `ℤ`, which interact with the order structure.
-/

public section


namespace Int

/--
theorem `isUnit_iff_abs_eq` / 定理 `isUnit_iff_abs_eq`

English:
theorem isUnit_iff_abs_eq
  given: {x : Int}
  statement: IsUnit x ↔ abs x = 1
  proof: by
  rw [isUnit_iff_natAbs_eq]; rw [abs_eq_natAbs]; rw [← Int.ofNat_one]; rw [natCast_inj]

中文:
定理 isUnit_iff_abs_eq
  条件: {x : 整数}
  结论: IsUnit x ↔ abs x = 1
  证明: by
  rw [isUnit_iff_natAbs_eq]; rw [abs_eq_natAbs]; rw [← Int.ofNat_one]; rw [natCast_inj]

Depends on / 依赖: Int.ofNat_one, abs_eq_natAbs, isUnit_iff_natAbs_eq, natCast_inj, ofNat_one
-/
theorem isUnit_iff_abs_eq {x : Int} : IsUnit x ↔ abs x = 1 := by
  rw [isUnit_iff_natAbs_eq]; rw [abs_eq_natAbs]; rw [← Int.ofNat_one]; rw [natCast_inj]

/--
theorem `isUnit_sq` / 定理 `isUnit_sq`

English:
theorem isUnit_sq
  given: {a : Int} (ha : IsUnit a)
  statement: a ^ 2 = 1
  proof: by rw [sq, isUnit_mul_self ha]

@[simp]

中文:
定理 isUnit_sq
  条件: {a : 整数} (ha : IsUnit a)
  结论: a ^ 2 = 1
  证明: by rw [sq, isUnit_mul_self ha]

@[simp]

Depends on / 依赖: isUnit_mul_self
-/
theorem isUnit_sq {a : Int} (ha : IsUnit a) : a ^ 2 = 1 := by rw [sq, isUnit_mul_self ha]

@[simp]
/--
theorem `units_sq` / 定理 `units_sq`

English:
theorem units_sq
  given: (u : Intˣ)
  statement: u ^ 2 = 1
  proof: by
  rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [isUnit_sq u.isUnit]

alias units_pow_two := units_sq

@[simp]

中文:
定理 units_sq
  条件: (u : 整数ˣ)
  结论: u ^ 2 = 1
  证明: by
  rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [isUnit_sq u.isUnit]

alias units_pow_two := units_sq

@[simp]

Depends on / 依赖: Units.ext_iff, Units.val_one, Units.val_pow_eq_pow_val, ext_iff, isUnit, isUnit_sq, u.isUnit, val_one, val_pow_eq_pow_val
-/
theorem units_sq (u : Intˣ) : u ^ 2 = 1 := by
  rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [isUnit_sq u.isUnit]

alias units_pow_two := units_sq

@[simp]
/--
theorem `units_mul_self` / 定理 `units_mul_self`

English:
theorem units_mul_self
  given: (u : Intˣ)
  statement: u * u = 1
  proof: by rw [← sq, units_sq]

@[simp]

中文:
定理 units_mul_self
  条件: (u : 整数ˣ)
  结论: u * u = 1
  证明: by rw [← sq, units_sq]

@[simp]

Depends on / 依赖: units_sq
-/
theorem units_mul_self (u : Intˣ) : u * u = 1 := by rw [← sq, units_sq]

@[simp]
/--
theorem `units_inv_eq_self` / 定理 `units_inv_eq_self`

English:
theorem units_inv_eq_self
  given: (u : Intˣ)
  statement: u⁻¹ = u
  proof: by rw [inv_eq_iff_mul_eq_one, units_mul_self]

中文:
定理 units_inv_eq_self
  条件: (u : 整数ˣ)
  结论: u⁻¹ = u
  证明: by rw [inv_eq_iff_mul_eq_one, units_mul_self]

Depends on / 依赖: inv_eq_iff_mul_eq_one, units_mul_self
-/
theorem units_inv_eq_self (u : Intˣ) : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, units_mul_self]

/--
theorem `units_div_eq_mul` / 定理 `units_div_eq_mul`

English:
theorem units_div_eq_mul
  given: (u₁ u₂ : Intˣ)
  statement: u₁ / u₂ = u₁ * u₂
  proof: by
  rw [div_eq_mul_inv]; rw [units_inv_eq_self]

中文:
定理 units_div_eq_mul
  条件: (u₁ u₂ : 整数ˣ)
  结论: u₁ / u₂ = u₁ * u₂
  证明: by
  rw [div_eq_mul_inv]; rw [units_inv_eq_self]

Depends on / 依赖: div_eq_mul_inv, units_inv_eq_self
-/
theorem units_div_eq_mul (u₁ u₂ : Intˣ) : u₁ / u₂ = u₁ * u₂ := by
  rw [div_eq_mul_inv]; rw [units_inv_eq_self]

-- `Units.val_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further
@[simp]
/--
theorem `units_coe_mul_self` / 定理 `units_coe_mul_self`

English:
theorem units_coe_mul_self
  given: (u : Intˣ)
  statement: (u * u : Int) = 1
  proof: by
  rw [← Units.val_mul]; rw [units_mul_self]; rw [Units.val_one]

中文:
定理 units_coe_mul_self
  条件: (u : 整数ˣ)
  结论: (u * u : 整数) = 1
  证明: by
  rw [← Units.val_mul]; rw [units_mul_self]; rw [Units.val_one]

Depends on / 依赖: Units.val_mul, Units.val_one, units_mul_self, val_mul, val_one
-/
theorem units_coe_mul_self (u : Intˣ) : (u * u : Int) = 1 := by
  rw [← Units.val_mul]; rw [units_mul_self]; rw [Units.val_one]

/--
theorem `neg_one_pow_ne_zero` / 定理 `neg_one_pow_ne_zero`

English:
theorem neg_one_pow_ne_zero
  given: {n : Nat}
  statement: (-1 : Int) ^ n != 0
  proof: by simp

中文:
定理 neg_one_pow_ne_zero
  条件: {n : 自然数}
  结论: (-1 : 整数) ^ n != 0
  证明: by simp
-/
theorem neg_one_pow_ne_zero {n : Nat} : (-1 : Int) ^ n != 0 := by simp

/--
theorem `sq_eq_one_of_sq_lt_four` / 定理 `sq_eq_one_of_sq_lt_four`

English:
theorem sq_eq_one_of_sq_lt_four
  given: {x : Int} (h1 : x ^ 2 < 4) (h2 : x != 0)
  statement: x ^ 2 = 1
  proof: sq_eq_one_iff.mpr
    ((abs_eq (zero_le_one' Int)).mp
      (le_antisymm (lt_add_one_iff.mp (abs_lt_of_sq_lt_sq h1 zero_le_two))
        (sub_one_lt_iff.mp (abs_pos.mpr h2))))

中文:
定理 sq_eq_one_of_sq_lt_four
  条件: {x : 整数} (h1 : x ^ 2 < 4) (h2 : x != 0)
  结论: x ^ 2 = 1
  证明: sq_eq_one_iff.mpr
    ((abs_eq (zero_le_one' Int)).mp
      (le_antisymm (lt_add_one_iff.mp (abs_lt_of_sq_lt_sq h1 zero_le_two))
        (sub_one_lt_iff.mp (abs_pos.mpr h2))))

Depends on / 依赖: abs_eq, abs_lt_of_sq_lt_sq, abs_pos, abs_pos.mpr, le_antisymm, lt_add_one_iff, lt_add_one_iff.mp, sq_eq_one_iff, sq_eq_one_iff.mpr, sub_one_lt_iff, sub_one_lt_iff.mp, zero_le_one, zero_le_two
-/
theorem sq_eq_one_of_sq_lt_four {x : Int} (h1 : x ^ 2 < 4) (h2 : x != 0) : x ^ 2 = 1 :=
  sq_eq_one_iff.mpr
    ((abs_eq (zero_le_one' Int)).mp
      (le_antisymm (lt_add_one_iff.mp (abs_lt_of_sq_lt_sq h1 zero_le_two))
        (sub_one_lt_iff.mp (abs_pos.mpr h2))))

/--
theorem `sq_eq_one_of_sq_le_three` / 定理 `sq_eq_one_of_sq_le_three`

English:
theorem sq_eq_one_of_sq_le_three
  given: {x : Int} (h1 : x ^ 2 <= 3) (h2 : x != 0)
  statement: x ^ 2 = 1
  proof: sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one (3 : Int))) h2

中文:
定理 sq_eq_one_of_sq_le_three
  条件: {x : 整数} (h1 : x ^ 2 <= 3) (h2 : x != 0)
  结论: x ^ 2 = 1
  证明: sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one (3 : Int))) h2

Depends on / 依赖: lt_add_one, lt_of_le_of_lt, sq_eq_one_of_sq_lt_four
-/
theorem sq_eq_one_of_sq_le_three {x : Int} (h1 : x ^ 2 <= 3) (h2 : x != 0) : x ^ 2 = 1 :=
  sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one (3 : Int))) h2

/--
theorem `units_pow_eq_pow_mod_two` / 定理 `units_pow_eq_pow_mod_two`

English:
theorem units_pow_eq_pow_mod_two
  given: (u : Intˣ) (n : Nat)
  statement: u ^ n = u ^ (n % 2)
  proof: by
  conv =>
    lhs
    rw [← Nat.mod_add_div n 2]
    rw [pow_add]; rw [pow_mul]; rw [units_sq]; rw [one_pow]; rw [mul_one]

中文:
定理 units_pow_eq_pow_mod_two
  条件: (u : 整数ˣ) (n : 自然数)
  结论: u ^ n = u ^ (n % 2)
  证明: by
  conv =>
    lhs
    rw [← Nat.mod_add_div n 2]
    rw [pow_add]; rw [pow_mul]; rw [units_sq]; rw [one_pow]; rw [mul_one]

Depends on / 依赖: Nat.mod_add_div, mod_add_div, mul_one, one_pow, pow_add, pow_mul, units_sq
-/
theorem units_pow_eq_pow_mod_two (u : Intˣ) (n : Nat) : u ^ n = u ^ (n % 2) := by
  conv =>
    lhs
    rw [← Nat.mod_add_div n 2]
    rw [pow_add]; rw [pow_mul]; rw [units_sq]; rw [one_pow]; rw [mul_one]

end Int
