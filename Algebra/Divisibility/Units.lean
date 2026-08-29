/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Divisibility and units

## Main definition

* `IsRelPrime x y`: that `x` and `y` are relatively prime, defined to mean that the only common
  divisors of `x` and `y` are the units.

-/

@[expose] public section

variable {α : Type*}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

/--
theorem `coe_dvd` / 定理 `coe_dvd`

English:
theorem coe_dvd
  statement: ↑u ∣ a
  proof: ⟨↑u⁻¹ * a, by simp⟩

中文:
定理 coe_dvd
  结论: ↑u ∣ a
  证明: ⟨↑u⁻¹ * a, by simp⟩
-/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩

/--
theorem `dvd_mul_right` / 定理 `dvd_mul_right`

English:
theorem dvd_mul_right
  statement: a ∣ b * u ↔ a ∣ b
  proof: Iff.intro (fun ⟨c, eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ => eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

中文:
定理 dvd_mul_right
  结论: a ∣ b * u ↔ a ∣ b
  证明: Iff.intro (fun ⟨c, eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ => eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

Depends on / 依赖: Iff.intro, Units.mul_inv_cancel_right, _root_, _root_.dvd_mul_right, dvd_mul_right, eq.symm, mul_assoc, mul_inv_cancel_right, mul_right
-/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ => eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

/--
theorem `mul_right_dvd` / 定理 `mul_right_dvd`

English:
theorem mul_right_dvd
  statement: a * u ∣ b ↔ a ∣ b
  proof: Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

中文:
定理 mul_right_dvd
  结论: a * u ∣ b ↔ a ∣ b
  证明: Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

Depends on / 依赖: Dvd.intro, Iff.intro, dvd_trans, eq.trans, mul_assoc, mul_inv, mul_one, u.mul_inv
-/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

/--
theorem `dvd_mul_left` / 定理 `dvd_mul_left`

English:
theorem dvd_mul_left
  statement: a ∣ u * b ↔ a ∣ b
  proof: by
  rw [mul_comm]
  apply dvd_mul_right

中文:
定理 dvd_mul_left
  结论: a ∣ u * b ↔ a ∣ b
  证明: by
  rw [mul_comm]
  apply dvd_mul_right

Depends on / 依赖: dvd_mul_right, mul_comm
-/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right

/--
theorem `mul_left_dvd` / 定理 `mul_left_dvd`

English:
theorem mul_left_dvd
  statement: ↑u * a ∣ b ↔ a ∣ b
  proof: by
  rw [mul_comm]
  apply mul_right_dvd

中文:
定理 mul_left_dvd
  结论: ↑u * a ∣ b ↔ a ∣ b
  证明: by
  rw [mul_comm]
  apply mul_right_dvd

Depends on / 依赖: mul_comm, mul_right_dvd
-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α}

/-- Units of a monoid divide any element of the monoid. -/
@[simp]
/--
theorem `dvd` / 定理 `dvd`

English:
theorem dvd
  given: (hu : IsUnit u)
  statement: u ∣ a
  proof: by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]

中文:
定理 dvd
  条件: (hu : IsUnit u)
  结论: u ∣ a
  证明: by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]

Depends on / 依赖: Units.coe_dvd, coe_dvd
-/
theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]
/--
theorem `dvd_mul_right` / 定理 `dvd_mul_right`

English:
theorem dvd_mul_right
  given: (hu : IsUnit u)
  statement: a ∣ b * u ↔ a ∣ b
  proof: by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

中文:
定理 dvd_mul_right
  条件: (hu : IsUnit u)
  结论: a ∣ b * u ↔ a ∣ b
  证明: by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

Depends on / 依赖: Units.dvd_mul_right, dvd_mul_right
-/
theorem dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`. -/
@[simp]
/--
theorem `mul_right_dvd` / 定理 `mul_right_dvd`

English:
theorem mul_right_dvd
  given: (hu : IsUnit u)
  statement: a * u ∣ b ↔ a ∣ b
  proof: by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

中文:
定理 mul_right_dvd
  条件: (hu : IsUnit u)
  结论: a * u ∣ b ↔ a ∣ b
  证明: by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

Depends on / 依赖: Units.mul_right_dvd, mul_right_dvd
-/
theorem mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

/--
theorem `isPrimal` / 定理 `isPrimal`

English:
theorem isPrimal
  given: (hu : IsUnit u)
  statement: IsPrimal u
  proof: fun _ _ _ => ⟨u, 1, hu.dvd, one_dvd _, (mul_one u).symm⟩

中文:
定理 isPrimal
  条件: (hu : IsUnit u)
  结论: IsPrimal u
  证明: fun _ _ _ => ⟨u, 1, hu.dvd, one_dvd _, (mul_one u).symm⟩

Depends on / 依赖: hu.dvd, mul_one, one_dvd
-/
theorem isPrimal (hu : IsUnit u) : IsPrimal u :=
  fun _ _ _ => ⟨u, 1, hu.dvd, one_dvd _, (mul_one u).symm⟩

end Monoid

section CommMonoid

variable [CommMonoid α] {a b u : α}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
associates of `b`. -/
@[simp]
/--
theorem `dvd_mul_left` / 定理 `dvd_mul_left`

English:
theorem dvd_mul_left
  given: (hu : IsUnit u)
  statement: a ∣ u * b ↔ a ∣ b
  proof: by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

中文:
定理 dvd_mul_left
  条件: (hu : IsUnit u)
  结论: a ∣ u * b ↔ a ∣ b
  证明: by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

Depends on / 依赖: Units.dvd_mul_left, dvd_mul_left
-/
theorem dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`. -/
@[simp]
/--
theorem `mul_left_dvd` / 定理 `mul_left_dvd`

English:
theorem mul_left_dvd
  given: (hu : IsUnit u)
  statement: u * a ∣ b ↔ a ∣ b
  proof: by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

中文:
定理 mul_left_dvd
  条件: (hu : IsUnit u)
  结论: u * a ∣ b ↔ a ∣ b
  证明: by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

Depends on / 依赖: Units.mul_left_dvd, mul_left_dvd
-/
theorem mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

/--
theorem `isUnit_iff_dvd_one` / 定理 `isUnit_iff_dvd_one`

English:
theorem isUnit_iff_dvd_one
  given: {x : α}
  statement: IsUnit x ↔ x ∣ 1
  proof: ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

中文:
定理 isUnit_iff_dvd_one
  条件: {x : α}
  结论: IsUnit x ↔ x ∣ 1
  证明: ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

Depends on / 依赖: IsUnit, IsUnit.dvd, h.symm, mul_comm
-/
theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

/--
theorem `isUnit_iff_forall_dvd` / 定理 `isUnit_iff_forall_dvd`

English:
theorem isUnit_iff_forall_dvd
  given: {x : α}
  statement: IsUnit x ↔ forall y, x ∣ y
  proof: isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩

中文:
定理 isUnit_iff_forall_dvd
  条件: {x : α}
  结论: IsUnit x ↔ 对任意 y, x ∣ y
  证明: isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩

Depends on / 依赖: h.trans, isUnit_iff_dvd_one, isUnit_iff_dvd_one.trans, one_dvd
-/
theorem isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ forall y, x ∣ y :=
  isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩

/--
theorem `isUnit_of_dvd_unit` / 定理 `isUnit_of_dvd_unit`

English:
theorem isUnit_of_dvd_unit
  given: {x y : α} (xy : x ∣ y) (hu : IsUnit y)
  statement: IsUnit x
  proof: isUnit_iff_dvd_one.2 xy.trans isUnit_iff_dvd_one.1 hu

中文:
定理 isUnit_of_dvd_unit
  条件: {x y : α} (xy : x ∣ y) (hu : IsUnit y)
  结论: IsUnit x
  证明: isUnit_iff_dvd_one.2 xy.trans isUnit_iff_dvd_one.1 hu

Depends on / 依赖: isUnit_iff_dvd_one, xy.trans
-/
theorem isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
isUnit_iff_dvd_one.2 xy.trans isUnit_iff_dvd_one.1 hu

/--
theorem `isUnit_of_dvd_one` / 定理 `isUnit_of_dvd_one`

English:
theorem isUnit_of_dvd_one
  given: {a : α} (h : a ∣ 1)
  statement: IsUnit (a : α)
  proof: isUnit_iff_dvd_one.mpr h

中文:
定理 isUnit_of_dvd_one
  条件: {a : α} (h : a ∣ 1)
  结论: IsUnit (a : α)
  证明: isUnit_iff_dvd_one.mpr h

Depends on / 依赖: isUnit_iff_dvd_one, isUnit_iff_dvd_one.mpr
-/
theorem isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α) :=
  isUnit_iff_dvd_one.mpr h

/--
theorem `not_isUnit_of_not_isUnit_dvd` / 定理 `not_isUnit_of_not_isUnit_dvd`

English:
theorem not_isUnit_of_not_isUnit_dvd
  given: {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b)
  statement: ¬IsUnit b
  proof: mt (isUnit_of_dvd_unit hb) ha

@[simp]

中文:
定理 not_isUnit_of_not_isUnit_dvd
  条件: {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b)
  结论: ¬IsUnit b
  证明: mt (isUnit_of_dvd_unit hb) ha

@[simp]

Depends on / 依赖: isUnit_of_dvd_unit
-/
theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (isUnit_of_dvd_unit hb) ha

@[simp]
/--
lemma `dvd_pow_self_iff` / 引理 `dvd_pow_self_iff`

English:
lemma dvd_pow_self_iff
  given: {x : α} {n : Nat}
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

中文:
引理 dvd_pow_self_iff
  条件: {x : α} {n : 自然数}
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

Depends on / 依赖: dvd_pow_self, eq_or_ne, isUnit_iff_dvd_one
-/
lemma dvd_pow_self_iff {x : α} {n : Nat} :
    x ∣ x ^ n ↔ n != 0 ∨ IsUnit x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

end CommMonoid

section RelPrime

/--
Definition of `IsRelPrime` / `IsRelPrime` 的定义

English:
definition IsRelPrime
  signature: [Monoid α] (x y : α)
  body: forall ⦃d⦄, d ∣ x -> d ∣ y -> IsUnit d

中文:
定义 IsRelPrime
  签名: [Monoid α] (x y : α)
  定义体: forall ⦃d⦄, d ∣ x -> d ∣ y -> IsUnit d

Depends on / 依赖: IsUnit
-/
def IsRelPrime [Monoid α] (x y : α) : Prop := forall ⦃d⦄, d ∣ x -> d ∣ y -> IsUnit d

variable [CommMonoid α] {x y z : α}

/--
theorem `IsRelPrime.symm` / 定理 `IsRelPrime.symm`

English:
theorem IsRelPrime.symm
  given: (H : IsRelPrime x y)
  statement: IsRelPrime y x
  proof: fun _ hx hy => H hy hx

中文:
定理 IsRelPrime.symm
  条件: (H : IsRelPrime x y)
  结论: IsRelPrime y x
  证明: fun _ hx hy => H hy hx
-/
@[symm] theorem IsRelPrime.symm (H : IsRelPrime x y) : IsRelPrime y x := fun _ hx hy => H hy hx

/--
Instance `symm_isRelPrime` / 实例 `symm_isRelPrime`

English:
instance symm_isRelPrime
  signature: : Std.Symm (IsRelPrime : α -> α -> Prop) where
  body: .symm

@[deprecated (since := "2026-06-10")] alias symmetric_isRelPrime := symm_isRelPrime

中文:
实例 symm_isRelPrime
  签名: : Std.Symm (IsRelPrime : α -> α -> 命题) where
  定义体: .symm

@[deprecated (since := "2026-06-10")] alias symmetric_isRelPrime := symm_isRelPrime
-/
instance symm_isRelPrime : Std.Symm (IsRelPrime : α -> α -> Prop) where
  symm _ _ := .symm

@[deprecated (since := "2026-06-10")] alias symmetric_isRelPrime := symm_isRelPrime

/--
theorem `isRelPrime_comm` / 定理 `isRelPrime_comm`

English:
theorem isRelPrime_comm
  statement: IsRelPrime x y ↔ IsRelPrime y x
  proof: ⟨IsRelPrime.symm, IsRelPrime.symm⟩

中文:
定理 isRelPrime_comm
  结论: IsRelPrime x y ↔ IsRelPrime y x
  证明: ⟨IsRelPrime.symm, IsRelPrime.symm⟩

Depends on / 依赖: IsRelPrime, IsRelPrime.symm
-/
theorem isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x :=
  ⟨IsRelPrime.symm, IsRelPrime.symm⟩

/--
theorem `isRelPrime_self` / 定理 `isRelPrime_self`

English:
theorem isRelPrime_self
  statement: IsRelPrime x x ↔ IsUnit x
  proof: ⟨(· dvd_rfl dvd_rfl), fun hu _ _ dvd => isUnit_of_dvd_unit dvd hu⟩

中文:
定理 isRelPrime_self
  结论: IsRelPrime x x ↔ IsUnit x
  证明: ⟨(· dvd_rfl dvd_rfl), fun hu _ _ dvd => isUnit_of_dvd_unit dvd hu⟩

Depends on / 依赖: dvd_rfl, isUnit_of_dvd_unit
-/
theorem isRelPrime_self : IsRelPrime x x ↔ IsUnit x :=
  ⟨(· dvd_rfl dvd_rfl), fun hu _ _ dvd => isUnit_of_dvd_unit dvd hu⟩

/--
theorem `IsUnit.isRelPrime_left` / 定理 `IsUnit.isRelPrime_left`

English:
theorem IsUnit.isRelPrime_left
  given: (h : IsUnit x)
  statement: IsRelPrime x y
  proof: fun _ hx _ => isUnit_of_dvd_unit hx h

中文:
定理 IsUnit.isRelPrime_left
  条件: (h : IsUnit x)
  结论: IsRelPrime x y
  证明: fun _ hx _ => isUnit_of_dvd_unit hx h

Depends on / 依赖: isUnit_of_dvd_unit
-/
theorem IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPrime x y :=
  fun _ hx _ => isUnit_of_dvd_unit hx h
/--
theorem `IsUnit.isRelPrime_right` / 定理 `IsUnit.isRelPrime_right`

English:
theorem IsUnit.isRelPrime_right
  given: (h : IsUnit y)
  statement: IsRelPrime x y
  proof: h.isRelPrime_left.symm

中文:
定理 IsUnit.isRelPrime_right
  条件: (h : IsUnit y)
  结论: IsRelPrime x y
  证明: h.isRelPrime_left.symm

Depends on / 依赖: h.isRelPrime_left.symm, isRelPrime_left
-/
theorem IsUnit.isRelPrime_right (h : IsUnit y) : IsRelPrime x y := h.isRelPrime_left.symm
/--
theorem `isRelPrime_one_left` / 定理 `isRelPrime_one_left`

English:
theorem isRelPrime_one_left
  statement: IsRelPrime 1 x
  proof: isUnit_one.isRelPrime_left

中文:
定理 isRelPrime_one_left
  结论: IsRelPrime 1 x
  证明: isUnit_one.isRelPrime_left

Depends on / 依赖: isRelPrime_left, isUnit_one, isUnit_one.isRelPrime_left
-/
theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left
/--
theorem `isRelPrime_one_right` / 定理 `isRelPrime_one_right`

English:
theorem isRelPrime_one_right
  statement: IsRelPrime x 1
  proof: isUnit_one.isRelPrime_right

中文:
定理 isRelPrime_one_right
  结论: IsRelPrime x 1
  证明: isUnit_one.isRelPrime_right

Depends on / 依赖: isRelPrime_right, isUnit_one, isUnit_one.isRelPrime_right
-/
theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right

/--
theorem `IsRelPrime.of_mul_left_left` / 定理 `IsRelPrime.of_mul_left_left`

English:
theorem IsRelPrime.of_mul_left_left
  given: (H : IsRelPrime (x * y) z)
  statement: IsRelPrime x z
  proof: fun _ hx => H (dvd_mul_of_dvd_left hx _)

中文:
定理 IsRelPrime.of_mul_left_left
  条件: (H : IsRelPrime (x * y) z)
  结论: IsRelPrime x z
  证明: fun _ hx => H (dvd_mul_of_dvd_left hx _)

Depends on / 依赖: dvd_mul_of_dvd_left
-/
theorem IsRelPrime.of_mul_left_left (H : IsRelPrime (x * y) z) : IsRelPrime x z :=
  fun _ hx => H (dvd_mul_of_dvd_left hx _)

/--
theorem `IsRelPrime.of_mul_left_right` / 定理 `IsRelPrime.of_mul_left_right`

English:
theorem IsRelPrime.of_mul_left_right
  given: (H : IsRelPrime (x * y) z)
  statement: IsRelPrime y z
  proof: (mul_comm x y ▸ H).of_mul_left_left

中文:
定理 IsRelPrime.of_mul_left_right
  条件: (H : IsRelPrime (x * y) z)
  结论: IsRelPrime y z
  证明: (mul_comm x y ▸ H).of_mul_left_left

Depends on / 依赖: mul_comm, of_mul_left_left
-/
theorem IsRelPrime.of_mul_left_right (H : IsRelPrime (x * y) z) : IsRelPrime y z :=
  (mul_comm x y ▸ H).of_mul_left_left

/--
theorem `IsRelPrime.of_mul_right_left` / 定理 `IsRelPrime.of_mul_right_left`

English:
theorem IsRelPrime.of_mul_right_left
  given: (H : IsRelPrime x (y * z))
  statement: IsRelPrime x y
  proof: by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left

中文:
定理 IsRelPrime.of_mul_right_left
  条件: (H : IsRelPrime x (y * z))
  结论: IsRelPrime x y
  证明: by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left

Depends on / 依赖: H.of_mul_left_left, isRelPrime_comm, of_mul_left_left
-/
theorem IsRelPrime.of_mul_right_left (H : IsRelPrime x (y * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left

/--
theorem `IsRelPrime.of_mul_right_right` / 定理 `IsRelPrime.of_mul_right_right`

English:
theorem IsRelPrime.of_mul_right_right
  given: (H : IsRelPrime x (y * z))
  statement: IsRelPrime x z
  proof: (mul_comm y z ▸ H).of_mul_right_left

中文:
定理 IsRelPrime.of_mul_right_right
  条件: (H : IsRelPrime x (y * z))
  结论: IsRelPrime x z
  证明: (mul_comm y z ▸ H).of_mul_right_left

Depends on / 依赖: mul_comm, of_mul_right_left
-/
theorem IsRelPrime.of_mul_right_right (H : IsRelPrime x (y * z)) : IsRelPrime x z :=
  (mul_comm y z ▸ H).of_mul_right_left

/--
theorem `IsRelPrime.of_dvd_left` / 定理 `IsRelPrime.of_dvd_left`

English:
theorem IsRelPrime.of_dvd_left
  given: (h : IsRelPrime y z) (dvd : x ∣ y)
  statement: IsRelPrime x z
  proof: by
  obtain ⟨d, rfl⟩ := dvd; exact IsRelPrime.of_mul_left_left h

中文:
定理 IsRelPrime.of_dvd_left
  条件: (h : IsRelPrime y z) (dvd : x ∣ y)
  结论: IsRelPrime x z
  证明: by
  obtain ⟨d, rfl⟩ := dvd; exact IsRelPrime.of_mul_left_left h

Depends on / 依赖: IsRelPrime, IsRelPrime.of_mul_left_left, of_mul_left_left
-/
theorem IsRelPrime.of_dvd_left (h : IsRelPrime y z) (dvd : x ∣ y) : IsRelPrime x z := by
  obtain ⟨d, rfl⟩ := dvd; exact IsRelPrime.of_mul_left_left h

/--
theorem `IsRelPrime.of_dvd_right` / 定理 `IsRelPrime.of_dvd_right`

English:
theorem IsRelPrime.of_dvd_right
  given: (h : IsRelPrime z y) (dvd : x ∣ y)
  statement: IsRelPrime z x
  proof: (h.symm.of_dvd_left dvd).symm

中文:
定理 IsRelPrime.of_dvd_right
  条件: (h : IsRelPrime z y) (dvd : x ∣ y)
  结论: IsRelPrime z x
  证明: (h.symm.of_dvd_left dvd).symm

Depends on / 依赖: h.symm.of_dvd_left, of_dvd_left
-/
theorem IsRelPrime.of_dvd_right (h : IsRelPrime z y) (dvd : x ∣ y) : IsRelPrime z x :=
  (h.symm.of_dvd_left dvd).symm

/--
theorem `IsRelPrime.isUnit_of_dvd` / 定理 `IsRelPrime.isUnit_of_dvd`

English:
theorem IsRelPrime.isUnit_of_dvd
  given: (H : IsRelPrime x y) (d : x ∣ y)
  statement: IsUnit x
  proof: H dvd_rfl d

中文:
定理 IsRelPrime.isUnit_of_dvd
  条件: (H : IsRelPrime x y) (d : x ∣ y)
  结论: IsUnit x
  证明: H dvd_rfl d

Depends on / 依赖: dvd_rfl
-/
theorem IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) (d : x ∣ y) : IsUnit x := H dvd_rfl d

section IsUnit

variable (hu : IsUnit x)

include hu

/--
theorem `isRelPrime_mul_unit_left_left` / 定理 `isRelPrime_mul_unit_left_left`

English:
theorem isRelPrime_mul_unit_left_left
  statement: IsRelPrime (x * y) z ↔ IsRelPrime y z
  proof: ⟨IsRelPrime.of_mul_left_right, fun H _ h => H (hu.dvd_mul_left.mp h)⟩

中文:
定理 isRelPrime_mul_unit_left_left
  结论: IsRelPrime (x * y) z ↔ IsRelPrime y z
  证明: ⟨IsRelPrime.of_mul_left_right, fun H _ h => H (hu.dvd_mul_left.mp h)⟩

Depends on / 依赖: IsRelPrime, IsRelPrime.of_mul_left_right, dvd_mul_left, hu.dvd_mul_left.mp, of_mul_left_right
-/
theorem isRelPrime_mul_unit_left_left : IsRelPrime (x * y) z ↔ IsRelPrime y z :=
  ⟨IsRelPrime.of_mul_left_right, fun H _ h => H (hu.dvd_mul_left.mp h)⟩

/--
theorem `isRelPrime_mul_unit_left_right` / 定理 `isRelPrime_mul_unit_left_right`

English:
theorem isRelPrime_mul_unit_left_right
  statement: IsRelPrime y (x * z) ↔ IsRelPrime y z
  proof: by
  rw [isRelPrime_comm]; rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_comm]

中文:
定理 isRelPrime_mul_unit_left_right
  结论: IsRelPrime y (x * z) ↔ IsRelPrime y z
  证明: by
  rw [isRelPrime_comm]; rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_comm]

Depends on / 依赖: isRelPrime_comm, isRelPrime_mul_unit_left_left
-/
theorem isRelPrime_mul_unit_left_right : IsRelPrime y (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_comm]; rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_comm]

/--
theorem `isRelPrime_mul_unit_left` / 定理 `isRelPrime_mul_unit_left`

English:
theorem isRelPrime_mul_unit_left
  statement: IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z
  proof: by
  rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_mul_unit_left_right hu]

中文:
定理 isRelPrime_mul_unit_left
  结论: IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z
  证明: by
  rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_mul_unit_left_right hu]

Depends on / 依赖: isRelPrime_mul_unit_left_left, isRelPrime_mul_unit_left_right
-/
theorem isRelPrime_mul_unit_left : IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_left_left hu]; rw [isRelPrime_mul_unit_left_right hu]

/--
theorem `isRelPrime_mul_unit_right_left` / 定理 `isRelPrime_mul_unit_right_left`

English:
theorem isRelPrime_mul_unit_right_left
  statement: IsRelPrime (y * x) z ↔ IsRelPrime y z
  proof: by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_left hu]

中文:
定理 isRelPrime_mul_unit_right_left
  结论: IsRelPrime (y * x) z ↔ IsRelPrime y z
  证明: by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_left hu]

Depends on / 依赖: isRelPrime_mul_unit_left_left, mul_comm
-/
theorem isRelPrime_mul_unit_right_left : IsRelPrime (y * x) z ↔ IsRelPrime y z := by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_left hu]

/--
theorem `isRelPrime_mul_unit_right_right` / 定理 `isRelPrime_mul_unit_right_right`

English:
theorem isRelPrime_mul_unit_right_right
  statement: IsRelPrime y (z * x) ↔ IsRelPrime y z
  proof: by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_right hu]

中文:
定理 isRelPrime_mul_unit_right_right
  结论: IsRelPrime y (z * x) ↔ IsRelPrime y z
  证明: by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_right hu]

Depends on / 依赖: isRelPrime_mul_unit_left_right, mul_comm
-/
theorem isRelPrime_mul_unit_right_right : IsRelPrime y (z * x) ↔ IsRelPrime y z := by
  rw [mul_comm]; rw [isRelPrime_mul_unit_left_right hu]

/--
theorem `isRelPrime_mul_unit_right` / 定理 `isRelPrime_mul_unit_right`

English:
theorem isRelPrime_mul_unit_right
  statement: IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z
  proof: by
  rw [isRelPrime_mul_unit_right_left hu]; rw [isRelPrime_mul_unit_right_right hu]

中文:
定理 isRelPrime_mul_unit_right
  结论: IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z
  证明: by
  rw [isRelPrime_mul_unit_right_left hu]; rw [isRelPrime_mul_unit_right_right hu]

Depends on / 依赖: isRelPrime_mul_unit_right_left, isRelPrime_mul_unit_right_right
-/
theorem isRelPrime_mul_unit_right : IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_right_left hu]; rw [isRelPrime_mul_unit_right_right hu]

end IsUnit

/--
theorem `IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal` / 定理 `IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal`

English:
theorem IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal
  statement: (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
  proof: by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact (H1.of_mul_left_right.isUnit_of_dvd hb).mul_right_dvd.mpr ha

中文:
定理 IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal
  结论: (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
  证明: by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact (H1.of_mul_left_right.isUnit_of_dvd hb).mul_right_dvd.mpr ha

Depends on / 依赖: H1.of_mul_left_right.isUnit_of_dvd, isUnit_of_dvd, mul_right_dvd, mul_right_dvd.mpr, of_mul_left_right
-/
theorem IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact (H1.of_mul_left_right.isUnit_of_dvd hb).mul_right_dvd.mpr ha

/--
theorem `IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal` / 定理 `IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal`

English:
theorem IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal
  statement: (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
  proof: H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h

中文:
定理 IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal
  结论: (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
  证明: H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h

Depends on / 依赖: H1.dvd_of_dvd_mul_right_of_isPrimal, dvd_of_dvd_mul_right_of_isPrimal, mul_comm
-/
theorem IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ z :=
  H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h

/--
theorem `IsRelPrime.mul_dvd_of_right_isPrimal` / 定理 `IsRelPrime.mul_dvd_of_right_isPrimal`

English:
theorem IsRelPrime.mul_dvd_of_right_isPrimal
  statement: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  proof: by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)

中文:
定理 IsRelPrime.mul_dvd_of_right_isPrimal
  结论: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  证明: by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)

Depends on / 依赖: H.symm.dvd_of_dvd_mul_left_of_isPrimal, dvd_of_dvd_mul_left_of_isPrimal, mul_dvd_mul_left
-/
theorem IsRelPrime.mul_dvd_of_right_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hy : IsPrimal y) : x * y ∣ z := by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)

/--
theorem `IsRelPrime.mul_dvd_of_left_isPrimal` / 定理 `IsRelPrime.mul_dvd_of_left_isPrimal`

English:
theorem IsRelPrime.mul_dvd_of_left_isPrimal
  statement: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  proof: by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

中文:
定理 IsRelPrime.mul_dvd_of_left_isPrimal
  结论: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  证明: by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

Depends on / 依赖: H.symm.mul_dvd_of_right_isPrimal, mul_comm, mul_dvd_of_right_isPrimal
-/
theorem IsRelPrime.mul_dvd_of_left_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hx : IsPrimal x) : x * y ∣ z := by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

/-! `IsRelPrime` enjoys desirable properties in a decomposition monoid.
See Lemma 6.3 in *On properties of square-free elements in commutative cancellative monoids*,
https://doi.org/10.1007/s00233-019-10022-3. -/

variable [DecompositionMonoid α]

/--
theorem `IsRelPrime.dvd_of_dvd_mul_right` / 定理 `IsRelPrime.dvd_of_dvd_mul_right`

English:
theorem IsRelPrime.dvd_of_dvd_mul_right
  given: (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
  statement: x ∣ y
  proof: H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)

中文:
定理 IsRelPrime.dvd_of_dvd_mul_right
  条件: (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
  结论: x ∣ y
  证明: H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, H1.dvd_of_dvd_mul_right_of_isPrimal, dvd_of_dvd_mul_right_of_isPrimal, primal
-/
theorem IsRelPrime.dvd_of_dvd_mul_right (H1 : IsRelPrime x z) (H2 : x ∣ y * z) : x ∣ y :=
  H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)

/--
theorem `IsRelPrime.dvd_of_dvd_mul_left` / 定理 `IsRelPrime.dvd_of_dvd_mul_left`

English:
theorem IsRelPrime.dvd_of_dvd_mul_left
  given: (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
  statement: x ∣ z
  proof: H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)

中文:
定理 IsRelPrime.dvd_of_dvd_mul_left
  条件: (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
  结论: x ∣ z
  证明: H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)

Depends on / 依赖: H1.dvd_of_dvd_mul_right, dvd_of_dvd_mul_right, mul_comm
-/
theorem IsRelPrime.dvd_of_dvd_mul_left (H1 : IsRelPrime x y) (H2 : x ∣ y * z) : x ∣ z :=
  H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)

/--
theorem `IsRelPrime.mul_left` / 定理 `IsRelPrime.mul_left`

English:
theorem IsRelPrime.mul_left
  given: (H1 : IsRelPrime x z) (H2 : IsRelPrime y z)
  statement: IsRelPrime (x * y) z
  proof: fun _ h hz => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (dvd_mul_right a b).trans hz).mul (H2 hb <| (dvd_mul_left b a).trans hz)

中文:
定理 IsRelPrime.mul_left
  条件: (H1 : IsRelPrime x z) (H2 : IsRelPrime y z)
  结论: IsRelPrime (x * y) z
  证明: fun _ h hz => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (dvd_mul_right a b).trans hz).mul (H2 hb <| (dvd_mul_left b a).trans hz)

Depends on / 依赖: dvd_mul_left, dvd_mul_right, exists_dvd_and_dvd_of_dvd_mul
-/
theorem IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsRelPrime y z) : IsRelPrime (x * y) z :=
  fun _ h hz => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (dvd_mul_right a b).trans hz).mul (H2 hb <| (dvd_mul_left b a).trans hz)

/--
theorem `IsRelPrime.mul_right` / 定理 `IsRelPrime.mul_right`

English:
theorem IsRelPrime.mul_right
  given: (H1 : IsRelPrime x y) (H2 : IsRelPrime x z)
  proof: by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2

中文:
定理 IsRelPrime.mul_right
  条件: (H1 : IsRelPrime x y) (H2 : IsRelPrime x z)
  证明: by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2

Depends on / 依赖: H1.mul_left, isRelPrime_comm, mul_left
-/
theorem IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : IsRelPrime x z) :
    IsRelPrime x (y * z) := by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2

/--
theorem `IsRelPrime.mul_left_iff` / 定理 `IsRelPrime.mul_left_iff`

English:
theorem IsRelPrime.mul_left_iff
  statement: IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z
  proof: ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

中文:
定理 IsRelPrime.mul_left_iff
  结论: IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z
  证明: ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

Depends on / 依赖: H.of_mul_left_left, H.of_mul_left_right, H1.mul_left, mul_left, of_mul_left_left, of_mul_left_right
-/
theorem IsRelPrime.mul_left_iff : IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

/--
theorem `IsRelPrime.mul_right_iff` / 定理 `IsRelPrime.mul_right_iff`

English:
theorem IsRelPrime.mul_right_iff
  statement: IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z
  proof: ⟨fun H => ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ => H1.mul_right H2⟩

中文:
定理 IsRelPrime.mul_right_iff
  结论: IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z
  证明: ⟨fun H => ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ => H1.mul_right H2⟩

Depends on / 依赖: H.of_mul_right_left, H.of_mul_right_right, H1.mul_right, mul_right, of_mul_right_left, of_mul_right_right
-/
theorem IsRelPrime.mul_right_iff : IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z :=
  ⟨fun H => ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ => H1.mul_right H2⟩

/--
theorem `IsRelPrime.mul_dvd` / 定理 `IsRelPrime.mul_dvd`

English:
theorem IsRelPrime.mul_dvd
  given: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  statement: x * y ∣ z
  proof: H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

中文:
定理 IsRelPrime.mul_dvd
  条件: (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  结论: x * y ∣ z
  证明: H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, H.mul_dvd_of_left_isPrimal, mul_dvd_of_left_isPrimal, primal
-/
theorem IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
  H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

end RelPrime
