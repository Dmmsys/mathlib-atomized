/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about commuting pairs of elements involving units.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {M : Type*}

section Monoid
variable [Monoid M] {n : Nat} {a b : M} {u u₁ u₂ : Mˣ}

namespace Commute

@[to_additive]
/--
theorem `units_inv_right` / 定理 `units_inv_right`

English:
theorem units_inv_right
  statement: Commute a u -> Commute a ↑u⁻¹
  proof: SemiconjBy.units_inv_right

@[to_additive (attr := simp)]

中文:
定理 units_inv_right
  结论: Commute a u -> Commute a ↑u⁻¹
  证明: SemiconjBy.units_inv_right

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_inv_right, units_inv_right
-/
theorem units_inv_right : Commute a u -> Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right

@[to_additive (attr := simp)]
/--
theorem `units_inv_right_iff` / 定理 `units_inv_right_iff`

English:
theorem units_inv_right_iff
  statement: Commute a ↑u⁻¹ ↔ Commute a u
  proof: SemiconjBy.units_inv_right_iff

@[to_additive]

中文:
定理 units_inv_right_iff
  结论: Commute a ↑u⁻¹ ↔ Commute a u
  证明: SemiconjBy.units_inv_right_iff

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_inv_right_iff, units_inv_right_iff
-/
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff

@[to_additive]
/--
theorem `units_inv_left` / 定理 `units_inv_left`

English:
theorem units_inv_left
  statement: Commute (↑u) a -> Commute (↑u⁻¹) a
  proof: SemiconjBy.units_inv_symm_left

@[to_additive (attr := simp)]

中文:
定理 units_inv_left
  结论: Commute (↑u) a -> Commute (↑u⁻¹) a
  证明: SemiconjBy.units_inv_symm_left

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_inv_symm_left, units_inv_symm_left
-/
theorem units_inv_left : Commute (↑u) a -> Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left

@[to_additive (attr := simp)]
/--
theorem `units_inv_left_iff` / 定理 `units_inv_left_iff`

English:
theorem units_inv_left_iff
  statement: Commute (↑u⁻¹) a ↔ Commute (↑u) a
  proof: SemiconjBy.units_inv_symm_left_iff

@[to_additive]

中文:
定理 units_inv_left_iff
  结论: Commute (↑u⁻¹) a ↔ Commute (↑u) a
  证明: SemiconjBy.units_inv_symm_left_iff

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_inv_symm_left_iff, units_inv_symm_left_iff
-/
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff

@[to_additive]
/--
theorem `units_val` / 定理 `units_val`

English:
theorem units_val
  statement: Commute u₁ u₂ -> Commute (u₁ : M) u₂
  proof: SemiconjBy.units_val

@[to_additive]

中文:
定理 units_val
  结论: Commute u₁ u₂ -> Commute (u₁ : M) u₂
  证明: SemiconjBy.units_val

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_val, units_val
-/
theorem units_val : Commute u₁ u₂ -> Commute (u₁ : M) u₂ :=
  SemiconjBy.units_val

@[to_additive]
/--
theorem `units_of_val` / 定理 `units_of_val`

English:
theorem units_of_val
  statement: Commute (u₁ : M) u₂ -> Commute u₁ u₂
  proof: SemiconjBy.units_of_val

@[to_additive (attr := simp)]

中文:
定理 units_of_val
  结论: Commute (u₁ : M) u₂ -> Commute u₁ u₂
  证明: SemiconjBy.units_of_val

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_of_val, units_of_val
-/
theorem units_of_val : Commute (u₁ : M) u₂ -> Commute u₁ u₂ :=
  SemiconjBy.units_of_val

@[to_additive (attr := simp)]
/--
theorem `units_val_iff` / 定理 `units_val_iff`

English:
theorem units_val_iff
  statement: Commute (u₁ : M) u₂ ↔ Commute u₁ u₂
  proof: SemiconjBy.units_val_iff

中文:
定理 units_val_iff
  结论: Commute (u₁ : M) u₂ ↔ Commute u₁ u₂
  证明: SemiconjBy.units_val_iff

Depends on / 依赖: SemiconjBy, SemiconjBy.units_val_iff, units_val_iff
-/
theorem units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_val_iff

end Commute

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive /-- If the sum of two commuting elements is an additive unit, then the left summand is
an additive unit. -/]
/--
Definition of `Units.leftOfMul` / `Units.leftOfMul` 的定义

English:
definition Units.leftOfMul
  signature: (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b)
  body: a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm]; rw [← hc.eq]; rw [hu]; rw [u.mul_inv]

中文:
定义 单位群.leftOfMul
  签名: (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b)
  定义体: a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm]; rw [← hc.eq]; rw [hu]; rw [u.mul_inv]
-/
def Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm]; rw [← hc.eq]; rw [hu]; rw [u.mul_inv]

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive /-- If the sum of two commuting elements is an additive unit, then the right summand
is an additive unit. -/]
/--
Definition of `Units.rightOfMul` / `Units.rightOfMul` 的定义

English:
definition Units.rightOfMul
  signature: (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b)
  body: u.leftOfMul b a (hc.eq ▸ hu) hc.symm

@[to_additive]

中文:
定义 单位群.rightOfMul
  签名: (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b)
  定义体: u.leftOfMul b a (hc.eq ▸ hu) hc.symm

@[to_additive]

Depends on / 依赖: hc.eq, hc.symm, leftOfMul, u.leftOfMul
-/
def Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.eq ▸ hu) hc.symm

@[to_additive]
/--
theorem `Commute.isUnit_mul_iff` / 定理 `Commute.isUnit_mul_iff`

English:
theorem Commute.isUnit_mul_iff
  given: (h : Commute a b)
  statement: IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b
  proof: ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩

@[to_additive (attr := simp)]

中文:
定理 Commute.isUnit_mul_iff
  条件: (h : Commute a b)
  结论: 是单位 (a * b) ↔ 是单位 a ∧ 是单位 b
  证明: ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩

@[to_additive (attr := simp)]

Depends on / 依赖: hu.symm, isUnit, leftOfMul, rightOfMul, u.leftOfMul, u.rightOfMul
-/
theorem Commute.isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩

@[to_additive (attr := simp)]
/--
theorem `isUnit_mul_self_iff` / 定理 `isUnit_mul_self_iff`

English:
theorem isUnit_mul_self_iff
  statement: IsUnit (a * a) ↔ IsUnit a
  proof: (Commute.refl a).isUnit_mul_iff.trans and_self_iff

@[to_additive (attr := simp)]

中文:
定理 isUnit_mul_self_iff
  结论: 是单位 (a * a) ↔ 是单位 a
  证明: (Commute.refl a).isUnit_mul_iff.trans and_self_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Commute, Commute.refl, and_self_iff, isUnit_mul_iff, isUnit_mul_iff.trans
-/
theorem isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).isUnit_mul_iff.trans and_self_iff

@[to_additive (attr := simp)]
/--
lemma `Commute.units_zpow_right` / 引理 `Commute.units_zpow_right`

English:
lemma Commute.units_zpow_right
  given: (h : Commute a u) (m : Int)
  statement: Commute a ↑(u ^ m)
  proof: SemiconjBy.units_zpow_right h m

@[to_additive (attr := simp)]

中文:
引理 Commute.units_zpow_right
  条件: (h : Commute a u) (m : 整数)
  结论: Commute a ↑(u ^ m)
  证明: SemiconjBy.units_zpow_right h m

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.units_zpow_right, units_zpow_right
-/
lemma Commute.units_zpow_right (h : Commute a u) (m : Int) : Commute a ↑(u ^ m) :=
  SemiconjBy.units_zpow_right h m

@[to_additive (attr := simp)]
/--
lemma `Commute.units_zpow_left` / 引理 `Commute.units_zpow_left`

English:
lemma Commute.units_zpow_left
  given: (h : Commute ↑u a) (m : Int)
  statement: Commute ↑(u ^ m) a
  proof: (h.symm.units_zpow_right m).symm

中文:
引理 Commute.units_zpow_left
  条件: (h : Commute ↑u a) (m : 整数)
  结论: Commute ↑(u ^ m) a
  证明: (h.symm.units_zpow_right m).symm

Depends on / 依赖: h.symm.units_zpow_right, units_zpow_right
-/
lemma Commute.units_zpow_left (h : Commute ↑u a) (m : Int) : Commute ↑(u ^ m) a :=
  (h.symm.units_zpow_right m).symm

/-- If a natural power of `x` is a unit, then `x` is a unit. -/
@[to_additive
/-- If a natural multiple of `x` is an additive unit, then `x` is an additive unit. -/]
/--
Definition of `Units.ofPow` / `Units.ofPow` 的定义

English:
definition Units.ofPow
  signature: (u : Mˣ) (x : M) {n : Nat} (hn : n != 0) (hu : x ^ n = u)
  body: u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)

中文:
定义 单位群.ofPow
  签名: (u : Mˣ) (x : M) {n : 自然数} (hn : n != 0) (hu : x ^ n = u)
  定义体: u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)

Depends on / 依赖: Commute, Commute.self_pow, Nat.pos_of_ne_zero, Nat.sub_add_cancel, Nat.succ_le_of_lt, _root_, _root_.pow_succ, leftOfMul, pos_of_ne_zero, pow_succ, self_pow, sub_add_cancel, succ_le_of_lt, u.leftOfMul
-/
def Units.ofPow (u : Mˣ) (x : M) {n : Nat} (hn : n != 0) (hu : x ^ n = u) : Mˣ :=
  u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)

/--
lemma `isUnit_pow_iff` / 引理 `isUnit_pow_iff`

English:
lemma isUnit_pow_iff
  given: (hn : n != 0)
  statement: IsUnit (a ^ n) ↔ IsUnit a
  proof: ⟨fun ⟨u, hu⟩ => (u.ofPow a hn hu.symm).isUnit, IsUnit.pow n⟩

@[to_additive]

中文:
引理 isUnit_pow_iff
  条件: (hn : n != 0)
  结论: 是单位 (a ^ n) ↔ 是单位 a
  证明: ⟨fun ⟨u, hu⟩ => (u.ofPow a hn hu.symm).isUnit, IsUnit.pow n⟩

@[to_additive]
-/
@[to_additive (attr := simp)] lemma isUnit_pow_iff (hn : n != 0) : IsUnit (a ^ n) ↔ IsUnit a :=
  ⟨fun ⟨u, hu⟩ => (u.ofPow a hn hu.symm).isUnit, IsUnit.pow n⟩

@[to_additive]
/--
lemma `isUnit_pow_succ_iff` / 引理 `isUnit_pow_succ_iff`

English:
lemma isUnit_pow_succ_iff
  statement: IsUnit (a ^ (n + 1)) ↔ IsUnit a
  proof: isUnit_pow_iff n.succ_ne_zero

中文:
引理 isUnit_pow_succ_iff
  结论: 是单位 (a ^ (n + 1)) ↔ 是单位 a
  证明: isUnit_pow_iff n.succ_ne_zero

Depends on / 依赖: isUnit_pow_iff, n.succ_ne_zero, succ_ne_zero
-/
lemma isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit a := isUnit_pow_iff n.succ_ne_zero

/--
lemma `isUnit_pow_iff_of_not_isUnit` / 引理 `isUnit_pow_iff_of_not_isUnit`

English:
lemma isUnit_pow_iff_of_not_isUnit
  given: (hx : ¬ IsUnit a) {n : Nat}
  proof: by
  rcases n with (_ | n) <;>
  simp [hx]

中文:
引理 isUnit_pow_iff_of_not_isUnit
  条件: (hx : ¬ 是单位 a) {n : 自然数}
  证明: by
  rcases n with (_ | n) <;>
  simp [hx]
-/
lemma isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUnit a) {n : Nat} :
    IsUnit (a ^ n) ↔ n = 0 := by
  rcases n with (_ | n) <;>
  simp [hx]

/-- If `a ^ n = 1`, `n ≠ 0`, then `a` is a unit. -/
@[to_additive (attr := simps!) /-- If `n • x = 0`, `n ≠ 0`, then `x` is an additive unit. -/]
/--
Definition of `Units.ofPowEqOne` / `Units.ofPowEqOne` 的定义

English:
definition Units.ofPowEqOne
  signature: (a : M) (n : Nat) (ha : a ^ n = 1) (hn : n != 0)
  body: Units.ofPow 1 a hn ha

@[to_additive (attr := simp)]

中文:
定义 单位群.ofPowEqOne
  签名: (a : M) (n : 自然数) (ha : a ^ n = 1) (hn : n != 0)
  定义体: Units.ofPow 1 a hn ha

@[to_additive (attr := simp)]

Depends on / 依赖: Units.ofPow
-/
def Units.ofPowEqOne (a : M) (n : Nat) (ha : a ^ n = 1) (hn : n != 0) : Mˣ := Units.ofPow 1 a hn ha

@[to_additive (attr := simp)]
/--
lemma `Units.pow_ofPowEqOne` / 引理 `Units.pow_ofPowEqOne`

English:
lemma Units.pow_ofPowEqOne
  given: (ha : a ^ n = 1) (hn : n != 0)
  proof: Units.ext by simp [ha]

@[to_additive]

中文:
引理 单位群.pow_ofPowEqOne
  条件: (ha : a ^ n = 1) (hn : n != 0)
  证明: Units.ext by simp [ha]

@[to_additive]

Depends on / 依赖: Units.ext
-/
lemma Units.pow_ofPowEqOne (ha : a ^ n = 1) (hn : n != 0) :
Units.ofPowEqOne _ n ha hn ^ n = 1 := Units.ext by simp [ha]

@[to_additive]
/--
lemma `IsUnit.of_pow_eq_one` / 引理 `IsUnit.of_pow_eq_one`

English:
lemma IsUnit.of_pow_eq_one
  given: (ha : a ^ n = 1) (hn : n != 0)
  statement: IsUnit a
  proof: (Units.ofPowEqOne _ n ha hn).isUnit

@[to_additive]

中文:
引理 是单位.of_pow_eq_one
  条件: (ha : a ^ n = 1) (hn : n != 0)
  结论: 是单位 a
  证明: (Units.ofPowEqOne _ n ha hn).isUnit

@[to_additive]

Depends on / 依赖: Units.ofPowEqOne, isUnit, ofPowEqOne
-/
lemma IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n != 0) : IsUnit a :=
  (Units.ofPowEqOne _ n ha hn).isUnit

@[to_additive]
/--
lemma `_root_.Units.commute_iff_inv_mul_cancel` / 引理 `_root_.Units.commute_iff_inv_mul_cancel`

English:
lemma _root_.Units.commute_iff_inv_mul_cancel
  given: {u : Mˣ} {a : M}
  proof: by
  rw [mul_assoc]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [eq_comm]; rw [Commute]; rw [SemiconjBy]

@[to_additive]

中文:
引理 _root_.单位群.commute_iff_inv_mul_cancel
  条件: {u : Mˣ} {a : M}
  证明: by
  rw [mul_assoc]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [eq_comm]; rw [Commute]; rw [SemiconjBy]

@[to_additive]

Depends on / 依赖: Commute, SemiconjBy, Units.inv_mul_eq_iff_eq_mul, eq_comm, inv_mul_eq_iff_eq_mul, mul_assoc
-/
lemma _root_.Units.commute_iff_inv_mul_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * a * u = a := by
  rw [mul_assoc]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [eq_comm]; rw [Commute]; rw [SemiconjBy]

@[to_additive]
/--
lemma `_root_.Units.commute_iff_inv_mul_cancel_assoc` / 引理 `_root_.Units.commute_iff_inv_mul_cancel_assoc`

English:
lemma _root_.Units.commute_iff_inv_mul_cancel_assoc
  given: {u : Mˣ} {a : M}
  proof: by
  rw [u.commute_iff_inv_mul_cancel]; rw [mul_assoc]

@[to_additive]

中文:
引理 _root_.单位群.commute_iff_inv_mul_cancel_assoc
  条件: {u : Mˣ} {a : M}
  证明: by
  rw [u.commute_iff_inv_mul_cancel]; rw [mul_assoc]

@[to_additive]

Depends on / 依赖: commute_iff_inv_mul_cancel, mul_assoc, u.commute_iff_inv_mul_cancel
-/
lemma _root_.Units.commute_iff_inv_mul_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * (a * u) = a := by
  rw [u.commute_iff_inv_mul_cancel]; rw [mul_assoc]

@[to_additive]
/--
lemma `_root_.Units.commute_iff_mul_inv_cancel` / 引理 `_root_.Units.commute_iff_mul_inv_cancel`

English:
lemma _root_.Units.commute_iff_mul_inv_cancel
  given: {u : Mˣ} {a : M}
  proof: by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [Commute]; rw [SemiconjBy]

@[to_additive]

中文:
引理 _root_.单位群.commute_iff_mul_inv_cancel
  条件: {u : Mˣ} {a : M}
  证明: by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [Commute]; rw [SemiconjBy]

@[to_additive]

Depends on / 依赖: Commute, SemiconjBy, Units.mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul
-/
lemma _root_.Units.commute_iff_mul_inv_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * a * ↑u⁻¹ = a := by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [Commute]; rw [SemiconjBy]

@[to_additive]
/--
lemma `_root_.Units.commute_iff_mul_inv_cancel_assoc` / 引理 `_root_.Units.commute_iff_mul_inv_cancel_assoc`

English:
lemma _root_.Units.commute_iff_mul_inv_cancel_assoc
  given: {u : Mˣ} {a : M}
  proof: by
  rw [u.commute_iff_mul_inv_cancel]; rw [mul_assoc]

中文:
引理 _root_.单位群.commute_iff_mul_inv_cancel_assoc
  条件: {u : Mˣ} {a : M}
  证明: by
  rw [u.commute_iff_mul_inv_cancel]; rw [mul_assoc]

Depends on / 依赖: commute_iff_mul_inv_cancel, mul_assoc, u.commute_iff_mul_inv_cancel
-/
lemma _root_.Units.commute_iff_mul_inv_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * (a * ↑u⁻¹) = a := by
  rw [u.commute_iff_mul_inv_cancel]; rw [mul_assoc]

end Monoid

namespace Commute

variable [DivisionMonoid M] {a b c d : M}

@[to_additive]
/--
lemma `div_eq_div_iff_of_isUnit` / 引理 `div_eq_div_iff_of_isUnit`

English:
lemma div_eq_div_iff_of_isUnit
  given: (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [hbd.right_comm]; rw [hd.div_mul_cancel]

@[to_additive]

中文:
引理 div_eq_div_iff_of_isUnit
  条件: (hbd : Commute b d) (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [hbd.right_comm]; rw [hd.div_mul_cancel]

@[to_additive]

Depends on / 依赖: div_mul_cancel, hb.div_mul_cancel, hb.mul, hbd.right_comm, hd.div_mul_cancel, mul_assoc, mul_left_inj, right_comm
-/
lemma div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj]; rw [← mul_assoc]; rw [hb.div_mul_cancel]; rw [← mul_assoc]; rw [hbd.right_comm]; rw [hd.div_mul_cancel]

@[to_additive]
/--
lemma `mul_inv_eq_mul_inv_iff_of_isUnit` / 引理 `mul_inv_eq_mul_inv_iff_of_isUnit`

English:
lemma mul_inv_eq_mul_inv_iff_of_isUnit
  given: (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hbd.div_eq_div_iff_of_isUnit hb hd]

@[to_additive]

中文:
引理 mul_inv_eq_mul_inv_iff_of_isUnit
  条件: (hbd : Commute b d) (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hbd.div_eq_div_iff_of_isUnit hb hd]

@[to_additive]

Depends on / 依赖: div_eq_div_iff_of_isUnit, div_eq_mul_inv, hbd.div_eq_div_iff_of_isUnit
-/
lemma mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [hbd.div_eq_div_iff_of_isUnit hb hd]

@[to_additive]
/--
lemma `inv_mul_eq_inv_mul_iff_of_isUnit` / 引理 `inv_mul_eq_inv_mul_iff_of_isUnit`

English:
lemma inv_mul_eq_inv_mul_iff_of_isUnit
  given: (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d)
  proof: by
  rw [← (hd.mul hb).mul_right_inj]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hb.mul_inv_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hbd.symm.left_comm]; rw [hd.mul_inv_cancel]; rw [mul_one]

中文:
引理 inv_mul_eq_inv_mul_iff_of_isUnit
  条件: (hbd : Commute b d) (hb : 是单位 b) (hd : 是单位 d)
  证明: by
  rw [← (hd.mul hb).mul_right_inj]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hb.mul_inv_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hbd.symm.left_comm]; rw [hd.mul_inv_cancel]; rw [mul_one]

Depends on / 依赖: hb.mul_inv_cancel, hbd.symm.left_comm, hd.mul, hd.mul_inv_cancel, left_comm, mul_assoc, mul_inv_cancel, mul_one, mul_right_inj
-/
lemma inv_mul_eq_inv_mul_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c := by
  rw [← (hd.mul hb).mul_right_inj]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hb.mul_inv_cancel]; rw [mul_one]; rw [← mul_assoc]; rw [mul_assoc d]; rw [hbd.symm.left_comm]; rw [hd.mul_inv_cancel]; rw [mul_one]

end Commute
