/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

open scoped Ring

variable {M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Ring

/--
theorem `mul_inverse_rev'` / 定理 `mul_inverse_rev'`

English:
theorem mul_inverse_rev'
  given: {a b : M₀} (h : Commute a b)
  proof: by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul]; rw [inverse_unit]; rw [inverse_unit]; rw [inverse_unit]; rw [← Units.val_mul]; rw [mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]

中文:
定理 mul_inverse_rev'
  条件: {a b : M₀} (h : Commute a b)
  证明: by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul]; rw [inverse_unit]; rw [inverse_unit]; rw [inverse_unit]; rw [← Units.val_mul]; rw [mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]

Depends on / 依赖: IsUnit, Units.val_mul, h.isUnit_mul_iff.mp, h.isUnit_mul_iff.mpr, inverse_non_unit, inverse_unit, isUnit_mul_iff, mul_inv_rev, mul_zero, not_and_or, not_and_or.mp, val_mul, zero_mul
-/
theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) :
    inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul]; rw [inverse_unit]; rw [inverse_unit]; rw [inverse_unit]; rw [← Units.val_mul]; rw [mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]

/--
theorem `mul_inverse_rev` / 定理 `mul_inverse_rev`

English:
theorem mul_inverse_rev
  given: {M₀} [CommMonoidWithZero M₀] (a b : M₀)
  proof: mul_inverse_rev' (Commute.all _ _)

中文:
定理 mul_inverse_rev
  条件: {M₀} [带零交换幺半群 M₀] (a b : M₀)
  证明: mul_inverse_rev' (Commute.all _ _)

Depends on / 依赖: Commute, Commute.all, mul_inverse_rev
-/
theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ :=
  mul_inverse_rev' (Commute.all _ _)

/--
lemma `inverse_pow` / 引理 `inverse_pow`

English:
lemma inverse_pow
  given: (r : M₀)
  statement: forall n : Nat, r⁻¹ʳ ^ n = (r ^ n)⁻¹ʳ

中文:
引理 inverse_pow
  条件: (r : M₀)
  结论: 对任意 n : 自然数, r⁻¹ʳ ^ n = (r ^ n)⁻¹ʳ
-/
lemma inverse_pow (r : M₀) : forall n : Nat, r⁻¹ʳ ^ n = (r ^ n)⁻¹ʳ
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ']; rw [pow_succ]; rw [Ring.mul_inverse_rev' ((Commute.refl r).pow_left n)]; rw [Ring.inverse_pow r n]

/--
lemma `inverse_pow_mul_eq_iff_eq_mul` / 引理 `inverse_pow_mul_eq_iff_eq_mul`

English:
lemma inverse_pow_mul_eq_iff_eq_mul
  given: {a : M₀} (b c : M₀) (ha : IsUnit a) {k : Nat}
  proof: by
  rw [Ring.inverse_pow]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

中文:
引理 inverse_pow_mul_eq_iff_eq_mul
  条件: {a : M₀} (b c : M₀) (ha : 是单位 a) {k : 自然数}
  证明: by
  rw [Ring.inverse_pow]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

Depends on / 依赖: IsUnit, IsUnit.pow, Ring.inverse_mul_eq_iff_eq_mul, Ring.inverse_pow, inverse_mul_eq_iff_eq_mul, inverse_pow
-/
lemma inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : Nat} :
    a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

end Ring

@[grind ←]
/--
theorem `Commute.ringInverse_ringInverse` / 定理 `Commute.ringInverse_ringInverse`

English:
theorem Commute.ringInverse_ringInverse
  given: {a b : M₀} (h : Commute a b)
  proof: (Ring.mul_inverse_rev' h.symm).symm.trans (congr_arg _ h.symm.eq).trans
    Ring.mul_inverse_rev' h

中文:
定理 Commute.ringInverse_ringInverse
  条件: {a b : M₀} (h : Commute a b)
  证明: (Ring.mul_inverse_rev' h.symm).symm.trans (congr_arg _ h.symm.eq).trans
    Ring.mul_inverse_rev' h

Depends on / 依赖: Ring.mul_inverse_rev, congr_arg, h.symm, h.symm.eq, mul_inverse_rev, symm.trans
-/
theorem Commute.ringInverse_ringInverse {a b : M₀} (h : Commute a b) :
    Commute a⁻¹ʳ b⁻¹ʳ :=
(Ring.mul_inverse_rev' h.symm).symm.trans (congr_arg _ h.symm.eq).trans
    Ring.mul_inverse_rev' h

namespace Commute

@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: [MulZeroClass G₀] (a : G₀)
  statement: Commute a 0
  proof: SemiconjBy.zero_right a

@[simp]

中文:
定理 zero_right
  条件: [乘零类 G₀] (a : G₀)
  结论: Commute a 0
  证明: SemiconjBy.zero_right a

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.zero_right, zero_right
-/
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: [MulZeroClass G₀] (a : G₀)
  statement: Commute 0 a
  proof: SemiconjBy.zero_left a a

中文:
定理 zero_left
  条件: [乘零类 G₀] (a : G₀)
  结论: Commute 0 a
  证明: SemiconjBy.zero_left a a

Depends on / 依赖: SemiconjBy, SemiconjBy.zero_left, zero_left
-/
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
/--
theorem `inv_left_iff₀` / 定理 `inv_left_iff₀`

English:
theorem inv_left_iff₀
  statement: Commute a⁻¹ b ↔ Commute a b
  proof: SemiconjBy.inv_symm_left_iff₀

中文:
定理 inv_left_iff₀
  结论: Commute a⁻¹ b ↔ Commute a b
  证明: SemiconjBy.inv_symm_left_iff₀

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_symm_left_iff
-/
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀

/--
theorem `inv_left₀` / 定理 `inv_left₀`

English:
theorem inv_left₀
  given: (h : Commute a b)
  statement: Commute a⁻¹ b
  proof: inv_left_iff₀.2 h

@[simp]

中文:
定理 inv_left₀
  条件: (h : Commute a b)
  结论: Commute a⁻¹ b
  证明: inv_left_iff₀.2 h

@[simp]
-/
theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

@[simp]
/--
theorem `inv_right_iff₀` / 定理 `inv_right_iff₀`

English:
theorem inv_right_iff₀
  statement: Commute a b⁻¹ ↔ Commute a b
  proof: SemiconjBy.inv_right_iff₀

中文:
定理 inv_right_iff₀
  结论: Commute a b⁻¹ ↔ Commute a b
  证明: SemiconjBy.inv_right_iff₀

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_right_iff
-/
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀

/--
theorem `inv_right₀` / 定理 `inv_right₀`

English:
theorem inv_right₀
  given: (h : Commute a b)
  statement: Commute a b⁻¹
  proof: inv_right_iff₀.2 h

@[simp]

中文:
定理 inv_right₀
  条件: (h : Commute a b)
  结论: Commute a b⁻¹
  证明: inv_right_iff₀.2 h

@[simp]
-/
theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

@[simp]
/--
theorem `div_right` / 定理 `div_right`

English:
theorem div_right
  given: (hab : Commute a b) (hac : Commute a c)
  statement: Commute a (b / c)
  proof: SemiconjBy.div_right hab hac

@[simp]

中文:
定理 div_right
  条件: (hab : Commute a b) (hac : Commute a c)
  结论: Commute a (b / c)
  证明: SemiconjBy.div_right hab hac

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.div_right, div_right
-/
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  SemiconjBy.div_right hab hac

@[simp]
/--
theorem `div_left` / 定理 `div_left`

English:
theorem div_left
  given: (hac : Commute a c) (hbc : Commute b c)
  statement: Commute (a / b) c
  proof: by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

中文:
定理 div_left
  条件: (hac : Commute a c) (hbc : Commute b c)
  结论: Commute (a / b) c
  证明: by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

Depends on / 依赖: div_eq_mul_inv, hac.mul_left, hbc.inv_left, mul_left
-/
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

end Commute

section GroupWithZero
variable [GroupWithZero G₀]

/--
theorem `pow_inv_comm₀` / 定理 `pow_inv_comm₀`

English:
theorem pow_inv_comm₀
  given: (a : G₀) (m n : Nat)
  statement: a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m
  proof: (Commute.refl a).inv_left₀.pow_pow m n

中文:
定理 pow_inv_comm₀
  条件: (a : G₀) (m n : 自然数)
  结论: a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m
  证明: (Commute.refl a).inv_left₀.pow_pow m n

Depends on / 依赖: Commute, Commute.refl, pow_pow
-/
theorem pow_inv_comm₀ (a : G₀) (m n : Nat) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

end GroupWithZero
