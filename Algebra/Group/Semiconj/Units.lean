/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
-- Some proofs and docs came from mathlib3 `src/algebra/commute.lean` (c) Neil Strickland
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open scoped Int

variable {M : Type*}

namespace SemiconjBy

section Monoid

variable [Monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive /-- If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it
semiconjugates `-x` to `-y`. -/]
/--
theorem `units_inv_right` / 定理 `units_inv_right`

English:
theorem units_inv_right
  given: {a : M} {x y : Mˣ} (h : SemiconjBy a x y)
  statement: SemiconjBy a ↑x⁻¹ ↑y⁻¹
  proof: calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]

@[to_additive (attr := simp)]

中文:
定理 units_inv_right
  条件: {a : M} {x y : Mˣ} (h : SemiconjBy a x y)
  结论: SemiconjBy a ↑x⁻¹ ↑y⁻¹
  证明: calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]

@[to_additive (attr := simp)]

Depends on / 依赖: Units.inv_mul_cancel_left, Units.mul_inv_cancel_right, h.eq, inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right
-/
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]

@[to_additive (attr := simp)]
/--
theorem `units_inv_right_iff` / 定理 `units_inv_right_iff`

English:
theorem units_inv_right_iff
  given: {a : M} {x y : Mˣ}
  statement: SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y
  proof: ⟨units_inv_right, units_inv_right⟩

中文:
定理 units_inv_right_iff
  条件: {a : M} {x y : Mˣ}
  结论: SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y
  证明: ⟨units_inv_right, units_inv_right⟩

Depends on / 依赖: units_inv_right
-/
theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y :=
  ⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive /-- If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to
`x`. -/]
/--
theorem `units_inv_symm_left` / 定理 `units_inv_symm_left`

English:
theorem units_inv_symm_left
  given: {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y)
  statement: SemiconjBy (↑a⁻¹) y x
  proof: calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]

@[to_additive (attr := simp)]

中文:
定理 units_inv_symm_left
  条件: {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y)
  结论: SemiconjBy (↑a⁻¹) y x
  证明: calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: Units.inv_mul_cancel_left, Units.mul_inv_cancel_right, h.eq, inv_mul_cancel_left, mul_assoc, mul_inv_cancel_right
-/
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `units_inv_symm_left_iff` / 定理 `units_inv_symm_left_iff`

English:
theorem units_inv_symm_left_iff
  given: {a : Mˣ} {x y : M}
  statement: SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y
  proof: ⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive]

中文:
定理 units_inv_symm_left_iff
  条件: {a : Mˣ} {x y : M}
  结论: SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y
  证明: ⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive]

Depends on / 依赖: units_inv_symm_left
-/
theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y :=
  ⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive]
/--
theorem `units_val` / 定理 `units_val`

English:
theorem units_val
  given: {a x y : Mˣ} (h : SemiconjBy a x y)
  statement: SemiconjBy (a : M) x y
  proof: congr_arg Units.val h

@[to_additive]

中文:
定理 units_val
  条件: {a x y : Mˣ} (h : SemiconjBy a x y)
  结论: SemiconjBy (a : M) x y
  证明: congr_arg Units.val h

@[to_additive]

Depends on / 依赖: Units.val, congr_arg
-/
theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  congr_arg Units.val h

@[to_additive]
/--
theorem `units_of_val` / 定理 `units_of_val`

English:
theorem units_of_val
  given: {a x y : Mˣ} (h : SemiconjBy (a : M) x y)
  statement: SemiconjBy a x y
  proof: Units.ext h

@[to_additive (attr := simp)]

中文:
定理 units_of_val
  条件: {a x y : Mˣ} (h : SemiconjBy (a : M) x y)
  结论: SemiconjBy a x y
  证明: Units.ext h

@[to_additive (attr := simp)]

Depends on / 依赖: Units.ext
-/
theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  Units.ext h

@[to_additive (attr := simp)]
/--
theorem `units_val_iff` / 定理 `units_val_iff`

English:
theorem units_val_iff
  given: {a x y : Mˣ}
  statement: SemiconjBy (a : M) x y ↔ SemiconjBy a x y
  proof: ⟨units_of_val, units_val⟩

@[to_additive (attr := simp)]

中文:
定理 units_val_iff
  条件: {a x y : Mˣ}
  结论: SemiconjBy (a : M) x y ↔ SemiconjBy a x y
  证明: ⟨units_of_val, units_val⟩

@[to_additive (attr := simp)]

Depends on / 依赖: units_of_val, units_val
-/
theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_val, units_val⟩

@[to_additive (attr := simp)]
/--
lemma `units_zpow_right` / 引理 `units_zpow_right`

English:
lemma units_zpow_right
  given: {a : M} {x y : Mˣ} (h : SemiconjBy a x y)

中文:
引理 units_zpow_right
  条件: {a : M} {x y : Mˣ} (h : SemiconjBy a x y)
-/
lemma units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) :
    forall m : Int, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : Nat) => by simp only [zpow_natCast, Units.val_pow_eq_pow_val, h, pow_right]
  | -[n+1] => by simp only [zpow_negSucc, Units.val_pow_eq_pow_val, units_inv_right, h, pow_right]

end Monoid
end SemiconjBy

namespace Units
variable [Monoid M]

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive /-- `a` semiconjugates `x` to `a + x + -a`. -/]
/--
lemma `mk_semiconjBy` / 引理 `mk_semiconjBy`

English:
lemma mk_semiconjBy
  given: (u : Mˣ) (x : M)
  statement: SemiconjBy (↑u) x (u * x * ↑u⁻¹)
  proof: by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]

中文:
引理 mk_semiconjBy
  条件: (u : Mˣ) (x : M)
  结论: SemiconjBy (↑u) x (u * x * ↑u⁻¹)
  证明: by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]

Depends on / 依赖: SemiconjBy, Units.inv_mul_cancel_right, inv_mul_cancel_right
-/
lemma mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]

/--
lemma `conj_pow` / 引理 `conj_pow`

English:
lemma conj_pow
  given: (u : Mˣ) (x : M) (n : Nat)
  proof: eq_divp_iff_mul_eq.2 ((u.mk_semiconjBy x).pow_right n).eq.symm

中文:
引理 conj_pow
  条件: (u : Mˣ) (x : M) (n : 自然数)
  证明: eq_divp_iff_mul_eq.2 ((u.mk_semiconjBy x).pow_right n).eq.symm

Depends on / 依赖: eq.symm, eq_divp_iff_mul_eq, mk_semiconjBy, pow_right, u.mk_semiconjBy
-/
lemma conj_pow (u : Mˣ) (x : M) (n : Nat) :
    ((↑u : M) * x * (↑u⁻¹ : M)) ^ n = (u : M) * x ^ n * (↑u⁻¹ : M) :=
  eq_divp_iff_mul_eq.2 ((u.mk_semiconjBy x).pow_right n).eq.symm

/--
lemma `conj_pow'` / 引理 `conj_pow'`

English:
lemma conj_pow'
  given: (u : Mˣ) (x : M) (n : Nat)
  proof: u⁻¹.conj_pow x n

中文:
引理 conj_pow'
  条件: (u : Mˣ) (x : M) (n : 自然数)
  证明: u⁻¹.conj_pow x n

Depends on / 依赖: conj_pow
-/
lemma conj_pow' (u : Mˣ) (x : M) (n : Nat) :
    ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M) := u⁻¹.conj_pow x n

end Units
