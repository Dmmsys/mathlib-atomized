/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.Algebra.Group.Basic

/-!
# Lemmas about semiconjugate elements of a group

-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace SemiconjBy
variable {G : Type*}

section DivisionMonoid
variable [DivisionMonoid G] {a x y : G}

@[to_additive (attr := simp)]
/--
theorem `inv_inv_symm_iff` / 定理 `inv_inv_symm_iff`

English:
theorem inv_inv_symm_iff
  statement: SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x
  proof: by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff

中文:
定理 inv_inv_symm_iff
  结论: SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x
  证明: by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff

Depends on / 依赖: SemiconjBy, eq_comm, inv_inj, mul_inv_rev, simp_rw
-/
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x := by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff

end DivisionMonoid

section Group
variable [Group G] {a x y : G}

/--
lemma `inv_symm_left_iff` / 引理 `inv_symm_left_iff`

English:
lemma inv_symm_left_iff
  statement: SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
  proof: by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff

中文:
引理 inv_symm_left_iff
  结论: SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
  证明: by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff
-/
@[to_additive (attr := simp)] lemma inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y := by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff

/--
lemma `inv_right_iff` / 引理 `inv_right_iff`

English:
lemma inv_right_iff
  statement: SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
  proof: by
  rw [← inv_symm_left_iff]; rw [inv_inv_symm_iff]

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

中文:
引理 inv_right_iff
  结论: SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
  证明: by
  rw [← inv_symm_left_iff]; rw [inv_inv_symm_iff]

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff
-/
@[to_additive (attr := simp)] lemma inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := by
  rw [← inv_symm_left_iff]; rw [inv_inv_symm_iff]

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

/--
lemma `zpow_right` / 引理 `zpow_right`

English:
lemma zpow_right
  given: (h : SemiconjBy a x y)

中文:
引理 zpow_right
  条件: (h : SemiconjBy a x y)
-/
@[to_additive (attr := simp)] lemma zpow_right (h : SemiconjBy a x y) :
    forall m : Int, SemiconjBy a (x ^ m) (y ^ m)
  | (n : Nat) => by simp [zpow_natCast, h.pow_right n]
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    apply pow_right h

variable (a) in
/--
lemma `eq_one_iff` / 引理 `eq_one_iff`

English:
lemma eq_one_iff
  given: (h : SemiconjBy a x y)
  statement: x = 1 ↔ y = 1
  proof: by
  rw [← conj_eq_one_iff (a := a) (b := x)]; rw [h.eq]; rw [mul_inv_cancel_right]

中文:
引理 eq_one_iff
  条件: (h : SemiconjBy a x y)
  结论: x = 1 ↔ y = 1
  证明: by
  rw [← conj_eq_one_iff (a := a) (b := x)]; rw [h.eq]; rw [mul_inv_cancel_right]
-/
@[to_additive] lemma eq_one_iff (h : SemiconjBy a x y) : x = 1 ↔ y = 1 := by
  rw [← conj_eq_one_iff (a := a) (b := x)]; rw [h.eq]; rw [mul_inv_cancel_right]

end Group
end SemiconjBy
