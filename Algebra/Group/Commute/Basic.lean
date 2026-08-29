/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Semiconj.Basic

/-!
# Additional lemmas about commuting pairs of elements in monoids

-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {G : Type*}

section Semigroup
variable [Semigroup G] {a b c : G}

open Function

@[to_additive]
/--
lemma `SemiconjBy.function_semiconj_mul_left` / 引理 `SemiconjBy.function_semiconj_mul_left`

English:
lemma SemiconjBy.function_semiconj_mul_left
  given: (h : SemiconjBy a b c)
  proof: fun j => by simp only [← mul_assoc, h.eq]

@[to_additive]

中文:
引理 SemiconjBy.function_semiconj_mul_left
  条件: (h : SemiconjBy a b c)
  证明: fun j => by simp only [← mul_assoc, h.eq]

@[to_additive]

Depends on / 依赖: h.eq, mul_assoc
-/
lemma SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Semiconj (a * ·) (b * ·) (c * ·) := fun j => by simp only [← mul_assoc, h.eq]

@[to_additive]
/--
lemma `Commute.function_commute_mul_left` / 引理 `Commute.function_commute_mul_left`

English:
lemma Commute.function_commute_mul_left
  given: (h : Commute a b)
  statement: Function.Commute (a * ·) (b * ·)
  proof: SemiconjBy.function_semiconj_mul_left h

@[to_additive]

中文:
引理 Commute.function_commute_mul_left
  条件: (h : Commute a b)
  结论: Function.Commute (a * ·) (b * ·)
  证明: SemiconjBy.function_semiconj_mul_left h

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.function_semiconj_mul_left, function_semiconj_mul_left
-/
lemma Commute.function_commute_mul_left (h : Commute a b) : Function.Commute (a * ·) (b * ·) :=
  SemiconjBy.function_semiconj_mul_left h

@[to_additive]
/--
lemma `SemiconjBy.function_semiconj_mul_right_swap` / 引理 `SemiconjBy.function_semiconj_mul_right_swap`

English:
lemma SemiconjBy.function_semiconj_mul_right_swap
  given: (h : SemiconjBy a b c)
  proof: fun j => by simp only [mul_assoc, ← h.eq]

@[to_additive]

中文:
引理 SemiconjBy.function_semiconj_mul_right_swap
  条件: (h : SemiconjBy a b c)
  证明: fun j => by simp only [mul_assoc, ← h.eq]

@[to_additive]

Depends on / 依赖: h.eq, mul_assoc
-/
lemma SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j => by simp only [mul_assoc, ← h.eq]

@[to_additive]
/--
lemma `Commute.function_commute_mul_right` / 引理 `Commute.function_commute_mul_right`

English:
lemma Commute.function_commute_mul_right
  given: (h : Commute a b)
  statement: Function.Commute (· * a) (· * b)
  proof: SemiconjBy.function_semiconj_mul_right_swap h

中文:
引理 Commute.function_commute_mul_right
  条件: (h : Commute a b)
  结论: Function.Commute (· * a) (· * b)
  证明: SemiconjBy.function_semiconj_mul_right_swap h

Depends on / 依赖: SemiconjBy, SemiconjBy.function_semiconj_mul_right_swap, function_semiconj_mul_right_swap
-/
lemma Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (· * a) (· * b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroup

namespace Commute

section DivisionMonoid

variable [DivisionMonoid G] {a b c d : G}

@[to_additive]
/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  statement: Commute a b -> Commute a⁻¹ b⁻¹
  proof: SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]

中文:
定理 inv_inv
  结论: Commute a b -> Commute a⁻¹ b⁻¹
  证明: SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]
-/
protected theorem inv_inv : Commute a b -> Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]
/--
theorem `inv_inv_iff` / 定理 `inv_inv_iff`

English:
theorem inv_inv_iff
  statement: Commute a⁻¹ b⁻¹ ↔ Commute a b
  proof: SemiconjBy.inv_inv_symm_iff

@[to_additive]

中文:
定理 inv_inv_iff
  结论: Commute a⁻¹ b⁻¹ ↔ Commute a b
  证明: SemiconjBy.inv_inv_symm_iff

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_inv_symm_iff, inv_inv_symm_iff
-/
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

@[to_additive]
/--
theorem `div_mul_div_comm` / 定理 `div_mul_div_comm`

English:
theorem div_mul_div_comm
  given: (hbd : Commute b d) (hbc : Commute b⁻¹ c)
  proof: by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]

中文:
定理 div_mul_div_comm
  条件: (hbd : Commute b d) (hbc : Commute b⁻¹ c)
  证明: by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]
-/
protected theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]
/--
theorem `mul_div_mul_comm` / 定理 `mul_div_mul_comm`

English:
theorem mul_div_mul_comm
  given: (hcd : Commute c d) (hbc : Commute b c⁻¹)
  proof: (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]

中文:
定理 mul_div_mul_comm
  条件: (hcd : Commute c d) (hbc : Commute b c⁻¹)
  证明: (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]
-/
protected theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) :=
  (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]
/--
theorem `div_div_div_comm` / 定理 `div_div_div_comm`

English:
theorem div_div_div_comm
  given: (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d)
  proof: by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]

中文:
定理 div_div_div_comm
  条件: (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d)
  证明: by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]
-/
protected theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]

end DivisionMonoid

section Group
variable [Group G] {a b : G}

@[to_additive (attr := simp)]
/--
lemma `inv_left_iff` / 引理 `inv_left_iff`

English:
lemma inv_left_iff
  statement: Commute a⁻¹ b ↔ Commute a b
  proof: SemiconjBy.inv_symm_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff

@[to_additive (attr := simp)]

中文:
引理 inv_left_iff
  结论: Commute a⁻¹ b ↔ Commute a b
  证明: SemiconjBy.inv_symm_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_symm_left_iff, inv_symm_left_iff
-/
lemma inv_left_iff : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff

@[to_additive (attr := simp)]
/--
lemma `inv_right_iff` / 引理 `inv_right_iff`

English:
lemma inv_right_iff
  statement: Commute a b⁻¹ ↔ Commute a b
  proof: SemiconjBy.inv_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive]

中文:
引理 inv_right_iff
  结论: Commute a b⁻¹ ↔ Commute a b
  证明: SemiconjBy.inv_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.inv_right_iff, inv_right_iff
-/
lemma inv_right_iff : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive]
/--
lemma `inv_mul_cancel` / 引理 `inv_mul_cancel`

English:
lemma inv_mul_cancel
  given: (h : Commute a b)
  statement: a⁻¹ * b * a = b
  proof: by
  rw [h.inv_left.eq]; rw [inv_mul_cancel_right]

@[to_additive]

中文:
引理 inv_mul_cancel
  条件: (h : Commute a b)
  结论: a⁻¹ * b * a = b
  证明: by
  rw [h.inv_left.eq]; rw [inv_mul_cancel_right]

@[to_additive]
-/
protected lemma inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq]; rw [inv_mul_cancel_right]

@[to_additive]
/--
lemma `inv_mul_cancel_assoc` / 引理 `inv_mul_cancel_assoc`

English:
lemma inv_mul_cancel_assoc
  given: (h : Commute a b)
  statement: a⁻¹ * (b * a) = b
  proof: by
  rw [← mul_assoc]; rw [h.inv_mul_cancel]

@[to_additive (attr := simp)]

中文:
引理 inv_mul_cancel_assoc
  条件: (h : Commute a b)
  结论: a⁻¹ * (b * a) = b
  证明: by
  rw [← mul_assoc]; rw [h.inv_mul_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: h.inv_mul_cancel, inv_mul_cancel, mul_assoc
-/
lemma inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc]; rw [h.inv_mul_cancel]

@[to_additive (attr := simp)]
/--
theorem `conj_iff` / 定理 `conj_iff`

English:
theorem conj_iff
  given: (h : G)
  statement: Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b
  proof: SemiconjBy.conj_iff

@[to_additive]

中文:
定理 conj_iff
  条件: (h : G)
  结论: Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b
  证明: SemiconjBy.conj_iff

@[to_additive]
-/
protected theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b :=
  SemiconjBy.conj_iff

@[to_additive]
/--
theorem `conj` / 定理 `conj`

English:
theorem conj
  given: (comm : Commute a b) (h : G)
  statement: Commute (h * a * h⁻¹) (h * b * h⁻¹)
  proof: (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]

中文:
定理 conj
  条件: (comm : Commute a b) (h : G)
  结论: Commute (h * a * h⁻¹) (h * b * h⁻¹)
  证明: (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]
-/
protected theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) :=
  (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]
/--
lemma `zpow_right` / 引理 `zpow_right`

English:
lemma zpow_right
  given: (h : Commute a b) (m : Int)
  statement: Commute a (b ^ m)
  proof: SemiconjBy.zpow_right h m

@[to_additive (attr := simp)]

中文:
引理 zpow_right
  条件: (h : Commute a b) (m : 整数)
  结论: Commute a (b ^ m)
  证明: SemiconjBy.zpow_right h m

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.zpow_right, zpow_right
-/
lemma zpow_right (h : Commute a b) (m : Int) : Commute a (b ^ m) := SemiconjBy.zpow_right h m

@[to_additive (attr := simp)]
/--
lemma `zpow_left` / 引理 `zpow_left`

English:
lemma zpow_left
  given: (h : Commute a b) (m : Int)
  statement: Commute (a ^ m) b
  proof: (h.symm.zpow_right m).symm

中文:
引理 zpow_left
  条件: (h : Commute a b) (m : 整数)
  结论: Commute (a ^ m) b
  证明: (h.symm.zpow_right m).symm

Depends on / 依赖: h.symm.zpow_right, zpow_right
-/
lemma zpow_left (h : Commute a b) (m : Int) : Commute (a ^ m) b := (h.symm.zpow_right m).symm

/--
lemma `zpow_zpow` / 引理 `zpow_zpow`

English:
lemma zpow_zpow
  given: (h : Commute a b) (m n : Int)
  statement: Commute (a ^ m) (b ^ n)
  proof: (h.zpow_left m).zpow_right n

中文:
引理 zpow_zpow
  条件: (h : Commute a b) (m n : 整数)
  结论: Commute (a ^ m) (b ^ n)
  证明: (h.zpow_left m).zpow_right n
-/
@[to_additive] lemma zpow_zpow (h : Commute a b) (m n : Int) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n

variable (a) (m n : Int)

/--
lemma `self_zpow` / 引理 `self_zpow`

English:
lemma self_zpow
  statement: Commute a (a ^ n)
  proof: (Commute.refl a).zpow_right n

中文:
引理 self_zpow
  结论: Commute a (a ^ n)
  证明: (Commute.refl a).zpow_right n
-/
@[to_additive] lemma self_zpow : Commute a (a ^ n) := (Commute.refl a).zpow_right n

/--
lemma `zpow_self` / 引理 `zpow_self`

English:
lemma zpow_self
  statement: Commute (a ^ n) a
  proof: (Commute.refl a).zpow_left n

中文:
引理 zpow_self
  结论: Commute (a ^ n) a
  证明: (Commute.refl a).zpow_left n
-/
@[to_additive] lemma zpow_self : Commute (a ^ n) a := (Commute.refl a).zpow_left n

/--
lemma `zpow_zpow_self` / 引理 `zpow_zpow_self`

English:
lemma zpow_zpow_self
  statement: Commute (a ^ m) (a ^ n)
  proof: (Commute.refl a).zpow_zpow m n

中文:
引理 zpow_zpow_self
  结论: Commute (a ^ m) (a ^ n)
  证明: (Commute.refl a).zpow_zpow m n
-/
@[to_additive] lemma zpow_zpow_self : Commute (a ^ m) (a ^ n) := (Commute.refl a).zpow_zpow m n

end Group
end Commute

section Group
variable [Group G]

/--
lemma `pow_inv_comm` / 引理 `pow_inv_comm`

English:
lemma pow_inv_comm
  given: (a : G) (m n : Nat)
  statement: a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m
  proof: (Commute.refl a).inv_left.pow_pow _ _

中文:
引理 pow_inv_comm
  条件: (a : G) (m n : 自然数)
  结论: a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m
  证明: (Commute.refl a).inv_left.pow_pow _ _
-/
@[to_additive] lemma pow_inv_comm (a : G) (m n : Nat) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _

end Group
