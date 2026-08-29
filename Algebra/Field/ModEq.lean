/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.MinImports

/-!
# Congruence modulo multiples of an element in a (semi)field

In this file we prove a few theorems about the congruence relation `_ ≡ _ [PMOD _]`
in a division semiring or a semifield.
-/

public section

namespace AddCommGroup

section DivisionSemiring
variable {K : Type*} [DivisionSemiring K] {a b c p : K}

/--
lemma `div_modEq_div` / 引理 `div_modEq_div`

English:
lemma div_modEq_div
  given: (hc : c != 0)
  statement: a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)]
  proof: by
  simp [modEq_iff_nsmul, add_div' _ _ _ hc, div_left_inj' hc, mul_assoc]

中文:
引理 div_modEq_div
  条件: (hc : c != 0)
  结论: a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)]
  证明: by
  simp [modEq_iff_nsmul, add_div' _ _ _ hc, div_left_inj' hc, mul_assoc]
-/
@[simp] lemma div_modEq_div (hc : c != 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [modEq_iff_nsmul, add_div' _ _ _ hc, div_left_inj' hc, mul_assoc]

/--
lemma `mul_modEq_mul_right` / 引理 `mul_modEq_mul_right`

English:
lemma mul_modEq_mul_right
  given: (hc : c != 0)
  statement: a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)]
  proof: by
  rw [div_eq_mul_inv]; rw [← div_modEq_div (inv_ne_zero hc)]; rw [div_inv_eq_mul]; rw [div_inv_eq_mul]

中文:
引理 mul_modEq_mul_right
  条件: (hc : c != 0)
  结论: a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)]
  证明: by
  rw [div_eq_mul_inv]; rw [← div_modEq_div (inv_ne_zero hc)]; rw [div_inv_eq_mul]; rw [div_inv_eq_mul]
-/
@[simp] lemma mul_modEq_mul_right (hc : c != 0) : a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv]; rw [← div_modEq_div (inv_ne_zero hc)]; rw [div_inv_eq_mul]; rw [div_inv_eq_mul]

end DivisionSemiring

section Semifield
variable {K : Type*} [Semifield K] {a b c p : K}

/--
lemma `mul_modEq_mul_left` / 引理 `mul_modEq_mul_left`

English:
lemma mul_modEq_mul_left
  given: (hc : c != 0)
  statement: c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)]
  proof: by
  simp [mul_comm c, hc]

中文:
引理 mul_modEq_mul_left
  条件: (hc : c != 0)
  结论: c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)]
  证明: by
  simp [mul_comm c, hc]
-/
@[simp] lemma mul_modEq_mul_left (hc : c != 0) : c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simp [mul_comm c, hc]

end Semifield
end AddCommGroup
