/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Conjugacy in a group with zero
-/

public section

assert_not_exists Multiset Ring
-- TODO
-- assert_not_exists DenselyOrdered

namespace GroupWithZero

variable {α : Type*} [GroupWithZero α] {a b : α}

/--
lemma `isConj_iff₀` / 引理 `isConj_iff₀`

English:
lemma isConj_iff₀
  statement: IsConj a b ↔ exists c : α, c != 0 ∧ c * a * c⁻¹ = b
  proof: by
  rw [IsConj]; rw [Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  congr! 2 with c
  exact and_congr_right (mul_inv_eq_iff_eq_mul₀ · |>.symm)

中文:
引理 isConj_iff₀
  结论: IsConj a b ↔ 存在 c : α, c != 0 ∧ c * a * c⁻¹ = b
  证明: by
  rw [IsConj]; rw [Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  congr! 2 with c
  exact and_congr_right (mul_inv_eq_iff_eq_mul₀ · |>.symm)
-/
@[simp] lemma isConj_iff₀ : IsConj a b ↔ exists c : α, c != 0 ∧ c * a * c⁻¹ = b := by
  rw [IsConj]; rw [Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  congr! 2 with c
  exact and_congr_right (mul_inv_eq_iff_eq_mul₀ · |>.symm)

/--
lemma `conj_pow₀` / 引理 `conj_pow₀`

English:
lemma conj_pow₀
  given: {s : Nat} {a d : α} (ha : a != 0)
  statement: (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a
  proof: let u : αˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  Units.conj_pow' u d s

中文:
引理 conj_pow₀
  条件: {s : 自然数} {a d : α} (ha : a != 0)
  结论: (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a
  证明: let u : αˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  Units.conj_pow' u d s

Depends on / 依赖: Units.conj_pow, conj_pow
-/
lemma conj_pow₀ {s : Nat} {a d : α} (ha : a != 0) : (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a :=
  let u : αˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  Units.conj_pow' u d s

end GroupWithZero
