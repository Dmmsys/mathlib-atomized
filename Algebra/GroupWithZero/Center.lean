/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Center of a group with zero
-/

public section

assert_not_exists RelIso Finset Ring Subsemigroup

variable {M₀ G₀ : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s : Set M₀}

/--
lemma `zero_mem_center` / 引理 `zero_mem_center`

English:
lemma zero_mem_center
  statement: (0 : M₀) in center M₀ where
  proof: by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]

中文:
引理 zero_mem_center
  结论: (0 : M₀) in center M₀ where
  证明: by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]
-/
@[simp] lemma zero_mem_center : (0 : M₀) in center M₀ where
  comm _ := by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]

/--
lemma `zero_mem_centralizer` / 引理 `zero_mem_centralizer`

English:
lemma zero_mem_centralizer
  statement: (0 : M₀) in centralizer s
  proof: by simp [mem_centralizer_iff]

中文:
引理 zero_mem_centralizer
  结论: (0 : M₀) in centralizer s
  证明: by simp [mem_centralizer_iff]
-/
@[simp] lemma zero_mem_centralizer : (0 : M₀) in centralizer s := by simp [mem_centralizer_iff]

end MulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

/--
lemma `center_units_subset` / 引理 `center_units_subset`

English:
lemma center_units_subset
  statement: center G₀ˣ subseteq ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
  proof: by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
· exact congr_arg Units.val hu Units.mk0 a ha

中文:
引理 center_units_subset
  结论: center G₀ˣ subseteq ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
  证明: by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
· exact congr_arg Units.val hu Units.mk0 a ha

Depends on / 依赖: Semigroup, Units.mk0, Units.val, _root_, _root_.Semigroup.mem_center_iff, congr_arg, eq_or_ne, mem_center_iff, mem_preimage, mul_zero, simp_rw, subset_def, zero_mul
-/
lemma center_units_subset : center G₀ˣ subseteq ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀ := by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
· exact congr_arg Units.val hu Units.mk0 a ha

/--
lemma `center_units_eq` / 引理 `center_units_eq`

English:
lemma center_units_eq
  statement: center G₀ˣ = ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
  proof: center_units_subset.antisymm subset_center_units

中文:
引理 center_units_eq
  结论: center G₀ˣ = ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀
  证明: center_units_subset.antisymm subset_center_units

Depends on / 依赖: antisymm, center_units_subset, center_units_subset.antisymm, subset_center_units
-/
lemma center_units_eq : center G₀ˣ = ((↑) : G₀ˣ -> G₀) ⁻¹' center G₀ :=
  center_units_subset.antisymm subset_center_units

/--
lemma `inv_mem_centralizer₀` / 引理 `inv_mem_centralizer₀`

English:
lemma inv_mem_centralizer₀
  given: (ha : a in centralizer s)
  statement: a⁻¹ in centralizer s
  proof: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_centralizer
  · rintro c hc
    rw [mul_inv_eq_iff_eq_mul₀ ha₀]; rw [mul_assoc]; rw [eq_inv_mul_iff_mul_eq₀ ha₀]; rw [ha c hc]

中文:
引理 inv_mem_centralizer₀
  条件: (ha : a in centralizer s)
  结论: a⁻¹ in centralizer s
  证明: by
  obtain rfl | ha₀ := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_centralizer
  · rintro c hc
    rw [mul_inv_eq_iff_eq_mul₀ ha₀]; rw [mul_assoc]; rw [eq_inv_mul_iff_mul_eq₀ ha₀]; rw [ha c hc]
-/
@[simp] lemma inv_mem_centralizer₀ (ha : a in centralizer s) : a⁻¹ in centralizer s := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_centralizer
  · rintro c hc
    rw [mul_inv_eq_iff_eq_mul₀ ha₀]; rw [mul_assoc]; rw [eq_inv_mul_iff_mul_eq₀ ha₀]; rw [ha c hc]

/--
lemma `div_mem_centralizer₀` / 引理 `div_mem_centralizer₀`

English:
lemma div_mem_centralizer₀
  given: (ha : a in centralizer s) (hb : b in centralizer s)
  proof: by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer₀ hb)

中文:
引理 div_mem_centralizer₀
  条件: (ha : a in centralizer s) (hb : b in centralizer s)
  证明: by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer₀ hb)
-/
@[simp] lemma div_mem_centralizer₀ (ha : a in centralizer s) (hb : b in centralizer s) :
    a / b in centralizer s := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer₀ hb)

end GroupWithZero
end Set
