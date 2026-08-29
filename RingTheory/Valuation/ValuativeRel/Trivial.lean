/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!

# Trivial Valuative Relations

Trivial valuative relations relate all non-zero elements to each other. Equivalently,
all elements are related to `1`: the relation is equal to the relation induced
by the trivial valuation which sends all non-zero elements to `1`.

## TODO

A trivial valuative relation is equivalent to the value group being isomorphic to `WithZero Unit`.

-/

@[expose] public section

namespace ValuativeRel

variable {R Γ : Type} [Ring R] [DecidableEq R] [IsDomain R]
  [LinearOrderedCommGroupWithZero Γ]

open WithZero

/-- The trivial valuative relation on a domain `R`, such that all non-zero elements are related.
The domain condition is necessary so that the relation is closed when multiplying.
-/
@[instance_reducible]
/--
Definition of `trivialRel` / `trivialRel` 的定义

English:
definition trivialRel
  signature: {R : Type} [Semiring R] [DecidableEq R] [IsDomain R]
  body: if y = 0 then x = 0 else True
  vle_total _ _ := by split_ifs <;> simp_all
  vle_trans _ _ := by split_ifs; simp_all
  vle_add _ _ := by split_ifs; simp_all
  mul_vle_mul_left _ _ := by split_ifs at * <;> simp_all
  vle_mul_cancel _ := by split_ifs <;> simp_all
  not_vle_one_zero := by split_ifs <;> simp_all
  vle_mul_comm {_ _} := by simpa using Or.symm

中文:
定义 trivialRel
  签名: {R : 类型} [半环 R] [DecidableEq R] [是整环 R]
  定义体: if y = 0 then x = 0 else True
  vle_total _ _ := by split_ifs <;> simp_all
  vle_trans _ _ := by split_ifs; simp_all
  vle_add _ _ := by split_ifs; simp_all
  mul_vle_mul_left _ _ := by split_ifs at * <;> simp_all
  vle_mul_cancel _ := by split_ifs <;> simp_all
  not_vle_one_zero := by split_ifs <;> simp_all
  vle_mul_comm {_ _} := by simpa using Or.symm
-/
def trivialRel {R : Type} [Semiring R] [DecidableEq R] [IsDomain R] : ValuativeRel R where
  vle x y := if y = 0 then x = 0 else True
  vle_total _ _ := by split_ifs <;> simp_all
  vle_trans _ _ := by split_ifs; simp_all
  vle_add _ _ := by split_ifs; simp_all
  mul_vle_mul_left _ _ := by split_ifs at * <;> simp_all
  vle_mul_cancel _ := by split_ifs <;> simp_all
  not_vle_one_zero := by split_ifs <;> simp_all
  vle_mul_comm {_ _} := by simpa using Or.symm

/--
lemma `eq_trivialRel_of_compatible_one` / 引理 `eq_trivialRel_of_compatible_one`

English:
lemma eq_trivialRel_of_compatible_one
  statement: [h : ValuativeRel R]
  proof: by
  ext
  change _ ↔ if _ = 0 then _ else _
  rw [hv.vle_iff_le]
  split_ifs <;>
  simp_all [Valuation.one_apply_of_ne_zero, Valuation.one_apply_le_one]

中文:
引理 eq_trivialRel_of_compatible_one
  结论: [h : ValuativeRel R]
  证明: by
  ext
  change _ ↔ if _ = 0 then _ else _
  rw [hv.vle_iff_le]
  split_ifs <;>
  simp_all [Valuation.one_apply_of_ne_zero, Valuation.one_apply_le_one]

Depends on / 依赖: Valuation, Valuation.one_apply_le_one, Valuation.one_apply_of_ne_zero, hv.vle_iff_le, one_apply_le_one, one_apply_of_ne_zero, split_ifs, vle_iff_le
-/
lemma eq_trivialRel_of_compatible_one [h : ValuativeRel R]
    [hv : Valuation.Compatible (1 : Valuation R Γ)] : h = trivialRel := by
  ext
  change _ ↔ if _ = 0 then _ else _
  rw [hv.vle_iff_le]
  split_ifs <;>
  simp_all [Valuation.one_apply_of_ne_zero, Valuation.one_apply_le_one]

/--
lemma `trivialRel_eq_ofValuation_one` / 引理 `trivialRel_eq_ofValuation_one`

English:
lemma trivialRel_eq_ofValuation_one
  proof: by
  convert! (eq_trivialRel_of_compatible_one (Γ := Γ)).symm
  exact Valuation.Compatible.ofValuation 1

中文:
引理 trivialRel_eq_ofValuation_one
  证明: by
  convert! (eq_trivialRel_of_compatible_one (Γ := Γ)).symm
  exact Valuation.Compatible.ofValuation 1

Depends on / 依赖: Compatible, Valuation, Valuation.Compatible.ofValuation, convert, eq_trivialRel_of_compatible_one, ofValuation
-/
lemma trivialRel_eq_ofValuation_one :
    trivialRel = ValuativeRel.ofValuation (1 : Valuation R Γ) := by
  convert! (eq_trivialRel_of_compatible_one (Γ := Γ)).symm
  exact Valuation.Compatible.ofValuation 1

variable (R Γ) in
/--
lemma `subsingleton_units_valueGroupWithZero_of_trivialRel` / 引理 `subsingleton_units_valueGroupWithZero_of_trivialRel`

English:
lemma subsingleton_units_valueGroupWithZero_of_trivialRel
  statement: [ValuativeRel R]
  proof: by
  constructor
  intro a b
  have : (valuation R).IsEquiv (1 : Valuation R Γ) := isEquiv _ _
  obtain ⟨r, s, hr⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq a
  obtain ⟨t, u, ht⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq b
  rw [Units.ext_iff]; rw [← hr]; rw [← ht]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [this.eq_iff] <;>
  simp [one_apply_posSubmonoid]

中文:
引理 subsingleton_units_valueGroupWithZero_of_trivialRel
  结论: [ValuativeRel R]
  证明: by
  constructor
  intro a b
  have : (valuation R).IsEquiv (1 : Valuation R Γ) := isEquiv _ _
  obtain ⟨r, s, hr⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq a
  obtain ⟨t, u, ht⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq b
  rw [Units.ext_iff]; rw [← hr]; rw [← ht]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [this.eq_iff] <;>
  simp [one_apply_posSubmonoid]

Depends on / 依赖: IsEquiv, Units.ext_iff, Valuation, div_eq_div_iff, eq_iff, exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq, ext_iff, isEquiv, map_mul, one_apply_posSubmonoid, this.eq_iff, valuation
-/
lemma subsingleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R]
    [Valuation.Compatible (1 : Valuation R Γ)] :
    Subsingleton (ValueGroupWithZero R)ˣ := by
  constructor
  intro a b
  have : (valuation R).IsEquiv (1 : Valuation R Γ) := isEquiv _ _
  obtain ⟨r, s, hr⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq a
  obtain ⟨t, u, ht⟩ := exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq b
  rw [Units.ext_iff]; rw [← hr]; rw [← ht]; rw [div_eq_div_iff]; rw [← map_mul]; rw [← map_mul]; rw [this.eq_iff] <;>
  simp [one_apply_posSubmonoid]

/--
lemma `not_isNontrivial_of_trivialRel` / 引理 `not_isNontrivial_of_trivialRel`

English:
lemma not_isNontrivial_of_trivialRel
  given: [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)]
  proof: by
  rintro ⟨⟨x, hx, hx'⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · simp_all [Subsingleton.elim u 1]

中文:
引理 not_isNontrivial_of_trivialRel
  条件: [ValuativeRel R] [赋值.余mpatible (1 : 赋值 R Γ)]
  证明: by
  rintro ⟨⟨x, hx, hx'⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · simp_all [Subsingleton.elim u 1]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, Subsingleton, Subsingleton.elim, eq_zero_or_unit, subsingleton_units_valueGroupWithZero_of_trivialRel
-/
lemma not_isNontrivial_of_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    ¬ IsNontrivial R := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · simp_all [Subsingleton.elim u 1]

/--
lemma `isDiscrete_trivialRel` / 引理 `isDiscrete_trivialRel`

English:
lemma isDiscrete_trivialRel
  given: [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)]
  proof: by
  refine ⟨⟨0, zero_lt_one, fun x => ?_⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp
  · rw [← Units.val_one, Units.val_lt_val]
    simp

中文:
引理 isDiscrete_trivialRel
  条件: [ValuativeRel R] [赋值.余mpatible (1 : 赋值 R Γ)]
  证明: by
  refine ⟨⟨0, zero_lt_one, fun x => ?_⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp
  · rw [← Units.val_one, Units.val_lt_val]
    simp

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, Units.val_lt_val, Units.val_one, eq_zero_or_unit, subsingleton_units_valueGroupWithZero_of_trivialRel, val_lt_val, val_one, zero_lt_one
-/
lemma isDiscrete_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    IsDiscrete R := by
  refine ⟨⟨0, zero_lt_one, fun x => ?_⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp
  · rw [← Units.val_one, Units.val_lt_val]
    simp

end ValuativeRel
